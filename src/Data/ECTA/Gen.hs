{-# LANGUAGE OverloadedStrings #-}

{- | Indexed generators whose transparent regions are represented as ECTAs.

An indexed source stores a finite cardinality and a function from indices to
values. Applicative composition builds an ECTA over those indices without
materializing the generated values. Values are decoded only when a concrete
term is inspected or sampled.
-}
module Data.ECTA.Gen (
    Indexed (..),
    ECTAGen,
    ECTAGenError (..),
    GenBackend (..),
    fromIndexed,
    fromBackend,
    elements,
    frequency,
    innerJoinOn,
    support,
    pmf,
    lower,
) where

import qualified Data.Map.Strict as Map
import Data.Ratio (denominator, numerator)
import qualified Data.Text as Text

import Data.ECTA (
    Edge (Edge),
    Node (EmptyNode, Node),
    getAllTerms,
    mkEdge,
    reducePartially,
 )
import Data.ECTA.Paths (mkEqConstraints, path)
import Data.ECTA.Term (Symbol (Symbol), Term (Term))

{- | A finite source addressed by a stable integer index.

The selector is called only with an index in @[0, indexedCardinality)@.
-}
data Indexed a = Indexed
    { indexedCardinality :: !Integer
    -- ^ Number of selectable values.
    , indexedSelect :: Integer -> a
    -- ^ Decode one valid index.
    }

-- | Backend operations needed only when sampling or crossing an opaque region.
class (Applicative gen) => GenBackend gen where
    -- | Select an integer in @[0, bound)@.
    selectInteger :: Integer -> gen Integer

    -- | Select one backend generator with a positive relative weight.
    frequencyGen :: [(Integer, gen a)] -> gen a

    -- | Retry until the generated value satisfies a predicate.
    filterGen :: (a -> Bool) -> gen a -> gen a

-- | Failure while constructing, inspecting, or sampling a generator.
data ECTAGenError
    = EmptyGenerator
    | NonPositiveWeight !Integer
    | CannotInspectOpaqueGenerator
    | InvalidGeneratorTerm !Term
    | SelectionOutOfRange !Integer !Integer
    deriving (Eq, Show)

-- | One transparent ECTA with a compiler from terms to weighted values.
data Static a = Static
    { staticSupport :: !Node
    , staticCompile :: Term -> Either ECTAGenError (Rational, a)
    }

-- | A generator is either inspectable ECTA structure or an opaque backend action.
data ECTAGen gen a
    = Transparent !(Either ECTAGenError (Static a))
    | Opaque !(gen (Either ECTAGenError a))

instance (Functor gen) => Functor (ECTAGen gen) where
    fmap apply (Transparent result) = Transparent $ fmap (mapStatic apply) result
    fmap apply (Opaque generated) = Opaque $ fmap (fmap apply) generated

instance (GenBackend gen) => Applicative (ECTAGen gen) where
    pure value = Transparent $ Right $ pureStatic value

    Transparent (Left err) <*> _ = Transparent $ Left err
    _ <*> Transparent (Left err) = Transparent $ Left err
    Transparent (Right functions) <*> Transparent (Right values) =
        Transparent $ Right $ applyStatic functions values
    functions <*> values =
        Opaque $ liftA2 (<*>) (lower functions) (lower values)

-- | Lift one finite indexed source into transparent ECTA structure.
fromIndexed :: Indexed a -> ECTAGen gen a
fromIndexed indexed
    | indexedCardinality indexed <= 0 = Transparent $ Left EmptyGenerator
    | otherwise = Transparent $ Right $ indexedStatic indexed

-- | Embed an opaque backend generator.
fromBackend :: (Functor gen) => gen a -> ECTAGen gen a
fromBackend generated = Opaque $ Right <$> generated

-- | Choose uniformly from a finite non-empty list.
elements :: [a] -> ECTAGen gen a
elements values =
    fromIndexed $
        Indexed
            (toInteger $ length values)
            (\index -> atIndex "elements" index values)

-- | Choose one generator with the supplied positive relative weight.
frequency ::
    (GenBackend gen) =>
    [(Integer, ECTAGen gen a)] ->
    ECTAGen gen a
frequency [] = Transparent $ Left EmptyGenerator
frequency alternatives
    | Just badWeight <- firstNonPositive alternatives =
        Transparent $ Left $ NonPositiveWeight badWeight
    | Just err <- firstError alternatives = Transparent $ Left err
    | Just staticAlternatives <- traverse getStatic alternatives =
        Transparent $ Right $ frequencyStatic staticAlternatives
    | otherwise =
        Opaque $
            frequencyGen
                [(weight, lower generator) | (weight, generator) <- alternatives]
  where
    firstNonPositive = go
      where
        go [] = Nothing
        go ((weight, _) : rest)
            | weight <= 0 = Just weight
            | otherwise = go rest

    firstError = go
      where
        go [] = Nothing
        go ((_, Transparent (Left err)) : _) = Just err
        go (_ : rest) = go rest

    getStatic (weight, Transparent (Right static)) = Just (weight, static)
    getStatic _ = Nothing

{- | Independently generate two values and condition their projected keys to
agree.

Transparent inputs are joined by adding an equality constraint between encoded
key indices. If either side is opaque, the backend performs rejection instead.
-}
innerJoinOn ::
    (GenBackend gen, Ord key) =>
    (left -> key) ->
    (right -> key) ->
    ECTAGen gen left ->
    ECTAGen gen right ->
    ECTAGen gen (left, right)
innerJoinOn _ _ (Transparent (Left err)) _ = Transparent $ Left err
innerJoinOn _ _ _ (Transparent (Left err)) = Transparent $ Left err
innerJoinOn leftKey rightKey (Transparent (Right left)) (Transparent (Right right)) =
    Transparent $ joinStatic leftKey rightKey left right
innerJoinOn leftKey rightKey left right =
    Opaque $ filterGen matches generatedPairs
  where
    generatedPairs = liftA2 (liftA2 (,)) (lower left) (lower right)
    matches (Left _) = True
    matches (Right (leftValue, rightValue)) =
        leftKey leftValue == rightKey rightValue

-- | Return the ECTA support of a fully transparent generator.
support :: ECTAGen gen a -> Either ECTAGenError Node
support (Transparent result) = staticSupport <$> result
support (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Aggregate the exact probability mass of every transparent result.
pmf :: (Ord a) => ECTAGen gen a -> Either ECTAGenError [(a, Rational)]
pmf (Transparent result) = do
    static <- result
    outcomes <- compileOutcomes static
    pure $
        Map.toAscList $
            Map.fromListWith (+) [(value, mass) | (mass, value) <- outcomes]
pmf (Opaque _) = Left CannotInspectOpaqueGenerator

-- | Lower to the backend, preserving construction and decoding errors.
lower :: (GenBackend gen) => ECTAGen gen a -> gen (Either ECTAGenError a)
lower (Transparent (Left err)) = pure $ Left err
lower (Transparent (Right static)) = sampleStatic static
lower (Opaque generated) = generated

mapStatic :: (a -> b) -> Static a -> Static b
mapStatic apply static =
    Static
        (staticSupport static)
        (fmap (fmap apply) . staticCompile static)

pureStatic :: a -> Static a
pureStatic value =
    Static
        (Node [Edge pureSymbol []])
        compile
  where
    compile term@(Term symbol [])
        | symbol == pureSymbol = Right (1, value)
        | otherwise = Left $ InvalidGeneratorTerm term
    compile term = Left $ InvalidGeneratorTerm term

indexedStatic :: Indexed a -> Static a
indexedStatic indexed =
    Static
        (Node [Edge symbol [] | symbol <- Map.keys indices])
        compile
  where
    cardinality = indexedCardinality indexed
    indices =
        Map.fromList
            [ (indexedSymbol index, index)
            | index <- [0 .. cardinality - 1]
            ]

    compile term@(Term symbol []) = case Map.lookup symbol indices of
        Just index ->
            Right
                ( 1 / fromInteger cardinality
                , indexedSelect indexed index
                )
        Nothing -> Left $ InvalidGeneratorTerm term
    compile term = Left $ InvalidGeneratorTerm term

applyStatic :: Static (a -> b) -> Static a -> Static b
applyStatic functions values =
    Static
        ( Node
            [ Edge
                applySymbol
                [staticSupport functions, staticSupport values]
            ]
        )
        compile
  where
    compile term@(Term symbol [functionTerm, valueTerm])
        | symbol == applySymbol = do
            (functionMass, function) <- staticCompile functions functionTerm
            (valueMass, value) <- staticCompile values valueTerm
            pure (functionMass * valueMass, function value)
        | otherwise = Left $ InvalidGeneratorTerm term
    compile term = Left $ InvalidGeneratorTerm term

frequencyStatic :: [(Integer, Static a)] -> Static a
frequencyStatic alternatives =
    Static
        ( Node
            [ Edge symbol [staticSupport static]
            | (symbol, (_, static)) <- Map.toAscList branches
            ]
        )
        compile
  where
    totalWeight = sum $ map fst alternatives
    branches =
        Map.fromList
            [ (frequencySymbol index, alternative)
            | (index, alternative) <- zip [0 :: Int ..] alternatives
            ]

    compile term@(Term symbol [child]) = case Map.lookup symbol branches of
        Just (weight, static) -> do
            (childMass, value) <- staticCompile static child
            pure
                ( fromInteger weight / fromInteger totalWeight * childMass
                , value
                )
        Nothing -> Left $ InvalidGeneratorTerm term
    compile term = Left $ InvalidGeneratorTerm term

joinStatic ::
    (Ord key) =>
    (left -> key) ->
    (right -> key) ->
    Static left ->
    Static right ->
    Either ECTAGenError (Static (left, right))
joinStatic leftKey rightKey left right = do
    leftEntries <- keyedTerms leftKey left
    rightEntries <- keyedTerms rightKey right
    let shared =
            Map.intersectionWith
                (,)
                (groupTerms leftEntries)
                (groupTerms rightEntries)
    if Map.null shared
        then Left EmptyGenerator
        else
            let numbered = zip [0 :: Int ..] $ Map.toAscList shared
                leftNode =
                    Node
                        [ Edge
                            leftKeyedSymbol
                            [keyNode keyIndex, singletonNode term]
                        | (keyIndex, (_, (leftTerms, _))) <- numbered
                        , term <- leftTerms
                        ]
                rightNode =
                    Node
                        [ Edge
                            rightKeyedSymbol
                            [keyNode keyIndex, singletonNode term]
                        | (keyIndex, (_, (_, rightTerms))) <- numbered
                        , term <- rightTerms
                        ]
                joined =
                    reducePartially $
                        Node
                            [ mkEdge
                                joinSymbol
                                [leftNode, rightNode]
                                (mkEqConstraints [[path [0, 0], path [1, 0]]])
                            ]
             in if joined == EmptyNode
                    then Left EmptyGenerator
                    else Right $ Static joined compile
  where
    compile term@(Term symbol [leftTerm, rightTerm])
        | symbol == joinSymbol = do
            (leftMass, leftValue) <- compileKeyed leftKeyedSymbol left leftTerm
            (rightMass, rightValue) <- compileKeyed rightKeyedSymbol right rightTerm
            pure (leftMass * rightMass, (leftValue, rightValue))
        | otherwise = Left $ InvalidGeneratorTerm term
    compile term = Left $ InvalidGeneratorTerm term

keyedTerms ::
    (value -> key) ->
    Static value ->
    Either ECTAGenError [(key, Term)]
keyedTerms key static =
    traverse
        ( \term -> do
            (_, value) <- staticCompile static term
            pure (key value, term)
        )
        (getAllTerms $ staticSupport static)

groupTerms :: (Ord key) => [(key, Term)] -> Map.Map key [Term]
groupTerms = Map.fromListWith (<>) . map (fmap pure)

compileKeyed ::
    Symbol ->
    Static a ->
    Term ->
    Either ECTAGenError (Rational, a)
compileKeyed expected static term@(Term symbol [_keyTerm, valueTerm])
    | symbol == expected = staticCompile static valueTerm
    | otherwise = Left $ InvalidGeneratorTerm term
compileKeyed _ _ term = Left $ InvalidGeneratorTerm term

keyNode :: Int -> Node
keyNode index = Node [Edge (keySymbol index) []]

singletonNode :: Term -> Node
singletonNode (Term symbol children) =
    Node [Edge symbol $ map singletonNode children]

compileOutcomes :: Static a -> Either ECTAGenError [(Rational, a)]
compileOutcomes static = do
    outcomes <- traverse (staticCompile static) $ getAllTerms $ staticSupport static
    normalize outcomes

sampleStatic ::
    (GenBackend gen) =>
    Static a ->
    gen (Either ECTAGenError a)
sampleStatic static = case compileOutcomes static >>= integerOutcomes of
    Left err -> pure $ Left err
    Right outcomes ->
        let total = sum $ map fst outcomes
         in choose outcomes total <$> selectInteger total
  where
    choose outcomes total selected
        | selected < 0 || selected >= total =
            Left $ SelectionOutOfRange selected total
        | otherwise = Right $ pick selected outcomes

    pick _ [] = error "sampleStatic: impossible empty distribution"
    pick selected ((weight, value) : remaining)
        | selected < weight = value
        | otherwise = pick (selected - weight) remaining

normalize :: [(Rational, a)] -> Either ECTAGenError [(Rational, a)]
normalize [] = Left EmptyGenerator
normalize outcomes =
    let total = sum $ map fst outcomes
     in if total <= 0
            then Left EmptyGenerator
            else Right [(mass / total, value) | (mass, value) <- outcomes]

integerOutcomes ::
    [(Rational, a)] ->
    Either ECTAGenError [(Integer, a)]
integerOutcomes [] = Left EmptyGenerator
integerOutcomes outcomes =
    let masses = map fst outcomes
        commonDenominator = foldl lcm 1 $ map denominator masses
        unscaled =
            [ numerator mass * (commonDenominator `div` denominator mass)
            | mass <- masses
            ]
        commonFactor = foldl gcd 0 unscaled
     in if any (<= 0) unscaled
            then Left EmptyGenerator
            else
                Right $
                    zip
                        (map (`div` commonFactor) unscaled)
                        (map snd outcomes)

atIndex :: String -> Integer -> [a] -> a
atIndex label index values
    | index < 0 = error $ label <> ": negative index"
    | otherwise = case drop (fromInteger index) values of
        value : _ -> value
        [] -> error $ label <> ": index out of range"

pureSymbol, applySymbol, joinSymbol, leftKeyedSymbol, rightKeyedSymbol :: Symbol
pureSymbol = "$ecta-gen/pure"
applySymbol = "$ecta-gen/apply"
joinSymbol = "$ecta-gen/join"
leftKeyedSymbol = "$ecta-gen/left-keyed"
rightKeyedSymbol = "$ecta-gen/right-keyed"

indexedSymbol :: Integer -> Symbol
indexedSymbol index = Symbol $ Text.pack $ "$ecta-gen/index/" <> show index

frequencySymbol :: Int -> Symbol
frequencySymbol index = Symbol $ Text.pack $ "$ecta-gen/frequency/" <> show index

keySymbol :: Int -> Symbol
keySymbol index = Symbol $ Text.pack $ "$ecta-gen/key/" <> show index
