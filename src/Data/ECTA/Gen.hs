{-# LANGUAGE OverloadedStrings #-}

{- | Indexed generators whose transparent regions are represented as ECTAs.

An indexed source stores a finite cardinality and a function from indices to
values. Applicative composition tracks exact cardinalities and rank-based
selection alongside the ECTA, without materializing the product language.
Joins count matched key-bucket products and unrank directly within them.
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

import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import Data.Ratio (denominator, numerator)
import Data.Sequence (Seq)
import qualified Data.Sequence as Sequence
import qualified Data.Text as Text

import Data.ECTA (
    Edge (Edge),
    Node (EmptyNode, Node),
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
    | SelectionOutOfRange !Integer !Integer
    deriving (Eq, Show)

-- | One term, its unnormalized mass, and its decoded value.
data Outcome a = Outcome
    { outcomeTerm :: Term
    , outcomeMass :: Rational
    , outcomeValue :: a
    }

-- | A finite language with exact cardinality and rank-based selection.
data OutcomeIndex a = OutcomeIndex
    { outcomeCardinality :: !Integer
    , outcomeUniformMass :: !(Maybe Rational)
    , outcomeSelect :: Integer -> Either ECTAGenError (Outcome a)
    }

-- | One equality-key bucket used to count and unrank a conditioned product.
data JoinGroup left right = JoinGroup
    { joinGroupIndex :: !Int
    , joinGroupLeft :: !(Seq (Outcome left))
    , joinGroupRight :: !(Seq (Outcome right))
    }

-- | One transparent ECTA with a matching indexed outcome language.
data Static a = Static
    { staticSupport :: !Node
    , staticOutcomes :: !(OutcomeIndex a)
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
        (mapOutcomeIndex apply $ staticOutcomes static)

pureStatic :: a -> Static a
pureStatic value =
    Static
        (Node [Edge pureSymbol []])
        ( OutcomeIndex
            1
            (Just 1)
            ( \index -> do
                checkIndex 1 index
                pure $ Outcome (Term pureSymbol []) 1 value
            )
        )

indexedStatic :: Indexed a -> Static a
indexedStatic indexed =
    Static
        (Node [Edge (indexedSymbol index) [] | index <- [0 .. cardinality - 1]])
        ( OutcomeIndex
            cardinality
            (Just $ 1 / fromInteger cardinality)
            select
        )
  where
    cardinality = indexedCardinality indexed
    select index = do
        checkIndex cardinality index
        pure $
            Outcome
                (Term (indexedSymbol index) [])
                (1 / fromInteger cardinality)
                (indexedSelect indexed index)

applyStatic :: Static (a -> b) -> Static a -> Static b
applyStatic functions values =
    Static
        ( Node
            [ Edge
                applySymbol
                [staticSupport functions, staticSupport values]
            ]
        )
        ( OutcomeIndex
            cardinality
            ((*) <$> outcomeUniformMass functionOutcomes <*> outcomeUniformMass valueOutcomes)
            select
        )
  where
    functionOutcomes = staticOutcomes functions
    valueOutcomes = staticOutcomes values
    valueCardinality = outcomeCardinality valueOutcomes
    cardinality = outcomeCardinality functionOutcomes * valueCardinality

    select index = do
        checkIndex cardinality index
        let (functionIndex, valueIndex) = index `divMod` valueCardinality
        functionOutcome <- outcomeSelect functionOutcomes functionIndex
        valueOutcome <- outcomeSelect valueOutcomes valueIndex
        pure $
            Outcome
                ( Term
                    applySymbol
                    [outcomeTerm functionOutcome, outcomeTerm valueOutcome]
                )
                (outcomeMass functionOutcome * outcomeMass valueOutcome)
                (outcomeValue functionOutcome $ outcomeValue valueOutcome)

frequencyStatic :: [(Integer, Static a)] -> Static a
frequencyStatic alternatives =
    Static
        ( Node
            [ Edge (frequencySymbol index) [staticSupport static]
            | (index, (_, static)) <- numbered
            ]
        )
        ( OutcomeIndex
            cardinality
            uniformMass
            select
        )
  where
    totalWeight = sum $ map fst alternatives
    numbered = zip [0 :: Int ..] alternatives
    cardinality = sum [outcomeCardinality $ staticOutcomes static | (_, static) <- alternatives]
    uniformMass = commonValue $ map branchUniformMass alternatives

    branchUniformMass (weight, static) =
        (fromInteger weight / fromInteger totalWeight *)
            <$> outcomeUniformMass (staticOutcomes static)

    select index = do
        checkIndex cardinality index
        (branchIndex, weight, static, childIndex) <- selectBranch index numbered
        child <- outcomeSelect (staticOutcomes static) childIndex
        pure $
            Outcome
                (Term (frequencySymbol branchIndex) [outcomeTerm child])
                ( fromInteger weight
                    / fromInteger totalWeight
                    * outcomeMass child
                )
                (outcomeValue child)

    selectBranch _ [] = Left EmptyGenerator
    selectBranch index ((branchIndex, (weight, static)) : remaining)
        | index < branchCardinality = Right (branchIndex, weight, static, index)
        | otherwise = selectBranch (index - branchCardinality) remaining
      where
        branchCardinality = outcomeCardinality $ staticOutcomes static

joinStatic ::
    (Ord key) =>
    (left -> key) ->
    (right -> key) ->
    Static left ->
    Static right ->
    Either ECTAGenError (Static (left, right))
joinStatic leftKey rightKey left right = do
    leftEntries <- keyedOutcomes leftKey left
    rightEntries <- keyedOutcomes rightKey right
    let shared =
            Map.intersectionWith
                (,)
                (groupOutcomes leftEntries)
                (groupOutcomes rightEntries)
    if Map.null shared
        then Left EmptyGenerator
        else
            let groups =
                    [ JoinGroup
                        keyIndex
                        (Sequence.fromList leftOutcomes)
                        (Sequence.fromList rightOutcomes)
                    | (keyIndex, (_, (leftOutcomes, rightOutcomes))) <-
                        zip [0 :: Int ..] $ Map.toAscList shared
                    ]
                leftNode =
                    Node
                        [ Edge
                            leftKeyedSymbol
                            [ keyNode $ joinGroupIndex group
                            , singletonNode $ outcomeTerm outcome
                            ]
                        | group <- groups
                        , outcome <- toList $ joinGroupLeft group
                        ]
                rightNode =
                    Node
                        [ Edge
                            rightKeyedSymbol
                            [ keyNode $ joinGroupIndex group
                            , singletonNode $ outcomeTerm outcome
                            ]
                        | group <- groups
                        , outcome <- toList $ joinGroupRight group
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
                    else Right $ Static joined $ joinOutcomeIndex left right groups

keyedOutcomes ::
    (value -> key) ->
    Static value ->
    Either ECTAGenError [(key, Outcome value)]
keyedOutcomes key static =
    map (\outcome -> (key $ outcomeValue outcome, outcome))
        <$> enumerateOutcomeIndex (staticOutcomes static)

groupOutcomes :: (Ord key) => [(key, Outcome value)] -> Map.Map key [Outcome value]
groupOutcomes = Map.fromListWith (<>) . map (fmap pure)

joinOutcomeIndex ::
    Static left ->
    Static right ->
    [JoinGroup left right] ->
    OutcomeIndex (left, right)
joinOutcomeIndex left right groups =
    OutcomeIndex
        cardinality
        ((*) <$> outcomeUniformMass (staticOutcomes left) <*> outcomeUniformMass (staticOutcomes right))
        select
  where
    cardinality = sum $ map joinGroupCardinality groups

    select index = do
        checkIndex cardinality index
        (group, groupIndex) <- selectJoinGroup index groups
        let rightCardinality = toInteger $ Sequence.length $ joinGroupRight group
            (leftIndex, rightIndex) = groupIndex `divMod` rightCardinality
            leftOutcome = Sequence.index (joinGroupLeft group) $ fromInteger leftIndex
            rightOutcome = Sequence.index (joinGroupRight group) $ fromInteger rightIndex
            keyTerm = Term (keySymbol $ joinGroupIndex group) []
            leftTerm =
                Term leftKeyedSymbol [keyTerm, outcomeTerm leftOutcome]
            rightTerm =
                Term rightKeyedSymbol [keyTerm, outcomeTerm rightOutcome]
        pure $
            Outcome
                (Term joinSymbol [leftTerm, rightTerm])
                (outcomeMass leftOutcome * outcomeMass rightOutcome)
                (outcomeValue leftOutcome, outcomeValue rightOutcome)

joinGroupCardinality :: JoinGroup left right -> Integer
joinGroupCardinality group =
    toInteger (Sequence.length $ joinGroupLeft group)
        * toInteger (Sequence.length $ joinGroupRight group)

selectJoinGroup ::
    Integer ->
    [JoinGroup left right] ->
    Either ECTAGenError (JoinGroup left right, Integer)
selectJoinGroup _ [] = Left EmptyGenerator
selectJoinGroup index (group : remaining)
    | index < cardinality = Right (group, index)
    | otherwise = selectJoinGroup (index - cardinality) remaining
  where
    cardinality = joinGroupCardinality group

keyNode :: Int -> Node
keyNode index = Node [Edge (keySymbol index) []]

singletonNode :: Term -> Node
singletonNode (Term symbol children) =
    Node [Edge symbol $ map singletonNode children]

compileOutcomes :: Static a -> Either ECTAGenError [(Rational, a)]
compileOutcomes static = do
    outcomes <- enumerateOutcomeIndex $ staticOutcomes static
    normalize [(outcomeMass outcome, outcomeValue outcome) | outcome <- outcomes]

sampleStatic ::
    (GenBackend gen) =>
    Static a ->
    gen (Either ECTAGenError a)
sampleStatic static
    | Just _ <- outcomeUniformMass outcomes =
        select <$> selectInteger cardinality
    | otherwise = case compileOutcomes static >>= integerOutcomes of
        Left err -> pure $ Left err
        Right weightedOutcomes ->
            let total = sum $ map fst weightedOutcomes
             in choose weightedOutcomes total <$> selectInteger total
  where
    outcomes = staticOutcomes static
    cardinality = outcomeCardinality outcomes

    select index = outcomeValue <$> outcomeSelect outcomes index

    choose weightedOutcomes total selected
        | selected < 0 || selected >= total =
            Left $ SelectionOutOfRange selected total
        | otherwise = Right $ pick selected weightedOutcomes

    pick _ [] = error "sampleStatic: impossible empty distribution"
    pick selected ((weight, value) : remaining)
        | selected < weight = value
        | otherwise = pick (selected - weight) remaining

mapOutcomeIndex :: (a -> b) -> OutcomeIndex a -> OutcomeIndex b
mapOutcomeIndex apply outcomes =
    OutcomeIndex
        (outcomeCardinality outcomes)
        (outcomeUniformMass outcomes)
        (\index -> mapOutcome apply <$> outcomeSelect outcomes index)

mapOutcome :: (a -> b) -> Outcome a -> Outcome b
mapOutcome apply outcome =
    Outcome
        (outcomeTerm outcome)
        (outcomeMass outcome)
        (apply $ outcomeValue outcome)

enumerateOutcomeIndex :: OutcomeIndex a -> Either ECTAGenError [Outcome a]
enumerateOutcomeIndex outcomes =
    traverse
        (outcomeSelect outcomes)
        [0 .. outcomeCardinality outcomes - 1]

commonValue :: (Eq a) => [Maybe a] -> Maybe a
commonValue [] = Nothing
commonValue (Just value : remaining)
    | all (== Just value) remaining = Just value
commonValue _ = Nothing

checkIndex :: Integer -> Integer -> Either ECTAGenError ()
checkIndex cardinality index
    | index < 0 || index >= cardinality =
        Left $ SelectionOutOfRange index cardinality
    | otherwise = Right ()

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
