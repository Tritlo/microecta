{-# LANGUAGE OverloadedStrings #-}

{- | The transparent-generator engine behind "Data.ECTA.Gen".

Finite languages are represented as a t'Static': an ECTA support paired with
an t'OutcomeIndex' that counts, selects, decodes, and samples outcomes by
rank. This module holds the builders, joins, group buckets, and symbols. The
sampling engine lives in "Data.ECTA.Gen.Internal.Sampler". The public generator
types and combinators live in "Data.ECTA.Gen".
-}
module Data.ECTA.Gen.Internal (
    -- * Sources and failures
    Indexed (..),
    ECTAGenError (..),
    explain,

    -- * Languages
    Outcome (..),
    OutcomeIndex (..),
    Static (..),
    Recursive (..),
    MassIndex,
    KeyedBucket (..),
    KeyedRecursive (..),

    -- * Building languages
    pureStatic,
    indexedStatic,
    applyStatic,
    frequencyStatic,
    atomicStatic,
    mapStatic,
    boundedStatic,
    recursiveFromStatic,
    bucketFromOutcomes,
    mergeBucketGroup,
    mergeComponentsByKey,
    mergeRecursiveGroups,
    keyedRecursive,
    keyedRecursiveFromBuckets,

    -- * Joins
    JoinGroup (..),
    joinStatic,
    relateStatic,
    joinNBucketStatic,
    recursiveJoin,
    groupOutcomes,

    -- * Argument chains
    ArgMaps (..),
    ArgChain (..),
    ArgStatics,
    lookupArgs,
    mapChain,
    chainMass,

    -- * Masses
    emptyMassIndex,
    keyedRecursiveMassAtSize,

    -- * Inspection and lowering
    enumerateOutcomeIndex,
    compileOutcomes,
    mapOutcomeIndex,
    sampleStatic,
    sampleStaticWithRank,
    compiledDecoder,
    checkIndex,
    normalize,

    -- * Support construction
    applySymbol,
    familyNode,
    frequencySymbol,
    joinNode,
    restrictToKey,
) where

import Data.Foldable (toList)
import Data.Kind (Type)
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Sequence
import qualified Data.Text as Text

import Data.ECTA (
    Edge (Edge),
    Node (Node),
    mkEdge,
    reducePartially,
 )
import Data.ECTA.Gen.Internal.Decoder (
    Plan (..),
    RankDecoder (..),
    compilePlan,
 )
import Data.ECTA.Gen.Internal.Sampler
import Data.ECTA.Gen.Internal.Size (
    SizeIndex (sizeClassCounts),
    choiceIndex,
    productIndex,
    sizeClasses,
    sizeIndex,
 )
import Data.ECTA.Gen.Sig (Sig (..))
import Data.ECTA.Paths (mkEqConstraints, path)
import Data.ECTA.Term (Symbol (Symbol), Term (Term))
import Data.Tree.Gen.Internal (Indexed (..))

{- | Failure while constructing, inspecting, or sampling a generator.

The derived 'Show' names the case; 'explain' says what it means and what to
do about it.
-}
data ECTAGenError
    = -- | The language has no members at all.
      EmptyGenerator
    | -- | A weighted alternative carried a weight below one.
      NonPositiveWeight !Integer
    | -- | The generator crosses an opaque region, which has no structure.
      CannotInspectOpaqueGenerator
    | -- | A rank fell outside a language of the given cardinality.
      SelectionOutOfRange !Integer !Integer
    | -- | Ranks start at zero, so a negative rank cannot select a member.
      NegativeRank !Integer
    | {- | Something needing a finite language met a recursive one, which has
      size classes rather than a cardinality.
      -}
      UnboundedGenerator
    | {- | Something needing one ECTA term per member met a recursive
      language, which retains its automaton rather than its members.
      -}
      CannotInspectRecursiveGenerator
    | {- | Alternatives that choose recursive structure carried unequal
      weights. Only finite choices closed by @atomic@ retain weights inside
      recursion.
      -}
      WeightedRecursiveAlternatives
    | -- | The operation family of an application is recursive.
      RecursiveOperationFamily
    | {- | An automaton's edges carry equality constraints, which correlate
      their children: the edge's count is an intersection, not a product.
      -}
      CannotCountConstrainedEdges
    | -- | An automaton has free recursive variables, so it is not a language.
      OpenAutomaton
    | {- | A recursive definition reaches itself without passing through an
      application, so it has no smallest member and no size to count.
      -}
      UnguardedRecursion
    deriving (Eq, Show)

{- | What one failure means, and what to do about it.

Written for the person who hit it: the first line says what the generator
could not do in the vocabulary of the library, and the rest says which
combinator resolves it.
-}
explain :: ECTAGenError -> String
explain EmptyGenerator =
    guidance
        [ "The language has no members."
        , "Common causes: elements or fromIndexed over an empty list, a"
        , "match, relate, or apply whose keys never agree, or a size bound"
        , "below one."
        ]
explain (NonPositiveWeight weight) =
    guidance
        [ "A weighted alternative carries the weight " <> show weight <> ". Weights are"
        , "relative counts, so every alternative needs a weight of one or more."
        , "Fix: give it a positive weight, or use oneof, which weights every"
        , "alternative equally."
        ]
explain CannotInspectOpaqueGenerator =
    guidance
        [ "The generator crosses an opaque region built with fromGen. An"
        , "opaque region has no ECTA structure, so it has no support, no"
        , "cardinality, and no ranks."
        , "Fix: build that region from elements, fromIndexed, or fromECTA, or"
        , "inspect the transparent parts around it instead."
        ]
explain (SelectionOutOfRange rank total)
    | total <= 0 =
        guidance
            [ "Rank " <> show rank <> " was asked of a language with no members."
            , "Fix: see EmptyGenerator for what leaves a language empty."
            ]
    | otherwise =
        guidance
            [ "Rank " <> show rank <> " is outside the language, which holds " <> show total
            , "members ranked 0 to " <> show (total - 1) <> "."
            , "Fix: a rank comes from unrank, toGenWithRank, or a forAll"
            , "counterexample, and replays only into the language it came from."
            , "For a recursive language that means the same size bound too:"
            , "countAtSize reports one size class, and upToSize fixes the"
            , "language a rank has to fall inside."
            ]
explain (NegativeRank rank) =
    guidance
        [ "Rank " <> show rank <> " is negative, but ranks start at zero."
        , "Fix: use a rank returned by toGenWithRank or forAll, or pass a"
        , "non-negative rank to unrank."
        ]
explain UnboundedGenerator =
    guidance
        [ "This needs a language with finitely many members, but the generator"
        , "is recursive: it has a count per size class rather than a"
        , "cardinality."
        , "Fix: bound it with upToSize first. Grouping and mass inspection"
        , "(groupBy, match, relate, pmf, countBy) additionally need one ECTA"
        , "term per member, which only a language read with fromECTA retains."
        , "If every member has one known key, keyed enters the grouped layer"
        , "without inspecting members."
        ]
explain CannotInspectRecursiveGenerator =
    guidance
        [ "The members of this language carry no ECTA term. A recursive"
        , "generator retains its automaton instead of a term per member, and a"
        , "term per member is what groupBy, match, relate, pmf, and countBy"
        , "read."
        , "Fix: keep the layer that needs terms finite, or read the language"
        , "from an automaton with fromECTA, whose members are terms."
        , "If every member has one known key, use keyed instead of groupBy."
        ]
explain WeightedRecursiveAlternatives =
    guidance
        [ "Alternatives that choose recursive structure carry different weights."
        , "Recursive structure is counted by size, so those weights cannot"
        , "also decide how deep the language recurses."
        , "Fix: use oneof, or oneofGrouped in a grouped family, and control"
        , "size with the bound. Put weighted finite choices behind atomic when"
        , "one complete choice should retain its distribution inside recursion."
        ]
explain RecursiveOperationFamily =
    guidance
        [ "The operation family passed to apply is recursive. Which components"
        , "an application has is decided by the operation signatures, so that"
        , "family has to be finite; only the argument families may recurse."
        , "Fix: build the operations with elements and groupBy, and let the"
        , "recursion go through the arguments."
        ]
explain CannotCountConstrainedEdges =
    guidance
        [ "An edge of this automaton carries equality constraints, which"
        , "correlate its children: the edge's count is the size of an"
        , "intersection rather than the product of its children's counts, and"
        , "fromECTA does not compute that."
        , "Fix: build a constrained language with the generator combinators,"
        , "where apply and match count their joins exactly, or read an"
        , "automaton whose edges are unconstrained."
        ]
explain OpenAutomaton =
    guidance
        [ "The automaton has free recursive variables, so it stands for the"
        , "body of a Mu rather than a language of its own."
        , "Fix: pass the whole recursive node, the one createMu returns, not a"
        , "node taken from inside it."
        ]
explain UnguardedRecursion =
    guidance
        [ "The recursive language reaches itself without passing through an"
        , "application, so its members never get smaller and no size class can"
        , "be counted."
        , "Fix: put every occurrence of the argument under <*>, as in"
        , "Branch <$> self <*> self, or under apply in a grouped family. An"
        , "alternative that is the argument itself, such as oneof [leaf, self],"
        , "is the shape to look for."
        ]

-- | One guidance message, one line per element.
guidance :: [String] -> String
guidance = intercalate "\n"

-- | One term, its normalized probability mass, and its decoded value.
data Outcome a = Outcome
    { outcomeTerm :: Term Symbol
    , outcomeMass :: Rational
    , outcomeValue :: a
    }

-- | A finite language with exact cardinality and rank-based selection.
data OutcomeIndex a = OutcomeIndex
    { outcomeCardinality :: !Integer
    , outcomeUniformMass :: !(Maybe Rational)
    , outcomeSelect :: Integer -> Either ECTAGenError (Outcome a)
    , outcomeValueAt :: Integer -> a
    , outcomeSampler :: Sampler a
    {- ^ The compositional sampler is demand-driven. Uniform lowering uses the
    compiled rank plan instead, while weighted and atomic paths force this
    fallback once when they need it.
    -}
    , outcomePlan :: Plan a
    }

-- | Decode positions of one enumerated outcome sequence.
seqPlan :: Seq (Outcome a) -> Plan a
seqPlan outcomes =
    PlanSelect
        (toInteger $ Sequence.length outcomes)
        (outcomeValue . Sequence.index outcomes . fromInteger)

-- | One compatible key-pair bucket used to count and unrank a conditioned product.
data JoinGroup left right = JoinGroup
    { joinGroupIndex :: !Int
    , joinGroupLeft :: !(Seq (Outcome left))
    , joinGroupRight :: !(Seq (Outcome right))
    }

-- | One transparent ECTA with a matching indexed outcome language.
data Static a = Static
    { staticSupport :: Node Symbol
    {- ^ The ECTA support is demand-driven. Counting, mass, and sampling
    use the outcome index without forcing this field. A support observer builds
    it when needed; finite combinators retain their support work as a thunk.
    -}
    , staticOutcomes :: !(OutcomeIndex a)
    , staticAtomic :: !Bool
    {- ^ Whether an explicit atomic boundary closes this finite language.

    Ordinary finite weights do not control recursive structure. 'atomicStatic'
    sets this marker so 'recursiveFromStatic' can preserve them as one source
    choice. The sampler itself already lives in 'staticOutcomes'.
    -}
    }

{- | One recursive ECTA and the size-stratified language it accepts.

The support is a @Mu@ node: a finite automaton standing for an unbounded
language. Members are reached through size classes rather than a
cardinality, and ranks are size-major, so bounding the language with
'boundedStatic' keeps every rank it already had.
-}
data Recursive a = Recursive
    { recursiveSupport :: Node Symbol
    {- ^ The ECTA support is demand-driven. Counting, mass, and sampling
    interpret the same recursive declaration without forcing this field.
    A support observer builds it once when needed.
    -}
    , recursiveIndex :: SizeIndex a
    , recursiveSampling :: SampleIndex a
    -- ^ A valid sampler at every size, tied through the recursive knot.
    , recursiveWeighted :: !Bool
    {- ^ Whether any reachable atom is non-uniform. This is read from the
    non-knot body, so bounded lowering can choose the sampler without forcing
    a Boolean fixpoint. 'False' permits uniform rank selection instead.
    -}
    , recursiveTerm :: Maybe (a -> Term Symbol)
    {- ^ How to read a member's ECTA term off its value, when the values are
    the accepted terms themselves. Every combinator drops it, because a
    mapped or combined value no longer stands for one term of the
    support.
    -}
    }

-- | View a finite language as one size-stratified recursive component.
recursiveFromStatic :: Static a -> Recursive a
recursiveFromStatic static =
    Recursive
        (staticSupport static)
        index
        sampling
        weighted
        Nothing
  where
    outcomes = staticOutcomes static
    index = sizeIndex $ outcomePlan outcomes
    (sampling, weighted)
        | staticAtomic static =
            ( atomicSampleIndex $ outcomeSampler outcomes
            , case outcomeUniformMass outcomes of
                Nothing -> True
                Just _ -> False
            )
        | otherwise = (uniformSampleIndex index, False)

{- | Bound a recursive language to its members of size at most the bound.

The result is an ordinary finite language with the same size-major ranks the
recursive language gives its members, so a rank replays through either. Size
classes retain their count-based probability. Finite choices closed with
'atomicStatic' retain their own distribution inside each class. The support
stays the recursive automaton — a size bound restricts the rank space, not the
set of terms the automaton accepts.

Members carry a retained t'Term' only when the values are the accepted terms
themselves, as they are for an automaton read with @fromECTA@; otherwise
inspection through 'outcomeSelect' reports
'CannotInspectRecursiveGenerator', while sampling, unranking, and shrinking
go through the value decoder and the plan.
-}
boundedStatic :: Int -> Recursive a -> Either ECTAGenError (Static a)
boundedStatic bound recursive
    | totalOutcomes <= 0 = Left EmptyGenerator
    | otherwise =
        Right $
            Static
                (recursiveSupport recursive)
                ( OutcomeIndex
                    totalOutcomes
                    uniformMass
                    select
                    selectValue
                    sampler
                    plan
                )
                False
  where
    select index = case recursiveTerm recursive of
        Nothing -> Left CannotInspectRecursiveGenerator
        Just readTerm -> do
            checkIndex totalOutcomes index
            let value = selectValue index
            pure $ Outcome (readTerm value) (1 / fromInteger totalOutcomes) value

    classes = sizeClasses bound $ recursiveIndex recursive
    plan = PlanSized classes
    totalOutcomes = sum [count | (_, count, _, _) <- classes]
    uniformMass
        | recursiveWeighted recursive = Nothing
        | otherwise = Just $ 1 / fromInteger totalOutcomes
    sampler
        | recursiveWeighted recursive =
            boundedSampler classes $ recursiveSampling recursive
        | otherwise = uniformSampler totalOutcomes selectValue

    selectValue = go classes
      where
        go [] _ =
            error
                "microecta-generator bug in Data.ECTA.Gen.Internal.boundedStatic: \
                \rank outside the bounded language"
        go ((_, count, decode, _) : rest) index
            | index < count = decode index
            | otherwise = go rest (index - count)

-- | One compact conditional generator and its mass in the whole distribution.
data KeyedBucket a = KeyedBucket
    { keyedBucketMass :: !Rational
    , keyedBucketStatic :: !(Static a)
    }

{- | One recursive language conditioned on a retained key.

The mass is unnormalized. Across all sibling keys it sums to the structural
member count at that size. This keeps language counts separate from sampler
probabilities while allowing keys to be merged without losing either.
-}
data KeyedRecursive a = KeyedRecursive
    { keyedRecursiveLanguage :: !(Recursive a)
    , keyedRecursiveMasses :: MassIndex
    , keyedRecursiveMassWeighted :: !Bool
    }

-- | A memoized unnormalized mass for every positive structural size.
newtype MassIndex = MassIndex [Rational]

-- | Read one size, returning zero outside the positive size classes.
massAtSize :: MassIndex -> Int -> Rational
massAtSize _ size | size < 1 = 0
massAtSize (MassIndex masses) size = masses !! (size - 1)

-- | Read one recursive group's mass at a size.
keyedRecursiveMassAtSize :: KeyedRecursive a -> Int -> Rational
keyedRecursiveMassAtSize recursive = massAtSize $ keyedRecursiveMasses recursive

-- | A language with no members at any size.
emptyMassIndex :: MassIndex
emptyMassIndex = MassIndex $ repeat 0

-- | Structural counts interpreted as unnormalized uniform mass.
countMassIndex :: SizeIndex a -> MassIndex
countMassIndex index =
    MassIndex $ map fromInteger (sizeClassCounts index) <> repeat 0

-- | One finite atom's complete mass at size one.
atomicMassIndex :: Rational -> MassIndex
atomicMassIndex mass = MassIndex $ mass : repeat 0

-- | Add alternative masses pointwise.
sumMassIndexes :: [MassIndex] -> MassIndex
sumMassIndexes indexes =
    MassIndex
        [ sum [massAtSize index size | index <- indexes]
        | size <- [1 ..]
        ]

-- | Turn every finite key bucket into one size-indexed recursive group.
keyedRecursiveFromBuckets :: Map.Map key (KeyedBucket a) -> Map.Map key (KeyedRecursive a)
keyedRecursiveFromBuckets buckets = fmap fromBucket buckets
  where
    totalCount =
        sum
            [ outcomeCardinality $ staticOutcomes $ keyedBucketStatic bucket
            | bucket <- Map.elems buckets
            ]

    fromBucket bucket =
        KeyedRecursive
            recursive
            masses
            massWeighted
      where
        static = keyedBucketStatic bucket
        recursive = recursiveFromStatic static
        bucketCount = outcomeCardinality $ staticOutcomes static
        masses
            | staticAtomic static =
                atomicMassIndex $ fromInteger totalCount * keyedBucketMass bucket
            | otherwise = countMassIndex $ recursiveIndex recursive
        massWeighted =
            staticAtomic static
                && fromInteger totalCount * keyedBucketMass bucket /= fromInteger bucketCount

-- | Put a complete recursive language under one key.
keyedRecursive :: Recursive a -> KeyedRecursive a
keyedRecursive recursive =
    KeyedRecursive
        recursive
        (countMassIndex $ recursiveIndex recursive)
        False

-- | Build one retained group from its outcomes, in rank order.
bucketFromOutcomes :: Bool -> [Outcome a] -> Either ECTAGenError (KeyedBucket a)
bucketFromOutcomes retainAtomic outcomes = do
    sampler <- sequenceSampler conditional
    pure $
        KeyedBucket bucketMass $
            Static
                bucketSupport
                ( OutcomeIndex
                    totalOutcomes
                    uniformMass
                    select
                    selectValue
                    sampler
                    (PlanSelect totalOutcomes selectValue)
                )
                retainAtomic
  where
    bucketMass = sum $ map outcomeMass outcomes
    conditional =
        Sequence.fromList
            [ outcome{outcomeMass = outcomeMass outcome / bucketMass}
            | outcome <- outcomes
            ]
    totalOutcomes = toInteger $ length outcomes
    uniformMass = commonValue $ Just . outcomeMass <$> toList conditional
    bucketSupport = Node [termEdge $ outcomeTerm outcome | outcome <- outcomes]
    termEdge (Term symbol children) = Edge symbol $ map singletonNode children

    select index = do
        checkIndex totalOutcomes index
        pure $ Sequence.index conditional $ fromInteger index

    selectValue = outcomeValue . Sequence.index conditional . fromInteger

{- | Group maps of every argument family, threaded through the operation type.

The group payload is a parameter: finite argument families carry a
@KeyedBucket@, recursive ones a t'Recursive', and everything that only walks
the chain is written once for both.
-}
data ArgMaps f (argKeys :: [Type]) operation result where
    MapsNil :: ArgMaps f '[] result result
    MapsCons ::
        (Ord argKey) =>
        Map.Map argKey (f arg) ->
        ArgMaps f argKeys operation result ->
        ArgMaps f (argKey ': argKeys) (arg -> operation) result

-- | The matched group of every argument family, in signature order.
data ArgChain f operation result where
    ChainNil :: ArgChain f result result
    ChainCons ::
        f arg ->
        ArgChain f operation result ->
        ArgChain f (arg -> operation) result

-- | The matched finite group of every argument family, in signature order.
type ArgStatics = ArgChain Static

-- | Find the argument group for every signature key.
lookupArgs ::
    Sig argKeys resultKey ->
    ArgMaps f argKeys operation result ->
    Maybe (ArgChain f operation result)
lookupArgs (key :-> _) (MapsCons groups MapsNil) = do
    group <- Map.lookup key groups
    Just $ ChainCons group ChainNil
lookupArgs (key :* rest) (MapsCons groups restMaps) = do
    group <- Map.lookup key groups
    chain <- lookupArgs rest restMaps
    Just $ ChainCons group chain

-- | Replace every group in a chain, keeping its shape.
mapChain :: (forall x. f x -> g x) -> ArgChain f operation result -> ArgChain g operation result
mapChain _ ChainNil = ChainNil
mapChain transform (ChainCons group rest) =
    ChainCons (transform group) (mapChain transform rest)

-- | The product of the matched groups' probability masses.
chainMass :: ArgChain KeyedBucket operation result -> Rational
chainMass ChainNil = 1
chainMass (ChainCons bucket rest) = keyedBucketMass bucket * chainMass rest

-- | Map the values of a static language.
mapStatic :: (a -> b) -> Static a -> Static b
mapStatic transform static =
    Static
        (staticSupport static)
        (mapOutcomeIndex transform $ staticOutcomes static)
        (staticAtomic static)

-- | Make every outcome of a finite language contribute one unit of size.
atomicStatic :: Static a -> Static a
atomicStatic static =
    static
        { staticOutcomes =
            outcomes
                { outcomePlan =
                    PlanSelect
                        (outcomeCardinality outcomes)
                        (outcomeValueAt outcomes)
                , outcomeSampler = retainedSampler
                }
        , staticAtomic = True
        }
  where
    outcomes = staticOutcomes static
    retainedSampler =
        case compiledWeightedSampler outcomes of
            Just sampler -> sampler
            Nothing -> outcomeSampler outcomes

-- | The one-outcome language of a single value.
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
            (\_ -> value)
            (uniformSampler 1 $ const value)
            (PlanSelect 1 $ const value)
        )
        False

-- | The language of one finite indexed source.
indexedStatic :: Indexed a -> Static a
indexedStatic indexed =
    Static
        (Node [Edge (indexedSymbol index) [] | index <- [0 .. totalOutcomes - 1]])
        ( OutcomeIndex
            totalOutcomes
            (Just $ 1 / fromInteger totalOutcomes)
            select
            (indexedSelect indexed)
            (uniformSampler totalOutcomes $ indexedSelect indexed)
            (PlanSelect totalOutcomes $ indexedSelect indexed)
        )
        False
  where
    totalOutcomes = indexedCardinality indexed
    select index = do
        checkIndex totalOutcomes index
        pure $
            Outcome
                (Term (indexedSymbol index) [])
                (1 / fromInteger totalOutcomes)
                (indexedSelect indexed index)

-- | The applicative product of a function language and an argument language.
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
            totalOutcomes
            ((*) <$> outcomeUniformMass functionOutcomes <*> outcomeUniformMass valueOutcomes)
            select
            selectValue
            ( productSampler
                valueCardinality
                (outcomeSampler functionOutcomes)
                (outcomeSampler valueOutcomes)
            )
            ( PlanAp
                valueCardinality
                (outcomePlan functionOutcomes)
                (outcomePlan valueOutcomes)
            )
        )
        False
  where
    functionOutcomes = staticOutcomes functions
    valueOutcomes = staticOutcomes values
    valueCardinality = outcomeCardinality valueOutcomes
    totalOutcomes = outcomeCardinality functionOutcomes * valueCardinality

    select index = do
        checkIndex totalOutcomes index
        let (functionIndex, valueIndex) = splitIndex index
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

    selectValue index =
        let (functionIndex, valueIndex) = splitIndex index
         in outcomeValueAt functionOutcomes functionIndex $
                outcomeValueAt valueOutcomes valueIndex

    splitIndex index = index `quotRem` valueCardinality

-- | Concatenate weighted alternatives with stable rank offsets.
frequencyStatic :: [(Integer, Static a)] -> Static a
frequencyStatic alternatives =
    Static
        ( Node
            [ Edge (frequencySymbol index) [staticSupport static]
            | (index, (_, static)) <- numbered
            ]
        )
        ( OutcomeIndex
            totalOutcomes
            uniformMass
            select
            selectValue
            sampler
            ( PlanChoice
                [ ( outcomeCardinality $ staticOutcomes static
                  , outcomePlan $ staticOutcomes static
                  )
                | (_, static) <- alternatives
                ]
            )
        )
        False
  where
    totalWeight = sum $ map fst alternatives
    numbered = zip [0 :: Int ..] alternatives
    rankedBranches =
        [ ( offset + outcomeCardinality (staticOutcomes static)
          , offset
          , branchIndex
          , weight
          , static
          )
        | (branchIndex, (offset, (weight, static))) <-
            zip [0 :: Int ..] $ offsetAlternatives alternatives
        ]
    totalOutcomes = sum [outcomeCardinality $ staticOutcomes static | (_, static) <- alternatives]
    uniformMass = commonValue $ map branchUniformMass alternatives
    sampler = case uniformMass of
        Just _ -> uniformSampler totalOutcomes selectValue
        Nothing -> frequencySampler alternatives

    branchUniformMass (weight, static) =
        (fromInteger weight / fromInteger totalWeight *)
            <$> outcomeUniformMass (staticOutcomes static)

    select index = do
        checkIndex totalOutcomes index
        let (branchIndex, weight, static, childIndex) = selectBranch index rankedBranches
        child <- outcomeSelect (staticOutcomes static) childIndex
        pure $
            Outcome
                (Term (frequencySymbol branchIndex) [outcomeTerm child])
                ( fromInteger weight
                    / fromInteger totalWeight
                    * outcomeMass child
                )
                (outcomeValue child)

    selectValue index =
        let (_, _, static, childIndex) = selectBranch index rankedBranches
         in outcomeValueAt (staticOutcomes static) childIndex

    selectBranch _ [] =
        error
            "microecta-generator bug in Data.ECTA.Gen.Internal.frequencyStatic: \
            \rank outside the alternatives"
    selectBranch index ((upperBound, offset, branchIndex, weight, static) : remaining)
        | index < upperBound = (branchIndex, weight, static, index - offset)
        | otherwise = selectBranch index remaining

-- | Join two languages on equal projected keys with one ECTA equality constraint.
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
    joinGroupedStatic left right $ map snd $ Map.toAscList shared

-- | Join two languages on a relation between their projected keys.
relateStatic ::
    (Ord leftKey, Ord rightKey) =>
    (left -> leftKey) ->
    (right -> rightKey) ->
    (leftKey -> rightKey -> Bool) ->
    Static left ->
    Static right ->
    Either ECTAGenError (Static (left, right))
relateStatic leftKey rightKey relation left right = do
    leftEntries <- keyedOutcomes leftKey left
    rightEntries <- keyedOutcomes rightKey right
    let leftGroups = groupOutcomes leftEntries
        rightGroups = groupOutcomes rightEntries
        related =
            [ (leftOutcomes, rightOutcomes)
            | (leftGroupKey, leftOutcomes) <- Map.toAscList leftGroups
            , (rightGroupKey, rightOutcomes) <- Map.toAscList rightGroups
            , relation leftGroupKey rightGroupKey
            ]
    joinGroupedStatic left right related

-- | Compile selected group products with one equality witness per product.
joinGroupedStatic ::
    Static left ->
    Static right ->
    [([Outcome left], [Outcome right])] ->
    Either ECTAGenError (Static (left, right))
joinGroupedStatic left right related =
    if null related
        then Left EmptyGenerator
        else
            let groups =
                    [ JoinGroup
                        keyIndex
                        (Sequence.fromList leftOutcomes)
                        (Sequence.fromList rightOutcomes)
                    | (keyIndex, (leftOutcomes, rightOutcomes)) <-
                        zip [0 :: Int ..] related
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
             in -- Every group came from two non-empty outcome buckets. Keep
                -- support reduction lazy; the outcome index already proves
                -- that the joined language is non-empty.
                (\outcomes -> Static joined outcomes False)
                    <$> joinOutcomeIndex left right groups

-- | Enumerate a language and pair every outcome with its projected key.
keyedOutcomes ::
    (value -> key) ->
    Static value ->
    Either ECTAGenError [(key, Outcome value)]
keyedOutcomes key static =
    map (\outcome -> (key $ outcomeValue outcome, outcome))
        <$> enumerateOutcomeIndex (staticOutcomes static)

-- | Group enumerated outcomes by key.
groupOutcomes :: (Ord key) => [(key, Outcome value)] -> Map.Map key [Outcome value]
groupOutcomes = Map.fromListWith (flip (<>)) . map (fmap pure)

-- | Count, select, and sample the matched groups of a two-way join.
joinOutcomeIndex ::
    Static left ->
    Static right ->
    [JoinGroup left right] ->
    Either ECTAGenError (OutcomeIndex (left, right))
joinOutcomeIndex left right groups = do
    rankSampler <- case uniformMass of
        Just _ -> pure $ uniformSampler totalOutcomes selectValue
        Nothing -> joinSampler groups
    pure $
        OutcomeIndex
            totalOutcomes
            uniformMass
            select
            selectValue
            rankSampler
            ( PlanChoice
                [ ( joinGroupCardinality group
                  , PlanAp
                        (toInteger $ Sequence.length $ joinGroupRight group)
                        (PlanMap (,) $ seqPlan $ joinGroupLeft group)
                        (seqPlan $ joinGroupRight group)
                  )
                | group <- groups
                ]
            )
  where
    totalOutcomes = sum $ map joinGroupCardinality groups
    uniformMass = case (outcomeUniformMass $ staticOutcomes left, outcomeUniformMass $ staticOutcomes right) of
        (Just _, Just _) -> Just $ 1 / fromInteger totalOutcomes
        _ -> Nothing
    totalMass = sum $ map joinGroupMass groups

    select index = do
        checkIndex totalOutcomes index
        let (group, leftOutcome, rightOutcome) = selectPair index
            keyTerm = Term (keySymbol $ joinGroupIndex group) []
            leftTerm =
                Term leftKeyedSymbol [keyTerm, outcomeTerm leftOutcome]
            rightTerm =
                Term rightKeyedSymbol [keyTerm, outcomeTerm rightOutcome]
        pure $
            Outcome
                (Term joinSymbol [leftTerm, rightTerm])
                ( outcomeMass leftOutcome
                    * outcomeMass rightOutcome
                    / totalMass
                )
                (outcomeValue leftOutcome, outcomeValue rightOutcome)

    selectValue index =
        let (_, leftOutcome, rightOutcome) = selectPair index
         in (outcomeValue leftOutcome, outcomeValue rightOutcome)

    selectPair index =
        let (group, groupIndex) = selectJoinGroup index groups
            rightCardinality = toInteger $ Sequence.length $ joinGroupRight group
            (leftIndex, rightIndex) = groupIndex `quotRem` rightCardinality
            leftOutcome = Sequence.index (joinGroupLeft group) $ fromInteger leftIndex
            rightOutcome = Sequence.index (joinGroupRight group) $ fromInteger rightIndex
         in (group, leftOutcome, rightOutcome)

-- | Number of pairs in one matched group.
joinGroupCardinality :: JoinGroup left right -> Integer
joinGroupCardinality group =
    toInteger (Sequence.length $ joinGroupLeft group)
        * toInteger (Sequence.length $ joinGroupRight group)

-- | Probability mass of one matched group.
joinGroupMass :: JoinGroup left right -> Rational
joinGroupMass group =
    sum (outcomeMass <$> joinGroupLeft group)
        * sum (outcomeMass <$> joinGroupRight group)

-- | Find the group holding a rank, with the rank rebased into it.
selectJoinGroup ::
    Integer ->
    [JoinGroup left right] ->
    (JoinGroup left right, Integer)
selectJoinGroup _ [] =
    error
        "microecta-generator bug in Data.ECTA.Gen.Internal.selectJoinGroup: \
        \rank outside the matched groups"
selectJoinGroup index (group : remaining)
    | index < groupSize = (group, index)
    | otherwise = selectJoinGroup (index - groupSize) remaining
  where
    groupSize = joinGroupCardinality group

-- | Sample a weighted two-way join, group by group.
joinSampler ::
    [JoinGroup left right] ->
    Either ECTAGenError (Sampler (left, right))
joinSampler groups = do
    weightedGroups <-
        integerOutcomes
            [ (joinGroupMass group, (offset, group))
            | (offset, group) <- offsetJoinGroups groups
            ]
    plans <- traverse branchPlan weightedGroups
    pure $
        Sampler
            ( frequencyGen
                [ ( weight
                  , liftA2
                        (,)
                        (runValueSampler leftSampler)
                        (runValueSampler rightSampler)
                  )
                | (weight, _, _, leftSampler, rightSampler) <- plans
                ]
            )
            ( frequencyGen
                [ ( weight
                  , liftA2
                        ( \(leftIndex, leftValue) (rightIndex, rightValue) ->
                            ( offset + leftIndex * rightCardinality + rightIndex
                            , (leftValue, rightValue)
                            )
                        )
                        (runRankSampler leftSampler)
                        (runRankSampler rightSampler)
                  )
                | (weight, offset, rightCardinality, leftSampler, rightSampler) <- plans
                ]
            )
  where
    branchPlan (weight, (offset, group)) = do
        leftSampler <- sequenceSampler $ joinGroupLeft group
        rightSampler <- sequenceSampler $ joinGroupRight group
        let rightCardinality = toInteger $ Sequence.length $ joinGroupRight group
        pure (weight, offset, rightCardinality, leftSampler, rightSampler)

-- | Pair every join group with its cumulative rank offset.
offsetJoinGroups :: [JoinGroup left right] -> [(Integer, JoinGroup left right)]
offsetJoinGroups = go 0
  where
    go _ [] = []
    go offset (group : remaining) =
        (offset, group) : go (offset + joinGroupCardinality group) remaining

-- | Merge weighted static languages into one group.
mergeBucketGroup :: [(Rational, Static a)] -> Either ECTAGenError (KeyedBucket a)
mergeBucketGroup alternatives = do
    weightedAlternatives <- integerOutcomes alternatives
    pure $
        KeyedBucket
            (sum $ map fst alternatives)
            (frequencyStatic weightedAlternatives)

-- | Merge weighted joined components into normalized result-key groups.
mergeComponentsByKey ::
    (Ord resultKey) =>
    [(resultKey, Rational, Static a)] ->
    Either ECTAGenError (Map.Map resultKey (KeyedBucket a))
mergeComponentsByKey [] = Left EmptyGenerator
mergeComponentsByKey components = do
    unnormalized <- traverse mergeBucketGroup grouped
    let totalAcceptedMass = sum $ keyedBucketMass <$> unnormalized
    pure $ fmap (normalizeBucket totalAcceptedMass) unnormalized
  where
    grouped =
        foldl'
            ( \groups (resultKey, mass, static) ->
                Map.insertWith
                    (flip (<>))
                    resultKey
                    [(mass, static)]
                    groups
            )
            Map.empty
            components

    normalizeBucket totalAcceptedMass bucket =
        bucket
            { keyedBucketMass =
                keyedBucketMass bucket / totalAcceptedMass
            }

-- | Join one operation group with its argument groups in one ECTA edge, with one equality constraint per argument.
joinNBucketStatic ::
    Int ->
    Static operation ->
    ArgStatics operation result ->
    Static result
joinNBucketStatic componentIndex operation arguments =
    -- This cannot fail: signature lookup supplies one non-empty bucket per
    -- component, so the outcome product proves non-emptiness without forcing
    -- support reduction.
    Static
        joined
        ( OutcomeIndex
            totalOutcomes
            uniformMass
            select
            selectValue
            rankSampler
            (chainPlan (outcomePlan operationOutcomes) arguments)
        )
        False
  where
    keyTerms =
        [ Term (argKeySymbol componentIndex position) []
        | position <- [0 .. chainLength arguments - 1]
        ]
    joined =
        reducePartially $
            joinNode componentIndex (staticSupport operation) (chainSupports arguments)
    operationOutcomes = staticOutcomes operation
    argumentsCardinality = chainCardinality arguments
    totalOutcomes = outcomeCardinality operationOutcomes * argumentsCardinality
    uniformMass =
        (*)
            <$> outcomeUniformMass operationOutcomes
            <*> chainUniformMass arguments
    rankSampler = chainSampler (outcomeSampler operationOutcomes) arguments
    decodeArguments = chainDecoder arguments

    select index = do
        checkIndex totalOutcomes index
        let (operationIndex, argumentIndex) = index `quotRem` argumentsCardinality
        operationOutcome <- outcomeSelect operationOutcomes operationIndex
        (argumentTerms, argumentsMass, value) <-
            selectChain (outcomeValue operationOutcome) arguments keyTerms argumentIndex
        let operationTerm =
                Term centerKeyedSymbol (keyTerms <> [outcomeTerm operationOutcome])
        pure $
            Outcome
                (Term joinNSymbol (operationTerm : argumentTerms))
                (outcomeMass operationOutcome * argumentsMass)
                value

    selectValue index =
        let (operationIndex, argumentIndex) = index `quotRem` argumentsCardinality
         in decodeArguments (outcomeValueAt operationOutcomes operationIndex) argumentIndex

{- | One joined edge: the operation group, one group per argument, and one
equality constraint per argument tying each argument to the operation's key
at that position.
-}
joinNode :: Int -> Node Symbol -> [Node Symbol] -> Node Symbol
joinNode componentIndex operationSupport argumentSupports =
    Node
        [ mkEdge
            joinNSymbol
            (operationNode : argumentNodes)
            ( mkEqConstraints
                [ [path [0, position], path [position + 1, 0]]
                | position <- [0 .. length argumentSupports - 1]
                ]
            )
        ]
  where
    keyNodes =
        [ singletonNode $ Term (argKeySymbol componentIndex position) []
        | position <- [0 .. length argumentSupports - 1]
        ]
    operationNode =
        Node [Edge centerKeyedSymbol (keyNodes <> [operationSupport])]
    argumentNodes =
        [ Node [Edge argKeyedSymbol [argKeyNode, argumentSupport]]
        | (argKeyNode, argumentSupport) <- zip keyNodes argumentSupports
        ]

{- | Restrict a recursive family to one key.

A recursive family is one @Mu@ whose edges carry their key as a first child,
so an occurrence at one key is the family under an edge holding that key's
label, with a constraint equating the two. The discrimination is the
automaton's own, which is what lets the whole family share one binder.
-}
restrictToKey :: Int -> Node Symbol -> Node Symbol
restrictToKey position family =
    Node
        [ mkEdge
            keyRestrictSymbol
            [keyNode position, family]
            (mkEqConstraints [[path [0], path [1, 0]]])
        ]

-- | One recursive family node: one key-labelled edge per key, in key order.
familyNode :: [(Int, Node Symbol)] -> Node Symbol
familyNode keyed =
    Node [Edge familySymbol [keyNode position, body] | (position, body) <- keyed]

{- | One joined component of a recursive keyed application.

Sizes and rank order match the finite join: the operation is one choice and
the arguments follow it left to right. The joined edge is not reduced, since
propagating constraints through a recursive node is not sound.
-}
recursiveJoin ::
    Int ->
    KeyedRecursive operation ->
    ArgChain KeyedRecursive operation result ->
    KeyedRecursive result
recursiveJoin componentIndex operation arguments =
    KeyedRecursive
        ( Recursive
            (joinNode componentIndex (recursiveSupport operationRecursive) (recursiveSupports arguments))
            joinedIndex
            joinedSampling
            joinedWeighted
            Nothing
        )
        joinedMasses
        joinedMassWeighted
  where
    operationRecursive = keyedRecursiveLanguage operation
    operationIndex = recursiveIndex operationRecursive
    joinedIndex = recursiveChainIndex operationIndex arguments
    joinedMasses =
        recursiveChainMass
            (keyedRecursiveMasses operation)
            arguments
    joinedSampling =
        recursiveChainSampling
            operationIndex
            (keyedRecursiveMasses operation)
            (recursiveSampling operationRecursive)
            arguments
    joinedWeighted =
        recursiveWeighted operationRecursive
            || recursiveChainWeighted arguments
            || joinedMassWeighted
    joinedMassWeighted =
        keyedRecursiveMassWeighted operation
            || recursiveChainMassWeighted arguments

-- | The support of every matched recursive argument group, in order.
recursiveSupports :: ArgChain KeyedRecursive operation result -> [Node Symbol]
recursiveSupports ChainNil = []
recursiveSupports (ChainCons recursive rest) =
    recursiveSupport (keyedRecursiveLanguage recursive) : recursiveSupports rest

-- | Consume the argument groups into the operation, left to right.
recursiveChainIndex ::
    SizeIndex operation ->
    ArgChain KeyedRecursive operation result ->
    SizeIndex result
recursiveChainIndex index ChainNil = index
recursiveChainIndex index (ChainCons recursive rest) =
    recursiveChainIndex
        (productIndex index $ recursiveIndex $ keyedRecursiveLanguage recursive)
        rest

-- | Multiply group masses through an applicative chain.
recursiveChainMass ::
    MassIndex ->
    ArgChain KeyedRecursive operation result ->
    MassIndex
recursiveChainMass mass ChainNil = mass
recursiveChainMass mass (ChainCons recursive rest) =
    recursiveChainMass
        (productMassIndex mass $ keyedRecursiveMasses recursive)
        rest

-- | Convolve two positive-size mass series.
productMassIndex :: MassIndex -> MassIndex -> MassIndex
productMassIndex left right =
    MassIndex
        [ sum
            [ massAtSize left leftSize * massAtSize right (size - leftSize)
            | leftSize <- [1 .. size - 1]
            ]
        | size <- [1 ..]
        ]

-- | Consume recursive argument samplers in the same product order as ranks.
recursiveChainSampling ::
    SizeIndex operation ->
    MassIndex ->
    SampleIndex operation ->
    ArgChain KeyedRecursive operation result ->
    SampleIndex result
recursiveChainSampling _ _ sampling ChainNil = sampling
recursiveChainSampling index mass sampling (ChainCons recursive rest) =
    recursiveChainSampling nextIndex nextMass nextSampling rest
  where
    recursive' = keyedRecursiveLanguage recursive
    nextIndex = productIndex index $ recursiveIndex recursive'
    nextMass = productMassIndex mass $ keyedRecursiveMasses recursive
    nextSampling =
        productMassSampleIndex
            index
            (massAtSize mass)
            sampling
            (recursiveIndex recursive')
            (keyedRecursiveMassAtSize recursive)
            (recursiveSampling recursive')

-- | Whether any recursive argument contains a weighted atomic choice.
recursiveChainWeighted :: ArgChain KeyedRecursive operation result -> Bool
recursiveChainWeighted ChainNil = False
recursiveChainWeighted (ChainCons recursive rest) =
    recursiveWeighted (keyedRecursiveLanguage recursive) || recursiveChainWeighted rest

-- | Whether a recursive argument's key mass differs from structural counts.
recursiveChainMassWeighted :: ArgChain KeyedRecursive operation result -> Bool
recursiveChainMassWeighted ChainNil = False
recursiveChainMassWeighted (ChainCons recursive rest) =
    keyedRecursiveMassWeighted recursive || recursiveChainMassWeighted rest

{- | Merge recursive groups sharing a key into one alternative each.

Alternatives keep their order, as they do in the finite merge, so ranks stay
deterministic.
-}
mergeRecursiveGroups :: [KeyedRecursive a] -> Maybe (KeyedRecursive a)
mergeRecursiveGroups [] = Nothing
mergeRecursiveGroups [only] = Just only
mergeRecursiveGroups alternatives =
    Just $
        KeyedRecursive
            ( Recursive
                ( Node
                    [ Edge (frequencySymbol branchIndex) [recursiveSupport $ keyedRecursiveLanguage alternative]
                    | (branchIndex, alternative) <- zip [0 ..] alternatives
                    ]
                )
                index
                (choiceMassSampleIndex indexedSamplers)
                weighted
                Nothing
            )
            masses
            massWeighted
  where
    index = choiceIndex $ map (recursiveIndex . keyedRecursiveLanguage) alternatives
    masses = sumMassIndexes $ map keyedRecursiveMasses alternatives
    massWeighted = any keyedRecursiveMassWeighted alternatives
    weighted =
        massWeighted
            || any (recursiveWeighted . keyedRecursiveLanguage) alternatives
    indexedSamplers =
        [ ( recursiveIndex $ keyedRecursiveLanguage alternative
          , keyedRecursiveMassAtSize alternative
          , recursiveSampling $ keyedRecursiveLanguage alternative
          )
        | alternative <- alternatives
        ]

-- | Number of arguments in the chain.
chainLength :: ArgStatics operation result -> Int
chainLength ChainNil = 0
chainLength (ChainCons _ rest) = 1 + chainLength rest

-- | ECTA support of every argument group, in order.
chainSupports :: ArgStatics operation result -> [Node Symbol]
chainSupports ChainNil = []
chainSupports (ChainCons static rest) = staticSupport static : chainSupports rest

-- | Product of the argument group cardinalities.
chainCardinality :: ArgStatics operation result -> Integer
chainCardinality ChainNil = 1
chainCardinality (ChainCons static rest) =
    outcomeCardinality (staticOutcomes static) * chainCardinality rest

-- | Product of the argument uniform masses, when all are uniform.
chainUniformMass :: ArgStatics operation result -> Maybe Rational
chainUniformMass ChainNil = Just 1
chainUniformMass (ChainCons static rest) =
    (*)
        <$> outcomeUniformMass (staticOutcomes static)
        <*> chainUniformMass rest

{- | Compose the mixed-radix rank sampler as a left 'productSampler' fold.

The composed rank is @operationRank@ most significant, then argument ranks
left to right, matching 'chainDecoder'.
-}
chainSampler :: Sampler operation -> ArgStatics operation result -> Sampler result
chainSampler sampler ChainNil = sampler
chainSampler sampler (ChainCons static rest) =
    chainSampler
        ( productSampler
            (outcomeCardinality $ staticOutcomes static)
            sampler
            (outcomeSampler $ staticOutcomes static)
        )
        rest

-- | Mirror 'chainSampler' as plan structure, one product per argument.
chainPlan :: Plan operation -> ArgStatics operation result -> Plan result
chainPlan plan ChainNil = plan
chainPlan plan (ChainCons static rest) =
    chainPlan
        ( PlanAp
            (outcomeCardinality $ staticOutcomes static)
            plan
            (outcomePlan $ staticOutcomes static)
        )
        rest

-- | Build a rank decoder once, capturing every suffix cardinality.
chainDecoder :: ArgStatics operation result -> operation -> Integer -> result
chainDecoder ChainNil = \value _ -> value
chainDecoder (ChainCons static ChainNil) =
    let valueAt = outcomeValueAt $ staticOutcomes static
     in \operation index -> operation $ valueAt index
chainDecoder (ChainCons first (ChainCons second ChainNil)) =
    let firstValueAt = outcomeValueAt $ staticOutcomes first
        secondOutcomes = staticOutcomes second
        secondCardinality = outcomeCardinality secondOutcomes
        secondValueAt = outcomeValueAt secondOutcomes
     in \operation index ->
            let (firstIndex, secondIndex) = index `quotRem` secondCardinality
             in operation (firstValueAt firstIndex) (secondValueAt secondIndex)
chainDecoder (ChainCons static rest) =
    let decodeRest = chainDecoder rest
        suffixCardinality = chainCardinality rest
        valueAt = outcomeValueAt $ staticOutcomes static
     in \partial index ->
            let (here, there) = index `quotRem` suffixCardinality
             in decodeRest (partial $ valueAt here) there

-- | Select one outcome per argument, threading terms, mass, and the applied value.
selectChain ::
    operation ->
    ArgStatics operation result ->
    [Term Symbol] ->
    Integer ->
    Either ECTAGenError ([Term Symbol], Rational, result)
selectChain value ChainNil _ _ = Right ([], 1, value)
selectChain partial (ChainCons static rest) (keyTerm : keyTerms) index = do
    let (here, there) = index `quotRem` chainCardinality rest
    outcome <- outcomeSelect (staticOutcomes static) here
    (terms, mass, value) <- selectChain (partial $ outcomeValue outcome) rest keyTerms there
    pure
        ( Term argKeyedSymbol [keyTerm, outcomeTerm outcome] : terms
        , outcomeMass outcome * mass
        , value
        )
selectChain _ (ChainCons _ _) [] _ =
    error
        "microecta-generator bug in Data.ECTA.Gen.Internal.selectChain: \
        \fewer key terms than arguments"

-- | Sample one outcome sequence by its masses.
sequenceSampler :: Seq (Outcome a) -> Either ECTAGenError (Sampler a)
sequenceSampler outcomes
    | Just _ <- commonValue $ Just . outcomeMass <$> toList outcomes =
        pure $ uniformSampler totalOutcomes selectValue
    | otherwise = do
        weightedRanks <-
            integerOutcomes
                [ (outcomeMass outcome, (index, outcomeValue outcome))
                | (index, outcome) <- zip [0 ..] $ toList outcomes
                ]
        pure $
            Sampler
                (frequencyGen [(weight, pure value) | (weight, (_, value)) <- weightedRanks])
                (frequencyGen [(weight, pure rankedValue) | (weight, rankedValue) <- weightedRanks])
  where
    totalOutcomes = toInteger $ Sequence.length outcomes
    selectValue = outcomeValue . Sequence.index outcomes . fromInteger

-- | Singleton key node labelling one matched group.
keyNode :: Int -> Node Symbol
keyNode index = Node [Edge (keySymbol index) []]

-- | The ECTA node accepting exactly one term.
singletonNode :: Term Symbol -> Node Symbol
singletonNode (Term symbol children) =
    Node [Edge symbol $ map singletonNode children]

-- | Enumerate a language as normalized mass and value pairs.
compileOutcomes :: Static a -> Either ECTAGenError [(Rational, a)]
compileOutcomes static = do
    outcomes <- enumerateOutcomeIndex $ staticOutcomes static
    normalize [(outcomeMass outcome, outcomeValue outcome) | outcome <- outcomes]

-- | Sample one value; uniform languages go through the compiled decoder.
sampleStatic ::
    (GenBackend gen) =>
    Static a ->
    gen (Either ECTAGenError a)
sampleStatic static
    | Just _ <- outcomeUniformMass outcomes =
        case compiledDecoder outcomes of
            SmallDecoder bound decode -> Right . decode <$> selectInt bound
            LargeDecoder bound decode -> Right . decode <$> selectInteger bound
    | otherwise =
        Right <$> runValueSampler (outcomeSampler outcomes)
  where
    outcomes = staticOutcomes static

-- | Sample one value together with its replay rank.
sampleStaticWithRank ::
    (GenBackend gen) =>
    Static a ->
    gen (Either ECTAGenError (Integer, a))
sampleStaticWithRank static
    | Just _ <- outcomeUniformMass outcomes =
        case compiledDecoder outcomes of
            SmallDecoder bound decode ->
                (\index -> Right (toInteger index, decode index)) <$> selectInt bound
            LargeDecoder bound decode ->
                (\index -> Right (index, decode index)) <$> selectInteger bound
    | otherwise =
        Right <$> runRankSampler (outcomeSampler outcomes)
  where
    outcomes = staticOutcomes static

-- | Compile the retained plan once, at lowering time.
compiledDecoder :: OutcomeIndex a -> RankDecoder a
compiledDecoder outcomes =
    compilePlan (outcomeCardinality outcomes) (outcomePlan outcomes)

-- | Largest non-uniform language compiled to one exact ticket selection.
weightedCompilationBound :: Integer
weightedCompilationBound = 32768

-- | Compile a small non-uniform language without aggregating equal values.
compiledWeightedSampler :: OutcomeIndex a -> Maybe (Sampler a)
compiledWeightedSampler outcomes
    | Just _ <- outcomeUniformMass outcomes = Nothing
    | outcomeCardinality outcomes > weightedCompilationBound = Nothing
    | otherwise = do
        enumerated <- either (const Nothing) Just $ enumerateOutcomeIndex outcomes
        weighted <-
            either (const Nothing) Just $
                integerOutcomes
                    [ (outcomeMass outcome, (rank, outcomeValue outcome))
                    | (rank, outcome) <- zip [0 ..] enumerated
                    ]
        (bound, decode) <- compileWeighted weighted
        pure $
            Sampler
                (snd . decode <$> selectInt bound)
                (decode <$> selectInt bound)

-- | Sample weighted alternatives with rank offsets.
frequencySampler :: [(Integer, Static a)] -> Sampler a
frequencySampler alternatives =
    Sampler
        ( frequencyGen
            [ (weight, runValueSampler $ outcomeSampler $ staticOutcomes static)
            | (weight, static) <- alternatives
            ]
        )
        ( frequencyGen
            [ ( weight
              , (\(rank, value) -> (offset + rank, value))
                    <$> runRankSampler (outcomeSampler $ staticOutcomes static)
              )
            | (offset, (weight, static)) <- offsetAlternatives alternatives
            ]
        )

-- | Pair every alternative with its cumulative rank offset.
offsetAlternatives :: [(Integer, Static a)] -> [(Integer, (Integer, Static a))]
offsetAlternatives = go 0
  where
    go _ [] = []
    go offset (alternative@(_, static) : remaining) =
        (offset, alternative)
            : go
                (offset + outcomeCardinality (staticOutcomes static))
                remaining

-- | Map the values of an outcome index.
mapOutcomeIndex :: (a -> b) -> OutcomeIndex a -> OutcomeIndex b
mapOutcomeIndex transform outcomes =
    OutcomeIndex
        (outcomeCardinality outcomes)
        (outcomeUniformMass outcomes)
        (\index -> mapOutcome transform <$> outcomeSelect outcomes index)
        (transform . outcomeValueAt outcomes)
        (mapSampler transform $ outcomeSampler outcomes)
        (PlanMap transform $ outcomePlan outcomes)

-- | Map the value of one outcome.
mapOutcome :: (a -> b) -> Outcome a -> Outcome b
mapOutcome transform outcome =
    Outcome
        (outcomeTerm outcome)
        (outcomeMass outcome)
        (transform $ outcomeValue outcome)

-- | Select every outcome in rank order.
enumerateOutcomeIndex :: OutcomeIndex a -> Either ECTAGenError [Outcome a]
enumerateOutcomeIndex outcomes =
    traverse
        (outcomeSelect outcomes)
        [0 .. outcomeCardinality outcomes - 1]

-- | The value shared by every entry, if any.
commonValue :: (Eq a) => [Maybe a] -> Maybe a
commonValue [] = Nothing
commonValue (Just value : remaining)
    | all (== Just value) remaining = Just value
commonValue _ = Nothing

-- | Reject a rank outside the language.
checkIndex :: Integer -> Integer -> Either ECTAGenError ()
checkIndex totalOutcomes index
    | index < 0 = Left $ NegativeRank index
    | index >= totalOutcomes =
        Left $ SelectionOutOfRange index totalOutcomes
    | otherwise = Right ()

-- | Scale masses so they sum to one.
normalize :: [(Rational, a)] -> Either ECTAGenError [(Rational, a)]
normalize [] = Left EmptyGenerator
normalize outcomes =
    let total = sum $ map fst outcomes
     in if total <= 0
            then Left EmptyGenerator
            else Right [(mass / total, value) | (mass, value) <- outcomes]

{- | Convert rational masses to the smallest equivalent integer weights,
rejecting a set that cannot be sampled.

This is 'integerMasses' with its positivity precondition checked: a language
with no outcomes, or one whose masses are not all positive, has nothing to
sample.
-}
integerOutcomes ::
    [(Rational, a)] ->
    Either ECTAGenError [(Integer, a)]
integerOutcomes [] = Left EmptyGenerator
integerOutcomes outcomes
    | any ((<= 0) . fst) outcomes = Left EmptyGenerator
    | otherwise = Right $ integerMasses outcomes

{- | Symbols labelling the ECTA structure this module builds. They are
namespaced so generated supports cannot collide with user symbols.
-}
pureSymbol, applySymbol, joinSymbol, joinNSymbol, centerKeyedSymbol, leftKeyedSymbol, rightKeyedSymbol, argKeyedSymbol, familySymbol, keyRestrictSymbol :: Symbol
pureSymbol = "$ecta-gen/pure"
applySymbol = "$ecta-gen/apply"
joinSymbol = "$ecta-gen/join"
centerKeyedSymbol = "$ecta-gen/center-keyed"
leftKeyedSymbol = "$ecta-gen/left-keyed"
rightKeyedSymbol = "$ecta-gen/right-keyed"
joinNSymbol = "$ecta-gen/join-n"
argKeyedSymbol = "$ecta-gen/arg-keyed"
familySymbol = "$ecta-gen/family"
keyRestrictSymbol = "$ecta-gen/at-key"

-- | Leaf symbol carrying one stable source index.
indexedSymbol :: Integer -> Symbol
indexedSymbol index = Symbol $ Text.pack $ "$ecta-gen/index/" <> show index

-- | Branch symbol carrying one alternative index.
frequencySymbol :: Int -> Symbol
frequencySymbol index = Symbol $ Text.pack $ "$ecta-gen/frequency/" <> show index

-- | Key symbol shared by one matched group.
keySymbol :: Int -> Symbol
keySymbol index = Symbol $ Text.pack $ "$ecta-gen/key/" <> show index

-- | Key symbol for one argument position of one joined component.
argKeySymbol :: Int -> Int -> Symbol
argKeySymbol componentIndex position =
    Symbol $
        Text.pack $
            "$ecta-gen/key/" <> show componentIndex <> "/" <> show position
