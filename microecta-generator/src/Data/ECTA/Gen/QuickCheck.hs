{-# LANGUAGE DerivingStrategies #-}

{- | QuickCheck integration for indexed ECTA generators.

A generator knows exactly how many values it has, and can be addressed by
rank:

>>> cardinality (elements [1 .. 4 :: Int])
Right 4
>>> unrank (elements "abcd") 2
Right 'c'

Applicative composition multiplies the counts without building the product:

>>> let paired = liftA2 (,) (elements [0, 1 :: Int]) (elements "xy")
>>> cardinality paired
Right 4
>>> map (unrank paired) [0 .. 3]
[Right (0,'x'),Right (0,'y'),Right (1,'x'),Right (1,'y')]

'match' keeps exactly the pairs whose projected keys agree, and counts them
without testing the product:

>>> let matched = match (even :==: even) (elements [0 .. 3 :: Int]) (elements [10 .. 13 :: Int])
>>> cardinality matched
Right 8
>>> unrank matched 0
Right (1,11)

Weights are exact rather than sampled:

>>> pmf (frequency [(3, elements [0 :: Int]), (1, elements [1])])
Right [(0,3 % 4),(1,1 % 4)]

A recursive language has no cardinality, but every size class is counted and
ranks are size-major:

>>> let tree = recur (\self -> oneof [elements [[] :: [Int]], liftA2 (:) (elements [0, 1]) self])
>>> map (countAtSize tree) [1 .. 4]
[Right 1,Right 2,Right 4,Right 8]
>>> unrank tree 3
Right [0,0]
-}
module Data.ECTA.Gen.QuickCheck (
    -- * Generators
    ECTAGen,
    Grouped,
    QuickCheckBackend,
    ECTAGenError (..),
    explain,

    -- * Sources
    Indexed (..),
    fromIndexed,
    elements,
    pool,
    freeze,
    fromECTA,
    fromGen,

    -- * Composing
    NodeLayer (..),
    node,
    frequency,
    oneof,
    uniformly,
    On (..),
    match,
    relate,
    relateM,

    -- * The grouped layer
    Sig (..),
    sigResult,
    Args (..),
    keyed,
    groupBy,
    regroupBy,
    mapWithKey,
    atKey,
    apply,
    frequencies,
    oneofGrouped,
    uniformlyGrouped,
    ungroup,
    relateGroupsM,
    relateN,
    filterGroupsM,

    -- * Recursion
    atomic,
    recur,
    recurGrouped,
    upToSize,

    -- * Inspection
    support,
    cardinality,
    sizes,
    countsAtSize,
    massesAtSize,
    countAtSize,
    minimumSize,
    countBy,
    pmf,
    pmfAtSize,
    smallest,
    unrank,
    sizeOfRank,
    smallerMembers,
    shrinkRank,

    -- * Sampling and properties
    toGen,
    toGenWithRank,
    toGenEither,
    toGenWithRankEither,
    forAll,
    forAllWithLimit,
    smallerMemberLimit,
    sized,

    -- * Qualified do-notation
    module Data.ECTA.Gen.Do,
) where

import Data.List (mapAccumL, sortOn)
import Data.Map.Strict (Map)
import Data.Ord (Down (..))
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)

import Data.ECTA (Node)
import Data.ECTA.Gen (
    Args (..),
    ECTAGenError (..),
    Indexed (..),
    NodeLayer (..),
    On (..),
    Sig (..),
    explain,
    node,
    sigResult,
 )
import qualified Data.ECTA.Gen as ECTA
import Data.ECTA.Gen.Do
import Data.ECTA.Term (Symbol, Term)

{- | QuickCheck as the sampling backend.

The wrapper exists to avoid an orphan 'ECTA.GenBackend' instance for 'QC.Gen'.
It is abstract, but it is exported because it appears in the type of an 'Args'
chain, which a caller may want to write a signature for.
-}
newtype QuickCheckBackend a = QuickCheckBackend (QC.Gen a)
    deriving newtype (Functor, Applicative)

instance ECTA.GenBackend QuickCheckBackend where
    selectInteger bound =
        QuickCheckBackend $ QC.chooseInteger (0, bound - 1)

    selectInt bound =
        QuickCheckBackend $ QC.chooseInt (0, bound - 1)

    frequencyGen alternatives =
        -- Ranked branches already carry their offsets, so sampling can put
        -- likely branches first without changing rank order.
        let ordered = sortOn (Down . fst) alternatives
            (total, cumulative) = mapAccumL accumulateWeight 0 ordered
         in QuickCheckBackend $ do
                selected <-
                    if total <= toInteger (maxBound :: Int)
                        then toInteger <$> QC.chooseInt (0, fromInteger total - 1)
                        else QC.chooseInteger (0, total - 1)
                pick selected cumulative
      where
        accumulateWeight total (weight, generated) =
            let upperBound = total + weight
             in (upperBound, (upperBound, generated))

        pick _ [] =
            error
                "microecta-generator bug in Data.ECTA.Gen.QuickCheck.frequencyGen: \
                \no alternative to pick"
        pick selected ((upperBound, QuickCheckBackend generated) : remaining)
            | selected < upperBound = generated
            | otherwise = pick selected remaining

    filterGen predicate (QuickCheckBackend generated) =
        QuickCheckBackend $ generated `QC.suchThat` predicate

-- | An indexed ECTA generator with QuickCheck as its opaque backend.
type ECTAGen = ECTA.ECTAGen QuickCheckBackend

-- | An ECTA generator classified by a projected key used to match ECTA paths.
type Grouped key = ECTA.Grouped QuickCheckBackend key

-- | Compile an effectful relation once per live projected key pair.
relateM ::
    (Ord leftKey, Ord rightKey) =>
    (left -> leftKey) ->
    (right -> rightKey) ->
    (leftKey -> rightKey -> IO (Either relationError Bool)) ->
    ECTAGen left ->
    ECTAGen right ->
    IO (Either relationError (ECTAGen (left, right)))
relateM = ECTA.relateM

-- | Compile an effectful relation over two already-grouped languages.
relateGroupsM ::
    (Ord resultKey) =>
    (leftKey -> rightKey -> IO (Either relationError Bool)) ->
    (leftKey -> rightKey -> resultKey) ->
    Grouped leftKey left ->
    Grouped rightKey right ->
    IO (Either relationError (Grouped resultKey (left, right)))
relateGroupsM = ECTA.relateGroupsM

-- | Compile one relation over a homogeneous list of grouped arguments.
relateN ::
    (Ord key) =>
    ([key] -> IO (Either relationError Bool)) ->
    [Grouped key a] ->
    IO (Either relationError (Grouped [key] [a]))
relateN = ECTA.relateN

-- | Select already-grouped languages with one effectful decision per key.
filterGroupsM ::
    (Ord key) =>
    (key -> IO (Either relationError Bool)) ->
    Grouped key a ->
    IO (Either relationError (Grouped key a))
filterGroupsM = ECTA.filterGroupsM

-- | Lift one finite indexed source into transparent ECTA structure.
fromIndexed :: Indexed a -> ECTAGen a
fromIndexed = ECTA.fromIndexed

-- | Choose uniformly from a finite non-empty list.
elements :: [a] -> ECTAGen a
elements = ECTA.elements

{- | Sample a finite pool from an ordinary QuickCheck generator.

The outer 'QC.Gen' draws the pool once. The resulting 'ECTAGen' is finite and
transparent, so it supports exact inspection, matching, relations, replay, and
ECTA-aware shrinking. Repeated draws remain repeated ranks and retain the
native generator's empirical weight. A non-positive pool size produces an
empty generator.
-}
pool :: Int -> QC.Gen a -> QC.Gen (ECTAGen a)
pool sampleCount native =
    elements <$> QC.vectorOf (max 0 sampleCount) native

{- | 'pool' with the draws fixed by a seed.

The native generator is run once, at QuickCheck size 30 (the default of
'QC.generate'), so the result is an ordinary transparent generator: it can be
weighted by 'uniformly', keyed, joined, replayed, and shrunk, and its ranks are
the same in every run under the same seed. That is the trade against 'pool',
which draws afresh each time its outer 'QC.Gen' runs. Use 'QC.resize' on the
native generator for another size.
-}
freeze :: Int -> Int -> QC.Gen a -> ECTAGen a
freeze seed sampleCount native =
    unGen (pool sampleCount native) (mkQCGen seed) 30

{- | Read an ECTA as a generator of the terms it accepts.

The automaton is the support and members are counted by size, so this draws
uniformly from the terms of at most the current QuickCheck size. Automata
whose edges carry equality constraints are rejected.
-}
fromECTA :: Node Symbol -> ECTAGen (Term Symbol)
fromECTA = ECTA.fromECTA

{- | Treat every member of a finite generator as one atomic source choice.

An already finite generator keeps its support, cardinality, ranks, values,
and distribution. That distribution is retained when the atom is used inside
'recur' or 'recurGrouped'. Put 'atomic' around the complete finite choice that
enters recursion; a finite composition outside the boundary is a new choice
and needs its own boundary. An acyclic automaton read with 'fromECTA' closes
its whole finite language without enumerating it or taking an inner
QuickCheck-size prefix. Bound a recursive language with 'upToSize' before
making it atomic, /outside/ the recursive definition: applying either to the
'recur' argument is rejected with 'BoundedRecursiveOccurrence'.
-}
atomic :: ECTAGen a -> ECTAGen a
atomic = ECTA.atomic

{- | Build a recursive generator from its own language.

The argument receives the generator being defined, so a language can refer
to itself. 'toGen' and 'forAll' bound it by QuickCheck's size parameter;
'upToSize' bounds it explicitly. Recursive structure follows the counted size
classes. Finite choices closed with 'atomic' retain their distribution inside
each class. Recursion must be guarded by '<*>', and alternatives around a
recursive occurrence must carry equal weights, which is what 'oneof' gives
without asking for them. A guarded cycle still needs a finite base member;
otherwise it is an empty generator.

The self-reference has to go through this combinator: a generator that
names itself directly is an infinite Haskell value and hangs while it is
being built. 'upToSize' and 'atomic' cannot be applied to the argument, or to
anything built from it; bound the finished language from outside instead.

The guard check is per definition, so inside a nested 'recur' an occurrence of
the /outer/ language must also sit under an application within the inner body.

'pure' is one source choice, so @pure f '<*>' x@ has one more choice than
@f '<$>' x@, and therefore different sizes and ranks; @pure f '<*>' self@
counts as guarded where @f '<$>' self@ does not.
-}
recur :: (ECTAGen a -> ECTAGen a) -> ECTAGen a
recur = ECTA.recur

{- | Build a recursive grouped family from its own languages.

The key set is solved first, then the languages are tied over it. All keys
share one @Mu@ node whose cycle carries the keyed joins' equality
constraints; 'ungroup' and 'atKey' are the exits into an ordinary recursive
generator. Recursion must be guarded by 'apply', and 'frequencies'
alternatives around a recursive occurrence must carry equal weights.
The generated language may be infinite, but it must use only finitely many
distinct keys. 'recurGrouped' discovers those keys before tying the recursive
languages, so a definition that creates a fresh key on every pass cannot
finish construction.
-}
recurGrouped :: (Ord key) => (Grouped key a -> Grouped key a) -> Grouped key a
recurGrouped = ECTA.recurGrouped

{- | Bound a generator to the members of size at most the given bound.

Size is the number of source choices in a member. Ranks are unchanged, so a
counterexample found under one bound replays under any larger bound.
-}
upToSize :: Int -> ECTAGen a -> ECTAGen a
upToSize = ECTA.upToSize

{- | Declare that every member of an inspectable generator has one key.

This preserves finite or recursive support without enumerating members.
Opaque generators cannot enter the grouped layer.
-}
keyed :: key -> ECTAGen a -> Grouped key a
keyed = ECTA.keyed

{- | Classify a transparent generator's outcomes by a projected key.

Building the groups enumerates the generator's outcomes once. Opaque
generators cannot be grouped.
-}
groupBy :: (Ord key) => (a -> key) -> ECTAGen a -> Grouped key a
groupBy = ECTA.groupBy

-- | Reclassify groups without enumerating their values.
regroupBy :: (Ord newKey) => (oldKey -> newKey) -> Grouped oldKey a -> Grouped newKey a
regroupBy = ECTA.regroupBy

-- | Map group values with access to their retained key.
mapWithKey :: (key -> a -> b) -> Grouped key a -> Grouped key b
mapWithKey = ECTA.mapWithKey

-- | Return the exact cardinality of each retained group.
sizes :: Grouped key a -> Either ECTAGenError (Map key Integer)
sizes = ECTA.sizes

{- | Return exact retained-key counts at one structural size.

Counts describe the language, not the sampling distribution.
-}
countsAtSize :: Grouped key a -> Int -> Either ECTAGenError (Map key Integer)
countsAtSize = ECTA.countsAtSize

-- | Return the exact retained-key sampling distribution at one structural size.
massesAtSize :: Grouped key a -> Int -> Either ECTAGenError (Map key Rational)
massesAtSize = ECTA.massesAtSize

-- | Select one retained group as an ordinary conditional generator.
atKey :: (Ord key) => key -> Grouped key a -> ECTAGen a
atKey = ECTA.atKey

{- | Apply a generated operation of any arity to one argument family per
signature component.

The operation family must already hold functions consuming the 'Args' chain
left to right; use 'fmap' to attach a compiling function.
-}
apply ::
    (Ord resultKey) =>
    Grouped (Sig argKeys resultKey) operation ->
    Args QuickCheckBackend argKeys operation result ->
    Grouped resultKey result
apply = ECTA.apply

{- | Choose among grouped generators with positive relative weights,
group by group.
-}
frequencies :: (Ord key) => [(Integer, Grouped key a)] -> Grouped key a
frequencies = ECTA.frequencies

{- | Choose uniformly among grouped generators, group by group.

'frequencies' with equal weights, which is the only shape a recursive
family admits.
-}
oneofGrouped :: (Ord key) => [Grouped key a] -> Grouped key a
oneofGrouped = ECTA.oneofGrouped

{- | Choose among grouped generators so that every member of the combined
language is equally likely: finite alternatives are combined in proportion to
their exact cardinalities, and alternatives around a recursive family with
equal weights.
-}
uniformlyGrouped :: (Ord key) => [Grouped key a] -> Grouped key a
uniformlyGrouped = ECTA.uniformlyGrouped

-- | Merge all retained groups while preserving their probability masses.
ungroup :: Grouped key a -> ECTAGen a
ungroup = ECTA.ungroup

-- | Choose one generator with the supplied positive relative weight.
frequency :: [(Integer, ECTAGen a)] -> ECTAGen a
frequency = ECTA.frequency

{- | Choose uniformly among generators.

Every alternative is equally likely, whatever the size of its language. In
a recursive definition this is the shape to reach for: weights around a
recursive occurrence are rejected.
-}
oneof :: [ECTAGen a] -> ECTAGen a
oneof = ECTA.oneof

{- | Choose among generators so that every member of the combined language is
equally likely: finite alternatives are combined in proportion to their
cardinalities, and alternatives around a recursive one with equal weights.
-}
uniformly :: [ECTAGen a] -> ECTAGen a
uniformly = ECTA.uniformly

-- | Generate two values whose projected keys agree.
match ::
    On left right ->
    ECTAGen left ->
    ECTAGen right ->
    ECTAGen (left, right)
match = ECTA.match

{- | Generate two values whose projected keys satisfy a relation.

Finite transparent inputs are conditioned without rejection. An opaque input
uses QuickCheck rejection filtering.
-}
relate ::
    (Ord leftKey, Ord rightKey) =>
    (left -> leftKey) ->
    (right -> rightKey) ->
    (leftKey -> rightKey -> Bool) ->
    ECTAGen left ->
    ECTAGen right ->
    ECTAGen (left, right)
relate = ECTA.relate

-- | Return the ECTA support of an inspectable generator.
support :: ECTAGen a -> Either ECTAGenError (Node Symbol)
support = ECTA.support

-- | Return the exact number of ranks in a transparent generator.
cardinality :: ECTAGen a -> Either ECTAGenError Integer
cardinality = ECTA.cardinality

-- | The number of members of one size, for any inspectable generator.
countAtSize :: ECTAGen a -> Int -> Either ECTAGenError Integer
countAtSize = ECTA.countAtSize

-- | The smallest structural size in an inspectable language.
minimumSize :: ECTAGen a -> Either ECTAGenError (Maybe Int)
minimumSize = ECTA.minimumSize

-- | Return the first member in structural size and rank order, or 'Nothing' if empty.
smallest :: ECTAGen a -> Either ECTAGenError (Maybe a)
smallest = ECTA.smallest

-- | Decode one stable rank from an inspectable generator.
unrank :: ECTAGen a -> Integer -> Either ECTAGenError a
unrank = ECTA.unrank

-- | Structural shrink candidates for one rank of a transparent generator.
shrinkRank :: ECTAGen a -> Integer -> [Integer]
shrinkRank = ECTA.shrinkRank

{- | Every member of strictly smaller size than the given rank's member, in
size order, as replayable rank and value. The stream is lazy; cap it before
use.
-}
smallerMembers :: ECTAGen a -> Integer -> [(Integer, a)]
smallerMembers = ECTA.smallerMembers

-- | The number of source choices in the member a rank decodes to.
sizeOfRank :: ECTAGen a -> Integer -> Maybe Int
sizeOfRank = ECTA.sizeOfRank

-- | Count ranked outcomes by a projected key.
countBy :: (Ord key) => (a -> key) -> ECTAGen a -> Either ECTAGenError (Map key Integer)
countBy = ECTA.countBy

-- | Aggregate the exact PMF of a finite transparent generator.
pmf :: (Ord a) => ECTAGen a -> Either ECTAGenError [(a, Rational)]
pmf = ECTA.pmf

{- | Aggregate the exact result distribution conditional on one structural size.

This enumerates the selected size class. Use 'countAtSize' for cardinality, or
'massesAtSize' when a retained-key distribution answers the question.
-}
pmfAtSize :: (Ord a) => ECTAGen a -> Int -> Either ECTAGenError [(a, Rational)]
pmfAtSize = ECTA.pmfAtSize

-- | Embed an ordinary QuickCheck generator as an opaque region.
fromGen :: QC.Gen a -> ECTAGen a
fromGen = ECTA.fromBackend . QuickCheckBackend

{- | Sample a non-recursive generator while retaining structured generator errors.

Unlike 'toGen', this does not bound a recursive generator from QuickCheck's
size parameter; apply 'upToSize' explicitly first.
-}
toGenEither :: ECTAGen a -> QC.Gen (Either ECTAGenError a)
toGenEither generator = case ECTA.lower generator of
    QuickCheckBackend generated -> generated

{- | Sample a finite transparent generator while retaining its stable rank and
errors.

Unlike 'toGenWithRank', this does not bound a recursive generator from
QuickCheck's size parameter; apply 'upToSize' explicitly first.
-}
toGenWithRankEither :: ECTAGen a -> QC.Gen (Either ECTAGenError (Integer, a))
toGenWithRankEither generator = case ECTA.lowerWithRank generator of
    QuickCheckBackend generated -> generated

{- | Sample through the generator type expected by QuickCheck.

Recursive generators are bounded by QuickCheck's size parameter.
-}
toGen :: ECTAGen a -> QC.Gen a
toGen generator
    | ECTA.isRecursive generator = QC.sized $ \size -> bounded !! max 0 size
    | Just (QuickCheckBackend direct) <- ECTA.lowerUniform generator = direct
    | otherwise = either (raise "toGen") id <$> toGenEither generator
  where
    bounded = [toGen (ECTA.upToSize (max firstSize size) generator) | size <- [0 ..]]
    firstSize = either (raise "toGen") (maybe 1 id) $ ECTA.minimumSize generator

{- | Sample an inspectable generator together with its stable replay rank.

Recursive generators are bounded by QuickCheck's size parameter.
-}
toGenWithRank :: ECTAGen a -> QC.Gen (Integer, a)
toGenWithRank generator
    | ECTA.isRecursive generator = QC.sized $ \size -> bounded !! max 0 size
    | Just (QuickCheckBackend direct) <- ECTA.lowerUniformWithRank generator = direct
    | otherwise = either (raise "toGenWithRank") id <$> toGenWithRankEither generator
  where
    bounded = [toGenWithRank (ECTA.upToSize (max firstSize size) generator) | size <- [0 ..]]
    firstSize = either (raise "toGenWithRank") (maybe 1 id) $ ECTA.minimumSize generator

{- | Fail a sample with the error's own guidance.

Sampling cannot return a failure, so a generator that could not be built
raises one here. The name is kept alongside the guidance so it can be
looked up or grepped for.
-}
raise :: String -> ECTAGenError -> a
raise called err =
    error $
        "Data.ECTA.Gen.QuickCheck."
            <> called
            <> ": "
            <> show err
            <> "\n"
            <> explain err

{- | Check a property over a transparent generator, shrinking to the
smallest failing member.

Shrink candidates first search every member of strictly smaller size, in size
order, capped at 'smallerMemberLimit', so the result is the globally smallest
failing member whenever the search reaches one. Component shrinking through
'shrinkRank' follows as a fallback, restricted to candidates of at most the
current size. For a recursive generator that fallback reads the candidates
from the form bounded at the current size, since a recursive generator has no
component shrinks of its own; bounding preserves ranks, so the candidates
replay against the unbounded generator unchanged. Every candidate is a member
of the generated language, and the failing rank is printed with the
counterexample, so 'unrank' replays it deterministically.

A generator with an opaque region has no ranks to shrink or replay, so it is
tested by sampling alone, with no shrinking.
-}
forAll :: (QC.Testable prop, Show a) => ECTAGen a -> (a -> prop) -> QC.Property
forAll = forAllWithLimit smallerMemberLimit

{- | 'forAll' with an explicit cap on the smaller-member search per shrink
step.

The cap bounds the members tested when the current failing member is
already minimal. When the language holds more small members than
'smallerMemberLimit' — command sequences, for example, accumulate many
short members — the default search never reaches the failing sizes and
structural shrinking alone cannot remove members in the middle of a
product. Raising the cap past the number of passing smaller members
restores the globally smallest failing member at the cost of testing that
many members per shrink step.
-}
forAllWithLimit ::
    (QC.Testable prop, Show a) => Int -> ECTAGen a -> (a -> prop) -> QC.Property
forAllWithLimit limit generator prop
    | ECTA.isOpaque generator = QC.forAll (toGen generator) prop
    | otherwise =
        QC.forAllShrinkShow
            (toGenWithRank generator)
            shrinkCandidates
            showRanked
            (prop . snd)
  where
    shrinkCandidates (rank, _) = smaller <> structural
      where
        smaller = take limit (smallerMembers generator rank)
        currentSize = sizeOfRank generator rank
        -- 'shrinkRank' has no candidates for a recursive generator, so the
        -- structural candidates come from the form bounded at the current
        -- size, whose shrinking is size-major halving. Bounding preserves
        -- ranks, and leaves a finite generator alone.
        bounded = maybe generator (`ECTA.upToSize` generator) currentSize
        -- Every 'shrinkRank' candidate already has a strictly smaller rank, so
        -- this guard only stops a candidate from growing in size; it is not
        -- what makes shrinking terminate. A candidate whose size cannot be
        -- read is out of range and is dropped by the 'unrank' guard below.
        notLarger candidate = case (sizeOfRank generator candidate, currentSize) of
            (Just candidateSize, Just size) -> candidateSize <= size
            _ -> True
        structural =
            [ (candidate, value)
            | candidate <- shrinkRank bounded rank
            , notLarger candidate
            , Right value <- [unrank generator candidate]
            ]

    showRanked (rank, value) = "rank " <> show rank <> ": " <> show value

{- | 'forAll' tests at most this many members of strictly smaller size per
shrink step before falling back to component shrinking.
-}
smallerMemberLimit :: Int
smallerMemberLimit = 1000

{- | Build the generator from QuickCheck's size parameter.

The generator for each size is built /and compiled/ once and shared across
samples, so neither the generator nor its decode plan is reconstructed on every
draw.
-}
sized :: (Int -> ECTAGen a) -> QC.Gen a
sized build = QC.sized $ \size -> towers !! max 0 size
  where
    towers = map (toGen . build) [0 ..]
