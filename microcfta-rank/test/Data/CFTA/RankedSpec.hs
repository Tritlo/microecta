module Data.CFTA.RankedSpec (spec) where

import Data.List (genericLength, sort)
import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import Test.QuickCheck (
    Gen,
    chooseInt,
    chooseInteger,
    conjoin,
    counterexample,
    forAllShow,
    oneof,
    property,
    sized,
    vectorOf,
    (.&&.),
    (===),
 )

import Data.CFTA.Index (Cardinality (..), Rank (..), Size, Weight (..), everyRank)
import qualified Data.CFTA.Ranked as Ranked
import Data.CFTA.Ranked.Internal (rankedPlan, share)
import Data.CFTA.Ranked.Internal.Sampler (Exact (..))
import Data.CFTA.Ranked.Internal.Shrink (smallestPlanRank)
import Data.CFTA.Ranked.Internal.Size (SizedRank (..), planPosition, sizeClassSelect, sizeIndex)

spec :: Spec
spec = do
    describe "against a list of members" $
        it "gives the ranks, the masses, the sizes, and the shrinks of the list" $
            property $
                forAllShow (sized $ \size -> described (min 3 (size `div` 25))) show $ \description ->
                    case build description of
                        Left err -> counterexample (show err) False
                        Right ranked ->
                            let listed = members description
                                ranks = everyRank $ Ranked.cardinality ranked
                                sizeAt rank = let (_, _, size) = listed !! fromEnum rank in size
                                checked = take 40 ranks
                             in conjoin $
                                    [ map (Ranked.unrank ranked) ranks === [Right value | (_, value, _) <- listed]
                                    , Map.fromListWith (+) [(sample, mass) | (mass, sample) <- runExact $ Ranked.lowerWithRank ranked]
                                        === Map.fromListWith (+) [(Ranked.RankedValue rank value, mass) | (rank, (mass, value, _)) <- zip [0 ..] listed]
                                    , Map.fromListWith (+) [(value, mass) | (mass, value) <- runExact $ Ranked.lower ranked]
                                        === Map.fromListWith (+) [(value, mass) | (mass, value, _) <- listed]
                                    , map (Ranked.sizeOfRank ranked) ranks === [Just size | (_, _, size) <- listed]
                                    , smallestPlanRank (rankedPlan $ share ranked) === smallestPlanRank (rankedPlan ranked)
                                    ]
                                        <> [ counterexample ("shrink " <> show rank) $
                                                [ candidate
                                                | candidate <- Ranked.shrinkRank ranked rank
                                                , candidate < 0 || candidate >= rank || sizeAt candidate > sizeAt rank
                                                ]
                                                    === []
                                           | rank <- checked
                                           ]
                                        <> [ counterexample ("smaller than " <> show rank) $
                                                let smaller = Ranked.smallerMembers ranked rank
                                                 in sort smaller === [Ranked.RankedValue other value | (other, (_, value, size)) <- zip [0 ..] listed, size < sizeAt rank]
                                                        .&&. map (sizeAt . Ranked.valueRank) smaller === sort (map (sizeAt . Ranked.valueRank) smaller)
                                           | rank <- checked
                                           ]

    describe "plan positions" $
        it "find the size class and position of every rank of a finite plan" $ do
            let languages = do
                    bit <- Ranked.fromIndexed (Ranked.Indexed 2 ((: []))) :: Either Ranked.RankedError (Ranked.Ranked [Rank])
                    let pair = (<>) <$> bit <*> bit
                        triple = (\a b c -> a <> b <> c) <$> bit <*> bit <*> bit
                    mixed <- Ranked.oneof [triple, bit, pair]
                    nested <- Ranked.oneof [(<>) <$> mixed <*> bit, pair]
                    pure [bit, pair, triple, mixed, nested]
            case languages of
                Left err -> expectationFailure $ show err
                Right plans ->
                    mapM_
                        ( \language -> do
                            let plan = rankedPlan language
                                Cardinality count = Ranked.cardinality language
                            [ fmap
                                (\(SizedRank size position) -> Ranked.valueRank $ sizeClassSelect (sizeIndex plan) size position)
                                (planPosition plan rank)
                              | rank <- everyRank $ Ranked.cardinality language
                              ]
                                `shouldBe` map Just (everyRank $ Ranked.cardinality language)
                            planPosition plan (Rank count) `shouldBe` Nothing
                        )
                        plans

    describe "structural shrinking" $ do
        it "never offers a member larger than the current one across choice branches" $ do
            let languages = do
                    small <- Ranked.fromIndexed (Ranked.Indexed 2 ((: []))) :: Either Ranked.RankedError (Ranked.Ranked [Rank])
                    let big = (\a b c -> a <> b <> c) <$> small <*> small <*> small
                    bigFirst <- Ranked.oneof [big, small]
                    smallFirst <- Ranked.oneof [small, big]
                    pure (bigFirst, smallFirst)
            case languages of
                Left err -> expectationFailure $ show err
                Right (bigFirst, smallFirst) -> do
                    -- Rank 8 is the size-one member [0] in the second branch.
                    Ranked.unrank bigFirst 8 `shouldBe` Right [0]
                    Ranked.shrinkRank bigFirst 8 `shouldBe` []
                    Ranked.smallerMembers bigFirst 8 `shouldBe` []
                    -- Rank 9 shrinks within its branch, never into the size-three branch.
                    Ranked.shrinkRank bigFirst 9 `shouldBe` [8]
                    -- A size-three member shrinks to the size-one branch when that branch comes first.
                    Ranked.unrank smallFirst 2 `shouldBe` Right [0, 0, 0]
                    take 1 (Ranked.shrinkRank smallFirst 2) `shouldBe` [0]

    describe "weighted indexed rank sources" $ do
        it "preserves exact ticket weights and returns replay ranks" $ do
            let outcomes = [(1, 'a'), (3, 'b'), (2, 'c')] :: [(Integer, Char)]
                ticketRanks = [1, 2, 0, 1, 2, 1] :: [Rank]
                source =
                    Ranked.WeightedIndexed
                        3
                        6
                        ((outcomes !!) . fromEnum)
                        ((ticketRanks !!) . fromInteger)
            case Ranked.fromWeightedIndexedOnDemand source of
                Left err -> expectationFailure $ show err
                Right ranked -> do
                    Ranked.cardinality ranked `shouldBe` 3
                    map (Ranked.unrank ranked) [0 .. 2] `shouldBe` map Right outcomes
                    runExact (Ranked.lowerWithRank ranked)
                        `shouldBe` [(1 % 6, Ranked.RankedValue rank (outcomes !! fromEnum rank)) | rank <- ticketRanks]
                    Map.fromListWith (+) [(value, mass) | (mass, value) <- runExact $ Ranked.lower ranked]
                        `shouldBe` Map.fromList [((1, 'a'), 1 % 6), ((3, 'b'), 3 % 6), ((2, 'c'), 2 % 6)]
                    Ranked.unrank ranked (-1) `shouldBe` Left (Ranked.NegativeRankedRank (-1))
                    Ranked.unrank ranked 3 `shouldBe` Left (Ranked.RankedSelectionOutOfRange 3 3)

        it "preserves weighted replay through maps and products" $ do
            let source = Ranked.WeightedIndexed 2 3 (\rank -> if rank == 0 then 'a' else 'b') (\ticket -> if ticket == 1 then 0 else 1)
            case Ranked.fromWeightedIndexedOnDemand source of
                Left err -> expectationFailure $ show err
                Right ranked -> do
                    let pairs = (,) <$> ranked <*> ranked
                        sampled = runExact $ Ranked.lowerWithRank pairs
                    Ranked.cardinality pairs `shouldBe` 4
                    map (Ranked.unrank pairs) [0 .. 3]
                        `shouldBe` map Right [('a', 'a'), ('a', 'b'), ('b', 'a'), ('b', 'b')]
                    [Ranked.unrank pairs rank == Right value | (_, Ranked.RankedValue rank value) <- sampled]
                        `shouldSatisfy` and
                    Map.fromListWith (+) [(value, mass) | (mass, Ranked.RankedValue _ value) <- sampled]
                        `shouldBe` Map.fromList [(('a', 'a'), 1 % 9), (('a', 'b'), 2 % 9), (('b', 'a'), 2 % 9), (('b', 'b'), 4 % 9)]

        it "checks source metadata without evaluating callbacks" $ do
            let inspect count mass =
                    fmap Ranked.cardinality
                        $ Ranked.fromWeightedIndexedOnDemand
                        $ Ranked.WeightedIndexed
                            count
                            mass
                            (error "construction decoded an indexed value" :: Rank -> ())
                            (error "construction decoded a sampling ticket")
            inspect 3 6 `shouldBe` Right 3
            inspect 0 0 `shouldBe` Left Ranked.EmptyRanked
            inspect (-1) 4 `shouldBe` Left Ranked.EmptyRanked
            inspect 3 0 `shouldBe` Left (Ranked.NonPositiveRankedWeight 0)
            inspect 3 (-1) `shouldBe` Left (Ranked.NonPositiveRankedWeight (-1))
            inspect 3 2 `shouldBe` Left (Ranked.InsufficientRankedWeight 3 2)

        it "samples Integer ticket mass beyond the machine Int range" $ do
            let mass = toInteger (maxBound :: Int) + 5
                source =
                    Ranked.WeightedIndexed
                        2
                        (Weight mass)
                        (\rank -> if rank == 0 then 'a' else 'b')
                        (\ticket -> if ticket == 0 then 0 else 1)
            case Ranked.fromWeightedIndexedOnDemand source of
                Left err -> expectationFailure $ show err
                Right ranked -> do
                    Ranked.cardinality ranked `shouldBe` 2
                    Ranked.unrank ranked 1 `shouldBe` Right 'b'
                    take 3 (runExact $ Ranked.lowerWithRank ranked)
                        `shouldBe` [(1 % mass, Ranked.RankedValue 0 'a'), (1 % mass, Ranked.RankedValue 1 'b'), (1 % mass, Ranked.RankedValue 1 'b')]

-- | A ranked language built from sources, choices, products, and maps.
data Described
    = -- | A weighted source; 'True' builds it on demand with tickets.
      Weighted Bool [(Integer, Int)]
    | -- | A uniform source; 'True' builds it on demand.
      Uniform Bool [Int]
    | Frequency [(Integer, Described)]
    | Oneof [Described]
    | Pair Described Described
    | Mapped Described
    deriving (Show)

-- | The members of a described language.
data Value = Atom Int | Both Value Value | Wrapped Value
    deriving (Eq, Ord, Show)

-- | A random description, nested to the given depth.
described :: Int -> Gen Described
described depth
    | depth <= 0 = source
    | otherwise =
        oneof
            [ source
            , Frequency <$> some ((,) <$> chooseInteger (1, 4) <*> described (depth - 1))
            , Oneof <$> some (described (depth - 1))
            , Pair <$> described (depth - 1) <*> described (depth - 1)
            , Mapped <$> described (depth - 1)
            ]
  where
    source =
        oneof
            [ Weighted <$> oneof [pure False, pure True] <*> some ((,) <$> chooseInteger (1, 4) <*> chooseInt (0, 9))
            , Uniform <$> oneof [pure False, pure True] <*> some (chooseInt (0, 9))
            ]
    some element = chooseInt (1, 3) >>= (`vectorOf` element)

{- | The members of a described language in rank order, with their masses and
sizes. A choice lists its branches in order, and a product varies its right
side fastest. A choice selects a branch by its weight, and a product selects
its sides independently. A source member has size one, and a product adds
the sizes of its sides.
-}
members :: Described -> [(Rational, Value, Size)]
members description = case description of
    Weighted _ entries -> [(weight % sum (map fst entries), Atom value, 1) | (weight, value) <- entries]
    Uniform _ values -> [(1 % genericLength values, Atom value, 1) | value <- values]
    Frequency branches ->
        [ (weight % sum (map fst branches) * mass, value, size)
        | (weight, branch) <- branches
        , (mass, value, size) <- members branch
        ]
    Oneof branches -> [(mass / genericLength branches, value, size) | branch <- branches, (mass, value, size) <- members branch]
    Pair left right ->
        [ (leftMass * rightMass, Both leftValue rightValue, leftSize + rightSize)
        | (leftMass, leftValue, leftSize) <- members left
        , (rightMass, rightValue, rightSize) <- members right
        ]
    Mapped inner -> [(mass, Wrapped value, size) | (mass, value, size) <- members inner]

build :: Described -> Either Ranked.RankedError (Ranked.Ranked Value)
build description = case description of
    Weighted False entries -> Ranked.fromWeighted [(Weight weight, Atom value) | (weight, value) <- entries]
    Weighted True entries ->
        Ranked.fromWeightedIndexedOnDemand $
            Ranked.WeightedIndexed
                (genericLength entries)
                (Weight $ sum $ map fst entries)
                (Atom . snd . (entries !!) . fromEnum)
                (([rank | (rank, (weight, _)) <- zip [0 ..] entries, _ <- [1 .. weight]] !!) . fromInteger)
    Uniform onDemand values ->
        (if onDemand then Ranked.fromIndexedOnDemand else Ranked.fromIndexed) $
            Ranked.Indexed (genericLength values) (Atom . (values !!) . fromEnum)
    Frequency branches -> Ranked.frequency =<< traverse (traverse build) [(Weight weight, branch) | (weight, branch) <- branches]
    Oneof branches -> Ranked.oneof =<< traverse build branches
    Pair left right -> (\leftRanked rightRanked -> Both <$> leftRanked <*> rightRanked) <$> build left <*> build right
    Mapped inner -> fmap Wrapped <$> build inner
