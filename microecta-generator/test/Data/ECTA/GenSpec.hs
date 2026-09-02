{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

module Data.ECTA.GenSpec (spec) where

import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import Data.String (fromString)
import Test.Hspec (Expectation, Spec, describe, expectationFailure, it, shouldBe, shouldNotBe, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as QCGen
import qualified Test.QuickCheck.Random as QCRandom

import Data.ECTA (Node (Node), edgeChildren, edgeSymbol)
import qualified Data.ECTA.Gen as Core
import Data.ECTA.Gen.QuickCheck (Args (..), ECTAGen, On (..), Sig ((:*), (:->)))
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.Internal.ECTA.Type (edgeEcs)
import Data.ECTA.Paths (EqConstraints (EmptyConstraints))

data UserId = Alice | Bob | Carol | Dave
    deriving (Bounded, Enum, Eq, Ord, Show)

data AuthenticationMethod = Password | Token
    deriving (Bounded, Enum, Eq, Ord, Show)

data AuthenticationFixture = AuthenticationFixture
    { authenticatedUser :: UserId
    , authenticationMethod :: AuthenticationMethod
    }
    deriving (Eq, Ord, Show)

data Path = HomeFile | ConfigFile | CacheFile
    deriving (Bounded, Enum, Eq, Ord, Show)

data FilesystemFixture = FilesystemFixture
    { fileOwner :: UserId
    , filePath :: Path
    }
    deriving (Eq, Ord, Show)

-- | Access roles used by the independent relation reference language.
data Role = Admin | Member
    deriving (Eq, Ord, Show)

-- | Resource classes used by the independent relation reference language.
data Classification = Public | Secret
    deriving (Eq, Ord, Show)

-- | Keys used to test a caller-declared group independently of its values.
data UserFamily = DeclaredUsers | OtherUsers
    deriving (Eq, Ord, Show)

-- | States used to check weighted operation keys inside recursive grouping.
data CoinPhase = Initial | SawHeads | SawTails | Unreachable
    deriving (Eq, Ord, Show)

-- | The permission relation exercised by 'relatedAccess'.
canRead :: Role -> Classification -> Bool
canRead Admin _ = True
canRead Member Public = True
canRead Member Secret = False

-- | A finite exact backend used to verify rank-sampling probabilities.
newtype Exact a = Exact {runExact :: [(Rational, a)]}

instance Functor Exact where
    fmap apply (Exact outcomes) =
        Exact [(mass, apply value) | (mass, value) <- outcomes]

instance Applicative Exact where
    pure value = Exact [(1, value)]
    Exact functions <*> Exact values =
        Exact
            [ (functionMass * valueMass, function value)
            | (functionMass, function) <- functions
            , (valueMass, value) <- values
            ]

instance Core.GenBackend Exact where
    selectInteger bound =
        Exact
            [ (1 / fromInteger bound, index)
            | index <- [0 .. bound - 1]
            ]

    frequencyGen alternatives =
        Exact
            [ (fromInteger weight / fromInteger totalWeight * mass, value)
            | (weight, Exact outcomes) <- alternatives
            , (mass, value) <- outcomes
            ]
      where
        totalWeight = sum $ map fst alternatives

    filterGen predicate (Exact outcomes) =
        Exact [(mass / acceptedMass, value) | (mass, value) <- accepted]
      where
        accepted = filter (predicate . snd) outcomes
        acceptedMass = sum $ map fst accepted

-- | Aggregate exact ticket multiplicities by their sampled result.
aggregateRights :: (Ord a) => [(Rational, Either e a)] -> [(Rational, a)]
aggregateRights outcomes =
    [ (mass, value)
    | (value, mass) <-
        Map.toAscList $
            Map.fromListWith
                (+)
                [ (value, mass)
                | (mass, Right value) <- outcomes
                ]
    ]

-- | All users shared by the independently authored fixture generators.
allUsers :: [UserId]
allUsers = [minBound .. maxBound]

-- | Transparent ECTA user generator.
generatedUserId :: ECTAGen UserId
generatedUserId = ECTAGen.elements allUsers

-- These are ordinary, closed generators. Neither accepts shared input.
authenticationFixture :: ECTAGen AuthenticationFixture
authenticationFixture = ECTAGen.node (fromString "authentication") $ ECTAGen.do
    user <- generatedUserId
    method <- ECTAGen.elements [Password, Token]
    ECTAGen.pure $ AuthenticationFixture user method

filesystemFixture :: ECTAGen FilesystemFixture
filesystemFixture = ECTAGen.node (fromString "filesystem") $ ECTAGen.do
    owner <- generatedUserId
    path <- ECTAGen.elements [HomeFile, ConfigFile, CacheFile]
    ECTAGen.pure $ FilesystemFixture owner path

-- ECTA composes the closed fixtures by matching their existing user fields.
matchedFixture :: ECTAGen (AuthenticationFixture, FilesystemFixture)
matchedFixture =
    ECTAGen.match
        (authenticatedUser :==: fileOwner)
        authenticationFixture
        filesystemFixture

-- | Access pairs generated through the relation under test.
relatedAccess :: ECTAGen ((Role, String), (Classification, String))
relatedAccess =
    ECTAGen.relate
        fst
        fst
        canRead
        (ECTAGen.elements [(Admin, "Ada"), (Admin, "Alex"), (Member, "Morgan")])
        (ECTAGen.elements [(Public, "guide"), (Secret, "keys")])

-- | Independently listed accepted pairs and their conditioned mass.
expectedAccessPmf :: [(((Role, String), (Classification, String)), Rational)]
expectedAccessPmf =
    [ (((Admin, "Ada"), (Public, "guide")), 1 % 5)
    , (((Admin, "Ada"), (Secret, "keys")), 1 % 5)
    , (((Admin, "Alex"), (Public, "guide")), 1 % 5)
    , (((Admin, "Alex"), (Secret, "keys")), 1 % 5)
    , (((Member, "Morgan"), (Public, "guide")), 1 % 5)
    ]

rawFixture :: ECTAGen (AuthenticationFixture, FilesystemFixture)
rawFixture = (,) <$> authenticationFixture <*> filesystemFixture

matchingUsers :: (AuthenticationFixture, FilesystemFixture) -> Bool
matchingUsers (authentication, filesystem) =
    authenticatedUser authentication == fileOwner filesystem

expectedPmf :: [((AuthenticationFixture, FilesystemFixture), Rational)]
expectedPmf =
    [ ( (AuthenticationFixture user method, FilesystemFixture user path)
      , 1 % 24
      )
    | user <- allUsers
    , method <- [minBound .. maxBound]
    , path <- [minBound .. maxBound]
    ]

{- | Enumerate the compiled decoder through the exact backend and require,
for every rank in order: uniform mass and agreement with 'Core.unrank'.
-}
decodesEveryRankExactly :: (Eq a, Show a) => Core.ECTAGen Exact a -> Expectation
decodesEveryRankExactly generator =
    case Core.cardinality generator of
        Left err -> expectationFailure $ show err
        Right total ->
            runExact (Core.lowerWithRank generator)
                `shouldBe` [ (1 % total, fmap (\value -> (rank, value)) (Core.unrank generator rank))
                           | rank <- [0 .. total - 1]
                           ]

spec :: Spec
spec = do
    describe "ECTAGen joins" $ do
        it "closes qualified do with one visible n-ary node" $
            case ECTAGen.support authenticationFixture of
                Right (Node [edge]) ->
                    (edgeSymbol edge, length $ edgeChildren edge)
                        `shouldBe` (fromString "authentication", 2)
                result -> expectationFailure $ "unexpected node support: " <> show result

        it "retains matching keys in key and source order with the conditioned product PMF" $ do
            ECTAGen.pmf matchedFixture `shouldBe` Right expectedPmf
            let ranks = [0 .. toInteger (length expectedPmf) - 1]
            traverse (ECTAGen.unrank matchedFixture) ranks
                `shouldBe` Right (map fst expectedPmf)

        it "relates different key types against the declared predicate" $ do
            ECTAGen.cardinality relatedAccess `shouldBe` Right 5
            ECTAGen.pmf relatedAccess `shouldBe` Right expectedAccessPmf

        it "preserves and conditions source weights across related groups" $
            ECTAGen.pmf
                ( ECTAGen.relate
                    id
                    id
                    canRead
                    (ECTAGen.frequency [(3, ECTAGen.elements [Admin]), (1, ECTAGen.elements [Member])])
                    (ECTAGen.elements [Public, Secret])
                )
                `shouldBe` Right
                    [ ((Admin, Public), 3 % 7)
                    , ((Admin, Secret), 3 % 7)
                    , ((Member, Public), 1 % 7)
                    ]

        it "matches the prototype's exact fixture and rejection counts" $ do
            fmap length (ECTAGen.pmf authenticationFixture) `shouldBe` Right 8
            fmap length (ECTAGen.pmf filesystemFixture) `shouldBe` Right 12
            case ECTAGen.pmf rawFixture of
                Left err -> expectationFailure $ show err
                Right rawPmf -> do
                    length rawPmf `shouldBe` 96
                    length (filter (not . matchingUsers . fst) rawPmf) `shouldBe` 72
                    sum
                        [ probability
                        | (pair, probability) <- rawPmf
                        , not $ matchingUsers pair
                        ]
                        `shouldBe` 3 % 4

        it "represents the join with an ECTA equality constraint" $
            case ECTAGen.support matchedFixture of
                Right (Node [edge]) -> edgeEcs edge `shouldNotBe` EmptyConstraints
                result -> expectationFailure $ "unexpected join support: " <> show result

        it "reports an empty join" $
            ECTAGen.pmf
                ( ECTAGen.match
                    (id :==: id)
                    (ECTAGen.elements [Alice])
                    (ECTAGen.elements [Bob])
                )
                `shouldBe` Left ECTAGen.EmptyGenerator

        it "reports a relation with no accepted live keys" $
            ECTAGen.pmf
                ( ECTAGen.relate
                    id
                    id
                    (\_ _ -> False)
                    (ECTAGen.elements [Admin])
                    (ECTAGen.elements [Public])
                )
                `shouldBe` Left ECTAGen.EmptyGenerator

        it "represents a relation with an ECTA equality witness" $
            case ECTAGen.support relatedAccess of
                Right (Node [edge]) -> edgeEcs edge `shouldNotBe` EmptyConstraints
                result -> expectationFailure $ "unexpected relation support: " <> show result

        it "preserves frequency weights around already-conditioned generators" $
            let rare =
                    Password
                        <$ ECTAGen.match
                            (id :==: id)
                            generatedUserId
                            (ECTAGen.elements [Carol])
                common =
                    Token
                        <$ ECTAGen.match
                            (id :==: id)
                            generatedUserId
                            (ECTAGen.elements [Alice])
             in ECTAGen.pmf (ECTAGen.frequency [(1, rare), (1, common)])
                    `shouldBe` Right [(Password, 1 % 2), (Token, 1 % 2)]

        it "conjoins every declared key equality" $ do
            let left = ECTAGen.elements [(0 :: Int, 0 :: Int, "left-00"), (0, 1, "left-01")]
                right =
                    ECTAGen.elements
                        [ (0 :: Int, 0 :: Int, "right-00")
                        , (0, 1, "right-01")
                        , (1, 0, "right-10")
                        ]
                firstKey (first, _, _) = first
                secondKey (_, second, _) = second
            traverse
                (ECTAGen.unrank $ ECTAGen.match ((firstKey :==: firstKey) :&&: (secondKey :==: secondKey)) left right)
                [0, 1]
                `shouldBe` Right
                    [ ((0, 0, "left-00"), (0, 0, "right-00"))
                    , ((0, 1, "left-01"), (0, 1, "right-01"))
                    ]

        it "samples a non-uniform join with exactly its inspected PMF" $ do
            let left :: Core.ECTAGen Exact UserId
                left =
                    Core.frequency
                        [ (4, Core.elements [Alice])
                        , (1, Core.elements [Bob, Carol])
                        ]
                right :: Core.ECTAGen Exact UserId
                right =
                    Core.frequency
                        [ (1, Core.elements [Alice])
                        , (3, Core.elements [Bob, Carol])
                        ]
                generator = Core.match (id Core.:==: id) left right
                sampled = runExact $ Core.lower generator
                sampledErrors = [err | (_, Left err) <- sampled]
                sampledPmf =
                    Map.toAscList $
                        Map.fromListWith
                            (+)
                            [(value, mass) | (mass, Right value) <- sampled]
            sampledErrors `shouldBe` []
            Right sampledPmf `shouldBe` Core.pmf generator

        it "matches a brute-force grouped apply with weighted multiplicities" $ do
            let centers :: [((Char, Int, Int, Int), String)]
                centers =
                    [ (('a', 0, 0, 0), "common")
                    , (('b', 0, 0, 0), "common")
                    , (('c', 1, 0, 1), "rare")
                    ]
                lefts :: [(Int, String)]
                lefts = [(0, "left-a"), (0, "left-b"), (1, "left-c")]
                rights :: [(Int, String)]
                rights = [(0, "right-a"), (0, "right-a"), (1, "right-b")]
                signature (_, leftKey, rightKey, resultKey) =
                    leftKey :* rightKey :-> resultKey
                operations =
                    ECTAGen.regroupBy signature $
                        ECTAGen.groupBy fst (ECTAGen.elements centers)
                grouped =
                    ECTAGen.ungroup $
                        ECTAGen.apply
                            ((,,) <$> operations)
                            ( ECTAGen.groupBy fst (ECTAGen.elements lefts)
                                :& ECTAGen.groupBy fst (ECTAGen.elements rights)
                                :& ANil
                            )
                accepted =
                    [ (center, left, right)
                    | center <- centers
                    , left <- lefts
                    , right <- rights
                    , let (_, expectedLeft, expectedRight, _) = fst center
                    , expectedLeft == fst left
                    , expectedRight == fst right
                    ]
                acceptedCount = toInteger $ length accepted
                expected =
                    Map.toAscList $
                        fmap (% acceptedCount) $
                            Map.fromListWith
                                (+)
                                [(value, 1) | value <- accepted]
            ECTAGen.sizes operations
                `shouldBe` Right (Map.fromList [(0 :* 0 :-> 0, 2), (1 :* 0 :-> 1, 1)])
            ECTAGen.pmf (ECTAGen.atKey (0 :* 0 :-> 0) operations)
                `shouldBe` Right [(centers !! 0, 1 % 2), (centers !! 1, 1 % 2)]
            ECTAGen.pmf grouped `shouldBe` Right expected

    describe "indexed and opaque sources" $ do
        it "decodes a transparent source from stable indices" $
            ECTAGen.pmf
                ( ECTAGen.fromIndexed $
                    ECTAGen.Indexed 3 $ \case
                        0 -> Alice
                        1 -> Bob
                        2 -> Carol
                        index -> error $ "unexpected index: " <> show index
                )
                `shouldBe` Right [(Alice, 1 % 3), (Bob, 1 % 3), (Carol, 1 % 3)]

        it "freezes native draws as transparent ranks, including duplicates" $ do
            let native = QC.chooseInteger (0, 3)
                seed = QCRandom.mkQCGen 20260818
                expected = QCGen.unGen (QC.vectorOf 8 native) seed 30
                pooled = QCGen.unGen (ECTAGen.pool 8 native) seed 30
            ECTAGen.cardinality pooled `shouldBe` Right 8
            traverse (ECTAGen.unrank pooled) [0 .. 7] `shouldBe` Right expected
            ECTAGen.countBy id pooled
                `shouldBe` Right (Map.fromListWith (+) [(value, 1) | value <- expected])

        it "uses one frozen pool on both sides of a constrained join" $ do
            let native = QC.chooseInteger (0, 3)
                seed = QCRandom.mkQCGen 20260818
                values = QCGen.unGen (QC.vectorOf 8 native) seed 30
                pooled = QCGen.unGen (ECTAGen.pool 8 native) seed 30
                equalPairs = ECTAGen.match (id :==: id) pooled pooled
                accepted = [(left, right) | left <- values, right <- values, left == right]
                acceptedCount = toInteger $ length accepted
                pooledExpectedPmf =
                    Map.toAscList $
                        fmap (% acceptedCount) $
                            Map.fromListWith (+) [(pair, 1) | pair <- accepted]
            ECTAGen.cardinality equalPairs `shouldBe` Right acceptedCount
            ECTAGen.pmf equalPairs `shouldBe` Right pooledExpectedPmf

        it "turns a non-positive pool size into an empty generator" $ do
            let freeze sampleCount =
                    QCGen.unGen
                        (ECTAGen.pool sampleCount (pure Alice))
                        (QCRandom.mkQCGen 20260818)
                        30
            ECTAGen.cardinality (freeze 0) `shouldBe` Left ECTAGen.EmptyGenerator
            ECTAGen.cardinality (freeze (-1)) `shouldBe` Left ECTAGen.EmptyGenerator

        it "reuses one indexed choice through fmap" $
            ECTAGen.pmf
                ( do
                    user <- ECTAGen.elements [Alice, Bob]
                    pure (user, user)
                )
                `shouldBe` Right [((Alice, Alice), 1 % 2), ((Bob, Bob), 1 % 2)]

        it "exposes exact cardinality and deterministic unranking" $ do
            let users = ECTAGen.elements [Alice, Bob, Carol]
            ECTAGen.cardinality users `shouldBe` Right 3
            traverse (ECTAGen.unrank users) [0, 1, 2]
                `shouldBe` Right [Alice, Bob, Carol]
            ECTAGen.unrank users 3
                `shouldBe` Left (ECTAGen.SelectionOutOfRange 3 3)

        it "finds a finite structural minimum beyond rank zero" $ do
            let larger = (,) <$> ECTAGen.elements [0 :: Int] <*> ECTAGen.elements [0 :: Int]
                smaller = ECTAGen.elements [(1, 1)]
                generator = ECTAGen.oneof [larger, smaller]
            ECTAGen.unrank generator 0 `shouldBe` Right (0, 0)
            ECTAGen.sizeOfRank generator 0 `shouldBe` Just 2
            ECTAGen.sizeOfRank generator 1 `shouldBe` Just 1
            ECTAGen.smallest generator `shouldBe` Right (Just (1, 1))

        it "returns a sampled rank that deterministically replays its value" $
            QC.property $
                QC.forAll (ECTAGen.toGenWithRank matchedFixture) $ \(rank, value) ->
                    ECTAGen.unrank matchedFixture rank QC.=== Right value

        modifyMaxSuccess (const 200) $
            it "replays weighted samples even when sampling reorders branches" $
                let weighted =
                        ECTAGen.frequency
                            [ (1, pure Alice)
                            , (3, ECTAGen.elements [Bob, Carol])
                            ]
                 in QC.forAll (ECTAGen.toGenWithRank weighted) $ \(rank, value) ->
                        ECTAGen.unrank weighted rank QC.=== Right value

        it "returns construction errors through the explicit sampling API" $ do
            let sample generator =
                    QCGen.unGen
                        (ECTAGen.toGenEither generator)
                        (QCRandom.mkQCGen 20260821)
                        30
            sample (ECTAGen.frequency [] :: ECTAGen UserId)
                `shouldBe` Left ECTAGen.EmptyGenerator
            sample (ECTAGen.frequency [(0, pure Alice)])
                `shouldBe` Left (ECTAGen.NonPositiveWeight 0)
            sample (ECTAGen.frequency [(-1, pure Alice)])
                `shouldBe` Left (ECTAGen.NonPositiveWeight (-1))

        it "samples a directly indexed source whose cardinality exceeds Int" $ do
            let total = toInteger (maxBound :: Int) + 17
                source = ECTAGen.fromIndexed $ ECTAGen.Indexed total id
                (rank, value) =
                    QCGen.unGen
                        (ECTAGen.toGenWithRank source)
                        (QCRandom.mkQCGen 20260821)
                        30
            value `shouldBe` rank
            rank `shouldSatisfy` (\selected -> selected >= 0 && selected < total)

        it "keeps fromGen opaque" $ do
            let opaque = ECTAGen.fromGen $ QC.elements [Alice, Bob]
                opaqueJoin =
                    ECTAGen.match (id :==: id) opaque (ECTAGen.elements [Bob])
            ECTAGen.pmf opaqueJoin
                `shouldBe` Left ECTAGen.CannotInspectOpaqueGenerator
            ECTAGen.cardinality opaque
                `shouldBe` Left ECTAGen.CannotInspectOpaqueGenerator
            ECTAGen.unrank opaque 0
                `shouldBe` Left ECTAGen.CannotInspectOpaqueGenerator

        it "allows an opaque source to participate in a join" $
            let opaque = ECTAGen.fromGen $ QC.elements [Alice, Bob]
                opaqueJoin =
                    ECTAGen.match (id :==: id) opaque (ECTAGen.elements [Bob])
             in QC.property
                    ( QC.forAll (ECTAGen.toGen opaqueJoin) $ \(left, right) ->
                        left QC.=== right
                    )

        it "allows an opaque source to participate in a relation" $
            let opaque = ECTAGen.fromGen $ QC.elements [Admin, Member]
                related =
                    ECTAGen.relate
                        id
                        id
                        canRead
                        opaque
                        (ECTAGen.elements [Secret])
             in QC.property
                    ( QC.forAll (ECTAGen.toGen related) $ \pair ->
                        pair QC.=== (Admin, Secret)
                    )

    describe "declared groups" $ do
        it "retains source-rank order inside each computed group" $ do
            let source = ECTAGen.elements [("b", 0 :: Int), ("a", 1), ("b", 2), ("a", 3)]
                selected = ECTAGen.atKey "a" $ ECTAGen.groupBy fst source
            traverse (ECTAGen.unrank selected) [0, 1]
                `shouldBe` Right [("a", 1), ("a", 3)]

        it "preserves a finite source's support, ranks, and distribution" $ do
            let source =
                    ECTAGen.frequency
                        [ (3, ECTAGen.elements [Alice])
                        , (1, ECTAGen.elements [Bob, Carol])
                        ]
                family = ECTAGen.keyed DeclaredUsers source
                selected = ECTAGen.atKey DeclaredUsers family
            ECTAGen.sizes family
                `shouldBe` Right (Map.singleton DeclaredUsers 3)
            ECTAGen.support selected `shouldBe` ECTAGen.support source
            traverse (ECTAGen.unrank selected) [0 .. 2]
                `shouldBe` traverse (ECTAGen.unrank source) [0 .. 2]
            ECTAGen.pmf selected `shouldBe` ECTAGen.pmf source
            ECTAGen.pmf (ECTAGen.atKey OtherUsers family)
                `shouldBe` Left ECTAGen.EmptyGenerator
            ECTAGen.smallest (ECTAGen.atKey OtherUsers family)
                `shouldBe` Right Nothing

        it "combines declared languages with the grouped choice weights" $ do
            let family =
                    ECTAGen.oneofGrouped
                        [ ECTAGen.keyed DeclaredUsers $ ECTAGen.elements [Alice, Bob]
                        , ECTAGen.keyed OtherUsers $ ECTAGen.elements [Carol]
                        ]
            ECTAGen.sizes family
                `shouldBe` Right (Map.fromList [(DeclaredUsers, 2), (OtherUsers, 1)])
            ECTAGen.pmf (ECTAGen.ungroup family)
                `shouldBe` Right [(Alice, 1 % 4), (Bob, 1 % 4), (Carol, 1 % 2)]

        it "preserves construction failures and rejects opaque sources" $ do
            let empty = ECTAGen.elements [] :: ECTAGen UserId
                opaque = ECTAGen.fromGen $ pure Alice
            ECTAGen.sizes (ECTAGen.keyed DeclaredUsers empty)
                `shouldBe` Left ECTAGen.EmptyGenerator
            ECTAGen.smallest empty `shouldBe` Right Nothing
            ECTAGen.countsAtSize (ECTAGen.keyed DeclaredUsers empty) (-1)
                `shouldBe` Left ECTAGen.EmptyGenerator
            ECTAGen.massesAtSize (ECTAGen.keyed DeclaredUsers empty) (-1)
                `shouldBe` Left ECTAGen.EmptyGenerator
            ECTAGen.pmfAtSize empty (-1)
                `shouldBe` Left ECTAGen.EmptyGenerator
            ECTAGen.sizes (ECTAGen.keyed DeclaredUsers opaque)
                `shouldBe` Left ECTAGen.CannotInspectOpaqueGenerator
            ECTAGen.smallest opaque
                `shouldBe` Left ECTAGen.CannotInspectOpaqueGenerator
            ECTAGen.pmfAtSize opaque (-1)
                `shouldBe` Left ECTAGen.CannotInspectOpaqueGenerator

        it "reports finite retained-key masses conditional on size" $ do
            let family =
                    ECTAGen.frequencies
                        [ (3, ECTAGen.keyed DeclaredUsers $ pure Alice)
                        , (1, ECTAGen.keyed OtherUsers $ pure Bob)
                        ]
            ECTAGen.massesAtSize family 0 `shouldBe` Right mempty
            ECTAGen.countsAtSize family 1
                `shouldBe` Right
                    ( Map.fromList
                        [ (DeclaredUsers, 1)
                        , (OtherUsers, 1)
                        ]
                    )
            ECTAGen.massesAtSize family 1
                `shouldBe` Right
                    ( Map.fromList
                        [ (DeclaredUsers, 3 % 4)
                        , (OtherUsers, 1 % 4)
                        ]
                    )
            ECTAGen.massesAtSize family 2 `shouldBe` Right mempty

    describe "recursive sampling" $ do
        it "preserves an atomic finite distribution and its stable ranks" $ do
            let coin :: Core.ECTAGen Exact Bool
                coin =
                    Core.atomic $
                        Core.frequency
                            [ (3, Core.elements [True])
                            , (1, Core.elements [False])
                            ]
                traces =
                    Core.recur $ \rest ->
                        Core.oneof
                            [ (: []) <$> coin
                            , (:) <$> coin <*> rest
                            ]
                bounded = Core.upToSize 2 traces
            let sampled = runExact $ Core.lowerWithRank bounded
            [() | (_, Left _) <- sampled] `shouldBe` []
            aggregateRights sampled
                `shouldBe` [ (1 % 4, (0, [True]))
                           , (1 % 12, (1, [False]))
                           , (3 % 8, (2, [True, True]))
                           , (1 % 8, (3, [True, False]))
                           , (1 % 8, (4, [False, True]))
                           , (1 % 24, (5, [False, False]))
                           ]
            traverse (Core.unrank bounded) [0 .. 5]
                `shouldBe` Right
                    [ [True]
                    , [False]
                    , [True, True]
                    , [True, False]
                    , [False, True]
                    , [False, False]
                    ]

        it "keeps finite weights out of recursion without an atomic boundary" $ do
            let coin :: Core.ECTAGen Exact Bool
                coin =
                    Core.frequency
                        [ (3, Core.elements [True])
                        , (1, Core.elements [False])
                        ]
                traces =
                    Core.recur $ \rest ->
                        Core.oneof
                            [ (: []) <$> coin
                            , (:) <$> coin <*> rest
                            ]
            map fst (runExact $ Core.lowerWithRank $ Core.upToSize 2 traces)
                `shouldBe` replicate 6 (1 % 6)

        it "preserves atomic distributions through recurGrouped and apply" $ do
            let atoms =
                    Core.keyed () $
                        Core.atomic $
                            Core.frequency
                                [ (3, Core.elements ["H"])
                                , (1, Core.elements ["T"])
                                ]
                operators =
                    Core.keyed (() :-> ()) $
                        Core.elements [("x" <>)]
                family =
                    Core.recurGrouped $ \self ->
                        Core.oneofGrouped
                            [ atoms
                            , Core.apply operators (self :& ANil)
                            ]
                bounded = Core.upToSize 2 $ Core.atKey () family
            let sampled = runExact $ Core.lowerWithRank bounded
            [() | (_, Left _) <- sampled] `shouldBe` []
            aggregateRights sampled
                `shouldBe` [ (3 % 8, (0, "H"))
                           , (1 % 8, (1, "T"))
                           , (3 % 8, (2, "xH"))
                           , (1 % 8, (3, "xT"))
                           ]

        it "keeps atomic mass between recursive operation keys" $ do
            let operations =
                    snd
                        <$> Core.groupBy
                            fst
                            ( Core.atomic $
                                Core.frequency
                                    [ (9, pure (Initial :-> SawHeads, (True :)))
                                    , (1, pure (Initial :-> SawTails, (False :)))
                                    ]
                            )
                family :: Core.Grouped Exact CoinPhase [Bool]
                family =
                    Core.recurGrouped $ \self ->
                        Core.oneofGrouped
                            [ Core.keyed Initial $ pure []
                            , Core.apply operations (self :& ANil)
                            ]
                traces = Core.ungroup family
            Core.countsAtSize family 2
                `shouldBe` Right
                    (Map.fromList [(SawHeads, 1), (SawTails, 1)])
            Core.massesAtSize family 2
                `shouldBe` Right
                    (Map.fromList [(SawHeads, 9 % 10), (SawTails, 1 % 10)])
            (sum <$> Core.countsAtSize family 2)
                `shouldBe` Core.countAtSize traces 2
            (sum <$> Core.massesAtSize family 2)
                `shouldBe` Right 1
            Core.pmfAtSize traces 2
                `shouldBe` Right [([False], 1 % 10), ([True], 9 % 10)]
            Core.smallest (Core.atKey SawHeads family)
                `shouldBe` Right (Just [True])
            Core.smallest (Core.atKey Unreachable family)
                `shouldBe` Right Nothing

    describe "compiled rank decoding" $ do
        it "decodes every rank of a mapped source" $
            decodesEveryRankExactly $
                show <$> Core.elements [1 :: Int .. 5]

        it "decodes every rank of nested uniform frequencies" $
            decodesEveryRankExactly $
                Core.frequency
                    [ (2, Core.elements "ab")
                    , (2, Core.frequency [(1, Core.elements "c"), (1, Core.elements "d")])
                    ]

        it "decodes every rank of an applicative product" $
            decodesEveryRankExactly $
                (,) <$> Core.elements [1 :: Int, 2, 3] <*> Core.elements "ab"

        it "decodes every rank of a grouped ternary application tower" $ do
            let operations =
                    Core.groupBy
                        (\(_, key1, key2, key3, resultKey) -> key1 :* key2 :* key3 :-> resultKey)
                        (Core.elements [("f", 0 :: Int, 0, 1, 0 :: Int), ("g", 0, 1, 1, 1), ("h", 1, 0, 0, 1)])
                family =
                    Core.groupBy fst (Core.elements [(0 :: Int, "a"), (0, "b"), (1, "c")])
                applied =
                    Core.apply
                        ((\(name, _, _, _, _) x y z -> name <> snd x <> snd y <> snd z) <$> operations)
                        (family :& family :& family :& ANil)
            decodesEveryRankExactly $
                Core.ungroup $
                    Core.mapWithKey (\key value -> (key, value)) applied

        it "decodes every rank of a mixed-depth frequencies tower" $ do
            let atomsFamily =
                    snd <$> Core.groupBy fst (Core.elements [(0 :: Int, "x"), (0, "y"), (1, "z")])
                operations =
                    Core.groupBy
                        (\(_, leftKey, rightKey, resultKey) -> leftKey :* rightKey :-> resultKey)
                        (Core.elements [("f", 0 :: Int, 0, 0), ("g", 0, 1, 1), ("h", 1, 0, 1)])
                layer children =
                    Core.apply
                        ((\(name, _, _, _) left right -> name <> left <> right) <$> operations)
                        (children :& children :& ANil)
                mixed =
                    Core.frequencies
                        [ (3, atomsFamily)
                        , (8, layer atomsFamily)
                        ]
            decodesEveryRankExactly $ Core.ungroup mixed

        it "agrees with unrank on every enumerated non-uniform rank" $ do
            let generator =
                    Core.frequency
                        [ (3, Core.elements [1 :: Int])
                        , (1, Core.elements [2, 3])
                        ]
                sampled = runExact $ Core.lowerWithRank generator
            [() | (_, Left _) <- sampled] `shouldBe` []
            [ Core.unrank generator rank == Right value
              | (_, Right (rank, value)) <- sampled
              ]
                `shouldSatisfy` and

        it "streams exactly the structurally smaller members in size order" $ do
            let atomsFamily =
                    snd <$> Core.groupBy fst (Core.elements [(0 :: Int, "x"), (0, "y"), (1, "z")])
                operations =
                    Core.groupBy
                        (\(_, leftKey, rightKey, resultKey) -> leftKey :* rightKey :-> resultKey)
                        (Core.elements [("f", 0 :: Int, 0, 0), ("g", 0, 1, 1), ("h", 1, 0, 1)])
                mixed :: Core.ECTAGen Exact String
                mixed =
                    Core.ungroup $
                        Core.frequencies
                            [ (3, atomsFamily)
                            ,
                                ( 8
                                , Core.apply
                                    ((\(name, _, _, _) left right -> name <> left <> right) <$> operations)
                                    (atomsFamily :& atomsFamily :& ANil)
                                )
                            ]
            case Core.cardinality mixed of
                Left err -> expectationFailure $ show err
                Right total -> do
                    let applicationRanks =
                            [ rank
                            | rank <- [0 .. total - 1]
                            , Right value <- [Core.unrank mixed rank]
                            , length value == 3
                            ]
                    case applicationRanks of
                        (firstApplication : _) -> do
                            map snd (Core.smallerMembers mixed firstApplication)
                                `shouldBe` ["x", "y", "z"]
                            [ Core.unrank mixed rank == Right value
                              | (rank, value) <- Core.smallerMembers mixed firstApplication
                              ]
                                `shouldSatisfy` and
                        [] -> expectationFailure "expected an application member"

        it "produces exactly the structural shrink candidates of a product" $
            let pairs :: Core.ECTAGen Exact (Int, Char)
                pairs = (,) <$> Core.elements [0 .. 3] <*> Core.elements "abcd"
             in Core.shrinkRank pairs 15 `shouldBe` [3, 11, 12, 14]

        modifyMaxSuccess (const 200) $
            it "replays sampled ranks below the Int cardinality boundary" $
                let chunk = ECTAGen.elements [0 :: Int .. 199]
                    wide =
                        (,,,,,,,)
                            <$> chunk
                            <*> chunk
                            <*> chunk
                            <*> chunk
                            <*> chunk
                            <*> chunk
                            <*> chunk
                            <*> chunk
                 in ECTAGen.cardinality wide QC.=== Right (200 ^ (8 :: Int))
                        QC..&&. QC.forAll
                            (ECTAGen.toGenWithRank wide)
                            ( \(rank, value) ->
                                ECTAGen.unrank wide rank QC.=== Right value
                            )

        modifyMaxSuccess (const 200) $
            it "replays sampled ranks beyond the Int cardinality boundary" $
                let chunk = ECTAGen.elements [0 :: Int .. 255]
                    wide =
                        (,,,,,,,)
                            <$> chunk
                            <*> chunk
                            <*> chunk
                            <*> chunk
                            <*> chunk
                            <*> chunk
                            <*> chunk
                            <*> chunk
                 in ECTAGen.cardinality wide QC.=== Right (256 ^ (8 :: Int))
                        QC..&&. QC.forAll
                            (ECTAGen.toGenWithRank wide)
                            ( \(rank, value) ->
                                ECTAGen.unrank wide rank QC.=== Right value
                            )
