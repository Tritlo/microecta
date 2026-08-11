{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE QualifiedDo #-}

module Data.ECTA.GenSpec (spec) where

import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import Test.Hspec (Expectation, Spec, describe, expectationFailure, it, shouldBe, shouldNotBe, shouldSatisfy)
import qualified Test.QuickCheck as QC

import Data.ECTA (Node (Node))
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

-- | All users shared by the independently authored fixture generators.
allUsers :: [UserId]
allUsers = [minBound .. maxBound]

-- | Transparent ECTA user generator.
generatedUserId :: ECTAGen UserId
generatedUserId = ECTAGen.elements allUsers

-- | Uniform QuickCheck generator used by the handwritten baseline.
generatedQuickCheckUserId :: QC.Gen UserId
generatedQuickCheckUserId = QC.elements allUsers

-- These are ordinary, closed generators. Neither accepts shared input.
authenticationFixture :: ECTAGen AuthenticationFixture
authenticationFixture = ECTAGen.do
    user <- generatedUserId
    method <- ECTAGen.elements [Password, Token]
    ECTAGen.pure $ AuthenticationFixture user method

filesystemFixture :: ECTAGen FilesystemFixture
filesystemFixture = ECTAGen.do
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

-- Ordinary QuickCheck can compose the same fixtures by retrying.
rejectionFixture :: QC.Gen (AuthenticationFixture, FilesystemFixture)
rejectionFixture = ECTAGen.toGen rawFixture `QC.suchThat` matchingUsers

-- If both generators can be refactored, handwritten sharing is simpler and
-- samples the user prior exactly once.
handwrittenFixture :: QC.Gen (AuthenticationFixture, FilesystemFixture)
handwrittenFixture = do
    user <- generatedQuickCheckUserId
    method <- QC.elements [Password, Token]
    path <- QC.elements [HomeFile, ConfigFile, CacheFile]
    pure
        ( AuthenticationFixture user method
        , FilesystemFixture user path
        )

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

-- | The ECTA match guarantees that authentication grants access to the file.
propMatchedAuthenticationCanRead :: QC.Property
propMatchedAuthenticationCanRead =
    QC.withNumTests 1000 $
        QC.forAll (ECTAGen.toGen matchedFixture) $ \(authentication, filesystem) ->
            authenticatedUser authentication QC.=== fileOwner filesystem

-- | QuickCheck rejection also guarantees access, but may retry many draws.
propRejectionAuthenticationCanRead :: QC.Property
propRejectionAuthenticationCanRead =
    QC.withNumTests 1000 $
        QC.forAll rejectionFixture $ \(authentication, filesystem) ->
            authenticatedUser authentication QC.=== fileOwner filesystem

-- | Choosing the shared user explicitly guarantees the same property.
propHandwrittenAuthenticationCanRead :: QC.Property
propHandwrittenAuthenticationCanRead =
    QC.withNumTests 1000 $
        QC.forAll handwrittenFixture $ \(authentication, filesystem) ->
            authenticatedUser authentication QC.=== fileOwner filesystem

-- | Independent generators do not guarantee that authentication grants access.
propIndependentAuthenticationCanRead :: QC.Property
propIndependentAuthenticationCanRead =
    QC.withNumTests 1000 $
        QC.expectFailure $
            QC.forAll (ECTAGen.toGen rawFixture) $ \(authentication, filesystem) ->
                authenticatedUser authentication QC.=== fileOwner filesystem

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
        it "retains only matching keys with the conditioned product PMF" $
            ECTAGen.pmf matchedFixture `shouldBe` Right expectedPmf

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

        it "matches authentication and ownership through ECTA" $
            propMatchedAuthenticationCanRead

        it "matches authentication and ownership through rejection" $
            propRejectionAuthenticationCanRead

        it "matches authentication and ownership through handwritten sharing" $
            propHandwrittenAuthenticationCanRead

        it "does not guarantee ownership for independent fixtures" $
            propIndependentAuthenticationCanRead

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

        it "returns a sampled rank that deterministically replays its value" $
            QC.property $
                QC.forAll (ECTAGen.toGenWithRank matchedFixture) $ \(rank, value) ->
                    ECTAGen.unrank matchedFixture rank QC.=== Right value

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

        it "produces exactly the structural shrink candidates of a product" $
            let pairs :: Core.ECTAGen Exact (Int, Char)
                pairs = (,) <$> Core.elements [0 .. 3] <*> Core.elements "abcd"
             in Core.shrinkRank pairs 15 `shouldBe` [3, 11, 12, 14]

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
             in QC.withNumTests 200 $
                    ECTAGen.cardinality wide QC.=== Right (200 ^ (8 :: Int))
                        QC..&&. QC.forAll
                            (ECTAGen.toGenWithRank wide)
                            ( \(rank, value) ->
                                ECTAGen.unrank wide rank QC.=== Right value
                            )

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
             in QC.withNumTests 200 $
                    ECTAGen.cardinality wide QC.=== Right (256 ^ (8 :: Int))
                        QC..&&. QC.forAll
                            (ECTAGen.toGenWithRank wide)
                            ( \(rank, value) ->
                                ECTAGen.unrank wide rank QC.=== Right value
                            )
