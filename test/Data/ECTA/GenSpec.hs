{-# LANGUAGE ApplicativeDo #-}

module Data.ECTA.GenSpec (spec) where

import qualified Data.Map.Strict as Map
import Data.Ratio ((%))
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldNotBe)
import qualified Test.QuickCheck as QC

import Data.ECTA (Node (Node))
import qualified Data.ECTA.Gen as Core
import Data.ECTA.Gen.QuickCheck (ECTAGen)
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.Internal.ECTA.Type (edgeEcs)
import Data.ECTA.Paths (EqConstraints (EmptyConstraints))

data UserId = Alice | Bob | Carol | Dave
    deriving (Eq, Ord, Show)

data AuthenticationMethod = Password | Token
    deriving (Eq, Ord, Show)

data Authentication = Authentication UserId AuthenticationMethod
    deriving (Eq, Ord, Show)

data Path = HomeFile | ConfigFile | CacheFile
    deriving (Eq, Ord, Show)

data Filesystem = Filesystem UserId Path
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

generatedUser :: ECTAGen UserId
generatedUser =
    ECTAGen.frequency
        [ (4, pure Alice)
        , (2, pure Bob)
        , (1, pure Carol)
        , (1, pure Dave)
        ]

authentication :: ECTAGen Authentication
authentication = do
    user <- generatedUser
    method <- ECTAGen.elements [Password, Token]
    pure $ Authentication user method

filesystem :: ECTAGen Filesystem
filesystem = do
    owner <- generatedUser
    path <- ECTAGen.elements [HomeFile, ConfigFile, CacheFile]
    pure $ Filesystem owner path

joined :: ECTAGen (Authentication, Filesystem)
joined =
    ECTAGen.innerJoinOn
        (\(Authentication user _) -> user)
        (\(Filesystem owner _) -> owner)
        authentication
        filesystem

expectedPmf :: [((Authentication, Filesystem), Rational)]
expectedPmf =
    [ ( (Authentication user method, Filesystem user path)
      , joinedUserMass user / 6
      )
    | user <- [Alice, Bob, Carol, Dave]
    , method <- [Password, Token]
    , path <- [HomeFile, ConfigFile, CacheFile]
    ]
  where
    joinedUserMass Alice = 8 % 11
    joinedUserMass Bob = 2 % 11
    joinedUserMass Carol = 1 % 22
    joinedUserMass Dave = 1 % 22

spec :: Spec
spec = do
    describe "ECTAGen joins" $ do
        it "retains only matching keys with the conditioned product PMF" $
            ECTAGen.pmf joined `shouldBe` Right expectedPmf

        it "represents the join with an ECTA equality constraint" $
            case ECTAGen.support joined of
                Right (Node [edge]) -> edgeEcs edge `shouldNotBe` EmptyConstraints
                result -> expectationFailure $ "unexpected join support: " <> show result

        it "reports an empty join" $
            ECTAGen.pmf
                ( ECTAGen.innerJoinOn
                    id
                    id
                    (ECTAGen.elements [Alice])
                    (ECTAGen.elements [Bob])
                )
                `shouldBe` Left ECTAGen.EmptyGenerator

        it "samples only matching keys" $
            QC.property $
                QC.forAll (ECTAGen.toGen joined) $ \(Authentication user _, Filesystem owner _) ->
                    user QC.=== owner

        it "preserves frequency weights around already-conditioned generators" $
            let rare =
                    Password
                        <$ ECTAGen.innerJoinOn
                            id
                            id
                            generatedUser
                            (ECTAGen.elements [Carol])
                common =
                    Token
                        <$ ECTAGen.innerJoinOn
                            id
                            id
                            generatedUser
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
                generator = Core.innerJoinOn id id left right
                sampled = runExact $ Core.lower generator
                sampledErrors = [err | (_, Left err) <- sampled]
                sampledPmf =
                    Map.toAscList $
                        Map.fromListWith
                            (+)
                            [(value, mass) | (mass, Right value) <- sampled]
            sampledErrors `shouldBe` []
            Right sampledPmf `shouldBe` Core.pmf generator

        it "matches a brute-force keyed join with weighted multiplicities" $ do
            let centers :: [((Int, Int, Int), String)]
                centers =
                    [ ((0, 0, 0), "common")
                    , ((0, 0, 0), "common")
                    , ((1, 0, 1), "rare")
                    ]
                lefts :: [(Int, String)]
                lefts = [(0, "left-a"), (0, "left-b"), (1, "left-c")]
                rights :: [(Int, String)]
                rights = [(0, "right-a"), (0, "right-a"), (1, "right-b")]
                keyed =
                    ECTAGen.forgetKey $
                        ECTAGen.innerJoin3Keyed
                            id
                            (ECTAGen.keyedElements fst centers)
                            (ECTAGen.keyedElements fst lefts)
                            (ECTAGen.keyedElements fst rights)
                accepted =
                    [ (center, left, right)
                    | center <- centers
                    , left <- lefts
                    , right <- rights
                    , let (expectedLeft, expectedRight, _) = fst center
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
            ECTAGen.pmf keyed `shouldBe` Right expected

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
                QC.forAll (ECTAGen.toGenWithRank joined) $ \(rank, value) ->
                    ECTAGen.unrank joined rank QC.=== Right value

        it "keeps fromGen opaque" $ do
            let opaque = ECTAGen.fromGen $ QC.elements [Alice, Bob]
                opaqueJoin =
                    ECTAGen.innerJoinOn id id opaque (ECTAGen.elements [Bob])
            ECTAGen.pmf opaqueJoin
                `shouldBe` Left ECTAGen.CannotInspectOpaqueGenerator
            ECTAGen.cardinality opaque
                `shouldBe` Left ECTAGen.CannotInspectOpaqueGenerator
            ECTAGen.unrank opaque 0
                `shouldBe` Left ECTAGen.CannotInspectOpaqueGenerator

        it "allows an opaque source to participate in a join" $
            let opaque = ECTAGen.fromGen $ QC.elements [Alice, Bob]
                opaqueJoin =
                    ECTAGen.innerJoinOn id id opaque (ECTAGen.elements [Bob])
             in QC.property
                    ( QC.forAll (ECTAGen.toGen opaqueJoin) $ \(left, right) ->
                        left QC.=== right
                    )
