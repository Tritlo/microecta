{-# LANGUAGE ApplicativeDo #-}

module Data.ECTA.GenSpec (spec) where

import Data.Ratio ((%))
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldNotBe)
import qualified Test.QuickCheck as QC

import Data.ECTA (Node (Node))
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
    describe "ECTAGen.innerJoinOn" $ do
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

        it "keeps fromGen opaque" $ do
            let opaque = ECTAGen.fromGen $ QC.elements [Alice, Bob]
                opaqueJoin =
                    ECTAGen.innerJoinOn id id opaque (ECTAGen.elements [Bob])
            ECTAGen.pmf opaqueJoin
                `shouldBe` Left ECTAGen.CannotInspectOpaqueGenerator

        it "allows an opaque source to participate in a join" $
            let opaque = ECTAGen.fromGen $ QC.elements [Alice, Bob]
                opaqueJoin =
                    ECTAGen.innerJoinOn id id opaque (ECTAGen.elements [Bob])
             in QC.property
                    ( QC.forAll (ECTAGen.toGen opaqueJoin) $ \(left, right) ->
                        left QC.=== right
                    )
