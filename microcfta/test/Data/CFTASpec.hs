{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeApplications #-}

module Data.CFTASpec (spec) where

import Data.Proxy (Proxy (Proxy))
import qualified Data.Tree as Tree
import Data.Typeable (typeRep)
import GHC.Generics (Generic)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldMatchList, shouldSatisfy)

import Data.CFTA (Transition (Transition))
import qualified Data.CFTA as Automaton
import Data.CFTA.Constraint (equalityConstraint, noConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import qualified Data.CFTA.Generic as Datatype
import Data.CFTA.Path (path)

data State = Expression
    deriving (Eq, Ord, Show)

spec :: Spec
spec = do
    describe "explicit-state automata" $ do
        it "builds an ordinary recursive FTA" $
            case Automaton.mkFTA
                Expression
                [(Expression, [Transition "zero" [] noConstraint, Transition "add" [Expression, Expression] noConstraint])] of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    Automaton.accepts automaton (Tree.Node "zero" []) `shouldBe` True
                    Automaton.accepts
                        automaton
                        (Tree.Node "add" [Tree.Node "zero" [], Tree.Node "zero" []])
                        `shouldBe` True
                    Automaton.toTree automaton
                        `shouldBe` Tree.Node
                            (Left $ Automaton.Expanded [] Expression)
                            [ Tree.Node (Right $ Automaton.Transition "zero" [] noConstraint) []
                            , Tree.Node
                                (Right $ Automaton.Transition "add" [Expression, Expression] noConstraint)
                                [ Tree.Node (Left $ Automaton.Recursive [Automaton.ViewStep 1 0] Expression) []
                                , Tree.Node (Left $ Automaton.Recursive [Automaton.ViewStep 1 1] Expression) []
                                ]
                            ]
                    let functionLabels = Tree.flatten $ Automaton.toTree $ Automaton.mapConstraints (const not) automaton
                    [Automaton.transitionConstraint edge True | Right edge <- functionLabels] `shouldBe` [False, False]

        it "checks the path equalities of each constraint" $
            case Automaton.mkFTA
                (0 :: Int)
                [ (0, [Transition "p" [1, 1] (equalityConstraint $ mkEqConstraints [[path [0], path [1]]])])
                , (1, [Transition "a" [] noConstraint, Transition "b" [] noConstraint])
                ] of
                Left err -> expectationFailure $ show err
                Right pairs ->
                    map (Automaton.accepts pairs) [leafPair "a" "a", leafPair "a" "b"] `shouldBe` [True, False]

        it "constructs the ordinary product intersection" $ do
            let left = Automaton.mkFTA Expression [(Expression, [Transition "left" [] noConstraint, Transition "shared" [] noConstraint])]
                right = Automaton.mkFTA Expression [(Expression, [Transition "shared" [] noConstraint, Transition "right" [] noConstraint])]
            case (left, right) of
                (Right leftAutomaton, Right rightAutomaton) ->
                    case Automaton.intersect leftAutomaton rightAutomaton of
                        Left err -> expectationFailure $ show err
                        Right intersection -> do
                            let ordinary = Automaton.dropConstraints intersection
                            Automaton.accepts ordinary (Tree.Node "shared" []) `shouldBe` True
                            Automaton.accepts ordinary (Tree.Node "left" []) `shouldBe` False
                            Automaton.accepts ordinary (Tree.Node "right" []) `shouldBe` False
                (Left err, _) -> expectationFailure $ show err
                (_, Left err) -> expectationFailure $ show err

        it "lists accepted terms by depth" $
            case Automaton.mkFTA
                Expression
                [(Expression, [Transition "zero" [] noConstraint, Transition "add" [Expression, Expression] noConstraint])] of
                Left err -> expectationFailure $ show err
                Right expressions -> do
                    let zero = Tree.Node "zero" []
                        add left right = Tree.Node "add" [left, right]
                        pair = add zero zero
                    take 5 (Automaton.terms expressions)
                        `shouldBe` [zero, pair, add pair pair, add pair zero, add zero pair]
                    Automaton.terms (Automaton.boundDepth 2 expressions) `shouldBe` take 5 (Automaton.terms expressions)
                    Automaton.states (Automaton.mapStates show expressions) `shouldBe` ["Expression"]
                    -- A second "add" over a sub-language accepts the same terms by more runs.
                    case Automaton.mkFTA
                        (0 :: Int)
                        [ (0, [Transition "zero" [] noConstraint, Transition "add" [0, 0] noConstraint, Transition "add" [1, 1] noConstraint])
                        , (1, [Transition "zero" [] noConstraint])
                        ] of
                        Left err -> expectationFailure $ show err
                        Right ambiguous -> Automaton.terms (Automaton.boundDepth 2 ambiguous) `shouldMatchList` take 5 (Automaton.terms expressions)

    describe "derived datatype grammars" $ do
        it "accepts a type argument that grows and then stops" $
            -- From Grows Int the states are Grows Int, Int, Stop, Grows (Maybe Int),
            -- and Maybe Int: Stop always leads back to Grows (Maybe Int).
            fmap (Automaton.states . Datatype.datatypeFTA) (Datatype.deriveFTAWith @(Grows Int) (Datatype.domain @Int [0]))
                `shouldSatisfy` either (const False) ((== 5) . length)

        it "rejects a growth that the growth limit does not allow" $
            fmap
                (Automaton.states . Datatype.datatypeFTA)
                (Datatype.deriveFTAWithGrowthLimit @(Grows Int) 0 (Datatype.domain @Int [0]))
                `shouldBe` Left (Datatype.NonRegularRecursion 0 (typeRep $ Proxy @(Grows Int)) (typeRep $ Proxy @(Grows (Maybe Int))))

        it "rejects a type argument that grows without end" $
            case Datatype.deriveFTAWith @(Nested Int) (Datatype.domain @Int [0]) of
                Left (Datatype.NonRegularRecursion limit _ _) -> limit `shouldBe` Datatype.defaultGrowthLimit
                other -> expectationFailure $ "expected NonRegularRecursion, got " <> either show (const "a grammar") other

        it "accepts exactly the encodings of the datatype's values" $ do
            case Datatype.deriveFTAWith @(Maybe Shape) (Datatype.domain @Int [0, 1]) of
                Left err -> expectationFailure $ show err
                Right datatype -> do
                    let grammar = Datatype.datatypeFTA datatype
                        values = [Nothing, Just (Dot 0), Just (Box 1 (Dot 1))]
                    map (Automaton.accepts grammar . Datatype.encodeTerm) values `shouldBe` [True, True, True]
                    map (Datatype.decodeTerm . Datatype.encodeTerm) values `shouldBe` map Just values
                    Automaton.accepts grammar (Datatype.encodeTerm (Just (Dot 7))) `shouldBe` False
                    Automaton.cycleState grammar `shouldSatisfy` (/= Nothing)

-- | A type argument that grows once: 'Stop' leads back to a fixed larger type.
data Grows a = Grows a Stop | Stopped
    deriving (Eq, Show, Generic)

instance (Datatype.HasFTA a) => Datatype.HasFTA (Grows a)

-- | The fixed type that 'Grows' reaches.
newtype Stop = Stop (Grows (Maybe Int))
    deriving (Eq, Show, Generic)

instance Datatype.HasFTA Stop

-- | A nested datatype: every level grows the type argument.
data Nested a = Nested a (Nested (Maybe a)) | Flat
    deriving (Eq, Show, Generic)

instance (Datatype.HasFTA a) => Datatype.HasFTA (Nested a)

-- | A small recursive datatype for the derivation checks.
data Shape = Dot Int | Box Int Shape
    deriving (Eq, Show, Generic)

instance Datatype.HasFTA Shape

-- | The term p(left, right) over two leaves.
leafPair :: String -> String -> Tree.Tree String
leafPair left right = Tree.Node "p" [Tree.Node left [], Tree.Node right []]
