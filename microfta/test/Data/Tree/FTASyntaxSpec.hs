{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeApplications #-}

module Data.Tree.FTASyntaxSpec (spec) where

import Data.Hashable (Hashable (..))
import qualified Data.Tree as Tree
import GHC.Generics (Generic)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldNotBe, shouldSatisfy)

import qualified Data.Tree.FTA as Automaton
import Data.Tree.FTA.Constraint (Constraint (..))
import qualified Data.Tree.FTA.Generic as Datatype
import qualified Data.Tree.FTA.Interned as Common
import qualified Data.Tree.FTA.Syntax as FTA
import Data.Tree.Term (Term (Term))

data State = Expression
    deriving (Eq, Ord, Show)

spec :: Spec
spec = do
    describe "shared FTA construction syntax" $ do
        it "builds an ordinary recursive FTA without unit annotations" $
            case FTA.automaton
                Expression
                [ FTA.row
                    Expression
                    [ FTA.transition "zero" []
                    , FTA.transition "add" [Expression, Expression]
                    ]
                ] of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    Automaton.accepts automaton (Term "zero" []) `shouldBe` True
                    Automaton.accepts
                        automaton
                        (Term "add" [Term "zero" [], Term "zero" []])
                        `shouldBe` True
                    Automaton.toTree automaton
                        `shouldBe` Tree.Node
                            "state Expression"
                            [ Tree.Node "\"zero\" [()]" []
                            , Tree.Node "\"add\" [()]" [Tree.Node "mu Expression" [], Tree.Node "mu Expression" []]
                            ]

        it "constructs the ordinary product intersection" $ do
            let left =
                    FTA.automaton
                        Expression
                        [FTA.row Expression [FTA.transition "left" [], FTA.transition "shared" []]]
                right =
                    FTA.automaton
                        Expression
                        [FTA.row Expression [FTA.transition "shared" [], FTA.transition "right" []]]
            case (left, right) of
                (Right leftAutomaton, Right rightAutomaton) ->
                    case Automaton.intersect leftAutomaton rightAutomaton of
                        Left err -> expectationFailure $ show err
                        Right intersection -> do
                            let ordinary = Automaton.stripGuards intersection
                            Automaton.accepts ordinary (Term "shared" []) `shouldBe` True
                            Automaton.accepts ordinary (Term "left" []) `shouldBe` False
                            Automaton.accepts ordinary (Term "right" []) `shouldBe` False
                (Left err, _) -> expectationFailure $ show err
                (_, Left err) -> expectationFailure $ show err

    describe "common interned automaton engine" $ do
        it "recognizes and intersects unit-constrained languages" $ do
            let choices = Common.Node [Common.Edge "a" [], Common.Edge "b" []] :: Common.PlainNode String
                other = Common.Node [Common.Edge "b" [], Common.Edge "c" []] :: Common.PlainNode String
                shared = Common.intersect choices other
            map (acceptPlain shared) [Term "a" [], Term "b" [], Term "c" []]
                `shouldBe` [False, True, False]
            Common.intersect choices choices `shouldBe` choices

        it "preserves recursive intersections and the explicit graph view" $ do
            let naturals = Common.createMu $ \rec ->
                    Common.Node
                        [Common.Edge "zero" [], Common.Edge "succ" [rec]]
                evens = Common.createMu $ \rec ->
                    Common.Node
                        [Common.Edge "zero" [], Common.Edge "succ" [Common.Node [Common.Edge "succ" [rec]]]]
                shared = Common.intersect naturals evens :: Common.PlainNode String
                terms = take 9 $ iterate (\term -> Term "succ" [term]) (Term "zero" [])
            map (acceptPlain shared) terms `shouldBe` map even [0 :: Int .. 8]
            case Common.toFTA shared of
                Left err -> expectationFailure $ show err
                Right graph -> map (Automaton.accepts graph) terms `shouldBe` map even [0 :: Int .. 8]

        it "keeps a large shared graph compact through traversal" $ do
            let leaf = Common.Node [Common.Edge "leaf" []] :: Common.PlainNode String
                graph = iterate (\child -> Common.Node [Common.Edge "pair" [child, child]]) leaf !! 24
            Common.nodeCount graph `shouldBe` 25
            Common.edgeCount graph `shouldBe` 25
            Common.mapNodes id graph `shouldBe` graph
            Common.union [graph, graph] `shouldBe` graph
            fmap (length . Tree.flatten) (Common.toTree graph) `shouldBe` Right 74

        it "keeps different constraint types and values distinct in the caches" $ do
            let plain = Common.Node [Common.Edge "a" []] :: Common.PlainNode String
                free = Common.Node [Common.Edge "a" []] :: Common.Node String Allowed
                onlyA = Common.Node [Common.mkEdge "a" [] (Only "a")]
                onlyB = Common.Node [Common.mkEdge "a" [] (Only "b")]
            Common.nodeIdentity plain `shouldNotBe` Common.nodeIdentity free
            onlyA `shouldNotBe` onlyB
            Common.nodeRepresentsWith acceptsAllowed onlyA (Term "a" []) `shouldBe` True
            Common.nodeRepresentsWith acceptsAllowed onlyB (Term "a" []) `shouldBe` False
            Common.intersect onlyA onlyB `shouldBe` Common.EmptyNode
            Common.intersect free onlyA `shouldBe` onlyA

        it "retains non-unit constraints in the explicit graph view" $ do
            let graph = Common.Node [Common.mkEdge "a" [] (Only "a")] :: Common.Node String Allowed
            case Common.toFTA graph of
                Left err -> expectationFailure $ show err
                Right view ->
                    map Automaton.transitionGuard (Automaton.transitionsFrom view $ Automaton.initialState view)
                        `shouldBe` [Only "a"]

        it "does not intersect constructors with different arities" $ do
            let leaf = Common.Node [Common.Edge "same" []] :: Common.PlainNode String
                unary = Common.Node [Common.Edge "same" [leaf]]
            Common.intersect leaf unary `shouldBe` Common.EmptyNode

        it "rejects an open recursive node in an explicit graph view" $ do
            let open = Common.Rec (Common.RecUnint 0) :: Common.PlainNode String
            Common.toFTA open `shouldBe` Left Common.OpenNode
            Common.toTree open `shouldBe` Left Common.OpenNode

        it "unfolds a recursive node a bounded number of times and refolds it" $ do
            let naturals = Common.createMu $ \rec ->
                    Common.Node [Common.Edge "zero" [], Common.Edge "succ" [rec]] :: Common.PlainNode String
                terms = take 4 $ iterate (\term -> Term "succ" [term]) (Term "zero" [])
                bounded = Common.unfoldBounded 2 naturals
            map (acceptPlain bounded) terms `shouldBe` [True, True, False, False]
            Common.refold (Common.unfoldOuterRec naturals) `shouldBe` naturals

        it "imports an acyclic explicit graph and exposes it again unchanged" $ do
            let rows =
                    [ FTA.row (0 :: Int) [FTA.transition "pair" [1, 1], FTA.transition "leaf" []]
                    , FTA.row 1 [FTA.transition "leaf" []]
                    ]
            case FTA.automaton 0 rows of
                Left err -> expectationFailure $ show err
                Right graph -> do
                    Tree.flatten (Automaton.toTree graph)
                        `shouldBe` ["state 0", "\"pair\" [()]", "state 1", "\"leaf\" [()]", "ref 1", "\"leaf\" [()]"]
                    case Common.fromFTA graph of
                        Left err -> expectationFailure $ show err
                        Right node -> do
                            acceptPlain node (Term "pair" [Term "leaf" [], Term "leaf" []]) `shouldBe` True
                            acceptPlain node (Term "pair" [Term "pair" [], Term "leaf" []]) `shouldBe` False
                            case Common.toFTA node of
                                Left err -> expectationFailure $ show err
                                Right view -> length (Automaton.states view) `shouldBe` 2

        it "removes an alternative that another alternative already accepts" $ do
            let leaf = Common.Node [Common.Edge "a" []] :: Common.PlainNode String
                both = Common.Node [Common.Edge "a" [], Common.Edge "b" []]
                redundant = Common.Node [Common.Edge "f" [leaf], Common.Edge "f" [both]]
            Common.edgeCount (Common.withoutRedundantEdges redundant) `shouldBe` 3
            acceptPlain (Common.withoutRedundantEdges redundant) (Term "f" [Term "a" []]) `shouldBe` True

    describe "derived datatype grammars" $ do
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

-- | A small recursive datatype for the derivation checks.
data Shape = Dot Int | Box Int Shape
    deriving (Eq, Show, Generic)

instance Datatype.HasFTA Shape

-- | A separate finite constraint theory used to test the common engine.
data Allowed = Anything | Only String | NothingAllowed
    deriving (Eq, Show)

-- | Force hash collisions so equality and runtime type checks are exercised.
instance Hashable Allowed where
    hashWithSalt salt _ = salt

instance Constraint Allowed where
    noConstraint = Anything
    conjoinConstraints Anything right = right
    conjoinConstraints left Anything = left
    conjoinConstraints left right
        | left == right = left
        | otherwise = NothingAllowed
    contradictory NothingAllowed = True
    contradictory _ = False

-- | Interpret the test constraint at one constructor.
acceptsAllowed :: Allowed -> Term String -> Bool
acceptsAllowed Anything _ = True
acceptsAllowed (Only expected) (Term actual _) = expected == actual
acceptsAllowed NothingAllowed _ = False

-- | Recognize an ordinary interned automaton.
acceptPlain :: Common.PlainNode String -> Term String -> Bool
acceptPlain = Common.nodeRepresentsWith (\() _ -> True)
