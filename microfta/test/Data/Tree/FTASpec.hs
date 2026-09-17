{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Data.Tree.FTASpec (spec) where

import Data.Hashable (Hashable (..))
import Data.Monoid (Sum (..))
import qualified Data.Tree as Tree
import GHC.Generics (Generic)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldNotBe, shouldSatisfy)

import Data.Tree.FTA (Transition (Transition))
import qualified Data.Tree.FTA as Automaton
import Data.Tree.FTA.Constraint (Constraint (..))
import qualified Data.Tree.FTA.Generic as Datatype
import qualified Data.Tree.FTA.Interned as Common

data State = Expression
    deriving (Eq, Ord, Show)

spec :: Spec
spec = do
    describe "explicit-state automata" $ do
        it "builds an ordinary recursive FTA" $
            case Automaton.mkFTA
                Expression
                [(Expression, [Transition "zero" [] (), Transition "add" [Expression, Expression] ()])] of
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
                            [ Tree.Node (Right $ Automaton.Transition "zero" [] ()) []
                            , Tree.Node
                                (Right $ Automaton.Transition "add" [Expression, Expression] ())
                                [ Tree.Node (Left $ Automaton.Recursive [(1, 0)] Expression) []
                                , Tree.Node (Left $ Automaton.Recursive [(1, 1)] Expression) []
                                ]
                            ]
                    let functionLabels = Tree.flatten $ Automaton.toTree $ Automaton.mapGuards (const not) automaton
                    [Automaton.transitionGuard edge True | Right edge <- functionLabels] `shouldBe` [False, False]

        it "constructs the ordinary product intersection" $ do
            let left = Automaton.mkFTA Expression [(Expression, [Transition "left" [] (), Transition "shared" [] ()])]
                right = Automaton.mkFTA Expression [(Expression, [Transition "shared" [] (), Transition "right" [] ()])]
            case (left, right) of
                (Right leftAutomaton, Right rightAutomaton) ->
                    case Automaton.intersect leftAutomaton rightAutomaton of
                        Left err -> expectationFailure $ show err
                        Right intersection -> do
                            let ordinary = Automaton.stripGuards intersection
                            Automaton.accepts ordinary (Tree.Node "shared" []) `shouldBe` True
                            Automaton.accepts ordinary (Tree.Node "left" []) `shouldBe` False
                            Automaton.accepts ordinary (Tree.Node "right" []) `shouldBe` False
                (Left err, _) -> expectationFailure $ show err
                (_, Left err) -> expectationFailure $ show err

    describe "common interned automaton engine" $ do
        it "recognizes and intersects unit-constrained languages" $ do
            let choices = Common.Node [Common.Edge "a" [], Common.Edge "b" []] :: Common.PlainNode String
                other = Common.Node [Common.Edge "b" [], Common.Edge "c" []] :: Common.PlainNode String
                shared = Common.intersect choices other
            map (acceptPlain shared) [Tree.Node "a" [], Tree.Node "b" [], Tree.Node "c" []]
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
                terms = take 9 $ iterate (\term -> Tree.Node "succ" [term]) (Tree.Node "zero" [])
            map (acceptPlain shared) terms `shouldBe` map even [0 :: Int .. 8]
            let recursiveNodes = Common.crush (\case Common.InternedMu _ -> Sum (1 :: Int); _ -> Sum 0)
            getSum (recursiveNodes $ Common.Node [Common.Edge "pair" [naturals, naturals]]) `shouldBe` 1
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
            Common.nodeRepresentsWith acceptsAllowed onlyA (Tree.Node "a" []) `shouldBe` True
            Common.nodeRepresentsWith acceptsAllowed onlyB (Tree.Node "a" []) `shouldBe` False
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
            fmap (length . Tree.flatten) (Common.toTree $ Common.union [leaf, unary]) `shouldBe` Right 5

        it "rejects an open recursive node in an explicit graph view" $ do
            let open = Common.Rec (Common.RecUnint 0) :: Common.PlainNode String
            Common.toFTA open `shouldBe` Left Common.OpenNode
            Common.toTree open `shouldBe` Left Common.OpenNode

        it "unfolds a recursive node a bounded number of times and refolds it" $ do
            let naturals = Common.createMu $ \rec ->
                    Common.Node [Common.Edge "zero" [], Common.Edge "succ" [rec]] :: Common.PlainNode String
                terms = take 4 $ iterate (\term -> Tree.Node "succ" [term]) (Tree.Node "zero" [])
                bounded = Common.unfoldBounded 2 naturals
            map (acceptPlain bounded) terms `shouldBe` [True, True, False, False]
            Common.refold (Common.unfoldOuterRec naturals) `shouldBe` naturals

        it "imports an acyclic explicit graph and exposes it again unchanged" $ do
            let rows =
                    [ (0 :: Int, [Transition "pair" [1, 1] (), Transition "leaf" [] ()])
                    , (1, [Transition "leaf" [] ()])
                    ]
            case Automaton.mkFTA 0 rows of
                Left err -> expectationFailure $ show err
                Right graph -> do
                    Tree.flatten (Automaton.toTree graph)
                        `shouldBe` [ Left $ Automaton.Expanded [] 0
                                   , Right $ Automaton.Transition "pair" [1, 1] ()
                                   , Left $ Automaton.Expanded [(0, 0)] 1
                                   , Right $ Automaton.Transition "leaf" [] ()
                                   , Left $ Automaton.Shared [(0, 1)] 1
                                   , Right $ Automaton.Transition "leaf" [] ()
                                   ]
                    case Common.fromFTA graph of
                        Left err -> expectationFailure $ show err
                        Right node -> do
                            acceptPlain node (Tree.Node "pair" [Tree.Node "leaf" [], Tree.Node "leaf" []]) `shouldBe` True
                            acceptPlain node (Tree.Node "pair" [Tree.Node "pair" [], Tree.Node "leaf" []]) `shouldBe` False
                            case Common.toFTA node of
                                Left err -> expectationFailure $ show err
                                Right view -> length (Automaton.states view) `shouldBe` 2

        it "removes an alternative that another alternative already accepts" $ do
            let leaf = Common.Node [Common.Edge "a" []] :: Common.PlainNode String
                both = Common.Node [Common.Edge "a" [], Common.Edge "b" []]
                redundant = Common.Node [Common.Edge "f" [leaf], Common.Edge "f" [both]]
            Common.edgeCount (Common.withoutRedundantEdges redundant) `shouldBe` 3
            acceptPlain (Common.withoutRedundantEdges redundant) (Tree.Node "f" [Tree.Node "a" []]) `shouldBe` True

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
acceptsAllowed :: Allowed -> Tree.Tree String -> Bool
acceptsAllowed Anything _ = True
acceptsAllowed (Only expected) (Tree.Node actual _) = expected == actual
acceptsAllowed NothingAllowed _ = False

-- | Recognize an ordinary interned automaton.
acceptPlain :: Common.PlainNode String -> Tree.Tree String -> Bool
acceptPlain = Common.nodeRepresentsWith (\() _ -> True)
