{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Data.CFTASpec (spec) where

import Control.Monad (forM_)
import Data.Functor.Identity (runIdentity)
import Data.Hashable (Hashable (..))
import Data.Monoid (Sum (..))
import qualified Data.Tree as Tree
import GHC.Generics (Generic)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldMatchList, shouldNotBe, shouldSatisfy)

import Data.CFTA (Transition (Transition), statesAt)
import qualified Data.CFTA as Automaton
import Data.CFTA.Constraint (Constraint (..))
import qualified Data.CFTA.Enumeration as Enumeration
import Data.CFTA.Equality.Constraint (EqConstraints (EmptyConstraints))
import qualified Data.CFTA.Generic as Datatype
import Data.CFTA.Interned (pathsMatching, requirePath)
import qualified Data.CFTA.Interned as Common
import Data.CFTA.Path (getPath, path)
import Data.CFTA.Template (Template (..), matchesTemplate, restrict, restrictFTA)

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
                    let functionLabels = Tree.flatten $ Automaton.toTree $ Automaton.mapConstraints (const not) automaton
                    [Automaton.transitionConstraint edge True | Right edge <- functionLabels] `shouldBe` [False, False]

        it "constructs the ordinary product intersection" $ do
            let left = Automaton.mkFTA Expression [(Expression, [Transition "left" [] (), Transition "shared" [] ()])]
                right = Automaton.mkFTA Expression [(Expression, [Transition "shared" [] (), Transition "right" [] ()])]
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
            case Automaton.mkFTA Expression [(Expression, [Transition "zero" [] (), Transition "add" [Expression, Expression] ()])] of
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
                        [(0, [Transition "zero" [] (), Transition "add" [0, 0] (), Transition "add" [1, 1] ()]), (1, [Transition "zero" [] ()])] of
                        Left err -> expectationFailure $ show err
                        Right ambiguous -> Automaton.terms (Automaton.boundDepth 2 ambiguous) `shouldMatchList` take 5 (Automaton.terms expressions)

        it "trims dead and unreachable states" $
            case Automaton.mkFTA
                (0 :: Int)
                [ (0, [Transition "f" [1, 2] (), Transition "leaf" [] ()])
                , (1, [Transition "s" [1] ()])
                , (2, [Transition "z" [] ()])
                , (3, [Transition "loop" [3] ()])
                ] of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    let trimmed = Automaton.trim automaton
                    Automaton.states trimmed `shouldBe` [0]
                    Automaton.transitionsFrom trimmed 0 `shouldBe` [Transition "leaf" [] ()]
                    Automaton.terms automaton `shouldBe` [Tree.Node "leaf" []]
                    acceptPlain (Common.fromFTA automaton) (Tree.Node "leaf" []) `shouldBe` True

    describe "common interned automaton engine" $ do
        it "recognizes and intersects unit-constrained languages" $ do
            let choices = Common.Node [Common.Edge "a" [], Common.Edge "b" []] :: Common.PlainNode String
                other = Common.Node [Common.Edge "b" [], Common.Edge "c" []] :: Common.PlainNode String
                shared = Common.intersect choices other
            map (acceptPlain shared) [Tree.Node "a" [], Tree.Node "b" [], Tree.Node "c" []]
                `shouldBe` [False, True, False]
            Common.intersect choices choices `shouldBe` choices

        it "imports a recursive explicit automaton as a Mu node" $ do
            case Automaton.mkFTA "nat" [("nat", [Transition "z" [] (), Transition "s" ["nat"] ()])] of
                Left err -> expectationFailure $ show err
                Right nat -> do
                    let imported = Common.fromFTA nat :: Common.PlainNode String
                    imported `shouldBe` Common.createMu (\self -> Common.Node [Common.Edge "z" [], Common.Edge "s" [self]])
                    Common.numNestedMu (Common.fromFTA (Automaton.boundDepth 2 nat) :: Common.PlainNode String) `shouldBe` 0
                    forM_ [0 .. 3] $ \depth -> do
                        Enumeration.terms (Common.boundDepth depth imported)
                            `shouldMatchList` Automaton.terms (Automaton.boundDepth depth nat)
                        Enumeration.plainTermsAtMost depth imported
                            `shouldBe` Automaton.terms (Automaton.boundDepth depth nat)

        it "imports mutually recursive states with nested binders" $ do
            let rows =
                    [ ("a", [Transition "leaf" [] (), Transition "f" ["b"] ()])
                    , ("b", [Transition "g" ["a", "b"] (), Transition "h" ["a"] ()])
                    ]
            case Automaton.mkFTA "a" rows of
                Left err -> expectationFailure $ show err
                Right graph -> do
                    let imported = Common.fromFTA graph :: Common.PlainNode String
                    Common.freeVars imported `shouldBe` mempty
                    forM_ [0 .. 4] $ \depth ->
                        Enumeration.terms (Common.boundDepth depth imported)
                            `shouldMatchList` Automaton.terms (Automaton.boundDepth depth graph)

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
            Common.acceptsWith acceptsAllowed onlyA (Tree.Node "a" []) `shouldBe` True
            Common.acceptsWith acceptsAllowed onlyB (Tree.Node "a" []) `shouldBe` False
            Common.intersect onlyA onlyB `shouldBe` Common.EmptyNode
            Common.intersect free onlyA `shouldBe` onlyA

        it "retains non-unit constraints in the explicit graph view" $ do
            let graph = Common.Node [Common.mkEdge "a" [] (Only "a")] :: Common.Node String Allowed
            case Common.toFTA graph of
                Left err -> expectationFailure $ show err
                Right view ->
                    map Automaton.transitionConstraint (Automaton.transitionsFrom view $ Automaton.initialState view)
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
            take 3 (Enumeration.plainTerms naturals) `shouldBe` take 3 terms
            Enumeration.plainTerms bounded `shouldBe` take 2 terms

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
                    let node = Common.fromFTA graph
                    acceptPlain node (Tree.Node "pair" [Tree.Node "leaf" [], Tree.Node "leaf" []]) `shouldBe` True
                    acceptPlain node (Tree.Node "pair" [Tree.Node "pair" [], Tree.Node "leaf" []]) `shouldBe` False
                    case Common.toFTA node of
                        Left err -> expectationFailure $ show err
                        Right view -> length (Automaton.states view) `shouldBe` 2

        it "reads, requires, and finds child-index paths" $ do
            let a = Common.Node [Common.Edge "a" []] :: Common.PlainNode String
                b = Common.Node [Common.Edge "b" []]
                graph = Common.Node [Common.Edge "leaf" [], Common.Edge "pair" [a, b]]
            getPath (path [1]) graph `shouldBe` b
            getPath (path [0]) (Common.union [graph, Common.Node [Common.Edge "pair" [b, a]]]) `shouldBe` Common.union [a, b]
            requirePath (path [0]) graph `shouldBe` Common.Node [Common.Edge "pair" [a, b]]
            pathsMatching (== b) graph `shouldBe` [path [1]]
            case Automaton.mkFTA
                (0 :: Int)
                [ (0, [Transition "pair" [1, 2] ()])
                , (1, [Transition "leaf" [] (), Transition "pair" [2, 1] ()])
                , (2, [Transition "leaf" [] ()])
                ] of
                Left err -> expectationFailure $ show err
                Right explicit -> do
                    let root = Transition "pair" [1, 2] ()
                    let below = statesAt (Automaton.transitionsFrom explicit)
                    below root (path [0]) `shouldBe` [1]
                    below root (path [0, 1]) `shouldBe` [1]
                    below root (path [1, 0]) `shouldBe` []

        it "removes an alternative that another alternative already accepts" $ do
            let leaf = Common.Node [Common.Edge "a" []] :: Common.PlainNode String
                both = Common.Node [Common.Edge "a" [], Common.Edge "b" []]
                redundant = Common.Node [Common.Edge "f" [leaf], Common.Edge "f" [both]]
            Common.edgeCount (Common.withoutRedundantEdges redundant) `shouldBe` 3
            acceptPlain (Common.withoutRedundantEdges redundant) (Tree.Node "f" [Tree.Node "a" []]) `shouldBe` True

    describe "templates" $
        it "restricts an automaton and an interned graph to the matching terms" $
            case Automaton.mkFTA Expression [(Expression, [Transition "zero" [] (), Transition "add" [Expression, Expression] ()])] of
                Left err -> expectationFailure $ show err
                Right expressions -> do
                    let template = TemplateNode "add" [TemplateNode "zero" [], Hole]
                        bounded = Automaton.boundDepth 2 expressions
                        expected = filter (matchesTemplate template) (Automaton.terms bounded)
                    length expected `shouldBe` 2
                    Automaton.terms (restrictFTA template bounded) `shouldMatchList` expected
                    Enumeration.plainTerms (restrict template (Common.fromFTA bounded)) `shouldBe` expected
                    -- The check constrains every "add" node, and the root "zero" passes it.
                    let accept _ transition term = pure (Automaton.transitionSymbol transition /= "add" || matchesTemplate template term)
                        zero = Tree.Node "zero" []
                        add left right = Tree.Node "add" [left, right]
                    runIdentity (Automaton.termsUpToM accept 2 expressions)
                        `shouldMatchList` [zero, add zero zero, add zero (add zero zero)]
                    runIdentity (Automaton.termsUpToM (\_ _ _ -> pure True) 2 expressions) `shouldBe` Automaton.terms bounded
                    -- The same check decides membership one term at a time.
                    map (runIdentity . Automaton.acceptsM accept expressions) [zero, add zero zero, add (add zero zero) zero]
                        `shouldBe` [True, True, False]
                    runIdentity (Automaton.acceptsM accept expressions (Tree.Node "mul" [zero, zero])) `shouldBe` False

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
    equalities _ = EmptyConstraints
    residual Anything = False
    residual _ = True

-- | Interpret the test constraint at one constructor.
acceptsAllowed :: Allowed -> Tree.Tree String -> Bool
acceptsAllowed Anything _ = True
acceptsAllowed (Only expected) (Tree.Node actual _) = expected == actual
acceptsAllowed NothingAllowed _ = False

-- | Recognize an ordinary interned automaton.
acceptPlain :: Common.PlainNode String -> Tree.Tree String -> Bool
acceptPlain = Common.acceptsWith (\() _ -> True)
