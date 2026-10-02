{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Data.CFTASpec (spec) where

import Control.Monad (forM_)
import Data.Functor.Identity (runIdentity)
import Data.Monoid (Sum (..))
import Data.Proxy (Proxy (Proxy))
import qualified Data.Tree as Tree
import Data.Typeable (typeRep)
import GHC.Generics (Generic)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldMatchList, shouldNotBe, shouldSatisfy)

import Data.CFTA (Transition (Transition), statesAt)
import qualified Data.CFTA as Automaton
import Data.CFTA.Constraint (Guard (..), equalityConstraint, noConstraint, residual, semanticConstraint)
import qualified Data.CFTA.Enumeration as Enumeration
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import qualified Data.CFTA.Generic as Datatype
import Data.CFTA.Interned (pathsMatching, requirePath)
import qualified Data.CFTA.Interned as Common
import Data.CFTA.Path (getPath, path)
import qualified Data.CFTA.Simple as Simple
import Data.CFTA.Template (Template (..), matchesTemplate, restrict, restrictFTA)

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
                                [ Tree.Node (Left $ Automaton.Recursive [(1, 0)] Expression) []
                                , Tree.Node (Left $ Automaton.Recursive [(1, 1)] Expression) []
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

        it "trims dead and unreachable states" $
            case Automaton.mkFTA
                (0 :: Int)
                [ (0, [Transition "f" [1, 2] noConstraint, Transition "leaf" [] noConstraint])
                , (1, [Transition "s" [1] noConstraint])
                , (2, [Transition "z" [] noConstraint])
                , (3, [Transition "loop" [3] noConstraint])
                ] of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    let trimmed = Automaton.trim automaton
                    Automaton.states trimmed `shouldBe` [0]
                    Automaton.transitionsFrom trimmed 0 `shouldBe` [Transition "leaf" [] noConstraint]
                    Automaton.terms automaton `shouldBe` [Tree.Node "leaf" []]
                    acceptPlain (Common.fromFTA automaton) (Tree.Node "leaf" []) `shouldBe` True

    describe "common interned automaton engine" $ do
        it "recognizes and intersects unit-constrained languages" $ do
            let choices = Common.Node [Common.Edge "a" [], Common.Edge "b" []] :: Common.Node String
                other = Common.Node [Common.Edge "b" [], Common.Edge "c" []] :: Common.Node String
                shared = Common.intersect choices other
            map (acceptPlain shared) [Tree.Node "a" [], Tree.Node "b" [], Tree.Node "c" []]
                `shouldBe` [False, True, False]
            Common.intersect choices choices `shouldBe` choices

        it "imports a recursive explicit automaton as a Mu node" $ do
            case Automaton.mkFTA "nat" [("nat", [Transition "z" [] noConstraint, Transition "s" ["nat"] noConstraint])] of
                Left err -> expectationFailure $ show err
                Right nat -> do
                    let imported = Common.fromFTA nat :: Common.Node String
                    imported `shouldBe` Common.createMu (\self -> Common.Node [Common.Edge "z" [], Common.Edge "s" [self]])
                    Common.numNestedMu (Common.fromFTA (Automaton.boundDepth 2 nat) :: Common.Node String) `shouldBe` 0
                    forM_ [0 .. 3] $ \depth -> do
                        Enumeration.terms (Common.boundDepth depth imported)
                            `shouldMatchList` Automaton.terms (Automaton.boundDepth depth nat)
                        Enumeration.plainTermsAtMost depth imported
                            `shouldBe` Automaton.terms (Automaton.boundDepth depth nat)
                    take 3 (Enumeration.plainTermsAtMost maxBound imported) `shouldBe` take 3 (Enumeration.plainTerms imported)

        it "substitutes the variable of each Mu by itself as the identity" $ do
            let nested =
                    Common.createMu $ \outer ->
                        Common.Node
                            [Common.Edge "f" [Common.createMu $ \inner -> Common.Node [Common.Edge "g" [outer, inner], Common.Edge "a" []]]]
                pair = Common.createMu $ \self -> Common.Node [Common.Edge "p" [self, nested], Common.Edge "b" []]
                mus node = case node of
                    Common.InternedMu mu -> mu : mus (Common.internedMuBody mu)
                    Common.InternedNode inner -> concat [mus child | edge <- Common.internedNodeEdges inner, child <- Common.edgeChildren edge]
                    _ -> []
            forM_ [nested, pair :: Common.Node String] $ \node -> do
                null (mus node) `shouldBe` False
                forM_ (mus node) $ \mu -> do
                    let self = Common.RecInt (Common.internedMuId mu)
                    Common.substFree self (Common.Rec self) (Common.internedMuBody mu) `shouldBe` Common.internedMuBody mu

        it "imports mutually recursive states with nested binders" $ do
            let rows =
                    [ ("a", [Transition "leaf" [] noConstraint, Transition "f" ["b"] noConstraint])
                    , ("b", [Transition "g" ["a", "b"] noConstraint, Transition "h" ["a"] noConstraint])
                    ]
            case Automaton.mkFTA "a" rows of
                Left err -> expectationFailure $ show err
                Right graph -> do
                    let imported = Common.fromFTA graph :: Common.Node String
                    Common.freeVars imported `shouldBe` mempty
                    forM_ [0 .. 4] $ \depth ->
                        Enumeration.terms (Common.boundDepth depth imported)
                            `shouldMatchList` Automaton.terms (Automaton.boundDepth depth graph)

        it "binds each state of a strongly connected component at most once on a path" $
            forM_ [1 .. 4] $ \size -> do
                -- Every state has a leaf and an edge to every state.
                let rows =
                        [ ( state
                          , Transition "leaf" [] noConstraint : [Transition ("to" <> show next) [next] noConstraint | next <- [0 .. size - 1]]
                          )
                        | state <- [0 .. size - 1 :: Int]
                        ]
                case Automaton.mkFTA 0 rows of
                    Left err -> expectationFailure $ show err
                    Right graph -> do
                        let imported = Common.fromFTA graph :: Common.Node String
                        Common.numNestedMu imported `shouldBe` size
                        forM_ [0 .. 2] $ \depth ->
                            Enumeration.terms (Common.boundDepth depth imported)
                                `shouldMatchList` Automaton.terms (Automaton.boundDepth depth graph)

        it "preserves recursive intersections and the explicit graph view" $ do
            let naturals = Common.createMu $ \rec ->
                    Common.Node
                        [Common.Edge "zero" [], Common.Edge "succ" [rec]]
                evens = Common.createMu $ \rec ->
                    Common.Node
                        [Common.Edge "zero" [], Common.Edge "succ" [Common.Node [Common.Edge "succ" [rec]]]]
                shared = Common.intersect naturals evens :: Common.Node String
                terms = take 9 $ iterate (\term -> Tree.Node "succ" [term]) (Tree.Node "zero" [])
            map (acceptPlain shared) terms `shouldBe` map even [0 :: Int .. 8]
            let recursiveNodes = Common.crush (\case Common.InternedMu _ -> Sum (1 :: Int); _ -> Sum 0)
            getSum (recursiveNodes $ Common.Node [Common.Edge "pair" [naturals, naturals]]) `shouldBe` 1
            case Common.toFTA shared of
                Left err -> expectationFailure $ show err
                Right graph -> map (Automaton.accepts graph) terms `shouldBe` map even [0 :: Int .. 8]

        it "keeps a large shared graph compact through traversal" $ do
            let leaf = Common.Node [Common.Edge "leaf" []] :: Common.Node String
                graph = iterate (\child -> Common.Node [Common.Edge "pair" [child, child]]) leaf !! 24
            Common.nodeCount graph `shouldBe` 25
            Common.edgeCount graph `shouldBe` 25
            Common.mapNodes id graph `shouldBe` graph
            Common.union [graph, graph] `shouldBe` graph
            fmap (length . Tree.flatten) (Common.toTree graph) `shouldBe` Right 74

        it "keeps different constraint values distinct in the caches" $ do
            let plain = Common.Node [Common.Edge "a" []] :: Common.Node String
                guarded guard = Common.Node [Common.mkEdge "a" [] (semanticConstraint guard)] :: Common.Node String
                same = guarded $ Same (path []) (path [])
                entails = guarded $ Entails (path []) (path [])
            Common.nodeIdentity plain `shouldNotBe` Common.nodeIdentity same
            same `shouldNotBe` entails
            Common.acceptsWith (\constraint _ -> not $ residual constraint) same (Tree.Node "a" []) `shouldBe` False
            Common.acceptsWith (\constraint _ -> not $ residual constraint) plain (Tree.Node "a" []) `shouldBe` True
            Common.intersect plain same `shouldBe` same
            guarded Bottom `shouldBe` Common.EmptyNode

        it "retains constraints in the explicit graph view" $ do
            let constraint = semanticConstraint $ Same (path []) (path [])
                graph = Common.Node [Common.mkEdge "a" [] constraint] :: Common.Node String
            case Common.toFTA graph of
                Left err -> expectationFailure $ show err
                Right view ->
                    map Automaton.transitionConstraint (Automaton.transitionsFrom view $ Automaton.initialState view)
                        `shouldBe` [constraint]

        it "does not intersect constructors with different arities" $ do
            let leaf = Common.Node [Common.Edge "same" []] :: Common.Node String
                unary = Common.Node [Common.Edge "same" [leaf]]
            Common.intersect leaf unary `shouldBe` Common.EmptyNode
            fmap (length . Tree.flatten) (Common.toTree $ Common.union [leaf, unary]) `shouldBe` Right 5

        it "rejects an open recursive node in an explicit graph view" $ do
            let open = Common.Rec (Common.RecUnint 0) :: Common.Node String
            Common.toFTA open `shouldBe` Left Common.OpenNode
            Common.toTree open `shouldBe` Left Common.OpenNode

        it "unfolds a recursive node a bounded number of times and refolds it" $ do
            let naturals = Common.createMu $ \rec ->
                    Common.Node [Common.Edge "zero" [], Common.Edge "succ" [rec]] :: Common.Node String
                terms = take 4 $ iterate (\term -> Tree.Node "succ" [term]) (Tree.Node "zero" [])
                bounded = Common.unfoldBounded 2 naturals
            map (acceptPlain bounded) terms `shouldBe` [True, True, False, False]
            Common.refold (Common.unfoldOuterRec naturals) `shouldBe` naturals
            take 3 (Enumeration.plainTerms naturals) `shouldBe` take 3 terms
            Enumeration.plainTerms bounded `shouldBe` take 2 terms

        it "imports an acyclic explicit graph and exposes it again unchanged" $ do
            let rows =
                    [ (0 :: Int, [Transition "pair" [1, 1] noConstraint, Transition "leaf" [] noConstraint])
                    , (1, [Transition "leaf" [] noConstraint])
                    ]
            case Automaton.mkFTA 0 rows of
                Left err -> expectationFailure $ show err
                Right graph -> do
                    Tree.flatten (Automaton.toTree graph)
                        `shouldBe` [ Left $ Automaton.Expanded [] 0
                                   , Right $ Automaton.Transition "pair" [1, 1] noConstraint
                                   , Left $ Automaton.Expanded [(0, 0)] 1
                                   , Right $ Automaton.Transition "leaf" [] noConstraint
                                   , Left $ Automaton.Shared [(0, 1)] 1
                                   , Right $ Automaton.Transition "leaf" [] noConstraint
                                   ]
                    let node = Common.fromFTA graph
                    acceptPlain node (Tree.Node "pair" [Tree.Node "leaf" [], Tree.Node "leaf" []]) `shouldBe` True
                    acceptPlain node (Tree.Node "pair" [Tree.Node "pair" [], Tree.Node "leaf" []]) `shouldBe` False
                    case Common.toFTA node of
                        Left err -> expectationFailure $ show err
                        Right view -> length (Automaton.states view) `shouldBe` 2

        it "reads, requires, and finds child-index paths" $ do
            let a = Common.Node [Common.Edge "a" []] :: Common.Node String
                b = Common.Node [Common.Edge "b" []]
                graph = Common.Node [Common.Edge "leaf" [], Common.Edge "pair" [a, b]]
            getPath (path [1]) graph `shouldBe` b
            getPath (path [0]) (Common.union [graph, Common.Node [Common.Edge "pair" [b, a]]]) `shouldBe` Common.union [a, b]
            requirePath (path [0]) graph `shouldBe` Common.Node [Common.Edge "pair" [a, b]]
            requirePath (path [-1]) graph `shouldBe` Common.EmptyNode
            pathsMatching (== b) graph `shouldBe` [path [1]]
            case Automaton.mkFTA
                (0 :: Int)
                [ (0, [Transition "pair" [1, 2] noConstraint])
                , (1, [Transition "leaf" [] noConstraint, Transition "pair" [2, 1] noConstraint])
                , (2, [Transition "leaf" [] noConstraint])
                ] of
                Left err -> expectationFailure $ show err
                Right explicit -> do
                    let root = Transition "pair" [1, 2] noConstraint
                    let below = statesAt (Automaton.transitionsFrom explicit)
                    below root (path [0]) `shouldBe` [1]
                    below root (path [0, 1]) `shouldBe` [1]
                    below root (path [1, 0]) `shouldBe` []

        it "removes an alternative that another alternative already accepts" $ do
            let leaf = Common.Node [Common.Edge "a" []] :: Common.Node String
                both = Common.Node [Common.Edge "a" [], Common.Edge "b" []]
                redundant = Common.Node [Common.Edge "f" [leaf], Common.Edge "f" [both]]
            Common.edgeCount (Common.withoutRedundantEdges redundant) `shouldBe` 3
            acceptPlain (Common.withoutRedundantEdges redundant) (Tree.Node "f" [Tree.Node "a" []]) `shouldBe` True

        it "removes a subsumed alternative of a recursive node and keeps its language" $ do
            let leaf = Common.Node [Common.Edge "a" []] :: Common.Node String
                -- The last pair accepts a subset of the terms of the first pair.
                subsumed = Common.createMu $ \self ->
                    Common.Node [Common.Edge "a" [], Common.Edge "pair" [self, self], Common.Edge "pair" [self, leaf]]
                -- The two pairs share only some terms, so both stay.
                overlapping = Common.createMu $ \self ->
                    Common.Node [Common.Edge "a" [], Common.Edge "pair" [leaf, self], Common.Edge "pair" [self, leaf]]
                reduced = Common.withoutRedundantEdges subsumed
            reduced `shouldBe` Common.createMu (\self -> Common.Node [Common.Edge "a" [], Common.Edge "pair" [self, self]])
            Common.withoutRedundantEdges overlapping `shouldBe` overlapping
            forM_ [0 .. 4] $ \depth ->
                Enumeration.terms (Common.boundDepth depth reduced)
                    `shouldMatchList` Enumeration.terms (Common.boundDepth depth subsumed)

    describe "templates" $
        it "restricts an automaton and an interned graph to the matching terms" $
            case Automaton.mkFTA
                Expression
                [(Expression, [Transition "zero" [] noConstraint, Transition "add" [Expression, Expression] noConstraint])] of
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
                    -- No junk: every term of the grammar is the encoding of a value.
                    let roundTrips term = fmap Datatype.encodeTerm (Datatype.decodeTerm term :: Maybe (Maybe Shape)) == Just term
                    case Simple.termsUpTo 3 grammar of
                        Nothing -> expectationFailure "the grammar has a constraint"
                        Just grammarTerms -> do
                            length grammarTerms `shouldSatisfy` (> 3)
                            filter (not . roundTrips) grammarTerms `shouldBe` []

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

-- | Recognize an ordinary interned automaton.
acceptPlain :: Common.Node String -> Tree.Tree String -> Bool
acceptPlain = Common.acceptsWith (\_ _ -> True)

-- | The term p(left, right) over two leaves.
leafPair :: String -> String -> Tree.Tree String
leafPair left right = Tree.Node "p" [Tree.Node left [], Tree.Node right []]
