{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Data.CFTASpec (spec) where

import Control.Monad (forM_)
import Data.Bits (testBit)
import Data.Monoid (Sum (..))
import Data.Proxy (Proxy (Proxy))
import qualified Data.Tree as Tree
import Data.Typeable (typeRep)
import GHC.Generics (Generic)
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldMatchList, shouldNotBe, shouldSatisfy)

import Data.CFTA (Transition (Transition), statesAt)
import qualified Data.CFTA as Automaton
import Data.CFTA.Constraint (Guard (..), equalitiesHold, equalityConstraint, noConstraint, residual, semanticConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import qualified Data.CFTA.Generic as Datatype
import Data.CFTA.Interned (pathsMatching, requirePath)
import qualified Data.CFTA.Interned as Common
import Data.CFTA.Path (getPath, path)

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

        it "imports empty and nonproductive recursive roots as closed empty nodes" $
            forM_ [[], [Transition "loop" [0] noConstraint]] $ \edges ->
                case Automaton.mkFTA (0 :: Int) [(0, edges)] of
                    Left err -> expectationFailure $ show err
                    Right graph -> do
                        let imported = Common.fromFTA graph :: Common.Node String
                        imported `shouldBe` Common.EmptyNode
                        Common.freeVars imported `shouldBe` mempty

        it "preserves equality constraints beneath nested recursive binders" $ do
            let same = equalityConstraint $ mkEqConstraints [[path [0], path [1]]]
                rows =
                    [ (0 :: Int, [Transition "z" [] noConstraint, Transition "p" [1, 1] same])
                    ,
                        ( 1
                        ,
                            [ Transition "a" [] noConstraint
                            , Transition "b" [] noConstraint
                            , Transition "back" [0] noConstraint
                            , Transition "next" [1] noConstraint
                            ]
                        )
                    ]
                a = Tree.Node "a" []
                b = Tree.Node "b" []
                back term = Tree.Node "back" [term]
                pair left right = Tree.Node "p" [left, right]
                terms = [pair a a, pair a b, pair (back (pair b b)) (back (pair b b)), pair (back (pair a b)) (back (pair a b))]
            case Automaton.mkFTA 0 rows of
                Left err -> expectationFailure $ show err
                Right graph -> do
                    let imported = Common.fromFTA graph :: Common.Node String
                    map (Automaton.accepts graph) terms `shouldBe` [True, False, True, False]
                    map (Common.acceptsWith equalitiesHold imported) terms `shouldBe` [True, False, True, False]
                    case Common.toFTA imported of
                        Left err -> expectationFailure $ show err
                        Right view -> map (Automaton.accepts view) terms `shouldBe` [True, False, True, False]

        it "keeps long recursive imports closed through complete cycles and unfolding" $
            forM_ [False, True] $ \chain -> do
                let size = if chain then 40 else 32 :: Int
                    rows =
                        [ ( state
                          , Transition ("leaf" <> show state) [] noConstraint
                                : [Transition "next" [if chain then state + 1 else (state + 1) `mod` size] noConstraint | not chain || state < size - 1]
                                    <> [Transition "prev" [state - 1] noConstraint | chain && state > 0]
                          )
                        | state <- [0 .. size - 1]
                        ]
                    walk :: [String] -> Int -> Tree.Tree String
                    walk steps ending = foldr (\symbol child -> Tree.Node symbol [child]) (Tree.Node ("leaf" <> show ending) []) steps
                    labels = if chain then replicate (size - 1) "next" <> replicate (size - 1) "prev" else replicate (2 * size) "next"
                case Automaton.mkFTA 0 rows of
                    Left err -> expectationFailure $ show err
                    Right graph -> do
                        let imported = Common.fromFTA graph :: Common.Node String
                        finished <- timeout 10000000 $ do
                            Common.nodeCount imported `shouldBe` size
                            Common.numNestedMu imported `shouldBe` if chain then size - 1 else 1
                            Common.freeVars imported `shouldBe` mempty
                            let unfolded = Common.unfoldOuterRec imported
                            Common.freeVars unfolded `shouldBe` mempty
                            forM_ [imported, unfolded] $ \node ->
                                map (acceptPlain node) [walk labels 0, walk labels 1] `shouldBe` [True, False]
                        finished `shouldBe` Just ()

        it "preserves every three-state unary graph through import and export" $ do
            -- Exhaust all 512 adjacency matrices, including disconnected SCCs,
            -- cycles broken by enclosing binders, and shared cyclic children.
            -- Distinct leaves and destination labels expose mistaken references.
            let terms =
                    concat
                        $ take 4
                        $ iterate
                            (\previous -> [Tree.Node ("to" <> show next) [term] | next <- [0 .. 2 :: Int], term <- previous])
                            [Tree.Node ("leaf" <> show state) [] | state <- [0 .. 2 :: Int]]
            forM_ [0 .. 511 :: Int] $ \mask -> do
                let rows =
                        [ ( state
                          , Transition ("leaf" <> show state) [] noConstraint
                                : [Transition ("to" <> show next) [next] noConstraint | next <- [0 .. 2], testBit mask (3 * state + next)]
                          )
                        | state <- [0 .. 2 :: Int]
                        ]
                    -- An independent path oracle, rather than the shared
                    -- recognition implementation used by both representations.
                    accepts state (Tree.Node symbol children) = case children of
                        [] -> symbol == "leaf" <> show state
                        [child] ->
                            or
                                [symbol == "to" <> show next && testBit mask (3 * state + next) && accepts next child | next <- [0 .. 2]]
                        _ -> False
                case Automaton.mkFTA 0 rows of
                    Left err -> expectationFailure $ show err
                    Right graph -> do
                        let imported = Common.fromFTA graph :: Common.Node String
                            expected = map (accepts 0) terms
                        Common.freeVars imported `shouldBe` mempty
                        map (acceptPlain imported) terms `shouldBe` expected
                        -- Change the state ordering: RecState positions change,
                        -- but binder identity and the closed result must not.
                        forM_ [negate . (+ 1), \state -> (state + 1) `mod` 3] $ \rename ->
                            Common.fromFTA (Automaton.mapStates rename graph) `shouldBe` imported
                        case Common.toFTA imported of
                            Left err -> expectationFailure $ show err
                            Right view -> map (Automaton.accepts view) terms `shouldBe` expected
                        case imported of
                            Common.InternedMu _ -> do
                                let unfolded = Common.unfoldOuterRec imported
                                Common.freeVars unfolded `shouldBe` mempty
                                map (acceptPlain unfolded) terms `shouldBe` expected
                            _ -> pure ()

        it "shares a downstream SCC across nested binder contexts" $ do
            let rows =
                    [ (0 :: Int, [Transition "a" [] noConstraint, Transition "p" [1, 2] noConstraint])
                    , (1, [Transition "b" [] noConstraint, Transition "q" [0, 1] noConstraint, Transition "down" [2] noConstraint])
                    , (2, [Transition "z" [] noConstraint, Transition "s" [3] noConstraint])
                    , (3, [Transition "w" [] noConstraint, Transition "t" [2, 3] noConstraint])
                    ]
                terms =
                    concat
                        $ take 3
                        $ iterate
                            ( \previous ->
                                [Tree.Node symbol [child] | symbol <- ["down", "s"], child <- previous]
                                    <> [Tree.Node symbol [left, right] | symbol <- ["p", "q", "t"], left <- previous, right <- previous]
                            )
                            [Tree.Node symbol [] | symbol <- ["a", "b", "z", "w"]]
            case Automaton.mkFTA 0 rows of
                Left err -> expectationFailure $ show err
                Right graph -> do
                    let imported = Common.fromFTA graph :: Common.Node String
                    Common.freeVars imported `shouldBe` mempty
                    map (acceptPlain imported) terms `shouldBe` map (Automaton.accepts graph) terms
                    case Common.toFTA imported of
                        Left err -> expectationFailure $ show err
                        Right view -> do
                            -- The second SCC is closed and shared by both parents.
                            let downstream =
                                    [ state
                                    | state <- Automaton.states view
                                    , any ((== "s") . Automaton.transitionSymbol) (Automaton.transitionsFrom view state)
                                    ]
                            length downstream `shouldBe` 1
                            map (Automaton.accepts view) terms `shouldBe` map (Automaton.accepts graph) terms

        it "substitutes nested binders using all and only their free bindings" $ do
            let x = Common.RecState 0
                y = Common.RecState 1
                unused = Common.RecState 2
                leaf symbol = Common.Node [Common.Edge symbol []] :: Common.Node String
                open = Common.createMu $ \self ->
                    Common.Node
                        [Common.Edge "z" [], Common.Edge "p" [Common.Rec x, Common.Rec y, self]]
                close a b = Common.substFree y (leaf b) $ Common.substFree x (leaf a) open
                expected a b = Common.createMu $ \self ->
                    Common.Node
                        [Common.Edge "z" [], Common.Edge "p" [leaf a, leaf b, self]]
            Common.freeVars open
                `shouldBe` Common.freeVars (Common.Node [Common.Edge "free" [Common.Rec x, Common.Rec y]] :: Common.Node String)
            Common.substFree unused (leaf "unused") open `shouldBe` open
            forM_ [("a", "b"), ("a", "c"), ("d", "b"), ("a", "b")] $ \(a, b) -> do
                close a b `shouldBe` expected a b
                Common.freeVars (close a b) `shouldBe` mempty
            -- Substituting an open node keeps its reference free, including
            -- beneath the nested binder, until the enclosing binder binds it.
            let nested = Common.createMu $ \outer -> Common.substFree x outer open
                closed = Common.substFree y (leaf "b") nested
            closed
                `shouldBe` Common.createMu
                    ( \outer -> Common.createMu $ \inner ->
                        Common.Node [Common.Edge "z" [], Common.Edge "p" [outer, leaf "b", inner]]
                    )
            Common.freeVars closed `shouldBe` mempty

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

    describe "explicit-state recognition" $
        it "rejects a transition whose guard is Bottom, as the interned view does" $ do
            let bottom = case Automaton.mkFTA ("q" :: String) [("q", [Transition "a" [] (semanticConstraint Bottom)])] of
                    Right fta -> fta
                    Left err -> error $ show err
                leaf = Tree.Node "a" [] :: Tree.Tree String
            (Automaton.accepts bottom leaf, Common.acceptsWith equalitiesHold (Common.fromFTA bottom) leaf)
                `shouldBe` (False, False)

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

        it "counts a growth only against the nearest type with the same constructor" $
            -- Maybe Chain2, Maybe Chain3, and Maybe (Maybe Bool) are on one path.
            -- Only the last is larger than the one before it.
            fmap
                (Automaton.states . Datatype.datatypeFTA)
                (Datatype.deriveFTAWithGrowthLimit @Chain1 1 mempty)
                `shouldSatisfy` either (const False) (not . null)

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

-- | A chain of distinct types under 'Maybe' that ends in a larger 'Maybe'.
newtype Chain1 = Chain1 (Maybe Chain2)
    deriving (Eq, Show, Generic)

instance Datatype.HasFTA Chain1

newtype Chain2 = Chain2 (Maybe Chain3)
    deriving (Eq, Show, Generic)

instance Datatype.HasFTA Chain2

newtype Chain3 = Chain3 (Maybe (Maybe Bool))
    deriving (Eq, Show, Generic)

instance Datatype.HasFTA Chain3

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
