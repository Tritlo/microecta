{-# LANGUAGE OverloadedStrings #-}

{- | Check each component of the interned automata against "Data.CFTA.Simple".

The automata are random explicit automata over at most three states, with
cycles and with equality constraints, some of which name a child that does
not exist. Each property compares one component with the definition in
"Data.CFTA.Simple": membership, enumeration, the constructions, and the
reductions. Terms are compared up to depth two, or three when the automaton
has few trees.
-}
module Data.CFTA.SimpleSpec (spec) where

import Control.Monad (forM, forM_)
import Data.Functor.Identity (Identity (..))
import Data.List (sort)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)
import Test.QuickCheck (Gen, chooseInt, elements, forAll, property, vectorOf, within)

import Data.CFTA (FTA, Transition (Transition), mapConstraints, mkFTA)
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (
    Constraint,
    conjoinConstraints,
    constraintPaths,
    equalitiesHold,
    equalityConstraint,
    noConstraint,
 )
import Data.CFTA.Enumeration (
    PartialSymbol (ConcreteSymbol),
    expandPartialTermFrag,
    noExpansionPreference,
    runs,
    terms,
    termsPruneWith,
    truncatedTerms,
 )
import Data.CFTA.Equality (
    accepts,
    dropConstraints,
    fixUnbounded,
    mkEqConstraints,
    reducePartially,
    termsMatching,
    withoutRedundantEdges,
 )
import qualified Data.CFTA.Interned as Interned
import Data.CFTA.Path (path, unPath)
import qualified Data.CFTA.Simple as Simple
import Data.CFTA.Template (Template (..), matchesTemplate, restrictFTA)

spec :: Spec
spec = describe "the interned automata against Data.CFTA.Simple" $ do
    it "accept the terms that the simple definition accepts, also after toFTA" $
        property $
            forAll automaton $ \explicit -> do
                let node = Interned.fromFTA explicit
                [(term, accepts node term) | term <- candidates explicit]
                    `shouldBe` [(term, simpleAccepts explicit term) | term <- candidates explicit]
                case Interned.toFTA node of
                    Left err -> expectationFailure $ show err
                    Right viewed ->
                        [(term, Simple.accepts viewed term) | term <- candidates explicit]
                            `shouldBe` [(term, Simple.accepts explicit term) | term <- candidates explicit]

    it "accept at the explicit view the terms that the simple definition accepts" $
        property $
            forAll automaton $ \explicit ->
                [(term, FTA.accepts explicit term) | term <- candidates explicit]
                    `shouldBe` [(term, simpleAccepts explicit term) | term <- candidates explicit]

    it "list at the explicit view the trees of the underlying graph up to each depth" $
        property $
            forAll automaton $ \explicit ->
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, sort (FTA.terms (FTA.boundDepth depth explicit))) `shouldBe` (depth, underlying depth explicit)

    it "check at the explicit view the terms that the simple definition accepts and lists" $
        property $
            forAll automaton $ \explicit -> within 10000000 $ do
                let check _ transition term = Identity $ equalitiesHold (FTA.transitionConstraint transition) term
                [(term, runIdentity (FTA.acceptsM check explicit term)) | term <- candidates explicit]
                    `shouldBe` [(term, simpleAccepts explicit term) | term <- candidates explicit]
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, sort (runIdentity (FTA.termsUpToM check depth explicit))) `shouldBe` (depth, simpleTerms depth explicit)

    it "restrict the explicit view to a template as filtering its trees does" $
        property $
            forAll ((,) <$> automaton <*> template) $ \(explicit, shape) -> within 10000000 $
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, sort (FTA.terms (FTA.boundDepth depth (restrictFTA shape explicit))))
                        `shouldBe` (depth, filter (matchesTemplate shape) (underlying depth explicit))

    it "enumerate the terms up to each depth that the simple definition lists" $
        property $
            forAll automaton $ \explicit -> do
                let node = Interned.fromFTA explicit
                forM_ [0 .. deepest explicit] $ \depth -> do
                    let expected = simpleTerms depth explicit
                        bounded = Interned.boundDepth depth node
                    (depth, sort (terms bounded)) `shouldBe` (depth, expected)
                    (depth, Set.fromList [term | partial <- truncatedTerms bounded, Just term <- [traverse concrete partial]])
                        `shouldBe` (depth, Set.fromList expected)
                    (depth, Set.fromList [term | (term, []) <- runs "Mu" bounded]) `shouldBe` (depth, Set.fromList expected)

    it "prune with an oracle as filtering the terms by the oracle does, in either expansion order" $
        -- The oracle rejects every fragment that holds a "b". A fragment only
        -- grows, so the rejection is monotone and the order does not matter.
        property $
            forAll automaton $ \explicit ->
                forM_ [0 .. deepest explicit] $ \depth -> do
                    let bounded = Interned.boundDepth depth (Interned.fromFTA explicit)
                        oracle _ _ (Left fragment) = do
                            partial <- expandPartialTermFrag fragment
                            return (holdsB partial, ())
                        oracle _ _ (Right _) = return (False, ())
                        holdsB (Tree.Node (ConcreteSymbol symbol) children) = symbol == "b" || any holdsB children
                        holdsB (Tree.Node _ children) = any holdsB children
                        preferLast _ holes = case reverse holes of
                            uv : _ -> Just uv
                            [] -> Nothing
                        expected = Set.fromList $ filter (notElem "b" . Tree.flatten) (simpleTerms depth explicit)
                    (depth, Set.fromList (termsPruneWith "Mu" () noExpansionPreference oracle bounded)) `shouldBe` (depth, expected)
                    (depth, Set.fromList (termsPruneWith "Mu" () preferLast oracle bounded)) `shouldBe` (depth, expected)

    it "intersect as the simple product does, which keeps the terms of both" $
        property $
            forAll ((,) <$> automaton <*> automaton) $ \(left, right) ->
                forM_ [0 .. min (deepest left) (deepest right)] $ \depth -> do
                    let expected = simpleTerms depth (Simple.intersect left right)
                    (depth, expected) `shouldBe` (depth, filter (simpleAccepts right) (simpleTerms depth left))
                    (depth, sort (terms (Interned.boundDepth depth (Interned.intersect (Interned.fromFTA left) (Interned.fromFTA right)))))
                        `shouldBe` (depth, expected)
                    case FTA.intersectWith sameSymbol conjoinConstraints left right of
                        Left err -> expectationFailure $ show err
                        Right explicitProduct -> (depth, simpleTerms depth explicitProduct) `shouldBe` (depth, expected)

    it "unite as the simple union does, which keeps the terms of either" $
        property $
            forAll ((,) <$> automaton <*> automaton) $ \(left, right) ->
                forM_ [0 .. min (deepest left) (deepest right)] $ \depth -> do
                    let expected = simpleTerms depth (Simple.union left right)
                    (depth, expected) `shouldBe` (depth, Set.toList $ Set.fromList $ simpleTerms depth left <> simpleTerms depth right)
                    (depth, sort (terms (Interned.boundDepth depth (Interned.union [Interned.fromFTA left, Interned.fromFTA right]))))
                        `shouldBe` (depth, expected)

    it "bound the depth as the simple bound does, which keeps the shallow terms" $
        property $
            forAll automaton $ \explicit ->
                forM_ [-1 .. deepest explicit] $ \depth -> do
                    let bounded = Simple.boundDepth depth explicit
                        shallow = filter ((<= depth) . treeDepth) (candidates explicit)
                    (depth, [(term, simpleAccepts bounded term) | term <- candidates explicit])
                        `shouldBe` (depth, [(term, term `elem` shallow && simpleAccepts explicit term) | term <- candidates explicit])
                    (depth, [(term, accepts (Interned.boundDepth depth (Interned.fromFTA explicit)) term) | term <- candidates explicit])
                        `shouldBe` (depth, [(term, simpleAccepts bounded term) | term <- candidates explicit])

    it "restrict to a template as filtering the terms by the template does" $
        property $
            forAll ((,) <$> automaton <*> template) $ \(explicit, shape) ->
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, sort (terms (Interned.boundDepth depth (termsMatching shape (Interned.fromFTA explicit)))))
                        `shouldBe` (depth, filter (matchesTemplate shape) (simpleTerms depth explicit))

    it "keep the language through each reduction" $
        -- Two states at most: the interned form nests a binder for each state
        -- of a cycle on every path, so three mutually recursive states can make
        -- withoutRedundantEdges, which intersects nodes, take seconds. The
        -- limit reports such a case rather than hanging.
        property $
            forAll (automatonOf 2) $ \explicit -> within 20000000 $ do
                let node = Interned.fromFTA explicit
                forM_ reductions $ \(name, reduce) -> do
                    let reduced = reduce node
                    (name, [(term, accepts reduced term) | term <- candidates explicit])
                        `shouldBe` (name, [(term, simpleAccepts explicit term) | term <- candidates explicit])
                    forM_ [0 .. deepest explicit] $ \depth ->
                        (name, depth, sort (terms (Interned.boundDepth depth reduced))) `shouldBe` (name, depth, simpleTerms depth explicit)

    it "drop the constraints to the underlying graph of the transitions that can accept" $
        -- An interned edge whose class names a child it does not have accepts
        -- nothing, and interning removes it, so dropping constraints cannot
        -- bring it back.
        property $
            forAll automaton $ \explicit ->
                forM_ [0 .. deepest explicit] $ \depth ->
                    (depth, sort (terms (Interned.boundDepth depth (dropConstraints (Interned.fromFTA explicit)))))
                        `shouldBe` (depth, underlying depth (withoutMissingChildren explicit))

    it "unfold recursion to a part of the language that grows with the rounds" $
        -- Two states at most, for the nesting of binders, as for the reductions.
        property $
            forAll (automatonOf 2) $ \explicit ->
                forM_ [0 .. deepest explicit] $ \depth -> do
                    let listed rounds = Set.fromList $ terms $ Interned.boundDepth depth $ Interned.unfoldBounded rounds $ Interned.fromFTA explicit
                        growing = [listed rounds | rounds <- [0 .. 3]] <> [Set.fromList (simpleTerms depth explicit)]
                    (depth, and (zipWith Set.isSubsetOf growing (drop 1 growing))) `shouldBe` (depth, True)
  where
    reductions =
        [ ("reducePartially" :: String, reducePartially)
        , ("withoutRedundantEdges", withoutRedundantEdges)
        , ("both to a fixpoint", fixUnbounded (withoutRedundantEdges . reducePartially))
        ]
    sameSymbol left right = if left == right then Just left else Nothing
    treeDepth (Tree.Node _ []) = 0 :: Int
    treeDepth (Tree.Node _ children) = 1 + maximum (map treeDepth children)
    concrete (ConcreteSymbol symbol) = Just symbol
    concrete _ = Nothing

-- | A random explicit automaton: at most three states, one arity per symbol, and equality constraints.
automaton :: Gen (FTA Int String Constraint)
automaton = automatonOf 3

-- | A random explicit automaton over at most the given number of states.
automatonOf :: Int -> Gen (FTA Int String Constraint)
automatonOf states = do
    count <- chooseInt (1, states)
    rows <- forM [0 .. count - 1] $ \state -> do
        width <- chooseInt (1, 3)
        (,) state <$> vectorOf width (transition count)
    pure $ either (error . show) id $ mkFTA 0 rows
  where
    transition count = do
        (symbol, arity) <- elements [("a", 0), ("b", 0), ("f", 1), ("g", 2)]
        children <- vectorOf arity (chooseInt (0, count - 1))
        classes <- elements $ case arity of
            0 -> [[]]
            1 -> [[], [], [[path [0, 0], path [0, 1]]]]
            _ ->
                [ []
                , []
                , [[path [0], path [1]]]
                , [[path [0, 0], path [1]]]
                , [[path [0, 1], path [1, 0]]]
                , [[path [0], path [2]]]
                ]
        pure $ Transition symbol children $ if null classes then noConstraint else equalityConstraint $ mkEqConstraints classes

-- | A random template over the symbols of 'automaton', two levels deep at most.
template :: Gen (Template String)
template = go (2 :: Int)
  where
    go 0 = pure Hole
    go depth = do
        children <- chooseInt (0, 2) >>= \count -> vectorOf count (go (depth - 1))
        symbol <- elements ["a", "b", "f", "g"]
        elements [Hole, AnyNode children, TemplateNode symbol children, AnyPrefix children, TemplatePrefix symbol children]

-- | The automaton without the transitions whose constraints name a child that they do not have.
withoutMissingChildren :: FTA Int String Constraint -> FTA Int String Constraint
withoutMissingChildren explicit =
    either (error . show) id $
        mkFTA
            (FTA.initialState explicit)
            [(state, filter fits (FTA.transitionsFrom explicit state)) | state <- FTA.states explicit]
  where
    fits (Transition _ children constraint) =
        and [0 <= index && index < length children | index : _ <- map unPath (constraintPaths constraint)]

-- | The deepest depth to compare: three when the underlying graph has few trees of depth two.
deepest :: FTA Int String Constraint -> Int
deepest explicit
    | length (underlying 2 explicit) <= 40 = 3
    | otherwise = 2

-- | The trees of the underlying graph up to a depth, without constraints.
underlying :: Int -> FTA Int String Constraint -> [Tree.Tree String]
underlying depth = fromMaybe [] . Simple.termsUpTo depth . mapConstraints (const noConstraint)

-- | Terms to test membership of: the trees of the underlying graph, and trees with a foreign symbol.
candidates :: FTA Int String Constraint -> [Tree.Tree String]
candidates explicit = underlying (deepest explicit) explicit <> [Tree.Node "c" [], Tree.Node "f" [Tree.Node "c" []]]

simpleAccepts :: (Ord state) => FTA state String Constraint -> Tree.Tree String -> Bool
simpleAccepts explicit = fromMaybe (error "an equality constraint needed a solver") . Simple.accepts explicit

simpleTerms :: (Ord state) => Int -> FTA state String Constraint -> [Tree.Tree String]
simpleTerms depth = fromMaybe (error "an equality constraint needed a solver") . Simple.termsUpTo depth
