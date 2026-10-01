{-# LANGUAGE OverloadedStrings #-}

{- | Check generation from equality-constrained automata against "Data.CFTA.Simple".

The automata are random explicit automata over at most three states, with
cycles and equality constraints, as in the core package's check. A generator
imported up to a depth has exactly the terms of the simple definition up to
that depth, and every rank gives its term back. A recursive import has, at
each size, the terms of the simple definition with that many nodes.
-}
module Data.CFTA.Gen.Equality.SimpleSpec (spec) where

import Control.Monad (forM, forM_)
import Data.CFTA.Index (Cardinality, Depth (..), everyRank)
import Data.List (sort)
import Data.Maybe (fromMaybe)
import Data.String (fromString)
import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, it, shouldBe)
import Test.QuickCheck (Gen, chooseInt, elements, forAll, property, vectorOf, within)

import Data.CFTA (FTA, Transition (Transition), mapConstraints, mkFTA)
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint, equalityConstraint, noConstraint)
import Data.CFTA.Equality.Constraint (mkEqConstraints)
import qualified Data.CFTA.Gen.Equality as ECTAGen
import Data.CFTA.Interned (fromFTA, numNestedMu, toFTA)
import Data.CFTA.Path (path)
import qualified Data.CFTA.Simple as Simple
import Data.CFTA.Symbol (Symbol)

spec :: Spec
spec = describe "generation from equality automata against Data.CFTA.Simple" $ do
    it "imports up to a depth exactly the terms of the simple definition" $
        property $
            forAll automaton $ \explicit ->
                forM_ [0 .. 2] $ \depth -> do
                    let generator = ECTAGen.fromAutomatonUpToDepth depth (fromFTA explicit)
                        expected = simpleTerms depth explicit
                        ranks = either (const []) everyRank $ ECTAGen.cardinality generator
                    (depth, ECTAGen.cardinality generator) `shouldBe` (depth, counted expected)
                    (depth, sort [term | rank <- ranks, Right term <- [ECTAGen.unrank generator rank]]) `shouldBe` (depth, expected)
                    (depth, [rank | rank <- ranks, (ECTAGen.rankOf generator =<< ECTAGen.termAt generator rank) /= Right rank])
                        `shouldBe` (depth, [])

    it "imports an automaton without constraints as its terms, by size when it is cyclic" $
        -- A recursive import cannot count an edge with constraints: its count is an intersection.
        property $
            -- Two states: interned intersection, which the ambiguity check uses, grows
            -- exponentially on three mutually recursive states.
            forAll (FTA.trim . mapConstraints (const noConstraint) <$> automatonOf 2) $ \explicit -> within 10000000 $ do
                let node = fromFTA explicit
                    generator = ECTAGen.fromAutomaton node
                    ranks = either (const []) everyRank $ ECTAGen.cardinality generator
                if numNestedMu node == 0
                    then -- An acyclic automaton gives one rank per distinct term.
                        sort [term | rank <- ranks, Right term <- [ECTAGen.unrank generator rank]] `shouldBe` sort (FTA.terms explicit)
                    else -- A cyclic one is counted by size, the number of nodes, and must be unambiguous.
                        forM_ [1 .. 3] $ \size ->
                            (size, ECTAGen.countAtSize generator size)
                                `shouldBe` ( size
                                           , if either (error . show) ambiguous (toFTA node)
                                                then Left ECTAGen.AmbiguousAutomaton
                                                else Right (toEnum (length [term | term <- simpleTerms 2 explicit, toEnum (length (Tree.flatten term)) == size]))
                                           )

-- | A random explicit automaton: at most three states, one arity per symbol, and equality constraints.
automaton :: Gen (FTA Int Symbol Constraint)
automaton = automatonOf 3

-- | A random explicit automaton over at most the given number of states.
automatonOf :: Int -> Gen (FTA Int Symbol Constraint)
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
            _ -> [[], [], [[path [0], path [1]]], [[path [0, 0], path [1]]], [[path [0, 1], path [1, 0]]]]
        pure
            $ Transition (fromString symbol) children
            $ if null classes then noConstraint else equalityConstraint $ mkEqConstraints classes

{- | Whether two distinct transitions of one state accept a common term. For
an automaton without constraints, they do when they have one symbol and the
languages of the children at each position intersect.
-}
ambiguous :: (Ord state, Show state) => FTA state Symbol Constraint -> Bool
ambiguous explicit =
    or
        [ and (zipWith overlap leftChildren rightChildren)
        | state <- FTA.states explicit
        , (index, Transition symbol leftChildren _) <- zip [0 :: Int ..] (FTA.transitionsFrom explicit state)
        , (other, Transition otherSymbol rightChildren _) <- zip [0 ..] (FTA.transitionsFrom explicit state)
        , index < other
        , symbol == otherSymbol
        , leftChildren /= rightChildren
        ]
  where
    -- Trimming keeps a transition at the initial state exactly when the language is not empty.
    overlap left right =
        let common = FTA.trim $ Simple.intersect (from left) (from right)
         in not $ null $ FTA.transitionsFrom common $ FTA.initialState common
    from state = either (error . show) id $ mkFTA state [(other, FTA.transitionsFrom explicit other) | other <- FTA.states explicit]

-- | The cardinality of a language with the given terms. An empty language is an error of its own.
counted :: [a] -> Either ECTAGen.GenError Cardinality
counted [] = Left ECTAGen.EmptyGenerator
counted members = Right $ toEnum $ length members

simpleTerms :: Depth -> FTA Int Symbol Constraint -> [Tree.Tree Symbol]
simpleTerms depth = fromMaybe (error "an equality constraint needed a solver") . Simple.termsUpTo depth
