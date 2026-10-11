{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.MinimizeSpec (spec) where

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe)

import Data.CFTA.Refinement (
    Automaton,
    MinimizeError (StaleSimilarity),
    Node (Node),
    Subtyping (..),
    Symbol (RefinedSymbol),
    Transition,
    Verdict (No, Yes),
    accepts,
    edgeChildren,
    minimize,
    noConstraint,
    reduce,
    refinementSubtypingOn,
    similarity,
    similarityPairs,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (refinementFormula, true, (./=), (.==), (.>=))
import Data.CFTA.Refinement.Guard (requires)
import qualified Data.CFTA.Refinement.Guard as Guard
import Data.CFTA.Refinement.Lattice (latticeEntailment)
import qualified Data.CFTA.Term as Term

spec :: Spec
spec =
    describe "similarity and minimization" $ do
        it "checks snapshots even when the similarity set is empty" $ do
            inferred <- similarity (Subtyping $ \_ _ _ -> pure No) similarAtoms
            case inferred of
                Left err -> expectationFailure $ show err
                Right related -> do
                    similarityPairs related `shouldBe` []
                    minimize naturalNode related `shouldBe` Left StaleSimilarity

        it "does not give a parent the other alternatives of the representative's node" $ do
            let ints =
                    Node
                        [ Transition "Int" (refinementFormula (.== 0)) [] noConstraint
                        , Transition "Int" (refinementFormula (.== 1)) [] noConstraint
                        ]
                root = case Guard.transition "div" (const true) [ints, ints] (\_ d -> d `requires` (./= 0)) of
                    Right edge -> Node [edge]
                    Left err -> error (show err)
                subtyping = refinementSubtypingOn latticeEntailment (Just . length . edgeChildren)
                int k = Term.Node (RefinedSymbol "Int" (refinementFormula (.== k))) []
                divide left right = Term.Node (RefinedSymbol "div" true) [int left, int right]
            accepts latticeEntailment root (divide 0 0) >>= (`shouldBe` No)
            reduced <- reduce latticeEntailment subtyping root
            case reduced of
                Left err -> expectationFailure $ show err
                Right result -> do
                    accepts latticeEntailment result (divide 0 0) >>= (`shouldBe` No)
                    accepts latticeEntailment result (divide 0 1) >>= (`shouldBe` Yes)

-- | An unrefined, unconstrained leaf transition.
plain :: Symbol -> Transition
plain symbol = Transition symbol true [] noConstraint

unknownAtom, naturalAtom :: Transition
unknownAtom = plain "unknown"
naturalAtom = Transition "natural" (refinementFormula (\v -> v .>= 0)) [] noConstraint

naturalNode :: Automaton
naturalNode = Node [naturalAtom]

-- | Two refinements sharing one node, as in an alternative row.
similarAtoms :: Automaton
similarAtoms = Node [unknownAtom, naturalAtom]
