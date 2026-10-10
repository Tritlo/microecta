{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.Refinement.SyntaxSpec (spec) where

import qualified Data.Set as Set
import qualified Data.Tree as Tree

import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldMatchList, shouldSatisfy)

import Data.CFTA.Refinement (
    AutomatonError (CyclicGuardReference, GuardArityMismatch, OpenAutomaton),
    Guard (Entails, Satisfies),
    Node (Mu, Node, Rec),
    RecNodeId (RecUnint),
    Symbol (RefinedSymbol),
    Verdict (..),
    accepts,
    automatonAlphabet,
    constraintAsGuard,
    denotationAtMost,
    edgeConstraint,
    mkEdge,
    noConstraint,
    nodeEdges,
    path,
    semanticConstraint,
    validate,
    pattern Transition,
 )
import Data.CFTA.Refinement.Expression (refinementFormula, true, (.==), (.>=))
import Data.CFTA.Refinement.Guard (automaton, contract, isSubtypeOf, requires, transition, unconstrained)
import Data.CFTA.Refinement.TestSupport (tableEntailment)

spec :: Spec
spec =
    describe "named guards and validation" $ do
        it "reports a named guard with the wrong number of arguments" $ do
            let leaf = Node [Transition "leaf" true [] noConstraint]
            automaton [transition "wrap" (const true) [leaf] (\actual expected -> actual `isSubtypeOf` expected)]
                `shouldBe` Left (GuardArityMismatch "wrap" 1 2)

        it "reports a contract that names more terms than the constructor has children" $ do
            let leaf = Node [Transition "leaf" true [] noConstraint]
            automaton [transition "pair" (const true) [leaf, leaf] (contract (\x y z -> x + y .== z))]
                `shouldBe` Left (GuardArityMismatch "pair" 2 3)
            either (const False) (const True) (automaton [transition "pair" (const true) [leaf, leaf] (contract (\x y -> x .== y))])
                `shouldBe` True

        it "builds transitions from refinements and named guards" $ do
            let nonNegative v = v .>= 0
                built = do
                    zero <- automaton [transition "zero" nonNegative [] unconstrained]
                    automaton [transition "sqrt" (const true) [zero] (`requires` nonNegative)]
            case built of
                Left err -> expectationFailure $ show err
                Right root ->
                    accepts
                        tableEntailment
                        root
                        (Tree.Node (RefinedSymbol "sqrt" true) [Tree.Node (RefinedSymbol "zero" (refinementFormula nonNegative)) []])
                        >>= (`shouldBe` Yes)

        it "interprets entailments carried by interned edges" $ do
            let nonNegative = refinementFormula (\v -> v .>= 0)
                alternatives =
                    Node
                        [ Transition "zero" nonNegative [] noConstraint
                        , Transition "unknown" true [] noConstraint
                        ]
                root =
                    Node
                        [ mkEdge
                            (RefinedSymbol "check" true)
                            [alternatives, alternatives]
                            (semanticConstraint $ Entails (path [0]) (path [1]))
                        ]
                terms =
                    [ Tree.Node (RefinedSymbol "check" true) [left, right]
                    | left <- [Tree.Node (RefinedSymbol "zero" nonNegative) [], Tree.Node (RefinedSymbol "unknown" true) []]
                    , right <- [Tree.Node (RefinedSymbol "zero" nonNegative) [], Tree.Node (RefinedSymbol "unknown" true) []]
                    ]
            validate root `shouldBe` Right ()
            automatonAlphabet root `shouldSatisfy` Set.member (RefinedSymbol "zero" nonNegative)
            map (constraintAsGuard . edgeConstraint) (nodeEdges root)
                `shouldBe` [Entails (path [0]) (path [1])]
            mapM (accepts tableEntailment root) terms
                >>= (`shouldBe` [Yes, Yes, No, Yes])
            denotationAtMost tableEntailment 1 root
                >>= either (expectationFailure . show) (`shouldMatchList` map (terms !!) [0, 1, 3])

        it "rejects a guard position inside a recursive node" $ do
            let root = Mu $ \self ->
                    Node
                        [ mkEdge
                            (RefinedSymbol "loop" true)
                            [self]
                            (semanticConstraint $ Satisfies (path [0]) true)
                        ]
            case validate root of
                Left (CyclicGuardReference _ target) -> target `shouldBe` path [0]
                other -> expectationFailure $ show other

        it "rejects free recursive references" $
            validate (Rec $ RecUnint 0) `shouldBe` Left OpenAutomaton
