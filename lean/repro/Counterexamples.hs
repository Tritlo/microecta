{-# LANGUAGE OverloadedStrings #-}

-- | Reproduce the implementation findings from the Lean spike.
module Main (main) where

import qualified Data.Tree as Tree

import Data.CFTA.Constraint (contractTermName, semanticConstraint)
import qualified Data.CFTA.Gen.Refinement as G
import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression (true, variable, (.==), (.>=))
import Data.CFTA.Refinement.Guard (argument, requires)
import Data.CFTA.Refinement.LiquidFixpoint (withZ3)

-- | Print complete evaluation, compiled cardinality, and atomic size observations.
main :: IO ()
main = withZ3 [] $ \solver -> do
    let p = path [0]
        child = Tree.Node (RefinedSymbol "x" (variable "v" .>= 0)) []
        term = Tree.Node (RefinedSymbol "host" true) [child]
        alias =
            semanticConstraint $
                Holds
                    [p, p]
                    (variable (contractTermName 0) .== variable (contractTermName 1))
        generated = G.refinedNode "host" (const true) alias $ G.leaf () "x" (.>= 0)
    putStrLn "Repeated-path tautology: expected Yes and Right 1"
    print =<< evaluateConstraint solver alias term
    print . (>>= G.cardinality) =<< G.compileWith solver generated
    let source =
            G.atomic $
                G.oneof
                    [ G.leaf (0 :: Int) "a" (const true)
                    , G.node "wrap" $ G.leaf 1 "b" (const true)
                    ]
        unobserved = G.refinedNode "outer" (const true) noConstraint source
        observed = G.refinedNode "outer" (const true) (requires (argument 0) (const true)) source
    putStrLn "Atomic source sizes: expected equal sizes for both ranks"
    print [G.sizeOfRank source rank | rank <- [0, 1]]
    putStrLn "Parent without observations: expected equal sizes for both ranks"
    print [G.sizeOfRank unobserved rank | rank <- [0, 1]]
    result <- G.compileWith solver observed
    putStrLn "Parent with a tautological observation: expected the same size classes"
    print $ fmap (\g -> [G.sizeOfRank g rank | rank <- [0, 1]]) result
    putStrLn "Shrinks after observation: expected no strictly smaller peer"
    print $ fmap (\g -> [G.smallerMembers g rank | rank <- [0, 1]]) result
    putStrLn "Values at size at most 1, before and after observation"
    print $ G.values $ G.upToSize 1 unobserved
    print $ result >>= G.values . G.upToSize 1
    putStrLn "Exact probabilities at size at most 1, before and after observation"
    print $ G.pmf $ G.upToSize 1 unobserved
    print $ result >>= G.pmf . G.upToSize 1
    let a = Node [Transition "a" true [] noConstraint]
        b = Node [Transition "b" true [] noConstraint]
        unequalChildren = semanticConstraint $ Not $ Same (path [0]) (path [1])
        grammar = Node [Transition "f" true [a, b] unequalChildren]
        subtype = refinementSubtypingOn solver $ \edge ->
            if transitionSymbol edge `elem` ["a", "b"] && edgeConstraint edge == noConstraint
                then Just ()
                else Nothing
    putStrLn "Semantic solutions before and after similarity minimization"
    print . fmap (map eraseRefinements) =<< denotationAtMost solver 1 grammar
    inferred <- similarity subtype grammar
    case either (Left . show) Right inferred >>= either (Left . show) Right . minimize grammar of
        Left err -> print err
        Right minimized -> print . fmap (map eraseRefinements) =<< denotationAtMost solver 1 minimized
    putStrLn "Semantic solutions after prune-then-minimize reduction"
    reduced <- reduce solver subtype grammar
    case reduced of
        Left err -> print err
        Right minimized -> print . fmap (map eraseRefinements) =<< denotationAtMost solver 1 minimized
