{-# LANGUAGE GADTs #-}

{- | Structural queries over a retained recipe.

The compilers ask these questions before they enumerate candidates or call the
solver. Each answer comes from the recipe alone, so none of them inspects a
generated Haskell value.
-}
module Data.CFTA.Gen.Refinement.Internal.Recipe (
    validateGenerator,
    childRecipeArity,
    rawRecipeCount,
    knownEmptyRecipe,
    knownEmptyChild,
    uniformlyWeightedRecipe,
    transparentCompiled,
    requiredImplications,
) where

import Control.Monad (void)
import Data.List (nub)

import Data.CFTA.Gen.Refinement.Internal.Error (GeneratorError)
import Data.CFTA.Gen.Refinement.Internal.Replay (cardinality, mapCompiled)
import Data.CFTA.Gen.Refinement.Internal.Types
import Data.CFTA.Refinement

-- | Report construction errors before enumerating candidates or using a solver.
validateGenerator :: LTAGen a -> Either GeneratorError ()
validateGenerator generator = void (generatorRecipe generator)

-- | Number of generated child positions in one free applicative spine.
childRecipeArity :: ChildRecipe a -> Int
childRecipeArity (PureChildRecipe _) = 0
childRecipeArity (OneChildRecipe _) = 1
childRecipeArity (ApplyChildRecipe functions arguments) =
    childRecipeArity functions + childRecipeArity arguments

-- | Count source occurrences without inspecting their values or refinements.
rawRecipeCount :: Recipe a -> Integer
rawRecipeCount (PoolRecipe entries) = toInteger $ length entries
rawRecipeCount (MapRecipe _ recipe) = rawRecipeCount recipe
rawRecipeCount (NodeRecipe _ _ _ childRecipe) = rawChildCount childRecipe
rawRecipeCount (ChoiceRecipe alternatives) = sum $ map (rawRecipeCount . snd) alternatives
rawRecipeCount (CompiledRecipe compiled) = cardinality compiled
-- 'prepareRecipe' replaces every 'AutomatonRecipe' before a count is taken.
rawRecipeCount (AutomatonRecipe _ _) =
    error
        "microcfta-generator bug in Data.CFTA.Gen.Refinement.Internal.Recipe.rawRecipeCount: an automaton source was not prepared"

-- | Count a prepared child product with its original mixed-radix dimensions.
rawChildCount :: ChildRecipe a -> Integer
rawChildCount (PureChildRecipe _) = 1
rawChildCount (OneChildRecipe recipe) = rawRecipeCount recipe
rawChildCount (ApplyChildRecipe functions arguments) = rawChildCount functions * rawChildCount arguments

-- | Detect an empty source without a solver or a value projection.
knownEmptyRecipe :: Recipe a -> Bool
knownEmptyRecipe (PoolRecipe entries) = null entries
knownEmptyRecipe (MapRecipe _ recipe) = knownEmptyRecipe recipe
knownEmptyRecipe (NodeRecipe _ _ constraint childRecipe) =
    fixedGuardVerdict (constraintGuard constraint) == Just False || knownEmptyChild childRecipe
knownEmptyRecipe (ChoiceRecipe alternatives) = all (knownEmptyRecipe . snd) alternatives
knownEmptyRecipe (AutomatonRecipe maximumHeight _) = maximumHeight < 0
knownEmptyRecipe _ = False

-- | An empty factor makes the complete child product empty.
knownEmptyChild :: ChildRecipe a -> Bool
knownEmptyChild (PureChildRecipe _) = False
knownEmptyChild (OneChildRecipe recipe) = knownEmptyRecipe recipe
knownEmptyChild (ApplyChildRecipe functions arguments) = knownEmptyChild functions || knownEmptyChild arguments

-- | Evaluate only Boolean constants; missing paths retain their core semantics.
fixedGuardVerdict :: Guard -> Maybe Bool
fixedGuardVerdict Top = Just True
fixedGuardVerdict Bottom = Just False
fixedGuardVerdict (Not nested) = not <$> fixedGuardVerdict nested
fixedGuardVerdict (And guards)
    | Just False `elem` results = Just False
    | all (== Just True) results = Just True
    | otherwise = Nothing
  where
    results = map fixedGuardVerdict guards
fixedGuardVerdict (Or guards)
    | Just True `elem` results = Just True
    | all (== Just False) results = Just False
    | otherwise = Nothing
  where
    results = map fixedGuardVerdict guards
fixedGuardVerdict (Substitute additions nested)
    | null additions || fixedGuardVerdict nested == Just False = fixedGuardVerdict nested
fixedGuardVerdict _ = Nothing

-- | Whether relational compilation preserves this recipe's source weights.
uniformlyWeightedRecipe :: Recipe a -> Bool
uniformlyWeightedRecipe (PoolRecipe _) = True
uniformlyWeightedRecipe (MapRecipe _ recipe) = uniformlyWeightedRecipe recipe
uniformlyWeightedRecipe (NodeRecipe _ _ _ childrenRecipe) = uniformlyWeightedChildren childrenRecipe
uniformlyWeightedRecipe (ChoiceRecipe alternatives) =
    all ((== 1) . fst) alternatives
        && all (uniformlyWeightedRecipe . snd) alternatives
uniformlyWeightedRecipe (AutomatonRecipe _ _) = True
uniformlyWeightedRecipe (CompiledRecipe _) = True

-- | Whether every source below one applicative child spine is unit-weighted.
uniformlyWeightedChildren :: ChildRecipe a -> Bool
uniformlyWeightedChildren (PureChildRecipe _) = True
uniformlyWeightedChildren (OneChildRecipe recipe) = uniformlyWeightedRecipe recipe
uniformlyWeightedChildren (ApplyChildRecipe functions arguments) =
    uniformlyWeightedChildren functions && uniformlyWeightedChildren arguments

-- | Preserve a compiled import when a caller only changes its value view.
transparentCompiled :: Recipe a -> Maybe (Compiled a)
transparentCompiled (CompiledRecipe compiled) = Just compiled
transparentCompiled (MapRecipe transform recipe) = mapCompiled transform <$> transparentCompiled recipe
transparentCompiled _ = Nothing

-- | Collect the distinct refinement implications that shrinking needs.
requiredImplications :: LTAGen a -> [(Refinement, Refinement)]
requiredImplications generator =
    either (const []) (nub . recipeImplications) $ generatorRecipe generator

-- | Inspect atomic refinement relations without traversing source products.
recipeImplications :: Recipe a -> [(Refinement, Refinement)]
recipeImplications (PoolRecipe entries) =
    [(source, target) | source <- refinements, target <- refinements, source /= target]
  where
    refinements = nub [refinement | Refined _ _ refinement <- entries]
recipeImplications (MapRecipe _ recipe) = recipeImplications recipe
recipeImplications (NodeRecipe _ _ _ childRecipe) = childImplications childRecipe
recipeImplications (ChoiceRecipe alternatives) = concatMap (recipeImplications . snd) alternatives
recipeImplications (AutomatonRecipe _ _) = []
recipeImplications (CompiledRecipe _) = []

-- | Collect refinement relations from the direct child sources.
childImplications :: ChildRecipe a -> [(Refinement, Refinement)]
childImplications (PureChildRecipe _) = []
childImplications (OneChildRecipe recipe) = recipeImplications recipe
childImplications (ApplyChildRecipe functions arguments) = childImplications functions <> childImplications arguments
