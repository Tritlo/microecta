-- | Small fixpoint helpers used by reduction and constraint saturation.
module Utility.Fixpoint (
    fix,
    fixUnbounded,
    fixMaybe,
) where

--------------------------------------------------------------

-- | Iterate until stable, failing after the given number of iterations.
fix :: (Show a, Eq a) => Int -> (a -> a) -> a -> a
fix (-1) _ _ = error "fix: Exceeded maxIters"
fix maxIters f x =
    let x' = f x
     in if x' == x
            then
                x
            else
                fix (maxIters - 1) f x'

-- | Iterate until stable with no iteration bound.
fixUnbounded :: (Eq a) => (a -> a) -> a -> a
fixUnbounded f x =
    let x' = f x
     in if x' == x
            then
                x
            else
                fixUnbounded f x'

-- | Iterate a partial step function until stable or failed.
fixMaybe :: (Eq a) => (a -> Maybe a) -> a -> Maybe a
fixMaybe f x = case f x of
    Nothing -> Nothing
    Just x' ->
        if x' == x
            then
                Just x
            else
                fixMaybe f x'
