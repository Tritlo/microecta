-- | Small fixpoint helpers used by reduction and constraint saturation.
module Utility.Fixpoint (
    fixUnbounded,
    fixMaybe,
) where

--------------------------------------------------------------

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
