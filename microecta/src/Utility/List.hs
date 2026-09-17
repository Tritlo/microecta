-- | Total list helpers shared by the term and automaton path operations.
module Utility.List (
    adjustAt,
) where

--------------------------------------------------------------

-- | Apply a function at one index, leaving an out-of-range index alone.
adjustAt :: Int -> (a -> a) -> [a] -> [a]
adjustAt i f xs
    | i < 0 = xs
    | otherwise = case splitAt i xs of
        (prefix, x : suffix) -> prefix ++ f x : suffix
        _ -> xs
