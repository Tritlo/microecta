-- | Total list helpers shared by the term and automaton path operations.
module Utility.List (
    atMay,
    adjustAt,
) where

--------------------------------------------------------------

-- | The element at an index, or 'Nothing' when the index is out of range.
atMay :: Int -> [a] -> Maybe a
atMay i xs
    | i < 0 = Nothing
    | otherwise = case drop i xs of
        x : _ -> Just x
        [] -> Nothing

-- | Apply a function at one index, leaving an out-of-range index alone.
adjustAt :: Int -> (a -> a) -> [a] -> [a]
adjustAt i f xs
    | i < 0 = xs
    | otherwise = case splitAt i xs of
        (prefix, x : suffix) -> prefix ++ f x : suffix
        _ -> xs
