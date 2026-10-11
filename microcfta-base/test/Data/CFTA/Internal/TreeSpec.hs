{- | The contract of the tree searches over rows.

A row maps a key to its alternatives, and an alternative has a symbol and the
keys of its children. The searches must agree with the direct recursion on
the rows: 'termsUpToBy' lists each term of depth at most the bound that the
check accepts, once, and 'acceptsBy' accepts exactly those terms.
-}
module Data.CFTA.Internal.TreeSpec (spec) where

import Data.Functor.Identity (Identity (..))
import Data.Hashable (hash)
import qualified Data.Set as Set
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Gen, chooseInt, elements, forAll, sublistOf, vectorOf)

import Data.CFTA.Index (Depth (..))
import Data.CFTA.Internal.Tree (acceptsBy, termLevelsBy, termsUpToBy)
import Data.CFTA.Term (Term, pattern Node)

type Alternative = (Char, [Int])

type Rows = [(Int, [Alternative])]

spec :: Spec
spec = describe "the tree searches" $ do
    prop "termsUpToBy lists each accepted term up to the bound once" $
        forAll example $ \(rows, bound) ->
            let listed = runIdentity (termsUpToBy fst snd accept rows (Depth bound) 0)
             in length listed == Set.size (Set.fromList listed)
                    && Set.fromList listed == direct rows check bound 0

    prop "termLevelsBy gives the levels of termsUpToBy that accepts every term" $
        forAll example $ \(rows, bound) ->
            concat (take (bound + 1) (termLevelsBy rows 0))
                == runIdentity (termsUpToBy fst snd (\_ _ _ -> pure True) rows (Depth bound) 0)

    prop "acceptsBy accepts exactly the terms that the check accepts" $
        forAll example $ \(rows, bound) ->
            let candidates = Set.unions [direct rows (\_ _ _ -> True) bound key | key <- keys]
                accepted = direct rows check bound 0
             in all
                    (\term -> runIdentity (acceptsBy (outgoing rows) fst snd accept 0 term) == Set.member term accepted)
                    candidates
  where
    accept key alternative term = pure (check key alternative term)

-- | A check that rejects about one candidate in four, by hash.
check :: Int -> Alternative -> Term Char -> Bool
check key alternative term = hash (key, alternative, term) `mod` 4 /= 0

-- | Each term of depth at most the bound that a key accepts, by direct recursion.
direct :: Rows -> (Int -> Alternative -> Term Char -> Bool) -> Int -> Int -> Set.Set (Term Char)
direct rows accepts bound key
    | bound < 0 = Set.empty
    | otherwise =
        Set.fromList
            [ term
            | alternative@(symbol, childKeys) <- outgoing rows key
            , children <- traverse (Set.toList . direct rows accepts (bound - 1)) childKeys
            , let term = Node symbol children
            , accepts key alternative term
            ]

outgoing :: Rows -> Int -> [Alternative]
outgoing rows key = concat (lookup key rows)

keys :: [Int]
keys = [0, 1, 2]

{- | Rows over three keys, and a bound up to two. The root key always has a
row, and the other keys can have none. Two symbols make alternatives that
share a symbol and an arity likely.
-}
example :: Gen (Rows, Int)
example = (,) <$> rows <*> chooseInt (0, 2)
  where
    rows = do
        others <- sublistOf (drop 1 keys)
        traverse (\key -> (,) key <$> alternatives) (0 : others)
    alternatives = do
        count <- chooseInt (1, 3)
        vectorOf count $ (,) <$> elements "ab" <*> (elements [0, 0, 1, 2] >>= \arity -> vectorOf arity (elements keys))
