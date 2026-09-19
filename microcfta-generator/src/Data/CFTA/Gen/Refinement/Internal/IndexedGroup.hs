{-# LANGUAGE OverloadedStrings #-}

-- | Compact private ECTA support for a finite imported group.
module Data.CFTA.Gen.Refinement.Internal.IndexedGroup (indexedGroup) where

import qualified Data.Map.Strict as Map
import qualified Data.Tree as Tree

import qualified Data.CFTA.Equality as Core
import Data.CFTA.Equality.Constraints (EqConstraints)
import qualified Data.CFTA.Gen.Equality.QuickCheck as ECTA
import Data.CFTA.Symbol (Symbol)

{- | Represent each index below the bound with one binary-code term.

The support shares equal bounds and has logarithmic size. Native ECTA ranks
follow term size and edge order. They do not follow decoded integer order.
-}
indexedGroup :: Integer -> (Integer -> a) -> ECTA.ECTAGen a
indexedGroup bound valueAt
    | bound <= 0 = ECTA.elements []
    | otherwise = valueAt . decode <$> ECTA.atomic (ECTA.fromECTA support)
  where
    support = fst $ build bound Map.empty

-- | Reuse one support node for each distinct positive bound.
build ::
    Integer ->
    Map.Map Integer (Core.Node Symbol EqConstraints) ->
    (Core.Node Symbol EqConstraints, Map.Map Integer (Core.Node Symbol EqConstraints))
build bound cache
    | Just existing <- Map.lookup bound cache = (existing, cache)
    | bound == 1 = retain (Core.Node [Core.Edge "$microlta-index-zero" []]) cache
    | otherwise =
        let (evenNode, withEven) = build ((bound + 1) `div` 2) cache
            (oddNode, withOdd) = build (bound `div` 2) withEven
         in retain
                ( Core.Node
                    [ Core.Edge "$microlta-index-even" [evenNode]
                    , Core.Edge "$microlta-index-odd" [oddNode]
                    ]
                )
                withOdd
  where
    retain support updated = (support, Map.insert bound support updated)

-- | Decode a term from the private nullary and unary alphabet.
decode :: Tree.Tree Symbol -> Integer
decode (Tree.Node symbol [])
    | symbol == "$microlta-index-zero" = 0
decode (Tree.Node symbol [child])
    | symbol == "$microlta-index-even" = 2 * decode child
    | symbol == "$microlta-index-odd" = 2 * decode child + 1
decode _ = error "indexedGroup: invalid private code term"
