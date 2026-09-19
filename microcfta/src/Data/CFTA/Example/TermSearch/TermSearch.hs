{-# LANGUAGE OverloadedStrings #-}

{- | Tiny term-search helpers retained from @ecta@.

The full search engine and Hoogle dataset are intentionally absent. This module
keeps the two operations downstream code uses: constrain a term node by a type
node with 'filterType', and run the standard reduction loop with 'reduceFully'.
-}
module Data.CFTA.Example.TermSearch.TermSearch (
    filterType,
    reduceFully,
) where

import Data.CFTA.Equality
import Data.CFTA.Equality.Constraints
import Data.CFTA.Interned.Operations (fixUnbounded)
import Data.CFTA.Symbol (Symbol)

-- | Constrain a term-search node by equating its type child with a type node.
filterType :: Node Symbol -> Node Symbol -> Node Symbol
filterType n t =
    Node [mkEdge "filter" [t, n] (mkEqConstraints [[path [0], path [1, 0]]])]

-- | Repeatedly propagate constraints and remove redundant edges to a fixpoint.
reduceFully :: Node Symbol -> Node Symbol
reduceFully = fixUnbounded (withoutRedundantEdges . reducePartially)
