{-# LANGUAGE OverloadedStrings #-}

{- | Tiny term-search helpers retained from @ecta@.

The full search engine and Hoogle dataset are intentionally absent. This module
keeps the two operations downstream code uses: constrain a term node by a type
node with 'filterType', and run the standard reduction loop with 'reduceFully'.
-}
module Application.TermSearch.TermSearch (
    filterType,
    reduceFully,
) where

import Data.ECTA
import Data.ECTA.Paths
import Utility.Fixpoint

-- | Constrain a term-search node by equating its type child with a type node.
filterType :: Node -> Node -> Node
filterType n t =
    Node [mkEdge "filter" [t, n] (mkEqConstraints [[path [0], path [1, 0]]])]

-- | Repeatedly propagate constraints and remove redundant edges to a fixpoint.
reduceFully :: Node -> Node
reduceFully = fixUnbounded (withoutRedundantEdges . reducePartially)
