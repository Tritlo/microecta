{-# LANGUAGE OverloadedStrings #-}

{- | Tiny term-search helpers retained from @ecta@.

The full search engine and Hoogle dataset are intentionally absent. This module
keeps the two operations downstream code uses: constrain a term node by a type
node with 'filterType', and run the standard reduction loop with 'reduceFully'.
-}
module Application.TermSearch.TermSearch (
    filterType,
    reduceFully,
    reduceFullyAndLog,
    reduceFullyAndLog',
) where

import System.IO (hFlush, stdout)

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

-- | Run 'reduceFully' while logging graph size for each round.
reduceFullyAndLog :: Node -> IO Node
reduceFullyAndLog = fmap fst . reduceFullyAndLog' 30

-- | Bounded logging variant of 'reduceFullyAndLog'.
reduceFullyAndLog' :: Int -> Node -> IO (Node, Int)
reduceFullyAndLog' maxRounds = go 0
  where
    go :: Int -> Node -> IO (Node, Int)
    go i n = do
        putStrLn $
            "Round "
                ++ show i
                ++ ": "
                ++ show (nodeCount n)
                ++ " nodes, "
                ++ show (edgeCount n)
                ++ " edges"
        hFlush stdout
        let n' = withoutRedundantEdges (reducePartially n)
        if n == n' || i >= maxRounds
            then return (n, i)
            else go (i + 1) n'
