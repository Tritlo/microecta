{-# LANGUAGE OverloadedStrings #-}

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

filterType :: Node -> Node -> Node
filterType n t =
    Node [mkEdge "filter" [t, n] (mkEqConstraints [[path [0], path [1, 0]]])]

reduceFully :: Node -> Node
reduceFully = fixUnbounded (withoutRedundantEdges . reducePartially)

reduceFullyAndLog :: Node -> IO Node
reduceFullyAndLog = fmap fst . reduceFullyAndLog' 30

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
