-- | Find accepted shrink targets through a shared graph of rejected sources.
module Data.LTA.Gen.Internal.ShrinkSearch (acceptedShrinks) where

import qualified Data.Set as Set

{- | Emit accepted targets before following rejected targets in depth-first order.

The starting source must belong to the accepted language. The first argument
is that language's exact cardinality. Successors must already satisfy their
shrink conditions. The lookup maps source occurrences to accepted ranks.

Each rejected source is expanded at most once. Repeated accepted ranks are
omitted. The search stops when every other accepted rank has been emitted.
Candidate lists remain lazy, and the search makes no solver calls.
-}
acceptedShrinks ::
    Integer ->
    (Integer -> [Integer]) ->
    (Integer -> Maybe Integer) ->
    Integer ->
    [Integer]
acceptedShrinks acceptedCount successors acceptedRankFor source
    | acceptedCount <= 1 = []
    | otherwise =
        scan
            (Set.singleton source)
            (maybe Set.empty Set.singleton $ acceptedRankFor source)
            (acceptedCount - 1)
            []
            []
            (successors source)
  where
    visit _ _ remaining _ | remaining <= 0 = []
    visit _ _ _ [] = []
    visit expanded emitted remaining (current : pending)
        | Set.member current expanded = visit expanded emitted remaining pending
        | otherwise =
            scan
                (Set.insert current expanded)
                emitted
                remaining
                []
                pending
                (successors current)

    scan _ _ remaining _ _ _ | remaining <= 0 = []
    scan expanded emitted remaining rejected pending [] =
        visit expanded emitted remaining (reverse rejected <> pending)
    scan expanded emitted remaining rejected pending (candidate : rest)
        | Set.member candidate expanded =
            scan expanded emitted remaining rejected pending rest
        | otherwise = case acceptedRankFor candidate of
            Just rank
                | Set.member rank emitted ->
                    scan expanded emitted remaining rejected pending rest
                | otherwise ->
                    rank
                        : scan expanded (Set.insert rank emitted) (remaining - 1) rejected pending rest
            Nothing ->
                scan expanded emitted remaining (candidate : rejected) pending rest
