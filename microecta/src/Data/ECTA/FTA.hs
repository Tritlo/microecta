{-# LANGUAGE BangPatterns #-}

{- | View an ECTA through the ordinary FTA structure it refines.

The conversion preserves equality constraints as transition annotations. It
does not solve or discard them.
-}
module Data.ECTA.FTA (
    ECTAState,
    ECTAFTAError (..),
    toFTA,
) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Typeable (Typeable)

import Data.Hashable (Hashable)

import Data.ECTA (Edge, Node (EmptyNode), edgeChildren, edgeEcs, edgeSymbol, nodeEdges)
import Data.ECTA.Internal.ECTA.Type (freeVars, nodeIdentity)
import Data.ECTA.Paths (EqConstraints)
import qualified Data.Tree.FTA as FTA

-- | Stable state identity in the FTA view of an ECTA.
data ECTAState
    = EmptyECTAState
    | ECTAState !Int
    deriving (Eq, Ord, Show)

-- | Failure while exposing an ECTA as an FTA.
data ECTAFTAError symbol
    = -- | An open recursive variable does not denote an FTA state.
      OpenECTA
    | -- | The resulting transition graph was structurally invalid.
      InvalidFTA !(FTA.FTAError ECTAState symbol)
    deriving (Eq, Show)

-- | Expose the ranked transition graph underlying an ECTA.
toFTA ::
    (Hashable symbol, Ord symbol, Typeable symbol) =>
    Node symbol ->
    Either (ECTAFTAError symbol) (FTA.FTA ECTAState symbol EqConstraints)
toFTA root
    | not (Set.null $ freeVars root) = Left OpenECTA
    | otherwise =
        case FTA.mkFTA (stateOf root) (Map.toList $ collect Map.empty [root]) of
            Left err -> Left (InvalidFTA err)
            Right automaton -> Right automaton
  where
    collect seen [] = seen
    collect seen (node : rest)
        | Map.member state seen = collect seen rest
        | otherwise =
            collect
                (Map.insert state (map edgeTransition edges) seen)
                (concatMap edgeChildren edges <> rest)
      where
        state = stateOf node
        edges = nodeEdges node

    edgeTransition :: Edge symbol -> FTA.Transition ECTAState symbol EqConstraints
    edgeTransition edge =
        FTA.Transition
            (edgeSymbol edge)
            (map stateOf $ edgeChildren edge)
            (edgeEcs edge)

stateOf :: Node symbol -> ECTAState
stateOf EmptyNode = EmptyECTAState
stateOf node = ECTAState (nodeIdentity node)
