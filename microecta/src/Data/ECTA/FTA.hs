{- | View an ECTA through the ordinary FTA structure it refines.

The conversion preserves equality constraints as transition annotations. It
does not solve or discard them.
-}
module Data.ECTA.FTA (
    ECTAState,
    ECTAFTAError (..),
    ViewPath,
    StateView (..),
    toFTA,
    toTree,
) where

import Data.Tree (Tree)
import Data.Typeable (Typeable)

import Data.Bifunctor (bimap)
import Data.Hashable (Hashable)

import Data.CFTA (StateView (..), ViewPath)
import qualified Data.CFTA as FTA
import qualified Data.CFTA.Interned as Common
import Data.ECTA.Internal.ECTA.Type (Edge (ECTAEdge), Node, fromInterned, toInterned)
import Data.ECTA.Paths (EqConstraints)

-- | Stable state identity in the FTA view of an ECTA.
type ECTAState = Common.InternedState

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
toFTA root = case Common.toFTA (toInterned root) of
    Left Common.OpenNode -> Left OpenECTA
    Left (Common.InvalidFTA err) -> Left (InvalidFTA err)
    Right graph -> Right graph

{- | Expose the reachable ECTA graph as typed state and transition labels.

The labels retain the original nodes and edges, including equality constraints.
'Recursive' and 'Shared' labels identify references. Map the labels to strings
before using @drawTree@. Open recursive variables return 'OpenECTA'. This view
does not require a ranked alphabet, enumerate terms, or solve constraints.
-}
toTree ::
    (Hashable symbol, Typeable symbol) =>
    Node symbol ->
    Either (ECTAFTAError symbol) (Tree (Either (StateView (Node symbol)) (Edge symbol)))
toTree root = case Common.toTree (toInterned root) of
    Left Common.OpenNode -> Left OpenECTA
    Left (Common.InvalidFTA err) -> Left (InvalidFTA err)
    Right tree -> Right $ fmap (bimap (fmap fromInterned) ECTAEdge) tree
