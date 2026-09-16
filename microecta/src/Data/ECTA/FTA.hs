{- | View an ECTA through the ordinary FTA structure it refines.

The conversion preserves equality constraints as transition annotations. It
does not solve or discard them.
-}
module Data.ECTA.FTA (
    ECTAState,
    ECTAFTAError (..),
    toFTA,
    toTree,
) where

import Data.Tree (Tree)
import Data.Typeable (Typeable)

import Data.Hashable (Hashable)

import Data.ECTA.Internal.ECTA.Type (Node, toInterned)
import Data.ECTA.Paths (EqConstraints)
import qualified Data.Tree.FTA as FTA
import qualified Data.Tree.FTA.Interned as Common

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

{- | Display the reachable ECTA graph with 'Data.Tree.drawTree'.

Transition labels retain equality constraints. Cycles end with @mu@ references;
other shared states end with @ref@ references. Open recursive variables fail as
in 'toFTA'. This operation does not enumerate terms or solve constraints.
-}
toTree ::
    (Hashable symbol, Ord symbol, Typeable symbol, Show symbol) =>
    Node symbol ->
    Either (ECTAFTAError symbol) (Tree String)
toTree = fmap FTA.toTree . toFTA
