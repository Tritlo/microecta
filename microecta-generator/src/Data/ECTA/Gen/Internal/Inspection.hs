-- | Optional display names carried beside the generator's semantic support.
module Data.ECTA.Gen.Internal.Inspection (
    InspectionSymbol (..),
    Inspection (..),
    plainSymbol,
    plainInspection,
    choiceInspection,
    labelInspection,
    joinInspection,
) where

import qualified Control.Monad.State.Strict as State
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import GHC.Generics (Generic)

import Data.CFTA.Equality (Edge (Edge), Node (Node), edgeChildren, edgeConstraint, edgeSymbol, mkEdge)
import qualified Data.CFTA.Equality as Core
import Data.CFTA.Equality.Constraints (EqConstraints)
import Data.CFTA.Symbol (Symbol)
import Data.ECTA.Gen.Internal.Support

{- | An original support symbol with an optional source or group name.

Names participate in diagnostic sharing. Two source occurrences can have the
same original symbol and different meanings. Use 'originalSymbol' to inspect
the support symbol. Display names do not participate in generation.
-}
data InspectionSymbol = InspectionSymbol
    { originalSymbol :: Symbol
    , displayLabel :: Maybe Text
    }
    deriving (Eq, Ord, Show, Generic)

instance Hashable InspectionSymbol

{- | A named diagnostic graph retained by an inspectable generator.

The graph retains construction structure and equality obligations. It is not
a replacement for the semantic support: diagnostic names can distinguish
otherwise equal nodes, and this graph does not run equality reduction.
All fields are lazy. Reading counts or decoding ranks does not build it.
-}
data Inspection = Inspection
    { inspectionName :: Maybe Text
    , inspectionGraph :: Node InspectionSymbol EqConstraints
    }
    deriving (Show)

-- | Retain a symbol without adding a display name.
plainSymbol :: Symbol -> InspectionSymbol
plainSymbol symbol = InspectionSymbol symbol Nothing

-- | Copy an imported graph with its labels, constraints, and bound references.
plainInspection :: Node Symbol EqConstraints -> Inspection
plainInspection root = Inspection Nothing $ State.evalState (visit Map.empty root) Map.empty
  where
    visit environment node = do
        memo <- State.get
        case Map.lookup node memo of
            Just copied -> pure copied
            Nothing -> do
                copied <- case node of
                    Core.EmptyNode -> pure Core.EmptyNode
                    Core.Rec ident -> pure $ Map.findWithDefault (Core.Rec ident) ident environment
                    Core.InternedMu binder ->
                        pure $ Core.createMu $ \self ->
                            State.evalState
                                ( visit
                                    (Map.insert (Core.RecInt $ Core.internedMuId binder) self environment)
                                    (Core.internedMuBody binder)
                                )
                                Map.empty
                    Core.InternedNode payload -> Node <$> traverse (copyEdge environment) (Core.internedNodeEdges payload)
                State.modify' $ Map.insert node copied
                pure copied
    copyEdge environment edge = do
        children <- traverse (visit environment) $ edgeChildren edge
        pure $ mkEdge (plainSymbol $ edgeSymbol edge) children $ edgeConstraint edge

-- | Preserve choice order and a name common to every alternative.
choiceInspection :: [Inspection] -> Inspection
choiceInspection alternatives =
    Inspection
        commonName
        ( Node
            [ Edge (plainSymbol $ frequencySymbol index) [inspectionGraph alternative]
            | (index, alternative) <- zip [0 ..] alternatives
            ]
        )
  where
    commonName = case map inspectionName alternatives of
        first : rest | all (== first) rest -> first
        _ -> Nothing

-- | Close one diagnostic child layer with the same domain constructor.
labelInspection :: Symbol -> Inspection -> Inspection
labelInspection symbol inspection =
    inspection
        { inspectionGraph =
            labelSupportWith originalSymbol (plainSymbol symbol) $ inspectionGraph inspection
        }

-- | Join diagnostic groups and name each equality witness from its argument.
joinInspection :: Int -> Inspection -> [Inspection] -> Inspection
joinInspection component operation arguments =
    Inspection Nothing $
        joinNodeWith namedSymbol component (inspectionGraph operation) (map inspectionGraph arguments)
  where
    names =
        Map.fromList
            [ (argKeySymbol component position, inspectionName argument)
            | (position, argument) <- zip [0 ..] arguments
            ]
    namedSymbol symbol = InspectionSymbol symbol $ Map.findWithDefault Nothing symbol names
