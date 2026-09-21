-- | Optional display names carried beside the generator's semantic support.
module Data.CFTA.Gen.Internal.Inspection (
    InspectionSymbol (..),
    Inspection (..),
    plainSymbol,
    plainInspection,
    choiceInspection,
    labelInspection,
    joinInspection,
) where

import Data.CFTA.Constraint (Constraint (..), HasEqualities (..))
import Data.Hashable (Hashable)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Data.CFTA.Equality (Edge (Edge), Node (Node))
import Data.CFTA.Gen.Internal.Support
import Data.CFTA.Gen.Label (Label (..))

{- | An original support label with an optional source or group name.

Names participate in diagnostic sharing. Two source occurrences can have the
same original label and different meanings. Use 'originalSymbol' to inspect
the support label. Display names do not participate in generation.
-}
data InspectionSymbol symbol = InspectionSymbol
    { originalSymbol :: Label symbol
    , displayLabel :: Maybe Text
    }
    deriving (Eq, Ord, Show, Generic)

instance (Hashable symbol) => Hashable (InspectionSymbol symbol)

{- | A named diagnostic graph retained by an inspectable generator.

The graph retains construction structure and equality obligations. It is not
a replacement for the semantic support: diagnostic names can distinguish
otherwise equal nodes, and this graph does not run equality reduction.
All fields are lazy. Reading counts or decoding ranks does not build it.
-}
data Inspection symbol constraint = Inspection
    { inspectionName :: Maybe Text
    , inspectionGraph :: Node (InspectionSymbol symbol) constraint
    }

deriving instance (Show symbol, Show constraint, Constraint constraint) => Show (Inspection symbol constraint)

-- | Retain a label without adding a display name.
plainSymbol :: Label symbol -> InspectionSymbol symbol
plainSymbol symbol = InspectionSymbol symbol Nothing

-- | Copy a support graph with its labels, constraints, and bound references.
plainInspection ::
    (Constraint constraint, Hashable symbol, Typeable symbol) =>
    Node (Label symbol) constraint -> Inspection symbol constraint
plainInspection = Inspection Nothing . relabel plainSymbol

-- | Preserve choice order and a name common to every alternative.
choiceInspection ::
    (Constraint constraint, Hashable symbol, Typeable symbol) =>
    [Inspection symbol constraint] -> Inspection symbol constraint
choiceInspection alternatives =
    Inspection
        commonName
        ( Node
            [ Edge (plainSymbol $ Choice index) [inspectionGraph alternative]
            | (index, alternative) <- zip [0 ..] alternatives
            ]
        )
  where
    commonName = case map inspectionName alternatives of
        first : rest | all (== first) rest -> first
        _ -> Nothing

-- | Close one diagnostic child layer with the same domain constructor.
labelInspection ::
    (Constraint constraint, Hashable symbol, Typeable symbol) =>
    symbol -> Inspection symbol constraint -> Inspection symbol constraint
labelInspection symbol inspection =
    inspection
        { inspectionGraph =
            labelSupportWith originalSymbol (plainSymbol $ Label symbol) $ inspectionGraph inspection
        }

-- | Join diagnostic groups and name each equality witness from its argument.
joinInspection ::
    (HasEqualities constraint, Hashable symbol, Typeable symbol) =>
    Int -> Inspection symbol constraint -> [Inspection symbol constraint] -> Inspection symbol constraint
joinInspection component operation arguments =
    Inspection Nothing $
        joinNodeWith namedSymbol component (inspectionGraph operation) (map inspectionGraph arguments)
  where
    names = Map.fromList $ zip [0 ..] $ map inspectionName arguments
    namedSymbol symbol@(ArgKey _ position) = InspectionSymbol symbol $ Map.findWithDefault Nothing position names
    namedSymbol symbol = plainSymbol symbol
