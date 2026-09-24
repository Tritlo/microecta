-- | Optional display names carried beside the generator's semantic support.
module Data.CFTA.Gen.Internal.Inspection (
    InspectionSymbol (..),
    Inspection (..),
    plainSymbol,
    plainInspection,
    choiceInspection,
    labelInspection,
    joinInspection,
    drawInspection,
) where

import Data.CFTA.Constraint (Constraint (..), HasEqualities (..))
import Data.Hashable (Hashable)
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Data.CFTA (StateView (..), ViewPath)
import Data.CFTA.Equality (Edge (Edge), Node (Node), edgeConstraint, edgeSymbol, toTree)
import Data.CFTA.Equality.Constraint (subsumptionOrderedEclasses, unPathEClass)
import Data.CFTA.Gen.Internal.Support
import Data.CFTA.Gen.Label (Label (..))
import Data.CFTA.Path (Path, unPath)

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

{- | Draw an inspection graph as an indented tree.

Each state line gives a local name, @q0@, @q1@, and so on, and the location of
the occurrence as @\@alternative:child/...@, or @\@root@. A state that is
already on the current path is drawn as @mu@, and a state that an earlier path
expanded is drawn as @ref@. A transition line gives the display name of the
transition when it has one. Otherwise it gives the symbol with 'show', or a
short name for a construction step. The equality classes of the transition
follow in brackets, and @[false]@ marks contradictory equalities. The drawing
does not show other parts of a constraint.
-}
drawInspection ::
    (Show symbol, Constraint constraint, Hashable symbol, Typeable symbol) =>
    Inspection symbol constraint -> String
drawInspection inspection = case toTree (inspectionGraph inspection) of
    Left _ -> "open inspection graph: a recursive variable is free at the root"
    Right tree ->
        let names = Map.fromList $ zip [state | Left (Expanded _ state) <- Tree.flatten tree] [0 :: Int ..]
            name state = maybe "q?" (("q" <>) . show) (Map.lookup state names)
            drawState view = case view of
                Expanded _ state -> located view $ name state
                Recursive _ state -> "mu " <> located view (name state)
                Shared _ state -> "ref " <> located view (name state)
         in Tree.drawTree $ fmap (either drawState drawTransition) tree
  where
    located view text = text <> " @" <> drawViewPath (viewPath view)
    drawTransition transition =
        drawSymbol (edgeSymbol transition) <> drawEqualities (equalities $ edgeConstraint transition)
    drawEqualities classes = case subsumptionOrderedEclasses classes of
        Nothing -> " [false]"
        Just [] -> ""
        Just ordered -> " [" <> intercalate ", " [intercalate " = " $ map drawPath $ unPathEClass paths | paths <- ordered] <> "]"

-- | Print a location in the tree view as alternative and child positions.
drawViewPath :: ViewPath -> String
drawViewPath [] = "root"
drawViewPath steps = intercalate "/" [show alternative <> ":" <> show child | (alternative, child) <- steps]

-- | Print a path as child positions separated by dots.
drawPath :: Path -> String
drawPath target = case unPath target of
    [] -> "root"
    positions -> intercalate "." $ map show positions

-- | Prefer the display name, and give construction steps short names.
drawSymbol :: (Show symbol) => InspectionSymbol symbol -> String
drawSymbol (InspectionSymbol _ (Just name)) = Text.unpack name
drawSymbol (InspectionSymbol label Nothing) = case label of
    Label symbol -> show symbol
    Choice index -> "choice " <> show index
    CenterKeyed -> "operation"
    ArgKeyed -> "argument"
    AtKey -> "at key"
    Family -> "family member"
    step -> show step
