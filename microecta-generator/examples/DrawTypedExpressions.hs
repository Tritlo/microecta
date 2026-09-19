{-# LANGUAGE OverloadedStrings #-}

-- | Draw retained source names and type groups of the typed expression generators.
module Main (main) where

import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Data.Tree (Tree, drawTree, flatten)

import qualified Data.CFTA as FTA
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Equality.Constraints (Path, subsumptionOrderedEclasses, unPath, unPathEClass)
import Data.CFTA.Symbol (Symbol (Symbol))
import qualified Data.ECTA.Gen as Gen
import Data.ECTA.Gen.Example.TypedExpressionLanguage (
    Type (TInt),
    depthByType,
    expressionGenAtDepth,
    recursiveExpressions,
 )

-- | Print finite and recursive diagnostic graphs.
main :: IO ()
main = do
    putStrLn "Source choices retain names and signatures. Equality witnesses show their type groups."
    putStrLn "State names q0, q1, ... are local to each drawing."
    putStrLn "Locations use @alternative:child/..., with @root for the initial state."
    drawSupport "Exact depth 1: both result types" $ expressionGenAtDepth 1
    drawSupport "Exact depth 1: TInt" $ Gen.atKey TInt $ depthByType 1
    drawSupport "Recursive: TInt" $ Gen.atKey TInt recursiveExpressions

-- | Read retained diagnostic metadata and draw its state and transition labels.
drawSupport :: String -> Gen.ECTAGen gen value -> IO ()
drawSupport title generator = do
    inspection <- either (fail . show) pure $ Gen.inspect generator
    tree <- either (fail . show) pure $ ECTA.toTree $ Gen.inspectionGraph inspection
    putStrLn $ "\n" <> title <> maybe "" (\name -> " [" <> Text.unpack name <> "]") (Gen.inspectionName inspection)
    putStrLn $ drawTree $ renderTree tree

-- | Assign local state names from typed labels and preserve all transitions.
renderTree ::
    Tree
        ( Either
            (FTA.StateView (ECTA.Node Gen.InspectionSymbol ECTA.EqConstraints))
            (ECTA.Edge Gen.InspectionSymbol ECTA.EqConstraints)
        ) ->
    Tree String
renderTree tree = fmap (either renderState renderTransition) tree
  where
    names = Map.fromList $ zip [state | Left (FTA.Expanded _ state) <- flatten tree] [0 :: Int ..]
    name state = "q" <> show (names Map.! state)
    renderState view = case fmap label view of
        FTA.Expanded _ rendered -> rendered
        FTA.Recursive _ rendered -> "mu " <> rendered
        FTA.Shared _ rendered -> "ref " <> rendered
      where
        label state = name state <> " @" <> renderViewPath (FTA.viewPath view)

-- | Print the location of this occurrence in the finite graph view.
renderViewPath :: FTA.ViewPath -> String
renderViewPath [] = "root"
renderViewPath steps = intercalate "/" [show alternative <> ":" <> show child | (alternative, child) <- steps]

-- | Keep the symbol and print equalities with child paths instead of trie internals.
renderTransition :: ECTA.Edge Gen.InspectionSymbol ECTA.EqConstraints -> String
renderTransition transition = renderSymbol (ECTA.edgeSymbol transition) <> equalities
  where
    equalities = case subsumptionOrderedEclasses $ ECTA.edgeConstraint transition of
        Nothing -> " [false]"
        Just [] -> ""
        Just classes ->
            " ["
                <> intercalate ", " [intercalate " = " $ map renderPath $ unPathEClass paths | paths <- classes]
                <> "]"

-- | Prefer retained domain names and use short names for construction steps.
renderSymbol :: Gen.InspectionSymbol -> String
renderSymbol (Gen.InspectionSymbol _ (Just label)) = Text.unpack label
renderSymbol (Gen.InspectionSymbol (Symbol symbol) Nothing) = Text.unpack $
    case Text.stripPrefix "$ecta-gen/" symbol of
        Just "center-keyed" -> "operation"
        Just "arg-keyed" -> "argument"
        Just "at-key" -> "select type"
        Just "family" -> "type alternative"
        Just private -> maybe ("gen:" <> private) ("choice " <>) $ Text.stripPrefix "frequency/" private
        Nothing -> symbol

-- | Print a path as child indexes separated by dots.
renderPath :: Path -> String
renderPath target = case unPath target of
    [] -> "root"
    indexes -> intercalate "." $ map show indexes
