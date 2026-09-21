{-# LANGUAGE OverloadedStrings #-}

-- | Draw retained source names and type groups of the typed expression generators.
module Main (main) where

import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Data.Tree (Tree, drawTree, flatten)

import qualified Data.CFTA as FTA
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Equality.Constraint (subsumptionOrderedEclasses, unPathEClass)
import qualified Data.CFTA.Gen.Equality as ECTAGen
import Data.CFTA.Gen.TypedExpressionLanguage (
    Type (TInt),
    depthByType,
    expressionGenAtDepth,
    recursiveExpressions,
 )
import Data.CFTA.Path (Path, unPath)
import Data.CFTA.Symbol (Symbol (Symbol))

-- | Print finite and recursive diagnostic graphs.
main :: IO ()
main = do
    putStrLn "Source choices retain names and signatures. Equality witnesses show their type groups."
    putStrLn "State names q0, q1, ... are local to each drawing."
    putStrLn "Locations use @alternative:child/..., with @root for the initial state."
    drawSupport "Exact depth 1: both result types" $ expressionGenAtDepth 1
    drawSupport "Exact depth 1: TInt" $ ECTAGen.atKey TInt $ depthByType 1
    drawSupport "Recursive: TInt" $ ECTAGen.atKey TInt recursiveExpressions

-- | Read retained diagnostic metadata and draw its state and transition labels.
drawSupport :: String -> ECTAGen.ECTAGen value -> IO ()
drawSupport title generator = do
    inspection <- either (fail . show) pure $ ECTAGen.inspect generator
    tree <- either (fail . show) pure $ ECTA.toTree $ ECTAGen.inspectionGraph inspection
    putStrLn $ "\n" <> title <> maybe "" (\name -> " [" <> Text.unpack name <> "]") (ECTAGen.inspectionName inspection)
    putStrLn $ drawTree $ renderTree tree

-- | Assign local state names from typed labels and preserve all transitions.
renderTree ::
    Tree
        ( Either
            (FTA.StateView (ECTA.Node (ECTAGen.InspectionSymbol Symbol) ECTA.EqConstraints))
            (ECTA.Edge (ECTAGen.InspectionSymbol Symbol) ECTA.EqConstraints)
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
renderTransition :: ECTA.Edge (ECTAGen.InspectionSymbol Symbol) ECTA.EqConstraints -> String
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
renderSymbol :: ECTAGen.InspectionSymbol Symbol -> String
renderSymbol (ECTAGen.InspectionSymbol _ (Just label)) = Text.unpack label
renderSymbol (ECTAGen.InspectionSymbol label Nothing) = case label of
    ECTAGen.Label (Symbol symbol) -> Text.unpack symbol
    ECTAGen.CenterKeyed -> "operation"
    ECTAGen.ArgKeyed -> "argument"
    ECTAGen.AtKey -> "select type"
    ECTAGen.Family -> "type alternative"
    ECTAGen.Choice index -> "choice " <> show index
    private -> "gen:" <> show private

-- | Print a path as child indexes separated by dots.
renderPath :: Path -> String
renderPath target = case unPath target of
    [] -> "root"
    indexes -> intercalate "." $ map show indexes
