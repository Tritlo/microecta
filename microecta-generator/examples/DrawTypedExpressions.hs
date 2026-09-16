{-# LANGUAGE OverloadedStrings #-}

-- | Draw the actual supports of the typed expression generators.
module Main (main) where

import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Data.Tree (Tree, drawTree, flatten)

import qualified Data.ECTA as ECTA
import qualified Data.ECTA.Gen as Gen
import Data.ECTA.Gen.Example.TypedExpressionLanguage (
    Type (TInt),
    depthByType,
    expressionGenAtDepth,
    recursiveExpressions,
 )
import Data.ECTA.Paths (Path, subsumptionOrderedEclasses, unPath, unPathEClass)
import Data.ECTA.Term (Symbol (Symbol))
import qualified Data.Tree.FTA as FTA

-- | Print finite and recursive supports without changing the generators.
main :: IO ()
main = do
    putStrLn "Private $ecta-gen/ labels use gen:. Source indices and key IDs remain opaque."
    putStrLn "State names q0, q1, ... are local to each drawing."
    putStrLn "Locations use @alternative:child/..., with @root for the initial state."
    drawSupport "Exact depth 1: both result types" $ expressionGenAtDepth 1
    drawSupport "Exact depth 1: TInt" $ Gen.atKey TInt $ depthByType 1
    drawSupport "Recursive: TInt" $ Gen.atKey TInt recursiveExpressions

-- | Read a generator's existing support and draw its state and transition labels.
drawSupport :: String -> Gen.ECTAGen gen value -> IO ()
drawSupport title generator = do
    root <- either (fail . show) pure $ Gen.support generator
    tree <- either (fail . show) pure $ ECTA.toTree root
    putStrLn $ "\n" <> title
    putStrLn $ drawTree $ renderTree tree

-- | Assign local state names from typed labels and preserve all transitions.
renderTree ::
    Tree (Either (FTA.StateView (ECTA.Node Symbol)) (ECTA.Edge Symbol)) ->
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
renderTransition :: ECTA.Edge Symbol -> String
renderTransition transition = renderSymbol (ECTA.edgeSymbol transition) <> equalities
  where
    equalities = case subsumptionOrderedEclasses $ ECTA.edgeEcs transition of
        Nothing -> " [false]"
        Just [] -> ""
        Just classes ->
            " ["
                <> intercalate ", " [intercalate " = " $ map renderPath $ unPathEClass paths | paths <- classes]
                <> "]"

-- | Shorten the private namespace without decoding source indices or key IDs.
renderSymbol :: Symbol -> String
renderSymbol (Symbol symbol) =
    Text.unpack $ maybe symbol ("gen:" <>) $ Text.stripPrefix "$ecta-gen/" symbol

-- | Print a path as child indexes separated by dots.
renderPath :: Path -> String
renderPath target = case unPath target of
    [] -> "root"
    indexes -> intercalate "." $ map show indexes
