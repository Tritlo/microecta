{- | Patterns over the terms of a language.

A 'Template' matches a term by its root symbol and child positions. 'Hole'
matches any complete subtree. Exact patterns require the complete child list;
prefix patterns constrain only the leading children. 'restrict' keeps exactly
the matching terms of an interned graph, and 'restrictFTA' those of an
explicit-state automaton. Neither interprets transition annotations; a
constraint theory reduces its constraints afterwards.
-}
module Data.CFTA.Template (
    Template (..),
    matchesTemplate,
    restrict,
    restrictFTA,
) where

import Data.Either (fromRight)
import Data.Hashable (Hashable)
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.CFTA (FTA, Transition (..))
import qualified Data.CFTA as FTA
import Data.CFTA.Constraint (Constraint)
import Data.CFTA.Interned.Operations (unfoldOuterRec)
import Data.CFTA.Interned.Type

-- | Pattern over first-order terms.
data Template symbol
    = -- | Match any complete subtree.
      Hole
    | -- | Match any root symbol with exactly these children.
      AnyNode ![Template symbol]
    | -- | Match this root symbol with exactly these children.
      TemplateNode !symbol ![Template symbol]
    | -- | Match any root symbol whose children begin with this prefix.
      AnyPrefix ![Template symbol]
    | -- | Match this root symbol when its children begin with this prefix.
      TemplatePrefix !symbol ![Template symbol]
    deriving (Eq, Ord, Read, Show)

{- | The pattern for each child of a constructor with the given symbol and
arity, or 'Nothing' when the constructor cannot match.
-}
childTemplates :: (Eq symbol) => Template symbol -> symbol -> Int -> Maybe [Template symbol]
childTemplates Hole _ arity = Just (replicate arity Hole)
childTemplates (AnyNode templates) _ arity = exact templates arity
childTemplates (TemplateNode symbol templates) actual arity
    | symbol == actual = exact templates arity
    | otherwise = Nothing
childTemplates (AnyPrefix templates) _ arity = prefix templates arity
childTemplates (TemplatePrefix symbol templates) actual arity
    | symbol == actual = prefix templates arity
    | otherwise = Nothing

exact, prefix :: [Template symbol] -> Int -> Maybe [Template symbol]
exact templates arity
    | length templates == arity = Just templates
    | otherwise = Nothing
prefix templates arity
    | length templates <= arity = Just (templates ++ replicate (arity - length templates) Hole)
    | otherwise = Nothing

-- | Test a concrete term against a template.
matchesTemplate :: (Eq symbol) => Template symbol -> Tree.Tree symbol -> Bool
matchesTemplate template (Tree.Node symbol children) =
    maybe False (\templates -> and (zipWith matchesTemplate templates children)) $
        childTemplates template symbol (length children)

-- | Keep exactly the terms of an interned graph that match a template.
restrict ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Template symbol -> Node symbol constraint -> Node symbol constraint
restrict Hole node = node
restrict (AnyPrefix []) node = node
restrict _ EmptyNode = EmptyNode
restrict template node@(Mu _) = restrict template (unfoldOuterRec node)
restrict template (Node edges) = Node (mapMaybe (restrictEdge template) edges)
restrict _ (Rec _) = error "restrict: unexpected free recursive reference"

restrictEdge ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Template symbol -> Edge symbol constraint -> Maybe (Edge symbol constraint)
restrictEdge Hole edge = Just edge
restrictEdge (AnyPrefix []) edge = Just edge
restrictEdge template edge =
    (\templates -> setChildren edge (zipWith restrict templates children))
        <$> childTemplates template (edgeSymbol edge) (length children)
  where
    children = edgeChildren edge

{- | Keep exactly the terms of an automaton that match a template.

Each result state pairs a source state with the pattern its terms must
match. Only reachable pairs are built.
-}
restrictFTA ::
    (Ord state, Ord symbol) =>
    Template symbol -> FTA state symbol constraint -> FTA (state, Template symbol) symbol constraint
restrictFTA template automaton =
    -- The input is ranked, so the restriction is ranked and validation cannot fail.
    fromRight (error "restrictFTA: the restriction of a ranked automaton is ranked")
        $ FTA.mkFTA initial
        $ build Set.empty [initial] []
  where
    initial = (FTA.initialState automaton, template)

    build _ [] rows = rows
    build visited (state : pending) rows
        | Set.member state visited = build visited pending rows
        | otherwise =
            build (Set.insert state visited) (concatMap transitionChildren outgoing <> pending) ((state, outgoing) : rows)
      where
        outgoing = restrictTransitions state

    restrictTransitions (state, wanted) = mapMaybe (restrictTransition wanted) (FTA.transitionsFrom automaton state)
    restrictTransition wanted transition =
        (\templates -> transition{transitionChildren = zip (transitionChildren transition) templates})
            <$> childTemplates wanted (transitionSymbol transition) (length $ transitionChildren transition)
