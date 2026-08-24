{- | Explicit patterns for concrete terms and ECTA languages.

A 'Template' separates wildcards and prefix matching from ordinary term
symbols. Exact constructors require the complete child list; prefix
constructors constrain only the leading children and leave the rest
unconstrained.
-}
module Data.ECTA.Template (
    Template (..),
    matchesTemplate,
    termsMatching,
) where

import Data.Maybe (mapMaybe)

import Data.ECTA.Internal.ECTA.Operations (reducePartially)
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Internal.Term

-- | Pattern over first-order terms.
data Template
    = -- | Match any complete subtree.
      Hole
    | -- | Match any root symbol with exactly these children.
      AnyNode ![Template]
    | -- | Match this root symbol with exactly these children.
      TemplateNode !Symbol ![Template]
    | -- | Match any root symbol whose children begin with this prefix.
      AnyPrefix ![Template]
    | -- | Match this root symbol when its children begin with this prefix.
      TemplatePrefix !Symbol ![Template]
    deriving (Eq, Ord, Read, Show)

-- | Test a concrete term against a template.
matchesTemplate :: Template -> Term -> Bool
matchesTemplate Hole _ = True
matchesTemplate (AnyNode templates) (Term _ children) =
    exactChildrenMatch templates children
matchesTemplate (TemplateNode symbol templates) (Term termSymbol children) =
    symbol == termSymbol && exactChildrenMatch templates children
matchesTemplate (AnyPrefix templates) (Term _ children) =
    childPrefixMatches templates children
matchesTemplate (TemplatePrefix symbol templates) (Term termSymbol children) =
    symbol == termSymbol && childPrefixMatches templates children

exactChildrenMatch :: [Template] -> [Term] -> Bool
exactChildrenMatch templates children =
    length templates == length children && childPrefixMatches templates children

childPrefixMatches :: [Template] -> [Term] -> Bool
childPrefixMatches [] _ = True
childPrefixMatches (template : templates) (child : children) =
    matchesTemplate template child && childPrefixMatches templates children
childPrefixMatches _ [] = False

{- | Keep exactly the terms in a node that match a template.

The original equality constraints are retained and reduced after the child
languages have been restricted. In particular, a 'Hole' at one constrained
position can be narrowed by a concrete template at an equal position.
-}
termsMatching :: Template -> Node -> Node
termsMatching Hole = id
termsMatching (AnyPrefix []) = id
termsMatching template = reducePartially . restrictNode template

restrictNode :: Template -> Node -> Node
restrictNode Hole node = node
restrictNode (AnyPrefix []) node = node
restrictNode _ EmptyNode = EmptyNode
restrictNode template node@(Mu body) = restrictNode template (body node)
restrictNode template (Node edges) = Node (mapMaybe (restrictEdge template) edges)
restrictNode _ (Rec _) = error "termsMatching: unexpected free recursive reference"

restrictEdge :: Template -> Edge -> Maybe Edge
restrictEdge Hole edge = Just edge
restrictEdge (AnyNode templates) edge = exactEdge templates edge
restrictEdge (TemplateNode symbol templates) edge
    | symbol == edgeSymbol edge = exactEdge templates edge
    | otherwise = Nothing
restrictEdge (AnyPrefix templates) edge = prefixEdge templates edge
restrictEdge (TemplatePrefix symbol templates) edge
    | symbol == edgeSymbol edge = prefixEdge templates edge
    | otherwise = Nothing

exactEdge :: [Template] -> Edge -> Maybe Edge
exactEdge templates edge
    | length templates == length children =
        Just $ setChildren edge (zipWith restrictNode templates children)
    | otherwise = Nothing
  where
    children = edgeChildren edge

prefixEdge :: [Template] -> Edge -> Maybe Edge
prefixEdge templates edge
    | length templates <= length children =
        let (prefix, suffix) = splitAt (length templates) children
         in Just $ setChildren edge (zipWith restrictNode templates prefix ++ suffix)
    | otherwise = Nothing
  where
    children = edgeChildren edge
