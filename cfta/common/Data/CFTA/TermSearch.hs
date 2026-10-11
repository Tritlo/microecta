{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}

{- | The term-search encoding of the ECTA paper, for the specs and benchmarks.

A type is a term: a type constructor with its arguments as children, and a
function type as the symbol @->@ with the arrow marker 'theArrowNode' and the
argument and result types. 'typeNode' encodes a Haskell type in this way, so
@typeNode \@(Maybe Int)@ is the node of the one term @Maybe(Int)@. A term
symbol has its type as its one child, and 'filterType' keeps the terms of one
type.
-}
module Data.CFTA.TermSearch (
    typeNode,
    theArrowNode,
    constFunc,
    filterType,
    reduceFully,
) where

import Data.Proxy (Proxy (Proxy))
import Data.String (fromString)
import Data.Typeable (TypeRep, Typeable, splitTyConApp, tyConName, typeRep, typeRepTyCon)

import Data.CFTA.Equality
import Data.CFTA.Symbol (Symbol)

-- | The node of one Haskell type, as in @typeNode \@(Int -> [Int])@.
typeNode :: forall a. (Typeable a) => Node Symbol
typeNode = typeRepNode $ typeRep $ Proxy @a

-- | The node of the type that a 'TypeRep' stands for.
typeRepNode :: TypeRep -> Node Symbol
typeRepNode typ = case splitTyConApp typ of
    (constructor, [argument, result])
        | constructor == typeRepTyCon (typeRep $ Proxy @(() -> ())) ->
            Node [Edge "->" [theArrowNode, typeRepNode argument, typeRepNode result]]
    (constructor, arguments) -> Node [Edge (fromString $ tyConName constructor) (map typeRepNode arguments)]

-- | The marker that is the first child of a function type.
theArrowNode :: Node Symbol
theArrowNode = Node [Edge "(->)" []]

-- | A term symbol with its type as its one child.
constFunc :: Symbol -> Node Symbol -> Edge Symbol
constFunc symbol typ = Edge symbol [typ]

-- | Keep the terms of a node whose type child equals a type node.
filterType :: Node Symbol -> Node Symbol -> Node Symbol
filterType n t =
    Node [mkEdge "filter" [t, n] (equalityConstraint $ mkEqConstraints [[path [0], path [1, 0]]])]

-- | Propagate the constraints and remove the redundant edges until nothing changes.
reduceFully :: Node Symbol -> Node Symbol
reduceFully = fixUnbounded (withoutRedundantEdges . reducePartially)
