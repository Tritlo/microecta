{-# LANGUAGE OverloadedStrings #-}

{- | Small constructors for the term-search ECTA encoding.

These helpers deliberately stay as small wrappers around @Node@ and @Edge@.
They are here to preserve the useful surface area of @ecta@ without bringing
back the larger search application.
-}
module Application.TermSearch.Utils (
    typeConst,
    theArrowNode,
    arrowType,
    mkDatatype,
    constFunc,
    genVar,
) where

import Data.Text (Text)

import Data.ECTA
import Data.ECTA.Term

-- | Nullary type constructor.
typeConst :: Text -> Node
typeConst s = Node [Edge (Symbol s) []]

-- | Marker node used as the first child of encoded function types.
theArrowNode :: Node
theArrowNode = Node [Edge "(->)" []]

-- | Function type in the term-search encoding.
arrowType :: Node -> Node -> Node
arrowType n1 n2 = Node [Edge "->" [theArrowNode, n1, n2]]

-- | Type constructor applied to encoded argument types.
mkDatatype :: Text -> [Node] -> Node
mkDatatype s ns = Node [Edge (Symbol s) ns]

-- | Term symbol with a single child describing its type.
constFunc :: Symbol -> Node -> Edge
constFunc s t = Edge s [t]

var1, var2, var3, var4, varAcc :: Node
var1 = Node [Edge "var1" []]
var2 = Node [Edge "var2" []]
var3 = Node [Edge "var3" []]
var4 = Node [Edge "var4" []]
varAcc = Node [Edge "acc" []]

varPrefix :: Text
varPrefix = "__gen_var_"

-- | Generate the canonical ECTA node for a type variable.
genVar :: Text -> Node
genVar "a" = var1
genVar "b" = var2
genVar "c" = var3
genVar "d" = var4
genVar "acc" = varAcc
genVar s = Node [Edge (Symbol $ varPrefix <> s) []]
