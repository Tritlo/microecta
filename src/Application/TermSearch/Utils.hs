{-# LANGUAGE OverloadedStrings #-}

{- | Small constructors for the term-search ECTA encoding.

These helpers deliberately stay as one-line wrappers around 'Node' and 'Edge'.
They are here to preserve the useful surface area of @ecta@ without bringing
back the larger search application.
-}
module Application.TermSearch.Utils (
    typeConst,
    constrType0,
    constrType1,
    constrType2,
    maybeType,
    listType,
    theArrowNode,
    arrowType,
    mkDatatype,
    constFunc,
    constArg,
    var1,
    var2,
    var3,
    var4,
    varAcc,
    genVar,
    isVar,
) where

import Data.Text (Text)
import qualified Data.Text as Text

import Data.ECTA
import Data.ECTA.Term

-- | Nullary type constructor.
typeConst :: Text -> Node
typeConst s = Node [Edge (Symbol s) []]

-- | Alias for 'typeConst'.
constrType0 :: Text -> Node
constrType0 = typeConst

-- | Unary type constructor.
constrType1 :: Text -> Node -> Node
constrType1 s n = Node [Edge (Symbol s) [n]]

-- | Binary type constructor.
constrType2 :: Text -> Node -> Node -> Node
constrType2 s n1 n2 = Node [Edge (Symbol s) [n1, n2]]

-- | @Maybe a@ in the term-search type encoding.
maybeType :: Node -> Node
maybeType = constrType1 "Maybe"

-- | @[a]@ in the term-search type encoding.
listType :: Node -> Node
listType = constrType1 "List"

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

-- | Alias for 'constFunc' when the symbol denotes an argument.
constArg :: Symbol -> Node -> Edge
constArg = constFunc

-- | Canonical generated type-variable nodes for common variable names.
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

-- | Check whether a node is one of the generated type-variable nodes.
isVar :: Node -> Bool
isVar x
    | x `elem` [var1, var2, var3, var4, varAcc] = True
isVar (Node [Edge (Symbol t) []]) = varPrefix `Text.isPrefixOf` t
isVar _ = False
