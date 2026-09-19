{-# LANGUAGE OverloadedStrings #-}

{- | Conversion from the tiny compatibility type language to ECTA nodes.

The old @Data.CFTA.TermSearch.Dataset@ module contained the large Hoogle
table. @microecta@ keeps this module name only for downstream compatibility; the
only remaining operation is 'typeToFta'.
-}
module Data.CFTA.TermSearch.Dataset (
    typeToFta,
) where

import Data.CFTA.Equality
import Data.CFTA.Symbol (Symbol)

import Data.CFTA.TermSearch.Type
import Data.CFTA.TermSearch.Utils

-- | Translate a 'TypeSkeleton' into the ECTA encoding used by term search.
typeToFta :: TypeSkeleton -> Node Symbol EqConstraints
typeToFta (TVar v) = genVar v
typeToFta (TFun t1 t2) = arrowType (typeToFta t1) (typeToFta t2)
typeToFta (TCons "Fun" [t1, t2]) = arrowType (typeToFta t1) (typeToFta t2)
typeToFta (TCons s ts) = mkDatatype s (map typeToFta ts)
