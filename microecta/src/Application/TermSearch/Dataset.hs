{-# LANGUAGE OverloadedStrings #-}

{- | Conversion from the tiny compatibility type language to ECTA nodes.

The old @Application.TermSearch.Dataset@ module contained the large Hoogle
table. @microecta@ keeps this module name only for downstream compatibility; the
only remaining operation is 'typeToFta'.
-}
module Application.TermSearch.Dataset (
    typeToFta,
) where

import Data.ECTA

import Application.TermSearch.Type
import Application.TermSearch.Utils

-- | Translate a 'TypeSkeleton' into the ECTA encoding used by term search.
typeToFta :: TypeSkeleton -> Node
typeToFta (TVar v) = genVar v
typeToFta (TFun t1 t2) = arrowType (typeToFta t1) (typeToFta t2)
typeToFta (TCons "Fun" [t1, t2]) = arrowType (typeToFta t1) (typeToFta t2)
typeToFta (TCons s ts) = mkDatatype s (map typeToFta ts)
