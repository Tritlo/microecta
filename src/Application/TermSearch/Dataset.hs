{-# LANGUAGE OverloadedStrings #-}

module Application.TermSearch.Dataset (
    typeToFta,
) where

import Data.ECTA

import Application.TermSearch.Type
import Application.TermSearch.Utils

typeToFta :: TypeSkeleton -> Node
typeToFta (TVar v) = genVar v
typeToFta (TFun t1 t2) = arrowType (typeToFta t1) (typeToFta t2)
typeToFta (TCons "Fun" [t1, t2]) = arrowType (typeToFta t1) (typeToFta t2)
typeToFta (TCons s ts) = mkDatatype s (map typeToFta ts)
