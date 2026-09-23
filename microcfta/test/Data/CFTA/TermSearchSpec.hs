{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.TermSearchSpec (spec) where

import qualified Data.Tree as Tree
import Test.Hspec

import Data.CFTA.Equality
import Data.CFTA.Symbol
import Data.CFTA.TermSearch.Dataset (typeToFta)
import Data.CFTA.TermSearch.TermSearch (filterType, reduceFully)
import Data.CFTA.TermSearch.Type (TypeSkeleton (..))
import Data.CFTA.TermSearch.Utils (
    arrowType,
    constFunc,
    genVar,
    mkDatatype,
    theArrowNode,
    typeConst,
 )

-----------------------------------------------------------------

intType :: Node Symbol EqConstraints
intType = typeConst "Int"

boolType :: Node Symbol EqConstraints
boolType = typeConst "Bool"

{- | Two constants of different types, in the term-search encoding: a term
symbol carries its type as its one child.
-}
constants :: Node Symbol EqConstraints
constants = Node [constFunc "one" intType, constFunc "true" boolType]

spec :: Spec
spec = do
    describe "type encoding" $ do
        it "a nullary constructor is a leaf" $
            typeToFta (TCons "Int" []) `shouldBe` intType

        it "an applied constructor keeps its arguments" $
            typeToFta (TCons "List" [TCons "Int" []])
                `shouldBe` mkDatatype "List" [intType]

        it "a function type is an arrow with the arrow marker first" $
            typeToFta (TFun (TCons "Int" []) (TCons "Bool" []))
                `shouldBe` arrowType intType boolType

        it "the arrow encoding leads with theArrowNode" $
            arrowType intType boolType
                `shouldBe` Node [Edge "->" [theArrowNode, intType, boolType]]

        it "TCons \"Fun\" is the same encoding as TFun" $
            typeToFta (TCons "Fun" [TCons "Int" [], TCons "Bool" []])
                `shouldBe` typeToFta (TFun (TCons "Int" []) (TCons "Bool" []))

    describe "type variables" $ do
        it "the canonical names get the canonical nodes" $ do
            genVar "a" `shouldBe` Node [Edge "var1" []]
            genVar "b" `shouldBe` Node [Edge "var2" []]
            genVar "c" `shouldBe` Node [Edge "var3" []]
            genVar "d" `shouldBe` Node [Edge "var4" []]
            genVar "acc" `shouldBe` Node [Edge "acc" []]

        it "any other name gets a prefixed node of its own" $ do
            genVar "zzz" `shouldBe` Node [Edge "__gen_var_zzz" []]
            genVar "zzz" `shouldNotBe` genVar "yyy"

        it "the prefix keeps a variable clear of the canonical nodes" $
            genVar "var1" `shouldNotBe` genVar "a"

        it "a variable type goes through genVar" $
            typeToFta (TVar "a") `shouldBe` genVar "a"

    describe "filterType" $ do
        it "keeps only the terms of the requested type" $
            terms (reduceFully (filterType constants intType))
                `shouldBe` [Tree.Node "filter" [Tree.Node "Int" [], Tree.Node "one" [Tree.Node "Int" []]]]

        it "keeps the other type when that is what is asked for" $
            terms (reduceFully (filterType constants boolType))
                `shouldBe` [Tree.Node "filter" [Tree.Node "Bool" [], Tree.Node "true" [Tree.Node "Bool" []]]]

        it "an unrepresented type leaves nothing" $
            reduceFully (filterType constants (typeConst "Char")) `shouldBe` EmptyNode

        it "filtering by a type both terms could have keeps both" $
            length (terms (reduceFully (filterType (Node [constFunc "one" intType, constFunc "two" intType]) intType)))
                `shouldBe` 2

    describe "reduceFully" $ do
        it "is a fixpoint" $ do
            let reduced = reduceFully (filterType constants intType)
            reduceFully reduced `shouldBe` reduced

        it "does not change what an unconstrained node accepts" $
            terms (reduceFully constants) `shouldMatchList` terms constants
