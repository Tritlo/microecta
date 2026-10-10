{-# LANGUAGE OverloadedStrings #-}

module Data.CFTA.TermSearchSpec (spec) where

import qualified Data.Tree as Tree
import Test.Hspec

import Data.CFTA.Equality
import Data.CFTA.Symbol
import Data.CFTA.TermSearch (constFunc, filterType, reduceFully, theArrowNode, typeNode)

-----------------------------------------------------------------

intType :: Node Symbol
intType = typeNode @Int

boolType :: Node Symbol
boolType = typeNode @Bool

{- | Two constants of different types, in the term-search encoding: a term
symbol carries its type as its one child.
-}
constants :: Node Symbol
constants = Node [constFunc "one" intType, constFunc "true" boolType]

spec :: Spec
spec = do
    describe "type encoding" $ do
        it "a nullary type constructor is a leaf" $
            intType `shouldBe` Node [Edge "Int" []]

        it "an applied type constructor keeps its arguments" $
            typeNode @(Maybe [Int])
                `shouldBe` Node [Edge "Maybe" [Node [Edge "List" [intType]]]]

        it "a function type is an arrow with the arrow marker first" $
            typeNode @(Int -> Bool)
                `shouldBe` Node [Edge "->" [theArrowNode, intType, boolType]]

        it "a curried function type nests its arrows to the right" $
            typeNode @(Int -> Bool -> Int)
                `shouldBe` Node [Edge "->" [theArrowNode, intType, typeNode @(Bool -> Int)]]

    describe "filterType" $ do
        it "keeps only the terms of the requested type" $
            terms (reduceFully (filterType constants intType))
                `shouldBe` [Tree.Node "filter" [Tree.Node "Int" [], Tree.Node "one" [Tree.Node "Int" []]]]

        it "keeps the other type when that is what is asked for" $
            terms (reduceFully (filterType constants boolType))
                `shouldBe` [Tree.Node "filter" [Tree.Node "Bool" [], Tree.Node "true" [Tree.Node "Bool" []]]]

        it "an unrepresented type leaves nothing" $
            reduceFully (filterType constants (typeNode @Char)) `shouldBe` EmptyNode

        it "filtering by a type both terms could have keeps both" $
            length (terms (reduceFully (filterType (Node [constFunc "one" intType, constFunc "two" intType]) intType)))
                `shouldBe` 2

    describe "reduceFully" $ do
        it "is a fixpoint" $ do
            let reduced = reduceFully (filterType constants intType)
            reduceFully reduced `shouldBe` reduced

        it "does not change what an unconstrained node accepts" $
            terms (reduceFully constants) `shouldMatchList` terms constants
