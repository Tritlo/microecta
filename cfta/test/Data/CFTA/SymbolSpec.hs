{-# LANGUAGE OverloadedStrings #-}

-- | The laws of the one symbol type: a symbol is its text and its refinement.
module Data.CFTA.SymbolSpec (spec) where

import Control.Monad (when)
import Data.Hashable (hash)
import Data.String (fromString)
import Test.Hspec (Spec, describe, it, shouldBe)
import Test.QuickCheck (Gen, elements, forAll, property)

import Data.CFTA.Refinement.Expression (refinementFormula, true, (.==), (.>=))
import Data.CFTA.Symbol (Symbol (RefinedSymbol, Symbol), symbolRefinement, symbolText)

spec :: Spec
spec = describe "symbols" $ do
    it "agree in equality, order, and hash with their text and refinement" $
        property $
            forAll ((,) <$> symbol <*> symbol) $ \(left, right) -> do
                (left == right) `shouldBe` (key left == key right)
                compare left right `shouldBe` compare (key left) (key right)
                when (left == right) $ hash left `shouldBe` hash right

    it "intern one symbol for each text and refinement" $
        property $
            forAll symbol $ \built ->
                RefinedSymbol (Symbol (symbolText built)) (symbolRefinement built) `shouldBe` built
  where
    key built = (symbolText built, symbolRefinement built)

-- | A symbol from two texts and four refinements, so equal texts with different refinements are common.
symbol :: Gen Symbol
symbol = do
    text <- elements ["a", "b"]
    refinement <- elements [true, refinementFormula (.== 0), refinementFormula (.== 1), refinementFormula (.>= 0)]
    pure $ RefinedSymbol (fromString text) refinement
