-- | The term type agrees with the rose tree it replaces.
module Data.CFTA.TermSpec (spec) where

import Control.Monad (foldM, forM_)
import Data.Hashable (hash)
import Data.List (permutations, (!?))
import qualified Data.Tree as Tree
import Test.Hspec (Spec, describe, it, shouldBe)
import Test.QuickCheck (Gen, choose, elements, forAll, listOf, property, sized, vectorOf)

import Data.CFTA.Path (ChildIndex (ChildIndex), getPath, modifyAtPath, path)
import Data.CFTA.Term (flatten, fromAssocs, fromRoseTree, toRoseTree, pattern Node)

spec :: Spec
spec = describe "terms" $ do
    it "agree in equality, order, and hash with their rose trees" $
        property $
            forAll ((,) <$> roseTree <*> roseTree) $ \(left, right) -> do
                (fromRoseTree left == fromRoseTree right) `shouldBe` (left == right)
                compare (fromRoseTree left) (fromRoseTree right) `shouldBe` compare left right
                hash (fromRoseTree left) `shouldBe` hash left

    it "round trip through rose trees and flatten in preorder" $
        property $
            forAll roseTree $ \tree -> do
                toRoseTree (fromRoseTree tree) `shouldBe` tree
                flatten (fromRoseTree tree) `shouldBe` Tree.flatten tree

    it "read and edit the subterm at a path" $
        property $
            forAll ((,) <$> roseTree <*> listOf (ChildIndex <$> choose (0, 4))) $ \(tree, indexes) -> do
                let term = fromRoseTree tree
                    target = path indexes
                getPath target term `shouldBe` fmap fromRoseTree (subtreeAt indexes tree)
                getPath target (modifyAtPath (fmap succ) target term) `shouldBe` fmap (fmap succ) (getPath target term)

    it "build a term from its children keyed by index in any order" $
        property $
            forAll (choose (0, 5) >>= (`vectorOf` roseTree)) $ \trees -> do
                let children = map fromRoseTree trees
                forM_ (permutations [0 .. length children - 1]) $ \order ->
                    fromAssocs 'a' (length children) [(index, children !! index) | index <- order] `shouldBe` Node 'a' children
  where
    subtreeAt = flip $ foldM (\(Tree.Node _ children) (ChildIndex index) -> children !? index)

-- | A rose tree of up to five children per node over two symbols, so equal subterms are common.
roseTree :: Gen (Tree.Tree Char)
roseTree = sized go
  where
    go size = do
        symbol <- elements "ab"
        arity <- choose (0, min 5 size)
        Tree.Node symbol <$> mapM (const $ go (size `div` 2)) [1 .. arity]
