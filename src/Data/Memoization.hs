{-# LANGUAGE OverloadedStrings #-}

-- | Quick-and-dirty, thread-unsafe, hash-based memoization.
module Data.Memoization (
    MemoCacheTag (..),
    resetAllCaches,
    memoIO,
    memo,
    memo2,
) where

import qualified Data.HashTable.IO as HT
import Data.Hashable (Hashable)
import Data.Text (Text)
import GHC.Generics (Generic)
import System.IO.Unsafe (unsafePerformIO)

import Data.Text.Extended.Pretty

data MemoCacheTag = NameTag Text
    deriving (Eq, Ord, Show, Generic)

instance Hashable MemoCacheTag

mkInnerTag :: MemoCacheTag -> MemoCacheTag
mkInnerTag (NameTag t) = NameTag (t <> "-inner")

instance Pretty MemoCacheTag where
    pretty (NameTag t) = t

resetAllCaches :: IO ()
resetAllCaches = return ()

memoIO :: forall a b. (Eq a, Hashable a) => MemoCacheTag -> (a -> b) -> IO (a -> IO b)
memoIO _ f = do
    ht :: HT.CuckooHashTable a b <- HT.new
    let f' x = do
            v <- HT.lookup ht x
            case v of
                Nothing -> do
                    let r = f x
                    HT.insert ht x r
                    return r
                Just r -> return r
    return f'

memo :: (Eq a, Hashable a) => MemoCacheTag -> (a -> b) -> (a -> b)
memo tag f =
    let f' = unsafePerformIO (memoIO tag f)
     in \x -> unsafePerformIO (f' x)

memo2 :: (Eq a, Hashable a, Eq b, Hashable b) => MemoCacheTag -> (a -> b -> c) -> a -> b -> c
memo2 tag f = memo tag (memo (mkInnerTag tag) . f)
