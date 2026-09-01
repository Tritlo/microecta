{-# LANGUAGE OverloadedStrings #-}

{- | Quick-and-dirty hash-based memoization.

The ECTA core relies on stable global memo tables for interning and recursive
graph operations. 'memo' is convenient when the memoized function is a
monomorphic top-level value. Polymorphic functions should allocate an explicit
'MemoCache' or 'TypeableMemoCache' once and use the corresponding @With@
operation, so typeclass dictionaries cannot accidentally turn the table into a
per-call allocation.

Safe from any thread. The table is an immutable map in an @IORef@, read
without blocking and updated with 'atomicModifyIORef''. Two racers may install
different thunks and return their own result, but both compute the same answer
because every function memoized here is pure.

The lazy map is important: an atomic update installs the result thunk without
forcing the memoized computation. That computation may itself intern or call
other memoized functions, so it must run outside the update.

The tables never evict, so a memoized function retains an entry for every
distinct argument it has ever been applied to, for the lifetime of the process.
That is what makes repeated work free, and it means memory grows with the
number of distinct inputs rather than with the work done. See the memory
section of the package README.
-}
module Data.Memoization (
    MemoCacheTag (..),
    MemoCache,
    TypeableMemoCache,
    newMemoCache,
    newTypeableMemoCache,
    memo,
    memo2,
    memoWith,
    memo2With,
    memoTypeableWith,
    memo2TypeableWith,
) where

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Hashable (Hashable (..), hash)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import Data.Text (Text)
import Data.Type.Equality ((:~~:) (HRefl))
import GHC.IO (unsafeDupablePerformIO)
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (SomeTypeRep (..), TypeRep, Typeable, eqTypeRep, typeRep)

{- | Name of a memo table.

The name is not stored in the table. It labels the call site for readers and
makes distinct source uses visibly distinct; table identity still belongs to
the particular 'memo' application, not to the text of the tag.
-}
newtype MemoCacheTag
    = NameTag Text
    deriving (Eq, Ord, Show)

memoIO :: forall a b. (Hashable a) => (a -> b) -> IO (a -> IO b)
memoIO f = do
    ref <- newIORef (HashMap.empty :: HashMap a b)
    let f' x = do
            cached <- HashMap.lookup x <$> readIORef ref
            case cached of
                Just r -> return r
                Nothing -> do
                    -- @r@ is never forced under the update: forcing it runs
                    -- the memoized computation, which interns, which comes
                    -- back through here and would diverge. Two racers may each
                    -- insert their own thunk; both compute the same answer,
                    -- because everything memoized here is pure.
                    let r = f x
                    atomicModifyIORef' ref (\m -> (HashMap.insert x r m, ()))
                    return r
    return f'

-- | Memoize a pure unary function in a process-global mutable hash table.
memo :: (Hashable a) => MemoCacheTag -> (a -> b) -> (a -> b)
{-# NOINLINE memo #-}
memo !_tag f =
    let f' = unsafePerformIO (memoIO f)
     in \x -> unsafePerformIO (f' x)

{- | Memoize a pure binary function in one table keyed by the pair.

Nesting two unary tables instead would allocate a fresh hash table for every
distinct first argument -- around a kilobyte each, before storing a single
entry. On a workload with 64k distinct first arguments that costs 167 MB
against this version's 68 MB, for no gain: measured on the core benchmark, the
pair key is within noise on time and allocates 0.1% more.
-}
memo2 :: (Hashable a, Hashable b) => MemoCacheTag -> (a -> b -> c) -> a -> b -> c
memo2 tag f = curry (memo tag (uncurry f))

{- | A memo table whose argument and result types are known statically.

The table is separate from the function so polymorphic callers can keep its
lifetime explicit. Reusing one table for different functions is invalid.
-}
newtype MemoCache a b = MemoCache (IORef (HashMap a b))

-- | Allocate an empty statically typed memo table.
newMemoCache :: IO (MemoCache a b)
newMemoCache = MemoCache <$> newIORef HashMap.empty

-- | Memoize one application in an explicitly supplied table.
memoWith :: (Hashable a) => MemoCache a b -> (a -> b) -> a -> b
memoWith (MemoCache ref) f x = unsafeDupablePerformIO $ do
    cached <- HashMap.lookup x <$> readIORef ref
    case cached of
        Just result -> return result
        Nothing -> do
            let result = f x
            -- Keep the winner without forcing either result thunk. The
            -- computation may itself re-enter this or another memo table.
            atomicModifyIORef' ref $ \m ->
                (HashMap.insertWith (\_new old -> old) x result m, ())
            winner <- HashMap.lookup x <$> readIORef ref
            return $ maybe result id winner

-- | Binary variant of 'memoWith', using one table keyed by the pair.
memo2With :: (Hashable a, Hashable b) => MemoCache (a, b) c -> (a -> b -> c) -> a -> b -> c
memo2With cache f = curry (memoWith cache (uncurry f))

{- | A heterogeneous memo-table family.

One value can hold applications at several runtime types. Argument and result
types are included in every key and checked on lookup. As with 'MemoCache', a
family belongs to one function and must not be shared between different
functions with the same type.
-}
newtype TypeableMemoCache = TypeableMemoCache (IORef (HashMap SomeMemoKey SomeMemoValue))

-- | Allocate an empty heterogeneous memo-table family.
newTypeableMemoCache :: IO TypeableMemoCache
newTypeableMemoCache = TypeableMemoCache <$> newIORef HashMap.empty

data SomeMemoKey where
    SomeMemoKey ::
        (Hashable a) =>
        !Int ->
        TypeRep a ->
        SomeTypeRep ->
        a ->
        SomeMemoKey

instance Eq SomeMemoKey where
    SomeMemoKey leftHash leftType leftResultType left
        == SomeMemoKey rightHash rightType rightResultType right =
            leftHash == rightHash
                && leftResultType == rightResultType
                && case eqTypeRep leftType rightType of
                    Just HRefl -> left == right
                    Nothing -> False

instance Hashable SomeMemoKey where
    hashWithSalt salt (SomeMemoKey cachedHash _ _ _) =
        salt `hashWithSalt` cachedHash

data SomeMemoValue where
    SomeMemoValue :: TypeRep b -> b -> SomeMemoValue

-- | Memoize one application in a heterogeneous table family.
memoTypeableWith ::
    forall a b.
    (Hashable a, Typeable a, Typeable b) =>
    TypeableMemoCache ->
    (a -> b) ->
    a ->
    b
{-# NOINLINE memoTypeableWith #-}
memoTypeableWith (TypeableMemoCache ref) f !x = unsafeDupablePerformIO $ do
    cached <- HashMap.lookup key <$> readIORef ref
    case cached of
        Just value -> return (extract value)
        Nothing -> do
            let result = f x
                wrapped = SomeMemoValue resultType result
            atomicModifyIORef' ref $ \m ->
                (HashMap.insertWith (\_new old -> old) key wrapped m, ())
            winner <- HashMap.lookup key <$> readIORef ref
            return $ maybe result extract winner
  where
    argumentType = typeRep @a
    resultType = typeRep @b
    key = SomeMemoKey cachedHash argumentType (SomeTypeRep resultType) x
    cachedHash = hashWithSalt typeHash x
    typeHash =
        hashWithSalt
            (hash $ SomeTypeRep argumentType)
            (SomeTypeRep resultType)

    extract (SomeMemoValue actual result) = case eqTypeRep resultType actual of
        Just HRefl -> result
        Nothing -> error "memoTypeableWith: cache returned a result of the wrong type"

-- | Binary variant of 'memoTypeableWith', keyed by the argument pair.
memo2TypeableWith ::
    (Hashable a, Hashable b, Typeable a, Typeable b, Typeable c) =>
    TypeableMemoCache ->
    (a -> b -> c) ->
    a ->
    b ->
    c
memo2TypeableWith cache f = curry (memoTypeableWith cache (uncurry f))
