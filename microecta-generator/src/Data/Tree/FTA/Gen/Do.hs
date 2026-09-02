{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}

{- | Qualified applicative do-notation for ordinary FTA child forests.

Enable @ApplicativeDo@ and @QualifiedDo@, then close every block with
'Data.Tree.FTA.Gen.node':

@
pair = FTA.node "pair" $ FTA.do
    left <- atoms
    right <- atoms
    FTA.pure (left, right)
@

Every bind contributes one direct constructor child. Later child generators
cannot depend on values bound earlier.
-}
module Data.Tree.FTA.Gen.Do (
    GenApply (..),
    fmap,
    pure,
    return,
    (>>=),
    join,
    fail,
) where

import GHC.TypeError (ErrorMessage (..), Unsatisfiable, unsatisfiable)
import qualified Prelude

import Data.Tree.FTA.Gen (
    Children,
    FTAGen,
    applyChildren,
    children,
 )

-- | Map an FTA language or an accumulated child forest.
fmap :: (Prelude.Functor f) => (a -> b) -> f a -> f b
fmap = Prelude.fmap

-- | Build a constructor result with no children.
pure :: a -> Children symbol a
pure = Prelude.pure

-- | Synonym for 'pure'.
return :: a -> Children symbol a
return = Prelude.pure

-- | Applicative application across FTA languages and child forests.
class GenApply f g h | f g -> h where
    -- | Combine independently generated child positions.
    (<*>) :: f (a -> b) -> g a -> h b

instance GenApply (FTAGen symbol) (FTAGen symbol) (Children symbol) where
    functions <*> arguments =
        applyChildren (children functions) (children arguments)

instance GenApply (FTAGen symbol) (Children symbol) (Children symbol) where
    functions <*> arguments =
        applyChildren (children functions) arguments

instance GenApply (Children symbol) (FTAGen symbol) (Children symbol) where
    functions <*> arguments =
        applyChildren functions (children arguments)

instance GenApply (Children symbol) (Children symbol) (Children symbol) where
    (<*>) = applyChildren

type NotApplicativeMessage =
    'Text "This FTA.do block cannot be desugared applicatively."
        ':$$: 'Text "Later child generators cannot depend on earlier values."
        ':$$: 'Text "End the block with FTA.pure and close it with FTA.node."

type CannotFailMessage =
    'Text "A pattern in this FTA.do block can fail."
        ':$$: 'Text "Bind a total pattern instead."

-- | Rejected at compile time: child construction is applicative.
(>>=) :: (Unsatisfiable NotApplicativeMessage) => generator -> continuation -> result
(>>=) = unsatisfiable

-- | Rejected at compile time: child construction is applicative.
join :: (Unsatisfiable NotApplicativeMessage) => generator -> result
join = unsatisfiable

-- | Rejected at compile time: child construction cannot discard outcomes.
fail :: (Unsatisfiable CannotFailMessage) => message -> result
fail = unsatisfiable
