{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoImplicitPrelude #-}

{- | Qualified applicative do-notation for LTA child forests.

Enable @ApplicativeDo@ and @QualifiedDo@, then close the block with
'Data.LTA.Gen.node':

@
pairs = LTA.node "pair" rootRefinement
    (\left right -> refines left right) $ LTA.do
    left <- choices
    right <- choices
    LTA.pure (left, right)
@

Every bind contributes one child witness. Later generators cannot depend on
earlier values; such a block is not an applicative tree constructor.
-}
module Data.LTA.Gen.Do (
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

import Data.LTA.Gen (
    Children,
    LTAGen,
    applyChildren,
    children,
 )

-- | Map either a child language or an accumulated child forest.
fmap :: (Prelude.Functor f) => (a -> b) -> f a -> f b
fmap = Prelude.fmap

-- | Build a constructor with no children.
pure :: a -> Children a
pure = Prelude.pure

-- | Synonym for 'pure'.
return :: a -> Children a
return = Prelude.pure

-- | Applicative application across child languages and accumulated forests.
class GenApply f g h | f g -> h where
    -- | Combine independently generated child positions.
    (<*>) :: f (a -> b) -> g a -> h b

instance GenApply LTAGen LTAGen Children where
    functions <*> arguments =
        applyChildren (children functions) (children arguments)

instance GenApply LTAGen Children Children where
    functions <*> arguments =
        applyChildren (children functions) arguments

instance GenApply Children LTAGen Children where
    functions <*> arguments =
        applyChildren functions (children arguments)

instance GenApply Children Children Children where
    (<*>) = applyChildren

type NotApplicativeMessage =
    'Text "This LTA.do block cannot be desugared applicatively."
        ':$$: 'Text "Later child generators cannot depend on earlier values."
        ':$$: 'Text "End the block with LTA.pure and put value-dependent"
        ':$$: 'Text "relationships in the node's liquid Guard instead."

type CannotFailMessage =
    'Text "A pattern in this LTA.do block can fail."
        ':$$: 'Text "Bind a total pattern; liquid guards filter complete witnesses."

-- | Rejected at compile time: child construction is applicative.
(>>=) :: (Unsatisfiable NotApplicativeMessage) => generator -> continuation -> result
(>>=) = unsatisfiable

-- | Rejected at compile time: child construction is applicative.
join :: (Unsatisfiable NotApplicativeMessage) => generator -> result
join = unsatisfiable

-- | Rejected at compile time: child construction cannot discard outcomes.
fail :: (Unsatisfiable CannotFailMessage) => message -> result
fail = unsatisfiable
