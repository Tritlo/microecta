{- | Signature and condition syntax for ECTA generators.

'Sig' writes many-sorted operation signatures over group keys, and 'On'
reifies key equalities between two generated values.
-}
module Data.ECTA.Gen.Sig (
    Sig (..),
    sigResult,
    On (..),
) where

import Data.Kind (Type)

{- | The input and result group keys for a generated operation.

Signatures are written like many-sorted operation signatures, with ':*'
between argument keys and ':->' before the result key:
@TInt ':*' TInt ':->' TBool@ is a binary signature with result key @TBool@.
Since ':->' binds tighter, the chain nests as
@TInt ':*' (TInt ':->' TBool)@: ':->' pairs the final argument key with the
result key and ':*' prepends further argument keys. Both are ordinary
constructors, so signatures can be pattern matched the way they are written.
-}
data Sig (argKeys :: [Type]) result where
    (:->) :: argKey -> result -> Sig '[argKey] result
    (:*) ::
        argKey ->
        Sig (nextKey ': argKeys) result ->
        Sig (argKey ': nextKey ': argKeys) result

infixr 5 :->
infixr 4 :*

instance (Eq argKey, Eq result) => Eq (Sig '[argKey] result) where
    (key :-> result) == (otherKey :-> otherResult) =
        key == otherKey && result == otherResult

instance
    (Eq argKey, Eq (Sig (nextKey ': argKeys) result)) =>
    Eq (Sig (argKey ': nextKey ': argKeys) result)
    where
    (key :* rest) == (otherKey :* otherRest) =
        key == otherKey && rest == otherRest

instance (Ord argKey, Ord result) => Ord (Sig '[argKey] result) where
    compare (key :-> result) (otherKey :-> otherResult) =
        compare key otherKey <> compare result otherResult

instance
    (Ord argKey, Ord (Sig (nextKey ': argKeys) result)) =>
    Ord (Sig (argKey ': nextKey ': argKeys) result)
    where
    compare (key :* rest) (otherKey :* otherRest) =
        compare key otherKey <> compare rest otherRest

instance (Show argKey, Show result) => Show (Sig '[argKey] result) where
    showsPrec depth (key :-> result) =
        showParen (depth > 5) $
            showsPrec 6 key . showString " :-> " . showsPrec 6 result

instance
    (Show argKey, Show (Sig (nextKey ': argKeys) result)) =>
    Show (Sig (argKey ': nextKey ': argKeys) result)
    where
    showsPrec depth (key :* rest) =
        showParen (depth > 4) $
            showsPrec 5 key . showString " :* " . showsPrec 4 rest

-- | The result key of a signature.
sigResult :: Sig argKeys result -> result
sigResult (_ :-> result) = result
sigResult (_ :* rest) = sigResult rest

{- | Reified key equalities between one value of each side.

@leftKey ':==:' rightKey@ requires the two projected keys to agree, and
':&&:' conjoins equalities. Keeping the projections as data lets a match
group each input by its own key instead of testing sampled pairs.
-}
data On left right where
    (:==:) :: (Ord key) => (left -> key) -> (right -> key) -> On left right
    (:&&:) :: On left right -> On left right -> On left right

infix 4 :==:
infixr 3 :&&:
