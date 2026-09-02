{-# LANGUAGE NoImplicitPrelude #-}

{- | Qualified do-notation for ECTA generators.

Enable @QualifiedDo@ and @ApplicativeDo@ together and qualify the block with a
module exporting these operators — either this module or
"Data.ECTA.Gen.QuickCheck", which re-exports it:

@
{\-# LANGUAGE ApplicativeDo #-\}
{\-# LANGUAGE QualifiedDo #-\}

import qualified Data.ECTA.Gen.QuickCheck as ECTAGen

authentication :: ECTAGen Authentication
authentication = ECTAGen.do
    user <- generatedUser
    method <- ECTAGen.elements [Password, Token]
    ECTAGen.pure (Authentication user method)
@

Statements must be independent: the block builds the same applicative product
as @<*>@ composition, so a later generator cannot use an earlier bound value.
The final statement must be written with a /qualified/ @pure@ or @return@;
GHC does not recognize the unqualified names inside a qualified block.

A grouped block generates one operation application of any arity. The first
bind chooses the operation family (keyed by 'Data.ECTA.Gen.Sig'), the
remaining binds choose one argument per signature component in order, and the
block builds exactly the 'Data.ECTA.Gen.apply' join:

@
binaryLayer children = ECTAGen.do
    operation <- binaryFunctionsBySignature
    left <- children
    right <- children
    ECTAGen.pure (compileBinary operation left right)
@
-}
module Data.ECTA.Gen.Do (
    GenApply (..),
    Applying,
    fmap,
    pure,
    return,
    (>>),
    (>>=),
    join,
    fail,
) where

import Data.Kind (Type)
import GHC.TypeError (ErrorMessage (..), Unsatisfiable, unsatisfiable)
import Prelude (Ord, type (~))
import qualified Prelude

import Data.ECTA.Gen (
    Args (..),
    ECTAGen,
    GenBackend,
    Grouped,
    Sig,
    apply,
 )

-- | Map with the 'Prelude.Functor' instance of either generator layer.
fmap :: (Prelude.Functor f) => (a -> b) -> f a -> f b
fmap = Prelude.fmap

{- | Lift one value into a flat generator.

Inside a qualified do-block the final statement must use this qualified name
(or 'return') for the block to fuse applicatively.
-}
pure :: (GenBackend gen) => a -> ECTAGen gen a
pure = Prelude.pure

-- | Synonym for 'pure'.
return :: (GenBackend gen) => a -> ECTAGen gen a
return = Prelude.pure

{- | Sequence two flat generators, keeping only the second value.

The discarded choice still occupies rank space: the sequence of an @m@-outcome
and an @n@-outcome generator has cardinality @m * n@.
-}
(>>) :: (GenBackend gen) => ECTAGen gen a -> ECTAGen gen b -> ECTAGen gen b
(>>) = (Prelude.*>)

{- | Applicative application for do-notation over both generator layers.

Flat generators apply directly through their 'Prelude.Applicative' instance.
A grouped operation family absorbs its argument families one at a time and
builds a single 'apply' join once the last argument arrives; the staging
never constructs an intermediate join. Instance selection distinguishes an
operation family from an argument family by the 'Sig' in its key, the
signature's key list tracks how many arguments remain, and unification
enforces that each argument family's key matches the corresponding signature
component.
-}
class GenApply f g h | f g -> h where
    -- | Apply one generated function layer to one generated argument layer.
    (<*>) :: f (a -> b) -> g a -> h b

instance (GenBackend gen) => GenApply (ECTAGen gen) (ECTAGen gen) (ECTAGen gen) where
    (<*>) = (Prelude.<*>)

{- | An operation family that has absorbed a prefix of its argument families
and awaits the families for @pendingKeys@.

A block result of this type means the do-block bound fewer arguments than the
operation's signature arity.
-}
newtype Applying gen (pendingKeys :: [Type]) resultKey b
    = Applying
        ( forall result.
          Args gen pendingKeys b result ->
          Grouped gen resultKey result
        )

-- The argument family's key is a fresh variable equated in the context rather
-- than repeated in the head, so instance selection does not need it fixed
-- already. An argument written as @keyed 0 ...@, whose key type is still open
-- and would default to Integer, then resolves against the operation's
-- signature the way it does when @apply@ is written out.
instance
    (argKey ~ argKey', Ord argKey, Ord resultKey) =>
    GenApply
        (Grouped gen (Sig '[argKey] resultKey))
        (Grouped gen argKey')
        (Grouped gen resultKey)
    where
    operations <*> argument = apply operations (argument :& ANil)

instance
    (argKey ~ argKey', Ord argKey, Ord resultKey) =>
    GenApply
        (Grouped gen (Sig (argKey ': nextKey ': pendingKeys) resultKey))
        (Grouped gen argKey')
        (Applying gen (nextKey ': pendingKeys) resultKey)
    where
    operations <*> argument =
        Applying (\rest -> apply operations (argument :& rest))

instance
    (argKey ~ argKey', Ord argKey) =>
    GenApply
        (Applying gen '[argKey] resultKey)
        (Grouped gen argKey')
        (Grouped gen resultKey)
    where
    Applying continue <*> argument = continue (argument :& ANil)

instance
    (argKey ~ argKey', Ord argKey) =>
    GenApply
        (Applying gen (argKey ': nextKey ': pendingKeys) resultKey)
        (Grouped gen argKey')
        (Applying gen (nextKey ': pendingKeys) resultKey)
    where
    Applying continue <*> argument =
        Applying (\rest -> continue (argument :& rest))

type NotApplicativeMessage =
    'Text "This qualified do-block cannot be desugared applicatively."
        ':$$: 'Text "Common causes, most likely first:"
        ':$$: 'Text "  * The block does not end with a qualified pure:"
        ':$$: 'Text "    write ECTAGen.pure <expr> (an unqualified pure or"
        ':$$: 'Text "    return is not recognized inside ECTAGen.do)."
        ':$$: 'Text "  * ApplicativeDo is not enabled in this module;"
        ':$$: 'Text "    qualified do-notation needs it alongside QualifiedDo."
        ':$$: 'Text "  * A statement binds a strict pattern, as in"
        ':$$: 'Text "    (a, b) <- match ...: ApplicativeDo needs a lazy one,"
        ':$$: 'Text "    so write ~(a, b) <- match ... instead."
        ':$$: 'Text "  * The block contains a let statement, which ApplicativeDo"
        ':$$: 'Text "    has nowhere to place: bind the value in the final"
        ':$$: 'Text "    ECTAGen.pure, or in a where clause."
        ':$$: 'Text "  * A later generator uses a value generated earlier."
        ':$$: 'Text "    ECTA generators are applicative, so choices are"
        ':$$: 'Text "    independent. Use match, relate, or apply, or embed"
        ':$$: 'Text "    a monadic QuickCheck Gen with"
        ':$$: 'Text "    fromGen (that region becomes opaque)."

type CannotFailMessage =
    'Text "This pattern can fail, and an ECTA generator cannot"
        ':$$: 'Text "discard outcomes. Bind a total pattern and condition"
        ':$$: 'Text "values with match or relate instead."

-- | Rejected at compile time: ECTA generators have no bind.
(>>=) :: (Unsatisfiable NotApplicativeMessage) => generator -> continuation -> result
(>>=) = unsatisfiable

-- | Rejected at compile time: ECTA generators have no bind.
join :: (Unsatisfiable NotApplicativeMessage) => generator -> result
join = unsatisfiable

-- | Rejected at compile time: ECTA generators cannot discard outcomes.
fail :: (Unsatisfiable CannotFailMessage) => message -> result
fail = unsatisfiable
