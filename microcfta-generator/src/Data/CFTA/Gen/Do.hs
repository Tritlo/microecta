{-# LANGUAGE NoImplicitPrelude #-}

{- | Qualified applicative do-notation for every generator layer.

Enable @ApplicativeDo@ and @QualifiedDo@ and qualify the block with a module
that exports these operators: this module, or one of the @QuickCheck@
facades, which re-export it. A block over the ordinary or the refinement
layer builds a child forest and is closed with that layer's @node@:

@
import qualified Data.CFTA.Gen.Refinement.QuickCheck as LTA

pairs = LTA.node "pair" subtypePair $ LTA.do
    left <- choices
    right <- choices
    LTA.pure (left, right)
@

A block over the equality layer builds a flat generator, or one operation
application of any arity when the first bind chooses an operation family
keyed by 'Data.CFTA.Gen.Equality.Sig':

@
import qualified Data.CFTA.Gen.Equality.QuickCheck as ECTAGen

binaryLayer children = ECTAGen.node "binary-application" $ ECTAGen.do
    operation <- binaryFunctionsBySignature
    left <- children
    right <- children
    ECTAGen.pure (compileBinary operation left right)
@

Statements are independent: the block builds the same applicative product as
@<*>@ composition, so a later generator cannot use an earlier bound value.
The final statement must use the /qualified/ 'pure' or 'return'; GHC does not
recognize the unqualified names inside a qualified block.
-}
module Data.CFTA.Gen.Do (
    GenApply (..),
    GenPure (..),
    Applying,
    fmap,
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

import qualified Data.CFTA.Gen as FTA
import Data.CFTA.Gen.Equality (
    Args (..),
    ECTAGen,
    Grouped,
    Sig,
    apply,
 )
import qualified Data.CFTA.Gen.Refinement as LTA
import Data.CFTA.Symbol (Symbol)

-- | Map a generator or an accumulated child forest of any layer.
fmap :: (Prelude.Functor f) => (a -> b) -> f a -> f b
fmap = Prelude.fmap

{- | The result of a block with no more binds.

For the ordinary and the refinement layer this is a constructor result with
no children; for the equality layer it is a flat generator with one value.
-}
class GenPure f where
    -- | Lift one value into the layer's block result.
    pure :: a -> f a

instance GenPure (FTA.Children symbol) where
    pure = Prelude.pure

instance GenPure LTA.Children where
    pure = Prelude.pure

instance GenPure ECTAGen where
    pure = Prelude.pure

-- | Synonym for 'pure'.
return :: (GenPure f) => a -> f a
return = pure

{- | Sequence two generators, keeping only the second value.

The discarded choice still occupies its position: the sequence of an
@m@-outcome and an @n@-outcome generator has cardinality @m * n@.
-}
(>>) :: (Prelude.Functor f, GenApply f g h) => f a -> g b -> h b
first >> second = fmap (\_ value -> value) first <*> second

{- | Applicative application for do-notation over every layer.

The ordinary and the refinement layer combine independently generated child
positions into a child forest. A flat equality generator applies directly
through its 'Prelude.Applicative' instance. A grouped operation family absorbs
its argument families one at a time and builds a single 'apply' join once the
last argument arrives; the staging never constructs an intermediate join.
Instance selection distinguishes an operation family from an argument family
by the 'Sig' in its key, the signature's key list tracks how many arguments
remain, and unification enforces that each argument family's key matches the
corresponding signature component.
-}
class GenApply f g h | f g -> h where
    -- | Apply one generated function layer to one generated argument layer.
    (<*>) :: f (a -> b) -> g a -> h b

instance GenApply (FTA.FTAGen symbol) (FTA.FTAGen symbol) (FTA.Children symbol) where
    functions <*> arguments =
        FTA.applyChildren (FTA.children functions) (FTA.children arguments)

instance GenApply (FTA.FTAGen symbol) (FTA.Children symbol) (FTA.Children symbol) where
    functions <*> arguments =
        FTA.applyChildren (FTA.children functions) arguments

instance GenApply (FTA.Children symbol) (FTA.FTAGen symbol) (FTA.Children symbol) where
    functions <*> arguments =
        FTA.applyChildren functions (FTA.children arguments)

instance GenApply (FTA.Children symbol) (FTA.Children symbol) (FTA.Children symbol) where
    (<*>) = FTA.applyChildren

instance GenApply LTA.LTAGen LTA.LTAGen LTA.Children where
    functions <*> arguments =
        LTA.applyChildren (LTA.children functions) (LTA.children arguments)

instance GenApply LTA.LTAGen LTA.Children LTA.Children where
    functions <*> arguments =
        LTA.applyChildren (LTA.children functions) arguments

instance GenApply LTA.Children LTA.LTAGen LTA.Children where
    functions <*> arguments =
        LTA.applyChildren functions (LTA.children arguments)

instance GenApply LTA.Children LTA.Children LTA.Children where
    (<*>) = LTA.applyChildren

instance GenApply ECTAGen ECTAGen ECTAGen where
    (<*>) = (Prelude.<*>)

{- | An operation family that has absorbed a prefix of its argument families
and awaits the families for @pendingKeys@.

A block result of this type means the do-block bound fewer arguments than the
operation's signature arity.
-}
newtype Applying (pendingKeys :: [Type]) resultKey b
    = Applying
        ( forall result.
          Args Symbol pendingKeys b result ->
          Grouped resultKey result
        )

-- The argument family's key is a fresh variable equated in the context rather
-- than repeated in the head, so instance selection does not need it fixed
-- already. An argument written as @keyed 0 ...@, whose key type is still open
-- and would default to Integer, then resolves against the operation's
-- signature the way it does when @apply@ is written out.
instance
    (argKey ~ argKey', Ord argKey, Ord resultKey) =>
    GenApply
        (Grouped (Sig '[argKey] resultKey))
        (Grouped argKey')
        (Grouped resultKey)
    where
    operations <*> argument = apply operations (argument :& ANil)

instance
    (argKey ~ argKey', Ord argKey, Ord resultKey) =>
    GenApply
        (Grouped (Sig (argKey ': nextKey ': pendingKeys) resultKey))
        (Grouped argKey')
        (Applying (nextKey ': pendingKeys) resultKey)
    where
    operations <*> argument =
        Applying (\rest -> apply operations (argument :& rest))

instance
    (argKey ~ argKey', Ord argKey) =>
    GenApply
        (Applying '[argKey] resultKey)
        (Grouped argKey')
        (Grouped resultKey)
    where
    Applying continue <*> argument = continue (argument :& ANil)

instance
    (argKey ~ argKey', Ord argKey) =>
    GenApply
        (Applying (argKey ': nextKey ': pendingKeys) resultKey)
        (Grouped argKey')
        (Applying (nextKey ': pendingKeys) resultKey)
    where
    Applying continue <*> argument =
        Applying (\rest -> continue (argument :& rest))

type NotApplicativeMessage =
    'Text "This qualified do-block cannot be desugared applicatively."
        ':$$: 'Text "Common causes, most likely first:"
        ':$$: 'Text "  * The block does not end with a qualified pure:"
        ':$$: 'Text "    write M.pure <expr> for the module alias M of the"
        ':$$: 'Text "    block (an unqualified pure or return is not"
        ':$$: 'Text "    recognized inside M.do)."
        ':$$: 'Text "  * ApplicativeDo is not enabled in this module;"
        ':$$: 'Text "    qualified do-notation needs it alongside QualifiedDo."
        ':$$: 'Text "  * A statement binds a strict pattern, as in"
        ':$$: 'Text "    (a, b) <- match ...: ApplicativeDo needs a lazy one,"
        ':$$: 'Text "    so write ~(a, b) <- match ... instead."
        ':$$: 'Text "  * The block contains a let statement, which ApplicativeDo"
        ':$$: 'Text "    has nowhere to place: bind the value in the final"
        ':$$: 'Text "    M.pure, or in a where clause."
        ':$$: 'Text "  * A later generator uses a value generated earlier."
        ':$$: 'Text "    Generators are applicative, so choices are"
        ':$$: 'Text "    independent. Relate values with the node's guard,"
        ':$$: 'Text "    with match, relate, or apply, or embed a monadic"
        ':$$: 'Text "    QuickCheck Gen with fromGen (that region becomes opaque)."

type CannotFailMessage =
    'Text "This pattern can fail, and a generator cannot discard"
        ':$$: 'Text "outcomes. Bind a total pattern and condition values"
        ':$$: 'Text "with the node's guard, match, or relate instead."

-- | Rejected at compile time: generators have no bind.
(>>=) :: (Unsatisfiable NotApplicativeMessage) => generator -> continuation -> result
(>>=) = unsatisfiable

-- | Rejected at compile time: generators have no bind.
join :: (Unsatisfiable NotApplicativeMessage) => generator -> result
join = unsatisfiable

-- | Rejected at compile time: generators cannot discard outcomes.
fail :: (Unsatisfiable CannotFailMessage) => message -> result
fail = unsatisfiable
