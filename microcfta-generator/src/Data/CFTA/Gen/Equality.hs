{- | Generators over equality-constrained tree automata.

An equality generator is a generator over 'Symbol' and 'EqConstraints', the
theory of "Data.CFTA.Equality": an edge may require that the subterms at
two of its paths are equal. Everything of "Data.CFTA.Gen" applies. The joins
'match', 'relate', and 'apply' express their keys as such equalities, so a
joined language is one automaton whose support carries the constraint.

This module fixes the theory in 'ECTAGen' and 'Grouped', and reads imported
automata with ranks ordered by symbol text, so that ranks do not depend on
the order in which symbols were interned.
-}
module Data.CFTA.Gen.Equality (
    -- * Generators
    ECTAGen,
    Grouped,
    module Data.CFTA.Gen,

    -- * Imported automata
    fromAutomaton,
    fromAutomatonUpToDepth,
) where

import Data.Text (Text)
import qualified Data.Tree as Tree

import Data.CFTA.Equality (Node)
import Data.CFTA.Equality.Constraint (EqConstraints)
import Data.CFTA.Gen hiding (Grouped, fromAutomaton, fromAutomatonUpToDepth)
import qualified Data.CFTA.Gen as Gen
import qualified Data.CFTA.Gen.Internal.Flat as Flat
import Data.CFTA.Symbol (Symbol (Symbol))

-- | A generator over equality-constrained tree automata.
type ECTAGen = Gen Symbol EqConstraints

-- | A grouped generator over equality-constrained tree automata.
type Grouped = Gen.Grouped Symbol EqConstraints

-- | The text of a symbol, the order in which symbolic counts rank constructors.
symbolText :: Symbol -> Text
symbolText (Symbol name) = name

{- | Read an equality-constrained automaton as a generator of the terms it
accepts, as 'Data.CFTA.Gen.fromAutomaton' does, with symbolic ranks ordered
by symbol text.
-}
fromAutomaton :: Node Symbol EqConstraints -> ECTAGen (Tree.Tree Symbol)
fromAutomaton = Flat.fromAutomaton symbolText

-- | Read the terms an automaton accepts up to a constructor-depth bound. A leaf has depth zero.
fromAutomatonUpToDepth :: Int -> Node Symbol EqConstraints -> ECTAGen (Tree.Tree Symbol)
fromAutomatonUpToDepth = Flat.fromAutomatonUpToDepth symbolText
