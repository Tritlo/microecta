{- | Generators over equality-constrained tree automata.

An equality generator is a generator over 'Symbol'. Its automata use the
theory of "Data.CFTA.Equality": an edge can require that the subterms at two
of its paths are equal ('Data.CFTA.Constraint.equalityConstraint'). All of
"Data.CFTA.Gen" applies. The joins 'match', 'relate', and 'apply' write their
keys as such equalities, so the support of a joined language is one automaton
with these constraints.

This module fixes the symbol type in 'ECTAGen' and 'Grouped'. Imported
automata rank constructors by arity, then by the order of 'Symbol': the text,
then the refinement. So ranks do not depend on the order in which symbols were
interned.
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

import Data.CFTA.Equality (Node)
import Data.CFTA.Gen hiding (Grouped, fromAutomaton, fromAutomatonUpToDepth)
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Index (Depth)
import Data.CFTA.Symbol (Symbol)
import Data.CFTA.Term (Term)

-- | A generator over equality-constrained tree automata.
type ECTAGen = Gen Symbol

-- | A grouped generator over equality-constrained tree automata.
type Grouped = Gen.Grouped Symbol

{- | Read an equality-constrained automaton as a generator of the terms it
accepts: 'Data.CFTA.Gen.fromAutomaton' at 'Symbol'.
-}
fromAutomaton :: Node Symbol -> ECTAGen (Term Symbol)
fromAutomaton = Gen.fromAutomaton

-- | Read the terms an automaton accepts up to a constructor-depth bound. A leaf has depth zero.
fromAutomatonUpToDepth :: Depth -> Node Symbol -> ECTAGen (Term Symbol)
fromAutomatonUpToDepth = Gen.fromAutomatonUpToDepth
