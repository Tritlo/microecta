{- | Finite generators whose support is a liquid tree automaton.

'pool' supplies refined atoms. 'node' adds one constructor around an
applicatively-built child forest; "Data.CFTA.Gen.Do" provides the corresponding
qualified-do syntax. 'compile' checks guards and refinement-shrink relations
once, then returns pure sampling, replay, and shrinking. A construction
failure stays inside the generator; 'compile' reports it.
-}
module Data.CFTA.Gen.Refinement (
    LTAGen,
    Compiled,
    CompiledSupport (..),
    GenError (..),
    explain,
    Generated (..),

    -- * Refined sources
    Refined (..),
    pool,
    minimizePoolBy,
    leaf,

    -- * Tree constructors
    node,
    refinedNode,
    refinedNodeBy,
    refinedNodeByRoots,
    RootObservation (..),
    unary,
    binary,
    frequency,
    oneof,
    fromAutomatonUpToDepth,
    fromDatatypeUpToDepth,

    -- * Compilation
    -- $choosing
    compile,

    -- ** Explicit compilers
    compileRelational,
    compileAutomaton,
    compileAutomatonWith,
    compileAutomatonUpToDepth,
    compileAutomatonUpToDepthWith,

    -- * Inspection, replay, and shrinking
    support,
    validOutcomes,
    mapCompiled,
    compiledSupport,
    compiledRanked,
    cardinality,
    unrank,
    termAt,
    shrinkRank,
    smallerMembers,

    -- * Qualified-do support
    Children,
    NodeLayer,
    children,
    applyChildren,
) where

import Data.CFTA.Gen.Error (GenError (..), explain)
import Data.CFTA.Gen.Refinement.Internal.AutomatonCompile (
    compileAutomaton,
    compileAutomatonUpToDepth,
    compileAutomatonUpToDepthWith,
    compileAutomatonWith,
 )
import Data.CFTA.Gen.Refinement.Internal.Compile (compile, validOutcomes)
import Data.CFTA.Gen.Refinement.Internal.Relational (compileRelational)
import Data.CFTA.Gen.Refinement.Internal.Replay (cardinality, mapCompiled, shrinkRank, smallerMembers, termAt, unrank)
import Data.CFTA.Gen.Refinement.Internal.Surface (
    binary,
    frequency,
    fromAutomatonUpToDepth,
    fromDatatypeUpToDepth,
    leaf,
    minimizePoolBy,
    node,
    oneof,
    pool,
    refinedNode,
    refinedNodeBy,
    refinedNodeByRoots,
    support,
    unary,
 )
import Data.CFTA.Gen.Refinement.Internal.Types (
    Children,
    Compiled (compiledRanked, compiledSupport),
    CompiledSupport (..),
    Generated (..),
    LTAGen,
    NodeLayer,
    Refined (..),
    RootObservation (..),
    applyChildren,
    children,
 )

{- $choosing
Use 'compile' to retain source order, weights, and semantic shrinking.
Compilation is symbolic. Unsupported value-computed refinements and guards
produce an error. Use 'validOutcomes' to enumerate a small input explicitly.

The explicit compilers exist for two situations. 'compileRelational' keeps
the native grouped ECTA rank order and structural shrinking of a generator
whose guards only inspect roots; its ranks and shrinks differ from
'compile'. 'compileAutomaton' and 'compileAutomatonUpToDepth' start from an
'Automaton' rather than a generator; prefer
'fromAutomatonUpToDepth' with 'compile' when the automaton can be one source among others.
-}
