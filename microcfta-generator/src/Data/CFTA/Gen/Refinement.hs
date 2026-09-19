{- | Finite generators whose support is a liquid tree automaton.

'pool' supplies refined atoms. 'node' adds one constructor around an
applicatively-built child forest; "Data.CFTA.Gen.Refinement.Do" provides the corresponding
qualified-do syntax. 'compile' checks guards and refinement-shrink relations
once, then returns pure sampling, replay, and shrinking.
-}
module Data.CFTA.Gen.Refinement (
    LTAGen,
    Compiled,
    CompiledSupport (..),
    GeneratorError (..),
    explain,
    Generated (..),

    -- * Refined sources
    Refined,
    refined,
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
    fromLTA,
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
    shrinkRank,
    smallerMembers,

    -- * Qualified-do support
    Children,
    NodeLayer,
    children,
    applyChildren,
) where

import Data.CFTA.Gen.Refinement.Internal.AutomatonCompile (
    compileAutomaton,
    compileAutomatonUpToDepth,
    compileAutomatonUpToDepthWith,
    compileAutomatonWith,
 )
import Data.CFTA.Gen.Refinement.Internal.Compile (compile, validOutcomes)
import Data.CFTA.Gen.Refinement.Internal.Error (GeneratorError (..), explain)
import Data.CFTA.Gen.Refinement.Internal.Relational (compileRelational)
import Data.CFTA.Gen.Refinement.Internal.Replay (cardinality, mapCompiled, shrinkRank, smallerMembers, unrank)
import Data.CFTA.Gen.Refinement.Internal.Surface (
    binary,
    frequency,
    fromDatatypeUpToDepth,
    fromLTA,
    leaf,
    minimizePoolBy,
    node,
    oneof,
    pool,
    refined,
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
    Refined,
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
'fromLTA' with 'compile' when the automaton can be one source among others.
-}
