# microecta

This repository contains four Cabal packages:

| Package | Purpose |
| --- | --- |
| [`microecta`](microecta/README.md) | A general FTA structure plus the equality-constrained tree automata core. |
| [`microecta-generator`](microecta-generator/README.md) | Shared ranked FTA generation plus ECTA-specific combinators and QuickCheck integration. |
| [`microlta`](microlta/) | Liquid tree automata using Liquid Fixpoint predicates and Z3 entailment. |
| [`microlta-generator`](microlta-generator/) | Compile-once liquid generators with pruning, replay, semantic shrinking, and bounded recursion. |

`Data.Tree.FTA` is the shared ranked-transition graph. `Data.Tree.FTA.Syntax`
constructs ordinary FTAs; `Data.ECTA.FTA.Syntax` owns equality-constrained
transitions, while `Data.LTA.Syntax` owns refinement-labelled transitions and
liquid guards. Constraint theories remain in their own namespaces.

`microecta-generator` depends on `microecta`; the core package does not depend
on the generator package or on QuickCheck. `Data.Tree.Gen` provides exact
finite ranks, backend-independent sampling, and shrinking, while
`Data.Tree.FTA.Gen` either compiles an acyclic ordinary FTA or builds one with
the `FTA.node`/`FTA.do` syntax before lowering it into that representation.
`microlta-generator` checks liquid guards and pool-refinement implications once,
then reuses this pure ranked layer for every sample, replay, and shrink.

Enter `nix-shell` to put Z3 on `PATH`, then run the semantic entailment example:

```sh
cabal run liquid-pairs
```

`microlta` implements refinement-labelled recognition, Boolean guards,
actual-for-formal position substitutions, semantic intersection, similarity
comparison, and recursive LTAs with the paper's acyclic-guard restriction.
`microlta-generator` adds named guard syntax, finite or frozen QuickCheck pools,
semantic pruning and shrinking, opt-in similarity minimisation, and explicitly
bounded generation from recursive LTAs. It is an automata and generator library,
not the Hegel component-based synthesizer from the paper.

See [`docs/automata-syntax.md`](docs/automata-syntax.md) for the side-by-side
FTA, ECTA, and LTA construction forms and the rationale for the guard-lambda
syntax.

## Three flagship languages

The generator APIs close qualified-do child blocks consistently with
`FTA.node`, `ECTA.node`, and `LTA.node`. Three worked languages make the added
expressive power concrete:

| Automaton | Example | What becomes possible |
| --- | --- | --- |
| FTA | [`UntypedExpressionLanguage`](microecta-generator/common/Data/Tree/FTA/UntypedExpressionLanguage.hs) | Generate integer expression shapes. Every term has the one implicit sort. |
| ECTA | [`TypedExpressionLanguage`](microecta-generator/common/Data/ECTA/TypedExpressionLanguage.hs) | Add integers and Booleans, then equate operation signatures with child result types. |
| LTA | [`StateMachineTraceLanguage`](microlta-generator/common/Data/LTA/StateMachineTraceLanguage.hs) | Carry a typed operand stack from one command to the next and prove dependent input/output state contracts with Z3. |

The LTA example generates a complete QuickCheck trace before executing it, as
state-machine testing requires. `Push`, `Add`, `And`, `Equal`, `Not`, and `Pop`
are retained only when the previous trace's output stack is a subtype of the
next command's input space. The resulting trace is then replayed through both
an abstract model and a separate concrete interpreter.

Two smaller examples remain useful alongside that progression. The ECTA
[filesystem ownership join](microecta-generator/test/Data/ECTA/GenSpec.hs)
shows flat equality conditioning, while
[`SafeBufferLanguage`](microlta-generator/common/Data/LTA/SafeBufferLanguage.hs)
shows Z3 proving symbolic bounds and dependent append lengths before a partial
buffer interpreter reaches QuickCheck.

## Generator benchmarks

The three flagship languages are benchmarked against both naive
recognition/rejection and a handwritten bespoke generator. Every comparison is
uniform over the same exact language at each depth or trace length; cells run
in fresh processes, include a cold first-sample measurement, and time out after
30 seconds. The measured tables and methodology live in the
[`microecta-generator`](microecta-generator/README.md#sampling-performance) and
[`microlta-generator`](microlta-generator/README.md#sampling-performance)
READMEs.

Generate all three FTA, ECTA, and LTA tables from the repository root with:

```sh
./scripts/benchmark-generators.sh
```

Build and test the whole workspace from the repository root:

```sh
cabal build all -j1
cabal test all -j1
```

The examples in the public entry-point modules are executable. Run them with
[`doctest`](https://hackage.haskell.org/package/doctest):

```sh
cabal install doctest
cabal repl --with-repl=doctest lib:microecta
cabal repl --with-repl=doctest lib:microecta-generator
cabal repl --with-repl=doctest lib:microlta
cabal repl --with-repl=doctest lib:microlta-generator
```
