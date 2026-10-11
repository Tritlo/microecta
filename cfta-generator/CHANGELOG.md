# Changelog

## 0.1.0.0 - Unreleased

Initial release. `cfta-generator` is one generator over the constrained
tree automata of `cfta`, with QuickCheck integration.

- `Data.CFTA.Gen`: one generator type, `Gen symbol a`, for every kind of
  automaton. An ordinary generator is `FTAGen symbol a`, that is
  `Gen symbol a`; the equality and refinement facades fix the symbol in
  `ECTAGen` and `LTAGen`. The sources are `elements`, `leaf`,
  `namedElements`, `fromIndexed`, and `fromGen`. `node` closes a constructor,
  and `frequency` and `oneof` choose. `match` and `relate` join two generators,
  and the grouped layer joins more with `Sig` signatures and `apply`. `recur`,
  `atomic`, and `upToSize` make and bound recursive languages. The exact
  inspectors are `cardinality`, `values`, `unrank`, `termAt` with its inverses
  `rankOf` and `ranksOf`, `support`, `inspect` with `drawInspection`, the
  counts by size, `pmf`, the structural `shrinkRank`, and `smallerMembers`. A
  generator keeps each construction failure as one `GenError`. `explain`
  describes it, and `orFail` fails with that text.
- Sizes count pays, as in FEAT: `pure` has size zero, an atom one, `<*>` adds
  the sizes of its sides, and `pay`, which `Data.CFTA.Gen` and
  `Data.CFTA.Ranked` export, adds one. A constructor pays one, so a built tree
  and an imported term both count their nodes. The `Functor` and
  `Applicative` laws hold for sizes. A join (`match`, `relate`) adds the sizes
  of its sides, as a product does. A recursion must reach each occurrence
  through a pay, or through a product whose other side has no member of size
  zero. It must also pass through a product or a constructor. See
  `docs/adr/0002-sizes-count-pays.md`.
- `Data.CFTA.Gen.QuickCheck`: `toGen`, `toGenWithRank`, `forAll` with
  size-minimal counterexamples, `sized`, and the frozen pools `samplePool`
  and `freeze`. `Data.CFTA.Gen.Do`: qualified applicative do-notation for
  every theory.
- Imported automata: `fromAutomaton` reads an acyclic automaton as a finite
  generator with one rank per distinct term, counted symbolically where
  alternatives overlap or equalities reach below direct children, and a
  cyclic automaton as a recursive generator counted by size.
  `fromAutomatonUpToDepth` bounds first. `fromDatatype` and
  `fromDatatypeUpToDepth` read derived grammars of any theory, and report
  `UndecodableConstructor` when the codec rejects a term of the grammar.
  Ranks order the constructors at each node by arity, then by the symbol,
  or in declaration order for a datatype, so they are the same in every run.
  `rankOfTerm` gives the rank of an accepted term, and `rankOfValue` the
  rank of a datatype value through its codec.
- Terms are `Term symbol` from `Data.CFTA.Term` of `cfta`:
  `fromAutomaton`, `fromAutomatonUpToDepth`, `termAt`, `rankOf`, `ranksOf`,
  `rankOfTerm`, `surface`, and the refinement witnesses take and give `Term`
  terms in place of `Data.Tree.Tree`.
- `Data.CFTA.Gen.Equality`: `ECTAGen`, symbol-text order for imports,
  and equality constraints from `Data.CFTA.Equality`. The engine's
  `support` and `termAt` return graphs and terms over `Data.CFTA.Gen.Label`,
  which wraps user symbols in `Label` and types the private labels;
  `surface` reads the user's term back.
- `Data.CFTA.Gen.Refinement`: `LTAGen`. Its sources are `elements`, which
  infers the exact refinement of each integer; `every`, a leaf of every value
  of a type with a `Literal` instance, such as `Integer`, `Word8`, `Char`,
  `Bool`, or an enumeration; `pool`, of values with hand-written refinements;
  `namedPool`; and `leaf`. `checkPool` asks the solver to prove the
  refinements of a pool. `satisfying` puts a condition on a drawn child, and
  on `every` it narrows the values. The constructors are `node`; `guarded`,
  whose contract relates the children; and `refinedNode` and
  `refinedNodeByRoots` for the paper's positional guards and result
  refinements. `measured` closes a constructor with a contract and a measure:
  the integer of each constructed term, as a term of the measures of its
  children, which becomes the constructor's refinement and stays a term of
  children from `every`. `measuredNode` takes a positional guard in place of
  the contract. `recurUpTo` unfolds a recursive description a bounded number
  of times. The module also has liquid automaton and datatype imports,
  `minimizePoolOn`, `compile` with Z3, `compileAssuming`, `compileWith`, and
  `validOutcomes`.
- `compile` folds the recipe of a generator once with the solver. It groups
  child languages by the observations a guard reads, decides each guard once
  for each tuple of groups, and prunes and splits imports by the same
  observations without enumerating terms. It counts the values of `every`
  without enumeration, also under a linear contract over several such
  children. The result is an ordinary finite generator with exact counts,
  source-ordered ranks, and structural shrinking, and sampling makes no solver
  calls. A constructor that needs the solver, and an import whose guards the
  engine cannot count, defer the generator until `compile`.
- `Data.CFTA.Ranked`: finite ranks, weighted sampling, replay, and structural
  shrinking, independent of automata, with `Data.CFTA.Ranked.QuickCheck`.
- The engine modules `Data.CFTA.Gen.Internal.*` and the ranked internals
  `Data.CFTA.Ranked.Internal.*` are exposed for integration and stay outside
  the PVP contract.
- Two test suites, `gen-tests` and `refinement-tests` (needs `z3`), and one
  copy of the generator benchmark harness.
