# Changelog

## 0.1.0.0 - Unreleased

Initial release. `microcfta-generator` is one generator over the constrained
tree automata of `microcfta`, with QuickCheck integration.

- `Data.CFTA.Gen`: one generator type, `Gen symbol constraint a`, for every
  constraint theory. An ordinary generator is `FTAGen symbol a`, that is
  `Gen symbol ()`; the equality and refinement facades fix the theory in
  `ECTAGen` and `LTAGen`. Sources (`elements`, `leaf`,
  `namedElements`, `fromIndexed`, `fromGen`), constructors closed with
  `node`, `frequency` and `oneof`, `match` and `relate` joins, the grouped
  layer with `Sig` signatures and `apply`, recursion with `recur`, `atomic`,
  and `upToSize`, and exact inspection: `cardinality`, `values`, `unrank`,
  `termAt`, `support`, `inspect` with `drawInspection`, size counts, `pmf`,
  structural `shrinkRank`, and `smallerMembers`. Every construction failure
  lives inside the generator as one `GenError` with `explain`, and `orFail`
  fails with that text.
- `Data.CFTA.Gen.QuickCheck`: `toGen`, `toGenWithRank`, `forAll` with
  size-minimal counterexamples, `sized`, and the frozen pools `samplePool`
  and `freeze`. `Data.CFTA.Gen.Do`: qualified applicative do-notation for
  every theory.
- Imported automata: `fromAutomaton` reads an acyclic automaton as a finite
  generator with one rank per distinct term, counted symbolically where
  alternatives overlap or equalities reach below direct children, and a
  cyclic automaton as a recursive generator counted by size.
  `fromAutomatonUpToDepth` bounds first. `fromDatatype` and
  `fromDatatypeUpToDepth` read derived grammars of any theory.
- `Data.CFTA.Gen.Equality`: `ECTAGen`, symbol-text rank order for imports,
  and the `EqConstraints` theory of `Data.CFTA.Equality`. The engine's
  `support` and `termAt` return graphs and terms over `Data.CFTA.Gen.Label`,
  which wraps user symbols in `Label` and types the private labels;
  `surface` reads the user's term back.
- `Data.CFTA.Gen.Refinement`: `LTAGen` with sources (`elements`, which infers
  the exact refinement of each integer; `integers`, a leaf of all integers
  that conditions narrow and that `compile` counts without enumeration, also
  under a linear contract over several integer children; `every`, the same for
  every value of a type with a `Literal` instance, such as `Word8`, `Char`,
  `Bool`, or an enumeration; `pool`, of values with hand-written
  refinements; `namedPool`; `leaf`; and `checkPool`, which asks the solver to
  prove the refinements of a pool), conditions on a drawn child with
  `satisfying`, constructors (`node`; `guarded`, whose contract relates the
  children; and `refinedNode` and `refinedNodeByRoots` for the paper's
  positional guards and result refinements), results with `ensuring`, a term
  of the children that becomes the constructor's refinement and stays a term
  of integer children, bounded recursion with `recurUpTo`, liquid automaton and datatype
  imports, `minimizePoolBy`, `compile` with Z3, `compileAssuming`,
  `compileWith`, and `validOutcomes`. A constructor that needs the solver,
  and an import whose guards the engine cannot count, defer the generator;
  `compile`
  folds the generator's recipe once with the solver: child languages are
  grouped by the observations a guard reads, the solver decides each guard
  once per tuple of groups, imports are pruned and split by the same
  observations without enumerating terms, and the result is an ordinary
  finite generator with exact counts, source-ordered ranks, structural
  shrinking, and no solver at sampling time.
- `Data.CFTA.Constraint` gains `indicators`, a constraint read as a signed
  sum of equality indicators, so the symbolic counter handles Boolean
  equality guards of the liquid theory without the solver.
- `Data.CFTA.Ranked`: finite ranks, weighted sampling, replay, and structural
  shrinking, independent of automata, with `Data.CFTA.Ranked.QuickCheck`.
- The engine modules `Data.CFTA.Gen.Internal.*` and the ranked internals
  `Data.CFTA.Ranked.Internal.*` are exposed for integration and stay outside
  the PVP contract.
- Two test suites, `gen-tests` and `refinement-tests` (needs `z3`), and one
  copy of the generator benchmark harness.
