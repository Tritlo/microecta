# Changelog

## 0.1.0.0 - Unreleased

Initial release. `microcfta-generator` is one generator over the constrained
tree automata of `microcfta`, with QuickCheck integration.

- `Data.CFTA.Gen`: one generator type, `Gen symbol a`, for every kind of
  automaton. An ordinary generator is `FTAGen symbol a`, that is
  `Gen symbol a`; the equality and refinement facades fix the symbol in
  `ECTAGen` and `LTAGen`. Sources (`elements`, `leaf`,
  `namedElements`, `fromIndexed`, `fromGen`), constructors closed with
  `node`, `frequency` and `oneof`, `match` and `relate` joins, the grouped
  layer with `Sig` signatures and `apply`, recursion with `recur`, `atomic`,
  and `upToSize`, and exact inspection: `cardinality`, `values`, `unrank`,
  `termAt` with its inverse `rankOf` and `ranksOf`, `support`, `inspect` with
  `drawInspection`, size counts, `pmf`,
  structural `shrinkRank`, and `smallerMembers`. A generator keeps every
  construction failure as one `GenError` with `explain`, and `orFail` fails
  with that text.
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
  refinements. `ensuring` gives a constructor a result term of its children,
  which becomes the constructor's refinement and stays a term of children from
  `every`; on a generator that is not such a constructor it reports
  `ResultNeedsConstructor`. `recurUpTo` unfolds a recursive description a bounded number of
  times. The module also has liquid automaton and datatype imports,
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
- `Data.CFTA.Constraint` gains `indicators`, a constraint read as a signed
  sum of equality indicators, so the symbolic counter handles Boolean
  equality guards of the liquid automata without the solver.
- `Data.CFTA.Ranked`: finite ranks, weighted sampling, replay, and structural
  shrinking, independent of automata, with `Data.CFTA.Ranked.QuickCheck`.
- The engine modules `Data.CFTA.Gen.Internal.*` and the ranked internals
  `Data.CFTA.Ranked.Internal.*` are exposed for integration and stay outside
  the PVP contract.
- Two test suites, `gen-tests` and `refinement-tests` (needs `z3`), and one
  copy of the generator benchmark harness.
