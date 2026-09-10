# LTA paper conformance

This file is the implementation ledger for the automaton abstraction and
transformations in *Liquid Tree Automata* by Ashish Mishra and Suresh
Jagannathan. MicroECTA may implement an equivalent operation more efficiently,
but an ECTA representation is never the definition of LTA semantics.

## Required architecture

The authoritative path is:

```text
ranked alphabet + LTA constraints
             |
             v
      LTA recognition and denotation
             |
             v
       Prune -> Similarity -> Minimize
             |
             v
       bounded enumeration
```

An optimization may lower a reduced LTA to ECTA only after proving that every
remaining constraint is expressible as positive ECTA path equality. Unsupported
constraints stay in the LTA; they are not erased, approximated, or rejected by
the semantics layer merely to make counting convenient.

## Conformance ledger

| Paper requirement | Current evidence | Status | Required correction |
| --- | --- | --- | --- |
| Definition 2: finite ranked alphabet, states, final states, and constrained transitions | A complete `LiquidSymbol` pair is one ranked-alphabet symbol; `automatonAlphabet` exposes the finite set. `mkAutomatonWithFinals` normalizes arbitrary `Qf` to one fresh state whose row is their union | Implemented by a documented language-preserving normalization | Keep the product alphabet distinct from the convenience surface encoding that annotates program roots |
| Figure 5: atomic syntactic equality and semantic entailment under substitution, negation, conjunction, and disjunction | `Guard` contains `Same`, `Entails`, `Substitute`, `Not`, `And`, and `Or`; `LiquidConstraint` can reify its normalized equality cache with `constraintAsGuard` | Implemented | Keep the split equality field as a compiled positive-conjunction cache only |
| Figure 6: acceptance checks the complete transition constraint over the candidate term | `accepts` checks positive cached equalities and the complete residual `Guard`; `Same` compares complete ranked trees. `denotationAtMost` is a bounded reference interpreter and deduplicates multiple accepting runs | Implemented | Use this deliberately materializing denotation as the bounded semantics oracle for optimizations |
| Definition 5: transitions at arbitrary positions | `transitionsAt` exposes transition traversal; internal state traversal shares the same path interpretation. Figure 12 checks the formula alternatives at its left position | Implemented | Retain this as the similarity primitive |
| Figure 9 P-Syn-Eq: syntactic intersection | `pruneSyntacticEqualities` extracts only positive conjunctive `Same` atoms, performs the exact-label FTA product, and retains the source LTA constraint. The generator fixture lowers two independent choices through MicroECTA and gets exactly the two equal pairs | Implemented | Extend bounded oracle comparisons before broadening the lowerable Boolean fragment |
| Figure 9 P-Sem-Ent and Equation 4: directional semantic intersection | `semanticIntersection` is directional and state splitting prunes homogeneous refinement-symbol combinations. The Figure 12 fixture represents each formula as a nullary `LiquidSymbol "predicate" formula` | Implemented | Keep checking bounded denotation before and after pruning |
| Figure 9 S-Trans/S-Eq: infer transition similarity from type subautomata | `similarity` computes transition pairs using a caller-supplied `Subtyping` relation | Implemented with a parameterized subtyping relation | Keep domain-specific subtyping outside the automaton mechanics |
| Figure 9 M-Trans/M-LTA: remove a supertype transition and redirect incoming edges | `minimize` batches the paper's transitive closure: it resolves transitive representatives, removes supertypes, and redirects incoming edges. It rejects shared-target or final-target shapes outside the paper construction invariant; fixtures cover direct, transitive, and overlapping-incomparable relations | Implemented under the paper construction invariant | Preserve the deterministic first-inferred representative policy unless the paper construction supplies a stronger ordering |
| Definition 7: constrained positions resolve only to acyclic states | `mkAutomaton` checks every referenced path against `cyclicStates` | Implemented | Preserve this check when the constraint AST is restored |
| Enumeration of equality-constrained residual languages | `pruneToECTA` lowers only the positive-equality fragment; `Data.LTA.ECTA` converts finite acyclic support to a real MicroECTA; the generator enumerates that ECTA as a correctness baseline | Implemented, materializing | Add a non-materializing equality-aware ranker without changing the boundary |
| Optional relational optimization | `compileRelational` uses retained applicative recipes and trusted root projections | Experimental | Keep behind an explicit optimization API and validate its language against the authoritative LTA path on bounded inputs |

## Acceptance gates

The implementation is paper-conforming only when all of the following hold:

1. Every constraint in Figure 5 is representable and recognized, including
   equality below `Not`, `Or`, and `Substitute`.
2. `Prune` preserves the LTA language and returns an LTA. ECTA lowering is a
   separately named operation that can fail without changing LTA semantics.
3. The paper's pruning, similarity, minimization, and cycle rules
   each have an executable correspondence in the code and an example derived
   from the paper.
4. The general implementation works without `compileRelational`.
5. Every optimization is checked against the general implementation on bounded
   automata before benchmark results are treated as LTA results.
6. Documentation distinguishes authoritative LTA semantics from optional ECTA
   and QuickCheck generator adapters.
