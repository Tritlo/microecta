# Next steps

## Fuse the expandable-variable scan

Treat experimental commit `e3987e0` as a prototype, not a patch to cherry-pick. It removed the per-expansion `refreshReferencedUVars` sweep and made `findExpandableUVars` collect candidates and resolve suspended-constraint targets in one pass, using `IntSet` rather than the older speculative bitvector idea. Port or adapt that design to `standard-ectagen` without losing its newer caller-directed `ExpansionOrder` behavior.

Before claiming an improvement, benchmark the current branch against the adapted implementation on constrained-enumeration workloads. Measure time and allocation separately, and isolate the refresh/scan work closely enough to confirm or retire the inherited claim that `refreshReferencedUVars` costs roughly one third of `enumerateFully`'s time and half its allocations. The old prototype's roughly threefold speedup is evidence that this is worth investigating, not an acceptance result for the current code.

Pursue the change only if the benchmark shows a repeatable improvement without changing enumeration results or expansion-order semantics.

## Experiment with typed recursive identifiers

Prototype parameterizing `Node` (and necessarily the recursive parts of `Edge` and related operations) over the recursive-identifier type. The aim is to make construction phases explicit and rule out invalid identifier forms—for example, keeping intersection-only `RecIntersect` references out of fully interned nodes—instead of representing every phase with the `RecNodeId` sum.

Keep this as a design experiment: it may spread a type parameter through the public API, interning and memoization keys, recursion helpers, intersection, substitution, and pattern synonyms, with possible inference and performance costs. Do not migrate production code as part of the experiment.

Pursue the design only if a small compiling prototype removes meaningful runtime invariants or partial cases while preserving a usable public API and showing no material benchmark regression. Otherwise document the boundary discovered and retain `RecNodeId` as the pragmatic representation.
