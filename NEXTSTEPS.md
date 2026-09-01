# Next steps

## Experiment with typed recursive identifiers

Prototype parameterizing `Node` (and necessarily the recursive parts of `Edge` and related operations) over the recursive-identifier type. The aim is to make construction phases explicit and rule out invalid identifier forms—for example, keeping intersection-only `RecIntersect` references out of fully interned nodes—instead of representing every phase with the `RecNodeId` sum.

Keep this as a design experiment: it may spread a type parameter through the public API, interning and memoization keys, recursion helpers, intersection, substitution, and pattern synonyms, with possible inference and performance costs. Do not migrate production code as part of the experiment.

Pursue the design only if a small compiling prototype removes meaningful runtime invariants or partial cases while preserving a usable public API and showing no material benchmark regression. Otherwise document the boundary discovered and retain `RecNodeId` as the pragmatic representation.
