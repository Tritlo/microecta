# Rank imported edges by arity and symbol text

## Why

`fromECTA` ranked the alternatives of a node in `nodeEdges` order. An interned
node keeps its edges in edge-identity order (`mkNode` builds it from a
`Set` of edges, and `Ord Edge` compares identities), which is the order in
which the process interned the edges. So the ranks of one automaton
depended on what the process had built before: two processes, or two
threads, could give different terms at one rank. `AGENTS.md` asks for the
opposite: "the same automaton or generator gives the same ranks in every
process". Sorting by `Ord Symbol` would not help, because `Symbol` compares
`InternedText` by its intern identity too.

`automatonIndex` now sorts the edges of each node by arity, then by the
symbol text, as `cfta`'s import sorts by arity, then by the key of the symbol
(in `cfta`'s first generator commits on `microcfta`; the test is in
`f128763e`, "Add the ordinary generator facade"). Arity
first keeps the leaves of a size class before its constructors, so rank
shrinking moves toward leaves. Edges with the same arity and symbol keep the
node's order, which is interning order; the `fromECTA` Haddock and the
CHANGELOG say so.

Probe (`GenProbe.hs`, group `order`): the symbol interned first is `order-b`
(resp. `order-d`). On `main`:

```
order: ranks 0 and 1 of fromECTA (Node [order-a, order-b]), order-b interned first: Right [Term "order-b" [],Term "order-a" []]
order: ranks 0 and 1 of a recursive import, order-d interned before order-c: Right [Term "order-d" [],Term "order-c" []]
```

On this branch:

```
order: ranks 0 and 1 of fromECTA (Node [order-a, order-b]), order-b interned first: Right [Term "order-a" [],Term "order-b" []]
order: ranks 0 and 1 of a recursive import, order-d interned before order-c: Right [Term "order-c" [],Term "order-d" []]
```

## Tests

Ported from `cfta`: "ranks imported alternatives in symbol order, not in
interning order" (in `RecursiveGenSpec`). It interns the later symbol first,
then checks the ranks of a finite and of a bounded recursive import. Its
symbols appear in no other test, because interning is global to the
process.

## Gate

GATE-RESULTS

## Cost

COST-RESULTS
