# microcfta-generator

Ranked generation, random sampling, replay, and shrinking for the automata of
[`microcfta`](../microcfta/README.md), with QuickCheck integration. There is
one generator type, `Gen symbol a`, and one facade per kind of automaton:

| Module | Purpose |
| --- | --- |
| `Data.CFTA.Ranked`, `Data.CFTA.Ranked.QuickCheck` | Finite ranks, weighted sampling, replay, and structural shrinking, independent of automata. |
