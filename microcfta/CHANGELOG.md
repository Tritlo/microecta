# Changelog

## 0.1.0.0 - Unreleased

Initial release. `microcfta` consolidates an ordinary tree automaton engine,
equality-constrained tree automata, and liquid tree automata into one package
with one representation. The equality layer descends from `microecta`, which
remains a separate ECTA-only package.

- `Data.CFTA.Symbol`: interned text symbols shared by every layer.
