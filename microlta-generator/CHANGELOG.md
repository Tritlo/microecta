# Changelog

## 0.1.0.0 - Unreleased

Initial release.

- Compilation remains symbolic. Bounded imports count overlapping runs and
  Boolean subtree equality without enumerating accepted terms. Unsupported
  guards and value-computed refinements return errors. `validOutcomes` retains
  explicit candidate enumeration for diagnostics.

- `Data.LTA.Gen` and `Data.LTA.Gen.Do`: finite generators whose support is a
  liquid tree automaton, built from refined pools and guarded constructors
  with qualified-do syntax, or imported from a bounded `Automaton` or a
  derived datatype grammar with liquid annotations.
- `compile` checks every guard once with the solver and returns pure
  sampling, replay through `unrank`, and semantic shrinking. Explicit
  automaton compilers and a relational compiler are available for their
  specific rank and shrink contracts.
- `Data.LTA.Gen.QuickCheck`: sampling, replay, shrinking, and opaque pools
  through QuickCheck.
