# Changelog

## 0.1.0.0 - Unreleased

Initial release. The refinement layer of `cfta` moves here:
`Data.CFTA.Refinement` and its modules, except
`Data.CFTA.Refinement.Expression`, which builds the formulas of a `Symbol`
and stays in `cfta`. The specs of the refinement layer and the
`cross-layer-speed` benchmark move along. The specs decide guards without
Z3; the specs that run Z3 are in `cfta-z3`.
