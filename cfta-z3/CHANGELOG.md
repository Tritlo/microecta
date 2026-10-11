# Changelog

## 0.1.0.0 - Unreleased

Initial release. `Data.CFTA.Refinement.LiquidFixpoint`, moved out of
`cfta`: the `Entailment` that decides implications with Z3 through the
SMT interface of Liquid Fixpoint. It translates each formula of
`Data.CFTA.Formula` to Liquid Fixpoint at the port and declares every name as
an integer; `withZ3`, `withZ3Assuming`, and `withZ3Timeout` take the names and
the assumptions as core values. This is the only package that depends on
`liquid-fixpoint`. The specs of `cfta` that run Z3 move here, so the tests of
`cfta` need no Z3.
