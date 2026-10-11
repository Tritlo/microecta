# Changelog

## 0.1.0.0 - Unreleased

Initial release. `Data.CFTA.Interned.Cache` and `Data.CFTA.Interned.Memo`,
moved out of `cfta`: sharded interning tables that give one identity to
each distinct key, and memo tables, both safe from any thread and selected by
the symbol type. A test suite states their contract.
