# microfta

Describe whole sets of trees with a finite graph. `microfta` derives tree
languages from Haskell datatypes, checks whether a value belongs to a language,
and combines languages with shared structure.

Use it to describe expression grammars, restrict recursive data, or build the
ordinary tree-automaton layer of a constraint system. A finite automaton can
represent an infinite language. You can inspect and transform its grammar
without enumerating its values.

- **Start with your datatype.** Derive `HasFTA` to get a grammar, constructor
  metadata, and codecs between Haskell values and constructor trees.
- **Restrict a language.** Choose finite literal domains, bound tree depth,
  and intersect grammars.
- **Share repeated structure.** Interned nodes reuse equal subgraphs across
  construction and operations.
- **Use the core on its own.** Recognition and graph operations need no
  generator, equality-constraint package, or solver.

## Operations at a glance

`microfta` constructs and transforms grammars, and checks supplied values.
It has no API for enumeration, language cardinality, random sampling, or shrinking.
Those operations belong to the separate `microfta-generator` package.

The table uses these module aliases:

```haskell
import qualified Data.Tree.FTA as FTA
import qualified Data.Tree.FTA.Generic as Generic
import qualified Data.Tree.FTA.Interned as Common
import qualified Data.Tree.FTA.Syntax as Syntax
```

| Operation | API | Result |
| --- | --- | --- |
| Derive a grammar from a datatype | `Generic.deriveFTA`, `Generic.deriveFTAWith` | A grammar with constructor metadata and typed codecs. |
| Build a grammar with named states | `Syntax.automaton`, `FTA.mkFTA` | A checked explicit-state graph. |
| Build a grammar from supplied trees | `FTA.fromTerms` | A grammar that accepts those trees. |
| Encode or decode one value | `Generic.encodeTerm`, `Generic.datatypeDecode` | A constructor tree or a typed value. This does not enumerate the grammar. |
| Check membership | `FTA.accepts`, `Common.nodeRepresentsWith` | Whether a supplied tree belongs. The interned API takes a constraint interpreter. |
| Bound tree depth | `FTA.boundDepth` | Another grammar, restricted to trees within the bound. |
| Intersect languages | `FTA.intersect`, `FTA.intersectWith`, `Common.intersect` | A grammar for the common trees. Annotations require the interpretation described below. |
| Inspect states, transitions, and cycles | `FTA.states`, `FTA.transitionsFrom`, `FTA.cyclicStates` | Graph structure, not accepted values. |
| Change symbols or annotations | `FTA.mapSymbols`, `FTA.annotate`, `FTA.mapGuards`, `FTA.stripGuards` | A transformed graph. Removing annotations does not solve constraints. |
| Build a shared or recursive grammar | `Common.Node`, `Common.Edge`, `Common.Mu` | An interned graph that reuses equal subgraphs. |
| Take a union of languages | `Common.union` | An interned grammar that accepts trees from any input. |
| Count graph nodes and edges | `Common.nodeCount`, `Common.edgeCount` | Graph size, not the number of accepted trees. |
| Convert between graph representations | `Common.toFTA`, `Common.fromFTA` | An explicit-state or interned graph. `fromFTA` requires an acyclic input. |
| Visualize a grammar | `FTA.toTree`, `Common.toTree` | A finite `Data.Tree.Tree String` for `drawTree`. Interned conversion can report an invalid root. |

`FTA` and `Common` are two representations in this package. `FTA` retains
explicit state names. `Common` uses interned nodes and edges to share structure.
Conversion between them does not produce the accepted values.

For example, `FTA.boundDepth 3 grammar` returns a finite grammar. To list its
values, use `microfta-generator`: compile the grammar, then use `cardinality`
and `unrank` to visit its accepting runs. Different runs can produce the same
value if the grammar is ambiguous.

## Start with a datatype

Suppose an expression is a literal or the sum of two expressions. Derive
`HasFTA` with `DeriveAnyClass`, alongside the usual `Generic` instance:

```haskell
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import GHC.Generics (Generic)

import qualified Data.Tree.FTA as FTA
import Data.Tree.FTA.Generic (HasFTA, datatypeDecode, datatypeFTA, deriveFTAWith, domain, encodeTerm)

-- | Arithmetic expressions with integer literals.
data Expr = Lit Int | Add Expr Expr
    deriving stock (Eq, Show, Generic)
    deriving anyclass (HasFTA)

-- | Derive a grammar, recognize values, and restrict their depth.
main :: IO ()
main = case deriveFTAWith @Expr (domain @Int [0, 1]) of
    Left err -> fail (show err)
    Right datatype -> do
        let grammar = datatypeFTA datatype
            value = Add (Lit 0) (Lit 1)
            shallow = FTA.boundDepth 2 grammar

        print (length (FTA.states grammar))
        print (FTA.accepts grammar (encodeTerm value))
        print (FTA.accepts grammar (encodeTerm (Lit 7)))
        print (datatypeDecode datatype (encodeTerm value) == Just value)
        print (FTA.accepts shallow (encodeTerm value))
        print (FTA.accepts shallow (encodeTerm (Add value (Lit 0))))
```

Add `microfta` to your component's `build-depends`. To try the example in this
checkout, save it as `Main.hs` at the workspace root and run:

```sh
cabal build microfta
cabal exec -- runghc -package=microfta Main.hs
```

The output is:

```text
2
True
False
True
True
False
```

The grammar has two states: one for `Expr` and one for `Int`. `Lit` connects
an expression to a literal. `Add` connects it to two more expressions. These
recursive transitions describe expressions of any depth with literals `0`
and `1`.

`encodeTerm` converts a value to a constructor tree. `FTA.accepts` checks that
tree against the grammar. The grammar rejects `Lit 7` because `7` is outside
the configured domain. `datatypeDecode` converts a constructor tree back to
the typed value.

`boundDepth 2` produces a finite language from the recursive grammar. Depth
counts edges from the root: an integer literal is at depth zero, `Lit 0` has
depth one, and `Add (Lit 0) (Lit 1)` has depth two. The nested `Add` in the last
check has depth three, so the bounded grammar rejects it.

### Choose domains and retain metadata

Use `deriveFTA @YourType` when no primitive field needs a domain. `Bool`,
lists, `Maybe`, `Either`, unit, and tuples have built-in `HasFTA` instances.
Derive `HasFTA` for each user datatype in a mutually recursive family.

`Int`, `Integer`, `Char`, and `Text` require explicit finite domains. Combine
domains with `(<>)`; for example, `domain @Int [0, 1] <> domain @Char ['a', 'b']`.
A missing domain produces `Left (MissingDomain ...)`.

The derived graph retains constructor names, field types, and record selector
names. `fieldNamed` locates a record field. `annotateDatatype` adds constructor
annotations while retaining the grammar and its codecs. A constraint layer
can interpret those annotations without rebuilding the datatype description.

The codecs describe the whole datatype. They do not enforce literal domains
or interpret annotations. Use recognition against the grammar to check those
domains. Derivation supports regular algebraic datatypes; it rejects recursion
that grows type arguments. Function fields have no built-in instance. GADTs
and existential fields cannot use the default `Generic` derivation.

## Build languages with shared structure

You can construct a language directly when no Haskell datatype describes it.
Here is a binary tree whose leaves can each be `"zero"` or `"one"`:

```haskell
import qualified Data.Tree.FTA.Interned as Common

choices :: Common.PlainNode String
choices = Common.Node [Common.Edge "zero" [], Common.Edge "one" []]

pair :: Common.PlainNode String -> Common.PlainNode String
pair child = Common.Node [Common.Edge "pair" [child, child]]

language :: Common.PlainNode String
language = iterate pair choices !! 5

sharedNodeCount :: Int
sharedNodeCount = Common.nodeCount language -- 6
```

Each accepted tree has 32 independently chosen leaves. The language contains
4,294,967,296 trees, but its graph has six shared nodes. Constructing the graph
does not construct those trees. Reusing `child` shares its language; it does
not require the two selected child trees to be equal.

`Common.union` combines alternatives. `Common.intersect` retains trees that
both inputs accept. `Common.nodeRepresentsWith (\() _ -> True)` recognizes
ordinary terms. `Common.toFTA` exposes each reachable node as one explicit
state for inspection or use by another package.

`Common.Mu` describes recursive languages. Each recursive cycle must pass
through a constructor edge; `Mu id` is not supported. `Common.toFTA` rejects
an open recursive root.

## Use named states when you need them

The explicit-state interface is useful when a grammar comes from a file or
state names are part of your application:

```haskell
import Data.Tree.FTA (FTAError, PlainFTA, accepts)
import qualified Data.Tree.FTA.Syntax as Syntax
import Data.Tree.Term (Term (Term))

naturals :: Either (FTAError Int String) (PlainFTA Int String)
naturals =
    Syntax.automaton
        0
        [ Syntax.row
            0
            [ Syntax.transition "zero" []
            , Syntax.transition "successor" [0]
            ]
        ]

oneAccepted :: Either (FTAError Int String) Bool
oneAccepted = fmap (`accepts` Term "successor" [Term "zero" []]) naturals

-- Right True
```

An automaton checks symbol arities and child-state references at construction.
Cycles are valid. `PlainFTA` uses `()` for transition annotations.

`Data.Tree.FTA.intersect` constructs reachable product states and pairs the
input annotations. Apply `stripGuards` to the result of two plain FTAs before
calling `accepts`. Use `intersectWith` when you need a different annotation
combination. `stripGuards` removes annotations; it does not solve constraints.

## Visualize a grammar

`FTA.toTree` returns a `Data.Tree.Tree String`. Use `drawTree` to display it.
The recursive `naturals` grammar above produces a finite diagram:

```haskell
import Data.Tree (drawTree)
import qualified Data.Tree.FTA as FTA

drawNaturals :: IO ()
drawNaturals = either (fail . show) (putStr . drawTree . FTA.toTree) naturals
```

```text
state 0
|
+- "zero" [()]
|
`- "successor" [()]
   |
   `- mu 0
```

Each state contains its transition alternatives. Transition labels show the
symbol and annotation; `()` is the ordinary unconstrained annotation. A `mu`
leaf refers to a state on the current path. A `ref` leaf refers to a state
expanded earlier. Each state is expanded once. The view contains only states
reachable from the initial state. It does not enumerate the accepted values.

`Common.toTree` provides the same view for interned graphs. It returns
`Either (FTAViewError symbol) (Tree String)`, because an interned root can have
an open recursive variable or an invalid ranked alphabet. Add `containers` to
your component's `build-depends` when you import `Data.Tree` directly.

## Module guide

| Module | Use it for |
| --- | --- |
| `Data.Tree.FTA.Generic` | Datatype derivation, finite domains, metadata, and typed codecs. |
| `Data.Tree.FTA` | Checked transition graphs, recognition, depth bounds, and product intersection. |
| `Data.Tree.FTA.Syntax` | Named states and transitions without unit-annotation boilerplate. |
| `Data.Tree.FTA.Interned` | Shared nodes and edges, recursive languages, union, and intersection. |
| `Data.Tree.Term` | Concrete constructor trees. |
| `Data.Tree.FTA.Constraint` | Conjunction, the unconstrained value, and known contradictions. |

The interned engine has a symbol type and a constraint type. Ordinary
languages use `()` as the constraint. A `Constraint` instance supplies
conjunction and known contradictions; `nodeRepresentsWith` takes the
concrete-term interpreter. This permits constraint-specific packages to share
the graph implementation.

## Memory and cache lifetime

The explicit-state graphs in `Data.Tree.FTA`, including the datatype tutorial
above, are ordinary Haskell values. The garbage collector can reclaim them
when no references remain.

The interned API uses process-global node, edge, and operation memo tables.
These tables hold strong references and do not evict entries. Reusing a graph
can reuse its cached entries, but constructing distinct graphs can retain
memory for the lifetime of the process. Completing generation or enumeration
does not clear these tables.

There is no safe public reset operation. Interned equality and hashing use
canonical identities. Removing a live node from its table can give a later
copy of the same structure a different identity. Account for this retention
when using the interned API in a long-running process.

## Development

Run the core tests from the workspace root:

```sh
cabal test microfta:unit-tests
```
