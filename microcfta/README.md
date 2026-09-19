# microcfta

Constrained finite tree automata for Haskell. One interned, hash-consed graph
`Node symbol constraint` describes a set of trees, a checked explicit-state
view `FTA state symbol constraint` names its states, and the constraint
parameter selects how much a transition can say:

| Constraint | Type | The transition says | Layer |
| --- | --- | --- | --- |
| none | `()` | These constructor shapes exist. | `Data.CFTA`, `Data.CFTA.Interned` |
| path equality | `EqConstraints` | These child positions hold the same term. | `Data.CFTA.Equality` |
| refinement | `LiquidConstraint` | This position's refinement implies that predicate. | `Data.CFTA.Refinement` |

The ordinary layer is a finite tree automaton (FTA). The equality layer is the
equality-constrained tree automaton (ECTA) of Koppel, Guo, de Vries,
Solar-Lezama and Polikarpova, [*Searching Entangled Program Spaces*, Proc.
ACM Program. Lang. 6(ICFP), 2022](https://doi.org/10.1145/3547622); its
engine descends from the [`microecta`](https://hackage.haskell.org/package/microecta)
package, which remains a separate, ECTA-only line. The refinement layer is the liquid tree automaton (LTA) of Mishra and
Jagannathan, with Liquid Fixpoint refinements and Z3 entailment. Concrete
terms are `Data.Tree.Tree` from `containers`.

- **Start with your datatype.** Derive `HasFTA` to get a grammar, constructor
  metadata, and codecs between Haskell values and constructor trees.
- **Restrict a language.** Choose finite literal domains, bound tree depth,
  intersect grammars, and restrict to a template.
- **Share repeated structure.** Interned nodes reuse equal subgraphs across
  construction and operations.
- **Add constraints only where you need them.** An automaton with no
  constraints is enumerated by the plain level-by-level enumerator. Equality
  constraints are propagated by reduction and solved by unification during
  enumeration. Refinement guards are discharged by pruning with a solver.

Language cardinality, random sampling, replay, and shrinking belong to the
separate `microcfta-generator` package.

## Operations at a glance

The ordinary layer constructs and transforms grammars, and checks supplied
values. `terms` lists the accepted terms by depth. Language cardinality, random
sampling, and shrinking belong to the separate `microcfta-generator` package.

The table uses these module aliases:

```haskell
import qualified Data.CFTA as FTA
import qualified Data.CFTA.Enumeration as Enumeration
import qualified Data.CFTA.Generic as Generic
import qualified Data.CFTA.Interned as Common
import qualified Data.CFTA.Template as Template
```

| Operation | API | Result |
| --- | --- | --- |
| Derive a grammar from a datatype | `Generic.deriveFTA`, `Generic.deriveFTAWith` | A grammar with constructor metadata and typed codecs. |
| Build a grammar with named states | `FTA.mkFTA` | A checked explicit-state graph. |
| Build a grammar from supplied trees | `FTA.fromTerms` | A grammar that accepts those trees. |
| Encode or decode one value | `Generic.encodeTerm`, `Generic.datatypeDecode` | A constructor tree or a typed value. This does not enumerate the grammar. |
| Check membership | `FTA.accepts`, `Common.nodeRepresentsWith` | Whether a supplied tree belongs. The interned API takes a constraint interpreter. |
| List accepted terms | `FTA.terms`, `Enumeration.terms`, `Enumeration.plainTerms` | Every term, by depth. `terms` solves constraints and stops at recursion; the other two ignore constraints and give an infinite list for a recursive grammar. |
| Restrict to a pattern | `Template.restrictFTA`, `Template.restrict` | A grammar for the terms that match a `Template`. |
| List terms a check accepts | `FTA.termsUpToM` | The terms up to a depth, each checked once by a monadic predicate that sees its transition. |
| Bound tree depth | `FTA.boundDepth` | Another grammar, restricted to trees within the bound. |
| Intersect languages | `FTA.intersect`, `FTA.intersectWith`, `Common.intersect` | A grammar for the common trees. Annotations require the interpretation described below. |
| Inspect states, transitions, and cycles | `FTA.states`, `FTA.transitionsFrom`, `FTA.cyclicStates` | Graph structure, not accepted values. |
| Change symbols or annotations | `FTA.mapSymbols`, `FTA.annotate`, `FTA.mapConstraints`, `FTA.dropConstraints` | A transformed graph. Removing annotations does not solve constraints. |
| Build a shared or recursive grammar | `Common.Node`, `Common.Edge`, `Common.Mu` | An interned graph that reuses equal subgraphs. |
| Take a union of languages | `Common.union` | An interned grammar that accepts trees from any input. |
| Count graph nodes and edges | `Common.nodeCount`, `Common.edgeCount` | Graph size, not the number of accepted trees. |
| Convert between graph representations | `Common.toFTA`, `Common.fromFTA` | An explicit-state or interned graph. `fromFTA` requires an acyclic input. |
| Visualize a grammar | `FTA.toTree`, `Common.toTree` | A finite tree of typed state and transition labels. Map the labels to strings for `drawTree`. |

`FTA` and `Common` are the two representations in this package. `FTA` retains
explicit state names. `Common` uses interned nodes and edges to share structure.
Conversion between them does not produce the accepted values.

For example, `FTA.terms (FTA.boundDepth 3 grammar)` lists the values of a
bounded grammar. `microcfta-generator` compiles a grammar into replay ranks
for sampling; different accepting runs can produce the same value if the
grammar is ambiguous.

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

import qualified Data.CFTA as FTA
import Data.CFTA.Generic (HasFTA, datatypeDecode, datatypeFTA, deriveFTAWith, domain, encodeTerm)

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

Add `microcfta` to your component's `build-depends`. To try the example in this
checkout, save it as `Main.hs` at the workspace root and run:

```sh
cabal build microcfta
cabal exec -- runghc -package=microcfta Main.hs
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

`Int`, `Integer`, `Char`, and `Text` are atomic: they require explicit finite
domains. Combine domains with `(<>)`; for example,
`domain @Int [0, 1] <> domain @Char ['a', 'b']`. A missing domain produces
`Left (MissingDomain ...)`. Make another `Show` and `Read` type atomic with
`deriving via (Atomic Double) instance HasFTA Double`, or write an instance
with `describeType = atomic` and your own codecs.

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
import qualified Data.CFTA.Interned as Common

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
state for inspection or for the explicit-state operations.

`Common.Mu` describes recursive languages. Each recursive cycle must pass
through a constructor edge; `Mu id` is not supported. `Common.toFTA` rejects
an open recursive root.

## Use named states when you need them

The explicit-state interface is useful when a grammar comes from a file or
state names are part of your application:

```haskell
import qualified Data.Tree as Tree
import Data.CFTA (FTAError, PlainFTA, Transition (Transition), accepts, mkFTA)

naturals :: Either (FTAError Int String) (PlainFTA Int String)
naturals = mkFTA 0 [(0, [Transition "zero" [] (), Transition "successor" [0] ()])]

oneAccepted :: Either (FTAError Int String) Bool
oneAccepted = fmap (`accepts` Tree.Node "successor" [Tree.Node "zero" []]) naturals

-- Right True
```

An automaton checks symbol arities and child-state references at construction.
Cycles are valid. `PlainFTA` uses `()` for transition annotations.

`Data.CFTA.intersect` constructs reachable product states and pairs the
input annotations. Apply `dropConstraints` to the result of two plain FTAs before
calling `accepts`. Use `intersectWith` when you need a different annotation
combination. `dropConstraints` removes annotations; it does not solve constraints.

## Visualize a grammar

`FTA.toTree` returns a finite tree with typed labels:

```haskell
toTree ::
    (Ord state) =>
    FTA state symbol constraint ->
    Tree (Either (StateView state) (Transition state symbol constraint))
```

`Left` contains a state definition or reference. `Right` contains the original
transition, including its symbol, children, and annotation. Use `fmap` to choose
the strings for `drawTree`. For the recursive `naturals` grammar above:

```haskell
import Data.List (intercalate)
import Data.Tree (drawTree)
import qualified Data.CFTA as FTA

-- | Show state names, reference markers, and occurrence locations.
renderNode :: FTA.StateView Int -> String
renderNode view = prefix ++ "q" ++ show (FTA.viewNode view) ++ " @" ++ renderPath (FTA.viewPath view)
  where
    prefix = case view of
        FTA.Expanded{} -> ""
        FTA.Recursive{} -> "mu "
        FTA.Shared{} -> "ref "

-- | Render zero-based alternative and child indexes from the root.
renderPath :: FTA.ViewPath -> String
renderPath [] = "root"
renderPath steps = intercalate "/" [show alternative ++ ":" ++ show child | (alternative, child) <- steps]

-- | Draw the natural-number grammar with plain constructor labels.
drawNaturals :: IO ()
drawNaturals = do
    grammar <- either (fail . show) pure naturals
    putStr $ drawTree $ fmap (either renderNode FTA.transitionSymbol) $ FTA.toTree grammar
```

```text
q0 @root
|
+- zero
|
`- successor
   |
   `- mu q0 @1:0
```

Each expanded state contains its transition alternatives. `Recursive` refers
to a state on the current path. `Shared` refers to a state expanded earlier.
Each state is expanded once. The example displays these references as
`mu` and `ref`, and omits the plain grammar's `()` annotation. These display
choices belong to the caller; `toTree` retains the original labels.

`viewNode` contains the original state. `viewPath :: ViewPath` locates this
occurrence in the finite graph view. `ViewPath` is `[(Int, Int)]`; each pair
selects a zero-based transition alternative and then its zero-based child.
The root is `[]`, displayed as `@root`. For example, `@0:1/2:0` follows child 1
of alternative 0, then child 0 of alternative 2. Recursive and shared references
have their own occurrence paths but retain the state of their definition.

This is a graph-view location, not a persistent state identity or a child-only
equality path. `map snd` extracts the child-only route for one occurrence. The
finite view does not list every route through a shared or recursive graph.
Paths are built when `toTree` is requested; normal generation does not build
them.

`Common.toTree` provides the same view for interned graphs. Its state labels
contain `Common.Node symbol constraint`; its transition labels contain
`Common.Edge symbol constraint`. It returns `Either (Common.FTAViewError symbol)`
around the tree because it rejects an open recursive root. It traverses the
graph directly and does not validate symbol arities. Neither view enumerates
the accepted values. Add `containers` to your component's `build-depends` when
you import `Data.Tree` directly.

## Equality constraints

The main entry point is `Data.CFTA.Equality`.

```haskell
import Data.CFTA.Equality
import qualified Data.Tree as Tree
```

An equality-constrained automaton is a `Node symbol EqConstraints`, which is a
set of outgoing `Edge symbol EqConstraints`s. An edge
has a symbol, child nodes, and optional equality constraints over paths into
those children. `Symbol` is the supplied interned text alphabet; its `IsString`
instance keeps the usual `OverloadedStrings` syntax. The `Node`, `Edge`, and
`Mu` patterns are the ones every theory shares; a signature such as
`Node Symbol EqConstraints` fixes the theory.

```haskell
intType :: Node Symbol EqConstraints
intType = Node [Edge "Int" []]

maybeIntType :: Node Symbol EqConstraints
maybeIntType = Node [Edge "Maybe" [intType]]

sameChildren :: Edge Symbol EqConstraints
sameChildren =
  mkEdge
    "Pair"
    [intType, intType]
    (mkEqConstraints [[path [0], path [1]]])
```

The alphabet can instead be an ordinary datatype. Edge construction needs
`Hashable` and `Typeable` for type-safe hash-consing; building a node from
existing edges needs only `Typeable`, and inspecting an existing node needs
neither. Operations that rebuild edges, such as intersection and reduction,
therefore carry both constraints. `termsWith` takes the value to use when
recursion is truncated, so the datatype does not need an `IsString` instance:

```haskell
import Data.Hashable (Hashable)
import GHC.Generics (Generic)

data NatSymbol = Zero | Succ | Recursion
  deriving (Eq, Generic, Show)

instance Hashable NatSymbol

zeroOrOne :: Node NatSymbol EqConstraints
zeroOrOne = Node [Edge Zero [], Edge Succ [Node [Edge Zero []]]]

terms :: [Tree.Tree NatSymbol]
terms = termsWith Recursion zeroOrOne
```

Useful operations:

- `union` combines alternatives.
- `intersect` keeps terms accepted by both automata.
- `reducePartially` propagates equality constraints and removes the
  alternatives those constraints locally rule out. It does not decide
  emptiness: a fully reduced automaton can still accept nothing.
- `withoutRedundantEdges` removes alternatives implied by other alternatives.
- `nodeRepresents` checks concrete term membership.
- `matchesTemplate` checks a concrete term against an explicit `Template`.
- `termsMatching` restricts a node to the accepted terms matching a template,
  while preserving its equality constraints.
- `terms` and `termsPrune` enumerate accepted terms. Both stop at
  an unconstrained `Mu`, which appears as the marker term `Mu`; unfold with
  `unfoldBounded` first to see past the recursion.

Enumeration lists accepting *runs*, not distinct terms. An ambiguous node --
two edges that accept a common term -- yields that term once per edge, so run
`withoutRedundantEdges` first or deduplicate the result if you need each term
once. And a constraint whose paths descend into a truncated `Mu` is dropped
rather than checked, so a term containing the `Mu` marker is not evidence that
the language below it is non-empty.

Templates do not overload ordinary symbols. `Hole` matches a complete
subtree, `TemplateNode` and `AnyNode` require exact arity, and
`TemplatePrefix` and `AnyPrefix` constrain only the leading children:

```haskell
unaryF = TemplateNode "f" [Hole] :: Template Symbol
anyF = TemplatePrefix "f" [] :: Template Symbol
```

### Visualize an equality automaton

`toTree` retains the original nodes and edges in typed labels:

```haskell
toTree ::
    (Hashable symbol, Typeable symbol) =>
    Node symbol EqConstraints ->
    Either (FTAViewError symbol)
        (Tree (Either (StateView (Node symbol EqConstraints)) (Edge symbol EqConstraints)))
```

`Left` contains an expanded node or a recursive or shared reference. `Right`
contains an original edge, including its equality constraints. Map the labels
to strings with `fmap (either renderNode renderEdge)` before using `drawTree`.
The renderer can choose domain names because node labels retain the nodes:

```haskell
module Main (main) where

import Data.List (intercalate)
import Data.Tree (drawTree)

import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Equality (EqConstraints, mkEqConstraints, path, subsumptionOrderedEclasses, unPath, unPathEClass)

-- | The one literal state in this example.
leaf :: ECTA.Node String EqConstraints
leaf = ECTA.Node [ECTA.Edge "Int" []]

-- | Equal pairs and recursive wrappers share the same expression state.
graph :: ECTA.Node String EqConstraints
graph = ECTA.createMu $ \self ->
    ECTA.Node
        [ ECTA.mkEdge "Pair" [leaf, leaf] (mkEqConstraints [[path [0], path [1]]])
        , ECTA.Edge "Again" [self]
        ]

-- | Use application-specific names for the original nodes.
renderNode :: ECTA.StateView (ECTA.Node String EqConstraints) -> String
renderNode view = case fmap (\node -> name node <> " @" <> renderViewPath (ECTA.viewPath view)) view of
    ECTA.Expanded _ label -> label
    ECTA.Recursive _ label -> "mu " <> label
    ECTA.Shared _ label -> "ref " <> label
  where
    name node
        | node == leaf = "literal"
        | otherwise = "expression"

-- | Identify the alternative and child at each step from the view root.
renderViewPath :: ECTA.ViewPath -> String
renderViewPath [] = "root"
renderViewPath steps = intercalate "/" [show alternative <> ":" <> show child | (alternative, child) <- steps]

-- | Keep equality paths while omitting empty constraints.
renderEdge :: ECTA.Edge String EqConstraints -> String
renderEdge edge = ECTA.edgeSymbol edge <> constraints
  where
    constraints = case subsumptionOrderedEclasses $ ECTA.edgeConstraint edge of
        Nothing -> " [false]"
        Just [] -> ""
        Just classes -> " [" <> intercalate ", " (map renderClass classes) <> "]"
    renderClass = intercalate " = " . map renderPath . unPathEClass
    renderPath target = case unPath target of
        [] -> "root"
        indexes -> intercalate "." $ map show indexes

-- | Choose labels after constructing the typed graph view.
main :: IO ()
main = do
    tree <- either (fail . show) pure $ ECTA.toTree graph
    putStr $ drawTree $ fmap (either renderNode renderEdge) tree
```

This program prints:

```text
expression @root
|
+- Pair [0 = 1]
|  |
|  +- literal @0:0
|  |  |
|  |  `- Int
|  |
|  `- ref literal @0:1
|
`- Again
   |
   `- mu expression @1:0
```

`Expanded`, `Recursive`, and `Shared` identify node definitions and references.
The example chooses the names `expression` and `literal`, and prints equality
paths instead of their internal trie representation. The renderer preserves
contradictions as `[false]` and omits only empty equality constraints.

`viewNode` retains the original node. `viewPath :: ViewPath` locates each
occurrence, including recursive and shared references. `ViewPath` is
`[(Int, Int)]`; each pair selects a zero-based edge alternative and then its
zero-based child. The root is `[]`, displayed as `@root`. For example,
`@0:1/2:0` follows child 1 of alternative 0, then child 0 of alternative 2.
References have their own occurrence paths and retain the node of their
definition.

These paths locate occurrences in one graph view. They are not persistent
node identities or the child-only `Path` used by equality constraints.
`map snd` extracts the child-only route for one occurrence. The finite view
does not list every route through a shared or recursive graph. Paths are built
only when `toTree` is requested; normal generation does not build them.

The view traverses the interned graph directly. Unlike `toFTA`, it does not
require a ranked alphabet. An open recursive variable returns `Left OpenNode`.
It does not enumerate terms or solve constraints. Add `containers` to your
component's `build-depends` when you import `Data.Tree` directly.

For the actual typed-expression generator, see
[`DrawTypedExpressions.hs`](../microcfta-generator/examples/DrawTypedExpressions.hs).
Run `cabal run cfta-draw-typed-expressions` from the workspace root. It draws
finite and recursive diagnostic graphs with local state names, occurrence
locations, source names, function signatures, and type-group witnesses.
The generator retains these names through `namedElements` and `nameGroups`.
`Gen.inspect` returns this diagnostic graph; `Gen.support` retains the original
semantic support. Each diagnostic symbol also retains its original symbol.
See [generator inspection](../microcfta-generator/README.md#inspect-a-generator)
for the API and its limits. The [ASCII reading guide](../microcfta-generator/README.md#read-the-ascii-tree)
walks through `@1:0/0:1`, shared references, and equality paths.

### Pruning API

`termsPrune` lets a caller drop branches of the enumeration before they
are explored. It calls an oracle twice around every UVar it expands, passing
the caller's own state, the UVar, and either:

- `Right node`, before that ECTA node is expanded
- `Left fragment`, after a `TermFragment` has been produced

A bare unconstrained `Mu` stops enumeration without being expanded and
therefore produces neither callback.

Return `True` to discard the current nondeterministic branch, or `False` to
keep enumerating with updated state.

What makes a term worth rejecting is entirely the caller's business.
The library supplies the callbacks, `expandPartialTermFrag` to read a partial
term, and no opinion about which shapes matter. Its `PartialSymbol` alphabet
keeps concrete symbols, unexpanded `UVarHole`s, and `TruncatedRecursion`
distinct; no placeholder can collide with a real symbol. `Tree.Tree` is a functor,
so a caller that deliberately wants one concrete alphabet can materialize a
partial term with `fmap resolvePartial`.

```haskell
-- Drop any branch whose partial term already contains a forbidden symbol.
prunedTerms :: [Symbol] -> Node Symbol EqConstraints -> [Tree.Tree Symbol]
prunedTerms forbidden =
  termsPrune () $ \() _ event ->
    case event of
      Right _ -> pure (False, ())
      Left fragment -> do
        partial <- expandPartialTermFrag fragment
        pure (any (`occursIn` partial) forbidden, ())
  where
    occursIn s (Tree.Node (ConcreteSymbol s') ts) =
      s == s' || any (occursIn s) ts
    occursIn s (Tree.Node _ ts) = any (occursIn s) ts
```

A `Right node` decision covers a whole UVar, so it removes every term under
that hole at once. The fact that `termsMatching template node` is non-empty
only proves that some terms match; it does not justify dropping the whole
node. Use `Left fragment` when the choice has to be made per branch.

The oracle's state is threaded down each nondeterministic branch separately,
which is what makes deferred checks work. When a check cannot be settled
because the fragment still holds an unexpanded hole, park it in that state
under the hole's `getUVarRepresentative` and settle it when the oracle is
called with `Left fragment` for that UVar — which is guaranteed to happen
before the branch completes.

`termsPruneWith` takes the truncated-recursion symbol explicitly, as
`termsWith` does, so an alphabet without an `IsString` instance can prune
too. It also adds a say in which hole is expanded next, so a parked check can
be settled before the branch it will kill is enumerated:

```haskell
-- Expand a hole some parked check is waiting on, if one is available.
resolveParkedFirst :: ExpansionOrder (IntMap [Tree.Tree Symbol])
resolveParkedFirst parked candidates =
  listToMaybe [uv | uv <- candidates, uvarToInt uv `IntMap.member` parked]

-- The recursion symbol comes first, so a datatype alphabet can prune too.
prunedNats oracle =
  termsPruneWith Recursion IntMap.empty resolveParkedFirst oracle
```

This steers order only. It cannot make a hole expandable early, and a UVar
that is not among the candidates is ignored. For an oracle whose rejections
are monotone — once a branch can be rejected it stays rejectable — it changes
how much work is done, not which terms come out.

A partial term reports an unexpanded hole as `UVarHole` and a recursive node
enumeration has finished with as `TruncatedRecursion`. A recursive node whose
equality constraints are still pending is a hole, not truncated recursion,
because it may still be expanded.

For repeated reduction, downstream code usually wants:

```haskell
reduceFully :: Node Symbol EqConstraints -> Node Symbol EqConstraints
reduceFully = fixUnbounded (withoutRedundantEdges . reducePartially)
```

The test and benchmark support module `Data.CFTA.TermSearch.TermSearch`
defines that helper.

## Refinements

`Data.CFTA.Refinement` is the liquid tree automata layer over `Data.CFTA`.
It uses the equality layer for cached positive equalities and the optional
lowering to an equality automaton.
Concrete annotated terms use `Data.Tree.Tree LiquidSymbol`. Construct a node
with `Tree.Node (LiquidSymbol symbol refinement) children`. The label retains
strict symbol and refinement fields. The tree label and child list use the
standard lazy `Data.Tree` representation. `eraseRefinements` maps each label
to its constructor symbol.

A transition has a ranked constructor, its Liquid Fixpoint refinement, child
states, and the paper's Boolean constraint language. Syntactic `Same` and semantic `Entails`
are LTA atoms. Guards support substitution, negation, conjunction, and disjunction.
Refinement implication is discharged through the small `Entailment`
boundary; `Data.CFTA.Refinement.LiquidFixpoint.withZ3` supplies the reusable
Z3 implementation.

`LiquidConstraint` implements the common engine's pure `Constraint` interface.
You can construct `Data.CFTA.Interned.Node LiquidSymbol LiquidConstraint`
with the same interned nodes and edges used by FTA and ECTA. `fromInterned`
retains its refinements and guards, assigns explicit state names, and runs the
normal LTA validation. It rejects open graphs and guards that inspect recursive
states. Construction does not call the solver. LTA recognition, pruning, and
semantic intersection remain operations of this layer.

Position substitutions apply simultaneously within each scope and avoid bound
variable capture in refinement expressions. Actual refinements remain facts
about the surrounding environment. A substitution does not rename those facts.
Equal complete actual terms share one value identity for semantic entailment.
Different actual terms with the same constructor name receive fresh solver
values with the sort declared for that name.

Bare `Same` compares the original annotated subtrees, as in ECTA. Inside a
`Substitute` scope it compares renamed views of those trees. Each scope replaces
formal constructor symbols and free names in refinement annotations with the
corresponding actual symbols. The first non-identity mapping for a repeated
formal name takes precedence. Nested scopes apply from inner to outer. Tree
shape and generated output terms stay unchanged; substitution does not splice
an actual subtree into a formal leaf. This is the library's specified
interpretation of the paper's general substitution syntax.

For equally refined leaves `x` and `y`, `Same(left,right)` rejects `pair(x,y)`.
The guard `[x/y].Same(left,right)` accepts it because both compared views contain
`x`. Refinement annotations still participate in exact syntactic comparison.
Use `withActualFor` or `withActualsFor` to scope the complete constraint,
including any cached positive equalities. Scoped equality remains an LTA guard;
it cannot be lowered directly to ordinary ECTA path equality.

`Entailment decide` retains the simple query interface. A query that needs fresh
declarations returns `Unknown` through that interface. `entailmentWithBindings`
accepts a callback that receives `(freshName, declaredName)` pairs. The Z3 adapter
declares each fresh value with the sort of `declaredName`. Generator query caches
include these bindings.

The complete pair `(constructor, refinement)` is one ranked-alphabet symbol,
not metadata outside the automaton. This can represent the paper literally: in
Figure 12 each formula is a nullary symbol such as
`LiquidSymbol "predicate" phi`, and the `f` transition relates its two formula
children. The generator DSL also offers a compressed convention in which a
program constructor carries its result refinement directly. That convention is
a surface encoding, not the definition of LTA.

`mkAutomatonWithFinals` accepts the paper's arbitrary final-state set, including
the empty set. It normalizes multiple final states to one fresh state whose row
is the union of the original final rows. An empty set becomes a fresh final
state with no transitions; a singleton needs no normalization. These cases
preserve Figure 6's denotation. The input state set can also be empty when the
final-state set is empty.

The literal Figure 12 shape is therefore ordinary Haskell data:

```haskell
figure12 =
  mkAutomaton qf
    [ (qf,
        [ Transition "f" true [qPredicate, qPredicate]
            (semanticConstraint (Entails (path [0]) (path [1])))
        ])
    , (qPredicate,
        [ Transition "predicate" phi1 [] unconstrainedConstraint
        , Transition "predicate" phi2 [] unconstrainedConstraint
        , Transition "predicate" phi3 [] unconstrainedConstraint
        ])
    ]
```

Here the three `(predicate, phi)` pairs are three distinct nullary alphabet
symbols. They are not a Haskell pool hidden behind `relate`.

Handwritten FTAs and LTAs deliberately have the same shape:

```haskell
import Data.CFTA.Refinement.Guard (requires, unconstrained)
import Data.CFTA.Refinement.Expression ((.>=.))
import qualified Data.CFTA.Refinement.Syntax as LTA

numbers =
  LTA.automaton expression
    [ LTA.row expression
        [ LTA.transition "sqrt" nonNegative [number]
            (\argument -> argument `requires` nonNegative)
        ]
    , LTA.row number
        [LTA.transition "zero" nonNegative [] unconstrained]
    ]
  where
    nonNegative = value .>=. 0
```

The lambda receives symbolic child positions in transition order. Useful guard
phrases are:

- ``candidate `requires` predicate`` for an ordinary precondition;
- ``actual `isSubtypeOf` expected`` for semantic subtyping;
- ``actual `isSameTermAs` expected`` for ECTA-style structural equality;
- `withActualFor actual formal guard` for dependent result types; the actual
  symbol is assumed to satisfy the refinement carried by its whole subtree;
- `allOf`, `anyOf`, and `notGuard` for Boolean composition, including `Same`.

`Satisfies position predicate` is a conservative convenience extension for the
common paper pattern `position Entails literalPredicate`. It avoids adding an
otherwise uninteresting predicate child to every surface DSL node; the literal
Figure 12 encoding can continue to use `Entails` between two tree positions.

Raw paths and guard constructors remain available for generated automata.
Named `Data.CFTA.Refinement.Syntax.transition` values retain construction errors until
`automaton` checks their rows. Wrap a raw `Data.CFTA.Refinement.Transition` in `Right` to
include it in a named-syntax row.

`denotationAtMost` is the small, materializing implementation of Figure 6. It
works for cyclic LTAs under an explicit tree-height bound and is the semantics
oracle against which optimized pruning and generation can be checked.

### Visualize a refined automaton

`toTree` converts the reachable graph to a finite tree with typed labels:

```haskell
toTree :: Automaton -> Tree (Either (StateView State) Transition)
```

`Left` contains a state definition or reference. `Right` contains the complete
transition, including its refinement and constraint. Map these labels to
strings before using `drawTree` from `containers`. This example defines its own
renderer and uses Liquid Fixpoint's `showpp` for refinement formulas:

```haskell
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.CFTA.Refinement
import Data.CFTA.Refinement.Expression (true, value, (.>=.))
import Data.List (intercalate)
import qualified Data.Text as Text
import Data.Tree (drawTree)
import Language.Fixpoint.Types (showpp)

-- | A square root whose argument must have a nonnegative refinement.
graph :: Either AutomatonError Automaton
graph =
    mkAutomaton
        (State 0)
        [
            ( State 0
            ,
                [ Transition
                    "sqrt"
                    true
                    [State 1]
                    (semanticConstraint (Satisfies (path [0]) nonNegative))
                ]
            )
        ,
            ( State 1
            , [Transition "zero" nonNegative [] unconstrainedConstraint]
            )
        ]
  where
    nonNegative = value .>=. (0 :: Int)

-- | Show state names, reference markers, and occurrence locations.
renderNode :: StateView State -> String
renderNode view = prefix ++ "q" ++ show (unState (viewNode view)) ++ " @" ++ renderPath (viewPath view)
  where
    prefix = case view of
        Expanded{} -> ""
        Recursive{} -> "mu "
        Shared{} -> "ref "

-- | Render zero-based alternative and child indexes from the root.
renderPath :: ViewPath -> String
renderPath [] = "root"
renderPath steps = intercalate "/" [show alternative ++ ":" ++ show child | (alternative, child) <- steps]

-- | Render symbols, nontrivial refinements, and complete constraints.
renderTransition :: Transition -> String
renderTransition transition =
    Text.unpack name ++ refinementLabel ++ guardLabel
  where
    Symbol name = transitionSymbol transition
    refinement = transitionRefinement transition
    refinementLabel
        | refinement == true = ""
        | otherwise = " {" ++ showpp refinement ++ "}"
    guardLabel = case constraintAsGuard (transitionConstraint transition) of
        Top -> ""
        Satisfies position predicate ->
            " [refinement("
                ++ intercalate "." (map show (unPath position))
                ++ ") entails "
                ++ showpp predicate
                ++ "]"
        guard -> " [" ++ show guard ++ "]"

-- | Draw the graph with the chosen state and transition labels.
main :: IO ()
main = do
    automaton <- either (fail . show) pure graph
    putStr $ drawTree $ fmap (either renderNode renderTransition) $ toTree automaton
```

Add `microcfta`, `containers`, `text`, and `liquid-fixpoint` to the component's
`build-depends`. To run the example in this checkout, save it as `Main.hs` at
the workspace root:

```sh
cabal build microcfta
cabal exec -- runghc -package=microcfta -package=liquid-fixpoint Main.hs
```

This program prints:

```text
q0 @root
|
`- sqrt [refinement(0) entails v >= 0]
   |
   `- q1 @0:0
      |
      `- zero {v >= 0}
```

`renderNode` and `renderTransition` are caller code. Change them to use domain
names or a different constraint notation. The example omits only `true`
refinements and `Top` guards. `constraintAsGuard` recovers the complete
constraint, including cached equalities. Guards other than `Satisfies` use a
`Show` fallback, so the renderer retains every obligation.

`Recursive` ends a cycle; `Shared` refers to a state expanded earlier. The
example displays these as `mu qN` and `ref qN`. `viewNode` retains the original
state, while `viewPath` locates each occurrence, including references.
`ViewPath` is `[(Int, Int)]`; each pair selects a zero-based alternative and its
zero-based child. The root is `[]`, displayed as `@root`. `@0:1/2:0` follows
child 1 of alternative 0, then child 0 of alternative 2.

View paths are graph-view locations, not persistent state identities. They
include alternative indexes and differ from the child-only paths in guards
and equality constraints. `map snd` gives the child-only route for one
occurrence; the finite view does not list every route through a shared graph.
`toTree` builds these paths on demand. Normal generation does not build them.
This view does not enumerate terms or call a solver.

### Cycles and pruning

Cycles are legal. A guard may not inspect a position whose state participates
in a cycle, matching the paper's restriction that keeps solver obligations
finite. `semanticIntersection` exposes Equation 4 directly: it retains the
antecedent transition only when that refinement entails the consequent. It is
directional, not a symmetric logical meet.

`prune solver automaton` implements both rules behind the paper's pruning pass
and returns another LTA.
For `P-Syn-Eq`, it uses the ordinary `Data.CFTA.intersectWith` product to
narrow the first position to the structural language also admitted at the
second. For `P-Sem-Ent`, it partitions transition sets at the observed positions
by refinement; actual/formal positions are partitioned by both refinement and
value-naming symbol. It retains precisely the combinations whose entailment
succeeds, replaces that semantic guard with `Top`, and removes newly dead
transitions to a fixed point. Nested positions produce shared state splits;
complete accepted terms are never constructed.

Pruning preserves missing observations until it evaluates the complete Boolean
guard. A missing path in an optional branch does not discard a candidate.
Semantic guards that need equality of complete compound actuals can remain on
the LTA: sparse root observations cannot always determine whether two actuals
share a value. In that case pruning retains the original transition and guard.
`accepts` and `denotationAtMost` continue to evaluate the complete terms.

`lowerToEqualityAutomaton` is a separate optimization. After `prune`, it
lowers residual `Top`, positive `Same`, and conjunctions of those atoms to
`EqConstraints`. Product intersection can remove disjoint
choices, but equality between independently selected arbitrary subtrees is not
in general a regular tree language. A negated, disjunctive, or still-semantic
constraint remains an LTA and makes this optional lowering fail explicitly.

### Similarity and minimization

`similarity` and `minimize` are core automaton operations corresponding to the
paper's S-Trans/S-Eq and M-Trans/M-LTA rules. A `Subtyping` callback receives
the current LTA and compares the type sub-automata associated with two program
transitions. This supports source languages that represent an expression's type
as a distinguished child state, as the paper does:

```haskell
let sourceSubtyping = Subtyping $ \current left right ->
      compareTypeStates current left right
Right related <- similarity sourceSubtyping automaton
Right reduced <- pure $ minimize automaton related
```

`reduce solver sourceSubtyping automaton` runs the complete static reduction
phase in the paper's order: `prune`, `similarity`, then `minimize`.

For an encoding that stores the complete result-type refinement on the program
transition, `refinementSubtypingBy` supplies a compact adapter. Its
projection represents the non-liquid type shape and can exclude structural
transitions:

```haskell
let sourceSubtyping = refinementSubtypingBy solver $ \transition ->
      typeClass (transitionSymbol transition)
Right related <- similarity sourceSubtyping automaton
Right reduced <- pure $ minimize automaton related
```

`similarityPairs` exposes directed `(subtype, supertype)` pairs as
`TransitionId`s. A `Similarity` also retains the exact source automaton.
`minimize` returns `StaleSimilarity` if transition contents, states, or the
accepting state have changed, including when the relation is empty.

Minimization applies a finite schedule of the paper's M-Trans rule. It resolves
transitive representatives, then considers each selected original supertype
once in table order. Each step retains existing incoming transitions and adds
copies that replace the supertype's target state with the representative's
target state in the children. Repeated occurrences of that state change
together. Later steps can copy transitions added by earlier steps. The step
removes only the selected original supertype transition and deduplicates equal
transitions. Shared target rows retain unrelated alternatives. One target can
have multiple representatives, and final transitions can participate.

Equivalent types keep the first transition in table order. When incomparable
subtypes can replace one supertype, the first inferred dominator selects its
representative. The state set and normalized final state stay unchanged. This
schedule does not promise a globally minimal automaton or an unchanged term
language.

The complete batch falls back to the original automaton if proposed redirects
make a representative depend on its removed target, a representative loses all
finite structural derivations, the last finite structural final derivation is
lost, or a copied guard would inspect a cyclic state. Successful batches remove
transitions with structurally unproductive children. These checks use graph
productivity; they do not prove that arbitrary transition guards are satisfiable.

## Module guide

| Module | Use it for |
| --- | --- |
| `Data.CFTA.Generic` | Datatype derivation, finite domains, metadata, and typed codecs. |
| `Data.CFTA` | Checked explicit-state graphs, recognition, depth bounds, product intersection, and enumeration. |
| `Data.CFTA.Interned` | Shared nodes and edges, recursive languages, union, intersection, and views. |
| `Data.CFTA.Template` | Patterns with holes and prefixes, and restriction of a grammar to a pattern. |
| `Data.CFTA.Path` | Child-index paths, and reading, editing, and requiring positions in a graph. |
| `Data.CFTA.Symbol` | Interned text symbols that compare and hash by identity. |
| `Data.CFTA.Constraint` | Conjunction, the unconstrained value, and known contradictions. |
| `Data.CFTA.Equality` | Equality-constrained nodes and edges, reduction, membership, templates, and constrained enumeration. |
| `Data.CFTA.Constraint.Equality` | Equality constraints over paths and their tries. |
| `Data.CFTA.Enumeration` | Enumeration for every theory: `terms`, `runs`, the lazy `plainTerms`, and the pruning oracles. |
| `Data.CFTA.Equality.Operations` | Reduction, membership, and template restriction; exposed for lower-level callers. |
| `Data.CFTA.Refinement` | Liquid tree automata: refined transitions, guards, recognition, pruning, similarity, minimization, and the bounded denotation. |
| `Data.CFTA.Refinement.Guard`, `Data.CFTA.Refinement.Syntax` | Guard syntax over named child positions and handwritten transition rows. |
| `Data.CFTA.Refinement.Expression` | Small helpers over Liquid Fixpoint refinement expressions. |
| `Data.CFTA.Refinement.LiquidFixpoint` | The Z3-backed `Entailment`. |
| `Data.Tree` from `containers` | Concrete constructor trees. |

The interned engine has a symbol type and a constraint type. A `Constraint`
instance supplies conjunction and known contradictions; `nodeRepresentsWith`
takes the concrete-term interpreter. The three layers share the graph
implementation and differ only in how they interpret the constraint.

## Memory and cache lifetime

The explicit-state graphs in `Data.CFTA`, including the datatype tutorial
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

## Performance notes

The core still uses the original hash-consing, memoization, union-find,
recursive-node, and path/equality-constraint machinery. Those are the hard parts
of ECTA and are intentionally kept.

Building ECTAs is safe from any thread. The hash-consing and memoization
tables are immutable maps in `IORef`s: reads never block, and atomic updates
retain the winning interned value, so one structure keeps one identity however
many threads raced for it.

It was not always so. In `microecta` 0.1.0.0 the tables were mutable and unsynchronized,
and building one structurally identical node from several threads on four
capabilities produced two different identities in 16 runs out of 20 -- no
exception, no crash, just two values that are structurally equal and compare
unequal, after which `Eq`, `Ord`, `Set` membership, memoization and `intersect`
were all quietly wrong. That mattered most for a parallel test runner: `tasty`
runs independent tests concurrently by default when the test binary is linked
with `-threaded` and run with `+RTS -N`, and `hspec` does under `parallel`, so
a property could be run that way without anything in the user's code looking
concurrent. The same probe now reports no disagreement in 25 runs.

Recursive-node shapes are computed before entering the interning cache and
stored in the uninterned description. Hashing and equality reuse that shape,
while the candidate value remains lazy during the atomic update; forcing it
there could build and intern further nodes.

The replacement is not a novel design. The `intern` package, already a
dependency here for interned text, has kept its caches as immutable maps in
`IORef`s updated atomically for years. It also shards them 1024 ways
to cut write contention, which this does not yet do; if a workload ever turns
out to be write-bound across many threads, that is the next step.

### Memory

Those tables never evict. Retained memory is proportional to the number of
*distinct* nodes, edges and symbols the process has ever constructed, and to
the memoized operations run over them. It is not proportional to the amount of
work done: repeating operations on values that already exist retains nothing
further.

Measured on the maintainer machine, holding the shape of the work fixed and
scaling only the count:

| workload | 4k iterations | 16k | 64k |
| --- | --- | --- | --- |
| intersect + reduce over a fixed symbol set | 0.1 MB | 0.1 MB | 0.1 MB |
| building fresh nodes, no memoized operations | 1.9 MB | 6.2 MB | 27.2 MB |
| both: fresh nodes, intersect + reduce | 5.3 MB | 30.5 MB | 105.8 MB |

Those last two rows are roughly half again what the mutable tables of
`microecta` 0.1.0.0 retained, which is what the immutable maps cost: a HAMT node carries more
overhead per entry than a slot in a flat mutable table. It buys thread safety
and, on the core benchmark, less of everything else: 0.77s and 4,765 MB in
`microecta` 0.1.0.0 against 0.30s and 2,161 MB now. Holding the cache fixed and adding only
the stored shape accounts for 0.69s and 4,317 MB of that, so the swap away from
the mutable table is the larger half. The tables are read far more often than
written, and a pure lookup in a HAMT beats an IO-boxed probe into a cuckoo
table.

The first row is the case to aim for. The others grow without bound, and there
is no way to release them: a long-running process that keeps building
*distinct* ECTAs will grow until it runs out of memory. This is the trade
hash-consing makes -- it is what buys O(1) equality and the memoized graph
algorithms -- but it makes the interned API a poor fit for a long-lived service that
constructs unboundedly many unrelated automata. Batch work in a process that
exits, or keep the set of distinct nodes bounded.

#### Why there is no `clearCaches`

Two escape hatches were tried and rejected on measurement.

Emptying the memo tables while keeping the intern cache is *safe* -- every
memoized function here is pure, so dropping entries costs recomputation and
nothing else -- but it recovers almost nothing. Most of what those tables hold
is interned nodes, which the intern cache retains regardless, and the registry
needed to find the tables is itself unbounded. Clearing every 1000 iterations
of the third workload above moved live bytes by about 3%.

Emptying the intern cache is not safe at all. Identity comes from it: two
structurally equal nodes interned either side of a clear get different `Id`s
and compare unequal, silently. It would only be sound when no `Node`, `Edge` or
`Symbol` from before the clear is still reachable, which nothing can check.

The standard remedy for that retention is a cache that holds its entries
weakly, so unreferenced nodes are collected and their table entries go with
them. [Filliâtre and Conchon, *Type-Safe Modular Hash-Consing*
(2006)](https://usr.lmf.cnrs.fr/~jcf/publis/hash-consing2.pdf) build exactly
that on OCaml's weak arrays. In Haskell the mechanism is weak pointers and
finalisers, from [Peyton Jones, Marlow and Elliott, *Stretching the Storage
Manager: Weak Pointers and Stable Names in Haskell*, IFL
1999](https://doi.org/10.1007/10722298_3).

Haskell's one shipped attempt at a weak intern table was
[`intern`](https://hackage.haskell.org/package/intern) 0.6, and 0.8 reverted it
four days later: removing an entry from a finaliser races with a comparison
already in flight over that entry. No maintained Haskell library ships weak
hash-consing today. This package does not do it, and neither does the `intern`
package it depends on for symbols, whose cache is strong and monotonic. Moving
to weak caches is a design change rather than a patch, so it is not in this
release.

The old dense `PathTrie` representation compiled poorly at `-O2`, to the point of
exhausting small development machines. The package uses a sparse `PathTrie` with
a compact single-child fast path. In the current benchmark suite this preserves
the important runtime shape while letting the library and benchmark build at
`-O2` inside a 512M compiler heap. CI enforces that budget so a regression fails
there rather than in a downstream build; the cap is deliberately not baked into
the library's `ghc-options`, where it would cap GHC for everyone who depends on
this package.

### Limits

Measured by scaling one dimension at a time until it stopped being practical,
on the maintainer machine with a 20-second budget per point.

Two things have a ceiling worth knowing about.

**Enumerating an unfolded recursive automaton.** For a three-edge recursive
type, `terms (unfoldBounded k t)` gives 677 terms at `k = 5` in a
millisecond, 458,330 at `k = 6` in a second, and does not finish `k = 7` in
twenty. The language grows faster than exponentially in the unfolding depth, so
this is the shape of the problem rather than a defect: reach for
`countAtSize` and `unrank` from `microcfta-generator` when you want to work
with a large language without materializing it.

**Equality constraints whose paths nest.** Congruence saturation in
`mkEqConstraints` is quadratic per round and iterates to a fixpoint, so classes
that pair paths which are prefixes of one another cost several times more per
level added. Class completion itself is a small union-find; the congruence
step is the quadratic part.

The cost is in the nesting, not the count. A thousand independent classes over
depth-two paths -- the shape term search and `apply` actually produce -- take
0.04s, and both use depth two with a handful of classes. If you are building
constraints by hand and they nest more than about ten deep, that is the wall.

Everything else measured flat over the range tried: intersecting two recursive
types up to ten branches each, intersecting two 12,800-edge finite nodes,
2,560 disjoint constraint classes, reducing a 64-link constrained chain, and
counting or unranking a bounded recursive generator.

Run the core benchmark suite with:

```sh
cabal bench microcfta:micro-bench --enable-optimization=2 --benchmark-options='1 +RTS -s -M512M -RTS'
```

The benchmark harness is deliberately dependency-light and prints CSV:

```text
benchmark,cpu_seconds,repeats,checksum
```

The suite covers the current high-risk core paths:

- path lookup in term-search-shaped nodes
- equality-constraint construction and descent
- finite and recursive intersection
- recursive-path reduction
- filtered term-search reduction and enumeration

The current optimized local snapshot, using GHC 9.12.2, multiplier `1`, and
`+RTS -s -M512M -RTS`, is about 2.16 GB allocated, 4.34 MB maximum residency,
and roughly 0.30s elapsed on the maintainer machine. Treat that as a
regression guard, not a portable absolute number.

Use a larger first argument for longer runs:

```sh
cabal bench microcfta:micro-bench --enable-optimization=2 --benchmark-options='3 +RTS -s -M512M -RTS'
```

## Dependencies

The library depends on `array`, `base`, `containers`, `hashable`, `intern`,
`liquid-fixpoint`, `mtl`, `text`, `transformers`, and `unordered-containers`. Only the refinement layer needs a solver: put `z3` on
`PATH` before using `Data.CFTA.Refinement.LiquidFixpoint`. `liquid-fixpoint`
is a heavy build dependency; it is included so that the three layers live in
one package.

## Development

Build and test from the workspace root. The test suite needs `z3` on `PATH`;
enter `nix-shell` to get it:

```sh
cabal build microcfta
cabal test microcfta:unit-tests
```

`-j1` keeps an optimized build of the core inside a small machine's memory.
To reproduce the compile-time memory budget CI enforces:

```sh
cabal build lib:microcfta --enable-optimization=2 \
  --ghc-options='+RTS -K512M -M512M -RTS'
```

The examples in `Data.CFTA.Equality` are executable. Run them with
[`doctest`](https://hackage.haskell.org/package/doctest):

```sh
cabal install doctest
cabal repl --with-repl=doctest lib:microcfta
```
