# Glossary

The words this repository uses for its domain, with the words of the sources
where they differ. Sources: the ECTA paper (Koppel et al., *Searching
Entangled Program Spaces*, ICFP 2022) and the `ecta` library; the LTA paper
(*Liquid Tree Automata*, arXiv:2605.13456); TATA (Comon et al., *Tree
Automata Techniques and Applications*); CLRS (union-find); Nijenhuis and
Wilf, and Feat (ranking).

## Terms and automata

- **Term**: a tree of symbols.
- **Arity**: the number of children of a symbol or a transition. All sources
  say arity.
- **Path**: the child indexes from the root of a term to one of its nodes.
  TATA and the LTA paper call this a *position* (`Pos(t)`, `t|p`, `i.j.k`);
  ECTA calls it a path. In this repository "position" never names a single
  number.
- **Child index**: one step of a path: the zero-based position of a child
  among the children of a term node or a transition. The LTA paper says
  *position index*.
- **Transition**: a rule `f(q1, ..., qn) -> q`. An **edge** is a transition
  of an interned automaton (the `ecta` library's `Edge`; the ECTA thesis says
  *hyperedge*). A **transition index** selects one transition of a state or
  node.
- **Node, state**: a node of an interned automaton is a state; ECTA uses both
  words for one thing.
- **Node identity, edge identity, symbol identity**: the identity that
  interning gives a node, an edge, or a symbol. The three are different
  types; the `ecta` library has one `Id` for all three.
- **View, view path, view step**: a tree view unfolds a graph; a view path
  locates one occurrence in it; each step is a transition index, then a
  child index.
- **Depth**: the longest root-to-leaf path of a term, in edges; a leaf has
  depth 0. TATA's *height* counts a constant as 1, so height = depth + 1.
  **Mu depth** is the nesting depth of `Mu` binders, a different quantity.

## Constraints

- **Equality class**: a set of paths that must hold equal subterms (ECTA:
  *path equivalence class*, PEC; type `PathEClass`).
- **Equality constraints**: the equality classes of a transition (ECTA:
  *path constraint set*, PCS; type `EqConstraints`).
- **Guard**: the formula on a transition: equal terms at two paths,
  refinements that a path satisfies or entails, formulas over the terms at
  paths, substitutions, and Boolean connectives. The LTA paper calls this the
  transition's *constraint* `ψ`.
- **Constraint**: the whole label of a transition: equality constraints and
  a guard.
- **Contract**: a guard about the children of a constructor, written as a
  function with one term for each child, in order.
- **Measure**: the integer of each term of a constructor, written as a term
  of the measures of its children (`measured`). The refinement of a constructed
  term is `v == measure`, so the contract of a parent reads it. Liquid Haskell
  says measure; the LTA paper calls a constructor's refinement its *result
  refinement*.
- **Observed**: what a guard can read at one path of a term: the symbol there
  and its **leafness** (leaf, inner, or mixed when some members of a group
  are leaves and some are not).
- **Similarity pair**: two transitions where the first (the **subtype**)
  refines the second (the **supertype**); the LTA paper writes `δi ≲ δj`.
  Minimization keeps the **representative** and removes the supertype.

## Ranking and sampling

- **Rank**: the zero-based index of a term or value in the enumeration
  order. **Unrank** is its inverse (Nijenhuis and Wilf). Not the CLRS rank
  of a union-find tree.
- **Cardinality**: the number of members of a language (Feat).
- **Size**: the number of source choices of a generated member, or the
  number of nodes of an accepted term. A **size class** holds the members of
  one size.
- **Class rank**: the rank of a member inside its size class. A **sized
  rank** is a size with a class rank.
- **Rank offset**: the first rank of a group of members in a larger
  language.
- **Weight**: a relative frequency weight of an alternative or a value
  (QuickCheck's word). Not the real-valued weight of a Boltzmann sampler.
- **Checked rank**: a rank of a term with whether the ranking checked every
  symbol of the term.
- **Occurrence**: the token of one recursion probe.

## Generators

- **Choice index**: the position of an alternative in a generator choice.
- **Component index**: which component of an n-way join.
- **Argument index**: the position of an argument of a join, a guard, or a
  contract.
- **Group index**: which matched key pair of a two-way join.
- **Key index**: the position of a key among the keys of a recursive family.

## Variables

Three kinds, never called only "variable":

- **Union-find variable** (`UVar`): a variable of the enumeration; each set
  has a **representative** and each other element a **parent** (CLRS).
- **Variable index** (`VarIndex`): the position of a variable in the
  variable list of one problem (the symbolic counter, the lattice counter,
  the open integer variables of a compiled group).
- **Recursion reference** (`RecNodeId`): the variable that a `Mu` binds.
