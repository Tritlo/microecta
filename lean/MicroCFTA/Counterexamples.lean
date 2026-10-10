import MicroCFTA.Language

/-!
# A similarity reduction that removes every guarded solution

The Haskell reproduction is `repro/Counterexamples.hs`. It uses `a` and `b`
with the same refinement type and a parent with a negative equality guard.
The minimizer replaces `b` by `a`. The resulting parent still has a finite
structural derivation, but it has no accepting derivation.

This module proves the before and after languages directly. It does not
encode the complete Haskell minimizer or its choice of representatives.
-/

namespace MicroCFTA.Counterexamples
open MicroCFTA.Language

/-- The states in the concrete counterexample. -/
inductive State where
  | root | left | right
  deriving DecidableEq

/-- The ranked alphabet in the concrete counterexample. -/
inductive Symbol where
  | f | a | b
  deriving DecidableEq

/-- The guard requires the two children to be different annotated terms. -/
def differentChildren (term : Term Symbol) : Bool :=
  !pathEquality [0] [1] term

/-- A leaf transition. -/
def leafEdge (symbol : Symbol) : Edge State Symbol :=
  ⟨symbol, [], fun _ => true⟩

/-- The parent transition with a negative equality guard. -/
def parentEdge (second : State) : Edge State Symbol :=
  ⟨.f, [.left, second], differentChildren⟩

/-- Before reduction, the root has the accepted term `f(a,b)`. -/
def before : Automaton State Symbol
  | .root => [parentEdge .right]
  | .left => [leafEdge .a]
  | .right => [leafEdge .b]

/-- After replacing the right leaf by the left representative, the right is empty. -/
def after : Automaton State Symbol
  | .root => [parentEdge .left]
  | .left => [leafEdge .a]
  | .right => []

/-- The original accepted term. -/
def witness : Term Symbol := .node .f [.node .a [], .node .b []]

/-- The surviving structural term. Its guard fails. -/
def rejectedWitness : Term Symbol := .node .f [.node .a [], .node .a []]

/-- The original automaton accepts its witness. -/
theorem before_accepts_witness : Accepts before .root witness :=
  enumerate_sound before 2 (by
    simp [enumerate, before, products, witness, leafEdge, parentEdge,
      differentChildren, pathEquality, Term.atPath, termEq, forestEq])

/-- The left state can derive only its leaf. -/
theorem after_left_unique {t : Term Symbol} (accepted : Accepts after .left t) :
    t = .node .a [] := by
  cases accepted with
  | node edge ts member children guard =>
      have edgeEq : edge = leafEdge .a := by simpa [after] using member
      subst edge
      cases children
      rfl

/-- No finite term is accepted after the representative replacement. -/
theorem after_accepts_nothing (t : Term Symbol) : ¬Accepts after .root t := by
  intro accepted
  cases accepted with
  | node edge ts member children guard =>
      have edgeEq : edge = parentEdge .left := by simpa [after] using member
      subst edge
      cases children with
      | cons left rest =>
          cases rest with
          | cons right rest =>
              cases rest
              have hl := after_left_unique left
              have hr := after_left_unique right
              simp [parentEdge, differentChildren, pathEquality, Term.atPath, hl, hr, termEq, forestEq] at guard

/-- Ignore the guards, as the minimizer's productivity check does. -/
def structuralAfter : Automaton State Symbol := fun state =>
  (after state).map (fun edge => {edge with guard := fun _ => true})

/-- The reduced root passes the finite structural productivity condition. -/
theorem after_is_structurally_productive :
    Accepts structuralAfter .root rejectedWitness :=
  enumerate_sound structuralAfter 2 (by
    simp [enumerate, structuralAfter, after, products, rejectedWitness,
      leafEdge, parentEdge])

/-- Structural productivity does not preserve existence of an accepted term. -/
theorem similarity_guard_counterexample :
    (∃ t, Accepts before .root t) ∧
      (∃ t, Accepts structuralAfter .root t) ∧
      ¬(∃ t, Accepts after .root t) := by
  refine ⟨⟨witness, before_accepts_witness⟩,
    ⟨rejectedWitness, after_is_structurally_productive⟩, ?_⟩
  rintro ⟨t, accepted⟩
  exact after_accepts_nothing t accepted

end MicroCFTA.Counterexamples
