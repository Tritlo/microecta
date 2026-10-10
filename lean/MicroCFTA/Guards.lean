import Std

/-!
# Guard decisions and the obligations of semantic pruning

The verdict operations follow `Data.CFTA.Refinement.Verdict`. The guard model
uses binary connectives. A Haskell list connective is their fold with `yes` or
`no`. Atomic decisions are parameters. The proofs do not certify an SMT solver.

The pruning model states the exact observation and partition obligations. It
does not assert that the Haskell trie construction meets these obligations.
The last sections expose two semantic boundaries: refutation is stronger than
failure of entailment, and repeated paths must share a value in `Holds`.
-/

namespace MicroCFTA.Guards

/-- The result of a guard query. -/
inductive Verdict where
  | yes | no | unknown
  deriving DecidableEq, Repr

/-- Complement a verdict. Preserve an unknown result. -/
def negate : Verdict → Verdict
  | .yes => .no
  | .no => .yes
  | .unknown => .unknown

/-- Conjoin two verdicts. -/
def conjunction : Verdict → Verdict → Verdict
  | .no, _ | _, .no => .no
  | .unknown, _ | _, .unknown => .unknown
  | .yes, .yes => .yes

/-- Disjoin two verdicts. -/
def disjunction : Verdict → Verdict → Verdict
  | .yes, _ | _, .yes => .yes
  | .unknown, _ | _, .unknown => .unknown
  | .no, .no => .no

theorem negate_involution (v : Verdict) : negate (negate v) = v := by
  cases v <;> rfl

theorem conjunction_associative (a b c : Verdict) :
    conjunction (conjunction a b) c = conjunction a (conjunction b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem disjunction_associative (a b c : Verdict) :
    disjunction (disjunction a b) c = disjunction a (disjunction b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem conjunction_commutative (a b : Verdict) :
    conjunction a b = conjunction b a := by
  cases a <;> cases b <;> rfl

theorem conjunction_idempotent (a : Verdict) : conjunction a a = a := by
  cases a <;> rfl

theorem conjunction_yes (a : Verdict) : conjunction .yes a = a := by
  cases a <;> rfl

theorem verdict_de_morgan (a b : Verdict) :
    negate (conjunction a b) = disjunction (negate a) (negate b) := by
  cases a <;> cases b <;> rfl

/-- A decided verdict agrees with a proposition. Unknown imposes no condition. -/
def Supports : Verdict → Prop → Prop
  | .yes, p => p
  | .no, p => ¬p
  | .unknown, _ => True

theorem conjunction_supports {a b : Verdict} {p q : Prop}
    (ha : Supports a p) (hb : Supports b q) :
    Supports (conjunction a b) (p ∧ q) := by
  cases a <;> cases b <;> simp_all [Supports, conjunction]

theorem disjunction_supports {a b : Verdict} {p q : Prop}
    (ha : Supports a p) (hb : Supports b q) :
    Supports (disjunction a b) (p ∨ q) := by
  cases a <;> cases b <;> simp_all [Supports, disjunction]

/-- The Boolean structure of a guard. Atomic negation is handled by an oracle. -/
inductive Guard (Atom : Type) where
  | top | bottom
  | atom (value : Atom)
  | not (inner : Guard Atom)
  | and (left right : Guard Atom)
  | or (left right : Guard Atom)

/-- Push polarity through the Boolean structure, as in `evaluateWith`. -/
def evaluate (query : Atom → Bool → Verdict) : Bool → Guard Atom → Verdict
  | positive, .top => if positive then .yes else .no
  | positive, .bottom => if positive then .no else .yes
  | positive, .atom a => query a positive
  | positive, .not g => evaluate query (!positive) g
  | positive, .and g h =>
      if positive then conjunction (evaluate query true g) (evaluate query true h)
      else disjunction (evaluate query false g) (evaluate query false h)
  | positive, .or g h =>
      if positive then disjunction (evaluate query true g) (evaluate query true h)
      else conjunction (evaluate query false g) (evaluate query false h)

/-- The corresponding positive and negative evidence semantics. -/
def Semantics (atom : Atom → Bool → Prop) : Bool → Guard Atom → Prop
  | positive, .top => positive = true
  | positive, .bottom => positive = false
  | positive, .atom a => atom a positive
  | positive, .not g => Semantics atom (!positive) g
  | positive, .and g h =>
      if positive then Semantics atom true g ∧ Semantics atom true h
      else Semantics atom false g ∨ Semantics atom false h
  | positive, .or g h =>
      if positive then Semantics atom true g ∨ Semantics atom true h
      else Semantics atom false g ∧ Semantics atom false h

/-- Sound atomic decisions imply sound decisions for every Boolean guard. -/
theorem evaluate_supports (query : Atom → Bool → Verdict)
    (atom : Atom → Bool → Prop)
    (atomicSound : ∀ a p, Supports (query a p) (atom a p))
    (g : Guard Atom) (positive : Bool) :
    Supports (evaluate query positive g) (Semantics atom positive g) := by
  induction g generalizing positive with
  | top => cases positive <;> simp [evaluate, Semantics, Supports]
  | bottom => cases positive <;> simp [evaluate, Semantics, Supports]
  | atom a => exact atomicSound a positive
  | not g ih => exact ih (!positive)
  | and g h ihg ihh =>
      cases positive
      · exact disjunction_supports (ihg false) (ihh false)
      · exact conjunction_supports (ihg true) (ihh true)
  | or g h ihg ihh =>
      cases positive
      · exact conjunction_supports (ihg false) (ihh false)
      · exact disjunction_supports (ihg true) (ihh true)

/-- Equal atomic observations give equal decisions for an arbitrary guard. -/
theorem evaluate_ext (left right : Atom → Bool → Verdict)
    (same : ∀ a p, left a p = right a p) (g : Guard Atom) (p : Bool) :
    evaluate left p g = evaluate right p g := by
  induction g generalizing p with
  | top => rfl
  | bottom => rfl
  | atom a => exact same a p
  | not g ih => exact ih (!p)
  | and g h ihg ihh => simp only [evaluate, ihg, ihh]
  | or g h ihg ihh => simp only [evaluate, ihg, ihh]

theorem evaluate_double_negation (query : Atom → Bool → Verdict)
    (g : Guard Atom) (p : Bool) :
    evaluate query p (.not (.not g)) = evaluate query p g := by
  cases p <;> rfl

/-- Decide whether a guard contains an atom that must remain structural. -/
def containsStructural (structural : Atom → Bool) : Guard Atom → Bool
  | .top | .bottom => false
  | .atom a => structural a
  | .not g => containsStructural structural g
  | .and g h | .or g h =>
      containsStructural structural g || containsStructural structural h

/-- Separate semantic conjuncts from structural guards. Neutral tops remain. -/
def splitGuard (structural : Atom → Bool) : Guard Atom → Guard Atom × Guard Atom
  | .and g h =>
      if containsStructural structural (.and g h) then
        let left := splitGuard structural g
        let right := splitGuard structural h
        (.and left.1 right.1, .and left.2 right.2)
      else (.and g h, .top)
  | g => if containsStructural structural g then (.top, g) else (g, .top)

theorem conjunction_yes_right (a : Verdict) : conjunction a .yes = a := by
  cases a <;> rfl

/-- Reordering independent conjuncts preserves all three verdicts. -/
theorem conjunction_interchange (a b c d : Verdict) :
    conjunction (conjunction a b) (conjunction c d) =
      conjunction (conjunction a c) (conjunction b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- The semantic/residual split preserves the complete guard decision. -/
theorem splitGuard_preserves (structural : Atom → Bool)
    (query : Atom → Bool → Verdict) (g : Guard Atom) :
    conjunction (evaluate query true (splitGuard structural g).1)
      (evaluate query true (splitGuard structural g).2) = evaluate query true g := by
  induction g with
  | top => simp [splitGuard, containsStructural, evaluate, conjunction]
  | bottom => simp [splitGuard, containsStructural, evaluate, conjunction]
  | atom a =>
      cases h : structural a <;>
        simp [splitGuard, containsStructural, h, evaluate,
          conjunction_yes, conjunction_yes_right]
  | not g ih =>
      cases h : containsStructural structural g <;>
        simp [splitGuard, containsStructural, h, evaluate,
          conjunction_yes, conjunction_yes_right]
  | or g h ihg ihh =>
      cases hc : containsStructural structural (.or g h) <;>
        simp only [splitGuard, hc, Bool.false_eq_true, ↓reduceIte,
          evaluate, conjunction_yes, conjunction_yes_right]
  | and g h ihg ihh =>
      cases hc : containsStructural structural (.and g h)
      · simp only [splitGuard, hc, Bool.false_eq_true, ↓reduceIte,
          conjunction_yes_right, evaluate]
      · simp only [splitGuard, hc, ↓reduceIte, evaluate]
        rw [conjunction_interchange, ihg, ihh]

/-- A finite group contains all entries with one observation key. -/
def groupByKey [DecidableEq Key] (key : Term → Key) (entries : List Term)
    (wanted : Key) : List Term :=
  entries.filter (fun entry => decide (key entry = wanted))

theorem mem_groupByKey [DecidableEq Key] (key : Term → Key)
    (entries : List Term) (wanted : Key) (entry : Term) :
    entry ∈ groupByKey key entries wanted ↔ entry ∈ entries ∧ key entry = wanted := by
  simp [groupByKey]

/-- Key partitioning neither inserts nor removes terms. -/
theorem groupByKey_cover [DecidableEq Key] (key : Term → Key)
    (entries : List Term) (entry : Term) :
    (∃ wanted, entry ∈ groupByKey key entries wanted) ↔ entry ∈ entries := by
  constructor
  · rintro ⟨wanted, member⟩
    exact ((mem_groupByKey key entries wanted entry).mp member).1
  · intro member
    exact ⟨key entry, (mem_groupByKey key entries (key entry) entry).mpr ⟨member, rfl⟩⟩

/-- Distinct keys have disjoint groups. This is required to preserve mass. -/
theorem groupByKey_disjoint [DecidableEq Key] (key : Term → Key)
    (entries : List Term) {left right : Key} (different : left ≠ right)
    (entry : Term) :
    ¬(entry ∈ groupByKey key entries left ∧ entry ∈ groupByKey key entries right) := by
  rintro ⟨inLeft, inRight⟩
  have hl := ((mem_groupByKey key entries left entry).mp inLeft).2
  have hr := ((mem_groupByKey key entries right entry).mp inRight).2
  exact different (hl.symm.trans hr)

/-- The result of retaining, deleting, or retaining the original guard. -/
def AfterPrune (decision : Verdict) (semantic residual : Prop) : Prop :=
  match decision with
  | .yes => residual
  | .no => False
  | .unknown => semantic ∧ residual

/-- A sound decision can remove its guard without changing accepted terms. -/
theorem discharge_preserves (decision : Verdict) (semantic residual : Prop)
    (sound : Supports decision semantic) :
    AfterPrune decision semantic residual ↔ semantic ∧ residual := by
  cases decision <;> simp_all [Supports, AfterPrune]

/-- An observation key is sufficient if each atomic query depends only on it. -/
def Sufficient (key : Term → Key) (query : Term → Atom → Bool → Verdict) : Prop :=
  ∀ x y, key x = key y → ∀ a p, query x a p = query y a p

/-- Sufficient observation keys make every guard homogeneous within a group. -/
theorem grouping_homogeneous (key : Term → Key)
    (query : Term → Atom → Bool → Verdict) (sufficient : Sufficient key query)
    {x y : Term} (same : key x = key y) (g : Guard Atom) (p : Bool) :
    evaluate (query x) p g = evaluate (query y) p g :=
  evaluate_ext (query x) (query y) (sufficient x y same) g p

/-- The accepted language before a partition is discharged. -/
def BeforePartition (member : Group → Term → Prop) (semantic residual : Term → Prop)
    (t : Term) : Prop :=
  ∃ group, member group t ∧ semantic t ∧ residual t

/-- The accepted language after each group gets a decision. -/
def AfterPartition (member : Group → Term → Prop) (decision : Group → Verdict)
    (semantic residual : Term → Prop) (t : Term) : Prop :=
  ∃ group, member group t ∧ AfterPrune (decision group) (semantic t) (residual t)

/-- Discharge preserves a partition when each decision is sound for each member. -/
theorem partition_discharge_preserves
    (member : Group → Term → Prop) (decision : Group → Verdict)
    (semantic residual : Term → Prop)
    (sound : ∀ group t, member group t → Supports (decision group) (semantic t))
    (t : Term) :
    AfterPartition member decision semantic residual t ↔
      BeforePartition member semantic residual t := by
  constructor
  · rintro ⟨group, inside, accepted⟩
    exact ⟨group, inside, (discharge_preserves _ _ _ (sound group t inside)).mp accepted⟩
  · rintro ⟨group, inside, accepted⟩
    exact ⟨group, inside, (discharge_preserves _ _ _ (sound group t inside)).mpr accepted⟩

/-- Covering the original language is the completeness obligation for splitting. -/
theorem partition_cover_preserves
    (language : Term → Prop) (member : Group → Term → Prop)
    (semantic residual : Term → Prop)
    (cover : ∀ t, (∃ group, member group t) ↔ language t) (t : Term) :
    BeforePartition member semantic residual t ↔ language t ∧ semantic t ∧ residual t := by
  constructor
  · rintro ⟨group, inside, accepted⟩
    exact ⟨(cover t).mp ⟨group, inside⟩, accepted⟩
  · rintro ⟨inside, accepted⟩
    obtain ⟨group, memberOf⟩ := (cover t).mpr inside
    exact ⟨group, memberOf, accepted⟩

/-- Equal selected values remain equal after a uniform symbol substitution. -/
theorem substitution_preserves_equality (substitute : Value → Value')
    {left right : Value} (same : left = right) : substitute left = substitute right :=
  congrArg substitute same

/-- An injective substitution also reflects equality. -/
theorem substitution_reflects_equality (substitute : Value → Value')
    (injective : Function.Injective substitute) (left right : Value) :
    substitute left = substitute right ↔ left = right :=
  ⟨fun same => injective same, congrArg substitute⟩

/-- General name substitution can merge distinct symbols. -/
theorem noninjective_substitution_can_create_equality :
    (fun _ : Bool => false) false = (fun _ : Bool => false) true ∧
      (false : Bool) ≠ true := by decide

/-- Semantic implication over a refinement domain. -/
def Entails (refinement requirement : Value → Prop) : Prop :=
  ∀ value, refinement value → requirement value

/-- Formula refutation implies failure of entailment if the domain has a value. -/
theorem refutation_implies_not_entails
    (refinement requirement : Value → Prop)
    (inhabited : ∃ value, refinement value)
    (refutes : Entails refinement (fun value => ¬requirement value)) :
    ¬Entails refinement requirement := by
  intro proves
  obtain ⟨value, inside⟩ := inhabited
  exact refutes value inside (proves value inside)

/-- Failure of implication does not imply implication of the negated formula. -/
theorem refutation_is_stronger_than_failure :
    ¬Entails (fun _ : Bool => True) (fun value => value = true) ∧
    ¬Entails (fun _ : Bool => True) (fun value => value ≠ true) := by
  unfold Entails
  decide

/-- An inconsistent refinement proves both a formula and its negation. -/
theorem empty_refinement_proves_both (requirement : Value → Prop) :
    Entails (fun _ => False) requirement ∧
      Entails (fun _ => False) (fun value => ¬requirement value) := by
  constructor <;> intro value impossible <;> exact False.elim impossible

/-- A contract ranges over one value per path, even if a path is named twice. -/
def HoldsByPosition (targets : Index → Path) (refinement : Path → Value → Prop)
    (formula : (Index → Value) → Prop) : Prop :=
  ∀ values : Path → Value,
    (∀ index, refinement (targets index) (values (targets index))) →
      formula (fun index => values (targets index))

/-- The current complete evaluator ranges over one value per occurrence. -/
def HoldsIndependently (targets : Index → Path) (refinement : Path → Value → Prop)
    (formula : (Index → Value) → Prop) : Prop :=
  ∀ values : Index → Value,
    (∀ index, refinement (targets index) (values index)) → formula values

/-- Independent formals are conservative for positive contract proofs. -/
theorem independent_holds_sound (targets : Index → Path)
    (refinement : Path → Value → Prop) (formula : (Index → Value) → Prop)
    (proved : HoldsIndependently targets refinement formula) :
    HoldsByPosition targets refinement formula := by
  intro values inside
  exact proved (fun index => values (targets index)) inside

/-- This conservatism loses completeness when two occurrences name one path. -/
theorem holds_alias_counterexample :
    HoldsByPosition (fun _ : Bool => ()) (fun (_ : Unit) (_ : Bool) => True)
      (fun values => values false = values true) ∧
    ¬HoldsIndependently (fun _ : Bool => ()) (fun (_ : Unit) (_ : Bool) => True)
      (fun values => values false = values true) := by
  constructor
  · intro values _
    rfl
  · intro proved
    have impossible : (false : Bool) = true := proved id (fun _ => trivial)
    cases impossible

/-- Position lookup gives one value to repeated occurrences of the same path. -/
theorem repeated_path_reflexive (valueAt : Path → Value) (path : Path) :
    valueAt path = valueAt path := rfl

/-- Independent formals cannot prove the equality required by repeated paths. -/
theorem independent_formals_lose_alias_completeness :
    (∀ value : Bool, value = value) ∧ ¬(∀ left right : Bool, left = right) := by
  decide

/-- Adding the missing alias assumption makes the contract valid. -/
theorem aliased_formals_restore_completeness
    (refinement : Value → Prop) :
    ∀ left right, refinement left → refinement right → left = right → left = right := by
  intro left right _ _ alias
  exact alias

/-- Replacing one of two unequal leaves by the other destroys a negative guard. -/
theorem representative_replacement_can_destroy_all_guarded_terms :
    (∃ left right : Bool, left = false ∧ right = true ∧ left ≠ right) ∧
      ¬(∃ left right : Bool, left = false ∧ right = false ∧ left ≠ right) := by
  decide

/-- A representative language can preserve a solution while losing exact terms. -/
theorem representative_preservation_is_not_language_equality :
    (∃ x : Bool, x = false) ∧
      (∀ _x : Bool, True → ∃ y : Bool, y = false) ∧
      ¬(∀ x : Bool, True ↔ x = false) := by decide

end MicroCFTA.Guards
