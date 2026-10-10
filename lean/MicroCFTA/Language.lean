import Std

/-!
# Finite-term language of a constrained tree automaton

A state has a finite list of outgoing edges. Edges can refer to the same state,
so the graph can contain cycles. Each guard checks the complete term built by
its edge. This includes path equality and refinement guards when their concrete
interpretation is decidable.

`Accepts` is the least finite-run semantics. `enumerate` is an executable
bounded interpreter. The proofs below connect these independent definitions.
The Haskell counterparts are `Internal.Tree.termsUpToBy`,
`Refinement.Denotation.accepts`, and `Refinement.Denotation.denotationAtMost`.
This model does not encode the suspended UVar implementation. In particular,
`Enumeration.terms` truncates recursion and does not decide residual guards;
its output is not the concrete accepted language modeled here.
-/

namespace MicroCFTA.Language

/-- A finite ordered tree. The symbol has no imposed arity. -/
inductive Term (Symbol : Type) where
  | node : Symbol → List (Term Symbol) → Term Symbol

/-- Relate the entries of two lists at the same positions. -/
inductive All₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : All₂ R [] []
  | cons : R a b → All₂ R as bs → All₂ R (a :: as) (b :: bs)

/-- Replace a pointwise relation by a weaker relation. -/
theorem All₂.imp {α β : Type} {R S : α → β → Prop}
    (f : ∀ a b, R a b → S a b) {as bs} (h : All₂ R as bs) : All₂ S as bs := by
  induction h with
  | nil => exact .nil
  | cons h hs ih => exact .cons (f _ _ h) ih

/-- Pointwise related lists have the same length. -/
theorem All₂.length_eq {α β : Type} {R : α → β → Prop}
    {as bs} (h : All₂ R as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simpa using ih

/-- Split a relation on a zipped list when both input lists have the same length. -/
theorem all₂_zip_iff {α β γ : Type} (R : α → γ → Prop) (S : β → γ → Prop)
    (as : List α) (bs : List β) (cs : List γ) (hlen : as.length = bs.length) :
    All₂ (fun p c => R p.1 c ∧ S p.2 c) (as.zip bs) cs ↔
      All₂ R as cs ∧ All₂ S bs cs := by
  induction as generalizing bs cs with
  | nil =>
      have : bs = [] := List.length_eq_zero_iff.mp hlen.symm
      subst bs
      constructor
      · intro h
        cases h
        exact ⟨.nil, .nil⟩
      · rintro ⟨h, _⟩
        cases h
        exact .nil
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          have htail : as.length = bs.length := by simpa using hlen
          constructor
          · intro h
            cases h with
            | cons hc hcs =>
                have hs := (ih bs _ htail).mp hcs
                exact ⟨.cons hc.1 hs.1, .cons hc.2 hs.2⟩
          · rintro ⟨hr, hs⟩
            cases hr with
            | cons hc hcs =>
                cases hs with
                | cons hd hds =>
                    exact .cons ⟨hc, hd⟩ ((ih bs _ htail).mpr ⟨hcs, hds⟩)

/-- The number of symbol nodes on a longest root-to-leaf path. -/
def Term.height {Symbol : Type} : Term Symbol → Nat
  | .node _ ts => ts.foldr (fun t n => max t.height n) 0 + 1

/-- The greatest height in a child list, or zero for an empty list. -/
def forestHeight {Symbol : Type} (ts : List (Term Symbol)) : Nat :=
  ts.foldr (fun t n => max t.height n) 0

/-- A nonempty tree has positive height. -/
theorem Term.height_pos {Symbol : Type} (t : Term Symbol) : 0 < t.height := by
  cases t
  simp [Term.height]

/-- Split a relation with child height bounds into its two requirements. -/
theorem all₂_height_iff {State Symbol : Type} (R : State → Term Symbol → Prop)
    (qs : List State) (ts : List (Term Symbol)) (fuel : Nat) :
    All₂ (fun q t => R q t ∧ t.height ≤ fuel) qs ts ↔
      All₂ R qs ts ∧ forestHeight ts ≤ fuel := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨.nil, Nat.zero_le _⟩
    | cons ht hts ih =>
        exact ⟨.cons ht.1 ih.1, Nat.max_le.mpr ⟨ht.2, ih.2⟩⟩
  · rintro ⟨h, hheight⟩
    induction h with
    | nil => exact .nil
    | cons ht hts ih =>
        have hmax := Nat.max_le.mp hheight
        exact .cons ⟨ht, hmax.1⟩ (ih hmax.2)

/-- One transition, with its guard interpreted on the complete output term. -/
structure Edge (State Symbol : Type) where
  label : Symbol
  children : List State
  guard : Term Symbol → Bool

/-- A finite outgoing list for each state. States need not form an acyclic graph. -/
abbrev Automaton (State Symbol : Type) := State → List (Edge State Symbol)

/-- A finite accepting run. Every child accepts and the edge guard holds. -/
inductive Accepts {State Symbol : Type} (A : Automaton State Symbol) :
    State → Term Symbol → Prop where
  | node (e : Edge State Symbol) (ts : List (Term Symbol)) :
      e ∈ A q → All₂ (Accepts A) e.children ts →
      e.guard (.node e.label ts) = true → Accepts A q (.node e.label ts)

/-- Acceptance at a node exposes a matching transition and its child runs. -/
theorem accepts_node_iff {State Symbol : Type} (A : Automaton State Symbol)
    (q : State) (symbol : Symbol) (ts : List (Term Symbol)) :
    Accepts A q (.node symbol ts) ↔ ∃ e, e ∈ A q ∧ e.label = symbol ∧
      All₂ (Accepts A) e.children ts ∧ e.guard (.node symbol ts) = true := by
  constructor
  · intro h
    cases h with
    | node e ts he hts hg => exact ⟨e, he, rfl, hts, hg⟩
  · rintro ⟨e, he, hs, hts, hg⟩
    subst symbol
    exact .node e ts he hts hg

/-- All ordered choices of one value for each list entry. -/
def products {α β : Type} (choices : α → List β) : List α → List (List β)
  | [] => [[]]
  | a :: as => (choices a).flatMap fun b => (products choices as).map (b :: ·)

/-- Cartesian products contain exactly the pointwise choices. -/
theorem mem_products {α β : Type} (choices : α → List β) (as : List α)
    (bs : List β) :
    bs ∈ products choices as ↔ All₂ (fun a b => b ∈ choices a) as bs := by
  induction as generalizing bs with
  | nil =>
      constructor
      · intro h
        have : bs = [] := by simpa [products] using h
        subst bs
        exact .nil
      · intro h
        cases h
        simp [products]
  | cons a as ih =>
      constructor
      · intro h
        obtain ⟨b, hb, rest, hrest, hEq⟩ :=
          (by simpa [products, List.mem_flatMap, List.mem_map] using h :
            ∃ b, b ∈ choices a ∧ ∃ rest, rest ∈ products choices as ∧ b :: rest = bs)
        subst bs
        exact .cons hb ((ih rest).mp hrest)
      · intro h
        cases h with
        | cons hb hrest =>
            exact List.mem_flatMap.mpr ⟨_, hb,
              List.mem_map.mpr ⟨_, (ih _).mpr hrest, rfl⟩⟩

/-- Enumerate finite runs with at most `fuel` symbol nodes on each root-to-leaf path.
Zero fuel yields no terms. Thus a Haskell height bound `d` uses `d + 1` fuel.
Different accepting runs can produce repeated terms in this list. -/
def enumerate {State Symbol : Type} (A : Automaton State Symbol) :
    Nat → State → List (Term Symbol)
  | 0, _ => []
  | fuel + 1, q => (A q).flatMap fun e =>
      ((products (enumerate A fuel) e.children).map (Term.node e.label)).filter e.guard

/-- One bounded enumeration step chooses an edge and all its child terms. -/
theorem mem_enumerate_succ {State Symbol : Type} (A : Automaton State Symbol)
    (fuel : Nat) (q : State) (t : Term Symbol) :
    t ∈ enumerate A (fuel + 1) q ↔
      ∃ e, e ∈ A q ∧ ∃ ts,
        All₂ (fun s u => u ∈ enumerate A fuel s) e.children ts ∧
        t = .node e.label ts ∧ e.guard t = true := by
  constructor
  · intro h
    obtain ⟨e, he, heterm⟩ := List.mem_flatMap.mp h
    obtain ⟨hm, hg⟩ := List.mem_filter.mp heterm
    obtain ⟨ts, hts, ht⟩ := List.mem_map.mp hm
    exact ⟨e, he, ts, (mem_products _ _ _).mp hts, ht.symm, hg⟩
  · rintro ⟨e, he, ts, hts, rfl, hg⟩
    exact List.mem_flatMap.mpr ⟨e, he, List.mem_filter.mpr
      ⟨List.mem_map.mpr ⟨ts, (mem_products _ _ _).mpr hts, rfl⟩, hg⟩⟩

/-- Every enumerated term has a finite accepting run. -/
theorem enumerate_sound {State Symbol : Type} (A : Automaton State Symbol)
    (fuel : Nat) {q : State} {t : Term Symbol}
    (h : t ∈ enumerate A fuel q) : Accepts A q t := by
  induction fuel generalizing q t with
  | zero => simp [enumerate] at h
  | succ fuel ih =>
      obtain ⟨e, he, ts, hts, rfl, hg⟩ := (mem_enumerate_succ _ _ _ _).mp h
      exact .node e ts he (hts.imp fun _ _ hu => ih hu) hg

/-- Bounded enumeration is sound and complete at the exact height bound. -/
theorem mem_enumerate_iff {State Symbol : Type} (A : Automaton State Symbol)
    (fuel : Nat) (q : State) (t : Term Symbol) :
    t ∈ enumerate A fuel q ↔ Accepts A q t ∧ t.height ≤ fuel := by
  induction fuel generalizing q t with
  | zero =>
      constructor
      · simp [enumerate]
      · intro h
        have hp := t.height_pos
        omega
  | succ fuel ih =>
      constructor
      · intro h
        obtain ⟨e, he, ts, hts, rfl, hg⟩ := (mem_enumerate_succ _ _ _ _).mp h
        have hs := (all₂_height_iff (Accepts A) e.children ts fuel).mp
          (hts.imp fun q t ht => (ih q t).mp ht)
        refine ⟨.node e ts he hs.1 hg, ?_⟩
        simpa [Term.height, forestHeight] using Nat.succ_le_succ hs.2
      · rintro ⟨ha, hh⟩
        cases ha with
        | node e ts he hts hg =>
            have hb : forestHeight ts ≤ fuel := by
              simpa [Term.height, forestHeight] using hh
            have hs := (all₂_height_iff (Accepts A) e.children ts fuel).mpr ⟨hts, hb⟩
            exact (mem_enumerate_succ _ _ _ _).mpr
              ⟨e, he, ts, hs.imp (fun q t ht => (ih q t).mpr ht), rfl, hg⟩

/-- Increasing the fuel by one preserves every enumerated term. -/
theorem enumerate_step {State Symbol : Type} (A : Automaton State Symbol)
    (fuel : Nat) {q : State} {t : Term Symbol}
    (h : t ∈ enumerate A fuel q) : t ∈ enumerate A (fuel + 1) q := by
  induction fuel generalizing q t with
  | zero => simp [enumerate] at h
  | succ fuel ih =>
      obtain ⟨e, he, ts, hts, rfl, hg⟩ := (mem_enumerate_succ _ _ _ _).mp h
      exact (mem_enumerate_succ _ _ _ _).mpr
        ⟨e, he, ts, hts.imp (fun _ _ hu => ih hu), rfl, hg⟩

/-- Increasing the fuel preserves every enumerated term. -/
theorem enumerate_mono {State Symbol : Type} (A : Automaton State Symbol)
    {n m : Nat} (hle : n ≤ m) {q : State} {t : Term Symbol}
    (h : t ∈ enumerate A n q) : t ∈ enumerate A m q := by
  induction hle with
  | refl => exact h
  | step hle ih => exact enumerate_step A _ ih

/-- Every finite accepting run appears at some finite fuel, even on a cyclic graph. -/
theorem enumerate_complete {State Symbol : Type} (A : Automaton State Symbol)
    {q : State} {t : Term Symbol} (h : Accepts A q t) :
    ∃ fuel, t ∈ enumerate A fuel q := by
  induction h using Accepts.rec
    (motive_2 := fun qs ts _ => ∃ fuel,
      All₂ (fun q t => t ∈ enumerate A fuel q) qs ts) with
  | node e ts he hts hg ih =>
      obtain ⟨fuel, hchildren⟩ := ih
      exact ⟨fuel + 1, (mem_enumerate_succ _ _ _ _).mpr
        ⟨e, he, ts, hchildren, rfl, hg⟩⟩
  | nil => exact ⟨0, .nil⟩
  | @cons q t qs ts ht hts iht ihs =>
      obtain ⟨n, hn⟩ := iht
      obtain ⟨m, hm⟩ := ihs
      exact ⟨max n m, .cons
        (enumerate_mono A (Nat.le_max_left _ _) hn)
        (hm.imp fun _ _ hu => enumerate_mono A (Nat.le_max_right _ _) hu)⟩

/-- The union of the finite enumeration lists is exactly the accepted language. -/
theorem accepts_iff_eventually_enumerated {State Symbol : Type}
    (A : Automaton State Symbol) (q : State) (t : Term Symbol) :
    Accepts A q t ↔ ∃ fuel, t ∈ enumerate A fuel q := by
  constructor
  · exact enumerate_complete A
  · rintro ⟨fuel, h⟩
    exact enumerate_sound A fuel h

/-- Match two transitions by symbol and arity, then conjoin their guards. -/
def intersectEdge {Q R Symbol : Type} [DecidableEq Symbol]
    (e : Edge Q Symbol) (f : Edge R Symbol) : List (Edge (Q × R) Symbol) :=
  if e.label = f.label ∧ e.children.length = f.children.length then
    [⟨e.label, e.children.zip f.children, fun t => e.guard t && f.guard t⟩]
  else []

/-- The synchronous product of two constrained tree automata. -/
def intersect {Q R Symbol : Type} [DecidableEq Symbol]
    (A : Automaton Q Symbol) (B : Automaton R Symbol) : Automaton (Q × R) Symbol :=
  fun p => (A p.1).flatMap fun e => (B p.2).flatMap (intersectEdge e)

/-- Expose the two source transitions of a product transition. -/
theorem mem_intersect_iff {Q R Symbol : Type} [DecidableEq Symbol]
    (A : Automaton Q Symbol) (B : Automaton R Symbol) (q : Q) (r : R)
    (g : Edge (Q × R) Symbol) :
    g ∈ intersect A B (q, r) ↔
      ∃ e, e ∈ A q ∧ ∃ f, f ∈ B r ∧ e.label = f.label ∧
        e.children.length = f.children.length ∧
        g = ⟨e.label, e.children.zip f.children, fun t => e.guard t && f.guard t⟩ := by
  simp only [intersect, List.mem_flatMap]
  constructor
  · rintro ⟨e, he, f, hf, hg⟩
    unfold intersectEdge at hg
    split at hg
    next h =>
      have hEq := List.mem_singleton.mp hg
      exact ⟨e, he, f, hf, h.1, h.2, hEq⟩
    next => simp at hg
  · rintro ⟨e, he, f, hf, hs, hl, rfl⟩
    exact ⟨e, he, f, hf, by simp [intersectEdge, hs, hl]⟩

/-- Every accepting product run yields an accepting run in each input automaton. -/
theorem intersect_sound {Q R Symbol : Type} [DecidableEq Symbol]
    (A : Automaton Q Symbol) (B : Automaton R Symbol)
    {p : Q × R} {t : Term Symbol} (h : Accepts (intersect A B) p t) :
    Accepts A p.1 t ∧ Accepts B p.2 t := by
  induction h using Accepts.rec
    (motive_2 := fun ps ts _ => All₂
      (fun (p : Q × R) t => Accepts A p.1 t ∧ Accepts B p.2 t) ps ts) with
  | @node p g ts hg hts hguard ih =>
      obtain ⟨e, he, f, hf, hs, hl, hEq⟩ := (mem_intersect_iff A B p.1 p.2 g).mp hg
      subst g
      have hchildren := (all₂_zip_iff (Accepts A) (Accepts B) _ _ _ hl).mp ih
      have hguards := Bool.and_eq_true _ _ |>.mp hguard
      refine ⟨.node e ts he hchildren.1 hguards.1, ?_⟩
      exact (accepts_node_iff B p.2 e.label ts).mpr
        ⟨f, hf, hs.symm, hchildren.2, hguards.2⟩
  | nil => exact .nil
  | cons ht hts iht ihs => exact .cons iht ihs

/-- Input runs for the same tree combine into an accepting product run. -/
theorem intersect_complete {Q R Symbol : Type} [DecidableEq Symbol]
    (A : Automaton Q Symbol) (B : Automaton R Symbol)
    {q : Q} {t : Term Symbol} (h : Accepts A q t) :
    ∀ r, Accepts B r t → Accepts (intersect A B) (q, r) t := by
  induction h using Accepts.rec
    (motive_2 := fun qs ts _ => ∀ rs, All₂ (Accepts B) rs ts →
      All₂ (Accepts (intersect A B)) (qs.zip rs) ts) with
  | @node q e ts he hts hg ih =>
      intro r hb
      obtain ⟨f, hf, hs, hfts, hfg⟩ := (accepts_node_iff B r _ _).mp hb
      let g : Edge (Q × R) Symbol :=
        ⟨e.label, e.children.zip f.children, fun t => e.guard t && f.guard t⟩
      have hlen : e.children.length = f.children.length :=
        hts.length_eq.trans hfts.length_eq.symm
      have hmem : g ∈ intersect A B (q, r) :=
        (mem_intersect_iff A B q r g).mpr ⟨e, he, f, hf, hs.symm, hlen, rfl⟩
      exact .node g ts hmem (ih _ hfts) (by simpa [g] using And.intro hg hfg)
  | nil rs hrs =>
      cases hrs
      exact .nil
  | cons ht hts iht ihs rs hrs =>
      cases hrs with
      | cons hr hrs => exact .cons (iht _ hr) (ihs _ hrs)

/-- Synchronous product preserves exactly the intersection of the two languages. -/
theorem accepts_intersect_iff {Q R Symbol : Type} [DecidableEq Symbol]
    (A : Automaton Q Symbol) (B : Automaton R Symbol)
    (q : Q) (r : R) (t : Term Symbol) :
    Accepts (intersect A B) (q, r) t ↔ Accepts A q t ∧ Accepts B r t := by
  constructor
  · exact intersect_sound A B
  · rintro ⟨ha, hb⟩
    exact intersect_complete A B ha r hb

/-- Product enumeration contains exactly the terms present in both input lists. -/
theorem mem_enumerate_intersect_iff {Q R Symbol : Type} [DecidableEq Symbol]
    (A : Automaton Q Symbol) (B : Automaton R Symbol)
    (fuel : Nat) (q : Q) (r : R) (t : Term Symbol) :
    t ∈ enumerate (intersect A B) fuel (q, r) ↔
      t ∈ enumerate A fuel q ∧ t ∈ enumerate B fuel r := by
  simp only [mem_enumerate_iff, accepts_intersect_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, hh⟩
    exact ⟨⟨ha, hh⟩, ⟨hb, hh⟩⟩
  · rintro ⟨⟨ha, hh⟩, ⟨hb, _⟩⟩
    exact ⟨⟨ha, hb⟩, hh⟩

mutual
  /-- Compare finite trees by symbol and ordered children. -/
  def termEq {Symbol : Type} [DecidableEq Symbol] : Term Symbol → Term Symbol → Bool
    | .node s ts, .node r us => decide (s = r) && forestEq ts us

  /-- Compare child lists by their finite trees. -/
  def forestEq {Symbol : Type} [DecidableEq Symbol] :
      List (Term Symbol) → List (Term Symbol) → Bool
    | [], [] => true
    | t :: ts, u :: us => termEq t u && forestEq ts us
    | _, _ => false
end

/-- The executable tree comparison decides structural equality. -/
theorem termEq_correct {Symbol : Type} [DecidableEq Symbol]
    (t u : Term Symbol) : termEq t u = true ↔ t = u := by
  induction t using Term.rec
    (motive_2 := fun (ts : List (Term Symbol)) => ∀ (us : List (Term Symbol)),
      forestEq ts us = true ↔ ts = us) generalizing u with
  | node symbol ts ih =>
      cases u with
      | node other us => simp [termEq, ih]
  | nil us => cases us <;> simp [forestEq]
  | cons t ts iht ihs us =>
      cases us with
      | nil => simp [forestEq]
      | cons u us => simp [forestEq, iht, ihs]

/-- Look up a subterm. An invalid child index produces no subterm. -/
def Term.atPath {Symbol : Type} : Term Symbol → List Nat → Option (Term Symbol)
  | t, [] => some t
  | .node _ ts, i :: rest => ts[i]?.bind (fun t => t.atPath rest)

/-- A child height does not exceed the greatest height in its child list. -/
theorem height_le_forestHeight {Symbol : Type} (ts : List (Term Symbol))
    (t : Term Symbol) (h : t ∈ ts) : t.height ≤ forestHeight ts := by
  induction ts with
  | nil => simp at h
  | cons u us ih =>
      rcases List.mem_cons.mp h with heq | htail
      · subst t
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

/-- Each path step strictly decreases the available tree height. -/
theorem atPath_height_bound {Symbol : Type} (t u : Term Symbol) (p : List Nat)
    (h : t.atPath p = some u) : u.height + p.length ≤ t.height := by
  induction p generalizing t with
  | nil =>
      have heq : t = u := Option.some.inj h
      subst t
      simp
  | cons i rest ih =>
      cases t with
      | node symbol ts =>
          obtain ⟨child, hchild, hu⟩ := Option.bind_eq_some_iff.mp h
          have hrec := ih child hu
          have hbound := height_le_forestHeight ts child (List.mem_of_getElem? hchild)
          simp only [Term.height, List.length_cons]
          change u.height + (rest.length + 1) ≤ forestHeight ts + 1
          omega

/-- Following a concatenated path equals following its two parts in order. -/
theorem atPath_append {Symbol : Type} (t : Term Symbol) (p rest : List Nat) :
    t.atPath (p ++ rest) = (t.atPath p).bind (fun u => u.atPath rest) := by
  induction p generalizing t with
  | nil => simp [Term.atPath]
  | cons i p ih =>
      cases t with
      | node symbol ts =>
          simp only [List.cons_append, Term.atPath]
          cases hchild : ts[i]? with
          | none => rfl
          | some child => simpa using ih child

/-- Two paths denote the same existing subterm. Missing paths do not satisfy equality. -/
def PathsEqual {Symbol : Type} (t : Term Symbol) (p q : List Nat) : Prop :=
  ∃ u, t.atPath p = some u ∧ t.atPath q = some u

/-- A finite tree cannot equal one of its proper subterms.
Rejecting a path equality with a strict prefix is therefore sound. -/
theorem strict_prefix_paths_not_equal {Symbol : Type} (t : Term Symbol)
    (p rest : List Nat) (hne : rest ≠ []) : ¬ PathsEqual t p (p ++ rest) := by
  rintro ⟨u, hp, hrest⟩
  rw [atPath_append, hp] at hrest
  have hbound := atPath_height_bound u u rest hrest
  have hlength : rest.length = 0 := by omega
  exact hne (List.length_eq_zero_iff.mp hlength)

/-- Decide equality of the two subterms when both paths exist. -/
def pathEquality {Symbol : Type} [DecidableEq Symbol]
    (p q : List Nat) (t : Term Symbol) : Bool :=
  match t.atPath p, t.atPath q with
  | some u, some v => termEq u v
  | _, _ => false

/-- The executable equality guard matches the path semantics. -/
theorem pathEquality_correct {Symbol : Type} [DecidableEq Symbol]
    (p q : List Nat) (t : Term Symbol) :
    pathEquality p q t = true ↔ PathsEqual t p q := by
  unfold pathEquality PathsEqual
  cases hp : t.atPath p <;> cases hq : t.atPath q <;> simp_all [termEq_correct]
  exact eq_comm

/-- Equality of a path with itself still requires that the path exists. -/
theorem pathEquality_self_iff {Symbol : Type} [DecidableEq Symbol]
    (p : List Nat) (t : Term Symbol) :
    pathEquality p p t = true ↔ ∃ u, t.atPath p = some u := by
  rw [pathEquality_correct]
  simp [PathsEqual]

/-- Two absent paths have equal optional lookup results. -/
theorem absent_lookup_results_equal {Symbol : Type} (symbol : Symbol) :
    (Term.node symbol []).atPath [0] = (Term.node symbol []).atPath [1] := rfl

/-- Two absent paths do not satisfy a path equality. -/
theorem absent_paths_not_equal {Symbol : Type} (symbol : Symbol) :
    ¬ PathsEqual (Term.node symbol []) [0] [1] := by
  simp [PathsEqual, Term.atPath]

/-- A guard on the first two children is exactly their tree equality. -/
theorem pathEquality_pair {Symbol : Type} [DecidableEq Symbol]
    (symbol : Symbol) (left right : Term Symbol) :
    pathEquality [0] [1] (.node symbol [left, right]) = true ↔ left = right := by
  simp [pathEquality, Term.atPath, termEq_correct]

/-- Enumerate two independent children and then apply their equality guard. -/
def equalPairCandidates {Q R Symbol : Type} [DecidableEq Symbol]
    (A : Automaton Q Symbol) (B : Automaton R Symbol)
    (fuel : Nat) (q : Q) (r : R) (symbol : Symbol) : List (Term Symbol) :=
  ((enumerate A fuel q).flatMap fun left =>
    (enumerate B fuel r).map fun right => Term.node symbol [left, right]).filter
      (pathEquality [0] [1])

/-- Enumerate a shared child from the intersection and use it at both positions. -/
def sharedPairCandidates {Q R Symbol : Type} [DecidableEq Symbol]
    (A : Automaton Q Symbol) (B : Automaton R Symbol)
    (fuel : Nat) (q : Q) (r : R) (symbol : Symbol) : List (Term Symbol) :=
  (enumerate (intersect A B) fuel (q, r)).map fun child =>
    Term.node symbol [child, child]

/-- Sharing an equal child from the intersected language preserves exactly the terms.
The child must be shared. Independent choices from the intersection do not establish equality.
This is the immediate-child instance of the UVar intersection used by enumeration. -/
theorem equality_sharing_preserves_terms {Q R Symbol : Type} [DecidableEq Symbol]
    (A : Automaton Q Symbol) (B : Automaton R Symbol)
    (fuel : Nat) (q : Q) (r : R) (symbol : Symbol) (t : Term Symbol) :
    t ∈ equalPairCandidates A B fuel q r symbol ↔
      t ∈ sharedPairCandidates A B fuel q r symbol := by
  constructor
  · intro h
    obtain ⟨hm, hg⟩ := List.mem_filter.mp h
    obtain ⟨left, hl, rest⟩ := List.mem_flatMap.mp hm
    obtain ⟨right, hr, ht⟩ := List.mem_map.mp rest
    subst t
    have heq := (pathEquality_pair symbol left right).mp hg
    subst right
    exact List.mem_map.mpr ⟨left,
      (mem_enumerate_intersect_iff A B fuel q r left).mpr ⟨hl, hr⟩, rfl⟩
  · intro h
    obtain ⟨child, hc, ht⟩ := List.mem_map.mp h
    subst t
    obtain ⟨ha, hb⟩ := (mem_enumerate_intersect_iff A B fuel q r child).mp hc
    exact List.mem_filter.mpr
      ⟨List.mem_flatMap.mpr ⟨child, ha, List.mem_map.mpr ⟨child, hb, rfl⟩⟩,
        (pathEquality_pair symbol child child).mpr rfl⟩

end MicroCFTA.Language
