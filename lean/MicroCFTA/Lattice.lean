import Std

/-!
# Integer counting identities

These proofs state the arithmetic invariants used by
`Data.CFTA.Refinement.Lattice`. Lists represent the entries of a signed map.
The proofs do not verify the Haskell map implementation or the full polynomial
eliminator. In particular, the antiderivative theorem has an explicit premise.
-/

namespace MicroCFTA.Lattice

/-- A Boolean formula over an arbitrary atom type. -/
inductive Formula (α : Type) where
  | atom : α → Formula α
  | top : Formula α
  | bottom : Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α
  | neg : Formula α → Formula α
  deriving Repr

/-- Evaluate the atoms at one integer assignment. -/
def eval (test : α → Bool) : Formula α → Bool
  | .atom a => test a
  | .top => true
  | .bottom => false
  | .conj p q => eval test p && eval test q
  | .disj p q => eval test p || eval test q
  | .neg p => !(eval test p)

/-- The integer indicator of a Boolean proposition. -/
def indicator (b : Bool) : Int := if b then 1 else 0

/-- A conjunction with an integer coefficient. -/
abbrev Signed (α : Type) := List (List (α × Bool) × Int)

/-- Evaluate a conjunction of positive or negative atoms. -/
def region (test : α → Bool) (xs : List (α × Bool)) : Bool :=
  xs.all fun (a, positive) => test a == positive

/-- Evaluate a signed sum at one assignment. -/
def score (test : α → Bool) : Signed α → Int
  | [] => 0
  | (xs, coefficient) :: rest =>
      coefficient * indicator (region test xs) + score test rest

/-- Multiply each signed conjunction by one conjunction. -/
def timesRegion (xs : List (α × Bool)) (coefficient : Int) (ys : Signed α) : Signed α :=
  ys.map fun (zs, weight) => (xs ++ zs, coefficient * weight)

/-- Multiply signed sums. This implements conjunction. -/
def conjoin (xs ys : Signed α) : Signed α :=
  xs.flatMap fun (zs, weight) => timesRegion zs weight ys

/-- Negate every coefficient. -/
def negate (xs : Signed α) : Signed α := xs.map fun (ys, weight) => (ys, -weight)

/-- Inclusion and exclusion for disjunction. -/
def disjoin (xs ys : Signed α) : Signed α := xs ++ ys ++ negate (conjoin xs ys)

theorem indicator_and (a b : Bool) : indicator (a && b) = indicator a * indicator b := by
  cases a <;> cases b <;> decide

theorem indicator_or (a b : Bool) :
    indicator (a || b) = indicator a + indicator b - indicator a * indicator b := by
  cases a <;> cases b <;> decide

theorem region_append (test : α → Bool) (xs ys : List (α × Bool)) :
    region test (xs ++ ys) = (region test xs && region test ys) := by
  simp [region]

theorem score_append (test : α → Bool) (xs ys : Signed α) :
    score test (xs ++ ys) = score test xs + score test ys := by
  induction xs with
  | nil => simp [score]
  | cons x xs ih => simp [score, ih, Int.add_assoc]

theorem score_timesRegion (test : α → Bool) (xs : List (α × Bool))
    (c : Int) (ys : Signed α) :
    score test (timesRegion xs c ys) = c * indicator (region test xs) * score test ys := by
  induction ys with
  | nil => simp [timesRegion, score]
  | cons y ys ih =>
    simp only [timesRegion, List.map_cons, score, region_append, indicator_and] at *
    rw [ih]
    grind

theorem score_conjoin (test : α → Bool) (xs ys : Signed α) :
    score test (conjoin xs ys) = score test xs * score test ys := by
  induction xs with
  | nil => simp [conjoin, score]
  | cons x xs ih =>
    simp only [conjoin, List.flatMap_cons, score_append, score_timesRegion, score] at *
    rw [ih]
    grind

theorem score_negate (test : α → Bool) (xs : Signed α) :
    score test (negate xs) = -score test xs := by
  induction xs with
  | nil => simp [negate, score]
  | cons x xs ih =>
    simp only [negate, List.map_cons, score] at *
    rw [ih]
    grind

theorem score_disjoin (test : α → Bool) (xs ys : Signed α) :
    score test (disjoin xs ys) =
      score test xs + score test ys - score test xs * score test ys := by
  simp [disjoin, score_append, score_negate, score_conjoin, Int.sub_eq_add_neg, Int.add_assoc]

/-- Compile a formula. A false polarity moves negation down to each atom. -/
def signed (positive : Bool) : Formula α → Signed α
  | .atom a => [([(a, positive)], 1)]
  | .top => if positive then [([], 1)] else []
  | .bottom => if positive then [] else [([], 1)]
  | .conj p q => if positive then conjoin (signed positive p) (signed positive q)
                            else disjoin (signed positive p) (signed positive q)
  | .disj p q => if positive then disjoin (signed positive p) (signed positive q)
                            else conjoin (signed positive p) (signed positive q)
  | .neg p => signed (!positive) p

/-- The signed compiler counts each satisfying assignment exactly once. -/
theorem signed_correct (test : α → Bool) (f : Formula α) (positive : Bool) :
    score test (signed positive f) = indicator (eval test f == positive) := by
  induction f generalizing positive with
  | atom a => cases positive <;> cases h : test a <;> simp [signed, score, region, eval, indicator, h]
  | top => cases positive <;> simp [signed, score, region, eval, indicator]
  | bottom => cases positive <;> simp [signed, score, region, eval, indicator]
  | conj p q ihp ihq =>
    cases positive <;> simp only [signed, Bool.false_eq_true, ↓reduceIte,
      score_conjoin, score_disjoin, ihp, ihq, eval]
    all_goals cases eval test p <;> cases eval test q <;> decide
  | disj p q ihp ihq =>
    cases positive <;> simp only [signed, Bool.false_eq_true, ↓reduceIte,
      score_conjoin, score_disjoin, ihp, ihq, eval]
    all_goals cases eval test p <;> cases eval test q <;> decide
  | neg p ih =>
    simp only [signed, ih, eval]
    cases positive <;> cases eval test p <;> decide

/-- Signed counts sum exactly over any finite list of candidate assignments. -/
theorem signed_count (candidates : List σ) (test : σ → α → Bool) (f : Formula α) :
    (candidates.map fun s => score (test s) (signed true f)).sum =
      (candidates.map fun s => indicator (eval (test s) f)).sum := by
  simp [signed_correct]

/-- Dividing all coefficients by a positive common divisor preserves an integer inequality.
The offset uses floor division. The value `z` is the divided linear part. -/
theorem normalize_divisor (d z offset : Int) (hd : 0 < d) :
    (0 ≤ d * z + offset) ↔ 0 ≤ z + offset / d := by
  have h := Int.ediv_nonneg_iff_of_pos (a := d * z + offset) hd
  rw [Int.mul_add_ediv_left z offset (by omega)] at h
  exact h.symm

/-- Integer strict inequalities become non-strict inequalities with an offset of one. -/
theorem strict_inequality (x y : Int) : x < y ↔ 0 ≤ y - x - 1 := by omega

/-- The negation of an integer lower bound is another integer lower bound. -/
theorem negate_inequality (x : Int) : (¬ 0 ≤ x) ↔ 0 ≤ -x - 1 := by omega

/-- Keep the smallest offset among inequalities with equal coefficients. -/
theorem tightest_offset (x a b : Int) :
    (0 ≤ x + a ∧ 0 ≤ x + b) ↔ 0 ≤ x + min a b := by omega

/-- Opposite directions with a negative total offset are inconsistent. -/
theorem opposite_inconsistent (x a b : Int) (h : a + b < 0) :
    ¬ (0 ≤ x + a ∧ 0 ≤ -x + b) := by omega

/-- One Fourier-Motzkin pair preserves every solution of its two source bounds. -/
theorem project_pair (a b x l u : Int) (ha : 0 < a) (hb : b < 0)
    (hl : 0 ≤ a * x + l) (hu : 0 ≤ b * x + u) :
    0 ≤ (-b) * l + a * u := by
  have h₁ := Int.mul_nonneg (show 0 ≤ -b by omega) hl
  have h₂ := Int.mul_nonneg (show 0 ≤ a by omega) hu
  grind

/-- A selected maximum must be greater than each earlier bound and at least each later bound. -/
def FirstMaximum (values : Nat → Int) (n chosen : Nat) : Prop :=
  chosen < n ∧ ∀ i, i < n →
    if i < chosen then values i < values chosen else values i ≤ values chosen

/-- The strict tie rule prevents two lower-bound pieces from counting the same point. -/
theorem firstMaximum_unique (values : Nat → Int) (n i j : Nat)
    (hi : FirstMaximum values n i) (hj : FirstMaximum values n j) : i = j := by
  obtain ⟨hin, hi⟩ := hi
  obtain ⟨hjn, hj⟩ := hj
  have h₁ := hi j hjn
  have h₂ := hj i hin
  split at h₁ <;> split at h₂ <;> omega

/-- Every nonempty finite list of bounds has a first maximum. -/
theorem firstMaximum_exists (values : Nat → Int) (n : Nat) (hn : 0 < n) :
    ∃ i, FirstMaximum values n i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hzero : n = 0
    · subst n
      exact ⟨0, by simp [FirstMaximum]⟩
    · obtain ⟨i, hi, hmax⟩ := ih (by omega)
      by_cases hnew : values i < values n
      · refine ⟨n, by omega, ?_⟩
        intro j hj
        by_cases hjn : j < n
        · simp only [hjn, ↓reduceIte]
          have h := hmax j hjn
          split at h <;> omega
        · have : j = n := by omega
          subst j
          simp
      · refine ⟨i, by omega, ?_⟩
        intro j hj
        by_cases hjn : j < n
        · exact hmax j hjn
        · have : j = n := by omega
          subst j
          have hni : ¬ n < i := by omega
          simp only [hni, ↓reduceIte]
          omega

/-- A finite sum starting at an arbitrary integer. -/
def intervalSum (f : Int → Rat) (start : Int) : Nat → Rat
  | 0 => 0
  | n + 1 => intervalSum f start n + f (start + n)

/-- A discrete antiderivative computes an interval sum, including negative endpoints. -/
theorem intervalSum_antiderivative (f F : Int → Rat)
    (step : ∀ x, F (x + 1) - F x = f x) (start : Int) (n : Nat) :
    intervalSum f start n = F (start + n) - F start := by
  induction n with
  | zero => simp [intervalSum]; grind
  | succ n ih =>
    simp only [intervalSum, ih]
    have h := step (start + n)
    have he : start + (↑(n + 1) : Int) = (start + n) + 1 := by omega
    rw [he]
    grind

end MicroCFTA.Lattice
