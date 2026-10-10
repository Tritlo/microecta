import MicroCFTA.Language
import MicroCFTA.Probability

/-!
# Language coverage and finite sampling

Uniformly sample the finite list of accepting runs from `Language.enumerate`.
This connects the language and probability proofs. Repeated terms receive the
sum of the masses of their runs. A nonempty language is required for a
normalized distribution.
-/

namespace MicroCFTA.Integration

open Language Probability

/-- The exact distribution obtained by choosing a bounded accepting run. -/
def samples (A : Automaton State Symbol) (fuel : Nat) (q : State) :
    Distribution (Term Symbol) := normalize (counting (enumerate A fuel q))

/-- Each observable event has its run count divided by the total run count. -/
theorem event_probability (A : Automaton State Symbol) (fuel : Nat) (q : State)
    (event : Term Symbol → Bool) :
    eventMass event (samples A fuel q) =
      ((enumerate A fuel q).countP event : Rat) / (enumerate A fuel q).length := by
  exact uniform_event_probability event (enumerate A fuel q)

/-- Every entry in the counting distribution has nonnegative mass. -/
theorem counting_nonnegative (values : List α) : Nonnegative (counting values) := by
  intro entry he
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp he
  change (0 : Rat) ≤ 1
  decide

/-- A bounded language with an accepted term has a normalized probability distribution. -/
theorem samples_probability (A : Automaton State Symbol) (fuel : Nat) (q : State)
    (t : Term Symbol) (ha : Accepts A q t) (hh : t.height ≤ fuel) :
    IsProbability (samples A fuel q) := by
  apply normalize_probability _ (counting_nonnegative _)
  rw [total_counting, Rat.natCast_pos]
  have hm := (mem_enumerate_iff A fuel q t).mpr ⟨ha, hh⟩
  exact List.length_pos_iff_exists_mem.mpr ⟨t, hm⟩

/-- An event has no accepting run exactly when its count is zero. -/
theorem event_count_zero_iff (A : Automaton State Symbol) (fuel : Nat) (q : State)
    (event : Term Symbol → Bool) :
    (enumerate A fuel q).countP event = 0 ↔
      ∀ t, Accepts A q t → t.height ≤ fuel → event t = false := by
  rw [List.countP_eq_zero]
  constructor
  · intro h t ha hh
    have ht := h t ((mem_enumerate_iff A fuel q t).mpr ⟨ha, hh⟩)
    cases he : event t <;> simp_all
  · intro h t ht
    obtain ⟨ha, hh⟩ := (mem_enumerate_iff A fuel q t).mp ht
    simp [h t ha hh]

/-- No rejected term can be returned by this finite-run sampler. -/
theorem rejected_event_zero (A : Automaton State Symbol) (fuel : Nat) (q : State)
    (event : Term Symbol → Bool)
    (rejects : ∀ t, Accepts A q t → event t = false) :
    eventMass event (samples A fuel q) = 0 := by
  rw [event_probability,
    (event_count_zero_iff A fuel q event).mpr (fun t ha _ => rejects t ha)]
  simp [Rat.div_def]

/-- Every bounded accepted term occurs at a valid replay rank. -/
theorem accepted_has_rank (A : Automaton State Symbol) (fuel : Nat) (q : State)
    (t : Term Symbol) (ha : Accepts A q t) (hh : t.height ≤ fuel) :
    ∃ rank, rank < (enumerate A fuel q).length ∧
      (enumerate A fuel q)[rank]? = some t := by
  have hm := (mem_enumerate_iff A fuel q t).mpr ⟨ha, hh⟩
  obtain ⟨rank, hr, he⟩ := List.mem_iff_getElem.mp hm
  exact ⟨rank, hr, by simpa [List.getElem?_eq_getElem hr] using congrArg some he⟩

/-- Every valid replay rank decodes to an accepted term within the bound. -/
theorem rank_is_accepted (A : Automaton State Symbol) (fuel : Nat) (q : State)
    (rank : Nat) (t : Term Symbol)
    (h : (enumerate A fuel q)[rank]? = some t) :
    Accepts A q t ∧ t.height ≤ fuel := by
  exact (mem_enumerate_iff A fuel q t).mp (List.mem_of_getElem? h)

/-- With nonzero total count, an event has positive probability exactly when
an accepted term within the bound satisfies it. -/
theorem event_positive_iff (A : Automaton State Symbol) (fuel : Nat) (q : State)
    (event : Term Symbol → Bool) (hn : 0 < (enumerate A fuel q).length) :
    0 < eventMass event (samples A fuel q) ↔
      ∃ t, Accepts A q t ∧ t.height ≤ fuel ∧ event t = true := by
  rw [event_probability, Rat.div_def,
    Rat.mul_pos_iff_of_pos_right (Rat.inv_pos.mpr (Rat.natCast_pos.mpr hn)),
    Rat.natCast_pos, List.countP_pos_iff]
  constructor
  · rintro ⟨t, hm, he⟩
    obtain ⟨ha, hh⟩ := (mem_enumerate_iff A fuel q t).mp hm
    exact ⟨t, ha, hh, he⟩
  · rintro ⟨t, ha, hh, he⟩
    exact ⟨t, (mem_enumerate_iff A fuel q t).mpr ⟨ha, hh⟩, he⟩

/-- Every bounded accepted term has positive output probability, including in
ambiguous automata where several runs produce that term. -/
theorem accepted_positive_probability [DecidableEq Symbol]
    (A : Automaton State Symbol) (fuel : Nat) (q : State) (t : Term Symbol)
    (ha : Accepts A q t) (hh : t.height ≤ fuel) :
    0 < eventMass (fun u => termEq u t) (samples A fuel q) := by
  have hm := (mem_enumerate_iff A fuel q t).mpr ⟨ha, hh⟩
  have hn := List.length_pos_iff_exists_mem.mpr ⟨t, hm⟩
  exact (event_positive_iff A fuel q _ hn).mpr
    ⟨t, ha, hh, (termEq_correct t t).mpr rfl⟩

/-- Acceptance is equivalent to positive output probability at some finite bound. -/
theorem accepts_iff_eventually_positive [DecidableEq Symbol]
    (A : Automaton State Symbol) (q : State) (t : Term Symbol) :
    Accepts A q t ↔ ∃ fuel, 0 < eventMass (fun u => termEq u t) (samples A fuel q) := by
  constructor
  · intro ha
    exact ⟨t.height, accepted_positive_probability A t.height q t ha (Nat.le_refl _)⟩
  · rintro ⟨fuel, hp⟩
    classical
    apply Classical.byContradiction
    intro hn
    have hz := rejected_event_zero A fuel q (fun u => termEq u t) (by
      intro u hu
      cases he : termEq u t
      · rfl
      · have hut := (termEq_correct u t).mp he
        subst u
        exact False.elim (hn hu))
    rw [hz] at hp
    exact Rat.lt_irrefl hp

end MicroCFTA.Integration
