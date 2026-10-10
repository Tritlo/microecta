import Std

/-!
# Finite sampling and replay ranks

This file models the arithmetic and exact finite sampler in
`microcfta-generator/src/Data/CFTA/Ranked/Internal/Sampler.hs`.
It uses natural ranks after the Haskell range checks.
Rational mass denotes the exact interpretation, not a statement about the
pseudorandom number generator in QuickCheck.
-/

namespace MicroCFTA.Probability

local instance : Std.Associative (α := Rat) (· * ·) := ⟨Rat.mul_assoc⟩
local instance : Std.Commutative (α := Rat) (· * ·) := ⟨Rat.mul_comm⟩

/-- Compose two ranks. The right cardinality is the radix. -/
def pairRank (rightCount left right : Nat) : Nat := left * rightCount + right

/-- Decode a product rank with the same radix. -/
def splitRank (rightCount rank : Nat) : Nat × Nat :=
  (rank / rightCount, rank % rightCount)

/-- Every pair of valid component ranks gives a valid product rank. -/
theorem pairRank_lt {leftCount rightCount left right : Nat}
    (hl : left < leftCount) (hr : right < rightCount) :
    pairRank rightCount left right < leftCount * rightCount := by
  unfold pairRank
  have h := Nat.mul_le_mul_right rightCount hl
  have hs : left * rightCount + rightCount ≤ leftCount * rightCount := by
    simpa [Nat.add_mul] using h
  omega

/-- Product decoding returns both original ranks. -/
theorem split_pair {rightCount left right : Nat} (hr : right < rightCount) :
    splitRank rightCount (pairRank rightCount left right) = (left, right) := by
  have hp : 0 < rightCount := by omega
  simp [splitRank, pairRank, Nat.mul_comm left rightCount,
    Nat.mul_add_div hp, Nat.div_eq_of_lt hr, Nat.add_mod, Nat.mod_eq_of_lt hr]

/-- Product encoding returns the original rank. -/
theorem pair_split (rightCount rank : Nat) :
    pairRank rightCount (splitRank rightCount rank).1
      (splitRank rightCount rank).2 = rank := by
  simpa [pairRank, splitRank, Nat.mul_comm] using Nat.div_add_mod rank rightCount

/-- A valid product rank decodes to valid component ranks. -/
theorem split_lt {leftCount rightCount rank : Nat}
    (hr : rank < leftCount * rightCount) :
    (splitRank rightCount rank).1 < leftCount ∧
      (splitRank rightCount rank).2 < rightCount := by
  have hp : 0 < rightCount := by
    cases rightCount with
    | zero => simp at hr
    | succ n => omega
  exact ⟨(Nat.div_lt_iff_lt_mul hp).2 hr, Nat.mod_lt _ hp⟩

/-- Two distinct valid pairs cannot have the same product rank. -/
theorem pairRank_injective {rightCount l₁ r₁ l₂ r₂ : Nat}
    (h₁ : r₁ < rightCount) (h₂ : r₂ < rightCount)
    (h : pairRank rightCount l₁ r₁ = pairRank rightCount l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  have e := congrArg (splitRank rightCount) h
  rw [split_pair h₁, split_pair h₂] at e
  exact Prod.mk.inj e

/-- Add a rank offset for a branch or a size class. -/
def offsetRank (offset rank : Nat) : Nat := offset + rank

/-- Remove the same rank offset. -/
theorem rebase_offset (offset rank : Nat) : offsetRank offset rank - offset = rank := by
  simp [offsetRank]

/-- Branch offsets preserve the bounds of each consecutive interval. -/
theorem offset_interval {offset count rank : Nat} (h : rank < count) :
    offset ≤ offsetRank offset rank ∧ offsetRank offset rank < offset + count := by
  simp only [offsetRank]
  omega

/-- Expand each integer weight to its sampling tickets. Values may repeat. -/
def tickets (weighted : List (Nat × α)) : List α :=
  weighted.flatMap fun (weight, value) => List.replicate weight value

/-- Integer weight before normalization. Repeated values keep every weight. -/
def eventWeight (predicate : α → Bool) : List (Nat × α) → Nat
  | [] => 0
  | (weight, value) :: rest =>
      (if predicate value then weight else 0) + eventWeight predicate rest

/-- Total ticket count. -/
def ticketCount : List (Nat × α) → Nat
  | [] => 0
  | (weight, _) :: rest => weight + ticketCount rest

/-- Ticket compilation preserves the total weight. -/
theorem tickets_length (weighted : List (Nat × α)) :
    (tickets weighted).length = ticketCount weighted := by
  induction weighted with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨weight, value⟩
      simp [tickets, ticketCount, List.flatMap_cons,
        show (rest.flatMap fun entry => List.replicate entry.1 entry.2).length =
          ticketCount rest from ih]

/-- Exactly the declared number of tickets satisfy each observable event. -/
theorem tickets_event_count (predicate : α → Bool) (weighted : List (Nat × α)) :
    (tickets weighted).countP predicate = eventWeight predicate weighted := by
  induction weighted with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨weight, value⟩
      simp only [tickets, List.flatMap_cons, List.countP_append,
        List.countP_replicate, eventWeight]
      rw [show (rest.flatMap fun entry => List.replicate entry.1 entry.2).countP predicate =
        eventWeight predicate rest from ih]

/-- Decode ordered ticket intervals by subtracting preceding widths. -/
def selectTicket : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (weight, value) :: rest, ticket =>
      if ticket < weight then some value else selectTicket rest (ticket - weight)

/-- Ordered interval selection is the same as indexing the ticket expansion. -/
theorem selectTicket_eq_getElem? (weighted : List (Nat × α)) (ticket : Nat) :
    selectTicket weighted ticket = (tickets weighted)[ticket]? := by
  induction weighted generalizing ticket with
  | nil => simp [selectTicket, tickets]
  | cons entry rest ih =>
      rcases entry with ⟨weight, value⟩
      simp only [selectTicket, tickets, List.flatMap_cons]
      split
      · next h => simp [List.getElem?_append, h]
      · next h =>
        rw [ih]
        simp [List.getElem?_append, h, tickets]

/-- Every in-range ticket selects a value, including zero-width branches. -/
theorem selectTicket_exists (weighted : List (Nat × α)) {ticket : Nat}
    (h : ticket < ticketCount weighted) : ∃ value, selectTicket weighted ticket = some value := by
  rw [selectTicket_eq_getElem?]
  have hl : ticket < (tickets weighted).length := by simpa [tickets_length] using h
  exact ⟨(tickets weighted)[ticket], List.getElem?_eq_getElem hl⟩

/-- A finite exact sampler lists each run and its rational mass. -/
abbrev Distribution (α : Type) := List (Rat × α)

/-- Sum the mass of all runs. -/
def total : Distribution α → Rat
  | [] => 0
  | (mass, _) :: rest => mass + total rest

/-- Apply a value function without changing run weights. -/
def map (f : α → β) (dist : Distribution α) : Distribution β :=
  dist.map fun (mass, value) => (mass, f value)

/-- Multiply every run weight by one factor. -/
def scale (factor : Rat) (dist : Distribution α) : Distribution α :=
  dist.map fun (mass, value) => (factor * mass, value)

/-- Independent applicative sampling multiplies component masses. -/
def product (left : Distribution α) (right : Distribution β) : Distribution (α × β) :=
  left.flatMap fun (lm, lv) => right.map fun (rm, rv) => (lm * rm, (lv, rv))

/-- Sum all run masses for an observable event. -/
def eventMass (predicate : α → Bool) : Distribution α → Rat
  | [] => 0
  | (mass, value) :: rest =>
      (if predicate value then mass else 0) + eventMass predicate rest

/-- Keep only the runs accepted by a predicate. -/
def restrict (predicate : α → Bool) (dist : Distribution α) : Distribution α :=
  dist.filter fun entry => predicate entry.2

/-- Normalize finite nonzero mass. The theorem below states its precondition. -/
def normalize (dist : Distribution α) : Distribution α := scale (total dist)⁻¹ dist

/-- Exact rejection sampling conditions on accepted runs. -/
def condition (predicate : α → Bool) (dist : Distribution α) : Distribution α :=
  normalize (restrict predicate dist)

/-- Concatenation adds run masses, including equal values. -/
theorem total_append (left right : Distribution α) :
    total (left ++ right) = total left + total right := by
  induction left with
  | nil => simp [total, Rat.zero_add]
  | cons entry rest ih =>
      rcases entry with ⟨mass, value⟩
      simp [total, ih, Rat.add_assoc]

/-- Mapping values preserves normalization even when outputs coincide. -/
theorem total_map (f : α → β) (dist : Distribution α) :
    total (map f dist) = total dist := by
  induction dist with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨mass, value⟩
      change mass + total (map f rest) = mass + total rest
      rw [ih]

/-- Scaling run masses scales their sum. -/
theorem total_scale (factor : Rat) (dist : Distribution α) :
    total (scale factor dist) = factor * total dist := by
  induction dist with
  | nil => simp [scale, total]
  | cons entry rest ih =>
      rcases entry with ⟨mass, value⟩
      simp only [scale, List.map_cons, total] at *
      rw [ih, Rat.mul_add]

/-- An independent product has the product of the component total masses. -/
theorem total_product (left : Distribution α) (right : Distribution β) :
    total (product left right) = total left * total right := by
  induction left with
  | nil => simp [product, total]
  | cons entry rest ih =>
      rcases entry with ⟨mass, value⟩
      have hmap : (right.map fun (rm, rv) => (mass * rm, (value, rv))) =
          map (fun rv => (value, rv)) (scale mass right) := by
        simp [map, scale, List.map_map]
      simp only [product, List.flatMap_cons]
      rw [hmap, total_append, total_map, total_scale]
      rw [show total (rest.flatMap fun (lm, lv) =>
        right.map fun (rm, rv) => (lm * rm, (lv, rv))) = total rest * total right from ih]
      simp [total, Rat.add_mul]

/-- Independent normalized samplers remain normalized. -/
theorem product_normalized (left : Distribution α) (right : Distribution β)
    (hl : total left = 1) (hr : total right = 1) :
    total (product left right) = 1 := by
  simp [total_product, hl, hr]

/-- Renormalization is exact whenever its total mass is nonzero. -/
theorem normalize_normalized (dist : Distribution α) (h : total dist ≠ 0) :
    total (normalize dist) = 1 := by
  rw [normalize, total_scale, Rat.inv_mul_cancel _ h]

/-- Filtering sums precisely the accepted event mass. -/
theorem total_restrict (predicate : α → Bool) (dist : Distribution α) :
    total (restrict predicate dist) = eventMass predicate dist := by
  induction dist with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨mass, value⟩
      simp only [restrict, List.filter_cons, eventMass]
      cases h : predicate value <;> simp [h, total, restrict, Rat.zero_add] at *
      · exact ih
      · rw [ih]

/-- Exact conditioning is normalized when acceptance has nonzero mass. -/
theorem condition_normalized (predicate : α → Bool) (dist : Distribution α)
    (h : eventMass predicate dist ≠ 0) : total (condition predicate dist) = 1 := by
  apply normalize_normalized
  simpa [total_restrict] using h

/-- Scaling a finite distribution scales every event probability. -/
theorem eventMass_scale (predicate : α → Bool) (factor : Rat) (dist : Distribution α) :
    eventMass predicate (scale factor dist) = factor * eventMass predicate dist := by
  induction dist with
  | nil => simp [scale, eventMass]
  | cons entry rest ih =>
      rcases entry with ⟨mass, value⟩
      change (if predicate value then factor * mass else 0) +
        eventMass predicate (scale factor rest) = _
      rw [ih]
      cases h : predicate value <;> simp [eventMass, h, Rat.mul_add, Rat.zero_add]

/-- Mapping sums the masses of all preimages of an event. -/
theorem eventMass_map (predicate : β → Bool) (f : α → β) (dist : Distribution α) :
    eventMass predicate (map f dist) = eventMass (predicate ∘ f) dist := by
  induction dist with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨mass, value⟩
      change (if predicate (f value) then mass else 0) + eventMass predicate (map f rest) = _
      rw [ih]
      rfl

/-- Restriction replaces an event by its intersection with acceptance. -/
theorem eventMass_restrict (event accepted : α → Bool) (dist : Distribution α) :
    eventMass event (restrict accepted dist) =
      eventMass (fun value => accepted value && event value) dist := by
  induction dist with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨mass, value⟩
      simp only [restrict, List.filter_cons]
      cases ha : accepted value <;> cases he : event value <;>
        simp [ha, he, eventMass, Rat.zero_add, restrict] at *
      all_goals rw [ih]

/-- Exact conditional probability is accepted event mass divided by acceptance. -/
theorem eventMass_condition (event accepted : α → Bool) (dist : Distribution α) :
    eventMass event (condition accepted dist) =
      eventMass (fun value => accepted value && event value) dist /
        eventMass accepted dist := by
  rw [condition, normalize, eventMass_scale, total_restrict, eventMass_restrict]
  rw [Rat.div_def, Rat.mul_comm]

/-- Appending outcomes adds their event masses. -/
theorem eventMass_append (predicate : α → Bool) (left right : Distribution α) :
    eventMass predicate (left ++ right) = eventMass predicate left + eventMass predicate right := by
  induction left with
  | nil => simp [eventMass, Rat.zero_add]
  | cons entry rest ih =>
      rcases entry with ⟨mass, value⟩
      simp [eventMass, ih, Rat.add_assoc]

/-- An impossible event has zero mass. -/
theorem eventMass_false (dist : Distribution α) : eventMass (fun _ => false) dist = 0 := by
  induction dist with
  | nil => rfl
  | cons entry rest ih => cases entry; simp [eventMass, ih, Rat.zero_add]

/-- Independent component events have the product of their probabilities. -/
theorem eventMass_product (leftEvent : α → Bool) (rightEvent : β → Bool)
    (left : Distribution α) (right : Distribution β) :
    eventMass (fun pair => leftEvent pair.1 && rightEvent pair.2) (product left right) =
      eventMass leftEvent left * eventMass rightEvent right := by
  induction left with
  | nil => simp [product, eventMass]
  | cons entry rest ih =>
      rcases entry with ⟨mass, value⟩
      have hm : (right.map fun (rm, rv) => (mass * rm, (value, rv))) =
          map (fun rv => (value, rv)) (scale mass right) := by
        simp [map, scale, List.map_map]
      simp only [product, List.flatMap_cons]
      rw [hm, eventMass_append, eventMass_map, eventMass_scale]
      rw [show eventMass (fun pair => leftEvent pair.1 && rightEvent pair.2)
        (rest.flatMap fun (lm, lv) => right.map fun (rm, rv) => (lm * rm, (lv, rv))) =
        eventMass leftEvent rest * eventMass rightEvent right from ih]
      cases h : leftEvent value
      · simp [Function.comp_def, h, eventMass, eventMass_false, Rat.zero_add]
      · simp [Function.comp_def, h, eventMass, Rat.add_mul]

/-- A rational probability of an integer ticket event. -/
def ticketProbability (predicate : α → Bool) (weighted : List (Nat × α)) : Rat :=
  ((tickets weighted).countP predicate : Rat) / (tickets weighted).length

/-- The ticket sampler gives exactly weight divided by total weight. -/
theorem ticketProbability_eq (predicate : α → Bool) (weighted : List (Nat × α)) :
    ticketProbability predicate weighted =
      (eventWeight predicate weighted : Rat) / ticketCount weighted := by
  simp [ticketProbability, tickets_event_count, tickets_length]

/-- Give mass one to each list occurrence before normalization. -/
def counting (values : List α) : Distribution α := values.map fun value => (1, value)

/-- Counting mass is the number of occurrences, including duplicates. -/
theorem total_counting (values : List α) : total (counting values) = values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      change 1 + total (counting rest) = ((rest.length + 1 : Nat) : Rat)
      rw [ih]
      simp [Rat.add_comm]

/-- Event mass for a counting distribution is its occurrence count. -/
theorem eventMass_counting (predicate : α → Bool) (values : List α) :
    eventMass predicate (counting values) = (values.countP predicate : Rat) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      change (if predicate value then 1 else 0) + eventMass predicate (counting rest) = _
      rw [ih]
      cases h : predicate value <;> simp [h, Rat.add_zero, Rat.add_comm]

/-- Uniform occurrence sampling has the exact event count divided by length. -/
theorem uniform_event_probability (predicate : α → Bool) (values : List α) :
    eventMass predicate (normalize (counting values)) =
      (values.countP predicate : Rat) / values.length := by
  rw [normalize, eventMass_scale, total_counting, eventMass_counting]
  rw [Rat.div_def, Rat.mul_comm]

/-- The expanded integer-ticket semantics agrees with exact weighted sampling. -/
theorem uniform_tickets_probability (predicate : α → Bool) (weighted : List (Nat × α)) :
    eventMass predicate (normalize (counting (tickets weighted))) =
      (eventWeight predicate weighted : Rat) / ticketCount weighted := by
  rw [uniform_event_probability, tickets_event_count, tickets_length]

/-- A distribution has no negative run mass. -/
def Nonnegative (dist : Distribution α) : Prop := ∀ entry ∈ dist, 0 ≤ entry.1

/-- A finite probability distribution has nonnegative masses and total one. -/
def IsProbability (dist : Distribution α) : Prop := Nonnegative dist ∧ total dist = 1

/-- The total of nonnegative runs is nonnegative. -/
theorem total_nonnegative (dist : Distribution α) (h : Nonnegative dist) : 0 ≤ total dist := by
  induction dist with
  | nil => exact Rat.le_refl
  | cons entry rest ih =>
      rcases entry with ⟨mass, value⟩
      apply Rat.add_nonneg
      · exact h (mass, value) (by simp)
      · exact ih (fun entry he => h entry (List.mem_cons_of_mem _ he))

/-- Nonnegative scaling preserves nonnegative masses. -/
theorem nonnegative_scale (factor : Rat) (dist : Distribution α)
    (hf : 0 ≤ factor) (hd : Nonnegative dist) : Nonnegative (scale factor dist) := by
  intro entry he
  obtain ⟨⟨mass, value⟩, hm, rfl⟩ := List.mem_map.mp he
  exact Rat.mul_nonneg hf (hd _ hm)

/-- Positive normalization produces a probability distribution. -/
theorem normalize_probability (dist : Distribution α)
    (hn : Nonnegative dist) (ht : 0 < total dist) : IsProbability (normalize dist) := by
  constructor
  · exact nonnegative_scale _ _ (Rat.le_of_lt (Rat.inv_pos.mpr ht)) hn
  · apply normalize_normalized
    exact Rat.ne_of_gt ht

/-- Uniform occurrence sampling is a probability distribution for a nonempty list. -/
theorem uniform_probability (values : List α) (h : 0 < values.length) :
    IsProbability (normalize (counting values)) := by
  apply normalize_probability
  · intro entry he
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp he
    change (0 : Rat) ≤ 1
    decide
  · rw [total_counting]
    exact Rat.natCast_pos.mpr h

/-- Independent probability distributions give a probability distribution. -/
theorem product_probability (left : Distribution α) (right : Distribution β)
    (hl : IsProbability left) (hr : IsProbability right) : IsProbability (product left right) := by
  constructor
  · intro entry he
    obtain ⟨⟨lm, lv⟩, hlm, her⟩ := List.mem_flatMap.mp he
    obtain ⟨⟨rm, rv⟩, hrm, rfl⟩ := List.mem_map.mp her
    exact Rat.mul_nonneg (hl.1 _ hlm) (hr.1 _ hrm)
  · exact product_normalized left right hl.2 hr.2

/-- A filtered nonnegative distribution still has nonnegative masses. -/
theorem nonnegative_restrict (predicate : α → Bool) (dist : Distribution α)
    (h : Nonnegative dist) : Nonnegative (restrict predicate dist) := by
  intro entry he
  exact h entry (List.mem_filter.mp he).1

/-- Conditioning a nonnegative distribution on positive mass is a probability. -/
theorem condition_probability (predicate : α → Bool) (dist : Distribution α)
    (hn : Nonnegative dist) (ha : 0 < eventMass predicate dist) :
    IsProbability (condition predicate dist) := by
  apply normalize_probability
  · exact nonnegative_restrict predicate dist hn
  · simpa [total_restrict] using ha

/-- The branch weights used by a finite frequency choice. -/
def branchWeight : List (Rat × Distribution α) → Rat
  | [] => 0
  | (weight, _) :: rest => weight + branchWeight rest

/-- Combine branches at their unnormalized external weights. -/
def mix : List (Rat × Distribution α) → Distribution α
  | [] => []
  | (weight, dist) :: rest => scale weight dist ++ mix rest

/-- Interpret frequency as external weight divided by the total weight. -/
def frequency (branches : List (Rat × Distribution α)) : Distribution α :=
  scale (branchWeight branches)⁻¹ (mix branches)

/-- The numerator of an event probability in a weighted choice. -/
def weightedEvent (predicate : α → Bool) : List (Rat × Distribution α) → Rat
  | [] => 0
  | (weight, dist) :: rest => weight * eventMass predicate dist + weightedEvent predicate rest

/-- A weighted mixture sums each branch weight times its event probability. -/
theorem eventMass_mix (predicate : α → Bool) (branches : List (Rat × Distribution α)) :
    eventMass predicate (mix branches) = weightedEvent predicate branches := by
  induction branches with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨weight, dist⟩
      rw [mix, eventMass_append, eventMass_scale, ih]
      rfl

/-- The exact frequency event probability is its weighted numerator over total weight. -/
theorem eventMass_frequency (predicate : α → Bool) (branches : List (Rat × Distribution α)) :
    eventMass predicate (frequency branches) =
      weightedEvent predicate branches / branchWeight branches := by
  rw [frequency, eventMass_scale, eventMass_mix, Rat.div_def, Rat.mul_comm]

/-- A mixture of normalized branches has the sum of external weights. -/
theorem total_mix (branches : List (Rat × Distribution α))
    (h : ∀ entry ∈ branches, total entry.2 = 1) :
    total (mix branches) = branchWeight branches := by
  induction branches with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨weight, dist⟩
      rw [mix, total_append, total_scale, h (weight, dist) (by simp), Rat.mul_one]
      rw [ih (fun entry he => h entry (List.mem_cons_of_mem _ he))]
      rfl

/-- Finite frequency choice is exactly normalized. -/
theorem frequency_normalized (branches : List (Rat × Distribution α))
    (hb : ∀ entry ∈ branches, total entry.2 = 1)
    (hw : branchWeight branches ≠ 0) : total (frequency branches) = 1 := by
  rw [frequency, total_scale, total_mix branches hb, Rat.inv_mul_cancel _ hw]

/-- Positive weighted choice preserves nonnegative run masses and normalization. -/
theorem frequency_probability (branches : List (Rat × Distribution α))
    (hb : ∀ entry ∈ branches, 0 ≤ entry.1 ∧ IsProbability entry.2)
    (hw : 0 < branchWeight branches) : IsProbability (frequency branches) := by
  constructor
  · apply nonnegative_scale
    · exact Rat.le_of_lt (Rat.inv_pos.mpr hw)
    · have nonneg : ∀ bs : List (Rat × Distribution α),
          (∀ entry ∈ bs, 0 ≤ entry.1 ∧ Nonnegative entry.2) → Nonnegative (mix bs) := by
        intro bs
        induction bs with
        | nil => intro h entry he; cases he
        | cons branch rest ih =>
            intro h entry he
            obtain ⟨hf, hd⟩ := h branch (by simp)
            rcases List.mem_append.mp he with he | he
            · exact nonnegative_scale branch.1 branch.2 hf hd entry he
            · exact ih (fun branch hm => h branch (List.mem_cons_of_mem _ hm)) entry he
      exact nonneg branches (fun entry hm => ⟨(hb entry hm).1, (hb entry hm).2.1⟩)
  · exact frequency_normalized branches (fun entry hm => (hb entry hm).2.2) (Rat.ne_of_gt hw)

/-- Scaling twice multiplies the scale factors. -/
theorem scale_scale (left right : Rat) (dist : Distribution α) :
    scale left (scale right dist) = scale (left * right) dist := by
  simp [scale, List.map_map, Rat.mul_assoc]

/-- A scale factor of one keeps every run unchanged. -/
theorem scale_one (dist : Distribution α) : scale 1 dist = dist := by
  simp [scale]

/-- A normalized bucket times its retained mass recovers its original runs. -/
theorem restore_normalized (dist : Distribution α) (h : total dist ≠ 0) :
    scale (total dist) (normalize dist) = dist := by
  rw [normalize, scale_scale, Rat.mul_inv_cancel _ h, scale_one]

/-- Removing a common nonzero scale leaves the normalized distribution unchanged. -/
theorem normalize_scale (factor : Rat) (dist : Distribution α) (hf : factor ≠ 0) :
    normalize (scale factor dist) = normalize dist := by
  rw [normalize, total_scale, scale_scale, Rat.inv_mul_rev]
  have hc : (total dist)⁻¹ * factor⁻¹ * factor = (total dist)⁻¹ := by
    rw [Rat.mul_assoc, Rat.inv_mul_cancel _ hf, Rat.mul_one]
  rw [hc]
  rfl

/-- An integer or rational weight rescaling preserves all event probabilities. -/
theorem normalized_scale_event (predicate : α → Bool) (factor : Rat)
    (dist : Distribution α) (hf : factor ≠ 0) :
    eventMass predicate (normalize (scale factor dist)) =
      eventMass predicate (normalize dist) := by
  rw [normalize_scale factor dist hf]

/-- Reordering runs preserves total mass. -/
theorem total_perm {left right : Distribution α} (h : left.Perm right) :
    total left = total right := by
  induction h with
  | nil => rfl
  | cons entry h ih =>
      rcases entry with ⟨mass, value⟩
      simp [total, ih]
  | swap x y rest =>
      rcases x with ⟨xm, xv⟩
      rcases y with ⟨ym, yv⟩
      simp [total, Rat.add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Reordering runs preserves every event mass, including duplicate outputs. -/
theorem eventMass_perm (predicate : α → Bool)
    {left right : Distribution α} (h : left.Perm right) :
    eventMass predicate left = eventMass predicate right := by
  induction h with
  | nil => rfl
  | cons entry h ih =>
      rcases entry with ⟨mass, value⟩
      simp [eventMass, ih]
  | swap x y rest =>
      rcases x with ⟨xm, xv⟩
      rcases y with ⟨ym, yv⟩
      simp [eventMass, Rat.add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Sorts and group order changes do not change the normalized distribution. -/
theorem normalized_perm_event (predicate : α → Bool)
    {left right : Distribution α} (h : left.Perm right) :
    eventMass predicate (normalize left) = eventMass predicate (normalize right) := by
  simp only [normalize, eventMass_scale]
  rw [total_perm h, eventMass_perm predicate h]

/-- A conditional bucket retains its original unnormalized mass. -/
def conditionalBuckets (groups : List (Distribution α)) : List (Rat × Distribution α) :=
  groups.map fun group => (total group, normalize group)

/-- Expanding normalized buckets at their original masses restores all runs. -/
theorem mix_conditionalBuckets (groups : List (Distribution α))
    (h : ∀ group ∈ groups, total group ≠ 0) :
    mix (conditionalBuckets groups) = groups.flatten := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      change scale (total group) (normalize group) ++ mix (conditionalBuckets rest) = _
      rw [restore_normalized group (h group (by simp)),
        ih (fun group hg => h group (List.mem_cons_of_mem _ hg))]
      rfl

/-- The retained group masses sum to the original run mass. -/
theorem weight_conditionalBuckets (groups : List (Distribution α)) :
    branchWeight (conditionalBuckets groups) = total groups.flatten := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      change total group + branchWeight (conditionalBuckets rest) = total (group ++ rest.flatten)
      rw [ih, total_append]

/-- Grouping, conditioning each group, and selecting by group mass is exact. -/
theorem regrouping_preserves_distribution (groups : List (Distribution α))
    (h : ∀ group ∈ groups, total group ≠ 0) :
    frequency (conditionalBuckets groups) = normalize groups.flatten := by
  rw [frequency, mix_conditionalBuckets groups h, weight_conditionalBuckets]
  rfl

/-- A matched join group selects each pair with its conditional product mass. -/
theorem join_group_pair_probability
    (leftMass rightMass leftGroupMass rightGroupMass acceptedMass : Rat)
    (hl : leftGroupMass ≠ 0) (hr : rightGroupMass ≠ 0) :
    (leftGroupMass * rightGroupMass / acceptedMass) *
      (leftMass / leftGroupMass) * (rightMass / rightGroupMass) =
      leftMass * rightMass / acceptedMass := by
  simp only [Rat.div_def]
  calc
    _ = leftMass * rightMass * acceptedMass⁻¹ *
        ((leftGroupMass * leftGroupMass⁻¹) * (rightGroupMass * rightGroupMass⁻¹)) := by ac_rfl
    _ = leftMass * rightMass * acceptedMass⁻¹ := by
      rw [Rat.mul_inv_cancel _ hl, Rat.mul_inv_cancel _ hr]
      simp

/-- Count-weighted branches with uniform members give equal global rank mass. -/
theorem count_weighted_uniform_rank (branchCount totalCount : Rat)
    (hb : branchCount ≠ 0) :
    branchCount / totalCount * (1 / branchCount) = 1 / totalCount := by
  simp only [Rat.div_def, Rat.one_mul]
  calc
    branchCount * totalCount⁻¹ * branchCount⁻¹ =
        (branchCount * branchCount⁻¹) * totalCount⁻¹ := by ac_rfl
    _ = totalCount⁻¹ := by rw [Rat.mul_inv_cancel _ hb, Rat.one_mul]

/-- Count-weighted size splits give each uniform pair the same mass. -/
theorem count_weighted_uniform_product (leftCount rightCount totalCount : Rat)
    (hl : leftCount ≠ 0) (hr : rightCount ≠ 0) :
    leftCount * rightCount / totalCount * (1 / leftCount) * (1 / rightCount) =
      1 / totalCount := by
  simpa only [Rat.one_mul] using
    join_group_pair_probability 1 1 leftCount rightCount totalCount hl hr

/-- A compiled equal-weight block decodes with quotient by ticket width. -/
theorem compiled_block_decode {width position within : Nat} (h : within < width) :
    (position * width + within) / width = position := by
  have hw : 0 < width := by omega
  rw [Nat.mul_comm position width, Nat.mul_add_div hw, Nat.div_eq_of_lt h, Nat.add_zero]

/-- Every ticket of a compiled equal-weight block decodes to a valid payload. -/
theorem compiled_block_range {width values ticket : Nat} (h : ticket < values * width) :
    ticket / width < values := by
  have hw : 0 < width := by
    cases width with
    | zero => simp at h
    | succ n => omega
  exact (Nat.div_lt_iff_lt_mul hw).2 h

/-- Duplicate outputs add mass. Equality of values does not merge their ranks. -/
theorem duplicate_outputs_mass :
    eventMass (fun value : Bool => value)
      (normalize (counting [true, true, false])) = 2 / 3 := by decide +kernel

/-- Uniform branches do not imply uniform ranks when branch sizes differ. -/
theorem oneof_unequal_cardinalities :
    eventMass (fun value : Nat => value == 0)
      (frequency [(1, normalize (counting [0])), (1, normalize (counting [1, 2]))]) = 1 / 2 ∧
    eventMass (fun value : Nat => value == 1)
      (frequency [(1, normalize (counting [0])), (1, normalize (counting [1, 2]))]) = 1 / 4 := by decide +kernel

/-- Before reconstruction, both atomic alternatives survive size bound one. -/
theorem atomic_size_bound_preserves_distribution :
    eventMass (fun pair : Nat × Bool => !pair.2)
      (condition (fun pair => pair.1 ≤ 1)
        [(1 / 2, (1, true)), (1 / 2, (1, false))]) = 1 / 2 := by decide +kernel

/-- Replacing atomic size by term size removes a previously admitted alternative. -/
theorem reconstructed_size_bound_changes_distribution :
    eventMass (fun pair : Nat × Bool => !pair.2)
      (condition (fun pair => pair.1 ≤ 1)
        [(1 / 2, (1, true)), (1 / 2, (2, false))]) = 0 := by decide +kernel

end MicroCFTA.Probability
