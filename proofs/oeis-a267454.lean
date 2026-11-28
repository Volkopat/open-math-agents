import OMAStatements.S_oeis_a267454

-- Problem: A267454: Total number of OFF cells after n iterations of Rule 131 from a single ON cell.
-- Upstream: formal-conjectures statements/oeis-a267454.lean (declaration OMA.S_oeis_a267454.main)
-- Credit: @nerotulip90 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof (Grok Bot w3): an explicit closed description P t i of the Rule 131 pattern (for t >= 3:
-- ON outside [-t, t], left half ON iff (t+i) % 3 = 0, interior right part periodic with
-- (8t+i) % 12 in {0,3,4,5,10}, two cells left of the tip ON iff t even, tip OFF), proved by
-- induction on t via region lemmas (with a decide check for t < 9). Counting gives
-- on(t+3) = on(t) + [1,3,1,4](t % 4) for t >= 3, hence the order-8 linear recurrence for a,
-- and the generating function follows coefficientwise from the recurrence and a(0..7).

namespace OMA.A267454Proof
open OMA.S_oeis_a267454 Finset

abbrev P (t : ℕ) (i : ℤ) : Prop :=
  (t = 0 ∧ i = 0) ∨ (t = 1 ∧ i ≠ 0 ∧ i ≠ 1) ∨ (t = 2 ∧ i ≠ -1 ∧ i ≠ 0 ∧ i ≠ 2) ∨
  (3 ≤ t ∧ (i < -(t:ℤ) ∨ (t:ℤ) < i ∨ (-(t:ℤ) ≤ i ∧ i ≤ 0 ∧ ((t:ℤ) + i) % 3 = 0) ∨
    (1 ≤ i ∧ i + 3 ≤ (t:ℤ) ∧ ((8 * (t:ℤ) + i) % 12 = 0 ∨ (8 * (t:ℤ) + i) % 12 = 3 ∨
      (8 * (t:ℤ) + i) % 12 = 4 ∨ (8 * (t:ℤ) + i) % 12 = 5 ∨ (8 * (t:ℤ) + i) % 12 = 10)) ∨
    ((t:ℤ) - 2 ≤ i ∧ i + 1 ≤ (t:ℤ) ∧ (t:ℤ) % 2 = 0)))

def S (z : ℤ) : Prop := z % 12 = 0 ∨ z % 12 = 3 ∨ z % 12 = 4 ∨ z % 12 = 5 ∨ z % 12 = 10

lemma L1 (t : ℕ) (x : ℤ) (ht : 3 ≤ t) (h : x < -(t:ℤ)) : P t x := by unfold P; omega
lemma L2 (t : ℕ) (x : ℤ) (ht : 3 ≤ t) (h1 : -(t:ℤ) ≤ x) (h2 : x ≤ 0) :
    P t x ↔ ((t:ℤ) + x) % 3 = 0 := by unfold P; omega
lemma L3 (t : ℕ) (x : ℤ) (ht : 3 ≤ t) (h1 : 1 ≤ x) (h2 : x + 3 ≤ (t:ℤ)) :
    P t x ↔ S (8 * (t:ℤ) + x) := by unfold P S; omega
lemma L4 (t : ℕ) (x : ℤ) (ht : 3 ≤ t) (h1 : (t:ℤ) - 2 ≤ x) (h2 : x + 1 ≤ (t:ℤ)) :
    P t x ↔ (t:ℤ) % 2 = 0 := by unfold P; omega
lemma L5 (t : ℕ) (ht : 3 ≤ t) : ¬ P t (t:ℤ) := by unfold P; omega
lemma L6 (t : ℕ) (x : ℤ) (ht : 3 ≤ t) (h : (t:ℤ) < x) : P t x := by unfold P; omega

lemma S_step (z : ℤ) : ((¬ S (z - 1) ∧ ¬ S z) ∨ (S (z - 1) ∧ S z ∧ S (z + 1))) ↔ S (z + 8) := by
  unfold S
  have : z % 12 = 0 ∨ z % 12 = 1 ∨ z % 12 = 2 ∨ z % 12 = 3 ∨ z % 12 = 4 ∨ z % 12 = 5 ∨
    z % 12 = 6 ∨ z % 12 = 7 ∨ z % 12 = 8 ∨ z % 12 = 9 ∨ z % 12 = 10 ∨ z % 12 = 11 := by omega
  rcases this with h|h|h|h|h|h|h|h|h|h|h|h <;> omega

lemma T12 (T : ℤ) : T % 12 = 0 ∨ T % 12 = 1 ∨ T % 12 = 2 ∨ T % 12 = 3 ∨ T % 12 = 4 ∨ T % 12 = 5 ∨
    T % 12 = 6 ∨ T % 12 = 7 ∨ T % 12 = 8 ∨ T % 12 = 9 ∨ T % 12 = 10 ∨ T % 12 = 11 := by omega

lemma step_big (t : ℕ) (ht : 9 ≤ t) (i : ℤ) :
    ((¬ P t (i - 1) ∧ ¬ P t i) ∨ (P t (i - 1) ∧ P t i ∧ P t (i + 1))) ↔ P (t + 1) i := by
  have h3 : 3 ≤ t := by omega
  have h3' : 3 ≤ t + 1 := by omega
  have hT : (9:ℤ) ≤ t := by exact_mod_cast ht
  have e : ((t + 1 : ℕ) : ℤ) = (t:ℤ) + 1 := by push_cast; ring
  set T : ℤ := (t:ℤ) with hTdef
  -- regions
  rcases lt_or_ge i (-T - 1) with ha | ha
  · rw [iff_true_intro (L1 t (i-1) h3 (by omega)), iff_true_intro (L1 t i h3 (by omega)),
      iff_true_intro (L1 t (i+1) h3 (by omega)), iff_true_intro (L1 (t+1) i h3' (by omega))]
    simp
  rcases eq_or_lt_of_le ha with hb | hb
  · rw [iff_true_intro (L1 t (i-1) h3 (by omega)), iff_true_intro (L1 t i h3 (by omega)),
      L2 t (i+1) h3 (by omega) (by omega), L2 (t+1) i h3' (by omega) (by omega)]
    rw [e]; simp only [not_true, and_false, false_or, true_and]; omega
  rcases eq_or_lt_of_le (show -T ≤ i by omega) with hc | hc
  · rw [iff_true_intro (L1 t (i-1) h3 (by omega)), L2 t i h3 (by omega) (by omega),
      L2 t (i+1) h3 (by omega) (by omega), L2 (t+1) i h3' (by omega) (by omega)]
    rw [e]; omega
  rcases lt_or_ge i 0 with hd | hd
  · rw [L2 t (i-1) h3 (by omega) (by omega), L2 t i h3 (by omega) (by omega),
      L2 t (i+1) h3 (by omega) (by omega), L2 (t+1) i h3' (by omega) (by omega)]
    rw [e]; omega
  rcases eq_or_lt_of_le hd with he | he
  · subst he
    rw [L2 t (0-1) h3 (by omega) (by omega), L2 t 0 h3 (by omega) (by omega),
      L2 (t+1) 0 h3' (by omega) (by omega)]
    rw [e]; omega
  rcases eq_or_lt_of_le (show (1:ℤ) ≤ i by omega) with hf | hf
  · subst hf
    rw [L2 t (1-1) h3 (by omega) (by omega), L3 t 1 h3 (by omega) (by omega),
      L3 t (1+1) h3 (by omega) (by omega), L3 (t+1) 1 h3' (by omega) (by omega)]
    rw [e]; unfold S
    rcases T12 T with h|h|h|h|h|h|h|h|h|h|h|h <;> omega
  rcases le_or_gt i (T - 4) with hg | hg
  · rw [L3 t (i-1) h3 (by omega) (by omega), L3 t i h3 (by omega) (by omega),
      L3 t (i+1) h3 (by omega) (by omega), L3 (t+1) i h3' (by omega) (by omega), e]
    have := S_step (8 * T + i)
    rw [show 8 * T + i - 1 = 8 * T + (i - 1) by ring, show 8 * T + i + 1 = 8 * T + (i + 1) by ring,
      show 8 * T + i + 8 = 8 * (T + 1) + i by ring] at this
    exact this
  rcases eq_or_lt_of_le (show T - 3 ≤ i by omega) with hh | hh
  · subst hh
    rw [L3 t (T-3-1) h3 (by omega) (by omega), L3 t (T-3) h3 (by omega) (by omega),
      L4 t (T-3+1) h3 (by omega) (by omega), L3 (t+1) (T-3) h3' (by omega) (by omega), e]
    unfold S
    rcases T12 (t:ℤ) with h|h|h|h|h|h|h|h|h|h|h|h <;> omega
  rcases eq_or_lt_of_le (show T - 2 ≤ i by omega) with hi | hi
  · subst hi
    rw [L3 t (T-2-1) h3 (by omega) (by omega), L4 t (T-2) h3 (by omega) (by omega),
      L4 t (T-2+1) h3 (by omega) (by omega), L3 (t+1) (T-2) h3' (by omega) (by omega), e]
    unfold S
    rcases T12 (t:ℤ) with h|h|h|h|h|h|h|h|h|h|h|h <;> omega
  rcases eq_or_lt_of_le (show T - 1 ≤ i by omega) with hj | hj
  · subst hj
    rw [L4 t (T-1-1) h3 (by omega) (by omega), L4 t (T-1) h3 (by omega) (by omega),
      show T - 1 + 1 = T by ring, iff_false_intro (L5 t h3),
      L4 (t+1) (T-1) h3' (by omega) (by omega), e]
    simp only [and_false, or_false, and_self]
    omega
  rcases eq_or_lt_of_le (show T ≤ i by omega) with hk | hk
  · subst hk
    rw [L4 t (T-1) h3 (by omega) (by omega), iff_false_intro (L5 t h3),
      iff_true_intro (L6 t (T+1) h3 (by omega)),
      L4 (t+1) T h3' (by omega) (by omega), e]
    simp only [and_false, false_and, or_false, and_true, and_self, not_false_eq_true]
    omega
  rcases eq_or_lt_of_le (show T + 1 ≤ i by omega) with hl | hl
  · subst hl
    have h5 := L5 (t+1) h3'
    rw [e] at h5
    rw [show T + 1 - 1 = T by ring, iff_false_intro (L5 t h3), iff_false_intro h5,
      iff_true_intro (L6 t (T+1) h3 (by omega)), iff_true_intro (L6 t (T+1+1) h3 (by omega))]
    simp
  · rw [iff_true_intro (L6 t (i-1) h3 (by omega)), iff_true_intro (L6 t i h3 (by omega)),
      iff_true_intro (L6 t (i+1) h3 (by omega)), iff_true_intro (L6 (t+1) i h3' (by omega))]
    simp

def Pb (t : ℕ) (i : ℤ) : Bool := decide (P t i)

lemma Pb_iff (t : ℕ) (i : ℤ) : Pb t i = true ↔ P t i := decide_eq_true_iff

lemma step_small : ∀ t : ℕ, t < 9 → ∀ k : ℕ, k < 25 →
    (((!Pb t ((k:ℤ) - 12 - 1) && !Pb t ((k:ℤ) - 12)) ||
      (Pb t ((k:ℤ) - 12 - 1) && Pb t ((k:ℤ) - 12) && Pb t ((k:ℤ) - 12 + 1))) =
      Pb (t + 1) ((k:ℤ) - 12)) := by decide

lemma P_step (t : ℕ) (i : ℤ) :
    ((¬ P t (i - 1) ∧ ¬ P t i) ∨ (P t (i - 1) ∧ P t i ∧ P t (i + 1))) ↔ P (t + 1) i := by
  rcases le_or_gt 9 t with ht | ht
  · exact step_big t ht i
  rcases le_or_gt (-12) i with h1 | h1
  · rcases le_or_gt i 12 with h2 | h2
    · have := step_small t ht (i + 12).toNat (by omega)
      rw [show (((i + 12).toNat : ℕ) : ℤ) - 12 = i by omega] at this
      rw [← Pb_iff, ← Pb_iff, ← Pb_iff, ← Pb_iff, ← this]
      cases Pb t (i - 1) <;> cases Pb t i <;> cases Pb t (i + 1) <;> simp
    · unfold P; push_cast; omega
  · unfold P; push_cast; omega


lemma rule131 (l c r : Bool) :
    ruleOut 131 l c r = ((!l && !c) || (l && c && r)) := by
  cases l <;> cases c <;> cases r <;> decide

lemma cell_iff (t : ℕ) : ∀ i : ℤ, cell 131 t i = true ↔ P t i := by
  induction t with
  | zero => intro i; simp [cell, P]
  | succ t ih =>
    intro i
    rw [← P_step]
    show ruleOut 131 (cell 131 t (i - 1)) (cell 131 t i) (cell 131 t (i + 1)) = true ↔ _
    rw [rule131, ← ih, ← ih, ← ih]
    cases cell 131 t (i - 1) <;> cases cell 131 t i <;> cases cell 131 t (i + 1) <;> simp

lemma onCount_eq (t : ℕ) :
    onCount 131 t = ∑ j ∈ range (2 * t + 1), if P t ((j : ℤ) - t) then 1 else 0 := by
  unfold onCount
  refine sum_congr rfl fun j _ => ?_
  simp only [cell_iff]

def g (t : ℕ) (x : ℤ) : ℕ := if P t x then 1 else 0

def on' (t : ℕ) : ℕ := ∑ j ∈ range (2 * t + 1), g t ((j : ℤ) - t)

lemma onCount_eq' (t : ℕ) : onCount 131 t = on' t := onCount_eq t

def δ (r : ℕ) : ℕ := if r = 0 then 1 else if r = 1 then 3 else if r = 2 then 1 else 4

lemma on_step_big (t : ℕ) (ht : 3 ≤ t) : on' (t + 3) = on' t + δ (t % 4) := by
  unfold on'
  rw [show 2 * (t + 3) + 1 = (3 + (2 * t - 2)) + 6 by omega, sum_range_add, sum_range_add,
    show 2 * t + 1 = (2 * t - 2) + 3 by omega, sum_range_add]
  have hA : ∑ x ∈ range 3, g (t + 3) (((x : ℕ) : ℤ) - ((t + 3 : ℕ) : ℤ)) = 1 := by
    have a0 : P (t + 3) (((0:ℕ) : ℤ) - ((t + 3 : ℕ) : ℤ)) := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    have a1 : ¬ P (t + 3) (((1:ℕ) : ℤ) - ((t + 3 : ℕ) : ℤ)) := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    have a2 : ¬ P (t + 3) (((2:ℕ) : ℤ) - ((t + 3 : ℕ) : ℤ)) := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    simp only [sum_range_succ, sum_range_zero, zero_add, g, a0, a1, a2]
    simp
  have hM : ∑ r ∈ range (2 * t - 2), g (t + 3) (((3 + r : ℕ) : ℤ) - ((t + 3 : ℕ) : ℤ))
      = ∑ r ∈ range (2 * t - 2), g t ((r : ℤ) - t) := by
    refine sum_congr rfl fun r hr => ?_
    have hr' := mem_range.1 hr
    have e1 : (((3 + r : ℕ) : ℤ) - ((t + 3 : ℕ) : ℤ)) = (r : ℤ) - t := by push_cast; ring
    rw [e1]
    unfold g
    congr 1
    apply propext
    rcases le_or_gt (r : ℤ) t with h | h
    · rw [L2 (t+3) ((r:ℤ) - t) (by omega) (by push_cast; omega) (by omega),
        L2 t ((r:ℤ) - t) ht (by omega) (by omega)]
      push_cast; omega
    · rw [L3 (t+3) ((r:ℤ) - t) (by omega) (by omega) (by push_cast; omega),
        L3 t ((r:ℤ) - t) ht (by omega) (by omega)]
      unfold S; push_cast; omega
  have hB : ∑ s ∈ range 6, g (t + 3) (((3 + (2 * t - 2) + s : ℕ) : ℤ) - ((t + 3 : ℕ) : ℤ)) =
      if t % 4 = 3 then 3 else 2 := by
    have e : ∀ s : ℕ, (((3 + (2 * t - 2) + s : ℕ) : ℤ) - ((t + 3 : ℕ) : ℤ)) = (t : ℤ) - 2 + s := by
      intro s; push_cast [show 2 * t - 2 + 2 = 2 * t by omega]; omega
    simp only [e]
    simp only [sum_range_succ, sum_range_zero, zero_add, g]
    have b0 : P (t+3) ((t:ℤ) - 2) ↔ (t % 4 = 0 ∨ t % 4 = 2) := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    have b1 : P (t+3) ((t:ℤ) - 2 + 1) ↔ t % 4 = 2 := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    have b2 : P (t+3) (t:ℤ) ↔ (t % 4 = 3 ∨ t % 4 = 0) := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    have b2' : P (t+3) ((t:ℤ) - 2 + 2) ↔ (t % 4 = 3 ∨ t % 4 = 0) := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    have b3 : P (t+3) ((t:ℤ) - 2 + 3) ↔ t % 2 = 1 := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    have b4 : P (t+3) ((t:ℤ) - 2 + 4) ↔ t % 2 = 1 := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    have b5 : ¬ P (t+3) ((t:ℤ) - 2 + 5) := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero] at *
    simp only [b0, b1, b2, b2', b3, b4, b5]
    have h4 : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
    have h2 : t % 2 = (t % 4) % 2 := by omega
    rcases h4 with h | h | h | h <;> rw [h] at h2 <;> simp [h, h2]
  have hC : ∑ s ∈ range 3, g t ((((2 * t - 2) + s : ℕ) : ℤ) - (t : ℤ)) =
      if t % 2 = 0 then 2 else 0 := by
    have e : ∀ s : ℕ, ((((2 * t - 2) + s : ℕ) : ℤ) - (t : ℤ)) = (t : ℤ) - 2 + s := by
      intro s; push_cast [show 2 * t - 2 + 2 = 2 * t by omega]; omega
    simp only [e]
    simp only [sum_range_succ, sum_range_zero, zero_add, g]
    have c0 : P t ((t:ℤ) - 2) ↔ t % 2 = 0 := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    have c1 : P t ((t:ℤ) - 2 + 1) ↔ t % 2 = 0 := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    have c2 : ¬ P t (t:ℤ) := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    have c2' : ¬ P t ((t:ℤ) - 2 + 2) := by unfold P; push_cast; (try simp only [true_and, false_and, false_or, or_false, and_false]); omega
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero] at *
    simp only [c0, c1, c2, c2']
    rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h]
  rw [hA, hM, hB, hC]
  unfold δ
  have h4 : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases h4 with h | h | h | h <;> simp [h, show t % 2 = (t % 4) % 2 by omega] <;> omega


lemma on_small : on' 0 = 1 ∧ on' 1 = 1 ∧ on' 2 = 2 ∧ on' 3 = 2 ∧ on' 4 = 4 ∧ on' 5 = 3 ∧
    on' 6 = 6 ∧ on' 7 = 5 := by decide

lemma on_step (t : ℕ) : on' (t + 3) = on' t + δ (t % 4) := by
  rcases lt_or_ge t 3 with h | h
  · obtain ⟨h0, h1, h2, h3, h4, h5, -, -⟩ := on_small
    interval_cases t <;> simp [δ, *]
  · exact on_step_big t h

def d (k : ℕ) : ℤ := (2 * k + 1 : ℤ) - on' k

lemma a_eq (n : ℕ) : a n = ∑ k ∈ range (n + 1), d k := by
  unfold a d
  refine sum_congr rfl fun k _ => ?_
  rw [onCount_eq']

lemma a_succ (n : ℕ) : a (n + 1) = a n + d (n + 1) := by
  rw [a_eq, a_eq, sum_range_succ]

lemma d_step (k : ℕ) : d (k + 3) = d k + 6 - δ (k % 4) := by
  unfold d; rw [on_step]; push_cast; ring

lemma rec_int (m : ℕ) :
    a (m + 8) = a (m + 7) + a (m + 5) - a (m + 3) - a (m + 1) + a m := by
  have s7 := a_succ (m + 7)
  have s4 := a_succ (m + 4)
  have s3 := a_succ (m + 3)
  have s0 := a_succ m
  have d5 := d_step (m + 5)
  have d1 := d_step (m + 1)
  have e : (m + 5) % 4 = (m + 1) % 4 := by omega
  rw [e] at d5
  simp only [show m + 7 + 1 = m + 8 by ring, show m + 4 + 1 = m + 5 by ring,
    show m + 3 + 1 = m + 4 by ring, show m + 5 + 3 = m + 8 by ring,
    show m + 1 + 3 = m + 4 by ring] at *
  linarith

lemma a_init : a 0 = 0 ∧ a 1 = 2 ∧ a 2 = 5 ∧ a 3 = 10 ∧ a 4 = 15 ∧ a 5 = 23 ∧
    a 6 = 30 ∧ a 7 = 40 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := on_small
  have z : a 0 = 0 := by rw [a_eq]; simp [d, h0]
  have s := a_succ
  simp only [d] at s
  refine ⟨z, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [s, z, h1, h2, h3, h4, h5, h6, h7]; norm_num

end OMA.A267454Proof

open OMA.S_oeis_a267454 OMA.A267454Proof PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267454.main := by
  show
    (∀ n : ℕ, 8 ≤ n → (a n : ℚ) = a (n - 1) + a (n - 3) - a (n - 5) - a (n - 7) + a (n - 8)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℚ) = X * (2 + 3 * X + 5 * X ^ 2 + 3 * X ^ 3 + 3 * X ^ 4 - X ^ 5))
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 3 = m + 5 by omega,
      show m + 8 - 5 = m + 3 by omega, show m + 8 - 7 = m + 1 by omega,
      show m + 8 - 8 = m by omega]
    exact_mod_cast rec_int m
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := a_init
    set F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ)) with hF
    have hL : F * ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℚ) =
        F - F * X ^ 1 - F * X ^ 3 + F * X ^ 5 + F * X ^ 7 - F * X ^ 8 := by ring
    have hR : (X * (2 + 3 * X + 5 * X ^ 2 + 3 * X ^ 3 + 3 * X ^ 4 - X ^ 5) : PowerSeries ℚ) =
        C 2 * X ^ 1 + C 3 * X ^ 2 + C 5 * X ^ 3 + C 3 * X ^ 4 + C 3 * X ^ 5 - C 1 * X ^ 6 := by
      simp only [map_ofNat, map_one]; ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, coeff_mul_X_pow', coeff_C_mul_X_pow, hF, coeff_mk]
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7] <;> norm_num
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    have r' : (a (m + 8) : ℚ) = a (m + 7) + a (m + 5) - a (m + 3) - a (m + 1) + a m := by
      exact_mod_cast rec_int m
    simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 3 = m + 5 by omega,
      show m + 8 - 5 = m + 3 by omega, show m + 8 - 7 = m + 1 by omega,
      show m + 8 - 8 = m by omega, show 1 ≤ m + 8 by omega, show 3 ≤ m + 8 by omega,
      show 5 ≤ m + 8 by omega, show 7 ≤ m + 8 by omega, show 8 ≤ m + 8 by omega, if_true,
      show ¬ (m + 8 = 1) by omega, show ¬ (m + 8 = 2) by omega,
      show ¬ (m + 8 = 3) by omega, show ¬ (m + 8 = 4) by omega, show ¬ (m + 8 = 5) by omega,
      show ¬ (m + 8 = 6) by omega, if_false]
    simp [coeff_C]
    linarith
