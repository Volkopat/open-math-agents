import OMAStatements.S_oeis_a325269
import Mathlib

-- Problem: A325269: Number of integer partitions of n with 2 distinct parts or at least 3 parts.
-- Upstream: formal-conjectures statements/oeis-a325269.lean:0 (declaration OMA.S_oeis_a325269.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! For n > 0 the partitions that are not counted are those with one part, which is only {n},
and those with two equal parts, which is only {n/2, n/2} and exists exactly when n is even. So
1 partition is removed when n is odd and 2 when n is even, which is 1 + ((n-1) mod 2). -/

namespace A325269Aux

open OMA.S_oeis_a325269

/-- The counted property. -/
abbrev Good {n : ℕ} (p : n.Partition) : Prop :=
  (p.parts.card = 2 ∧ p.parts.Nodup) ∨ 3 ≤ p.parts.card

/-- The partition {m, m} of 2 m. -/
def pairP (m : ℕ) (hm : 0 < m) : (2 * m).Partition where
  parts := {m, m}
  parts_pos := by
    intro i hi
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, or_self] at hi
    omega
  parts_sum := by
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
    ring

theorem classify {n : ℕ} (hn : 0 < n) (p : n.Partition) (hp : ¬ Good p) :
    p.parts = {n} ∨ ∃ m, n = 2 * m ∧ p.parts = {m, m} := by
  unfold Good at hp
  have hsum := p.parts_sum
  have hc : p.parts.card = 0 ∨ p.parts.card = 1 ∨ (p.parts.card = 2 ∧ ¬ p.parts.Nodup) := by
    by_contra h
    apply hp
    by_cases h2 : p.parts.card = 2
    · left
      refine ⟨h2, ?_⟩
      by_contra hnd
      exact h (Or.inr (Or.inr ⟨h2, hnd⟩))
    · right
      by_contra h3
      apply h
      omega
  rcases hc with h0 | h1 | ⟨h2, hnd⟩
  · rw [Multiset.card_eq_zero] at h0
    rw [h0] at hsum
    simp at hsum
    omega
  · obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp h1
    rw [hx] at hsum
    simp at hsum
    left
    rw [hx, hsum]
  · obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.mp h2
    rw [hxy] at hsum hnd
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hsum
    have hxe : x = y := by
      by_contra hne
      apply hnd
      simp [hne]
    subst hxe
    right
    exact ⟨x, by omega, hxy⟩

theorem not_good_indiscrete {n : ℕ} (hn : 0 < n) : ¬ Good (Nat.Partition.indiscrete n) := by
  unfold Good
  rw [Nat.Partition.indiscrete_parts (by omega)]
  simp

theorem not_good_pair (m : ℕ) (hm : 0 < m) : ¬ Good (pairP m hm) := by
  unfold Good pairP
  simp

theorem count_odd (m : ℕ) :
    (Finset.univ.filter (fun p : (2 * m + 1).Partition => ¬ Good p)).card = 1 := by
  have h : Finset.univ.filter (fun p : (2 * m + 1).Partition => ¬ Good p) =
      {Nat.Partition.indiscrete (2 * m + 1)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hp
      rcases classify (by omega) p hp with h | ⟨k, hk, _⟩
      · apply Nat.Partition.ext
        rw [h, Nat.Partition.indiscrete_parts (by omega)]
      · omega
    · intro hp
      rw [hp]
      exact not_good_indiscrete (by omega)
  rw [h, Finset.card_singleton]

theorem count_even (m : ℕ) (hm : 0 < m) :
    (Finset.univ.filter (fun p : (2 * m).Partition => ¬ Good p)).card = 2 := by
  have hne : Nat.Partition.indiscrete (2 * m) ≠ pairP m hm := by
    intro h
    have h' := congrArg (fun p : (2 * m).Partition => p.parts.card) h
    simp only [Nat.Partition.indiscrete_parts (show 2 * m ≠ 0 by omega)] at h'
    simp [pairP] at h'
  have h : Finset.univ.filter (fun p : (2 * m).Partition => ¬ Good p) =
      {Nat.Partition.indiscrete (2 * m), pairP m hm} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hp
      rcases classify (by omega) p hp with h | ⟨k, hk, hk'⟩
      · left
        apply Nat.Partition.ext
        rw [h, Nat.Partition.indiscrete_parts (by omega)]
      · right
        have hkm : k = m := by omega
        subst hkm
        apply Nat.Partition.ext
        rw [hk']
        rfl
    · intro hp
      rcases hp with hp | hp
      · rw [hp]
        exact not_good_indiscrete (by omega)
      · rw [hp]
        exact not_good_pair m hm
  rw [h, Finset.card_pair hne]

theorem formula (n : ℕ) (hn : 0 < n) : a n = Fintype.card n.Partition - (1 + (n - 1) % 2) := by
  have ha : a n = (Finset.univ.filter (fun p : n.Partition => Good p)).card := by
    unfold a
    exact Fintype.card_subtype _
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset n.Partition)) (fun p => Good p)
  rw [Finset.card_univ] at hsplit
  rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
  · subst hm
    have hc := count_even m (by omega)
    have hmod : (2 * m - 1) % 2 = 1 := by omega
    rw [ha, hmod]
    omega
  · subst hm
    have hc := count_odd m
    have hmod : (2 * m + 1 - 1) % 2 = 0 := by omega
    rw [ha, hmod]
    omega

end A325269Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a325269.main :=
  A325269Aux.formula
