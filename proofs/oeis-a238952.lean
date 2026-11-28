import OMAStatements.S_oeis_a238952
import Mathlib

open Finset Nat

namespace A238952Proof

lemma step_div (n i : ℕ) (hn : 1 ≤ n) : n / i - (n - 1) / i = if i ∣ n then 1 else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.succ_div]
  exact Nat.add_sub_cancel_left _ _

lemma rhs_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 (n / 2), i.divisors.card * (n / i - (n - 1) / i)
      = ∑ i ∈ n.properDivisors, i.divisors.card := by
  have h1 : ∀ i ∈ Finset.Icc 1 (n / 2), i.divisors.card * (n / i - (n - 1) / i)
      = if i ∣ n then i.divisors.card else 0 := by
    intro i _
    rw [step_div n i hn]
    split_ifs <;> simp
  rw [sum_congr rfl h1, ← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [mem_filter, mem_Icc, mem_properDivisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, by omega⟩
  · rintro ⟨h3, h4⟩
    obtain ⟨k, rfl⟩ := h3
    have hi : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h
        simp at hn
      · exact h
    have hk : 2 ≤ k := by
      by_contra hk
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · simp at hn
      · simp at h4
    refine ⟨⟨hi, ?_⟩, dvd_mul_right _ _⟩
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    exact Nat.mul_le_mul_left i hk

end A238952Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a238952.main := by
  intro n hn
  unfold OMA.S_oeis_a238952.arcs
  rw [A238952Proof.rhs_eq n hn]
  have hn0 : n ≠ 0 := by omega
  rw [← insert_self_properDivisors hn0, sum_insert self_notMem_properDivisors]
  have h2 : ∀ i ∈ n.properDivisors, i.divisors.card = i.properDivisors.card + 1 := by
    intro i hi
    have hi0 : i ≠ 0 := (pos_of_mem_properDivisors hi).ne'
    rw [← insert_self_properDivisors hi0,
      card_insert_of_notMem self_notMem_properDivisors]
  rw [sum_congr rfl h2, sum_add_distrib, sum_const, smul_eq_mul, mul_one]
  exact Nat.add_comm _ _
