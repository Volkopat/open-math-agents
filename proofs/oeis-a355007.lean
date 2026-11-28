import OMAStatements.S_oeis_a355007

namespace OMA.P_oeis_a355007

open Polynomial

lemma coeff_prod (c : ℕ) : ∀ m k : ℕ,
    (∏ j ∈ Finset.Icc 1 m, (C (j : ℕ) + C c * X)).coeff k =
      c ^ k * Nat.stirlingFirst (m + 1) (k + 1) := by
  intro m
  induction m with
  | zero =>
    intro k
    rcases k with _ | k
    · simp [Nat.stirlingFirst]
    · simp [coeff_one, Nat.stirlingFirst_eq_zero_of_lt (show 1 < k + 1 + 1 by omega)]
  | succ m ih =>
    intro k
    rw [Finset.prod_Icc_succ_top (by omega)]
    rw [mul_add, coeff_add, ← mul_assoc, coeff_mul_C]
    rcases k with _ | k
    · rw [coeff_mul_X_zero, ih 0, Nat.stirlingFirst_succ_succ (m + 1) 0]
      simp
      ring
    · rw [coeff_mul_X, coeff_mul_C, ih (k + 1), ih k,
        Nat.stirlingFirst_succ_succ (m + 1) (k + 1)]
      ring

end OMA.P_oeis_a355007

theorem OMA.solution : type_of% @OMA.S_oeis_a355007.main := by
  intro n k hk hkn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold OMA.S_oeis_a355007.T OMA.S_oeis_a355007.A056856
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel, OMA.P_oeis_a355007.coeff_prod]
  ring
