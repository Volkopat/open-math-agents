import OMAStatements.S_oeis_a059138
import Mathlib

open OMA.S_oeis_a059138
open PowerSeries

namespace P059138

theorem sum_v (N : ℕ) :
    ∑ k ∈ Finset.range N, padicValNat 2 (k + 1) = padicValNat 2 N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero N)]
    ring

theorem digits_m (m : ℕ) : Nat.digits 2 (2 ^ m - 1) = List.replicate m 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 2 ^ (m + 1) - 1 = 1 + 2 * (2 ^ m - 1) := by
      have := Nat.one_le_two_pow (n := m)
      rw [pow_succ]; omega
    rw [h1, Nat.digits_add 2 (by norm_num) 1 _ (by norm_num) (by norm_num), ih]
    rfl

theorem v_fact (m : ℕ) : padicValNat 2 (2 ^ m - 1).factorial = 2 ^ m - 1 - m := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) (2 ^ m - 1)
  rw [digits_m] at h
  simp at h
  omega

theorem coll (k : ℕ) : collapsed2 k = 36 * padicValNat 2 k + 18 := by
  simp [collapsed2, element, ruler]
  ring

theorem closed (n : ℕ) : (a n : ℤ) = 18 * (-5 + 3 * 2 ^ (1 + n) - 2 * n) := by
  have h : a n = 36 * (2 ^ (n + 1) - 1 - (n + 1)) + 18 * (2 ^ (n + 1) - 1) := by
    unfold a
    simp only [coll]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_v, v_fact]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  have hle : n + 1 + 1 ≤ 2 ^ (n + 1) := by
    have := Nat.lt_two_pow_self (n := n + 1)
    omega
  rw [h]
  have e1 : ((2 ^ (n + 1) - 1 - (n + 1) : ℕ) : ℤ) = 2 ^ (n + 1) - 1 - (n + 1) := by
    push_cast [show 1 ≤ 2 ^ (n + 1) by omega, show n + 1 ≤ 2 ^ (n + 1) - 1 by omega]
    ring
  have e2 : ((2 ^ (n + 1) - 1 : ℕ) : ℤ) = 2 ^ (n + 1) - 1 := by
    push_cast [show 1 ≤ 2 ^ (n + 1) by omega]
    ring
  push_cast [e1, e2]
  rw [add_comm 1 n]
  ring

theorem recur (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega, closed]
  push_cast
  ring

theorem qa (n : ℕ) : (a n : ℚ) = 18 * (-5 + 3 * 2 ^ (1 + n) - 2 * n) := by
  have := closed n
  exact_mod_cast this

end P059138

theorem OMA.solution : type_of% @OMA.S_oeis_a059138.main := by
  refine ⟨P059138.closed, P059138.recur, ?_⟩
  have hp : ((X - 1) ^ 2 * (2 * X - 1) : PowerSeries ℚ) =
      X ^ 0 * C (-1 : ℚ) + X ^ 1 * C (4 : ℚ) + X ^ 2 * C (-5 : ℚ) + X ^ 3 * C (2 : ℚ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  have hr : (-18 * (X + 1) : PowerSeries ℚ) = X ^ 0 * C (-18 : ℚ) + X ^ 1 * C (-18 : ℚ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [hp, hr]
  ext n
  simp only [mul_add, ← mul_assoc, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  rcases n with _ | _ | _ | n
  · norm_num [P059138.qa]
  · norm_num [P059138.qa]
  · norm_num [P059138.qa]
  · simp only [show ¬ (n + 3 = 0) by omega, show ¬ (n + 3 = 1) by omega, show ¬ (n + 3 ≤ 0) by omega, show ¬ (n + 3 ≤ 1) by omega, if_true, if_false,
      show 2 ≤ n + 3 by omega, show 3 ≤ n + 3 by omega, show 1 ≤ n + 3 by omega, show 0 ≤ n + 3 by omega,
      show n + 3 - 0 = n + 3 by omega, show n + 3 - 1 = n + 2 by omega,
      show n + 3 - 2 = n + 1 by omega, show n + 3 - 3 = n by omega, P059138.qa]
    push_cast
    ring
