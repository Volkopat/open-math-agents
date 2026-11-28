import OMAStatements.S_oeis_a146955
import Mathlib

/-!
Credit: @ivillar
Proof: for n = k + 1 >= 1 every polynomial in the definition has degree at most n, so the row
sum is additive. The coefficients of (x+1)^n sum to 2^n, and x^m and x^(n-m) each contribute 1
for 1 <= m <= n-1. With Sum_{m=1..n-1} (2^m + 2m) = 2^n - 2 + n(n-1) and 2^(n-4) = 2^n/16 the
row sum is 2^n + 2^(n-3) (2^n - 2 + n(n-1)) = 2^n (2^n + 6 - n + n^2)/8.
-/

open Polynomial in
theorem OMA.solution : type_of% @OMA.S_oeis_a146955.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hX : ∀ j : ℕ, j ≤ k + 1 →
      ∑ i ∈ Finset.range (k + 1 + 1), ((X : ℚ[X]) ^ j).coeff i = 1 := by
    intro j hj
    simp [coeff_X_pow, Finset.mem_range, show j < k + 1 + 1 by omega]
  have h1 : ∑ i ∈ Finset.range (k + 1 + 1), (((X : ℚ[X]) + 1) ^ (k + 1)).coeff i =
      2 ^ (k + 1) := by
    simp only [coeff_X_add_one_pow]
    exact_mod_cast Nat.sum_range_choose (k + 1)
  have hB : ∑ i ∈ Finset.range (k + 1 + 1),
      (∑ m ∈ Finset.Icc 1 k, C ((2 : ℚ) ^ m + 2 * m) * (X ^ m + X ^ (k + 1 - m))).coeff i =
      ∑ m ∈ Finset.Icc 1 k, ((2 : ℚ) ^ m + 2 * m) * 2 := by
    simp only [finsetSum_coeff]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mem_Icc] at hm
    simp only [coeff_C_mul, coeff_add, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hX m (by omega), hX (k + 1 - m) (by omega)]
    ring
  have hS : ∀ j : ℕ, ∑ m ∈ Finset.Icc 1 j, ((2 : ℚ) ^ m + 2 * m) * 2 =
      2 * (2 ^ (j + 1) - 2 + ((j : ℚ) + 1) * j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      ring
  have hk : (2 : ℚ) ^ (((k + 1 : ℕ) : ℤ) - 4) = 2 ^ (k + 1) / 16 := by
    rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
    norm_num
  unfold OMA.S_oeis_a146955.rowSum OMA.S_oeis_a146955.p
  rw [if_neg (by omega), show k + 1 - 1 = k by omega]
  simp only [coeff_add, coeff_C_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, hB, hS k, hk]
  push_cast
  ring
