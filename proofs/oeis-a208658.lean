import OMAStatements.S_oeis_a208658
import Mathlib

-- Problem: A208658, the row-sum formula and generating function.
-- Upstream: formal-conjectures statements/oeis-a208658.lean (declaration OMA.S_oeis_a208658.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: the binomial row sums give a(n) = n (2^n - 1) - 2^(n-1); this closed form is annihilated
-- by (1-x)^2 (1-2x)^2, and the first five coefficients are checked directly.

namespace OMA.P_oeis_a208658

open OMA.S_oeis_a208658

theorem closed (n : ℕ) (hn : 1 ≤ n) : a n = (n : ℤ) * ((2 : ℤ) ^ n - 1) - (2 : ℤ) ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold a
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Nat.add_sub_cancel]
  have h1 : ∑ k ∈ Finset.range (m + 1), ((Nat.choose (m + 1) (k + 1) : ℕ) : ℤ) = 2 ^ (m + 1) - 1 := by
    have := Nat.sum_range_choose (m + 1)
    rw [Finset.sum_range_succ'] at this
    simp only [Nat.choose_zero_right] at this
    have h' : ∑ k ∈ Finset.range (m + 1), Nat.choose (m + 1) (k + 1) = 2 ^ (m + 1) - 1 := by
      omega
    rw [← Nat.cast_sum, h']
    have : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
    push_cast [this]
    ring
  have h2 : ∑ k ∈ Finset.range (m + 1), ((Nat.choose m k : ℕ) : ℤ) = 2 ^ m := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  rw [h1, h2]

theorem rec4 (m : ℕ) : a (m + 5) = 6 * a (m + 4) - 13 * a (m + 3) + 12 * a (m + 2) - 4 * a (m + 1) := by
  rw [closed _ (by omega), closed _ (by omega), closed _ (by omega), closed _ (by omega),
    closed _ (by omega)]
  simp only [Nat.add_sub_cancel, show m + 5 - 1 = m + 4 by omega, show m + 4 - 1 = m + 3 by omega,
    show m + 3 - 1 = m + 2 by omega, show m + 2 - 1 = m + 1 by omega]
  push_cast
  ring

open PowerSeries in
theorem gf : ((1-PowerSeries.X)^2*(1-2*PowerSeries.X)^2*F =
      (4 : PowerSeries ℤ)*PowerSeries.X^2 - 7*PowerSeries.X^3 + 2*PowerSeries.X^4) := by
  have hden : ((1 - X) ^ 2 * (1 - 2 * X) ^ 2 : PowerSeries ℤ) =
      1 - C (6 : ℤ) * X ^ 1 + C (13 : ℤ) * X ^ 2 - C (12 : ℤ) * X ^ 3 + C (4 : ℤ) * X ^ 4 := by
    simp only [map_ofNat]
    ring
  have hnum : ((4 : PowerSeries ℤ) * X ^ 2 - 7 * X ^ 3 + 2 * X ^ 4) =
      C (4 : ℤ) * X ^ 2 - C (7 : ℤ) * X ^ 3 + C (2 : ℤ) * X ^ 4 := by
    simp only [map_ofNat]
  have a0 : a 0 = 0 := rfl
  have a1 : a 1 = 0 := by rw [closed 1 le_rfl]; norm_num
  have a2 : a 2 = 4 := by rw [closed 2 (by norm_num)]; norm_num
  have a3 : a 3 = 17 := by rw [closed 3 (by norm_num)]; norm_num
  have a4 : a 4 = 52 := by rw [closed 4 (by norm_num)]; norm_num
  rw [hden, hnum, mul_comm]
  ext n
  simp only [F, mul_sub, mul_add, mul_one, map_sub, map_add, mul_left_comm (mk a) (C _),
    coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [a0, a1, a2, a3, a4]
  · simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, ↓reduceIte]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    rw [rec4]
    ring

end OMA.P_oeis_a208658

theorem OMA.solution : type_of% @OMA.S_oeis_a208658.main :=
  ⟨OMA.P_oeis_a208658.closed, OMA.P_oeis_a208658.gf⟩
