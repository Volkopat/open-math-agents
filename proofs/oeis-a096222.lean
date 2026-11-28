import OMAStatements.S_oeis_a096222
import Mathlib

namespace OMA.S_oeis_a096222

open PowerSeries

theorem rectCount_eq (p q : ℕ) : rectCount p q = (p + 1).choose 2 * (q + 1).choose 2 := by
  simp [rectCount, Finset.card_product, Finset.card_powersetCard, Finset.card_range]

theorem a_eq (n : ℕ) : (a n : ℚ) =
    ((2 : ℚ) ^ (n / 2) + 1) * 2 ^ (n / 2) / 2 * (((2 : ℚ) ^ ((n + 1) / 2) + 1) * 2 ^ ((n + 1) / 2) / 2) := by
  rw [a, rectCount_eq]
  push_cast
  rw [Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 48 * a (n - 3) + 64 * a (n - 4) := by
  have key : (a n : ℚ) = 6 * a (n - 1) - 48 * a (n - 3) + 64 * a (n - 4) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 3 = k + 1 by omega,
      show k + 4 - 4 = k by omega, a_eq, a_eq, a_eq, a_eq]
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · simp only [show (2 * j + 4) / 2 = j + 2 by omega, show (2 * j + 4 + 1) / 2 = j + 2 by omega,
        show (2 * j + 3) / 2 = j + 1 by omega,
        show (2 * j + 1) / 2 = j by omega, show (2 * j + 1 + 1) / 2 = j + 1 by omega,
        show 2 * j / 2 = j by omega]
      ring
    · simp only [show (2 * j + 1 + 4) / 2 = j + 2 by omega,
        show (2 * j + 1 + 4 + 1) / 2 = j + 3 by omega,
        show (2 * j + 1 + 3) / 2 = j + 2 by omega,
        show (2 * j + 1 + 1) / 2 = j + 1 by omega, show (2 * j + 1 + 1 + 1) / 2 = j + 1 by omega,
        show (2 * j + 1) / 2 = j by omega]
      ring
  exact_mod_cast key

theorem a0 : (a 0 : ℚ) = 1 := by rw [a_eq]; norm_num
theorem a1 : (a 1 : ℚ) = 3 := by rw [a_eq]; norm_num
theorem a2 : (a 2 : ℚ) = 9 := by rw [a_eq]; norm_num
theorem a3 : (a 3 : ℚ) = 30 := by rw [a_eq]; norm_num

theorem gf_mul : A * ((1 - 2 * X) * (1 - 4 * X) * (1 - 8 * X ^ 2)) =
    1 - 3 * X - 9 * X ^ 2 + 24 * X ^ 3 := by
  have hD : A * ((1 - 2 * X) * (1 - 4 * X) * (1 - 8 * X ^ 2)) =
      A - C 6 * (A * X ^ 1) + C 48 * (A * X ^ 3) - C 64 * (A * X ^ 4) := by
    simp only [map_ofNat]
    ring
  have hN : (1 - 3 * X - 9 * X ^ 2 + 24 * X ^ 3 : ℚ⟦X⟧) =
      C 1 * X ^ 0 - C 3 * X ^ 1 - C 9 * X ^ 2 + C 24 * X ^ 3 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 4 with hm | hm
  · interval_cases m <;> norm_num [a0, a1, a2, a3]
  · have hr := recurrence m (by omega)
    have hq : (a m : ℚ) = 6 * a (m - 1) - 48 * a (m - 3) + 64 * a (m - 4) := by
      exact_mod_cast hr
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ m := by omega
    have h3 : 3 ≤ m := by omega
    have h4 : 4 ≤ m := by omega
    have k0 : m - 0 ≠ 0 := by omega
    have k1 : m - 1 ≠ 0 := by omega
    have k2 : m - 2 ≠ 0 := by omega
    have k3 : m - 3 ≠ 0 := by omega
    simp only [h1, h2, h3, h4, Nat.zero_le, k0, k1, k2, k3, coeff_C, if_true, if_false, hq]
    ring

end OMA.S_oeis_a096222

theorem OMA.solution : type_of% @OMA.S_oeis_a096222.main := by
  refine ⟨?_, OMA.S_oeis_a096222.recurrence⟩
  have h0 : PowerSeries.constantCoeff ((1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X) *
      (1 - 8 * PowerSeries.X ^ 2) : PowerSeries ℚ) ≠ 0 := by simp
  rw [← OMA.S_oeis_a096222.gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]
