import OMAStatements.S_oeis_a004138
import Mathlib

open OMA.S_oeis_a004138 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a004138.main := by
  have hq : ∀ F : PowerSeries ℚ, F * ((X - 1) * (2 * X ^ 4 - X ^ 3 + X ^ 2 + X - 1)) = F - C (2 : ℚ) * (F * X ^ 1) + C (2 : ℚ) * (F * X ^ 3) - C (3 : ℚ) * (F * X ^ 4) + C (2 : ℚ) * (F * X ^ 5) := by
    intro F; simp only [map_ofNat, map_one, pow_one]; ring
  have hr : (-(-1 + X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4) : PowerSeries ℚ) = 1 - X ^ 2 + C (4 : ℚ) * X ^ 3 - C (2 : ℚ) * X ^ 4 := by
    simp only [map_ofNat, map_one, pow_one]; ring
  rw [hq, hr]
  ext n
  simp only [map_add, map_sub, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
  by_cases hn : n < 5
  · interval_cases n <;> norm_num [a]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m + 0 by omega]
    have e1 : a (m + 5 + 1) = a (m + 5) + a (m + 4) - a (m + 3) + 2 * a (m + 2) + 2 := rfl
    have e2 : a (m + 4 + 1) = a (m + 4) + a (m + 3) - a (m + 2) + 2 * a (m + 1) + 2 := rfl
    simp only [show m + 0 + 1 = m + 1 by omega, show m + 1 + 1 = m + 2 by omega, show m + 2 + 1 = m + 3 by omega, show m + 3 + 1 = m + 4 by omega] at *
    push_cast [e1, e2]
    ring
