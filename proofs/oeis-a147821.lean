import OMAStatements.S_oeis_a147821
import Mathlib

open OMA.S_oeis_a147821 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a147821.main := by
  refine ⟨?_, ?_⟩
  · have hq : ∀ F : PowerSeries ℚ, F * (1 - X) ^ 11 = F - C (11 : ℚ) * (F * X ^ 1) + C (55 : ℚ) * (F * X ^ 2) - C (165 : ℚ) * (F * X ^ 3) + C (330 : ℚ) * (F * X ^ 4) - C (462 : ℚ) * (F * X ^ 5) + C (462 : ℚ) * (F * X ^ 6) - C (330 : ℚ) * (F * X ^ 7) + C (165 : ℚ) * (F * X ^ 8) - C (55 : ℚ) * (F * X ^ 9) + C (11 : ℚ) * (F * X ^ 10) - (F * X ^ 11) := by
      intro F; simp only [map_ofNat]; ring
    have hr : (12 * X ^ 4 * (9 + 416 * X + 1826 * X ^ 2 + 46 * X ^ 3 + 291 * X ^ 4 - 78 * X ^ 5 + 10 * X ^ 6) : PowerSeries ℚ) = C (108 : ℚ) * X ^ 4 + C (4992 : ℚ) * X ^ 5 + C (21912 : ℚ) * X ^ 6 + C (552 : ℚ) * X ^ 7 + C (3492 : ℚ) * X ^ 8 - C (936 : ℚ) * X ^ 9 + C (120 : ℚ) * X ^ 10 := by
      simp only [map_ofNat, map_one, pow_one]; ring
    rw [hq, hr]
    ext n
    simp only [map_add, map_sub, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    by_cases hn : n < 11
    · interval_cases n <;> norm_num [a]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
      simp only [show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega, show m + 11 - 3 = m + 8 by omega, show m + 11 - 4 = m + 7 by omega, show m + 11 - 5 = m + 6 by omega, show m + 11 - 6 = m + 5 by omega, show m + 11 - 7 = m + 4 by omega, show m + 11 - 8 = m + 3 by omega, show m + 11 - 9 = m + 2 by omega, show m + 11 - 10 = m + 1 by omega, show m + 11 - 11 = m + 0 by omega, if_true]
      simp only [a]; push_cast; ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
    simp only [show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega, show m + 11 - 3 = m + 8 by omega, show m + 11 - 4 = m + 7 by omega, show m + 11 - 5 = m + 6 by omega, show m + 11 - 6 = m + 5 by omega, show m + 11 - 7 = m + 4 by omega, show m + 11 - 8 = m + 3 by omega, show m + 11 - 9 = m + 2 by omega, show m + 11 - 10 = m + 1 by omega, show m + 11 - 11 = m + 0 by omega]
    simp only [a]; push_cast; ring
