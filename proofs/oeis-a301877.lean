import OMAStatements.S_oeis_a301877
import Mathlib

/-!
# A301877: sums of the groups of natural numbers with Narayana-cows sizes: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 1, …, X ^ 11` on both sides gives, one after the other,

  `a 1, …, a 11 = 1, 2, 3, 4, 11, 24, 46, 99, 216, 455, 969`.

But the claimed recurrence at `n = 11` evaluates to `908` instead of `969`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a301877 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a301877.main) := by
  rintro ⟨hgf, hX⟩
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 + X ^ 2 - X ^ 3) * (1 - X - X ^ 3) * (1 - X - 2 * X ^ 2 - X ^ 3))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-2 : ℤ) * (S * X ^ 1) + C (-3 : ℤ) * (S * X ^ 3) + C (3 : ℤ) * (S * X ^ 4) + C (3 : ℤ) * (S * X ^ 5) + C (3 : ℤ) * (S * X ^ 6) + C (-1 : ℤ) * (S * X ^ 8) + C (-1 : ℤ) * (S * X ^ 9) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((X * (1 - X) * (1 + X - 5 * X ^ 3 - 5 * X ^ 4 - 3 * X ^ 5 + X ^ 6 + 2 * X ^ 7 + X ^ 8) : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 1 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (-5 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (2 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 9 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 10 : PowerSeries ℤ) * C (-1 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v1 : a 1 = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 1 : ℕ) : ℤ) = 1)
  have v2 : a 2 = 2 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 2 : ℕ) : ℤ) = 2)
  have v3 : a 3 = 3 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 3 : ℕ) : ℤ) = 3)
  have v4 : a 4 = 4 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 4 : ℕ) : ℤ) = 4)
  have v5 : a 5 = 11 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 5 : ℕ) : ℤ) = 11)
  have v6 : a 6 = 24 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 6 : ℕ) : ℤ) = 24)
  have v7 : a 7 = 46 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 7 : ℕ) : ℤ) = 46)
  have v8 : a 8 = 99 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6, v7] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 8 : ℕ) : ℤ) = 99)
  have v9 : a 9 = 216 := by
    have h := congrArg (PowerSeries.coeff 9) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6, v7, v8] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 9 : ℕ) : ℤ) = 216)
  have v10 : a 10 = 455 := by
    have h := congrArg (PowerSeries.coeff 10) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6, v7, v8, v9] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 10 : ℕ) : ℤ) = 455)
  have v11 : a 11 = 969 := by
    have h := congrArg (PowerSeries.coeff 11) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 11 : ℕ) : ℤ) = 969)
  -- the claimed recurrence at `n = 11` contradicts these values
  have hr := hX 11 (by first | decide | norm_num)
  norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] at hr
