import OMAStatements.S_oeis_a246919
import Mathlib

/-!
# A246919: longest nontrivial integral cevian of an equilateral triangle of side n: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 1, …, X ^ 16` on both sides gives, one after the other,

  `a 1, …, a 16 = 0, 0, 7, 0, 19, 14, 37, 13, 61, 38, 91, 28, 127, 74, 169, 49`.

But the claimed recurrence at `n = 16` evaluates to `45` instead of `49`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a246919 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a246919.main) := by
  rintro ⟨hX, hgf⟩
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) ^ 3 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 3)) =
      C (1 : ℤ) * (S * X ^ 0) + C (-3 : ℤ) * (S * X ^ 4) + C (3 : ℤ) * (S * X ^ 8) + C (-1 : ℤ) * (S * X ^ 12) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((X ^ 3 * (7 + 19 * X ^ 2 + 14 * X ^ 3 + 16 * X ^ 4 + 13 * X ^ 5 + 4 * X ^ 6 - 4 * X ^ 7 + X ^ 8 - 11 * X ^ 9 + X ^ 10 + 2 * X ^ 11 + 4 * X ^ 13) : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 3 : PowerSeries ℤ) * C (7 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (19 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (14 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (16 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (13 : ℤ) + (X ^ 9 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 10 : PowerSeries ℤ) * C (-4 : ℤ) + (X ^ 11 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 12 : PowerSeries ℤ) * C (-11 : ℤ) + (X ^ 13 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 14 : PowerSeries ℤ) * C (2 : ℤ) + (X ^ 16 : PowerSeries ℤ) * C (4 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v1 : a 1 = 0 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 1 : ℕ) : ℤ) = 0)
  have v2 : a 2 = 0 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 2 : ℕ) : ℤ) = 0)
  have v3 : a 3 = 7 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 3 : ℕ) : ℤ) = 7)
  have v4 : a 4 = 0 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 4 : ℕ) : ℤ) = 0)
  have v5 : a 5 = 19 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 5 : ℕ) : ℤ) = 19)
  have v6 : a 6 = 14 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 6 : ℕ) : ℤ) = 14)
  have v7 : a 7 = 37 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 7 : ℕ) : ℤ) = 37)
  have v8 : a 8 = 13 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6, v7] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 8 : ℕ) : ℤ) = 13)
  have v9 : a 9 = 61 := by
    have h := congrArg (PowerSeries.coeff 9) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6, v7, v8] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 9 : ℕ) : ℤ) = 61)
  have v10 : a 10 = 38 := by
    have h := congrArg (PowerSeries.coeff 10) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6, v7, v8, v9] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 10 : ℕ) : ℤ) = 38)
  have v11 : a 11 = 91 := by
    have h := congrArg (PowerSeries.coeff 11) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 11 : ℕ) : ℤ) = 91)
  have v12 : a 12 = 28 := by
    have h := congrArg (PowerSeries.coeff 12) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 12 : ℕ) : ℤ) = 28)
  have v13 : a 13 = 127 := by
    have h := congrArg (PowerSeries.coeff 13) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 13 : ℕ) : ℤ) = 127)
  have v14 : a 14 = 74 := by
    have h := congrArg (PowerSeries.coeff 14) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 14 : ℕ) : ℤ) = 74)
  have v15 : a 15 = 169 := by
    have h := congrArg (PowerSeries.coeff 15) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 15 : ℕ) : ℤ) = 169)
  have v16 : a 16 = 49 := by
    have h := congrArg (PowerSeries.coeff 16) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 16 : ℕ) : ℤ) = 49)
  -- the claimed recurrence at `n = 16` contradicts these values
  have hr := hX 16 (by first | decide | norm_num)
  norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16] at hr
