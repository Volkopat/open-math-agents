import OMAStatements.S_oeis_a284182
import Mathlib

/-!
# OEIS A284182: Barker's conjectures for the x-axis, from the origin to the right edge of the 2D Rule 813: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 13` on both sides gives, one after the other,

  `a 0, …, a 13 = 1, 1, 5, 5, 29, 61, 117, 213, 381, 509, 2037, 4053, 8061, 16381`.

But the claimed recurrence at `n = 13` evaluates to `15869` instead of `16381`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a284182 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284182.main) := by
  rintro ⟨hX, hgf⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) * (1 + X) * (1 - 2 * X) * (1 + X ^ 2))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-2 : ℤ) * (S * X ^ 1) + C (-1 : ℤ) * (S * X ^ 4) + C (2 : ℤ) * (S * X ^ 5) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((1 - X + 3 * X ^ 2 - 5 * X ^ 3 + 18 * X ^ 4 + 4 * X ^ 5 - 8 * X ^ 6 - 16 * X ^ 7 - 64 * X ^ 8 - 256 * X ^ 9 + 1024 * X ^ 10 + 512 * X ^ 13 - 1024 * X ^ 14 : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 1 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (3 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (-5 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (18 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (-8 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (-16 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (-64 : ℤ) + (X ^ 9 : PowerSeries ℤ) * C (-256 : ℤ) + (X ^ 10 : PowerSeries ℤ) * C (1024 : ℤ) + (X ^ 13 : PowerSeries ℤ) * C (512 : ℤ) + (X ^ 14 : PowerSeries ℤ) * C (-1024 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : f 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 0 : ℕ) : ℤ) = 1)
  have v1 : f 1 = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℕ) : ℤ) = 1)
  have v2 : f 2 = 5 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℕ) : ℤ) = 5)
  have v3 : f 3 = 5 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℕ) : ℤ) = 5)
  have v4 : f 4 = 29 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℕ) : ℤ) = 29)
  have v5 : f 5 = 61 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℕ) : ℤ) = 61)
  have v6 : f 6 = 117 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℕ) : ℤ) = 117)
  have v7 : f 7 = 213 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 7 : ℕ) : ℤ) = 213)
  have v8 : f 8 = 381 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 8 : ℕ) : ℤ) = 381)
  have v9 : f 9 = 509 := by
    have h := congrArg (PowerSeries.coeff 9) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 9 : ℕ) : ℤ) = 509)
  have v10 : f 10 = 2037 := by
    have h := congrArg (PowerSeries.coeff 10) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 10 : ℕ) : ℤ) = 2037)
  have v11 : f 11 = 4053 := by
    have h := congrArg (PowerSeries.coeff 11) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 11 : ℕ) : ℤ) = 4053)
  have v12 : f 12 = 8061 := by
    have h := congrArg (PowerSeries.coeff 12) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 12 : ℕ) : ℤ) = 8061)
  have v13 : f 13 = 16381 := by
    have h := congrArg (PowerSeries.coeff 13) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 13 : ℕ) : ℤ) = 16381)
  -- the claimed recurrence at `n = 13` contradicts these values
  have hr := hX 13 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] at hr
