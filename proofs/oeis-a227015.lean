import OMAStatements.S_oeis_a227015
import Mathlib

/-!
# Floors of harmonic means of successive cubic intervals: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 8` on both sides gives, one after the other,

  `a 0, …, a 8 = 0, 2, 8, 26, 60, 117, 203, 324, 487`.

But the claimed recurrence at `n = 8` evaluates to `484` instead of `487`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a227015 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a227015.main) := by
  rintro ⟨hX, hgf, -, -⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((X-1)^4 * (1 + X + X^2 + X^3))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-3 : ℤ) * (S * X ^ 1) + C (3 : ℤ) * (S * X ^ 2) + C (-1 : ℤ) * (S * X ^ 3) + C (-1 : ℤ) * (S * X ^ 4) + C (3 : ℤ) * (S * X ^ 5) + C (-3 : ℤ) * (S * X ^ 6) + C (1 : ℤ) * (S * X ^ 7) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : ((X * (2 + 2*X + 8*X^2 + 4*X^3 + 5*X^4 + 4*X^5 - 2*X^6 + 3*X^7 - 3*X^8 + X^9)) : PowerSeries ℤ) =
      (X ^ 1 : PowerSeries ℤ) * C (2 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (2 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (8 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (5 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (-2 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (3 : ℤ) + (X ^ 9 : PowerSeries ℤ) * C (-3 : ℤ) + (X ^ 10 : PowerSeries ℤ) * C (1 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : f 0 = 0 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 0 : ℤ) : ℤ) = 0)
  have v1 : f 1 = 2 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℤ) : ℤ) = 2)
  have v2 : f 2 = 8 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℤ) : ℤ) = 8)
  have v3 : f 3 = 26 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℤ) : ℤ) = 26)
  have v4 : f 4 = 60 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℤ) : ℤ) = 60)
  have v5 : f 5 = 117 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℤ) : ℤ) = 117)
  have v6 : f 6 = 203 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℤ) : ℤ) = 203)
  have v7 : f 7 = 324 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 7 : ℤ) : ℤ) = 324)
  have v8 : f 8 = 487 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 8 : ℤ) : ℤ) = 487)
  -- the claimed recurrence at `n = 8` contradicts these values
  have hr := hX 8 (by first | decide | norm_num) (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8] at hr
