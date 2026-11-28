import OMAStatements.S_oeis_a239358
import Mathlib

/-!
# OEIS A239358: Barker's conjectures for n X 5 0..2 arrays with no element equal to one plus the sum of elements to its left or one plus the sum of elements above it or one plus the sum of the elements diagonally to its northwest, modulo 3: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 1, …, X ^ 6` on both sides gives, one after the other,

  `a 1, …, a 6 = 6, 16, 32, 60, 106, 156`.

But the claimed recurrence at `n = 6` evaluates to `176` instead of `156`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a239358 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a239358.main) := by
  rintro ⟨hgf, hX⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℚ, S * ((1 - X) ^ 4) =
      C (1 : ℚ) * (S * X ^ 0) + C (-4 : ℚ) * (S * X ^ 1) + C (6 : ℚ) * (S * X ^ 2) + C (-4 : ℚ) * (S * X ^ 3) + C (1 : ℚ) * (S * X ^ 4) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : ((X * (6 - 8 * X + 4 * X ^ 2 + 4 * X ^ 3 - 20 * X ^ 5 + 22 * X ^ 6 - X ^ 7 - 7 * X ^ 8 + 6 * X ^ 9 + X ^ 11)) : PowerSeries ℚ) =
      (X ^ 1 : PowerSeries ℚ) * C (6 : ℚ) + (X ^ 2 : PowerSeries ℚ) * C (-8 : ℚ) + (X ^ 3 : PowerSeries ℚ) * C (4 : ℚ) + (X ^ 4 : PowerSeries ℚ) * C (4 : ℚ) + (X ^ 6 : PowerSeries ℚ) * C (-20 : ℚ) + (X ^ 7 : PowerSeries ℚ) * C (22 : ℚ) + (X ^ 8 : PowerSeries ℚ) * C (-1 : ℚ) + (X ^ 9 : PowerSeries ℚ) * C (-7 : ℚ) + (X ^ 10 : PowerSeries ℚ) * C (6 : ℚ) + (X ^ 12 : PowerSeries ℚ) * C (1 : ℚ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v1 : f 1 = 6 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℕ) : ℚ) = 6)
  have v2 : f 2 = 16 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℕ) : ℚ) = 16)
  have v3 : f 3 = 32 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℕ) : ℚ) = 32)
  have v4 : f 4 = 60 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℕ) : ℚ) = 60)
  have v5 : f 5 = 106 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℕ) : ℚ) = 106)
  have v6 : f 6 = 156 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℕ) : ℚ) = 156)
  -- the claimed recurrence at `n = 6` contradicts these values
  have hr := hX 6 (by first | decide | norm_num)
  norm_num [v1, v2, v3, v4, v5, v6] at hr
