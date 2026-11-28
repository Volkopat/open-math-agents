import OMAStatements.S_oeis_a284940
import Mathlib

/-!
# OEIS A284940: Barker's conjectures for the diagonal from the corner to the origin of the 2D Rule 107: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 8` on both sides gives, one after the other,

  `a 0, …, a 8 = 1, 11, 11, 1111, 110, 111111, 1100, 11111111, 11110`.

But the claimed recurrence at `n = 8` evaluates to `11000` instead of `11110`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a284940 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284940.main) := by
  rintro ⟨hX, hgf⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-111 : ℤ) * (S * X ^ 2) + C (1110 : ℤ) * (S * X ^ 4) + C (-1000 : ℤ) * (S * X ^ 6) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((1 + 11 * X - 100 * X ^ 2 - 110 * X ^ 3 - X ^ 4 + 100 * X ^ 6 + 110 * X ^ 8 - 11100 * X ^ 10 + 10000 * X ^ 12 : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 1 : PowerSeries ℤ) * C (11 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (-100 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (-110 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (100 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (110 : ℤ) + (X ^ 10 : PowerSeries ℤ) * C (-11100 : ℤ) + (X ^ 12 : PowerSeries ℤ) * C (10000 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : f 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 0 : ℕ) : ℤ) = 1)
  have v1 : f 1 = 11 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℕ) : ℤ) = 11)
  have v2 : f 2 = 11 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℕ) : ℤ) = 11)
  have v3 : f 3 = 1111 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℕ) : ℤ) = 1111)
  have v4 : f 4 = 110 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℕ) : ℤ) = 110)
  have v5 : f 5 = 111111 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℕ) : ℤ) = 111111)
  have v6 : f 6 = 1100 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℕ) : ℤ) = 1100)
  have v7 : f 7 = 11111111 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 7 : ℕ) : ℤ) = 11111111)
  have v8 : f 8 = 11110 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 8 : ℕ) : ℤ) = 11110)
  -- the claimed recurrence at `n = 8` contradicts these values
  have hr := hX 8 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8] at hr
