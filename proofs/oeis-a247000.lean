import OMAStatements.S_oeis_a247000
import Mathlib

/-!
# A247000: maximal number of palindromes in a circular binary word of length n: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 1, …, X ^ 7` on both sides gives, one after the other,

  `a 1, …, a 7 = 1, 2, 4, 6, 7, 9, 10`.

But the claimed recurrence at `n = 7` evaluates to `11` instead of `10`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a247000 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a247000.main) := by
  rintro ⟨hX, hgf⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((X - 1) ^ 2 * (X ^ 2 + X + 1))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-1 : ℤ) * (S * X ^ 1) + C (-1 : ℤ) * (S * X ^ 3) + C (1 : ℤ) * (S * X ^ 4) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((X * (X ^ 13 - X ^ 12 + X ^ 11 - X ^ 10 + X ^ 9 - X ^ 8 + X ^ 7 - X ^ 6 + X ^ 3 + 2 * X ^ 2 + X + 1) : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 1 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (2 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 9 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 10 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 11 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 12 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 13 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 14 : PowerSeries ℤ) * C (1 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v1 : f 1 = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℕ) : ℤ) = 1)
  have v2 : f 2 = 2 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℕ) : ℤ) = 2)
  have v3 : f 3 = 4 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℕ) : ℤ) = 4)
  have v4 : f 4 = 6 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℕ) : ℤ) = 6)
  have v5 : f 5 = 7 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℕ) : ℤ) = 7)
  have v6 : f 6 = 9 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℕ) : ℤ) = 9)
  have v7 : f 7 = 10 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 7 : ℕ) : ℤ) = 10)
  -- the claimed recurrence at `n = 7` contradicts these values
  have hr := hX 7 (by first | decide | norm_num)
  norm_num [v1, v2, v3, v4, v5, v6, v7] at hr
