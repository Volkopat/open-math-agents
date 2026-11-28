import OMAStatements.S_oeis_a210377
import Mathlib

/-!
# A210377: number of 2 X 2 matrices with all terms in {0,1,...,n} and (sum of terms) = n + 5: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 7` on both sides gives, one after the other,

  `a 0, …, a 7 = 0, 0, 4, 31, 80, 146, 224, 315`.

But the claimed recurrence at `n = 7` evaluates to `309` instead of `315`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a210377 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a210377.main) := by
  rintro ⟨hgf, -, hX⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * ((1 - X) ^ 4) =
      C (1 : ℤ) * (S * X ^ 0) + C (-4 : ℤ) * (S * X ^ 1) + C (6 : ℤ) * (S * X ^ 2) + C (-4 : ℤ) * (S * X ^ 3) + C (1 : ℤ) * (S * X ^ 4) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((X ^ 2 * (4 + 15 * X - 20 * X ^ 2 - 4 * X ^ 3 + 6 * X ^ 5) : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 2 : PowerSeries ℤ) * C (4 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (15 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (-20 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (-4 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (6 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : f 0 = 0 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 0 : ℕ) : ℤ) = 0)
  have v1 : f 1 = 0 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℕ) : ℤ) = 0)
  have v2 : f 2 = 4 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℕ) : ℤ) = 4)
  have v3 : f 3 = 31 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℕ) : ℤ) = 31)
  have v4 : f 4 = 80 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℕ) : ℤ) = 80)
  have v5 : f 5 = 146 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℕ) : ℤ) = 146)
  have v6 : f 6 = 224 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℕ) : ℤ) = 224)
  have v7 : f 7 = 315 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 7 : ℕ) : ℤ) = 315)
  -- the claimed recurrence at `n = 7` contradicts these values
  have hr := hX 7 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7] at hr
