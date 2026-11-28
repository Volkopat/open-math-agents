import OMAStatements.S_oeis_a271489
import Mathlib

/-!
# OEIS A271489: Barker's conjectures for the maximal term of the TRIP-Stern sequence (e,132,e): the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 10` on both sides gives, one after the other,

  `a 0, …, a 10 = 1, 2, 3, 4, 5, 7, 10, 13, 18, 25, 34`.

But the claimed recurrence at `n = 10` evaluates to `33` instead of `34`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a271489 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a271489.main) := by
  rintro ⟨hX, hgf⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - 2 * X ^ 3 - X ^ 6 - X ^ 9))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-2 : ℤ) * (S * X ^ 3) + C (-1 : ℤ) * (S * X ^ 6) + C (-1 : ℤ) * (S * X ^ 9) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : ((((1 + 2 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 8 + X ^ 10 - X ^ 13) : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 1 : PowerSeries ℤ) * C (2 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (3 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (2 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 10 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 13 : PowerSeries ℤ) * C (-1 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : f 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 0 : ℕ) : ℤ) = 1)
  have v1 : f 1 = 2 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℕ) : ℤ) = 2)
  have v2 : f 2 = 3 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℕ) : ℤ) = 3)
  have v3 : f 3 = 4 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℕ) : ℤ) = 4)
  have v4 : f 4 = 5 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℕ) : ℤ) = 5)
  have v5 : f 5 = 7 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℕ) : ℤ) = 7)
  have v6 : f 6 = 10 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℕ) : ℤ) = 10)
  have v7 : f 7 = 13 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 7 : ℕ) : ℤ) = 13)
  have v8 : f 8 = 18 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 8 : ℕ) : ℤ) = 18)
  have v9 : f 9 = 25 := by
    have h := congrArg (PowerSeries.coeff 9) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 9 : ℕ) : ℤ) = 25)
  have v10 : f 10 = 34 := by
    have h := congrArg (PowerSeries.coeff 10) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 10 : ℕ) : ℤ) = 34)
  -- the claimed recurrence at `n = 10` contradicts these values
  have hr := hX 10 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] at hr
