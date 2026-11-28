import OMAStatements.S_oeis_a271648
import Mathlib

/-!
# OEIS A271648: Barker's conjectures for the permutations containing 2143...(2n)(2n-1): the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 8` on both sides gives, one after the other,

  `a 0, …, a 8 = 6, 119, 2279, 18042, 83921, 284428, 782795, 1859374, 3957717`.

But the claimed recurrence at `n = 8` evaluates to `3957716` instead of `3957717`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a271648 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a271648.main) := by
  rintro ⟨hX, hgf⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) ^ 7)) =
      C (1 : ℤ) * (S * X ^ 0) + C (-7 : ℤ) * (S * X ^ 1) + C (21 : ℤ) * (S * X ^ 2) + C (-35 : ℤ) * (S * X ^ 3) + C (35 : ℤ) * (S * X ^ 4) + C (-21 : ℤ) * (S * X ^ 5) + C (7 : ℤ) * (S * X ^ 6) + C (-1 : ℤ) * (S * X ^ 7) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((6 + 77 * X + 1572 * X ^ 2 + 4378 * X ^ 3 + 1531 * X ^ 4 + 137 * X ^ 5 - 22 * X ^ 6 + X ^ 8 : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (6 : ℤ) + (X ^ 1 : PowerSeries ℤ) * C (77 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (1572 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (4378 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (1531 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (137 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (-22 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (1 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : f 0 = 6 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 0 : ℕ) : ℤ) = 6)
  have v1 : f 1 = 119 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 1 : ℕ) : ℤ) = 119)
  have v2 : f 2 = 2279 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℕ) : ℤ) = 2279)
  have v3 : f 3 = 18042 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℕ) : ℤ) = 18042)
  have v4 : f 4 = 83921 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℕ) : ℤ) = 83921)
  have v5 : f 5 = 284428 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℕ) : ℤ) = 284428)
  have v6 : f 6 = 782795 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 6 : ℕ) : ℤ) = 782795)
  have v7 : f 7 = 1859374 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 7 : ℕ) : ℤ) = 1859374)
  have v8 : f 8 = 3957717 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 8 : ℕ) : ℤ) = 3957717)
  -- the claimed recurrence at `n = 8` contradicts these values
  have hr := hX 8 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8] at hr
