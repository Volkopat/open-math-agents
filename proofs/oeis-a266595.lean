import OMAStatements.S_oeis_a266595
import Mathlib

/-!
# OEIS A266595: Barker's conjectures for the OFF cells of Rule 37: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 5` on both sides gives, one after the other,

  `a 0, …, a 5 = 0, 2, 2, 5, 6, 5`.

But the claimed recurrence at `n = 5` evaluates to `8` instead of `5`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a266595 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a266595.main) := by
  rintro ⟨-, hX, hgf⟩
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) ^ 2 * (1 + X) ^ 2)) =
      C (1 : ℤ) * (S * X ^ 0) + C (-2 : ℤ) * (S * X ^ 2) + C (1 : ℤ) * (S * X ^ 4) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((X * (2 + 2 * X + X ^ 2 + 2 * X ^ 3 - 3 * X ^ 4) : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 1 : PowerSeries ℤ) * C (2 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (2 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (2 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (-3 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : a 0 = 0 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 0 : ℕ) : ℤ) = 0)
  have v1 : a 1 = 2 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 1 : ℕ) : ℤ) = 2)
  have v2 : a 2 = 2 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 2 : ℕ) : ℤ) = 2)
  have v3 : a 3 = 5 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 3 : ℕ) : ℤ) = 5)
  have v4 : a 4 = 6 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 4 : ℕ) : ℤ) = 6)
  have v5 : a 5 = 5 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 5 : ℕ) : ℤ) = 5)
  -- the claimed recurrence at `n = 5` contradicts these values
  have hr := hX 5 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5] at hr
