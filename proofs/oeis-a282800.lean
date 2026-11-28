import OMAStatements.S_oeis_a282800
import Mathlib

/-!
# OEIS A282800: Barker's conjectures for the x-axis, from the left edge to the origin of the 2D Rule 507: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 5` on both sides gives, one after the other,

  `a 0, …, a 5 = 1, 1, 111, 100, 11111, 10100`.

But the claimed recurrence at `n = 5` evaluates to `10000` instead of `10100`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a282800 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282800.main) := by
  rintro ⟨hX, hgf⟩
  -- from here on the sequence is an arbitrary function `f`
  generalize a = f at hgf hX
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-101 : ℤ) * (S * X ^ 2) + C (100 : ℤ) * (S * X ^ 4) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((1 + 2 * X) * (1 - X + 12 * X ^ 2 - 25 * X ^ 3 + 50 * X ^ 4 : PowerSeries ℤ)) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 1 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (10 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (100 : ℤ) := by
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
  have v2 : f 2 = 111 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 2 : ℕ) : ℤ) = 111)
  have v3 : f 3 = 100 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 3 : ℕ) : ℤ) = 100)
  have v4 : f 4 = 11111 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 4 : ℕ) : ℤ) = 11111)
  have v5 : f 5 = 10100 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((f 5 : ℕ) : ℤ) = 10100)
  -- the claimed recurrence at `n = 5` contradicts these values
  have hr := hX 5 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5] at hr
