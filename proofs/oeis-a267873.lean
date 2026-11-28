import OMAStatements.S_oeis_a267873
import Mathlib

/-!
# A267873: Number of ON (black) cells in the n-th iteration of the "Rule 235" elementary cellular automaton starting with a single ON (black) cell: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 4` on both sides gives, one after the other,

  `a 0, …, a 4 = 1, 1, 4, 7, 9`.

But the claimed recurrence at `n = 4` evaluates to `10` instead of `9`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a267873 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267873.main) := by
  rintro ⟨hX, hgf⟩
  -- clear the inverse
  have hmul : A * (((1 - X) ^ 2) : PowerSeries ℚ) = (1 - X + 3 * X ^ 2 - X ^ 4) := by
    rw [hgf, mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]
  clear hgf
  have hgf := hmul
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℚ, S * (((1 - X) ^ 2)) =
      C (1 : ℚ) * (S * X ^ 0) + C (-2 : ℚ) * (S * X ^ 1) + C (1 : ℚ) * (S * X ^ 2) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : (((1 - X + 3 * X ^ 2 - X ^ 4)) : PowerSeries ℚ) =
      (X ^ 0 : PowerSeries ℚ) * C (1 : ℚ) + (X ^ 1 : PowerSeries ℚ) * C (-1 : ℚ) + (X ^ 2 : PowerSeries ℚ) * C (3 : ℚ) + (X ^ 4 : PowerSeries ℚ) * C (-1 : ℚ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : a 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk, A] at h
    simp at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 0 : ℕ) : ℚ) = 1)
  have v1 : a 1 = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk, A] at h
    simp [v0] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 1 : ℕ) : ℚ) = 1)
  have v2 : a 2 = 4 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk, A] at h
    simp [v0, v1] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 2 : ℕ) : ℚ) = 4)
  have v3 : a 3 = 7 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk, A] at h
    simp [v0, v1, v2] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 3 : ℕ) : ℚ) = 7)
  have v4 : a 4 = 9 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk, A] at h
    simp [v0, v1, v2, v3] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 4 : ℕ) : ℚ) = 9)
  -- the claimed recurrence at `n = 4` contradicts these values
  have hr := hX 4 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4] at hr
