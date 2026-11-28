import OMAStatements.S_oeis_a267589
import Mathlib

/-!
# A267589: Decimal representation of the middle column of the Rule 169 elementary cellular automaton starting with a single ON (black) cell.: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 5` on both sides gives, one after the other,

  `a 0, …, a 5 = 1, 2, 5, 10, 20, 41`.

But the claimed recurrence at `n = 5` evaluates to `40` instead of `41`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a267589 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267589.main) := by
  rintro ⟨hX, hgf⟩
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) * (1 - 2 * X))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-3 : ℤ) * (S * X ^ 1) + C (2 : ℤ) * (S * X ^ 2) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : ((1 - X + X ^ 2 - X ^ 3 + X ^ 5) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 1 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (1 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : a 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 0 : ℕ) : ℤ) = 1)
  have v1 : a 1 = 2 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 1 : ℕ) : ℤ) = 2)
  have v2 : a 2 = 5 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 2 : ℕ) : ℤ) = 5)
  have v3 : a 3 = 10 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 3 : ℕ) : ℤ) = 10)
  have v4 : a 4 = 20 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 4 : ℕ) : ℤ) = 20)
  have v5 : a 5 = 41 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 5 : ℕ) : ℤ) = 41)
  -- the claimed recurrence at `n = 5` contradicts these values
  have hr := hX 5 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5] at hr
