import OMAStatements.S_oeis_a266612
import Mathlib

/-!
# A266612: Binary representation of the middle column of the Rule 41 elementary cellular automaton starting with a single ON (black) cell.: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 4` on both sides gives, one after the other,

  `a 0, …, a 4 = 1, 10, 101, 1010, 10100`.

But the claimed recurrence at `n = 4` evaluates to `10101` instead of `10100`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a266612 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a266612.main) := by
  rintro ⟨-, hX, hgf⟩
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) * (1 + X) * (1 - 10 * X))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-10 : ℤ) * (S * X ^ 1) + C (-1 : ℤ) * (S * X ^ 2) + C (10 : ℤ) * (S * X ^ 3) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : ((1 - X ^ 4 + X ^ 5) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (1 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : a 0 = 1 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 0 : ℕ) : ℤ) = 1)
  have v1 : a 1 = 10 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 1 : ℕ) : ℤ) = 10)
  have v2 : a 2 = 101 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 2 : ℕ) : ℤ) = 101)
  have v3 : a 3 = 1010 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 3 : ℕ) : ℤ) = 1010)
  have v4 : a 4 = 10100 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 4 : ℕ) : ℤ) = 10100)
  -- the claimed recurrence at `n = 4` contradicts these values
  have hr := hX 4 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4] at hr
