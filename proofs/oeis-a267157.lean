import OMAStatements.S_oeis_a267157
import Mathlib

/-!
# A267157: Decimal representation of the middle column of the Rule 107 elementary cellular automaton starting with a single ON (black) cell.: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 10` on both sides gives, one after the other,

  `a 0, …, a 10 = 1, 2, 4, 9, 19, 39, 79, 159, 319, 639, 1278`.

But the claimed recurrence at `n = 10` evaluates to `1279` instead of `1278`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a267157 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267157.main) := by
  rintro ⟨-, hX, hgf⟩
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) * (1 + X) * (1 - 2 * X))) =
      C (1 : ℤ) * (S * X ^ 0) + C (-2 : ℤ) * (S * X ^ 1) + C (-1 : ℤ) * (S * X ^ 2) + C (2 : ℤ) * (S * X ^ 3) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : ((1 - X ^ 2 + X ^ 3 + X ^ 4 - X ^ 10) : PowerSeries ℤ) =
      (X ^ 0 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 3 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 10 : PowerSeries ℤ) * C (-1 : ℤ) := by
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
  have v2 : a 2 = 4 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 2 : ℕ) : ℤ) = 4)
  have v3 : a 3 = 9 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 3 : ℕ) : ℤ) = 9)
  have v4 : a 4 = 19 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 4 : ℕ) : ℤ) = 19)
  have v5 : a 5 = 39 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 5 : ℕ) : ℤ) = 39)
  have v6 : a 6 = 79 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 6 : ℕ) : ℤ) = 79)
  have v7 : a 7 = 159 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 7 : ℕ) : ℤ) = 159)
  have v8 : a 8 = 319 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 8 : ℕ) : ℤ) = 319)
  have v9 : a 9 = 639 := by
    have h := congrArg (PowerSeries.coeff 9) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 9 : ℕ) : ℤ) = 639)
  have v10 : a 10 = 1278 := by
    have h := congrArg (PowerSeries.coeff 10) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] at h
    first | exact h | omega | exact_mod_cast (by linarith : ((a 10 : ℕ) : ℤ) = 1278)
  -- the claimed recurrence at `n = 10` contradicts these values
  have hr := hX 10 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] at hr
