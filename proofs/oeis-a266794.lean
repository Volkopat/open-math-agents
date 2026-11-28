import OMAStatements.S_oeis_a266794
import Mathlib

/-!
# A266794: Number of OFF (white) cells in the n-th iteration of the Rule 61 elementary cellular automaton starting with a single ON (black) cell.: the conjectured package is inconsistent

The generating-function identity determines the sequence completely.  Comparing the
coefficients of `X ^ 0, …, X ^ 8` on both sides gives, one after the other,

  `a 0, …, a 8 = 0, 1, 3, 2, 5, 4, 8, 4, 12`.

But the claimed recurrence at `n = 8` evaluates to `11` instead of `12`.
So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a266794 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a266794.main) := by
  rintro ⟨-, hX, hgf⟩
  -- expand both polynomials into monomials
  have el : ∀ S : PowerSeries ℤ, S * (((1 - X) ^ 2 * (1 + X) ^ 2)) =
      C (1 : ℤ) * (S * X ^ 0) + C (-2 : ℤ) * (S * X ^ 2) + C (1 : ℤ) * (S * X ^ 4) := by
    intro S
    simp only [map_neg, map_one, map_ofNat]
    ring
  have er : ((X * (1 + 3 * X - X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7)) : PowerSeries ℤ) =
      (X ^ 1 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 2 : PowerSeries ℤ) * C (3 : ℤ) + (X ^ 4 : PowerSeries ℤ) * C (-1 : ℤ) + (X ^ 5 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 6 : PowerSeries ℤ) * C (1 : ℤ) + (X ^ 7 : PowerSeries ℤ) * C (-2 : ℤ) + (X ^ 8 : PowerSeries ℤ) * C (1 : ℤ) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [el, er] at hgf
  -- read off the coefficients one at a time
  have v0 : a 0 = 0 := by
    have h := congrArg (PowerSeries.coeff 0) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 0 : ℕ) : ℤ) = 0)
  have v1 : a 1 = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 1 : ℕ) : ℤ) = 1)
  have v2 : a 2 = 3 := by
    have h := congrArg (PowerSeries.coeff 2) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 2 : ℕ) : ℤ) = 3)
  have v3 : a 3 = 2 := by
    have h := congrArg (PowerSeries.coeff 3) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 3 : ℕ) : ℤ) = 2)
  have v4 : a 4 = 5 := by
    have h := congrArg (PowerSeries.coeff 4) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 4 : ℕ) : ℤ) = 5)
  have v5 : a 5 = 4 := by
    have h := congrArg (PowerSeries.coeff 5) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 5 : ℕ) : ℤ) = 4)
  have v6 : a 6 = 8 := by
    have h := congrArg (PowerSeries.coeff 6) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 6 : ℕ) : ℤ) = 8)
  have v7 : a 7 = 4 := by
    have h := congrArg (PowerSeries.coeff 7) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 7 : ℕ) : ℤ) = 4)
  have v8 : a 8 = 12 := by
    have h := congrArg (PowerSeries.coeff 8) hgf
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, PowerSeries.coeff_mk] at h
    simp [v0, v1, v2, v3, v4, v5, v6, v7] at h
    first | omega | linarith | exact_mod_cast (by linarith : ((a 8 : ℕ) : ℤ) = 12)
  -- the claimed recurrence at `n = 8` contradicts these values
  have hr := hX 8 (by first | decide | norm_num)
  norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8] at hr
