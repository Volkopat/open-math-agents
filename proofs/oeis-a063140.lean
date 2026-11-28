import OMAStatements.S_oeis_a063140
import Mathlib

/-!
# A063140: the exponential generating function of `0, 5, 28, 52, 76, …`

Expanding `20 + X + 4 eˣ (6X - 5) = 20 + X + 24 X eˣ - 20 eˣ`, the coefficient of `Xⁿ` is

* `20 - 20 = 0` for `n = 0`,
* `1 + 24 - 20 = 5` for `n = 1`,
* `24 / (n-1)! - 20 / n! = (24 n - 20) / n!` for `n ≥ 2`,

which is `a n / n!` in each case.
-/

open OMA.S_oeis_a063140 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a063140.main := by
  have er : (20 + X + 4 * exp ℚ * (6 * X - 5) : PowerSeries ℚ) =
      X ^ 0 * C 20 + X ^ 1 * C 1 + C 24 * (exp ℚ * X ^ 1) - C 20 * (exp ℚ * X ^ 0) := by
    simp only [map_ofNat, map_one]
    ring
  rw [er]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, coeff_mk,
    coeff_exp]
  rcases n with _ | _ | n
  · simp [a]
  · simp [a]
    norm_num
  · have h1 : n + 2 - 1 = n + 1 := rfl
    have h0 : n + 2 - 0 = n + 2 := rfl
    have hf : ((n + 2).factorial : ℚ) = ((n : ℚ) + 2) * ((n + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hpos : ((n + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [h1, h0]
    simp [a, hf]
    field_simp
    ring
