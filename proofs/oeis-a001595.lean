import OMAStatements.S_oeis_a001595
import Mathlib

open OMA.S_oeis_a001595 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a001595.main := by
  have h : mk a * (1 - 2 * (X : ℤ⟦X⟧) + X ^ 3) = 1 - X + X ^ 2 := by
    ext n
    rcases n with _ | _ | _ | n <;>
    simp [mul_add, mul_sub, ← mul_assoc, pow_succ, two_mul, a, coeff_X, coeff_one]
    ring
  exact ⟨h, by linear_combination h⟩
