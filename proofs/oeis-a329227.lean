import OMAStatements.S_oeis_a329227
import Mathlib

open OMA.S_oeis_a329227 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a329227.main := by
  rw [show ((1 - 2 * X + X ^ 2 - X ^ 3) * (1 + X - X ^ 3) : ℤ⟦X⟧) =
    1 - X ^ 1 - X ^ 2 - X ^ 3 + X ^ 4 - X ^ 5 + X ^ 6 by ring]
  ext (_ | _ | _ | _ | _ | _ | m) <;> simp [mul_sub, mul_add, coeff_mul_X_pow', coeff_X_pow, a, P] <;> ring
