import OMAStatements.S_oeis_a110320
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a110320.main := by
  intro S A B C _ _ hA hB hC n _
  have e1 : 2 * X ^ 2 * A = C - X * C - X ^ 2 * C - 1 := by
    linear_combination C * hA - (2 * X ^ 2 * A + 1) * hC
  have e2 : B = C - X ^ 2 * C + 1 := by
    linear_combination C * hB + (1 - B) * hC
  have c1 := congrArg (coeff (n + 2)) e1
  have c2 := congrArg (coeff (n + 2)) e2
  have l1 : coeff (n + 2) (2 * X ^ 2 * A) = 2 * coeff n A := by
    rw [show (2 * X ^ 2 * A : ℚ⟦X⟧) = X ^ 2 * A + X ^ 2 * A by ring, map_add, coeff_X_pow_mul']
    simp; ring
  have l3 : coeff (n + 2) (X * C) = coeff (n + 1) C := by rw [mul_comm, coeff_succ_mul_X]
  have l4 : coeff (n + 2) (X ^ 2 * C) = coeff n C := by
    rw [coeff_X_pow_mul']; simp
  have l5 : coeff (n + 2) (1 : ℚ⟦X⟧) = 0 := by simp [coeff_one]
  rw [l1, map_sub, map_sub, map_sub, l3, l4, l5] at c1
  rw [map_add, map_sub, l4, l5] at c2
  rw [c2]
  linarith
