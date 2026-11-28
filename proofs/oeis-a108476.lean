import OMAStatements.S_oeis_a108476

open OMA.S_oeis_a108476 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a108476.main := by
  have key : mk (fun n => (A002605 (n + 1) * A026150 n : ℚ)) *
      (1 - 6 * X - 12 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ) = 1 - 4 * X := by
    ext (_ | _ | _ | m) <;> simp [mul_sub, mul_add, ← map_ofNat C, ← mul_assoc, coeff_mul_X_pow',
      mul_comm _ (C _), A002605, A026150, coeff_one] <;> ring
  intro n
  rw [a, ← key, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp), mul_one, coeff_mk]
