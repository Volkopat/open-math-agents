import OMAStatements.S_oeis_a108475

open OMA.S_oeis_a108475 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a108475.main := by
  have key : mk (fun n => (pell (n + 1) * pellLucas n : ℚ)) *
      (1 - 5 * X - 5 * X ^ 2 + X ^ 3 : PowerSeries ℚ) = 1 - 3 * X := by
    ext (_ | _ | _ | m) <;> simp [mul_sub, mul_add, ← map_ofNat C, ← mul_assoc, coeff_mul_X_pow',
      mul_comm _ (C _), pell, pellLucas, coeff_one] <;> ring
  intro n
  rw [a, ← key, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp), mul_one, coeff_mk]
