import OMAStatements.S_oeis_a267156

/-!
# A267156: the conjectured package is inconsistent

Coefficient 10 of the generating-function identity reads
`a 10 - 10 a 9 - a 8 + 10 a 7 = -1`, while the claimed recurrence at `n = 10` says that the
same combination is `0`. So the conjunction of the claims is false, whatever the sequence is.
-/

open OMA.S_oeis_a267156 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267156.main) := by
  rintro ⟨-, h, g⟩
  rw [show ∀ A : PowerSeries ℤ, A * ((1 - X) * (1 + X) * (1 - 10 * X)) =
    A - C 10 * (A * X ^ 1) - A * X ^ 2 + C 10 * (A * X ^ 3) by intro; simp; ring] at g
  have := congrArg (coeff 10) g
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow'] at this
  simp [coeff_X_pow] at this
  linarith [h 10 (by norm_num)]
