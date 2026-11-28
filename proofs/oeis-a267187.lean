import OMAStatements.S_oeis_a267187

/-!
# A267187: the conjectured package is inconsistent

The denominator `(1 - X) ^ 2 (1 + X) (1 + X ^ 2)` is `1 - X - X ^ 4 + X ^ 5`, so coefficient 8
of the generating-function identity reads `a 8 - a 7 - a 4 + a 3 = -1`, while the claimed
recurrence at `n = 8` says that the same combination is `0`. So the conjunction of the claims is
false, whatever the sequence is.
-/

open OMA.S_oeis_a267187 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267187.main) := by
  rintro ⟨h, g⟩
  rw [show ∀ A : PowerSeries ℤ, A * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2)) =
    A - A * X ^ 1 - A * X ^ 4 + A * X ^ 5 by intro; ring, show (X * (3 - 2 * X + 3 * X ^ 2 -
    4 * X ^ 3 + 3 * X ^ 4 - X ^ 7 - X ^ 8) : PowerSeries ℤ) = C 3 * X ^ 1 - C 2 * X ^ 2 +
    C 3 * X ^ 3 - C 4 * X ^ 4 + C 3 * X ^ 5 - X ^ 8 - X ^ 9 by simp; ring] at g
  have := congrArg (coeff 8) g
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_C] at this
  simp [coeff_X_pow] at this
  linarith [h 8 (by norm_num)]
