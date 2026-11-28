import OMAStatements.S_oeis_a283752
import Mathlib

/-!
# OEIS A283752: Barker's conjectures for the x-axis (left edge to origin, base 2) of Rule 758: the conjectured package is inconsistent

The denominator expands to `1 - X - 16 X^4 + 16 X^5`, so the coefficient of `X ^ 6` in the
generating-function identity reads `a 6 - a 5 - 16 a 2 + 16 a 1 = 8`. The claimed recurrence at
`n = 6` says that the same combination is `0`. So the conjunction of the claims is false.
-/

open OMA.S_oeis_a283752 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a283752.main) := by
  rintro ⟨h, hX⟩
  have := congrArg (coeff 6) h
  rw [show ∀ S : ℤ⟦X⟧, S * ((1 - X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2)) =
      S - X ^ 1 * S - X ^ 4 * S * C 16 + X ^ 5 * S * C 16 from fun S => by simp; ring,
    show ((1 + 2 * X ^ 2) * (1 + 2 * X + 4 * X ^ 3 - 8 * X ^ 4 - 8 * X ^ 5 + 24 * X ^ 6) :
      ℤ⟦X⟧) = X ^ 6 * C 8 + X ^ 7 * (X * 48 - 16) + (1 + X ^ 1 * C 2 + X ^ 2 * C 2 +
        X ^ 3 * C 8 - X ^ 4 * C 8) from by simp; ring] at this
  simp only [map_add, map_sub, coeff_mul_C, coeff_X_pow_mul', coeff_X_pow, coeff_one] at this
  have := hX 6 (by norm_num)
  simp_all
  omega
