import OMAStatements.S_oeis_a282483
import Mathlib

/-!
# OEIS A282483: Barker's conjectures for the x-axis (origin to right edge, base 10) of Rule 478: the conjectured package is inconsistent

The denominator expands to `(1) X^0 + (-100) X^2 + (-1) X^4 + (100) X^6`, the denominator of the claimed recurrence. So the coefficient
of `X ^ 10` in the generating-function identity says that the recurrence combination at `n = 10`
equals `10000000`, while the claimed recurrence at `n = 10` says that it is `0`. So the conjunction of
the claims is false.
-/

open OMA.S_oeis_a282483 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282483.main) := by
  rintro ⟨hX, h⟩
  generalize a = f at h hX
  have := congrArg (coeff 10) h
  rw [show ∀ S : ℤ⟦X⟧, S * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + X ^ 2)) =
      S + X ^ 2 * S * C (-100) + X ^ 4 * S * C (-1) + X ^ 6 * S * C 100 from fun S => by simp; ring,
    show (1 + 11 * X - 89 * X ^ 2 + 11 * X ^ 3 - 1090 * X ^ 4 - 100000 * X ^ 5 + 1099000 * X ^ 6 + 10000000 * X ^ 10 : ℤ⟦X⟧) =
      X ^ 0 * C 1 + X ^ 1 * C 11 + X ^ 2 * C (-89) + X ^ 3 * C 11 + X ^ 4 * C (-1090) + X ^ 5 * C (-100000) + X ^ 6 * C 1099000 + X ^ 10 * C 10000000 from by simp; ring] at this
  simp only [map_add, map_sub, coeff_mul_C, coeff_X_pow_mul', coeff_X_pow, coeff_mk] at this
  have := hX 10 (by norm_num)
  norm_num at *
  omega
