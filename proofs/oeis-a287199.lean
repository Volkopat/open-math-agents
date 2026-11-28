import OMAStatements.S_oeis_a287199
import Mathlib

/-!
# OEIS A287199: Decimal representation of the diagonal from the origin to the corner of Rule 259: the conjectured package is inconsistent

The denominator expands to `(1) X^0 + (-5) X^2 + (4) X^4`, the denominator of the claimed recurrence. So the coefficient
of `X ^ 5` in the generating-function identity says that the recurrence combination at `n = 5`
equals `12`, while the claimed recurrence at `n = 5` says that it is `0`. So the conjunction of
the claims is false.
-/

open OMA.S_oeis_a287199 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a287199.main) := by
  rintro ⟨h, -, -, hX⟩
  generalize a = f at h hX
  have := congrArg (coeff 5) h
  rw [show ∀ S : ℤ⟦X⟧, S * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      S + X ^ 2 * S * C (-5) + X ^ 4 * S * C 4 from fun S => by simp; ring,
    show (1 + 3 * X - X ^ 2 - 12 * X ^ 3 + 12 * X ^ 5 : ℤ⟦X⟧) =
      X ^ 0 * C 1 + X ^ 1 * C 3 + X ^ 2 * C (-1) + X ^ 3 * C (-12) + X ^ 5 * C 12 from by simp; ring] at this
  simp only [map_add, map_sub, coeff_mul_C, coeff_X_pow_mul', coeff_X_pow, coeff_mk] at this
  have := hX 5 (by norm_num)
  norm_num at *
  omega
