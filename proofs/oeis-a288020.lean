import OMAStatements.S_oeis_a288020
import Mathlib

/-!
# OEIS A288020: Barker's conjectures for the diagonal (corner to origin, base 10) of Rule 501: the conjectured package is inconsistent

The denominator expands to `(1) X^0 + (-101) X^2 + (100) X^4`, the denominator of the claimed recurrence. So the coefficient
of `X ^ 6` in the generating-function identity says that the recurrence combination at `n = 6`
equals `-1000`, while the claimed recurrence at `n = 6` says that it is `0`. So the conjunction of
the claims is false.
-/

open OMA.S_oeis_a288020 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288020.main) := by
  rintro ⟨h, -, -, hX⟩
  generalize a = f at h hX
  have := congrArg (coeff 6) h
  rw [show ∀ S : ℤ⟦X⟧, S * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      S + X ^ 2 * S * C (-101) + X ^ 4 * S * C 100 from fun S => by simp; ring,
    show (1 + 10 * X - 100 * X ^ 2 + 100 * X ^ 3 + 10 * X ^ 4 - 1000 * X ^ 6 - 10 * X ^ 7 + 1000 * X ^ 9 : ℤ⟦X⟧) =
      X ^ 0 * C 1 + X ^ 1 * C 10 + X ^ 2 * C (-100) + X ^ 3 * C 100 + X ^ 4 * C 10 + X ^ 6 * C (-1000) + X ^ 7 * C (-10) + X ^ 9 * C 1000 from by simp; ring] at this
  simp only [map_add, map_sub, coeff_mul_C, coeff_X_pow_mul', coeff_X_pow, coeff_mk] at this
  have := hX 6 (by norm_num)
  norm_num at *
  omega
