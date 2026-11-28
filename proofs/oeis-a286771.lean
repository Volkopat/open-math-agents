import OMAStatements.S_oeis_a286771
import Mathlib

/-!
# OEIS A286771: Binary representation of the diagonal from the origin to the corner of Rule 221: the conjectured package is inconsistent

The denominator expands to `(1) X^0 + (-101) X^2 + (100) X^4`, the denominator of the claimed recurrence. So the coefficient
of `X ^ 6` in the generating-function identity says that the recurrence combination at `n = 6`
equals `-10000`, while the claimed recurrence at `n = 6` says that it is `0`. So the conjunction of
the claims is false.
-/

open OMA.S_oeis_a286771 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a286771.main) := by
  rintro ⟨h, -, -, hX⟩
  generalize a = f at h hX
  have := congrArg (coeff 6) h
  rw [show ∀ S : ℤ⟦X⟧, S * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      S + X ^ 2 * S * C (-101) + X ^ 4 * S * C 100 from fun S => by simp; ring,
    show (1 + X - 101 * X ^ 2 + 10 * X ^ 3 + 10100 * X ^ 4 - 10000 * X ^ 6 : ℤ⟦X⟧) =
      X ^ 0 * C 1 + X ^ 1 * C 1 + X ^ 2 * C (-101) + X ^ 3 * C 10 + X ^ 4 * C 10100 + X ^ 6 * C (-10000) from by simp; ring] at this
  simp only [map_add, map_sub, coeff_mul_C, coeff_X_pow_mul', coeff_X_pow, coeff_mk] at this
  have := hX 6 (by norm_num)
  norm_num at *
  omega
