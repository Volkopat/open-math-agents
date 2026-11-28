import OMAStatements.S_oeis_a282412
import Mathlib

/-!
# OEIS A282412: Barker's conjectures for the x-axis (origin to right edge, base 10) of Rule 467: the conjectured package is inconsistent

The denominator expands to `(1) X^0 + (-101) X^2 + (100) X^4`, the denominator of the claimed recurrence. So the coefficient
of `X ^ 5` in the generating-function identity says that the recurrence combination at `n = 5`
equals `1000`, while the claimed recurrence at `n = 5` says that it is `0`. So the conjunction of
the claims is false.
-/

open OMA.S_oeis_a282412 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282412.main) := by
  rintro ⟨-, hX, h⟩
  generalize a = f at h hX
  have := congrArg (coeff 5) h
  rw [show ∀ S : ℤ⟦X⟧, S * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      S + X ^ 2 * S * C (-101) + X ^ 4 * S * C 100 from fun S => by simp; ring,
    show (1 + 10 * X + 10 * X ^ 2 - 1010 * X ^ 3 + 1000 * X ^ 5 : ℤ⟦X⟧) =
      X ^ 0 * C 1 + X ^ 1 * C 10 + X ^ 2 * C 10 + X ^ 3 * C (-1010) + X ^ 5 * C 1000 from by simp; ring] at this
  simp only [map_add, map_sub, coeff_mul_C, coeff_X_pow_mul', coeff_X_pow, coeff_mk] at this
  have := hX 5 (by norm_num)
  norm_num at *
  omega
