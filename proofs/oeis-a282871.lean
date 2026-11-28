import OMAStatements.S_oeis_a282871
import Mathlib

/-!
# OEIS A282871: Barker's conjectures for the x-axis (left edge to origin, base 10) of Rule 617: the conjectured package is inconsistent

The denominator expands to `(1) X^0 + (-1) X^1 + (-100) X^2 + (100) X^3`, the denominator of the claimed recurrence. So the coefficient
of `X ^ 6` in the generating-function identity says that the recurrence combination at `n = 6`
equals `100`, while the claimed recurrence at `n = 6` says that it is `0`. So the conjunction of
the claims is false.
-/

open OMA.S_oeis_a282871 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282871.main) := by
  rintro ⟨h, -, hX⟩
  generalize a = f at h hX
  have := congrArg (coeff 6) h
  rw [show ∀ S : ℤ⟦X⟧, S * ((1 - X) * (1 - 10 * X) * (1 + 10 * X)) =
      S + X ^ 1 * S * C (-1) + X ^ 2 * S * C (-100) + X ^ 3 * S * C 100 from fun S => by simp; ring,
    show (1 - X - 89 * X ^ 2 + 90 * X ^ 3 + 9 * X ^ 4 + 100 * X ^ 6 : ℤ⟦X⟧) =
      X ^ 0 * C 1 + X ^ 1 * C (-1) + X ^ 2 * C (-89) + X ^ 3 * C 90 + X ^ 4 * C 9 + X ^ 6 * C 100 from by simp; ring] at this
  simp only [map_add, map_sub, coeff_mul_C, coeff_X_pow_mul', coeff_X_pow, coeff_mk] at this
  have := hX 6 (by norm_num)
  norm_num at *
  omega
