import OMAStatements.S_oeis_a282915
import Mathlib

/-!
# OEIS A282915: Barker's conjectures for the x-axis (left edge to origin, base 10) of Rule 529: the conjectured package is inconsistent

The denominator expands to `(1) X^0 + (-1) X^2 + (-10000) X^4 + (10000) X^6`, the denominator of the claimed recurrence. So the coefficient
of `X ^ 10` in the generating-function identity says that the recurrence combination at `n = 10`
equals `-1000`, while the claimed recurrence at `n = 10` says that it is `0`. So the conjunction of
the claims is false.
-/

open OMA.S_oeis_a282915 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282915.main) := by
  rintro ⟨hX, h⟩
  generalize a = f at h hX
  have := congrArg (coeff 10) h
  rw [show ∀ S : ℤ⟦X⟧, S * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2)) =
      S + X ^ 2 * S * C (-1) + X ^ 4 * S * C (-10000) + X ^ 6 * S * C 10000 from fun S => by simp; ring,
    show (1 - 9890 * X ^ 4 + X ^ 5 + 10989 * X ^ 6 - 1000 * X ^ 10 : ℤ⟦X⟧) =
      X ^ 0 * C 1 + X ^ 4 * C (-9890) + X ^ 5 * C 1 + X ^ 6 * C 10989 + X ^ 10 * C (-1000) from by simp; ring] at this
  simp only [map_add, map_sub, coeff_mul_C, coeff_X_pow_mul', coeff_X_pow, coeff_mk] at this
  have := hX 10 (by norm_num)
  norm_num at *
  omega
