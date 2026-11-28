import OMAStatements.S_oeis_a284178
import Mathlib

/-!
# A284178: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 809, based on the 5-celled von Neumann neighborhood.: the conjectured package is inconsistent

The denominator expands to `(1) X^0 + (-4) X^2 + (-1) X^8 + (4) X^10`, the denominator of the claimed recurrence. So the coefficient
of `X ^ 17` in the generating-function identity says that the recurrence combination at `n = 17`
equals `256`, while the claimed recurrence at `n = 17` says that it is `0`. So the conjunction of
the claims is false.
-/

open OMA.S_oeis_a284178 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284178.main) := by
  rintro ⟨h, hX⟩
  have := congrArg (coeff 17) h
  rw [show ∀ S : ℤ⟦X⟧, S * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + X ^ 2) * (1 + X ^ 4)) =
      S + X ^ 2 * S * C (-4) + X ^ 8 * S * C (-1) + X ^ 10 * S * C 4 from fun S => by simp; ring] at this
  simp only [← map_ofNat (C (R := ℤ)), map_add, map_sub, coeff_mul_C, coeff_X_pow_mul', coeff_X_pow, coeff_mk, coeff_C_mul, coeff_X, coeff_one] at this
  have := hX 17 (by norm_num)
  norm_num at *
  omega
