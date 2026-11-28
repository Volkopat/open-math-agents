import OMAStatements.S_oeis_a282828
import Mathlib

/-!
# A282828: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 521, based on the 5-celled von Neumann neighborhood.: the conjectured package is inconsistent

The denominator expands to `1 - X^2 - 256 X^8 + 256 X^10`, so the coefficient of `X ^ 17` in the
generating-function identity reads `a 17 - a 15 - 256 a 9 + 256 a 7 = -32`. The claimed
recurrence at `n = 17` says that the same combination is `0`. So the conjunction of the claims
is false.
-/

open OMA.S_oeis_a282828 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282828.main) := by
  rintro ⟨hX, h⟩
  have := congrArg (coeff 17) h
  rw [show ∀ S : ℤ⟦X⟧, S * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) *
      (1 + 16 * X ^ 4)) = S - X ^ 2 * S - X ^ 8 * S * C 256 + X ^ 10 * S * C 256 from
      fun S => by simp; ring] at this
  simp only [← map_ofNat (C (R := ℤ)), map_add, map_sub, coeff_mul_C, coeff_C_mul,
    coeff_X_pow_mul', coeff_X_pow, coeff_one, coeff_mk] at this
  have := hX 17 (by norm_num)
  norm_num at *
  omega
