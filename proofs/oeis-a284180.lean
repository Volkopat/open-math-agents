import OMAStatements.S_oeis_a284180
import Mathlib

/-!
# OEIS A284180: Barker's conjectures for the x-axis (origin to right edge, base 10) of Rule 813: the conjectured package is inconsistent

The denominator expands to `(1) X^0 + (-10) X^1 + (-1) X^4 + (10) X^5`, the denominator of the claimed recurrence. So the coefficient
of `X ^ 5` in the generating-function identity says that the recurrence combination at `n = 5`
equals `100`, while the claimed recurrence at `n = 5` says that it is `0`. So the conjunction of
the claims is false.
-/

open OMA.S_oeis_a284180 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284180.main) := by
  rintro ⟨h, hX⟩
  generalize a = f at h hX
  have := congrArg (coeff 5) h
  rw [show ∀ S : ℤ⟦X⟧, S * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + X ^ 2)) =
      S + X ^ 1 * S * C (-10) + X ^ 4 * S * C (-1) + X ^ 5 * S * C 10 from fun S => by simp; ring] at this
  simp only [← map_ofNat (C (R := ℤ)), map_add, map_sub, coeff_mul_C, coeff_X_pow_mul', coeff_X_pow, coeff_mk, coeff_C_mul, coeff_X, coeff_one] at this
  have := hX 5 (by norm_num)
  norm_num at *
  omega
