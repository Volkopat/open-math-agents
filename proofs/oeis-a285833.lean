import OMAStatements.S_oeis_a285833
import Mathlib

/-!
# OEIS A285833: Barker's conjectures for the diagonal (origin to corner, base 10) of Rule 107: the conjectured package is inconsistent

The denominator expands to `(1) X^0 + (-111) X^2 + (1110) X^4 + (-1000) X^6`, the denominator of the claimed recurrence. So the coefficient
of `X ^ 8` in the generating-function identity says that the recurrence combination at `n = 8`
equals `11000000`, while the claimed recurrence at `n = 8` says that it is `0`. So the conjunction of
the claims is false.
-/

open OMA.S_oeis_a285833 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285833.main) := by
  rintro ⟨h, hX⟩
  generalize a = f at h hX
  have := congrArg (coeff 8) h
  rw [show ∀ S : ℤ⟦X⟧, S * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) =
      S + X ^ 2 * S * C (-111) + X ^ 4 * S * C 1110 + X ^ 6 * S * C (-1000) from fun S => by simp; ring] at this
  simp only [← map_ofNat (C (R := ℤ)), map_add, map_sub, coeff_mul_C, coeff_X_pow_mul', coeff_X_pow, coeff_mk, coeff_C_mul, coeff_X, coeff_one] at this
  have := hX 8 (by norm_num)
  norm_num at *
  omega
