import OMAStatements.S_oeis_a005379
import Mathlib

/-!
# A005379: Plouffe's conjectured generating function for Hofstadter's male sequence is false

Since `(1 - X ^ 8) (1 - X) = 1 - X - X ^ 8 + X ^ 9`, the coefficient of `X ^ 33` on the left is
`a 33 - a 32 - a 25 + a 24 = 20 - 20 - 16 + 15 = -1`, while the right-hand side is a polynomial
of degree `10`, so its coefficient of `X ^ 33` is `0`.
-/

namespace OMA.S_oeis_a005379

open PowerSeries

lemma a_24 : a 24 = 15 := by decide +kernel
lemma a_25 : a 25 = 16 := by decide +kernel
lemma a_32 : a 32 = 20 := by decide +kernel
lemma a_33 : a 33 = 20 := by decide +kernel

end OMA.S_oeis_a005379

open OMA.S_oeis_a005379 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a005379.main) := by
  intro h
  have el : gf * ((1 - X ^ 8) * (1 - X)) = gf - gf * X ^ 1 - gf * X ^ 8 + gf * X ^ 9 := by ring
  have er : (X ^ 2 * (1 + X ^ 3 + X ^ 6 + X + X ^ 4 + X ^ 7 - X ^ 8) : PowerSeries ℤ) =
      X ^ 2 + X ^ 5 + X ^ 8 + X ^ 3 + X ^ 6 + X ^ 9 - X ^ 10 := by ring
  rw [el, er] at h
  have h33 := congrArg (PowerSeries.coeff 33) h
  simp [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, gf, PowerSeries.coeff_mk,
    a_24, a_25, a_32, a_33] at h33
