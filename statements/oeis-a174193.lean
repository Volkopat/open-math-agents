import Mathlib

/-!
# A174193: almost avoiding permutations in Av(321)^{+1} (conjectured g.f.)

Source: https://oeis.org/A174193
Credit: @sntntHb

A174193 is defined as the expansion of the (conjectured) generating function
`(1-8x+13x^2+24x^3-48x^4 - (1-6x+x^2+34x^3-26x^4-4x^5) sqrt(1-4x)) /
 (2 x^2 (1-x) (1-4x)^2)`, offset 0: `1, 1, 2, 6, 23, 103, 488, 2320, ...`.

Here `sqrt(1-4x)` is the power series `1 - 2 x C(x)` with `C(x)` the Catalan g.f.
(its square is `1 - 4x`). The numerator is divisible by `x^2`, so `a(n)` is the
coefficient of `x^(n+2)` in `numerator / ((1-x)(1-4x)^2)`, divided by `2`.

Formalizes R. J. Mathar's conjectured recurrence (OEIS A174193, Jun 14 2016):
`-(n+2)(404489n-1866368)a(n) + (3147815n^2-8680082n-14098754)a(n-1)
 + 2(-2336439n^2+652022n+14514849)a(n-2) + 8(-1044770n^2+10585023n-20370553)a(n-3)
 + 8(642982n-2004177)(2n-9)a(n-4) = 0`, stated for every `n >= 4`
(checked numerically for `4 <= n < 68`).
-/

namespace OMA.S_oeis_a174193

open PowerSeries

/-- The Catalan generating function `C(x) = sum catalan n x^n`. -/
noncomputable def C : PowerSeries ℚ := PowerSeries.mk fun n => (catalan n : ℚ)

/-- `sqrt(1-4x) = 1 - 2 x C(x)`. -/
noncomputable def S : PowerSeries ℚ := 1 - 2 * X * C

/-- The numerator of the generating function. -/
noncomputable def num : PowerSeries ℚ :=
  (1 - 8 * X + 13 * X ^ 2 + 24 * X ^ 3 - 48 * X ^ 4) -
    (1 - 6 * X + X ^ 2 + 34 * X ^ 3 - 26 * X ^ 4 - 4 * X ^ 5) * S

/-- A174193: `a(n) = [x^(n+2)] num / ((1-x)(1-4x)^2) / 2`. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2) (num * ((1 - X) * (1 - 4 * X) ^ 2)⁻¹) / 2

/-- Mathar's conjectured fourth-order holonomic recurrence, for every `n >= 4`. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n →
      -((n : ℚ) + 2) * (404489 * (n : ℚ) - 1866368) * a n +
        (3147815 * (n : ℚ) ^ 2 - 8680082 * (n : ℚ) - 14098754) * a (n - 1) +
        2 * (-2336439 * (n : ℚ) ^ 2 + 652022 * (n : ℚ) + 14514849) * a (n - 2) +
        8 * (-1044770 * (n : ℚ) ^ 2 + 10585023 * (n : ℚ) - 20370553) * a (n - 3) +
        8 * (642982 * (n : ℚ) - 2004177) * (2 * (n : ℚ) - 9) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a174193
