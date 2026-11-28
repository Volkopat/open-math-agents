import Mathlib

/-!
# A131135: Denominator of (ordinary) expansion of log((x/2-1)/(x-1)).

Source: https://oeis.org/A131135
Credit: @agchua

Michel Marcus (Sep 12 2019), in the formula section of A131135:
  a(n) = denominator((1-1/2^n)/n), for n > 0, conjectured. - _Michel Marcus_, Sep 12 2019
A131135 has offset 0; the claim is stated for n >= 1, as printed.

The function (x/2-1)/(x-1) is the formal power series F = (x/2 - 1) * (x - 1)^(-1) over the
rationals; its constant term is 1. Its logarithm is Mathlib's formal logarithm
`PowerSeries.logOf F`, which is log(1 + X) = X - X^2/2 + X^3/3 - ... with F - 1 substituted for X.
a(n) is the denominator of the coefficient of x^n in it; this reproduces the listed terms
1, 2, 8, 24, 64, 160, 128, 896, ...
-/

namespace OMA.S_oeis_a131135

/-- (x/2 - 1)/(x - 1) as a formal power series over ℚ. -/
noncomputable def F : PowerSeries ℚ :=
  (PowerSeries.C (1 / 2 : ℚ) * PowerSeries.X - 1) * (PowerSeries.X - 1)⁻¹

/-- A131135(n): the denominator of the coefficient of x^n in the expansion of log(F). -/
noncomputable def a (n : ℕ) : ℕ := (PowerSeries.coeff n (PowerSeries.logOf F)).den

/-- Marcus's conjecture: a(n) = denominator((1 - 1/2^n)/n) for n > 0. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = ((1 - 1 / 2 ^ n : ℚ) / n).den := by
  sorry

end OMA.S_oeis_a131135
