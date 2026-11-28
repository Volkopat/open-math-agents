import Mathlib

/-!
# A227081: Row sums of A124576.

Source: https://oeis.org/A227081
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 8, 40, 212, 1152, 6360, 35520, 200132, ...
The entry gives the generating function
  1/(6*x -1 +2*sqrt((2*x-1)*(6*x-1)))
(Vaclav Kotesovec, Jul 06 2013). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 12*x^2 - 8*x + 1 the series is, in normalised form,
  (1 - 6*x + (2)*sqrt(R)) / (12*x^2 - 20*x + 3),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture () reads
  Conjecture: 3*n*a(n) +2*(-13*n+9)*a(n-1) +4*(13*n-21)*a(n-2) +24*(-n+2)*a(n-3)=0.
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a227081

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 8 * X + 12 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A227081: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 6 * X + (2) * S)
      * (3 - 20 * X + 12 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A227081. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (3 * (n : ℚ)) * a n + (-26 * (n : ℚ) + 18) * a (n - 1) + (52 * (n : ℚ) - 84) * a (n - 2)
      + (-24 * (n : ℚ) + 48) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a227081
