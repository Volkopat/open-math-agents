import Mathlib

/-!
# A188464: Diagonal sums of triangle A188463.

Source: https://oeis.org/A188464
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 3, 8, 22, 62, 178, 519, 1533, 4578, ...
The entry gives the generating function
  (1-3*x+x^2-x^3-(1-x)*sqrt(1-4*x+2*x^2+x^4))/(2*x^4)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 + 2*x^2 - 4*x + 1 the series is, in normalised form,
  (-x^3 + x^2 - 3*x + 1 + (x - 1)*sqrt(R)) / (2*x^4),
which is the expression used below (the division by x^4 is the shift of the index by 4).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 17 2011) reads
  Conjecture: (n+4)*a(n)-(4*n+9)*a(n-1) +(2*n-1)*a(n-2) -a(n-3) +(n-3)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a188464

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 2 * X ^ 2 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A188464: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 4)
    ((1 - 3 * X + X ^ 2 - X ^ 3 + (-1 + X) * S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A188464. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 4) * a n + (-4 * (n : ℚ) - 9) * a (n - 1) + (2 * (n : ℚ) - 1) * a (n - 2)
      + (-1) * a (n - 3) + ((n : ℚ) - 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a188464
