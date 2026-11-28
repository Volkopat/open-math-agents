import Mathlib

/-!
# A181933: a(n) = Sum_{k=0..n} binomial(n+k,k)*sin(Pi*(n+k)/2).

Source: https://oeis.org/A181933
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 1, -3, 9, -30, 106, -385, 1421, -5304, ...
The entry gives the generating function
  (1/2)*(sqrt(4*x+1)*(1+x)-3*x-1)/(sqrt(4*x+1)*(x^2+3*x+1)-4*x^2-5*x-1)
(Vladimir Kruchinin, Mar 28 2016). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 4*x + 1 the series is, in normalised form,
  (4*x^2 + 5*x + 1 + (x - 1)*sqrt(R)) / (8*x^3 + 18*x^2 + 20*x + 4),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: +2*n*a(n) +8*n*a(n-1) +(-n+20)*a(n-2) +5*(-n+4)*a(n-3) +2*(-2*n+5)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a181933

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 + 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A181933: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 + 5 * X + 4 * X ^ 2 + (-1 + X) * S)
      * (4 + 20 * X + 18 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A181933. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (2 * (n : ℚ)) * a n + (8 * (n : ℚ)) * a (n - 1) + (-(n : ℚ) + 20) * a (n - 2)
      + (-5 * (n : ℚ) + 20) * a (n - 3) + (-4 * (n : ℚ) + 10) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a181933
