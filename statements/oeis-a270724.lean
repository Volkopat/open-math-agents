import Mathlib

/-!
# A270724: a(n) = ((n+2)/2)*Sum_{k=0..n/2} (Sum_{i=0..n-2*k} (binomial(k+1,n-2*k-i)*binomial(k+i,k))/(k+1)*C(k)), where C(k) is Catalan numbers.

Source: https://oeis.org/A270724
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 3, 5, 10, 20, 42, 93, 213, 504, ...
The entry gives the generating function
  ((-x^2+x+1)*(1-sqrt(1-(4*x^2*(x+1))/(1-x))))/(2*x^2*(1-x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 4*x^4 - 3*x^2 - 2*x + 1 the series is, in normalised form,
  (x^3 - 2*x^2 + 1 + (x^2 - x - 1)*sqrt(R)) / (2*x^5 - 2*x^4 - 2*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Oct 07 2016) reads
  Conjecture: (n+2)*a(n) +(-n-2)*a(n-1) +(-7*n+6)*a(n-2) +10*a(n-3) +(13*n-32)*a(n-4) +(5*n-32)*a(n-5) +(-11*n+52)*a(n-6) +4*(-n+6)*a(n-7) +4*(n-7)*a(n-8)=0
It involves a(n-8) and the offset is 0, so it is stated for n >= 8.
-/

namespace OMA.S_oeis_a270724

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2 + 4 * X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A270724: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - 2 * X ^ 2 + X ^ 3 + (-1 - X + X ^ 2) * S)
      * (2 - 2 * X - 2 * X ^ 2 + 2 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A270724. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    ((n : ℚ) + 2) * a n + (-(n : ℚ) - 2) * a (n - 1) + (-7 * (n : ℚ) + 6) * a (n - 2)
      + (10) * a (n - 3) + (13 * (n : ℚ) - 32) * a (n - 4) + (5 * (n : ℚ) - 32) * a (n - 5)
      + (-11 * (n : ℚ) + 52) * a (n - 6) + (-4 * (n : ℚ) + 24) * a (n - 7)
      + (4 * (n : ℚ) - 28) * a (n - 8) = 0 := by
  sorry

end OMA.S_oeis_a270724
