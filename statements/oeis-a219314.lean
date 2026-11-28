import Mathlib

/-!
# A219314: Composition of the inverse binomial transform of Fibonacci numbers and the Catalan transform of Fibonacci numbers.

Source: https://oeis.org/A219314
Credit: @ivillar

Status: open conjecture of the entry (the first of the two recurrences given there); it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 0, 1, 0, 3, 3, 13, 26, 77, 192, ...
The entry gives the generating function
  ((1+2*x)*sqrt(1-2*x-3*x^2) - 1 + x + 2*x^2)/(2*(1+x)*(1-2*x-4*x^2))
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-2*X-3*X^2 the radicand. 
The series is written as (G) / (C * x^0) with C of nonzero constant term; the division by
x^0 is the shift of the index by 0. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: n*a(n) -2*n*a(n-1) +11*(-n+2)*a(n-2) +4*(2*n-5)*a(n-3) +8*(5*n-17)*a(n-4) +24*(n-4)*a(n-5)=0.
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a219314

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A219314: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-1 + X + 2 * X ^ 2 + (1 + 2 * X) * S)
      * (2 - 2 * X - 12 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A219314. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℚ)) * a n + (-2 * (n : ℚ)) * a (n - 1) + (-11 * (n : ℚ) + 22) * a (n - 2)
      + (8 * (n : ℚ) - 20) * a (n - 3) + (40 * (n : ℚ) - 136) * a (n - 4)
      + (24 * (n : ℚ) - 96) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a219314
