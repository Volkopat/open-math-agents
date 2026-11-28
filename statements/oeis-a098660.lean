import Mathlib

/-!
# A098660: E.g.f. BesselI(0,2*sqrt(2)*x) + BesselI(1,2*sqrt(2)*x)/sqrt(2).

Source: https://oeis.org/A098660
Credit: @ivillar

Status: false as stated. With a(0..3) = 1, 1, 4, 6 the left side at n = 3 is 4*6 + 2*4 - 3*1 - 1*1 = 28, not 0; the statement is kept as the target of a disproof.

The sequence (offset 0) begins 1, 1, 4, 6, 24, 40, 160, 280, 1120, ...
The entry gives the generating function
  (1+4*x-sqrt(1-8*x^2))/(4*x*sqrt(1-8*x^2))
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-8*X^2 the radicand. Multiplying numerator and denominator by sqrt(1-8x^2) gives the form used below.
The series is written as (G) / (C * x^1) with C of nonzero constant term; the division by
x^1 is the shift of the index by 1. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 15 2011) reads
  Conjecture: (n+1)*a(n) + (n-1)*a(n-1) - n*a(n-2) + (2-n)*a(n-3) = 0.
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a098660

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 8 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A098660: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((-1 + 8 * X ^ 2 + (1 + 4 * X) * S)
      * (4 - 32 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A098660 (false as stated, see the Status line). -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ) + 1) * a n + ((n : ℚ) - 1) * a (n - 1) + (-(n : ℚ)) * a (n - 2)
      + (-(n : ℚ) + 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a098660
