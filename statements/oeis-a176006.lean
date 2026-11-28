import Mathlib

/-!
# A176006: The number of branching configurations of RNA (see Sankoff, 1985) with n or fewer hairpins.

Source: https://oeis.org/A176006
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 1, 2, 4, 10, 32, 122, 516, 2322, 10880, ...
The entry gives the generating function
  (3 - x - sqrt(1 - 6*x + x^2))/(2*(1 - x))
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-6*X+X^2 the radicand. 
The series is written as (G) / (C * x^0) with C of nonzero constant term; the division by
x^0 is the shift of the index by 0. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jul 24 2012) reads
  Conjecture : n*a(n) +(9-7*n)*a(n-1) +(7*n-12)*a(n-2) +(3-n)*a(n-3)=0.
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a176006

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A176006: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((3 - X - S)
      * (2 - 2 * X : PowerSeries ℚ)⁻¹)

/-- The recurrence for A176006. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ)) * a n + (-7 * (n : ℚ) + 9) * a (n - 1) + (7 * (n : ℚ) - 12) * a (n - 2)
      + (-(n : ℚ) + 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a176006
