import Mathlib

/-!
# A063395: T(2n,n) with T(n,m) as in A063394.

Source: https://oeis.org/A063395
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 3, 19, 131, 979, 7683, 62099, 511619, 4271699, ...
The entry gives the generating function
  4x/sqrt(1-10x+9x^2) + (1-2x)/(1-x)
(Ralf Stephan, Mar 23 2004). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 9*x^2 - 10*x + 1 the series is, in normalised form,
  (18*x^2 - 11*x + 1 + (4*x)*sqrt(R)) / (9*x^2 - 10*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 10 2013) reads
  Conjecture: (-n+1)*a(n) +(11*n-17)*a(n-1) +(-19*n+43)*a(n-2) +9*(n-3)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a063395

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 10 * X + 9 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A063395: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 11 * X + 18 * X ^ 2 + (4 * X) * S)
      * (1 - 10 * X + 9 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A063395. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (-(n : ℚ) + 1) * a n + (11 * (n : ℚ) - 17) * a (n - 1) + (-19 * (n : ℚ) + 43) * a (n - 2)
      + (9 * (n : ℚ) - 27) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a063395
