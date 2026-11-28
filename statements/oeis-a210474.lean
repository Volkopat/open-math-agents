import Mathlib

/-!
# A210474: The number of different lattice paths from (0,0) to (2n,0) using steps of S={(i,i) or (i,-i): i=1,2,...,n} with j flaws(j=1,2,...,n-1), where the j flaws is the sum of lengths of down steps below the x-axis. (For down steps that are partly above and partly below the x-axis we just count the part below the x-axis.) This number is independent of the number of flaws.

Source: https://oeis.org/A210474
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 0, 4, 24, 156, 1072, 7668, 56520, 426380, ...
The entry gives the generating function
  (1-x)*(1+3*x-sqrt(9*x^2-10*x+1))/(8*x)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 9*x^2 - 10*x + 1 the series is, in normalised form,
  (-3*x^2 + 2*x + 1 + (x - 1)*sqrt(R)) / (8*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture:  (n+1)*a(n) +2*(-5*n+3)*a(n-1) +9*(n-3)*a(n-2)=0
The recurrence fails for n in [2] (small n, where the inhomogeneous part of the differential
equation is felt), so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a210474

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 10 * X + 9 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A210474: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 + 2 * X - 3 * X ^ 2 + (-1 + X) * S)
      * (8 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A210474. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ) + 1) * a n + (-10 * (n : ℚ) + 6) * a (n - 1) + (9 * (n : ℚ) - 27) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a210474
