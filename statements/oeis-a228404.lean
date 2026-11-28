import Mathlib

/-!
# A228404: The number of complete binary trees with bicolored twigs. A twig is a vertex with one child on the boundary and the other child having no descendants.

Source: https://oeis.org/A228404
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 8, 24, 76, 249, 836, 2860, 9932, ...
The entry gives the generating function
  1 - x + 2*x*C^2 + x*C^4, where C = (1 - sqrt(1 - 4*x))/(2*x) is the g.f. of the Catalan numbers A000108
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (-2*x^4 - 2*x^3 + 4*x^2 - 4*x + 1 + (-2*x^2 + 2*x - 1)*sqrt(R)) / (2*x^3),
which is the expression used below (the division by x^3 is the shift of the index by 3).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Aug 08 2015) reads
  Conjecture: -5*(n+3)*(n-2)*a(n) + 5*(-n^2-n+18)*a(n-1) + 5*(-n^2-n+48)*a(n-2) +(-5*n^2+20029*n+720)*a(n-3) + (-5*n^2-104153*n+186654)*a(n-4) + (-5*n^2 +130153*n -508806)*a(n-5) + 13650*(2*n-11)*(n-7)*a(n-6) = 0
The recurrence fails for n in [6] (small n, where the inhomogeneous part of the differential
equation is felt), so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a228404

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A228404: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 3)
    ((1 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 + (-1 + 2 * X - 2 * X ^ 2) * S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A228404. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (-5 * (n : ℚ) ^ 2 - 5 * (n : ℚ) + 30) * a n
      + (-5 * (n : ℚ) ^ 2 - 5 * (n : ℚ) + 90) * a (n - 1)
      + (-5 * (n : ℚ) ^ 2 - 5 * (n : ℚ) + 240) * a (n - 2)
      + (-5 * (n : ℚ) ^ 2 + 20029 * (n : ℚ) + 720) * a (n - 3)
      + (-5 * (n : ℚ) ^ 2 - 104153 * (n : ℚ) + 186654) * a (n - 4)
      + (-5 * (n : ℚ) ^ 2 + 130153 * (n : ℚ) - 508806) * a (n - 5)
      + (27300 * (n : ℚ) ^ 2 - 341250 * (n : ℚ) + 1051050) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a228404
