import Mathlib

/-!
# A111053: Number of permutations which avoid the patterns 1324 and (2143 with Bruhat restriction {2<->3}). Also the number of permutations whose graphs are acyclic.

Source: https://oeis.org/A111053
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 2, 6, 22, 89, 379, 1661, 7405, 33367, ...
The entry gives the generating function
  ((1-x)*(1-4*x-2*x^2)-(1-5*x)*sqrt(1-4*x))/(2*(1-5*x+2*x^2-x^3))
(Ralf Stephan, May 09 2007). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (2*x^3 + 2*x^2 - 5*x + 1 + (5*x - 1)*sqrt(R)) / (-2*x^3 + 4*x^2 - 10*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Aug 14 2012) reads
  Conjecture: n*(n+5)*a(n) +3*(20-13*n-3*n^2)*a(n-1) +2*(11*n^2+40*n-150)*a(n-2) +3*(40-11*n-3*n^2)*a(n-3) +2*(n+6)*(2*n-5)*a(n-4)=0
It involves a(n-4) and the offset is 1, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a111053

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A111053: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 5 * X + 2 * X ^ 2 + 2 * X ^ 3 + (-1 + 5 * X) * S)
      * (2 - 10 * X + 4 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A111053. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℚ) ^ 2 + 5 * (n : ℚ)) * a n + (-9 * (n : ℚ) ^ 2 - 39 * (n : ℚ) + 60) * a (n - 1)
      + (22 * (n : ℚ) ^ 2 + 80 * (n : ℚ) - 300) * a (n - 2)
      + (-9 * (n : ℚ) ^ 2 - 33 * (n : ℚ) + 120) * a (n - 3)
      + (4 * (n : ℚ) ^ 2 + 14 * (n : ℚ) - 60) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a111053
