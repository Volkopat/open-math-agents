import Mathlib

/-!
# A159771: Number of n-leaf binary trees that do not contain (()((()())((()())()))) as a subtree.

Source: https://oeis.org/A159771
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 1, 2, 5, 14, 41, 124, 385, 1220, ...
The entry gives the generating function
  ((1-2*x+3*x^2) - sqrt((1+x^2)*(1-4*x+x^2)))/(4*x)
(Paul D. Hanna, Aug 02 2012). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 4*x^3 + 2*x^2 - 4*x + 1 the series is, in normalised form,
  (3*x^2 - 2*x + 1 + (-1)*sqrt(R)) / (4*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jul 17 2014) reads
  Conjecture: (n+1)*a(n) +2*(-2*n+1)*a(n-1) +2*(n-2)*a(n-2) +2*(-2*n+7)*a(n-3) +(n-5)*a(n-4)=0
It involves a(n-4) and the offset is 1, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a159771

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A159771: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 - 2 * X + 3 * X ^ 2 - S)
      * (4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A159771. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℚ) + 1) * a n + (-4 * (n : ℚ) + 2) * a (n - 1) + (2 * (n : ℚ) - 4) * a (n - 2)
      + (-4 * (n : ℚ) + 14) * a (n - 3) + ((n : ℚ) - 5) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a159771
