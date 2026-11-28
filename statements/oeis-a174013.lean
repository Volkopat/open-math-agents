import Mathlib

/-!
# A174013: Sequence whose Hankel transform is a (1,1) Somos-4 sequence.

Source: https://oeis.org/A174013
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 3, 6, 12, 22, 37, 56, 73, ...
The entry gives the generating function
  -(1-3*x-x^2-sqrt(1-2*x-x^2+6*x^3+5*x^4))/(2*x*(1-x-x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 5*x^4 + 6*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (x^2 + 3*x - 1 + (1)*sqrt(R)) / (-2*x^3 - 2*x^2 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jan 12 2013) reads
  Conjecture: (n+1)*a(n) +n*a(n-1) +12*(-n+1)*a(n-2) +3*(3*n-8)*a(n-3) +6*(6*n-23)*a(n-4) +11*(-n+2)*a(n-5) +(-49*n+253)*a(n-6) +20*(-n+6)*a(n-7)=0
It involves a(n-7) and the offset is 0, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a174013

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 + 6 * X ^ 3 + 5 * X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A174013: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((-1 + 3 * X + X ^ 2 + S)
      * (2 - 2 * X - 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A174013. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    ((n : ℚ) + 1) * a n + (n : ℚ) * a (n - 1) + (-12 * (n : ℚ) + 12) * a (n - 2)
      + (9 * (n : ℚ) - 24) * a (n - 3) + (36 * (n : ℚ) - 138) * a (n - 4)
      + (-11 * (n : ℚ) + 22) * a (n - 5) + (-49 * (n : ℚ) + 253) * a (n - 6)
      + (-20 * (n : ℚ) + 120) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a174013
