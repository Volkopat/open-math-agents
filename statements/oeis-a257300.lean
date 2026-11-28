import Mathlib

/-!
# A257300: Number of Motzkin paths of length n with no peaks at level 2.

Source: https://oeis.org/A257300
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 4, 8, 17, 38, 88, 210, ...
The entry gives the generating function
  1/(1 - x - x^2/(1 - x + x^2*(1 - M(x)))), where M(x) = (1 - x - sqrt(1 - 2*x - 3*x^2))/(2*x^2) is the g.f. of the Motzkin numbers A001006
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -3*x^2 - 2*x + 1 the series is, in normalised form,
  (-2*x^3 + 2*x^2 - 5*x + 3 + (-1)*sqrt(R)) / (2*x^4 - 2*x^3 + 6*x^2 - 6*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Sep 24 2016) reads
  Conjecture: n*a(n) +(-5*n+3)*a(n-1) +6*(n)*a(n-2) +2*(n-9)*a(n-3) +6*(-n+4)*a(n-4) +(n-6)*a(n-5) +3*(-n+3)*a(n-6)=0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a257300

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A257300: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((3 - 5 * X + 2 * X ^ 2 - 2 * X ^ 3 - S)
      * (2 - 6 * X + 6 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A257300. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (n : ℚ) * a n + (-5 * (n : ℚ) + 3) * a (n - 1) + (6 * (n : ℚ)) * a (n - 2)
      + (2 * (n : ℚ) - 18) * a (n - 3) + (-6 * (n : ℚ) + 24) * a (n - 4)
      + ((n : ℚ) - 6) * a (n - 5) + (-3 * (n : ℚ) + 9) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a257300
