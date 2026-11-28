import Mathlib

/-!
# A182894: Number of weighted lattice paths in L_n having no (1,0)-steps at level 0. The members of L_n  are paths of weight n that start at (0,0) , end on the horizontal axis and whose steps are of the following four kinds: an (1,0)-step with weight 1, an (1,0)-step with weight 2, a (1,1)-step with weight 2, and a (1,-1)-step with weight 1. The weight of a path is the sum of the weights of its steps.

Source: https://oeis.org/A182894
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 0, 0, 2, 2, 4, 12, 24, 54, ...
The entry gives the generating function
  1/( z+z^2+sqrt((1+z+z^2)(1-3z+z^2)) )
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 2*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (-x^2 - x + (1)*sqrt(R)) / (-4*x^3 - 2*x^2 - 2*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: n*a(n) +(-4*n+3)*a(n-1) +(n-3)*a(n-2) -3*a(n-3) +3*(5*n-14)*a(n-4) +6*(n-3)*a(n-5) +6*(n-4)*a(n-6) +4*(-n+6)*a(n-7)=0
It involves a(n-7) and the offset is 0, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a182894

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A182894: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-X - X ^ 2 + S)
      * (1 - 2 * X - 2 * X ^ 2 - 4 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A182894. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (n : ℚ) * a n + (-4 * (n : ℚ) + 3) * a (n - 1) + ((n : ℚ) - 3) * a (n - 2)
      + (-3) * a (n - 3) + (15 * (n : ℚ) - 42) * a (n - 4) + (6 * (n : ℚ) - 18) * a (n - 5)
      + (6 * (n : ℚ) - 24) * a (n - 6) + (-4 * (n : ℚ) + 24) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a182894
