import Mathlib

/-!
# A182904: Number of weighted lattice paths in L_n having no peaks. The members of L_n are paths of weight n that start at (0,0), end on the horizontal axis and whose steps are of the following four kinds: an (1,0)-step with weight 1, an (1,0)-step with weight 2, a (1,1)-step with weight 2, and a (1,-1)-step with weight 1. The weight of a path is the sum of the weights of its steps. A peak is a (1,1)-step followed by a (1,-1)-step.

Source: https://oeis.org/A182904
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 4, 9, 21, 48, 112, 263, ...
The entry gives the generating function
  1/sqrt(1-2z-z^2-z^4-2z^5+z^6)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^6 - 2*x^5 - x^4 - x^2 - 2*x + 1 the series is, in normalised form,
  (0 + (1)*sqrt(R)) / (x^6 - 2*x^5 - x^4 - x^2 - 2*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: n*a(n) +(n-2)*a(n-1) +(-7*n+10)*a(n-2) +3*(-n+2)*a(n-3) +(-n+2)*a(n-4) +(-5*n+14)*a(n-5) +(-5*n+18)*a(n-6) +3*(n-4)*a(n-7)=0
It involves a(n-7) and the offset is 0, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a182904

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A182904: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((S)
      * (1 - 2 * X - X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A182904. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (n : ℚ) * a n + ((n : ℚ) - 2) * a (n - 1) + (-7 * (n : ℚ) + 10) * a (n - 2)
      + (-3 * (n : ℚ) + 6) * a (n - 3) + (-(n : ℚ) + 2) * a (n - 4)
      + (-5 * (n : ℚ) + 14) * a (n - 5) + (-5 * (n : ℚ) + 18) * a (n - 6)
      + (3 * (n : ℚ) - 12) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a182904
