import Mathlib

/-!
# A166287: Number of peak plateaux in all Dyck paths of semilength n with no UUU's and no DDD's (U=(1,1), D=(1,-1)).

Source: https://oeis.org/A166287
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 0, 1, 3, 8, 21, 53, 133, ...
The entry gives the generating function
  (1-z-z^2-h)/[2(1-z)h], where h = sqrt((1-3z+z^2)(1+z+z^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 2*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (-x^4 + 2*x^3 + x^2 + 2*x - 1 + (-x^2 - x + 1)*sqrt(R)) / (-2*x^5 + 6*x^4 - 2*x^3 + 2*x^2 - 6*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: n*a(n) +(-4*n+3)*a(n-1) +3*(n-1)*a(n-2) +(n-9)*a(n-3) +(3*n-5)*a(n-4) +(-3*n+7)*a(n-5) +(-2*n+13)*a(n-6) +(n-6)*a(n-7)=0
It involves a(n-7) and the offset is 0, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a166287

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A166287: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-1 + 2 * X + X ^ 2 + 2 * X ^ 3 - X ^ 4 + (1 - X - X ^ 2) * S)
      * (2 - 6 * X + 2 * X ^ 2 - 2 * X ^ 3 + 6 * X ^ 4 - 2 * X ^ 5 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A166287. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (n : ℚ) * a n + (-4 * (n : ℚ) + 3) * a (n - 1) + (3 * (n : ℚ) - 3) * a (n - 2)
      + ((n : ℚ) - 9) * a (n - 3) + (3 * (n : ℚ) - 5) * a (n - 4)
      + (-3 * (n : ℚ) + 7) * a (n - 5) + (-2 * (n : ℚ) + 13) * a (n - 6)
      + ((n : ℚ) - 6) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a166287
