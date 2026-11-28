import Mathlib

/-!
# A110198: Antidiagonal sums of number triangle A110197.

Source: https://oeis.org/A110198
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 4, 9, 20, 46, 109, 262, 638, ...
The entry gives the generating function
  1/((1-x)*sqrt((1+x+x^2)*(1-3x+x^2)))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 2*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (0 + (1)*sqrt(R)) / (-x^5 + 3*x^4 - x^3 + x^2 - 3*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 15 2012) reads
  Conjecture: n*a(n) +(-3*n+1)*a(n-1) +n*a(n-2) +(-n+2)*a(n-3) +(3*n-5)*a(n-4) +(-n+2)*a(n-5)=0
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a110198

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A110198: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((S)
      * (1 - 3 * X + X ^ 2 - X ^ 3 + 3 * X ^ 4 - X ^ 5 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A110198. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (n : ℚ) * a n + (-3 * (n : ℚ) + 1) * a (n - 1) + (n : ℚ) * a (n - 2)
      + (-(n : ℚ) + 2) * a (n - 3) + (3 * (n : ℚ) - 5) * a (n - 4)
      + (-(n : ℚ) + 2) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a110198
