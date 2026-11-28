import Mathlib

/-!
# A252354: Number of Motzkin paths of length n with no level steps at height 2.

Source: https://oeis.org/A252354
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 4, 9, 20, 46, 106, 248, ...
The entry gives the generating function
  1/(1 - x - x^2*(1/(1 - x - x^2*R(x)))), where R(x) = (1 + x - sqrt(1 - 2*x - 3*x^2))/(2*x*(1 + x)) is the g.f. of the Riordan numbers A005043
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -3*x^2 - 2*x + 1 the series is, in normalised form,
  (-3*x^4 + 9*x^3 - 6*x + 2 + (-x^3)*sqrt(R)) / (2*x^5 - 8*x^4 + 12*x^3 + 4*x^2 - 8*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Sep 24 2016) reads
  Conjecture: (-n+3)*a(n) +3*(2*n-7)*a(n-1) +(-7*n+24)*a(n-2) +2*(-7*n+36)*a(n-3) +2*(11*n-51)*a(n-4) +3*(3*n-23)*a(n-5) +(-10*n+63)*a(n-6) +3*(n-6)*a(n-7)=0
It involves a(n-7) and the offset is 0, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a252354

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A252354: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((2 - 6 * X + 9 * X ^ 3 - 3 * X ^ 4 + (-X ^ 3) * S)
      * (2 - 8 * X + 4 * X ^ 2 + 12 * X ^ 3 - 8 * X ^ 4 + 2 * X ^ 5 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A252354. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (-(n : ℚ) + 3) * a n + (6 * (n : ℚ) - 21) * a (n - 1) + (-7 * (n : ℚ) + 24) * a (n - 2)
      + (-14 * (n : ℚ) + 72) * a (n - 3) + (22 * (n : ℚ) - 102) * a (n - 4)
      + (9 * (n : ℚ) - 69) * a (n - 5) + (-10 * (n : ℚ) + 63) * a (n - 6)
      + (3 * (n : ℚ) - 18) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a252354
