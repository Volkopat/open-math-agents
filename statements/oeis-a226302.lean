import Mathlib

/-!
# A226302: a(n) = P_n(-1), where P_n(x) is a certain polynomial arising in the enumeration of tatami mat coverings.

Source: https://oeis.org/A226302
Credit: @vivanpoddar

The sequence (offset 2) begins 1, -1, 2, -4, 6, -14, 20, -48, 70, ...
The entry gives the generating function
  1/sqrt(1-4*x^2) - x/((1-2*x^2)*sqrt(1-4*x^2))   (given there for offset 0)
(see the entry), taken times x^2 so that the exponent of x is the index n of the entry.
It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (x^3 + x^2)*sqrt(R) / (-4*x^3 - 2*x^2 + 2*x + 1),
which is the expression used below.
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 06 2013) reads
  Conjecture: (-n+2)*a(n) +(-n+2)*a(n-1) +2*(3*n-11)*a(n-2) +2*(3*n-14)*a(n-3) +4*(-2*n+9)*a(n-4) +8*(-n+6)*a(n-5)=0
It involves a(n-5) and the offset is 2, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a226302

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A226302: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    (((X ^ 2 + X ^ 3) * S)
      * (1 + 2 * X - 2 * X ^ 2 - 4 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A226302. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (-(n : ℚ) + 2) * a n + (-(n : ℚ) + 2) * a (n - 1) + (6 * (n : ℚ) - 22) * a (n - 2)
      + (6 * (n : ℚ) - 28) * a (n - 3) + (-8 * (n : ℚ) + 36) * a (n - 4)
      + (-8 * (n : ℚ) + 48) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a226302
