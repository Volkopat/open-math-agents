import Mathlib

/-!
# A067299: Second column of triangle A067298.

Source: https://oeis.org/A067299
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 2, 5, 32, 284, 2960, 33872, 411776, 5221568, 68299520, ...
The entry gives the generating function
  ((1+x)*c(2, 2; x)-1)/x, with c(2, 2; x) := (1-3*x*c(4*x))/(1-2*x*c(4*x))^2 g.f. for A064340 and c(x) is g.f. for A000108 (Catalan).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-16*X the radicand. Here c(4x) = (1 - sqrt(1 - 16x))/(8x). Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^0) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^0 is the shift of the index by 0. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jul 21 2016) reads
  Conjecture: n*(17*n-7)*a(n) +2*(-119*n^2+270*n-96)*a(n-1) -16*(17*n+10)*(2*n-3)*a(n-2)=0.
It involves a(n-2) and the offset is 0, so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a067299

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 16 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A067299: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((7 + 33 * X + 48 * X ^ 2 + 20 * X ^ 3 + (-3 - 15 * X - 24 * X ^ 2 - 12 * X ^ 3) * S)
      * (2 + 16 * X + 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A067299. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (17 * (n : ℚ) ^ 2 - 7 * (n : ℚ)) * a n
      + (-238 * (n : ℚ) ^ 2 + 540 * (n : ℚ) - 192) * a (n - 1)
      + (-544 * (n : ℚ) ^ 2 + 496 * (n : ℚ) + 480) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a067299
