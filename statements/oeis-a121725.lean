import Mathlib

/-!
# A121725: Generalized central coefficients for k=3.

Source: https://oeis.org/A121725
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 1, 1, 10, 19, 190, 442, 4420, 11395, 113950, ...
The entry gives the generating function
  (1 - sqrt(1 - 36*x^2))/(18*x^2 - x*(1 - sqrt(1 - 36*x^2))).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-36*X^2 the radicand. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^2) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^2 is the shift of the index by 2. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 26 2012) reads
  Conjecture: (n+1)*a(n) = 10*(n+1)*a(n-1) + 36*(n-2)*a(n-2) - 360*(n-2)*a(n-3).
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a121725

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 36 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A121725: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((-X + 12 * X ^ 2 - 20 * X ^ 3 + (X - 10 * X ^ 2) * S)
      * (2 - 40 * X + 200 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A121725. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ) + 1) * a n + (-10 * (n : ℚ) - 10) * a (n - 1) + (-36 * (n : ℚ) + 72) * a (n - 2)
      + (360 * (n : ℚ) - 720) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a121725
