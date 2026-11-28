import Mathlib

/-!
# A191782: Sum of the lengths of the first ascents in all n-length left factors of Dyck paths.

Source: https://oeis.org/A191782
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 1) begins 1, 3, 6, 13, 24, 49, 90, 181, 335, ...
The entry gives the generating function
  z*c*(1+z*c^2)/((1-z)*(1-z*c)), where c = (1-sqrt(1 -4*z^2)) / (2*z^2).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-4*X^2 the radicand. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^6) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^6 is the shift of the index by 6. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: -(n+3)*(6*n-17)*a(n) +2*(6*n^2-2*n-57)*a(n-1) +3*(6*n^2-17*n+27)*a(n-2) -2*(2*n-3)*(12*n-25)*a(n-3) +4*(6*n-11)*(n-3)*a(n-4)=0.
It involves a(n-4) and the offset is 1, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a191782

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A191782: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 6)
    ((-X ^ 3 + X ^ 4 + 3 * X ^ 5 - 3 * X ^ 6 + 2 * X ^ 7 + (X ^ 3 - X ^ 4 - X ^ 5 + X ^ 6) * S)
      * (2 - 6 * X + 4 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A191782. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (-6 * (n : ℚ) ^ 2 - (n : ℚ) + 51) * a n + (12 * (n : ℚ) ^ 2 - 4 * (n : ℚ) - 114) * a (n - 1)
      + (18 * (n : ℚ) ^ 2 - 51 * (n : ℚ) + 81) * a (n - 2)
      + (-48 * (n : ℚ) ^ 2 + 172 * (n : ℚ) - 150) * a (n - 3)
      + (24 * (n : ℚ) ^ 2 - 116 * (n : ℚ) + 132) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a191782
