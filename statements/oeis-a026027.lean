import Mathlib

/-!
# A026027: a(n) = number of (s(0), s(1), ..., s(2*n-1)) such that s(i) is a nonnegative integer and |s(i) - s(i-1)| = 1 for i = 1,2,...,n, s(0) = 3, s(2*n-1) = 6. Also a(n) = T(2*n-1,n-2), where T is defined in A026022.

Source: https://oeis.org/A026027
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 2) begins 1, 5, 21, 84, 329, 1274, 4900, 18768, 71706, ...
The entry gives the generating function
  (1+x^2C^4)*C^5, where C=(1-sqrt(1-4*x))/(2*x).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-4*X the radicand. The g.f. as given is the series of a(n+2); multiplying it by x^2 aligns it with the offset 2. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^10) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^10 is the shift of the index by 10. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 22 2013) reads
  Conjecture: (13*n+118)*(n+5)*a(n) +(13*n^2-969*n-3490)*a(n-1) +2*(-203*n^2+1080*n+758)*a(n-2) +4*(73*n-182)*(2*n-5)*a(n-3)=0.
It involves a(n-3) and the offset is 2, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a026027

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A026027: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 10)
    ((X ^ 5 - 9 * X ^ 6 + 28 * X ^ 7 - 35 * X ^ 8 + 14 * X ^ 9 + (-X ^ 5 + 7 * X ^ 6 - 16 * X ^ 7 + 13 * X ^ 8 - 2 * X ^ 9) * S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A026027. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (13 * (n : ℚ) ^ 2 + 183 * (n : ℚ) + 590) * a n
      + (13 * (n : ℚ) ^ 2 - 969 * (n : ℚ) - 3490) * a (n - 1)
      + (-406 * (n : ℚ) ^ 2 + 2160 * (n : ℚ) + 1516) * a (n - 2)
      + (584 * (n : ℚ) ^ 2 - 2916 * (n : ℚ) + 3640) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026027
