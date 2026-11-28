import Mathlib

/-!
# A026163: Sum{T(k,k-1)}, k = 1,2,...,n, where T is the array in A026148.

Source: https://oeis.org/A026163
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 2, 6, 16, 45, 126, 356, 1008, 2862, ...
The entry gives the generating function
  (2*x-1)*((x+1)^(1/2)*(1-3*x)^(1/2)*(x-1)*(x^2+2*x-1)+x^4-4*x^3-2*x^2+4*x-1)/(2*x^8)
(see the entry), taken times x^1 so that the exponent of x is the index n of the entry. It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -3*x^2 - 2*x + 1 the series is, in normalised form,
  (2*x^5 - 9*x^4 + 10*x^2 - 6*x + 1 + (2*x^4 + x^3 - 7*x^2 + 5*x - 1)*sqrt(R)) / (2*x^7),
which is the expression used below (the division by x^7 is the shift of the index by 7).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 23 2013) reads
  Conjecture: -(n+7)*(3*n-31)*a(n) +3*(-n^2-35*n-76)*a(n-1) +2*(32*n^2+27*n-459)*a(n-2) +(-47*n^2+286*n-204)*a(n-3) -3*(37*n-51)*(n-2)*a(n-4)=0
It involves a(n-4) and the offset is 1, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a026163

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A026163: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 7)
    ((1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 4 + 2 * X ^ 5 + (-1 + 5 * X - 7 * X ^ 2 + X ^ 3 + 2 * X ^ 4) * S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A026163. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (-3 * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 217) * a n
      + (-3 * (n : ℚ) ^ 2 - 105 * (n : ℚ) - 228) * a (n - 1)
      + (64 * (n : ℚ) ^ 2 + 54 * (n : ℚ) - 918) * a (n - 2)
      + (-47 * (n : ℚ) ^ 2 + 286 * (n : ℚ) - 204) * a (n - 3)
      + (-111 * (n : ℚ) ^ 2 + 375 * (n : ℚ) - 306) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026163
