import Mathlib

/-!
# A191398: Number of dispersed Dyck paths of length n (i.e., Motzkin paths of length n with no (1,0)-steps at positive heights) having no DHU's (here U=(1,1), H=(1,0), and D=(1,-1)).

Source: https://oeis.org/A191398
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 3, 6, 9, 18, 28, 56, ...
The entry gives the generating function
  2/(1-z-2*z^3+(1-z)*sqrt(1-4*z^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (-2*x^3 - x + 1 + (x - 1)*sqrt(R)) / (2*x^6 + 4*x^4 - 6*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: -(n+2)*(n-3)*a(n) +(3*n^2-3*n-14)*a(n-1) +2*(n^2-7*n+8)*a(n-2) +4*(-3*n^2+12*n-10)*a(n-3) +(7*n^2-31*n+38)*a(n-4) +4*a(n-5) +4*(n-2)^2*a(n-6)=0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a191398

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A191398: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - X - 2 * X ^ 3 + (-1 + X) * S)
      * (2 - 6 * X + 4 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A191398. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (-(n : ℚ) ^ 2 + (n : ℚ) + 6) * a n + (3 * (n : ℚ) ^ 2 - 3 * (n : ℚ) - 14) * a (n - 1)
      + (2 * (n : ℚ) ^ 2 - 14 * (n : ℚ) + 16) * a (n - 2)
      + (-12 * (n : ℚ) ^ 2 + 48 * (n : ℚ) - 40) * a (n - 3)
      + (7 * (n : ℚ) ^ 2 - 31 * (n : ℚ) + 38) * a (n - 4) + (4) * a (n - 5)
      + (4 * (n : ℚ) ^ 2 - 16 * (n : ℚ) + 16) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a191398
