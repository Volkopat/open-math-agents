import Mathlib

/-!
# A166290: Number of UDUD's in all Dyck paths of semilength n with no UUU's and no DDD's (U=(1,1), D=(1,-1)).

Source: https://oeis.org/A166290
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 1, 3, 9, 24, 63, 164, 423, ...
The entry gives the generating function
  (z-1)*(z+2)/(2*z^2) + (2-3*z-2*z^2-2*z^3+z^4) / [2*z^2*sqrt((1+z+z^2)*(1-3z+z^2))]
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 2*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (x^6 - x^5 - 5*x^4 + x^3 + x^2 + 5*x - 2 + (x^4 - 2*x^3 - 2*x^2 - 3*x + 2)*sqrt(R)) / (2*x^6 - 4*x^5 - 2*x^4 - 4*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: -(n+2)*(60283*n-319055)*a(n) +(-60283*n^2-13090*n+236862)*a(n-1) +(588710*n^2-2858167*n+437486)*a(n-2) +(-32043*n^2+2024290*n-2826488)*a(n-3) +(134686*n^2+585099*n-3417942)*a(n-4) +(-514307*n^2+4366464*n-8945002)*a(n-5) +(166729*n-863288)*(n-6)*a(n-6)=0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a166290

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A166290: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((-2 + 5 * X + X ^ 2 + X ^ 3 - 5 * X ^ 4 - X ^ 5 + X ^ 6 + (2 - 3 * X - 2 * X ^ 2 - 2 * X ^ 3 + X ^ 4) * S)
      * (2 - 4 * X - 2 * X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A166290. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (-60283 * (n : ℚ) ^ 2 + 198489 * (n : ℚ) + 638110) * a n
      + (-60283 * (n : ℚ) ^ 2 - 13090 * (n : ℚ) + 236862) * a (n - 1)
      + (588710 * (n : ℚ) ^ 2 - 2858167 * (n : ℚ) + 437486) * a (n - 2)
      + (-32043 * (n : ℚ) ^ 2 + 2024290 * (n : ℚ) - 2826488) * a (n - 3)
      + (134686 * (n : ℚ) ^ 2 + 585099 * (n : ℚ) - 3417942) * a (n - 4)
      + (-514307 * (n : ℚ) ^ 2 + 4366464 * (n : ℚ) - 8945002) * a (n - 5)
      + (166729 * (n : ℚ) ^ 2 - 1863662 * (n : ℚ) + 5179728) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a166290
