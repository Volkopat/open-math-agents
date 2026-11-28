import Mathlib

/-!
# A166300: Number of Dyck paths of semilength n, having no ascents and no descents of length 1, and having no UUDD's starting at level 0.

Source: https://oeis.org/A166300
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 0, 0, 1, 1, 2, 5, 10, 22, ...
The entry gives the generating function
  2/(1 + z + z^2 + sqrt((1 + z + z^2)*(1 - 3*z + z^2)))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 2*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (x^2 + x + 1 + (-1)*sqrt(R)) / (2*x^3 + 2*x^2 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 24 2012) reads
  Conjecture: (n+1)*a(n) +2*(-n+1)*a(n-1) +(-n+1)*a(n-2) +2*(-n+1)*a(n-3) +(n-3)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a166300

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A166300: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 + X + X ^ 2 - S)
      * (2 + 2 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A166300. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 1) * a n + (-2 * (n : ℚ) + 2) * a (n - 1) + (-(n : ℚ) + 1) * a (n - 2)
      + (-2 * (n : ℚ) + 2) * a (n - 3) + ((n : ℚ) - 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a166300
