import Mathlib

/-!
# A114584: Number of Motzkin paths of length n having no UHD's (U=(1,1), H=(1,0), D=(1,-1)).

Source: https://oeis.org/A114584
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 3, 7, 15, 36, 85, 209, ...
The entry gives the generating function
  (1-z+z^3-sqrt((1+z+z^3)(1-3z+z^3)))/(2z^2)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^6 - 2*x^4 + 2*x^3 - 3*x^2 - 2*x + 1 the series is, in normalised form,
  (x^3 - x + 1 + (-1)*sqrt(R)) / (2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Feb 16 2018) reads
  Conjecture: +(n+2)*a(n) +(n+2)*a(n-1) +3*(-3*n+2)*a(n-2) +(-7*n+13)*a(n-3) +(4*n-13)*a(n-4) +6*(-n+5)*a(n-5) +(n-7)*a(n-6) +3*(n-8)*a(n-7)=0
It involves a(n-7) and the offset is 0, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a114584

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2 + 2 * X ^ 3 - 2 * X ^ 4 + X ^ 6

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A114584: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - X + X ^ 3 - S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A114584. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    ((n : ℚ) + 2) * a n + ((n : ℚ) + 2) * a (n - 1) + (-9 * (n : ℚ) + 6) * a (n - 2)
      + (-7 * (n : ℚ) + 13) * a (n - 3) + (4 * (n : ℚ) - 13) * a (n - 4)
      + (-6 * (n : ℚ) + 30) * a (n - 5) + ((n : ℚ) - 7) * a (n - 6)
      + (3 * (n : ℚ) - 24) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a114584
