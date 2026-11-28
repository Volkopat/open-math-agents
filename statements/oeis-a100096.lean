import Mathlib

/-!
# A100096: An inverse Chebyshev transform of the Jacobsthal numbers.

Source: https://oeis.org/A100096
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 1, 1, 6, 9, 36, 66, 218, 449, ...
The entry gives the generating function
  x*sqrt(1-4*x^2)*(3*sqrt(1-4*x^2)+2*x+1)/(2*(4*x^2-1)*(10*x^2+x-2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (-6*x^2 + 3*x + (x)*sqrt(R)) / (40*x^3 - 16*x^2 - 10*x + 4),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 24 2012) reads
  Conjecture: 2*(-n+1)*a(n) +(n+3)*a(n-1) +18*(n-2)*a(n-2) +4*(-n-2)*a(n-3) +40*(-n+3)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a100096

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A100096: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((3 * X - 6 * X ^ 2 + (X) * S)
      * (4 - 10 * X - 16 * X ^ 2 + 40 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A100096. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (-2 * (n : ℚ) + 2) * a n + ((n : ℚ) + 3) * a (n - 1) + (18 * (n : ℚ) - 36) * a (n - 2)
      + (-4 * (n : ℚ) - 8) * a (n - 3) + (-40 * (n : ℚ) + 120) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a100096
