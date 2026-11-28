import Mathlib

/-!
# A100099: An inverse Chebyshev transform of x/(1-2x).

Source: https://oeis.org/A100099
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 1, 2, 7, 16, 46, 110, 295, 720, ...
The entry gives the generating function
  sqrt(1-4x^2)(sqrt(1-4x^2)+4x-1)/(2(5x-2)(4x^2-1))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (1 - 4*x^2 + (4*x - 1)*sqrt(R)) / (40*x^3 - 16*x^2 - 10*x + 4),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Dec 14 2011) reads
  Conjecture: 2n*a(n) +(-13n+16)*a(n-1) +4(3n-8)*a(n-2) +4(13n-29)*a(n-3) +80(3-n)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a100099

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A100099: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 4 * X ^ 2 + (-1 + 4 * X) * S)
      * (4 - 10 * X - 16 * X ^ 2 + 40 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A100099. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (2 * (n : ℚ)) * a n + (-13 * (n : ℚ) + 16) * a (n - 1) + (12 * (n : ℚ) - 32) * a (n - 2)
      + (52 * (n : ℚ) - 116) * a (n - 3) + (-80 * (n : ℚ) + 240) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a100099
