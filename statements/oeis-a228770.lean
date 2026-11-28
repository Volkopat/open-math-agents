import Mathlib

/-!
# A228770: The number of sum indecomposable permutations which avoid the patterns 3124 and 4312.

Source: https://oeis.org/A228770
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 1, 3, 12, 51, 217, 912, 3785, 15554, ...
The entry gives the generating function
  -(24*x^6 - 71*x^5 + 84*x^4 - 45*x^3 + 11*x^2 + sqrt(-4*x + 1)*(4*x^6 - 25*x^5 + 40*x^4 - 29*x^3 + 9*x^2 - x) - x)/(8*x^6 - 54*x^5 + 117*x^4 - 114*x^3 + 54*x^2 - sqrt(-4*x + 1)*(12*x^5 - 43*x^4 + 58*x^3 - 36*x^2 + 10*x - 1) - 12*x + 1)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (9*x^3 - 18*x^2 + 8*x - 1 + (4*x^4 - 7*x^3 + 10*x^2 - 6*x + 1)*sqrt(R)) / (-8*x^4 + 18*x^3 - 12*x^2 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: -(n+1)*(39961*n-2474598)*a(n) +(-39961*n^2-25975201*n+4949196) *a(n-1) +3*(1460811*n^2+27429105*n-41310802) *a(n-2) +3 *(-8653921*n^2-4750029*n+74360724) *a(n-3) +4*(15005713*n^2-82481258*n+83094771) *a(n-4) +12*(-4937548*n^2+40726604*n-73155719) *a(n-5) +16*(652718*n-2110173)*(2*n-13) *a(n-6)=0
It involves a(n-6) and the offset is 1, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a228770

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A228770: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((-1 + 8 * X - 18 * X ^ 2 + 9 * X ^ 3 + (1 - 6 * X + 10 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4) * S)
      * (2 - 12 * X + 18 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A228770. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (-39961 * (n : ℚ) ^ 2 + 2434637 * (n : ℚ) + 2474598) * a n
      + (-39961 * (n : ℚ) ^ 2 - 25975201 * (n : ℚ) + 4949196) * a (n - 1)
      + (4382433 * (n : ℚ) ^ 2 + 82287315 * (n : ℚ) - 123932406) * a (n - 2)
      + (-25961763 * (n : ℚ) ^ 2 - 14250087 * (n : ℚ) + 223082172) * a (n - 3)
      + (60022852 * (n : ℚ) ^ 2 - 329925032 * (n : ℚ) + 332379084) * a (n - 4)
      + (-59250576 * (n : ℚ) ^ 2 + 488719248 * (n : ℚ) - 877868628) * a (n - 5)
      + (20886976 * (n : ℚ) ^ 2 - 203290880 * (n : ℚ) + 438915984) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a228770
