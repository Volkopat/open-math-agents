import Mathlib

/-!
# A099553: Mathar's recurrence

Source: https://oeis.org/A099553
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A099553 (offset 3): number of rooted 2-connected loopless 4-regular planar maps with n inner faces;
data 1, 2, 10, 42, 209, 1066, 5726, 31688, 180234, 1047356, 6198500, 37253790, ...

Conjecture (R. J. Mathar, Aug 28 2018):
3*n *(3*n-1) *(5*n-8) *(3*n-2)*a(n) -(n-2) *(2*n-3) *(355*n^2 -703*n +300)*a(n-1)
-98*(n-2) *(5*n-3) *(2*n-3) *(2*n-5) *a(n-2) = 0.

Formalization: the entry gives the algebraic equation
0 = 8*y^4 + (32*x + 12)*y^3 + (48*x^2 + 23*x + 6)*y^2 + (32*x^3 + 10*x^2 - 10*x + 1)*y + x^3*(8*x - 1)
for the g.f. y = A(x) (Gheorghe Coserea, Jul 12 2018), and this is used as the definition here. G is
the formal power series over ℚ with zero constant term satisfying this equation (at x = 0 the
equation reads y*(2*y+1)^3 = 0, and the constant term 0 selects the g.f. among the solutions);
a(n) = [x^n] G, which is 0 for n < 3. The sequence has offset 3 and the recurrence involves a(n-2), so
every index is at least the offset for n ≥ 5. `main` is stated for n ≥ 4, with a(2) = 0 as given by the
g.f.; this includes every n ≥ 5. It is checked by the data, for example at n = 4:
(15840)*(2) + (-31680)*(1) + (-49980)*(0) = 0.
-/

namespace OMA.S_oeis_a099553

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A099553, for n ≥ 4. -/
theorem main : ∀ G : ℚ⟦X⟧, coeff 0 G = 0 →
    8 * G ^ 4 + (32 * X + 12) * G ^ 3 + (48 * X ^ 2 + 23 * X + 6) * G ^ 2 + (32 * X ^ 3 + 10 * X ^ 2 - 10 * X + 1) * G + X ^ 3 * (8 * X - 1) = 0 →
    ∀ n : ℕ, 4 ≤ n →
      (-48 * (n : ℚ) + 246 * (n : ℚ) ^ 2 - 351 * (n : ℚ) ^ 3 + 135 * (n : ℚ) ^ 4) * coeff n G + (-1800 + 6318 * (n : ℚ) - 7651 * (n : ℚ) ^ 2 + 3891 * (n : ℚ) ^ 3 - 710 * (n : ℚ) ^ 4) * coeff (n - 1) G +
        (-8820 + 28518 * (n : ℚ) - 30086 * (n : ℚ) ^ 2 + 12936 * (n : ℚ) ^ 3 - 1960 * (n : ℚ) ^ 4) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a099553
