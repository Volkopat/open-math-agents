import Mathlib

/-!
# A071684: Mathar's recurrence

Source: https://oeis.org/A071684
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Jul 05 2018); the entry records it as a conjecture and notes no proof or
verification of it.

A071684 (offset 1): number of plane trees with n edges and having an odd number of leaves;
data 1, 1, 2, 7, 22, 66, 212, 715, 2438, 8398, 29372, 104006, ...

Conjecture (R. J. Mathar, Jul 05 2018):
n*(n+1)*(10*n-37)*a(n) + 2*n*(5*n^2-42*n+91)*a(n-1) + 4*(-40*n^3+270*n^2-560*n+357)*a(n-2) +
8*(n-3)*(5*n^2-42*n+91)*a(n-3) - 16*(n-4)*(25*n-51)*(2*n-7)*a(n-4) = 0.

Formalization: The entry gives the g.f. (1/4)*((1+4*x^2)^(1/2) - (1-4*x)^(1/2) - 2*x)/x (Vladeta Jovovic, Apr 19 2003), and
this closed form is used as the definition here. T and W are the formal power series over ℚ with
T^2 = 1-4*x, W^2 = 1+4*x^2 and constant terms 1 (the constant terms select the branches of the square
roots); and G is determined by 4*x*G = W - T - 2*x (its constant term 0 is recorded as a hypothesis);
a(n) = [x^n] G. The sequence has offset 1, and [x^k] G = 0 for k < 1. The recurrence involves a(n-4); with
a(k) read as [x^k] G (so a(k) = 0 below the offset) it holds for n ≥ 4, and `main` is stated
for this range, which contains every n ≥ 5 (where all indices are at least the offset).
It is checked by the data, for example at n = 5:
(390)*(22) + (60)*(7) + (-2772)*(2) + (96)*(1) + (-3552)*(1) = 0.
-/

namespace OMA.S_oeis_a071684

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A071684, for n ≥ 4. -/
theorem main : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 4 * X →
    coeff 0 T = 1 →
    W ^ 2 = 1 + 4 * X ^ 2 →
    coeff 0 W = 1 →
    4 * X * G = W - T - 2 * X →
    coeff 0 G = 0 →
    ∀ n : ℕ, 4 ≤ n →
      (-37 * (n : ℚ) - 27 * (n : ℚ) ^ 2 + 10 * (n : ℚ) ^ 3) * coeff n G + (182 * (n : ℚ) - 84 * (n : ℚ) ^ 2 + 10 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (1428 - 2240 * (n : ℚ) + 1080 * (n : ℚ) ^ 2 - 160 * (n : ℚ) ^ 3) * coeff (n - 2) G + (-2184 + 1736 * (n : ℚ) - 456 * (n : ℚ) ^ 2 + 40 * (n : ℚ) ^ 3) * coeff (n - 3) G +
        (22848 - 23440 * (n : ℚ) + 7632 * (n : ℚ) ^ 2 - 800 * (n : ℚ) ^ 3) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a071684
