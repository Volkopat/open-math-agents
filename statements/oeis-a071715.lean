import Mathlib

/-!
# A071715: Mathar's recurrence

Source: https://oeis.org/A071715
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A071715 (offset 0): expansion of (1+x*C^4)*C^4, where C = (1-(1-4*x)^(1/2))/(2*x) is g.f. for Catalan numbers, A000108;
data 1, 5, 22, 92, 373, 1482, 5810, 22576, 87210, 335597, 1288276, 4938100, ...

Conjecture (R. J. Mathar, Aug 25 2013):
(891*n+6824)*(n+7)*a(n) + (891*n^2-38453*n-250970)*a(n-1) + 4*(-5040*n^2-4271*n+8095)*a(n-2) +
4*(1170*n+3847)*(2*n-1)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G = (1 + x*c^4)*c^4;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (94970)*(92) + (-358310)*(22) + (-200312)*(5) + (147140)*(1) = 0.
-/

namespace OMA.S_oeis_a071715

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A071715, for n ≥ 3. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G = (1 + X * c ^ 4) * c ^ 4 →
    ∀ n : ℕ, 3 ≤ n →
      (47768 + 13061 * (n : ℚ) + 891 * (n : ℚ) ^ 2) * coeff n G + (-250970 - 38453 * (n : ℚ) + 891 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (32380 - 17084 * (n : ℚ) - 20160 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-15388 + 26096 * (n : ℚ) + 9360 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a071715
