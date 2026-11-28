import Mathlib

/-!
# A106181: Mathar's recurrence

Source: https://oeis.org/A106181
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A106181 (offset 0): expansion of c(-x^2)(1+2x-sqrt(1+4x^2))/2, c(x) the g.f. of A000108;
data 0, 1, -1, -1, 2, 2, -5, -5, 14, 14, -42, -42, ...

Conjecture (R. J. Mathar, Nov 15 2011):
(n+2)*a(n) + n*a(n-1) + 4*(n-1)*a(n-2) + 4*(n-3)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1+4*x^2 and constant term 1, that is S = sqrt(1+4x^2)
(the constant term selects the branch of the square root); c is the series c(-x^2), with c(x) the Catalan
g.f., determined by -2*x^2*c = 1 - S; and the g.f. G is determined by 2*G = c*(1 + 2*x - S);
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (5)*(-1) + (3)*(-1) + (8)*(1) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a106181

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A106181, for n ≥ 3. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 + 4 * X ^ 2 →
    coeff 0 S = 1 →
    -(2 * X ^ 2 * c) = 1 - S →
    2 * G = c * (1 + 2 * X - S) →
    ∀ n : ℕ, 3 ≤ n →
      (2 + (n : ℚ)) * coeff n G + ((n : ℚ)) * coeff (n - 1) G +
        (-4 + 4 * (n : ℚ)) * coeff (n - 2) G + (-12 + 4 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a106181
