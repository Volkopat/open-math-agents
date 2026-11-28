import Mathlib

/-!
# A101601: Mathar's recurrence

Source: https://oeis.org/A101601
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A101601 (offset 0): expansion of g.f. c(3x)^3, where c(x) is the g.f. of A000108;
data 1, 9, 81, 756, 7290, 72171, 729729, 7505784, 78298974, 826489170, 8811646074, 94753804536, ...

Conjecture (R. J. Mathar, Nov 15 2011):
(n+3)*a(n) - 3*(5*n+7)*a(n-1) + 18*(2*n-1)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-12*x and constant term 1, that is S = sqrt(1-12x)
(the constant term selects the branch of the square root); c is the series c(3x), with c(x) the Catalan
g.f., determined by 6*x*c = 1 - S; and the g.f. G is determined by G = c^3;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (5)*(81) + (-51)*(9) + (54)*(1) = 0.
-/

namespace OMA.S_oeis_a101601

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A101601, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 12 * X →
    coeff 0 S = 1 →
    6 * X * c = 1 - S →
    G = c ^ 3 →
    ∀ n : ℕ, 2 ≤ n →
      (3 + (n : ℚ)) * coeff n G + (-21 - 15 * (n : ℚ)) * coeff (n - 1) G +
        (-18 + 36 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a101601
