import Mathlib

/-!
# A102882: Mathar's recurrence

Source: https://oeis.org/A102882
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A102882 (offset 0): expansion of (1+2x)/sqrt((1-3x^2)(1+4x+5x^2));
data 1, 0, 1, 2, -3, 16, -27, 66, -79, 96, 129, -686, ...

Conjecture (R. J. Mathar, Nov 09 2012):
n*(n+1)*a(n) +2*(2*n+3)*(n-1)*a(n-1) +2*(n^2-7)*a(n-2) +6*(5+n-2*n^2)*a(n-3)
-15*(n+2)*(n-3)*a(n-4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = (1-3*x^2)*(1+4*x+5*x^2) and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*S = 1 + 2*x;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (20)*(-3) + (66)*(2) + (18)*(1) + (-138)*(0) + (-90)*(1) = 0.
-/

namespace OMA.S_oeis_a102882

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A102882, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 + 4 * X + 2 * X ^ 2 - 12 * X ^ 3 - 15 * X ^ 4 →
    coeff 0 S = 1 →
    G * S = 1 + 2 * X →
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℚ) + (n : ℚ) ^ 2) * coeff n G + (-6 + 2 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-14 + 2 * (n : ℚ) ^ 2) * coeff (n - 2) G + (30 + 6 * (n : ℚ) - 12 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (90 + 15 * (n : ℚ) - 15 * (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a102882
