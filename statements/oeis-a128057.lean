import Mathlib

/-!
# A128057: Mathar's recurrence

Source: https://oeis.org/A128057
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A128057 (offset 0): expansion of (1+x)/sqrt(1+4x^2);
data 1, 1, -2, -2, 6, 6, -20, -20, 70, 70, -252, -252, ...

Conjecture (R. J. Mathar, Dec 02 2014):
n*(5*n-9)*a(n) +4*a(n-1) +4*(5*n-4)*(n-2)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1+4*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*S = 1 + x;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (2)*(-2) + (4)*(1) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a128057

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A128057, for n ≥ 2. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 + 4 * X ^ 2 →
    coeff 0 S = 1 →
    G * S = 1 + X →
    ∀ n : ℕ, 2 ≤ n →
      (-9 * (n : ℚ) + 5 * (n : ℚ) ^ 2) * coeff n G + (4) * coeff (n - 1) G +
        (32 - 56 * (n : ℚ) + 20 * (n : ℚ) ^ 2) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a128057
