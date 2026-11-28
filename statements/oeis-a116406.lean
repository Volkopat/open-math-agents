import Mathlib

/-!
# A116406: Mathar's recurrence

Source: https://oeis.org/A116406
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A116406 (offset 0): expansion of ((1 + x - 2x^2) + (1+x)*sqrt(1-4x^2))/(2(1-4x^2));
data 1, 1, 2, 3, 7, 11, 26, 42, 99, 163, 382, 638, ...

Conjecture (R. J. Mathar, Nov 28 2014):
n*(n-3)*a(n) +2*(-n^2+4*n-2)*a(n-1) -4*(n-2)^2*a(n-2) +8*(n-2)*(n-3)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
2*(1 - 4*x^2)*G = (1 + x - 2*x^2) + (1 + x)*S;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (0)*(3) + (2)*(2) + (-4)*(1) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a116406

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A116406, for n ≥ 3. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X ^ 2 →
    coeff 0 S = 1 →
    2 * (1 - 4 * X ^ 2) * G = (1 + X - 2 * X ^ 2) + (1 + X) * S →
    ∀ n : ℕ, 3 ≤ n →
      (-3 * (n : ℚ) + (n : ℚ) ^ 2) * coeff n G + (-4 + 8 * (n : ℚ) - 2 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-16 + 16 * (n : ℚ) - 4 * (n : ℚ) ^ 2) * coeff (n - 2) G + (48 - 40 * (n : ℚ) + 8 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a116406
