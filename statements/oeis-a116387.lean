import Mathlib

/-!
# A116387: Mathar's recurrence

Source: https://oeis.org/A116387
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A116387 (offset 0): expansion of 1/(sqrt(1-2*x-3*x^2)*(2-M(x))), where M(x) is the g.f. of the Motzkin numbers A001006;
data 1, 2, 7, 22, 72, 234, 763, 2486, 8099, 26372, 85833, 279226, ...

Conjecture (R. J. Mathar, Nov 15 2011):
n*(17*n-142)*a(n) + (17*n^2 + 95*n + 138)*a(n-1) + (-391*n^2 + 2488*n - 2908)*a(n-2) + (-17*n^2 -
603*n + 1892)*a(n-3) + 2*(697*n-2021)*(n-4)*a(n-4) + 60*(17*n-47)*(n-4)*a(n-5) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-2*x-3*x^2 and constant term 1, that is
S = sqrt(1-2x-3x^2) (the constant term selects the branch of the square root); M is the Motzkin g.f.,
determined by 2*x^2*M = 1 - x - S; and the g.f. G is determined by G*S*(2 - M) = 1;
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (-285)*(234) + (1038)*(72) + (-243)*(22) + (-1548)*(7) + (2928)*(2) + (2280)*(1) = 0.
-/

namespace OMA.S_oeis_a116387

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A116387, for n ≥ 5. -/
theorem main : ∀ S M G : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
    coeff 0 S = 1 →
    2 * X ^ 2 * M = 1 - X - S →
    G * (S * (2 - M)) = 1 →
    ∀ n : ℕ, 5 ≤ n →
      (-142 * (n : ℚ) + 17 * (n : ℚ) ^ 2) * coeff n G + (138 + 95 * (n : ℚ) + 17 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-2908 + 2488 * (n : ℚ) - 391 * (n : ℚ) ^ 2) * coeff (n - 2) G + (1892 - 603 * (n : ℚ) - 17 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (16168 - 9618 * (n : ℚ) + 1394 * (n : ℚ) ^ 2) * coeff (n - 4) G + (11280 - 6900 * (n : ℚ) + 1020 * (n : ℚ) ^ 2) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a116387
