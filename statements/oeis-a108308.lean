import Mathlib

/-!
# A108308: Mathar's recurrence

Source: https://oeis.org/A108308
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A108308 (offset 0): expansion of 1/(1-x^2*c(2*x)), c(x) the g.f. of A000108;
data 1, 0, 1, 2, 9, 44, 245, 1462, 9157, 59368, 395033, 2682282, ...

Conjecture (R. J. Mathar, Dec 10 2011):
2*(n-1)*a(n) + (41-17*n)*a(n-1) + 4*(2*n-5)*a(n-2) + (n-1)*a(n-3) + 4*(5-2*n)*a(n-4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-8*x and constant term 1, that is S = sqrt(1-8x)
(the constant term selects the branch of the square root); c is the series c(2x), with c(x) the Catalan
g.f., determined by 4*x*c = 1 - S; and the g.f. G is determined by G*(1 - x^2*c) = 1;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (6)*(9) + (-27)*(2) + (12)*(1) + (3)*(0) + (-12)*(1) = 0.
-/

namespace OMA.S_oeis_a108308

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A108308, for n ≥ 4. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 8 * X →
    coeff 0 S = 1 →
    4 * X * c = 1 - S →
    G * (1 - X ^ 2 * c) = 1 →
    ∀ n : ℕ, 4 ≤ n →
      (-2 + 2 * (n : ℚ)) * coeff n G + (41 - 17 * (n : ℚ)) * coeff (n - 1) G +
        (-20 + 8 * (n : ℚ)) * coeff (n - 2) G + (-1 + (n : ℚ)) * coeff (n - 3) G +
        (20 - 8 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a108308
