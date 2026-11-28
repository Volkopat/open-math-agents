import Mathlib

/-!
# A157328: Mathar's recurrence

Source: https://oeis.org/A157328
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A157328 (offset 0): expansion of 1/(1-2x*c(4x)) with c(x) g.f. of Catalan numbers (A000108);
data 1, 2, 12, 104, 1072, 12192, 147648, 1867392, 24380160, 326105600, 4445965312, 61555599360, ...

Conjecture (R. J. Mathar, Dec 14 2011):
n*a(n) + 2*(12 - 7n)*a(n - 1) + 16*(3 - 2n)*a(n - 2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-16*x and constant term 1, that is S = sqrt(1-16x)
(the constant term selects the branch of the square root); c is the series c(4x), with c(x) the Catalan
g.f., determined by 8*x*c = 1 - S; and the g.f. G is determined by G*(1 - 2*x*c) = 1;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (2)*(12) + (-4)*(2) + (-16)*(1) = 0.
-/

namespace OMA.S_oeis_a157328

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A157328, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 16 * X →
    coeff 0 S = 1 →
    8 * X * c = 1 - S →
    G * (1 - 2 * X * c) = 1 →
    ∀ n : ℕ, 2 ≤ n →
      ((n : ℚ)) * coeff n G + (24 - 14 * (n : ℚ)) * coeff (n - 1) G +
        (48 - 32 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a157328
