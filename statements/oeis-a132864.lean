import Mathlib

/-!
# A132864: Mathar's recurrence

Source: https://oeis.org/A132864
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A132864 (offset 0): expansion of 1/(1-4x*c(5x)), where c(x) is the g.f. of A000108;
data 1, 4, 36, 424, 5716, 83544, 1288296, 20637264, 340116276, 5730014584, 98241641656, 1708602483504, ...

Conjecture (R. J. Mathar, Nov 15 2011):
n*a(n) + 2*(15 - 2*n)*a(n - 1) + 160*(3 - 2*n)*a(n - 2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-20*x and constant term 1, that is S = sqrt(1-20x)
(the constant term selects the branch of the square root); c is the series c(5x), with c(x) the Catalan
g.f., determined by 10*x*c = 1 - S; and the g.f. G is determined by G*(1 - 4*x*c) = 1;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (2)*(36) + (22)*(4) + (-160)*(1) = 0.
-/

namespace OMA.S_oeis_a132864

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A132864, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 20 * X →
    coeff 0 S = 1 →
    10 * X * c = 1 - S →
    G * (1 - 4 * X * c) = 1 →
    ∀ n : ℕ, 2 ≤ n →
      ((n : ℚ)) * coeff n G + (30 - 4 * (n : ℚ)) * coeff (n - 1) G +
        (480 - 320 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a132864
