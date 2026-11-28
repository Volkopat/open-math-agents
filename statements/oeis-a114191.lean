import Mathlib

/-!
# A114191: Mathar's recurrence

Source: https://oeis.org/A114191
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A114191 (offset 0): expansion of 1/(1+x*c(-2*x)), c(x) the g.f. of A000108;
data 1, -1, 3, -13, 67, -381, 2307, -14589, 95235, -636925, 4341763, -30056445, ...

Conjecture (R. J. Mathar, Nov 14 2011):
n*a(n) + (7*n-12)*a(n-1) + 4*(3-2*n)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1+8*x and constant term 1, that is S = sqrt(1+8x)
(the constant term selects the branch of the square root); c is the series c(-2x), with c(x) the Catalan
g.f., determined by -4*x*c = 1 - S; and the g.f. G is determined by G*(1 + x*c) = 1;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (2)*(3) + (2)*(-1) + (-4)*(1) = 0.
-/

namespace OMA.S_oeis_a114191

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A114191, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 + 8 * X →
    coeff 0 S = 1 →
    -(4 * X * c) = 1 - S →
    G * (1 + X * c) = 1 →
    ∀ n : ℕ, 2 ≤ n →
      ((n : ℚ)) * coeff n G + (-12 + 7 * (n : ℚ)) * coeff (n - 1) G +
        (12 - 8 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a114191
