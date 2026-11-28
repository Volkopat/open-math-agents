import Mathlib

/-!
# A132364: Mathar's recurrence

Source: https://oeis.org/A132364
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A132364 (offset 0): expansion of 1/(1-x^2*c(x)), c(x) the g.f. of A000108;
data 1, 0, 1, 1, 3, 7, 20, 59, 184, 593, 1964, 6642, ...

Conjecture (R. J. Mathar, Aug 28 2015):
(-n + 1)*a(n) + (5*n - 11)*a(n - 1) + 2*(-2*n + 5)*a(n - 2) + (-n + 1)*a(n - 3) + 2*(2*n - 5)*a(n
- 4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(1 - x^2*c) = 1;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (-3)*(3) + (9)*(1) + (-6)*(1) + (-3)*(0) + (6)*(1) = 0.
-/

namespace OMA.S_oeis_a132364

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A132364, for n ≥ 4. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (1 - X ^ 2 * c) = 1 →
    ∀ n : ℕ, 4 ≤ n →
      (1 - (n : ℚ)) * coeff n G + (-11 + 5 * (n : ℚ)) * coeff (n - 1) G +
        (10 - 4 * (n : ℚ)) * coeff (n - 2) G + (1 - (n : ℚ)) * coeff (n - 3) G +
        (-10 + 4 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a132364
