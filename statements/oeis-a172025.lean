import Mathlib

/-!
# A172025: Mathar's recurrence

Source: https://oeis.org/A172025
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A172025 (offset 0): expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=3;
data 1, 4, 16, 62, 239, 920, 3544, 13672, 52834, 204528, 793092, 3080226, ...

Conjecture (R. J. Mathar, Feb 19 2016):
2*n*(n+3)*a(n) + (-7*n^2 - 17*n - 8)*a(n-1) -2*(n+2)*(2*n+1)*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1, that is S = sqrt(1-4x)
(the constant term selects the branch of the square root); c is the series c(x), with c(x) the Catalan
g.f., determined by 2*x*c = 1 - S; and the g.f. G is determined by G*(3*S - 1 + 4*x) = 2*c^3;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (20)*(16) + (-70)*(4) + (-40)*(1) = 0.
-/

namespace OMA.S_oeis_a172025

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A172025, for n ≥ 2. -/
theorem main : ∀ S c G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * c = 1 - S →
    G * (3 * S - 1 + 4 * X) = 2 * c ^ 3 →
    ∀ n : ℕ, 2 ≤ n →
      (6 * (n : ℚ) + 2 * (n : ℚ) ^ 2) * coeff n G + (-8 - 17 * (n : ℚ) - 7 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-4 - 10 * (n : ℚ) - 4 * (n : ℚ) ^ 2) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a172025
