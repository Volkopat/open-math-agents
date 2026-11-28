import Mathlib

/-!
# A174783: Mathar's recurrence

Source: https://oeis.org/A174783
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A174783 (offset 0): expansion of (1+2x-sqrt(1-4x^2))/(2(1-x^2)*sqrt(1-4x^2));
data 0, 1, 1, 3, 4, 9, 14, 29, 49, 99, 175, 351, ...

Conjecture (R. J. Mathar, Nov 13 2012):
n*a(n) - 2*a(n - 1) + (8 - 5*n)*a(n - 2) + 2*a(n - 3) + 4*(n - 2)*a(n - 4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*(2*(1 - x^2)*S) = 1 + 2*x - S;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (4)*(4) + (-2)*(3) + (-12)*(1) + (2)*(1) + (8)*(0) = 0.
-/

namespace OMA.S_oeis_a174783

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A174783, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X ^ 2 →
    coeff 0 S = 1 →
    G * (2 * (1 - X ^ 2) * S) = 1 + 2 * X - S →
    ∀ n : ℕ, 4 ≤ n →
      ((n : ℚ)) * coeff n G + (-2) * coeff (n - 1) G +
        (8 - 5 * (n : ℚ)) * coeff (n - 2) G + (2) * coeff (n - 3) G +
        (-8 + 4 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a174783
