import Mathlib

/-!
# A239204: Mathar's recurrence

Source: https://oeis.org/A239204
Credit: @ivillar

A239204 (offset 0): expansion of ((x-1)*sqrt(x^2-6*x+1)-x^2-4*x+1)/(8*x^3);
data 1, 4, 17, 76, 353, 1688, 8257, 41128, ...

Conjecture (R. J. Mathar, Nov 02 2014): D-finite with recurrence
(n+3)*a(n) + (-7*n-10)*a(n-1) + (7*n-3)*a(n-2) + (-n+2)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = x^2-6*x+1 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
8*x^3*G = (x-1)*S - x^2 - 4*x + 1; a(n) = [x^n] G. The recurrence involves a(n-3), so it is
stated for n ≥ 3; it is checked by the data, for example at n = 4:
7*353 - 38*76 + 25*17 - 2*4 = 0.
-/

namespace OMA.S_oeis_a239204

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A239204. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = X ^ 2 - 6 * X + 1 → coeff 0 S = 1 →
    8 * X ^ 3 * G = (X - 1) * S - X ^ 2 - 4 * X + 1 →
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℚ) + 3) * coeff n G + (-7 * (n : ℚ) - 10) * coeff (n - 1) G +
        (7 * (n : ℚ) - 3) * coeff (n - 2) G + (-(n : ℚ) + 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a239204
