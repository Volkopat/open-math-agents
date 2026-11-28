import Mathlib

/-!
# A247102: Mathar's recurrence

Source: https://oeis.org/A247102
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A247102 (offset 0): expansion of g.f. (6*x+2)/(sqrt(-3*x^2-6*x+1)*(4*x^2+4*x)) - (2*x+1)/(2*x^2+2*x);
data 2, 10, 53, 298, 1727, 10207, 61154, 370090, 2256983, 13848085, 85387040, 528646015, ...

Conjecture (R. J. Mathar, Jan 25 2020): D-finite with recurrence
(n+1)*a(n) + (-2*n-5)*a(n-1) + 3*(-8*n+7)*a(n-2) + 15*(-2*n+3)*a(n-3) + 9*(-n+2)*a(n-4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = -3*x^2-6*x+1 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*(4*x^2+4*x)*S = 6*x + 2 - 2*(2*x+1)*S, which is the stated expression multiplied by
S*(4*x^2+4*x);
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (5)*(1727) + (-13)*(298) + (-75)*(53) + (-75)*(10) + (-18)*(2) = 0.
-/

namespace OMA.S_oeis_a247102

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A247102, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 6 * X - 3 * X ^ 2 →
    coeff 0 S = 1 →
    G * ((4 * X ^ 2 + 4 * X) * S) = 6 * X + 2 - 2 * (2 * X + 1) * S →
    ∀ n : ℕ, 4 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (-5 - 2 * (n : ℚ)) * coeff (n - 1) G +
        (21 - 24 * (n : ℚ)) * coeff (n - 2) G + (45 - 30 * (n : ℚ)) * coeff (n - 3) G +
        (18 - 9 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a247102
