import Mathlib

/-!
# A188482: Mathar's recurrence

Source: https://oeis.org/A188482
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A188482 (offset 0): diagonal sums of the Riordan matrix (1/(1-4x),(1-sqrt(1-4x))/(2*sqrt(1-4x))) (A188481);
data 1, 4, 17, 71, 295, 1221, 5040, 20761, 85380, 350659, 1438568, 5896098, ...

Conjecture (R. J. Mathar, Jun 14 2016):
(-n+1)*a(n) + (7*n-9)*a(n-1) + 2*(-4*n+7)*a(n-2) + (-15*n+23)*a(n-3) + 2*(-2*n+3)*a(n-4) = 0.

Formalization: The entry gives the g.f. of the diagonal sums in closed form,
(2 - 7*x - 4*x^2 + x*sqrt(1-4*x))/(2 - 14*x + 16*x^2 + 30*x^3 + 8*x^4), and this closed form is used as the
definition here. S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1 (the constant
term selects the branch of the square root), and G is determined by
(2 - 14*x + 16*x^2 + 30*x^3 + 8*x^4)*G = 2 - 7*x - 4*x^2 + x*S;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (-3)*(295) + (19)*(71) + (-18)*(17) + (-37)*(4) + (-10)*(1) = 0.
-/

namespace OMA.S_oeis_a188482

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A188482, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    (2 - 14 * X + 16 * X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4) * G = 2 - 7 * X - 4 * X ^ 2 + X * S →
    ∀ n : ℕ, 4 ≤ n →
      (1 - (n : ℚ)) * coeff n G + (-9 + 7 * (n : ℚ)) * coeff (n - 1) G +
        (14 - 8 * (n : ℚ)) * coeff (n - 2) G + (23 - 15 * (n : ℚ)) * coeff (n - 3) G +
        (6 - 4 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a188482
