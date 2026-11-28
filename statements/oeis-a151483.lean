import Mathlib

/-!
# A151483: Mathar's recurrence

Source: https://oeis.org/A151483
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A151483 (offset 0): number of walks within N^2 (the first quadrant of Z^2) starting at (0,0), ending
on the vertical axis and consisting of n steps taken from
{(-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0)};
data 1, 1, 4, 12, 48, 192, 832, 3712, 17152, 81152, 392192, 1928192, ...

Conjecture (R. J. Mathar, Jun 14 2016):
+(n+3)*a(n) -4*n*a(n-1) +12*(-n+1)*a(n-2) = 0.

Formalization: the entry gives the g.f. in closed form,
((1-6*x)*(1-4*x-12*x^2)^(1/2)-4*x^2+8*x-1)/(32*x^3) (Mark van Hoeij, Aug 20 2014), and this closed
form is used as the definition here. S is the formal power series over ℚ with
S^2 = 1-4*x-12*x^2 and constant term 1 (the constant term selects the branch of the square root),
and the g.f. G is determined by 32*x^3*G = (1 - 6*x)*S - 4*x^2 + 8*x - 1;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (5)*(4) + (-8)*(1) + (-12)*(1) = 0.
-/

namespace OMA.S_oeis_a151483

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A151483, for n ≥ 2. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X - 12 * X ^ 2 →
    coeff 0 S = 1 →
    32 * X ^ 3 * G = (1 - 6 * X) * S - 4 * X ^ 2 + 8 * X - 1 →
    ∀ n : ℕ, 2 ≤ n →
      (3 + (n : ℚ)) * coeff n G + (-4 * (n : ℚ)) * coeff (n - 1) G +
        (12 - 12 * (n : ℚ)) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a151483
