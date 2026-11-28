import Mathlib

/-!
# A184120: Mathar's recurrence

Source: https://oeis.org/A184120
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A184120 (offset 0): expansion of (1/(1+4x+2x^2))*c(x/(1+4x+2x^2)), c(x) the g.f. of A000108;
data 1, -3, 8, -23, 70, -218, 688, -2195, 7062, -22866, 74416, -243206, ...

Conjecture (R. J. Mathar, Nov 17 2011):
(n+1)*a(n) +2*(2n+1)*a(n-1) +4*(n-1)*a(n-2) +4*(2n-5)*a(n-3) +4*(n-3)*a(n-4) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1+4*x+2*x^2) = 1+2*x^2 and constant term 1, that is
T = sqrt(1 - 4*y) for y = x/(1+4*x+2*x^2) (the constant term selects the branch of the square root). Since
y*c(y) = (1 - sqrt(1-4*y))/2 for the Catalan g.f. c, the stated g.f. G is determined by
2*x*G = 1 - T;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (5)*(70) + (18)*(-23) + (12)*(8) + (12)*(-3) + (4)*(1) = 0.
-/

namespace OMA.S_oeis_a184120

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A184120, for n ≥ 4. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * (1 + 4 * X + 2 * X ^ 2) = 1 + 2 * X ^ 2 →
    coeff 0 T = 1 →
    2 * X * G = 1 - T →
    ∀ n : ℕ, 4 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (2 + 4 * (n : ℚ)) * coeff (n - 1) G +
        (-4 + 4 * (n : ℚ)) * coeff (n - 2) G + (-20 + 8 * (n : ℚ)) * coeff (n - 3) G +
        (-12 + 4 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a184120
