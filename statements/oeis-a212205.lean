import Mathlib

/-!
# A212205: Mathar's recurrence

Source: https://oeis.org/A212205
Credit: @ivillar

A212205 (offset 0): g.f. ((1+2*x)*sqrt(1-6*x^2+x^4)-1+5*x^2-2*x^3)/(2*x*(1-6*x^2));
data 1, 1, 2, 4, 8, 18, 36, 86, 172, 426, 852, 2162, ...

Conjecture (R. J. Mathar, Aug 20 2018): D-finite with recurrence
(n+1)*a(n) + 2*(n-1)*a(n-1) + 6*(-2*n+1)*a(n-2) + 12*(-2*n+5)*a(n-3) + (37*n-77)*a(n-4)
+ 2*(37*n-151)*a(n-5) + 6*(-n+5)*a(n-6) + 12*(-n+7)*a(n-7) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-6*x^2+x^4 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
2*x*(1-6*x^2)*G = (1+2*x)*S - 1 + 5*x^2 - 2*x^3;
a(n) = [x^n] G. The recurrence involves a(n-7), so it is stated for n ≥ 7; it is checked by the data, for
example at n = 7: (8)*(86) + (12)*(36) + (-78)*(18) + (-108)*(8) + (182)*(4) + (216)*(2) + (-12)*(1) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a212205

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A212205, for n ≥ 7. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 6 * X ^ 2 + X ^ 4 →
    coeff 0 S = 1 →
    2 * X * (1 - 6 * X ^ 2) * G = (1 + 2 * X) * S - 1 + 5 * X ^ 2 - 2 * X ^ 3 →
    ∀ n : ℕ, 7 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (-2 + 2 * (n : ℚ)) * coeff (n - 1) G +
        (6 - 12 * (n : ℚ)) * coeff (n - 2) G + (60 - 24 * (n : ℚ)) * coeff (n - 3) G +
        (-77 + 37 * (n : ℚ)) * coeff (n - 4) G + (-302 + 74 * (n : ℚ)) * coeff (n - 5) G +
        (30 - 6 * (n : ℚ)) * coeff (n - 6) G + (84 - 12 * (n : ℚ)) * coeff (n - 7) G = 0 := by
  sorry

end OMA.S_oeis_a212205
