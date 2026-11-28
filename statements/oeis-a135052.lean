import Mathlib

/-!
# A135052: Mathar's recurrence

Source: https://oeis.org/A135052
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A135052 (offset 0): expansion of g.f.: (1-2*x-sqrt(1-4*x+8*x^3-4*x^4))/(2*x^2*(1-x));
data 1, 1, 3, 7, 19, 51, 143, 407, 1183, 3487, 10415, 31439, ...

Conjecture (R. J. Mathar, Apr 19 2015): D-finite with recurrence
(n + 2)*a(n) + (-5*n - 4)*a(n - 1) + 2*(2*n + 1)*a(n - 2) + 4*(2*n - 5)*a(n - 3) + 12*(-n + 3)*a(n
- 4) + 4*(n - 4)*a(n - 5) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x+8*x^3-4*x^4 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
2*x^2*(1 - x)*G = 1 - 2*x - S;
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (7)*(51) + (-29)*(19) + (22)*(7) + (20)*(3) + (-24)*(1) + (4)*(1) = 0.
-/

namespace OMA.S_oeis_a135052

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A135052, for n ≥ 5. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X + 8 * X ^ 3 - 4 * X ^ 4 →
    coeff 0 S = 1 →
    2 * X ^ 2 * (1 - X) * G = 1 - 2 * X - S →
    ∀ n : ℕ, 5 ≤ n →
      (2 + (n : ℚ)) * coeff n G + (-4 - 5 * (n : ℚ)) * coeff (n - 1) G +
        (2 + 4 * (n : ℚ)) * coeff (n - 2) G + (-20 + 8 * (n : ℚ)) * coeff (n - 3) G +
        (36 - 12 * (n : ℚ)) * coeff (n - 4) G + (-16 + 4 * (n : ℚ)) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a135052
