import Mathlib

/-!
# A136304: Mathar's recurrence

Source: https://oeis.org/A136304
Credit: @ivillar

Status: known result. The entry records: Conjecture verified using differential equation -z^3 + 3*z^2 - 3*z + 1 + (6*z^5
- 20*z^4 + 20*z^3 - 18*z^2 + 7*z - 1)*g(z) + (4*z^6 - 13*z^5 + 23*z^4 - 21*z^3 + 8*z^2 - z)*g'(z)
satisfied by the G.f. - Robert Israel, Feb 23 2026

A136304 (offset 0): expansion of g.f. (1-z)^2*(1-sqrt(1-4*z))/(2*z*(1 - 3*z + 2*z^2 - z^3));
data 1, 2, 5, 14, 40, 116, 344, 1047, 3273, 10500, 34503, 115838, ...

Conjecture (R. J. Mathar, Feb 29 2016):
(n+1)*a(n) + (-8*n+1)*a(n-1) + 3*(7*n-8)*a(n-2) + (-23*n+49)*a(n-3) + (13*n-32)*a(n-4) +
2*(-2*n+7)*a(n-5) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
2*x*(1 - 3*x + 2*x^2 - x^3)*G = (1 - x)^2*(1 - S);
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (6)*(116) + (-39)*(40) + (81)*(14) + (-66)*(5) + (33)*(2) + (-6)*(1) = 0.
-/

namespace OMA.S_oeis_a136304

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A136304, for n ≥ 5. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    2 * X * (1 - 3 * X + 2 * X ^ 2 - X ^ 3) * G = (1 - X) ^ 2 * (1 - S) →
    ∀ n : ℕ, 5 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (1 - 8 * (n : ℚ)) * coeff (n - 1) G +
        (-24 + 21 * (n : ℚ)) * coeff (n - 2) G + (49 - 23 * (n : ℚ)) * coeff (n - 3) G +
        (-32 + 13 * (n : ℚ)) * coeff (n - 4) G + (14 - 4 * (n : ℚ)) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a136304
