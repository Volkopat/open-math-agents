import Mathlib

/-!
# A174171: Mathar's recurrence

Source: https://oeis.org/A174171
Credit: @ivillar

Status: known result. The entry records: Conjecture verified using the differential equation -4*x^2 - 2 + (2*x^3 - 7*x^2
- 3*x + 2)*y(x) + (4*x^5 + 4*x^4 - 7*x^3 - 2*x^2 + x)*y'(x) = 0 satisfied by the g.f. - Robert
Israel, May 20 2026

A174171 (offset 0): a generalized Chebyshev transform of the Motzkin numbers A001006;
data 1, 1, 4, 8, 25, 65, 197, 571, 1753, 5351, 16746, 52626, ...

Conjecture (R. J. Mathar, Sep 30 2012):
(n+2)*a(n) -(2*n+1)*a(n-1) +7*(1-n)*a(n-2) +2*(2*n-5)*a(n-3) +4*(n-4)*a(n-4) = 0.

Formalization: The entry gives the g.f. of this transform of the Motzkin numbers in closed form,
(1-x-2x^2-sqrt(1-2x-7x^2+4x^3+4x^4))/(2x^2), and this closed form is used as the definition here. S is the
formal power series over ℚ with S^2 = 1-2*x-7*x^2+4*x^3+4*x^4 and constant term 1 (the constant term
selects the branch of the square root), and G is determined by 2*x^2*G = 1 - x - 2*x^2 - S;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (6)*(25) + (-9)*(8) + (-21)*(4) + (6)*(1) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a174171

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A174171, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X - 7 * X ^ 2 + 4 * X ^ 3 + 4 * X ^ 4 →
    coeff 0 S = 1 →
    2 * X ^ 2 * G = 1 - X - 2 * X ^ 2 - S →
    ∀ n : ℕ, 4 ≤ n →
      (2 + (n : ℚ)) * coeff n G + (-1 - 2 * (n : ℚ)) * coeff (n - 1) G +
        (7 - 7 * (n : ℚ)) * coeff (n - 2) G + (-10 + 4 * (n : ℚ)) * coeff (n - 3) G +
        (-16 + 4 * (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a174171
