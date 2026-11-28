import Mathlib

/-!
# A102879: Mathar's recurrence

Source: https://oeis.org/A102879
Credit: @ivillar

Status: known result. The entry records: Conjecture verified using the differential equation x*(x^2+1)*(x^2-4*x+1)*g'' +
(4*x^4-10*x^3+2*x^2+2*x-2)*g' + 4*(x^2-x+1)*g = 0 satisfied by the g.f. - Robert Israel, Aug 28
2018

A102879 (offset 0): a Chebyshev transform of the first kind of the central binomial numbers;
data 1, 2, 4, 14, 48, 162, 556, 1934, 6784, 23954, 85044, 303294, ...

Conjecture (R. J. Mathar, Nov 09 2012):
n*(n-3)*a(n) - 2*(2*n-1)*(n-3)*a(n-1) + 2*(2-4*n+n^2)*a(n-2) - 2*(n-1)*(2*n-7)*a(n-3)
+ (n-1)*(n-4)*a(n-4) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x+2*x^2-4*x^3+x^4 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
S*G = 1 - x^2;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (4)*(48) + (-14)*(14) + (4)*(4) + (-6)*(2) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a102879

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A102879, for n ≥ 4. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4 →
    coeff 0 S = 1 →
    S * G = 1 - X ^ 2 →
    ∀ n : ℕ, 4 ≤ n →
      (-3 * (n : ℚ) + (n : ℚ) ^ 2) * coeff n G + (-6 + 14 * (n : ℚ) - 4 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (4 - 8 * (n : ℚ) + 2 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-14 + 18 * (n : ℚ) - 4 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (4 - 5 * (n : ℚ) + (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a102879
