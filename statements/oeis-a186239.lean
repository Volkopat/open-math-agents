import Mathlib

/-!
# A186239: Mathar's recurrence

Source: https://oeis.org/A186239
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A186239 (offset 0): g.f. A(x) satisfies A(x) = 1+x*A(x)+x^2*A(x)^2+2*x^3*A(x)^3;
data 1, 1, 2, 6, 17, 51, 163, 533, 1779, 6055, 20908, 73052, ...

Conjecture (R. J. Mathar, Nov 14 2011):
4*(2*n+3)*(n+1)*a(n) +(113*n^2-91*n-72)*a(n-1) + 3*(-135*n^2+263*n-108)*a(n-2)
-3*(107*n-119)*(n-2)*a(n-3) -1411*(n-2)*(n-3)*a(n-4) = 0.

Formalization: G is the formal power series over ℚ with G = 1 + x*G + x^2*G^2 + 2*x^3*G^3; this equation
determines G, and its constant term is 1;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (220)*(17) + (1372)*(6) + (-3648)*(2) + (-1854)*(1) + (-2822)*(1) = 0.
-/

namespace OMA.S_oeis_a186239

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A186239, for n ≥ 4. -/
theorem main : ∀ G : ℚ⟦X⟧, G = 1 + X * G + X ^ 2 * G ^ 2 + 2 * X ^ 3 * G ^ 3 →
    ∀ n : ℕ, 4 ≤ n →
      (12 + 20 * (n : ℚ) + 8 * (n : ℚ) ^ 2) * coeff n G + (-72 - 91 * (n : ℚ) + 113 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-324 + 789 * (n : ℚ) - 405 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-714 + 999 * (n : ℚ) - 321 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-8466 + 7055 * (n : ℚ) - 1411 * (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a186239
