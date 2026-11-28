import Mathlib

/-!
# A184018: Mathar's recurrence

Source: https://oeis.org/A184018
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A184018 (offset 0): expansion of c(x/(1-x-x^2)) / (1-x-x^2), c(x) the g.f. of A000108;
data 1, 2, 6, 19, 67, 254, 1017, 4236, 18168, 79680, 355635, 1609912, ...

Conjecture (R. J. Mathar, Nov 15 2011):
(n+1)*a(n) + 2*(1-3*n)*a(n-1) + 3*(n-1)*a(n-2) + 2*(3*n-5)*a(n-3) + (n-3)*a(n-4) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1-x-x^2) = 1-5*x-x^2 and constant term 1, that is
T = sqrt(1 - 4*y) for y = x/(1-x-x^2) (the constant term selects the branch of the square root). Since
y*c(y) = (1 - sqrt(1-4*y))/2 for the Catalan g.f. c, the stated g.f. G is determined by
2*x*G = 1 - T;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (5)*(67) + (-22)*(19) + (9)*(6) + (14)*(2) + (1)*(1) = 0.
-/

namespace OMA.S_oeis_a184018

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A184018, for n ≥ 4. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * (1 - X - X ^ 2) = 1 - 5 * X - X ^ 2 →
    coeff 0 T = 1 →
    2 * X * G = 1 - T →
    ∀ n : ℕ, 4 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (2 - 6 * (n : ℚ)) * coeff (n - 1) G +
        (-3 + 3 * (n : ℚ)) * coeff (n - 2) G + (-10 + 6 * (n : ℚ)) * coeff (n - 3) G +
        (-3 + (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a184018
