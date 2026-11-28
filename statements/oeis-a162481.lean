import Mathlib

/-!
# A162481: Mathar's recurrence

Source: https://oeis.org/A162481
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A162481 (offset 0): expansion of (1/(1-x)^3)*c(x/(1-x)^3), c(x) the g.f. of A000108;
data 1, 4, 14, 54, 235, 1119, 5658, 29800, 161621, 896198, 5056824, 28938519, ...

Conjecture (R. J. Mathar, Dec 11 2011):
(n+1)*a(n) + 2*(1-4*n)*a(n-1) + 2*(5*n-3)*a(n-2) + 4*(2-n)*a(n-3) + (n-3)*a(n-4) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1-x)^3 = (1-x)^3 - 4*x and constant term 1, that is
T = sqrt(1 - 4*y) for y = x/(1-x)^3 (the constant term selects the branch of the square root). Since
y*c(y) = (1 - sqrt(1-4*y))/2 for the Catalan g.f. c, the stated g.f. G is determined by
2*x*G = 1 - T;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (5)*(235) + (-30)*(54) + (34)*(14) + (-8)*(4) + (1)*(1) = 0.
-/

namespace OMA.S_oeis_a162481

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A162481, for n ≥ 4. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * (1 - X) ^ 3 = (1 - X) ^ 3 - 4 * X →
    coeff 0 T = 1 →
    2 * X * G = 1 - T →
    ∀ n : ℕ, 4 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (2 - 8 * (n : ℚ)) * coeff (n - 1) G +
        (-6 + 10 * (n : ℚ)) * coeff (n - 2) G + (8 - 4 * (n : ℚ)) * coeff (n - 3) G +
        (-3 + (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a162481
