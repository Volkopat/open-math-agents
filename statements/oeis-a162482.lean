import Mathlib

/-!
# A162482: Mathar's recurrence

Source: https://oeis.org/A162482
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A162482 (offset 0): expansion of (1/(1-x)^3)*M(x/(1-x)^3), M(x) the g.f. of Motzkin numbers A001006;
data 1, 4, 14, 53, 218, 945, 4235, 19441, 90947, 432030, 2078416, 10105435, ...

Conjecture (R. J. Mathar, Feb 10 2015):
(n+2)*a(n) +4*(-2*n-1)*a(n-1) +18*(n-1)*a(n-2) +13*(-2*n+5)*a(n-3) +17*(n-4)*a(n-4)
+3*(-2*n+11)*a(n-5) +(n-7)*a(n-6) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1-x)^6 = (1-x)^6 - 2*x*(1-x)^3 - 3*x^2 and constant
term 1, that is T = sqrt(1 - 2*y - 3*y^2) for y = x/(1-x)^3 (the constant term selects the branch of
the square root). Since M(y) = (1 - y - sqrt(1-2*y-3*y^2))/(2*y^2) for the Motzkin g.f. M, the stated
g.f. G is determined by 2*x^2*G = (1-x)^3*(1-T) - x;
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (8)*(4235) + (-52)*(945) + (90)*(218) + (-91)*(53) + (34)*(14) + (-3)*(4) + (-1)*(1) = 0.
-/

namespace OMA.S_oeis_a162482

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A162482, for n ≥ 6. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * (1 - X) ^ 6 = (1 - X) ^ 6 - 2 * X * (1 - X) ^ 3 - 3 * X ^ 2 →
    coeff 0 T = 1 →
    2 * X ^ 2 * G = (1 - X) ^ 3 * (1 - T) - X →
    ∀ n : ℕ, 6 ≤ n →
      (2 + (n : ℚ)) * coeff n G + (-4 - 8 * (n : ℚ)) * coeff (n - 1) G +
        (-18 + 18 * (n : ℚ)) * coeff (n - 2) G + (65 - 26 * (n : ℚ)) * coeff (n - 3) G +
        (-68 + 17 * (n : ℚ)) * coeff (n - 4) G + (33 - 6 * (n : ℚ)) * coeff (n - 5) G +
        (-7 + (n : ℚ)) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a162482
