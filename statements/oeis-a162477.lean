import Mathlib

/-!
# A162477: Mathar's recurrence

Source: https://oeis.org/A162477
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A162477 (offset 0): expansion of (1/(1-x)^2)*c(x/(1-x)^4) where c(x) is the g.f. of A000108;
data 1, 3, 11, 50, 255, 1391, 7939, 46821, 283081, 1745212, 10929625, 69338213, ...

Conjecture (R. J. Mathar, Nov 17 2011):
(n+1)*a(n) +4*(1-2*n)*a(n-1) +6*(n-2)*a(n-2) +2*(7-2*n)*a(n-3) +(n-5)*a(n-4) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1-x)^4 = (1-x)^4 - 4*x and constant term 1, that is
T = sqrt(1 - 4*y) for y = x/(1-x)^4 (the constant term selects the branch of the square root). Since
y*c(y) = (1 - sqrt(1-4*y))/2 for the Catalan g.f. c, the stated g.f. G is determined by
2*x*G = (1-x)^2*(1-T);
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (5)*(255) + (-28)*(50) + (12)*(11) + (-2)*(3) + (-1)*(1) = 0.
-/

namespace OMA.S_oeis_a162477

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A162477, for n ≥ 4. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * (1 - X) ^ 4 = (1 - X) ^ 4 - 4 * X →
    coeff 0 T = 1 →
    2 * X * G = (1 - X) ^ 2 * (1 - T) →
    ∀ n : ℕ, 4 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (4 - 8 * (n : ℚ)) * coeff (n - 1) G +
        (-12 + 6 * (n : ℚ)) * coeff (n - 2) G + (14 - 4 * (n : ℚ)) * coeff (n - 3) G +
        (-5 + (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a162477
