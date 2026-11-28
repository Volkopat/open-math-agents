import Mathlib

/-!
# A188314: Mathar's recurrence

Source: https://oeis.org/A188314
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A188314 (offset 0): expansion of (1/(1-x))*c(x/((1-x)*(1-x^2))) where c(x) is the g.f. of A000108;
data 1, 2, 5, 16, 57, 219, 883, 3687, 15803, 69128, 307363, 1385003, ...

Conjecture (R. J. Mathar, Nov 15 2011):
(n+1)*a(n) +(n+2)*a(n-1) +(42-26*n)*a(n-2) +30*(3-n)*a(n-3) +(n-5)*a(n-4) +5*(n-6)*a(n-5) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1-x)*(1-x^2) = (1-x)*(1-x^2) - 4*x and constant term 1, that is
T = sqrt(1 - 4*y) for y = x/((1-x)*(1-x^2)) (the constant term selects the branch of the square root). Since
y*c(y) = (1 - sqrt(1-4*y))/2 for the Catalan g.f. c, the stated g.f. G is determined by
2*x*G = (1-x^2)*(1-T);
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (6)*(219) + (7)*(57) + (-88)*(16) + (-60)*(5) + (0)*(2) + (-5)*(1) = 0.
-/

namespace OMA.S_oeis_a188314

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A188314, for n ≥ 5. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * ((1 - X) * (1 - X ^ 2)) = (1 - X) * (1 - X ^ 2) - 4 * X →
    coeff 0 T = 1 →
    2 * X * G = (1 - X ^ 2) * (1 - T) →
    ∀ n : ℕ, 5 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (2 + (n : ℚ)) * coeff (n - 1) G +
        (42 - 26 * (n : ℚ)) * coeff (n - 2) G + (90 - 30 * (n : ℚ)) * coeff (n - 3) G +
        (-5 + (n : ℚ)) * coeff (n - 4) G + (-30 + 5 * (n : ℚ)) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a188314
