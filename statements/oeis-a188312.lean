import Mathlib

/-!
# A188312: Mathar's recurrence

Source: https://oeis.org/A188312
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A188312 (offset 0): expansion of (1/(1-x^2))*c(x/((1-x)*(1-x^2))) where c(x) is the g.f. of A000108;
data 1, 1, 4, 12, 45, 174, 709, 2978, 12825, 56303, 251060, 1133943, ...

Conjecture (R. J. Mathar, Nov 15 2011):
(n+1)*a(n) +(3-4*n)*a(n-1) + (7-6*n)*a(n-2) -a(n-3) +(n-4)*a(n-4) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1-x)*(1-x^2) = (1-x)*(1-x^2) - 4*x and constant term 1, that is
T = sqrt(1 - 4*y) for y = x/((1-x)*(1-x^2)) (the constant term selects the branch of the square root). Since
y*c(y) = (1 - sqrt(1-4*y))/2 for the Catalan g.f. c, the stated g.f. G is determined by
2*x*G = (1-x)*(1-T);
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (5)*(45) + (-13)*(12) + (-17)*(4) + (-1)*(1) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a188312

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A188312, for n ≥ 4. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * ((1 - X) * (1 - X ^ 2)) = (1 - X) * (1 - X ^ 2) - 4 * X →
    coeff 0 T = 1 →
    2 * X * G = (1 - X) * (1 - T) →
    ∀ n : ℕ, 4 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (3 - 4 * (n : ℚ)) * coeff (n - 1) G +
        (7 - 6 * (n : ℚ)) * coeff (n - 2) G + (-1) * coeff (n - 3) G +
        (-4 + (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a188312
