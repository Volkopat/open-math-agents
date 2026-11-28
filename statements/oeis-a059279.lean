import Mathlib

/-!
# A059279: Mathar's recurrence

Source: https://oeis.org/A059279
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A059279 (offset 0): g.f. is ((1-x)/(1-2*x)) * G(x*(1-x)/(1-2*x)) where G(x) is g.f. for Catalan numbers A000108;
data 1, 2, 6, 20, 72, 276, 1112, 4656, 20080, 88608, 398144, 1815248, ...

Conjecture (R. J. Mathar, Nov 15 2011):
(n+1)*a(n) +2*(1-4*n)*a(n-1) + 4*(4*n-5)*a(n-2) +4*(5-2*n)*a(n-3) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1-2*x) = 1-6*x+4*x^2 and constant term 1, that is
T = sqrt(1 - 4*y) for y = x*(1-x)/(1-2*x) (the constant term selects the branch of the square root). Since
y*c(y) = (1 - sqrt(1-4*y))/2 for the Catalan g.f. c, the stated g.f. G is determined by
2*x*G = 1 - T;
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (4)*(20) + (-22)*(6) + (28)*(2) + (-4)*(1) = 0.
-/

namespace OMA.S_oeis_a059279

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A059279, for n ≥ 3. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * (1 - 2 * X) = 1 - 6 * X + 4 * X ^ 2 →
    coeff 0 T = 1 →
    2 * X * G = 1 - T →
    ∀ n : ℕ, 3 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (2 - 8 * (n : ℚ)) * coeff (n - 1) G +
        (-20 + 16 * (n : ℚ)) * coeff (n - 2) G + (20 - 8 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a059279
