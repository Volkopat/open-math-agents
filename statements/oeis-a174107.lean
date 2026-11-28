import Mathlib

/-!
# A174107: Mathar's recurrence

Source: https://oeis.org/A174107
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A174107 (offset 0): expansion of (1/(1-x+x^2))c(x/(1-x+x^2)), c(x) the g.f. of A000108;
data 1, 2, 4, 11, 37, 134, 505, 1964, 7834, 31880, 131833, 552392, ...

Conjecture (R. J. Mathar, Nov 15 2011):
(n+1)*a(n) +2*(1-3n)*a(n-1) +7*(n-1)*a(n-2) +2*(5-3*n)*a(n-3) +(n-3)*a(n-4) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1-x+x^2) = 1-5*x+x^2 and constant term 1, that is
T = sqrt(1 - 4*y) for y = x/(1-x+x^2) (the constant term selects the branch of the square root). Since
y*c(y) = (1 - sqrt(1-4*y))/2 for the Catalan g.f. c, the stated g.f. G is determined by
2*x*G = 1 - T;
a(n) = [x^n] G. The recurrence involves a(n-4), so it is stated for n ≥ 4; it is checked by the data, for
example at n = 4: (5)*(37) + (-22)*(11) + (21)*(4) + (-14)*(2) + (1)*(1) = 0.
-/

namespace OMA.S_oeis_a174107

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A174107, for n ≥ 4. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * (1 - X + X ^ 2) = 1 - 5 * X + X ^ 2 →
    coeff 0 T = 1 →
    2 * X * G = 1 - T →
    ∀ n : ℕ, 4 ≤ n →
      (1 + (n : ℚ)) * coeff n G + (2 - 6 * (n : ℚ)) * coeff (n - 1) G +
        (-7 + 7 * (n : ℚ)) * coeff (n - 2) G + (10 - 6 * (n : ℚ)) * coeff (n - 3) G +
        (-3 + (n : ℚ)) * coeff (n - 4) G = 0 := by
  sorry

end OMA.S_oeis_a174107
