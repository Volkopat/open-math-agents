import Mathlib

/-!
# A162479: Mathar's recurrence

Source: https://oeis.org/A162479
Credit: @ivillar

A162479 (offset 0): expansion of 1/((1-x)*sqrt(1-4x/(1-x)^4));
data 1, 3, 17, 105, 671, 4393, 29249, 197117, 1340579, 9182013, 63247587, 437684991, ...

Conjecture (R. J. Mathar, Nov 17 2011): D-finite with recurrence
n*a(n) + 3*(2-3*n)*a(n-1) + 2*(7*n-13)*a(n-2) + 2*(12-5*n)*a(n-3) + (5*n-16)*a(n-4) + (4-n)*a(n-5) = 0.

Formalization: T is the formal power series over ℚ with T^2*(1-x)^4 = (1-x)^4 - 4*x and constant
term 1, that is T = sqrt(1-4x/(1-x)^4) (the constant term selects the branch of the square
root), and the g.f. G is the inverse of (1-x)*T, that is G*((1-x)*T) = 1;
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (5)*(4393) + (-39)*(671) + (44)*(105) + (-26)*(17) + (9)*(3) + (-1)*(1) = 0.
-/

namespace OMA.S_oeis_a162479

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A162479, for n ≥ 5. -/
theorem main : ∀ T G : ℚ⟦X⟧, T ^ 2 * (1 - X) ^ 4 = (1 - X) ^ 4 - 4 * X →
    coeff 0 T = 1 →
    G * ((1 - X) * T) = 1 →
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℚ)) * coeff n G + (6 - 9 * (n : ℚ)) * coeff (n - 1) G +
        (-26 + 14 * (n : ℚ)) * coeff (n - 2) G + (24 - 10 * (n : ℚ)) * coeff (n - 3) G +
        (-16 + 5 * (n : ℚ)) * coeff (n - 4) G + (4 - (n : ℚ)) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a162479
