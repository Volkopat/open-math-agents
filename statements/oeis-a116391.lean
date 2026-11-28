import Mathlib

/-!
# A116391: Mathar's recurrence

Source: https://oeis.org/A116391
Credit: @ivillar

A116391 (offset 0): expansion of 1/((1+x)*(sqrt(1-4*x^2)-x));
data 1, 0, 3, 2, 11, 14, 47, 78, 217, 408, 1039, 2086, ...

Conjecture (R. J. Mathar, Jan 23 2020): D-finite with recurrence
n*a(n) + n*a(n-1) + 3*(-3*n+4)*a(n-2) + 3*(-3*n+4)*a(n-3) + 20*(n-3)*a(n-4) + 20*(n-3)*a(n-5) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-4*x^2 and constant term 1 (the
constant term selects the branch of the square root), and the g.f. G is the inverse of
(1+x)*(S-x), that is G*((1+x)*(S-x)) = 1; a(n) = [x^n] G. The recurrence involves a(n-5), so it
is stated for n ≥ 5; it is checked by the data, for example at n = 5:
5*14 + 5*11 - 33*2 - 33*3 + 40*0 + 40*1 = 0.
-/

namespace OMA.S_oeis_a116391

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of 1/((1+x)(sqrt(1-4x^2)-x)). -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X ^ 2 → coeff 0 S = 1 →
    G * ((1 + X) * (S - X)) = 1 →
    ∀ n : ℕ, 5 ≤ n →
      (n : ℚ) * coeff n G + (n : ℚ) * coeff (n - 1) G +
        3 * (-3 * (n : ℚ) + 4) * coeff (n - 2) G + 3 * (-3 * (n : ℚ) + 4) * coeff (n - 3) G +
        20 * ((n : ℚ) - 3) * coeff (n - 4) G + 20 * ((n : ℚ) - 3) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a116391
