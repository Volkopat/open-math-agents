import Mathlib

/-!
# A294159: Mathar's recurrence

Source: https://oeis.org/A294159
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A294159 (offset 0): alternating row sums of triangle A291844;
data 1, 1, 2, 6, 18, 55, 171, 538, 1708, 5461, 17560, 56728, ...

Conjecture (R. J. Mathar, Jun 17 2020): D-finite with recurrence
n*a(n) +(-3*n+1)*a(n-1) +2*(-n+3)*a(n-2) +2*(n-5)*a(n-3) +(n-4)*a(n-4)
+(n-5)*a(n-5) = 0.

Formalization: G is the formal power series over ℚ with constant term 1 satisfying the equation given in the entry,
(x^3 + x^2 + 3*x - 1)*(G^2 - G) + x = 0 (the equation has two power series solutions, G and 1 - G; the
constant term a(0) = 1 selects the g.f.);
a(n) = [x^n] G. The recurrence involves a(n-5), so it is stated for n ≥ 5; it is checked by the data, for
example at n = 5: (5)*(55) + (-14)*(18) + (-4)*(6) + (0)*(2) + (1)*(1) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a294159

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A294159, for n ≥ 5. -/
theorem main : ∀ G : ℚ⟦X⟧, coeff 0 G = 1 →
    (X ^ 3 + X ^ 2 + 3 * X - 1) * (G ^ 2 - G) + X = 0 →
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℚ)) * coeff n G + (1 - 3 * (n : ℚ)) * coeff (n - 1) G +
        (6 - 2 * (n : ℚ)) * coeff (n - 2) G + (-10 + 2 * (n : ℚ)) * coeff (n - 3) G +
        (-4 + (n : ℚ)) * coeff (n - 4) G + (-5 + (n : ℚ)) * coeff (n - 5) G = 0 := by
  sorry

end OMA.S_oeis_a294159
