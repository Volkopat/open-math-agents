import Mathlib

/-!
# A239201: Mathar's recurrence

Source: https://oeis.org/A239201
Credit: @ivillar

A239201 (offset 1): expansion of
-(x*sqrt(5*x^2-6*x+1) - 2*x^3 + 3*x^2 - x)/((3*x^2-4*x+1)*sqrt(5*x^2-6*x+1) + 5*x^3 - 11*x^2 + 7*x - 1);
data 2, 5, 17, 68, 293, 1310, 5984, 27725, 129773, 612158, 2905322, 13857035, ...

Conjecture (R. J. Mathar, Oct 07 2016): D-finite with recurrence
(-n+1)*a(n) + (7*n-11)*a(n-1) + (-11*n+25)*a(n-2) + 5*(n-3)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 5*x^2-6*x+1 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*((3*x^2-4*x+1)*S + 5*x^3 - 11*x^2 + 7*x - 1) = -(x*S - 2*x^3 + 3*x^2 - x) (the factor on the left is a
nonzero power series, with lowest term 2*x^2);
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (-2)*(17) + (10)*(5) + (-8)*(2) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a239201

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A239201, for n ≥ 3. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 6 * X + 5 * X ^ 2 →
    coeff 0 S = 1 →
    G * ((3 * X ^ 2 - 4 * X + 1) * S + 5 * X ^ 3 - 11 * X ^ 2 + 7 * X - 1) =
      -(X * S - 2 * X ^ 3 + 3 * X ^ 2 - X) →
    ∀ n : ℕ, 3 ≤ n →
      (1 - (n : ℚ)) * coeff n G + (-11 + 7 * (n : ℚ)) * coeff (n - 1) G +
        (25 - 11 * (n : ℚ)) * coeff (n - 2) G + (-15 + 5 * (n : ℚ)) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a239201
