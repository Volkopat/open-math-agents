import Mathlib

/-!
# A244886: Mathar's recurrence

Source: https://oeis.org/A244886
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A244886 (offset 0): g.f. (1-x+sqrt(1-2*x-3*x^2))/(1-3*x+x^2+x^3+(1-x^2)*sqrt(1-2*x-3*x^2));
data 1, 1, 2, 4, 9, 22, 56, 147, 393, 1065, 2915, 8042, ...

Conjecture (R. J. Mathar, Jan 24 2020): D-finite with recurrence
n*a(n) + (-5*n+3)*a(n-1) + 2*n*a(n-2) + (13*n-30)*a(n-3) - 3*a(n-4) + (-8*n+21)*a(n-5)
+ 3*(-n+3)*a(n-6) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-2*x-3*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*(1-3*x+x^2+x^3+(1-x^2)*S) = 1 - x + S (the factor on the left has constant term 2);
a(n) = [x^n] G. The recurrence involves a(n-6), so it is stated for n ≥ 6; it is checked by the data, for
example at n = 6: (6)*(56) + (-27)*(22) + (12)*(9) + (48)*(4) + (-3)*(2) + (-27)*(1) + (-9)*(1) = 0.
-/

namespace OMA.S_oeis_a244886

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A244886, for n ≥ 6. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
    coeff 0 S = 1 →
    G * (1 - 3 * X + X ^ 2 + X ^ 3 + (1 - X ^ 2) * S) = 1 - X + S →
    ∀ n : ℕ, 6 ≤ n →
      ((n : ℚ)) * coeff n G + (3 - 5 * (n : ℚ)) * coeff (n - 1) G +
        (2 * (n : ℚ)) * coeff (n - 2) G + (-30 + 13 * (n : ℚ)) * coeff (n - 3) G +
        (-3) * coeff (n - 4) G + (21 - 8 * (n : ℚ)) * coeff (n - 5) G +
        (9 - 3 * (n : ℚ)) * coeff (n - 6) G = 0 := by
  sorry

end OMA.S_oeis_a244886
