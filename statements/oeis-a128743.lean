import Mathlib

/-!
# A128743: Mathar's recurrence

Source: https://oeis.org/A128743
Credit: @ivillar

Status: known result. The entry records: Conjecture verified using the differential equation
4*g(z)+(20*z^3+2*z^2-2*z)*g'(z)+(25*z^4-15*z^3)*g''(z)+(5*z^5-6*z^4+z^3)*g'''(z)=0 satisfied by
the G.f. - Robert Israel, Dec 25 2017

A128743 (offset 0): number of UU's (i.e., doublerises) in all skew Dyck paths of semilength n;
data 0, 0, 2, 13, 69, 346, 1700, 8286, 40264, 195488, 949302, 4613025, ...

Conjecture (R. J. Mathar, Jun 17 2016):
(n+1)*(n-2)^2*a(n) -(n-1)*(6*n^2-15*n+4)*a(n-1) +5*(n-2)*(n-1)^2*a(n-2) = 0.

Formalization: S is the formal power series over ℚ with S^2 = 1-6*x+5*x^2 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
2*x*S*G = 1 - 4*x + x^2 + (x - 1)*S;
a(n) = [x^n] G. The recurrence involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for
example at n = 2: (0)*(2) + (2)*(0) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a128743

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A128743, for n ≥ 2. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 6 * X + 5 * X ^ 2 →
    coeff 0 S = 1 →
    2 * X * S * G = 1 - 4 * X + X ^ 2 + (X - 1) * S →
    ∀ n : ℕ, 2 ≤ n →
      (4 - 3 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) * coeff n G + (4 - 19 * (n : ℚ) + 21 * (n : ℚ) ^ 2 - 6 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-10 + 25 * (n : ℚ) - 20 * (n : ℚ) ^ 2 + 5 * (n : ℚ) ^ 3) * coeff (n - 2) G = 0 := by
  sorry

end OMA.S_oeis_a128743
