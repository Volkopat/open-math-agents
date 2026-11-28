import Mathlib

/-!
# A240688: Mathar's recurrence

Source: https://oeis.org/A240688
Credit: @ivillar

Status: known result. The entry records: Mathar's conjectural third-order recurrence above can be verified using Maple's
gfun:-rectodiffeq command.

A240688 (offset 0): expansion of -(x*sqrt(-4*x^2-4*x+1)-2*x^2-3*x) / ((x+1)*sqrt(-4*x^2-4*x+1)+ 4*x^3+8*x^2+3*x-1);
data 1, 1, 5, 19, 81, 351, 1553, 6959, 31489, 143551, 658305, 3033471, ...

Conjecture (R. J. Mathar, Jun 14 2016):
n*(n-1)*a(n) -(3*n-2)*(n-1)*a(n-1) +2*(-4*n^2+7*n-1)*a(n-2) -4*n*(n-2)*a(n-3) = 0.

Formalization: S is the formal power series over ℚ with S^2 = -4*x^2-4*x+1 and constant term 1
(the constant term selects the branch of the square root), and the g.f. G is determined by
G*((x + 1)*S + 4*x^3 + 8*x^2 + 3*x - 1) = -(x*S - 2*x^2 - 3*x);
a(n) = [x^n] G. The recurrence involves a(n-3), so it is stated for n ≥ 3; it is checked by the data, for
example at n = 3: (6)*(19) + (-14)*(5) + (-32)*(1) + (-12)*(1) = 0.
-/

namespace OMA.S_oeis_a240688

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of the g.f. of A240688, for n ≥ 3. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X - 4 * X ^ 2 →
    coeff 0 S = 1 →
    G * ((X + 1) * S + 4 * X ^ 3 + 8 * X ^ 2 + 3 * X - 1) = -(X * S - 2 * X ^ 2 - 3 * X) →
    ∀ n : ℕ, 3 ≤ n →
      (-(n : ℚ) + (n : ℚ) ^ 2) * coeff n G + (-2 + 5 * (n : ℚ) - 3 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (-2 + 14 * (n : ℚ) - 8 * (n : ℚ) ^ 2) * coeff (n - 2) G + (8 * (n : ℚ) - 4 * (n : ℚ) ^ 2) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a240688
