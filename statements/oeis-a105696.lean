import Mathlib

/-!
# A105696: Mathar's recurrence

Source: https://oeis.org/A105696
Credit: @ivillar

Status: known result: the entry records a verification through a differential equation for the g.f. (Robert Israel, Jun 05 2026).

A105696 (offset 0): expansion of (1-x)/sqrt((1-3*x)/(1+x));
data 1, 1, 2, 6, 16, 44, 122, 342, 966, 2746, ...

Conjecture (R. J. Mathar, Jan 22 2020): D-finite with recurrence
n*a(n) + (-3*n+2)*a(n-1) + (-n+2)*a(n-2) + 3*(n-4)*a(n-3) = 0.
Robert Israel (Jun 05 2026) records in the entry that the conjecture is verified using a
differential equation satisfied by the g.f.

Formalization: the g.f. is the formal power series F over ℚ with constant term 1 and
F^2*(1-3*x) = (1-x)^2*(1+x); these two conditions determine F, the constant term selecting the
branch of the square root, and a(n) = [x^n] F. The recurrence involves a(n-3), so it is stated
for n ≥ 3; it is checked by the data, for example at n = 4: 4*16 - 10*6 - 2*2 + 0 = 0.
-/

namespace OMA.S_oeis_a105696

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of (1 - x) sqrt((1 + x)/(1 - 3x)). -/
theorem main : ∀ F : ℚ⟦X⟧, F ^ 2 * (1 - 3 * X) = (1 - X) ^ 2 * (1 + X) → coeff 0 F = 1 →
    ∀ n : ℕ, 3 ≤ n →
      (n : ℚ) * coeff n F + (-3 * (n : ℚ) + 2) * coeff (n - 1) F +
        (-(n : ℚ) + 2) * coeff (n - 2) F + 3 * ((n : ℚ) - 4) * coeff (n - 3) F = 0 := by
  sorry

end OMA.S_oeis_a105696
