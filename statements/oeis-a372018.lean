import Mathlib

/-!
# A372018: Mathar's conjecture a(2n+1) = 2*A371364(n)

Source: https://oeis.org/A372018
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Apr 22 2024); the entry records it as a conjecture and notes no proof or
verification of it.

A372018 (offset 0): g.f. A(x) satisfies A(x) = ( 1 + 4*x*A(x)/(1 - x*A(x)) )^(1/2);
data 1, 2, 4, 10, 30, 98, 336, 1194, 4360, 16258, 61644, 236938, ...

Conjecture (R. J. Mathar, Apr 22 2024): a(2n+1) = 2*A371364().

Formalization: the entry prints the right side as 2*A371364() without an index; the data fix it as
2*A371364(n): a(1) = 2 = 2*1, a(3) = 10 = 2*5, a(5) = 98 = 2*49, a(7) = 1194 = 2*597 (A371364, offset 0,
begins 1, 5, 49, 597, 8129, ...). A is the formal power series over ℚ with constant term 1 and
A^2*(1 - x*A) = 1 - x*A + 4*x*A, that is the defining equation A = (1 + 4*x*A/(1 - x*A))^(1/2) squared and
multiplied by 1 - x*A (the constant term 1 selects the branch of the square root; the equation then has
exactly one solution). A371364 is the expansion of (1/x) * Series_Reversion( x * (1-4*x)^2 / (1-3*x) ): T is
that series reversion, the formal power series with constant term 0 and T*(1 - 4*T)^2 = x*(1 - 3*T), and
A371364(n) = [x^(n+1)] T. `main` states [x^(2n+1)] A = 2 [x^(n+1)] T for all n ≥ 0.
-/

namespace OMA.S_oeis_a372018

open PowerSeries

/-- Mathar's conjecture a(2n+1) = 2*A371364(n) for A372018, with A the g.f. of A372018 and T the series
reversion whose coefficients [x^(n+1)] T are A371364(n). -/
theorem main : ∀ A T : ℚ⟦X⟧, coeff 0 A = 1 →
    A ^ 2 * (1 - X * A) = 1 - X * A + 4 * X * A →
    coeff 0 T = 0 →
    T * (1 - 4 * T) ^ 2 = X * (1 - 3 * T) →
    ∀ n : ℕ, coeff (2 * n + 1) A = 2 * coeff (n + 1) T := by
  sorry

end OMA.S_oeis_a372018
