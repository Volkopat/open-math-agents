import Mathlib

/-!
# A187430: Irwin's conjecture relating the sequence to the Catalan generating function

Source: https://oeis.org/A187430
Credit: @ivillar

Status: open conjecture (Benedict W. J. Irwin, Jan 13 2017); the entry records it as a conjecture and notes no
proof or verification of it.

A187430 (offset 0): number of nonnegative walks of n steps with step sizes 1 and 2, starting and ending at 0;
data 1, 0, 2, 2, 11, 24, 93, 272, 971, 3194, 11293, 39148, ...

Conjecture (Benedict W. J. Irwin, Jan 13 2017):
1 + Sum_{n>=0} a(n)*(-1)^n x^(n+1)/(1-x)^(2*n+2) = C(x), the g.f. for the Catalan numbers A000108.

Formalization: the entry records that Sum_{n>=0} a(n)*x^(n+1) is the compositional inverse of
x*(1-x^2)^2/(1+x^3)^2 (Ira M. Gessel, Sep 19 2017), and this is used as the definition here: F is the formal
power series over ℚ with constant term 0 and F*(1 - F^2)^2 = x*(1 + F^3)^2 (this equation has exactly one
solution with constant term 0, F = x + 2*x^3 + 2*x^4 + 11*x^5 + ...), so a(n) = [x^(n+1)] F. Since
(-1)^n x^(n+1)/(1-x)^(2n+2) = -(-x/(1-x)^2)^(n+1), the sum in the conjecture is -F(-x/(1-x)^2), the series F
with -x/(1-x)^2 substituted for the variable (`PowerSeries.subst`; the substituted series has constant term
0, so the substitution is the convergent sum of the conjecture). C is the Catalan g.f., the formal power
series with C = 1 + x*C^2. `main` states 1 - F(-x/(1-x)^2) = C. It is checked by the data: with
y = x/(1-x)^2 = x + 2*x^2 + 3*x^3 + ..., 1 + y + 2*y^3 - 2*y^4 + 11*y^5 - ... = 1 + x + 2*x^2 + 5*x^3 + 14*x^4 + ...
-/

namespace OMA.S_oeis_a187430

open PowerSeries

/-- Irwin's conjecture for A187430: 1 + Sum_{n>=0} a(n) (-1)^n x^(n+1)/(1-x)^(2n+2) = C(x), where
F = Sum_{n>=0} a(n) x^(n+1) is the compositional inverse of x(1-x^2)^2/(1+x^3)^2 and the sum is
-F(-x/(1-x)^2). -/
theorem main : ∀ F C : ℚ⟦X⟧, coeff 0 F = 0 →
    F * (1 - F ^ 2) ^ 2 = X * (1 + F ^ 3) ^ 2 →
    C = 1 + X * C ^ 2 →
    1 - PowerSeries.subst (-(X * ((1 - X : ℚ⟦X⟧)⁻¹) ^ 2) : ℚ⟦X⟧) F = C := by
  sorry

end OMA.S_oeis_a187430
