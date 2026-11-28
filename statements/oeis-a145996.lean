import Mathlib

/-!
# Rational roots of the polynomials in OEIS A145996

Artur Jasinski conjectured that the five listed nonnegative integer parameters
give all rational-root cases, including the degenerate polynomial at one.
Source: https://oeis.org/A145996 (OEIS Foundation, CC BY-SA 4.0).
-/

namespace OMA.S_oeis_a145996

def polynomialValue (k x : ℚ) : ℚ :=
  4*k-k^2+5*k^2*x+(20*k-20*k^2)*x^3+(16-32*k+16*k^2)*x^5

theorem main : ∀ k : ℕ, (∃ x : ℚ, polynomialValue k x = 0) ↔
    k=0 ∨ k=1 ∨ k=2 ∨ k=4 ∨ k=243 := by
  sorry

end OMA.S_oeis_a145996
