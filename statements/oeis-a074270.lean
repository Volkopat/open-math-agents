import Mathlib

/-!
# A074270: a(n) = the least positive number X such that Cn(X) is X-smooth, where Cn is the n-th cyclotomic polynomial and "X-smooth" means "having no prime factor > X".

Source: https://oeis.org/A074270
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Inspired by a conjecture quoted in the entry: for each nonzero polynomial P with integer coefficients, there is an integer X such that P(X) is X-smooth. Certain cyclotomic polynomials seem to stress the conjecture, but no refutation is yet known. If a(11) exists, it is greater than 1060000.
-/

namespace OMA.S_oeis_a074270

/-- The conjecture: for every nonzero integer polynomial `P`, there exists a positive
integer `X` such that `P(X)` is `X`-smooth (nonzero and all prime divisors are at most `X`). -/
theorem main :
    ∀ P : Polynomial ℤ, P ≠ 0 →
      ∃ X : ℕ, 0 < X ∧ P.eval (X : ℤ) ≠ 0 ∧
        ∀ p : ℕ, Nat.Prime p → (p : ℤ) ∣ P.eval (X : ℤ) → p ≤ X := by sorry

end OMA.S_oeis_a074270
