import Mathlib

/-!
# A096291: Sum of digits(product of nonzero digits(n^n))

Source: https://oeis.org/A096291
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) = sum of digits of (product of nonzero digits of n^n).
Conjecture: a(n) = a(n+1) for infinitely many positive integers.
-/

namespace OMA.S_oeis_a096291

def sumDigits (m : ℕ) : ℕ :=
  (Nat.digits 10 m).sum

def prodNonzeroDigits (m : ℕ) : ℕ :=
  ((Nat.digits 10 m).filter (· ≠ 0)).prod

def a (n : ℕ) : ℕ :=
  sumDigits (prodNonzeroDigits (n ^ n))

theorem main :
    Set.Infinite {n : ℕ | 0 < n ∧ a n = a (n + 1)} := by
  sorry

end OMA.S_oeis_a096291
