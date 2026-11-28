import Mathlib

/-!
# A096301: Product of nonzero digits(sum of digits(n^n))

Source: https://oeis.org/A096301
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) = product of nonzero digits of (sum of digits of n^n).
Conjecture: a(n) = a(n+1) for infinitely many positive integers.
-/

namespace OMA.S_oeis_a096301

def sumDigits (m : ℕ) : ℕ :=
  (Nat.digits 10 m).sum

def prodNonzeroDigits (m : ℕ) : ℕ :=
  ((Nat.digits 10 m).filter (· ≠ 0)).prod

def a (n : ℕ) : ℕ :=
  prodNonzeroDigits (sumDigits (n ^ n))

theorem main :
    Set.Infinite {n : ℕ | 0 < n ∧ a n = a (n + 1)} := by
  sorry

end OMA.S_oeis_a096301
