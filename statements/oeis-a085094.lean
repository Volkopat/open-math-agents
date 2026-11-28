import Mathlib

/-!
# A085094: Smallest k such that n*k-1 is a palindrome, or 0 if no such number exists.

Source: https://oeis.org/A085094
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: No entry is zero. For every n there exists a k such that n*k-1 is a palindrome.
-/

namespace OMA.S_oeis_a085094

def IsPalindrome10 (n : ℕ) : Prop :=
  (Nat.digits 10 n).reverse = Nat.digits 10 n

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ IsPalindrome10 (n * k - 1) := by
  sorry

end OMA.S_oeis_a085094
