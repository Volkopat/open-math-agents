import Mathlib

/-!
# A082207: Palindromes whose product of digits is a positive palindrome.

Source: https://oeis.org/A082207
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: There are infinitely many terms in the sequence (of the type 777) for which the product of digits > 10.
-/

namespace OMA.S_oeis_a082207

def isPalindrome (n : ℕ) : Prop :=
  (Nat.digits 10 n).reverse = Nat.digits 10 n

def digitProd (n : ℕ) : ℕ :=
  (Nat.digits 10 n).prod

theorem main :
    Set.Infinite {n : ℕ | isPalindrome n ∧ 10 < digitProd n ∧ isPalindrome (digitProd n)} := by
  sorry

end OMA.S_oeis_a082207
