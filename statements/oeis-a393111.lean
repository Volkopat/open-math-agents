import Mathlib

/-!
# OEIS A393111: Simmons' conjecture, no base-10 palindrome is a k-th power with k ≥ 5

Source: https://oeis.org/A393111 (OEIS Foundation, CC BY-SA 4.0).
Credit: @corentingenton
Formalization: AI-generated with Claude Code (model claude-opus-5-5).

Entry A393111, offset 0: Distance from 2^n to the nearest base-10 palindrome.
Comment: Gustavus Simmons has conjectured that there are no palindromes of the form b^k with
k >= 5 and b >= 2 (see Wikipedia link). If the conjecture is true, a(n) > 0 for all n >= 4.

Formalization notes:
* A base-10 palindrome is a number whose decimal digits read the same in both directions:
  `(Nat.digits 10 m).Palindrome` (`Nat.digits` has no leading zeros).
* The conjecture stated in the entry is Simmons' conjecture: for all b >= 2 and k >= 5, b^k is not a
  palindrome. The second sentence of the comment is a consequence for b = 2 (a(n) > 0 means that
  2^n is not itself a palindrome; for n = 4, 16 is not one) and is not stated separately.
* Controls: 11^4 = 14641 is a palindrome (so k >= 5 cannot be lowered to 4), while 11^5 = 161051
  and 2^5 = 32 are not.
-/

namespace OMA.S_oeis_a393111

/-- Simmons' conjecture: no b^k with b >= 2 and k >= 5 is a base-10 palindrome. -/
theorem main : ∀ b k : ℕ, 2 ≤ b → 5 ≤ k → ¬ (Nat.digits 10 (b ^ k)).Palindrome := by
  sorry

end OMA.S_oeis_a393111
