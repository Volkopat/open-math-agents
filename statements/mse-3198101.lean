import Mathlib

/-!
# Pairs of Palindromic Primes Without Digit 1 Whose Product Is Palindromic

Source: https://math.stackexchange.com/questions/3198101/pairs-of-palindromic-primes-without-1-and-have-a-palindromic-product
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

## Problem Statement
Question (1): Are there only finitely many pairs `(a, b)` of base-10 palindromic
primes neither of which contains the digit `1` in base 10, such that the product
`a * b` is also a base-10 palindrome?

## Formalization Notes
A natural number `n` is a base-10 palindrome iff `(Nat.digits 10 n).reverse = Nat.digits 10 n`.
Not containing the digit `1` is `1 ∉ Nat.digits 10 n`.
-/

namespace OMA.S_mse_3198101

def IsPalindrome10 (n : ℕ) : Prop :=
  (Nat.digits 10 n).reverse = Nat.digits 10 n

theorem main :
    {p : ℕ × ℕ |
      p.1.Prime ∧ p.2.Prime ∧
      IsPalindrome10 p.1 ∧ IsPalindrome10 p.2 ∧
      1 ∉ Nat.digits 10 p.1 ∧ 1 ∉ Nat.digits 10 p.2 ∧
      IsPalindrome10 (p.1 * p.2)}.Finite := by
  sorry

end OMA.S_mse_3198101
