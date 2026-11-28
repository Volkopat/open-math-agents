import Mathlib

/-!
# A023108: 196 and the reverse-and-add process

Source: https://oeis.org/A023108
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A023108): 196 is the smallest initial term which does not lead to a
palindrome under repeated applications of `x ↦ x + reverse(x)` (A056964, base 10).

Conventions:
* "Leads to a palindrome": some iterate `T^[k] x` with `k ≥ 0` is a base-10 palindrome (the
  sequence's convention, under which palindromes such as `1` lead to a palindrome at `k = 0`).
* The statement has two parts: every positive `x < 196` leads to a palindrome, and `196` does
  not.
-/

namespace OMA.S_oeis_a023108

/-- Reverse the base-10 digits. -/
def rev (x : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 x).reverse

/-- Reverse-and-add. -/
def T (x : ℕ) : ℕ := x + rev x

/-- `x` is a base-10 palindrome. -/
def IsPalindrome (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

theorem main :
    (∀ x : ℕ, 0 < x → x < 196 → ∃ k, IsPalindrome (T^[k] x)) ∧
      ∀ k, ¬ IsPalindrome (T^[k] 196) := by
  sorry

end OMA.S_oeis_a023108
