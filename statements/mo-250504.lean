import Mathlib

/-!
# Is every integer greater than 1 the sum of a palindrome and a prime?

Source: https://mathoverflow.net/questions/250504 (CC BY-SA 3.0).

Question: is every integer greater than `1` the sum of a prime and a nonnegative palindrome, a
number whose canonical base-`10` expansion is a palindrome? Verified in the comments up to `10⁷`;
`main` states the expected yes. One-digit numbers, and `0`, count as palindromes: a number is a
palindrome when its list of decimal digits (`Nat.digits 10`, no leading zeros) equals its reverse.
-/

namespace OMA.S_mo_250504

/-- `x` is a palindrome in base `10`. -/
def IsPalindrome (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

theorem main : ∀ n : ℕ, 1 < n → ∃ p q : ℕ, p.Prime ∧ IsPalindrome q ∧ n = p + q := by
  sorry

end OMA.S_mo_250504
