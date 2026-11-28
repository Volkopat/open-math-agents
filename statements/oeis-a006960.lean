import Mathlib

/-!
# A006960: Reverse and Add! sequence starting with 196.

Source: https://oeis.org/A006960
Credit: @divmxnd0x

Conjecture (stated in A006960): 196 is the smallest initial term which does not lead to a
palindrome.

Formalization notes:
* `revAdd n = n + reverse(n)` in base 10 (`reverse` reverses the decimal digits, dropping leading
  zeros), the map generating A006960 from `196`.
* "Leads to a palindrome" means that some iterate `revAdd^[k] n` (`k ≥ 0`) is a palindrome in base
  10. The conjecture has two parts: the trajectory of `196` never contains a palindrome, and every
  smaller positive starting value does reach one.
-/

namespace OMA.S_oeis_a006960

/-- The decimal reversal of `n`. -/
def reverse (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- One "reverse and add" step. -/
def revAdd (n : ℕ) : ℕ := n + reverse n

/-- `n` is a palindrome in base 10. -/
def IsPalindrome (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- `196` never reaches a palindrome, and every positive `n < 196` does. -/
theorem main : (∀ k : ℕ, ¬ IsPalindrome (revAdd^[k] 196)) ∧
    ∀ n : ℕ, 0 < n → n < 196 → ∃ k : ℕ, IsPalindrome (revAdd^[k] n) := by
  sorry

end OMA.S_oeis_a006960
