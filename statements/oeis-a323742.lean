import Mathlib

/-!
# A323742: (2n+1)-digit palindromes in three consecutive bases

Source: https://oeis.org/A323742

A323742 (offset 1) is a(n) = the smallest number that is a (2n+1)-digit palindrome in three
consecutive integer bases, or 0 if no such number exists: 178, 154593982, 3360633, 0, 0, 0.
For example 178 = 454_6 = 343_7 = 262_8.
Its comments state the conjecture (Matej Veselovac): a(n) = 0 for all n >= 4, that is, for
n >= 4 no number is a (2n+1)-digit palindrome in three consecutive bases.

Conventions:
* Bases are integers b >= 2; the three consecutive bases are b, b + 1, b + 2.
* The base-b digits of m are `Nat.digits b m` (least significant first); m has 2n + 1 digits in
  base b when this list has length 2n + 1, and it is a palindrome when the list equals its reverse.
-/

namespace OMA.S_oeis_a323742

/-- `m` is a palindrome with exactly `L` digits in base `b`. -/
def IsPalindromeWithDigits (b L m : ℕ) : Prop :=
  (Nat.digits b m).length = L ∧ (Nat.digits b m).reverse = Nat.digits b m

/-- For `n ≥ 4`, no number is a `(2n+1)`-digit palindrome in three consecutive bases. -/
theorem main : ∀ n : ℕ, 4 ≤ n → ¬ ∃ m b : ℕ, 2 ≤ b ∧
    ∀ i < 3, IsPalindromeWithDigits (b + i) (2 * n + 1) m := by
  sorry

end OMA.S_oeis_a323742
