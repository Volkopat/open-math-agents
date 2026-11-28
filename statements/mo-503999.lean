import Mathlib

/-!
# Is 1001 the only palindrome which is a product of three consecutive primes?

Source: https://mathoverflow.net/questions/503999 (CC BY-SA 4.0).

Question (the title): is `1001 = 7 · 11 · 13` the only decimal palindrome that is the product of
three consecutive primes? A search over all such products below the poser's bound found no other.
`main` states the expected yes. The primes are `Nat.nth Nat.Prime i` (`i = 0` gives `2`), and a
number is a decimal palindrome when its list of base-`10` digits equals its reverse.
-/

namespace OMA.S_mo_503999

/-- `n` is a palindrome in base `10`. -/
def IsPalindrome (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

theorem main : ∀ i : ℕ,
    IsPalindrome (Nat.nth Nat.Prime i * Nat.nth Nat.Prime (i + 1) * Nat.nth Nat.Prime (i + 2)) →
      Nat.nth Nat.Prime i * Nat.nth Nat.Prime (i + 1) * Nat.nth Nat.Prime (i + 2) = 1001 := by
  sorry

end OMA.S_mo_503999
