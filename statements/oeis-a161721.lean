import Mathlib

/-!
# The decimal digits of the primes in OEIS A161721

Source: https://oeis.org/A161721
Credit: @laurilehtinen

Chai Wah Wu and Robert G. Wilson v conjectured on January 7, 2015 that a term
other than 3 has only digits 0, 1 and 2, and that each term has at most one 2.
The sequence requires primality both before and after reversal, and a palindromic product.
-/

namespace OMA.S_oeis_a161721

def digitalReverse (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

theorem main : ∀ p : ℕ, p.Prime → (digitalReverse p).Prime →
    (Nat.digits 10 (p * digitalReverse p)).Palindrome →
    (p ≠ 3 → ∀ d ∈ Nat.digits 10 p, d ≤ 2) ∧ (Nat.digits 10 p).count 2 ≤ 1 := by
  sorry

end OMA.S_oeis_a161721
