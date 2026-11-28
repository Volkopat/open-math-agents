import Mathlib

/-!
# A253631: Palindromic primes with digits in {0, 1} whose squares are palindromes

Source: https://oeis.org/A253631

Conjecture (OEIS A253631):
`A253631(n) = A225603(n + 2)` for all `n ≥ 1`; equivalently, every base-10 palindromic
prime `p > 3` whose square `p^2` is also a base-10 palindrome has only decimal digits
`0` and `1`.

Conventions:
- First terms of A225603 (palindromic primes whose square is a palindrome):
  `2, 3, 11, 101, 100111001, ...`.
- Excluding `2` and `3` (`p > 3`), all remaining terms are conjectured to belong to
  A253631 (using only digits `0` and `1`).
-/

namespace OMA.S_oeis_a253631

/-- Predicate stating that `n` is a base-10 palindrome. -/
def IsPalindrome10 (n : ℕ) : Prop :=
  Nat.digits 10 n = (Nat.digits 10 n).reverse

/-- Conjecture: every base-10 palindromic prime `p > 3` whose square is a palindrome
contains only the decimal digits `0` and `1`. -/
theorem main :
    ∀ p : ℕ, 3 < p → Nat.Prime p → IsPalindrome10 p → IsPalindrome10 (p ^ 2) →
      ∀ d ∈ Nat.digits 10 p, d = 0 ∨ d = 1 := by
  sorry

end OMA.S_oeis_a253631
