import Mathlib

/-!
# Palindromic primes with palindromic squares and no digit 1

Source: https://math.stackexchange.com/questions/3197125
Are `2` and `3` the only primes that do not contain the digit `1`, are palindromes, and have
palindromic squares? `main` states the affirmative answer.

Conventions. Decimal digits; a palindrome is a number whose digit list is a palindrome.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_3197125

/-- `n` is a decimal palindrome. -/
def IsPal (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

theorem main :
    ∀ p : ℕ, p.Prime → 1 ∉ Nat.digits 10 p → IsPal p → IsPal (p ^ 2) → p = 2 ∨ p = 3 := by
  sorry

end OMA.S_mse_3197125
