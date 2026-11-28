import Mathlib

/-!
# OEIS A014092: Numbers that are not the sum of 2 primes

Source: https://oeis.org/A014092
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Goldbach): Every even integer greater than 2 is the sum of two primes;
equivalently, every integer greater than 2 that is not the sum of two primes is odd
(and hence equal to 2 plus 1 or an odd composite number).
-/

namespace OMA.S_oeis_a014092

def IsNotSumOfTwoPrimes (n : ℕ) : Prop :=
  ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p + q ≠ n

theorem main :
    ∀ n : ℕ, n > 2 → IsNotSumOfTwoPrimes n → Odd n := by
  sorry

end OMA.S_oeis_a014092
