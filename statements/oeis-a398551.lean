import Mathlib

/-!
# A398551: Even numbers that are not sums of two isolated primes.

Source: https://oeis.org/A398551
Credit: @azmiozgen

Conjecture (from the entry): 628 is the last term.

Formalization notes:
* An isolated prime (A007510) is a prime p with neither p - 2 nor p + 2 prime (2 is isolated).
* Stated as: 628 is not a sum of two isolated primes, and every even n > 628 is.
* Controls (computed): among even n < 100000 the last three non-represented are 482, 512, 628.
-/

namespace OMA.S_oeis_a398551

/-- `p` is an isolated prime. -/
def IsIsolated (p : ℕ) : Prop := p.Prime ∧ ¬ (p - 2).Prime ∧ ¬ (p + 2).Prime

/-- The conjecture of the entry. -/
theorem main :
    (¬ ∃ p q : ℕ, IsIsolated p ∧ IsIsolated q ∧ p + q = 628) ∧
      ∀ n : ℕ, 628 < n → Even n → ∃ p q : ℕ, IsIsolated p ∧ IsIsolated q ∧ p + q = n := by
  sorry

end OMA.S_oeis_a398551
