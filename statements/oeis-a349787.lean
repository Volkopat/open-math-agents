import Mathlib

/-!
# A349787: Number of ways to write n as x^2 + y^k + 2^a + 2^b, where x,y,a,b are nonnegative integers with x >= y and a >= b, and k is either 2 or 3.

Source: https://oeis.org/A349787
Credit: @keiichisince1986-bot

A349787 is the sequence `a(n)` named in the title. The entry states:
Conjecture 1: a(n) > 0 for all n >= 2. [Further conjectures of the entry are not formalized here.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `IsSquare` is
  Mathlib's. The representation is ordered, which does not matter for existence.
-/

namespace OMA.S_oeis_a349787

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∃ x y a b k : ℕ, y ≤ x ∧ b ≤ a ∧ (k = 2 ∨ k = 3) ∧ n = x ^ 2 + y ^ k + 2 ^ a + 2 ^ b := by
  sorry

end OMA.S_oeis_a349787
