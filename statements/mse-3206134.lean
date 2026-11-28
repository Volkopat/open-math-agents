import Mathlib

/-!
# Can the product of `n > 5` positive integers in A.P. be a palindrome?

Source: https://math.stackexchange.com/questions/3206134
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (1): can the product of `n` positive integers in arithmetic progression, `n > 5`, be a
(decimal) palindrome? A computer search found none; `main` states that the answer is no.

Conventions:
* The progression is `a, a + d, …, a + (n-1)d` with `a ≥ 1` and common difference `d ≥ 1` (a
  constant progression such as `1, 1, …, 1` would trivially give the palindrome `1`).
* A palindrome is a number whose decimal digit list equals its reverse.
-/

namespace OMA.S_mse_3206134

/-- `m` is a decimal palindrome. -/
def IsPalindrome (m : ℕ) : Prop := (Nat.digits 10 m).reverse = Nat.digits 10 m

/-- No product of `n ≥ 6` terms of a nonconstant positive arithmetic progression is a
palindrome. -/
theorem main : ∀ n a d : ℕ, 6 ≤ n → 1 ≤ a → 1 ≤ d →
    ¬ IsPalindrome (∏ i ∈ Finset.range n, (a + i * d)) := by
  sorry

end OMA.S_mse_3206134
