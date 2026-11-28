import Mathlib

/-!
# Are odd primitive abundant numbers quasi practical?

Source: https://mathoverflow.net/questions/516513
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (MathOverflow): if `n` is an odd primitive abundant number (not a multiple of another
abundant number), is `(n+1)/2` a sum of distinct divisors of `n`?

Conventions:
* `n` is abundant if `σ(n) > 2n` (sum of proper divisors exceeds `n`); primitive abundant if it is
  abundant and no proper divisor of `n` is abundant ("not a multiple of other abundant numbers").
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_516513

/-- Abundant numbers. -/
def IsAbundant (n : ℕ) : Prop := n < ∑ d ∈ n.properDivisors, d

theorem main :
    ∀ n : ℕ, Odd n → IsAbundant n → (∀ d ∈ n.properDivisors, ¬ IsAbundant d) →
      ∃ s ⊆ n.divisors, ∑ d ∈ s, d = (n + 1) / 2 := by
  sorry

end OMA.S_mo_516513
