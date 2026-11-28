import Mathlib

/-!
# OEIS A064708: runs of numbers with exactly two distinct prime factors

Source: https://oeis.org/A064708
`a n` is the initial term of the first run of (at least) `n` consecutive numbers each with
exactly two distinct prime factors. Eggleton and MacDougall prove that no terms exist beyond
`a(9)` and conjecture that `a(9)` does not exist either, i.e. there is no run of `9`
consecutive integers each having exactly two distinct prime factors.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a064708

theorem main : ¬ ∃ m : ℕ, ∀ i < 9, (m + i).primeFactors.card = 2 := by
  sorry

end OMA.S_oeis_a064708
