import Mathlib

/-!
# OEIS A096319: last digit of sums of primes is not eventually periodic

Source: https://oeis.org/A096319
`a n` is the final decimal digit of the sum of the first `n` primes. Conjecture: this sequence
carried to infinity is non-repeating, i.e. not eventually periodic (so the decimal formed by
concatenating its terms is irrational).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a096319

/-- Last digit of `∑_{i < n} prime(i+1)`. -/
noncomputable def a (n : ℕ) : ℕ := (∑ i ∈ Finset.range n, Nat.nth Nat.Prime i) % 10

theorem main : ¬ ∃ N T : ℕ, 0 < T ∧ ∀ n ≥ N, a (n + T) = a n := by
  sorry

end OMA.S_oeis_a096319
