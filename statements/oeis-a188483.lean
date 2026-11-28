import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Divisors

open scoped BigOperators

namespace OMA.S_oeis_a188483

/-- Sum of positive divisors `σ(n)`. -/
def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- OEIS A188483 (Kravitz conjecture): no positive integer `n` has abundance `σ(n) - 2n`
equal to a positive odd square `(2k + 1)^2`. -/
theorem main :
    ∀ n : ℕ, 0 < n → ¬ ∃ k : ℕ, sigma n = 2 * n + (2 * k + 1) ^ 2 := by
  sorry

end OMA.S_oeis_a188483
