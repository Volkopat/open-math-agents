import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a397578

/-- The sum of positive divisors function `σ(k) = A000203(k)`. -/
def sigma (k : ℕ) : ℕ :=
  ∑ d ∈ k.divisors, d

/-- Conjecture (OEIS A397578): for every positive integer `n ≥ 1`, there exists `k ≥ 2` such that
`σ(k) > σ(k - 1) * n` and `σ(k) > σ(k + 1) * n`, i.e., `a(n)` exists for all `n ≥ 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ k : ℕ, 2 ≤ k ∧ sigma k > sigma (k - 1) * n ∧ sigma k > sigma (k + 1) * n := by
  sorry

end OMA.S_oeis_a397578
