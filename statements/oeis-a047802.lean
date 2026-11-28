import Mathlib

/-!
# A047802: Cubefree conjecture for smallest abundant numbers avoiding the first n primes

Source: https://oeis.org/A047802
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A047802: Smallest abundant number (sigma(x) > 2x) which is not divisible by any of the
first n primes.

Statement:
Conjecture: other than a(1) = 945, all terms are cubefree.

Conventions:
- `a(n)` is 0-indexed: `a(0) = 12` (avoiding 0 primes), `a(1) = 945` (avoiding `2`), etc.
- `ArithmeticFunction.sigma 1 x` is the sum-of-divisors function `sigma(x)`.
-/

namespace OMA.S_oeis_a047802

/-- `a(n)`: smallest abundant number not divisible by any of the first `n` primes. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {x : ℕ | 0 < x ∧ 2 * x < ArithmeticFunction.sigma 1 x ∧
    ∀ k < n, ¬ Nat.nth Nat.Prime k ∣ x}

theorem main :
    ∀ n : ℕ, n ≠ 1 → ∀ p : ℕ, Nat.Prime p → ¬ p ^ 3 ∣ a n := by
  sorry

end OMA.S_oeis_a047802
