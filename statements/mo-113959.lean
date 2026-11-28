import Mathlib

/-!
# A function whose fixed points are the primes

Source: https://mathoverflow.net/questions/113959/a-function-whose-fixed-points-are-the-primes
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `a(n)` be the largest proper divisor of `n` and `f(n) = n + a(n) - 1` for `n ≥ 2`; the fixed
points of `f` are the primes. Question: is every number preperiodic, i.e. is
`f(f(⋯ f(n) ⋯))` eventually prime? `main` states the positive answer.

For `n ≥ 2` the largest proper divisor is `n / p` with `p` the least prime factor of `n`
(`Nat.minFac`). Since `f(n) ≥ n`, iterates stay `≥ 2`.
-/

namespace OMA.S_mo_113959

/-- `f(n) = n + a(n) - 1`, `a(n)` the largest proper divisor. -/
def f (n : ℕ) : ℕ := n + n / n.minFac - 1

/-- Every `n ≥ 2` reaches a prime under iteration of `f`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, (f^[k] n).Prime := by
  sorry

end OMA.S_mo_113959
