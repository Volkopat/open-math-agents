import Mathlib

/-!
# OEIS A066919: Iterating phi on Even Numbers and sigma on Odd Numbers Reaches 1

Source: https://oeis.org/A066919
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Define $f(n) = \phi(n)$ if $n$ is even, and $f(n) = \sigma(n)$ if $n$ is odd.

Conjecture: For every positive integer $n \ge 1$, repeated application of $f$ to $n$
eventually reaches $1$.
-/

namespace OMA.S_oeis_a066919

/-- Sum of positive divisors of `n`. -/
def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- `f(n) = φ(n)` if `n` is even, `σ(n)` if `n` is odd. -/
def step (n : ℕ) : ℕ :=
  if n % 2 = 0 then Nat.totient n else sigma n

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, step^[k] n = 1 := by
  sorry

end OMA.S_oeis_a066919
