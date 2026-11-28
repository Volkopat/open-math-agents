import Mathlib

/-!
# A087372: Smallest k such that 3^k + 2n is prime

Source: https://oeis.org/A087372
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) is the smallest k such that 3^k + 2n is a prime, or 0 if no such k exists.
Conjecture: There exists a finite M such that a(n) < M for all n.
-/

namespace OMA.S_oeis_a087372

/-- `a(n)` is the smallest `k` such that `3^k + 2n` is prime, or `0` if none exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | (3 ^ k + 2 * n).Prime}

theorem main :
    ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n → a n < M := by
  sorry

end OMA.S_oeis_a087372
