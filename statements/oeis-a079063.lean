import Mathlib

/-!
# A079063: Least k such that sqrt(prime(n+k)) - sqrt(prime(n)) > 1.

Source: https://oeis.org/A079063
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Inspired by Andrica's conjecture. If it is true, a(n) > 1 for all n.
Conjecture: there is a constant c > 0 such that for n large enough, a(n) > c*sqrt(n)
and we can take c = 0.4.
-/

namespace OMA.S_oeis_a079063

/-- Least `k` such that `√prime(n+k) - √prime(n) > 1` (0-indexed primes). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { k : ℕ | Real.sqrt (Nat.nth Nat.Prime (n + k) : ℝ) -
    Real.sqrt (Nat.nth Nat.Prime n : ℝ) > 1 }

theorem main :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (a n : ℝ) > ((2 : ℝ) / 5) * Real.sqrt (n : ℝ) := by sorry

end OMA.S_oeis_a079063
