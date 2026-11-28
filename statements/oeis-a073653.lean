import Mathlib

/-!
# A073653: Greedy distinct primes with consecutive triple sums prime

Source: https://oeis.org/A073653
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(1) = 3, a(2) = 5; for n > 2, a(n) = smallest prime not included earlier such that
a(n-2) + a(n-1) + a(n) is a prime.
Conjecture: Every odd prime eventually appears, and a(n) ~ prime(n).
-/

namespace OMA.S_oeis_a073653

open Filter Topology

/-- The greedy sequence `a` (0-indexed: `a 0 = 3`, `a 1 = 5`). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.strongRecOn n fun m ih =>
    match m with
    | 0 => 3
    | 1 => 5
    | m' + 2 =>
      sInf { p : ℕ | Nat.Prime p ∧
        (∀ k (hk : k < m' + 2), p ≠ ih k hk) ∧
        Nat.Prime (ih m' (by omega) + ih (m' + 1) (by omega) + p) }

theorem main :
    (∀ p : ℕ, Nat.Prime p → Odd p → ∃ n : ℕ, a n = p) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / (Nat.nth Nat.Prime n : ℝ)) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a073653
