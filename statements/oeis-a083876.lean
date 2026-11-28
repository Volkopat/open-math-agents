import Mathlib

/-!
# A083876: Least pseudoprime to base 2 through base prime(n).

Source: https://oeis.org/A083876
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: for n > 1, a(n) is the smallest Carmichael number k with lpf(k) > prime(n).
-/

namespace OMA.S_oeis_a083876

def isCarmichael (k : ℕ) : Prop :=
  1 < k ∧ ¬ Nat.Prime k ∧ ∀ b : ℕ, Nat.Coprime b k → b ^ (k - 1) % k = 1

noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 < m ∧ ¬ Nat.Prime m ∧
    ∀ b : ℕ, 2 ≤ b → b ≤ Nat.nth Nat.Prime (n - 1) → b ^ (m - 1) % m = 1}

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      a n = sInf {k : ℕ | isCarmichael k ∧ Nat.nth Nat.Prime (n - 1) < k.minFac} := by
  sorry

end OMA.S_oeis_a083876
