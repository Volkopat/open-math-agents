import Mathlib

/-!
# A072633: Smallest m >= 1 with 1^n + 2^n + ... + m^n >= (m+1)^n

Source: https://oeis.org/A072633
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Smallest positive integer m where 1^n + 2^n + 3^n + ... + m^n is greater than or equal
to (m+1)^n.
Conjecture: a(n) = 1 + round(n / log(2)).
-/

namespace OMA.S_oeis_a072633

/-- Smallest positive integer `m` such that `∑_{k=1..m} k^n ≥ (m + 1)^n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | 1 ≤ m ∧ (m + 1) ^ n ≤ ∑ k ∈ Finset.Icc 1 m, k ^ n }

theorem main :
    ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = 1 + round ((n : ℝ) / Real.log 2) := by
  sorry

end OMA.S_oeis_a072633
