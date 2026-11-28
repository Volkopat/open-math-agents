import Mathlib

/-!
# A094339: Beginning with 2, least number not occurring earlier that divides the sum of all previous terms.

Source: https://oeis.org/A094339
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: this is a rearrangement of natural numbers.
-/

namespace OMA.S_oeis_a094339

/-- Prefix list of the first `n` terms of A094339. -/
noncomputable def prefixList : ℕ → List ℕ
  | 0 => []
  | 1 => [2]
  | n + 2 =>
    let prev := prefixList (n + 1)
    let nxt := sInf {m : ℕ | 1 ≤ m ∧ m ∉ prev ∧ m ∣ prev.sum}
    prev ++ [nxt]

/-- The `n`-th term of A094339 (1-indexed). -/
noncomputable def a (n : ℕ) : ℕ :=
  (prefixList n).getLastD 0

theorem main :
    ∀ m : ℕ, 1 ≤ m → ∃! n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a094339
