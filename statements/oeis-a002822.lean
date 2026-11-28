import Mathlib

/-!
# A002822: twin primes `6m ± 1`

Source: https://oeis.org/A002822
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Bob Selcoe, listed in A002822): when `a(n) = 6j`, `j` is also in the sequence, where
the sequence lists the numbers `m` such that `6m - 1` and `6m + 1` are twin primes.

Conventions:
* `m ≥ 1`; `j` ranges over positive integers.
-/

namespace OMA.S_oeis_a002822

/-- `m` is in A002822. -/
def InSeq (m : ℕ) : Prop := 1 ≤ m ∧ (6 * m - 1).Prime ∧ (6 * m + 1).Prime

theorem main : ∀ j : ℕ, 1 ≤ j → InSeq (6 * j) → InSeq j := by
  sorry

end OMA.S_oeis_a002822
