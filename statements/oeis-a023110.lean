import Mathlib

/-!
# A023110: Squares which remain squares when the last decimal digit is removed

Source: https://oeis.org/A023110
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

## Problem Statement
Let `A023110` be the increasing sequence of squares `m` such that `⌊m / 10⌋` is also a square
(`0, 1, 4, 9, 16, 49, 169, 256, ...`).

Conjecture (Colin Barker, Dec 31 2017): Indexing from 0 (`a(0) = 0, a(1) = 1, ...`, which is
shifted by 1 from OEIS's 1-indexed `a(1) = 0, a(2) = 1, ...`), the linear recurrence
`a(n) = 1443 * a(n - 7) - 1443 * a(n - 14) + a(n - 21)`
holds for all `n ≥ 22` (corresponding to `n > 22` in 1-based indexing).
-/

namespace OMA.S_oeis_a023110

/-- `m` is a square that remains a square when its last base-10 digit is removed. -/
def isA023110 (m : ℕ) : Prop :=
  IsSquare m ∧ IsSquare (m / 10)

/-- The `n`-th term (0-indexed) of A023110. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth isA023110 n

theorem main :
    ∀ n : ℕ, 22 ≤ n →
      (a n : ℤ) = 1443 * (a (n - 7) : ℤ) - 1443 * (a (n - 14) : ℤ) + (a (n - 21) : ℤ) := by
  sorry

end OMA.S_oeis_a023110
