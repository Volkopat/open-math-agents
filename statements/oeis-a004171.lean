import Mathlib

/-!
# A004171: a(n) = 2^(2n+1)

Source: https://oeis.org/A004171
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Statement:
A number of the form `2^(2n+1)` can never be the first power of 2 in a Collatz
sequence, except for the Collatz sequence starting with that number itself.
In other words, if a Collatz trajectory starting at a positive integer `x` reaches
`2^(2n+1)` at some step `t ≥ 1`, then some strictly earlier term in the trajectory
is already a power of 2.
-/

namespace OMA.S_oeis_a004171

/-- One step of the Collatz map. -/
def collatzStep (m : ℕ) : ℕ :=
  if m % 2 = 0 then m / 2 else 3 * m + 1

/-- The `t`-th iterate of the Collatz map starting from `x`. -/
def collatzOrbit (x t : ℕ) : ℕ :=
  collatzStep^[t] x

/-- Predicate asserting that `m` is a power of `2`. -/
def isPowerOfTwo (m : ℕ) : Prop :=
  ∃ e : ℕ, m = 2 ^ e

/-- No odd power of `2` (`2^(2n+1)`) can be the first power of `2` encountered in a
Collatz trajectory starting at a positive integer `x`, unless `x = 2^(2n+1)` itself. -/
theorem main :
    ∀ x n t : ℕ, 0 < x → 0 < t → collatzOrbit x t = 2 ^ (2 * n + 1) →
      ∃ s < t, isPowerOfTwo (collatzOrbit x s) := by
  sorry

end OMA.S_oeis_a004171
