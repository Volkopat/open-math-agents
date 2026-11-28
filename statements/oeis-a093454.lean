import Mathlib

/-!
# A093454: a(n) = floor((LCM of next n numbers)/n!).

Source: https://oeis.org/A093454
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: There are finitely many numbers of the form {LCM of next n numbers}/n!
which are not integers.
-/

namespace OMA.S_oeis_a093454

/-- The `n`-th block of consecutive positive integers (1-indexed):
`n*(n-1)/2 + 1, ..., n*(n+1)/2`. -/
def block (n : ℕ) : Finset ℕ :=
  Finset.Icc (n * (n - 1) / 2 + 1) (n * (n + 1) / 2)

/-- The least common multiple of the `n`-th block of `n` consecutive positive integers. -/
def blockLcm (n : ℕ) : ℕ :=
  (block n).lcm id

theorem main :
    {n : ℕ | 1 ≤ n ∧ ¬ (Nat.factorial n ∣ blockLcm n)}.Finite := by
  sorry

end OMA.S_oeis_a093454
