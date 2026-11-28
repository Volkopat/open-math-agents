import Mathlib

/-!
# A072124: Smallest factorial containing exactly n 1's

Source: https://oeis.org/A072124
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
Among `0 ≤ n ≤ 10000`, there are exactly `746` values of `n` for which no factorial `k!`
contains exactly `n` occurrences of the digit `1` in its base-10 representation.

Conventions:
- The number of `1`'s in `k!` is `(Nat.digits 10 (Nat.factorial k)).count 1`.
- Cardinality is stated with `Set.ncard`.
-/

namespace OMA.S_oeis_a072124

theorem main :
    Set.ncard
      {n : ℕ | n ≤ 10000 ∧ ∀ k : ℕ, (Nat.digits 10 (Nat.factorial k)).count 1 ≠ n} = 746 := by
  sorry

end OMA.S_oeis_a072124
