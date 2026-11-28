import Mathlib

/-!
# A100571: Cubes m^3 such that m^3 is the sum of m-1 consecutive primes plus a larger prime.

Source: https://oeis.org/A100571
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: the sequence consists of all cubes `m^3` with `m > 1` except `8^3 = 512`.
-/

namespace OMA.S_oeis_a100571

/-- `m^3` is the sum of `m - 1` consecutive primes plus a strictly larger prime. -/
def IsCubeConsecPrimeSum (m : ℕ) : Prop :=
  ∃ i q : ℕ, Nat.Prime q ∧
    Nat.nth Nat.Prime (i + m - 2) < q ∧
    m ^ 3 = (∑ j ∈ Finset.range (m - 1), Nat.nth Nat.Prime (i + j)) + q

theorem main :
    ∀ m : ℕ, 1 < m → (IsCubeConsecPrimeSum m ↔ m ≠ 8) := by
  sorry

end OMA.S_oeis_a100571
