import Mathlib

/-!
# Consecutive prime partition numbers

OEIS A355728 conjectures that infinitely many positive indices have prime
partition numbers at both the index and its successor.

Source: https://oeis.org/A355728
Credit: @K2izis
-/

namespace OMA.S_oeis_a355728

/-- The number of integer partitions of n. -/
def partitionCount (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

theorem main :
    Set.Infinite {k : ℕ | 1 ≤ k ∧ (partitionCount k).Prime ∧ (partitionCount (k + 1)).Prime} := by
  sorry

end OMA.S_oeis_a355728
