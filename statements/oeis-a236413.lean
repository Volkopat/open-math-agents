import Mathlib

/-!
# A236413: Positive integers m with p(m)^2 + q(m)^2 prime

Source: https://oeis.org/A236413
Credit: @gblacher2

Here `p(.)` is the partition function (A000041) and `q(.)` is the strict partition function
(A000009), the number of partitions into distinct parts. The entry states that, according to
the conjecture in A236412 (Zhi-Wei Sun), the sequence should have infinitely many terms.

In Mathlib, `p(m)` is the number of elements of `Nat.Partition m`, and `q(m)` is the number of
elements of `Nat.Partition.distincts m`, the partitions of `m` whose parts are pairwise distinct.
-/

namespace OMA.S_oeis_a236413

/-- `p(m)`: the number of partitions of `m` (A000041). -/
def partitionNumber (m : ℕ) : ℕ := Fintype.card (Nat.Partition m)

/-- `q(m)`: the number of partitions of `m` into distinct parts (A000009). -/
def strictPartitionNumber (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- There are infinitely many positive integers `m` with `p(m)^2 + q(m)^2` prime. -/
theorem main :
    {m : ℕ | 0 < m ∧ (partitionNumber m ^ 2 + strictPartitionNumber m ^ 2).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a236413
