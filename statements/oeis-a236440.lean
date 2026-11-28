import Mathlib

/-!
# A236440: Positive integers m with A000009(m)^2 + A047967(m)^2 prime

Source: https://oeis.org/A236440
Credit: @gblacher2

`A000009(m)` is the number of partitions of `m` into distinct parts, and `A047967(m)` is the
number of partitions of `m` with some part repeated (so `A047967(m) = A000041(m) - A000009(m)`).
The entry states that, according to the conjecture in A236439 (Zhi-Wei Sun), the sequence should
have infinitely many terms.

In Mathlib, a partition `c : Nat.Partition m` has its parts in the multiset `c.parts`; it has
distinct parts exactly when `c.parts.Nodup`, and some part repeated exactly when it does not.
-/

namespace OMA.S_oeis_a236440

/-- `A000009(m)`: the number of partitions of `m` into distinct parts. -/
def distinctPartitionCount (m : ℕ) : ℕ := (Nat.Partition.distincts m).card

/-- `A047967(m)`: the number of partitions of `m` with some part repeated. -/
def repeatedPartitionCount (m : ℕ) : ℕ :=
  (Finset.univ.filter fun c : Nat.Partition m => ¬ c.parts.Nodup).card

/-- There are infinitely many positive integers `m` with `A000009(m)^2 + A047967(m)^2` prime. -/
theorem main :
    {m : ℕ | 0 < m ∧
      (distinctPartitionCount m ^ 2 + repeatedPartitionCount m ^ 2).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a236440
