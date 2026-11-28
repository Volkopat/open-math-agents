import Mathlib

/-!
# A382427: Number of integer partitions of n that can be partitioned into constant blocks with
distinct sums.

Source: https://oeis.org/A382427
Credit: @esracummings31-blip

Conjecture (Gus Wiseman): this is also the number of integer partitions of n having a permutation
with all distinct run-sums. We formalize the underlying statement: a partition can be
partitioned into constant blocks with distinct sums iff it has a permutation with all distinct
run-sums.

Conventions.
* A partition of y into constant blocks is a multiset P of nonempty multisets, each consisting of
  copies of a single value, whose sum (multiset union) is the multiset of parts of y. The block
  sums must be pairwise distinct.
* A permutation of the parts of y is a list l with the same multiset of entries; its run-sums are
  the sums of its maximal runs of equal consecutive entries, i.e. of the blocks of
  `l.splitBy (· == ·)`.
-/

namespace OMA.S_oeis_a382427

/-- y can be partitioned into constant blocks with distinct sums. -/
def HasConstBlockPartition {n : ℕ} (y : Nat.Partition n) : Prop :=
  ∃ P : Multiset (Multiset ℕ), P.sum = y.parts ∧
    (∀ b ∈ P, b ≠ 0 ∧ ∃ v, b = Multiset.replicate (Multiset.card b) v) ∧
    (P.map Multiset.sum).Nodup

/-- The run-sums of a list: sums of its maximal runs of equal consecutive entries. -/
def runSums (l : List ℕ) : List ℕ := (l.splitBy (· == ·)).map List.sum

/-- y has a permutation with all distinct run-sums. -/
def HasDistinctRunSumPerm {n : ℕ} (y : Nat.Partition n) : Prop :=
  ∃ l : List ℕ, (l : Multiset ℕ) = y.parts ∧ (runSums l).Nodup

theorem main : ∀ (n : ℕ) (y : Nat.Partition n), HasConstBlockPartition y ↔ HasDistinctRunSumPerm y := by
  sorry

end OMA.S_oeis_a382427
