import Mathlib

/-!
# OEIS A000629: Row sums of A154921

Source: https://oeis.org/A000629
Triangle: https://oeis.org/A154921 (formula (1))
Ordered partitions: https://oeis.org/A000670
Credit: @justusklocke-cloud
-/

namespace OMA.S_oeis_a000629

/-- A000629 counts cyclically ordered partitions of `n + 1` labeled beads. -/
def necklaceCount (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond (n + 1) (k + 1) * k.factorial

/-- A000670 counts linearly ordered partitions of `n` labeled points. -/
def orderedPartitionCount (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), Nat.stirlingSecond n j * j.factorial

/-- A154921, with `k` fallen horses and an ordered partition of the remaining finishers. -/
def triangleEntry (n k : ℕ) : ℕ :=
  n.choose k * orderedPartitionCount (n - k)

/-- A000629 is the sequence of row sums of A154921. -/
theorem main : ∀ n : ℕ,
    necklaceCount n = ∑ k ∈ Finset.range (n + 1), triangleEntry n k := by
  sorry

end OMA.S_oeis_a000629
