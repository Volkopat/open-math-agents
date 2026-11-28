import Mathlib

/-!
# A221650: Tetrahedron P(n,j,k) = T(j,k)*p(n-j), where T(j,k) = 1 if k divides j otherwise 0.

Source: https://oeis.org/A221650
Credit: @agchua

Comments of A221650 (unsigned; the entry is by Omar E. Pol, Jan 21 2013):
  Conjecture 1: P(n,j,k) is the number of partitions of n that contain at least m parts of
  size k, where m = j/k, if k divides j otherwise P(n,j,k) = 0.
  Conjecture 2: P(n,j,k) is the number of parts that are the m-th part of size k in all
  partitions of n, where m = j/k, if k divides j otherwise P(n,j,k) = 0.
Offset of A221650: 1 (data 1, 1, 1, 1, 2, 1, 1, 1, 0, 1, 3, ...).

The tetrahedron has slices n >= 1, rows 1 <= j <= n and columns 1 <= k <= j (see the entry's
example); p is the partition function A000041, here the number of elements of Nat.Partition.
In Conjecture 2, the c parts of size k of a partition of n are numbered 1, ..., c, and the
partition contributes the number of them that are numbered m (one if 1 <= m <= c, else none);
these numbers are summed over all partitions of n.
-/

namespace OMA.S_oeis_a221650

/-- T(j,k) = 1 if k divides j, otherwise 0. -/
def T (j k : ℕ) : ℕ := if k ∣ j then 1 else 0

/-- P(n,j,k) = T(j,k)*p(n-j), with p(m) the number of partitions of m. -/
noncomputable def P (n j k : ℕ) : ℕ := T j k * Fintype.card (Nat.Partition (n - j))

/-- Conjectures 1 and 2 of the entry, for every entry P(n,j,k) of the tetrahedron. -/
theorem main : ∀ n j k : ℕ, 1 ≤ n → 1 ≤ j → j ≤ n → 1 ≤ k → k ≤ j →
    ((k ∣ j → P n j k = ((Finset.univ : Finset (Nat.Partition n)).filter
        (fun q => j / k ≤ q.parts.count k)).card) ∧ (¬ k ∣ j → P n j k = 0)) ∧
    ((k ∣ j → P n j k = ∑ q : Nat.Partition n,
        ((Finset.Icc 1 (q.parts.count k)).filter (fun i => i = j / k)).card) ∧
      (¬ k ∣ j → P n j k = 0)) := by
  sorry

end OMA.S_oeis_a221650
