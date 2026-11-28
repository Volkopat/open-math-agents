import Mathlib

/-!
# A325269: partitions with two distinct parts or at least three parts

Source: https://oeis.org/A325269
Credit: @ivillar

Status: known result: the entry records a proof (Vladeta Jovovic, Nov 14 2026).

A325269 (offset 0): a(n) is the number of integer partitions of n with 2 distinct parts or at
least 3 parts; data 0, 0, 0, 2, 3, 6, 9, 14, 20, 29, 40, 55, ...
(for n = 4 the partitions are 3+1, 2+1+1 and 1+1+1+1).

Conjecture (R. J. Mathar, Dec 13 2022): a(n) = A000041(n) - A000034(n-1) for n > 0, where
A000041 is the number of partitions of n and A000034 is the periodic sequence 1, 2, 1, 2, ...
(A000034(m) = 1 + (m mod 2)). Vladeta Jovovic (Nov 14 2026) records a proof in the entry.

Formalization: partitions of n are Mathlib's `Nat.Partition n`, whose `parts` is the multiset of
parts. "2 distinct parts" means exactly two parts, which are different (`Multiset.Nodup`); the
entry's g.f. removes exactly the empty partition, the partitions with one part and the partitions
with two equal parts. The subtraction is in ℕ and is exact.
-/

namespace OMA.S_oeis_a325269

/-- a(n): the number of partitions of n with exactly two parts that are distinct, or with at
least three parts. -/
def a (n : ℕ) : ℕ :=
  Fintype.card {p : n.Partition // (p.parts.card = 2 ∧ p.parts.Nodup) ∨ 3 ≤ p.parts.card}

/-- Mathar's formula a(n) = p(n) - A000034(n-1) for n > 0. -/
theorem main : ∀ n : ℕ, 0 < n → a n = Fintype.card n.Partition - (1 + (n - 1) % 2) := by
  sorry

end OMA.S_oeis_a325269
