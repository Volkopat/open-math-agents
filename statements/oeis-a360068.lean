import Mathlib

/-!
# A360068: Number of integer partitions of n such that the parts have the same mean as the multiplicities.

Source: https://oeis.org/A360068
Credit: @agchua

Comment line of A360068 (the entry is by Gus Wiseman, Jan 27 2023):
  Conjecture: If n is squarefree, then a(n) = 0.
The entry has offset 0. `a n` counts the partitions p of n (Mathlib's `Nat.Partition n`) such
that the mean of the parts, counted with repetition, equals the mean of the multiplicities of
the distinct parts, as in the entry's Mathematica program (it compares the Mean of the partition
with the Mean of the lengths of its runs of equal parts). Both means are computed in ℚ; for
n = 0 both are 0/0 = 0 in Lean, which agrees with the listed a(0) = 1.
Range: the listed term a(1) = 1 (the partition (1)) shows that the claim fails for the
squarefree number n = 1, a boundary case. For n >= 2 the claim has content, and it is stated for
every squarefree n >= 2.
-/

namespace OMA.S_oeis_a360068

/-- The mean of the parts of p, counted with repetition. -/
def meanParts {n : ℕ} (p : Nat.Partition n) : ℚ :=
  (p.parts.sum : ℚ) / (Multiset.card p.parts : ℚ)

/-- The mean of the multiplicities of the distinct parts of p. -/
def meanMult {n : ℕ} (p : Nat.Partition n) : ℚ :=
  ((∑ x ∈ p.parts.toFinset, p.parts.count x : ℕ) : ℚ) / (p.parts.toFinset.card : ℚ)

/-- A360068(n): the number of partitions of n whose parts have the same mean as their
multiplicities. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition n => meanParts p = meanMult p)).card

/-- The conjecture, for every squarefree n >= 2: a(n) = 0. -/
theorem main : ∀ n : ℕ, 2 ≤ n → Squarefree n → a n = 0 := by
  sorry

end OMA.S_oeis_a360068
