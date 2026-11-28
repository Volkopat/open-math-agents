import Mathlib

/-!
# A381636: Numbers whose prime indices cannot be partitioned into constant blocks with distinct
sums.

Source: https://oeis.org/A381636
Credit: @esracummings31-blip

Conjecture (Gus Wiseman): these are the zeros of A382876, the number of ways to permute the
prime indices of n so that the run-sums are all different.

Conventions.
* The prime indices of n form the multiset of m with prime(m) | n, counted with multiplicity;
  for a prime p its index is pi(p) = `Nat.primeCounting p` (so prime(m) has index m).
* A partition of a multiset M into constant blocks is a multiset P of nonempty multisets, each
  consisting of copies of a single value, whose sum is M; the block sums must be distinct.
* A382876(n) counts the distinct lists that are permutations of the prime indices of n whose
  run-sums (sums of the maximal runs of equal consecutive entries, the blocks of
  `l.splitBy (· == ·)`) are pairwise distinct.
-/

namespace OMA.S_oeis_a381636

/-- The prime indices of n, listed in weakly increasing order. -/
def primeIndexList (n : ℕ) : List ℕ := n.primeFactorsList.map Nat.primeCounting

/-- The multiset of prime indices of n. -/
def primeIndices (n : ℕ) : Multiset ℕ := (primeIndexList n : Multiset ℕ)

/-- M can be partitioned into constant blocks with distinct sums. -/
def HasConstBlockPartition (M : Multiset ℕ) : Prop :=
  ∃ P : Multiset (Multiset ℕ), P.sum = M ∧
    (∀ b ∈ P, b ≠ 0 ∧ ∃ v, b = Multiset.replicate (Multiset.card b) v) ∧
    (P.map Multiset.sum).Nodup

/-- The run-sums of a list. -/
def runSums (l : List ℕ) : List ℕ := (l.splitBy (· == ·)).map List.sum

/-- A382876(n): the number of permutations of the prime indices of n with distinct run-sums. -/
def A382876 (n : ℕ) : ℕ :=
  ((primeIndexList n).permutations.toFinset.filter (fun l => (runSums l).Nodup)).card

/-- n is in A381636. -/
def InA381636 (n : ℕ) : Prop := ¬ HasConstBlockPartition (primeIndices n)

theorem main : ∀ n : ℕ, 1 ≤ n → (InA381636 n ↔ A382876 n = 0) := by
  sorry

end OMA.S_oeis_a381636
