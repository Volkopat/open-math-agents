import Mathlib

/-!
# A340061: Irregular triangle read by rows T(n,k) in which row n lists n blocks, where the m-th
block consists of A000041(n-m) copies of m, with n >= 1 and m >= 1.

Source: https://oeis.org/A340061
Credit: @esracummings31-blip

Conjecture (Omar E. Pol): all divisors of all terms of row n are also all parts of all partitions
of n.

Conventions.
* "All divisors of all terms of row n" is the multiset obtained by listing, for every term t of
  row n (with repetition), all positive divisors of t. "All parts of all partitions of n" is the
  multiset of parts of all partitions of n (with repetition). The conjecture is the equality of
  these two multisets (as in the OEIS example for n = 6: nineteen 1's, eight 2's, four 3's, two
  4's, one 5 and one 6 on both sides).
* A000041(j) is the number of partitions of j.
* The further remark in the entry, that every section of the set of partitions of n has
  "essentially the same correspondence" (see A336811), is not a precise statement and is not
  formalized here.
-/

namespace OMA.S_oeis_a340061

/-- A000041: the number of partitions of j. -/
def A000041 (j : ℕ) : ℕ := Fintype.card (Nat.Partition j)

/-- Row n of A340061: for m = 1..n, the block of A000041(n-m) copies of m. -/
def row (n : ℕ) : List ℕ :=
  (List.range n).flatMap (fun i => List.replicate (A000041 (n - (i + 1))) (i + 1))

theorem main : ∀ n : ℕ, 1 ≤ n →
    ((row n : Multiset ℕ).bind (fun t => (Nat.divisors t).val)) =
      (Finset.univ : Finset (Nat.Partition n)).val.bind (fun p => p.parts) := by
  sorry

end OMA.S_oeis_a340061
