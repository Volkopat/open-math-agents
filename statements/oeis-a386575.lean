import Mathlib

/-!
# A386575: Number of distinct separable and pairwise disjoint sets of strict integer partitions,
one of each exponent in the prime factorization of n.

Source: https://oeis.org/A386575
Credit: @esracummings31-blip

Conjecture (Gus Wiseman): a(n) > 0 iff the multiset of prime factors of n has a permutation with
all distinct run lengths.

Conventions.
* a(n) > 0 means that at least one admissible family exists. A family assigns to every prime p a
  strict integer partition of the exponent of p in n, encoded as a finite set S p of positive
  integers with sum `n.factorization p` (so S p = ∅ when p ∤ n); for p ≠ q the sets S p and S q
  are disjoint. (Indexing by primes rather than by exponents does not affect existence.)
* The sets S p are the blocks of a set partition of their union U. It is separable iff U has a
  permutation (a duplicate-free list w listing exactly the elements of U) whose adjacent elements
  always lie in different blocks.
* A permutation of the prime factors of n is a list l with the same multiset of entries as
  `n.primeFactorsList`; its run lengths are the lengths of the blocks of `l.splitBy (· == ·)`.
-/

namespace OMA.S_oeis_a386575

/-- There is a separable pairwise disjoint family of strict partitions of the exponents of n. -/
def HasSeparableFamily (n : ℕ) : Prop :=
  ∃ S : ℕ → Finset ℕ,
    (∀ p, 0 ∉ S p) ∧
    (∀ p, ∑ x ∈ S p, x = n.factorization p) ∧
    (∀ p q, p ≠ q → Disjoint (S p) (S q)) ∧
    ∃ w : List ℕ, w.Nodup ∧ (∀ x, x ∈ w ↔ ∃ p, x ∈ S p) ∧
      w.IsChain (fun x y => ∀ p, x ∈ S p → y ∉ S p)

/-- The multiset of prime factors of n has a permutation with all distinct run lengths. -/
def HasDistinctRunPerm (n : ℕ) : Prop :=
  ∃ l : List ℕ, (l : Multiset ℕ) = (n.primeFactorsList : Multiset ℕ) ∧
    ((l.splitBy (· == ·)).map List.length).Nodup

theorem main : ∀ n : ℕ, 1 ≤ n → (HasSeparableFamily n ↔ HasDistinctRunPerm n) := by
  sorry

end OMA.S_oeis_a386575
