import Mathlib

/-!
# A391629: Number of multisets summing to n (or reversed partitions of n) that are not the first
sums of any integer partition.

Source: https://oeis.org/A391629
Credit: @esracummings31-blip

Conjecture: a(n) = A000041(n) - A368684(n), for n >= 1.

Conventions.
* A multiset summing to n is an integer partition q of n written as its weakly increasing list
  of parts (the entry: "a multiset is a finite weakly increasing sequence of positive integers").
* An integer partition p is a finite weakly decreasing sequence of positive integers (of any
  sum).
* The first sums of a nonempty sequence (a, b, c, d, ...) are (a+b, b+c, c+d, ...); for a list
  `p` this is `List.zipWith (· + ·) p p.tail`.
* a(n) counts the partitions q of n such that no integer partition p has first sums equal to
  the weakly increasing list of parts of q. (This matches the listed terms, e.g. a(6) = 9:
  only (6) = first sums of (5,1) and (2,2,2) = first sums of (1,1,1,1) are excluded.)
* A000041(n) = number of partitions of n; A368684(n) = number of partitions of n into 2 parts
  (s, n-s), 1 <= s <= n-s, such that the smaller part s divides both n and floor(n/2).
-/

namespace OMA.S_oeis_a391629

/-- First sums of a sequence. -/
def firstSums (p : List ℕ) : List ℕ := List.zipWith (· + ·) p p.tail

/-- The parts of a partition in weakly increasing order (the multiset as a sequence). -/
def partsAsc {n : ℕ} (q : Nat.Partition n) : List ℕ := q.parts.sort (· ≤ ·)

/-- `q` is the first sums of some integer partition. -/
def IsFirstSumsOfPartition {n : ℕ} (q : Nat.Partition n) : Prop :=
  ∃ p : List ℕ, (∀ x ∈ p, 0 < x) ∧ p.Pairwise (· ≥ ·) ∧ firstSums p = partsAsc q

/-- A391629(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  open Classical in (Finset.univ.filter (fun q : Nat.Partition n => ¬ IsFirstSumsOfPartition q)).card

/-- A000041. -/
def A000041 (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- A368684. -/
def A368684 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n / 2)).filter (fun s => s ∣ n ∧ s ∣ n / 2)).card

theorem main : ∀ n : ℕ, 1 ≤ n → a n = A000041 n - A368684 n := by
  sorry

end OMA.S_oeis_a391629
