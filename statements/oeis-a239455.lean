import Mathlib

/-!
# A239455: Number of Look-and-Say partitions of n.

Source: https://oeis.org/A239455
Credit: @esracummings31-blip

Conjecture (Gus Wiseman, Aug 11 2025): a partition is Look-and-Say iff it has a permutation with
all distinct run-lengths.

Conventions.
* For a partition p whose distinct parts y(1) > ... > y(h) occur with multiplicities
  m(1), ..., m(h), the Look-and-Say partition LS(p) consists of y(i) copies of m(i) for each i
  ("m(1) y(1)'s, ..., m(h) y(h)'s", with the roles of m and y reversed). A partition y of n is
  Look-and-Say if y = LS(p) for some partition p of n (LS preserves the sum).
* A permutation of the parts of y is a list l with the same multiset of entries; its run-lengths
  are the lengths of its maximal runs of equal consecutive entries, i.e. of the blocks of
  `l.splitBy (· == ·)`.
-/

namespace OMA.S_oeis_a239455

/-- LS(p): for each distinct part v of p, take v copies of its multiplicity. -/
def LS (p : Multiset ℕ) : Multiset ℕ :=
  ∑ v ∈ p.toFinset, Multiset.replicate v (p.count v)

/-- y is a Look-and-Say partition of n. -/
def IsLookAndSay {n : ℕ} (y : Nat.Partition n) : Prop :=
  ∃ p : Nat.Partition n, LS p.parts = y.parts

/-- The run-lengths of a list: lengths of its maximal runs of equal consecutive entries. -/
def runLengths (l : List ℕ) : List ℕ := (l.splitBy (· == ·)).map List.length

/-- y has a permutation with all distinct run-lengths. -/
def HasDistinctRunPerm {n : ℕ} (y : Nat.Partition n) : Prop :=
  ∃ l : List ℕ, (l : Multiset ℕ) = y.parts ∧ (runLengths l).Nodup

theorem main : ∀ (n : ℕ) (y : Nat.Partition n), IsLookAndSay y ↔ HasDistinctRunPerm y := by
  sorry

end OMA.S_oeis_a239455
