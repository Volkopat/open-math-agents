import Mathlib

/-!
# A384350: Number of subsets of {1..n} containing at least one element that is a sum of distinct
non-elements.

Source: https://oeis.org/A384350
Credit: @esracummings31-blip

Conjecture (Gus Wiseman): a(n) is also the number of subsets of {1..n} such that it is possible
in more than one way to choose a disjoint family of strict integer partitions, one of each
element.

Conventions.
* A subset S of {1..n} contains "an element that is a sum of distinct non-elements" if some
  s in S equals the sum of a finite set T of positive integers none of which lies in S.
* A strict integer partition of s is a finite set of positive integers with sum s.
* A disjoint family of strict integer partitions, one of each element of S, is a choice
  `f s` of a strict partition of s for every s in S, with `f s` and `f t` disjoint for s ≠ t.
  Two choices are the same way iff they agree at every element of S.
* "More than one way" means there are two such families that differ at some element of S.
-/

namespace OMA.S_oeis_a384350

/-- Some element of `S` is a sum of distinct non-elements of `S`. -/
def HasNonElementSum (S : Finset ℕ) : Prop :=
  ∃ s ∈ S, ∃ T : Finset ℕ, (∀ t ∈ T, 0 < t ∧ t ∉ S) ∧ T.sum id = s

/-- `f` is a disjoint family of strict integer partitions, one of each element of `S`. -/
def IsFamily (S : Finset ℕ) (f : ℕ → Finset ℕ) : Prop :=
  (∀ s ∈ S, (∀ x ∈ f s, 0 < x) ∧ (f s).sum id = s) ∧
  (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint (f s) (f t))

/-- There is more than one way to choose such a family. -/
def MoreThanOneWay (S : Finset ℕ) : Prop :=
  ∃ f g : ℕ → Finset ℕ, IsFamily S f ∧ IsFamily S g ∧ ∃ s ∈ S, f s ≠ g s

/-- A384350(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  open Classical in ((Finset.Icc 1 n).powerset.filter HasNonElementSum).card

theorem main : ∀ n : ℕ,
    a n = (open Classical in ((Finset.Icc 1 n).powerset.filter MoreThanOneWay).card) := by
  sorry

end OMA.S_oeis_a384350
