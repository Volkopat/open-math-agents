import Mathlib

/-!
# A002720: Number of partial permutations of an n-set; number of n X n binary matrices with at most one 1 in each row and column.

Source: https://oeis.org/A002720
Credit: @maaaakks

Conjecture (John Tyler Rascoe, Feb 28 2024), quoted from the entry:
"a(n)*k is the sum of the largest parts in all integer partitions containing their own
first differences with n + 1 parts and least part k."

## Reading

* `a n` (offset 0, data 1, 2, 7, 34, 209, 1546, ...) is the number of partial permutations
  of an `n`-set, i.e. of partial bijections `Fin n ⇀ Fin n`. Such a partial bijection is
  determined by its domain (an `i`-subset), its range (an `i`-subset) and a bijection between
  them, so `a n = ∑_{i=0}^{n} C(n,i)^2 * i!`; this is the formula recorded in the entry,
  and it is used below as the definition of `a`.
* An integer partition is a finite multiset of positive integers (`Multiset ℕ` with all
  elements positive).
* "Partitions containing their own first differences" is the notion of OEIS A364673
  ("Number of (necessarily strict) integer partitions of n containing all of their own first
  differences"): write the parts in weakly decreasing order `y_1 ≥ y_2 ≥ ... ≥ y_m`; the first
  differences are `y_i - y_{i+1}` (`1 ≤ i < m`), and the partition "contains" them when every
  difference is one of the parts (set containment, as in the A364673 example
  `(12,6,3,2,1)`, whose differences `(6,3,1,1)` satisfy `{1,3,6} ⊆ {1,2,3,6,12}`).
  A repeated part would give the difference `0`, which is not a part, so such partitions are
  necessarily strict; we nevertheless quantify over all partitions (multisets).
* "with n + 1 parts and least part k": the multiset has cardinality `n + 1`, contains `k`, and
  every part is `≥ k`. Here `k ≥ 1` (parts are positive) and `n ≥ 0`.
* "the sum of the largest parts in all" such partitions: the set of such partitions is a priori
  a subset of the infinite type `Multiset ℕ`; we assert that it is finite and that the
  (`finsum`) sum of the largest parts `p.sup` over it equals `a n * k`.

Check for `n = 0`: the only partition is `(k)`, with largest part `k = a 0 * k`.
-/

namespace OMA.S_oeis_a002720

/-- The number of partial permutations of an `n`-set, `∑_{i=0}^{n} C(n,i)^2 * i!`
(choose the domain, the range, and a bijection between them). -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), n.choose i ^ 2 * i.factorial

/-- A partition (multiset of parts) contains its own first differences: listing the parts in
weakly decreasing order `l`, every difference `l[i] - l[i+1]` of consecutive parts is a part. -/
def ContainsOwnFirstDifferences (p : Multiset ℕ) : Prop :=
  ∀ i (h : i + 1 < (p.sort (· ≥ ·)).length),
    (p.sort (· ≥ ·))[i] - (p.sort (· ≥ ·))[i + 1] ∈ p

/-- Integer partitions containing their own first differences, with `n + 1` parts and least
part `k`. -/
def admissible (n k : ℕ) : Set (Multiset ℕ) :=
  {p | (∀ x ∈ p, 0 < x) ∧ Multiset.card p = n + 1 ∧ k ∈ p ∧ (∀ x ∈ p, k ≤ x) ∧
    ContainsOwnFirstDifferences p}

theorem main : ∀ n k : ℕ, 1 ≤ k →
    (admissible n k).Finite ∧ ∑ᶠ p ∈ admissible n k, p.sup = a n * k := by
  sorry

end OMA.S_oeis_a002720
