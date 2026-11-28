import Mathlib

/-!
# Monotone patterns are the only stable consecutive patterns

Shaoshi Chen, Hanqian Fang and Sergey Kitaev, "On stable patterns and properties on permutations
of multisets", arXiv:2602.13566, Conjecture 6.1.
Source: https://arxiv.org/abs/2602.13566

For a multiplicity vector (k₁, …, kₙ), M(k₁, …, kₙ)* is the set of permutations (words) of the
multiset with kᵢ copies of the letter i. A consecutive pattern p with distinct letters occurs at a
position of a word when the factor of length |p| starting there is order-isomorphic to p. The
pattern p is stable if, for every multiset and every s, the number of permutations of the
multiset with exactly s occurrences of p does not change when the multiplicities are permuted
(Section 2). Conjecture 6.1: a consecutive pattern is stable if and only if it is monotone, i.e.
equal to 12⋯ℓ or ℓ(ℓ-1)⋯1. The "if" direction is Theorem 4.5 of the paper.

Conventions here: patterns are lists of 0, …, ℓ-1 (a permutation of `List.range ℓ`, as the paper
assumes distinct letters throughout), letters of a word are 0, …, n-1, and multiplicities are a
`List ℕ`, so permuting multiplicities is `List.Perm` (zero multiplicities allowed, as in the
paper's 𝓜ₙ). Order-isomorphism is written as `f[a] < f[b] ↔ p[a] < p[b]` for all positions,
which forces the factor's letters to be distinct.

Literature: searches found no resolution. A brute-force check (multisets of total size ≤ 8 on at
most 4 letters) found an unstabilising pair of multisets for each non-monotone pattern of length
3 and none for 123, 321; for length 4 that range is too small to separate patterns.
-/

namespace OMA.S_arxiv_2602_13566

/-- The permutations of the multiset with `k[i]` copies of the letter `i`. -/
def words (k : List ℕ) : List (List ℕ) :=
  ((k.mapIdx fun i c => List.replicate c i).flatten).permutations.dedup

/-- The number of consecutive occurrences of the pattern `p` in the word `w`. -/
def occurrences (p w : List ℕ) : ℕ :=
  ((List.range w.length).filter fun j =>
    let f := (w.drop j).take p.length
    f.length = p.length ∧
      ∀ a < p.length, ∀ b < p.length, (f.getD a 0 < f.getD b 0 ↔ p.getD a 0 < p.getD b 0)).length

/-- The number of permutations of the multiset `k` with exactly `s` occurrences of `p`. -/
def count (p k : List ℕ) (s : ℕ) : ℕ :=
  ((words k).filter fun w => occurrences p w = s).length

/-- The pattern `p` is stable: its distribution is invariant under permuting multiplicities. -/
def Stable (p : List ℕ) : Prop :=
  ∀ k k' : List ℕ, k.Perm k' → ∀ s, count p k s = count p k' s

theorem main : ∀ p : List ℕ, p.Perm (List.range p.length) →
    (Stable p ↔ p = List.range p.length ∨ p = (List.range p.length).reverse) := by
  sorry

end OMA.S_arxiv_2602_13566
