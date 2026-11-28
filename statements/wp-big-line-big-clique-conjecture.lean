import Mathlib

-- Big-line-big-clique conjecture (Kára, Pór, Wood 2005)
-- Source: https://en.wikipedia.org/wiki/Big-line-big-clique_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
Source: for any positive integers `k` and `ℓ` there should exist a number `n_{k,ℓ}` such that every
set of `n_{k,ℓ}` points (in the Euclidean plane) contains `ℓ` collinear points (a big line), `k`
mutually visible points (a big clique), or both. Two points of the set are visible to each other
when no third point of the set blocks them, i.e. the segment between them contains no other
point of the set.

Conventions:
* The plane is `EuclideanSpace ℝ (Fin 2)`; point sets are finite (`Finset`).
* Every set of at least `n` points is required to satisfy the dichotomy: this is the wording of
  the original (Kára–Pór–Wood, Discrete Comput. Geom. 34 (2005), Conjecture 2, cited by the
  source: every set of at least `n` points contains `ℓ` collinear or `k` pairwise visible points).
  The original takes `k, ℓ ≥ 2`; the source's positive `k, ℓ` adds only trivial cases.
* `p, q` (distinct) are visible in `S` iff no point of `S` lies in the open segment between them
  (`openSegment`, which for `p ≠ q` excludes exactly the two endpoints).
* A big line is an `ℓ`-element subset that is `Collinear`; a big clique is a `k`-element subset of
  pairwise visible points (visibility measured in the whole set `S`).
-/

namespace OMA.S_wp_big_line_big_clique_conjecture

/-- `p` and `q` see each other within `S`: no point of `S` lies strictly between them. -/
def Visible (S : Finset (EuclideanSpace ℝ (Fin 2))) (p q : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∀ r ∈ S, r ∉ openSegment ℝ p q

/-- The big-line-big-clique conjecture. -/
theorem main : ∀ k ℓ : ℕ, 0 < k → 0 < ℓ → ∃ n : ℕ, ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    n ≤ S.card →
      (∃ L ⊆ S, L.card = ℓ ∧ Collinear ℝ (L : Set (EuclideanSpace ℝ (Fin 2)))) ∨
      (∃ C ⊆ S, C.card = k ∧ ∀ p ∈ C, ∀ q ∈ C, p ≠ q → Visible S p q) := by
  sorry

end OMA.S_wp_big_line_big_clique_conjecture
