import Mathlib

/-!
# A Hall-type criterion for matchings of a given size

Source: https://mathoverflow.net/questions/459015
Asked by MathOverflow user errorist.

Let `G = (X, Y, E)` be a bipartite graph with `|X| = |Y| = n`. Hall's marriage theorem says
that `G` has a perfect matching if and only if `|S| ≤ |N(S)|` for every `S ⊆ X`. The question
asks whether there is a generalization of this theorem for checking whether `G` has a
matching of size `k`, for a given `k ≤ n`.

This file formalizes the deficiency version of Hall's theorem as the answer: `G` has a
matching of size `k` if and only if `|S| ≤ |N(S)| + (n - k)` for every `S ⊆ X`.

Translation choices.
* The two sides are finite types `X` and `Y` with `n` elements each, and the edge relation is
  a decidable relation `E : X → Y → Prop`.
* A matching of size `k` is given by a set `S ⊆ X` of `k` vertices and a map `f : X → Y`
  which is injective on `S` and sends each `x ∈ S` to a neighbour `f x` of `x`; its edges are
  the pairs `(x, f x)` for `x ∈ S`.
* `N(S)` is the set of vertices of `Y` adjacent to some vertex of `S`.
-/

namespace OMA.S_mo_459015

theorem main :
    ∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      (E : X → Y → Prop) [DecidableRel E] (n k : ℕ),
      Fintype.card X = n → Fintype.card Y = n → k ≤ n →
      ((∃ S : Finset X, S.card = k ∧ ∃ f : X → Y, Set.InjOn f S ∧ ∀ x ∈ S, E x (f x)) ↔
        ∀ S : Finset X, S.card ≤ (Finset.univ.filter fun y => ∃ x ∈ S, E x y).card + (n - k)) := by
  sorry

end OMA.S_mo_459015
