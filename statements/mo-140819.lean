import Mathlib

/-!
# Graphs with graphic imbalance sequences (Imbalance Conjecture)

Source: https://mathoverflow.net/questions/140819/graphs-with-graphic-imbalance-sequences
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For an edge `e = uv` of a simple graph `G`, its imbalance is `imb(e) = |d(u) - d(v)|`.
Imbalance Conjecture: if `imb(e) > 0` for every edge `e` of `G`, then the multiset of edge
imbalances `M_G` is graphic.

## Encoding

* `G` is a finite simple graph. A multiset of nonnegative integers indexed by the edges is
  graphic if some simple graph on one vertex per entry has exactly these degrees; so `main` asks
  for a simple graph `H` on the vertex type `G.edgeSet` in which the vertex `s(u, v)` has degree
  `|d(u) - d(v)|`.
-/

namespace OMA.S_mo_140819

/-- The imbalance `|d(u) - d(v)|` of the (unordered) pair `u, v`. -/
noncomputable def imb {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : ℕ :=
  Int.natAbs ((G.degree u : ℤ) - G.degree v)

theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ u v, G.Adj u v → 0 < imb G u v) →
        ∃ (H : SimpleGraph G.edgeSet) (_ : DecidableRel H.Adj),
          ∀ u v (h : G.Adj u v), H.degree ⟨s(u, v), h⟩ = imb G u v := by
  sorry

end OMA.S_mo_140819
