import Mathlib

/-!
# Imbalance conjecture

Source: https://mathoverflow.net/questions/426935 (CC BY-SA 4.0); posed by Sergiy Kozerenko on
27 August 2021, Lviv Scottish Book, Volume 3, page 92.

Let `G` be a finite simple undirected graph. The imbalance of an edge `e = uv` is
`imb(e) = |d(u) - d(v)|`, where `d` is the vertex degree; `M_G` is the multiset of all edge
imbalances. A multiset is graphic if it is the multiset of vertex degrees of some graph.
Imbalance Conjecture: if `imb(e) ≥ 1` for every edge `e` of `G`, then `M_G` is graphic.

Formalization notes:
* `G` is a simple graph on a finite type `V` (in `Type`); decidability is classical.
* `imb` is defined on `Sym2 V` as `Nat.dist (d u) (d v) = |d(u) - d(v)|`, and `M_G` is the image
  of the edge set under `imb`, as a multiset.
* "Graphic" means: equal to the degree multiset of a simple graph on some `Fin n` (so the witness
  graph has exactly one vertex per element of the multiset).
* Checked numerically: holds for all 3825 graphs with 2 to 6 labelled vertices in which every
  edge has imbalance at least 1 (graphicality tested with the Erdős–Gallai criterion).
-/

namespace OMA.S_mo_426935

open Classical

/-- The imbalance `|d(u) - d(v)|` of a pair `{u, v}`. -/
noncomputable def imb {V : Type} [Fintype V] (G : SimpleGraph V) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun u v => Nat.dist (G.degree u) (G.degree v), fun _ _ => Nat.dist_comm _ _⟩

/-- `M_G`: the multiset of the imbalances of the edges of `G`. -/
noncomputable def M {V : Type} [Fintype V] (G : SimpleGraph V) : Multiset ℕ :=
  G.edgeFinset.val.map (imb G)

/-- A multiset of naturals is graphic: it is the degree multiset of some simple graph. -/
def IsGraphic (D : Multiset ℕ) : Prop :=
  ∃ (n : ℕ) (H : SimpleGraph (Fin n)), (Finset.univ : Finset (Fin n)).val.map (fun v => H.degree v) = D

/-- If every edge of a finite simple graph has imbalance at least 1, its imbalance multiset is
graphic. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    (∀ e ∈ G.edgeSet, 1 ≤ imb G e) → IsGraphic (M G) := by
  sorry

end OMA.S_mo_426935
