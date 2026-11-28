import Mathlib

/-!
# Domination in plane triangulations

Source: https://www.openproblemgarden.org/op/domination_in_plane_triangulations
Credit: @pyaf

Conjecture (Matheson, Tarjan): every sufficiently large plane triangulation `G` has a dominating
set of size `≤ (1/4) |V(G)|`.

Conventions:
- Graphs are finite simple graphs, given as a `SimpleGraph` on a finite vertex type `V`.
- A graph is planar if it has a plane drawing: distinct points of `ℝ²` for the vertices and,
  for every edge, an arc (a continuous injective image of `[0, 1]`) joining its endpoints,
  whose interior meets no vertex and no other edge's interior (`IsPlanar`, reused verbatim from
  `statements/wp-apex-graph.lean`).
- A plane triangulation is a simple plane graph in which every face is a triangle. For simple
  graphs on at least three vertices these are exactly the maximal planar graphs: planar, and
  adding any missing edge destroys planarity. Since the claim is only for sufficiently large
  graphs, triangulations are encoded as maximal planar graphs (`IsTriangulation`).
- `S` is a dominating set if every vertex lies in `S` or is adjacent to a vertex of `S`.
- "Sufficiently large" means: for all graphs with at least `N` vertices, for some fixed `N`.
  The bound `|S| ≤ |V(G)| / 4` is stated without division: `4 |S| ≤ |V(G)|`.
-/

namespace OMA.S_opg_domination_in_plane_triangulations

/-- `G` has a plane drawing: vertices at distinct points, edges as arcs joining their endpoints,
with arc interiors avoiding all vertices and the interiors of all other arcs. -/
def IsPlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (pos : V → ℝ × ℝ) (arc : G.edgeSet → C(unitInterval, ℝ × ℝ)),
    Function.Injective pos ∧
    (∀ e, Function.Injective (arc e)) ∧
    (∀ e, Sym2.map pos e.1 = s(arc e 0, arc e 1)) ∧
    (∀ e (t : unitInterval), (t : ℝ) ∈ Set.Ioo 0 1 → ∀ v, arc e t ≠ pos v) ∧
    (∀ e f, e ≠ f → ∀ s t : unitInterval, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      arc e s ≠ arc f t)

/-- `G` is a plane triangulation: planar, and adding any missing edge destroys planarity. -/
def IsTriangulation {V : Type} (G : SimpleGraph V) : Prop :=
  IsPlanar G ∧ ∀ u v, u ≠ v → ¬ G.Adj u v → ¬ IsPlanar (G ⊔ SimpleGraph.edge u v)

/-- `S` dominates `G`: every vertex is in `S` or has a neighbour in `S`. -/
def IsDominatingSet {V : Type} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v, v ∈ S ∨ ∃ u ∈ S, G.Adj u v

theorem main :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      N ≤ Fintype.card V → IsTriangulation G →
        ∃ S : Finset V, IsDominatingSet G S ∧ 4 * S.card ≤ Fintype.card V := by
  sorry

end OMA.S_opg_domination_in_plane_triangulations
