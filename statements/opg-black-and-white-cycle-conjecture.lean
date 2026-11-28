import Mathlib

/-!
# Black and White Cycle Conjecture

Source: https://www.openproblemgarden.org/op/black_and_white_cycle_conjecture
(posted by Arthur Hoffmann-Ostenhof, September 2026; the bibliography on the page is empty).
Credit: @Mapika

The source: let `G` be a cubic graph with a nowhere-zero 4-flow. Colour an edge `e` black if
`G - e` does not have a nowhere-zero 4-flow, and white if `G - e` has one. Then `G` contains a
white cycle but not a black cycle. Here a cycle is a connected 2-regular graph, and a cycle is
black (white) if each of its edges is black (white).

This conjecture strengthens the 3-edge-coloring conjecture of the same author (the related
problem on the source page, stated here as `statements/opg-3-edge-coloring-conjecture.lean`):
a white cycle contains a white edge. No upstream formal-conjectures declaration states it.

Conventions, chosen to agree with the merged statement of the 3-edge-coloring conjecture:
* Graphs are finite multigraphs: a finite vertex type `V`, a finite edge type `E`, and for
  each edge `e` a tail `src e` and a head `tgt e`. The orientation is only a reference
  orientation (reversing an edge negates its flow value). Parallel edges are allowed, as is
  usual in flow theory and as the author's setting requires (the 3-edge-coloring conjecture
  excludes `|V(G)| ≤ 2`, which only matters for multigraphs, and the cubic graph
  homeomorphic to `K₄ - e` is the theta multigraph). Loops are allowed too; this changes
  nothing, because a cubic graph with a loop has a bridge and so no nowhere-zero flow.
* Cubic: every vertex has degree 3, a loop counting twice.
* A nowhere-zero 4-flow is `f : E → ℤ` with `0 < |f e| < 4` on every edge and, at every
  vertex, total inflow equal to total outflow (equivalently, by Tutte, a nowhere-zero
  `ℤ/4`-flow).
* `G - e` is the multigraph on the same vertices with edge type `{d : E // d ≠ e}`.
* A cycle of `G` is given by its edge set `C`: `C` is nonempty, every vertex is incident with
  0 or 2 edges of `C` (a loop counting twice), and the subgraph formed by the edges of `C` is
  connected (any two vertices met by `C` are joined by a walk using edges of `C`). This is
  exactly a connected 2-regular subgraph, its vertices being the ends of its edges; digons
  (two parallel edges) are cycles.
* `G` is assumed to have at least one vertex, the usual convention that a graph is nonempty.
  Without it the empty graph, which is vacuously cubic and has the empty nowhere-zero
  4-flow but no cycle at all, would be a trivial counterexample. Disconnected graphs are
  allowed, as in the source.
-/

namespace OMA.S_opg_black_and_white_cycle_conjecture

/-- Number of edge ends at `v` among the edges in `C` (a loop at `v` counts twice). -/
def degIn {V E : Type*} [DecidableEq V] (src tgt : E → V) (C : Finset E) (v : V) : ℕ :=
  (C.filter fun e => src e = v).card + (C.filter fun e => tgt e = v).card

/-- Conservation of `f` at every vertex of the multigraph `(V, E, src, tgt)`. -/
def IsConservative {V E : Type*} [Fintype E] [DecidableEq V] (src tgt : E → V)
    (f : E → ℤ) : Prop :=
  ∀ v, ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), f e =
    ∑ e ∈ Finset.univ.filter (fun e => src e = v), f e

/-- The multigraph `(V, E, src, tgt)` has a nowhere-zero 4-flow. -/
def HasNZ4Flow {V E : Type*} [Fintype E] [DecidableEq V] (src tgt : E → V) : Prop :=
  ∃ f : E → ℤ, (∀ d, 0 < |f d| ∧ |f d| < 4) ∧ IsConservative src tgt f

/-- The edge `e` is white: `G - e`, the multigraph with the edge `e` deleted, has a nowhere-zero
4-flow. An edge that is not white is black. -/
def IsWhite {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V] (src tgt : E → V)
    (e : E) : Prop :=
  HasNZ4Flow (fun d : {d : E // d ≠ e} => src d.1) (fun d : {d : E // d ≠ e} => tgt d.1)

/-- The edge set `C` is (the edge set of) a cycle: a nonempty, connected, 2-regular subgraph. -/
def IsCycle {V E : Type*} [DecidableEq V] (src tgt : E → V) (C : Finset E) : Prop :=
  C.Nonempty ∧ (∀ v, degIn src tgt C v = 0 ∨ degIn src tgt C v = 2) ∧
    ∀ u w, 0 < degIn src tgt C u → 0 < degIn src tgt C w →
      (SimpleGraph.fromRel fun a b => ∃ e ∈ C, src e = a ∧ tgt e = b).Reachable u w

/-- **Black and White Cycle Conjecture (Hoffmann-Ostenhof).** Let `G` be a finite nonempty cubic
multigraph with a nowhere-zero 4-flow. Then `G` has a cycle all of whose edges are white, and no
cycle all of whose edges are black. -/
theorem main : ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (src tgt : E → V), Nonempty V →
    (∀ v : V, degIn src tgt Finset.univ v = 3) → HasNZ4Flow src tgt →
      (∃ C : Finset E, IsCycle src tgt C ∧ ∀ e ∈ C, IsWhite src tgt e) ∧
        ¬ ∃ C : Finset E, IsCycle src tgt C ∧ ∀ e ∈ C, ¬ IsWhite src tgt e := by
  sorry

end OMA.S_opg_black_and_white_cycle_conjecture
