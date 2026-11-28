import Mathlib

/-!
# Every prism over a 3-connected planar graph is hamiltonian

Open Problem Garden:
https://www.openproblemgarden.org/op/every_prism_over_a_3_connected_planar_graph_is_hamiltonian
Conjecture (Kaiser, Král', Rosenfeld, Ryjáček, Voss): if `G` is a 3-connected planar graph,
then the prism `G □ K₂` has a Hamilton cycle.

Conventions. Graphs are finite simple graphs. Planarity is given by a straight-line drawing
in `ℝ²` (vertices at distinct points, two distinct edge segments meet only in common endpoints); by
Fáry's theorem this is equivalent to planarity. `G` is 3-connected when it has at least four
vertices and stays connected after deleting any set of at most two vertices. The prism is
Mathlib's box product `G □ ⊤` with the complete graph on `Fin 2`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_opg_every_prism_over_a_3_connected_planar_graph_is_hamiltonian

open SimpleGraph

/-- A straight-line plane drawing of `G`. -/
def HasStraightLineDrawing {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ pos : V → EuclideanSpace ℝ (Fin 2), Function.Injective pos ∧
    ∀ u v x y : V, G.Adj u v → G.Adj x y → s(u, v) ≠ s(x, y) →
      segment ℝ (pos u) (pos v) ∩ segment ℝ (pos x) (pos y) ⊆
        pos '' (({u, v} : Set V) ∩ {x, y})

/-- `G` is 3-connected: at least four vertices, and deleting at most two vertices leaves a
connected graph. -/
def ThreeConnected {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card ≤ 2 → (G.induce ((S : Set V)ᶜ)).Connected

theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ThreeConnected G → HasStraightLineDrawing G →
      (G □ (⊤ : SimpleGraph (Fin 2))).IsHamiltonian := by
  sorry

end OMA.S_opg_every_prism_over_a_3_connected_planar_graph_is_hamiltonian
