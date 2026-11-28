import Mathlib

/-!
# Every 4-connected toroidal graph has a Hamilton cycle

Source: https://www.openproblemgarden.org/op/every_4_connected_toroidal_graph_has_a_hamilton_cycle
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Grünbaum, Nash-Williams): every 4-connected toroidal graph has a Hamilton cycle.

## Encoding

* Graphs are finite simple graphs (`SimpleGraph` on a `Fintype`).
* `G` is `k`-vertex-connected if it has more than `k` vertices and `G - X` is connected for
  every set `X` of fewer than `k` vertices.
* The torus is `(ℝ/ℤ)²`, i.e. `AddCircle (1 : ℝ) × AddCircle (1 : ℝ)`. A graph is toroidal if
  it embeds in the torus: distinct points for the vertices and, for every edge, an arc (a
  continuous injective image of `[0, 1]`) joining its endpoints, whose interior meets no vertex
  and no other edge's interior. (Planar graphs are toroidal.)
* Hamilton cycle: Mathlib's `SimpleGraph.IsHamiltonian`.
-/

namespace OMA.S_opg_every_4_connected_toroidal_graph_has_a_hamilton_cycle

open SimpleGraph

/-- The torus `(ℝ/ℤ)²`. -/
abbrev Torus : Type := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- `G` is `k`-vertex-connected. -/
def IsKVertexConnected {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ X : Finset V, X.card < k → (G.induce ((X : Set V)ᶜ)).Connected

/-- `G` has an embedding in the torus. -/
def IsToroidal {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ (pos : V → Torus) (arc : G.edgeSet → C(unitInterval, Torus)),
    Function.Injective pos ∧
    (∀ e, Function.Injective (arc e)) ∧
    (∀ e, Sym2.map pos e.1 = s(arc e 0, arc e 1)) ∧
    (∀ e (t : unitInterval), (t : ℝ) ∈ Set.Ioo 0 1 → ∀ v, arc e t ≠ pos v) ∧
    (∀ e f, e ≠ f → ∀ s t : unitInterval, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      arc e s ≠ arc f t)

theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsKVertexConnected G 4 → IsToroidal G → G.IsHamiltonian := by
  sorry

end OMA.S_opg_every_4_connected_toroidal_graph_has_a_hamilton_cycle
