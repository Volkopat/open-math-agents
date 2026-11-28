import Mathlib

/-!
# Mapping planar graphs to odd cycles

Source: https://www.openproblemgarden.org/op/mapping_planar_graphs_to_odd_cycles
Credit: @pyaf

Conjecture: Every planar graph of girth `≥ 4k` has a homomorphism to `C_{2k+1}`.

Conventions:
- `k` ranges over positive integers (for `k = 0`, `C_1` is not a graph). The case `k = 1` is
  Grötzsch's theorem.
- Graphs are finite simple graphs, given as a `SimpleGraph` on a finite vertex type `V`.
- The girth is Mathlib's `egirth`, the length of a shortest cycle, `⊤` for a forest; so a
  forest has girth `≥ 4k` for every `k`.
- `C_{2k+1}` is Mathlib's `cycleGraph (2 * k + 1)`; a homomorphism is `G →g H`.
- A graph is planar if it has a plane drawing: distinct points of `ℝ²` for the vertices and,
  for every edge, an arc (a continuous injective image of `[0, 1]`) joining its endpoints,
  whose interior meets no vertex and no other edge's interior (as in the merged statement
  `wp-apex-graph`).
-/

namespace OMA.S_opg_mapping_planar_graphs_to_odd_cycles

open SimpleGraph

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

theorem main :
    ∀ (k : ℕ), 1 ≤ k → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      IsPlanar G → ((4 * k : ℕ) : ℕ∞) ≤ G.egirth → Nonempty (G →g cycleGraph (2 * k + 1)) := by
  sorry

end OMA.S_opg_mapping_planar_graphs_to_odd_cycles
