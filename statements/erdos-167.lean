import Mathlib

/-!
# Erdős Problem 167

Source: https://www.erdosproblems.com/167
Credit: @Ciphore

Tuza's problem comparing the size of a largest edge-disjoint triangle packing with the
smallest edge set meeting every triangle.
-/

namespace OMA.S_erdos_167

/-- A family of vertex-disjointly represented triangles whose pairwise intersections have
at most one vertex, equivalently whose triangles are edge-disjoint. -/
def IsEdgeDisjointTrianglePacking {V : Type*} (G : SimpleGraph V) [DecidableEq V]
    (T : Finset (Finset V)) : Prop :=
  (∀ t ∈ T, G.IsNClique 3 t) ∧ ∀ t ∈ T, ∀ u ∈ T, t ≠ u → (t ∩ u).card ≤ 1

/-- If a finite graph has no edge-disjoint triangle packing of more than `k` triangles,
then at most `2k` edges can be removed to make it triangle-free. -/
theorem main : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ),
    (∀ T : Finset (Finset V), IsEdgeDisjointTrianglePacking G T → T.card ≤ k) →
    ∃ F : Finset (Sym2 V), F.card ≤ 2 * k ∧
      (∀ e ∈ F, e ∈ G.edgeSet) ∧ (G.deleteEdges (F : Set (Sym2 V))).CliqueFree 3 := by
  sorry

end OMA.S_erdos_167
