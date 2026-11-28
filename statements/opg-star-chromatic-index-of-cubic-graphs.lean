import Mathlib

/-!
# Star chromatic index of cubic graphs

Source: https://www.openproblemgarden.org/op/star_chromatic_index_of_cubic_graphs
Credit: @datdzrgb
-/

namespace OMA.S_opg_star_chromatic_index_of_cubic_graphs

def IsStarEdgeColoring {V E : Type*} (G : Graph V E) (col : G.edgeSet → Fin 6) : Prop :=
  (∀ e f : G.edgeSet, e ≠ f → (∃ v : V, G.Inc e.val v ∧ G.Inc f.val v) → col e ≠ col f) ∧
  (∀ (v : Fin 5 → V) (e : Fin 4 → G.edgeSet), Function.Injective v →
    (∀ i : Fin 4, G.IsLink (e i).val (v i.castSucc) (v i.succ)) →
    3 ≤ (Set.range (col ∘ e)).ncard) ∧
  (∀ (v : Fin 4 → V) (e : Fin 4 → G.edgeSet), Function.Injective v →
    (∀ i : Fin 4, G.IsLink (e i).val (v i) (v (i + 1))) →
    3 ≤ (Set.range (col ∘ e)).ncard)

/-- Every loopless subcubic graph, allowing parallel edges, admits a star edge coloring
with at most six colors. -/
theorem main :
    ∀ (n m : ℕ) (G : Graph (Fin n) (Fin m)), G.Loopless →
      (∀ v, (G.incidenceSet v).ncard ≤ 3) →
      ∃ col : G.edgeSet → Fin 6, IsStarEdgeColoring G col := by
  sorry

end OMA.S_opg_star_chromatic_index_of_cubic_graphs
