import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Borodin's conjecture on degenerate colorings of planar graphs

Open Problem Garden:
https://www.openproblemgarden.org/op/degenerate_colorings_of_planar_graphs

O. V. Borodin, *A proof of B. Grünbaum's conjecture on the acyclic 5-colorability of planar
graphs*, Dokl. Akad. Nauk SSSR 231 (1976), 18–20.
-/

namespace OMA.S_opg_degenerate_colorings_of_planar_graphs

/-- Each edge is represented once, with its smaller vertex first. -/
def Edge {n : ℕ} (G : SimpleGraph (Fin n)) :=
  { e : Fin n × Fin n // e.1 < e.2 ∧ G.Adj e.1 e.2 }

/-- A planar drawing places vertices at distinct points and represents each edge by a simple arc.
Arc interiors are disjoint and contain no drawn vertex. -/
def Planar {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ pos : Fin n → ℝ × ℝ, Function.Injective pos ∧
    ∃ arc : Edge G → ℝ → ℝ × ℝ,
      (∀ e, ContinuousOn (arc e) (Set.Icc 0 1) ∧ Set.InjOn (arc e) (Set.Icc 0 1) ∧
        arc e 0 = pos e.val.1 ∧ arc e 1 = pos e.val.2) ∧
      (∀ e v, pos v ∉ arc e '' Set.Ioo 0 1) ∧
      (∀ e f, e ≠ f → Disjoint (arc e '' Set.Ioo 0 1) (arc f '' Set.Ioo 0 1))

open scoped Classical in
/-- The graph induced by `U` is `r`-degenerate if every nonempty vertex subset of `U` has
a vertex with at most `r` neighbors in that subset. -/
def DegenerateOn {n : ℕ} (G : SimpleGraph (Fin n)) (U : Set (Fin n)) (r : ℕ) : Prop :=
  ∀ T : Finset (Fin n), (∀ v ∈ T, v ∈ U) → T.Nonempty →
    ∃ v ∈ T, (T.filter (G.Adj v)).card ≤ r

/-- Every finite simple planar graph has a proper five-coloring such that any union of
`k` color classes induces a `(k - 1)`-degenerate graph for `1 ≤ k ≤ 4`. -/
theorem main :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), Planar G →
      ∃ C : G.Coloring (Fin 5), ∀ K : Finset (Fin 5), 1 ≤ K.card → K.card ≤ 4 →
        DegenerateOn G {v | C v ∈ K} (K.card - 1) := by
  sorry

end OMA.S_opg_degenerate_colorings_of_planar_graphs
