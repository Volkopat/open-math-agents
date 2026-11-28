import OMAStatements.S_opg_triangle_packing_vs_triangle_edge_transversal
import Mathlib

/-! Tuza's conjecture: a finite graph with at most k pairwise edge-disjoint triangles has a set of
at most 2k edges meeting every triangle. The cases k = 0 and k = 1 are classical (Tuza 1990):
for k = 1 any two triangles share an edge, and once two distinct triangles abc and acd exist,
every other triangle shares two vertices with both, hence contains a, c or b, d, so the two
edges ac and bd meet all triangles (a single triangle is met by one edge). H1 is Tuza's
conjecture for k at most 1, for every finite graph. The cases k at least 2 (H2) remain open in
general. -/

namespace OMA.R_opg_triangle_packing_vs_triangle_edge_transversal_R1

/-- Tuza's conjecture for graphs with at most one edge-disjoint triangle (k at most 1). -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ), k ≤ 1 →
    (∀ T : Finset (Finset V), (∀ t ∈ T, G.IsNClique 3 t) →
        (∀ t ∈ T, ∀ s ∈ T, t ≠ s → (t ∩ s).card ≤ 1) → T.card ≤ k) →
    ∃ S : Finset (Sym2 V), S.card ≤ 2 * k ∧
      (G.deleteEdges (S : Set (Sym2 V))).CliqueFree 3

/-- The open part: Tuza's conjecture for k at least 2. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ), 2 ≤ k →
    (∀ T : Finset (Finset V), (∀ t ∈ T, G.IsNClique 3 t) →
        (∀ t ∈ T, ∀ s ∈ T, t ≠ s → (t ∩ s).card ≤ 1) → T.card ≤ k) →
    ∃ S : Finset (Sym2 V), S.card ≤ 2 * k ∧
      (G.deleteEdges (S : Set (Sym2 V))).CliqueFree 3

theorem main : H1 → H2 →
    type_of% @OMA.S_opg_triangle_packing_vs_triangle_edge_transversal.main := by
  intro h1 h2 V _ _ G k hk
  rcases Nat.lt_or_ge k 2 with h | h
  · exact h1 V G k (by omega) hk
  · exact h2 V G k h hk

end OMA.R_opg_triangle_packing_vs_triangle_edge_transversal_R1
