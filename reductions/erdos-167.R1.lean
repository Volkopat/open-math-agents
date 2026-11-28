import OMAStatements.S_erdos_167
import Mathlib

/-!
Reduction erdos-167.R1: Tuza's conjecture split by the packing number.

H1 is the classical case of all graphs with no two edge-disjoint triangles (packing number at
most 1): then at most 2 edges meet every triangle (Tuza 1981: either all triangles share an edge,
or they all lie on four vertices). This is a known case, not progress on the conjecture.
H2 is the open remainder: packing bound k at least 2.
-/

namespace OMA.R_erdos_167_R1

open OMA.S_erdos_167 (IsEdgeDisjointTrianglePacking)

/-- Tuza's bound for graphs without two edge-disjoint triangles (packing number at most 1). -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ), k ≤ 1 →
    (∀ T : Finset (Finset V), IsEdgeDisjointTrianglePacking G T → T.card ≤ k) →
    ∃ F : Finset (Sym2 V), F.card ≤ 2 * k ∧
      (∀ e ∈ F, e ∈ G.edgeSet) ∧ (G.deleteEdges (F : Set (Sym2 V))).CliqueFree 3

/-- The open remainder: Tuza's bound for packing bounds `k ≥ 2`. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ), 2 ≤ k →
    (∀ T : Finset (Finset V), IsEdgeDisjointTrianglePacking G T → T.card ≤ k) →
    ∃ F : Finset (Sym2 V), F.card ≤ 2 * k ∧
      (∀ e ∈ F, e ∈ G.edgeSet) ∧ (G.deleteEdges (F : Set (Sym2 V))).CliqueFree 3

theorem main : H1 → H2 → type_of% @OMA.S_erdos_167.main := by
  intro h1 h2 V _ _ G k hk
  rcases le_or_gt k 1 with h | h
  · exact h1 G k h hk
  · exact h2 G k h hk

end OMA.R_erdos_167_R1
