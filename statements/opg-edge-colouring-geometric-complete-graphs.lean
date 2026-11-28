import Mathlib

/-!
# Edge-colouring geometric complete graphs

Source: https://www.openproblemgarden.org/op/edge_colouring_geometric_complete_graphs
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For a set `P` of `n` points in the plane, no three collinear, `K_P` is the complete geometric
graph (straight segments). Two distinct edges are *crossing* if they meet at a point interior
to both, *disjoint* if they do not meet. `A(n), B(n), C(n), D(n)` are the least numbers of
colours such that every `K_P` on `n` points has an edge colouring in which, respectively,
crossing / disjoint / non-disjoint / non-crossing edges get distinct colours.

The source asks for these values and records one conjecture per variant; `main` is their
conjunction:
* (A) `A(n) ≤ (1 - ε) n` for some `ε > 0`;
* (B) `B(n) ≤ (1 - ε) n` for some `ε > 0`;
* (C) `C(n) ∈ O(n log n)` (the weaker of the two Variant C conjectures);
* (D) `D(n) / n → ∞`.
Bounds "for some `ε`" and `O(·)` are read asymptotically (for all large `n`).
-/

namespace OMA.S_opg_edge_colouring_geometric_complete_graphs

open Filter

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The closed segment of an edge. -/
def seg (e : Sym2 Plane) : Set Plane :=
  Sym2.lift ⟨fun p q => segment ℝ p q, fun p q => segment_symm ℝ p q⟩ e

/-- The relative interior of the segment of an edge. -/
def oseg (e : Sym2 Plane) : Set Plane :=
  Sym2.lift ⟨fun p q => openSegment ℝ p q, fun p q => openSegment_symm ℝ p q⟩ e

/-- Edges of `K_P`. -/
def IsEdge (P : Finset Plane) (e : Sym2 Plane) : Prop := ¬ e.IsDiag ∧ ∀ p ∈ e, p ∈ P

/-- No three points of `P` are collinear. -/
def GeneralPosition (P : Finset Plane) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, p ≠ q → p ≠ r → q ≠ r → ¬ Collinear ℝ {p, q, r}

def Crossing (e f : Sym2 Plane) : Prop := (oseg e ∩ oseg f).Nonempty
def DisjointEdges (e f : Sym2 Plane) : Prop := seg e ∩ seg f = ∅

/-- Least number of colours for `K_P` when conflicting edges must get distinct colours. -/
noncomputable def chi (conflict : Sym2 Plane → Sym2 Plane → Prop) (P : Finset Plane) : ℕ :=
  sInf {c | ∃ col : Sym2 Plane → Fin c, ∀ e f, IsEdge P e → IsEdge P f → e ≠ f →
    conflict e f → col e ≠ col f}

/-- Least number of colours that works for every `K_P` on `n` points. -/
noncomputable def worst (conflict : Sym2 Plane → Sym2 Plane → Prop) (n : ℕ) : ℕ :=
  sSup {k | ∃ P : Finset Plane, P.card = n ∧ GeneralPosition P ∧ k = chi conflict P}

noncomputable def A (n : ℕ) : ℕ := worst Crossing n
noncomputable def B (n : ℕ) : ℕ := worst DisjointEdges n
noncomputable def C (n : ℕ) : ℕ := worst (fun e f => ¬ DisjointEdges e f) n
noncomputable def D (n : ℕ) : ℕ := worst (fun e f => ¬ Crossing e f) n

/-- The four conjectures of the source. -/
theorem main :
    (∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop, (A n : ℝ) ≤ (1 - ε) * n) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop, (B n : ℝ) ≤ (1 - ε) * n) ∧
    (∃ K : ℝ, ∀ᶠ n : ℕ in atTop, (C n : ℝ) ≤ K * n * Real.log n) ∧
    Tendsto (fun n : ℕ => (D n : ℝ) / n) atTop atTop := by
  sorry

end OMA.S_opg_edge_colouring_geometric_complete_graphs
