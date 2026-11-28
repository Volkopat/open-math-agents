import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1
import Mathlib

/-! Kostochka's total-coloring proof splits into the six-color theorem in Section 3,
the reduction to regular matched multigraphs in Section 6, and the seven-color
theorem for those multigraphs in Sections 4 and 5. The multiplicity of an edge
is a natural number. Each color set for an adjacent pair colors its parallel copies. -/

namespace OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1
open SimpleGraph

/-- A finite simple graph of maximum degree four admits a six-total-coloring. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.maxDegree = 4 → G.TotalColorable 6

/-- Any counterexample of maximum degree five yields a 5-regular loopless multigraph
whose support has a perfect matching and which also has no seven-total-coloring. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.maxDegree = 5 → ¬ G.TotalColorable 7 →
    ∃ (W : Type) (_ : Fintype W) (A : SimpleGraph W) (mult : W → W → ℕ),
      (∀ x y, mult x y = mult y x) ∧ (∀ x, mult x x = 0) ∧
      (∀ x, ∑ y, mult x y = 5) ∧ (∀ x y, A.Adj x y ↔ 0 < mult x y) ∧
      (∃ M : A.Subgraph, M.IsPerfectMatching) ∧
      ¬ ∃ (vc : W → Fin 7) (ec : W → W → Finset (Fin 7)),
        (∀ x y, ec x y = ec y x) ∧ (∀ x y, (ec x y).card = mult x y) ∧
        (∀ x y, A.Adj x y → vc x ≠ vc y) ∧ (∀ x y, vc x ∉ ec x y) ∧
        (∀ x y z, y ≠ z → Disjoint (ec x y) (ec x z))

/-- Every 5-regular loopless multigraph whose support has a perfect matching
has a seven-total-coloring. Distinct parallel edges receive distinct colors. -/
def H3 : Prop :=
  ∀ (W : Type) [Fintype W] (A : SimpleGraph W) (mult : W → W → ℕ),
    (∀ x y, mult x y = mult y x) → (∀ x, mult x x = 0) →
    (∀ x, ∑ y, mult x y = 5) → (∀ x y, A.Adj x y ↔ 0 < mult x y) →
    (∃ M : A.Subgraph, M.IsPerfectMatching) →
    ∃ (vc : W → Fin 7) (ec : W → W → Finset (Fin 7)),
        (∀ x y, ec x y = ec y x) ∧ (∀ x y, (ec x y).card = mult x y) ∧
        (∀ x y, A.Adj x y → vc x ≠ vc y) ∧ (∀ x y, vc x ∉ ec x y) ∧
        (∀ x y z, y ≠ z → Disjoint (ec x y) (ec x z))

theorem main : H1 → H2 → H3 → OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1.H2 := by
  intro four reduce regular V _ _ G _ degree
  rcases degree with h | h
  · rw [h]
    exact Nat.sInf_le (four G h)
  · rw [h]
    apply Nat.sInf_le
    by_contra no
    obtain ⟨W,t,A,mult,symm,loops,deg,supp,matching,bad⟩ := reduce G h no
    exact bad (@regular W t A mult symm loops deg supp matching)

end OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1
