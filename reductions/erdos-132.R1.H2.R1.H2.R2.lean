import OMAReductions.R_erdos_132_R1_H2_R1

/-!
For sites on a common circle, each pinned distance meets that circle at most twice.
Adding the center affects only the shared radius and loses at most one rare distance.
This removes these configurations from the residual rare-distance question.

Erdős problem 132, https://www.erdosproblems.com/132.
-/

namespace OMA.R_erdos_132_R1_H2_R1_H2_R2

open Finset OMA.S_erdos_132
open scoped InnerProductSpace

/-- Points on a circle, with its center also permitted. -/
def H1 : Prop :=
  ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))) (o : EuclideanSpace ℝ (Fin 2)) (r : ℝ),
    (∀ x ∈ A, x = o ∨ dist x o = r) → ∀ k : ℕ,
    2*k+3 ≤ A.card → k ≤ (rareDistances A).card

/-- The residual configuration lies on no circle even after discarding its center. -/
def H2 : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ A.card →
    (A.offDiag.image (fun p => dist p.1 p.2)).card+2 ≤ A.card/2+k →
    (∀ (o u v : EuclideanSpace ℝ (Fin 2)), LinearIndependent ℝ ![u,v] → 0 ≤ ⟪u,v⟫_ℝ →
      ∀ x y : ℕ → ℝ, StrictMono x → StrictMono y → ∀ r s : ℕ,
      A ≠ (((range (r+1)) ×ˢ (range (s+1))).image (fun p => o + x p.1 • u + y p.2 • v))) →
    (∀ S ⊆ A.offDiag.image (fun p => dist p.1 p.2), 2*k ≤ S.card →
      2*k*(A.card+1) < (A.offDiag.filter (fun p => dist p.1 p.2 ∈ S)).card) →
    (¬ ∃ (o : EuclideanSpace ℝ (Fin 2)) (r : ℝ), ∀ x ∈ A, x = o ∨ dist x o = r) →
    k ≤ (rareDistances A).card

theorem main : H1 → H2 → OMA.R_erdos_132_R1_H2_R1.H2 := by
  classical
  intro circle residual k
  obtain ⟨N,hn⟩ := residual k
  refine ⟨max N (2*k+3), ?_⟩
  intro A hsize few nongrid dense
  by_cases normalized : ∃ (o : EuclideanSpace ℝ (Fin 2)) (r : ℝ), ∀ x ∈ A, x = o ∨ dist x o = r
  · obtain ⟨o,r,haround⟩ := normalized
    exact circle A o r haround k ((le_max_right _ _).trans hsize)
  · exact hn A ((le_max_left _ _).trans hsize) few nongrid dense normalized

end OMA.R_erdos_132_R1_H2_R1_H2_R2
