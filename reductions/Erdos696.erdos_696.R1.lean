import FormalConjectures.ErdosProblems.«696»

open Erdos696

-- Reduction Erdos696.erdos_696.R1 of Erdős Problem 696
-- Credit: @cks442-star
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos696_erdos_696_R1

def H1 : Prop :=
  ∃ M δ : ℝ, 0 < δ ∧
    {n : ℕ | (h n : ℝ) > 0 ∧ (H n : ℝ) / (h n : ℝ) ≤ M}.HasDensity δ

def H2 : Prop :=
  ∀ (S T : Set ℕ) (δ : ℝ), 0 < δ → T.HasDensity δ → Disjoint S T →
    ¬ S.HasDensity 1

theorem main : H1 → H2 → type_of% @Erdos696.erdos_696 := by
  intro hBound hDensity
  intro hAll
  obtain ⟨M, δ, hδ, hT⟩ := hBound
  let S : Set ℕ := {n | (h n : ℝ) > 0 ∧ (H n : ℝ) / (h n : ℝ) > M}
  let T : Set ℕ := {n | (h n : ℝ) > 0 ∧ (H n : ℝ) / (h n : ℝ) ≤ M}
  have hDisjoint : Disjoint S T := by
    rw [Set.disjoint_left]
    intro n hnS hnT
    exact (not_le_of_gt hnS.2) hnT.2
  have hS : S.HasDensity 1 := by simpa [S] using hAll M
  exact hDensity S T δ hδ hT hDisjoint hS

end OMA.R_Erdos696_erdos_696_R1
