import OMAReductions.R_OeisA111291_colton_conjecture_R1

-- Reduction OeisA111291.colton_conjecture.R1.H4.R1 of step OeisA111291.colton_conjecture.R1.H4
-- Credit: @AaronRai123

namespace OMA.R_OeisA111291_colton_conjecture_R1_H4_R1

def H1 : Prop :=
  ∀ x : ℝ, 5393 ≤ x →
    x / (Real.log x - 1) ≤ (⌊x⌋₊.primeCounting : ℝ)

def H2 : Prop :=
  ∀ x : ℝ, 60184 ≤ x →
    (⌊x⌋₊.primeCounting : ℝ) ≤ x / (Real.log x - 11 / 10)

theorem main : H1 → H2 → OMA.R_OeisA111291_colton_conjecture_R1.H4 := by
  intro h₁ h₂
  exact ⟨h₁, h₂⟩

end OMA.R_OeisA111291_colton_conjecture_R1_H4_R1
