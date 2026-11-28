import OMAReductions.R_Erdos30_erdos_30_R3

-- Reduction Erdos30.erdos_30.R3.H1.R1 of step Erdos30.erdos_30.R3.H1.
-- Credit: @PetrouilFan
-- H1 is the strictly stronger exact doubling inequality (no subpolynomial slack).
-- H2 is the proved transfer from the exact form to the target slack form.

namespace OMA.R_Erdos30_erdos_30_R3_H1_R1

def H1 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ m : ℕ, K ≤ m →
    2 * (Erdos30.h (m ^ 2) : ℝ) ≤ Erdos30.h ((2 * m) ^ 2)

def H2 : Prop :=
  (∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ m : ℕ, K ≤ m →
    2 * (Erdos30.h (m ^ 2) : ℝ) ≤ Erdos30.h ((2 * m) ^ 2)) →
  ∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ m : ℕ, K ≤ m →
    2 * (Erdos30.h (m ^ 2) : ℝ) ≤ Erdos30.h ((2 * m) ^ 2) + (m : ℝ) ^ δ

lemma upstream_bridge : H2 := by
  intro h δ hδ
  obtain ⟨K, hK⟩ := h δ hδ
  refine ⟨K, fun m hm ↦ ?_⟩
  have hnonneg : 0 ≤ (m : ℝ) ^ δ := Real.rpow_nonneg (by positivity) δ
  linarith [hK m hm]

theorem main : H1 → H2 → OMA.R_Erdos30_erdos_30_R3.H1 := by
  intro h1 h2
  exact h2 h1

end OMA.R_Erdos30_erdos_30_R3_H1_R1
