import OMAReductions.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1
import Mathlib

/-!
The rigid jump case can be restricted further to minimisers with short
supporting segments. The support estimate also gives an inverse-square gap
from squared length four when the diameter exceeds two.
-/

open EuclideanGeometry Filter Finset Erdos103
open scoped Classical ENNReal

namespace OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1_H2_R1

private theorem congruent_of_common_source {A X Y : Finset ℝ²}
    (hX : Congruent A X) (hY : Congruent A Y) : Congruent X Y := by
  obtain ⟨f, hf⟩ := hX
  obtain ⟨g, hg⟩ := hY
  have hfInv : f.symm '' (X : Set ℝ²) = A := by
    rw [← hf, Set.image_image]
    simp
  refine ⟨f.symm.trans g, ?_⟩
  change ((g : ℝ² → ℝ²) ∘ (f.symm : ℝ² → ℝ²)) '' (X : Set ℝ²) = Y
  rw [Set.image_comp, hfInv, hg]

private theorem finite_of_unique {n : ℕ} {A : Finset ℝ²}
    (hUnique : ∀ B, IsMinimiser n B → Congruent A B) : Erdos103.h n ≠ ⊤ := by
  have hOne : Erdos103.h n ≤ 1 := by
    unfold Erdos103.h
    refine iSup_le fun S => iSup_le fun hS => ?_
    have hCard : S.card ≤ 1 := card_le_one.mpr (fun X hXS Y hYS => by
      by_contra hXY
      exact hS.2 X hXS Y hYS hXY
        (congruent_of_common_source (hUnique X (hS.1 X hXS)) (hUnique Y (hS.1 Y hYS))))
    exact_mod_cast hCard
  intro hTop
  rw [hTop] at hOne
  simp at hOne

/-- The support-line bound for a minimiser when there are only finitely many
optimal congruence classes. -/
def H1 : Prop :=
  ∀ (n : ℕ) (A : Finset ℝ²), 5 ≤ n → IsMinimiser n A → Erdos103.h n ≠ ⊤ →
    ∀ a ∈ A, ∀ b ∈ A, ∀ u : ℝ², ‖u‖ = 1 →
      (∀ q ∈ A, inner ℝ q u ≤ inner ℝ a u) → inner ℝ b u = inner ℝ a u →
      dist a b < 2 ∧ (2 < Metric.diam (A : Set ℝ²) →
        dist a b ^ 2 + ((Metric.diam (A : Set ℝ²))⁻¹) ^ 2 ≤ 4)

/-- The rigid jump case with the additional support-line bounds on the
given minimiser. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², IsMinimiser n A →
    (∀ B ∈ separatedSets (n + 1),
      Metric.diam (A : Set ℝ²) < Metric.diam (B : Set ℝ²)) →
    (∀ X : Finset ℝ², IsMinimiser n X → ∀ p ∈ X, ∀ v : ℝ², v ≠ 0 →
      (∃ q ∈ X, dist p q = 1 ∧ 0 < inner ℝ v (q - p)) ∨
      (∃ r ∈ X, dist p r = Metric.diam (X : Set ℝ²) ∧ inner ℝ v (r - p) ≤ 0)) →
    (∀ a ∈ A, ∀ b ∈ A, ∀ u : ℝ², ‖u‖ = 1 →
      (∀ q ∈ A, inner ℝ q u ≤ inner ℝ a u) → inner ℝ b u = inner ℝ a u →
      dist a b < 2 ∧ (2 < Metric.diam (A : Set ℝ²) →
        dist a b ^ 2 + ((Metric.diam (A : Set ℝ²))⁻¹) ^ 2 ≤ 4)) →
    ∃ B : Finset ℝ², IsMinimiser n B ∧ ¬ Congruent A B

theorem main : H1 → H2 → OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1.H2 := by
  intro hSupport hResidual
  unfold H2 at hResidual
  unfold OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1.H2
  filter_upwards [hResidual, eventually_ge_atTop (5 : ℕ)] with n hN hFive
  intro A hA hJump hBlocked
  by_contra hNo
  have hUnique (B : Finset ℝ²) (hB : IsMinimiser n B) : Congruent A B := by
    by_contra hNotCongruent
    exact hNo ⟨B, hB, hNotCongruent⟩
  have hFinite := finite_of_unique hUnique
  exact hNo (hN A hA hJump hBlocked (hSupport n A hFive hA hFinite))

end OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1_H2_R1
