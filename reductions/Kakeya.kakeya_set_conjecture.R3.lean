import FormalConjectures.Wikipedia.Kakeya
import Mathlib
-- H1 and H2 restate kakeya_maximal and kakeyaMaximal_implies_kakeya of OpenAI/math 3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0) with their definitions unfolded.
open MeasureTheory
open scoped ENNReal

namespace OMA.R_Kakeya_kakeya_set_conjecture_R3

def H1 : Prop := ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ f : EuclideanSpace ℝ (Fin n) → ℂ, MemLp f n →
    MemLp (fun ω : EuclideanSpace ℝ (Fin n) => ⨆ x : EuclideanSpace ℝ (Fin n),
        (∫⁻ y in ⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), Metric.ball (x + t • ω) δ, ‖f y‖ₑ) /
          volume (⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), Metric.ball (x + t • ω) δ)) n
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.map Subtype.val) ∧
    eLpNorm (fun ω : EuclideanSpace ℝ (Fin n) => ⨆ x : EuclideanSpace ℝ (Fin n),
        (∫⁻ y in ⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), Metric.ball (x + t • ω) δ, ‖f y‖ₑ) /
          volume (⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), Metric.ball (x + t • ω) δ)) n
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.map Subtype.val) ≤
      ENNReal.ofReal (C * δ ^ (-ε)) * eLpNorm f n volume

def H2 : Prop := (∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ f : EuclideanSpace ℝ (Fin n) → ℂ, MemLp f n →
    MemLp (fun ω : EuclideanSpace ℝ (Fin n) => ⨆ x : EuclideanSpace ℝ (Fin n),
        (∫⁻ y in ⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), Metric.ball (x + t • ω) δ, ‖f y‖ₑ) /
          volume (⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), Metric.ball (x + t • ω) δ)) n
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.map Subtype.val) ∧
    eLpNorm (fun ω : EuclideanSpace ℝ (Fin n) => ⨆ x : EuclideanSpace ℝ (Fin n),
        (∫⁻ y in ⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), Metric.ball (x + t • ω) δ, ‖f y‖ₑ) /
          volume (⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), Metric.ball (x + t • ω) δ)) n
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.map Subtype.val) ≤
      ENNReal.ofReal (C * δ ^ (-ε)) * eLpNorm f n volume) →
    ∀ n : ℕ, 2 ≤ n → ∀ F : Set (EuclideanSpace ℝ (Fin n)),
      (∀ ω : EuclideanSpace ℝ (Fin n), ‖ω‖ = 1 →
        ∃ x, {y | ∃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), y = x + t • ω} ⊆ F) →
      dimH F = n

theorem main : H1 → H2 → type_of% @Kakeya.kakeya_set_conjecture := by
  intro h1 h2 n hn S hS
  rcases Nat.lt_or_ge n 2 with hlt | h2n
  · obtain rfl : n = 1 := by omega
    apply le_antisymm
    · simpa [Real.dimH_univ_eq_finrank] using dimH_mono (Set.subset_univ S)
    · obtain ⟨a, ha⟩ := hS (EuclideanSpace.single 0 (1 : ℝ)) (by simp)
      have hne : a ≠ a + EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
        intro h
        have h0 : (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) = 0 := by
          simpa using h.symm
        have := congrArg (fun z : EuclideanSpace ℝ (Fin 1) => z 0) h0
        simp at this
      have hseg := Real.dimH_segment hne
      rw [← affineSegment_eq_segment] at hseg
      calc ((1 : ℕ) : ℝ≥0∞)
          = dimH (affineSegment ℝ a (a + EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) := by
            rw [hseg]; simp
        _ ≤ dimH S := dimH_mono ha
  · refine h2 h1 n h2n S ?_
    intro ω hω
    obtain ⟨a, ha⟩ := hS ω hω
    refine ⟨a + (1 / 2 : ℝ) • ω, ?_⟩
    rintro y ⟨t, ⟨ht0, ht1⟩, rfl⟩
    apply ha
    refine ⟨t + 1 / 2, ⟨by linarith, by linarith⟩, ?_⟩
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_left]
    module

end OMA.R_Kakeya_kakeya_set_conjecture_R3
