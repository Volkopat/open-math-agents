import OMAStatements.S_mo_76624
import Mathlib

namespace OMA.S_mo_76624
open MeasureTheory Filter Topology

lemma null_pt (t : ℝ) : (volume : Measure unitInterval) {ω : unitInterval | (ω : ℝ) = t} = 0 := by
  have : {ω : unitInterval | (ω : ℝ) = t} = Subtype.val ⁻¹' {t} := rfl
  rw [this]
  rw [show (volume : Measure unitInterval) = (volume : Measure ℝ).comap Subtype.val from rfl]
  rw [(MeasurableEmbedding.subtype_coe (measurableSet_Icc (a := (0:ℝ)) (b := 1))).comap_apply]
  have : Subtype.val '' (Subtype.val ⁻¹' {t} : Set unitInterval) ⊆ {t} := by
    rintro _ ⟨x, hx, rfl⟩; exact hx
  exact measure_mono_null this (by simp)

end OMA.S_mo_76624

open MeasureTheory Filter Topology in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_76624.main) := by
  intro h
  have key := h unitInterval (volume : Measure unitInterval) 1
    (fun _ t ω => if (ω : ℝ) = t then 1 else 0) one_pos
    (fun n t => Measurable.ite (measurableSet_eq_fun measurable_subtype_coe measurable_const) measurable_const measurable_const)
    (by
      have : ∀ n : ℕ, (⨆ t ∈ Set.Icc (0:ℝ) 1, ∫⁻ ω, ENNReal.ofReal |(if (ω : ℝ) = t then (1:ℝ) else 0)| ∂(volume : Measure unitInterval)) = 0 := by
        intro n
        refine le_antisymm (iSup₂_le fun t _ => ?_) bot_le
        have h0 : (fun ω : unitInterval => ENNReal.ofReal |(if (ω : ℝ) = t then (1:ℝ) else 0)|) =ᵐ[volume] 0 := by
          have h1 := OMA.S_mo_76624.null_pt t
          have h2 : ∀ᵐ ω : unitInterval ∂(volume : Measure unitInterval), (ω : ℝ) ≠ t := by
            rw [ae_iff]; simpa using h1
          filter_upwards [h2] with ω hω
          simp [hω]
        rw [lintegral_congr_ae h0]; simp
      exact (tendsto_const_nhds (x := (0:ENNReal))).congr (fun n : ℕ => (this n).symm))
  have hge : ∀ _n : ℕ, (1 : ENNReal) ≤ ∫⁻ ω : unitInterval, ⨆ t ∈ Set.Icc (0:ℝ) 1, ENNReal.ofReal |(if (ω : ℝ) = t then (1:ℝ) else 0)| ∂(volume : Measure unitInterval) := by
    intro _n
    calc (1 : ENNReal) = ∫⁻ ω : unitInterval, 1 ∂(volume : Measure unitInterval) := by simp
      _ ≤ _ := by
        apply lintegral_mono
        intro ω
        refine le_iSup₂_of_le (ω : ℝ) ω.2 ?_
        simp
  have := ge_of_tendsto key (Filter.Eventually.of_forall hge)
  simp at this
