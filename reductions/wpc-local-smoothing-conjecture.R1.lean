import OMAStatements.S_wpc_local_smoothing_conjecture

/-! Quantitative estimate adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). Separate the integral measurability needed for Mathlib MemLp from the uniform Fourier estimate. -/
open MeasureTheory OMA.S_wpc_local_smoothing_conjecture
noncomputable section
namespace OMA.R_wpc_local_smoothing_conjecture_R1

def H1 : Prop :=
    ∀ n : ℕ, 2 ≤ n → ∀ p α : ℝ, 2 * (n : ℝ) / ((n : ℝ) - 1) ≤ p →
      ((n : ℝ) - 1) * (1 / 2 - 1 / p) - 1 / p < α →
      ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
        eLpNorm (besselPotential α f) (ENNReal.ofReal p) volume < ⊤ ∧
        eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral (-z.2) f z.1)
          (ENNReal.ofReal p) (observationMeasure n) ≤
        ENNReal.ofReal C *
          eLpNorm (besselPotential (α) f)
            (ENNReal.ofReal p) volume

def H2 : Prop := ∀ (n : ℕ) (α : ℝ) (f : SchwartzMap (Space n) ℂ),
    Measurable (besselPotential α f) ∧
    Measurable (fun z : Space n × ℝ ↦ halfWaveIntegral (-z.2) f z.1)

theorem main : H1 → H2 → type_of% @OMA.S_wpc_local_smoothing_conjecture.main := by
  intro estimate meas n hn p α hp hα
  obtain ⟨C, hC, h⟩ := estimate n hn p α hp hα
  refine ⟨C, hC, fun f => ?_⟩
  obtain ⟨hJ, hb⟩ := h f
  obtain ⟨mJ, mW⟩ := meas n α f
  exact ⟨⟨mJ.aestronglyMeasurable, hJ⟩, ⟨mW.aestronglyMeasurable, hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ)⟩, hb⟩

end OMA.R_wpc_local_smoothing_conjecture_R1
