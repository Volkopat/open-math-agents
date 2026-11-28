import OMAStatements.S_mo_344923
import Mathlib

open MeasureTheory
open scoped ENNReal

open OMA.S_mo_344923 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_344923.main) := fun h => by
  let μ : Measure (ℝ × ℝ) := (2 : ℝ≥0∞)⁻¹ • (.dirac 0 + .dirac 1)
  have hp : IsProbabilityMeasure μ := ⟨by simp [μ, ← two_mul, ENNReal.mul_inv_cancel]⟩
  have := h ℝ ℝ μ hp (fun _ => 0) (LipschitzWith.const' 0)
  simp [mutualInformation, Measure.map_const, Measure.fst, Measure.snd, Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_snd, Measure.dirac_prod_dirac, eq_comm (a := (0 : ℝ≥0∞))] at this
  rw [InformationTheory.klDiv_eq_zero_iff] at this
  have := congrArg (fun ν : Measure (ℝ × ℝ) => ν ({0} ×ˢ {1})) this
  rw [Measure.prod_prod] at this
  simp [μ, Measure.map_apply measurable_fst, Measure.map_apply measurable_snd] at this
