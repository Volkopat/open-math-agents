import OMAStatements.S_mo_142767
import Mathlib

open MeasureTheory Filter Set
open scoped Topology ENNReal

open OMA.S_mo_142767



theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_142767.main) := by
  intro h
  let x (n : ℕ) : Fin 1 → ℝ := fun _ => ((n : ℝ) + 1)⁻¹
  let z : Fin 1 → ℝ := 0
  have hx : Tendsto x atTop (𝓝 z) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_mono (fun (n : ℕ) => le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1))
        tendsto_natCast_atTop_atTop)
  have hne (n : ℕ) : x n ≠ z := by
    intro e
    have he := congrFun e (0 : Fin 1)
    change ((n : ℝ) + 1)⁻¹ = 0 at he
    exact (ne_of_gt (by positivity : 0 < ((n : ℝ) + 1)⁻¹)) he
  have hint : IntegralsConverge (fun n => Measure.dirac (x n)) (Measure.dirac z) := by
    intro f hf
    simpa only [integral_dirac, Function.comp_def] using ((hf.continuous.continuousAt (x := z)).tendsto.comp hx)
  have hs := h 1 _ _ hint {z} (measurableSet_singleton z)
  have hz (n : ℕ) : Measure.dirac (x n) {z} = 0 := by
    simp [hne]
  have ho : Measure.dirac z {z} = 1 := Measure.dirac_apply_of_mem (mem_singleton z)
  simp only [hz, ho] at hs
  have hc : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0) := tendsto_const_nhds
  exact zero_ne_one (tendsto_nhds_unique hc hs)
