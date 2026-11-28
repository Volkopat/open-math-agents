import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1
import Mathlib

/-! With y = log (m log 2), y (c y^eta - 2) tends to infinity, so exp (-c y^(1+eta)) is eventually at most
(log 2)^2 / exp(y)^2 = 1 / m^2, which is summable. -/

open Filter Real Topology

namespace OMA.E142Summ2

theorem summ (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    Summable (fun m : ℕ ↦ Real.exp (-c * Real.log (Real.log ((2 : ℝ) ^ m)) ^ (1 + η))) := by
  set L := Real.log 2 with hLdef
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hy : Tendsto (fun m : ℕ => Real.log ((m : ℝ) * L)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hL)
  have hg : Tendsto (fun y : ℝ => y * (c * y ^ η + (-2))) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ (-2) ((tendsto_rpow_atTop hη).const_mul_atTop hc))
  have hev := (hg.comp hy).eventually (eventually_ge_atTop (-2 * Real.log L))
  have hsum : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hsum ?_
  filter_upwards [hev, hy.eventually (eventually_gt_atTop 0), eventually_ge_atTop 1] with m hm hypos hm1
  simp only [Function.comp] at hm
  have hlog : Real.log ((2 : ℝ) ^ m) = (m : ℝ) * L := by rw [Real.log_pow]
  rw [hlog]
  set y := Real.log ((m : ℝ) * L) with hydef
  have hmL : 0 < (m : ℝ) * L := mul_pos (by exact_mod_cast hm1) hL
  have hexpy : Real.exp y = (m : ℝ) * L := Real.exp_log hmL
  have hsplit : y ^ (1 + η) = y * y ^ η := by rw [Real.rpow_add hypos, Real.rpow_one]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have key : -c * y ^ (1 + η) ≤ 2 * Real.log L - 2 * y := by rw [hsplit]; nlinarith
  calc Real.exp (-c * y ^ (1 + η)) ≤ Real.exp (2 * Real.log L - 2 * y) := Real.exp_le_exp.mpr key
    _ = L ^ 2 / (Real.exp y) ^ 2 := by
        rw [Real.exp_sub, show 2 * Real.log L = Real.log (L ^ 2) by rw [Real.log_pow]; norm_num,
          Real.exp_log (by positivity), show 2 * y = (2 : ℕ) * y by norm_num, Real.exp_nat_mul]
    _ = 1 / (m : ℝ) ^ 2 := by rw [hexpy]; field_simp

end OMA.E142Summ2

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R1.H2 :=
  fun c η hc hη => OMA.E142Summ2.summ c η hc hη
