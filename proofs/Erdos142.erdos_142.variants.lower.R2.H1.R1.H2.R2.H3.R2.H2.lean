import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2
import Mathlib

/-! A stretched exponential is summable: `(j L)^2 * exp (-c (j L)^e) → 0` (via `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`),
so the terms are eventually at most `C / (L^2 j^2)`, which is summable. -/

open Filter Real Topology

namespace OMA.E142Summ

theorem summ (C c e : ℝ) (hC : 0 < C) (hc : 0 < c) (he : 0 < e) :
    Summable (fun j : ℕ ↦ C * Real.exp (-c * ((j : ℝ) * Real.log 4) ^ e)) := by
  set L := Real.log 4 with hLdef
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hlin : Tendsto (fun j : ℕ => (j : ℝ) * L) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hL
  have key : Tendsto (fun j : ℕ => (((j : ℝ) * L) ^ e) ^ (2 / e) * exp (-c * ((j : ℝ) * L) ^ e))
      atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 / e) c hc).comp ((tendsto_rpow_atTop he).comp hlin)
  have hev := key.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hg : Summable (fun j : ℕ => C * (1 / L ^ 2) * (1 / (j : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hx : 0 < (j : ℝ) * L := mul_pos hjpos hL
  have hpow : (((j : ℝ) * L) ^ e) ^ (2 / e) = ((j : ℝ) * L) ^ 2 := by
    rw [← Real.rpow_mul hx.le, mul_div_cancel₀ _ he.ne']; norm_num
  rw [hpow] at hj
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsq : 0 < ((j : ℝ) * L) ^ 2 := by positivity
  have h1 : exp (-c * ((j : ℝ) * L) ^ e) ≤ 1 / ((j : ℝ) * L) ^ 2 := by
    rw [le_div_iff₀ hsq]; linarith
  calc C * exp (-c * ((j : ℝ) * L) ^ e) ≤ C * (1 / ((j : ℝ) * L) ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hC.le
    _ = C * (1 / L ^ 2) * (1 / (j : ℝ) ^ 2) := by rw [mul_pow]; field_simp

end OMA.E142Summ

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R2.H2 :=
  fun C c e hC hc he => OMA.E142Summ.summ C c e hC hc he
