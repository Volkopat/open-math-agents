import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H2: hypothesis H2 of reduction Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1
-- Credit: @MattGaiser
-- For large j the term is at most j^(-2): log (log (4^j)) ≥ log j and c * (log j)^η ≥ 2 eventually.

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1.H2 := by
  intro c η hc hη
  have hlogj : Filter.Tendsto (fun j : ℕ => Real.log (j : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hP : Filter.Tendsto (fun j : ℕ => Real.log (j : ℝ) ^ η) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hη).comp hlogj
  refine Summable.of_norm_bounded_eventually_nat (g := fun j : ℕ => ((j : ℝ) ^ 2)⁻¹)
    (Real.summable_nat_pow_inv.mpr (by norm_num)) ?_
  filter_upwards [Filter.eventually_ge_atTop 1, hlogj.eventually_gt_atTop 0,
    hP.eventually_ge_atTop (2 / c)] with j hj hl hp
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have h4 : (1 : ℝ) ≤ Real.log 4 := by
    have he : Real.exp 1 ≤ 4 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 4 := Real.log_le_log (Real.exp_pos 1) he
  have hLge : Real.log (j : ℝ) ≤ Real.log (Real.log ((4 : ℝ) ^ j)) := by
    rw [Real.log_pow]
    apply Real.log_le_log hjpos
    nlinarith [mul_le_mul_of_nonneg_left h4 hjpos.le]
  have hLpos : 0 < Real.log (Real.log ((4 : ℝ) ^ j)) := hl.trans_le hLge
  have hpow : 2 / c ≤ Real.log (Real.log ((4 : ℝ) ^ j)) ^ η :=
    hp.trans (Real.rpow_le_rpow hl.le hLge hη.le)
  have hgain : 2 * Real.log (j : ℝ) ≤ c * Real.log (Real.log ((4 : ℝ) ^ j)) ^ (1 + η) := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
    have h2 : 2 ≤ Real.log (Real.log ((4 : ℝ) ^ j)) ^ η * c := (div_le_iff₀ hc).mp hpow
    nlinarith [mul_le_mul_of_nonneg_left h2 hLpos.le]
  have hsq : (2 : ℝ) * Real.log (j : ℝ) = Real.log ((j : ℝ) ^ 2) := by
    rw [Real.log_pow]; norm_num
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-c * Real.log (Real.log ((4 : ℝ) ^ j)) ^ (1 + η))
      ≤ Real.exp (-(2 * Real.log (j : ℝ))) := Real.exp_le_exp.mpr (by linarith)
    _ = ((j : ℝ) ^ 2)⁻¹ := by
      rw [hsq, Real.exp_neg, Real.exp_log (by positivity)]
