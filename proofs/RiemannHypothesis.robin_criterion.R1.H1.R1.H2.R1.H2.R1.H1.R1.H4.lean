import OMAReductions.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1_H1_R1
import Mathlib

open Real MeasureTheory Set

theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H2_R1_H2_R1_H1_R1.H4 := by
  intro s b hs hsb
  let f (t : ℝ) := ((2*log t+1)/(t^3*(log t)^2))*Chebyshev.theta t
  have bound := integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) (c := s) (by linarith)
  have hf : IntegrableOn f (Ioi s) := by
    apply (bound.const_mul (3*log 4)).mono'
    · have htheta := Chebyshev.theta_mono.measurable
      have hm : Measurable f := by dsimp [f]; fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ts : s<t := ht
      have ht0 : 0<t := by linarith
      have hl : 1 ≤ log t := by
        rw [Real.le_log_iff_exp_le ht0]
        linarith [Real.exp_one_lt_d9]
      have hθ := Chebyshev.theta_le_log4_mul_x ht0.le
      have hθ0 := Chebyshev.theta_nonneg t
      have hK : 0 ≤ (2*log t+1)/(t^3*(log t)^2) := div_nonneg (by linarith) (by positivity)
      have hK' : (2*log t+1)/(t^3*(log t)^2) ≤ 3/t^3 := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [mul_nonneg (show 0 ≤ t^3 by positivity)
          (show 0 ≤ 3*(log t)^2-(2*log t+1) by nlinarith [sq_nonneg (log t-1)])]
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hK hθ0)]
      calc _ ≤ (3/t^3)*(log 4*t) := mul_le_mul hK' hθ hθ0 (by positivity)
           _ = (3*log 4)*t^(-2:ℝ) := by
             rw [show t^(-2:ℝ) = (t^2)⁻¹ by rw [Real.rpow_neg ht0.le]; norm_num]
             field_simp
  simpa only [intervalIntegral.integral_of_le hsb] using intervalIntegral.integral_Ioi_sub_Ioi hf hsb

