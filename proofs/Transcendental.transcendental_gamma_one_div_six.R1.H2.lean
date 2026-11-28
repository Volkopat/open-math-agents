import OMAReductions.R_Transcendental_transcendental_gamma_one_div_six_R1
import Mathlib

-- Step Transcendental.transcendental_gamma_one_div_six.R1.H2: hypothesis H2 of reduction Transcendental.transcendental_gamma_one_div_six.R1
-- Credit: @luciusacarr
-- H2 := ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 3) =     Real.Gamma (1 / 3) * Real.Gamma (1 / 2) / (3 * Real.Gamma (5 / 6))
-- Adapted from @LordMike's Beta-integral proof for the 1/4 case (PR #10619).

lemma gamma_h2_aux_beta :
    (Complex.betaIntegral ((1/3:ℝ):ℂ) ((1/2:ℝ):ℂ)).re =
      ∫ t in (0:ℝ)..1, t ^ ((1/3:ℝ) - 1) * (1 - t) ^ ((1/2:ℝ) - 1) := by
  have h : (∫ x in (0:ℝ)..1, (x:ℂ) ^ (((1/3:ℝ):ℂ) - 1) * (1 - (x:ℂ)) ^ (((1/2:ℝ):ℂ) - 1))
      = ((∫ t in (0:ℝ)..1, t ^ ((1/3:ℝ) - 1) * (1 - t) ^ ((1/2:ℝ) - 1) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hx
    obtain ⟨h0, h1⟩ := hx
    have h2 : (0:ℝ) ≤ 1 - x := by linarith
    have e1 : ((1/3:ℝ):ℂ) - 1 = (((1/3:ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((1/2:ℝ):ℂ) - 1 = (((1/2:ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, Complex.ofReal_mul, Complex.ofReal_cpow h0.le, Complex.ofReal_cpow h2]
    push_cast
    rfl
  unfold Complex.betaIntegral
  rw [h, Complex.ofReal_re]

lemma gamma_h2_aux_subst :
    ∫ x in (0:ℝ)..1, 1 / √(1 - x ^ 3) =
      (1/3) * ∫ t in (0:ℝ)..1, t ^ ((1/3:ℝ) - 1) * (1 - t) ^ ((1/2:ℝ) - 1) := by
  rw [← intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have himg : (fun x : ℝ => x ^ 3) '' Set.Ioo 0 1 = Set.Ioo 0 1 := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
      exact ⟨by positivity, pow_lt_one₀ hx0.le hx1 (by norm_num)⟩
    · rintro ⟨hy0, hy1⟩
      refine ⟨y ^ (((3:ℕ):ℝ)⁻¹), ⟨Real.rpow_pos_of_pos hy0 _, ?_⟩, ?_⟩
      · exact Real.rpow_lt_one hy0.le hy1 (by norm_num)
      · exact Real.rpow_inv_natCast_pow hy0.le (by norm_num)
  have hinj : Set.InjOn (fun x : ℝ => x ^ 3) (Set.Ioo 0 1) := by
    intro a ha b hb hab
    exact (pow_left_inj₀ ha.1.le hb.1.le (by norm_num)).mp hab
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      HasDerivWithinAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) (Set.Ioo 0 1) x := by
    intro x _
    have h : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
      simpa using hasDerivAt_pow 3 x
    exact h.hasDerivWithinAt
  have key := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun t : ℝ => (1/3:ℝ) * (t ^ ((1/3:ℝ) - 1) * (1 - t) ^ ((1/2:ℝ) - 1)))
  rw [himg] at key
  rw [key]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  obtain ⟨hx0, hx1⟩ := hx
  have hx3 : x ^ 3 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
  have hs : 1 / √(1 - x ^ 3) = (1 - x ^ 3) ^ ((1/2:ℝ) - 1) := by
    rw [Real.sqrt_eq_rpow, show (1/2:ℝ) - 1 = -(1/2) by norm_num,
      Real.rpow_neg (by linarith), one_div]
  have h3 : (x ^ 3) ^ ((1/3:ℝ) - 1) = (x ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    rw [show ((3:ℕ):ℝ) * ((1/3:ℝ) - 1) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg hx0.le,
      Real.rpow_natCast]
  show 1 / √(1 - x ^ 3) = |3 * x ^ 2| • ((1/3:ℝ) * ((x ^ 3) ^ ((1/3:ℝ) - 1) * (1 - x ^ 3) ^ ((1/2:ℝ) - 1)))
  rw [hs, h3, abs_of_pos (by positivity), smul_eq_mul]
  have hx2 : x ^ 2 ≠ 0 := by positivity
  field_simp

theorem OMA.solution : OMA.R_Transcendental_transcendental_gamma_one_div_six_R1.H2 := by
  unfold OMA.R_Transcendental_transcendental_gamma_one_div_six_R1.H2
  have hb := ProbabilityTheory.beta_eq_betaIntegralReal (1/3) (1/2) (by norm_num) (by norm_num)
  unfold ProbabilityTheory.beta at hb
  rw [show (1/3:ℝ) + 1/2 = 5/6 by norm_num] at hb
  rw [gamma_h2_aux_subst, ← gamma_h2_aux_beta, ← hb]
  ring
