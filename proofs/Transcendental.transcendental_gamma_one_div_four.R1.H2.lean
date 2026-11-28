import OMAReductions.R_Transcendental_transcendental_gamma_one_div_four_R1

/-! Euler's Beta integral: substitute t = x ^ 4 in B(1/4, 1/2), then use Gamma(s)Gamma(t) = Gamma(s+t)B(s,t). -/

open MeasureTheory Set Real

/-- The image of `(0,1)` under `x ↦ x ^ 4` is `(0,1)`. -/
lemma image_pow_four : (fun x : ℝ => x ^ 4) '' Ioo 0 1 = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    exact ⟨by positivity, pow_lt_one₀ hx0.le hx1 (by norm_num)⟩
  · rintro ⟨ht0, ht1⟩
    refine ⟨t ^ ((1 : ℝ) / 4), ⟨rpow_pos_of_pos ht0 _, ?_⟩, ?_⟩
    · exact rpow_lt_one ht0.le ht1 (by norm_num)
    · simp only
      rw [← rpow_natCast, ← rpow_mul ht0.le]
      norm_num

/-- The integrand after the substitution `t = x ^ 4`. -/
lemma integrand_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    |4 * x ^ 3| • (((x ^ 4 : ℝ) : ℂ) ^ ((1 / 4 : ℂ) - 1) * (1 - ((x ^ 4 : ℝ) : ℂ)) ^ ((1 / 2 : ℂ) - 1))
      = 4 * (((1 / √(1 - x ^ 4)) : ℝ) : ℂ) := by
  obtain ⟨hx0, hx1⟩ := hx
  have h4 : x ^ 4 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
  have hpos : 0 < 1 - x ^ 4 := by linarith
  have e1 : ((x ^ 4 : ℝ) : ℂ) ^ ((1 / 4 : ℂ) - 1) = ((x ^ (-3 : ℝ) : ℝ) : ℂ) := by
    have : ((1 / 4 : ℂ) - 1) = ((-3 / 4 : ℝ) : ℂ) := by push_cast; norm_num
    rw [this, ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [← rpow_natCast, ← rpow_mul hx0.le]
    norm_num
  have e2 : (1 - ((x ^ 4 : ℝ) : ℂ)) ^ ((1 / 2 : ℂ) - 1) = (((1 - x ^ 4) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
    have : ((1 / 2 : ℂ) - 1) = ((-1 / 2 : ℝ) : ℂ) := by push_cast; norm_num
    rw [this, show (1 - ((x ^ 4 : ℝ) : ℂ)) = ((1 - x ^ 4 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hpos.le]
  have e3 : (1 - x ^ 4) ^ (-1 / 2 : ℝ) = 1 / √(1 - x ^ 4) := by
    rw [sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, rpow_neg hpos.le]
    exact (one_div _).symm
  have e4 : x ^ 3 * x ^ (-3 : ℝ) = 1 := by
    rw [rpow_neg hx0.le, ← rpow_natCast]
    norm_num
    field_simp
  rw [e1, e2, e3, abs_of_pos (by positivity), Complex.real_smul]
  have key : (4 * x ^ 3) * (x ^ (-3 : ℝ) * (1 / √(1 - x ^ 4))) = 4 * (1 / √(1 - x ^ 4)) := by
    rw [← mul_assoc, mul_assoc 4, e4, mul_one]
  exact_mod_cast key

theorem OMA.solution : OMA.R_Transcendental_transcendental_gamma_one_div_four_R1.H2 := by
  unfold OMA.R_Transcendental_transcendental_gamma_one_div_four_R1.H2
  set I := ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 4) with hI
  -- Beta integral via Gamma
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (1 / 4 : ℂ)) (t := (1 / 2 : ℂ))
    (by norm_num) (by norm_num)
  have hsum : (1 / 4 : ℂ) + 1 / 2 = ((3 / 4 : ℝ) : ℂ) := by push_cast; norm_num
  rw [hsum, show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; rfl,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl] at hB
  simp only [Complex.Gamma_ofReal] at hB
  -- betaIntegral as a set integral, then change variables
  have hbeta : Complex.betaIntegral (1 / 4) (1 / 2) = 4 * (I : ℂ) := by
    unfold Complex.betaIntegral
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      ← image_pow_four]
    rw [integral_image_eq_integral_abs_deriv_smul (f' := fun x => 4 * x ^ 3) measurableSet_Ioo
      (fun x _ => by simpa using (hasDerivAt_pow 4 x).hasDerivWithinAt)
      (fun a ha b hb hab => by
        exact (pow_left_inj₀ ha.1.le hb.1.le (by norm_num)).mp hab)]
    rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => integrand_eq hx)]
    rw [integral_const_mul, integral_complex_ofReal, hI, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  rw [show ((1 / 4 : ℝ) : ℂ) = 1 / 4 by push_cast; rfl,
    show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; rfl, hbeta] at hB
  have hG : (0 : ℝ) < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hR : Real.Gamma (1 / 4) * Real.Gamma (1 / 2) = Real.Gamma (3 / 4) * (4 * I) := by
    exact_mod_cast hB
  field_simp
  linarith
