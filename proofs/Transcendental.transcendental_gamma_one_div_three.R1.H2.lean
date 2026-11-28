import OMAReductions.R_Transcendental_transcendental_gamma_one_div_three_R1
import Mathlib

-- Step H2 of Transcendental.transcendental_gamma_one_div_three.R1.
-- Credit: @LordMike

open MeasureTheory Set

/-- Real form of the Beta integral, from the complex Beta-Gamma relation. -/
lemma oma_h2_beta_real (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have hc := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  have hB : Complex.betaIntegral (a : ℂ) (b : ℂ) =
      ((∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1) : ℝ) : ℂ) := by
    unfold Complex.betaIntegral
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    obtain ⟨h0, h1⟩ := ht
    have e1 : (t : ℂ) ^ ((a : ℂ) - 1) = ((t ^ (a - 1) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow h0, Complex.ofReal_sub, Complex.ofReal_one]
    have e2 : (1 - (t : ℂ)) ^ ((b : ℂ) - 1) = (((1 - t) ^ (b - 1) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (sub_nonneg.mpr h1), Complex.ofReal_sub, Complex.ofReal_sub,
        Complex.ofReal_one]
    simp only
    rw [e1, e2, Complex.ofReal_mul]
  have hsum : (a : ℂ) + (b : ℂ) = ((a + b : ℝ) : ℂ) := by push_cast; ring
  rw [hB, hsum, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at hc
  have hpos : Real.Gamma (a + b) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  rw [eq_div_iff hpos]
  have key : ((∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1) : ℝ) : ℂ) *
      ((Real.Gamma (a + b) : ℝ) : ℂ) = ((Real.Gamma a * Real.Gamma b : ℝ) : ℂ) := by
    push_cast
    linear_combination -hc
  exact_mod_cast key

/-- The substitution `t = x ^ 3` on `(0, 1)`. -/
lemma oma_h2_cube_subst (g : ℝ → ℝ) :
    ∫ t in Ioo (0 : ℝ) 1, g t = ∫ x in Ioo (0 : ℝ) 1, |3 * x ^ 2| • g (x ^ 3) := by
  have hinj : InjOn (fun x : ℝ => x ^ 3) (Ioo 0 1) := by
    intro x hx y hy hxy
    simp only at hxy
    exact (pow_left_inj₀ hx.1.le hy.1.le (by norm_num)).mp hxy
  have himg : (fun x : ℝ => x ^ 3) '' Ioo 0 1 = Ioo 0 1 := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy0, hy1⟩, rfl⟩
      exact ⟨pow_pos hy0 3, pow_lt_one₀ hy0.le hy1 (by norm_num)⟩
    · rintro ⟨hx0, hx1⟩
      refine ⟨x ^ ((1 : ℝ) / 3), ⟨Real.rpow_pos_of_pos hx0 _, ?_⟩, ?_⟩
      · exact Real.rpow_lt_one hx0.le hx1 (by norm_num)
      · show (x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = x
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        norm_num
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) (Ioo 0 1) x := by
    intro x _
    have h' : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
      simpa using hasDerivAt_pow 3 x
    exact h'.hasDerivWithinAt
  have := integral_image_eq_integral_abs_deriv_smul (f := fun x : ℝ => x ^ 3)
    (f' := fun x : ℝ => 3 * x ^ 2) measurableSet_Ioo hd hinj g
  rw [himg] at this
  exact this

lemma oma_h2_integrand (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    |3 * x ^ 2| • ((x ^ 3) ^ ((1 : ℝ) / 3 - 1) * (1 - x ^ 3) ^ ((1 : ℝ) / 2 - 1)) =
      3 * (1 / √(1 - x ^ 3)) := by
  have h3 : (0 : ℝ) < 1 - x ^ 3 := by
    have : x ^ 3 < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
    linarith
  have hA : (x ^ 3) ^ ((1 : ℝ) / 3 - 1) = (x ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast x 3, ← Real.rpow_mul hx0.le]
    rw [show ((3 : ℕ) : ℝ) * ((1 : ℝ) / 3 - 1) = -2 by norm_num, Real.rpow_neg hx0.le]
    norm_num
  have hB : (1 - x ^ 3) ^ ((1 : ℝ) / 2 - 1) = 1 / √(1 - x ^ 3) := by
    rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, Real.rpow_neg h3.le, ← Real.sqrt_eq_rpow,
      one_div]
  simp only [smul_eq_mul]
  rw [abs_of_nonneg (by positivity), hA, hB]
  field_simp

theorem OMA.solution : OMA.R_Transcendental_transcendental_gamma_one_div_three_R1.H2 := by
  unfold OMA.R_Transcendental_transcendental_gamma_one_div_three_R1.H2
  have hB := oma_h2_beta_real (1 / 3) (1 / 2) (by norm_num) (by norm_num)
  have h56 : (1 : ℝ) / 3 + 1 / 2 = 5 / 6 := by norm_num
  rw [h56] at hB
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hB ⊢
  have hc := oma_h2_cube_subst (fun t : ℝ => t ^ ((1 : ℝ) / 3 - 1) * (1 - t) ^ ((1 : ℝ) / 2 - 1))
  beta_reduce at hc
  rw [setIntegral_congr_fun measurableSet_Ioo
    (fun x hx => oma_h2_integrand x hx.1 hx.2), integral_const_mul] at hc
  have h3 : (3 : ℝ) * ∫ x in Ioo (0 : ℝ) 1, 1 / √(1 - x ^ 3) =
      Real.Gamma (1 / 3) * Real.Gamma (1 / 2) / Real.Gamma (5 / 6) := by
    rw [← hB, hc]
  have hJ : ∫ x in Ioo (0 : ℝ) 1, 1 / √(1 - x ^ 3) =
      Real.Gamma (1 / 3) * Real.Gamma (1 / 2) / Real.Gamma (5 / 6) / 3 := by
    linarith
  rw [hJ]
  ring
