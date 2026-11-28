import OMAReductions.R_riemannZeta_simple_prop_lt_R1

/-! Let x = 1/√2 and t = tan x. Then montgomeryTaylorConst⁻¹ = (1 + t/√2)/(√2 t)
= 1/(√2 t) + 1/2 = 1/2 + cos x/(√2 sin x), which gives the identity H = 2 - c⁻¹. For the bound,
0 < x < π/2 gives x < tan x (`Real.lt_tan`), i.e. cos x < √2 sin x, so
(1/√2) · cos x / sin x < 1 and H > 1/2. -/

open Real in
theorem OMA.solution : OMA.R_riemannZeta_simple_prop_lt_R1.H2 := by
  unfold OMA.R_riemannZeta_simple_prop_lt_R1.H2
  dsimp only
  have hr : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
  have hr0 : √2 ≠ (0 : ℝ) := hr.ne'
  have hr2 : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have hx0 : (0 : ℝ) < (√2)⁻¹ := inv_pos.2 hr
  have hr1 : (1 : ℝ) < √2 := by
    have h := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) < 2 by norm_num)
    rwa [Real.sqrt_one] at h
  have hx1 : (√2)⁻¹ < (1 : ℝ) := inv_lt_one_of_one_lt₀ hr1
  have hxpi : (√2)⁻¹ < π / 2 := by linarith [Real.pi_gt_three]
  have hsin : 0 < Real.sin (√2)⁻¹ :=
    Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_gt_three])
  have hcos : 0 < Real.cos (√2)⁻¹ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hxpi⟩
  have hs0 : Real.sin (√2)⁻¹ ≠ 0 := hsin.ne'
  have hc0 : Real.cos (√2)⁻¹ ≠ 0 := hcos.ne'
  have htan : (√2)⁻¹ < Real.tan (√2)⁻¹ := Real.lt_tan hx0 hxpi
  have htan_eq : Real.tan (√2)⁻¹ = Real.sin (√2)⁻¹ / Real.cos (√2)⁻¹ := Real.tan_eq_sin_div_cos _
  have ht0 : Real.tan (√2)⁻¹ ≠ 0 := by
    rw [htan_eq]
    exact (div_pos hsin hcos).ne'
  refine ⟨?_, ?_⟩
  · have hc : ZetaZeros.montgomeryTaylorConst⁻¹ =
        1 / 2 + Real.cos (√2)⁻¹ / (√2 * Real.sin (√2)⁻¹) := by
      unfold ZetaZeros.montgomeryTaylorConst
      rw [one_div (√2), inv_div]
      have e1 : ∀ t r : ℝ, t ≠ 0 → r ≠ 0 →
          (1 + t / r) / (r * t) = 1 / (r * t) + 1 / (r * r) := by
        intro t r ht hr'
        field_simp
        try ring
      rw [e1 _ _ ht0 hr0, hr2, htan_eq]
      field_simp
      try ring
    rw [hc]
    ring
  · have h1 : Real.cos (√2)⁻¹ / Real.sin (√2)⁻¹ < √2 := by
      rw [div_lt_iff₀ hsin]
      have h2 := htan
      rw [htan_eq, lt_div_iff₀ hcos] at h2
      have h4 := mul_lt_mul_of_pos_left h2 hr
      rw [← mul_assoc, mul_inv_cancel₀ hr0, one_mul] at h4
      exact h4
    have h3 : (√2)⁻¹ * (Real.cos (√2)⁻¹ / Real.sin (√2)⁻¹) < 1 := by
      calc (√2)⁻¹ * (Real.cos (√2)⁻¹ / Real.sin (√2)⁻¹) < (√2)⁻¹ * √2 :=
            mul_lt_mul_of_pos_left h1 hx0
        _ = 1 := inv_mul_cancel₀ hr0
    linarith
