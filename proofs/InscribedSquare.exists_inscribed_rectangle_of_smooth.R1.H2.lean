import OMAReductions.R_InscribedSquare_exists_inscribed_rectangle_of_smooth_R1

/-! Take w = 1 + r i and ζ = w^2 / (1 + r^2). Then ‖ζ‖ = ‖w‖^2 / (1 + r^2) = 1,
1 + ζ = 2 w / (1 + r^2) ≠ 0, and 1 - ζ = -i r (1 + ζ), so ‖1 - ζ‖ = r ‖1 + ζ‖ and 1 - ζ ≠ 0. -/

theorem OMA.solution : OMA.R_InscribedSquare_exists_inscribed_rectangle_of_smooth_R1.H2 := by
  intro r hr
  set w : ℂ := 1 + (r : ℂ) * Complex.I with hw
  set D : ℂ := 1 + (r : ℂ) ^ 2 with hD
  have hDr : D = ((1 + r ^ 2 : ℝ) : ℂ) := by rw [hD]; push_cast; ring
  have hD0 : D ≠ 0 := by
    rw [hDr]
    exact_mod_cast (by positivity : (1 + r ^ 2 : ℝ) ≠ 0)
  have hDn : ‖D‖ = 1 + r ^ 2 := by
    rw [hDr]
    exact Complex.norm_of_nonneg (by positivity)
  have hwn : ‖w‖ ^ 2 = 1 + r ^ 2 := by
    have h := Complex.normSq_add_mul_I 1 r
    simp only [Complex.ofReal_one] at h
    rw [hw, Complex.sq_norm, h, one_pow]
  have hw0 : w ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp [hw] at h'
  have hplus : 1 + w ^ 2 / D = 2 * w / D := by
    rw [eq_div_iff hD0, add_mul, div_mul_cancel₀ _ hD0, one_mul, hw, hD]
    linear_combination (r : ℂ) ^ 2 * Complex.I_sq
  have hplus0 : 1 + w ^ 2 / D ≠ 0 := by
    rw [hplus]
    exact div_ne_zero (mul_ne_zero two_ne_zero hw0) hD0
  have hminus : 1 - w ^ 2 / D = -Complex.I * (r : ℂ) * (1 + w ^ 2 / D) := by
    rw [hplus, one_sub_div hD0, mul_div_assoc']
    congr 1
    rw [hw, hD]
    linear_combination (r : ℂ) ^ 2 * Complex.I_sq
  refine ⟨w ^ 2 / D, ?_, ?_, hplus0, ?_⟩
  · rw [norm_div, norm_pow, hwn, hDn, div_self (by positivity)]
  · rw [hminus]
    refine mul_ne_zero (mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) ?_) hplus0
    exact_mod_cast hr.ne'
  · rw [hminus, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_of_nonneg hr.le]
