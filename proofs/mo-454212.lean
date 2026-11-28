import OMAStatements.S_mo_454212

theorem OMA.solution : type_of% @OMA.S_mo_454212.main := by
  intro G _ d hd g h
  obtain ⟨hn, hz, hinv, hneg⟩ := hd
  -- Take the three group elements g⁻¹, 1, h with weights t, -(t+1), 1.
  have quadratic (t : ℝ) :
      0 ≤ d g * (t * t) + (d g + d h - d (g * h)) * t + d h := by
    have H := hneg 3 ![g⁻¹, 1, h] ![t, -(t + 1), 1] (by simp [Fin.sum_univ_three])
    simp [Fin.sum_univ_three, ← mul_inv_rev, hinv, hz] at H
    linarith only [H]
  have bound := discrim_le_zero quadratic
  unfold discrim at bound
  have cross : d (g * h) - d g - d h ≤ 2 * Real.sqrt (d g) * Real.sqrt (d h) := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, mul_pow, Real.sq_sqrt (hn g), Real.sq_sqrt (hn h)]
    linarith only [bound]
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity, by nlinarith only [cross, Real.sq_sqrt (hn g), Real.sq_sqrt (hn h)]⟩
