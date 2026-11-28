import OMAReductions.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1

-- Step wpc-local-smoothing-conjecture.R1.H1.R1.H2.R1.H3: hypothesis H3 of reduction wpc-local-smoothing-conjecture.R1.H1.R1.H2.R1
-- Credit: @luciusacarr
-- H3 := ∀ (A : ℕ) (ε : ℝ), 0 < ε →   let d := fun j : ℕ => ((2:ℝ)⁻¹ ^ j)   Summable (fun j => d j ^ ε * (1+Real.log (1/d j))^A)

/-! With `d j = 2^(-j)` the term is `r^j (1 + j log 2)^A` where `r = (1/2)^ε < 1`. Since
`log 2 < 1` it is at most `(j+1)^A r^j`, a polynomial times a geometric sequence, which is
summable (`summable_pow_mul_geometric_of_norm_lt_one`, shifted by one). -/

theorem OMA.solution : OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1.H3 := by
  intro A ε hε
  simp only
  set r : ℝ := (2 : ℝ)⁻¹ ^ ε with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hε
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- the dominating series
  have hsum : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ A * r ^ j) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one A
      (show ‖r‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    have h' := (summable_nat_add_iff 1).mpr h
    have hr' : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
    refine (h'.mul_left r⁻¹).congr ?_
    intro j
    push_cast
    rw [pow_succ]
    field_simp
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hsum
  · have h1 : 0 ≤ (1 : ℝ) + Real.log (1 / (2 : ℝ)⁻¹ ^ j) := by
      rw [one_div, ← inv_pow, inv_inv, Real.log_pow]
      positivity
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (pow_nonneg h1 _)
  · have hd : ((2 : ℝ)⁻¹ ^ j) ^ ε = r ^ j := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num), mul_comm]
    have hlog : Real.log (1 / (2 : ℝ)⁻¹ ^ j) = j * Real.log 2 := by
      rw [one_div, ← inv_pow, inv_inv, Real.log_pow]
    rw [hd, hlog, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 _)
    apply pow_le_pow_left₀ (by positivity)
    have : (j : ℝ) * Real.log 2 ≤ j := by
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    linarith
