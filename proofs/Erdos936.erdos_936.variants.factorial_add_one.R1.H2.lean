import OMAReductions.R_Erdos936_erdos_936_variants_factorial_add_one_R1

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_add_one_R1.H2 := by
  intro C e
  filter_upwards [(FloorSemiring.tendsto_pow_div_factorial_atTop ((4 : ℝ) ^ e)).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (C + 1)))] with n h
  rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul] at h
  have : (primorial n : ℝ) ^ e ≤ ((4 : ℝ) ^ e) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]; exact_mod_cast Nat.pow_le_pow_left (primorial_le_four_pow n) e
  exact_mod_cast (by push_cast; nlinarith [mul_le_mul_of_nonneg_left this C.cast_nonneg, (by positivity : (0 : ℝ) ≤ ((4 : ℝ) ^ e) ^ n)] :
    ((C * primorial n ^ e : ℕ) : ℝ) < n.factorial)
