import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1

-- Step Erdos338.erdos_338.variants.triangular.R1.H1.R1.H1.R1.H2
-- Credit: @caa1982

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1.H2 := by
  unfold OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1.H2
  rw [Filter.eventually_atTop]
  refine ⟨3 ^ 20, fun m hm => ?_⟩
  dsimp only
  set N := 8 * m + 3
  have hN_gt : (3 : ℝ) ^ 20 < (N : ℝ) := by
    have : 3 ^ 20 < N := by omega
    exact_mod_cast this
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_trans (by positivity) hN_gt
  have hsqrt4 : (N.sqrt.sqrt : ℝ) ^ 4 ≤ (N : ℝ) := by
    have h1 : N.sqrt.sqrt * N.sqrt.sqrt ≤ N.sqrt := Nat.sqrt_le N.sqrt
    have h2 : N.sqrt * N.sqrt ≤ N := Nat.sqrt_le N
    have h3 : N.sqrt.sqrt ^ 4 ≤ N := by
      calc N.sqrt.sqrt ^ 4 = (N.sqrt.sqrt * N.sqrt.sqrt) * (N.sqrt.sqrt * N.sqrt.sqrt) := by ring
        _ ≤ N.sqrt * N.sqrt := Nat.mul_le_mul h1 h1
        _ ≤ N := h2
    exact_mod_cast h3
  have hpow : (3 * (N.sqrt.sqrt : ℝ)) ^ 20 < ((N : ℝ) ^ (3 / 10 : ℝ)) ^ 20 := by
    have hR : ((N : ℝ) ^ (3 / 10 : ℝ)) ^ 20 = (N : ℝ) ^ 6 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN_pos)]
      norm_num
    rw [hR]
    calc (3 * (N.sqrt.sqrt : ℝ)) ^ 20
        = (3 : ℝ) ^ 20 * ((N.sqrt.sqrt : ℝ) ^ 4) ^ 5 := by ring
      _ ≤ (3 : ℝ) ^ 20 * (N : ℝ) ^ 5 := by
          gcongr
      _ < (N : ℝ) * (N : ℝ) ^ 5 := by
          gcongr
      _ = (N : ℝ) ^ 6 := by ring
  by_contra! hle
  have hpow_le : ((N : ℝ) ^ (3 / 10 : ℝ)) ^ 20 ≤ (3 * (N.sqrt.sqrt : ℝ)) ^ 20 :=
    pow_le_pow_left₀ (by positivity) hle 20
  linarith
