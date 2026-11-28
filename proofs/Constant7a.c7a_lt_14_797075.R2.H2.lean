import OMAReductions.R_Constant7a_c7a_lt_14_797075_R2

/-!
Proof of `OMA.R_Constant7a_c7a_lt_14_797075_R2.H2`.

If `|π - m / n| < C / n ^ p` with `n ≥ 1` and `C > 0`, then `|m / n| ≤ π + C`, so
`|π ^ 2 - m ^ 2 / n ^ 2| = |π - m / n| * |π + m / n| < C (2 π + C) / (n ^ 2) ^ (p / 2)`.
The approximations are nontrivial because `π` is irrational, so `π ^ 2` is a Liouville number
with exponent `p / 2` along the denominators `n ^ 2`. Multiplying by the rational `1 / 6`
preserves this (`LiouvilleWith.mul_rat`).
-/

open Filter Real

theorem OMA.solution : OMA.R_Constant7a_c7a_lt_14_797075_R2.H2 := by
  intro p hp h
  have hsq : LiouvilleWith (p / 2) (π ^ 2) := by
    obtain ⟨C, hC0, hC⟩ := h.exists_pos
    refine ⟨C * (2 * π + C), ?_⟩
    refine Tendsto.frequently_map (fun n : ℕ => n ^ 2) (tendsto_pow_atTop two_ne_zero) ?_ hC
    rintro n ⟨hn, m, hne, hlt⟩
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hnp : (1 : ℝ) ≤ (n : ℝ) ^ p := Real.one_le_rpow hnR hp
    have hnp0 : (0 : ℝ) < (n : ℝ) ^ p := by linarith
    refine ⟨m ^ 2, ?_, ?_⟩
    · intro heq
      push_cast at heq
      have hsq' : π ^ 2 = ((m : ℝ) / n) ^ 2 := by rw [heq, div_pow]
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq' with h1 | h1
      · exact hne h1
      · exact irrational_pi ⟨((-m : ℤ) : ℚ) / n, by push_cast; rw [h1]; ring⟩
    · have hpow : (((n ^ 2 : ℕ) : ℝ)) ^ (p / 2) = (n : ℝ) ^ p := by
        push_cast
        rw [← Real.rpow_natCast_mul hnpos.le]
        congr 1
        push_cast
        ring
      rw [hpow]
      have hfac : π ^ 2 - (((m ^ 2 : ℤ) : ℝ) / ((n ^ 2 : ℕ) : ℝ)) =
          (π - (m : ℝ) / n) * (π + (m : ℝ) / n) := by
        push_cast
        field_simp
        ring
      rw [hfac, abs_mul]
      have hCn : C / (n : ℝ) ^ p ≤ C := div_le_self hC0.le hnp
      have hb : |π + (m : ℝ) / n| ≤ 2 * π + C := by
        have h1 : |(m : ℝ) / n| ≤ π + C := by
          have := abs_sub_abs_le_abs_sub ((m : ℝ) / n) π
          rw [abs_sub_comm] at this
          have hpi : |π| = π := abs_of_pos Real.pi_pos
          linarith
        have := abs_add_le π ((m : ℝ) / n)
        rw [abs_of_pos Real.pi_pos] at this
        linarith
      have hB : 0 < 2 * π + C := by linarith [Real.pi_pos]
      calc |π - (m : ℝ) / n| * |π + (m : ℝ) / n|
          ≤ |π - (m : ℝ) / n| * (2 * π + C) := by gcongr
        _ < C / (n : ℝ) ^ p * (2 * π + C) := by gcongr
        _ = C * (2 * π + C) / (n : ℝ) ^ p := by ring
  have h6 := hsq.mul_rat (r := (1 / 6 : ℚ)) (by norm_num)
  have heq : π ^ 2 * (((1 / 6 : ℚ)) : ℝ) = π ^ 2 / 6 := by push_cast; ring
  rwa [heq] at h6
