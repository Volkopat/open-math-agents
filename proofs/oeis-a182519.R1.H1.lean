import OMAReductions.R_oeis_a182519_R1

theorem OMA.solution : OMA.R_oeis_a182519_R1.H1 := by
  intro n p q hp hpq hgap
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  have hdiv_eq : (q : ℝ) / (p : ℝ) = ((q : ℝ) - (p : ℝ)) / (p : ℝ) + 1 := by
    field_simp [hp_pos.ne']
    ring
  have hdiv_nn : (0 : ℝ) ≤ (q : ℝ) / (p : ℝ) := by positivity
  have hexp1 : (q : ℝ) / (p : ℝ) ≤ Real.exp (((q : ℝ) - (p : ℝ)) / (p : ℝ)) := by
    rw [hdiv_eq]
    exact Real.add_one_le_exp _
  have hexp_pow : ((q : ℝ) / (p : ℝ)) ^ n ≤ Real.exp ((n : ℝ) * (((q : ℝ) - (p : ℝ)) / (p : ℝ))) := by
    calc ((q : ℝ) / (p : ℝ)) ^ n
        ≤ (Real.exp (((q : ℝ) - (p : ℝ)) / (p : ℝ))) ^ n := pow_le_pow_left₀ hdiv_nn hexp1 n
      _ = Real.exp ((n : ℝ) * (((q : ℝ) - (p : ℝ)) / (p : ℝ))) := (Real.exp_nat_mul _ n).symm
  have hlt_log : (n : ℝ) * (((q : ℝ) - (p : ℝ)) / (p : ℝ)) < Real.log (p : ℝ) := by
    rw [← mul_div_assoc, div_lt_iff₀ hp_pos, mul_comm (Real.log (p : ℝ)) (p : ℝ)]
    exact hgap
  have hlt_p : ((q : ℝ) / (p : ℝ)) ^ n < (p : ℝ) := by
    calc ((q : ℝ) / (p : ℝ)) ^ n
        ≤ Real.exp ((n : ℝ) * (((q : ℝ) - (p : ℝ)) / (p : ℝ))) := hexp_pow
      _ < Real.exp (Real.log (p : ℝ)) := Real.exp_lt_exp.mpr hlt_log
      _ = (p : ℝ) := Real.exp_log hp_pos
  have hpn_pos : (0 : ℝ) < (p : ℝ) ^ n := pow_pos hp_pos n
  have hreal : ((q : ℝ) ^ n) < (p : ℝ) ^ (n + 1) := by
    calc (q : ℝ) ^ n
        = ((q : ℝ) / (p : ℝ)) ^ n * (p : ℝ) ^ n := by
          rw [div_pow, div_mul_cancel₀ _ hpn_pos.ne']
      _ < (p : ℝ) * (p : ℝ) ^ n := mul_lt_mul_of_pos_right hlt_p hpn_pos
      _ = (p : ℝ) ^ (n + 1) := (pow_succ' (p : ℝ) n).symm
  exact_mod_cast hreal
