import OMAReductions.R_mse_1426354_R1

open OMA.S_mse_1426354

theorem OMA.solution : OMA.R_mse_1426354_R1.H1 := by
  intro n hn hσ
  have hnReal : (5041 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 5041 ≤ n by omega)
  have hnPos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hexpOne : Real.exp 1 ≤ 11 / 4 :=
    Real.exp_one_lt_d9.le.trans (by norm_num)
  have hexpPow (k : ℕ) : Real.exp (k : ℝ) ≤ (11 / 4 : ℝ) ^ k := by
    calc
      Real.exp (k : ℝ) = Real.exp 1 ^ k := by simpa using Real.exp_nat_mul 1 k
      _ ≤ (11 / 4 : ℝ) ^ k := pow_le_pow_left₀ (Real.exp_pos 1).le hexpOne k
  have hharm := log_add_one_le_harmonic n
  have h8 : (8 : ℝ) ≤ (harmonic n : ℝ) := by
    refine ((Real.le_log_iff_exp_le hnPos).2 ?_).trans hharm
    calc
      Real.exp 8 ≤ (11 / 4 : ℝ) ^ 8 := by exact_mod_cast hexpPow 8
      _ ≤ (5041 : ℝ) := by norm_num
      _ ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hlog : (2 : ℝ) ≤ Real.log (harmonic n : ℝ) := by
    refine (Real.le_log_iff_exp_le (by linarith)).2 ?_
    calc
      Real.exp 2 ≤ (11 / 4 : ℝ) ^ 2 := by exact_mod_cast hexpPow 2
      _ ≤ 8 := by norm_num
      _ ≤ (harmonic n : ℝ) := h8
  have hExp : (n : ℝ) ≤ Real.exp (harmonic n : ℝ) := by
    have h := Real.exp_le_exp.mpr hharm
    rw [Real.exp_log hnPos] at h
    push_cast at h
    linarith
  calc
    (ArithmeticFunction.sigma 1 n : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hσ
    _ = (n : ℝ) * 2 := mul_comm _ _
    _ ≤ tailTerm n :=
      mul_le_mul hExp hlog (by norm_num) (Real.exp_pos _).le
