import OMAReductions.R_Erdos727_erdos_727_variants_k_2_R1

theorem OMA.solution : OMA.R_Erdos727_erdos_727_variants_k_2_R1.H1 := by
  intro n
  have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega] at this
  rw [← this, show (n + 2).factorial ^ 2 = ((n + 1) * (n + 2)) ^ 2 * (n.factorial * n.factorial) by
    simp [Nat.factorial_succ]; ring, mul_assoc]
  exact Nat.mul_dvd_mul_iff_right (by positivity)
