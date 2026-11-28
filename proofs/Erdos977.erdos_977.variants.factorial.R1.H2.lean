import OMAReductions.R_Erdos977_erdos_977_variants_factorial_R1

theorem OMA.solution : OMA.R_Erdos977_erdos_977_variants_factorial_R1.H2 := by
  intro C K
  simpa only [Nat.sub_zero] using Nat.eventually_mul_pow_lt_factorial_sub C K 0
