import OMAReductions.R_Erdos936_erdos_936_variants_factorial_sub_one_R1

-- Adapted from the factorial-plus-one proof by @NoahPuckett-IO.
theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_sub_one_R1.H1 := by
  intro c hc powerful
  rw [← Finset.prod_pow]
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hc.ne']
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  exact Nat.pow_dvd_pow p (((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization
    hc.ne').mp (powerful p hp))
