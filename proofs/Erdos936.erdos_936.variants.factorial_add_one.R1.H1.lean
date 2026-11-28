import OMAReductions.R_Erdos936_erdos_936_variants_factorial_add_one_R1

-- Step Erdos936.erdos_936.variants.factorial_add_one.R1.H1: hypothesis H1 of reduction Erdos936.erdos_936.variants.factorial_add_one.R1
-- Credit: @NoahPuckett-IO
-- Write c as the product of p ^ v_p(c) over its prime factors; powerful means every v_p(c) is at least 2.

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_add_one_R1.H1 := by
  intro c hc hpow
  rw [← Finset.prod_pow]
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hc.ne']
  refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
  have hprime := Nat.prime_of_mem_primeFactors hp
  exact Nat.pow_dvd_pow p ((hprime.pow_dvd_iff_le_factorization hc.ne').mp (hpow p hp))
