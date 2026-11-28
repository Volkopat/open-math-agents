import OMAReductions.R_Erdos936_erdos_936_variants_two_pow_sub_one_R1
import Mathlib

/-- Step Erdos936.erdos_936.variants.two_pow_sub_one.R1.H1. -/
theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_two_pow_sub_one_R1.H1 := by
  intro c hc hp
  rw [← Finset.prod_pow]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hc.ne']
  rw [Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hpf
  apply pow_dvd_pow
  exact ((Nat.prime_of_mem_primeFactors hpf).pow_dvd_iff_le_factorization hc.ne').mp (hp p hpf)
