import OMAReductions.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1

theorem OMA.solution : OMA.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1.H2 := by
  intro n hn hnp
  have h := Nat.minFac_sq_le_self (by omega) hnp
  have e := Nat.div_mul_cancel n.minFac_dvd
  have := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Nat.mem_properDivisors.2
    ⟨Nat.div_dvd_of_dvd n.minFac_dvd, Nat.div_lt_self (by omega) (Nat.minFac_prime (by omega)).one_lt⟩)
  rw [Erdos955.s, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self,
    Nat.add_sub_cancel]
  simp only [id] at this
  have : n.minFac ≤ n / n.minFac := Nat.le_of_mul_le_mul_right (by nlinarith) n.minFac_pos
  nlinarith
