import OMAReductions.R_OeisA1599_eq_one_of_odd_of_a_R1

theorem OMA.solution : OMA.R_OeisA1599_eq_one_of_odd_of_a_R1.H1 := by
  rintro n hn ⟨-, h⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, ArithmeticFunction.sigma_zero_apply_prime_pow hp,
    Finset.sum_range_succ'] at h
  simp only [pow_succ', ← Finset.mul_sum, pow_zero] at h
  have := Nat.le_of_dvd (by omega) ((((Nat.coprime_mul_left_add_left 1 p _).2
    (Nat.coprime_one_left p)).pow_right k).dvd_of_dvd_mul_left h)
  have := Finset.card_nsmul_le_sum (Finset.range k) (p ^ ·) 1 fun i _ => Nat.one_le_pow _ _ hp.pos
  simp at this
  nlinarith [hp.two_le]
