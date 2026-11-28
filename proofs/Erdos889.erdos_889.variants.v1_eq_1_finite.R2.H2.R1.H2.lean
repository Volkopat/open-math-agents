import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H2_R1

/-! The upper bound from the merged square reduction supplies a pair of
fresh primes above its effective threshold, for every middle exponent. -/

theorem OMA.solution : OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H2_R1.H2 := by
  refine ⟨0,2^(2^21),?_⟩
  intro p _ _ high _ _ _ _
  by_contra missing
  have big : 1<p^2 := lt_of_le_of_lt (@Nat.one_le_two_pow (2^21)) high
  have sol := Erdos889.Missing.predecessor_solution_of_missing big missing
  exact (Nat.not_lt_of_ge (Nat.le_sub_one_of_lt high)) (Erdos889.effective_binary_cutoff sol)
