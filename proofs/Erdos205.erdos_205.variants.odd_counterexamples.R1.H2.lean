import OMAReductions.R_Erdos205_erdos_205_variants_odd_counterexamples_R1

/-! The prime-factor count with multiplicity is monotone along divisibility. -/

theorem OMA.solution : OMA.R_Erdos205_erdos_205_variants_odd_counterexamples_R1.H2 := by
  rintro a _ hb ⟨c, rfl⟩
  rw [ArithmeticFunction.cardFactors_mul (left_ne_zero_of_mul hb) (right_ne_zero_of_mul hb)]
  exact Nat.le_add_right _ _
