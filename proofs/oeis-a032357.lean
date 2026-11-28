import OMAStatements.S_oeis_a032357

open OMA.S_oeis_a032357 Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a032357.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have r (j : ℕ) : ((j:ℤ)+2) * catalan (j+1) = 2*(2*j+1) * catalan j := by
    have h := j.succ_mul_centralBinom_succ
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at h
    zify at h
    exact mul_left_cancel₀ j.cast_add_one_ne_zero (by linear_combination h)
  have d (j : ℕ) : a (j+1) = catalan (j+1) - a j := by
    rw [a, sum_range_succ, a, eq_sub_iff_add_eq', ← add_assoc, ← sum_add_distrib, sum_eq_zero] <;>
    simp +contextual [Nat.succ_sub, Nat.le_of_lt_succ, pow_succ]
  have := r (k+1)
  simp [d, add_assoc] at *
  linear_combination this
