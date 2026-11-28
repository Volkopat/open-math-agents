import OMAStatements.S_oeis_a112702

theorem OMA.solution : type_of% @OMA.S_oeis_a112702.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have r (j : ℕ) : ((j:ℤ)+2) * catalan (j+1) = 2*(2*j+1) * catalan j := by
    have h := j.succ_mul_centralBinom_succ
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at h
    zify at h
    exact mul_left_cancel₀ j.cast_add_one_ne_zero (by linear_combination h)
  have := r (k+1)
  simp [OMA.S_oeis_a112702.a, Finset.sum_range_succ, add_assoc, pow_succ] at *
  linear_combination 64*8^k*this
