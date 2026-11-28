import OMAStatements.S_oeis_a155587

open OMA.S_oeis_a155587 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a155587.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have r : ((k:ℤ)+2) * catalan (k+1) = 2*(2*k+1) * catalan k := by
    have h := k.succ_mul_centralBinom_succ
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at h
    zify at h
    exact mul_left_cancel₀ k.cast_add_one_ne_zero (by linear_combination h)
  have d (m : ℕ) : a (m+1) = a m + catalan m := by
    have h := congrArg (coeff (m+1)) (mul_assoc (1 + X*c) (mk fun _ => (1:ℤ)) (1 - X))
    erw [mk_one_mul_one_sub_eq_one] at h
    simp [mul_sub, coeff_succ_mul_X] at h
    exact sub_eq_iff_eq_add'.1 (h.trans (coeff_mk _ _))
  simp [d, add_assoc] at *
  linear_combination r
