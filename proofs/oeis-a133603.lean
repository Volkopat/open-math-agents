import OMAStatements.S_oeis_a133603

theorem OMA.solution : type_of% @OMA.S_oeis_a133603.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have r (j : ℕ) : ((j:ℤ)+2) * catalan (j+1) = 2*(2*j+1) * catalan j := by
    have h := j.succ_mul_centralBinom_succ
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at h
    zify at h
    exact mul_left_cancel₀ j.cast_add_one_ne_zero (by linear_combination h)
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · have r0 := r (2*i+1)
    have r1 := r (2*i+2)
    simp [OMA.S_oeis_a133603.a, add_assoc, show ∀ c, (2*i+c)%2 = c%2 by omega] at *
    linear_combination (96*i^3+296*i^2+252*i+56)*r0 +(24*i^3+80*i^2+82*i+24)*r1
  · have r0 := r (2*i+1)
    have r1 := r (2*i+2)
    have r2 := r (2*i+3)
    simp [OMA.S_oeis_a133603.a, add_assoc, show ∀ c, (2*i+c)%2 = c%2 by omega] at *
    linear_combination (96*i^3+488*i^2+796*i+420)*r0 +(120*i^3+568*i^2+834*i+378)*r1 +(24*i^3+116*i^2+180*i+88)*r2
