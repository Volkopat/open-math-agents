import OMAStatements.S_oeis_a133602

open OMA.S_oeis_a133602 in
theorem OMA.solution : type_of% @OMA.S_oeis_a133602.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have r (j : ℕ) : ((j:ℤ)+2) * catalan (j+1) = 2*(2*j+1) * catalan j := by
    have h := j.succ_mul_centralBinom_succ
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at h
    zify at h
    exact mul_left_cancel₀ j.cast_add_one_ne_zero (by linear_combination h)
  have e (m : ℕ) : a (m+1) = (if m % 2 = 0 then catalan m else 0) + catalan (m+1) := by
    rw [a, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp [T, add_assoc]
    · intro x hx
      have := Finset.mem_range.1 hx
      rw [T, if_neg (by omega), if_neg (by omega), zero_mul]
  rcases k with _ | k
  · simp [a, T, Finset.sum_range_succ]
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · have r0 := r (2*i)
    have r1 := r (2*i+1)
    have r2 := r (2*i+2)
    simp [e, add_assoc, show ∀ c, (2*i+c)%2 = c%2 by omega] at *
    linear_combination (96*i^3+344*i^2+380*i+132)*r0 +(120*i^3+388*i^2+356*i+88)*r1 +(24*i^3+80*i^2+82*i+24)*r2
  · have r0 := r (2*i+2)
    have r1 := r (2*i+3)
    simp [e, add_assoc, show ∀ c, (2*i+c)%2 = c%2 by omega] at *
    linear_combination (96*i^3+440*i^2+620*i+268)*r0 +(24*i^3+116*i^2+180*i+88)*r1
