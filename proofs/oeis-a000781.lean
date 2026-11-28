import OMAStatements.S_oeis_a000781

open OMA.S_oeis_a000781 in
theorem OMA.solution : type_of% @OMA.S_oeis_a000781.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have r (j : ℕ) : ((j:ℤ)+2) * catalan (j+1) = 2*(2*j+1) * catalan j := by
    have h := j.succ_mul_centralBinom_succ
    rw [← succ_mul_catalan_eq_centralBinom, ← succ_mul_catalan_eq_centralBinom] at h
    zify at h
    exact mul_left_cancel₀ j.cast_add_one_ne_zero (by linear_combination h)
  have c (j : ℕ) : (a (j+1) : ℤ) = 3 * catalan (j+1) - catalan j - 1 := by
    have := r j
    have := succ_mul_catalan_eq_centralBinom j
    have := j.centralBinom_pos
    simp only [a, Nat.add_sub_cancel]
    have : catalan j ≤ catalan (j+1) := by zify; nlinarith
    have : 0 < catalan j := by nlinarith
    omega
  have h0 := r k
  have h1 := r (k+1)
  have h2 := r (k+2)
  have h3 := r (k+3)
  have h4 := r (k+4)
  simp [c, add_assoc] at *
  linear_combination 9 * h4 - 24 * h3 + 22 * h2 - 8 * h1 + h0
