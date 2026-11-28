import OMAStatements.S_oeis_a051960

theorem OMA.solution : type_of% @OMA.S_oeis_a051960.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have r (j : ℕ) : ((j:ℤ)+2) * catalan (j+1) = 2*(2*j+1) * catalan j := by
    have h1 := succ_mul_catalan_eq_centralBinom (j+1)
    have h2 := succ_mul_catalan_eq_centralBinom j
    have h3 := j.succ_mul_centralBinom_succ
    zify at h1 h2 h3
    exact mul_left_cancel₀ (by positivity : (j:ℤ)+1 ≠ 0) (by linear_combination (j+1)*h1 + h3 - 2*(2*j+1)*h2)
  have r1 := r (k+1)
  simp [OMA.S_oeis_a051960.a, add_assoc] at r1 ⊢
  linear_combination (3*k+8)*r1 + (6*k+4)*r k
