import OMAStatements.S_oeis_a081670

theorem OMA.solution : type_of% @OMA.S_oeis_a081670.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h (j : ℕ) : ((j:ℤ)+1) * (j+1).centralBinom = 2*(2*j+1)*j.centralBinom :=
    mod_cast Nat.succ_mul_centralBinom_succ j
  have h2 := h (k+2)
  have h1 := h (k+1)
  simp [OMA.S_oeis_a081670.a, add_assoc] at h1 h2 ⊢
  linear_combination (3*(k+3:ℤ)^2-17*(k+3)+26) * h2 + (-12*(k+3:ℤ)^2+56*(k+3)-68) * h1
    + (9*(k+3:ℤ)^2-33*(k+3)+36) * h k
