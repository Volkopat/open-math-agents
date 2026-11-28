import OMAStatements.S_oeis_a261681

theorem OMA.solution : type_of% @OMA.S_oeis_a261681.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have u (i : ℕ) : ((2*i+1) * (2*i).choose i : ℤ) = (2*i+1).choose i * (i+1) := by
    rw [← Nat.choose_symm_half]
    exact_mod_cast Nat.add_one_mul_choose_eq (2*i) i
  have q (i : ℕ) : ((2*i+2).choose (i+1) : ℤ) = 2 * (2*i+1).choose i := by
    rw [Nat.choose_succ_succ', Nat.choose_symm_half]
    push_cast
    ring
  have u1 := u (k/2+1)
  have q0 := q (k/2)
  have q1 := q (k/2+1)
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · have u0 := u i
    simp [OMA.S_oeis_a261681.a, mul_add, add_assoc, pow_succ, show ∀ c, (2*i+c)/2 = i + c/2 by omega] at *
    linear_combination (16*i+8)*u0 +(16*i^2+12*i-2)*q0 -(4*i+2)*u1 +(-4*i^2-10*i)*q1
  · have u2 := u (i+2)
    simp [OMA.S_oeis_a261681.a, mul_add, add_assoc, pow_succ, show ∀ c, (2*i+c)/2 = i + c/2 by omega] at *
    linear_combination (-16*i^2-32*i-16)*q0 -(16*i+8)*u1 +(4*i^2+18*i+12)*q1 +(4*i+2)*u2
