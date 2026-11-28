import OMAStatements.S_oeis_a201686

theorem OMA.solution : type_of% @OMA.S_oeis_a201686.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have u (i : ℕ) : ((2*i+1) * (2*i).choose i : ℤ) = (2*i+1).choose i * (i+1) := by
    rw [← Nat.choose_symm_half]
    exact_mod_cast Nat.add_one_mul_choose_eq (2*i) i
  have q (i : ℕ) : ((2*i+2).choose (i+1) : ℤ) = 2 * (2*i+1).choose i := by
    rw [Nat.choose_succ_succ', Nat.choose_symm_half]
    push_cast
    ring
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · have u0 := u i
    have q0 := q i
    have q1 := q (i+1)
    simp [OMA.S_oeis_a201686.a, mul_add, add_assoc, show ∀ c, (2*i+c)/2 = i + c/2 by omega] at *
    linear_combination -4*u0 +(-6*i-5)*q0 +(2*i+5)*q1
  · have u1 := u (i+1)
    have u2 := u (i+2)
    have q0 := q i
    have q1 := q (i+1)
    simp [OMA.S_oeis_a201686.a, mul_add, add_assoc, show ∀ c, (2*i+c)/2 = i + c/2 by omega] at *
    linear_combination (4*i+4)*q0 +6*u1 -2*q1 -2*u2
