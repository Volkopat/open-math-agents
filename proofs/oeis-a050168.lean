import OMAStatements.S_oeis_a050168

theorem OMA.solution : type_of% @OMA.S_oeis_a050168.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have u (i : ℕ) : ((2*i+1) * (2*i).choose i : ℤ) = (2*i+1).choose i * (i+1) := by
    rw [← Nat.choose_symm_half]
    exact_mod_cast Nat.add_one_mul_choose_eq (2*i) i
  have q (i : ℕ) : ((2*i+2).choose (i+1) : ℤ) = 2 * (2*i+1).choose i := by
    rw [Nat.choose_succ_succ', Nat.choose_symm_half]
    push_cast
    ring
  rcases k with _ | k
  · simp [OMA.S_oeis_a050168.a, Nat.choose]
  have u1 := u (k/2+1)
  have q0 := q (k/2)
  have q1 := q (k/2+1)
  have w0 := (k/2).choose_symm_half
  have w1 := (k/2+1).choose_symm_half
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · have u0 := u i
    simp [OMA.S_oeis_a050168.a, mul_add, add_assoc, show ∀ c, (2*i+c)/2 = i + c/2 by omega] at *
    rw [w0, w1]
    linear_combination -4*u0 +(10*i+11)*q0 -8*u1 +(2*i+5)*q1
  · have u2 := u (i+2)
    simp [OMA.S_oeis_a050168.a, mul_add, add_assoc, show ∀ c, (2*i+c)/2 = i + c/2 by omega] at *
    rw [w0, w1]
    linear_combination (4*i+4)*q0 -10*u1 +(8*i+18)*q1 -2*u2
