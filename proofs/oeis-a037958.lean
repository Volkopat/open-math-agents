import OMAStatements.S_oeis_a037958

open OMA.S_oeis_a037958 in
theorem OMA.solution : type_of% @OMA.S_oeis_a037958.main := by
  intro n hn
  rcases lt_or_ge n 10 with h | h
  · interval_cases n <;> simp [a]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · have h1 := Nat.add_one_mul_choose_eq (2*i+9) i
    have h2 := Nat.choose_mul_succ_eq (2*i+8) i
    rw [show 2*i+8+1-i = i+9 by omega] at h2
    zify at h1 h2
    simp +arith [a, add_assoc, show ∀ c, (2*i+c)/2 = i + c/2 by omega] at *
    linear_combination 2*(2*i+19)*h1 + 4*(2*i+10)*h2
  · have h1 := Nat.choose_mul_succ_eq (2*i+10) (i+1)
    have h2 := Nat.add_one_mul_choose_eq (2*i+9) i
    rw [show 2*i+10+1-(i+1) = i+10 by omega] at h1
    zify at h1 h2
    simp +arith [a, add_assoc, show ∀ c, (2*i+c)/2 = i + c/2 by omega] at *
    linear_combination 2*(2*i+3)*h1 + 4*(2*i+11)*h2
