import OMAStatements.S_oeis_a081205

open OMA.S_oeis_a081205 in
theorem OMA.solution : type_of% @OMA.S_oeis_a081205.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have c (m j t : ℕ) (h : (m+2)/2+(m+1) = t) (h2 : t - m = j) : (a m : ℚ) = t.factorial / (m.factorial * j.factorial) := by
    subst h h2
    exact Nat.cast_choose ℚ (by omega)
  qify
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [c (2*i+2) (i+3) (3*i+5) (by omega) (by omega), c (2*i+2-1) (i+2) (3*i+3) (by omega) (by omega), c (2*i+2-2) (i+2) (3*i+2) (by omega) (by omega)]
    simp [mul_add, Nat.factorial_succ]
    field_simp
    ring
  · rw [c (2*i+1+2) (i+3) (3*i+6) (by omega) (by omega), c (2*i+1+2-1) (i+3) (3*i+5) (by omega) (by omega), c (2*i+1+2-2) (i+2) (3*i+3) (by omega) (by omega)]
    simp [mul_add, Nat.factorial_succ]
    field_simp
    ring
