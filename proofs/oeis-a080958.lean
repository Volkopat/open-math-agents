import OMAStatements.S_oeis_a080958

open OMA.S_oeis_a080958 in
theorem OMA.solution : type_of% @OMA.S_oeis_a080958.main := by
  have s (n : ℕ) : a (n + 1) = (n + 1) * a n + (-1) ^ n * (n + 2) * n.factorial := by
    simp only [a, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rintro (_ | m) h
  · omega
  have h0 := s m
  have h1 := s (m + 1)
  push_cast [Nat.factorial_succ, add_tsub_cancel_right] at *
  linear_combination (-(m + 2 : ℚ)) * h1 - (m + 1 : ℚ) * (m + 3) * h0
