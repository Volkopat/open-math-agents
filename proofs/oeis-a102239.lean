import OMAStatements.S_oeis_a102239

open OMA.S_oeis_a102239

theorem OMA.solution : type_of% @OMA.S_oeis_a102239.main := by
  have hs : ∀ n, s (n + 1) = 5 * s n + 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [s, Finset.sum_range_succ, pow_succ] at *
      omega
  intro n
  simp only [a, hs]
  rcases Nat.mod_two_eq_zero_or_one (s n) with h | h <;> omega
