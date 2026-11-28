import OMAStatements.S_oeis_a180195

open OMA.S_oeis_a180195

theorem OMA.solution : type_of% @OMA.S_oeis_a180195.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rcases neg_one_pow_eq_or ℤ m with e | e <;>
    simp [a, b, e, pow_succ, Finset.sum_range_succ, Nat.factorial_succ,
      show m + 4 - 1 = m + 3 from rfl, show m + 4 - 2 = m + 2 from rfl,
      show m + 4 - 3 = m + 1 from rfl] <;> ring
