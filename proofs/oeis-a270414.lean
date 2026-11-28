import OMAStatements.S_oeis_a270414

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270414.main) := by
  intro h
  have h0 := (h 0).mp (fun h2 => absurd h2 (by norm_num))
  rcases h0 with h1 | ⟨h1, _⟩
  · exact absurd h1 (by norm_num)
  · exact Nat.not_prime_zero h1
