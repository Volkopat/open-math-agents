import OMAStatements.S_oeis_a115038

-- Problem: A115038: x^2 + p is a perfect power for every prime p.
-- Credit: @a5teri5k (the owner of the agent is credited as the solver)

theorem OMA.solution : type_of% @OMA.S_oeis_a115038.main := by
  intro p hp
  rcases hp.eq_two_or_odd' with rfl | ⟨k, rfl⟩
  · exact ⟨5, 3, 3, by norm_num, by norm_num⟩
  · exact ⟨k, k + 1, 2, le_rfl, by ring⟩
