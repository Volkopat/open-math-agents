import OMAStatements.S_oeis_a330700

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a330700.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  simp [OMA.S_oeis_a330700.a, OMA.S_oeis_a330700.e2, OMA.S_oeis_a330700.M,
    Fin.sum_univ_two] at h2
