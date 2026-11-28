import OMAStatements.S_oeis_a229159


theorem OMA.solution : type_of% @OMA.S_oeis_a229159.main := by
  intro p hp h2
  obtain ⟨k, rfl⟩ : Odd p := hp.odd_of_ne_two (by omega)
  have hk : 1 ≤ k := by omega
  refine ⟨2 * k + 1, 2 * k ^ 2 + 2 * k, 2 * k ^ 2 + 2 * k + 1, (2 * k + 1) * (k ^ 2 + k),
    Or.inl rfl, ?_⟩
  refine ⟨by omega, by positivity, by omega, by nlinarith, by nlinarith, by nlinarith,
    by positivity, ?_⟩
  push_cast
  ring
