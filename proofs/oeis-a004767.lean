import OMAStatements.S_oeis_a004767

theorem OMA.solution : type_of% @OMA.S_oeis_a004767.main := by
  intro m hm
  rw [Nat.odd_iff] at hm
  rw [Nat.odd_iff]
  constructor
  · rintro ⟨h1, _⟩
    exact ⟨m / 4, by unfold OMA.S_oeis_a004767.a; omega⟩
  · rintro ⟨n, rfl⟩
    unfold OMA.S_oeis_a004767.a
    omega
