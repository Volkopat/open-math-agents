import OMAStatements.S_oeis_a174525

theorem OMA.solution : type_of% @OMA.S_oeis_a174525.main := by
  rintro N ⟨r, rfl⟩ hodd hne
  obtain ⟨u, rfl⟩ := (Nat.odd_mul.1 hodd).1
  have hu : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; simp at hne)
  refine ⟨u * u, 4 * (u * u) + 2 * u + 1, by nlinarith, by nlinarith, by omega, by nlinarith,
    ⟨u * (2 * u + 1) + 1, by ring⟩, ⟨4 * (u * u) + 3 * u + 1, by ring⟩, fun h => ?_⟩
  nlinarith [show u * u < 4 * (u * u) + 2 * u + 1 by omega, show 1 < (2 * u + 1) * (2 * u + 1) by nlinarith]
