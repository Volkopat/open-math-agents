import OMAStatements.S_oeis_a268554

theorem OMA.solution : type_of% @OMA.S_oeis_a268554.main := by
  rintro (_ | m) hn
  · omega
  rw [Nat.add_sub_cancel]
  unfold OMA.S_oeis_a268554.a
  rw [show 4 * (m + 1) = 4 * m + 3 + 1 by ring, show 3 * (m + 1) = 3 * m + 2 + 1 by ring,
    show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring
