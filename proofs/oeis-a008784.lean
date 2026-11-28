import OMAStatements.S_oeis_a008784

theorem OMA.solution : type_of% @OMA.S_oeis_a008784.main := by
  intro k hk
  simp only [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_pow, Nat.cast_one,
    add_eq_zero_iff_eq_neg]
  constructor
  · rintro ⟨x, hx⟩
    let _ : NeZero k := ⟨by omega⟩
    exact ⟨x.val + k, by simpa [ZMod.natCast_self, ZMod.natCast_zmod_val] using hx,
      by
        have : 1 ≤ x.val + k := by omega
        nlinarith⟩
  · rintro ⟨m, hm, -⟩
    exact ⟨m, hm⟩
