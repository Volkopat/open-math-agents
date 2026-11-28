import OMAStatements.S_oeis_a244628
theorem OMA.solution : type_of% @OMA.S_oeis_a244628.main := by
  intro p hp hm
  have := Fact.mk hp
  have hs : legendreSym p 2 = -1 := by
    rw [legendreSym.at_two (by omega), ZMod.χ₈_nat_eq_if_mod_eight, show p % 2 = 1 by omega]
    rcases hm with h | h <;> simp [h]
  have h : ((2 ^ ((p - 1) / 2) : ℕ) : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by
    rw [Nat.cast_sub hp.one_lt.le, ZMod.natCast_self, Nat.cast_one, zero_sub]
    simpa [hs, show (p - 1) / 2 = p / 2 by omega] using (legendreSym.eq_pow p 2).symm
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast_of_lt (Nat.sub_lt hp.pos one_pos)] at this
