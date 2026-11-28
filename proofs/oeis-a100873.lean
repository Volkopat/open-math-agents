import OMAStatements.S_oeis_a100873

/- Reduce the divisibility claim to the prime residue field and use `ZMod.pow_card`. -/

theorem OMA.solution : type_of% @OMA.S_oeis_a100873.main := by
  intro p _ hq
  have := Fact.mk hq
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.pow_card]
  exact_mod_cast ZMod.natCast_self (p + 2)
