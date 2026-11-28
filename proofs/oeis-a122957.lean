import OMAStatements.S_oeis_a122957

-- Credit: @tjgksruf9801 (shorter proof). Counterexample m = 22: phi 21 = 12 > phi 22 = 10, so
-- A066362 21 = 22, but phi 30 = 8 < phi 22, so 22 is not a term of A122957.

open OMA.S_oeis_a122957 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a122957.main) := fun H => by
  have h : A066362 21 = 22 := by
    rw [A066362, dif_pos ⟨22, by decide, by decide⟩, Nat.find_eq_iff]
    exact ⟨⟨by decide, by decide⟩, fun k hk h => absurd h.1 (by omega)⟩
  have := ((H 22).2 ⟨by decide, 21, by decide, h⟩).1.2 30 (by decide)
  revert this
  decide
