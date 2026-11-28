import OMAStatements.S_oeis_a016789

-- Problem: oeis-a016789
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

theorem OMA.solution : type_of% @OMA.S_oeis_a016789.main := by
  intro y
  have cube : ((y : ℤ) ^ 3) % 3 = (y : ℤ) % 3 := by
    apply (ZMod.intCast_eq_intCast_iff' ((y : ℤ) ^ 3) y 3).mp
    push_cast
    exact ZMod.pow_card _
  have modEq (z : ℤ) : (∃ k : ℤ, z = 3 * k + 2) ↔ z % 3 = 2 :=
    ⟨fun ⟨k, hk⟩ => by omega, fun hz => ⟨z / 3, by omega⟩⟩
  rw [modEq, cube]
  unfold OMA.S_oeis_a016789.a
  exact ⟨fun ⟨n, hn⟩ => by omega, fun h => ⟨y / 3, by omega⟩⟩
