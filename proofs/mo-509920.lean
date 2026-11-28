import OMAStatements.S_mo_509920

/-! Disproof: for `n = 0` and `S = ∅` the Zeckendorf list is empty, so the target type
`Fin 0` is empty and no map `g : ℕ → Fin 0` exists. -/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_509920.main) := by
  intro h
  obtain ⟨g, _⟩ := h 0 ∅ (by simp) (by simp)
  have h0 : (Nat.zeckendorf 0).length = 0 := by simp
  exact (Fin.cast h0 (g 0)).elim0
