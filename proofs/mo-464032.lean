import OMAStatements.S_mo_464032

def OMA.cex : Equiv.Perm (Fin (2 * 3 + 1)) :=
  ⟨![2, 5, 0, 3, 6, 1, 4], ![2, 5, 0, 3, 6, 1, 4], by decide, by decide⟩

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_464032.main) := by
  intro h
  have := h 3 OMA.cex (by decide)
  revert this
  decide
