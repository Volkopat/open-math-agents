import OMAStatements.S_mo_217656
open OMA.S_mo_217656 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_217656.main) := by
  intro h
  obtain ⟨m, -, f, c⟩ := h 3 2 (by decide)
  let A : Selection 3 2 := ⟨{0, 1}, rfl⟩
  let B : Selection 3 2 := ⟨{0, 2}, rfl⟩
  let C : Selection 3 2 := ⟨{1, 2}, rfl⟩
  have s := c B A C ⟨2, by decide⟩
  rw [f C B 2 (by decide) (by decide)] at s
  have h0 := congrArg Subtype.val (f B A 0 (by decide) (by decide))
  have h1 := congrArg Subtype.val (f C A 1 (by decide) (by decide))
  rcases Finset.mem_insert.1 (m B A ⟨2, by decide⟩).2 with e | e
  · have := congrArg Subtype.val ((m B A).injective (Subtype.ext (e.trans h0.symm)))
    simp at this
  · have := congrArg Subtype.val ((m C A).injective (s.symm.trans (Subtype.ext ((Finset.mem_singleton.1 e).trans h1.symm))))
    simp at this
