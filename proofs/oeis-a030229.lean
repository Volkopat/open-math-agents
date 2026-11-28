import OMAStatements.S_oeis_a030229

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a030229.main) := by
  intro h
  have h1 := h 1 1 ⟨Nat.one_pos, squarefree_one, by simp⟩ le_rfl
  rw [show OMA.S_oeis_a030229.M 1 = 1 by ext i j; fin_cases i; fin_cases j; rfl, inv_one] at h1
  norm_num at h1
