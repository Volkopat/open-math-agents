import OMAReductions.R_mo_342377_R1

theorem OMA.solution : OMA.R_mo_342377_R1.H2 := by
  intro a c ha hc h
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  simp [Nat.ascFactorial, show b + 2 - 1 = b + 1 by omega] at h
  rcases le_or_gt (2 * b + 5) (2 * (c ^ 2 + 3 * c + 1)) with h' | h' <;> nlinarith
