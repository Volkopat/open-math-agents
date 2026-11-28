import OMAReductions.R_OeisA249609_conjecture_R1

-- Step OeisA249609.conjecture.R1.H1: hypothesis H1 of reduction OeisA249609.conjecture.R1
-- Credit: @Ciphore
-- H1 := ∀ n : ℕ, n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) → OeisA249609.a n = 0  /-- The open direction: a row is entirely odious only for those five indices. -/

theorem OMA.solution : OMA.R_OeisA249609_conjecture_R1.H1 := by
  intro n hn
  simp at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
