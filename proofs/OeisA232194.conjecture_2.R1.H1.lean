import OMAReductions.R_OeisA232194_conjecture_2_R1

-- Step OeisA232194.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA232194.conjecture_2.R1
-- Credit: @Ciphore
-- H1 := ∀ n : ℕ, n ∈ ({3, 4, 6, 20, 24} : Finset ℕ) → OeisA232194.a n = 1  /-- The open direction: count one happens only at the five listed indices. -/

set_option maxHeartbeats 2000000000 in
set_option maxRecDepth 1000000 in
theorem OMA.solution : OMA.R_OeisA232194_conjecture_2_R1.H1 := by
  intro n hn
  simp at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
