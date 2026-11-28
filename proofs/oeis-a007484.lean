import OMAStatements.S_oeis_a007484

open OMA.S_oeis_a007484

theorem OMA.solution : type_of% @OMA.S_oeis_a007484.main := by
  intro n
  induction n using Nat.twoStepInduction <;> first | rfl | (simp only [a, b, c] at *; omega)
