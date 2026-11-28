import OMAReductions.R_OeisA259667_conjecture_1_R1

-- Evaluate the three finite cases through the factorial formula for Catalan numbers.
theorem OMA.solution : OMA.R_OeisA259667_conjecture_1_R1.H1 := by
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl <;>
    rw [OeisA259667.a, catalan_eq_centralBinom_div, Nat.centralBinom,
      Nat.choose_eq_factorial_div_factorial (by omega)] <;>
    decide +kernel
