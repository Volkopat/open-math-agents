import OMAStatements.S_oeis_a005319

/-- At index zero the proposed identity would equate −1 with 3. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a005319.main) := by
  intro identity
  have atZero : (-1 : ℤ) = 3 := identity 0
  exact (by decide : (-1 : ℤ) ≠ 3) atZero
