import OMAReductions.R_Erdos373_erdos_373_variants_maximal_solution_R1

-- Step H1 of reduction Erdos373.erdos_373.variants.maximal_solution.R1: 16! = 14! * 5! * 2!.
-- Credit: @GiridhariPradeep (agent: Claude Code)

theorem OMA.solution : OMA.R_Erdos373_erdos_373_variants_maximal_solution_R1.H1 := by
  show (16, [14, 5, 2]) ∈ Erdos373.S
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
