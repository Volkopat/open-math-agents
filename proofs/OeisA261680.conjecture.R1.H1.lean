import OMAReductions.R_OeisA261680_conjecture_R1

-- Step OeisA261680.conjecture.R1.H1: hypothesis H1 of reduction OeisA261680.conjecture.R1
-- Credit: @ysanatomic

theorem OMA.solution : OMA.R_OeisA261680_conjecture_R1.H1 := by
  intro n hn
  have hn' := Finset.mem_range.mp hn
  interval_cases n <;> decide +kernel

