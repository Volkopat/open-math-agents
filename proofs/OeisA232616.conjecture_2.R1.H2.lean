import OMAReductions.R_OeisA232616_conjecture_2_R1

-- Step OeisA232616.conjecture_2.R1.H2: hypothesis H2 of reduction OeisA232616.conjecture_2.R1
-- Credit: @JamesSlash. 2^5 - 5 = 27 = 3^3 and 2^7 - 7 = 121 = 11^2.

theorem OMA.solution : OMA.R_OeisA232616_conjecture_2_R1.H2 := by
  rintro x y n m - - - - (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> norm_num
