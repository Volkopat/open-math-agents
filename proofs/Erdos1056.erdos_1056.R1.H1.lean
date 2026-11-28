import OMAReductions.R_Erdos1056_erdos_1056_R1

-- Step Erdos1056.erdos_1056.R1.H1: hypothesis H1 of reduction Erdos1056.erdos_1056.R1
-- Credit: @Raimo33

/-! Witness p = 11, b = (3, 5, 8): upstream `erdos_1056.variants.k2`. -/

theorem OMA.solution : OMA.R_Erdos1056_erdos_1056_R1.H1 := ⟨11, by norm_num, ![3, 5, 8], by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> omega,
  Erdos1056.erdos_1056.variants.k2⟩
