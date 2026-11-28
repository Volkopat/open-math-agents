import OMAReductions.R_Erdos1056_erdos_1056_R1

-- Step Erdos1056.erdos_1056.R1.H2: hypothesis H2 of reduction Erdos1056.erdos_1056.R1
-- Credit: @Raimo33

/-! Witness p = 17, b = (2, 6, 12, 16): upstream `erdos_1056.variants.k3`. -/

theorem OMA.solution : OMA.R_Erdos1056_erdos_1056_R1.H2 := ⟨17, by norm_num, ![2, 6, 12, 16], by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all <;> omega,
  Erdos1056.erdos_1056.variants.k3⟩
