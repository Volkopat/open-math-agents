import OMAStatements.S_mse_3193902

theorem OMA.solution : type_of% @OMA.S_mse_3193902.main := by
  intro b _
  refine ⟨1, le_rfl, ?_⟩
  simpa only [one_pow] using (show (Nat.digits 10 1).sum = 1 from by decide +kernel)