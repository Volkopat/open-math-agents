import OMAStatements.S_oeis_a075375

set_option maxRecDepth 20000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a075375.main) := by
  intro h
  have h169 := h 169 (by norm_num)
  have hval : OMA.S_oeis_a075375.a 169 = 164 := by decide +kernel
  rw [hval] at h169
  norm_num at h169
