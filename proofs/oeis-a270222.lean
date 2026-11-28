import OMAStatements.S_oeis_a270222

open OMA.S_oeis_a270222

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270222.main) := by
  intro h
  have hf := h.2.1 0
  have h0 : a 0 = 1 := by decide
  rw [h0] at hf
  norm_num at hf
