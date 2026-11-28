import OMAStatements.S_mo_308189
open Polynomial in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_308189.main) := by
  intro h
  obtain ⟨M, ⟨⟨w, hw, rfl⟩, -⟩, H⟩ := h (X + C 2) (by simp) fun w hw h0 => by
    rw [eval_add, eval_X, eval_C, add_eq_zero_iff_eq_neg] at h0; norm_num [h0] at hw
  have r : OMA.S_mo_308189.rotationBound (X + C 2) = 2 / 3 := by
    norm_num [OMA.S_mo_308189.rotationBound]
  have h1 := H 1 (-1) (by simp) (by simp)
  have h2 := norm_add_le w 2
  norm_num [r, hw] at h1 h2
  linarith
