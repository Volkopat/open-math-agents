import OMAStatements.S_oeis_a289242
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a289242.main) := by
  intro h
  have h22 := h 22
  have e1 : ((OMA.S_oeis_a289242.w 22).length : ℤ) = 268184 := by decide +kernel
  have e2 : OMA.S_oeis_a289242.A289004 22 = 268182 := by decide +kernel
  rw [e1, e2] at h22
  norm_num at h22
