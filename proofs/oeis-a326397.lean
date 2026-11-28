import OMAStatements.S_oeis_a326397
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a326397.main) := by
  intro h
  have h₁ := h.2.1 5 (by decide)
  have h₂ := h.2.2 5 (by decide)
  have e := h₁.symm.trans h₂
  norm_num at e