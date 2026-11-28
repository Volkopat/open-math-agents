import OMAStatements.S_oeis_a285666
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285666.main) := by
  intro h
  have := h 2 (by norm_num)
  revert this
  decide +kernel

