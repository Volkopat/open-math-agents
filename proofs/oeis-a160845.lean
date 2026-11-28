import OMAStatements.S_oeis_a160845
import Mathlib

open OMA.S_oeis_a160845

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a160845.main) := by
  intro h
  have h0 := h.2 1
  revert h0
  decide +kernel
