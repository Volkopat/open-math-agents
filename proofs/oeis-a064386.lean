import OMAStatements.S_oeis_a064386
import Mathlib

open OMA.S_oeis_a064386

set_option maxHeartbeats 400000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a064386.main) := by
  intro h
  have h0 := h.2.2 1
  revert h0
  decide +kernel
