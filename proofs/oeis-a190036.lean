import OMAStatements.S_oeis_a190036
import Mathlib

open OMA.S_oeis_a190036

set_option maxHeartbeats 0 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a190036.main) := by
  intro h
  have h1 := h.2 1
  revert h1
  decide +kernel
