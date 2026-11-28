import OMAStatements.S_oeis_a051397
import Mathlib.Tactic.Ring

theorem OMA.solution : type_of% @OMA.S_oeis_a051397.main := by
  rintro (_ | _ | m) h
  · omega
  · omega
  simp [OMA.S_oeis_a051397.a]
  push_cast
  ring
