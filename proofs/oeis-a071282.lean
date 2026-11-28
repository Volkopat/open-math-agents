import OMAStatements.S_oeis_a071282
import Mathlib.Tactic

open OMA.S_oeis_a071282 in
theorem OMA.solution : type_of% @OMA.S_oeis_a071282.main := by
  intro i
  have : i % 6 < 6 := Nat.mod_lt _ (by omega)
  simp only [denominatorAt, S_oeis_a071282.peirce, expandStream]
  split_ifs <;> (interval_cases h : i % 6 <;> first | rfl | omega)
