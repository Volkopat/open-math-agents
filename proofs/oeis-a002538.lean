import OMAStatements.S_oeis_a002538
import Mathlib

open OMA.S_oeis_a002538 in
theorem OMA.solution : type_of% @OMA.S_oeis_a002538.main := by
  rintro (_ | _ | _ | m) h
  any_goals omega
  simp [a, Nat.factorial_succ]
  ring
