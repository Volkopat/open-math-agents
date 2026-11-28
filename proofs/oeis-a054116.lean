import OMAStatements.S_oeis_a054116
import Mathlib

open OMA.S_oeis_a054116 in
theorem OMA.solution : type_of% @OMA.S_oeis_a054116.main := by
  rintro (_ | _ | _ | _ | m) h
  any_goals omega
  simp [a, Finset.sum_Icc_succ_top, Nat.factorial_succ]
  ring
