import OMAStatements.S_oeis_a111883
import Mathlib

open OMA.S_oeis_a111883

theorem OMA.solution : type_of% @OMA.S_oeis_a111883.main := by
  rintro (_|_|_|m) hn
  iterate 3 omega
  simp [a, involutions]
  push_cast
  ring
