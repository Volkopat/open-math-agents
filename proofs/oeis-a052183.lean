import OMAStatements.S_oeis_a052183
import Mathlib

open OMA.S_oeis_a052183 in
theorem OMA.solution : type_of% @OMA.S_oeis_a052183.main := by
  intro t
  simp only [a, Nat.mul_add, Nat.reduceMul, ← Nat.factorial_mul_ascFactorial]
  norm_num [Nat.ascFactorial]
  field_simp
  ring
