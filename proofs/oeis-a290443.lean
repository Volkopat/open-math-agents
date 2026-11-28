import OMAStatements.S_oeis_a290443
import Mathlib

open OMA.S_oeis_a290443

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a290443.main) := by
  intro h
  have e := h 3 (by decide)
  have h2 : catalan 2 = 2 := by decide +kernel
  have h3 : catalan 3 = 5 := by decide +kernel
  norm_num [a, motzkin, h2, h3, catalan_one] at e