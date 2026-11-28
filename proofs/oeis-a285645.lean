import OMAStatements.S_oeis_a285645
import Mathlib
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: the fourth conjunct (a n = 5 a(n-2) - 4 a(n-4) for n > 3) fails at n = 5:
-- direct kernel evaluation gives a 1 = 2, a 3 = 12, a 5 = 60, while 5*12 - 4*2 = 52.
-- (It also fails at n = 6 and n = 8; it holds for all n > 8.)

open OMA.S_oeis_a285645

set_option maxRecDepth 100000 in
theorem a_vals : a 1 = 2 ∧ a 3 = 12 ∧ a 5 = 60 := by decide +kernel

theorem main_disproof : ¬ (type_of% @OMA.S_oeis_a285645.main) := by
  intro h
  have := h.2.2.2 5 (by norm_num)
  obtain ⟨h1, h3, h5⟩ := a_vals
  norm_num [h1, h3, h5] at this


theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285645.main) := main_disproof
