import OMAStatements.S_mo_267889
import Mathlib

-- Problem: mo-267889, is E|B \ A| = E|B| (1 - E|A| / n), where A is the set of values of m
-- uniform draws from n values and B the set of values of |A| further uniform draws?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For n = m = 2: E|A| = 3/2, E|B| = (1 + 3/2)/2 = 5/4 and E|B \ A| = (1/2 + 0)/2 = 1/4,
-- while (5/4) (1 - 3/4) = 5/16. The finite computation is checked by evaluation.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_267889.main) := by
  intro h
  have h22 := h 2 2 (by norm_num)
  revert h22
  decide +kernel
