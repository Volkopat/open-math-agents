import OMAStatements.S_mo_261486
import Mathlib

-- Problem: mo-261486, is v_q (d(n)) <= 2 for every prime q, where
-- d(n) = n^(n-1) + (-1)^(n+1) (n-1)^(n-1)?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For n = 136 the number d(136) = 136^135 - 135^135 is divisible by 11^3 = 1331.
-- (Found by a direct search; further examples are (n, q) = (279, 5), (346, 13), (347, 5).)

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_261486.main) := by
  intro h
  have key : ((11 : ℕ) : ℤ) ^ 3 ∣ OMA.S_mo_261486.d 136 := by
    unfold OMA.S_mo_261486.d
    first
      | decide +kernel
      | norm_num
  exact h 136 (by norm_num) 11 (by norm_num) key
