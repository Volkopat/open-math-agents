import OMAStatements.S_oeis_a126364
import Mathlib

-- Problem: A126364, Number of base 10 n-digit numbers with adjacent digits differing by one or less.
-- Upstream: formal-conjectures statements/oeis-a126364.lean (declaration OMA.S_oeis_a126364.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Disproof: at n = 12 the proposed relation fails, as the statement's own documentation records:
-- a(12) = 1161634 while 3 a(11) - A025565(12) = 3 * 398746 - 34606 = 1161632. The three values
-- are computed by the kernel from the definitions.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a126364.main) := by
  intro h
  have h12 := h 12 (by decide)
  revert h12
  decide +kernel
