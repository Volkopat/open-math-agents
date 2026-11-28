import OMAStatements.S_oeis_a288710

-- Problem: A288710: 0-limiting word of the mapping 00->1000, 10->0001, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a288710.lean:0 (declaration OMA.S_oeis_a288710.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Disproof: the iterate w(3) = 10000100011000 (listed in the entry) has 14 letters, while
-- A288925(3) = 13.

open OMA.S_oeis_a288710 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288710.main) := by
  intro h
  have h3 := h 3
  have e1 : (w 3).length = 14 := by decide
  have e2 : A288925 3 = 13 := rfl
  rw [e1, e2] at h3
  norm_num at h3
