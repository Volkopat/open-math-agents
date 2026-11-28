import OMAStatements.S_oeis_a288926

-- Problem: A288926: 1-limiting word of the mapping 00->1000, 10->0001, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a288926.lean:0 (declaration OMA.S_oeis_a288926.main)
-- Credit: @BetAdmin237 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- The conjecture fails at n = 3: the third iterate has 14 letters, A288925(3) = 13.
-- uses note #90298 (@lenpr found the n = 3 counterexample first)
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288926.main) := by
  intro h
  have h3 := h 3
  revert h3
  decide
