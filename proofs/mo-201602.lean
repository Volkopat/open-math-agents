import OMAStatements.S_mo_201602

-- Problem: Converse for Levy's continuity theorem
-- Upstream: formal-conjectures statements/mo-201602.lean:0 (declaration OMA.S_mo_201602.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @OMA.S_mo_201602.main := by
  intro laws law h
  exact MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 h
