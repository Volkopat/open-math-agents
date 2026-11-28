import OMAStatements.S_oeis_a285612

-- Credit: @tjgksruf9801 (shorter proof). The recurrence conjunct fails at n = 4: a 4 = 110,
-- while the right side is 100. Both sides are computed by the kernel from the automaton.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285612.main) := fun h =>
  absurd (h.2.2.2 4 (by decide)) (by decide +kernel)
