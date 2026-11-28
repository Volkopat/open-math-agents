import OMAStatements.S_oeis_a285643

-- Credit: @tjgksruf9801 (shorter proof). The recurrence conjunct fails at n = 5: a 5 = 111100,
-- while the right side is 110100. Both sides are computed by the kernel from the automaton.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285643.main) := fun h =>
  absurd (h.2.2.2 5 (by decide)) (by decide +kernel)
