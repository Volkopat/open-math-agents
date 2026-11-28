import OMAStatements.S_oeis_a284482

-- Credit: @tjgksruf9801 (shorter proof). The recurrence conjunct fails at n = 7: a 7 = 247,
-- while the right side is 255. Both sides are computed by the kernel from the automaton.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284482.main) := fun h =>
  absurd (h.2 7 (by decide)) (by decide +kernel)
