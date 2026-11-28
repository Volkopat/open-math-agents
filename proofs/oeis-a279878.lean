import OMAStatements.S_oeis_a279878

-- Credit: @tjgksruf9801 (shorter proof). The recurrence conjunct fails at n = 8: a 8 = 111110000,
-- while the right side is 111010000. Both sides are computed by the kernel from the automaton.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a279878.main) := fun h =>
  absurd (h.1 8 (by decide)) (by decide +kernel)
