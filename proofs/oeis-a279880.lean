import OMAStatements.S_oeis_a279880

-- Credit: @tjgksruf9801 (shorter proof). The recurrence conjunct fails at n = 8: a 8 = 496,
-- while the right side is 464. Both sides are computed by the kernel from the automaton.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a279880.main) := fun h =>
  absurd (h.1 8 (by decide)) (by decide +kernel)
