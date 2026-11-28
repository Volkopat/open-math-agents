import OMAStatements.S_oeis_a282654

-- Credit: @tjgksruf9801 (shorter proof). The recurrence conjunct fails at n = 7: a 7 = 68,
-- while the right side is 64. Both sides are computed by the kernel from the automaton.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282654.main) := fun h =>
  absurd (h.1 7 (by decide)) (by decide +kernel)
