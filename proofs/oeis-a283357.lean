import OMAStatements.S_oeis_a283357

-- Credit: @tjgksruf9801 (shorter proof). The recurrence fails at n = 7: a 7 = 190 but
-- a 6 + 4 * a 5 - 4 * a 4 = 186.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a283357.main) := fun h =>
  absurd (h.2.2 7 (by decide)) (by decide +kernel)
