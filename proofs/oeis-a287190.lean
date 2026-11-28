import OMAStatements.S_oeis_a287190

-- Credit: @tjgksruf9801 (shorter proof). The recurrence fails at n = 6: a 6 = 11 but
-- 101 * a 4 - 100 * a 2 = 1111.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a287190.main) := fun h =>
  absurd (h.2.2.2 6 (by decide)) (by decide +kernel)
