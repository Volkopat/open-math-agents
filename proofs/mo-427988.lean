import OMAStatements.S_mo_427988

-- Credit: @tjgksruf9801 (shorter proof). Same set A = {0, 1, 3, 5, 8, 20, 23, 25, 27, 28}:
-- A + A + A covers [0, 28] and [56, 84] but misses 42.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_427988.main) := fun h => by
  have := h 28 (by decide) {0, 1, 3, 5, 8, 20, 23, 25, 27, 28} (by decide +kernel)
    (by decide +kernel)
  revert this
  decide +kernel
