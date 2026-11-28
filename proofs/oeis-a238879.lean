import OMAStatements.S_oeis_a238879

-- Credit: @tjgksruf9801 (shorter proof). a 2 = T 0 2 + T 1 2 + T 2 2 = 2, but catalan 1 = 1.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a238879.main) := fun h => by
  have := h.1 1
  rw [catalan_one] at this
  revert this
  decide +kernel
