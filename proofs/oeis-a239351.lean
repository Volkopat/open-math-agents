import OMAStatements.S_oeis_a239351

-- Credit: @tjgksruf9801 (shorter proof). The third known representation of 3 as a sum of
-- three cubes (Booker and Sutherland, 2019) is neither (1, 1, 1) nor (4, 4, -5).

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a239351.main) := fun h => by
  have := h (-472715493453327032) (-569936821113563493509) 569936821221962380720
    ⟨by decide, by decide, by decide⟩
  omega
