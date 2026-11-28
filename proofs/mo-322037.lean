import OMAStatements.S_mo_322037

-- The existing counterexample is the vector (0,1,2,0,0,2,1)/6.
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_322037.main) := by
  intro h
  have h := h 7 3 (by decide) (by decide) ![0,1/6,1/3,0,0,1/3,1/6]
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_succ])
  norm_num [OMA.S_mo_322037.quadratic, Fin.sum_univ_seven,
    Finset.sum_range_succ] at h
  dsimp only [Matrix.cons_val] at h
  norm_num at h
