import OMAStatements.S_mo_186002

-- The regularity identity makes 1 - a*x an annihilator; if it vanished, x would be an inverse.
theorem OMA.solution : type_of% @OMA.S_mo_186002.main := by
  intro R _ h a ha
  obtain ⟨x, hx⟩ := h a
  refine ⟨1 - a * x, fun e => ha (IsUnit.of_mul_eq_one x (sub_eq_zero.mp e).symm), ?_⟩
  linear_combination -hx
