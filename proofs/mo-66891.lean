import OMAStatements.S_mo_66891

theorem OMA.solution : type_of% @OMA.S_mo_66891.main := by
  intro α _ μ A _ h
  exact MeasureTheory.measure_limsup_atTop_eq_zero h
