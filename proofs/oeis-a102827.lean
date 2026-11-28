import OMAStatements.S_oeis_a102827

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a102827.main) :=
  fun h => h 10 (by decide) 332 (by decide +kernel)
