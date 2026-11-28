import OMAStatements.S_oeis_a270684

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270684.main) := by
  rintro ⟨_, _, hodd, hrec, _⟩
  have h5 := hrec 5 (by decide)
  have v5 : OMA.S_oeis_a270684.a 5 = 8 := hodd 5 (by decide) (by decide)
  have v3 : OMA.S_oeis_a270684.a 3 = 8 := hodd 3 (by decide) (by decide)
  have v1 : OMA.S_oeis_a270684.a 1 = 7 := by decide
  norm_num [v5, v3, v1] at h5
