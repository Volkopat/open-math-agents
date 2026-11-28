import OMAStatements.S_oeis_a082994

-- The reverse of 288 is 882. Their product is 504², while 16² < 288 < 17².
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a082994.main) := by
  intro h
  exact (by decide +kernel : ¬ IsSquare (288 : ℕ))
    (h 288 (by decide) (by decide) (by decide) ⟨504, by decide⟩).1
