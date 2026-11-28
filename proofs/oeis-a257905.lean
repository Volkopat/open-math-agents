import OMAStatements.S_oeis_a257905

open OMA.S_oeis_a257905

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a257905.main) := by
  intro h
  have hrepeat : (orbit 3 0 0).a = (orbit 3 0 2).a := by decide
  have heq : (0 : ℕ) = 2 := (h 3 0).1.1 hrepeat
  omega