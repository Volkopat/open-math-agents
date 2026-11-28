import OMAStatements.S_mo_503437

open OMA.S_mo_503437

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_503437.main) := by
  intro h
  exact (by decide +kernel : ¬ 0 ≤ score 19104014532625) (h 19104014532625 (by decide)).1