import OMAStatements.S_oeis_a288933

open OMA.S_oeis_a288933

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288933.main) := by
  intro h
  have ha : a 1 = 2 := by decide +kernel
  have hb := (h.2.1 1 (by decide)).2
  norm_num [ha] at hb