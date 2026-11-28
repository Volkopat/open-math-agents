import OMAStatements.S_oeis_a270684

open OMA.S_oeis_a270684

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270684.main) := fun ⟨_, _, o, r, _⟩ => by
  have := r 5 (by decide)
  norm_num [o 5 (by decide) (by decide), o 3 (by decide) (by decide), show a 1 = 7 by decide] at this
