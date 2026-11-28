import OMAStatements.S_oeis_a282803
open OMA.S_oeis_a282803 (a)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282803.main) := fun ⟨_, o, r, _⟩ => by
  have := r 5 (by decide)
  norm_num [o 5 (by decide) rfl, o 3 (by decide) rfl, show a 1 = 2 by decide +kernel] at this
