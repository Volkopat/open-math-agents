import OMAStatements.S_oeis_a085785

open OMA.S_oeis_a085785

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a085785.main) := by
  intro h
  obtain ⟨m, hm⟩ := h 1 le_rfl
  have hf : f (3 / 4) = 3 / 4 := by norm_num [f, Int.ceil_eq_iff]
  norm_num [Function.iterate_fixed hf] at hm
