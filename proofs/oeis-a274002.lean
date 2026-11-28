import OMAStatements.S_oeis_a274002

theorem OMA.solution : type_of% @OMA.S_oeis_a274002.main := fun p =>
  ⟨fun ⟨a,q,b,c,d⟩ => ⟨a,q,b,c,fun k => pow_right_comm 4 _ k ▸ d.trans (Nat.sub_one_dvd_pow_sub_one _ k)⟩,
   fun ⟨a,q,b,c,d⟩ => ⟨a,q,b,c,pow_one 4 ▸ d 1⟩⟩
