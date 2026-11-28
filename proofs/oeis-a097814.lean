import OMAStatements.S_oeis_a097814

theorem OMA.solution : type_of% @OMA.S_oeis_a097814.main := by
  rintro (_ | _ | m) h
  · omega
  · omega
  simp [OMA.S_oeis_a097814.a]
  push_cast
  ring
