import OMAStatements.S_oeis_a005555

theorem OMA.solution : type_of% @OMA.S_oeis_a005555.main := fun H => by
  have h := congrArg PowerSeries.constantCoeff H
  norm_num [map_ofNat, OMA.S_oeis_a005555.a, OMA.S_oeis_a005555.terms] at h
