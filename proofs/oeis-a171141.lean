import OMAStatements.S_oeis_a171141

theorem OMA.solution : type_of% @OMA.S_oeis_a171141.main := by
  intro n hn hm p hp hq h
  have := Nat.mul_self_inj.1 (by nlinarith : (p + 1) * (p + 1) = (6 * n + 6) * (6 * n + 6))
  have := hp.eq_one_or_self_of_dvd 41
  have := hq.eq_one_or_self_of_dvd 41
  omega
