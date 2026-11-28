import OMAStatements.S_oeis_a177680

theorem OMA.solution : type_of% @OMA.S_oeis_a177680.main := by
  rintro n ⟨⟨p, hp, hp2, hpe⟩, q, hq, hq2, hqe⟩ hn
  have := hp.eq_one_or_self_of_dvd 5
  have := hp2.eq_one_or_self_of_dvd 5
  have := hq.eq_one_or_self_of_dvd 5
  have := hq2.eq_one_or_self_of_dvd 5
  rcases (by omega : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4) with
    h | h | h | h | h <;> omega
