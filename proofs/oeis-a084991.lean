import OMAStatements.S_oeis_a084991


theorem OMA.solution : type_of% @OMA.S_oeis_a084991.main := by
  refine ⟨fun k hk hodd => ⟨?_, ?_⟩, fun hG k hk hev h2 => ⟨hk, hG k hev h2⟩⟩
  · rintro ⟨-, p, q, hp, hq, rfl⟩
    rcases hp.eq_two_or_odd' with rfl | hpo
    · simpa using hq
    rcases hq.eq_two_or_odd' with rfl | hqo
    · simpa using hp
    exact absurd hodd (Nat.not_odd_iff_even.mpr (hpo.add_odd hqo))
  · intro hpr
    refine ⟨hk, 2, k - 2, Nat.prime_two, hpr, ?_⟩
    have := hpr.two_le
    omega
