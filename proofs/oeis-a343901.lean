import OMAStatements.S_oeis_a343901

theorem OMA.solution : type_of% @OMA.S_oeis_a343901.main := fun n hn =>
  (Set.ncard_pos ((Set.finite_Iic (n.totient + 1)).subset fun p hp => by
    have := Nat.le_of_dvd (Nat.totient_pos.2 (by omega)) hp.2
    show p ≤ n.totient + 1
    omega)).2 ⟨2, Nat.prime_two, one_dvd _⟩
