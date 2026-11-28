import OMAReductions.R_oeis_a083382_R1

/-! Row 0 is the prime 2 in (0, n] (n ≥ 2). Row 1 is Bertrand's postulate: a prime in (n, 2n]
(`Nat.exists_prime_lt_and_le_two_mul`). -/

theorem OMA.solution : OMA.R_oeis_a083382_R1.H1 := by
  intro n hn row hrow
  interval_cases row
  · exact ⟨2, Nat.prime_two, by omega, by omega⟩
  · obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
    exact ⟨p, hp, by omega, by omega⟩
