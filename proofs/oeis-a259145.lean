import OMAStatements.S_oeis_a259145

theorem OMA.solution : type_of% @OMA.S_oeis_a259145.main := by
  intro k hp
  by_contra hc
  obtain ⟨p, pp, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  rcases k with _|_|k
  · norm_num at hp
  · simp at hc
  have := (Nat.prime_dvd_prime_iff_eq pp hp).1 (Nat.dvd_sub (dvd_pow h1 two_ne_zero) h2)
  have := Nat.totient_lt (k+1+1) (by omega)
  have := Nat.le_of_dvd (by omega) h1
  have : 2 * (k+1+1) ≤ (k+1+1) ^ 2 := by nlinarith
  omega
