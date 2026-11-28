import OMAStatements.S_oeis_a352844
theorem OMA.solution : type_of% @OMA.S_oeis_a352844.main := by
  intro n
  refine ⟨2 ^ (n + 1), Nat.one_lt_two_pow n.succ_ne_zero, ?_⟩
  simp [OMA.S_oeis_a352844.sopfr, Nat.primeFactors_prime_pow n.succ_ne_zero Nat.prime_two,
    Nat.divisors_prime_pow Nat.prime_two, Nat.prime_two.factorization_self]
  omega
