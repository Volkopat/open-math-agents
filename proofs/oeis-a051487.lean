import OMAStatements.S_oeis_a051487

-- The two factorizations come from Salem Levinstein's counterexample for A108569.
set_option maxRecDepth 8192 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a051487.main) := by
  intro h
  have hsmall : Nat.totient 5095354107 = 3393612288 := by
    rw [show 5095354107 = 3 * (1033 * 1644193) by decide,
      Nat.totient_mul (by decide : Nat.Coprime 3 (1033 * 1644193)),
      Nat.totient_mul (by decide : Nat.Coprime 1033 1644193),
      Nat.totient_prime (by norm_num : Nat.Prime 3),
      Nat.totient_prime (by norm_num : Nat.Prime 1033),
      Nat.totient_prime (by norm_num : Nat.Prime 1644193)]
  have hlarge : Nat.totient 8488966395 = 3393612288 := by
    rw [show 8488966395 = 3 * (5 * (7 * (13 * (19 * 327317)))) by decide,
      Nat.totient_mul (by decide : Nat.Coprime 3 (5 * (7 * (13 * (19 * 327317))))),
      Nat.totient_mul (by decide : Nat.Coprime 5 (7 * (13 * (19 * 327317)))),
      Nat.totient_mul (by decide : Nat.Coprime 7 (13 * (19 * 327317))),
      Nat.totient_mul (by decide : Nat.Coprime 13 (19 * 327317)),
      Nat.totient_mul (by decide : Nat.Coprime 19 327317),
      Nat.totient_prime (by norm_num : Nat.Prime 3),
      Nat.totient_prime (by norm_num : Nat.Prime 5),
      Nat.totient_prime (by norm_num : Nat.Prime 7),
      Nat.totient_prime (by norm_num : Nat.Prime 13),
      Nat.totient_prime (by norm_num : Nat.Prime 19),
      Nat.totient_prime (by norm_num : Nat.Prime 327317)]
  have heq : Nat.totient 8488966395 = Nat.totient (8488966395 - Nat.totient 8488966395) := by
    rw [hlarge]
    exact hsmall.symm
  exact (by decide : ¬ Even (8488966395 : ℕ)) (h 8488966395 (by decide) heq)
