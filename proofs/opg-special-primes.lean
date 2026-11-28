import OMAStatements.S_opg_special_primes

-- Problem opg-special-primes: for primes p, q with q = 1 (mod p),
-- 2^((q-1)/p) = 1 (mod q) if and only if p * ord_q(2) divides q - 1.
-- Upstream: statements/opg-special-primes.lean (declaration OMA.S_opg_special_primes.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: write q - 1 = p * m. Then (q-1)/p = m, and 2^m = 1 in Z/q exactly when the order of 2 divides m,
-- which is the same as p * ord dividing p * m = q - 1.

theorem OMA.solution : type_of% @OMA.S_opg_special_primes.main := by
  intro p q hp hq hqp
  have hdvd : p ∣ q - 1 := (Nat.modEq_iff_dvd' hq.one_lt.le).mp hqp.symm
  obtain ⟨m, hm⟩ := hdvd
  have hdiv : (q - 1) / p = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m hp.pos
  have key : (2 ^ m ≡ 1 [MOD q]) ↔ ((2 : ZMod q) ^ m = 1) := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  rw [hdiv, hm, Nat.mul_dvd_mul_iff_left hp.pos, orderOf_dvd_iff_pow_eq_one]
  exact key
