import OMAStatements.S_oeis_a009191

theorem OMA.solution : type_of% @OMA.S_oeis_a009191.main := by
  intro k hk
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (k + 1)
  have hpk : ¬ p ∣ k := fun h => by
    have hle := Nat.le_of_dvd hk h
    omega
  have hcop_kp : Nat.Coprime k p := (hp.coprime_iff_not_dvd.mpr hpk).symm
  have hcop_kpow : Nat.Coprime k (p ^ (k - 1)) := hcop_kp.pow_right (k - 1)
  have hcard_pos : 0 < k.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk.ne'⟩
  have hcard_le : k.divisors.card ≤ k := Nat.card_divisors_le_self k
  have hp_ndvd_card : ¬ p ∣ k.divisors.card := fun h => by
    have hle := Nat.le_of_dvd hcard_pos h
    omega
  have hcop_pcard : Nat.Coprime p k.divisors.card := hp.coprime_iff_not_dvd.mpr hp_ndvd_card
  have hcop_powcard : Nat.Coprime (p ^ (k - 1)) k.divisors.card := hcop_pcard.pow_left (k - 1)
  refine ⟨k * p ^ (k - 1), ?_⟩
  unfold OMA.S_oeis_a009191.a
  rw [hcop_kpow.card_divisors_mul]
  rw [Nat.divisors_prime_pow hp (k - 1), Finset.card_map, Finset.card_range]
  have hk_sub : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [hk_sub, mul_comm k.divisors.card k]
  rw [Nat.gcd_mul_left, hcop_powcard.gcd_eq_one, mul_one]
