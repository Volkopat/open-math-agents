import OMAStatements.S_oeis_a147803


open UniqueFactorizationMonoid in
theorem OMA.solution : type_of% @OMA.S_oeis_a147803.main := by
  intro n m hm hlt
  have hn : n ≠ 0 := by
    rintro rfl
    have : m = 0 := by simpa using hlt
    subst this
    norm_num at hm
  have h5 : Nat.Coprime (5 ^ n - m) 5 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)]
    intro hd
    have h55 : 5 ∣ 5 ^ n := dvd_pow_self 5 hn
    have : 5 ∣ m := by
      have := Nat.dvd_sub h55 hd
      rwa [Nat.sub_sub_self hlt.le] at this
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (by norm_num)] at hm
    exact hm this
  have hcop : Nat.Coprime (m * (5 ^ n - m)) (5 ^ n) :=
    Nat.Coprime.pow_right n (Nat.Coprime.mul_left hm h5)
  rw [radical_mul (Nat.coprime_iff_isRelPrime.mp hcop), radical_pow _ hn,
    radical_of_prime (a := (5 : ℕ)) (Nat.prime_iff.mp (by norm_num)), mul_comm]
  simp
