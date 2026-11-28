import OMAStatements.S_oeis_a062397

lemma OMA.a062397_geom_mod (x d q : ℕ) (h : x % d = 1 % d) :
    (∑ i ∈ Finset.range q, x ^ i) % d = q % d := by
  rw [Finset.sum_nat_mod]
  have hi : ∀ i ∈ Finset.range q, x ^ i % d = 1 % d := fun i _ => by
    rw [Nat.pow_mod, h, ← Nat.pow_mod, one_pow]
  rw [Finset.sum_congr rfl hi, Finset.sum_const, Finset.card_range, smul_eq_mul,
    Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_one]

lemma OMA.a062397_not_prime_pow (n x q : ℕ) (hq : q.Prime) : 10 ^ n + 1 ≠ x ^ q := by
  intro h
  by_cases hq2 : q = 2
  · subst hq2
    have h3 := congrArg (Nat.cast : ℕ → ZMod 3) h
    push_cast at h3
    rw [show (10 : ZMod 3) = 1 from rfl, one_pow] at h3
    generalize (x : ZMod 3) = y at h3
    revert y h3
    decide
  by_cases hq3 : q = 3
  · subst hq3
    have h9 := congrArg (Nat.cast : ℕ → ZMod 9) h
    push_cast at h9
    rw [show (10 : ZMod 9) = 1 from rfl, one_pow] at h9
    generalize (x : ZMod 9) = y at h9
    revert y h9
    decide
  have hq5 : 5 ≤ q := by
    have := hq.two_le
    rcases (show q = 4 ∨ 5 ≤ q by omega) with h4 | h4
    · subst h4; exact absurd hq (by decide)
    · exact h4
  have hx2 : 2 ≤ x := by
    rcases (show x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with h0 | h0 | h0
    · subst h0; rw [zero_pow hq.ne_zero] at h; exact absurd h (Nat.succ_ne_zero _)
    · subst h0; rw [one_pow] at h; have := Nat.one_le_pow n 10 (by norm_num); omega
    · exact h0
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : 2 ^ q ≤ x ^ q := Nat.pow_le_pow_left hx2 q
    have : 2 ^ 5 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq5
    simp at h; omega
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  set Φ := ∑ i ∈ Finset.range q, (y + 1) ^ i with hΦ
  have hgeom : Φ * y + 1 = (y + 1) ^ q := geom_sum_mul_add y q
  have hΦy : Φ * y = 10 ^ n := by omega
  -- x is odd
  have hxodd : (y + 1) % 2 = 1 := by
    have hodd : Odd ((y + 1) ^ q) := by
      rw [← h]
      have : Even (10 ^ n) := (Nat.even_pow' (by omega)).mpr (by decide)
      exact this.add_one
    have := (Nat.odd_pow_iff hq.ne_zero).mp hodd
    exact Nat.odd_iff.mp this
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  have hΦ2 : Φ % 2 = 1 := by
    rw [hΦ, OMA.a062397_geom_mod (y + 1) 2 q (by rw [hxodd]), hqodd]
  -- Φ is a power of 5
  have hΦdvd : Φ ∣ 5 ^ n * 2 ^ n := by
    rw [← mul_pow, show (5 : ℕ) * 2 = 10 by norm_num, ← hΦy]
    exact Dvd.intro y rfl
  have hcop : Nat.Coprime Φ (2 ^ n) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  have hΦ5 : Φ ∣ 5 ^ n := hcop.dvd_of_dvd_mul_right hΦdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hΦ5
  have hΦbig : (y + 1) ^ (q - 1) ≤ Φ :=
    Finset.single_le_sum (f := fun i => (y + 1) ^ i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
  have hpow4 : (y + 1) ^ 4 ≤ (y + 1) ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h16 : 2 ^ 4 ≤ (y + 1) ^ 4 := Nat.pow_le_pow_left hx2 4
  have hj2 : 2 ≤ j := by
    rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with h0 | h0 | h0
    · subst h0; simp at hj; omega
    · subst h0; simp at hj; omega
    · exact h0
  have h25 : 25 ∣ Φ := by
    rw [hj]; exact (pow_dvd_pow 5 hj2 : 5 ^ 2 ∣ 5 ^ j)
  -- x ≡ 1 mod 5
  have hx5 : (y + 1) % 5 = 1 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hz := congrArg (Nat.cast : ℕ → ZMod 5) h
    push_cast at hz
    rw [show (10 : ZMod 5) = 0 from rfl, zero_pow (by omega), zero_add] at hz
    set X : ZMod 5 := ((y + 1 : ℕ) : ZMod 5) with hX
    have hXq : X ^ q = 1 := by rw [hX]; push_cast; exact hz.symm
    have hX0 : X ≠ 0 := by
      intro h0; rw [h0, zero_pow (by omega)] at hXq; exact zero_ne_one hXq
    have hX4 : X ^ 4 = 1 := ZMod.pow_card_sub_one_eq_one hX0
    have hg : Nat.gcd q 4 = 1 := by
      have : Nat.Coprime q (2 ^ 2) :=
        Nat.Coprime.pow_right 2 ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
      simpa using this
    have hX1 : X = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hXq, hX4⟩
      rwa [hg, pow_one] at this
    have : ((y + 1 : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) := by rw [← hX, hX1, Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp this
  by_cases hq5' : q = 5
  · subst hq5'
    obtain ⟨s, hs⟩ : ∃ s, y + 1 = 5 * s + 1 := ⟨(y + 1) / 5, by omega⟩
    have hΦs : Φ = 5 + 25 * (2 * s + 10 * s ^ 2 + 25 * s ^ 3 + 25 * s ^ 4) := by
      rw [hΦ, hs]; simp [Finset.sum_range_succ]; ring
    omega
  · have hmod := OMA.a062397_geom_mod (y + 1) 5 q (by rw [hx5])
    have hq50 : q % 5 ≠ 0 := by
      intro h0
      exact hq5' ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hq).mp
        (Nat.dvd_of_mod_eq_zero h0)).symm
    rw [← hΦ] at hmod
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a062397.main := by
  rintro n ⟨m, k, hk, h⟩
  obtain ⟨q, hq, ⟨t, rfl⟩⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
  rw [OMA.S_oeis_a062397.a, mul_comm, pow_mul] at h
  exact OMA.a062397_not_prime_pow n (m ^ t) q hq h
