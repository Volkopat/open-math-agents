import FormalConjectures.Wikipedia.Mersenne

theorem OMA.solution : type_of% @Mersenne.sq_dvd_mersenne_iff_isWieferichPrime := by
  intro q p hq hp hdvd
  unfold mersenne at hdvd ⊢
  have h1 : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    by_contra h
    have : p = 2 := by omega
    subst this
    have : 2 ∣ 2 ^ q := dvd_pow_self 2 hq.ne_zero
    omega
  have := Fact.mk hp
  have := Fact.mk hq
  have hz : (2 : ZMod p) ^ q = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (2 ^ q) 1 p).2 ((Nat.modEq_iff_dvd' h1).2 hdvd).symm
  have hne1 : (2 : ZMod p) ≠ 1 := fun h => by
    have : (2 : ℕ) ≡ 1 [MOD p] :=
      (ZMod.natCast_eq_natCast_iff 2 1 p).1 (by simpa only [Nat.cast_ofNat, Nat.cast_one] using h)
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hne0 : (2 : ZMod p) ≠ 0 := fun h => by
    have := Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 2 p).1 (by simpa only [Nat.cast_ofNat] using h))
    omega
  obtain ⟨m, hm⟩ : q ∣ p - 1 := orderOf_eq_prime hz hne1 ▸ ZMod.orderOf_dvd_card_sub_one hne0
  rw [IsWieferichPrime, isWieferichPrimeBase_iff_pow_modEq (by norm_num)]
  refine ⟨fun h2 => ⟨hp, ?_⟩, fun ⟨_, hw⟩ => ?_⟩
  · rw [hm, pow_mul]
    simpa only [one_pow] using (((Nat.modEq_iff_dvd' h1).2 h2).symm).pow m
  · obtain ⟨k, hk⟩ := hdvd
    have h2q : 2 ^ q = 1 + p * k := by omega
    have hpow : ∀ n : ℕ, (1 + p * k) ^ n ≡ 1 + n * (p * k) [MOD p ^ 2] := by
      intro n
      induction n with
      | zero => simp only [pow_zero, zero_mul, add_zero, Nat.ModEq.refl]
      | succ n ih =>
        rw [pow_succ]
        refine (ih.mul_right _).trans ?_
        rw [Nat.ModEq, show (1 + n * (p * k)) * (1 + p * k) = 1 + (n + 1) * (p * k) + p ^ 2 * (n * k ^ 2) by ring,
          Nat.add_mul_mod_self_left]
    have hd : p ^ 2 ∣ m * (p * k) := by
      have hm1 : 1 + m * (p * k) ≡ 1 [MOD p ^ 2] :=
        (hpow m).symm.trans (by rw [← h2q, ← pow_mul, ← hm]; exact hw)
      simpa only [Nat.add_sub_cancel_left] using
        (Nat.modEq_iff_dvd' (by omega : 1 ≤ 1 + m * (p * k))).1 hm1.symm
    have hpmk : p ∣ m * k := by
      rw [sq, show m * (p * k) = p * (m * k) by ring] at hd
      exact (Nat.mul_dvd_mul_iff_left hp.pos).1 hd
    obtain ⟨t, rfl⟩ : p ∣ k := (hp.dvd_mul.1 hpmk).resolve_left fun hpm => by
      have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hm; omega
      have := Nat.le_of_dvd hm0 hpm
      have : m ≤ p - 1 := hm ▸ Nat.le_mul_of_pos_left m hq.pos
      omega
    exact ⟨t, by rw [hk]; ring⟩
