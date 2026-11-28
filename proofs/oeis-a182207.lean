import OMAStatements.S_oeis_a182207

open OMA.S_oeis_a182207

lemma lift_base (C p g : ℕ) [NeZero C] (hp : p ∣ C) (hg : g.Coprime p)
    (hferm : ∀ b : ℕ, b.Coprime C → b ^ (C - 1) ≡ 1 [MOD C]) :
    (g : ZMod p) ^ (C - 1) = 1 := by
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (n := p) hp (ZMod.unitOfCoprime g hg)
  have hcop := ZMod.val_coe_unit_coprime u
  have hmod := (hferm _ hcop).of_dvd hp
  rw [← ZMod.natCast_eq_natCast_iff] at hmod
  push_cast at hmod
  have hval : (((u : ZMod C).val : ℕ) : ZMod p) = g := by
    rw [ZMod.natCast_val]
    have := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) hu
    simpa [ZMod.unitsMap] using this
  rw [hval] at hmod
  exact hmod

lemma korselt_dvd (C q : ℕ) [NeZero C] (hq : q.Prime) (hqC : q ∣ C)
    (hferm : ∀ b : ℕ, b.Coprime C → b ^ (C - 1) ≡ 1 [MOD C]) : q - 1 ∣ C - 1 := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod q)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hu
  have hcop : (u : ZMod q).val.Coprime q := ZMod.val_coe_unit_coprime u
  have h := lift_base C q _ hqC hcop hferm
  rw [ZMod.natCast_val, ZMod.cast_id] at h
  have h2 : u ^ (C - 1) = 1 := by
    ext
    simpa using h
  rw [← hu]
  exact orderOf_dvd_of_pow_eq_one h2

theorem OMA.solution : type_of% @OMA.S_oeis_a182207.main := by
  intro C p hC hp hq hpC hqC
  obtain ⟨hC1, -, hferm⟩ := hC
  have : NeZero C := ⟨by omega⟩
  have hd := korselt_dvd C _ hq hqC hferm
  have h2 := hp.two_le
  obtain ⟨k, hk⟩ := hd
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · subst h
      obtain ⟨c, hc⟩ := hpC
      omega
    · exact h
  obtain ⟨t, rfl⟩ : ∃ t, p = 2 * t + 1 := ⟨p / 2, by omega⟩
  have ht : 1 ≤ t := by omega
  have e1 : 2 * (2 * t + 1) - 1 = 4 * t + 1 := by omega
  have e2 : 2 * (2 * t + 1) - 2 = 4 * t := by omega
  rw [e1] at hq hqC hk ⊢
  rw [e2]
  rw [show 4 * t + 1 - 1 = 4 * t by omega] at hk
  obtain ⟨m, rfl⟩ : (2 * t + 1) * (4 * t + 1) ∣ C :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((Nat.coprime_primes hp hq).2 (by omega)) hpC hqC
  have hk' : ((2 * t + 1 : ℕ) : ℤ) * (4 * t + 1) * m - 1 = 4 * t * k := by
    have h0 : 1 ≤ (2 * t + 1) * (4 * t + 1) * m := by omega
    have := congrArg (fun x : ℕ => (x : ℤ)) hk
    push_cast [Nat.cast_sub h0] at this
    push_cast
    linarith
  have hmod : (2 * t + 1) ≡ m [MOD 4 * t] := by
    rw [Nat.modEq_iff_dvd]
    refine ⟨(2 * t + 1) * k - (1 + (t + 1) * (4 * t + 1)) * m, ?_⟩
    push_cast at hk' ⊢
    linear_combination (2 * (t:ℤ) + 1) * hk'
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt (by omega)] at hmod
  refine ⟨m / (4 * t), ?_⟩
  have := Nat.div_add_mod m (4 * t)
  rw [← hmod] at this
  rw [mul_comm (m / (4 * t)), this]
