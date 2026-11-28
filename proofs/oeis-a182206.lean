import OMAStatements.S_oeis_a182206

open OMA.S_oeis_a182206

lemma ord {p : ℕ} (n : ℕ) {k : ℕ} (g : ZMod p) (hn : 0 < n)
    (h : g ^ n = 1 ∧ ∀ m < n, 0 < m → g ^ m ≠ 1) (hk : g ^ k = 1) : n ∣ k :=
  (orderOf_eq_iff hn).2 h ▸ orderOf_dvd_of_pow_eq_one hk

/-- From the Fermat property and a prime-modulus base `g` lift a congruence to `ZMod p`. -/
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

theorem OMA.solution : type_of% @OMA.S_oeis_a182206.main := by
  intro C hC h37 h73
  obtain ⟨hC1, -, hferm⟩ := hC
  have : NeZero C := ⟨by omega⟩
  have h2 := lift_base C 37 2 h37 (by norm_num) hferm
  have h5 := lift_base C 73 5 h73 (by norm_num) hferm
  push_cast at h2 h5
  obtain ⟨k1, hk1⟩ := ord 36 _ (by norm_num) ⟨by decide, by decide⟩ h2
  obtain ⟨k2, hk2⟩ := ord 72 _ (by norm_num) ⟨by decide, by decide⟩ h5
  obtain ⟨m, rfl⟩ : 37 * 73 ∣ C :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h37 h73
  have hm : m % 72 = 37 := by omega
  by_cases h37m : m = 37
  · subst h37m
    have h38 := lift_base _ 1369 38 (by norm_num) (by norm_num) hferm
    rw [show 37 * 73 * 37 - 1 = 37 * 2700 + 36 by norm_num, pow_add, pow_mul] at h38
    have e37 : ((38 : ℕ) : ZMod 1369) ^ 37 = 1 := by decide
    have e36 : ((38 : ℕ) : ZMod 1369) ^ 36 ≠ 1 := by decide
    rw [e37, one_pow, one_mul] at h38
    exact absurd h38 e36
  · refine ⟨(m - 91) / 18, ?_⟩
    omega
