import OMAStatements.S_oeis_a002586


private def reducedExponent (p : ℕ) : ℕ :=
  (p - 1) / Nat.gcd 48 (p - 1)

private theorem noSmallResidue : ∀ p : Fin 257, 2 < (p : ℕ) → (p : ℕ).Prime →
    ((2 : ℕ) ^ (8 * reducedExponent p) % p ≠ ((p : ℕ) - 1) ^ reducedExponent p % p) ∧
    ((2 : ℕ) ^ (40 * reducedExponent p) % p ≠ ((p : ℕ) - 1) ^ reducedExponent p % p) := by
  decide +kernel

private theorem periodDvd (p : ℕ) : p - 1 ∣ 48 * reducedExponent p := by
  unfold reducedExponent
  let g := Nat.gcd 48 (p - 1)
  have hl : g * (48 / g) = 48 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hr : g * ((p - 1) / g) = p - 1 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  refine ⟨48 / g, ?_⟩
  change 48 * ((p - 1) / g) = (p - 1) * (48 / g)
  calc
    48 * ((p - 1) / g) = (g * (48 / g)) * ((p - 1) / g) := by rw [hl]
    _ = (g * ((p - 1) / g)) * (48 / g) := by ring
    _ = (p - 1) * (48 / g) := by rw [hr]

private theorem noSmallPrime (a k p : ℕ) (ha : a = 8 ∨ a = 40)
    (hp : p.Prime) (hsmall : p < 257) : ¬ p ∣ 2 ^ (a + 48 * k) + 1 := by
  intro hd
  have hpositive : a + 48 * k ≠ 0 := by rcases ha with h | h <;> omega
  by_cases hp2 : p = 2
  · subst p
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hpositive
    have hmod := Nat.mod_eq_zero_of_dvd hd
    rw [hr, pow_succ] at hmod
    omega
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  let _ : Fact p.Prime := ⟨hp⟩
  have hnz : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
    exact hp2 ((Nat.dvd_prime Nat.prime_two).1 hdiv |>.resolve_left hp.ne_one)
  have h0 := (ZMod.natCast_eq_zero_iff (2 ^ (a + 48 * k) + 1) p).2 hd
  push_cast at h0
  have h1 : (((p - 1 : ℕ) : ZMod p)) + 1 = 0 := by
    have he : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
    have hcast := congrArg (fun x : ℕ => (x : ZMod p)) he
    push_cast at hcast
    simpa using hcast
  have heq : (2 : ZMod p) ^ (a + 48 * k) = ((p - 1 : ℕ) : ZMod p) :=
    add_right_cancel (h0.trans h1.symm)
  obtain ⟨v, hv⟩ := periodDvd p
  have hcycle : (((2 : ZMod p) ^ 48) ^ k) ^ reducedExponent p = 1 := by
    calc
      (((2 : ZMod p) ^ 48) ^ k) ^ reducedExponent p =
          (2 : ZMod p) ^ ((48 * reducedExponent p) * k) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      _ = ((2 : ZMod p) ^ (p - 1)) ^ (v * k) := by rw [hv, Nat.mul_assoc, pow_mul]
      _ = 1 := by simp [ZMod.pow_card_sub_one_eq_one hnz]
  have hpow := congrArg (fun z : ZMod p => z ^ reducedExponent p) heq
  rw [pow_add, pow_mul (2 : ZMod p) 48 k, mul_pow, hcycle, mul_one, ← pow_mul] at hpow
  have hnat : 2 ^ (a * reducedExponent p) % p = (p - 1) ^ reducedExponent p % p := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ _).1
    push_cast
    exact hpow
  rcases ha with rfl | rfl
  · exact (noSmallResidue ⟨p, hsmall⟩ hp_gt hp).1 hnat
  · exact (noSmallResidue ⟨p, hsmall⟩ hp_gt hp).2 hnat

private theorem divides257 (j k : ℕ) : 257 ∣ 2 ^ (8 + 16 * j + 48 * k) + 1 := by
  apply (ZMod.natCast_eq_zero_iff _ _).1
  have h : (2 : ZMod 257) ^ 16 = 1 := by decide
  have h' : (2 : ZMod 257) ^ 8 + 1 = 0 := by decide
  have he : 8 + 16 * j + 48 * k = 8 + 16 * (j + 3 * k) := by omega
  push_cast
  rw [he, pow_add, pow_mul, h, one_pow, mul_one, h']

private theorem least257 (a k : ℕ) (ha : a = 8 ∨ a = 40)
    (hd : 257 ∣ 2 ^ (a + 48 * k) + 1) : (2 ^ (a + 48 * k) + 1).minFac = 257 := by
  let m := 2 ^ (a + 48 * k) + 1
  have hm : m ≠ 1 := by
    dsimp [m]
    have hpow : 0 < (2 : ℕ) ^ (a + 48 * k) := by positivity
    omega
  have hle : m.minFac ≤ 257 := Nat.minFac_le_of_dvd (by decide) hd
  have hnot : ¬ m.minFac < 257 := fun h =>
    noSmallPrime a k m.minFac ha (Nat.minFac_prime hm) h (Nat.minFac_dvd m)
  exact le_antisymm hle (Nat.le_of_not_gt hnot)

theorem OMA.solution : type_of% @OMA.S_oeis_a002586.main := by
  intro k
  unfold OMA.S_oeis_a002586.a
  refine ⟨least257 8 k (Or.inl rfl) ?_, least257 40 k (Or.inr rfl) ?_⟩
  · simpa using divides257 0 k
  · exact divides257 2 k

