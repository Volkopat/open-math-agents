import OMAReductions.R_AgrawalConjecture_agrawal_conjecture_variants_popovych_R1

/-!
# Proof of `AgrawalConjecture.agrawal_conjecture.variants.popovych.R1.H1`

Proves that if `(X + 2) ^ n ≡ X ^ n + 2 (mod X ^ r - 1)` in `(ZMod n)[X]` (`n > 1`), then every
prime `p` with `p ^ 2 ∣ n` satisfies `p ≠ 3` and `(3 : ZMod (p ^ 2)) ^ (p - 1) = 1`.

1. Evaluating at `X = 1` kills the ideal `Ideal.span {X ^ r - 1}` (since `1 ^ r - 1 = 0`), yielding
   `(3 : ZMod n) ^ n = 3`.
2. Projecting along `ZMod n →+* ZMod (p ^ 2)` gives `(3 : ZMod (p ^ 2)) ^ n = 3`.
3. If `p = 3`, then `n ≥ 2` implies `(3 : ZMod 9) ^ n = 0 ≠ 3`, contradiction; hence `p ≠ 3`.
4. Thus `3` is a unit `u` in `ZMod (p ^ 2)` with `u ^ (n - 1) = 1`, so `orderOf u` divides both
   `n - 1` and `Nat.card (ZMod (p ^ 2))ˣ = p * (p - 1)`. Since `p ∣ n`, `p.Coprime (n - 1)`,
   whence `orderOf u ∣ p - 1` and `(3 : ZMod (p ^ 2)) ^ (p - 1) = 1`.
-/

theorem OMA.solution : OMA.R_AgrawalConjecture_agrawal_conjecture_variants_popovych_R1.H1 := by
  intro n r hn
  dsimp only
  intro hq p hp hp2
  -- Evaluate the quotient identity at X = 1 in ZMod n
  have hmem : (Polynomial.X + 2 : Polynomial (ZMod n)) ^ n -
      (Polynomial.X ^ n + 2 : Polynomial (ZMod n)) ∈
      Ideal.span ({Polynomial.X ^ r - 1} : Set (Polynomial (ZMod n))) := by
    rw [← Ideal.Quotient.eq]
    exact hq
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨g, hg⟩ := hmem
  have heval := congrArg (Polynomial.eval (1 : ZMod n)) hg
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_mul, Polynomial.eval_one, one_pow, sub_self,
    zero_mul] at heval
  have h3n_mod_n : (3 : ZMod n) ^ n = 3 := by
    have h12 : (1 : ZMod n) + 2 = 3 := by norm_num
    rw [h12] at heval
    exact sub_eq_zero.mp heval
  -- Project to ZMod (p ^ 2) via ZMod.castHom
  let proj : ZMod n →+* ZMod (p ^ 2) := ZMod.castHom hp2 (ZMod (p ^ 2))
  have h3n : (3 : ZMod (p ^ 2)) ^ n = 3 := by
    have := congrArg proj h3n_mod_n
    simpa [map_pow, map_ofNat] using this
  -- Part 1: p ≠ 3
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h9 : (3 : ZMod (3 ^ 2)) ^ n = 0 := by
      have hsplit : n = 2 + (n - 2) := by omega
      rw [hsplit, pow_add]
      have h32 : (3 : ZMod (3 ^ 2)) ^ 2 = 0 := by decide
      rw [h32, zero_mul]
    rw [h9] at h3n
    have : ((0 : ZMod (3 ^ 2)) = (3 : ZMod (3 ^ 2))) → False := by decide
    exact this h3n
  -- Part 2: (3 : ZMod (p ^ 2)) ^ (p - 1) = 1
  have hcop3 : Nat.Coprime 3 (p ^ 2) := by
    refine Nat.Coprime.pow_right 2 ?_
    exact (Nat.coprime_primes (by decide) hp).mpr (Ne.symm hp3)
  let u : (ZMod (p ^ 2))ˣ := ZMod.unitOfCoprime 3 hcop3
  have hu_val : (u : ZMod (p ^ 2)) = 3 := ZMod.coe_unitOfCoprime 3 hcop3
  have hu_n1 : u ^ (n - 1) = 1 := by
    apply Units.ext
    have h1 : (u : ZMod (p ^ 2)) ^ (n - 1) * (u : ZMod (p ^ 2)) = 1 * (u : ZMod (p ^ 2)) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hu_val, one_mul]
      exact h3n
    have h2 := congrArg (fun x => x * (u⁻¹ : ZMod (p ^ 2))) h1
    simpa [mul_assoc, Units.val_pow_eq_pow_val] using h2
  have hord_n1 : orderOf u ∣ n - 1 := orderOf_dvd_of_pow_eq_one hu_n1
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hcard : Nat.card (ZMod (p ^ 2))ˣ = p * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp (by decide : 0 < 2)]
    simp
  have hord_card : orderOf u ∣ p * (p - 1) := by
    rw [← hcard]
    exact orderOf_dvd_natCard u
  have hcop_p : Nat.Coprime (orderOf u) p := by
    have hp_n : p ∣ n := dvd_trans (dvd_pow_self p (by decide)) hp2
    have hcop_pn1 : p.Coprime (n - 1) := by
      have : p.Coprime (n - 1) ↔ ¬ p ∣ n - 1 := hp.coprime_iff_not_dvd
      rw [this]
      intro hd
      have h1 : p ∣ n - (n - 1) := Nat.dvd_sub hp_n hd
      rw [show n - (n - 1) = 1 by omega] at h1
      exact hp.not_dvd_one h1
    exact (hcop_pn1.coprime_dvd_right hord_n1).symm
  have hord_p1 : orderOf u ∣ p - 1 := hcop_p.dvd_of_dvd_mul_left hord_card
  have hu_p1 : u ^ (p - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hord_p1
  refine ⟨hp3, ?_⟩
  have hval := congrArg (fun x : (ZMod (p ^ 2))ˣ => (x : ZMod (p ^ 2))) hu_p1
  simpa [hu_val, Units.val_pow_eq_pow_val] using hval
