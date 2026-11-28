import FormalConjectures.Wikipedia.WallSunSun

/-!
# Square factors of Fibonacci numbers at factorial indices

Credit: @Pixelstorm44. A prime larger than n is coprime to n!, so a square
factor above this cutoff cannot arise by multiplying an index by the prime.
The transfer lemma makes this observation precise. The converse below shows
that the cutoff retains every Wall–Sun–Sun prime greater than five.
-/

namespace OMA.R_WallSunSun_infinite_isWallSunSunPrime_R1

private theorem qpow (R : Type*) [CommRing R] (k : ℕ) :
    (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R) ^ (k + 1) = !![(Nat.fib (k + 2) : R), (Nat.fib (k + 1) : R);
                      (Nat.fib (k + 1) : R), (Nat.fib k : R)] := by
  induction k with
  | zero => simp [Nat.fib_two]
  | succ k ih =>
    rw [pow_succ, ih]
    simp [Nat.fib_add_two]
    constructor <;> ring

private theorem lucas_fib (k : ℕ) :
    lucasNumber (k + 1) = (Nat.fib (k + 2) : ℤ) + Nat.fib k := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k h₀ h₁ =>
    have h : lucasNumber (k + 2 + 1) = lucasNumber (k + 1 + 1) + lucasNumber (k + 1) := by
      simp [lucasNumber, LucasSequence.V]
    rw [h, h₀, h₁]
    push_cast [Nat.fib_add_two]
    ring

private theorem trace_congruence (p : ℕ) (hp : p.Prime) :
    lucasNumber p ≡ 1 [ZMOD (p : ℤ)] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  let p := k + 1
  let : Fact p.Prime := ⟨hp⟩
  apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
  have h := ZMod.trace_pow_card (p := p) (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
  change ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ (k + 1)).trace = _ at h
  rw [qpow] at h
  rw [lucas_fib]
  simpa [Matrix.trace, Fin.sum_univ_two] using h

private theorem lucas_product (p : ℕ) (ho : Odd p) :
    (lucasNumber p - 1) * (lucasNumber p + 1) =
      5 * (Nat.fib (p - 1) : ℤ) * Nat.fib (p + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ho.pos.ne'
  have hc := congrArg Matrix.det (qpow ℤ k)
  rw [Matrix.det_pow] at hc
  simp only [Matrix.det_fin_two] at hc
  change ((1:ℤ) * 0 - 1 * 1) ^ (k + 1) = (Nat.fib (k + 2):ℤ) * Nat.fib k - (Nat.fib (k + 1):ℤ) * Nat.fib (k + 1) at hc
  norm_num only [mul_zero, mul_one, zero_sub] at hc
  rw [ho.neg_one_pow] at hc
  rw [lucas_fib]
  simp only [Nat.succ_sub_one]
  rw [Nat.fib_add_two, Nat.cast_add] at hc ⊢
  nlinarith

private theorem neighboring_index (p : ℕ) (hp : p.Prime) (h5 : 5 < p) :
    ∃ m ∈ ({p - 1, p + 1} : Set ℕ), p ∣ Nat.fib m := by
  have h := (trace_congruence p hp).symm.dvd
  have hprod := lucas_product p (hp.odd_of_ne_two (by omega))
  have hd : (p : ℤ) ∣ 5 * (Nat.fib (p - 1) : ℤ) * Nat.fib (p + 1) := hprod ▸ dvd_mul_of_dvd_left h _
  have hz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hn : ¬ (p : ℤ) ∣ 5 := by
    exact_mod_cast (show ¬ p ∣ 5 from fun d => by have := Nat.le_of_dvd (by decide : 0 < 5) d; omega)
  rcases hz.dvd_mul.mp hd with h | h
  · exact ⟨_, Or.inl rfl, Int.natCast_dvd_natCast.mp ((hz.dvd_mul.mp h).resolve_left hn)⟩
  · exact ⟨_, Or.inr rfl, Int.natCast_dvd_natCast.mp h⟩

private theorem of_neighbor_square {p m : ℕ} (hp : p.Prime) (h5 : 5 < p)
    (hm : m ∈ ({p - 1, p + 1} : Set ℕ)) (hd : p ^ 2 ∣ Nat.fib m) : IsWallSunSunPrime p := by
  have hz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h1 := (trace_congruence p hp).symm.dvd
  have hn : ¬ (p : ℤ) ∣ lucasNumber p + 1 := by
    intro h
    have h2 := dvd_sub h h1
    ring_nf at h2
    have : p ∣ 2 := by exact_mod_cast h2
    have := Nat.le_of_dvd (by decide : 0 < 2) this
    omega
  refine ⟨hp, Int.ModEq.symm (Int.modEq_iff_dvd.mpr ?_)⟩
  apply hz.pow_dvd_of_dvd_mul_right 2 hn
  rw [lucas_product p (hp.odd_of_ne_two (by omega))]
  have d : (p : ℤ) ^ 2 ∣ (Nat.fib m : ℤ) := by exact_mod_cast hd
  rcases hm with h | h
  · subst m
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right d _) _
  · change m = p + 1 at h
    subst m
    exact dvd_mul_of_dvd_right d _

/-- The first-order term in a power of the companion matrix when its off-diagonal entry squares to zero. -/
private theorem scalar_lift {R : Type*} [CommRing R] (a b : R) (hb : b ^ 2 = 0) (k : ℕ) :
    (!![a + b, b; b, a] : Matrix (Fin 2) (Fin 2) R) ^ (k + 1) =
      let t := ((k + 1 : ℕ) : R) * a ^ k * b
      !![a ^ (k + 1) + t, t; t, a ^ (k + 1)] := by
  induction k with
  | zero => simp
  | succ k ih =>
    dsimp only at *
    rw [pow_succ, ih, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Nat.cast_succ, pow_succ] <;> ring_nf <;> simp [hb]

private theorem fib_lift {m p : ℕ} (hp : p ≠ 0) (hm : p ∣ Nat.fib m) :
    p ^ 2 ∣ Nat.fib (p * m) := by
  cases m with
  | zero => simp
  | succ k =>
    let R := ZMod (p ^ 2)
    let a : R := Nat.fib k
    let b : R := Nat.fib (k + 1)
    obtain ⟨u, hu⟩ := hm
    have hb : b = (p : R) * (u : R) := by
      change (Nat.fib (k + 1) : ZMod (p ^ 2)) = _
      rw [hu, Nat.cast_mul]
    have hpp : (p : R) ^ 2 = 0 := by
      exact_mod_cast (ZMod.natCast_self (p ^ 2))
    have hbb : b ^ 2 = 0 := by rw [hb, mul_pow, hpp, zero_mul]
    have hpb : (p : R) * b = 0 := by rw [hb, ← mul_assoc, ← sq, hpp, zero_mul]
    have he : (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R) ^ (k + 1) = !![a + b, b; b, a] := by
      rw [qpow]
      simp [a, b, Nat.fib_add_two]
    obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero hp
    change p = l + 1 at hl
    have hpow := scalar_lift a b hbb l
    rw [← hl, ← he, ← pow_mul, mul_comm] at hpow
    have hpos : 0 < p * (k + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hp) (Nat.succ_pos _)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hj, qpow] at hpow
    have hoff := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) hpow
    rw [hj]
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    change (Nat.fib (j + 1) : R) = (p : R) * a ^ l * b at hoff
    rw [hoff, mul_right_comm, hpb, zero_mul]

/-- Repeated factors larger than the factorial cutoff occur at arbitrarily large cutoffs. -/
def H1 : Prop := ∀ B : ℕ, ∃ n ≥ B, ∃ p > n, p.Prime ∧ p ^ 2 ∣ Nat.fib n.factorial

/-- At an index coprime to p, a repeated prime factor transfers to a neighbor of p. -/
def H2 : Prop := ∀ n p : ℕ, p.Prime → 5 < p → p.Coprime n → p ^ 2 ∣ Nat.fib n →
    ∃ m ∈ ({p - 1, p + 1} : Set ℕ), p ^ 2 ∣ Nat.fib m

theorem transfer_proved : H2 := by
  intro n p hp h5 hcop hd
  obtain ⟨m, hm, hfib⟩ := neighboring_index p hp h5
  refine ⟨m, hm,?_⟩
  have hg := Nat.dvd_gcd hd (fib_lift hp.ne_zero hfib)
  rw [← Nat.fib_gcd] at hg
  apply hg.trans (Nat.fib_dvd _ _ ?_)
  exact (hcop.symm.coprime_dvd_left (Nat.gcd_dvd_left _ _)).dvd_of_dvd_mul_left
    (Nat.gcd_dvd_right n (p * m))

/-- Each Wall–Sun–Sun prime above five occurs above the cutoff at its predecessor. -/
theorem factorial_witness {p : ℕ} (hp : IsWallSunSunPrime p) (h5 : 5 < p) :
    p ^ 2 ∣ Nat.fib (p - 1).factorial := by
  have hprod := dvd_mul_of_dvd_left hp.lucasNumber_modeq.symm.dvd (lucasNumber p + 1)
  rw [lucas_product p (hp.prime.odd_of_ne_two (by omega)), mul_assoc] at hprod
  have hd : p ^ 2 ∣ 5 * (Nat.fib (p - 1) * Nat.fib (p + 1)) := by exact_mod_cast hprod
  have hn : ¬ p ∣ 5 := fun d => by have := Nat.le_of_dvd (by decide : 0 < 5) d; omega
  have hpair := hp.prime.prime.pow_dvd_of_dvd_mul_left 2 hn hd
  have hc : (Nat.fib (p - 1)).Coprime (Nat.fib (p + 1)) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.prime.ne_zero
    simpa [Nat.fib_add_two] using Nat.fib_coprime_fib_succ k
  by_cases h : p ∣ Nat.fib (p - 1)
  · have hn' : ¬ p ∣ Nat.fib (p + 1) := hp.prime.coprime_iff_not_dvd.mp (hc.coprime_dvd_left h)
    have hd' := hp.prime.prime.pow_dvd_of_dvd_mul_right 2 hn' hpair
    exact hd'.trans (Nat.fib_dvd _ _ (Nat.dvd_factorial (by omega) le_rfl))
  · have hd' := hp.prime.prime.pow_dvd_of_dvd_mul_left 2 h hpair
    apply hd'.trans (Nat.fib_dvd _ _ ?_)
    obtain ⟨k, hk⟩ := hp.prime.odd_of_ne_two (by omega)
    have hk' : k + 1 ∣ (p - 2).factorial := Nat.dvd_factorial (by omega) (by omega)
    have htwo : 2 ∣ p - 1 := ⟨k, by omega⟩
    have hmul := Nat.mul_dvd_mul htwo hk'
    rw [show 2 * (k + 1) = p + 1 by omega, show p - 1 = (p - 2) + 1 by omega,
      ← Nat.factorial_succ] at hmul
    simpa only [show p - 2 + 1 = p - 1 by omega] using hmul

theorem main : H1 → H2 → type_of% @WallSunSun.infinite_isWallSunSunPrime := by
  intro h₁ h₂
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨n, hn, p, hp, hprime, hd⟩ := h₁ (max B 5)
  have h5 : 5 < p := lt_of_le_of_lt ((le_max_right _ _).trans hn) hp
  have hc := hprime.coprime_iff_not_dvd.mpr (mt hprime.dvd_factorial.mp hp.not_ge)
  obtain ⟨m, hm, hs⟩ := h₂ _ _ hprime h5 hc hd
  exact ⟨p, of_neighbor_square hprime h5 hm hs, lt_of_le_of_lt ((le_max_left _ _).trans hn) hp⟩

/-- The factorial test also follows from infinitude, so it loses no potential witnesses. -/
theorem factorial_test_iff :
    H1 ↔ {p : ℕ | IsWallSunSunPrime p}.Infinite := by
  refine ⟨fun h => main h transfer_proved, ?_⟩
  intro hinf B
  obtain ⟨p, hp, hB⟩ := hinf.exists_gt (B + 5)
  change IsWallSunSunPrime p at hp
  exact ⟨p - 1, by omega, p, by omega, hp.prime, factorial_witness hp (by omega)⟩

end OMA.R_WallSunSun_infinite_isWallSunSunPrime_R1
