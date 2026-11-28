import OMAStatements.S_oeis_a114783

-- Reduction of OEIS A114783. Credit: @Chihiro-g
namespace OMA.R_oeis_a114783_R1

open OMA.S_oeis_a114783

/-- Decimal repunit primes occur at unbounded lengths. -/
def H1 : Prop := ∀ B : ℕ, ∃ e > B, Nat.Prime ((10 ^ e - 1) / 9)

/-- For every other offset c, if 9p = 10^d + c has a prime seed p with d decimal
digits and p different from 2 and 5, it has prime solutions at unbounded exponents. -/
def H2 : Prop := ∀ c : ℤ, c ≠ -1 →
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≠ 5 ∧ 9 * (p : ℤ) = 10 ^ (Nat.digits 10 p).length + c) →
  ∀ B : ℕ, ∃ e > B, ∃ q : ℕ, q.Prime ∧ 9 * (q : ℤ) = 10 ^ e + c

lemma repunit_identity (k : ℕ) : 9 * ((10 ^ k - 1) / 9) + 1 = 10 ^ k := by
  have hm : (10 ^ k : ℕ) % 9 = 1 := by rw [Nat.pow_mod]; simp
  have hp : 0 < (10 ^ k : ℕ) := by positivity
  omega

lemma prefixed_identity (k p : ℕ) :
    9 * (prefixed k p : ℤ) =
      10 ^ (k + (Nat.digits 10 p).length) + (9 * (p : ℤ) - 10 ^ (Nat.digits 10 p).length) := by
  have h := congrArg (fun x : ℕ => (x : ℤ)) (repunit_identity k)
  push_cast at h
  unfold prefixed
  push_cast
  rw [pow_add]
  linear_combination (10 : ℤ) ^ (Nat.digits 10 p).length * h

lemma excluded_endings {k p : ℕ} (hk : 1 ≤ k) (hp : p = 2 ∨ p = 5) :
    ¬ (prefixed k p).Prime := by
  have hpow : 10 ^ 1 ≤ (10 ^ k : ℕ) := Nat.pow_le_pow_right (by decide) hk
  have hpos : 0 < ((10 ^ k - 1) / 9 : ℕ) := by omega
  rcases hp with rfl | rfl
  · change ¬ Nat.Prime (1 * ((10 ^ k - 1) / 9) * 10 + 2)
    intro h
    have := h.eq_one_or_self_of_dvd 2 (by omega)
    omega
  · change ¬ Nat.Prime (1 * ((10 ^ k - 1) / 9) * 10 + 5)
    intro h
    have := h.eq_one_or_self_of_dvd 5 (by omega)
    omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a114783.main := by
  intro hrep hoff n hn
  have htwo : prime 1 = 2 := Nat.nth_prime_zero_eq_two
  have hfive : prime 3 = 5 := Nat.nth_prime_two_eq_five
  constructor
  · rintro ⟨k, hk, hprime⟩
    exact ⟨fun h => excluded_endings hk (Or.inl (h ▸ htwo)) hprime,
           fun h => excluded_endings hk (Or.inr (h ▸ hfive)) hprime⟩
  · rintro ⟨hn1, hn3⟩
    let p := prime n
    let d := (Nat.digits 10 p).length
    let c : ℤ := 9 * (p : ℤ) - 10 ^ d
    have inj := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective
    have hp2 : p ≠ 2 := by
      intro h
      have he : n - 1 = 0 := inj (h.trans htwo.symm)
      omega
    have hp5 : p ≠ 5 := by
      intro h
      have he : n - 1 = 2 := inj (h.trans hfive.symm)
      omega
    have seed : 9 * (p : ℤ) = 10 ^ d + c := by dsimp [c]; ring
    obtain ⟨e, he, q, hq, eq⟩ : ∃ e > d, ∃ q : ℕ, q.Prime ∧ 9 * (q : ℤ) = 10 ^ e + c := by
      by_cases hc : c = -1
      · obtain ⟨e, he, hprime⟩ := hrep d
        refine ⟨e, he, _, hprime, ?_⟩
        have hid := congrArg (fun x : ℕ => (x : ℤ)) (repunit_identity e)
        push_cast at hid
        omega
      · exact hoff c hc ⟨p, Nat.prime_nth_prime _, hp2, hp5, seed⟩ d
    refine ⟨e - d, by omega, ?_⟩
    have hid : 9 * (prefixed (e - d) p : ℤ) = 10 ^ ((e - d) + d) + c :=
      prefixed_identity (e - d) p
    rw [Nat.sub_add_cancel he.le] at hid
    have hsame : prefixed (e - d) p = q := by omega
    exact hsame.symm ▸ hq

lemma prefixed_succ (k p : ℕ) :
    prefixed (k + 1) p = 10 ^ (k + (Nat.digits 10 p).length) + prefixed k p := by
  have h := repunit_identity k
  have h' := repunit_identity (k + 1)
  rw [pow_succ] at h'
  have step : (10 ^ (k + 1) - 1) / 9 = (10 ^ k - 1) / 9 + 10 ^ k := by omega
  unfold prefixed
  rw [step, pow_add]
  ring

lemma prefixed_length (k p : ℕ) :
    (Nat.digits 10 (prefixed k p)).length = k + (Nat.digits 10 p).length := by
  induction k with
  | zero => simp [prefixed]
  | succ k ih =>
    let d := (Nat.digits 10 p).length
    have hu := Nat.lt_base_pow_length_digits (m := prefixed k p) (by decide : 1 < 10)
    rw [ih] at hu
    rw [prefixed_succ]
    apply Nat.le_antisymm
    · apply (Nat.digits_length_le_iff (by decide : 1 < 10) _).2
      rw [show k + 1 + d = (k + d) + 1 by omega, pow_succ]
      dsimp only [d]
      omega
    · have hl := (Nat.lt_digits_length_iff (k := k + d) (by decide : 1 < 10)
          (10 ^ (k + d) + prefixed k p)).2 (Nat.le_add_right _ _)
      dsimp only [d] at hl
      omega

/-- Iterating the conjectured extension keeps the offset fixed and strictly increases
the digit length. This proves necessity of the unboundedness assumptions as well. -/
lemma orbit_unbounded (h : type_of% @OMA.S_oeis_a114783.main)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) (B : ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ 5 ∧ B < (Nat.digits 10 q).length ∧
      9 * (q : ℤ) - 10 ^ (Nat.digits 10 q).length =
      9 * (p : ℤ) - 10 ^ (Nat.digits 10 p).length := by
  induction B with
  | zero =>
    refine ⟨p, hp, hp2, hp5, ?_, rfl⟩
    exact (Nat.lt_digits_length_iff (by decide) p).2 (by simpa using (Nat.le_trans (by decide : 1 ≤ 2) hp.two_le))
  | succ B ih =>
    obtain ⟨q, hq, hq2, hq5, hlen, hoff⟩ := ih
    let n := Nat.count Nat.Prime q + 1
    have hn : prime n = q := by simp [prime, n, Nat.nth_count hq]
    have hn1 : n ≠ 1 := by
      rintro he
      exact hq2 (hn.symm.trans (he ▸ Nat.nth_prime_zero_eq_two : prime n = 2))
    have hn3 : n ≠ 3 := by
      rintro he
      exact hq5 (hn.symm.trans (he ▸ Nat.nth_prime_two_eq_five : prime n = 5))
    obtain ⟨k, hk, hkq⟩ := (h n (by dsimp [n]; omega)).2 ⟨hn1, hn3⟩
    rw [hn] at hkq
    have hlen' := prefixed_length k q
    have htwo : (Nat.digits 10 2).length = 1 := by decide
    have hfive : (Nat.digits 10 5).length = 1 := by decide
    have longer : 1 < (Nat.digits 10 (prefixed k q)).length := by omega
    refine ⟨prefixed k q, hkq, fun he => ?_, fun he => ?_, by omega, ?_⟩
    · rw [he, htwo] at longer; omega
    · rw [he, hfive] at longer; omega
    · rw [hlen', prefixed_identity]
      linarith

lemma necessary (h : type_of% @OMA.S_oeis_a114783.main) : H1 ∧ H2 := by
  constructor
  · intro B
    obtain ⟨q, hq, _, _, hlen, hoff⟩ :=
      orbit_unbounded h 11 (by decide) (by decide) (by decide) B
    have h11 : (Nat.digits 10 11).length = 2 := by decide
    rw [h11] at hoff
    norm_num at hoff
    refine ⟨_, hlen, ?_⟩
    have hid := congrArg (fun x : ℕ => (x : ℤ)) (repunit_identity (Nat.digits 10 q).length)
    push_cast at hid
    have heq : (10 ^ (Nat.digits 10 q).length - 1) / 9 = q := by omega
    exact heq.symm ▸ hq
  · rintro c _ ⟨p, hp, hp2, hp5, seed⟩ B
    obtain ⟨q, hq, _, _, hlen, hoff⟩ := orbit_unbounded h p hp hp2 hp5 B
    exact ⟨_, hlen, q, hq, by linarith⟩

end OMA.R_oeis_a114783_R1
