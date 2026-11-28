import OMAStatements.S_oeis_a365965

-- Problem: A365965: Numbers k such that A139315(k) = 0 but k is not in A138511.
-- Upstream: formal-conjectures statements/oeis-a365965.lean:0 (declaration OMA.S_oeis_a365965.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write k = 2^a p^b r with r prime to 2p. Then d(4pk) = (a+3)(b+2) d(r) and
-- d(k) = (a+1)(b+1) d(r), so d(4pk) = 2 d(k) forces a b = b + 4, i.e. (a,b) = (2,4), (3,2) or
-- (5,1). Then the multiplier 8, 16 or 64 (each smaller than 4p, as p >= 17) already doubles d(k),
-- so 4p k is never the least such multiple and A139315(4p) = 0. And 4p = q1 q2 with q1, q2 prime
-- would make 2p prime.

namespace A365965aux

theorem ppow (q i : ℕ) (hq : q.Prime) : (q ^ i).divisors.card = i + 1 := by
  rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hq]

theorem dcount (p A B r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (h2r : Nat.Coprime 2 r)
    (hpr : Nat.Coprime p r) :
    (2 ^ A * (p ^ B * r)).divisors.card = (A + 1) * ((B + 1) * r.divisors.card) := by
  have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have c1 : Nat.Coprime (2 ^ A) (p ^ B * r) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow A B h2p) (Nat.Coprime.pow_left A h2r)
  have c2 : Nat.Coprime (p ^ B) r := Nat.Coprime.pow_left B hpr
  rw [Nat.Coprime.card_divisors_mul c1, Nat.Coprime.card_divisors_mul c2, ppow 2 A Nat.prime_two,
    ppow p B hp]

theorem decomp (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    ∃ a b r : ℕ, k = 2 ^ a * (p ^ b * r) ∧ Nat.Coprime 2 r ∧ Nat.Coprime p r ∧ r ≠ 0 := by
  obtain ⟨k1, hk1⟩ : ∃ k1, k1 = k / 2 ^ k.factorization 2 := ⟨_, rfl⟩
  have e1 : 2 ^ k.factorization 2 * k1 = k := by
    rw [hk1]
    exact Nat.ordProj_mul_ordCompl_eq_self k 2
  have c1 : Nat.Coprime 2 k1 := by
    rw [hk1]
    exact Nat.coprime_ordCompl Nat.prime_two hk
  have hk10 : k1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at e1
    exact hk e1.symm
  have e2 : p ^ k1.factorization p * (k1 / p ^ k1.factorization p) = k1 :=
    Nat.ordProj_mul_ordCompl_eq_self k1 p
  have c2 : Nat.Coprime p (k1 / p ^ k1.factorization p) := Nat.coprime_ordCompl hp hk10
  refine ⟨k.factorization 2, k1.factorization p, k1 / p ^ k1.factorization p, ?_, ?_, c2, ?_⟩
  · rw [e2, e1]
  · exact Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ e2) c1
  · intro h
    rw [h, mul_zero] at e2
    exact hk10 e2.symm

end A365965aux

open OMA.S_oeis_a365965 A365965aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a365965.main := by
  intro p hp hp13
  have hp2 : p ≠ 2 := by omega
  have hp17 : 17 ≤ p := by
    rcases Nat.lt_or_ge p 17 with h | h
    · interval_cases p <;> norm_num at hp
    · exact h
  refine ⟨?_, ?_⟩
  · unfold A139315
    rw [dif_neg]
    rintro ⟨k, hk1, hd, hmin⟩
    obtain ⟨a, b, r, rfl, h2r, hpr, hr0⟩ := decomp p k hp (by omega)
    have hD : 0 < r.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hr0⟩
    have hdk := dcount p a b r hp hp2 h2r hpr
    have h4 : 4 * p * (2 ^ a * (p ^ b * r)) = 2 ^ (a + 2) * (p ^ (b + 1) * r) := by ring
    rw [h4, dcount p (a + 2) (b + 1) r hp hp2 h2r hpr, hdk] at hd
    have hmul : ∀ c : ℕ, 2 ^ c * (2 ^ a * (p ^ b * r)) = 2 ^ (a + c) * (p ^ b * r) :=
      fun c => by ring
    have hm : ∀ c : ℕ, 2 ^ c < 4 * p →
        (a + c + 1) * ((b + 1) * r.divisors.card) ≠
          2 * ((a + 1) * ((b + 1) * r.divisors.card)) := by
      intro c hc
      have h := hmin (2 ^ c) Nat.one_le_two_pow hc
      rwa [hmul c, dcount p (a + c) b r hp hp2 h2r hpr, hdk] at h
    have E : (a + 3) * (b + 2) = 2 * (a + 1) * (b + 1) := by
      apply Nat.eq_of_mul_eq_mul_right hD
      calc (a + 3) * (b + 2) * r.divisors.card
          = (a + 2 + 1) * ((b + 1 + 1) * r.divisors.card) := by ring
        _ = 2 * ((a + 1) * ((b + 1) * r.divisors.card)) := hd
        _ = 2 * (a + 1) * (b + 1) * r.divisors.card := by ring
    have hab : a * b = b + 4 := by nlinarith [E]
    have hb1 : 1 ≤ b := by
      by_contra h
      have hb0 : b = 0 := by omega
      subst hb0
      omega
    have ha2 : 2 ≤ a := by
      rcases Nat.lt_or_ge a 2 with h | h
      · interval_cases a <;> omega
      · exact h
    have hb4 : b ≤ 4 := by
      have h := Nat.mul_le_mul_right b ha2
      omega
    have ha5 : a ≤ 5 := by
      by_contra h
      have h6 : 6 ≤ a := by omega
      have h' := Nat.mul_le_mul_right b h6
      omega
    have hcases : (a = 2 ∧ b = 4) ∨ (a = 3 ∧ b = 2) ∨ (a = 5 ∧ b = 1) := by
      interval_cases a <;> interval_cases b <;> omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hm 3 (by norm_num; omega) (by ring)
    · exact hm 4 (by norm_num; omega) (by ring)
    · exact hm 6 (by norm_num; omega) (by ring)
  · rintro ⟨q1, q2, hq1, hq2, _, heq⟩
    have h2 : 2 ∣ q1 * q2 := ⟨2 * p, by rw [← heq]; ring⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · have e : 2 = q1 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq1).mp h
      subst e
      have hq2' : q2 = 2 * p := by omega
      have h2q : 2 ∣ q2 := ⟨p, hq2'⟩
      have e2 : 2 = q2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq2).mp h2q
      omega
    · have e : 2 = q2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq2).mp h
      subst e
      have hq1' : q1 = 2 * p := by omega
      have h2q : 2 ∣ q1 := ⟨p, hq1'⟩
      have e2 : 2 = q1 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq1).mp h2q
      omega
