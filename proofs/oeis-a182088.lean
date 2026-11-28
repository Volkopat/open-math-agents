import OMAStatements.S_oeis_a182088

-- Problem: A182088: Carmichael numbers of the form C = (30n-29)*(60n-59)*(90n-89)*(180n-179), where n is a natural number.
-- Upstream: formal-conjectures statements/oeis-a182088.lean:0 (declaration OMA.S_oeis_a182088.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea (Korselt, the easy direction): if c is a product of distinct primes p with p - 1
-- dividing c - 1, then b^(c-1) == 1 mod each p by Fermat, hence mod c. With n = m + 1 the
-- factors are 30m+1, 60m+1, 90m+1, 180m+1 and their product is 180m*K + 1 with
-- K = 6(30m)^3 + 12(30m)^2 + 235m + 2. For the converse, n = 2 gives
-- C = 31146661 = 7 * 13 * 31 * 61 * 181, a Carmichael number, while 90*2 - 89 = 91 = 7 * 13.

open OMA.S_oeis_a182088 in
theorem OMA.solution : type_of% @OMA.S_oeis_a182088.main := by
  have kor : ∀ c p : ℕ, p.Prime → p ∣ c → (p - 1) ∣ (c - 1) →
      ∀ b : ℕ, Nat.Coprime b c → b ^ (c - 1) ≡ 1 [MOD p] := by
    intro c p hp hpc hdiv b hb
    have hbp : Nat.Coprime b p := Nat.Coprime.coprime_dvd_right hpc hb
    have hf : b ^ (p - 1) ≡ 1 [MOD p] := by
      have h1 := Nat.ModEq.pow_totient hbp
      rw [Nat.totient_prime hp] at h1
      exact h1
    obtain ⟨t, ht⟩ := hdiv
    rw [ht, pow_mul]
    have h2 := hf.pow t
    rw [one_pow] at h2
    exact h2
  have comb : ∀ x a q : ℕ, x ≡ 1 [MOD a] → x ≡ 1 [MOD q] → Nat.Coprime a q →
      x ≡ 1 [MOD a * q] := by
    intro x a q h1 h2 h3
    exact (Nat.modEq_and_modEq_iff_modEq_mul h3).mp ⟨h1, h2⟩
  have kor4 : ∀ p1 p2 p3 p4 : ℕ, p1.Prime → p2.Prime → p3.Prime → p4.Prime →
      p1 ≠ p2 → p1 ≠ p3 → p1 ≠ p4 → p2 ≠ p3 → p2 ≠ p4 → p3 ≠ p4 →
      (p1 - 1) ∣ (p1 * p2 * p3 * p4 - 1) → (p2 - 1) ∣ (p1 * p2 * p3 * p4 - 1) →
      (p3 - 1) ∣ (p1 * p2 * p3 * p4 - 1) → (p4 - 1) ∣ (p1 * p2 * p3 * p4 - 1) →
      IsCarmichael (p1 * p2 * p3 * p4) := by
    intro p1 p2 p3 p4 h1 h2 h3 h4 n12 n13 n14 n23 n24 n34 d1 d2 d3 d4
    have c12 := (Nat.coprime_primes h1 h2).mpr n12
    have c13 := (Nat.coprime_primes h1 h3).mpr n13
    have c14 := (Nat.coprime_primes h1 h4).mpr n14
    have c23 := (Nat.coprime_primes h2 h3).mpr n23
    have c24 := (Nat.coprime_primes h2 h4).mpr n24
    have c34 := (Nat.coprime_primes h3 h4).mpr n34
    refine ⟨?_, ?_, ?_⟩
    · have hle := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1.two_le h2.two_le)
        h3.two_le) h4.two_le
      exact Nat.lt_of_lt_of_le (by norm_num) hle
    · have hne : p2 * p3 * p4 ≠ 1 := by
        intro h
        have h5 := Nat.mul_le_mul (Nat.mul_le_mul h2.two_le h3.two_le) h4.two_le
        rw [h] at h5
        omega
      rw [show p1 * p2 * p3 * p4 = p1 * (p2 * p3 * p4) by ring]
      exact Nat.not_prime_mul h1.one_lt.ne' hne
    · intro b hb
      have m1 := kor (p1 * p2 * p3 * p4) p1 h1 ⟨p2 * p3 * p4, by ring⟩ d1 b hb
      have m2 := kor (p1 * p2 * p3 * p4) p2 h2 ⟨p1 * p3 * p4, by ring⟩ d2 b hb
      have m3 := kor (p1 * p2 * p3 * p4) p3 h3 ⟨p1 * p2 * p4, by ring⟩ d3 b hb
      have m4 := kor (p1 * p2 * p3 * p4) p4 h4 ⟨p1 * p2 * p3, by ring⟩ d4 b hb
      exact comb _ _ _ (comb _ _ _ (comb _ _ _ m1 m2 c12) m3 (Nat.Coprime.mul_left c13 c23)) m4
        (Nat.Coprime.mul_left (Nat.Coprime.mul_left c14 c24) c34)
  refine ⟨?_, ?_⟩
  · intro n hn hall
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨h1, h2, h3, h4⟩ := hall
    rw [show 30 * (m + 1) - 29 = 30 * m + 1 by omega] at h1
    rw [show 60 * (m + 1) - 59 = 60 * m + 1 by omega] at h2
    rw [show 90 * (m + 1) - 89 = 90 * m + 1 by omega] at h3
    rw [show 180 * (m + 1) - 179 = 180 * m + 1 by omega] at h4
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0] at h1
        norm_num at h1
      · exact h0
    have hC : C (m + 1) = (30 * m + 1) * (60 * m + 1) * (90 * m + 1) * (180 * m + 1) := by
      unfold C
      rw [show 30 * (m + 1) - 29 = 30 * m + 1 by omega,
        show 60 * (m + 1) - 59 = 60 * m + 1 by omega,
        show 90 * (m + 1) - 89 = 90 * m + 1 by omega,
        show 180 * (m + 1) - 179 = 180 * m + 1 by omega]
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 6 * (30 * m) ^ 3 + 12 * (30 * m) ^ 2 + 235 * m + 2 :=
      ⟨_, rfl⟩
    have hprod : (30 * m + 1) * (60 * m + 1) * (90 * m + 1) * (180 * m + 1) =
        180 * m * K + 1 := by
      rw [hK]
      ring
    have hsub : (30 * m + 1) * (60 * m + 1) * (90 * m + 1) * (180 * m + 1) - 1 =
        180 * m * K := by
      rw [hprod, Nat.add_sub_cancel]
    rw [hC]
    apply kor4 _ _ _ _ h1 h2 h3 h4 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    · rw [hsub, show 30 * m + 1 - 1 = 30 * m by omega]
      exact ⟨6 * K, by ring⟩
    · rw [hsub, show 60 * m + 1 - 1 = 60 * m by omega]
      exact ⟨3 * K, by ring⟩
    · rw [hsub, show 90 * m + 1 - 1 = 90 * m by omega]
      exact ⟨2 * K, by ring⟩
    · rw [hsub, show 180 * m + 1 - 1 = 180 * m by omega]
      exact ⟨K, by ring⟩
  · refine ⟨2, by norm_num, ?_, ?_⟩
    · have hC2 : C 2 = 31146661 := by
        unfold C
        norm_num
      rw [hC2]
      refine ⟨by norm_num, by norm_num, ?_⟩
      intro b hb
      have m1 := kor 31146661 7 (by norm_num) (by norm_num) (by norm_num) b hb
      have m2 := kor 31146661 13 (by norm_num) (by norm_num) (by norm_num) b hb
      have m3 := kor 31146661 31 (by norm_num) (by norm_num) (by norm_num) b hb
      have m4 := kor 31146661 61 (by norm_num) (by norm_num) (by norm_num) b hb
      have m5 := kor 31146661 181 (by norm_num) (by norm_num) (by norm_num) b hb
      have e := comb _ _ _ (comb _ _ _ (comb _ _ _ (comb _ _ _ m1 m2 (by decide)) m3
        (by decide)) m4 (by decide)) m5 (by decide)
      rw [show 7 * 13 * 31 * 61 * 181 = 31146661 by norm_num] at e
      exact e
    · intro h
      obtain ⟨_, _, h3, _⟩ := h
      norm_num at h3
