import OMAStatements.S_oeis_a387319

-- Problem: A387319: Numbers k for which modulo 3 and modulo another multiple of 3 are coincident among the fractions (2*k mod m)/m for 1 <= m <= k.
-- Upstream: formal-conjectures statements/oeis-a387319.lean:0 (declaration OMA.S_oeis_a387319.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: if 2k = g*w then the fraction at m = 3*g is (w mod 3)/3. Composite k: 3 | k gives
-- j = 2 (both fractions 0); k even, 3 not dividing k, k >= 12 gives j = 4; k odd, prime to 3, with
-- smallest prime factor q and k = q*b (b >= q >= 5) gives j = q if q = 1 mod 3 and j = 2q if
-- q = 2 mod 3 (then b >= 7 unless k = 25). A prime p: 3 < 3j <= p and equal fractions give
-- 3*(3j)*(q1 - q2) = 2p(3j - 3), so p divides q1 - q2, which is impossible.

open OMA.S_oeis_a387319 in
theorem OMA.solution : type_of% @OMA.S_oeis_a387319.main := by
  have G : ∀ k g w c : ℕ, 2 * k = g * w → 0 < g →
      fracVal k (c * g) = ((w % c : ℕ) : ℚ) / (c : ℚ) := by
    intro k g w c hk hg
    unfold fracVal
    rw [hk, show c * g = g * c by ring, Nat.mul_mod_mul_left]
    have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hg']
  have aux : ∀ p a b q1 q2 r1 r2 : ℕ, p.Prime → 3 ≤ a → a < b → b < p →
      a * q1 + r1 = 2 * p → b * q2 + r2 = 2 * p → r1 * b = r2 * a → False := by
    intro p a b q1 q2 r1 r2 hp ha hab hbp E1 E2 E3
    have Z1 : (a : ℤ) * q1 + r1 = 2 * p := by exact_mod_cast E1
    have Z2 : (b : ℤ) * q2 + r2 = 2 * p := by exact_mod_cast E2
    have Z3 : (r1 : ℤ) * b = r2 * a := by exact_mod_cast E3
    have hZ : (a : ℤ) * b * ((q1 : ℤ) - q2) = (p : ℤ) * (2 * ((b : ℤ) - a)) := by
      linear_combination (b : ℤ) * Z1 - (a : ℤ) * Z2 - Z3
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hpa : ¬ (p : ℤ) ∣ (a : ℤ) := by
      intro h
      have h' : p ∣ a := Int.natCast_dvd_natCast.mp h
      have := Nat.le_of_dvd (by omega) h'
      omega
    have hpb : ¬ (p : ℤ) ∣ (b : ℤ) := by
      intro h
      have h' : p ∣ b := Int.natCast_dvd_natCast.mp h
      have := Nat.le_of_dvd (by omega) h'
      omega
    have hdvd : (p : ℤ) ∣ (a : ℤ) * b * ((q1 : ℤ) - q2) := Dvd.intro _ hZ.symm
    obtain ⟨t, ht⟩ : (p : ℤ) ∣ ((q1 : ℤ) - q2) := by
      rcases hpZ.dvd_or_dvd hdvd with h | h
      · rcases hpZ.dvd_or_dvd h with h' | h'
        · exact absurd h' hpa
        · exact absurd h' hpb
      · exact h
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hk : (a : ℤ) * b * t = 2 * ((b : ℤ) - a) := by
      apply mul_left_cancel₀ hp0
      rw [ht] at hZ
      linear_combination hZ
    have ha3 : (3 : ℤ) ≤ a := by exact_mod_cast ha
    have hab' : (a : ℤ) < b := by exact_mod_cast hab
    have hab0 : (0 : ℤ) ≤ (a : ℤ) * b := by positivity
    rcases le_or_gt t 0 with ht0 | ht0
    · have h1 : 0 ≤ (a : ℤ) * b * (-t) := mul_nonneg hab0 (by linarith)
      linarith
    · have h1 : (a : ℤ) * b * 1 ≤ (a : ℤ) * b * t := mul_le_mul_of_nonneg_left (by omega) hab0
      have h2 : (3 : ℤ) * b ≤ (a : ℤ) * b := mul_le_mul_of_nonneg_right ha3 (by positivity)
      linarith
  refine ⟨?_, ?_⟩
  · intro k hk hnp h4 h8 h10 h25
    by_cases h3 : 3 ∣ k
    · obtain ⟨b, rfl⟩ := h3
      have hb1 : b ≠ 1 := by
        rintro rfl
        exact hnp Nat.prime_three
      refine ⟨2, le_rfl, by omega, ?_⟩
      unfold fracVal
      rw [show 2 * (3 * b) % (3 * 2) = 0 by omega, show 2 * (3 * b) % 3 = 0 by omega]
      simp
    · by_cases h2 : 2 ∣ k
      · obtain ⟨b, rfl⟩ := h2
        have hb1 : b ≠ 1 := by
          rintro rfl
          exact hnp Nat.prime_two
        refine ⟨4, by norm_num, by omega, ?_⟩
        unfold fracVal
        rw [show 2 * (2 * b) % (3 * 4) = 4 * (2 * (2 * b) % 3) by omega]
        push_cast
        ring
      · have hk1 : k ≠ 1 := by omega
        obtain ⟨q, hq, ⟨b, hb⟩, hqmin⟩ : ∃ q, q.Prime ∧ q ∣ k ∧ ∀ r, r.Prime → r ∣ k → q ≤ r :=
          ⟨k.minFac, Nat.minFac_prime hk1, Nat.minFac_dvd k,
            fun r hr hrk => Nat.minFac_le_of_dvd hr.two_le hrk⟩
        have hq2 : q % 2 = 1 := by
          have h : ¬ 2 ∣ q := fun h => h2 (by rw [hb]; exact Dvd.dvd.mul_right h _)
          omega
        have hq3 : q % 3 ≠ 0 := by
          have h : ¬ 3 ∣ q := fun h => h3 (by rw [hb]; exact Dvd.dvd.mul_right h _)
          omega
        have hq5 : 5 ≤ q := by
          have := hq.two_le
          omega
        have hb1 : b ≠ 1 := by
          rintro rfl
          rw [mul_one] at hb
          exact hnp (by rw [hb]; exact hq)
        have hb0 : b ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hb
          omega
        have hqb : q ≤ b := by
          have hr := Nat.minFac_prime hb1
          have hrb : b.minFac ∣ b := Nat.minFac_dvd b
          have h1 : q ≤ b.minFac := hqmin _ hr (by rw [hb]; exact Dvd.dvd.mul_left hrb q)
          have h2 : b.minFac ≤ b := Nat.minFac_le (by omega)
          omega
        have hb2 : b % 2 = 1 := by
          have h : ¬ 2 ∣ b := fun h => h2 (by rw [hb]; exact Dvd.dvd.mul_left h _)
          omega
        have hb3 : b % 3 ≠ 0 := by
          have h : ¬ 3 ∣ b := fun h => h3 (by rw [hb]; exact Dvd.dvd.mul_left h _)
          omega
        rcases Nat.lt_or_ge (q % 3) 2 with hq1 | hq1
        · have hq1' : q % 3 = 1 := by omega
          have hle : q * 3 ≤ q * b := Nat.mul_le_mul_left q (by omega)
          refine ⟨q, by omega, by rw [hb]; omega, ?_⟩
          have hm : 2 * k % 3 = 2 * b % 3 := by
            rw [hb, show 2 * (q * b) = q * (2 * b) by ring, Nat.mul_mod, hq1', one_mul, Nat.mod_mod]
          rw [G k q (2 * b) 3 (by rw [hb]; ring) hq.pos]
          unfold fracVal
          rw [hm]
        · have hq2' : q % 3 = 2 := by omega
          have hb7 : 7 ≤ b := by
            by_contra hlt
            have hb5 : b = 5 := by omega
            have hq5' : q = 5 := by omega
            rw [hb5, hq5'] at hb
            omega
          have hle : q * 6 ≤ q * b := Nat.mul_le_mul_left q (by omega)
          refine ⟨2 * q, by omega, by rw [hb]; omega, ?_⟩
          have hm : 2 * k % 3 = b % 3 := by
            rw [hb, show 2 * (q * b) = (2 * q) * b by ring, Nat.mul_mod,
              show 2 * q % 3 = 1 by omega, one_mul, Nat.mod_mod]
          rw [G k (2 * q) b 3 (by rw [hb]; ring) (by omega)]
          unfold fracVal
          rw [hm]
  · intro p hp hin
    obtain ⟨j, hj2, hjp, heq⟩ := hin
    have hp3 : p ≠ 3 * j := by
      intro h
      have h3 : 3 ∣ p := ⟨j, h⟩
      rcases hp.eq_one_or_self_of_dvd 3 h3 with h' | h'
      · omega
      · omega
    unfold fracVal at heq
    have hq1 : ((3 * j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show 3 * j ≠ 0 by omega)
    have hq2 : ((3 : ℕ) : ℚ) ≠ 0 := by norm_num
    rw [div_eq_div_iff hq1 hq2] at heq
    have hc : 2 * p % (3 * j) * 3 = 2 * p % 3 * (3 * j) := by exact_mod_cast heq
    exact aux p 3 (3 * j) (2 * p / 3) (2 * p / (3 * j)) (2 * p % 3) (2 * p % (3 * j)) hp le_rfl
      (by omega) (by omega) (Nat.div_add_mod _ _) (Nat.div_add_mod _ _) hc.symm
