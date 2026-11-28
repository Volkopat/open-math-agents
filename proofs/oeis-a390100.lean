import OMAStatements.S_oeis_a390100

-- Problem: A390100: Numbers k with exactly three coincident values among the fractions (2*k mod m)/m for 1 <= m <= k.
-- Upstream: formal-conjectures statements/oeis-a390100.lean:0 (declaration OMA.S_oeis_a390100.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: if 2k = g*w then the fraction at m = c*g is (w mod c)/c, so two factorizations
-- 2k = g1*w1 = g2*w2 with w1 = w2 mod c and c*g1, c*g2 <= k give a repeated value. Repeated values
-- of d are repeated values of d*j (scale m by j). For k = j*p (p prime, j <= 3) two equal nonzero
-- fractions at m1 < m2 give m1*m2*t = 2j(m2 - m1) with t >= 1, so m1 < 2j: k = p has only the
-- repeated value 0, k = 2p at most 0 and the value at m = 3, k = 3p exactly 0, 1/2 (m = 4, 12) and
-- (6p mod 5)/5 (m = 5, 30). Every other composite k > 52 is a multiple of a number with four
-- repeated values: 4t, 6t, 9t, 5r, q*r (q, r primes, 7 <= q <= r) or one of eleven small seeds.

set_option maxHeartbeats 1000000 in
open OMA.S_oeis_a390100 in
theorem OMA.solution : type_of% @OMA.S_oeis_a390100.main := by
  have memR : ∀ k m1 m2 : ℕ, 1 ≤ m1 → m1 ≤ k → 1 ≤ m2 → m2 ≤ k → m1 ≠ m2 →
      fracVal k m1 = fracVal k m2 → fracVal k m1 ∈ repeatedValues k := by
    intro k m1 m2 h1 h2 h3 h4 hne heq
    unfold repeatedValues
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨h1, h2⟩), ?_⟩
    have hsub : ({m1, m2} : Finset ℕ) ⊆
        (Finset.Icc 1 k).filter (fun m => fracVal k m = fracVal k m1) := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter, Finset.mem_Icc]
      rcases hx with rfl | rfl
      · exact ⟨⟨h1, h2⟩, rfl⟩
      · exact ⟨⟨h3, h4⟩, heq.symm⟩
    have hc : ({m1, m2} : Finset ℕ).card = 2 := Finset.card_pair hne
    calc 2 = ({m1, m2} : Finset ℕ).card := hc.symm
      _ ≤ _ := Finset.card_le_card hsub
  have memR' : ∀ (k : ℕ) (v : ℚ), v ∈ repeatedValues k → ∃ m1 m2 : ℕ, 1 ≤ m1 ∧ m1 < m2 ∧
      m2 ≤ k ∧ fracVal k m1 = v ∧ fracVal k m2 = v := by
    intro k v hv
    unfold repeatedValues at hv
    rw [Finset.mem_filter] at hv
    have h2 : 2 ≤ ((Finset.Icc 1 k).filter (fun m => fracVal k m = v)).card := hv.2
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
      (show 1 < ((Finset.Icc 1 k).filter (fun m => fracVal k m = v)).card by omega)
    rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, ha.1.1, h, hb.1.2, ha.2, hb.2⟩
    · exact ⟨b, a, hb.1.1, h, ha.1.2, hb.2, ha.2⟩
  have G : ∀ k g w c : ℕ, 2 * k = g * w → 0 < g →
      fracVal k (c * g) = ((w % c : ℕ) : ℚ) / (c : ℚ) := by
    intro k g w c hk hg
    unfold fracVal
    rw [hk, show c * g = g * c by ring, Nat.mul_mod_mul_left]
    have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hg']
  have PV : ∀ k g1 w1 g2 w2 c : ℕ, 2 * k = g1 * w1 → 2 * k = g2 * w2 → 0 < g1 → 0 < g2 →
      g1 ≠ g2 → 0 < c → c * g1 ≤ k → c * g2 ≤ k → w1 % c = w2 % c →
      ((w1 % c : ℕ) : ℚ) / (c : ℚ) ∈ repeatedValues k := by
    intro k g1 w1 g2 w2 c h1 h2 hg1 hg2 hne hc hb1 hb2 hw
    have e1 := G k g1 w1 c h1 hg1
    have e2 := G k g2 w2 c h2 hg2
    rw [← e1]
    refine memR k (c * g1) (c * g2) (Nat.mul_pos hc hg1) hb1 (Nat.mul_pos hc hg2) hb2 ?_ ?_
    · intro h
      exact hne (Nat.eq_of_mul_eq_mul_left hc h)
    · rw [e1, e2, hw]
  have Mono : ∀ k d j : ℕ, k = d * j → 0 < j → repeatedValues d ⊆ repeatedValues k := by
    intro k d j hk hj v hv
    obtain ⟨m1, m2, h1, h12, h2, e1, e2⟩ := memR' d v hv
    have sc : ∀ m : ℕ, fracVal k (m * j) = fracVal d m := by
      intro m
      unfold fracVal
      rw [hk, show 2 * (d * j) = j * (2 * d) by ring, show m * j = j * m by ring,
        Nat.mul_mod_mul_left]
      have hj' : (j : ℚ) ≠ 0 := by exact_mod_cast hj.ne'
      rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hj']
    have hb : m2 * j ≤ k := by
      rw [hk]
      exact Nat.mul_le_mul_right j h2
    have hb1 : m1 * j ≤ k := le_trans (Nat.mul_le_mul_right j h12.le) hb
    have hne : m1 * j ≠ m2 * j := by
      intro h
      have := Nat.eq_of_mul_eq_mul_right hj h
      omega
    have hm := memR k (m1 * j) (m2 * j) (Nat.mul_pos h1 hj) hb1 (Nat.mul_pos (by omega) hj) hb
      hne (by rw [sc, sc, e1, e2])
    rw [sc, e1] at hm
    exact hm
  have card4 : ∀ (S : Finset ℚ) (a b c d : ℚ), a ∈ S → b ∈ S → c ∈ S → d ∈ S → a ≠ b →
      a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → 4 ≤ S.card := by
    intro S a b c d ha hb hc hd hab hac had hbc hbd hcd
    have hsub : ({a, b, c, d} : Finset ℚ) ⊆ S := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact hd
    have h1 : c ∉ ({d} : Finset ℚ) := by
      rw [Finset.mem_singleton]
      exact hcd
    have h2 : b ∉ ({c, d} : Finset ℚ) := by
      rw [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hbc h
      · exact hbd h
    have h3 : a ∉ ({b, c, d} : Finset ℚ) := by
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h | h)
      · exact hab h
      · exact hac h
      · exact had h
    have hcard : ({a, b, c, d} : Finset ℚ).card = 4 := by
      rw [Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h1, Finset.card_singleton]
    calc 4 = ({a, b, c, d} : Finset ℚ).card := hcard.symm
      _ ≤ S.card := Finset.card_le_card hsub
  have NE : ∀ a b c d : ℕ, 0 < b → 0 < d → a * d ≠ c * b →
      (a : ℚ) / (b : ℚ) ≠ (c : ℚ) / (d : ℚ) := by
    intro a b c d hb hd h h'
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [div_eq_div_iff hb' hd'] at h'
    exact h (by exact_mod_cast h')
  have D : ∀ a b c d : ℕ, 0 < b → 0 < d → Nat.Coprime a b → Nat.Coprime c d → b ≠ d →
      (a : ℚ) / (b : ℚ) ≠ (c : ℚ) / (d : ℚ) := by
    intro a b c d hb hd hab hcd hbd h'
    have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [div_eq_div_iff hb' hd'] at h'
    have h : a * d = c * b := by exact_mod_cast h'
    have h1 : b ∣ d := (Nat.Coprime.symm hab).dvd_of_dvd_mul_left ⟨c, by rw [h]; ring⟩
    have h2 : d ∣ b := (Nat.Coprime.symm hcd).dvd_of_dvd_mul_left ⟨a, by rw [← h]; ring⟩
    exact hbd (Nat.dvd_antisymm h1 h2)
  have CM : ∀ w c : ℕ, Nat.Coprime w c → Nat.Coprime (w % c) c := by
    intro w c h
    show Nat.gcd (w % c) c = 1
    rw [← Nat.gcd_rec]
    exact Nat.Coprime.symm h
  have Z : ∀ k : ℕ, 2 ≤ k → ((0 : ℕ) : ℚ) / ((1 : ℕ) : ℚ) ∈ repeatedValues k := by
    intro k hk
    have e1 : fracVal k 1 = ((0 : ℕ) : ℚ) / ((1 : ℕ) : ℚ) := by
      unfold fracVal
      rw [Nat.mod_one]
    have e2 : fracVal k 2 = ((0 : ℕ) : ℚ) / ((1 : ℕ) : ℚ) := by
      unfold fracVal
      rw [Nat.mul_mod_right]
      simp
    rw [← e1]
    exact memR k 1 2 le_rfl (by omega) (by omega) hk (by norm_num) (by rw [e1, e2])
  have pm : ∀ p a : ℕ, p.Prime → 2 ≤ a → a < p → p % a ≠ 0 := by
    intro p a hp ha hap h0
    rcases hp.eq_one_or_self_of_dvd a (Nat.dvd_of_mod_eq_zero h0) with h | h <;> omega
  have aux : ∀ p j a b q1 q2 r1 r2 : ℕ, p.Prime → 1 ≤ j → 1 ≤ a → a < b → ¬ p ∣ a →
      ¬ p ∣ b → a * q1 + r1 = 2 * (j * p) → b * q2 + r2 = 2 * (j * p) → r1 * b = r2 * a →
      a < 2 * j := by
    intro p j a b q1 q2 r1 r2 hp hj ha hab hpa hpb E1 E2 E3
    have Z1 : (a : ℤ) * q1 + r1 = 2 * (j * p) := by exact_mod_cast E1
    have Z2 : (b : ℤ) * q2 + r2 = 2 * (j * p) := by exact_mod_cast E2
    have Z3 : (r1 : ℤ) * b = r2 * a := by exact_mod_cast E3
    have hZ : (a : ℤ) * b * ((q1 : ℤ) - q2) = (p : ℤ) * (2 * j * ((b : ℤ) - a)) := by
      linear_combination (b : ℤ) * Z1 - (a : ℤ) * Z2 - Z3
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hpa' : ¬ (p : ℤ) ∣ (a : ℤ) := fun h => hpa (Int.natCast_dvd_natCast.mp h)
    have hpb' : ¬ (p : ℤ) ∣ (b : ℤ) := fun h => hpb (Int.natCast_dvd_natCast.mp h)
    have hdvd : (p : ℤ) ∣ (a : ℤ) * b * ((q1 : ℤ) - q2) := Dvd.intro _ hZ.symm
    obtain ⟨t, ht⟩ : (p : ℤ) ∣ ((q1 : ℤ) - q2) := by
      rcases hpZ.dvd_or_dvd hdvd with h | h
      · rcases hpZ.dvd_or_dvd h with h' | h'
        · exact absurd h' hpa'
        · exact absurd h' hpb'
      · exact h
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hk : (a : ℤ) * b * t = 2 * j * ((b : ℤ) - a) := by
      apply mul_left_cancel₀ hp0
      rw [ht] at hZ
      linear_combination hZ
    have ha1 : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hab' : (a : ℤ) < b := by exact_mod_cast hab
    have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
    have hab0 : (0 : ℤ) ≤ (a : ℤ) * b := by positivity
    have hpos : (0 : ℤ) < 2 * j * ((b : ℤ) - a) := mul_pos (by linarith) (by linarith)
    rcases le_or_gt t 0 with ht0 | ht0
    · have h1 : 0 ≤ (a : ℤ) * b * (-t) := mul_nonneg hab0 (by linarith)
      linarith
    · have h1 : (a : ℤ) * b * 1 ≤ (a : ℤ) * b * t := mul_le_mul_of_nonneg_left (by omega) hab0
      by_contra hcon
      have h2 : (2 * j : ℤ) ≤ a := by exact_mod_cast (show 2 * j ≤ a by omega)
      have h3 : (2 * j : ℤ) * b ≤ (a : ℤ) * b := mul_le_mul_of_nonneg_right h2 (by positivity)
      have h4 : (0 : ℤ) < j * a := mul_pos (by linarith) (by linarith)
      linarith
  have NZ : ∀ p j m : ℕ, p.Prime → 1 ≤ j → j ≤ 3 → 1 ≤ m → m ≤ j * p → p ∣ m →
      2 * (j * p) % m = 0 := by
    intro p j m hp hj hj3 hm1 hm hpm
    obtain ⟨i, rfl⟩ := hpm
    have hp0 := hp.pos
    have hi1 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with h | h
      · rw [h, mul_zero] at hm1
        omega
      · exact h
    have hij : i ≤ j := by
      by_contra h
      have h5 : p * (j + 1) ≤ p * i := Nat.mul_le_mul_left p (by omega)
      have h6 : p * (j + 1) = j * p + p := by ring
      omega
    have hdiv : i ∣ 2 * j := by
      interval_cases j <;> interval_cases i <;> norm_num
    apply Nat.mod_eq_zero_of_dvd
    obtain ⟨c, hc⟩ := hdiv
    exact ⟨c, by rw [show 2 * (j * p) = p * (2 * j) by ring, hc]; ring⟩
  have UB : ∀ (p j k : ℕ) (v : ℚ), p.Prime → 1 ≤ j → j ≤ 3 → k = j * p →
      v ∈ repeatedValues k →
      v = fracVal k 1 ∨ ∃ m : ℕ, 1 ≤ m ∧ m < 2 * j ∧ 2 * k % m ≠ 0 ∧ v = fracVal k m := by
    intro p j k v hp hj hj3 hk hv
    obtain ⟨m1, m2, h1, h12, h2, e1, e2⟩ := memR' k v hv
    have hq1 : (m1 : ℚ) ≠ 0 := by exact_mod_cast (show m1 ≠ 0 by omega)
    have hq2 : (m2 : ℚ) ≠ 0 := by exact_mod_cast (show m2 ≠ 0 by omega)
    by_cases hr : 2 * k % m1 = 0
    · left
      rw [← e1]
      unfold fracVal
      rw [hr, Nat.mod_one]
      simp
    · right
      refine ⟨m1, h1, ?_, hr, e1.symm⟩
      have hr2 : 2 * k % m2 ≠ 0 := by
        intro h0
        apply hr
        have h3 : fracVal k m1 = fracVal k m2 := by rw [e1, e2]
        unfold fracVal at h3
        rw [h0, Nat.cast_zero, zero_div, div_eq_zero_iff] at h3
        rcases h3 with h | h
        · exact_mod_cast h
        · exact absurd h hq1
      have hc : fracVal k m1 = fracVal k m2 := by rw [e1, e2]
      unfold fracVal at hc
      rw [div_eq_div_iff hq1 hq2] at hc
      have E3 : 2 * k % m1 * m2 = 2 * k % m2 * m1 := by exact_mod_cast hc
      subst hk
      exact aux p j m1 m2 (2 * (j * p) / m1) (2 * (j * p) / m2) _ _ hp hj h1 h12
        (fun h => hr (NZ p j m1 hp hj hj3 h1 (by omega) h))
        (fun h => hr2 (NZ p j m2 hp hj hj3 (by omega) h2 h))
        (Nat.div_add_mod _ _) (Nat.div_add_mod _ _) E3
  have seedL : ∀ s m1 m2 m3 m4 m5 m6 : ℕ,
      (2 ≤ s ∧ 1 ≤ m1 ∧ m1 < m2 ∧ m2 ≤ s ∧ 1 ≤ m3 ∧ m3 < m4 ∧ m4 ≤ s ∧ 1 ≤ m5 ∧ m5 < m6 ∧
        m6 ≤ s) →
      (fracVal s m1 = fracVal s m2 ∧ fracVal s m3 = fracVal s m4 ∧
        fracVal s m5 = fracVal s m6) →
      (fracVal s m1 ≠ 0 ∧ fracVal s m3 ≠ 0 ∧ fracVal s m5 ≠ 0 ∧ fracVal s m1 ≠ fracVal s m3 ∧
        fracVal s m1 ≠ fracVal s m5 ∧ fracVal s m3 ≠ fracVal s m5) →
      4 ≤ (repeatedValues s).card := by
    intro s m1 m2 m3 m4 m5 m6 hb he hd
    obtain ⟨hs, a1, a2, a3, b1, b2, b3, c1, c2, c3⟩ := hb
    obtain ⟨e1, e2, e3⟩ := he
    obtain ⟨n1, n2, n3, d12, d13, d23⟩ := hd
    have z := Z s hs
    have hz : ((0 : ℕ) : ℚ) / ((1 : ℕ) : ℚ) = 0 := by simp
    rw [hz] at z
    exact card4 _ 0 _ _ _ z (memR s m1 m2 a1 (by omega) (by omega) a3 (by omega) e1)
      (memR s m3 m4 b1 (by omega) (by omega) b3 (by omega) e2)
      (memR s m5 m6 c1 (by omega) (by omega) c3 (by omega) e3)
      (Ne.symm n1) (Ne.symm n2) (Ne.symm n3) d12 d13 d23
  have S35 : 4 ≤ (repeatedValues 35).card :=
    seedL 35 3 21 4 20 6 15 (by norm_num) (by norm_num [fracVal]) (by norm_num [fracVal])
  have S48 : 4 ≤ (repeatedValues 48).card :=
    seedL 48 5 30 9 36 15 40 (by norm_num) (by norm_num [fracVal]) (by norm_num [fracVal])
  have S50 : 4 ≤ (repeatedValues 50).card :=
    seedL 50 3 12 6 15 8 40 (by norm_num) (by norm_num [fracVal]) (by norm_num [fracVal])
  have S54 : 4 ≤ (repeatedValues 54).card :=
    seedL 54 5 30 8 24 20 45 (by norm_num) (by norm_num [fracVal]) (by norm_num [fracVal])
  have S56 : 4 ≤ (repeatedValues 56).card :=
    seedL 56 3 12 6 24 10 35 (by norm_num) (by norm_num [fracVal]) (by norm_num [fracVal])
  have S60 : 4 ≤ (repeatedValues 60).card :=
    seedL 60 7 56 9 36 16 48 (by norm_num) (by norm_num [fracVal]) (by norm_num [fracVal])
  have S63 : 4 ≤ (repeatedValues 63).card :=
    seedL 63 4 12 5 30 10 35 (by norm_num) (by norm_num [fracVal]) (by norm_num [fracVal])
  have S72 : 4 ≤ (repeatedValues 72).card :=
    seedL 72 5 30 7 56 10 60 (by norm_num) (by norm_num [fracVal]) (by norm_num [fracVal])
  have S75 : 4 ≤ (repeatedValues 75).card :=
    seedL 75 4 12 8 40 18 45 (by norm_num) (by norm_num [fracVal]) (by norm_num [fracVal])
  have S90 : 4 ≤ (repeatedValues 90).card :=
    seedL 90 8 24 14 63 16 80 (by norm_num) (by norm_num [fracVal]) (by norm_num [fracVal])
  have S135 : 4 ≤ (repeatedValues 135).card :=
    seedL 135 4 36 8 72 14 63 (by norm_num) (by norm_num [fracVal]) (by norm_num [fracVal])
  have F4 : ∀ t : ℕ, t % 3 ≠ 0 → t % 7 ≠ 0 → 14 ≤ t → 4 ≤ (repeatedValues (4 * t)).card := by
    intro t h3 h7 ht
    have v1 := PV (4 * t) 8 t 2 (4 * t) 3 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v2 := PV (4 * t) 4 (2 * t) 1 (8 * t) 3 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v3 := PV (4 * t) 8 t 1 (8 * t) 7 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    exact card4 _ _ _ _ _ (Z (4 * t) (by omega)) v1 v2 v3
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
  have F6 : ∀ t : ℕ, t % 2 = 1 → t % 3 ≠ 0 → t % 5 ≠ 0 → 6 ≤ t →
      4 ≤ (repeatedValues (6 * t)).card := by
    intro t h2 h3 h5 ht
    have v1 := PV (6 * t) 12 t 4 (3 * t) 2 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v2 := PV (6 * t) 12 t 3 (4 * t) 3 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v3 := PV (6 * t) 6 (2 * t) 1 (12 * t) 5 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    exact card4 _ _ _ _ _ (Z (6 * t) (by omega)) v1 v2 v3
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
  have F9 : ∀ t : ℕ, t % 2 = 1 → t % 5 ≠ 0 → 8 ≤ t → 4 ≤ (repeatedValues (9 * t)).card := by
    intro t h2 h5 ht
    have v1 := PV (9 * t) 18 t 6 (3 * t) 2 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v2 := PV (9 * t) 18 t 2 (9 * t) 4 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v3 := PV (9 * t) 6 (3 * t) 1 (18 * t) 5 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    exact card4 _ _ _ _ _ (Z (9 * t) (by omega)) v1 v2 v3
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
  have F5 : ∀ r : ℕ, r % 2 = 1 → r % 3 ≠ 0 → 8 ≤ r → 4 ≤ (repeatedValues (5 * r)).card := by
    intro r h2 h3 hr
    have v1 := PV (5 * r) 10 r 2 (5 * r) 2 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v2 := PV (5 * r) 10 r 2 (5 * r) 4 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v3 := PV (5 * r) 5 (2 * r) 2 (5 * r) 3 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    exact card4 _ _ _ _ _ (Z (5 * r) (by omega)) v1 v2 v3
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
  have FQ : ∀ s c r : ℕ, 3 ≤ s → c + 1 = 2 * s → r.Prime → c + 2 ≤ r →
      4 ≤ (repeatedValues ((c + 2) * r)).card := by
    intro s c r hs hcs hr hcr
    have hA : (c + 2) * 4 ≤ (c + 2) * r := Nat.mul_le_mul_left _ (by omega)
    have hq : c + 2 = 2 * s + 1 := by omega
    have i1 : (c + 2) * r = r + 2 * (s * r) := by
      rw [hq]
      ring
    have i2 : (c + 2) * r = r + s * (2 * r) := by
      rw [hq]
      ring
    have i3 : (c + 2) * r = 2 * r + c * r := by ring
    have v1 := PV ((c + 2) * r) (2 * (c + 2)) r 2 ((c + 2) * r) 2 (by ring) (by ring)
      (by omega) (by norm_num) (by omega) (by norm_num)
      (by
        calc 2 * (2 * (c + 2)) = (c + 2) * 4 := by ring
          _ ≤ (c + 2) * r := hA)
      (by omega)
      (by rw [i1, Nat.add_mul_mod_self_left])
    have v2 := PV ((c + 2) * r) (2 * (c + 2)) r 2 ((c + 2) * r) s (by ring) (by ring)
      (by omega) (by norm_num) (by omega) (by omega)
      (by
        calc s * (2 * (c + 2)) = (c + 2) * (2 * s) := by ring
          _ ≤ (c + 2) * r := Nat.mul_le_mul_left _ (by omega))
      (by omega)
      (by rw [i2, Nat.add_mul_mod_self_left])
    have v3 := PV ((c + 2) * r) (c + 2) (2 * r) 2 ((c + 2) * r) c (by ring) (by ring)
      (by omega) (by norm_num) (by omega) (by omega)
      (by
        calc c * (c + 2) = (c + 2) * c := by ring
          _ ≤ (c + 2) * r := Nat.mul_le_mul_left _ (by omega))
      (by omega)
      (by rw [i3, Nat.add_mul_mod_self_left])
    have cop0 : Nat.Coprime 0 1 := Nat.coprime_one_right 0
    have cop2 : Nat.Coprime (r % 2) 2 :=
      CM r 2 (Nat.coprime_of_lt_prime (by norm_num) (by omega) hr)
    have cops : Nat.Coprime (r % s) s :=
      CM r s (Nat.coprime_of_lt_prime (by omega) (by omega) hr)
    have h2c : Nat.Coprime 2 c := by
      show Nat.gcd 2 c = 1
      rw [Nat.gcd_rec, show c % 2 = 1 by omega, Nat.gcd_one_left]
    have copc : Nat.Coprime (2 * r % c) c :=
      CM (2 * r) c (Nat.coprime_mul_iff_left.mpr
        ⟨h2c, Nat.coprime_of_lt_prime (by omega) (by omega) hr⟩)
    exact card4 _ _ _ _ _ (Z ((c + 2) * r) (by omega)) v1 v2 v3
      (D _ _ _ _ (by norm_num) (by norm_num) cop0 cop2 (by norm_num))
      (D _ _ _ _ (by norm_num) (by omega) cop0 cops (by omega))
      (D _ _ _ _ (by norm_num) (by omega) cop0 copc (by omega))
      (D _ _ _ _ (by norm_num) (by omega) cop2 cops (by omega))
      (D _ _ _ _ (by norm_num) (by omega) cop2 copc (by omega))
      (D _ _ _ _ (by omega) (by omega) cops copc (by omega))
  refine ⟨?_, ?_⟩
  · intro p hp hp7
    unfold InSeq
    have hp2 : p % 2 ≠ 0 := pm p 2 hp le_rfl (by omega)
    have hp3 : p % 3 ≠ 0 := pm p 3 hp (by norm_num) (by omega)
    have hp5 : p % 5 ≠ 0 := pm p 5 hp (by norm_num) (by omega)
    have hp11 : 11 ≤ p := by omega
    have hsub : repeatedValues (3 * p) ⊆
        {fracVal (3 * p) 1, fracVal (3 * p) 4, fracVal (3 * p) 5} := by
      intro v hv
      rcases UB p 3 (3 * p) v hp (by norm_num) le_rfl rfl hv with h | ⟨m, hm1, hm2, hm3, rfl⟩
      · rw [h]
        simp
      · have hm6 : m < 6 := by omega
        interval_cases m
        · exact absurd (Nat.mod_one _) hm3
        · exact absurd (Nat.mul_mod_right 2 (3 * p)) hm3
        · exact absurd (show 2 * (3 * p) % 3 = 0 by omega) hm3
        · simp
        · simp
    have m1 : fracVal (3 * p) 1 ∈ repeatedValues (3 * p) :=
      memR _ 1 2 le_rfl (by omega) (by norm_num) (by omega) (by norm_num)
        (by
          unfold fracVal
          rw [Nat.mod_one, Nat.mul_mod_right]
          simp)
    have m4 : fracVal (3 * p) 4 ∈ repeatedValues (3 * p) :=
      memR _ 4 12 (by norm_num) (by omega) (by norm_num) (by omega) (by norm_num)
        (by
          unfold fracVal
          rw [show 2 * (3 * p) % 4 = 2 by omega, show 2 * (3 * p) % 12 = 6 by omega]
          norm_num)
    have m5 : fracVal (3 * p) 5 ∈ repeatedValues (3 * p) :=
      memR _ 5 30 (by norm_num) (by omega) (by norm_num) (by omega) (by norm_num)
        (by
          unfold fracVal
          rw [show 2 * (3 * p) % 5 = p % 5 by omega,
            show 2 * (3 * p) % 30 = 6 * (p % 5) by omega]
          push_cast
          ring)
    have h14 : fracVal (3 * p) 1 ≠ fracVal (3 * p) 4 :=
      NE (2 * (3 * p) % 1) 1 (2 * (3 * p) % 4) 4 (by norm_num) (by norm_num) (by omega)
    have h15 : fracVal (3 * p) 1 ≠ fracVal (3 * p) 5 :=
      NE (2 * (3 * p) % 1) 1 (2 * (3 * p) % 5) 5 (by norm_num) (by norm_num) (by omega)
    have h45 : fracVal (3 * p) 4 ≠ fracVal (3 * p) 5 :=
      NE (2 * (3 * p) % 4) 4 (2 * (3 * p) % 5) 5 (by norm_num) (by norm_num) (by omega)
    have heq : repeatedValues (3 * p) =
        {fracVal (3 * p) 1, fracVal (3 * p) 4, fracVal (3 * p) 5} := by
      apply Finset.Subset.antisymm hsub
      intro v hv
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact m1
      · exact m4
      · exact m5
    rw [heq]
    exact Finset.card_eq_three.mpr ⟨_, _, _, h14, h15, h45, rfl⟩
  · intro k hk hIn
    by_contra hne
    unfold InSeq at hIn
    have four : ∀ d j : ℕ, k = d * j → 0 < j → 4 ≤ (repeatedValues d).card → False := by
      intro d j hdj hj h4
      have := Finset.card_le_card (Mono k d j hdj hj)
      omega
    obtain ⟨e, k1, h2k1, hk1⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (show k ≠ 0 by omega) 2 (by norm_num)
    have hk10 : k1 ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk1
      omega
    obtain ⟨f, v, h3v, hv⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk10 3 (by norm_num)
    have h2v : ¬ 2 ∣ v := fun h => h2k1 (by rw [hv]; exact Dvd.dvd.mul_left h _)
    have hkf : k = 2 ^ e * (3 ^ f * v) := by rw [hk1, hv]
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [mul_zero, mul_zero] at hkf
      omega
    have hv2 : v % 2 = 1 := by omega
    have hv3 : v % 3 ≠ 0 := by omega
    rcases Nat.lt_or_ge v 2 with hv1 | hv1
    · -- v = 1, k = 2^e 3^f
      have hv1' : v = 1 := by omega
      subst hv1'
      rw [mul_one] at hkf
      rcases Nat.lt_or_ge f 3 with hf | hf
      · interval_cases f
        · rw [pow_zero, mul_one] at hkf
          rcases Nat.lt_or_ge e 6 with he | he
          · have h32 : 2 ^ e ≤ 32 := by
              calc 2 ^ e ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
                _ = 32 := by norm_num
            omega
          · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 6 := ⟨e - 6, by omega⟩
            exact four (4 * 16) (2 ^ e') (by rw [hkf]; ring) (by positivity)
              (F4 16 (by norm_num) (by norm_num) (by norm_num))
        · rw [pow_one] at hkf
          rcases Nat.lt_or_ge e 4 with he | he
          · have h8 : 2 ^ e ≤ 8 := by
              calc 2 ^ e ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
                _ = 8 := by norm_num
            omega
          · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 4 := ⟨e - 4, by omega⟩
            exact four 48 (2 ^ e') (by rw [hkf]; ring) (by positivity) S48
        · rcases Nat.lt_or_ge e 3 with he | he
          · have h4 : 2 ^ e ≤ 4 := by
              calc 2 ^ e ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
                _ = 4 := by norm_num
            have hk9 : k = 2 ^ e * 9 := by rw [hkf]; ring
            omega
          · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 3 := ⟨e - 3, by omega⟩
            exact four 72 (2 ^ e') (by rw [hkf]; ring) (by positivity) S72
      · rcases Nat.lt_or_ge e 1 with he | he
        · have he0 : e = 0 := by omega
          subst he0
          rw [pow_zero, one_mul] at hkf
          rcases Nat.lt_or_ge f 4 with hf4 | hf4
          · have hf3 : f = 3 := by omega
            subst hf3
            norm_num at hkf
            omega
          · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 4 := ⟨f - 4, by omega⟩
            exact four (9 * 9) (3 ^ f') (by rw [hkf]; ring) (by positivity)
              (F9 9 (by norm_num) (by norm_num) (by norm_num))
        · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
          obtain ⟨f', rfl⟩ : ∃ f', f = f' + 3 := ⟨f - 3, by omega⟩
          exact four 54 (2 ^ e' * 3 ^ f') (by rw [hkf]; ring) (by positivity) S54
    · by_cases hvp : v.Prime
      · -- v = p prime, p >= 5
        have hv5 : 5 ≤ v := by
          have := hvp.two_le
          omega
        rcases Nat.lt_or_ge e 2 with he | he
        · rcases Nat.lt_or_ge e 1 with he1 | he1
          · have he0 : e = 0 := by omega
            subst he0
            rw [pow_zero, one_mul] at hkf
            rcases Nat.lt_or_ge f 2 with hf | hf
            · interval_cases f
              · rw [pow_zero, one_mul] at hkf
                have hsub : repeatedValues k ⊆ {fracVal k 1} := by
                  intro x hx
                  rcases UB v 1 k x hvp le_rfl (by norm_num) (by omega) hx with
                    h | ⟨m, hm1, hm2, hm3, rfl⟩
                  · rw [h]
                    exact Finset.mem_singleton_self _
                  · have hm : m = 1 := by omega
                    subst hm
                    exact absurd (Nat.mod_one _) hm3
                have h1 := Finset.card_le_card hsub
                rw [Finset.card_singleton] at h1
                omega
              · rw [pow_one] at hkf
                exact hne ⟨v, hvp, by omega, hkf⟩
            · rcases Nat.lt_or_ge v 8 with hv8 | hv8
              · have hv57 : v = 5 ∨ v = 7 := by omega
                rcases hv57 with rfl | rfl
                · rcases Nat.lt_or_ge f 3 with hf3 | hf3
                  · have hf2 : f = 2 := by omega
                    subst hf2
                    norm_num at hkf
                    omega
                  · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 3 := ⟨f - 3, by omega⟩
                    exact four 135 (3 ^ f') (by rw [hkf]; ring) (by positivity) S135
                · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
                  exact four 63 (3 ^ f') (by rw [hkf]; ring) (by positivity) S63
              · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
                exact four (9 * v) (3 ^ f') (by rw [hkf]; ring) (by positivity)
                  (F9 v hv2 (pm v 5 hvp (by norm_num) (by omega)) hv8)
          · have he1' : e = 1 := by omega
            subst he1'
            rw [pow_one] at hkf
            rcases Nat.lt_or_ge f 1 with hf | hf
            · have hf0 : f = 0 := by omega
              subst hf0
              rw [pow_zero, one_mul] at hkf
              have hsub : repeatedValues k ⊆ {fracVal k 1, fracVal k 3} := by
                intro x hx
                rcases UB v 2 k x hvp (by norm_num) (by norm_num) (by omega) hx with
                  h | ⟨m, hm1, hm2, hm3, rfl⟩
                · rw [h]
                  simp
                · have hm4 : m < 4 := by omega
                  interval_cases m
                  · exact absurd (Nat.mod_one _) hm3
                  · exact absurd (Nat.mul_mod_right 2 k) hm3
                  · simp
              have h1 := Finset.card_le_card hsub
              have h2 : ({fracVal k 1, fracVal k 3} : Finset ℚ).card ≤ 2 := Finset.card_le_two
              omega
            · rcases Nat.lt_or_ge v 7 with hv7 | hv7
              · have hv5e : v = 5 := by omega
                subst hv5e
                rcases Nat.lt_or_ge f 2 with hf2 | hf2
                · have hf1 : f = 1 := by omega
                  subst hf1
                  norm_num at hkf
                  omega
                · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
                  exact four 90 (3 ^ f') (by rw [hkf]; ring) (by positivity) S90
              · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
                exact four (6 * v) (3 ^ f') (by rw [hkf]; ring) (by positivity)
                  (F6 v hv2 hv3 (pm v 5 hvp (by norm_num) (by omega)) (by omega))
        · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
          by_cases hbig : 14 ≤ v ∧ v % 7 ≠ 0
          · exact four (4 * v) (2 ^ e' * 3 ^ f) (by rw [hkf]; ring) (by positivity)
              (F4 v hv3 hbig.2 hbig.1)
          · have hv7or : v = 5 ∨ v = 7 ∨ v = 11 ∨ v = 13 := by
              by_contra hcon
              exact hbig ⟨by omega, pm v 7 hvp (by norm_num) (by omega)⟩
            rcases Nat.lt_or_ge f 1 with hf | hf
            · have hf0 : f = 0 := by omega
              subst hf0
              rw [pow_zero, one_mul] at hkf
              rcases hv7or with rfl | rfl | rfl | rfl
              · rcases Nat.lt_or_ge e' 2 with he2 | he2
                · have h2' : 2 ^ e' ≤ 2 := by
                    calc 2 ^ e' ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
                      _ = 2 := by norm_num
                  have hk20 : k = 2 ^ e' * 20 := by rw [hkf]; ring
                  omega
                · obtain ⟨e'', rfl⟩ : ∃ e'', e' = e'' + 2 := ⟨e' - 2, by omega⟩
                  exact four (4 * 20) (2 ^ e'') (by rw [hkf]; ring) (by positivity)
                    (F4 20 (by norm_num) (by norm_num) (by norm_num))
              · rcases Nat.lt_or_ge e' 1 with he1 | he1
                · have he0 : e' = 0 := by omega
                  subst he0
                  norm_num at hkf
                  omega
                · obtain ⟨e'', rfl⟩ : ∃ e'', e' = e'' + 1 := ⟨e' - 1, by omega⟩
                  exact four 56 (2 ^ e'') (by rw [hkf]; ring) (by positivity) S56
              · rcases Nat.lt_or_ge e' 1 with he1 | he1
                · have he0 : e' = 0 := by omega
                  subst he0
                  norm_num at hkf
                  omega
                · obtain ⟨e'', rfl⟩ : ∃ e'', e' = e'' + 1 := ⟨e' - 1, by omega⟩
                  exact four (4 * 22) (2 ^ e'') (by rw [hkf]; ring) (by positivity)
                    (F4 22 (by norm_num) (by norm_num) (by norm_num))
              · rcases Nat.lt_or_ge e' 1 with he1 | he1
                · have he0 : e' = 0 := by omega
                  subst he0
                  norm_num at hkf
                  omega
                · obtain ⟨e'', rfl⟩ : ∃ e'', e' = e'' + 1 := ⟨e' - 1, by omega⟩
                  exact four (4 * 26) (2 ^ e'') (by rw [hkf]; ring) (by positivity)
                    (F4 26 (by norm_num) (by norm_num) (by norm_num))
            · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
              rcases hv7or with rfl | h7
              · exact four 60 (2 ^ e' * 3 ^ f') (by rw [hkf]; ring) (by positivity) S60
              · exact four (6 * v) (2 ^ (e' + 1) * 3 ^ f') (by rw [hkf]; ring) (by positivity)
                  (F6 v hv2 hv3 (by omega) (by omega))
      · -- v composite, prime factors at least 5
        have hv1' : v ≠ 1 := by omega
        obtain ⟨q, hq, hqv, hqmin⟩ : ∃ q, q.Prime ∧ q ∣ v ∧ ∀ r, r.Prime → r ∣ v → q ≤ r :=
          ⟨v.minFac, Nat.minFac_prime hv1', Nat.minFac_dvd v,
            fun r hr hrv => Nat.minFac_le_of_dvd hr.two_le hrv⟩
        obtain ⟨v', hv'⟩ := hqv
        have hq2 : q % 2 = 1 := by
          have h : ¬ 2 ∣ q := fun h => h2v (by rw [hv']; exact Dvd.dvd.mul_right h _)
          omega
        have hq3 : q % 3 ≠ 0 := by
          have h : ¬ 3 ∣ q := fun h => h3v (by rw [hv']; exact Dvd.dvd.mul_right h _)
          omega
        have hq5 : 5 ≤ q := by
          have := hq.two_le
          omega
        have hv'2 : v' % 2 = 1 := by
          have h : ¬ 2 ∣ v' := fun h => h2v (by rw [hv']; exact Dvd.dvd.mul_left h _)
          omega
        have hv'3 : v' % 3 ≠ 0 := by
          have h : ¬ 3 ∣ v' := fun h => h3v (by rw [hv']; exact Dvd.dvd.mul_left h _)
          omega
        have hv'ne : v' ≠ 1 := by
          rintro rfl
          rw [mul_one] at hv'
          exact hvp (by rw [hv']; exact hq)
        rcases Nat.lt_or_ge q 7 with hq7 | hq7
        · have hq5e : q = 5 := by omega
          subst hq5e
          rcases Nat.lt_or_ge v' 8 with hv8 | hv8
          · have hv57 : v' = 5 ∨ v' = 7 := by omega
            rcases hv57 with rfl | rfl
            · rcases Nat.lt_or_ge e 1 with he | he
              · rcases Nat.lt_or_ge f 1 with hf | hf
                · have he0 : e = 0 := by omega
                  have hf0 : f = 0 := by omega
                  subst he0
                  subst hf0
                  rw [hv'] at hkf
                  norm_num at hkf
                  omega
                · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
                  exact four 75 (2 ^ e * 3 ^ f') (by rw [hkf, hv']; ring) (by positivity) S75
              · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
                exact four 50 (2 ^ e' * 3 ^ f) (by rw [hkf, hv']; ring) (by positivity) S50
            · exact four 35 (2 ^ e * 3 ^ f) (by rw [hkf, hv']; ring) (by positivity) S35
          · exact four (5 * v') (2 ^ e * 3 ^ f) (by rw [hkf, hv']; ring) (by positivity)
              (F5 v' hv'2 hv'3 hv8)
        · obtain ⟨r, hr, hrv'⟩ : ∃ r, r.Prime ∧ r ∣ v' :=
            ⟨v'.minFac, Nat.minFac_prime hv'ne, Nat.minFac_dvd v'⟩
          have hqr : q ≤ r := hqmin r hr (by rw [hv']; exact Dvd.dvd.mul_left hrv' q)
          obtain ⟨w, hw⟩ := hrv'
          have hw0 : 0 < w := by
            rcases Nat.eq_zero_or_pos w with h | h
            · rw [h, mul_zero] at hw
              omega
            · exact h
          have hFQ := FQ (q / 2) (q - 2) r (by omega) (by omega) hr (by omega)
          exact four ((q - 2 + 2) * r) (2 ^ e * 3 ^ f * w)
            (by rw [hkf, hv', hw, show q - 2 + 2 = q by omega]; ring)
            (Nat.mul_pos (by positivity) hw0) hFQ
