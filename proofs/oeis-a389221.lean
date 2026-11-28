import OMAStatements.S_oeis_a389221

-- Problem: A389221: Numbers k with exactly four coincident values among the fractions (2*k mod m)/m for 1 <= m <= k.
-- Upstream: formal-conjectures statements/oeis-a389221.lean:0 (declaration OMA.S_oeis_a389221.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: if 2k = g*w then the fraction at m = c*g is (w mod c)/c, so two factorizations
-- 2k = g1*w1 = g2*w2 with w1 = w2 mod c and c*g1, c*g2 <= k give a repeated value. Repeated values
-- of d are repeated values of d*j (scale m by j). For k = j*p (p prime, j <= 4) two equal nonzero
-- fractions at m1 < m2 with p not dividing m1, m2 give m1*m2*t = 2j(m2 - m1) with t >= 1, so
-- m1 < 2j. Hence p, 2p, 3p have at most 1, 2, 3 repeated values, and for p > 13 the repeated
-- values of 4p are exactly 0, f(3), f(6), f(7) (m = 3p gives 2/3, which is f(3) or f(6); m1 = 5
-- is impossible). Every other k > 80 is a multiple of a number with five repeated values:
-- 5t, 6t, 8t, 9t (t with small coprimality conditions), q*r (q, r primes, 7 <= q <= r, two cases
-- by q mod 4) or one of sixteen small seeds.

set_option maxHeartbeats 4000000 in
open OMA.S_oeis_a389221 in
theorem OMA.solution : type_of% @OMA.S_oeis_a389221.main := by
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
  have card5 : ∀ (S : Finset ℚ) (a b c d e : ℚ), a ∈ S → b ∈ S → c ∈ S → d ∈ S → e ∈ S →
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
      5 ≤ S.card := by
    intro S a b c d e ha hb hc hd he hab hac had hae hbc hbd hbe hcd hce hde
    have hsub : ({a, b, c, d, e} : Finset ℚ) ⊆ S := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact hd
      · exact he
    have h1 : d ∉ ({e} : Finset ℚ) := by
      rw [Finset.mem_singleton]
      exact hde
    have h2 : c ∉ ({d, e} : Finset ℚ) := by
      rw [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · exact hcd h
      · exact hce h
    have h3 : b ∉ ({c, d, e} : Finset ℚ) := by
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h | h)
      · exact hbc h
      · exact hbd h
      · exact hbe h
    have h4 : a ∉ ({b, c, d, e} : Finset ℚ) := by
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h | h | h)
      · exact hab h
      · exact hac h
      · exact had h
      · exact hae h
    have hcard : ({a, b, c, d, e} : Finset ℚ).card = 5 := by
      rw [Finset.card_insert_of_notMem h4, Finset.card_insert_of_notMem h3,
        Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1, Finset.card_singleton]
    calc 5 = ({a, b, c, d, e} : Finset ℚ).card := hcard.symm
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
  have auxT : ∀ p j a b q1 q2 r1 r2 : ℕ, p.Prime → 1 ≤ j → 1 ≤ a → a < b → ¬ p ∣ a →
      ¬ p ∣ b → a * q1 + r1 = 2 * (j * p) → b * q2 + r2 = 2 * (j * p) → r1 * b = r2 * a →
      ∃ t : ℤ, 0 < t ∧ (a : ℤ) * b * t = 2 * j * ((b : ℤ) - a) := by
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
    refine ⟨t, ?_, hk⟩
    rcases le_or_gt t 0 with ht0 | ht0
    · have h1 : 0 ≤ (a : ℤ) * b * (-t) := mul_nonneg hab0 (by linarith)
      linarith
    · exact ht0
  have aux : ∀ p j a b q1 q2 r1 r2 : ℕ, p.Prime → 1 ≤ j → 1 ≤ a → a < b → ¬ p ∣ a →
      ¬ p ∣ b → a * q1 + r1 = 2 * (j * p) → b * q2 + r2 = 2 * (j * p) → r1 * b = r2 * a →
      a < 2 * j := by
    intro p j a b q1 q2 r1 r2 hp hj ha hab hpa hpb E1 E2 E3
    obtain ⟨t, ht0, hk⟩ := auxT p j a b q1 q2 r1 r2 hp hj ha hab hpa hpb E1 E2 E3
    have ha1 : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hab' : (a : ℤ) < b := by exact_mod_cast hab
    have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
    have hab0 : (0 : ℤ) ≤ (a : ℤ) * b := by positivity
    have h1 : (a : ℤ) * b * 1 ≤ (a : ℤ) * b * t := mul_le_mul_of_nonneg_left (by omega) hab0
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
  have UB4 : ∀ (p : ℕ) (v : ℚ), p.Prime → 13 < p → v ∈ repeatedValues (4 * p) →
      v = fracVal (4 * p) 1 ∨ v = fracVal (4 * p) 3 ∨ v = fracVal (4 * p) 6 ∨
        v = fracVal (4 * p) 7 := by
    intro p v hp hp13 hv
    obtain ⟨m1, m2, h1, h12, h2, e1, e2⟩ := memR' (4 * p) v hv
    have hq1 : (m1 : ℚ) ≠ 0 := by exact_mod_cast (show m1 ≠ 0 by omega)
    have hq2 : (m2 : ℚ) ≠ 0 := by exact_mod_cast (show m2 ≠ 0 by omega)
    have hp3 : p % 3 ≠ 0 := pm p 3 hp (by norm_num) (by omega)
    have T : ∀ m : ℕ, 1 ≤ m → m ≤ 4 * p → p ∣ m → 2 * (4 * p) % m ≠ 0 → m = 3 * p := by
      intro m hm1 hm hpm hr
      obtain ⟨i, rfl⟩ := hpm
      have hp0 := hp.pos
      have hi1 : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with h | h
        · rw [h, mul_zero] at hm1
          omega
        · exact h
      have hi4 : i ≤ 4 := by
        by_contra h
        have h5 : p * 5 ≤ p * i := Nat.mul_le_mul_left p (by omega)
        omega
      interval_cases i
      · exact (hr (Nat.mod_eq_zero_of_dvd ⟨8, by ring⟩)).elim
      · exact (hr (Nat.mod_eq_zero_of_dvd ⟨4, by ring⟩)).elim
      · ring
      · exact (hr (Nat.mod_eq_zero_of_dvd ⟨2, by ring⟩)).elim
    have e3p : fracVal (4 * p) (3 * p) = 2 / 3 := by
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      unfold fracVal
      rw [show 2 * (4 * p) % (3 * p) = 2 * p by
        rw [show 2 * (4 * p) = 2 * p + 3 * p * 2 by ring, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (show 2 * p < 3 * p by omega)]]
      push_cast
      rw [mul_div_mul_right _ _ hp0]
    have V3p : (2 : ℚ) / 3 = fracVal (4 * p) 3 ∨ (2 : ℚ) / 3 = fracVal (4 * p) 6 := by
      rcases (show p % 3 = 1 ∨ p % 3 = 2 by omega) with h | h
      · left
        unfold fracVal
        rw [show 2 * (4 * p) % 3 = 2 by omega]
        norm_num
      · right
        unfold fracVal
        rw [show 2 * (4 * p) % 6 = 4 by omega]
        norm_num
    by_cases hr : 2 * (4 * p) % m1 = 0
    · left
      rw [← e1]
      unfold fracVal
      rw [hr, Nat.mod_one]
      simp
    · right
      have hr2 : 2 * (4 * p) % m2 ≠ 0 := by
        intro h0
        apply hr
        have h3 : fracVal (4 * p) m1 = fracVal (4 * p) m2 := by rw [e1, e2]
        unfold fracVal at h3
        rw [h0, Nat.cast_zero, zero_div, div_eq_zero_iff] at h3
        rcases h3 with h | h
        · exact_mod_cast h
        · exact absurd h hq1
      by_cases hpd1 : p ∣ m1
      · rw [← e1, T m1 h1 (by omega) hpd1 hr, e3p]
        rcases V3p with h | h
        · left
          exact h
        · right
          left
          exact h
      · by_cases hpd2 : p ∣ m2
        · rw [← e2, T m2 (by omega) h2 hpd2 hr2, e3p]
          rcases V3p with h | h
          · left
            exact h
          · right
            left
            exact h
        · have hc : fracVal (4 * p) m1 = fracVal (4 * p) m2 := by rw [e1, e2]
          unfold fracVal at hc
          rw [div_eq_div_iff hq1 hq2] at hc
          have E3 : 2 * (4 * p) % m1 * m2 = 2 * (4 * p) % m2 * m1 := by exact_mod_cast hc
          obtain ⟨t, ht0, hk⟩ := auxT p 4 m1 m2 _ _ _ _ hp (by norm_num) h1 h12 hpd1 hpd2
            (Nat.div_add_mod _ _) (Nat.div_add_mod _ _) E3
          have hm8 : m1 < 2 * 4 := aux p 4 m1 m2 _ _ _ _ hp (by norm_num) h1 h12 hpd1 hpd2
            (Nat.div_add_mod _ _) (Nat.div_add_mod _ _) E3
          have hm8' : m1 < 8 := by omega
          rw [← e1]
          interval_cases m1
          · omega
          · omega
          · left
            rfl
          · omega
          · exfalso
            push_cast at hk
            rcases (show t = 1 ∨ 2 ≤ t by omega) with ht | ht
            · subst ht
              omega
            · have hm2 : (0 : ℤ) ≤ (m2 : ℤ) := by positivity
              nlinarith
          · right
            left
            rfl
          · right
            right
            rfl
  have seedL5 : ∀ s m1 m2 m3 m4 m5 m6 m7 m8 : ℕ,
      (2 ≤ s ∧ 1 ≤ m1 ∧ m1 < m2 ∧ m2 ≤ s ∧ 1 ≤ m3 ∧ m3 < m4 ∧ m4 ≤ s ∧ 1 ≤ m5 ∧ m5 < m6 ∧
        m6 ≤ s ∧ 1 ≤ m7 ∧ m7 < m8 ∧ m8 ≤ s) →
      (fracVal s m1 = fracVal s m2 ∧ fracVal s m3 = fracVal s m4 ∧
        fracVal s m5 = fracVal s m6 ∧ fracVal s m7 = fracVal s m8) →
      (fracVal s m1 ≠ 0 ∧ fracVal s m3 ≠ 0 ∧ fracVal s m5 ≠ 0 ∧ fracVal s m7 ≠ 0 ∧
        fracVal s m1 ≠ fracVal s m3 ∧ fracVal s m1 ≠ fracVal s m5 ∧
        fracVal s m1 ≠ fracVal s m7 ∧ fracVal s m3 ≠ fracVal s m5 ∧
        fracVal s m3 ≠ fracVal s m7 ∧ fracVal s m5 ≠ fracVal s m7) →
      5 ≤ (repeatedValues s).card := by
    intro s m1 m2 m3 m4 m5 m6 m7 m8 hb he hd
    obtain ⟨hs, a1, a2, a3, b1, b2, b3, c1, c2, c3, d1, d2, d3⟩ := hb
    obtain ⟨e1, e2, e3, e4⟩ := he
    obtain ⟨n1, n2, n3, n4, d12, d13, d14, d23, d24, d34⟩ := hd
    have z := Z s hs
    have hz : ((0 : ℕ) : ℚ) / ((1 : ℕ) : ℚ) = 0 := by simp
    rw [hz] at z
    exact card5 _ 0 _ _ _ _ z (memR s m1 m2 a1 (by omega) (by omega) a3 (by omega) e1)
      (memR s m3 m4 b1 (by omega) (by omega) b3 (by omega) e2)
      (memR s m5 m6 c1 (by omega) (by omega) c3 (by omega) e3)
      (memR s m7 m8 d1 (by omega) (by omega) d3 (by omega) e4)
      (Ne.symm n1) (Ne.symm n2) (Ne.symm n3) (Ne.symm n4) d12 d13 d14 d23 d24 d34
  have S81 : 5 ≤ (repeatedValues 81).card :=
    seedL5 81 4 12 5 30 8 72 14 63 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S72 : 5 ≤ (repeatedValues 72).card :=
    seedL5 72 5 30 7 56 10 60 14 63 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S96 : 5 ≤ (repeatedValues 96).card :=
    seedL5 96 5 30 7 56 9 36 10 60 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S108 : 5 ≤ (repeatedValues 108).card :=
    seedL5 108 5 30 7 56 10 60 14 63 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S128 : 5 ≤ (repeatedValues 128).card :=
    seedL5 128 3 12 5 80 6 24 7 56 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S42 : 5 ≤ (repeatedValues 42).card :=
    seedL5 42 5 30 8 24 9 36 10 35 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S60 : 5 ≤ (repeatedValues 60).card :=
    seedL5 60 7 56 9 36 16 48 18 45 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S90 : 5 ≤ (repeatedValues 90).card :=
    seedL5 90 8 24 14 63 16 80 21 70 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S135 : 5 ≤ (repeatedValues 135).card :=
    seedL5 135 4 12 7 105 8 40 14 63 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S63 : 5 ≤ (repeatedValues 63).card :=
    seedL5 63 4 12 5 30 10 35 24 56 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S112 : 5 ≤ (repeatedValues 112).card :=
    seedL5 112 3 12 5 80 6 24 10 35 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S160 : 5 ≤ (repeatedValues 160).card :=
    seedL5 160 3 12 6 15 7 56 9 90 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S75 : 5 ≤ (repeatedValues 75).card :=
    seedL5 75 4 12 8 40 18 45 21 70 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S100 : 5 ≤ (repeatedValues 100).card :=
    seedL5 100 3 12 6 15 7 56 9 90 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S105 : 5 ≤ (repeatedValues 105).card :=
    seedL5 105 4 12 8 40 9 63 18 45 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have S140 : 5 ≤ (repeatedValues 140).card :=
    seedL5 140 3 12 6 15 9 90 16 80 (by norm_num) (by norm_num [fracVal])
      (by norm_num [fracVal])
  have F5 : ∀ t : ℕ, t % 2 = 1 → t % 3 ≠ 0 → 8 ≤ t → 5 ≤ (repeatedValues (5 * t)).card := by
    intro t h2 h3 ht
    have v1 := PV (5 * t) 10 t 2 (5 * t) 2 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v2 := PV (5 * t) 10 t 2 (5 * t) 4 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v3 := PV (5 * t) 5 (2 * t) 2 (5 * t) 3 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v4 := PV (5 * t) 10 t 1 (10 * t) 3 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    exact card5 _ _ _ _ _ _ (Z (5 * t) (by omega)) v1 v2 v3 v4
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
  have F6 : ∀ t : ℕ, t % 2 = 1 → t % 3 ≠ 0 → t % 5 ≠ 0 → 10 ≤ t →
      5 ≤ (repeatedValues (6 * t)).card := by
    intro t h2 h3 h5 ht
    have v1 := PV (6 * t) 12 t 4 (3 * t) 2 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v2 := PV (6 * t) 12 t 3 (4 * t) 3 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v3 := PV (6 * t) 6 (2 * t) 1 (12 * t) 5 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v4 := PV (6 * t) 12 t 2 (6 * t) 5 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    exact card5 _ _ _ _ _ _ (Z (6 * t) (by omega)) v1 v2 v3 v4
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
  have F8 : ∀ t : ℕ, t % 3 ≠ 0 → t % 5 ≠ 0 → t % 7 ≠ 0 → 10 ≤ t →
      5 ≤ (repeatedValues (8 * t)).card := by
    intro t h3 h5 h7 ht
    have v1 := PV (8 * t) 16 t 4 (4 * t) 3 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v2 := PV (8 * t) 8 (2 * t) 2 (8 * t) 3 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v3 := PV (8 * t) 8 (2 * t) 1 (16 * t) 7 (by ring) (by ring) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v4 := PV (8 * t) 16 t 1 (16 * t) 5 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    exact card5 _ _ _ _ _ _ (Z (8 * t) (by omega)) v1 v2 v3 v4
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
  have F9 : ∀ t : ℕ, t % 2 = 1 → t % 5 ≠ 0 → 10 ≤ t → 5 ≤ (repeatedValues (9 * t)).card := by
    intro t h2 h5 ht
    have v1 := PV (9 * t) 18 t 6 (3 * t) 2 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v2 := PV (9 * t) 18 t 2 (9 * t) 4 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v3 := PV (9 * t) 6 (3 * t) 1 (18 * t) 5 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    have v4 := PV (9 * t) 18 t 3 (6 * t) 5 (by ring) (by ring) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by omega) (by omega) (by omega)
    exact card5 _ _ _ _ _ _ (Z (9 * t) (by omega)) v1 v2 v3 v4
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
      (NE _ _ _ _ (by norm_num) (by norm_num) (by omega))
  have FQo : ∀ u r : ℕ, 1 ≤ u → r.Prime → 4 * u + 3 ≤ r →
      5 ≤ (repeatedValues ((4 * u + 3) * r)).card := by
    intro u r hu hr hqr
    have hA : (4 * u + 3) * 4 ≤ (4 * u + 3) * r := Nat.mul_le_mul_left _ (by omega)
    have v1 := PV ((4 * u + 3) * r) (2 * (4 * u + 3)) r 2 ((4 * u + 3) * r) 2 (by ring)
      (by ring) (by omega) (by norm_num) (by omega) (by norm_num)
      (by
        calc 2 * (2 * (4 * u + 3)) = (4 * u + 3) * 4 := by ring
          _ ≤ (4 * u + 3) * r := hA)
      (by omega)
      (by rw [show (4 * u + 3) * r = r + 2 * ((2 * u + 1) * r) by ring,
        Nat.add_mul_mod_self_left])
    have v2 := PV ((4 * u + 3) * r) (2 * (4 * u + 3)) r 2 ((4 * u + 3) * r) (2 * u + 1)
      (by ring) (by ring) (by omega) (by norm_num) (by omega) (by omega)
      (by
        calc (2 * u + 1) * (2 * (4 * u + 3)) = (4 * u + 3) * (4 * u + 2) := by ring
          _ ≤ (4 * u + 3) * r := Nat.mul_le_mul_left _ (by omega))
      (by omega)
      (by rw [show (4 * u + 3) * r = r + (2 * u + 1) * (2 * r) by ring,
        Nat.add_mul_mod_self_left])
    have v3 := PV ((4 * u + 3) * r) (4 * u + 3) (2 * r) 1 (2 * ((4 * u + 3) * r)) (2 * u + 1)
      (by ring) (by ring) (by omega) (by norm_num) (by omega) (by omega)
      (by
        calc (2 * u + 1) * (4 * u + 3) = (4 * u + 3) * (2 * u + 1) := by ring
          _ ≤ (4 * u + 3) * r := Nat.mul_le_mul_left _ (by omega))
      (by omega)
      (by rw [show 2 * ((4 * u + 3) * r) = 2 * r + (2 * u + 1) * (4 * r) by ring,
        Nat.add_mul_mod_self_left])
    have v4 := PV ((4 * u + 3) * r) (4 * u + 3) (2 * r) 2 ((4 * u + 3) * r) (4 * u + 1)
      (by ring) (by ring) (by omega) (by norm_num) (by omega) (by omega)
      (by
        calc (4 * u + 1) * (4 * u + 3) = (4 * u + 3) * (4 * u + 1) := by ring
          _ ≤ (4 * u + 3) * r := Nat.mul_le_mul_left _ (by omega))
      (by omega)
      (by rw [show (4 * u + 3) * r = 2 * r + (4 * u + 1) * r by ring,
        Nat.add_mul_mod_self_left])
    have cop0 : Nat.Coprime 0 1 := Nat.coprime_one_right 0
    have cop2 : Nat.Coprime (r % 2) 2 :=
      CM r 2 (Nat.coprime_of_lt_prime (by norm_num) (by omega) hr)
    have crs : Nat.Coprime r (2 * u + 1) := Nat.coprime_of_lt_prime (by omega) (by omega) hr
    have cops : Nat.Coprime (r % (2 * u + 1)) (2 * u + 1) := CM r _ crs
    have c2s : Nat.Coprime 2 (2 * u + 1) := by
      show Nat.gcd 2 (2 * u + 1) = 1
      rw [Nat.gcd_rec, show (2 * u + 1) % 2 = 1 by omega, Nat.gcd_one_left]
    have cop2s : Nat.Coprime (2 * r % (2 * u + 1)) (2 * u + 1) :=
      CM (2 * r) _ (Nat.coprime_mul_iff_left.mpr ⟨c2s, crs⟩)
    have c2t : Nat.Coprime 2 (4 * u + 1) := by
      show Nat.gcd 2 (4 * u + 1) = 1
      rw [Nat.gcd_rec, show (4 * u + 1) % 2 = 1 by omega, Nat.gcd_one_left]
    have crt : Nat.Coprime r (4 * u + 1) := Nat.coprime_of_lt_prime (by omega) (by omega) hr
    have cop2t : Nat.Coprime (2 * r % (4 * u + 1)) (4 * u + 1) :=
      CM (2 * r) _ (Nat.coprime_mul_iff_left.mpr ⟨c2t, crt⟩)
    have dcd : ((r % (2 * u + 1) : ℕ) : ℚ) / ((2 * u + 1 : ℕ) : ℚ) ≠
        ((2 * r % (2 * u + 1) : ℕ) : ℚ) / ((2 * u + 1 : ℕ) : ℚ) := by
      refine NE _ _ _ _ (by omega) (by omega) ?_
      intro h
      have h1 : r % (2 * u + 1) = 2 * r % (2 * u + 1) :=
        Nat.eq_of_mul_eq_mul_right (by omega) h
      have h2 : (2 * u + 1) ∣ 2 * r - r := (Nat.modEq_iff_dvd' (by omega)).mp h1
      rw [show 2 * r - r = r by omega] at h2
      have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm crs) h2
      omega
    exact card5 _ _ _ _ _ _ (Z ((4 * u + 3) * r) (by omega)) v1 v2 v3 v4
      (D _ _ _ _ (by norm_num) (by norm_num) cop0 cop2 (by norm_num))
      (D _ _ _ _ (by norm_num) (by omega) cop0 cops (by omega))
      (D _ _ _ _ (by norm_num) (by omega) cop0 cop2s (by omega))
      (D _ _ _ _ (by norm_num) (by omega) cop0 cop2t (by omega))
      (D _ _ _ _ (by norm_num) (by omega) cop2 cops (by omega))
      (D _ _ _ _ (by norm_num) (by omega) cop2 cop2s (by omega))
      (D _ _ _ _ (by norm_num) (by omega) cop2 cop2t (by omega))
      dcd
      (D _ _ _ _ (by omega) (by omega) cops cop2t (by omega))
      (D _ _ _ _ (by omega) (by omega) cop2s cop2t (by omega))
  have FQe : ∀ u r : ℕ, 2 ≤ u → r.Prime → 4 * u + 5 ≤ r →
      5 ≤ (repeatedValues ((4 * u + 5) * r)).card := by
    intro u r hu hr hqr
    have hA : (4 * u + 5) * 4 ≤ (4 * u + 5) * r := Nat.mul_le_mul_left _ (by omega)
    have v1 := PV ((4 * u + 5) * r) (2 * (4 * u + 5)) r 2 ((4 * u + 5) * r) 2 (by ring)
      (by ring) (by omega) (by norm_num) (by omega) (by norm_num)
      (by
        calc 2 * (2 * (4 * u + 5)) = (4 * u + 5) * 4 := by ring
          _ ≤ (4 * u + 5) * r := hA)
      (by omega)
      (by rw [show (4 * u + 5) * r = r + 2 * ((2 * u + 2) * r) by ring,
        Nat.add_mul_mod_self_left])
    have v2 := PV ((4 * u + 5) * r) (2 * (4 * u + 5)) r 2 ((4 * u + 5) * r) (2 * u + 2)
      (by ring) (by ring) (by omega) (by norm_num) (by omega) (by omega)
      (by
        calc (2 * u + 2) * (2 * (4 * u + 5)) = (4 * u + 5) * (4 * u + 4) := by ring
          _ ≤ (4 * u + 5) * r := Nat.mul_le_mul_left _ (by omega))
      (by omega)
      (by rw [show (4 * u + 5) * r = r + (2 * u + 2) * (2 * r) by ring,
        Nat.add_mul_mod_self_left])
    have v3 := PV ((4 * u + 5) * r) (2 * (4 * u + 5)) r 2 ((4 * u + 5) * r) (u + 1)
      (by ring) (by ring) (by omega) (by norm_num) (by omega) (by omega)
      (by
        calc (u + 1) * (2 * (4 * u + 5)) = (4 * u + 5) * (2 * u + 2) := by ring
          _ ≤ (4 * u + 5) * r := Nat.mul_le_mul_left _ (by omega))
      (by omega)
      (by rw [show (4 * u + 5) * r = r + (u + 1) * (4 * r) by ring,
        Nat.add_mul_mod_self_left])
    have v4 := PV ((4 * u + 5) * r) (4 * u + 5) (2 * r) 2 ((4 * u + 5) * r) (4 * u + 3)
      (by ring) (by ring) (by omega) (by norm_num) (by omega) (by omega)
      (by
        calc (4 * u + 3) * (4 * u + 5) = (4 * u + 5) * (4 * u + 3) := by ring
          _ ≤ (4 * u + 5) * r := Nat.mul_le_mul_left _ (by omega))
      (by omega)
      (by rw [show (4 * u + 5) * r = 2 * r + (4 * u + 3) * r by ring,
        Nat.add_mul_mod_self_left])
    have cop0 : Nat.Coprime 0 1 := Nat.coprime_one_right 0
    have cop2 : Nat.Coprime (r % 2) 2 :=
      CM r 2 (Nat.coprime_of_lt_prime (by norm_num) (by omega) hr)
    have cops : Nat.Coprime (r % (2 * u + 2)) (2 * u + 2) :=
      CM r _ (Nat.coprime_of_lt_prime (by omega) (by omega) hr)
    have copu : Nat.Coprime (r % (u + 1)) (u + 1) :=
      CM r _ (Nat.coprime_of_lt_prime (by omega) (by omega) hr)
    have c2t : Nat.Coprime 2 (4 * u + 3) := by
      show Nat.gcd 2 (4 * u + 3) = 1
      rw [Nat.gcd_rec, show (4 * u + 3) % 2 = 1 by omega, Nat.gcd_one_left]
    have crt : Nat.Coprime r (4 * u + 3) := Nat.coprime_of_lt_prime (by omega) (by omega) hr
    have cop2t : Nat.Coprime (2 * r % (4 * u + 3)) (4 * u + 3) :=
      CM (2 * r) _ (Nat.coprime_mul_iff_left.mpr ⟨c2t, crt⟩)
    exact card5 _ _ _ _ _ _ (Z ((4 * u + 5) * r) (by omega)) v1 v2 v3 v4
      (D _ _ _ _ (by norm_num) (by norm_num) cop0 cop2 (by norm_num))
      (D _ _ _ _ (by norm_num) (by omega) cop0 cops (by omega))
      (D _ _ _ _ (by norm_num) (by omega) cop0 copu (by omega))
      (D _ _ _ _ (by norm_num) (by omega) cop0 cop2t (by omega))
      (D _ _ _ _ (by norm_num) (by omega) cop2 cops (by omega))
      (D _ _ _ _ (by norm_num) (by omega) cop2 copu (by omega))
      (D _ _ _ _ (by norm_num) (by omega) cop2 cop2t (by omega))
      (D _ _ _ _ (by omega) (by omega) cops copu (by omega))
      (D _ _ _ _ (by omega) (by omega) cops cop2t (by omega))
      (D _ _ _ _ (by omega) (by omega) copu cop2t (by omega))
  refine ⟨?_, ?_⟩
  · intro p hp hp13
    unfold InSeq
    have hp3 : p % 3 ≠ 0 := pm p 3 hp (by norm_num) (by omega)
    have hp7 : p % 7 ≠ 0 := pm p 7 hp (by norm_num) (by omega)
    have hsub : repeatedValues (4 * p) ⊆
        {fracVal (4 * p) 1, fracVal (4 * p) 3, fracVal (4 * p) 6, fracVal (4 * p) 7} := by
      intro v hv
      rcases UB4 p v hp hp13 hv with h | h | h | h
      · rw [h]
        simp
      · rw [h]
        simp
      · rw [h]
        simp
      · rw [h]
        simp
    have m1 : fracVal (4 * p) 1 ∈ repeatedValues (4 * p) :=
      memR _ 1 2 le_rfl (by omega) (by norm_num) (by omega) (by norm_num)
        (by
          unfold fracVal
          rw [Nat.mod_one, Nat.mul_mod_right]
          simp)
    have m3 : fracVal (4 * p) 3 ∈ repeatedValues (4 * p) :=
      memR _ 3 12 (by norm_num) (by omega) (by norm_num) (by omega) (by norm_num)
        (by
          unfold fracVal
          rw [show 2 * (4 * p) % 12 = 4 * (2 * (4 * p) % 3) by omega]
          push_cast
          ring)
    have m6 : fracVal (4 * p) 6 ∈ repeatedValues (4 * p) :=
      memR _ 6 24 (by norm_num) (by omega) (by norm_num) (by omega) (by norm_num)
        (by
          unfold fracVal
          rw [show 2 * (4 * p) % 24 = 4 * (2 * (4 * p) % 6) by omega]
          push_cast
          ring)
    have m7 : fracVal (4 * p) 7 ∈ repeatedValues (4 * p) :=
      memR _ 7 56 (by norm_num) (by omega) (by norm_num) (by omega) (by norm_num)
        (by
          unfold fracVal
          rw [show 2 * (4 * p) % 56 = 8 * (2 * (4 * p) % 7) by omega]
          push_cast
          ring)
    have d13 : fracVal (4 * p) 1 ≠ fracVal (4 * p) 3 :=
      NE (2 * (4 * p) % 1) 1 (2 * (4 * p) % 3) 3 (by norm_num) (by norm_num) (by omega)
    have d16 : fracVal (4 * p) 1 ≠ fracVal (4 * p) 6 :=
      NE (2 * (4 * p) % 1) 1 (2 * (4 * p) % 6) 6 (by norm_num) (by norm_num) (by omega)
    have d17 : fracVal (4 * p) 1 ≠ fracVal (4 * p) 7 :=
      NE (2 * (4 * p) % 1) 1 (2 * (4 * p) % 7) 7 (by norm_num) (by norm_num) (by omega)
    have d36 : fracVal (4 * p) 3 ≠ fracVal (4 * p) 6 :=
      NE (2 * (4 * p) % 3) 3 (2 * (4 * p) % 6) 6 (by norm_num) (by norm_num) (by omega)
    have d37 : fracVal (4 * p) 3 ≠ fracVal (4 * p) 7 :=
      NE (2 * (4 * p) % 3) 3 (2 * (4 * p) % 7) 7 (by norm_num) (by norm_num) (by omega)
    have d67 : fracVal (4 * p) 6 ≠ fracVal (4 * p) 7 :=
      NE (2 * (4 * p) % 6) 6 (2 * (4 * p) % 7) 7 (by norm_num) (by norm_num) (by omega)
    have h4 := card4 _ _ _ _ _ m1 m3 m6 m7 d13 d16 d17 d36 d37 d67
    have h4' := le_trans (Finset.card_le_card hsub) Finset.card_le_four
    omega
  · intro k hk hIn
    by_contra hne
    unfold InSeq at hIn
    have five : ∀ d j : ℕ, k = d * j → 0 < j → 5 ≤ (repeatedValues d).card → False := by
      intro d j hdj hj h5
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
      rcases Nat.lt_or_ge f 4 with hf | hf
      · interval_cases f
        · rcases Nat.lt_or_ge e 7 with he | he
          · have h64 : 2 ^ e ≤ 64 := by
              calc 2 ^ e ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
                _ = 64 := by norm_num
            have hk' : k = 2 ^ e := by rw [hkf]; ring
            omega
          · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 7 := ⟨e - 7, by omega⟩
            exact five 128 (2 ^ e') (by rw [hkf]; ring) (by positivity) S128
        · rcases Nat.lt_or_ge e 5 with he | he
          · have h16 : 2 ^ e ≤ 16 := by
              calc 2 ^ e ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
                _ = 16 := by norm_num
            have hk' : k = 2 ^ e * 3 := by rw [hkf]; ring
            omega
          · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 5 := ⟨e - 5, by omega⟩
            exact five 96 (2 ^ e') (by rw [hkf]; ring) (by positivity) S96
        · rcases Nat.lt_or_ge e 3 with he | he
          · have h4 : 2 ^ e ≤ 4 := by
              calc 2 ^ e ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
                _ = 4 := by norm_num
            have hk' : k = 2 ^ e * 9 := by rw [hkf]; ring
            omega
          · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 3 := ⟨e - 3, by omega⟩
            exact five 72 (2 ^ e') (by rw [hkf]; ring) (by positivity) S72
        · rcases Nat.lt_or_ge e 2 with he | he
          · have h2 : 2 ^ e ≤ 2 := by
              calc 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
                _ = 2 := by norm_num
            have hk' : k = 2 ^ e * 27 := by rw [hkf]; ring
            omega
          · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
            exact five 108 (2 ^ e') (by rw [hkf]; ring) (by positivity) S108
      · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 4 := ⟨f - 4, by omega⟩
        exact five 81 (2 ^ e * 3 ^ f') (by rw [hkf]; ring) (by positivity) S81
    · by_cases hvp : v.Prime
      · -- v = p prime, p >= 5, k = 2^e 3^f p
        have hv5 : 5 ≤ v := by
          have := hvp.two_le
          omega
        by_cases h6 : 1 ≤ e ∧ 1 ≤ f
        · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
          obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
          rcases Nat.lt_or_ge v 11 with hv11 | hv11
          · have hv57 : v = 5 ∨ v = 7 := by omega
            rcases hv57 with rfl | rfl
            · rcases Nat.lt_or_ge e' 1 with he1 | he1
              · have he0 : e' = 0 := by omega
                subst he0
                rcases Nat.lt_or_ge f' 1 with hf1 | hf1
                · have hf0 : f' = 0 := by omega
                  subst hf0
                  norm_num at hkf
                  omega
                · obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by omega⟩
                  exact five 90 (3 ^ f'') (by rw [hkf]; ring) (by positivity) S90
              · obtain ⟨e'', rfl⟩ : ∃ e'', e' = e'' + 1 := ⟨e' - 1, by omega⟩
                exact five 60 (2 ^ e'' * 3 ^ f') (by rw [hkf]; ring) (by positivity) S60
            · exact five 42 (2 ^ e' * 3 ^ f') (by rw [hkf]; ring) (by positivity) S42
          · exact five (6 * v) (2 ^ e' * 3 ^ f') (by rw [hkf]; ring) (by positivity)
              (F6 v hv2 hv3 (pm v 5 hvp (by norm_num) (by omega)) (by omega))
        · by_cases h9 : 2 ≤ f
          · have he0 : e = 0 := by omega
            subst he0
            obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
            rcases Nat.lt_or_ge v 11 with hv11 | hv11
            · have hv57 : v = 5 ∨ v = 7 := by omega
              rcases hv57 with rfl | rfl
              · rcases Nat.lt_or_ge f' 1 with hf1 | hf1
                · have hf0 : f' = 0 := by omega
                  subst hf0
                  norm_num at hkf
                  omega
                · obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by omega⟩
                  exact five 135 (3 ^ f'') (by rw [hkf]; ring) (by positivity) S135
              · exact five 63 (3 ^ f') (by rw [hkf]; ring) (by positivity) S63
            · exact five (9 * v) (3 ^ f') (by rw [hkf]; ring) (by positivity)
                (F9 v hv2 (pm v 5 hvp (by norm_num) (by omega)) (by omega))
          · by_cases h8 : 3 ≤ e
            · have hf0 : f = 0 := by omega
              subst hf0
              obtain ⟨e', rfl⟩ : ∃ e', e = e' + 3 := ⟨e - 3, by omega⟩
              rcases Nat.lt_or_ge v 11 with hv11 | hv11
              · have hv57 : v = 5 ∨ v = 7 := by omega
                rcases hv57 with rfl | rfl
                · rcases Nat.lt_or_ge e' 2 with he2 | he2
                  · have h2 : 2 ^ e' ≤ 2 := by
                      calc 2 ^ e' ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
                        _ = 2 := by norm_num
                    have hk' : k = 2 ^ e' * 40 := by rw [hkf]; ring
                    omega
                  · obtain ⟨e'', rfl⟩ : ∃ e'', e' = e'' + 2 := ⟨e' - 2, by omega⟩
                    exact five 160 (2 ^ e'') (by rw [hkf]; ring) (by positivity) S160
                · rcases Nat.lt_or_ge e' 1 with he1 | he1
                  · have he0 : e' = 0 := by omega
                    subst he0
                    norm_num at hkf
                    omega
                  · obtain ⟨e'', rfl⟩ : ∃ e'', e' = e'' + 1 := ⟨e' - 1, by omega⟩
                    exact five 112 (2 ^ e'') (by rw [hkf]; ring) (by positivity) S112
              · exact five (8 * v) (2 ^ e') (by rw [hkf]; ring) (by positivity)
                  (F8 v hv3 (pm v 5 hvp (by norm_num) (by omega))
                    (pm v 7 hvp (by norm_num) (by omega)) (by omega))
            · have hj : (e = 0 ∧ f = 0) ∨ (e = 1 ∧ f = 0) ∨ (e = 2 ∧ f = 0) ∨
                  (e = 0 ∧ f = 1) := by
                omega
              rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · have hk1' : k = 1 * v := by rw [hkf]; ring
                have hsub : repeatedValues k ⊆ {fracVal k 1} := by
                  intro x hx
                  rcases UB v 1 k x hvp le_rfl (by norm_num) hk1' hx with
                    h | ⟨m, hm1, hm2, hm3, rfl⟩
                  · rw [h]
                    exact Finset.mem_singleton_self _
                  · have hm : m = 1 := by omega
                    subst hm
                    exact absurd (Nat.mod_one _) hm3
                have h1 := Finset.card_le_card hsub
                rw [Finset.card_singleton] at h1
                omega
              · have hk2 : k = 2 * v := by rw [hkf]; ring
                have hsub : repeatedValues k ⊆ {fracVal k 1, fracVal k 3} := by
                  intro x hx
                  rcases UB v 2 k x hvp (by norm_num) (by norm_num) hk2 hx with
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
              · have hk4 : k = 4 * v := by rw [hkf]; ring
                exact hne ⟨v, hvp, by omega, hk4⟩
              · have hk3 : k = 3 * v := by rw [hkf]; ring
                have hsub : repeatedValues k ⊆ {fracVal k 1, fracVal k 4, fracVal k 5} := by
                  intro x hx
                  rcases UB v 3 k x hvp (by norm_num) le_rfl hk3 hx with
                    h | ⟨m, hm1, hm2, hm3, rfl⟩
                  · rw [h]
                    simp
                  · have hm6 : m < 6 := by omega
                    interval_cases m
                    · exact absurd (Nat.mod_one _) hm3
                    · exact absurd (Nat.mul_mod_right 2 k) hm3
                    · exact absurd (show 2 * k % 3 = 0 by omega) hm3
                    · simp
                    · simp
                have h1 := Finset.card_le_card hsub
                have h2 : ({fracVal k 1, fracVal k 4, fracVal k 5} : Finset ℚ).card ≤ 3 :=
                  Finset.card_le_three
                omega
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
            · rcases Nat.lt_or_ge f 1 with hf | hf
              · have hf0 : f = 0 := by omega
                subst hf0
                rcases Nat.lt_or_ge e 2 with he | he
                · have h2 : 2 ^ e ≤ 2 := by
                    calc 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
                      _ = 2 := by norm_num
                  have hk' : k = 2 ^ e * 25 := by rw [hkf, hv']; ring
                  omega
                · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
                  exact five 100 (2 ^ e') (by rw [hkf, hv']; ring) (by positivity) S100
              · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
                exact five 75 (2 ^ e * 3 ^ f') (by rw [hkf, hv']; ring) (by positivity) S75
            · rcases Nat.lt_or_ge f 1 with hf | hf
              · have hf0 : f = 0 := by omega
                subst hf0
                rcases Nat.lt_or_ge e 2 with he | he
                · have h2 : 2 ^ e ≤ 2 := by
                    calc 2 ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
                      _ = 2 := by norm_num
                  have hk' : k = 2 ^ e * 35 := by rw [hkf, hv']; ring
                  omega
                · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
                  exact five 140 (2 ^ e') (by rw [hkf, hv']; ring) (by positivity) S140
              · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
                exact five 105 (2 ^ e * 3 ^ f') (by rw [hkf, hv']; ring) (by positivity) S105
          · exact five (5 * v') (2 ^ e * 3 ^ f) (by rw [hkf, hv']; ring) (by positivity)
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
          rcases (show q % 4 = 1 ∨ q % 4 = 3 by omega) with h4 | h4
          · obtain ⟨u, rfl⟩ : ∃ u, q = 4 * u + 5 := ⟨(q - 5) / 4, by omega⟩
            exact five ((4 * u + 5) * r) (2 ^ e * 3 ^ f * w) (by rw [hkf, hv', hw]; ring)
              (Nat.mul_pos (by positivity) hw0) (FQe u r (by omega) hr hqr)
          · obtain ⟨u, rfl⟩ : ∃ u, q = 4 * u + 3 := ⟨(q - 3) / 4, by omega⟩
            exact five ((4 * u + 3) * r) (2 ^ e * 3 ^ f * w) (by rw [hkf, hv', hw]; ring)
              (Nat.mul_pos (by positivity) hw0) (FQo u r (by omega) hr hqr)
