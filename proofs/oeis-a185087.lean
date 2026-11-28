import OMAStatements.S_oeis_a185087

section Proof

private def fTerm (m k : ℕ) : ℚ :=
  if k ≤ m / 2 then (Nat.choose (m - k) k : ℚ) * (catalan (k + 1) : ℚ) else 0

private def gTerm (n k : ℕ) : ℚ :=
  if k = 0 ∨ n < 2 * k then 0
  else if 2 * k = n then -((n : ℚ) + 4) * (catalan (k + 1) : ℚ)
  else
    -((4 * (k : ℚ) + 2) * ((n : ℚ) - 2) *
      (Nat.choose (n - k - 2) (k - 1) : ℚ) * (catalan k : ℚ)) /
      ((n : ℚ) - 2 * (k : ℚ))

private lemma fTerm_pos {m k : ℕ} (h : k ≤ m / 2) :
    fTerm m k = (Nat.choose (m - k) k : ℚ) * (catalan (k + 1) : ℚ) := by
  simp [fTerm, h]

private lemma fTerm_neg {m k : ℕ} (h : m / 2 < k) :
    fTerm m k = 0 := by
  simp [fTerm, show ¬ (k ≤ m / 2) by omega]

private lemma gTerm_zero (n : ℕ) : gTerm n 0 = 0 := by
  simp [gTerm]

private lemma gTerm_lt {n k : ℕ} (h : n < 2 * k) : gTerm n k = 0 := by
  simp [gTerm, h]

private lemma gTerm_eq {n k : ℕ} (hk : 1 ≤ k) (h : 2 * k = n) :
    gTerm n k = -((n : ℚ) + 4) * (catalan (k + 1) : ℚ) := by
  simp [gTerm, show ¬ k = 0 by omega, h]

private lemma gTerm_gt {n k : ℕ} (hk : 1 ≤ k) (h : 2 * k < n) :
    gTerm n k =
      -((4 * (k : ℚ) + 2) * ((n : ℚ) - 2) *
        (Nat.choose (n - k - 2) (k - 1) : ℚ) * (catalan k : ℚ)) /
        ((n : ℚ) - 2 * (k : ℚ)) := by
  simp [gTerm, show ¬ k = 0 by omega, show ¬ n < 2 * k by omega, show 2 * k ≠ n by omega]

private lemma catalan_rat_div (m : ℕ) :
    (catalan (m + 1) : ℚ) = (4 * (m : ℚ) + 2) * (catalan m : ℚ) / ((m : ℚ) + 2) := by
  have h1 : (m + 1) * catalan m = m.centralBinom := succ_mul_catalan_eq_centralBinom m
  have h2 : (m + 2) * catalan (m + 1) = (m + 1).centralBinom :=
    succ_mul_catalan_eq_centralBinom (m + 1)
  have h3 : (m + 1) * (m + 1).centralBinom = 2 * (2 * m + 1) * m.centralBinom :=
    Nat.succ_mul_centralBinom_succ m
  have hnat : (m + 1) * ((m + 2) * catalan (m + 1)) = (m + 1) * ((4 * m + 2) * catalan m) := by
    rw [h2, h3, ← h1]
    ring
  have hq : ((m : ℚ) + 1) * (((m : ℚ) + 2) * (catalan (m + 1) : ℚ)) =
      ((m : ℚ) + 1) * ((4 * (m : ℚ) + 2) * (catalan m : ℚ)) := by
    exact_mod_cast hnat
  have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have hmul := mul_left_cancel₀ hm1 hq
  rw [eq_div_iff (by positivity)]
  linarith

private lemma a_eq_sum_fTerm {m n : ℕ} (hm : m ≤ n) :
    (OMA.S_oeis_a185087.a m : ℚ) = ∑ k ∈ Finset.range (n / 2 + 2), fTerm m k := by
  unfold OMA.S_oeis_a185087.a
  push_cast
  have h1 :
      (∑ k ∈ Finset.range (m / 2 + 1), (Nat.choose (m - k) k : ℚ) * (catalan (k + 1) : ℚ)) =
        ∑ k ∈ Finset.range (m / 2 + 1), fTerm m k :=
    Finset.sum_congr rfl fun k hk =>
      (fTerm_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).symm
  rw [h1]
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun k hk hknot => ?_
  rw [Finset.mem_range] at hk hknot
  exact fTerm_neg (by omega)

private lemma wz_step (n k : ℕ) (hn : 3 ≤ n) :
    ((n : ℚ) + 4) * fTerm n k -
      (2 * (n : ℚ) + 5) * fTerm (n - 1) k -
      3 * ((n : ℚ) + 1) * fTerm (n - 2) k +
      2 * (2 * (n : ℚ) - 1) * fTerm (n - 3) k =
    gTerm n (k + 1) - gTerm n k := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [fTerm_pos (by omega), fTerm_pos (by omega), fTerm_pos (by omega), fTerm_pos (by omega),
      gTerm_zero, gTerm_gt (by omega) (by omega)]
    rw [show (1 : ℕ) - 1 = 0 by rfl, show catalan 1 = 1 by simp [catalan_succ]]
    simp only [Nat.choose_zero_right]
    have hden : (n : ℚ) - 2 ≠ 0 := by
      have : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
      linarith
    push_cast
    field_simp [hden]
    ring
  · have hkpos : 1 ≤ k := Nat.pos_of_ne_zero hk0
    rcases lt_trichotomy n (2 * k) with hlt | heq | hgt
    · rw [fTerm_neg (by omega), fTerm_neg (by omega), fTerm_neg (by omega),
        fTerm_neg (by omega), gTerm_lt (by omega), gTerm_lt (by omega)]
      ring
    · subst heq
      rw [fTerm_pos (by omega), fTerm_neg (by omega), fTerm_neg (by omega),
        fTerm_neg (by omega), gTerm_lt (by omega), gTerm_eq hkpos rfl]
      rw [show 2 * k - k = k by omega, Nat.choose_self]
      push_cast
      ring
    · by_cases h2k1 : n = 2 * k + 1
      · subst h2k1
        rw [fTerm_pos (by omega), fTerm_pos (by omega), fTerm_neg (by omega),
          fTerm_neg (by omega), gTerm_lt (by omega), gTerm_gt hkpos (by omega)]
        rw [show 2 * k + 1 - k - 2 = k - 1 by omega,
          show 2 * k + 1 - k = k + 1 by omega,
          show 2 * k + 1 - 1 - k = k by omega,
          Nat.choose_succ_self_right k, Nat.choose_self, Nat.choose_self, catalan_rat_div k]
        have hk2_ne : (k : ℚ) + 2 ≠ 0 := by positivity
        have hden : (2 * (k : ℚ) + 1 - 2 * (k : ℚ)) ≠ 0 := by
          intro h
          linarith
        push_cast
        field_simp [hk2_ne, hden]
        ring
      · by_cases h2k2 : n = 2 * k + 2
        · subst h2k2
          have hch_k : k.choose (k - 1) = k := by
            have := Nat.choose_succ_self_right (k - 1)
            rwa [Nat.sub_add_cancel hkpos] at this
          have hch2_nat : (k + 1) * (k + 2) = (k + 2).choose k * 2 := by
            have hmul := Nat.choose_mul_succ_eq (k + 1) k
            have hsub : k + 1 + 1 - k = 2 := by omega
            rw [Nat.add_assoc, hsub, Nat.choose_succ_self_right k] at hmul
            exact hmul
          have hch2 : ((k + 2).choose k : ℚ) = ((k : ℚ) + 1) * ((k : ℚ) + 2) / 2 := by
            have hq : ((k : ℚ) + 1) * ((k : ℚ) + 2) = ((k + 2).choose k : ℚ) * 2 := by
              exact_mod_cast hch2_nat
            linarith
          rw [fTerm_pos (by omega), fTerm_pos (by omega), fTerm_pos (by omega),
            fTerm_neg (by omega), gTerm_eq (by omega) (by omega), gTerm_gt hkpos (by omega)]
          rw [show 2 * k + 2 - k - 2 = k by omega,
            show 2 * k + 2 - k = k + 2 by omega,
            show 2 * k + 2 - 1 - k = k + 1 by omega,
            show 2 * k + 2 - 2 - k = k by omega,
            Nat.choose_succ_self_right k, Nat.choose_self, hch_k]
          push_cast
          rw [hch2, catalan_rat_div (k + 1), catalan_rat_div k]
          have hk2_ne : (k : ℚ) + 2 ≠ 0 := by positivity
          have hk3_ne : ((k + 1 : ℕ) : ℚ) + 2 ≠ 0 := by positivity
          have hden : (2 * (k : ℚ) + 2 - 2 * (k : ℚ)) ≠ 0 := by
            intro h
            linarith
          push_cast
          field_simp [hk2_ne, hk3_ne, hden]
          ring
        · have hn2k3 : 2 * k + 3 ≤ n := by omega
          set a : ℕ := n - k - 3 with ha_def
          have ha_ge : k ≤ a := by omega
          have hka : (k : ℚ) ≤ a := by exact_mod_cast ha_ge
          have hB_k_nat : a.choose k * k = a.choose (k - 1) * (a + 1 - k) := by
            have := Nat.choose_succ_right_eq a (k - 1)
            rwa [Nat.sub_add_cancel hkpos, show a - (k - 1) = a + 1 - k by omega] at this
          have hB_a1_nat : (a + 1) * a.choose (k - 1) = (a + 1).choose k * k := by
            have := Nat.add_one_mul_choose_eq a (k - 1)
            rwa [Nat.sub_add_cancel hkpos] at this
          have hB_a2_nat : (a + 1).choose k * (a + 2) = (a + 2).choose k * (a + 2 - k) := by
            simpa [Nat.add_assoc] using Nat.choose_mul_succ_eq (a + 1) k
          have hB_a3_nat : (a + 2).choose k * (a + 3) = (a + 3).choose k * (a + 3 - k) := by
            simpa [Nat.add_assoc] using Nat.choose_mul_succ_eq (a + 2) k
          have hB_g0_nat : a.choose (k - 1) * (a + 1) = (a + 1).choose (k - 1) * (a + 2 - k) := by
            have := Nat.choose_mul_succ_eq a (k - 1)
            rwa [show a + 1 - (k - 1) = a + 2 - k by omega] at this
          have hk_ne : (k : ℚ) ≠ 0 := by
            have : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hkpos
            linarith
          have ha2k_ne : (a : ℚ) + 2 - (k : ℚ) ≠ 0 := by linarith
          have ha3k_ne : (a : ℚ) + 3 - (k : ℚ) ≠ 0 := by linarith
          have hk2_ne : (k : ℚ) + 2 ≠ 0 := by positivity
          have hn_eq_a : (n : ℚ) = (a : ℚ) + (k : ℚ) + 3 := by
            have : n = a + k + 3 := by omega
            exact_mod_cast this
          have hBk : (a.choose k : ℚ) =
              (a.choose (k - 1) : ℚ) * ((a : ℚ) + 1 - (k : ℚ)) / (k : ℚ) := by
            have hq : (a.choose k : ℚ) * (k : ℚ) =
                (a.choose (k - 1) : ℚ) * ((a : ℚ) + 1 - (k : ℚ)) := by
              have hle : k ≤ a + 1 := by omega
              have := congrArg (Nat.cast (R := ℚ)) hB_k_nat
              push_cast [hle] at this
              exact this
            rw [eq_div_iff hk_ne]
            exact hq
          have hBa1 : ((a + 1).choose k : ℚ) =
              ((a : ℚ) + 1) * (a.choose (k - 1) : ℚ) / (k : ℚ) := by
            have hq : ((a : ℚ) + 1) * (a.choose (k - 1) : ℚ) =
                ((a + 1).choose k : ℚ) * (k : ℚ) := by exact_mod_cast hB_a1_nat
            rw [eq_div_iff hk_ne]
            exact hq.symm
          have hBa2 : ((a + 2).choose k : ℚ) =
              ((a + 1).choose k : ℚ) * ((a : ℚ) + 2) / ((a : ℚ) + 2 - (k : ℚ)) := by
            have hq : ((a + 1).choose k : ℚ) * ((a : ℚ) + 2) =
                ((a + 2).choose k : ℚ) * ((a : ℚ) + 2 - (k : ℚ)) := by
              have hle : k ≤ a + 2 := by omega
              have := congrArg (Nat.cast (R := ℚ)) hB_a2_nat
              push_cast [hle] at this
              exact this
            rw [eq_div_iff ha2k_ne]
            exact hq.symm
          have hBa3 : ((a + 3).choose k : ℚ) =
              ((a + 2).choose k : ℚ) * ((a : ℚ) + 3) / ((a : ℚ) + 3 - (k : ℚ)) := by
            have hq : ((a + 2).choose k : ℚ) * ((a : ℚ) + 3) =
                ((a + 3).choose k : ℚ) * ((a : ℚ) + 3 - (k : ℚ)) := by
              have hle : k ≤ a + 3 := by omega
              have := congrArg (Nat.cast (R := ℚ)) hB_a3_nat
              push_cast [hle] at this
              exact this
            rw [eq_div_iff ha3k_ne]
            exact hq.symm
          have hBg0 : ((a + 1).choose (k - 1) : ℚ) =
              (a.choose (k - 1) : ℚ) * ((a : ℚ) + 1) / ((a : ℚ) + 2 - (k : ℚ)) := by
            have hq : (a.choose (k - 1) : ℚ) * ((a : ℚ) + 1) =
                ((a + 1).choose (k - 1) : ℚ) * ((a : ℚ) + 2 - (k : ℚ)) := by
              have hle : k ≤ a + 2 := by omega
              have := congrArg (Nat.cast (R := ℚ)) hB_g0_nat
              push_cast [hle] at this
              exact this
            rw [eq_div_iff ha2k_ne]
            exact hq.symm
          rw [fTerm_pos (by omega), fTerm_pos (by omega), fTerm_pos (by omega),
            fTerm_pos (by omega), gTerm_gt (by omega) (by omega), gTerm_gt hkpos (by omega)]
          rw [show n - k - 2 = a + 1 by omega,
            show n - k = a + 3 by omega,
            show n - 1 - k = a + 2 by omega,
            show n - 2 - k = a + 1 by omega,
            show n - 3 - k = a by omega,
            show n - (k + 1) - 2 = a by omega,
            show k + 1 - 1 = k by omega]
          rw [hBa3, hBa2, hBa1, hBk, hBg0, catalan_rat_div k, hn_eq_a]
          push_cast
          have ha1k_ne : (a : ℚ) + 1 - (k : ℚ) ≠ 0 := by linarith
          have hden0 : ((a : ℚ) + (k : ℚ) + 3 - 2 * (k : ℚ)) = (a : ℚ) + 3 - (k : ℚ) := by ring
          have hden1 : ((a : ℚ) + (k : ℚ) + 3 - 2 * ((k : ℚ) + 1)) = (a : ℚ) + 1 - (k : ℚ) := by ring
          have ha3k_alt : 3 + (a : ℚ) - (k : ℚ) ≠ 0 := by linarith
          rw [hden0, hden1]
          field_simp [hk_ne, ha1k_ne, ha2k_ne, ha3k_ne, ha3k_alt, hk2_ne]
          ring

end Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a185087.main := by
  intro n hn
  qify
  rw [a_eq_sum_fTerm le_rfl, a_eq_sum_fTerm (n.sub_le 1), a_eq_sum_fTerm (n.sub_le 2),
    a_eq_sum_fTerm (n.sub_le 3)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun k _ => wz_step n k hn, Finset.sum_range_sub (gTerm n),
    gTerm_zero, gTerm_lt (by omega), sub_zero]
