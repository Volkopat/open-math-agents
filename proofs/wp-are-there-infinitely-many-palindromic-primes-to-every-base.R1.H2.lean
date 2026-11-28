import OMAReductions.R_wp_are_there_infinitely_many_palindromic_primes_to_every_base_R1

-- Problem: Are there infinitely many palindromic primes to every base? (step R1.H2)
-- Credit: @luciusacarr

section

private lemma ofDigits_lt {b : ℕ} (hb : 0 < b) :
    ∀ l : List ℕ, (∀ x ∈ l, x < b) → Nat.ofDigits b l < b ^ l.length
  | [], _ => by simp
  | a :: l, h => by
      have ha : a < b := h a (by simp)
      have hl : Nat.ofDigits b l < b ^ l.length := ofDigits_lt hb l (fun x hx => h x (by simp [hx]))
      rw [Nat.ofDigits_cons, List.length_cons, pow_succ']
      calc
        a + b * Nat.ofDigits b l < b + b * Nat.ofDigits b l := Nat.add_lt_add_right ha _
        _ = b * (Nat.ofDigits b l + 1) := by ring
        _ ≤ b * b ^ l.length := Nat.mul_le_mul_left b hl

private lemma ofDigits_inj {b : ℕ} :
    ∀ {l1 l2 : List ℕ}, l1.length = l2.length → (∀ x ∈ l1, x < b) → (∀ x ∈ l2, x < b) →
      Nat.ofDigits b l1 = Nat.ofDigits b l2 → l1 = l2
  | [], [], _, _, _, _ => rfl
  | a :: l1, c :: l2, hlen, h1, h2, heq => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [Nat.ofDigits_cons, Nat.ofDigits_cons] at heq
      have ha : a < b := h1 a (by simp)
      have hc : c < b := h2 c (by simp)
      have hac : a = c := by
        have hm := congrArg (· % b) heq
        simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] using hm
      subst hac
      have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le a) ha
      have hrest : Nat.ofDigits b l1 = Nat.ofDigits b l2 := by
        have hmul : b * Nat.ofDigits b l1 = b * Nat.ofDigits b l2 := by omega
        exact Nat.mul_left_cancel hb hmul
      congr 1
      exact ofDigits_inj hlen (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx])) hrest

private lemma digits_take_ofDigits {b s n : ℕ} (hb : 1 < b) (hs : s ≤ (b.digits n).length) :
    Nat.ofDigits b ((b.digits n).take s) = n % b ^ s ∧
      Nat.ofDigits b ((b.digits n).drop s) = n / b ^ s := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hlen : ((b.digits n).take s).length = s := List.length_take_of_le hs
  have hlt : Nat.ofDigits b ((b.digits n).take s) < b ^ s :=
    calc
      Nat.ofDigits b ((b.digits n).take s)
          < b ^ ((b.digits n).take s).length :=
            ofDigits_lt hb0 _ fun x hx => Nat.digits_lt_base hb (List.mem_of_mem_take hx)
      _ = b ^ s := by rw [hlen]
  have hsplit : n = Nat.ofDigits b ((b.digits n).take s) +
      b ^ s * Nat.ofDigits b ((b.digits n).drop s) := by
    conv_lhs => rw [← Nat.ofDigits_digits b n, ← List.take_append_drop s (b.digits n)]
    rw [Nat.ofDigits_append, hlen]
  have hm : Nat.ofDigits b ((b.digits n).take s) = n % b ^ s := by
    conv_rhs => rw [hsplit]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hd : Nat.ofDigits b ((b.digits n).drop s) = n / b ^ s := by
    have hmul : b ^ s * Nat.ofDigits b ((b.digits n).drop s) = b ^ s * (n / b ^ s) := by
      have := Nat.div_add_mod n (b ^ s)
      omega
    exact Nat.mul_left_cancel (pow_pos hb0 s) hmul
  exact ⟨hm, hd⟩

private lemma palindrome_top_eq_of_mod_eq {b d s n1 n2 : ℕ} (hb : 1 < b) (hs : s ≤ d)
    (hd1 : (b.digits n1).length = d) (hd2 : (b.digits n2).length = d)
    (hpal1 : (b.digits n1).reverse = b.digits n1)
    (hpal2 : (b.digits n2).reverse = b.digits n2)
    (hmod : n1 % b ^ s = n2 % b ^ s) :
    n1 / b ^ (d - s) = n2 / b ^ (d - s) := by
  have ht1 := digits_take_ofDigits hb (hs.trans_eq hd1.symm)
  have ht2 := digits_take_ofDigits hb (hs.trans_eq hd2.symm)
  have htake : (b.digits n1).take s = (b.digits n2).take s := by
    apply ofDigits_inj
    · rw [List.length_take_of_le (hs.trans_eq hd1.symm),
        List.length_take_of_le (hs.trans_eq hd2.symm)]
    · exact fun x hx => Nat.digits_lt_base hb (List.mem_of_mem_take hx)
    · exact fun x hx => Nat.digits_lt_base hb (List.mem_of_mem_take hx)
    · rw [ht1.1, ht2.1, hmod]
  have hdrop : (b.digits n1).drop (d - s) = (b.digits n2).drop (d - s) := by
    have h1 : (b.digits n1).drop (d - s) = ((b.digits n1).take s).reverse := by
      rw [List.reverse_take, hpal1, hd1]
    have h2 : (b.digits n2).drop (d - s) = ((b.digits n2).take s).reverse := by
      rw [List.reverse_take, hpal2, hd2]
    rw [h1, h2, htake]
  have hds1 := digits_take_ofDigits hb (Nat.sub_le d s |>.trans_eq hd1.symm)
  have hds2 := digits_take_ofDigits hb (Nat.sub_le d s |>.trans_eq hd2.symm)
  rw [← hds1.2, ← hds2.2, hdrop]

private lemma quotient_diff_lt_sq {b d n1 n2 : ℕ} (hb : 2 ≤ b) (hd : 1 ≤ d)
    (hpow1 : b ^ (d - 1) ≤ n1) (hn12 : n1 ≤ n2)
    (hsq1 : IsSquare n1) (hsq2 : IsSquare n2)
    (hd1 : (b.digits n1).length = d) (hd2 : (b.digits n2).length = d)
    (hpal1 : (b.digits n1).reverse = b.digits n1)
    (hpal2 : (b.digits n2).reverse = b.digits n2)
    (hrem : n1.sqrt % b ^ (d / 4) = n2.sqrt % b ^ (d / 4)) :
    n2.sqrt / b ^ (d / 4) - n1.sqrt / b ^ (d / 4) < b ^ 2 := by
  set s := d / 4
  have hs : s ≤ d := Nat.div_le_self d 4
  have hb1 : 1 < b := lt_of_lt_of_le (by decide) hb
  have hb0 : 0 < b := lt_trans zero_lt_one hb1
  obtain ⟨m1, rfl⟩ := hsq1
  obtain ⟨m2, rfl⟩ := hsq2
  have hm1_eq : (m1 * m1).sqrt = m1 := Nat.sqrt_eq m1
  have hm2_eq : (m2 * m2).sqrt = m2 := Nat.sqrt_eq m2
  rw [hm1_eq, hm2_eq] at hrem ⊢
  have hm12 : m1 ≤ m2 := by
    by_contra hlt
    have hgt : m2 < m1 := Nat.lt_of_not_ge hlt
    have : m2 * m2 < m1 * m1 := Nat.mul_lt_mul_of_lt_of_lt hgt hgt
    omega
  have hnmod : (m1 * m1) % b ^ s = (m2 * m2) % b ^ s := by
    rw [Nat.mul_mod, Nat.mul_mod m2, hrem]
  have htop : (m1 * m1) / b ^ (d - s) = (m2 * m2) / b ^ (d - s) :=
    palindrome_top_eq_of_mod_eq hb1 hs hd1 hd2 hpal1 hpal2 hnmod
  have hdiff_lt : m2 * m2 - m1 * m1 < b ^ (d - s) := by
    have hK := Nat.div_add_mod (m1 * m1) (b ^ (d - s))
    have hL := Nat.div_add_mod (m2 * m2) (b ^ (d - s))
    have hmodL := Nat.mod_lt (m2 * m2) (pow_pos hb0 (d - s))
    rw [htop] at hK
    have hq_le : b ^ (d - s) * (m2 * m2 / b ^ (d - s)) ≤ m1 * m1 := by
      rw [← hK]; exact Nat.le_add_right _ _
    calc
      m2 * m2 - m1 * m1 ≤ m2 * m2 - b ^ (d - s) * (m2 * m2 / b ^ (d - s)) :=
        Nat.sub_le_sub_left hq_le _
      _ = m2 * m2 % b ^ (d - s) := by omega
      _ < b ^ (d - s) := hmodL
  set q1 := m1 / b ^ s
  set q2 := m2 / b ^ s
  have hmq : m2 - m1 = (q2 - q1) * b ^ s := by
    have h1Z : (b ^ s : ℤ) * q1 + (m1 % b ^ s : ℤ) = m1 := by
      exact_mod_cast Nat.div_add_mod m1 (b ^ s)
    have h2Z : (b ^ s : ℤ) * q2 + (m2 % b ^ s : ℤ) = m2 := by
      exact_mod_cast Nat.div_add_mod m2 (b ^ s)
    have hremZ : (m1 % b ^ s : ℤ) = m2 % b ^ s := by exact_mod_cast hrem
    have hq12 : q1 ≤ q2 := Nat.div_le_div_right hm12
    zify [hm12, hq12]
    have hmul : ((q2 : ℤ) - q1) * b ^ s = b ^ s * q2 - b ^ s * q1 := by ring
    linarith [h1Z, h2Z, hremZ, hmul]
  have hfac : (m2 - m1) * (m2 + m1) = m2 * m2 - m1 * m1 := by
    have hsq_le : m1 * m1 ≤ m2 * m2 := Nat.mul_le_mul hm12 hm12
    zify [hm12, hsq_le]
    ring
  have hsum_sq : 4 * b ^ (d - 1) ≤ (m2 + m1) * (m2 + m1) := by
    have : 2 * m1 ≤ m2 + m1 := by omega
    calc
      4 * b ^ (d - 1) ≤ 4 * (m1 * m1) := Nat.mul_le_mul_left 4 hpow1
      _ = (2 * m1) * (2 * m1) := by ring
      _ ≤ (m2 + m1) * (m2 + m1) := Nat.mul_le_mul this this
  have hexp : 2 * d - 2 * s ≤ 2 * s + (d - 1) + 4 := by omega
  have hpow_le : (b ^ (d - s)) ^ 2 ≤ b ^ 4 * b ^ (2 * s + (d - 1)) := by
    calc
      (b ^ (d - s)) ^ 2 = b ^ (2 * (d - s)) := by rw [← pow_mul]; ring_nf
      _ = b ^ (2 * d - 2 * s) := by congr 1; omega
      _ ≤ b ^ (2 * s + (d - 1) + 4) := Nat.pow_le_pow_right hb0 hexp
      _ = b ^ 4 * b ^ (2 * s + (d - 1)) := by rw [Nat.add_comm _ 4, pow_add]
  have hmain : ((q2 - q1) ^ 2 * 4) * b ^ (2 * s + (d - 1)) < b ^ 4 * b ^ (2 * s + (d - 1)) := by
    calc
      ((q2 - q1) ^ 2 * 4) * b ^ (2 * s + (d - 1))
          = ((q2 - q1) * b ^ s) ^ 2 * (4 * b ^ (d - 1)) := by
              rw [pow_add, pow_mul]; ring
      _ = (m2 - m1) ^ 2 * (4 * b ^ (d - 1)) := by rw [hmq]
      _ ≤ (m2 - m1) ^ 2 * ((m2 + m1) * (m2 + m1)) := Nat.mul_le_mul_left _ hsum_sq
      _ = ((m2 - m1) * (m2 + m1)) ^ 2 := by ring
      _ = (m2 * m2 - m1 * m1) ^ 2 := by rw [hfac]
      _ < (b ^ (d - s)) ^ 2 := Nat.pow_lt_pow_left hdiff_lt (by decide)
      _ ≤ b ^ 4 * b ^ (2 * s + (d - 1)) := hpow_le
  have hlt4 : (q2 - q1) ^ 2 * 4 < b ^ 4 :=
    Nat.lt_of_mul_lt_mul_right hmain
  by_contra hge
  have hge' : b ^ 2 ≤ q2 - q1 := Nat.le_of_not_lt hge
  have : b ^ 4 ≤ (q2 - q1) ^ 2 * 4 := by
    calc
      b ^ 4 = (b ^ 2) ^ 2 := by ring
      _ ≤ (q2 - q1) ^ 2 := Nat.pow_le_pow_left hge' 2
      _ ≤ (q2 - q1) ^ 2 * 4 := Nat.le_mul_of_pos_right _ (by decide)
  omega

private lemma pow4_growth_helper :
    ∀ K : ℕ, (79 + 6 * K) ^ 4 ≤ 2 ^ 26 * 2 ^ K
  | 0 => by decide
  | K + 1 => by
      have ih := pow4_growth_helper K
      have hid : 2 * (79 + 6 * K) ^ 4 = (79 + 6 * (K + 1)) ^ 4 +
          (25699537 + 8926872 * K + 1135512 * K ^ 2 + 63072 * K ^ 3 + 1296 * K ^ 4) := by ring
      have hstep : (79 + 6 * (K + 1)) ^ 4 ≤ 2 * (79 + 6 * K) ^ 4 := by
        rw [hid]; exact Nat.le_add_right _ _
      calc
        (79 + 6 * (K + 1)) ^ 4 ≤ 2 * (79 + 6 * K) ^ 4 := hstep
        _ ≤ 2 * (2 ^ 26 * 2 ^ K) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ 26 * 2 ^ (K + 1) := by rw [pow_succ]; ring

private lemma exists_pow_ge_mul_poly (C : ℕ) :
    ∃ T : ℕ, ∀ t ≥ T, (1 + 3 * t) ^ 4 * C ≤ 2 ^ t := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, C ≤ 2 ^ K := ⟨C, Nat.le_of_lt (Nat.lt_two_pow_self)⟩
  refine ⟨26 + 2 * K, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base =>
      have h1 := pow4_growth_helper K
      calc
        (1 + 3 * (26 + 2 * K)) ^ 4 * C = (79 + 6 * K) ^ 4 * C := by ring_nf
        _ ≤ (2 ^ 26 * 2 ^ K) * 2 ^ K := Nat.mul_le_mul h1 hK
        _ = 2 ^ (26 + 2 * K) := by rw [← pow_add, ← pow_add]; ring_nf
  | succ t ht ih =>
      have ht6 : 6 ≤ t := by omega
      have hstep : (1 + 3 * (t + 1)) ^ 4 ≤ 2 * (1 + 3 * t) ^ 4 := by
        obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le' ht6
        have hid : 2 * (1 + 3 * (u + 6)) ^ 4 = (1 + 3 * (u + 6 + 1)) ^ 4 +
            (26386 + 36840 * u + 12852 * u ^ 2 + 1728 * u ^ 3 + 81 * u ^ 4) := by ring
        rw [hid]; exact Nat.le_add_right _ _
      calc
        (1 + 3 * (t + 1)) ^ 4 * C ≤ 2 * (1 + 3 * t) ^ 4 * C :=
          Nat.mul_le_mul_right C hstep
        _ = 2 * ((1 + 3 * t) ^ 4 * C) := by ring
        _ ≤ 2 * 2 ^ t := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (t + 1) := by rw [pow_succ']

end

theorem OMA.solution : OMA.R_wp_are_there_infinitely_many_palindromic_primes_to_every_base_R1.H2 := by
  intro b hb
  have hb1 : 1 < b := lt_of_lt_of_le (by decide) hb
  have hb0 : 0 < b := lt_trans zero_lt_one hb1
  obtain ⟨T, hT⟩ := exists_pow_ge_mul_poly (16 * (b ^ 9 + 1))
  refine ⟨T, fun t ht => ?_⟩
  let S : Finset ℕ := (Finset.range (2 ^ (3 * t))).filter fun n =>
    IsSquare n ∧ (b.digits n).reverse = b.digits n
  let Sd (d : ℕ) : Finset ℕ := (S.erase 0).filter fun n => (b.digits n).length = d
  have hSd_card : ∀ d : ℕ, 1 ≤ d → (Sd d).card ≤ b ^ (d / 4) * b ^ 2 := by
    intro d hd
    have hsub : Sd d ⊆ (Finset.range (b ^ (d / 4))).biUnion fun r =>
        (Sd d).filter fun n => n.sqrt % b ^ (d / 4) = r := by
      intro n hn
      rw [Finset.mem_biUnion]
      refine ⟨n.sqrt % b ^ (d / 4), Finset.mem_range.2 ?_, Finset.mem_filter.2 ⟨hn, rfl⟩⟩
      exact Nat.mod_lt _ (pow_pos hb0 _)
    refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
    calc
      ∑ r ∈ Finset.range (b ^ (d / 4)), ((Sd d).filter fun n => n.sqrt % b ^ (d / 4) = r).card
          ≤ ∑ _r ∈ Finset.range (b ^ (d / 4)), b ^ 2 := by
            refine Finset.sum_le_sum fun r _ => ?_
            set Fr := (Sd d).filter fun n => n.sqrt % b ^ (d / 4) = r
            by_cases hne : Fr.Nonempty
            · set Q := Fr.image fun n => n.sqrt / b ^ (d / 4)
              have hQ : Q.Nonempty := hne.image _
              set q0 := Q.min' hQ
              obtain ⟨n0, hn0_mem, hq0⟩ := Finset.mem_image.1 (Finset.min'_mem Q hQ)
              have hFr_sd : ∀ n ∈ Fr, n ∈ S ∧ n ≠ 0 ∧ (b.digits n).length = d ∧
                  n.sqrt % b ^ (d / 4) = r := by
                intro n hn
                simp only [Fr, Sd, Finset.mem_filter, Finset.mem_erase] at hn
                exact ⟨hn.1.1.2, hn.1.1.1, hn.1.2, hn.2⟩
              have hn0_prop := hFr_sd n0 hn0_mem
              have hn0_sq : IsSquare n0 := (Finset.mem_filter.1 hn0_prop.1).2.1
              have hn0_pal : (b.digits n0).reverse = b.digits n0 :=
                (Finset.mem_filter.1 hn0_prop.1).2.2
              have hpow0 : b ^ (d - 1) ≤ n0 := by
                have hle := Nat.base_pow_length_digits_le b n0 hb1 hn0_prop.2.1
                rw [hn0_prop.2.2.1] at hle
                have hmul : b * b ^ (d - 1) ≤ b * n0 := by
                  simpa [← pow_succ', Nat.sub_add_cancel hd] using hle
                exact Nat.le_of_mul_le_mul_left hmul hb0
              have hinj : Finset.card Fr ≤ (Finset.range (b ^ 2)).card := by
                refine Finset.card_le_card_of_injOn (fun n => n.sqrt / b ^ (d / 4) - q0) ?_ ?_
                · intro n hn
                  have hn_prop := hFr_sd n hn
                  have hn_sq : IsSquare n := (Finset.mem_filter.1 hn_prop.1).2.1
                  have hn_pal : (b.digits n).reverse = b.digits n :=
                    (Finset.mem_filter.1 hn_prop.1).2.2
                  have hq_ge : q0 ≤ n.sqrt / b ^ (d / 4) :=
                    Finset.min'_le Q _ (Finset.mem_image_of_mem _ hn)
                  have hm0_le : n0.sqrt ≤ n.sqrt := by
                    have h1 := Nat.div_add_mod n0.sqrt (b ^ (d / 4))
                    have h2 := Nat.div_add_mod n.sqrt (b ^ (d / 4))
                    rw [hq0, hn0_prop.2.2.2] at h1
                    rw [hn_prop.2.2.2] at h2
                    dsimp only [q0] at hq_ge
                    have hmul := Nat.mul_le_mul_left (b ^ (d / 4)) hq_ge
                    omega
                  have hn0_le : n0 ≤ n := by
                    obtain ⟨a0, ha0⟩ := hn0_sq
                    obtain ⟨a, ha⟩ := hn_sq
                    subst ha0 ha
                    rw [Nat.sqrt_eq, Nat.sqrt_eq] at hm0_le
                    exact Nat.mul_le_mul hm0_le hm0_le
                  have hlt := quotient_diff_lt_sq hb hd hpow0 hn0_le hn0_sq hn_sq
                    hn0_prop.2.2.1 hn_prop.2.2.1 hn0_pal hn_pal
                    (hn0_prop.2.2.2.trans hn_prop.2.2.2.symm)
                  dsimp only [q0]
                  rw [← hq0]
                  exact Finset.mem_range.2 hlt
                · intro n1 hn1 n2 hn2 heq
                  have hp1 := hFr_sd n1 hn1
                  have hp2 := hFr_sd n2 hn2
                  have hq1_ge : q0 ≤ n1.sqrt / b ^ (d / 4) :=
                    Finset.min'_le Q _ (Finset.mem_image_of_mem _ hn1)
                  have hq2_ge : q0 ≤ n2.sqrt / b ^ (d / 4) :=
                    Finset.min'_le Q _ (Finset.mem_image_of_mem _ hn2)
                  dsimp only at heq
                  have hq_eq : n1.sqrt / b ^ (d / 4) = n2.sqrt / b ^ (d / 4) := by omega
                  have hm_eq : n1.sqrt = n2.sqrt := by
                    have h1 := Nat.div_add_mod n1.sqrt (b ^ (d / 4))
                    have h2 := Nat.div_add_mod n2.sqrt (b ^ (d / 4))
                    rw [hq_eq, hp1.2.2.2, ← hp2.2.2.2] at h1
                    omega
                  obtain ⟨a1, ha1⟩ := (Finset.mem_filter.1 hp1.1).2.1
                  obtain ⟨a2, ha2⟩ := (Finset.mem_filter.1 hp2.1).2.1
                  subst ha1 ha2
                  rw [Nat.sqrt_eq, Nat.sqrt_eq] at hm_eq
                  rw [hm_eq]
              simpa using hinj
            · simp [Finset.not_nonempty_iff_eq_empty.1 hne]
      _ = b ^ (d / 4) * b ^ 2 := by simp
  have hS_sub : S.erase 0 ⊆ (Finset.Icc 1 (3 * t)).biUnion Sd := by
    intro n hn
    rw [Finset.mem_biUnion]
    have hne : n ≠ 0 := (Finset.mem_erase.1 hn).1
    have hnS : n ∈ S := (Finset.mem_erase.1 hn).2
    have hn_lt : n < 2 ^ (3 * t) := Finset.mem_range.1 (Finset.mem_filter.1 hnS).1
    have hdig_ne : b.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 hne
    have hd1 : 1 ≤ (b.digits n).length := List.length_pos_of_ne_nil hdig_ne
    have hle_b : b ^ ((b.digits n).length - 1) ≤ n := by
      have hle := Nat.base_pow_length_digits_le b n hb1 hne
      have hmul : b * b ^ ((b.digits n).length - 1) ≤ b * n := by
        simpa [← pow_succ', Nat.sub_add_cancel hd1] using hle
      exact Nat.le_of_mul_le_mul_left hmul hb0
    have h2lt : 2 ^ ((b.digits n).length - 1) < 2 ^ (3 * t) :=
      calc
        2 ^ ((b.digits n).length - 1) ≤ b ^ ((b.digits n).length - 1) := Nat.pow_le_pow_left hb _
        _ ≤ n := hle_b
        _ < 2 ^ (3 * t) := hn_lt
    have hd_lt : (b.digits n).length - 1 < 3 * t :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 h2lt
    refine ⟨(b.digits n).length, Finset.mem_Icc.2 ⟨hd1, by omega⟩, Finset.mem_filter.2 ⟨hn, rfl⟩⟩
  have hSd_pow4 : ∀ d ∈ Finset.Icc 1 (3 * t), (Sd d).card ^ 4 ≤ b ^ 9 * 2 ^ (3 * t) := by
    intro d hd_mem
    have hd1 : 1 ≤ d := (Finset.mem_Icc.1 hd_mem).1
    by_cases hne : (Sd d).Nonempty
    · obtain ⟨n, hn⟩ := hne
      simp only [Sd, Finset.mem_filter, Finset.mem_erase] at hn
      have hn_lt : n < 2 ^ (3 * t) := Finset.mem_range.1 (Finset.mem_filter.1 hn.1.2).1
      have hle_b : b ^ (d - 1) ≤ n := by
        have hle := Nat.base_pow_length_digits_le b n hb1 hn.1.1
        rw [hn.2] at hle
        have hmul : b * b ^ (d - 1) ≤ b * n := by
          simpa [← pow_succ', Nat.sub_add_cancel hd1] using hle
        exact Nat.le_of_mul_le_mul_left hmul hb0
      have h4_le : (b ^ (d / 4)) ^ 4 ≤ b * 2 ^ (3 * t) := by
        calc
          (b ^ (d / 4)) ^ 4 = b ^ (4 * (d / 4)) := by rw [← pow_mul]; ring_nf
          _ ≤ b ^ d := Nat.pow_le_pow_right hb0 (by omega)
          _ = b * b ^ (d - 1) := by conv_lhs => rw [← Nat.sub_add_cancel hd1, pow_succ']
          _ ≤ b * n := Nat.mul_le_mul_left b hle_b
          _ ≤ b * 2 ^ (3 * t) := Nat.mul_le_mul_left b hn_lt.le
      calc
        (Sd d).card ^ 4 ≤ (b ^ (d / 4) * b ^ 2) ^ 4 := Nat.pow_le_pow_left (hSd_card d hd1) 4
        _ = (b ^ (d / 4)) ^ 4 * b ^ 8 := by ring
        _ ≤ (b * 2 ^ (3 * t)) * b ^ 8 := Nat.mul_le_mul_right (b ^ 8) h4_le
        _ = b ^ 9 * 2 ^ (3 * t) := by ring
    · simp [Finset.not_nonempty_iff_eq_empty.1 hne]
  let M : ℕ := (Finset.Icc 1 (3 * t)).sup fun d => (Sd d).card
  have hM_pow4 : M ^ 4 ≤ b ^ 9 * 2 ^ (3 * t) := by
    by_cases hne : (Finset.Icc 1 (3 * t)).Nonempty
    · obtain ⟨d0, hd0, hsup⟩ := Finset.exists_mem_eq_sup (Finset.Icc 1 (3 * t)) hne
        (fun d => (Sd d).card)
      dsimp only [M]
      rw [hsup]
      exact hSd_pow4 d0 hd0
    · have hM0 : M = 0 := by simp [M, Finset.not_nonempty_iff_eq_empty.1 hne]
      simp [hM0]
  have hS_le : S.card ≤ (1 + 3 * t) * (M + 1) := by
    have hsub0 : S ⊆ insert 0 (S.erase 0) := fun x hx => by
      by_cases hx0 : x = 0 <;> simp [hx0, hx]
    have h1 : S.card ≤ (S.erase 0).card + 1 :=
      (Finset.card_le_card hsub0).trans (Finset.card_insert_le _ _)
    have h2 : (S.erase 0).card ≤ ∑ d ∈ Finset.Icc 1 (3 * t), (Sd d).card :=
      (Finset.card_le_card hS_sub).trans Finset.card_biUnion_le
    have h3 : ∑ d ∈ Finset.Icc 1 (3 * t), (Sd d).card ≤ (Finset.Icc 1 (3 * t)).card * M := by
      calc
        ∑ d ∈ Finset.Icc 1 (3 * t), (Sd d).card
            ≤ ∑ _d ∈ Finset.Icc 1 (3 * t), M :=
              Finset.sum_le_sum fun d hd => Finset.le_sup (f := fun d => (Sd d).card) hd
        _ = (Finset.Icc 1 (3 * t)).card * M := by simp
    have hcard_Icc : (Finset.Icc 1 (3 * t)).card ≤ 3 * t := by
      rw [Nat.card_Icc]
      omega
    calc
      S.card ≤ (S.erase 0).card + 1 := h1
      _ ≤ (Finset.Icc 1 (3 * t)).card * M + 1 := by omega
      _ ≤ (3 * t) * M + 1 := by gcongr
      _ ≤ (1 + 3 * t) * (M + 1) := by nlinarith
  have hM1_pow4 : (M + 1) ^ 4 ≤ 16 * (b ^ 9 + 1) * 2 ^ (3 * t) := by
    have h16 : (M + 1) ^ 4 ≤ 16 * (M ^ 4 + 1) := by
      have : M + 1 ≤ 2 * max M 1 := by omega
      calc
        (M + 1) ^ 4 ≤ (2 * max M 1) ^ 4 := Nat.pow_le_pow_left this 4
        _ = 16 * (max M 1) ^ 4 := by ring
        _ ≤ 16 * (M ^ 4 + 1) := by
          gcongr
          rcases le_total M 1 with h | h
          · rw [max_eq_right h]; norm_num
          · rw [max_eq_left h]; exact Nat.le_add_right _ _
    have h2pos : 1 ≤ 2 ^ (3 * t) := Nat.one_le_pow _ _ (by decide)
    calc
      (M + 1) ^ 4 ≤ 16 * (M ^ 4 + 1) := h16
      _ ≤ 16 * (b ^ 9 * 2 ^ (3 * t) + 2 ^ (3 * t)) := by gcongr
      _ = 16 * (b ^ 9 + 1) * 2 ^ (3 * t) := by ring
  have hS_pow4 : S.card ^ 4 ≤ (2 ^ t) ^ 4 := by
    calc
      S.card ^ 4 ≤ ((1 + 3 * t) * (M + 1)) ^ 4 := Nat.pow_le_pow_left hS_le 4
      _ = (1 + 3 * t) ^ 4 * (M + 1) ^ 4 := by ring
      _ ≤ (1 + 3 * t) ^ 4 * (16 * (b ^ 9 + 1) * 2 ^ (3 * t)) :=
        Nat.mul_le_mul_left _ hM1_pow4
      _ = ((1 + 3 * t) ^ 4 * (16 * (b ^ 9 + 1))) * 2 ^ (3 * t) := by ring
      _ ≤ 2 ^ t * 2 ^ (3 * t) := Nat.mul_le_mul_right _ (hT t ht)
      _ = (2 ^ t) ^ 4 := by rw [← pow_add, ← pow_mul]; ring_nf
  exact le_of_pow_le_pow_left₀ (by decide) (Nat.zero_le _) hS_pow4
