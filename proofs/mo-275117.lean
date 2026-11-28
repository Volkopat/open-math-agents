import OMAStatements.S_mo_275117

namespace OMA.S_mo_275117_Proof

private lemma prime_dvd_totient_imp {q : ℕ} (hq : q.Prime) :
    ∀ m : ℕ, m ≠ 0 → q ∣ m.totient →
      ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ ((p = q ∧ q ^ 2 ∣ m) ∨ q ∣ p - 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm0 hd
    by_cases hm1 : m = 1
    · subst hm1
      simp at hd
      have := hq.two_le
      omega
    · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
      set k := m.factorization p
      set u := ordCompl[p] m
      have hk : 1 ≤ k := Nat.Prime.factorization_pos_of_dvd hp hm0 hpm
      have hmul : p ^ k * u = m := Nat.ordProj_mul_ordCompl_eq_self m p
      have hcop : (p ^ k).Coprime u := (Nat.coprime_ordCompl hp hm0).pow_left k
      have htot : m.totient = (p ^ k).totient * u.totient := by
        rw [← hmul, Nat.totient_mul hcop]
      rw [htot, Nat.totient_prime_pow hp (by omega : 0 < k)] at hd
      rcases hq.dvd_mul.mp hd with h1 | h2
      · rcases hq.dvd_mul.mp h1 with hpow | hpm1
        · have hqp : q ∣ p := hq.dvd_of_dvd_pow hpow
          have hpq : p = q := ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp).symm
          have hk2 : 2 ≤ k := by
            by_contra hklt
            have hk1 : k = 1 := by omega
            rw [hk1] at hpow
            simp at hpow
            have := hq.two_le
            omega
          refine ⟨p, hp, hpm, Or.inl ⟨hpq, ?_⟩⟩
          rw [← hpq, ← hmul]
          exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow p hk2) u
        · exact ⟨p, hp, hpm, Or.inr hpm1⟩
      · have hu_pos : 0 < u := Nat.ordCompl_pos p hm0
        have hu_lt : u < m := by
          have hp2 : 2 ≤ p ^ k := by
            calc 2 ≤ p := hp.two_le
              _ = p ^ 1 := (pow_one p).symm
              _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
          nlinarith
        obtain ⟨r, hr, hru, hcond⟩ := ih u hu_lt (by omega) h2
        have hrm : r ∣ m := dvd_trans hru (hmul ▸ dvd_mul_left u (p ^ k))
        refine ⟨r, hr, hrm, ?_⟩
        rcases hcond with ⟨hrq, hq2u⟩ | hqr
        · exact Or.inl ⟨hrq, dvd_trans hq2u (hmul ▸ dvd_mul_left u (p ^ k))⟩
        · exact Or.inr hqr

private lemma totient_ne_68 (m : ℕ) : m.totient ≠ 68 := by
  intro hm
  have hm0 : m ≠ 0 := by intro h; subst h; simp at hm
  have h17p : Nat.Prime 17 := by decide
  have h17d : 17 ∣ m.totient := by rw [hm]; decide
  obtain ⟨p, hp, hpm, hcond⟩ := prime_dvd_totient_imp h17p m hm0 h17d
  rcases hcond with ⟨rfl, h17sq⟩ | h17pm1
  · have hdvd : (17 ^ 2).totient ∣ m.totient := Nat.totient_dvd_of_dvd h17sq
    rw [Nat.totient_prime_pow h17p (by decide : 0 < 2), hm] at hdvd
    norm_num at hdvd
  · have hdvd : p.totient ∣ m.totient := Nat.totient_dvd_of_dvd hpm
    rw [Nat.totient_prime hp, hm] at hdvd
    obtain ⟨t, ht⟩ := h17pm1
    have hp2 : 2 ≤ p := hp.two_le
    have ht_pos : 1 ≤ t := by omega
    have ht_dvd : t ∣ 4 := by
      have : 17 * t ∣ 17 * 4 := by simpa [ht] using hdvd
      exact (mul_dvd_mul_iff_left (by decide : 17 ≠ 0)).mp this
    have ht_le : t ≤ 4 := Nat.le_of_dvd (by decide) ht_dvd
    interval_cases t
    · have : p = 18 := by omega
      subst this; exact absurd hp (by decide)
    · have : p = 35 := by omega
      subst this; exact absurd hp (by decide)
    · have : p = 52 := by omega
      subst this; exact absurd hp (by decide)
    · have : p = 69 := by omega
      subst this; exact absurd hp (by decide)

private lemma two_dvd_totient_of_odd_gt_one {u : ℕ} (hu1 : 1 < u) (hodd : u % 2 = 1) :
    2 ∣ u.totient := by
  obtain ⟨p, hp, hpu⟩ := Nat.exists_prime_and_dvd (by omega : u ≠ 1)
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | h
    · obtain ⟨t, ht⟩ := hpu; omega
    · exact h
  have hd1 : 2 ∣ p - 1 := by omega
  have hd2 : p.totient ∣ u.totient := Nat.totient_dvd_of_dvd hpu
  rw [Nat.totient_prime hp] at hd2
  exact dvd_trans hd1 hd2

private lemma totient_mod_four_eq_two {m : ℕ} (hmod : m.totient % 4 = 2) (hgt : 2 < m.totient) :
    ∃ p e : ℕ, p.Prime ∧ p % 2 = 1 ∧ m.totient = p ^ e * (p - 1) := by
  have hm0 : m ≠ 0 := by intro h; subst h; simp at hmod
  set a := m.factorization 2
  set u := ordCompl[2] m
  have hmul : 2 ^ a * u = m := Nat.ordProj_mul_ordCompl_eq_self m 2
  have hcop : (2 ^ a).Coprime u := (Nat.coprime_ordCompl Nat.prime_two hm0).pow_left a
  have htot : m.totient = (2 ^ a).totient * u.totient := by
    rw [← hmul, Nat.totient_mul hcop]
  have hu_pos : 0 < u := Nat.ordCompl_pos 2 hm0
  have hu_odd : u % 2 = 1 := by
    have hnd : ¬ 2 ∣ u := Nat.not_dvd_ordCompl Nat.prime_two hm0
    omega
  have hu_gt1 : 1 < u := by
    by_contra hle
    have hu1 : u = 1 := by omega
    rw [hu1, Nat.totient_one, mul_one] at htot
    rcases lt_or_ge a 3 with ha | ha
    · interval_cases a
      · simp at htot; omega
      · simp at htot; omega
      · have h4t : (2 ^ 2).totient = 2 := by decide
        rw [h4t] at htot
        omega
    · rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < a)] at htot
      have h4 : 4 ∣ 2 ^ (a - 1) := by
        have : 2 ^ 2 ∣ 2 ^ (a - 1) := Nat.pow_dvd_pow 2 (by omega)
        simpa using this
      have h4m : 4 ∣ m.totient := by
        rw [htot]
        exact dvd_mul_of_dvd_left h4 _
      omega
  have h2u : 2 ∣ u.totient := two_dvd_totient_of_odd_gt_one hu_gt1 hu_odd
  have ha_le1 : a ≤ 1 := by
    by_contra hge
    have ha2 : 2 ≤ a := by omega
    have h2a : 2 ∣ (2 ^ a).totient := by
      rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < a)]
      norm_num
      omega
    have h4m : 4 ∣ m.totient := by
      rw [htot]
      obtain ⟨x, hx⟩ := h2a
      obtain ⟨y, hy⟩ := h2u
      exact ⟨x * y, by rw [hx, hy]; ring⟩
    omega
  have h2a_tot : (2 ^ a).totient = 1 := by
    interval_cases a <;> simp
  rw [h2a_tot, one_mul] at htot
  obtain ⟨p, hp, hpu⟩ := Nat.exists_prime_and_dvd (by omega : u ≠ 1)
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | h
    · obtain ⟨t, ht⟩ := hpu; omega
    · exact h
  set k := u.factorization p
  set v := ordCompl[p] u
  have hu0 : u ≠ 0 := by omega
  have hk : 1 ≤ k := Nat.Prime.factorization_pos_of_dvd hp hu0 hpu
  have hmul_u : p ^ k * v = u := Nat.ordProj_mul_ordCompl_eq_self u p
  have hcop_u : (p ^ k).Coprime v := (Nat.coprime_ordCompl hp hu0).pow_left k
  have htot_u : u.totient = (p ^ k).totient * v.totient := by
    rw [← hmul_u, Nat.totient_mul hcop_u]
  have hv_pos : 0 < v := Nat.ordCompl_pos p hu0
  have hv_odd : v % 2 = 1 := by
    have hv_dvd : v ∣ u := hmul_u ▸ dvd_mul_left v (p ^ k)
    by_contra hne
    have h2v : 2 ∣ v := by omega
    have h2u_dvd : 2 ∣ u := dvd_trans h2v hv_dvd
    omega
  have hv1 : v = 1 := by
    by_contra hne
    have hv_gt1 : 1 < v := by omega
    have h2v : 2 ∣ v.totient := two_dvd_totient_of_odd_gt_one hv_gt1 hv_odd
    have h2pk : 2 ∣ (p ^ k).totient := by
      rw [Nat.totient_prime_pow hp (by omega : 0 < k)]
      exact dvd_mul_of_dvd_right (by omega : 2 ∣ p - 1) _
    have h4m : 4 ∣ m.totient := by
      rw [htot, htot_u]
      obtain ⟨x, hx⟩ := h2pk
      obtain ⟨y, hy⟩ := h2v
      exact ⟨x * y, by rw [hx, hy]; ring⟩
    omega
  refine ⟨p, k - 1, hp, hp_odd, ?_⟩
  rw [htot, htot_u, hv1, Nat.totient_one, mul_one, Nat.totient_prime_pow hp (by omega : 0 < k)]

private lemma pow_mod_periodic {p e d M : ℕ} (hM : 1 < M) (hper : p ^ d % M = 1) :
    p ^ e % M = (p % M) ^ (e % d) % M := by
  have hdiv : e = d * (e / d) + e % d := (Nat.div_add_mod e d).symm
  conv_lhs => rw [hdiv]
  rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, hper, one_pow,
    Nat.mod_eq_of_lt hM, one_mul, Nat.mod_mod, Nat.pow_mod]

private lemma mod_of_add_two_dvd {x M y : ℕ} (hM : 2 < M) (hd : M ∣ y) (h : x + 2 = y) :
    x % M = M - 2 := by
  obtain ⟨t, rfl⟩ := hd
  cases t with
  | zero => simp at h
  | succ k =>
    have hx : x = M * k + (M - 2) := by
      have hm : M * (k + 1) = M * k + M := Nat.mul_succ M k
      omega
    rw [hx, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

private lemma mod_three_of_add_two {x y : ℕ} (hy : y % 3 = 1) (h : x + 2 = y) :
    x % 3 = 2 := by
  omega

private lemma mod_nine_of_add_two {x y : ℕ} (hy : y % 9 = 7) (h : x + 2 = y) :
    x % 9 = 5 := by
  omega

private lemma mod_three_deduction {p e : ℕ} (hp : p.Prime) (hgt : 2 < p ^ e * (p - 1))
    (hmod3 : (p ^ e * (p - 1)) % 3 = 2) : p % 3 = 2 ∧ e % 2 = 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp3 : p % 3 = 2 := by
    have hp3_lt : p % 3 < 3 := Nat.mod_lt p (by decide)
    interval_cases h : p % 3
    · have hp_eq : p = 3 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)).symm
      subst hp_eq
      rcases e with _ | e
      · norm_num at hgt
      · have h3d : 3 ∣ 3 ^ (e + 1) * (3 - 1) :=
          dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) _
        have h0 : (3 ^ (e + 1) * (3 - 1)) % 3 = 0 := Nat.mod_eq_zero_of_dvd h3d
        omega
    · have h3d : 3 ∣ p ^ e * (p - 1) := dvd_mul_of_dvd_right (by omega : 3 ∣ p - 1) _
      have h0 : (p ^ e * (p - 1)) % 3 = 0 := Nat.mod_eq_zero_of_dvd h3d
      omega
    · rfl
  have he_odd : e % 2 = 1 := by
    by_contra hne
    have he0 : e % 2 = 0 := by omega
    have hp2_3 : p ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hp3]
    have hpe3 : p ^ e % 3 = 1 := by
      rw [pow_mod_periodic (by decide : 1 < 3) hp2_3, he0]
      norm_num
    have hpm1_3 : (p - 1) % 3 = 1 := by omega
    rw [Nat.mul_mod, hpe3, hpm1_3] at hmod3
    omega
  exact ⟨hp3, he_odd⟩

private lemma mod_four_deduction {p e : ℕ} (hp_odd : p % 2 = 1)
    (hmod4 : (p ^ e * (p - 1)) % 4 = 2) : p % 4 = 3 := by
  have hcases : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases hcases with h1 | h3
  · have h4d : 4 ∣ p ^ e * (p - 1) := dvd_mul_of_dvd_right (by omega : 4 ∣ p - 1) _
    have h0 : (p ^ e * (p - 1)) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4d
    omega
  · exact h3

private lemma mod_five_deduction {p e : ℕ} (hp : p.Prime) (he_odd : e % 2 = 1)
    (hmod5 : (p ^ e * (p - 1)) % 5 = 3) : p % 5 = 2 := by
  have hp2 : 2 ≤ p := hp.two_le
  have he_pos : 1 ≤ e := by omega
  have hp5_lt : p % 5 < 5 := Nat.mod_lt p (by decide)
  have he4_cases : e % 4 = 1 ∨ e % 4 = 3 := by omega
  interval_cases h : p % 5
  · have h5d : 5 ∣ p ^ e * (p - 1) :=
      dvd_mul_of_dvd_left (dvd_trans (Nat.dvd_of_mod_eq_zero h) (dvd_pow_self p (by omega))) _
    have h0 : (p ^ e * (p - 1)) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5d
    omega
  · have h5d : 5 ∣ p ^ e * (p - 1) := dvd_mul_of_dvd_right (by omega : 5 ∣ p - 1) _
    have h0 : (p ^ e * (p - 1)) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5d
    omega
  · rfl
  · have hp4_5 : p ^ 4 % 5 = 1 := by rw [Nat.pow_mod, h]
    have hpe5 : p ^ e % 5 = 3 ^ (e % 4) % 5 := by
      rw [pow_mod_periodic (by decide : 1 < 5) hp4_5, h]
    have hpm1_5 : (p - 1) % 5 = 2 := by omega
    rw [Nat.mul_mod, hpe5, hpm1_5] at hmod5
    rcases he4_cases with he4 | he4 <;> rw [he4] at hmod5 <;> norm_num at hmod5
  · have hp4_5 : p ^ 4 % 5 = 1 := by rw [Nat.pow_mod, h]
    have hpe5 : p ^ e % 5 = 4 ^ (e % 4) % 5 := by
      rw [pow_mod_periodic (by decide : 1 < 5) hp4_5, h]
    have hpm1_5 : (p - 1) % 5 = 3 := by omega
    rw [Nat.mul_mod, hpe5, hpm1_5] at hmod5
    rcases he4_cases with he4 | he4 <;> rw [he4] at hmod5 <;> norm_num at hmod5

private lemma mod_eight_deduction {p e : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (he_odd : e % 2 = 1) (hmod8 : (p ^ e * (p - 1)) % 8 = 6) : p % 8 = 3 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hcases : p % 8 = 3 ∨ p % 8 = 7 := by omega
  rcases hcases with h3 | h7
  · exact h3
  · have hp2_8 : p ^ 2 % 8 = 1 := by rw [Nat.pow_mod, h7]
    have hpe8 : p ^ e % 8 = 7 := by
      rw [pow_mod_periodic (by decide : 1 < 8) hp2_8, h7, he_odd]
      norm_num
    have hpm1_8 : (p - 1) % 8 = 6 := by omega
    rw [Nat.mul_mod, hpe8, hpm1_8] at hmod8
    omega

private lemma mod_nine_deduction {p e : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2)
    (he_odd : e % 2 = 1) (hmod9 : (p ^ e * (p - 1)) % 9 = 5) : e % 3 ≠ 1 := by
  intro he3_eq
  have hp2 : 2 ≤ p := hp.two_le
  have he6 : e % 6 = 1 := by omega
  have hp9_cases : p % 9 = 2 ∨ p % 9 = 5 ∨ p % 9 = 8 := by omega
  have hp6_9 : p ^ 6 % 9 = 1 := by
    rw [Nat.pow_mod]
    rcases hp9_cases with h | h | h <;> rw [h]
  have hpe9 : p ^ e % 9 = p % 9 := by
    rw [pow_mod_periodic (by decide : 1 < 9) hp6_9, he6, pow_one, Nat.mod_mod]
  rw [Nat.mul_mod, hpe9] at hmod9
  rcases hp9_cases with h | h | h
  · have hpm1 : (p - 1) % 9 = 1 := by omega
    rw [h, hpm1] at hmod9; omega
  · have hpm1 : (p - 1) % 9 = 4 := by omega
    rw [h, hpm1] at hmod9; omega
  · have hpm1 : (p - 1) % 9 = 7 := by omega
    rw [h, hpm1] at hmod9; omega

private lemma not_sq_two_mod_five : ¬ IsSquare (2 : ZMod 5) := by decide
private lemma not_sq_three_mod_seven : ¬ IsSquare (3 : ZMod 7) := by decide
private lemma not_sq_five_mod_seven : ¬ IsSquare (5 : ZMod 7) := by decide
private lemma not_sq_six_mod_seven : ¬ IsSquare (6 : ZMod 7) := by decide

private lemma qr_mod_seven {p e l : ℕ} (hp : p.Prime) (he_pos : 1 ≤ e)
    (hp8 : p % 8 = 3) (hp5 : p % 5 = 2)
    (heq : p ^ e * (p - 1) + 2 = 7 * 10 ^ (l + 3)) :
    p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp_ne2 : p ≠ 2 := by omega
  have hp4 : p % 4 = 3 := by omega
  have hleg2 : legendreSym p 2 = -1 := by
    rw [legendreSym.eq_neg_one_iff p]
    norm_cast
    rw [ZMod.exists_sq_eq_two_iff hp_ne2]
    omega
  have hleg5 : legendreSym p 5 = -1 := by
    change legendreSym p (5 : ℕ) = -1
    rw [legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by decide) hp_ne2]
    rw [legendreSym.mod 5 (p : ℤ)]
    have hp5_int : ((p : ℤ) % (5 : ℕ)) = 2 := by exact_mod_cast hp5
    rw [hp5_int, legendreSym.eq_neg_one_iff 5]
    exact not_sq_two_mod_five
  have hleg10 : legendreSym p 10 = 1 := by
    have : (10 : ℤ) = 2 * 5 := by norm_num
    rw [this, legendreSym.mul p, hleg2, hleg5]
    norm_num
  have hleg10pow : legendreSym p ((10 : ℤ) ^ (l + 3)) = 1 := by
    change (legendreSym.hom p) ((10 : ℤ) ^ (l + 3)) = 1
    rw [map_pow]
    change (legendreSym p 10) ^ (l + 3) = 1
    rw [hleg10, one_pow]
  have hcast_eq : (((7 * (10 : ℤ) ^ (l + 3)) : ℤ) : ZMod p) = ((2 : ℤ) : ZMod p) := by
    have hpdvd : p ∣ p ^ e * (p - 1) := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
    have hzero : ((p ^ e * (p - 1) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hpdvd
    have hcast : ((p ^ e * (p - 1) + 2 : ℕ) : ZMod p) = ((7 * 10 ^ (l + 3) : ℕ) : ZMod p) := by
      rw [heq]
    rw [Nat.cast_add, hzero, zero_add] at hcast
    push_cast at hcast ⊢
    exact hcast.symm
  have hleg_rhs : legendreSym p (7 * (10 : ℤ) ^ (l + 3)) = legendreSym p 2 := by
    simp only [legendreSym, hcast_eq]
  have hleg7 : legendreSym p 7 = -1 := by
    rw [legendreSym.mul p, hleg10pow, mul_one, hleg2] at hleg_rhs
    exact hleg_rhs
  have hleg7p : legendreSym 7 p = 1 := by
    rw [legendreSym.quadratic_reciprocity_three_mod_four (p := p) (q := 7) hp4 (by decide)]
    change -legendreSym p 7 = 1
    rw [hleg7]
    norm_num
  rw [legendreSym.mod 7 (p : ℤ)] at hleg7p
  have hp7_lt : p % 7 < 7 := Nat.mod_lt p (by decide)
  interval_cases h : p % 7
  · have hint : ((p : ℤ) % (7 : ℕ)) = 0 := by exact_mod_cast h
    rw [hint] at hleg7p
    simp at hleg7p
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · have hint : ((p : ℤ) % (7 : ℕ)) = 3 := by exact_mod_cast h
    rw [hint] at hleg7p
    have hnsq : legendreSym 7 3 = -1 := by
      rw [legendreSym.eq_neg_one_iff 7]
      exact not_sq_three_mod_seven
    omega
  · exact Or.inr (Or.inr rfl)
  · have hint : ((p : ℤ) % (7 : ℕ)) = 5 := by exact_mod_cast h
    rw [hint] at hleg7p
    have hnsq : legendreSym 7 5 = -1 := by
      rw [legendreSym.eq_neg_one_iff 7]
      exact not_sq_five_mod_seven
    omega
  · have hint : ((p : ℤ) % (7 : ℕ)) = 6 := by exact_mod_cast h
    rw [hint] at hleg7p
    have hnsq : legendreSym 7 6 = -1 := by
      rw [legendreSym.eq_neg_one_iff 7]
      exact not_sq_six_mod_seven
    omega

private lemma mod_seven_contradiction {p e : ℕ} (hp : p.Prime)
    (hp7 : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) (he3 : e % 3 ≠ 1)
    (hmod7 : (p ^ e * (p - 1)) % 7 = 5) : False := by
  have hp2 : 2 ≤ p := hp.two_le
  have he3_lt : e % 3 < 3 := Nat.mod_lt e (by decide)
  rcases hp7 with h1 | h2 | h4
  · have h7d : 7 ∣ p ^ e * (p - 1) := dvd_mul_of_dvd_right (by omega : 7 ∣ p - 1) _
    have h0 : (p ^ e * (p - 1)) % 7 = 0 := Nat.mod_eq_zero_of_dvd h7d
    omega
  · have hp3_7 : p ^ 3 % 7 = 1 := by rw [Nat.pow_mod, h2]
    have hpe7 : p ^ e % 7 = 2 ^ (e % 3) % 7 := by
      rw [pow_mod_periodic (by decide : 1 < 7) hp3_7, h2]
    have hpm1_7 : (p - 1) % 7 = 1 := by omega
    rw [Nat.mul_mod, hpe7, hpm1_7] at hmod7
    interval_cases e % 3 <;> norm_num at hmod7
  · have hp3_7 : p ^ 3 % 7 = 1 := by rw [Nat.pow_mod, h4]
    have hpe7 : p ^ e % 7 = 4 ^ (e % 3) % 7 := by
      rw [pow_mod_periodic (by decide : 1 < 7) hp3_7, h4]
    have hpm1_7 : (p - 1) % 7 = 3 := by omega
    rw [Nat.mul_mod, hpe7, hpm1_7] at hmod7
    interval_cases h3 : e % 3
    · norm_num at hmod7
    · exact absurd rfl he3
    · norm_num at hmod7

private lemma no_sol_n_1 {p e : ℕ} (hp : p.Prime) (he_odd : e % 2 = 1)
    (hp3 : p % 3 = 2) (hp4 : p % 4 = 3) (hp5 : p % 5 = 2)
    (heq : p ^ e * (p - 1) + 2 = 7 * 10 ^ 2) : False := by
  have hp_ge : 47 ≤ p := by omega
  have hpe_ge : p ≤ p ^ e := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos (by omega)
  have hprod_ge : 47 * 46 ≤ p ^ e * (p - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

private lemma main_proof : ∀ l m : ℕ, Nat.totient m ≠ 7 * 10 ^ (l + 1) - 2 := by
  intro l m hm
  rcases l with _ | l
  · norm_num at hm
    exact totient_ne_68 m hm
  · have hm' : m.totient = 7 * 10 ^ (l + 2) - 2 := by simpa [Nat.add_assoc] using hm
    have h10_ge : 100 ≤ 10 ^ (l + 2) := by
      calc 100 = 10 ^ 2 := by norm_num
        _ ≤ 10 ^ (l + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hgt : 2 < m.totient := by omega
    have hmt_add : m.totient + 2 = 7 * 10 ^ (l + 2) := by omega
    have h4_dvd : 4 ∣ 7 * 10 ^ (l + 2) :=
      dvd_mul_of_dvd_right (dvd_trans (by decide : 4 ∣ 10 ^ 2) (Nat.pow_dvd_pow 10 (Nat.le_add_left 2 l))) 7
    have hmod4 : m.totient % 4 = 2 := mod_of_add_two_dvd (by decide) h4_dvd hmt_add
    obtain ⟨p, e, hp, hp_odd, hpe⟩ := totient_mod_four_eq_two hmod4 hgt
    have heq : p ^ e * (p - 1) + 2 = 7 * 10 ^ (l + 2) := hpe ▸ hmt_add
    have h7_mod3 : (7 * 10 ^ (l + 2)) % 3 = 1 := by
      rw [Nat.mul_mod, Nat.pow_mod]
      norm_num
    have hmod3 : (p ^ e * (p - 1)) % 3 = 2 := mod_three_of_add_two h7_mod3 heq
    obtain ⟨hp3, he_odd⟩ := mod_three_deduction hp (hpe ▸ hgt) hmod3
    have hp4 : p % 4 = 3 := mod_four_deduction hp_odd (hpe ▸ hmod4)
    have h5_dvd : 5 ∣ 7 * 10 ^ (l + 2) :=
      dvd_mul_of_dvd_right
        (dvd_trans (by decide : 5 ∣ 10 ^ 1) (Nat.pow_dvd_pow 10 (Nat.le_trans (by decide : 1 ≤ 2) (Nat.le_add_left 2 l)))) 7
    have hmod5 : (p ^ e * (p - 1)) % 5 = 3 := mod_of_add_two_dvd (by decide) h5_dvd heq
    have hp5 : p % 5 = 2 := mod_five_deduction hp he_odd hmod5
    rcases l with _ | l
    · exact no_sol_n_1 hp he_odd hp3 hp4 hp5 heq
    · have heq' : p ^ e * (p - 1) + 2 = 7 * 10 ^ (l + 3) := by simpa [Nat.add_assoc] using heq
      have h8_dvd : 8 ∣ 7 * 10 ^ (l + 3) :=
        dvd_mul_of_dvd_right (dvd_trans (by decide : 8 ∣ 10 ^ 3) (Nat.pow_dvd_pow 10 (Nat.le_add_left 3 l))) 7
      have hmod8 : (p ^ e * (p - 1)) % 8 = 6 := mod_of_add_two_dvd (by decide) h8_dvd heq'
      have hp8 : p % 8 = 3 := mod_eight_deduction hp hp4 he_odd hmod8
      have h7_mod9 : (7 * 10 ^ (l + 3)) % 9 = 7 := by
        rw [Nat.mul_mod, Nat.pow_mod]
        norm_num
      have hmod9 : (p ^ e * (p - 1)) % 9 = 5 := mod_nine_of_add_two h7_mod9 heq'
      have he3 : e % 3 ≠ 1 := mod_nine_deduction hp hp3 he_odd hmod9
      have he_pos : 1 ≤ e := Nat.pos_of_ne_zero (fun h => by rw [h] at he_odd; simp at he_odd)
      have hp7 : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 :=
        qr_mod_seven hp he_pos hp8 hp5 heq'
      have hmod7 : (p ^ e * (p - 1)) % 7 = 5 :=
        mod_of_add_two_dvd (by decide) (dvd_mul_right 7 _) heq'
      exact mod_seven_contradiction hp hp7 he3 hmod7

end OMA.S_mo_275117_Proof

theorem OMA.solution : type_of% @OMA.S_mo_275117.main :=
  OMA.S_mo_275117_Proof.main_proof
