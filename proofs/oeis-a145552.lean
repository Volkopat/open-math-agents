import OMAStatements.S_oeis_a145552

namespace OMA.S_oeis_a145552_proof

private lemma exists_prime_mod_three_eq_two_of_mod_three_eq_two (n : ℕ) (hn : n % 3 = 2) :
    ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 3 = 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hn2 : 2 ≤ n := by omega
      let p := n.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      have hmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
      rcases hmod with h0 | h1 | h2
      · have h3p : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
        have hp3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p).symm
        rw [hp3] at hpdvd
        omega
      · have hlt : n / p < n := Nat.div_lt_self (by omega) hp.one_lt
        have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpdvd
        have hmod_div : (n / p) % 3 = 2 := by
          have := congrArg (· % 3) hmul
          rw [Nat.mul_mod, h1, one_mul, Nat.mod_mod] at this
          omega
        obtain ⟨q, hq, hqdvd, hqmod⟩ := ih (n / p) hlt hmod_div
        exact ⟨q, hq, dvd_trans hqdvd (Nat.div_dvd_of_dvd hpdvd), hqmod⟩
      · exact ⟨p, hp, hpdvd, h2⟩

private lemma exists_gt_prime_mod_three_eq_two (N : ℕ) :
    ∃ p > N, Nat.Prime p ∧ p % 3 = 2 := by
  let M := 3 * (N + 2).factorial - 1
  have hfac : 2 ≤ (N + 2).factorial := by
    have h1 := Nat.factorial_pos (N + 1)
    rw [Nat.factorial_succ]
    nlinarith
  have hM : M % 3 = 2 := by
    dsimp [M]
    omega
  obtain ⟨p, hp, hpdvd, hpmod⟩ := exists_prime_mod_three_eq_two_of_mod_three_eq_two M hM
  refine ⟨p, ?_, hp, hpmod⟩
  by_contra hle
  push Not at hle
  have hle2 : p ≤ N + 2 := by omega
  have hpfac : p ∣ (N + 2).factorial := Nat.dvd_factorial hp.pos hle2
  have hp3 : p ∣ 3 * (N + 2).factorial := dvd_mul_of_dvd_right hpfac 3
  have hMeq : 3 * (N + 2).factorial = M + 1 := by
    dsimp [M]
    omega
  rw [hMeq] at hp3
  have hp1 : p ∣ 1 := (Nat.dvd_add_right hpdvd).mp hp3
  exact hp.not_dvd_one hp1

private lemma legendreSym_neg_three_eq_neg_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp3 : p % 3 = 2) : legendreSym p (-3) = -1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hneg : legendreSym p (-3) = ZMod.χ₄ p * legendreSym p 3 := by
    simpa using legendreSym.at_neg hp2 3
  have hqr : legendreSym p 3 = (-1) ^ (3 / 2 * (p / 2)) * legendreSym 3 p := by
    simpa using legendreSym.quadratic_reciprocity' (p := 3) (q := p) (by norm_num) hp2
  have h3p : legendreSym 3 p = -1 := by
    rw [legendreSym.mod 3 (p : ℤ)]
    have hp_mod : (p : ℤ) % (3 : ℕ) = 2 := by omega
    rw [hp_mod, legendreSym.eq_neg_one_iff]
    norm_cast
    rw [ZMod.exists_sq_eq_two_iff (by norm_num)]
    norm_num
  have hp_odd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp2
  have hchi : ZMod.χ₄ p = (-1) ^ (p / 2) := ZMod.χ₄_eq_neg_one_pow hp_odd
  rw [hneg, hqr, h3p, hchi]
  have hpow : (-1 : ℤ) ^ (p / 2) * (-1 : ℤ) ^ (p / 2) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  norm_num at hpow ⊢
  linarith

private lemma prime_dvd_sq_sub_mul_add_sq {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2) {a b : ℤ}
    (h : (p : ℤ) ∣ a ^ 2 - a * b + b ^ 2) : (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b := by
  rcases eq_or_ne p 2 with rfl | hp2
  · rcases Int.even_or_odd a with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;>
      rcases Int.even_or_odd b with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · exact ⟨⟨k, by ring⟩, ⟨l, by ring⟩⟩
    · exfalso
      obtain ⟨m, hm⟩ := h
      have hform : (k + k) ^ 2 - (k + k) * (2 * l + 1) + (2 * l + 1) ^ 2 =
          2 * (2 * k ^ 2 - k * (2 * l + 1) + 2 * l ^ 2 + 2 * l) + 1 := by ring
      rw [hform] at hm
      omega
    · exfalso
      obtain ⟨m, hm⟩ := h
      have hform : (2 * k + 1) ^ 2 - (2 * k + 1) * (l + l) + (l + l) ^ 2 =
          2 * (2 * k ^ 2 + 2 * k - (2 * k + 1) * l + 2 * l ^ 2) + 1 := by ring
      rw [hform] at hm
      omega
    · exfalso
      obtain ⟨m, hm⟩ := h
      have hform : (2 * k + 1) ^ 2 - (2 * k + 1) * (2 * l + 1) + (2 * l + 1) ^ 2 =
          2 * (2 * k ^ 2 + k - 2 * k * l + l + 2 * l ^ 2) + 1 := by ring
      rw [hform] at hm
      omega
  · have : Fact p.Prime := ⟨hp⟩
    have hleg : legendreSym p (-3) = -1 := legendreSym_neg_three_eq_neg_one hp2 hp3
    have h4 : (p : ℤ) ∣ (2 * a - b) ^ 2 - (-3) * b ^ 2 := by
      have hid : (2 * a - b) ^ 2 - (-3) * b ^ 2 = 4 * (a ^ 2 - a * b + b ^ 2) := by ring
      rw [hid]
      exact dvd_mul_of_dvd_right h 4
    obtain ⟨h1, hb⟩ := legendreSym.prime_dvd_of_eq_neg_one hleg h4
    have h2a : (p : ℤ) ∣ 2 * a := by
      have hid : 2 * a = (2 * a - b) + b := by ring
      rw [hid]
      exact dvd_add h1 hb
    have hprime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have ha : (p : ℤ) ∣ a := by
      rcases hprime_int.dvd_or_dvd h2a with hp_dvd_2 | ha
      · exfalso
        have hp2_nat : p ∣ 2 := Int.natCast_dvd_natCast.mp hp_dvd_2
        have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2_nat
        have hp_ge : 2 ≤ p := hp.two_le
        omega
      · exact ha
    exact ⟨ha, hb⟩

private lemma prime_dvd_of_sum_cubes_eq_pow {p k m x y : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2)
    (hk : 1 ≤ k) (hbound : 4 * m < p ^ (2 * k)) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxy : x ^ 3 + y ^ 3 = p ^ k * m) : p ∣ x ∧ p ∣ y := by
  by_contra hnot
  have hpx_iff_py : p ∣ x ↔ p ∣ y := by
    have hpdvd_sum : p ∣ x ^ 3 + y ^ 3 := by
      rw [hxy]
      exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m
    constructor
    · intro hpx
      have hpx3 : p ∣ x ^ 3 := dvd_pow hpx (by norm_num)
      have hpy3 : p ∣ y ^ 3 := (Nat.dvd_add_right hpx3).mp hpdvd_sum
      exact hp.dvd_of_dvd_pow hpy3
    · intro hpy
      have hpy3 : p ∣ y ^ 3 := dvd_pow hpy (by norm_num)
      have hpx3 : p ∣ x ^ 3 := (Nat.dvd_add_left hpy3).mp hpdvd_sum
      exact hp.dvd_of_dvd_pow hpx3
  have hnx : ¬ p ∣ x := fun h => hnot ⟨h, hpx_iff_py.mp h⟩
  have hny : ¬ p ∣ y := fun h => hnot ⟨hpx_iff_py.mpr h, h⟩
  let qz : ℤ := (x : ℤ) ^ 2 - (x : ℤ) * (y : ℤ) + (y : ℤ) ^ 2
  have hqz_nonneg : 0 ≤ qz := by
    dsimp [qz]
    nlinarith [sq_nonneg ((x : ℤ) - y)]
  let q : ℕ := qz.toNat
  have hq_cast : (q : ℤ) = qz := Int.toNat_of_nonneg hqz_nonneg
  have hnq : ¬ p ∣ q := by
    intro hpq
    have hpq_int : (p : ℤ) ∣ qz := by
      rw [← hq_cast]
      exact Int.natCast_dvd_natCast.mpr hpq
    obtain ⟨hax, _⟩ := prime_dvd_sq_sub_mul_add_sq hp hp3 hpq_int
    exact hnx (Int.natCast_dvd_natCast.mp hax)
  have hmul_nat : (x + y) * q = p ^ k * m := by
    zify
    rw [hq_cast]
    dsimp [qz]
    calc
      ((x : ℤ) + y) * ((x : ℤ) ^ 2 - (x : ℤ) * (y : ℤ) + (y : ℤ) ^ 2) =
          (x : ℤ) ^ 3 + (y : ℤ) ^ 3 := by ring
      _ = (p : ℤ) ^ k * m := by exact_mod_cast hxy
  have hcop : Nat.Coprime (p ^ k) q := (hp.coprime_iff_not_dvd.mpr hnq).pow_left k
  have hpk_dvd : p ^ k ∣ x + y := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [hmul_nat]
    exact dvd_mul_right (p ^ k) m
  have hpk_le : p ^ k ≤ x + y := Nat.le_of_dvd (by omega) hpk_dvd
  have hineq : (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
    zify
    nlinarith [sq_nonneg ((x : ℤ) - y)]
  have hp3k : (p ^ k) ^ 3 ≤ 4 * (p ^ k * m) := by
    calc
      (p ^ k) ^ 3 ≤ (x + y) ^ 3 := Nat.pow_le_pow_left hpk_le 3
      _ ≤ 4 * (x ^ 3 + y ^ 3) := hineq
      _ = 4 * (p ^ k * m) := by rw [hxy]
  have hpk_pos : 0 < p ^ k := pow_pos hp.pos k
  have hp2k : p ^ (2 * k) ≤ 4 * m := by
    have h1 : p ^ k * p ^ (2 * k) = (p ^ k) ^ 3 := by ring
    have h2 : p ^ k * p ^ (2 * k) ≤ p ^ k * (4 * m) := by
      rw [h1]
      linarith
    exact Nat.le_of_mul_le_mul_left h2 hpk_pos
  omega

private lemma prime_sq_dvd_of_sum_cubes_eq {p m x y : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2)
    (hbound : 4 * m < p ^ 6) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxy : x ^ 3 + y ^ 3 = p ^ 6 * m) : p ^ 2 ∣ x ∧ p ^ 2 ∣ y := by
  have hp12 : 4 * m < p ^ (2 * 6) := by
    have h1 : p ^ 6 ≤ p ^ (2 * 6) := Nat.pow_le_pow_right hp.pos (by norm_num)
    omega
  obtain ⟨hpx, hpy⟩ := prime_dvd_of_sum_cubes_eq_pow hp hp3 (by norm_num) hp12 hx hy hxy
  rcases hpx with ⟨x1, rfl⟩
  rcases hpy with ⟨y1, rfl⟩
  have hx1 : 1 ≤ x1 := Nat.pos_of_mul_pos_left hx
  have hy1 : 1 ≤ y1 := Nat.pos_of_mul_pos_left hy
  have hxy1 : x1 ^ 3 + y1 ^ 3 = p ^ 3 * m := by
    have hp3_ne : p ^ 3 ≠ 0 := pow_ne_zero 3 hp.ne_zero
    apply mul_left_cancel₀ hp3_ne
    calc
      p ^ 3 * (x1 ^ 3 + y1 ^ 3) = (p * x1) ^ 3 + (p * y1) ^ 3 := by ring
      _ = p ^ 6 * m := hxy
      _ = p ^ 3 * (p ^ 3 * m) := by ring
  have hp6 : 4 * m < p ^ (2 * 3) := by simpa using hbound
  obtain ⟨hpx1, hpy1⟩ := prime_dvd_of_sum_cubes_eq_pow hp hp3 (by norm_num) hp6 hx1 hy1 hxy1
  rcases hpx1 with ⟨x0, rfl⟩
  rcases hpy1 with ⟨y0, rfl⟩
  refine ⟨⟨x0, by ring⟩, ⟨y0, by ring⟩⟩

private lemma pow_two_unique_interval {a L U k : ℕ} (h1 : L ≤ 2 ^ a) (h2 : 2 ^ a ≤ U)
    (hk1 : 2 ^ k < L) (hk2 : U < 2 ^ (k + 2)) : a = k + 1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : a ≤ k := by omega
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hle
    omega
  · have hge : k + 2 ≤ a := by omega
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hge
    omega

private lemma pow_two_none_interval {a L U k : ℕ} (h1 : L ≤ 2 ^ a) (h2 : 2 ^ a ≤ U)
    (hk1 : 2 ^ k < L) (hk2 : U < 2 ^ (k + 1)) : False := by
  rcases le_or_gt a k with hle | hgt
  · have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hle
    omega
  · have hge : k + 1 ≤ a := by omega
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hge
    omega

private lemma sol_base (x y : ℕ) (hx : 1 ≤ x) (hxy : x ≤ y)
    (heq : x ^ 3 + y ^ 3 = 6080256576) :
    (x = 228 ∧ y = 1824) ∨ (x = 1026 ∧ y = 1710) := by
  let s := x + y
  have hs_lower : 1826 ≤ s := by
    by_contra hlt
    have hs_le : s ≤ 1825 := by omega
    have hy : 1 ≤ y := by omega
    have hlt3 : x ^ 3 + y ^ 3 < s ^ 3 := by
      have hid : s ^ 3 = x ^ 3 + y ^ 3 + 3 * x * y * (x + y) := by dsimp [s]; ring
      have hpos : 0 < 3 * x * y * (x + y) := by positivity
      omega
    have hs3 : s ^ 3 ≤ 1825 ^ 3 := Nat.pow_le_pow_left hs_le 3
    norm_num at hs3
    omega
  have hs_upper : s ≤ 2897 := by
    by_contra hgt
    have hs_ge : 2898 ≤ s := by omega
    have h4 : s ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
      dsimp [s]
      zify
      nlinarith [sq_nonneg ((x : ℤ) - y)]
    have hs3 : 2898 ^ 3 ≤ s ^ 3 := Nat.pow_le_pow_left hs_ge 3
    norm_num at hs3
    omega
  have hsdvd : s ∣ 6080256576 := by
    rw [← heq]
    have hzdvd : (s : ℤ) ∣ (x : ℤ) ^ 3 + (y : ℤ) ^ 3 := by
      refine ⟨(x : ℤ) ^ 2 - (x : ℤ) * (y : ℤ) + (y : ℤ) ^ 2, ?_⟩
      dsimp [s]
      ring
    exact Int.natCast_dvd_natCast.mp (by exact_mod_cast hzdvd)
  have hfac : (6080256576 : ℕ) = 2 ^ 6 * (3 ^ 6 * 19 ^ 4) := by norm_num
  rw [hfac] at hsdvd
  obtain ⟨d2, d319, hd2, hd319, hs_eq1⟩ := dvd_mul.mp hsdvd
  obtain ⟨d3, d19, hd3, hd19, hd319_eq⟩ := dvd_mul.mp hd319
  obtain ⟨a, ha_le, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
  obtain ⟨b, hb_le, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd3
  have hp19 : Nat.Prime 19 := by norm_num
  obtain ⟨c, hc_le, rfl⟩ := (Nat.dvd_prime_pow hp19).mp hd19
  have hs_eq : s = 2 ^ a * 3 ^ b * 19 ^ c := by
    rw [hs_eq1, hd319_eq, mul_assoc]
  have hs_cases : s = 2166 ∨ s = 2052 ∨ s = 2888 ∨ s = 1944 ∨ s = 2736 ∨ s = 2592 := by
    rcases lt_trichotomy c 2 with hc_lt | rfl | hc_gt
    · interval_cases c
      · rw [pow_zero, mul_one] at hs_eq
        interval_cases b
        · rw [pow_zero, mul_one] at hs_eq
          have ha := Nat.pow_le_pow_right (by norm_num : 0 < 2) ha_le
          norm_num at ha
          omega
        · rw [pow_one] at hs_eq
          have ha := Nat.pow_le_pow_right (by norm_num : 0 < 2) ha_le
          norm_num at ha
          omega
        · have ha := Nat.pow_le_pow_right (by norm_num : 0 < 2) ha_le
          norm_num at ha hs_eq
          omega
        · have ha := Nat.pow_le_pow_right (by norm_num : 0 < 2) ha_le
          norm_num at ha hs_eq
          omega
        · have h2a : 23 ≤ 2 ^ a ∧ 2 ^ a ≤ 35 := by norm_num at hs_eq; omega
          have ha : a = 5 := pow_two_unique_interval (k := 4) h2a.1 h2a.2 (by norm_num) (by norm_num)
          subst ha
          norm_num at hs_eq
          omega
        · have h2a : 8 ≤ 2 ^ a ∧ 2 ^ a ≤ 11 := by norm_num at hs_eq; omega
          have ha : a = 3 := pow_two_unique_interval (k := 2) h2a.1 h2a.2 (by norm_num) (by norm_num)
          subst ha
          norm_num at hs_eq
          omega
        · have h2a : 3 ≤ 2 ^ a ∧ 2 ^ a ≤ 3 := by norm_num at hs_eq; omega
          exfalso
          exact pow_two_none_interval (k := 1) h2a.1 h2a.2 (by norm_num) (by norm_num)
      · rw [pow_one] at hs_eq
        rcases le_or_gt b 4 with hb_small | hb_big
        · interval_cases b
          · rw [pow_zero, mul_one] at hs_eq
            have ha := Nat.pow_le_pow_right (by norm_num : 0 < 2) ha_le
            norm_num at ha hs_eq
            omega
          · rw [pow_one] at hs_eq
            have h2a : 33 ≤ 2 ^ a ∧ 2 ^ a ≤ 50 := by omega
            exfalso
            exact pow_two_none_interval (k := 5) h2a.1 h2a.2 (by norm_num) (by norm_num)
          · have h2a : 11 ≤ 2 ^ a ∧ 2 ^ a ≤ 16 := by norm_num at hs_eq; omega
            have ha : a = 4 := pow_two_unique_interval (k := 3) h2a.1 h2a.2 (by norm_num) (by norm_num)
            subst ha
            norm_num at hs_eq
            omega
          · have h2a : 4 ≤ 2 ^ a ∧ 2 ^ a ≤ 5 := by norm_num at hs_eq; omega
            have ha : a = 2 := pow_two_unique_interval (k := 1) h2a.1 h2a.2 (by norm_num) (by norm_num)
            subst ha
            norm_num at hs_eq
            omega
          · have h2a : 2 ≤ 2 ^ a ∧ 2 ^ a ≤ 1 := by norm_num at hs_eq; omega
            omega
        · exfalso
          have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
          have h3 : 3 ^ 5 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb_big
          have hmul : 3 ^ 5 * 19 ≤ 2 ^ a * 3 ^ b * 19 := by nlinarith
          norm_num at hmul
          omega
    · have h19_2 : 19 ^ 2 = 361 := by norm_num
      rw [h19_2] at hs_eq
      rcases le_or_gt b 1 with hb_small | hb_big
      · interval_cases b
        · rw [pow_zero, mul_one] at hs_eq
          have h2a : 6 ≤ 2 ^ a ∧ 2 ^ a ≤ 8 := by omega
          have ha : a = 3 := pow_two_unique_interval (k := 2) h2a.1 h2a.2 (by norm_num) (by norm_num)
          subst ha
          norm_num at hs_eq
          omega
        · rw [pow_one] at hs_eq
          have h2a : 2 ≤ 2 ^ a ∧ 2 ^ a ≤ 2 := by omega
          have ha : a = 1 := pow_two_unique_interval (k := 0) h2a.1 h2a.2 (by norm_num) (by norm_num)
          subst ha
          norm_num at hs_eq
          omega
      · exfalso
        have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
        have h3 : 3 ^ 2 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb_big
        have hmul : 3 ^ 2 * 361 ≤ 2 ^ a * 3 ^ b * 361 := by nlinarith
        norm_num at hmul
        omega
    · exfalso
      have h1 : 1 ≤ 2 ^ a * 3 ^ b := Nat.succ_le_of_lt (by positivity)
      have h19 : 19 ^ 3 ≤ 19 ^ c := Nat.pow_le_pow_right (by norm_num) hc_gt
      have hmul : 19 ^ 3 ≤ 2 ^ a * 3 ^ b * 19 ^ c := by nlinarith
      norm_num at hmul
      omega
  have hd_eq : s * (s ^ 2 + 3 * (y - x) ^ 2) = 4 * 6080256576 := by
    rw [← heq]
    dsimp [s]
    zify [hxy]
    ring
  rcases hs_cases with hs | hs | hs | hs | hs | hs
  · exfalso
    rw [hs] at hd_eq
    have hd2 : (y - x) ^ 2 = 2178996 := by omega
    rcases le_or_gt (y - x) 1476 with hle | hgt
    · nlinarith
    · have hge : 1477 ≤ y - x := by omega
      nlinarith
  · left
    rw [hs] at hd_eq
    have hd2 : (y - x) ^ 2 = 1596 ^ 2 := by omega
    have hdx : y - x = 1596 := by nlinarith
    dsimp [s] at hs
    omega
  · exfalso
    rw [hs] at hd_eq
    omega
  · exfalso
    rw [hs] at hd_eq
    have hd2 : (y - x) ^ 2 = 2910560 := by omega
    rcases le_or_gt (y - x) 1706 with hle | hgt
    · nlinarith
    · have hge : 1707 ≤ y - x := by omega
      nlinarith
  · right
    rw [hs] at hd_eq
    have hd2 : (y - x) ^ 2 = 684 ^ 2 := by omega
    have hdx : y - x = 684 := by nlinarith
    dsimp [s] at hs
    omega
  · exfalso
    rw [hs] at hd_eq
    have hd2 : (y - x) ^ 2 = 888216 := by omega
    rcases le_or_gt (y - x) 942 with hle | hgt
    · nlinarith
    · have hge : 943 ≤ y - x := by omega
      nlinarith

private lemma r_pow_six_mul_base {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2)
    (hbound : 4 * 6080256576 < p ^ 6) :
    OMA.S_oeis_a145552.r (p ^ 6 * 6080256576) = 2 := by
  unfold OMA.S_oeis_a145552.r
  have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
  have hp6_ge : p ^ 2 ≤ p ^ 6 := Nat.pow_le_pow_right hp.pos (by norm_num)
  have hfilter :
      (Finset.Icc 1 (p ^ 6 * 6080256576) ×ˢ Finset.Icc 1 (p ^ 6 * 6080256576)).filter
        (fun t => t.1 ≤ t.2 ∧ t.1 ^ 3 + t.2 ^ 3 = p ^ 6 * 6080256576) =
      {(p ^ 2 * 228, p ^ 2 * 1824), (p ^ 2 * 1026, p ^ 2 * 1710)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hx1, _⟩, ⟨hy1, _⟩⟩, hxy, heq⟩
      obtain ⟨⟨x0, rfl⟩, ⟨y0, rfl⟩⟩ :=
        prime_sq_dvd_of_sum_cubes_eq hp hp3 hbound hx1 hy1 heq
      have hx0 : 1 ≤ x0 := Nat.pos_of_mul_pos_left hx1
      have hx0y0 : x0 ≤ y0 := Nat.le_of_mul_le_mul_left hxy hp2_pos
      have heq0 : x0 ^ 3 + y0 ^ 3 = 6080256576 := by
        have hp6_ne : p ^ 6 ≠ 0 := pow_ne_zero 6 hp.ne_zero
        apply mul_left_cancel₀ hp6_ne
        calc
          p ^ 6 * (x0 ^ 3 + y0 ^ 3) = (p ^ 2 * x0) ^ 3 + (p ^ 2 * y0) ^ 3 := by ring
          _ = p ^ 6 * 6080256576 := heq
      rcases sol_base x0 y0 hx0 hx0y0 heq0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · refine ⟨⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, by omega, by ring⟩
        · calc
            p ^ 2 * 228 ≤ p ^ 6 * 228 := Nat.mul_le_mul_right 228 hp6_ge
            _ ≤ p ^ 6 * 6080256576 := Nat.mul_le_mul_left (p ^ 6) (by norm_num)
        · calc
            p ^ 2 * 1824 ≤ p ^ 6 * 1824 := Nat.mul_le_mul_right 1824 hp6_ge
            _ ≤ p ^ 6 * 6080256576 := Nat.mul_le_mul_left (p ^ 6) (by norm_num)
      · refine ⟨⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, by omega, by ring⟩
        · calc
            p ^ 2 * 1026 ≤ p ^ 6 * 1026 := Nat.mul_le_mul_right 1026 hp6_ge
            _ ≤ p ^ 6 * 6080256576 := Nat.mul_le_mul_left (p ^ 6) (by norm_num)
        · calc
            p ^ 2 * 1710 ≤ p ^ 6 * 1710 := Nat.mul_le_mul_right 1710 hp6_ge
            _ ≤ p ^ 6 * 6080256576 := Nat.mul_le_mul_left (p ^ 6) (by norm_num)
  rw [hfilter]
  apply Finset.card_pair
  intro hpair
  have h1 := congrArg Prod.fst hpair
  dsimp at h1
  omega

end OMA.S_oeis_a145552_proof

theorem OMA.solution : type_of% @OMA.S_oeis_a145552.main := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨p, hp_gt, hp_prime, hp3⟩ :=
    OMA.S_oeis_a145552_proof.exists_gt_prime_mod_three_eq_two (max N (4 * 6080256576))
  have hp_gt_N : N < p := lt_of_le_of_lt (le_max_left _ _) hp_gt
  have hp_gt_4m : 4 * 6080256576 < p := lt_of_le_of_lt (le_max_right _ _) hp_gt
  have hp6_ge_p : p ≤ p ^ 6 := Nat.le_self_pow (by norm_num) p
  have hp_bound : 4 * 6080256576 < p ^ 6 := lt_of_lt_of_le hp_gt_4m hp6_ge_p
  refine ⟨p ^ 6 * 6080256576, ⟨⟨p ^ 3 * 77976, by ring⟩, ?_⟩, ?_⟩
  · exact OMA.S_oeis_a145552_proof.r_pow_six_mul_base hp_prime hp3 hp_bound
  · have hlt : p ≤ p ^ 6 * 6080256576 :=
      le_trans hp6_ge_p (Nat.le_mul_of_pos_right _ (by norm_num))
    omega
