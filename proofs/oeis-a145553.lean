import OMAStatements.S_oeis_a145553

namespace OMA.S_oeis_a145553_proof

private lemma exists_prime_dvd_of_mod_three_eq_two :
    ∀ m : ℕ, m % 3 = 2 → ∃ p : ℕ, Nat.Prime p ∧ p ∣ m ∧ p % 3 = 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hp : Nat.Prime m
    · exact ⟨m, hp, dvd_rfl, hm⟩
    · have hm2 : 2 ≤ m := by omega
      let p := m.minFac
      have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
      have hp_dvd : p ∣ m := Nat.minFac_dvd m
      rcases hp_dvd with ⟨q, hq⟩
      have hq_lt : q < m := by
        have hp2 : 2 ≤ p := hp_prime.two_le
        nlinarith
      have hmod : (p * q) % 3 = 2 := by rw [← hq]; exact hm
      rw [Nat.mul_mod] at hmod
      have hp_cases : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
      rcases hp_cases with h0 | h1 | h2
      · rw [h0] at hmod; norm_num at hmod
      · have hq_mod : q % 3 = 2 := by
          have hq_cases : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
          rcases hq_cases with hq0 | hq1 | hq2
          · rw [h1, hq0] at hmod; norm_num at hmod
          · rw [h1, hq1] at hmod; norm_num at hmod
          · exact hq2
        rcases ih q hq_lt hq_mod with ⟨r, hrp, hrd, hrm⟩
        exact ⟨r, hrp, dvd_trans hrd ⟨p, by rw [hq, mul_comm]⟩, hrm⟩
      · exact ⟨p, hp_prime, ⟨q, hq⟩, h2⟩

private lemma exists_prime_gt_mod_three_eq_two (N : ℕ) :
    ∃ p : ℕ, p > N ∧ Nat.Prime p ∧ p % 3 = 2 := by
  let M := max N 2
  have hM2 : 2 ≤ M := le_max_right N 2
  have hfact : 2 ≤ Nat.factorial M := le_trans hM2 (Nat.self_le_factorial M)
  let K := 3 * Nat.factorial M - 1
  have hK_mod : K % 3 = 2 := by omega
  rcases exists_prime_dvd_of_mod_three_eq_two K hK_mod with ⟨p, hp_prime, hp_dvd, hp_mod⟩
  refine ⟨p, ?_, hp_prime, hp_mod⟩
  by_contra hle
  push Not at hle
  have hp_le_M : p ≤ M := le_trans hle (le_max_left N 2)
  have hp_dvd_fact : p ∣ Nat.factorial M := Nat.dvd_factorial hp_prime.pos hp_le_M
  have hp_dvd_3fact : p ∣ 3 * Nat.factorial M := dvd_mul_of_dvd_right hp_dvd_fact 3
  have hp_dvd_one : p ∣ 1 := by
    have hsub : 3 * Nat.factorial M - K = 1 := by omega
    rw [← hsub]
    exact Nat.dvd_sub hp_dvd_3fact hp_dvd
  have : p ≤ 1 := Nat.le_of_dvd (by omega) hp_dvd_one
  have := hp_prime.two_le
  omega

private lemma dvd_both_of_cube_sum {p a b k : ℕ}
    (hp : Nat.Prime p) (hp59 : 59 ≤ p) (hp3 : p % 3 = 2)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hk : 3 ≤ k)
    (hsum : a ^ 3 + b ^ 3 = p ^ k * 77976 ^ 2) :
    p ∣ a ∧ p ∣ b := by
  have hdvd_iff : p ∣ a ↔ p ∣ b := by
    have hpk : p ∣ p ^ k * 77976 ^ 2 :=
      dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
    constructor
    · intro hpa
      have hpa3 : p ∣ a ^ 3 := dvd_pow hpa (by omega)
      have hpb3 : p ∣ b ^ 3 := (Nat.dvd_add_right hpa3).mp (by rw [hsum]; exact hpk)
      exact hp.dvd_of_dvd_pow hpb3
    · intro hpb
      have hpb3 : p ∣ b ^ 3 := dvd_pow hpb (by omega)
      have hpa3 : p ∣ a ^ 3 := (Nat.dvd_add_left hpb3).mp (by rw [hsum]; exact hpk)
      exact hp.dvd_of_dvd_pow hpa3
  by_contra hnot
  have hna : ¬ (p ∣ a) := fun h => hnot ⟨h, hdvd_iff.mp h⟩
  have hnb : ¬ (p ∣ b) := fun h => hnot ⟨hdvd_iff.mpr h, h⟩
  have : Fact p.Prime := ⟨hp⟩
  let e : ℕ := (2 * p - 1) / 3
  have he : 3 * e = 2 * p - 1 := by omega
  have hpow : ∀ u : ZMod p, u ^ (2 * p - 1) = u := by
    intro u
    by_cases hu : u = 0
    · subst hu
      rw [zero_pow (by omega)]
    · have hsplit : 2 * p - 1 = p + (p - 1) := by omega
      rw [hsplit, pow_add, ZMod.pow_card, ZMod.pow_card_sub_one_eq_one hu, mul_one]
  have hsum_mod : (a : ZMod p) ^ 3 + (b : ZMod p) ^ 3 = 0 := by
    have hcast : ((a ^ 3 + b ^ 3 : ℕ) : ZMod p) = ((p ^ k * 77976 ^ 2 : ℕ) : ZMod p) :=
      congrArg Nat.cast hsum
    push_cast at hcast
    rw [ZMod.natCast_self, zero_pow (by omega), zero_mul] at hcast
    exact hcast
  have hcube_eq : (a : ZMod p) ^ 3 = (- (b : ZMod p)) ^ 3 := by
    have h1 : (a : ZMod p) ^ 3 = - ((b : ZMod p) ^ 3) := eq_neg_of_add_eq_zero_left hsum_mod
    rw [h1]
    ring
  have hab_mod : (a : ZMod p) = - (b : ZMod p) := by
    have h1 : ((a : ZMod p) ^ 3) ^ e = ((- (b : ZMod p)) ^ 3) ^ e := congrArg (· ^ e) hcube_eq
    rw [← pow_mul, ← pow_mul, he, hpow, hpow] at h1
    exact h1
  have hquad_ne : (a : ZMod p) ^ 2 - (a : ZMod p) * (b : ZMod p) + (b : ZMod p) ^ 2 ≠ 0 := by
    rw [hab_mod]
    have hring : (- (b : ZMod p)) ^ 2 - (- (b : ZMod p)) * (b : ZMod p) + (b : ZMod p) ^ 2 =
        (3 : ZMod p) * (b : ZMod p) ^ 2 := by ring
    rw [hring]
    have hb0 : (b : ZMod p) ≠ 0 := by
      intro h0
      exact hnb ((ZMod.natCast_eq_zero_iff b p).mp h0)
    have h30 : (3 : ZMod p) ≠ 0 := by
      intro h0
      have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h0
      have : p ≤ 3 := Nat.le_of_dvd (by omega) hd
      omega
    exact mul_ne_zero h30 (pow_ne_zero 2 hb0)
  have hle_ab : a * b ≤ a ^ 2 + b ^ 2 := by nlinarith
  let Q : ℕ := a ^ 2 + b ^ 2 - a * b
  have hQ_cast : (Q : ZMod p) = (a : ZMod p) ^ 2 - (a : ZMod p) * (b : ZMod p) + (b : ZMod p) ^ 2 := by
    dsimp [Q]
    rw [Nat.cast_sub hle_ab]
    push_cast
    ring
  have hp_ndvd_Q : ¬ (p ∣ Q) := by
    intro hd
    have h0 : (Q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff Q p).mpr hd
    rw [hQ_cast] at h0
    exact hquad_ne h0
  have hprod : (a + b) * Q = a ^ 3 + b ^ 3 := by
    dsimp [Q]
    zify [hle_ab]
    ring
  have hpk_dvd_prod : p ^ k ∣ (a + b) * Q := by
    rw [hprod, hsum]
    exact dvd_mul_right _ _
  have hcop : Nat.Coprime (p ^ k) Q := (hp.coprime_iff_not_dvd.mpr hp_ndvd_Q).pow_left k
  have hpk_dvd_sum : p ^ k ∣ a + b := hcop.dvd_of_dvd_mul_right hpk_dvd_prod
  have hle_sum : p ^ k ≤ a + b := Nat.le_of_dvd (by omega) hpk_dvd_sum
  have hineq_z : ((a + b : ℕ) : ℤ) ^ 3 ≤ 4 * ((a ^ 3 + b ^ 3 : ℕ) : ℤ) := by
    push_cast
    have h4 : 4 * ((a : ℤ) ^ 3 + (b : ℤ) ^ 3) - ((a : ℤ) + b) ^ 3 =
        ((a : ℤ) + b) * (3 * ((a : ℤ) - b) ^ 2) := by ring
    have hnonneg : 0 ≤ ((a : ℤ) + b) * (3 * ((a : ℤ) - b) ^ 2) := by positivity
    linarith
  have hineq : (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by exact_mod_cast hineq_z
  have hpk3 : (p ^ k) ^ 3 ≤ 4 * (p ^ k * 77976 ^ 2) := by
    calc (p ^ k) ^ 3 ≤ (a + b) ^ 3 := Nat.pow_le_pow_left hle_sum 3
      _ ≤ 4 * (a ^ 3 + b ^ 3) := hineq
      _ = 4 * (p ^ k * 77976 ^ 2) := by rw [hsum]
  have hpk2 : p ^ k * p ^ (2 * k) ≤ p ^ k * (4 * 77976 ^ 2) := by
    have h1 : (p ^ k) ^ 3 = p ^ k * p ^ (2 * k) := by
      rw [← pow_mul, show k * 3 = k + 2 * k by omega, pow_add]
    linarith
  have hpk_pos : 0 < p ^ k := pow_pos hp.pos k
  have h2k_le : p ^ (2 * k) ≤ 4 * 77976 ^ 2 := Nat.le_of_mul_le_mul_left hpk2 hpk_pos
  have h59_le : 59 ^ 6 ≤ p ^ (2 * k) := by
    calc 59 ^ 6 ≤ p ^ 6 := Nat.pow_le_pow_left hp59 6
      _ ≤ p ^ (2 * k) := Nat.pow_le_pow_right hp.pos (by omega)
  have : (59 : ℕ) ^ 6 ≤ 4 * 77976 ^ 2 := le_trans h59_le h2k_le
  norm_num at this

private lemma dvd_prime_cube_factors {d : ℕ} (hd : d ∣ 2 ^ 6 * 3 ^ 6 * 19 ^ 4) :
    ∃ a ≤ 6, ∃ b ≤ 6, ∃ c ≤ 4, d = 2 ^ a * 3 ^ b * 19 ^ c := by
  have hd' : d ∣ 2 ^ 6 * (3 ^ 6 * 19 ^ 4) := by simpa [mul_assoc] using hd
  rcases Nat.dvd_mul.mp hd' with ⟨d1, d23, hd1, hd23, rfl⟩
  rcases Nat.dvd_mul.mp hd23 with ⟨d2, d3, hd2, hd3, rfl⟩
  rw [Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)] at hd1
  rw [Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)] at hd2
  rw [Nat.dvd_prime_pow (by norm_num : Nat.Prime 19)] at hd3
  rcases hd1 with ⟨a, ha, rfl⟩
  rcases hd2 with ⟨b, hb, rfl⟩
  rcases hd3 with ⟨c, hc, rfl⟩
  exact ⟨a, ha, b, hb, c, hc, by ring⟩

private lemma factor_range {a b c : ℕ} (ha : a ≤ 6) (hb : b ≤ 6) (hc : c ≤ 2)
    (hlo : 1826 ≤ 2 ^ a * 3 ^ b * 19 ^ c) (hhi : 2 ^ a * 3 ^ b * 19 ^ c ≤ 2897) :
    2 ^ a * 3 ^ b * 19 ^ c = 1944 ∨ 2 ^ a * 3 ^ b * 19 ^ c = 2052 ∨
    2 ^ a * 3 ^ b * 19 ^ c = 2166 ∨ 2 ^ a * 3 ^ b * 19 ^ c = 2592 ∨
    2 ^ a * 3 ^ b * 19 ^ c = 2736 ∨ 2 ^ a * 3 ^ b * 19 ^ c = 2888 := by
  have h2a_pos : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by omega)
  have h3b_pos : 1 ≤ 3 ^ b := Nat.one_le_pow b 3 (by omega)
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  · -- c = 0
    have hb4 : 4 ≤ b := by
      by_contra h
      have h3b : 3 ^ b ≤ 27 :=
        le_trans (Nat.pow_le_pow_right (by omega) (show b ≤ 3 by omega)) (by norm_num)
      have h2a : 2 ^ a ≤ 64 :=
        le_trans (Nat.pow_le_pow_right (by omega) ha) (by norm_num)
      have : 2 ^ a * 3 ^ b * 19 ^ 0 ≤ 64 * 27 * 1 := by
        gcongr
        norm_num
      omega
    rcases (by omega : b = 4 ∨ b = 5 ∨ b = 6) with rfl | rfl | rfl
    · rcases (by omega : a ≤ 4 ∨ a = 5 ∨ a = 6) with ha4 | rfl | rfl
      · have h2a : 2 ^ a ≤ 16 := le_trans (Nat.pow_le_pow_right (by omega) ha4) (by norm_num)
        have : 2 ^ a * 3 ^ 4 * 19 ^ 0 ≤ 16 * 81 * 1 := by gcongr <;> norm_num
        omega
      · right; right; right; left; norm_num
      · norm_num at hhi
    · rcases (by omega : a ≤ 2 ∨ a = 3 ∨ 4 ≤ a) with ha2 | rfl | ha4
      · have h2a : 2 ^ a ≤ 4 := le_trans (Nat.pow_le_pow_right (by omega) ha2) (by norm_num)
        have : 2 ^ a * 3 ^ 5 * 19 ^ 0 ≤ 4 * 243 * 1 := by gcongr <;> norm_num
        omega
      · left; norm_num
      · have h2a : 16 ≤ 2 ^ a := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) ha4)
        have : 16 * 243 * 1 ≤ 2 ^ a * 3 ^ 5 * 19 ^ 0 := by gcongr <;> norm_num
        omega
    · rcases (by omega : a ≤ 1 ∨ 2 ≤ a) with ha1 | ha2
      · have h2a : 2 ^ a ≤ 2 := le_trans (Nat.pow_le_pow_right (by omega) ha1) (by norm_num)
        have : 2 ^ a * 3 ^ 6 * 19 ^ 0 ≤ 2 * 729 * 1 := by gcongr <;> norm_num
        omega
      · have h2a : 4 ≤ 2 ^ a := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) ha2)
        have : 4 * 729 * 1 ≤ 2 ^ a * 3 ^ 6 * 19 ^ 0 := by gcongr <;> norm_num
        omega
  · -- c = 1
    have hb4 : b ≤ 4 := by
      by_contra h
      have h3b : 243 ≤ 3 ^ b :=
        le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) (show 5 ≤ b by omega))
      have : 1 * 243 * 19 ≤ 2 ^ a * 3 ^ b * 19 ^ 1 := by gcongr <;> norm_num
      omega
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4) with rfl | rfl | rfl | rfl | rfl
    · have h2a : 2 ^ a ≤ 64 := le_trans (Nat.pow_le_pow_right (by omega) ha) (by norm_num)
      have : 2 ^ a * 3 ^ 0 * 19 ^ 1 ≤ 64 * 1 * 19 := by gcongr <;> norm_num
      omega
    · rcases (by omega : a ≤ 5 ∨ a = 6) with ha5 | rfl
      · have h2a : 2 ^ a ≤ 32 := le_trans (Nat.pow_le_pow_right (by omega) ha5) (by norm_num)
        have : 2 ^ a * 3 ^ 1 * 19 ^ 1 ≤ 32 * 3 * 19 := by gcongr <;> norm_num
        omega
      · norm_num at hhi
    · rcases (by omega : a ≤ 3 ∨ a = 4 ∨ 5 ≤ a) with ha3 | rfl | ha5
      · have h2a : 2 ^ a ≤ 8 := le_trans (Nat.pow_le_pow_right (by omega) ha3) (by norm_num)
        have : 2 ^ a * 3 ^ 2 * 19 ^ 1 ≤ 8 * 9 * 19 := by gcongr <;> norm_num
        omega
      · right; right; right; right; left; norm_num
      · have h2a : 32 ≤ 2 ^ a := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) ha5)
        have : 32 * 9 * 19 ≤ 2 ^ a * 3 ^ 2 * 19 ^ 1 := by gcongr <;> norm_num
        omega
    · rcases (by omega : a ≤ 1 ∨ a = 2 ∨ 3 ≤ a) with ha1 | rfl | ha3
      · have h2a : 2 ^ a ≤ 2 := le_trans (Nat.pow_le_pow_right (by omega) ha1) (by norm_num)
        have : 2 ^ a * 3 ^ 3 * 19 ^ 1 ≤ 2 * 27 * 19 := by gcongr <;> norm_num
        omega
      · right; left; norm_num
      · have h2a : 8 ≤ 2 ^ a := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) ha3)
        have : 8 * 27 * 19 ≤ 2 ^ a * 3 ^ 3 * 19 ^ 1 := by gcongr <;> norm_num
        omega
    · rcases (by omega : a = 0 ∨ 1 ≤ a) with rfl | ha1
      · norm_num at hlo
      · have h2a : 2 ≤ 2 ^ a := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) ha1)
        have : 2 * 81 * 19 ≤ 2 ^ a * 3 ^ 4 * 19 ^ 1 := by gcongr <;> norm_num
        omega
  · -- c = 2
    have hb1 : b ≤ 1 := by
      by_contra h
      have h3b : 9 ≤ 3 ^ b :=
        le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) (show 2 ≤ b by omega))
      have : 1 * 9 * 361 ≤ 2 ^ a * 3 ^ b * 19 ^ 2 := by gcongr <;> norm_num
      omega
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · rcases (by omega : a ≤ 2 ∨ a = 3 ∨ 4 ≤ a) with ha2 | rfl | ha4
      · have h2a : 2 ^ a ≤ 4 := le_trans (Nat.pow_le_pow_right (by omega) ha2) (by norm_num)
        have : 2 ^ a * 3 ^ 0 * 19 ^ 2 ≤ 4 * 1 * 361 := by gcongr <;> norm_num
        omega
      · right; right; right; right; right; norm_num
      · have h2a : 16 ≤ 2 ^ a := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) ha4)
        have : 16 * 1 * 361 ≤ 2 ^ a * 3 ^ 0 * 19 ^ 2 := by gcongr <;> norm_num
        omega
    · rcases (by omega : a = 0 ∨ a = 1 ∨ 2 ≤ a) with rfl | rfl | ha2
      · norm_num at hlo
      · right; right; left; norm_num
      · have h2a : 4 ≤ 2 ^ a := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) ha2)
        have : 4 * 3 * 361 ≤ 2 ^ a * 3 ^ 1 * 19 ^ 2 := by gcongr <;> norm_num
        omega

private lemma base_solutions {x y : ℕ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hsum : x ^ 3 + y ^ 3 = 77976 ^ 2) :
    (x = 228 ∧ y = 1824) ∨ (x = 1026 ∧ y = 1710) := by
  let d := x + y
  have hd_dvd : d ∣ 2 ^ 6 * 3 ^ 6 * 19 ^ 4 := by
    have hdiv_z : (d : ℤ) ∣ ((77976 ^ 2 : ℕ) : ℤ) := by
      refine ⟨(x : ℤ) ^ 2 - (x : ℤ) * (y : ℤ) + (y : ℤ) ^ 2, ?_⟩
      have hcast : ((x ^ 3 + y ^ 3 : ℕ) : ℤ) = ((77976 ^ 2 : ℕ) : ℤ) := congrArg Nat.cast hsum
      push_cast at hcast
      calc ((77976 ^ 2 : ℕ) : ℤ) = (x : ℤ) ^ 3 + (y : ℤ) ^ 3 := by
            push_cast; exact hcast.symm
        _ = (d : ℤ) * ((x : ℤ) ^ 2 - (x : ℤ) * (y : ℤ) + (y : ℤ) ^ 2) := by
            dsimp [d]; push_cast; ring
    have hdiv_n : d ∣ 77976 ^ 2 := Int.ofNat_dvd.mp hdiv_z
    simpa [show (77976 : ℕ) ^ 2 = 2 ^ 6 * 3 ^ 6 * 19 ^ 4 by norm_num] using hdiv_n
  have hd_lo : 1826 ≤ d := by
    by_contra h
    have hle : d ≤ 1825 := by omega
    have hcube : x ^ 3 + y ^ 3 < d ^ 3 := by
      have hpos : 0 < 3 * x * y * (x + y) := by
        have hy1 : 1 ≤ y := le_trans hx hxy
        positivity
      calc x ^ 3 + y ^ 3 < x ^ 3 + y ^ 3 + 3 * x * y * (x + y) := by omega
        _ = d ^ 3 := by dsimp [d]; ring
    have h1825 : d ^ 3 ≤ 1825 ^ 3 := Nat.pow_le_pow_left hle 3
    norm_num [hsum] at hcube h1825
    omega
  have hd_hi : d ≤ 2897 := by
    by_contra h
    have hge : 2898 ≤ d := by omega
    have h4 : d ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
      have hz : ((d : ℕ) : ℤ) ^ 3 ≤ 4 * ((x ^ 3 + y ^ 3 : ℕ) : ℤ) := by
        dsimp [d]
        push_cast
        have hdiff : 4 * ((x : ℤ) ^ 3 + y ^ 3) - ((x : ℤ) + y) ^ 3 =
            ((x : ℤ) + y) * (3 * ((y : ℤ) - x) ^ 2) := by ring
        have hnn : 0 ≤ ((x : ℤ) + y) * (3 * ((y : ℤ) - x) ^ 2) := by positivity
        linarith
      exact_mod_cast hz
    have h2898 : 2898 ^ 3 ≤ d ^ 3 := Nat.pow_le_pow_left hge 3
    rw [hsum] at h4
    norm_num at h4 h2898
    omega
  rcases dvd_prime_cube_factors hd_dvd with ⟨a, ha, b, hb, c, hc, hd_eq⟩
  have hc2 : c ≤ 2 := by
    by_contra hc3
    have hc_ge : 3 ≤ c := by omega
    have h19 : 19 ^ 3 ≤ 19 ^ c := Nat.pow_le_pow_right (by omega) hc_ge
    have h1 : 0 < 2 ^ a * 3 ^ b := by positivity
    have : 6859 ≤ d := by
      calc 6859 = 1 * 19 ^ 3 := by norm_num
        _ ≤ (2 ^ a * 3 ^ b) * 19 ^ c := Nat.mul_le_mul h1 h19
        _ = d := hd_eq.symm
    omega
  have hd_cases : d = 1944 ∨ d = 2052 ∨ d = 2166 ∨ d = 2592 ∨ d = 2736 ∨ d = 2888 := by
    rw [hd_eq] at hd_lo hd_hi ⊢
    exact factor_range ha hb hc2 hd_lo hd_hi
  have hrel : d * (d ^ 2 + 3 * (y - x) ^ 2) = 4 * 77976 ^ 2 := by
    have hcast : (x : ℤ) ^ 3 + (y : ℤ) ^ 3 = (77976 : ℤ) ^ 2 := by exact_mod_cast hsum
    have hz : (d : ℤ) * ((d : ℤ) ^ 2 + 3 * ((y : ℤ) - x) ^ 2) = 4 * (77976 : ℤ) ^ 2 := by
      dsimp [d]
      push_cast
      linear_combination 4 * hcast
    zify [hxy]
    exact hz
  rcases hd_cases with h | h | h | h | h | h
  · -- d = 1944
    rw [h] at hrel
    have hsq : (y - x) ^ 2 = 2910560 := by omega
    exfalso
    by_cases hle : y - x ≤ 1706
    · have : (y - x) ^ 2 ≤ 1706 ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    · have : 1707 ^ 2 ≤ (y - x) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
  · -- d = 2052
    rw [h] at hrel
    have hsq : (y - x) ^ 2 = 1596 ^ 2 := by omega
    have hdiff : y - x = 1596 := by nlinarith
    left
    omega
  · -- d = 2166
    rw [h] at hrel
    have hsq : (y - x) ^ 2 = 2178996 := by omega
    exfalso
    by_cases hle : y - x ≤ 1476
    · have : (y - x) ^ 2 ≤ 1476 ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    · have : 1477 ^ 2 ≤ (y - x) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
  · -- d = 2592
    rw [h] at hrel
    have hsq : (y - x) ^ 2 = 888216 := by omega
    exfalso
    by_cases hle : y - x ≤ 942
    · have : (y - x) ^ 2 ≤ 942 ^ 2 := Nat.pow_le_pow_left hle 2
      omega
    · have : 943 ^ 2 ≤ (y - x) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
  · -- d = 2736
    rw [h] at hrel
    have hsq : (y - x) ^ 2 = 684 ^ 2 := by omega
    have hdiff : y - x = 684 := by nlinarith
    right
    omega
  · -- d = 2888
    rw [h] at hrel
    omega

private lemma r_base : OMA.S_oeis_a145553.r (77976 ^ 2) = 2 := by
  unfold OMA.S_oeis_a145553.r
  have heq :
      (Finset.Icc 1 (77976 ^ 2) ×ˢ Finset.Icc 1 (77976 ^ 2)).filter
          (fun t => t.1 ≤ t.2 ∧ t.1 ^ 3 + t.2 ^ 3 = 77976 ^ 2) =
        {(228, 1824), (1026, 1710)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hx1, _⟩, ⟨hy1, _⟩⟩, hxy, hsum⟩
      exact base_solutions hx1 hxy hsum
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
  rw [heq, Finset.card_pair]
  decide

private lemma r_prime_mul {p : ℕ} (hp : Nat.Prime p) (hp59 : 59 ≤ p) (hp3 : p % 3 = 2) :
    OMA.S_oeis_a145553.r ((77976 * p ^ 3) ^ 2) = 2 := by
  conv_rhs => rw [← r_base]
  unfold OMA.S_oeis_a145553.r
  let f : ℕ × ℕ → ℕ × ℕ := fun t => (p ^ 2 * t.1, p ^ 2 * t.2)
  have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
  have hinj : Function.Injective f := by
    rintro ⟨x1, y1⟩ ⟨x2, y2⟩ h
    simp only [f, Prod.mk.injEq] at h
    ext <;> exact Nat.eq_of_mul_eq_mul_left hp2_pos (by tauto)
  have heq :
      (Finset.Icc 1 ((77976 * p ^ 3) ^ 2) ×ˢ Finset.Icc 1 ((77976 * p ^ 3) ^ 2)).filter
          (fun t => t.1 ≤ t.2 ∧ t.1 ^ 3 + t.2 ^ 3 = (77976 * p ^ 3) ^ 2) =
        ((Finset.Icc 1 (77976 ^ 2) ×ˢ Finset.Icc 1 (77976 ^ 2)).filter
          (fun t => t.1 ≤ t.2 ∧ t.1 ^ 3 + t.2 ^ 3 = 77976 ^ 2)).image f := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_image,
      Prod.exists]
    constructor
    · rintro ⟨⟨⟨hx1, _⟩, ⟨hy1, _⟩⟩, hxy, hsum⟩
      have hsum' : x ^ 3 + y ^ 3 = p ^ 6 * 77976 ^ 2 := by
        rw [hsum]; ring
      obtain ⟨hpx, hpy⟩ := dvd_both_of_cube_sum hp hp59 hp3 hx1 hy1 (by omega) hsum'
      rcases hpx with ⟨x1, rfl⟩
      rcases hpy with ⟨y1, rfl⟩
      have hx1_pos : 1 ≤ x1 := by
        by_contra h; have : x1 = 0 := by omega
        subst this; simp at hx1
      have hy1_pos : 1 ≤ y1 := by
        by_contra h; have : y1 = 0 := by omega
        subst this; simp at hy1
      have hsum1 : x1 ^ 3 + y1 ^ 3 = p ^ 3 * 77976 ^ 2 := by
        have hp3_pos : 0 < p ^ 3 := pow_pos hp.pos 3
        apply Nat.eq_of_mul_eq_mul_left hp3_pos
        calc p ^ 3 * (x1 ^ 3 + y1 ^ 3) = (p * x1) ^ 3 + (p * y1) ^ 3 := by ring
          _ = p ^ 6 * 77976 ^ 2 := hsum'
          _ = p ^ 3 * (p ^ 3 * 77976 ^ 2) := by ring
      obtain ⟨hpx1, hpy1⟩ := dvd_both_of_cube_sum hp hp59 hp3 hx1_pos hy1_pos (by omega) hsum1
      rcases hpx1 with ⟨x', rfl⟩
      rcases hpy1 with ⟨y', rfl⟩
      have hx'_pos : 1 ≤ x' := by
        by_contra h; have : x' = 0 := by omega
        subst this; simp at hx1_pos
      have hy'_pos : 1 ≤ y' := by
        by_contra h; have : y' = 0 := by omega
        subst this; simp at hy1_pos
      have hsum'2 : x' ^ 3 + y' ^ 3 = 77976 ^ 2 := by
        have hp3_pos : 0 < p ^ 3 := pow_pos hp.pos 3
        apply Nat.eq_of_mul_eq_mul_left hp3_pos
        calc p ^ 3 * (x' ^ 3 + y' ^ 3) = (p * x') ^ 3 + (p * y') ^ 3 := by ring
          _ = p ^ 3 * 77976 ^ 2 := hsum1
      have hx'_le_y' : x' ≤ y' := by
        nlinarith [hp2_pos]
      have hx'_le_M : x' ≤ 77976 ^ 2 := by
        have h1 : x' ≤ x' ^ 3 := Nat.le_self_pow (by omega) x'
        have h2 : x' ^ 3 ≤ x' ^ 3 + y' ^ 3 := Nat.le_add_right _ _
        omega
      have hy'_le_M : y' ≤ 77976 ^ 2 := by
        have h1 : y' ≤ y' ^ 3 := Nat.le_self_pow (by omega) y'
        have h2 : y' ^ 3 ≤ x' ^ 3 + y' ^ 3 := Nat.le_add_left _ _
        omega
      refine ⟨x', y', ⟨⟨⟨hx'_pos, hx'_le_M⟩, ⟨hy'_pos, hy'_le_M⟩⟩, hx'_le_y', hsum'2⟩, ?_⟩
      simp only [f, Prod.mk.injEq]
      constructor <;> ring
    · rintro ⟨x', y', ⟨⟨⟨hx1, hxM⟩, ⟨hy1, hyM⟩⟩, hxy, hsum'⟩, hfeq⟩
      simp only [f, Prod.mk.injEq] at hfeq
      rcases hfeq with ⟨rfl, rfl⟩
      have hsum : (p ^ 2 * x') ^ 3 + (p ^ 2 * y') ^ 3 = (77976 * p ^ 3) ^ 2 := by
        calc (p ^ 2 * x') ^ 3 + (p ^ 2 * y') ^ 3 = p ^ 6 * (x' ^ 3 + y' ^ 3) := by ring
          _ = p ^ 6 * 77976 ^ 2 := by rw [hsum']
          _ = (77976 * p ^ 3) ^ 2 := by ring
      have hx_pos : 1 ≤ p ^ 2 * x' := Nat.mul_pos hp2_pos hx1
      have hy_pos : 1 ≤ p ^ 2 * y' := Nat.mul_pos hp2_pos hy1
      have hxy' : p ^ 2 * x' ≤ p ^ 2 * y' := Nat.mul_le_mul_left (p ^ 2) hxy
      have hle_M : ∀ u : ℕ, u ≤ u ^ 3 := fun u => by
        rcases eq_or_ne u 0 with rfl | hu
        · simp
        · exact Nat.le_self_pow (by omega) u
      have hx_le : p ^ 2 * x' ≤ (77976 * p ^ 3) ^ 2 := by
        calc p ^ 2 * x' ≤ (p ^ 2 * x') ^ 3 := hle_M _
          _ ≤ (p ^ 2 * x') ^ 3 + (p ^ 2 * y') ^ 3 := Nat.le_add_right _ _
          _ = (77976 * p ^ 3) ^ 2 := hsum
      have hy_le : p ^ 2 * y' ≤ (77976 * p ^ 3) ^ 2 := by
        calc p ^ 2 * y' ≤ (p ^ 2 * y') ^ 3 := hle_M _
          _ ≤ (p ^ 2 * x') ^ 3 + (p ^ 2 * y') ^ 3 := Nat.le_add_left _ _
          _ = (77976 * p ^ 3) ^ 2 := hsum
      exact ⟨⟨⟨hx_pos, hx_le⟩, ⟨hy_pos, hy_le⟩⟩, hxy', hsum⟩
  rw [heq, Finset.card_image_of_injective _ hinj]

end OMA.S_oeis_a145553_proof

theorem OMA.solution : type_of% @OMA.S_oeis_a145553.main := by
  change {n : ℕ | OMA.S_oeis_a145553.r (n ^ 2) = 2}.Infinite
  rw [Set.infinite_iff_exists_gt]
  intro B
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    OMA.S_oeis_a145553_proof.exists_prime_gt_mod_three_eq_two (max B 59)
  have hp59 : 59 ≤ p := le_trans (le_max_right B 59) (le_of_lt hp_gt)
  have hpB : B < p := lt_of_le_of_lt (le_max_left B 59) hp_gt
  have hp_pos : 1 ≤ p ^ 3 := Nat.one_le_pow 3 p hp_prime.pos
  refine ⟨77976 * p ^ 3, ?_, ?_⟩
  · exact OMA.S_oeis_a145553_proof.r_prime_mul hp_prime hp59 hp_mod
  · change B < 77976 * p ^ 3
    have hpos_p : 0 < p := hp_prime.pos
    calc B < p := hpB
      _ ≤ p * (77976 * p ^ 2) := Nat.le_mul_of_pos_right p (by positivity)
      _ = 77976 * p ^ 3 := by ring
