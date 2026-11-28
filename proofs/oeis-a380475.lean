import OMAStatements.S_oeis_a380475

namespace OeisA380475

open Finset BigOperators

-- ============================================================================
-- Section 1: Exact Enumeration of the First 30 Primes and Primorial Places
-- ============================================================================

private lemma nth_prime_step {k p q : ℕ}
    (hk : Nat.nth Nat.Prime k = p)
    (hpq : p < q)
    (hq : Nat.Prime q)
    (hbetween : ∀ x, p < x → x < q → ¬ Nat.Prime x) :
    Nat.nth Nat.Prime (k + 1) = q := by
  have hp : Nat.Prime p := hk ▸ Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k
  have hcnt_p : Nat.count Nat.Prime p = k := by
    rw [← hk]
    exact Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime k
  have hfilt : (range q).filter Nat.Prime = insert p ((range p).filter Nat.Prime) := by
    ext x
    simp only [mem_filter, mem_range, mem_insert]
    constructor
    · rintro ⟨hxq, hxp⟩
      by_cases hlt : x < p
      · exact Or.inr ⟨hlt, hxp⟩
      · by_cases heq : x = p
        · exact Or.inl heq
        · exact absurd hxp (hbetween x (by omega) hxq)
    · rintro (rfl | ⟨hxp, hprime⟩)
      · exact ⟨hpq, hp⟩
      · exact ⟨lt_trans hxp hpq, hprime⟩
  have hnotmem : p ∉ (range p).filter Nat.Prime := by simp
  have hcnt_q : Nat.count Nat.Prime q = k + 1 := by
    rw [Nat.count_eq_card_filter_range, hfilt, card_insert_of_notMem hnotmem,
      ← Nat.count_eq_card_filter_range, hcnt_p]
  rw [← hcnt_q]
  exact Nat.nth_count hq

private lemma q0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
private lemma q1 : Nat.nth Nat.Prime 1 = 3 :=
  nth_prime_step q0 (by omega) (by norm_num) (by intro x h1 h2; omega)
private lemma q2 : Nat.nth Nat.Prime 2 = 5 :=
  nth_prime_step q1 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x; norm_num)
private lemma q3 : Nat.nth Nat.Prime 3 = 7 :=
  nth_prime_step q2 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x; norm_num)
private lemma q4 : Nat.nth Nat.Prime 4 = 11 :=
  nth_prime_step q3 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q5 : Nat.nth Nat.Prime 5 = 13 :=
  nth_prime_step q4 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x; norm_num)
private lemma q6 : Nat.nth Nat.Prime 6 = 17 :=
  nth_prime_step q5 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q7 : Nat.nth Nat.Prime 7 = 19 :=
  nth_prime_step q6 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x; norm_num)
private lemma q8 : Nat.nth Nat.Prime 8 = 23 :=
  nth_prime_step q7 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q9 : Nat.nth Nat.Prime 9 = 29 :=
  nth_prime_step q8 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q10 : Nat.nth Nat.Prime 10 = 31 :=
  nth_prime_step q9 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x; norm_num)
private lemma q11 : Nat.nth Nat.Prime 11 = 37 :=
  nth_prime_step q10 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q12 : Nat.nth Nat.Prime 12 = 41 :=
  nth_prime_step q11 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q13 : Nat.nth Nat.Prime 13 = 43 :=
  nth_prime_step q12 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x; norm_num)
private lemma q14 : Nat.nth Nat.Prime 14 = 47 :=
  nth_prime_step q13 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q15 : Nat.nth Nat.Prime 15 = 53 :=
  nth_prime_step q14 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q16 : Nat.nth Nat.Prime 16 = 59 :=
  nth_prime_step q15 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q17 : Nat.nth Nat.Prime 17 = 61 :=
  nth_prime_step q16 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x; norm_num)
private lemma q18 : Nat.nth Nat.Prime 18 = 67 :=
  nth_prime_step q17 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q19 : Nat.nth Nat.Prime 19 = 71 :=
  nth_prime_step q18 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q20 : Nat.nth Nat.Prime 20 = 73 :=
  nth_prime_step q19 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x; norm_num)
private lemma q21 : Nat.nth Nat.Prime 21 = 79 :=
  nth_prime_step q20 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q22 : Nat.nth Nat.Prime 22 = 83 :=
  nth_prime_step q21 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q23 : Nat.nth Nat.Prime 23 = 89 :=
  nth_prime_step q22 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q24 : Nat.nth Nat.Prime 24 = 97 :=
  nth_prime_step q23 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q25 : Nat.nth Nat.Prime 25 = 101 :=
  nth_prime_step q24 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q26 : Nat.nth Nat.Prime 26 = 103 :=
  nth_prime_step q25 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x; norm_num)
private lemma q27 : Nat.nth Nat.Prime 27 = 107 :=
  nth_prime_step q26 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)
private lemma q28 : Nat.nth Nat.Prime 28 = 109 :=
  nth_prime_step q27 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x; norm_num)
private lemma q29 : Nat.nth Nat.Prime 29 = 113 :=
  nth_prime_step q28 (by omega) (by norm_num) (by intro x h1 h2; interval_cases x <;> norm_num)

private lemma place_succ (j : ℕ) :
    OMA.S_oeis_a380475.place (j + 1) = OMA.S_oeis_a380475.place j * Nat.nth Nat.Prime j := by
  unfold OMA.S_oeis_a380475.place
  exact Finset.prod_range_succ (Nat.nth Nat.Prime) j

private lemma place_mono {a b : ℕ} (hab : a ≤ b) :
    OMA.S_oeis_a380475.place a ≤ OMA.S_oeis_a380475.place b := by
  induction hab with
  | refl => exact le_rfl
  | @step m _ ih =>
    rw [place_succ]
    have hq : 1 ≤ Nat.nth Nat.Prime m :=
      (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime m).one_le
    exact le_trans ih (Nat.le_mul_of_pos_right _ (by omega))

private lemma place0 : OMA.S_oeis_a380475.place 0 = 1 := by
  unfold OMA.S_oeis_a380475.place; simp
private lemma place1 : OMA.S_oeis_a380475.place 1 = 2 := by
  rw [place_succ, place0, q0]
private lemma place2 : OMA.S_oeis_a380475.place 2 = 6 := by
  rw [place_succ, place1, q1]
private lemma place3 : OMA.S_oeis_a380475.place 3 = 30 := by
  rw [place_succ, place2, q2]
private lemma place4 : OMA.S_oeis_a380475.place 4 = 210 := by
  rw [place_succ, place3, q3]
private lemma place5 : OMA.S_oeis_a380475.place 5 = 2310 := by
  rw [place_succ, place4, q4]
private lemma place6 : OMA.S_oeis_a380475.place 6 = 30030 := by
  rw [place_succ, place5, q5]
private lemma place7 : OMA.S_oeis_a380475.place 7 = 510510 := by
  rw [place_succ, place6, q6]
private lemma place8 : OMA.S_oeis_a380475.place 8 = 9699690 := by
  rw [place_succ, place7, q7]
private lemma place9 : OMA.S_oeis_a380475.place 9 = 223092870 := by
  rw [place_succ, place8, q8]
private lemma place10 : OMA.S_oeis_a380475.place 10 = 6469693230 := by
  rw [place_succ, place9, q9]
private lemma place11 : OMA.S_oeis_a380475.place 11 = 200560490130 := by
  rw [place_succ, place10, q10]
private lemma place12 : OMA.S_oeis_a380475.place 12 = 7420738134810 := by
  rw [place_succ, place11, q11]
private lemma place13 : OMA.S_oeis_a380475.place 13 = 304250263527210 := by
  rw [place_succ, place12, q12]
private lemma place14 : OMA.S_oeis_a380475.place 14 = 13082761331670030 := by
  rw [place_succ, place13, q13]
private lemma place15 : OMA.S_oeis_a380475.place 15 = 614889782588491410 := by
  rw [place_succ, place14, q14]
private lemma place16 : OMA.S_oeis_a380475.place 16 = 32589158477190044730 := by
  rw [place_succ, place15, q15]
private lemma place17 : OMA.S_oeis_a380475.place 17 = 1922760350154212639070 := by
  rw [place_succ, place16, q16]
private lemma place18 : OMA.S_oeis_a380475.place 18 = 117288381359406970983270 := by
  rw [place_succ, place17, q17]
private lemma place19 : OMA.S_oeis_a380475.place 19 = 7858321551080267055879090 := by
  rw [place_succ, place18, q18]
private lemma place20 : OMA.S_oeis_a380475.place 20 = 557940830126698960967415390 := by
  rw [place_succ, place19, q19]
private lemma place21 : OMA.S_oeis_a380475.place 21 = 40729680599249024150621323470 := by
  rw [place_succ, place20, q20]
private lemma place22 : OMA.S_oeis_a380475.place 22 = 3217644767340672907899084554130 := by
  rw [place_succ, place21, q21]
private lemma place23 : OMA.S_oeis_a380475.place 23 = 267064515689275851355624017992790 := by
  rw [place_succ, place22, q22]
private lemma place24 : OMA.S_oeis_a380475.place 24 = 23768741896345550770650537601358310 := by
  rw [place_succ, place23, q23]
private lemma place25 : OMA.S_oeis_a380475.place 25 = 2305567963945518424753102147331756070 := by
  rw [place_succ, place24, q24]
private lemma place26 : OMA.S_oeis_a380475.place 26 = 232862364358497360900063316880507363070 := by
  rw [place_succ, place25, q25]
private lemma place27 : OMA.S_oeis_a380475.place 27 = 23984823528925228172706521638692258396210 := by
  rw [place_succ, place26, q26]
private lemma place28 : OMA.S_oeis_a380475.place 28 = 2566376117594999414479597815340071648394470 := by
  rw [place_succ, place27, q27]
private lemma place29 : OMA.S_oeis_a380475.place 29 = 279734996817854936178276161872067809674997230 := by
  rw [place_succ, place28, q28]
private lemma place30 : OMA.S_oeis_a380475.place 30 = 31610054640417607788145206291543662493274686990 := by
  rw [place_succ, place29, q29]

-- ============================================================================
-- Section 2: Structural Binary Modular Exponentiation and Pocklington Criterion
-- ============================================================================

private def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m => 1 % m
  | fuel + 1, a, e, m =>
    if e = 0 then 1 % m
    else
      let half := powModAux fuel a (e / 2) m
      let sq := (half * half) % m
      if e % 2 = 0 then sq else (sq * a) % m

private lemma powModAux_eq : ∀ (fuel a e m : ℕ), e < 2 ^ fuel →
    powModAux fuel a e m = a ^ e % m
  | 0, a, e, m, h => by
    have he : e = 0 := by simpa using h
    subst he; rfl
  | fuel + 1, a, e, m, h => by
    unfold powModAux
    split_ifs with he0 heven
    · subst he0; simp
    · dsimp only
      have hlt : e / 2 < 2 ^ fuel := by
        rw [pow_succ'] at h; omega
      rw [powModAux_eq fuel a (e / 2) m hlt]
      have hsq : (a ^ (e / 2) % m * (a ^ (e / 2) % m)) % m = a ^ (2 * (e / 2)) % m := by
        rw [← Nat.mul_mod, ← pow_add, show e / 2 + e / 2 = 2 * (e / 2) by ring]
      rw [hsq, show 2 * (e / 2) = e by omega]
    · dsimp only
      have hlt : e / 2 < 2 ^ fuel := by
        rw [pow_succ'] at h; omega
      rw [powModAux_eq fuel a (e / 2) m hlt]
      have hsq : (a ^ (e / 2) % m * (a ^ (e / 2) % m)) % m = a ^ (2 * (e / 2)) % m := by
        rw [← Nat.mul_mod, ← pow_add, show e / 2 + e / 2 = 2 * (e / 2) by ring]
      rw [hsq, Nat.mod_mul_mod, ← pow_succ, show 2 * (e / 2) + 1 = e by omega]

private def evalPow65536 (b0 b1 b2 b3 b4 b5 b6 e m : ℕ) : ℕ :=
  let r0 := powModAux 16 b0 (e % 65536) m
  let r1 := powModAux 16 b1 ((e / 65536) % 65536) m
  let r2 := powModAux 16 b2 ((e / 65536 ^ 2) % 65536) m
  let r3 := powModAux 16 b3 ((e / 65536 ^ 3) % 65536) m
  let r4 := powModAux 16 b4 ((e / 65536 ^ 4) % 65536) m
  let r5 := powModAux 16 b5 ((e / 65536 ^ 5) % 65536) m
  let r6 := powModAux 16 b6 ((e / 65536 ^ 6) % 65536) m
  ((((((r0 * r1 % m) * r2 % m) * r3 % m) * r4 % m) * r5 % m) * r6) % m

private lemma pow_mod_base_pow {a m r1 r2 B1 B2 : ℕ}
    (h1 : a ^ B1 % m = r1) (h2 : r1 ^ B2 % m = r2) :
    a ^ (B1 * B2) % m = r2 := by
  rw [pow_mul, Nat.pow_mod, h1, h2]

private lemma evalPow65536_eq {a m b0 b1 b2 b3 b4 b5 b6 e : ℕ}
    (h0 : a ^ 1 % m = b0)
    (h1 : b0 ^ 65536 % m = b1)
    (h2 : b1 ^ 65536 % m = b2)
    (h3 : b2 ^ 65536 % m = b3)
    (h4 : b3 ^ 65536 % m = b4)
    (h5 : b4 ^ 65536 % m = b5)
    (h6 : b5 ^ 65536 % m = b6)
    (he : e < 65536 ^ 7) :
    a ^ e % m = evalPow65536 b0 b1 b2 b3 b4 b5 b6 e m := by
  have ha1 : a ^ 65536 % m = b1 := by
    rw [show (65536 : ℕ) = 1 * 65536 by norm_num]; exact pow_mod_base_pow h0 h1
  have ha2 : a ^ (65536 ^ 2) % m = b2 := by
    rw [show (65536 : ℕ) ^ 2 = 65536 * 65536 by norm_num]; exact pow_mod_base_pow ha1 h2
  have ha3 : a ^ (65536 ^ 3) % m = b3 := by
    rw [show (65536 : ℕ) ^ 3 = 65536 ^ 2 * 65536 by norm_num]; exact pow_mod_base_pow ha2 h3
  have ha4 : a ^ (65536 ^ 4) % m = b4 := by
    rw [show (65536 : ℕ) ^ 4 = 65536 ^ 3 * 65536 by norm_num]; exact pow_mod_base_pow ha3 h4
  have ha5 : a ^ (65536 ^ 5) % m = b5 := by
    rw [show (65536 : ℕ) ^ 5 = 65536 ^ 4 * 65536 by norm_num]; exact pow_mod_base_pow ha4 h5
  have ha6 : a ^ (65536 ^ 6) % m = b6 := by
    rw [show (65536 : ℕ) ^ 6 = 65536 ^ 5 * 65536 by norm_num]; exact pow_mod_base_pow ha5 h6
  set d0 := e % 65536
  set d1 := (e / 65536) % 65536
  set d2 := (e / 65536 ^ 2) % 65536
  set d3 := (e / 65536 ^ 3) % 65536
  set d4 := (e / 65536 ^ 4) % 65536
  set d5 := (e / 65536 ^ 5) % 65536
  set d6 := (e / 65536 ^ 6) % 65536
  have hexp : e = d0 + 65536 * d1 + 65536 ^ 2 * d2 + 65536 ^ 3 * d3 +
      65536 ^ 4 * d4 + 65536 ^ 5 * d5 + 65536 ^ 6 * d6 := by
    have hdiv0 := Nat.div_add_mod e 65536
    have hdiv1 := Nat.div_add_mod (e / 65536) 65536
    have hdiv2 := Nat.div_add_mod (e / 65536 ^ 2) 65536
    have hdiv3 := Nat.div_add_mod (e / 65536 ^ 3) 65536
    have hdiv4 := Nat.div_add_mod (e / 65536 ^ 4) 65536
    have hdiv5 := Nat.div_add_mod (e / 65536 ^ 5) 65536
    have hdiv6 := Nat.div_add_mod (e / 65536 ^ 6) 65536
    have hs1 : (e / 65536) / 65536 = e / 65536 ^ 2 := by rw [Nat.div_div_eq_div_mul]; rfl
    have hs2 : (e / 65536 ^ 2) / 65536 = e / 65536 ^ 3 := by rw [Nat.div_div_eq_div_mul]; rfl
    have hs3 : (e / 65536 ^ 3) / 65536 = e / 65536 ^ 4 := by rw [Nat.div_div_eq_div_mul]; rfl
    have hs4 : (e / 65536 ^ 4) / 65536 = e / 65536 ^ 5 := by rw [Nat.div_div_eq_div_mul]; rfl
    have hs5 : (e / 65536 ^ 5) / 65536 = e / 65536 ^ 6 := by rw [Nat.div_div_eq_div_mul]; rfl
    have hs6 : (e / 65536 ^ 6) / 65536 = e / 65536 ^ 7 := by rw [Nat.div_div_eq_div_mul]; rfl
    have htop : e / 65536 ^ 7 = 0 := Nat.div_eq_of_lt he
    rw [hs1] at hdiv1; rw [hs2] at hdiv2; rw [hs3] at hdiv3
    rw [hs4] at hdiv4; rw [hs5] at hdiv5; rw [hs6, htop] at hdiv6
    have hd6 : e / 65536 ^ 6 = d6 := by omega
    have hd5 : e / 65536 ^ 5 = 65536 * d6 + d5 := by omega
    have hd4 : e / 65536 ^ 4 = 65536 * (65536 * d6 + d5) + d4 := by omega
    have hd3 : e / 65536 ^ 3 = 65536 * (65536 * (65536 * d6 + d5) + d4) + d3 := by omega
    have hd2 : e / 65536 ^ 2 = 65536 * (65536 * (65536 * (65536 * d6 + d5) + d4) + d3) + d2 := by omega
    have hd1 : e / 65536 = 65536 * (65536 * (65536 * (65536 * (65536 * d6 + d5) + d4) + d3) + d2) + d1 := by omega
    calc e = 65536 * (e / 65536) + d0 := by omega
      _ = 65536 * (65536 * (65536 * (65536 * (65536 * (65536 * d6 + d5) + d4) + d3) + d2) + d1) + d0 := by rw [hd1]
      _ = d0 + 65536 * d1 + 65536 ^ 2 * d2 + 65536 ^ 3 * d3 +
            65536 ^ 4 * d4 + 65536 ^ 5 * d5 + 65536 ^ 6 * d6 := by ring
  have hlt : ∀ x : ℕ, x % 65536 < 2 ^ 16 := fun x =>
    Nat.mod_lt x (by decide : 0 < 65536)
  unfold evalPow65536
  dsimp only
  rw [powModAux_eq 16 b0 d0 m (hlt _),
    powModAux_eq 16 b1 d1 m (hlt _),
    powModAux_eq 16 b2 d2 m (hlt _),
    powModAux_eq 16 b3 d3 m (hlt _),
    powModAux_eq 16 b4 d4 m (hlt _),
    powModAux_eq 16 b5 d5 m (hlt _),
    powModAux_eq 16 b6 d6 m (hlt _)]
  have hb0_pow : b0 ^ d0 % m = a ^ d0 % m := by
    rw [← h0, ← Nat.pow_mod, pow_one]
  have hb1_pow : b1 ^ d1 % m = a ^ (65536 * d1) % m := by
    rw [← ha1, ← Nat.pow_mod, ← pow_mul]
  have hb2_pow : b2 ^ d2 % m = a ^ (65536 ^ 2 * d2) % m := by
    rw [← ha2, ← Nat.pow_mod, ← pow_mul]
  have hb3_pow : b3 ^ d3 % m = a ^ (65536 ^ 3 * d3) % m := by
    rw [← ha3, ← Nat.pow_mod, ← pow_mul]
  have hb4_pow : b4 ^ d4 % m = a ^ (65536 ^ 4 * d4) % m := by
    rw [← ha4, ← Nat.pow_mod, ← pow_mul]
  have hb5_pow : b5 ^ d5 % m = a ^ (65536 ^ 5 * d5) % m := by
    rw [← ha5, ← Nat.pow_mod, ← pow_mul]
  have hb6_pow : b6 ^ d6 % m = a ^ (65536 ^ 6 * d6) % m := by
    rw [← ha6, ← Nat.pow_mod, ← pow_mul]
  rw [hb0_pow, hb1_pow, hb2_pow, hb3_pow, hb4_pow, hb5_pow, hb6_pow]
  rw [← Nat.mul_mod (a ^ d0), ← pow_add,
    ← Nat.mul_mod (a ^ (d0 + 65536 * d1)), ← pow_add,
    ← Nat.mul_mod (a ^ (d0 + 65536 * d1 + 65536 ^ 2 * d2)), ← pow_add,
    ← Nat.mul_mod (a ^ (d0 + 65536 * d1 + 65536 ^ 2 * d2 + 65536 ^ 3 * d3)), ← pow_add,
    ← Nat.mul_mod (a ^ (d0 + 65536 * d1 + 65536 ^ 2 * d2 + 65536 ^ 3 * d3 + 65536 ^ 4 * d4)), ← pow_add,
    ← Nat.mul_mod (a ^ (d0 + 65536 * d1 + 65536 ^ 2 * d2 + 65536 ^ 3 * d3 + 65536 ^ 4 * d4 + 65536 ^ 5 * d5)), ← pow_add,
    ← hexp]

private lemma coprime_of_mul_eq_add_one {x m u v : ℕ} (h : u * x = v * m + 1) :
    Nat.Coprime x m := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hd1 : Nat.gcd x m ∣ u * x := dvd_mul_of_dvd_right (Nat.gcd_dvd_left x m) u
  have hd2 : Nat.gcd x m ∣ v * m := dvd_mul_of_dvd_right (Nat.gcd_dvd_right x m) v
  have hd : Nat.gcd x m ∣ 1 := by
    rw [h] at hd1
    exact (Nat.dvd_add_right hd2).mp hd1
  exact Nat.eq_one_of_dvd_one hd

private lemma pocklington {m F a : ℕ} (hm : 1 < m) (hFpos : 0 < F)
    (hFdvd : F ∣ m - 1) (hFsq : m < F * F)
    (hfermat : a ^ (m - 1) % m = 1)
    (hcop : ∀ q : ℕ, q.Prime → q ∣ F → Nat.Coprime (a ^ ((m - 1) / q) % m - 1) m) :
    Nat.Prime m := by
  by_contra hnotprime
  set r := m.minFac
  have hr : r.Prime := Nat.minFac_prime (by omega)
  have hrm : r ∣ m := Nat.minFac_dvd m
  have hrsq : r * r ≤ m := by
    have := Nat.minFac_sq_le_self (by omega : 0 < m) hnotprime
    simpa [sq, r] using this
  have : Fact r.Prime := ⟨hr⟩
  have hmod_r : a ^ (m - 1) % r = 1 := by
    rw [← Nat.mod_mod_of_dvd _ hrm, hfermat, Nat.mod_eq_of_lt hr.one_lt]
  have hpow_zmod : ((a : ZMod r) ^ (m - 1)) = 1 := by
    rw [← Nat.cast_pow, show (1 : ZMod r) = ((1 : ℕ) : ZMod r) by simp,
      ZMod.natCast_eq_natCast_iff', hmod_r, Nat.mod_eq_of_lt hr.one_lt]
  set d := orderOf (a : ZMod r)
  have hd_m1 : d ∣ m - 1 := orderOf_dvd_of_pow_eq_one hpow_zmod
  have ha0 : (a : ZMod r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : m - 1 ≠ 0)] at hpow_zmod
    exact zero_ne_one hpow_zmod
  have hd_r1 : d ∣ r - 1 := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one ha0)
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (by have := hr.two_le; omega) hd_r1
  have hm1_ne : m - 1 ≠ 0 := by omega
  have hFd : F ∣ d := by
    rw [← Nat.factorization_le_iff_dvd hFpos.ne' hd0]
    intro q
    by_cases hFq0 : F.factorization q = 0
    · rw [hFq0]; exact Nat.zero_le _
    · have hq_mem : q ∈ F.primeFactors := by
        rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr hFq0
      have hq : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
      have hqF : q ∣ F := Nat.dvd_of_mem_primeFactors hq_mem
      have hqm1 : q ∣ m - 1 := dvd_trans hqF hFdvd
      by_contra hlt_not
      have hlt : d.factorization q < F.factorization q := by omega
      have hF_le_m1 : F.factorization ≤ (m - 1).factorization :=
        (Nat.factorization_le_iff_dvd hFpos.ne' hm1_ne).mpr hFdvd
      have hd_le_m1 : d.factorization ≤ (m - 1).factorization :=
        (Nat.factorization_le_iff_dvd hd0 hm1_ne).mpr hd_m1
      have hdiv_ne : (m - 1) / q ≠ 0 := by
        have hpos : 0 < m - 1 := by omega
        have hle : q ≤ m - 1 := Nat.le_of_dvd hpos hqm1
        exact (Nat.div_pos hle hq.pos).ne'
      have hmul_eq : q * ((m - 1) / q) = m - 1 := Nat.mul_div_cancel' hqm1
      have hfac_m1 : (m - 1).factorization = q.factorization + ((m - 1) / q).factorization := by
        conv_lhs => rw [← hmul_eq]
        rw [Nat.factorization_mul hq.ne_zero hdiv_ne]
      have hd_dvd_div : d ∣ (m - 1) / q := by
        rw [← Nat.factorization_le_iff_dvd hd0 hdiv_ne]
        intro l
        have h1 := hd_le_m1 l
        have h2 := congrArg (fun f : ℕ →₀ ℕ => f l) hfac_m1
        simp only [Finsupp.add_apply, hq.factorization, Finsupp.single_apply] at h2
        by_cases hlq : q = l
        · subst hlq
          have hFm1 := hF_le_m1 q
          simp only [↓reduceIte] at h2
          omega
        · simp only [hlq, ↓reduceIte, zero_add] at h2
          omega
      have hpow_div : (a : ZMod r) ^ ((m - 1) / q) = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp hd_dvd_div
      have hmod_div : a ^ ((m - 1) / q) % r = 1 := by
        have hcast : (((a ^ ((m - 1) / q) : ℕ) : ZMod r)) = ((1 : ℕ) : ZMod r) := by
          simpa using hpow_div
        rw [ZMod.natCast_eq_natCast_iff'] at hcast
        rwa [Nat.mod_eq_of_lt hr.one_lt] at hcast
      set x := a ^ ((m - 1) / q) % m
      have hx_mod_r : x % r = 1 := by
        simp only [x, Nat.mod_mod_of_dvd _ hrm, hmod_div]
      have hx_pos : 1 ≤ x := by
        by_contra h0
        have : x = 0 := by omega
        rw [this, Nat.zero_mod] at hx_mod_r
        omega
      have hr_dvd_x1 : r ∣ x - 1 := by
        apply Nat.dvd_of_mod_eq_zero
        have hxdiv := Nat.div_add_mod x r
        have heq : x - 1 = r * (x / r) := by omega
        rw [heq, Nat.mul_mod_right]
      have hcop_q := hcop q hq hqF
      have hr_dvd_1 : r ∣ 1 := by
        rw [← hcop_q.gcd_eq_one]
        exact Nat.dvd_gcd hr_dvd_x1 hrm
      exact hr.not_dvd_one hr_dvd_1
  have hFr : F ∣ r - 1 := dvd_trans hFd hd_r1
  have hF_le : F ≤ r - 1 := Nat.le_of_dvd (by have := hr.two_le; omega) hFr
  have hF_lt : F < r := by have := hr.two_le; omega
  have hsq_lt : F * F < r * r := Nat.mul_lt_mul'' hF_lt hF_lt
  omega

-- ============================================================================
-- Section 3: Counterexample Witness and Deterministic Primality Certificates
-- ============================================================================

private def p1 : ℕ := 2
private def p2 : ℕ := 3
private def p3 : ℕ := 600601
private def p4 : ℕ := 8348341
private def p5 : ℕ := 522158383333960400380558296881791

private def witness : Finset ℕ := {p1, p2, p3, p4, p5}

private def nVal : ℕ := 15708681581691956599944511148034831482650783986

private lemma prime_dvd_prime_pow {q r k : ℕ} (hq : q.Prime) (hr : r.Prime) (h : q ∣ r ^ k) :
    q = r :=
  (Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow h)

private lemma prime_p1 : Nat.Prime p1 := by unfold p1; norm_num
private lemma prime_p2 : Nat.Prime p2 := by unfold p2; norm_num

private lemma prime_p3 : Nat.Prime p3 := by
  have hF : (600600 : ℕ) = 2 ^ 3 * 3 * 5 ^ 2 * 7 * 11 * 13 := by norm_num
  refine pocklington (F := 600600) (a := 37) (by unfold p3; omega) (by omega)
    (by unfold p3; exact dvd_rfl) (by unfold p3; norm_num) ?_ ?_
  · rw [← powModAux_eq 25 37 (p3 - 1) p3 (by unfold p3; norm_num)]
    decide
  · intro q hq hqF
    rw [hF] at hqF
    have hq_cases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 := by
      rcases hq.dvd_mul.mp hqF with h | h13
      · rcases hq.dvd_mul.mp h with h | h11
        · rcases hq.dvd_mul.mp h with h | h7
          · rcases hq.dvd_mul.mp h with h | h5
            · rcases hq.dvd_mul.mp h with h2 | h3
              · exact Or.inl (prime_dvd_prime_pow hq (by norm_num) h2)
              · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3))
            · exact Or.inr (Or.inr (Or.inl (prime_dvd_prime_pow hq (by norm_num) h5)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h7))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h11)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h13)))))
    rcases hq_cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
      · rw [← powModAux_eq 25 37 ((p3 - 1) / _) p3 (by unfold p3; norm_num)]
        decide

private lemma prime_p4 : Nat.Prime p4 := by
  have hF : (8348340 : ℕ) = 2 ^ 2 * 3 * 5 * 7 * 11 * 13 * 139 := by norm_num
  refine pocklington (F := 8348340) (a := 22) (by unfold p4; omega) (by omega)
    (by unfold p4; exact dvd_rfl) (by unfold p4; norm_num) ?_ ?_
  · rw [← powModAux_eq 25 22 (p4 - 1) p4 (by unfold p4; norm_num)]
    decide
  · intro q hq hqF
    rw [hF] at hqF
    have hq_cases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 139 := by
      rcases hq.dvd_mul.mp hqF with h | h139
      · rcases hq.dvd_mul.mp h with h | h13
        · rcases hq.dvd_mul.mp h with h | h11
          · rcases hq.dvd_mul.mp h with h | h7
            · rcases hq.dvd_mul.mp h with h | h5
              · rcases hq.dvd_mul.mp h with h2 | h3
                · exact Or.inl (prime_dvd_prime_pow hq (by norm_num) h2)
                · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3))
              · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h5)))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h7))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h11)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h13))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h139))))))
    rcases hq_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · rw [← powModAux_eq 25 22 ((p4 - 1) / _) p4 (by unfold p4; norm_num)]
        decide

private def b0p5 : ℕ := 12
private def b1p5 : ℕ := 74024172263519985819309412714477
private def b2p5 : ℕ := 480611481024182703374735194779986
private def b3p5 : ℕ := 301566340834482353042135921136697
private def b4p5 : ℕ := 182609712920359211175476806898675
private def b5p5 : ℕ := 214752076723188120257719736261941
private def b6p5 : ℕ := 223243568360137785307017344565304

private lemma hb0p5 : (12 : ℕ) ^ 1 % p5 = b0p5 := by decide
private lemma hb1p5 : b0p5 ^ 65536 % p5 = b1p5 := by
  rw [← powModAux_eq 17 b0p5 65536 p5 (by norm_num)]; decide
private lemma hb2p5 : b1p5 ^ 65536 % p5 = b2p5 := by
  rw [← powModAux_eq 17 b1p5 65536 p5 (by norm_num)]; decide
private lemma hb3p5 : b2p5 ^ 65536 % p5 = b3p5 := by
  rw [← powModAux_eq 17 b2p5 65536 p5 (by norm_num)]; decide
private lemma hb4p5 : b3p5 ^ 65536 % p5 = b4p5 := by
  rw [← powModAux_eq 17 b3p5 65536 p5 (by norm_num)]; decide
private lemma hb5p5 : b4p5 ^ 65536 % p5 = b5p5 := by
  rw [← powModAux_eq 17 b4p5 65536 p5 (by norm_num)]; decide
private lemma hb6p5 : b5p5 ^ 65536 % p5 = b6p5 := by
  rw [← powModAux_eq 17 b5p5 65536 p5 (by norm_num)]; decide

private lemma pow_mod_p5 (e : ℕ) (he : e < 65536 ^ 7) :
    12 ^ e % p5 = evalPow65536 b0p5 b1p5 b2p5 b3p5 b4p5 b5p5 b6p5 e p5 :=
  evalPow65536_eq hb0p5 hb1p5 hb2p5 hb3p5 hb4p5 hb5p5 hb6p5 he

private lemma prime_p5 : Nat.Prime p5 := by
  have hF : (44724788738499870 : ℕ) =
      2 * 3 ^ 2 * 5 * 7 ^ 3 * 11 * 13 * 17 * 19 * 23 * 29 * 31 * 37 * 41 := by norm_num
  refine pocklington (F := 44724788738499870) (a := 12) (by unfold p5; omega) (by omega)
    ⟨11674921180443217, by unfold p5; norm_num⟩ (by unfold p5; norm_num) ?_ ?_
  · rw [pow_mod_p5 (p5 - 1) (by unfold p5; norm_num)]
    decide
  · intro q hq hqF
    rw [hF] at hqF
    have hq_cases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨
        q = 17 ∨ q = 19 ∨ q = 23 ∨ q = 29 ∨ q = 31 ∨ q = 37 ∨ q = 41 := by
      rcases hq.dvd_mul.mp hqF with h | h41
      · rcases hq.dvd_mul.mp h with h | h37
        · rcases hq.dvd_mul.mp h with h | h31
          · rcases hq.dvd_mul.mp h with h | h29
            · rcases hq.dvd_mul.mp h with h | h23
              · rcases hq.dvd_mul.mp h with h | h19
                · rcases hq.dvd_mul.mp h with h | h17
                  · rcases hq.dvd_mul.mp h with h | h13
                    · rcases hq.dvd_mul.mp h with h | h11
                      · rcases hq.dvd_mul.mp h with h | h7
                        · rcases hq.dvd_mul.mp h with h | h5
                          · rcases hq.dvd_mul.mp h with h2 | h3
                            · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h2)
                            · exact Or.inr (Or.inl (prime_dvd_prime_pow hq (by norm_num) h3))
                          · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h5)))
                        · exact Or.inr (Or.inr (Or.inr (Or.inl (prime_dvd_prime_pow hq (by norm_num) h7))))
                      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h11)))))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h13))))))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h17)))))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h19))))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h23)))))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h29))))))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h31)))))))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h37))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h41))))))))))))
    rcases hq_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hx : 12 ^ ((p5 - 1) / 2) % p5 = 522158383333960400380558296881790 := by
        rw [pow_mod_p5 _ (by unfold p5; norm_num)]; decide
      rw [hx]; exact coprime_of_mul_eq_add_one (u := 261079191666980200190279148440895) (v := 261079191666980200190279148440894) (by unfold p5; norm_num)
    · have hx : 12 ^ ((p5 - 1) / 3) % p5 = 276748324709369077921004141910575 := by
        rw [pow_mod_p5 _ (by unfold p5; norm_num)]; decide
      rw [hx]; exact coprime_of_mul_eq_add_one (u := 81803352874863774153184718323738) (v := 43356463453060291729584222168021) (by unfold p5; norm_num)
    · have hx : 12 ^ ((p5 - 1) / 5) % p5 = 8017379945574256010534748185989 := by
        rw [pow_mod_p5 _ (by unfold p5; norm_num)]; decide
      rw [hx]; exact coprime_of_mul_eq_add_one (u := 144536137763912108766814554886667) (v := 2219252183447190741914547775445) (by unfold p5; norm_num)
    · have hx : 12 ^ ((p5 - 1) / 7) % p5 = 408125782691590505141069662580612 := by
        rw [pow_mod_p5 _ (by unfold p5; norm_num)]; decide
      rw [hx]; exact coprime_of_mul_eq_add_one (u := 133238462824087313221211751817379) (v := 104140915209487457781670732618648) (by unfold p5; norm_num)
    · have hx : 12 ^ ((p5 - 1) / 11) % p5 = 57598073238326276350941755817546 := by
        rw [pow_mod_p5 _ (by unfold p5; norm_num)]; decide
      rw [hx]; exact coprime_of_mul_eq_add_one (u := 282463310252400152394309292385262) (v := 31157868858063180769023794953379) (by unfold p5; norm_num)
    · have hx : 12 ^ ((p5 - 1) / 13) % p5 = 384572094181969308719254315134965 := by
        rw [pow_mod_p5 _ (by unfold p5; norm_num)]; decide
      rw [hx]; exact coprime_of_mul_eq_add_one (u := 188876465862546734152616927282128) (v := 139108401467514380980236271937601) (by unfold p5; norm_num)
    · have hx : 12 ^ ((p5 - 1) / 17) % p5 = 309342373007523315563556924412310 := by
        rw [pow_mod_p5 _ (by unfold p5; norm_num)]; decide
      rw [hx]; exact coprime_of_mul_eq_add_one (u := 322056333933267908675252130379010) (v := 190795884468835924014259924878679) (by unfold p5; norm_num)
    · have hx : 12 ^ ((p5 - 1) / 19) % p5 = 439280257422726159985321798646990 := by
        rw [pow_mod_p5 _ (by unfold p5; norm_num)]; decide
      rw [hx]; exact coprime_of_mul_eq_add_one (u := 385636490344808758750779697112704) (v := 324427419260485820914050213922305) (by unfold p5; norm_num)
    · have hx : 12 ^ ((p5 - 1) / 23) % p5 = 111254860493701090480882414683808 := by
        rw [pow_mod_p5 _ (by unfold p5; norm_num)]; decide
      rw [hx]; exact coprime_of_mul_eq_add_one (u := 453226676449586598149034559625144) (v := 96567769990533212033556372888377) (by unfold p5; norm_num)
    · have hx : 12 ^ ((p5 - 1) / 29) % p5 = 22240989424400114563521964175548 := by
        rw [pow_mod_p5 _ (by unfold p5; norm_num)]; decide
      rw [hx]; exact coprime_of_mul_eq_add_one (u := 267159353147012478131280523970876) (v := 11379475150879624801083955915181) (by unfold p5; norm_num)
    · have hx : 12 ^ ((p5 - 1) / 31) % p5 = 65487379338055243380888766269874 := by
        rw [pow_mod_p5 _ (by unfold p5; norm_num)]; decide
      rw [hx]; exact coprime_of_mul_eq_add_one (u := 338665026148567663243942128055945) (v := 42474248702694736984877946302024) (by unfold p5; norm_num)
    · have hx : 12 ^ ((p5 - 1) / 37) % p5 = 312934141382312543919137351631276 := by
        rw [pow_mod_p5 _ (by unfold p5; norm_num)]; decide
      rw [hx]; exact coprime_of_mul_eq_add_one (u := 247459358592911753612820663471401) (v := 148304584164385170658220644493214) (by unfold p5; norm_num)
    · have hx : 12 ^ ((p5 - 1) / 41) % p5 = 194284055217799716428479681108740 := by
        rw [pow_mod_p5 _ (by unfold p5; norm_num)]; decide
      rw [hx]; exact coprime_of_mul_eq_add_one (u := 437105178658397299245265370894019) (v := 162637562427375154473912228384440) (by unfold p5; norm_num)

private lemma witness_prime : ∀ p ∈ witness, Nat.Prime p := by
  intro p hp
  simp only [witness, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact prime_p1
  · exact prime_p2
  · exact prime_p3
  · exact prime_p4
  · exact prime_p5

private lemma witness_card : witness.card = 5 := by
  decide

private lemma witness_prod : ∏ p ∈ witness, p = nVal := by
  decide

-- ============================================================================
-- Section 4: Verification of noCarries and Main Disproof
-- ============================================================================

private lemma sum_witness (g : ℕ → ℕ) :
    ∑ p ∈ witness, g p = g p1 + g p2 + g p3 + g p4 + g p5 := by
  unfold witness
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private lemma witness_noCarries : OMA.S_oeis_a380475.noCarries (∏ p ∈ witness, p) witness := by
  intro j
  rw [witness_prod, sum_witness]
  by_cases hj : j < 30
  · interval_cases j
    · simp only [OMA.S_oeis_a380475.digit, place0, q0, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place1, q1, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place2, q2, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place3, q3, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place4, q4, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place5, q5, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place6, q6, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place7, q7, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place8, q8, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place9, q9, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place10, q10, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place11, q11, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place12, q12, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place13, q13, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place14, q14, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place15, q15, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place16, q16, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place17, q17, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place18, q18, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place19, q19, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place20, q20, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place21, q21, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place22, q22, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place23, q23, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place24, q24, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place25, q25, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place26, q26, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place27, q27, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place28, q28, nVal, p1, p2, p3, p4, p5]; norm_num
    · simp only [OMA.S_oeis_a380475.digit, place29, q29, nVal, p1, p2, p3, p4, p5]; norm_num
  · have hpl : nVal < OMA.S_oeis_a380475.place j := by
      have hle : OMA.S_oeis_a380475.place 30 ≤ OMA.S_oeis_a380475.place j :=
        place_mono (by omega)
      have hlt : nVal < OMA.S_oeis_a380475.place 30 := by
        rw [place30]; unfold nVal; norm_num
      exact lt_of_lt_of_le hlt hle
    have hzero : ∀ p : ℕ, OMA.S_oeis_a380475.digit (nVal / p) j = 0 := by
      intro p
      unfold OMA.S_oeis_a380475.digit
      have hdiv : nVal / p < OMA.S_oeis_a380475.place j :=
        lt_of_le_of_lt (Nat.div_le_self nVal p) hpl
      rw [Nat.div_eq_of_lt hdiv, Nat.zero_mod]
    simp only [hzero, add_zero]
    exact (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j).pos

theorem disproof_proof : ¬ (∀ s : Finset ℕ, (∀ p ∈ s, Nat.Prime p) →
    OMA.S_oeis_a380475.noCarries (∏ p ∈ s, p) s → s.card ≤ 4) := by
  intro h
  have hcard := h witness witness_prime witness_noCarries
  rw [witness_card] at hcard
  omega

end OeisA380475

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a380475.main) :=
  OeisA380475.disproof_proof
