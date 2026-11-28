import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1

-- Reduction AgohGiuga.agoh_giuga.variants.giuga.R2.H1.R1.H1.R1 of step AgohGiuga.agoh_giuga.variants.giuga.R2.H1.R1.H1
-- Credit: @subham-n, @Alewawa
-- uses note #84636
-- uses note #84645

/-! Reduction of AgohGiuga.agoh_giuga.variants.giuga.R2.H1.R1.H1 into three explicit subcases on the mod-5 residues of prime factors. -/

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1_H1_R1

open scoped BigOperators

/- ## Section 1: Exact mod-5, mod-4, mod-25, and mod-125 structural congruences -/

private lemma prod_pf_of_sqf {n : ℕ} (hn : Squarefree n) (hn0 : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p = n := by
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
  rw [Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hle : n.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hn0).mp hn p
  have hpos : 0 < n.factorization p := Nat.Prime.factorization_pos_of_dvd
    (Nat.prime_of_mem_primeFactors hp) hn0 (Nat.dvd_of_mem_primeFactors hp)
  have heq : n.factorization p = 1 := by omega
  simp [heq]

private lemma sum_div_eq_mul_add_one_loc {n k : ℕ} (hn0 : n ≠ 0)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    ∑ p ∈ n.primeFactors, n / p = k * n + 1 := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hmul : ∑ p ∈ n.primeFactors, ((n / p : ℕ) : ℚ) = (k * n + 1 : ℕ) := by
    have h1 : (n : ℚ) * (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ)) = (n : ℚ) * (k : ℚ) := by
      rw [hsum]
    rw [mul_sub, Finset.mul_sum, mul_one_div_cancel hnQ] at h1
    have h2 : ∑ p ∈ n.primeFactors, (n : ℚ) * (1 / (p : ℚ)) =
        ∑ p ∈ n.primeFactors, ((n / p : ℕ) : ℚ) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
      rw [mul_one_div, Nat.cast_div hdvd hp0]
    rw [h2] at h1
    push_cast
    linarith
  exact_mod_cast hmul

private lemma sum_real_gt_k_loc {n k : ℕ} (hn0 : n ≠ 0)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    (k : ℝ) < ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hq : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) = (k : ℚ) + 1 / (n : ℚ) := by linarith
  have hr : ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) = (k : ℝ) + 1 / (n : ℝ) := by
    have := congrArg (Rat.cast (K := ℝ)) hq
    simpa [Rat.cast_sum] using this
  rw [hr]
  linarith [one_div_pos.mpr hnpos]

private lemma primeFactors_partition_30 {n : ℕ} (hn0 : n ≠ 0) (h3 : 3 ∣ n) (h5 : 5 ∣ n)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29) :
    n.primeFactors = insert 3 (insert 5
      ((n.primeFactors.filter (fun p => p % 30 = 17)) ∪
       ((n.primeFactors.filter (fun p => p % 30 = 23)) ∪
        (n.primeFactors.filter (fun p => p % 30 = 29))))) := by
  ext p
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hp
    rcases hprimes p hp with rfl | rfl | h17 | h23 | h29
    · left; rfl
    · right; left; rfl
    · right; right; left; exact ⟨hp, h17⟩
    · right; right; right; left; exact ⟨hp, h23⟩
    · right; right; right; right; exact ⟨hp, h29⟩
  · rintro (rfl | rfl | ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩)
    · exact Nat.mem_primeFactors.mpr ⟨by decide, h3, hn0⟩
    · exact Nat.mem_primeFactors.mpr ⟨by decide, h5, hn0⟩
    · exact hp
    · exact hp
    · exact hp

private lemma prod_mod5_pow {S : Finset ℕ} {a : ℕ} (hS : ∀ p ∈ S, p % 5 = a % 5) :
    (∏ p ∈ S, p) % 5 = (a ^ S.card) % 5 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    rw [Finset.prod_insert hps, Finset.card_insert_of_notMem hps, pow_succ']
    have hp := hS p (Finset.mem_insert_self p s)
    have hs := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
    rw [Nat.mul_mod, hp, hs, ← Nat.mul_mod]

private lemma five_tail_count_mod_4 {n : ℕ} (hnSqf : Squarefree n) (h3 : 3 ∣ n) (h5 : 5 ∣ n)
    (h900 : n % 900 = 705)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29) :
    ((n.primeFactors.filter (fun p => p % 30 = 17)).card +
      3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
      2 * (n.primeFactors.filter (fun p => p % 30 = 29)).card) % 4 = 1 := by
  have hn0 : n ≠ 0 := by omega
  let P17 := n.primeFactors.filter (fun p => p % 30 = 17)
  let P23 := n.primeFactors.filter (fun p => p % 30 = 23)
  let P29 := n.primeFactors.filter (fun p => p % 30 = 29)
  have hpart := primeFactors_partition_30 hn0 h3 h5 hprimes
  have hnprod : ∏ p ∈ n.primeFactors, p = n := prod_pf_of_sqf hnSqf hn0
  have hnot3 : 3 ∉ insert 5 (P17 ∪ (P23 ∪ P29)) := by simp [P17, P23, P29]
  have hnot5 : 5 ∉ P17 ∪ (P23 ∪ P29) := by simp [P17, P23, P29]
  have hdisj1 : Disjoint P17 (P23 ∪ P29) := Finset.disjoint_left.mpr fun p h1 h2 => by
    simp [P17, P23, P29] at h1 h2; omega
  have hdisj2 : Disjoint P23 P29 := Finset.disjoint_left.mpr fun p h1 h2 => by
    simp [P23, P29] at h1 h2; omega
  have hfact : n = 3 * 5 * (∏ p ∈ P17, p) * (∏ p ∈ P23, p) * (∏ p ∈ P29, p) := by
    rw [← hnprod, hpart, Finset.prod_insert hnot3, Finset.prod_insert hnot5,
      Finset.prod_union hdisj1, Finset.prod_union hdisj2]
    ring
  have hdiv5 : n / 5 = 3 * (∏ p ∈ P17, p) * (∏ p ∈ P23, p) * (∏ p ∈ P29, p) := by
    have hmul : n = 5 * (3 * (∏ p ∈ P17, p) * (∏ p ∈ P23, p) * (∏ p ∈ P29, p)) := by
      linarith [hfact]
    rw [hmul, Nat.mul_div_right _ (by decide)]
  have hdiv5_mod : (n / 5) % 5 = 1 := by omega
  have hp17 : (∏ p ∈ P17, p) % 5 = (2 ^ P17.card) % 5 := prod_mod5_pow fun p hp => by
    simp [P17] at hp; omega
  have hp23 : (∏ p ∈ P23, p) % 5 = (3 ^ P23.card) % 5 := prod_mod5_pow fun p hp => by
    simp [P23] at hp; omega
  have hp29 : (∏ p ∈ P29, p) % 5 = (4 ^ P29.card) % 5 := prod_mod5_pow fun p hp => by
    simp [P29] at hp; omega
  have hpow3 : (3 ^ P23.card) % 5 = (2 ^ (3 * P23.card)) % 5 := by
    have h8 : 3 = (2 ^ 3) % 5 := rfl
    conv_lhs => rw [h8, ← Nat.pow_mod, ← pow_mul]
  have hpow4 : (4 ^ P29.card) % 5 = (2 ^ (2 * P29.card)) % 5 := by
    have h4 : 4 = (2 ^ 2) % 5 := rfl
    conv_lhs => rw [h4, ← Nat.pow_mod, ← pow_mul]
  have hcongr : (n / 5) % 5 = (2 ^ (3 + P17.card + 3 * P23.card + 2 * P29.card)) % 5 := by
    rw [hdiv5]
    calc (3 * (∏ p ∈ P17, p) * (∏ p ∈ P23, p) * (∏ p ∈ P29, p)) % 5
        = ((3 * ((∏ p ∈ P17, p) % 5)) * ((∏ p ∈ P23, p) % 5) * ((∏ p ∈ P29, p) % 5)) % 5 := by
            simp only [Nat.mul_mod, Nat.mod_mod]
      _ = (2 ^ 3 % 5 * (2 ^ P17.card % 5) * (2 ^ (3 * P23.card) % 5) *
            (2 ^ (2 * P29.card) % 5)) % 5 := by
            rw [hp17, hp23, hp29, hpow3, hpow4]; rfl
      _ = (2 ^ 3 * 2 ^ P17.card * 2 ^ (3 * P23.card) * 2 ^ (2 * P29.card)) % 5 := by
            simp only [Nat.mul_mod, Nat.mod_mod]
      _ = (2 ^ (3 + P17.card + 3 * P23.card + 2 * P29.card)) % 5 := by
            simp only [pow_add, mul_assoc]
  rw [hdiv5_mod] at hcongr
  let E := 3 + P17.card + 3 * P23.card + 2 * P29.card
  have hE : (2 ^ E) % 5 = (2 ^ (E % 4)) % 5 := by
    have hdiv : E = 4 * (E / 4) + E % 4 := (Nat.div_add_mod E 4).symm
    conv_lhs => rw [hdiv, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have h16 : (2 ^ 4) % 5 = 1 := rfl
    rw [h16]
    simp
  have hr : 1 = (2 ^ (E % 4)) % 5 := by rw [← hE]; exact hcongr
  have hlt : E % 4 < 4 := Nat.mod_lt _ (by decide)
  rcases (by omega : E % 4 = 0 ∨ E % 4 = 1 ∨ E % 4 = 2 ∨ E % 4 = 3) with h | h | h | h
  · change (P17.card + 3 * P23.card + 2 * P29.card) % 4 = 1
    omega
  · rw [h] at hr; simp at hr
  · rw [h] at hr; simp at hr
  · rw [h] at hr; simp at hr

private lemma two_dvd_c29_of_card_odd {n k : ℕ} (h3 : 3 ∣ n) (h5 : 5 ∣ n) (h900 : n % 900 = 705)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)
    (hk2 : 2 ∣ k) (hcard8 : n.primeFactors.card % 8 = (k + 1) % 8)
    (hmod4 : ((n.primeFactors.filter (fun p => p % 30 = 17)).card +
      3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
      2 * (n.primeFactors.filter (fun p => p % 30 = 29)).card) % 4 = 1) :
    2 ∣ (n.primeFactors.filter (fun p => p % 30 = 29)).card := by
  have hn0 : n ≠ 0 := by omega
  let P17 := n.primeFactors.filter (fun p => p % 30 = 17)
  let P23 := n.primeFactors.filter (fun p => p % 30 = 23)
  let P29 := n.primeFactors.filter (fun p => p % 30 = 29)
  have hpart := primeFactors_partition_30 hn0 h3 h5 hprimes
  have hnot3 : 3 ∉ insert 5 (P17 ∪ (P23 ∪ P29)) := by simp [P17, P23, P29]
  have hnot5 : 5 ∉ P17 ∪ (P23 ∪ P29) := by simp [P17, P23, P29]
  have hdisj1 : Disjoint P17 (P23 ∪ P29) := Finset.disjoint_left.mpr fun p h1 h2 => by
    simp [P17, P23, P29] at h1 h2; omega
  have hdisj2 : Disjoint P23 P29 := Finset.disjoint_left.mpr fun p h1 h2 => by
    simp [P23, P29] at h1 h2; omega
  have hcard : n.primeFactors.card = 2 + P17.card + P23.card + P29.card := by
    rw [hpart, Finset.card_insert_of_notMem hnot3, Finset.card_insert_of_notMem hnot5,
      Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2]
    ring
  rcases hk2 with ⟨m, rfl⟩
  have hodd : n.primeFactors.card % 2 = 1 := by omega
  have hc29 : P29.card % 2 = 0 := by
    change (P17.card + 3 * P23.card + 2 * P29.card) % 4 = 1 at hmod4
    omega
  exact Nat.dvd_of_mod_eq_zero hc29

private lemma mod_125_of_three_five_dvd {n k : ℕ} (_hnSqf : Squarefree n) (h3 : 3 ∣ n) (h5 : 5 ∣ n)
    (h900 : n % 900 = 705)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    n % 125 = (25 * (k + 2 * (n.primeFactors.filter (fun p => p % 30 = 17)).card +
      3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
      (n.primeFactors.filter (fun p => p % 30 = 29)).card + 3) + 5) % 125 := by
  have hn0 : n ≠ 0 := by omega
  have hsum_nat := sum_div_eq_mul_add_one_loc hn0 hsum
  let P17 := n.primeFactors.filter (fun p => p % 30 = 17)
  let P23 := n.primeFactors.filter (fun p => p % 30 = 23)
  let P29 := n.primeFactors.filter (fun p => p % 30 = 29)
  have hpart := primeFactors_partition_30 hn0 h3 h5 hprimes
  have hnot3 : 3 ∉ insert 5 (P17 ∪ (P23 ∪ P29)) := by simp [P17, P23, P29]
  have hnot5 : 5 ∉ P17 ∪ (P23 ∪ P29) := by simp [P17, P23, P29]
  have hdisj1 : Disjoint P17 (P23 ∪ P29) := Finset.disjoint_left.mpr fun p h1 h2 => by
    simp [P17, P23, P29] at h1 h2; omega
  have hdisj2 : Disjoint P23 P29 := Finset.disjoint_left.mpr fun p h1 h2 => by
    simp [P23, P29] at h1 h2; omega
  have hsum_split : ∑ p ∈ n.primeFactors, n / p =
      n / 3 + n / 5 + (∑ p ∈ P17, n / p) + (∑ p ∈ P23, n / p) + (∑ p ∈ P29, n / p) := by
    rw [hpart, Finset.sum_insert hnot3, Finset.sum_insert hnot5,
      Finset.sum_union hdisj1, Finset.sum_union hdisj2]
    ring
  have hdvd5m : ∀ {p : ℕ}, p ∈ n.primeFactors → p ≠ 5 → 5 * p ∣ n := fun {p} hp hne5 => by
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.dvd_of_mem_primeFactors hp
    have hcop : Nat.Coprime 5 p := (by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr fun h5p =>
      hne5 ((Nat.Prime.dvd_iff_eq hp_prime (by decide)).mp h5p)
    exact hcop.mul_dvd_of_dvd_of_dvd h5 hpdvd
  have hterm_mod : ∀ {p : ℕ}, p ∈ n.primeFactors → p ≠ 5 → ∀ a b : ℕ,
      p % 5 = a → (a * b) % 5 = 1 → (n / p) % 25 = (5 * b) % 25 := by
    intro p hp hne5 a b hpa hab
    have h5p : 5 * p ∣ n := hdvd5m hp hne5
    have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
    let q := n / (5 * p)
    have hq_eq : 5 * p * q = n := Nat.mul_div_cancel' h5p
    have hnp_eq : n / p = 5 * q := by
      have : n = p * (5 * q) := by linarith
      rw [this, Nat.mul_div_right _ hp0]
    have hqp_eq : q * p = n / 5 := by
      have : n = 5 * (q * p) := by linarith
      rw [this, Nat.mul_div_right _ (by decide)]
    have hmod5 : (n / 5) % 5 = 1 := by omega
    have hqp_mod : ((q % 5) * a) % 5 = 1 := by
      rw [← hpa, ← Nat.mul_mod, hqp_eq, hmod5]
    have hb_lt : b % 5 < 5 := Nat.mod_lt _ (by decide)
    have hb_mod : (a * (b % 5)) % 5 = 1 := by
      calc (a * (b % 5)) % 5 = (a * b) % 5 := by rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
        _ = 1 := hab
    have hq5 : q % 5 = b % 5 := by
      have h1 : (q % 5) < 5 := Nat.mod_lt _ (by decide)
      have ha_lt : a < 5 := by rw [← hpa]; exact Nat.mod_lt _ (by decide)
      rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) with rfl | rfl | rfl | rfl | rfl
      · simp at hqp_mod
      · omega
      · omega
      · omega
      · omega
    have hqb : 5 * q = 25 * (q / 5) + 5 * (b % 5) := by omega
    have hbb : 5 * b = 25 * (b / 5) + 5 * (b % 5) := by omega
    rw [hnp_eq, hqb, hbb]
    omega
  have h3mem : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h3, hn0⟩
  have hn3 : (n / 3) % 25 = 10 := by
    simpa using hterm_mod h3mem (by decide) 3 2 rfl (by decide)
  have hp17_sum : (∑ p ∈ P17, n / p) % 25 = (15 * P17.card) % 25 := by
    have : ∀ p ∈ P17, (n / p) % 25 = 15 := fun p hp => by
      simp only [P17, Finset.mem_filter] at hp
      exact hterm_mod hp.1 (by omega) 2 3 (by omega) (by decide)
    calc (∑ p ∈ P17, n / p) % 25 = (∑ p ∈ P17, (n / p) % 25) % 25 := by
            rw [Finset.sum_nat_mod]
      _ = (∑ _p ∈ P17, 15) % 25 := by rw [Finset.sum_congr rfl this]
      _ = (15 * P17.card) % 25 := by simp [mul_comm]
  have hp23_sum : (∑ p ∈ P23, n / p) % 25 = (10 * P23.card) % 25 := by
    have : ∀ p ∈ P23, (n / p) % 25 = 10 := fun p hp => by
      simp only [P23, Finset.mem_filter] at hp
      exact hterm_mod hp.1 (by omega) 3 2 (by omega) (by decide)
    calc (∑ p ∈ P23, n / p) % 25 = (∑ p ∈ P23, (n / p) % 25) % 25 := by
            rw [Finset.sum_nat_mod]
      _ = (∑ _p ∈ P23, 10) % 25 := by rw [Finset.sum_congr rfl this]
      _ = (10 * P23.card) % 25 := by simp [mul_comm]
  have hp29_sum : (∑ p ∈ P29, n / p) % 25 = (20 * P29.card) % 25 := by
    have : ∀ p ∈ P29, (n / p) % 25 = 20 := fun p hp => by
      simp only [P29, Finset.mem_filter] at hp
      exact hterm_mod hp.1 (by omega) 4 4 (by omega) (by decide)
    calc (∑ p ∈ P29, n / p) % 25 = (∑ p ∈ P29, (n / p) % 25) % 25 := by
            rw [Finset.sum_nat_mod]
      _ = (∑ _p ∈ P29, 20) % 25 := by rw [Finset.sum_congr rfl this]
      _ = (20 * P29.card) % 25 := by simp [mul_comm]
  have hlhs_mod : (∑ p ∈ n.primeFactors, n / p) % 25 =
      (n / 5 + 10 + 15 * P17.card + 10 * P23.card + 20 * P29.card) % 25 := by
    rw [hsum_split]
    simp only [Nat.add_mod, hn3, hp17_sum, hp23_sum, hp29_sum, Nat.mod_mod]
    rw [Nat.add_comm 10 (n / 5 % 25 % 25)]
  have hrhs_mod : (k * n + 1) % 25 = (5 * k + 1) % 25 := by
    have hn25 : n = 25 * (n / 25) + 5 := by omega
    have hkn : k * n + 1 = 25 * (k * (n / 25)) + (5 * k + 1) := by nlinarith
    rw [hkn, Nat.mul_add_mod]
  have h5_eq : (n / 5) % 25 = (5 * (k + 2 * P17.card + 3 * P23.card + P29.card + 3) + 1) % 25 := by
    have heq25 : (n / 5 + 10 + 15 * P17.card + 10 * P23.card + 20 * P29.card) % 25 = (5 * k + 1) % 25 := by
      rw [← hlhs_mod, hsum_nat, hrhs_mod]
    omega
  let M := k + 2 * P17.card + 3 * P23.card + P29.card + 3
  have hM_lt : (n / 5) % 25 = 5 * (M % 5) + 1 := by
    have h5M : (5 * M + 1) % 25 = 5 * (M % 5) + 1 := by
      have hdivM : M = 5 * (M / 5) + M % 5 := (Nat.div_add_mod M 5).symm
      have h5M' : 5 * M + 1 = 25 * (M / 5) + (5 * (M % 5) + 1) := by omega
      rw [h5M', Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    exact h5_eq.trans h5M
  have hn5_div : n / 5 = 25 * (n / 5 / 25) + (n / 5) % 25 := (Nat.div_add_mod (n / 5) 25).symm
  have hn_eq : n = 5 * (n / 5) := (Nat.mul_div_cancel' h5).symm
  change n % 125 = (25 * M + 5) % 125
  have hM_div : M = 5 * (M / 5) + M % 5 := (Nat.div_add_mod M 5).symm
  omega

/- ## Section 2: Self-contained Selberg Lambda-squared sieve for primes ≡ 17, 23, 29 (mod 30) -/

private lemma sqf_coprime_div {u r : ℕ} (hu : Squarefree u) (hr : r ∣ u) :
    Nat.Coprime r (u / r) := by
  by_contra hnc
  have hgcd : Nat.gcd r (u / r) ≠ 1 := hnc
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hgcd
  have hpr : p ∣ r := hpd.trans (Nat.gcd_dvd_left r (u / r))
  have hpdiv : p ∣ u / r := hpd.trans (Nat.gcd_dvd_right r (u / r))
  have hpp : p * p ∣ r * (u / r) := mul_dvd_mul hpr hpdiv
  rw [Nat.mul_div_cancel' hr] at hpp
  exact hp.not_isUnit (hu p hpp)

private lemma sum_inv_totient_divisors {d : ℕ} (hd : Squarefree d) (hd0 : d ≠ 0) :
    ∑ t ∈ d.divisors, (1 / (t.totient : ℝ)) = (d : ℝ) / (d.totient : ℝ) := by
  have hdt_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0))
  rw [eq_div_iff hdt_pos.ne']
  rw [Finset.sum_mul]
  have hbij : ∑ t ∈ d.divisors, 1 / (t.totient : ℝ) * (d.totient : ℝ) =
      ∑ s ∈ d.divisors, (s.totient : ℝ) := by
    refine Finset.sum_bij (fun t _ => d / t) ?_ ?_ ?_ ?_
    · intro t ht
      rw [Nat.mem_divisors] at ht ⊢
      exact ⟨Nat.div_dvd_of_dvd ht.1, ht.2⟩
    · intro t1 ht1 t2 ht2 heq
      rw [Nat.mem_divisors] at ht1 ht2
      have := congrArg (fun x => d / x) heq
      simpa [Nat.div_div_self ht1.1 hd0, Nat.div_div_self ht2.1 hd0] using this
    · intro s hs
      rw [Nat.mem_divisors] at hs
      refine ⟨d / s, ?_, Nat.div_div_self hs.1 hd0⟩
      rw [Nat.mem_divisors]
      exact ⟨Nat.div_dvd_of_dvd hs.1, hs.2⟩
    · intro t ht
      rw [Nat.mem_divisors] at ht
      have hcop := sqf_coprime_div hd ht.1
      have hm : t * (d / t) = d := Nat.mul_div_cancel' ht.1
      have htot : d.totient = t.totient * (d / t).totient := by
        conv_lhs => rw [← hm, Nat.totient_mul hcop]
      have ht0 : t ≠ 0 := ne_zero_of_dvd_ne_zero hd0 ht.1
      have htt_pos : (0 : ℝ) < (t.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero ht0))
      rw [htot]
      push_cast
      field_simp [htt_pos.ne']
  rw [hbij]
  exact_mod_cast Nat.sum_totient d

private lemma primeFactors_mul_prime {r p : ℕ} (hr0 : r ≠ 0) (hp : p.Prime) (_hpr : ¬ p ∣ r) :
    (r * p).primeFactors = insert p r.primeFactors := by
  rw [Nat.primeFactors_mul hr0 hp.ne_zero, hp.primeFactors, Finset.union_comm, Finset.singleton_union]

private lemma sum_mu_divisors_sqf {u : ℕ} (hu : Squarefree u) (hu0 : u ≠ 0) :
    ∑ r ∈ u.divisors, (-1 : ℝ) ^ r.primeFactors.card = if u = 1 then 1 else 0 := by
  by_cases hu1 : u = 1
  · subst hu1; simp
  · simp only [if_neg hu1]
    obtain ⟨p, hp, hpu⟩ := Nat.exists_prime_and_dvd hu1
    refine Finset.sum_involution (fun r _ => if p ∣ r then r / p else r * p) ?_ ?_ ?_ ?_
    · intro r hr
      rw [Nat.mem_divisors] at hr
      have hr0 : r ≠ 0 := ne_zero_of_dvd_ne_zero hu0 hr.1
      by_cases hpr : p ∣ r
      · simp only [hpr, ↓reduceIte]
        have hnot : ¬ p ∣ r / p := fun hdiv => by
          have hpp : p * p ∣ r := by
            have := mul_dvd_mul_left p hdiv
            rwa [Nat.mul_div_cancel' hpr] at this
          exact hp.not_isUnit (hu p (hpp.trans hr.1))
        have hdiv0 : r / p ≠ 0 := fun h0 => by
          rw [← Nat.mul_div_cancel' hpr, h0, mul_zero] at hr0; exact hr0 rfl
        have hpf : r.primeFactors = insert p (r / p).primeFactors := by
          conv_lhs => rw [← Nat.div_mul_cancel hpr, primeFactors_mul_prime hdiv0 hp hnot]
        have hp_nmem : p ∉ (r / p).primeFactors := fun hm =>
          hnot (Nat.dvd_of_mem_primeFactors hm)
        rw [hpf, Finset.card_insert_of_notMem hp_nmem]
        ring
      · simp only [hpr, ↓reduceIte]
        have hpf : (r * p).primeFactors = insert p r.primeFactors := primeFactors_mul_prime hr0 hp hpr
        have hp_nmem : p ∉ r.primeFactors := fun hm =>
          hpr (Nat.dvd_of_mem_primeFactors hm)
        rw [hpf, Finset.card_insert_of_notMem hp_nmem]
        ring
    · intro r hr _
      rw [Nat.mem_divisors] at hr
      have hr0 : 0 < r := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hu0 hr.1)
      have hp2 : 2 ≤ p := hp.two_le
      by_cases hpr : p ∣ r
      · simp only [hpr, ↓reduceIte]
        exact (Nat.div_lt_self hr0 (by omega)).ne
      · simp only [hpr, ↓reduceIte]
        have : r < r * p := by nlinarith
        exact this.ne'
    · intro r hr
      rw [Nat.mem_divisors] at hr ⊢
      refine ⟨?_, hu0⟩
      by_cases hpr : p ∣ r
      · simp only [hpr, ↓reduceIte]
        exact (Nat.div_dvd_of_dvd hpr).trans hr.1
      · simp only [hpr, ↓reduceIte]
        have hcop : Nat.Coprime r p := (hp.coprime_iff_not_dvd.mpr hpr).symm
        exact hcop.mul_dvd_of_dvd_of_dvd hr.1 hpu
    · intro r hr
      rw [Nat.mem_divisors] at hr
      by_cases hpr : p ∣ r
      · simp only [hpr, ↓reduceIte]
        have hnot : ¬ p ∣ r / p := fun hdiv => by
          have hpp : p * p ∣ r := by
            have := mul_dvd_mul_left p hdiv
            rwa [Nat.mul_div_cancel' hpr] at this
          exact hp.not_isUnit (hu p (hpp.trans hr.1))
        simp [hnot, Nat.div_mul_cancel hpr]
      · simp only [hpr, ↓reduceIte]
        have hdp : p ∣ r * p := dvd_mul_left p r
        simp [hdp, Nat.mul_div_cancel _ hp.pos]

private lemma block_count_mod30_dvd (X m r : ℕ) (hm1 : 1 ≤ m) (hm30 : Nat.Coprime m 30)
    (hr : r < 30) :
    X / (30 * m) ≤ ((Finset.Icc 1 X).filter (fun n => n % 30 = r ∧ m ∣ n)).card ∧
    ((Finset.Icc 1 X).filter (fun n => n % 30 = r ∧ m ∣ n)).card ≤ X / (30 * m) + 1 := by
  have hm30' : Nat.Coprime 30 m := hm30.symm
  let cr := Nat.chineseRemainder hm30' r 0
  let a0 := cr.val % (30 * m)
  have hMpos : 0 < 30 * m := by positivity
  have ha0_lt : a0 < 30 * m := Nat.mod_lt _ hMpos
  have ha0_mod30 : a0 % 30 = r := by
    have h1 : cr.val % 30 = r % 30 := cr.2.1
    change (cr.val % (30 * m)) % 30 = r
    rw [Nat.mod_mod_of_dvd cr.val (dvd_mul_right 30 m), h1, Nat.mod_eq_of_lt hr]
  have ha0_dvdm : m ∣ a0 := by
    have h1 : cr.val % m = 0 % m := cr.2.2
    rw [Nat.dvd_iff_mod_eq_zero]
    change (cr.val % (30 * m)) % m = 0
    rw [Nat.mod_mod_of_dvd cr.val (dvd_mul_left m 30), h1, Nat.zero_mod]
  have hiff : ∀ n : ℕ, (n % 30 = r ∧ m ∣ n) ↔ n % (30 * m) = a0 := fun n => by
    constructor
    · rintro ⟨hn30, hnm⟩
      have hmod30 : n ≡ a0 [MOD 30] := by change n % 30 = a0 % 30; rw [hn30, ha0_mod30]
      have hmodm : n ≡ a0 [MOD m] := by
        change n % m = a0 % m
        rw [Nat.mod_eq_zero_of_dvd hnm, Nat.mod_eq_zero_of_dvd ha0_dvdm]
      have hmodM : n ≡ a0 [MOD 30 * m] := (Nat.modEq_and_modEq_iff_modEq_mul hm30').mp ⟨hmod30, hmodm⟩
      change n % (30 * m) = a0 % (30 * m) at hmodM
      rwa [Nat.mod_eq_of_lt ha0_lt] at hmodM
    · intro hM
      refine ⟨?_, ?_⟩
      · have : n % 30 = (n % (30 * m)) % 30 := (Nat.mod_mod_of_dvd _ (dvd_mul_right 30 m)).symm
        rw [this, hM, ha0_mod30]
      · have hmodm : n % m = (n % (30 * m)) % m := (Nat.mod_mod_of_dvd _ (dvd_mul_left m 30)).symm
        rw [Nat.dvd_iff_mod_eq_zero, hmodm, hM]
        exact Nat.mod_eq_zero_of_dvd ha0_dvdm
  let B := (Finset.Icc 1 X).filter (fun n => n % 30 = r ∧ m ∣ n)
  let Q := X / (30 * m)
  constructor
  · have hlower_fn : Finset.image (fun q => q * (30 * m) + if a0 = 0 then (30 * m) else a0)
        (Finset.range Q) ⊆ B := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨q, hq, rfl⟩
      rw [Finset.mem_range] at hq
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, (hiff _).mpr ?_⟩
      · by_cases ha : a0 = 0
        · simp [ha]; omega
        · simp [ha]; omega
      · have hqX : (q + 1) * (30 * m) ≤ Q * (30 * m) := Nat.mul_le_mul_right _ hq
        have hQX : Q * (30 * m) ≤ X := Nat.div_mul_le_self X (30 * m)
        by_cases ha : a0 = 0
        · simp [ha]
          linarith [add_one_mul q (30 * m), hqX, hQX]
        · simp [ha]
          have ha_le : a0 ≤ 30 * m := ha0_lt.le
          linarith [add_one_mul q (30 * m), hqX, hQX, ha_le]
      · by_cases ha : a0 = 0
        · simp [ha]
        · simp [ha, Nat.add_mod, Nat.mod_eq_of_lt ha0_lt]
    have hinj : Function.Injective (fun q => q * (30 * m) + if a0 = 0 then (30 * m) else a0) := by
      intro q1 q2 heq
      exact mul_right_cancel₀ hMpos.ne' (Nat.add_right_cancel heq)
    calc Q = (Finset.range Q).card := (Finset.card_range Q).symm
      _ = ((Finset.range Q).image _).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ B.card := Finset.card_le_card hlower_fn
  · have himg : B.image (fun n => (n - 1) / (30 * m)) ⊆ Finset.range (Q + 1) := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨n, hn, rfl⟩
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      have : (n - 1) / (30 * m) ≤ X / (30 * m) := Nat.div_le_div_right (by omega)
      omega
    have hinj : ∀ n1 ∈ B, ∀ n2 ∈ B, (n1 - 1) / (30 * m) = (n2 - 1) / (30 * m) → n1 = n2 := by
      intro n1 hn1 n2 hn2 heq
      rw [Finset.mem_filter, Finset.mem_Icc] at hn1 hn2
      have hm1' := (hiff n1).mp hn1.2
      have hm2' := (hiff n2).mp hn2.2
      by_cases ha : a0 = 0
      · have hd1 : (30 * m) ∣ n1 := Nat.dvd_of_mod_eq_zero (by rwa [ha] at hm1')
        have hd2 : (30 * m) ∣ n2 := Nat.dvd_of_mod_eq_zero (by rwa [ha] at hm2')
        obtain ⟨k1, hk1⟩ := hd1
        obtain ⟨k2, hk2⟩ := hd2
        have hk1_pos : 1 ≤ k1 := by
          by_contra hk; have : k1 = 0 := by omega
          rw [this, mul_zero] at hk1; omega
        have hk2_pos : 1 ≤ k2 := by
          by_contra hk; have : k2 = 0 := by omega
          rw [this, mul_zero] at hk2; omega
        have hq1 : (n1 - 1) / (30 * m) = k1 - 1 := by
          rw [hk1]
          have hsub : 30 * m * k1 - 1 = (30 * m) * (k1 - 1) + (30 * m - 1) := by
            conv_lhs => rw [show k1 = (k1 - 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
            omega
          rw [hsub, Nat.mul_add_div hMpos, Nat.div_eq_of_lt (by omega)]; ring
        have hq2 : (n2 - 1) / (30 * m) = k2 - 1 := by
          rw [hk2]
          have hsub : 30 * m * k2 - 1 = (30 * m) * (k2 - 1) + (30 * m - 1) := by
            conv_lhs => rw [show k2 = (k2 - 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
            omega
          rw [hsub, Nat.mul_add_div hMpos, Nat.div_eq_of_lt (by omega)]; ring
        rw [hq1, hq2] at heq
        have hk : k1 = k2 := by omega
        rw [hk1, hk2, hk]
      · have h1pos : 1 ≤ a0 := by omega
        have hn1_eq : n1 = (30 * m) * (n1 / (30 * m)) + a0 := by
          rw [← hm1']; exact (Nat.div_add_mod n1 (30 * m)).symm
        have hn2_eq : n2 = (30 * m) * (n2 / (30 * m)) + a0 := by
          rw [← hm2']; exact (Nat.div_add_mod n2 (30 * m)).symm
        have hdiv0 : (a0 - 1) / (30 * m) = 0 := Nat.div_eq_of_lt (by omega)
        have hq1 : (n1 - 1) / (30 * m) = n1 / (30 * m) := by
          have hsub : n1 - 1 = (30 * m) * (n1 / (30 * m)) + (a0 - 1) := by
            conv_lhs => rw [hn1_eq]
            omega
          rw [hsub, Nat.mul_add_div hMpos, hdiv0]; ring
        have hq2 : (n2 - 1) / (30 * m) = n2 / (30 * m) := by
          have hsub : n2 - 1 = (30 * m) * (n2 / (30 * m)) + (a0 - 1) := by
            conv_lhs => rw [hn2_eq]
            omega
          rw [hsub, Nat.mul_add_div hMpos, hdiv0]; ring
        rw [hq1, hq2] at heq
        rw [hn1_eq, hn2_eq, heq]
    calc B.card = (B.image (fun n => (n - 1) / (30 * m))).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (Q + 1)).card := Finset.card_le_card himg
      _ = Q + 1 := Finset.card_range (Q + 1)

private lemma block_count_mod30_err (X m : ℕ) (hm1 : 1 ≤ m) (hm30 : Nat.Coprime m 30) :
    |(((Finset.Icc 1 X).filter (fun n => (n % 30 = 17 ∨ n % 30 = 23 ∨ n % 30 = 29) ∧ m ∣ n)).card : ℝ) -
      (X : ℝ) / (10 * (m : ℝ))| ≤ 3 := by
  let A := Finset.Icc 1 X
  let B17 := A.filter (fun n => n % 30 = 17 ∧ m ∣ n)
  let B23 := A.filter (fun n => n % 30 = 23 ∧ m ∣ n)
  let B29 := A.filter (fun n => n % 30 = 29 ∧ m ∣ n)
  let B := A.filter (fun n => (n % 30 = 17 ∨ n % 30 = 23 ∨ n % 30 = 29) ∧ m ∣ n)
  have hB : B = B17 ∪ (B23 ∪ B29) := by
    ext n; simp only [B, B17, B23, B29, Finset.mem_union, Finset.mem_filter]; tauto
  have h1 : Disjoint B17 (B23 ∪ B29) := Finset.disjoint_left.mpr fun n h1 h2 => by
    simp [B17, B23, B29] at h1 h2; omega
  have h2 : Disjoint B23 B29 := Finset.disjoint_left.mpr fun n h1 h2 => by
    simp [B23, B29] at h1 h2; omega
  have hcard : B.card = B17.card + B23.card + B29.card := by
    rw [hB, Finset.card_union_of_disjoint h1, Finset.card_union_of_disjoint h2]; ring
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm1
  have herr : ∀ r < 30, |((A.filter (fun n => n % 30 = r ∧ m ∣ n)).card : ℝ) -
      (X : ℝ) / (30 * (m : ℝ))| ≤ 1 := fun r hr => by
    obtain ⟨hl, hu⟩ := block_count_mod30_dvd X m r hm1 hm30 hr
    have hMpos : 0 < 30 * m := by omega
    have hq1 : (X / (30 * m) : ℕ) * (30 * m) ≤ X := Nat.div_mul_le_self X (30 * m)
    have hq2 : X < (X / (30 * m) + 1) * (30 * m) := by linarith [Nat.lt_mul_div_succ X hMpos]
    have hq1R : ((X / (30 * m) : ℕ) : ℝ) * (30 * (m : ℝ)) ≤ (X : ℝ) := by exact_mod_cast hq1
    have hq2R : (X : ℝ) < (((X / (30 * m) : ℕ) : ℝ) + 1) * (30 * (m : ℝ)) := by exact_mod_cast hq2
    have hdiv_lo : (X : ℝ) / (30 * (m : ℝ)) - 1 < ((X / (30 * m) : ℕ) : ℝ) := by
      have : (X : ℝ) / (30 * (m : ℝ)) < ((X / (30 * m) : ℕ) : ℝ) + 1 :=
        (div_lt_iff₀ (by positivity)).mpr hq2R
      linarith
    have hdiv_hi : ((X / (30 * m) : ℕ) : ℝ) ≤ (X : ℝ) / (30 * (m : ℝ)) :=
      (le_div_iff₀ (by positivity)).mpr hq1R
    have hlR : ((X / (30 * m) : ℕ) : ℝ) ≤ ((A.filter (fun n => n % 30 = r ∧ m ∣ n)).card : ℝ) := by
      exact_mod_cast hl
    have huR : ((A.filter (fun n => n % 30 = r ∧ m ∣ n)).card : ℝ) ≤ ((X / (30 * m) : ℕ) : ℝ) + 1 := by
      exact_mod_cast hu
    rw [abs_le]
    constructor <;> linarith
  have e17 := herr 17 (by decide)
  have e23 := herr 23 (by decide)
  have e29 := herr 29 (by decide)
  have hcast : (B.card : ℝ) - (X : ℝ) / (10 * (m : ℝ)) =
      (((B17.card : ℝ) - (X : ℝ) / (30 * (m : ℝ))) +
       ((B23.card : ℝ) - (X : ℝ) / (30 * (m : ℝ)))) +
       ((B29.card : ℝ) - (X : ℝ) / (30 * (m : ℝ))) := by
    rw [hcard]; push_cast; field_simp [hmpos.ne']; ring
  rw [hcast]
  calc |((B17.card : ℝ) - (X : ℝ) / (30 * (m : ℝ))) +
        ((B23.card : ℝ) - (X : ℝ) / (30 * (m : ℝ))) +
        ((B29.card : ℝ) - (X : ℝ) / (30 * (m : ℝ)))|
      ≤ |((B17.card : ℝ) - (X : ℝ) / (30 * (m : ℝ))) +
          ((B23.card : ℝ) - (X : ℝ) / (30 * (m : ℝ)))| +
          |(B29.card : ℝ) - (X : ℝ) / (30 * (m : ℝ))| := abs_add_le _ _
    _ ≤ (|(B17.card : ℝ) - (X : ℝ) / (30 * (m : ℝ))| +
          |(B23.card : ℝ) - (X : ℝ) / (30 * (m : ℝ))|) +
          |(B29.card : ℝ) - (X : ℝ) / (30 * (m : ℝ))| := by gcongr; exact abs_add_le _ _
    _ ≤ 1 + 1 + 1 := by linarith [e17, e23, e29]
    _ = 3 := by norm_num

private lemma selberg_pi30_le (X z : ℕ) (hz : 1 ≤ z) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) ≤
      (z : ℝ) +
      (X : ℝ) / (10 * ∑ d ∈ (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
        (1 / (d.totient : ℝ))) +
      3 * (((Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)).card : ℝ) ^ 2 := by
  let D := (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)
  let L : ℝ := ∑ l ∈ D, (1 / (l.totient : ℝ))
  let mu : ℕ → ℝ := fun n => (-1 : ℝ) ^ n.primeFactors.card
  let lam : ℕ → ℝ := fun d =>
    (mu d * (d : ℝ)) / (L * (d.totient : ℝ)) *
      ∑ m ∈ D.filter (fun m => d * m ≤ z ∧ Nat.Coprime m d), (1 / (m.totient : ℝ))
  have h1D : 1 ∈ D := by
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_refl 1, hz⟩, squarefree_one, Nat.coprime_one_left 30⟩
  have hD_pos : ∀ d ∈ D, 1 ≤ d ∧ d ≤ z ∧ Squarefree d ∧ Nat.Coprime d 30 := fun d hd => by
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    exact ⟨hd.1.1, hd.1.2, hd.2.1, hd.2.2⟩
  have hL_ge : 1 ≤ L := by
    have hterm : ∀ l ∈ D, (0 : ℝ) ≤ 1 / (l.totient : ℝ) := fun l _ => by positivity
    calc (1 : ℝ) = 1 / ((1 : ℕ).totient : ℝ) := by simp
      _ ≤ ∑ l ∈ D, (1 / (l.totient : ℝ)) := Finset.single_le_sum hterm h1D
  have hL_pos : 0 < L := lt_of_lt_of_le one_pos hL_ge
  have hlam1 : lam 1 = 1 := by
    have hf : D.filter (fun m => 1 * m ≤ z ∧ Nat.Coprime m 1) = D := by
      ext m; simp only [Finset.mem_filter, one_mul, Nat.coprime_one_right_eq_true, and_true]
      constructor
      · intro hm; exact hm.1
      · intro hm; exact ⟨hm, (hD_pos m hm).2.1⟩
    simp only [lam, hf, Nat.primeFactors_one, Finset.card_empty, pow_zero, Nat.cast_one,
      mul_one, Nat.totient_one, mu]
    rw [one_div, inv_mul_cancel₀ hL_pos.ne']
  have hlam_abs : ∀ d ∈ D, |lam d| ≤ 1 := fun d hd => by
    obtain ⟨hd1, hdz, hdSqf, hd30⟩ := hD_pos d hd
    have hd0 : d ≠ 0 := by omega
    have hdt_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd1)
    let Mset := D.filter (fun m => d * m ≤ z ∧ Nat.Coprime m d)
    have hprod_le_L : (∑ t ∈ d.divisors, (1 / (t.totient : ℝ))) *
        (∑ m ∈ Mset, (1 / (m.totient : ℝ))) ≤ L := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_product']
      let Pset := d.divisors ×ˢ Mset
      have hmap : Pset.image (fun x => x.1 * x.2) ⊆ D := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨⟨t, m⟩, htm, rfl⟩
        rw [Finset.mem_product, Nat.mem_divisors] at htm
        rcases htm with ⟨⟨htd, _⟩, hmM⟩
        rw [Finset.mem_filter] at hmM
        rcases hmM with ⟨hmD, hdmz, hcmd⟩
        obtain ⟨hm1, _, hmSqf, hm30⟩ := hD_pos m hmD
        have ht1 : 1 ≤ t := by
          by_contra h0; have : t = 0 := by omega
          rw [this, zero_dvd_iff] at htd; exact hd0 htd
        have htSqf : Squarefree t := hdSqf.squarefree_of_dvd htd
        have ht30 : Nat.Coprime t 30 := hd30.coprime_dvd_left htd
        have hctm : Nat.Coprime t m := hcmd.symm.coprime_dvd_left htd
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.mul_pos ht1 hm1, ?_⟩, ?_, ht30.mul_left hm30⟩
        · exact (Nat.mul_le_mul_right m (Nat.le_of_dvd hd1 htd)).trans hdmz
        · exact (Nat.squarefree_mul hctm).mpr ⟨htSqf, hmSqf⟩
      have hinj : ∀ x ∈ Pset, ∀ y ∈ Pset, x.1 * x.2 = y.1 * y.2 → x = y := by
        rintro ⟨t1, m1⟩ hx ⟨t2, m2⟩ hy heq
        rw [Finset.mem_product, Nat.mem_divisors] at hx hy
        have h1d := hx.1.1
        have h2d := hy.1.1
        rw [Finset.mem_filter] at hx hy
        have hc1 : Nat.Coprime d m1 := hx.2.2.2.symm
        have hc2 : Nat.Coprime d m2 := hy.2.2.2.symm
        have hg1 : Nat.gcd d (t1 * m1) = t1 := by
          rw [Nat.Coprime.gcd_mul_right_cancel_right t1 hc1.symm, Nat.gcd_eq_right h1d]
        have hg2 : Nat.gcd d (t2 * m2) = t2 := by
          rw [Nat.Coprime.gcd_mul_right_cancel_right t2 hc2.symm, Nat.gcd_eq_right h2d]
        have ht_eq : t1 = t2 := by rw [← hg1, heq, hg2]
        have ht1_pos : 0 < t1 := by
          by_contra h0; have : t1 = 0 := by omega
          rw [this, zero_dvd_iff] at h1d; exact hd0 h1d
        have hm_eq : m1 = m2 := by
          rw [ht_eq] at heq
          have : 0 < t2 := ht_eq ▸ ht1_pos
          exact mul_left_cancel₀ this.ne' heq
        exact Prod.ext ht_eq hm_eq
      have hterm_eq : ∀ x ∈ Pset, (1 / (x.1.totient : ℝ)) * (1 / (x.2.totient : ℝ)) =
          1 / ((x.1 * x.2).totient : ℝ) := fun ⟨t, m⟩ htm => by
        rw [Finset.mem_product, Nat.mem_divisors, Finset.mem_filter] at htm
        have hcop : Nat.Coprime t m := htm.2.2.2.symm.coprime_dvd_left htm.1.1
        rw [Nat.totient_mul hcop]; push_cast; ring
      calc ∑ x ∈ Pset, (1 / (x.1.totient : ℝ)) * (1 / (x.2.totient : ℝ))
          = ∑ x ∈ Pset, (1 / ((x.1 * x.2).totient : ℝ)) := Finset.sum_congr rfl hterm_eq
        _ = ∑ u ∈ Pset.image (fun x => x.1 * x.2), (1 / (u.totient : ℝ)) :=
            (Finset.sum_image (f := fun u : ℕ => 1 / (u.totient : ℝ)) hinj).symm
        _ ≤ ∑ u ∈ D, (1 / (u.totient : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hmap fun _ _ _ => by positivity
    rw [sum_inv_totient_divisors hdSqf hd0] at hprod_le_L
    have hmu_abs : |mu d| = 1 := by simp [mu]
    have hsum_nn : 0 ≤ ∑ m ∈ Mset, (1 / (m.totient : ℝ)) := Finset.sum_nonneg fun _ _ => by positivity
    have hlam_abs_eq : |lam d| = ((d : ℝ) / (L * (d.totient : ℝ))) *
        ∑ m ∈ Mset, (1 / (m.totient : ℝ)) := by
      simp only [lam, abs_mul, abs_div, hmu_abs, one_mul]
      have hd_nn : (0 : ℝ) ≤ (d : ℝ) := by positivity
      rw [abs_of_nonneg hd_nn, abs_of_nonneg hL_pos.le,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d.totient : ℝ)), abs_of_nonneg hsum_nn]
    rw [hlam_abs_eq]
    have h1 : ((d : ℝ) / (L * (d.totient : ℝ))) * ∑ m ∈ Mset, (1 / (m.totient : ℝ)) =
        (((d : ℝ) / (d.totient : ℝ)) * ∑ m ∈ Mset, (1 / (m.totient : ℝ))) / L := by ring
    rw [h1]
    exact (div_le_one hL_pos).mpr hprod_le_L
  have hdiag : ∀ l ∈ D, ∑ d ∈ D.filter (fun d => l ∣ d), lam d / (d : ℝ) =
      mu l / (L * (l.totient : ℝ)) := fun l hl => by
    obtain ⟨hl1, hlz, hlSqf, hl30⟩ := hD_pos l hl
    have hl0 : l ≠ 0 := by omega
    have hlt_pos : (0 : ℝ) < (l.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hl1)
    let P_pairs := (D ×ˢ D).filter (fun x => l * (x.1 * x.2) ≤ z ∧
      Nat.Coprime x.1 l ∧ Nat.Coprime x.2 (l * x.1))
    let S_inner := ∑ d ∈ D.filter (fun d => l ∣ d), lam d / (d : ℝ)
    have hstep1 : S_inner = (mu l / (L * (l.totient : ℝ))) *
        ∑ x ∈ P_pairs, mu x.1 / ((x.1.totient : ℝ) * (x.2.totient : ℝ)) := by
      have hbij : ∑ d ∈ D.filter (fun d => l ∣ d), lam d / (d : ℝ) =
          ∑ r ∈ D.filter (fun r => l * r ≤ z ∧ Nat.Coprime r l),
            (mu (l * r) / (L * ((l * r).totient : ℝ))) *
              ∑ m ∈ D.filter (fun m => l * r * m ≤ z ∧ Nat.Coprime m (l * r)),
                (1 / (m.totient : ℝ)) := by
        refine Finset.sum_bij (fun d _ => d / l) ?_ ?_ ?_ ?_
        · intro d hd
          rw [Finset.mem_filter] at hd
          rcases hd with ⟨hdD, hld⟩
          obtain ⟨hd1, hdz, hdSqf, hd30⟩ := hD_pos d hdD
          have hd0 : d ≠ 0 := by omega
          have hr1 : 1 ≤ d / l := Nat.div_pos (Nat.le_of_dvd hd1 hld) hl1
          have hrz : d / l ≤ z := (Nat.div_le_self d l).trans hdz
          have hrSqf : Squarefree (d / l) := hdSqf.squarefree_of_dvd (Nat.div_dvd_of_dvd hld)
          have hr30 : Nat.Coprime (d / l) 30 := hd30.coprime_dvd_left (Nat.div_dvd_of_dvd hld)
          have hcl : Nat.Coprime (d / l) l := (sqf_coprime_div hdSqf hld).symm
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr1, hrz⟩, hrSqf, hr30⟩, ?_, hcl⟩
          rw [Nat.mul_div_cancel' hld]; exact hdz
        · intro d1 hd1 d2 hd2 heq
          rw [Finset.mem_filter] at hd1 hd2
          have := congrArg (fun x => l * x) heq
          simpa [Nat.mul_div_cancel' hd1.2, Nat.mul_div_cancel' hd2.2] using this
        · intro r hr
          rw [Finset.mem_filter] at hr
          rcases hr with ⟨hrD, hlrz, hrl⟩
          obtain ⟨hr1, _, hrSqf, hr30⟩ := hD_pos r hrD
          refine ⟨l * r, ?_, Nat.mul_div_right r hl1⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hl1 hr1, hlrz⟩,
            (Nat.squarefree_mul hrl.symm).mpr ⟨hlSqf, hrSqf⟩, hl30.mul_left hr30⟩, dvd_mul_right l r⟩
        · intro d hd
          rw [Finset.mem_filter] at hd
          obtain ⟨hd1, _, _, _⟩ := hD_pos d hd.1
          have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd1
          have hdt_pos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd1)
          have hld_eq : l * (d / l) = d := Nat.mul_div_cancel' hd.2
          simp only [lam, hld_eq]
          field_simp [hd_pos.ne', hL_pos.ne', hdt_pos.ne']
      dsimp only [S_inner]
      rw [hbij]
      have hterm_r : ∀ r ∈ D.filter (fun r => l * r ≤ z ∧ Nat.Coprime r l),
          (mu (l * r) / (L * ((l * r).totient : ℝ))) *
            ∑ m ∈ D.filter (fun m => l * r * m ≤ z ∧ Nat.Coprime m (l * r)), (1 / (m.totient : ℝ)) =
          (mu l / (L * (l.totient : ℝ))) *
            ∑ m ∈ D.filter (fun m => l * r * m ≤ z ∧ Nat.Coprime m (l * r)),
              mu r / ((r.totient : ℝ) * (m.totient : ℝ)) := fun r hr => by
        rw [Finset.mem_filter] at hr
        obtain ⟨hr1, _, _, _⟩ := hD_pos r hr.1
        have hrl : Nat.Coprime l r := hr.2.2.symm
        have hmu_lr : mu (l * r) = mu l * mu r := by
          have hr0 : r ≠ 0 := by omega
          dsimp only [mu]
          rw [Nat.primeFactors_mul hl0 hr0,
            Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hrl), pow_add]
        have htot_lr : (l * r).totient = l.totient * r.totient := Nat.totient_mul hrl
        rw [hmu_lr, htot_lr]
        simp_rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.mem_filter] at hm
        obtain ⟨hm1, _, _, _⟩ := hD_pos m hm.1
        push_cast
        have hrt_pos : (0 : ℝ) < (r.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr1)
        have hmt_pos : (0 : ℝ) < (m.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hm1)
        field_simp [hL_pos.ne', hlt_pos.ne', hrt_pos.ne', hmt_pos.ne']
      rw [Finset.sum_congr rfl hterm_r, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_sigma']
      refine Finset.sum_bij (fun x _ => (x.1, x.2)) ?_ ?_ ?_ ?_
      · intro x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_sigma.mp hx
        obtain ⟨hx1D, _, hx1_cop⟩ := Finset.mem_filter.mp hx1
        obtain ⟨hx2D, hx2_mul, hx2_cop⟩ := Finset.mem_filter.mp hx2
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx1D, hx2D⟩,
          by simpa [mul_assoc] using hx2_mul, hx1_cop, hx2_cop⟩
      · rintro ⟨r1, m1⟩ _ ⟨r2, m2⟩ _ heq
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rfl
      · rintro ⟨r, m⟩ hrm
        rw [Finset.mem_filter, Finset.mem_product] at hrm
        obtain ⟨hm1, _, _, _⟩ := hD_pos m hrm.1.2
        have hlr : l * r ≤ l * (r * m) := Nat.mul_le_mul_left l (Nat.le_mul_of_pos_right r hm1)
        refine ⟨Sigma.mk r m, Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨hrm.1.1, hlr.trans hrm.2.1, hrm.2.2.1⟩,
          Finset.mem_filter.mpr ⟨hrm.1.2, by simpa [mul_assoc] using hrm.2.1, hrm.2.2.2⟩⟩, rfl⟩
      · intro x _; rfl
    have hstep2 : ∑ x ∈ P_pairs, mu x.1 / ((x.1.totient : ℝ) * (x.2.totient : ℝ)) =
        ∑ u ∈ D.filter (fun u => l * u ≤ z ∧ Nat.Coprime u l),
          (1 / (u.totient : ℝ)) * ∑ r ∈ u.divisors, mu r := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_sigma']
      refine Finset.sum_bij (fun x _ => Sigma.mk (x.1 * x.2) x.1) ?_ ?_ ?_ ?_
      · rintro ⟨r, m⟩ hrm
        rw [Finset.mem_filter, Finset.mem_product] at hrm
        obtain ⟨hr1, _, hrSqf, hr30⟩ := hD_pos r hrm.1.1
        obtain ⟨hm1, _, hmSqf, hm30⟩ := hD_pos m hrm.1.2
        have hcml : Nat.Coprime m l := hrm.2.2.2.coprime_dvd_right (dvd_mul_right l r)
        have hcmr : Nat.Coprime m r := hrm.2.2.2.coprime_dvd_right (dvd_mul_left r l)
        have hrmD : r * m ∈ D := Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hr1 hm1,
            (Nat.le_mul_of_pos_left (r * m) hl1).trans hrm.2.1⟩,
           (Nat.squarefree_mul hcmr.symm).mpr ⟨hrSqf, hmSqf⟩, hr30.mul_left hm30⟩
        exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨hrmD, hrm.2.1, hrm.2.2.1.mul_left hcml⟩,
          Nat.mem_divisors.mpr ⟨dvd_mul_right r m, (Nat.mul_pos hr1 hm1).ne'⟩⟩
      · rintro ⟨r1, m1⟩ h1 ⟨r2, m2⟩ h2 heq
        rw [Finset.mem_filter, Finset.mem_product] at h1 h2
        obtain ⟨hr1, _, _, _⟩ := hD_pos r1 h1.1.1
        have hr_eq : r1 = r2 := congrArg (fun x : Σ _ : ℕ, ℕ => x.2) heq
        have hmul_eq : r1 * m1 = r2 * m2 := congrArg Sigma.fst heq
        rw [hr_eq] at hmul_eq
        have hr2_pos : 0 < r2 := by omega
        exact Prod.ext hr_eq (mul_left_cancel₀ hr2_pos.ne' hmul_eq)
      · rintro ⟨u, r⟩ hur
        rw [Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors] at hur
        rcases hur with ⟨⟨huD, hluz, hcul⟩, hru, hu0⟩
        obtain ⟨hu1, huz, huSqf, hu30⟩ := hD_pos u huD
        have hr1 : 1 ≤ r := by
          by_contra h0; have : r = 0 := by omega
          rw [this, zero_dvd_iff] at hru; exact hu0 hru
        have hm1 : 1 ≤ u / r := Nat.div_pos (Nat.le_of_dvd hu1 hru) hr1
        have hrD : r ∈ D := Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hr1, (Nat.le_of_dvd hu1 hru).trans huz⟩,
           huSqf.squarefree_of_dvd hru, hu30.coprime_dvd_left hru⟩
        have hmD : u / r ∈ D := Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hm1, (Nat.div_le_self u r).trans huz⟩,
           huSqf.squarefree_of_dvd (Nat.div_dvd_of_dvd hru),
           hu30.coprime_dvd_left (Nat.div_dvd_of_dvd hru)⟩
        have hcr_m : Nat.Coprime (u / r) r := (sqf_coprime_div huSqf hru).symm
        have hcr_l : Nat.Coprime r l := hcul.coprime_dvd_left hru
        have hcm_l : Nat.Coprime (u / r) l := hcul.coprime_dvd_left (Nat.div_dvd_of_dvd hru)
        refine ⟨(r, u / r), ?_, Sigma.ext (Nat.mul_div_cancel' hru) (by simp)⟩
        rw [Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨hrD, hmD⟩, ?_, hcr_l, hcm_l.mul_right hcr_m⟩
        rwa [Nat.mul_div_cancel' hru]
      · rintro ⟨r, m⟩ hrm
        rw [Finset.mem_filter, Finset.mem_product] at hrm
        have hcmr : Nat.Coprime r m := (hrm.2.2.2.coprime_dvd_right (dvd_mul_left r l)).symm
        rw [Nat.totient_mul hcmr]; push_cast; ring
    have hstep3 : ∑ u ∈ D.filter (fun u => l * u ≤ z ∧ Nat.Coprime u l),
        (1 / (u.totient : ℝ)) * ∑ r ∈ u.divisors, mu r = 1 := by
      have hterm_u : ∀ u ∈ D.filter (fun u => l * u ≤ z ∧ Nat.Coprime u l),
          (1 / (u.totient : ℝ)) * ∑ r ∈ u.divisors, mu r = if u = 1 then (1 : ℝ) else 0 := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨hu1, _, huSqf, _⟩ := hD_pos u hu.1
        rw [sum_mu_divisors_sqf huSqf (by omega)]
        by_cases hu_eq : u = 1
        · subst hu_eq; simp
        · simp [hu_eq]
      rw [Finset.sum_congr rfl hterm_u, Finset.sum_ite_eq']
      have h1mem : 1 ∈ D.filter (fun u => l * u ≤ z ∧ Nat.Coprime u l) :=
        Finset.mem_filter.mpr ⟨h1D, by simpa using hlz, Nat.coprime_one_left l⟩
      simp [h1mem]
    change S_inner = mu l / (L * (l.totient : ℝ))
    rw [hstep1, hstep2, hstep3, mul_one]
  let P30 := (Finset.Icc 1 X).filter (fun p => p.Prime ∧
    (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))
  let A30 := (Finset.Icc 1 X).filter (fun n => n % 30 = 17 ∨ n % 30 = 23 ∨ n % 30 = 29)
  have hP_split : P30.card ≤ z + (P30.filter (fun p => z < p)).card := by
    have hsub : P30 = P30.filter (fun p => p ≤ z) ∪ P30.filter (fun p => z < p) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter]
      by_cases hpz : p ≤ z
      · simp [hpz, show ¬ z < p by omega]
      · simp [hpz, show z < p by omega]
    have hle_z : (P30.filter (fun p => p ≤ z)).card ≤ z := by
      have hs : P30.filter (fun p => p ≤ z) ⊆ Finset.Icc 1 z := fun p hp => by
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hp
        exact Finset.mem_Icc.mpr ⟨hp.1.1.1, hp.2⟩
      exact (Finset.card_le_card hs).trans (by simp)
    have hcard_le := Finset.card_union_le (P30.filter (fun p => p ≤ z)) (P30.filter (fun p => z < p))
    rw [← hsub] at hcard_le
    omega
  have hP_le_R : ((P30.filter (fun p => z < p)).card : ℝ) ≤
      ∑ n ∈ A30, (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 := by
    have hP_sub : P30.filter (fun p => z < p) ⊆ A30 := fun p hp => by
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      exact Finset.mem_filter.mpr ⟨hp.1.1, hp.1.2.2⟩
    have hwt : ∀ n ∈ P30.filter (fun p => z < p),
        (1 : ℝ) ≤ (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 := fun p hp => by
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      have hp_prime : p.Prime := hp.1.2.1
      have hzp : z < p := hp.2
      have hterm : ∀ d ∈ D, (if d ∣ p then lam d else 0) = (if d = 1 then (1 : ℝ) else 0) := by
        intro d hd
        obtain ⟨hd1, hdz, _, _⟩ := hD_pos d hd
        by_cases hdp : d ∣ p
        · have hd1_eq : d = 1 := by
            rcases (Nat.dvd_prime hp_prime).mp hdp with rfl | rfl
            · rfl
            · omega
          rw [hd1_eq]; simp [hlam1]
        · have hdne : d ≠ 1 := fun h => hdp (h ▸ one_dvd p)
          simp [hdp, hdne]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
      simp [h1D]
    calc ((P30.filter (fun p => z < p)).card : ℝ)
        = ∑ _n ∈ P30.filter (fun p => z < p), (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ P30.filter (fun p => z < p), (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 :=
          Finset.sum_le_sum hwt
      _ ≤ ∑ n ∈ A30, (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hP_sub fun _ _ _ => sq_nonneg _
  have hQ_expand : ∑ n ∈ A30, (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 =
      ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 *
        ((A30.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ) := by
    have hsq : ∀ n : ℕ, (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 =
        ∑ d1 ∈ D, ∑ d2 ∈ D, (if Nat.lcm d1 d2 ∣ n then lam d1 * lam d2 else 0) := fun n => by
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d1 _ => Finset.sum_congr rfl fun d2 _ => ?_
      by_cases h1 : d1 ∣ n <;> by_cases h2 : d2 ∣ n <;> simp [h1, h2, Nat.lcm_dvd_iff]
    rw [Finset.sum_congr rfl (fun n _ => hsq n), Finset.sum_comm]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d2 _ => ?_
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hQ_bound : ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 *
      ((A30.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ) ≤
      (X : ℝ) / (10 : ℝ) * (∑ d1 ∈ D, ∑ d2 ∈ D, (lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ)) +
      3 * (D.card : ℝ) ^ 2 := by
    have hpair : ∀ d1 ∈ D, ∀ d2 ∈ D,
        lam d1 * lam d2 * ((A30.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ) ≤
        (X : ℝ) / 10 * ((lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ)) + 3 := by
      intro d1 hd1 d2 hd2
      obtain ⟨h11, _, _, h130⟩ := hD_pos d1 hd1
      obtain ⟨h21, _, _, h230⟩ := hD_pos d2 hd2
      have hm1 : 1 ≤ Nat.lcm d1 d2 := Nat.one_le_iff_ne_zero.mpr (Nat.lcm_ne_zero (by omega) (by omega))
      have hm30 : Nat.Coprime (Nat.lcm d1 d2) 30 := (h130.mul_left h230).coprime_dvd_left (Nat.lcm_dvd_mul d1 d2)
      have herr := block_count_mod30_err X (Nat.lcm d1 d2) hm1 hm30
      have hA_eq : A30.filter (fun n => Nat.lcm d1 d2 ∣ n) =
          (Finset.Icc 1 X).filter (fun n =>
            (n % 30 = 17 ∨ n % 30 = 23 ∨ n % 30 = 29) ∧ Nat.lcm d1 d2 ∣ n) := by
        ext n; simp only [A30, Finset.mem_filter]; tauto
      rw [hA_eq]
      have hlam_p : |lam d1 * lam d2| ≤ 1 := by
        rw [abs_mul]; nlinarith [hlam_abs d1 hd1, hlam_abs d2 hd2, abs_nonneg (lam d1), abs_nonneg (lam d2)]
      let err := (((Finset.Icc 1 X).filter (fun n =>
        (n % 30 = 17 ∨ n % 30 = 23 ∨ n % 30 = 29) ∧ Nat.lcm d1 d2 ∣ n)).card : ℝ) -
        (X : ℝ) / (10 * (Nat.lcm d1 d2 : ℝ))
      have herr_mul : lam d1 * lam d2 * err ≤ 3 := by
        have h1 : lam d1 * lam d2 * err ≤ |lam d1 * lam d2| * |err| := by
          rw [← abs_mul]; exact le_abs_self _
        have h2 : |lam d1 * lam d2| * |err| ≤ 1 * 3 :=
          mul_le_mul hlam_p herr (abs_nonneg _) (by positivity)
        linarith
      have hsub_eq : lam d1 * lam d2 * (((Finset.Icc 1 X).filter (fun n =>
          (n % 30 = 17 ∨ n % 30 = 23 ∨ n % 30 = 29) ∧ Nat.lcm d1 d2 ∣ n)).card : ℝ) -
          (X : ℝ) / 10 * ((lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ)) = lam d1 * lam d2 * err := by
        dsimp only [err]; ring
      linarith [hsub_eq, herr_mul]
    calc ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 * ((A30.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ)
        ≤ ∑ d1 ∈ D, ∑ d2 ∈ D, ((X : ℝ) / 10 * ((lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ)) + 3) :=
          Finset.sum_le_sum fun d1 hd1 => Finset.sum_le_sum fun d2 hd2 => hpair d1 hd1 d2 hd2
      _ = (X : ℝ) / 10 * (∑ d1 ∈ D, ∑ d2 ∈ D, (lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ)) +
            3 * (D.card : ℝ) ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
          ring
  have hQ_eval : ∑ d1 ∈ D, ∑ d2 ∈ D, (lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ) = 1 / L := by
    have hsplit_lcm : ∀ d1 ∈ D, ∀ d2 ∈ D,
        (lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ) =
        ∑ l ∈ D, (if l ∣ d1 ∧ l ∣ d2 then
          (l.totient : ℝ) * (lam d1 / (d1 : ℝ)) * (lam d2 / (d2 : ℝ)) else 0) := by
      intro d1 hd1 d2 hd2
      obtain ⟨h11, h1z, h1Sqf, h130⟩ := hD_pos d1 hd1
      obtain ⟨h21, _, _, _⟩ := hD_pos d2 hd2
      have hgcd_ne0 : Nat.gcd d1 d2 ≠ 0 := Nat.gcd_ne_zero_left (by omega)
      have hgcd_lcm : (Nat.gcd d1 d2 : ℝ) * (Nat.lcm d1 d2 : ℝ) = (d1 : ℝ) * (d2 : ℝ) := by
        exact_mod_cast Nat.gcd_mul_lcm d1 d2
      have hd1_ne0 : (d1 : ℝ) ≠ 0 := by positivity
      have hd2_ne0 : (d2 : ℝ) ≠ 0 := by positivity
      have hlcm_ne0 : (Nat.lcm d1 d2 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero (by omega) (by omega))
      have h1 : (lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ) =
          (Nat.gcd d1 d2 : ℝ) * ((lam d1 / (d1 : ℝ)) * (lam d2 / (d2 : ℝ))) := by
        field_simp [hlcm_ne0, hd1_ne0, hd2_ne0]
        linear_combination (lam d1 * lam d2) * hgcd_lcm.symm
      rw [h1]
      have hdiv_eq : (Nat.gcd d1 d2).divisors = D.filter (fun l => l ∣ d1 ∧ l ∣ d2) := by
        ext l
        rw [Nat.mem_divisors, Nat.dvd_gcd_iff, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hl_d1, hl_d2⟩, _⟩
          have hl1 : 1 ≤ l := by
            by_contra h0; have : l = 0 := by omega
            rw [this, zero_dvd_iff] at hl_d1; omega
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl1, (Nat.le_of_dvd h11 hl_d1).trans h1z⟩,
            h1Sqf.squarefree_of_dvd hl_d1, h130.coprime_dvd_left hl_d1⟩, hl_d1, hl_d2⟩
        · rintro ⟨_, hl_d1, hl_d2⟩
          exact ⟨⟨hl_d1, hl_d2⟩, hgcd_ne0⟩
      have htot : (Nat.gcd d1 d2 : ℝ) = ∑ l ∈ D.filter (fun l => l ∣ d1 ∧ l ∣ d2), (l.totient : ℝ) := by
        rw [← hdiv_eq]; exact_mod_cast (Nat.sum_totient (Nat.gcd d1 d2)).symm
      rw [htot, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun d1 hd1 => Finset.sum_congr rfl fun d2 hd2 => hsplit_lcm d1 hd1 d2 hd2]
    have hswap1 : (∑ d1 ∈ D, ∑ d2 ∈ D, ∑ l ∈ D, (if l ∣ d1 ∧ l ∣ d2 then
        (l.totient : ℝ) * (lam d1 / (d1 : ℝ)) * (lam d2 / (d2 : ℝ)) else 0)) =
        ∑ l ∈ D, (l.totient : ℝ) * (∑ d1 ∈ D.filter (fun d => l ∣ d), lam d1 / (d1 : ℝ)) *
          (∑ d2 ∈ D.filter (fun d => l ∣ d), lam d2 / (d2 : ℝ)) := by
      have h1 : ∀ d1 ∈ D, (∑ d2 ∈ D, ∑ l ∈ D, (if l ∣ d1 ∧ l ∣ d2 then
          (l.totient : ℝ) * (lam d1 / (d1 : ℝ)) * (lam d2 / (d2 : ℝ)) else 0)) =
          ∑ l ∈ D, (if l ∣ d1 then (l.totient : ℝ) * (lam d1 / (d1 : ℝ)) *
            ∑ d2 ∈ D.filter (fun d => l ∣ d), lam d2 / (d2 : ℝ) else 0) := by
        intro d1 _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        by_cases hld1 : l ∣ d1
        · simp only [hld1, true_and, ↓reduceIte, Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d2 _ => ?_
          split_ifs <;> ring
        · simp only [hld1, false_and, ↓reduceIte, Finset.sum_const_zero]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.sum_filter, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [hswap1]
    have hterm_l : ∀ l ∈ D,
        (l.totient : ℝ) * (∑ d1 ∈ D.filter (fun d => l ∣ d), lam d1 / (d1 : ℝ)) *
          (∑ d2 ∈ D.filter (fun d => l ∣ d), lam d2 / (d2 : ℝ)) =
        (1 / L ^ 2) * (1 / (l.totient : ℝ)) := fun l hl => by
      obtain ⟨hl1, _, _, _⟩ := hD_pos l hl
      have hlt_pos : (0 : ℝ) < (l.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hl1)
      rw [hdiag l hl]
      have hmu2 : mu l * mu l = 1 := by simp [mu, ← pow_add, ← two_mul]
      calc (l.totient : ℝ) * (mu l / (L * (l.totient : ℝ))) * (mu l / (L * (l.totient : ℝ)))
          = (mu l * mu l) * ((l.totient : ℝ) / ((L * (l.totient : ℝ)) * (L * (l.totient : ℝ)))) := by ring
        _ = 1 * ((l.totient : ℝ) / ((L * (l.totient : ℝ)) * (L * (l.totient : ℝ)))) := by rw [hmu2]
        _ = (1 / L ^ 2) * (1 / (l.totient : ℝ)) := by field_simp [hL_pos.ne', hlt_pos.ne']
    rw [Finset.sum_congr rfl hterm_l, ← Finset.mul_sum]
    change (1 / L ^ 2) * L = 1 / L
    field_simp [hL_pos.ne']
  have hP_cardR : (P30.card : ℝ) ≤ (z : ℝ) + ((P30.filter (fun p => z < p)).card : ℝ) := by
    exact_mod_cast hP_split
  have hR_bound : ((P30.filter (fun p => z < p)).card : ℝ) ≤
      (X : ℝ) / 10 * (1 / L) + 3 * (D.card : ℝ) ^ 2 := by
    calc ((P30.filter (fun p => z < p)).card : ℝ)
        ≤ ∑ n ∈ A30, (∑ d ∈ D, (if d ∣ n then lam d else 0)) ^ 2 := hP_le_R
      _ = ∑ d1 ∈ D, ∑ d2 ∈ D, lam d1 * lam d2 *
            ((A30.filter (fun n => Nat.lcm d1 d2 ∣ n)).card : ℝ) := hQ_expand
      _ ≤ (X : ℝ) / 10 * (∑ d1 ∈ D, ∑ d2 ∈ D, (lam d1 * lam d2) / (Nat.lcm d1 d2 : ℝ)) +
            3 * (D.card : ℝ) ^ 2 := hQ_bound
      _ = (X : ℝ) / 10 * (1 / L) + 3 * (D.card : ℝ) ^ 2 := by rw [hQ_eval]
  calc (P30.card : ℝ) ≤ (z : ℝ) + ((P30.filter (fun p => z < p)).card : ℝ) := hP_cardR
    _ ≤ (z : ℝ) + ((X : ℝ) / 10 * (1 / L) + 3 * (D.card : ℝ) ^ 2) := by linarith [hR_bound]
    _ = (z : ℝ) + (X : ℝ) / (10 * L) + 3 * (D.card : ℝ) ^ 2 := by ring

/- ## Section 3: Finite L(z) bounds, analytic L(z) lower bound, and asymptotic pi30 bounds -/

private lemma d_eq_fast {z : ℕ} (hz : z ≤ 300) :
    (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30) =
    (Finset.Icc 1 z).filter (fun d => Nat.Coprime d 30 ∧ d % 49 ≠ 0 ∧ d % 121 ≠ 0 ∧
      d % 169 ≠ 0 ∧ d % 289 ≠ 0) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, hdSqf, hd30⟩
    refine ⟨h1, hd30, ?_, ?_, ?_, ?_⟩
    · intro h49; exact (by decide : ¬ IsUnit 7) (hdSqf 7 (by omega))
    · intro h121; exact (by decide : ¬ IsUnit 11) (hdSqf 11 (by omega))
    · intro h169; exact (by decide : ¬ IsUnit 13) (hdSqf 13 (by omega))
    · intro h289; exact (by decide : ¬ IsUnit 17) (hdSqf 17 (by omega))
  · rintro ⟨h1, hd30, h49, h121, h169, h289⟩
    refine ⟨h1, ?_, hd30⟩
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp ⟨k, hpk⟩
    have hp17 : p ≤ 17 := by
      by_contra hp18
      have : 18 ≤ p := by omega
      have h18 : 324 ≤ p * p := by nlinarith
      have hpos_k : 1 ≤ k := by
        by_contra hk; have : k = 0 := by omega
        rw [this, mul_zero] at hpk; omega
      have : 324 ≤ d := by nlinarith
      omega
    have hndvd : p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 := by
      refine ⟨?_, ?_, ?_⟩ <;> intro hpeq <;> subst hpeq
      · have : 2 ∣ Nat.gcd d 30 := Nat.dvd_gcd ⟨2 * k, by linarith⟩ (by decide)
        rw [hd30] at this; exact absurd this (by decide)
      · have : 3 ∣ Nat.gcd d 30 := Nat.dvd_gcd ⟨3 * k, by linarith⟩ (by decide)
        rw [hd30] at this; exact absurd this (by decide)
      · have : 5 ∣ Nat.gcd d 30 := Nat.dvd_gcd ⟨5 * k, by linarith⟩ (by decide)
        rw [hd30] at this; exact absurd this (by decide)
    have hcases : p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 := by
      have hpr := hp
      have hplt : p < 18 := by omega
      interval_cases p <;> first | exact absurd hpr (by decide) | omega
    rcases hcases with rfl | rfl | rfl | rfl <;> omega

private lemma sum_inv_totient_ge_of_nat (D : Finset ℕ) (S : ℕ)
    (hS : S ≤ ∑ d ∈ D, 1000000 / d.totient) :
    (S : ℝ) / 1000000 ≤ ∑ d ∈ D, (1 / (d.totient : ℝ)) := by
  have h1 : (S : ℝ) ≤ ∑ d ∈ D, (1000000 / d.totient : ℕ) := by exact_mod_cast hS
  have h2 : ∀ d ∈ D, ((1000000 / d.totient : ℕ) : ℝ) ≤ 1000000 * (1 / (d.totient : ℝ)) := fun d _ => by
    by_cases hdt : d.totient = 0
    · simp [hdt]
    · have hpos : (0 : ℝ) < (d.totient : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdt)
      rw [mul_one_div, le_div_iff₀ hpos]
      exact_mod_cast Nat.div_mul_le_self 1000000 d.totient
  have h3 : (S : ℝ) ≤ 1000000 * ∑ d ∈ D, (1 / (d.totient : ℝ)) := by
    rw [Finset.mul_sum]
    push_cast at h1
    exact h1.trans (Finset.sum_le_sum h2)
  linarith

private lemma d29_bound :
    ((Finset.Icc 1 29).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)).card = 8 ∧
    (1549222 : ℝ) / 1000000 ≤
      ∑ d ∈ (Finset.Icc 1 29).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
        (1 / (d.totient : ℝ)) := by
  rw [d_eq_fast (by decide)]
  let D := (Finset.Icc 1 29).filter (fun d => Nat.Coprime d 30 ∧ d % 49 ≠ 0 ∧ d % 121 ≠ 0 ∧
    d % 169 ≠ 0 ∧ d % 289 ≠ 0)
  have hdec : D.card = 8 ∧ ∑ d ∈ D, 1000000 / d.totient = 1549222 := by decide +kernel
  exact ⟨hdec.1, sum_inv_totient_ge_of_nat D 1549222 (le_of_eq hdec.2.symm)⟩

private lemma d100_bound :
    ((Finset.Icc 1 100).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)).card = 25 ∧
    (1854689 : ℝ) / 1000000 ≤
      ∑ d ∈ (Finset.Icc 1 100).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
        (1 / (d.totient : ℝ)) := by
  rw [d_eq_fast (by decide)]
  let D := (Finset.Icc 1 100).filter (fun d => Nat.Coprime d 30 ∧ d % 49 ≠ 0 ∧ d % 121 ≠ 0 ∧
    d % 169 ≠ 0 ∧ d % 289 ≠ 0)
  have hdec : D.card = 25 ∧ ∑ d ∈ D, 1000000 / d.totient = 1854689 := by decide +kernel
  exact ⟨hdec.1, sum_inv_totient_ge_of_nat D 1854689 (le_of_eq hdec.2.symm)⟩

private lemma d300_bound :
    ((Finset.Icc 1 300).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)).card = 76 ∧
    (2151904 : ℝ) / 1000000 ≤
      ∑ d ∈ (Finset.Icc 1 300).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
        (1 / (d.totient : ℝ)) := by
  rw [d_eq_fast (by decide)]
  let D := (Finset.Icc 1 300).filter (fun d => Nat.Coprime d 30 ∧ d % 49 ≠ 0 ∧ d % 121 ≠ 0 ∧
    d % 169 ≠ 0 ∧ d % 289 ≠ 0)
  have hdec : D.card = 76 ∧ ∑ d ∈ D, 1000000 / d.totient = 2151904 := by decide +kernel
  exact ⟨hdec.1, sum_inv_totient_ge_of_nat D 2151904 (le_of_eq hdec.2.symm)⟩

private lemma log_lt_of_pow_lt {a : ℝ} {p q : ℕ} (ha : 0 < a) (hq : 0 < q)
    (h : a ^ q < (2.7182818283 : ℝ) ^ p) :
    Real.log a < (p : ℝ) / (q : ℝ) := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hexp : Real.exp 1 ^ p = Real.exp (p : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
  have hlt : a ^ q < Real.exp (p : ℝ) := by
    by_cases hp : p = 0
    · subst hp; simp at h ⊢; exact h
    · exact h.trans ((pow_lt_pow_left₀ he (by norm_num) hp).trans_eq hexp)
  have hlog := Real.log_lt_log (pow_pos ha q) hlt
  rw [Real.log_pow, Real.log_exp] at hlog
  exact (lt_div_iff₀ (Nat.cast_pos.mpr hq)).mpr (by linarith)

private lemma log_ten_gt : (23 / 10 : ℝ) < Real.log 10 := by
  have he : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have hpow : (2.7182818286 : ℝ) ^ 23 < (10 : ℝ) ^ 10 := by norm_num
  have hexp : Real.exp (23 : ℕ) < (10 : ℝ) ^ 10 := by
    have h1 : Real.exp 1 ^ 23 = Real.exp (23 : ℕ) := by rw [← Real.exp_nat_mul, mul_one]
    exact (h1 ▸ pow_lt_pow_left₀ he (Real.exp_pos 1).le (by decide)).trans hpow
  have hlog := Real.log_lt_log (Real.exp_pos _) hexp
  rw [Real.log_exp, Real.log_pow] at hlog
  push_cast at hlog
  linarith

private lemma sqf_prod_of_primes (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    Squarefree (∏ p ∈ F, p) ∧ (∏ p ∈ F, p).primeFactors = F ∧
      (∏ p ∈ F, p).totient = ∏ p ∈ F, (p - 1) := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    have hp := hF p (Finset.mem_insert_self p s)
    obtain ⟨ih1, ih2, ih3⟩ := ih (fun q hq => hF q (Finset.mem_insert_of_mem hq))
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hqs => ?_
      have hq := hF q (Finset.mem_insert_of_mem hqs)
      exact (hp.coprime_iff_not_dvd).mpr fun hdiv => by
        have := (Nat.Prime.dvd_iff_eq hq hp.ne_one).mp hdiv
        subst this; exact hps hqs
    have hs0 : (∏ q ∈ s, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hqs =>
      (hF q (Finset.mem_insert_of_mem hqs)).ne_zero
    rw [Finset.prod_insert hps, Finset.prod_insert hps]
    refine ⟨?_, ?_, ?_⟩
    · exact (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, ih1⟩
    · rw [Nat.primeFactors_mul hp.ne_zero hs0, hp.primeFactors, ih2, Finset.singleton_union]
    · rw [Nat.totient_mul hcop, Nat.totient_prime hp, ih3]

private lemma sum_inv_primes_subset_le (z : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∀ M : Finset ℕ, (∀ m ∈ M, 1 ≤ m ∧ m ≤ z ∧ m.primeFactors ⊆ S) →
      ∑ m ∈ M, (1 / (m : ℝ)) ≤ ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) := by
  induction S using Finset.induction_on with
  | empty =>
    intro M hM
    have hsub : M ⊆ {1} := fun m hm => by
      obtain ⟨hm1, _, hmp⟩ := hM m hm
      rw [Finset.subset_empty] at hmp
      have hm_eq : m = 1 := by
        by_contra hm_ne1
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hm_ne1
        have hmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩
        rw [hmp] at hmem; simp at hmem
      simp [hm_eq]
    calc ∑ m ∈ M, (1 / (m : ℝ)) ≤ ∑ m ∈ ({1} : Finset ℕ), (1 / (m : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 1 := by simp
      _ = ∏ p ∈ ∅, ((p : ℝ) / ((p : ℝ) - 1)) := by simp
  | @insert p s hps ih =>
    intro M hM
    have hp := hS p (Finset.mem_insert_self p s)
    have hss : ∀ q ∈ s, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hmaps : ∀ m ∈ M, padicValNat p m ∈ Finset.range (z + 1) := fun m hm => by
      obtain ⟨hm1, hmz, _⟩ := hM m hm
      rw [Finset.mem_range]
      have hpow : p ^ padicValNat p m ∣ m := pow_padicValNat_dvd
      have hle_m : p ^ padicValNat p m ≤ m := Nat.le_of_dvd hm1 hpow
      have hk_lt : padicValNat p m < p ^ padicValNat p m := by
        calc padicValNat p m < 2 ^ padicValNat p m := Nat.lt_two_pow_self
          _ ≤ p ^ padicValNat p m := Nat.pow_le_pow_left hp.two_le _
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hfiber : ∀ k ∈ Finset.range (z + 1),
        ∑ m ∈ M.filter (fun m => padicValNat p m = k), (1 / (m : ℝ)) ≤
          (1 / (p : ℝ)) ^ k * ∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1)) := by
      intro k _
      let Mk := M.filter (fun m => padicValNat p m = k)
      let Mk' := Mk.image (fun m => m / p ^ k)
      have hM'_prop : ∀ m' ∈ Mk', 1 ≤ m' ∧ m' ≤ z ∧ m'.primeFactors ⊆ s := by
        intro m' hm'
        rcases Finset.mem_image.mp hm' with ⟨m, hm, rfl⟩
        rw [Finset.mem_filter] at hm
        obtain ⟨hm1, hmz, hmp⟩ := hM m hm.1
        have hpk : p ^ k ∣ m := hm.2 ▸ pow_padicValNat_dvd
        have hpk_pos : 0 < p ^ k := pow_pos hp.pos k
        refine ⟨Nat.div_pos (Nat.le_of_dvd hm1 hpk) hpk_pos, (Nat.div_le_self m _).trans hmz, ?_⟩
        intro q hq
        have hqm : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors hq,
           (Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd hpk), by omega⟩
        rcases Finset.mem_insert.mp (hmp hqm) with rfl | hqs
        · exfalso
          have hp_m' : q ∣ m / q ^ k := Nat.dvd_of_mem_primeFactors hq
          have hpk1 : q ^ (k + 1) ∣ m := by
            have := mul_dvd_mul_left (q ^ k) hp_m'
            rwa [Nat.mul_div_cancel' hpk, ← pow_succ] at this
          have hle_k1 : k + 1 ≤ padicValNat q m := by
            have : Fact q.Prime := ⟨hp⟩
            exact (padicValNat_dvd_iff_le (by omega)).mp hpk1
          omega
        · exact hqs
      have hinj : ∀ m1 ∈ Mk, ∀ m2 ∈ Mk, m1 / p ^ k = m2 / p ^ k → m1 = m2 := by
        intro m1 hm1 m2 hm2 heq
        rw [Finset.mem_filter] at hm1 hm2
        have h1 : p ^ k ∣ m1 := hm1.2 ▸ pow_padicValNat_dvd
        have h2 : p ^ k ∣ m2 := hm2.2 ▸ pow_padicValNat_dvd
        rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
      have hterm : ∀ m ∈ Mk, (1 / (m : ℝ)) = (1 / (p : ℝ)) ^ k * (1 / ((m / p ^ k : ℕ) : ℝ)) := by
        intro m hm
        rw [Finset.mem_filter] at hm
        have h1 : p ^ k ∣ m := hm.2 ▸ pow_padicValNat_dvd
        have hmul : (m : ℝ) = (p : ℝ) ^ k * ((m / p ^ k : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' h1).symm
        rw [hmul]; simp [mul_comm]
      calc ∑ m ∈ Mk, (1 / (m : ℝ))
          = (1 / (p : ℝ)) ^ k * ∑ m ∈ Mk, (1 / ((m / p ^ k : ℕ) : ℝ)) := by
              rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
        _ = (1 / (p : ℝ)) ^ k * ∑ m' ∈ Mk', (1 / (m' : ℝ)) := by
              rw [Finset.sum_image hinj]
        _ ≤ (1 / (p : ℝ)) ^ k * ∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1)) :=
              mul_le_mul_of_nonneg_left (ih hss Mk' hM'_prop) (by positivity)
    have hgeom : ∑ k ∈ Finset.range (z + 1), (1 / (p : ℝ)) ^ k ≤ (p : ℝ) / ((p : ℝ) - 1) := by
      have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
      have hr_lt : (1 / (p : ℝ)) < 1 := div_lt_one (by positivity) |>.mpr hp1
      have h1r : 0 < 1 - (1 / (p : ℝ)) := sub_pos.mpr hr_lt
      rw [geom_sum_eq hr_lt.ne]
      have hnum : (1 / (p : ℝ)) ^ (z + 1) - 1 ≥ -1 := by
        have : 0 ≤ (1 / (p : ℝ)) ^ (z + 1) := by positivity
        linarith
      have hsub : 1 - (1 / (p : ℝ)) ^ (z + 1) ≤ 1 := by linarith
      calc ((1 / (p : ℝ)) ^ (z + 1) - 1) / (1 / (p : ℝ) - 1)
          = (1 - (1 / (p : ℝ)) ^ (z + 1)) / (1 - 1 / (p : ℝ)) := by
              rw [← neg_sub (1 : ℝ) ((1 / (p : ℝ)) ^ (z + 1)), ← neg_sub (1 : ℝ) (1 / (p : ℝ)), neg_div_neg_eq]
        _ ≤ 1 / (1 - 1 / (p : ℝ)) := div_le_div_of_nonneg_right hsub h1r.le
        _ = (p : ℝ) / ((p : ℝ) - 1) := by field_simp [show (p : ℝ) ≠ 0 by positivity]
    calc ∑ k ∈ Finset.range (z + 1), ∑ m ∈ M.filter (fun m => padicValNat p m = k), (1 / (m : ℝ))
        ≤ ∑ k ∈ Finset.range (z + 1), (1 / (p : ℝ)) ^ k * ∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1)) :=
          Finset.sum_le_sum hfiber
      _ = (∑ k ∈ Finset.range (z + 1), (1 / (p : ℝ)) ^ k) * ∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1)) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ ((p : ℝ) / ((p : ℝ) - 1)) * ∏ q ∈ s, ((q : ℝ) / ((q : ℝ) - 1)) := by
          refine mul_le_mul_of_nonneg_right hgeom ?_
          refine Finset.prod_nonneg fun q hq => ?_
          have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (hss q hq).one_lt
          have : (0 : ℝ) < (q : ℝ) - 1 := by linarith
          positivity
      _ = ∏ q ∈ insert p s, ((q : ℝ) / ((q : ℝ) - 1)) :=
          (Finset.prod_insert (f := fun q : ℕ => (q : ℝ) / ((q : ℝ) - 1)) hps).symm

private lemma analytic_L_lower {z : ℕ} (hz : 10 ≤ z) :
    Real.log ((z : ℝ) + 1) + 1 / 2 ≤
      (15 / 4 : ℝ) * ∑ d ∈ (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
        (1 / (d.totient : ℝ)) := by
  let D := (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)
  let skel : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors.filter (fun p => Nat.Coprime p 30), p
  have hmaps : ∀ n ∈ Finset.Icc 1 z, skel n ∈ D := fun n hn => by
    rw [Finset.mem_Icc] at hn
    let Fn := n.primeFactors.filter (fun p => Nat.Coprime p 30)
    have hFn : ∀ p ∈ Fn, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    obtain ⟨hsqf, _, _⟩ := sqf_prod_of_primes Fn hFn
    have hcop : Nat.Coprime (skel n) 30 := Nat.Coprime.prod_left fun p hp =>
      (Finset.mem_filter.mp hp).2
    have hdvd : skel n ∣ n := by
      have hn0 : n ≠ 0 := by omega
      have : ∀ F : Finset ℕ, (∀ p ∈ F, p.Prime ∧ p ∣ n) → (∏ p ∈ F, p) ∣ n := fun F hF => by
        induction F using Finset.induction_on with
        | empty => simp
        | @insert p s hps ih =>
          rw [Finset.prod_insert hps]
          have hps' := ih fun q hq => hF q (Finset.mem_insert_of_mem hq)
          have hpp := hF p (Finset.mem_insert_self p s)
          have hc : Nat.Coprime p (∏ q ∈ s, q) := Nat.Coprime.prod_right fun q hq => by
            have hqp := hF q (Finset.mem_insert_of_mem hq)
            exact (hpp.1.coprime_iff_not_dvd).mpr fun hd => by
              have := (Nat.Prime.dvd_iff_eq hqp.1 hpp.1.ne_one).mp hd
              subst this; exact hps hq
          exact hc.mul_dvd_of_dvd_of_dvd hpp.2 hps'
      exact this Fn fun p hp => by
        rw [Finset.mem_filter] at hp
        exact ⟨Nat.prime_of_mem_primeFactors hp.1, Nat.dvd_of_mem_primeFactors hp.1⟩
    have hs1 : 1 ≤ skel n := Nat.one_le_iff_ne_zero.mpr (ne_zero_of_dvd_ne_zero (by omega) hdvd)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hs1, (Nat.le_of_dvd hn.1 hdvd).trans hn.2⟩,
      hsqf, hcop⟩
  have hharmonic : ∑ n ∈ Finset.Icc 1 z, (1 / (n : ℝ)) ≤ (15 / 4 : ℝ) * ∑ d ∈ D, (1 / (d.totient : ℝ)) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
    have hfiber : ∀ s ∈ D, ∑ n ∈ (Finset.Icc 1 z).filter (fun n => skel n = s), (1 / (n : ℝ)) ≤
        (15 / 4 : ℝ) * (1 / (s.totient : ℝ)) := fun s hs => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hs
      obtain ⟨⟨hs1, _⟩, hsSqf, hs30⟩ := hs
      let Ns := (Finset.Icc 1 z).filter (fun n => skel n = s)
      let Ms := Ns.image (fun n => n / s)
      have hsdvd : ∀ n ∈ Ns, s ∣ n := fun n hn => by
        rw [Finset.mem_filter] at hn
        rw [← hn.2]
        have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn.1).1; omega
        have : ∀ F : Finset ℕ, (∀ p ∈ F, p.Prime ∧ p ∣ n) → (∏ p ∈ F, p) ∣ n := fun F hF => by
          induction F using Finset.induction_on with
          | empty => simp
          | @insert p t hpt ih =>
            rw [Finset.prod_insert hpt]
            have hpt' := ih fun q hq => hF q (Finset.mem_insert_of_mem hq)
            have hpp := hF p (Finset.mem_insert_self p t)
            have hc : Nat.Coprime p (∏ q ∈ t, q) := Nat.Coprime.prod_right fun q hq => by
              have hqp := hF q (Finset.mem_insert_of_mem hq)
              exact (hpp.1.coprime_iff_not_dvd).mpr fun hd => by
                have := (Nat.Prime.dvd_iff_eq hqp.1 hpp.1.ne_one).mp hd
                subst this; exact hpt hq
            exact hc.mul_dvd_of_dvd_of_dvd hpp.2 hpt'
        exact this _ fun p hp => by
          rw [Finset.mem_filter] at hp
          exact ⟨Nat.prime_of_mem_primeFactors hp.1, Nat.dvd_of_mem_primeFactors hp.1⟩
      have hinj : ∀ n1 ∈ Ns, ∀ n2 ∈ Ns, n1 / s = n2 / s → n1 = n2 := fun n1 h1 n2 h2 heq => by
        rw [← Nat.mul_div_cancel' (hsdvd n1 h1), ← Nat.mul_div_cancel' (hsdvd n2 h2), heq]
      have hterm : ∀ n ∈ Ns, (1 / (n : ℝ)) = (1 / (s : ℝ)) * (1 / ((n / s : ℕ) : ℝ)) := fun n hn => by
        have hm : (n : ℝ) = (s : ℝ) * ((n / s : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' (hsdvd n hn)).symm
        rw [hm]; simp [mul_comm]
      have hS_primes : ∀ p ∈ ({2, 3, 5} : Finset ℕ) ∪ s.primeFactors, p.Prime := fun p hp => by
        rw [Finset.mem_union] at hp
        rcases hp with h | h
        · simp at h; rcases h with rfl | rfl | rfl <;> decide
        · exact Nat.prime_of_mem_primeFactors h
      have hMs_prop : ∀ m ∈ Ms, 1 ≤ m ∧ m ≤ z ∧ m.primeFactors ⊆ {2, 3, 5} ∪ s.primeFactors := by
        intro m hm
        rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
        have hsn := hsdvd n hn
        rw [Finset.mem_filter, Finset.mem_Icc] at hn
        refine ⟨Nat.div_pos (Nat.le_of_dvd hn.1.1 hsn) hs1, (Nat.div_le_self n s).trans hn.1.2, ?_⟩
        intro q hq
        have hqp := Nat.prime_of_mem_primeFactors hq
        have hqn : q ∣ n := (Nat.dvd_of_mem_primeFactors hq).trans (Nat.div_dvd_of_dvd hsn)
        rw [Finset.mem_union]
        by_cases hq235 : q = 2 ∨ q = 3 ∨ q = 5
        · left; simp; tauto
        · right
          have hq30 : Nat.Coprime q 30 := by
            refine (hqp.coprime_iff_not_dvd).mpr fun hd30 => ?_
            have hle30 : q ≤ 30 := Nat.le_of_dvd (by decide) hd30
            have hlt31 : q < 31 := by omega
            interval_cases q <;> first | exact absurd hqp (by decide) | omega
          have hq_mem : q ∈ n.primeFactors.filter (fun p => Nat.Coprime p 30) :=
            Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hqp, hqn, by omega⟩, hq30⟩
          have hqs : q ∣ s := by
            rw [← hn.2]
            exact Finset.dvd_prod_of_mem id hq_mem
          exact Nat.mem_primeFactors.mpr ⟨hqp, hqs, by omega⟩
      have hsum_Ms := sum_inv_primes_subset_le z ({2, 3, 5} ∪ s.primeFactors) hS_primes Ms hMs_prop
      have hdisj235 : Disjoint ({2, 3, 5} : Finset ℕ) s.primeFactors :=
        Finset.disjoint_left.mpr fun p h1 h2 => by
          have hps := Nat.dvd_of_mem_primeFactors h2
          simp at h1
          rcases h1 with rfl | rfl | rfl
          · exact absurd (Nat.dvd_gcd hps (by decide : 2 ∣ 30)) (by rw [hs30]; decide)
          · exact absurd (Nat.dvd_gcd hps (by decide : 3 ∣ 30)) (by rw [hs30]; decide)
          · exact absurd (Nat.dvd_gcd hps (by decide : 5 ∣ 30)) (by rw [hs30]; decide)
      have hprod_split : ∏ p ∈ ({2, 3, 5} : Finset ℕ) ∪ s.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) =
          (15 / 4 : ℝ) * ((s : ℝ) / (s.totient : ℝ)) := by
        rw [Finset.prod_union hdisj235]
        have h15_4 : ∏ p ∈ ({2, 3, 5} : Finset ℕ), ((p : ℝ) / ((p : ℝ) - 1)) = (15 / 4 : ℝ) := by
          norm_num
        have hsp : ∏ p ∈ s.primeFactors, p = s := prod_pf_of_sqf hsSqf (by omega)
        have hspf := fun p (hp : p ∈ s.primeFactors) => Nat.prime_of_mem_primeFactors hp
        obtain ⟨_, _, htot_s⟩ := sqf_prod_of_primes s.primeFactors hspf
        rw [hsp] at htot_s
        have htot_eq : ∏ p ∈ s.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) = (s : ℝ) / (s.totient : ℝ) := by
          have h1 : ∏ p ∈ s.primeFactors, (p : ℝ) = (s : ℝ) := by
            calc ∏ p ∈ s.primeFactors, (p : ℝ)
                = ((∏ p ∈ s.primeFactors, p : ℕ) : ℝ) := (Nat.cast_prod _ _).symm
              _ = (s : ℝ) := by exact_mod_cast hsp
          have h2 : ∏ p ∈ s.primeFactors, ((p : ℝ) - 1) = (s.totient : ℝ) := by
            have : ∀ p ∈ s.primeFactors, (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := fun p hp => by
              have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
              rw [Nat.cast_sub hp1, Nat.cast_one]
            calc ∏ p ∈ s.primeFactors, ((p : ℝ) - 1)
                = ∏ p ∈ s.primeFactors, ((p - 1 : ℕ) : ℝ) := Finset.prod_congr rfl this
              _ = ((∏ p ∈ s.primeFactors, (p - 1) : ℕ) : ℝ) := (Nat.cast_prod _ _).symm
              _ = (s.totient : ℝ) := by rw [← htot_s]
          rw [Finset.prod_div_distrib, h1, h2]
        rw [h15_4, htot_eq]
      calc ∑ n ∈ Ns, (1 / (n : ℝ))
          = (1 / (s : ℝ)) * ∑ n ∈ Ns, (1 / ((n / s : ℕ) : ℝ)) := by
              rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
        _ = (1 / (s : ℝ)) * ∑ m ∈ Ms, (1 / (m : ℝ)) := by rw [Finset.sum_image hinj]
        _ ≤ (1 / (s : ℝ)) * ((15 / 4 : ℝ) * ((s : ℝ) / (s.totient : ℝ))) := by
              rw [← hprod_split]
              exact mul_le_mul_of_nonneg_left hsum_Ms (by positivity)
        _ = (15 / 4 : ℝ) * (1 / (s.totient : ℝ)) := by
              have hs_ne : (s : ℝ) ≠ 0 := by positivity
              field_simp [hs_ne]
    exact Finset.sum_le_sum hfiber
  have hlog_sub : ∀ n : ℕ, 1 ≤ n → Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    intro n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have h1 := Real.log_le_sub_one_of_pos (div_pos hn1_pos hn_pos)
    rw [Real.log_div hn1_pos.ne' hn_pos.ne'] at h1
    have : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by field_simp [hn_pos.ne']; ring
    linarith
  have hIoc_tele : ∀ b : ℕ, 10 ≤ b →
      Real.log ((b : ℝ) + 1) - Real.log 11 ≤ ∑ n ∈ Finset.Ioc 10 b, (1 / (n : ℝ)) := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base => simp; norm_num
    | succ b hb ih =>
      have hsplit : Finset.Ioc 10 (b + 1) = insert (b + 1) (Finset.Ioc 10 b) := by
        ext x; simp only [Finset.mem_insert, Finset.mem_Ioc]; omega
      have hnot : b + 1 ∉ Finset.Ioc 10 b := by simp
      rw [hsplit, Finset.sum_insert hnot]
      have hstep := hlog_sub (b + 1) (by omega)
      push_cast at hstep ⊢
      linarith
  have hsplit_Icc : Finset.Icc 1 z = Finset.Icc 1 10 ∪ Finset.Ioc 10 z := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 10) (Finset.Ioc 10 z) := Finset.disjoint_left.mpr fun n h1 h2 => by
    simp at h1 h2; omega
  have h10 : ∑ n ∈ (Finset.Icc 1 10 : Finset ℕ), (1 / (n : ℝ)) = (7381 : ℝ) / 2520 := by
    have hq : ∑ n ∈ (Finset.Icc 1 10 : Finset ℕ), (1 / (n : ℚ)) = 7381 / 2520 := by
      norm_num [Finset.sum_Icc_succ_top]
    have hr := congrArg (Rat.cast (K := ℝ)) hq
    simpa [Rat.cast_sum] using hr
  have hlog11 : Real.log (11 : ℝ) < (12 : ℝ) / 5 :=
    log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
  have hlog_lower : Real.log ((z : ℝ) + 1) + 1 / 2 ≤ ∑ n ∈ Finset.Icc 1 z, (1 / (n : ℝ)) := by
    rw [hsplit_Icc, Finset.sum_union hdisj, h10]
    linarith [hIoc_tele z hz]
  exact hlog_lower.trans hharmonic

private lemma card_D_le (z : ℕ) :
    ((Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)).card ≤ 8 * (z / 30 + 1) := by
  let R8 : Finset ℕ := (Finset.range 30).filter (fun r => Nat.Coprime r 30)
  have hR8 : R8.card = 8 := by decide
  let D := (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)
  have himg : D.image (fun d => (d / 30, d % 30)) ⊆ Finset.range (z / 30 + 1) ×ˢ R8 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    rw [Finset.mem_product, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le (Nat.div_le_div_right hd.1.2),
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt d (by decide)), ?_⟩⟩
    change Nat.gcd (d % 30) 30 = 1
    rw [← Nat.gcd_rec 30 d, Nat.gcd_comm]
    exact hd.2.2
  have hinj : ∀ d1 ∈ D, ∀ d2 ∈ D, (d1 / 30, d1 % 30) = (d2 / 30, d2 % 30) → d1 = d2 := by
    intro d1 _ d2 _ heq
    have hq : d1 / 30 = d2 / 30 := (Prod.ext_iff.mp heq).1
    have hr : d1 % 30 = d2 % 30 := (Prod.ext_iff.mp heq).2
    omega
  calc D.card = (D.image (fun d => (d / 30, d % 30))).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (z / 30 + 1) ×ˢ R8).card := Finset.card_le_card himg
    _ = (z / 30 + 1) * 8 := by rw [Finset.card_product, Finset.card_range, hR8]
    _ = 8 * (z / 30 + 1) := mul_comm _ _

private lemma log_div_sqrt_le {X X0 : ℝ} (hX0 : 10 ≤ X0) (hX : X0 ≤ X)
    {x0_hi : ℝ} (hx0 : Real.log X0 ≤ x0_hi) :
    Real.log X / Real.sqrt X ≤ x0_hi / Real.sqrt X0 := by
  have hX0pos : 0 < X0 := by linarith
  have hXpos : 0 < X := by linarith
  let u := Real.sqrt (X / X0)
  have hu1 : 1 ≤ u := by
    rw [Real.le_sqrt' (by positivity), one_pow, one_le_div hX0pos]; exact hX
  have hu_pos : 0 < u := by linarith
  have hlog_u : Real.log (X / X0) ≤ 2 * (u - 1) := by
    have hsq : X / X0 = u * u := (Real.mul_self_sqrt (div_pos hXpos hX0pos).le).symm
    rw [hsq, Real.log_mul hu_pos.ne' hu_pos.ne']
    linarith [Real.log_le_sub_one_of_pos hu_pos]
  have h2_le : 2 ≤ Real.log X0 := by
    have hpow : (2.7182818286 : ℝ) ^ 2 < 10 := by norm_num
    have hexp2 : Real.exp (2 : ℝ) < 10 := by
      have he : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
      have h1 : Real.exp 1 ^ 2 = Real.exp (2 : ℕ) := by rw [← Real.exp_nat_mul, mul_one]
      have h2 := (pow_lt_pow_left₀ he (Real.exp_pos 1).le (by decide)).trans hpow
      simpa [h1] using h2
    have hl10 : (2 : ℝ) < Real.log 10 := by
      have := Real.log_lt_log (Real.exp_pos 2) hexp2
      rwa [Real.log_exp] at this
    exact hl10.le.trans (Real.log_le_log (by norm_num) hX0)
  have hlogX : Real.log X ≤ Real.log X0 * u := by
    have hdiv : X = X0 * (X / X0) := (mul_div_cancel₀ X hX0pos.ne').symm
    have hmul : Real.log X = Real.log X0 + Real.log (X / X0) := by
      conv_lhs => rw [hdiv]
      exact Real.log_mul hX0pos.ne' (div_pos hXpos hX0pos).ne'
    have h2u : 2 * (u - 1) ≤ Real.log X0 * (u - 1) :=
      mul_le_mul_of_nonneg_right h2_le (by linarith)
    linarith
  have hsqrtX : Real.sqrt X = Real.sqrt X0 * u := by
    rw [← Real.sqrt_mul hX0pos.le, mul_div_cancel₀ X hX0pos.ne']
  have hsqrt_pos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hsqrt0_pos : 0 < Real.sqrt X0 := Real.sqrt_pos.mpr hX0pos
  calc Real.log X / Real.sqrt X
      ≤ (Real.log X0 * u) / (Real.sqrt X0 * u) := by
          rw [← hsqrtX]
          exact div_le_div_of_nonneg_right hlogX hsqrt_pos.le
    _ = Real.log X0 / Real.sqrt X0 := by field_simp [hu_pos.ne', hsqrt0_pos.ne']
    _ ≤ x0_hi / Real.sqrt X0 := div_le_div_of_nonneg_right hx0 hsqrt0_pos.le

private lemma pi30_le_of_params (X0 : ℕ) (hX0_10 : 10 ≤ X0) (X : ℕ) (hX : X0 ≤ X)
    (x0_lo x0_hi logx0_hi eps1 C_target : ℝ)
    (hx0_lo_2 : 2 ≤ x0_lo) (hx0_lo : x0_lo ≤ Real.log (X0 : ℝ))
    (hx0_hi : Real.log (X0 : ℝ) ≤ x0_hi)
    (hlogx0 : Real.log x0_lo ≤ logx0_hi)
    (hb_neg : (1 / 2 : ℝ) - 11 / 12 - (logx0_hi - 1) / 2 ≤ 0)
    (hL_pos_c : 0 < (4 / 15 : ℝ) * ((1 / 2 : ℝ) * (1 - 1 / x0_lo) +
      ((1 / 2 : ℝ) - 11 / 12 - (logx0_hi - 1) / 2) / x0_lo))
    (heps1_pos : 0 < eps1) (heps1 : x0_hi / (X0 : ℝ) ≤ eps1 ^ 2)
    (hS_min : 28 ≤ (1 : ℝ) / eps1)
    (hC : 1 / (10 * ((4 / 15 : ℝ) * ((1 / 2 : ℝ) * (1 - 1 / x0_lo) +
      ((1 / 2 : ℝ) - 11 / 12 - (logx0_hi - 1) / 2) / x0_lo))) +
      64 / 1875 + (138 / 25 : ℝ) * eps1 + 192 * eps1 ^ 2 ≤ C_target) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) ≤
      C_target * (X : ℝ) / Real.log (X : ℝ) := by
  have hX0R : (10 : ℝ) ≤ (X0 : ℝ) := by exact_mod_cast hX0_10
  have hXR : (X0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
  have hlog_ge : x0_lo ≤ Real.log (X : ℝ) := hx0_lo.trans (Real.log_le_log (by linarith) hXR)
  have hlog_pos : 0 < Real.log (X : ℝ) := by linarith
  have hx0_hi_nn : 0 ≤ x0_hi := (Real.log_nonneg (by linarith : (1 : ℝ) ≤ (X0 : ℝ))).trans hx0_hi
  have hlog_sqrt := log_div_sqrt_le hX0R hXR hx0_hi
  have hlog_div_X : Real.log (X : ℝ) / (X : ℝ) ≤ eps1 ^ 2 := by
    have hsqX : Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ) = (X : ℝ) := Real.mul_self_sqrt hXpos.le
    have hsq0 : Real.sqrt (X0 : ℝ) * Real.sqrt (X0 : ℝ) = (X0 : ℝ) := Real.mul_self_sqrt (by linarith)
    have hsqrt_le : Real.sqrt (X0 : ℝ) ≤ Real.sqrt (X : ℝ) := Real.sqrt_le_sqrt hXR
    have h1 : Real.log (X : ℝ) / (X : ℝ) =
        (Real.log (X : ℝ) / Real.sqrt (X : ℝ)) / Real.sqrt (X : ℝ) := by
      rw [div_div, hsqX]
    have h2 : (x0_hi / Real.sqrt (X0 : ℝ)) / Real.sqrt (X0 : ℝ) = x0_hi / (X0 : ℝ) := by
      rw [div_div, hsq0]
    rw [h1]
    calc (Real.log (X : ℝ) / Real.sqrt (X : ℝ)) / Real.sqrt (X : ℝ)
        ≤ (x0_hi / Real.sqrt (X0 : ℝ)) / Real.sqrt (X : ℝ) :=
          div_le_div_of_nonneg_right hlog_sqrt (Real.sqrt_nonneg _)
      _ ≤ (x0_hi / Real.sqrt (X0 : ℝ)) / Real.sqrt (X0 : ℝ) :=
          div_le_div_of_nonneg_left (div_nonneg hx0_hi_nn (Real.sqrt_nonneg _))
            (Real.sqrt_pos.mpr (by linarith)) hsqrt_le
      _ = x0_hi / (X0 : ℝ) := h2
      _ ≤ eps1 ^ 2 := heps1
  let S := Real.sqrt ((X : ℝ) / Real.log (X : ℝ))
  have hS_pos : 0 < S := Real.sqrt_pos.mpr (div_pos hXpos hlog_pos)
  have hS_sq : S ^ 2 = (X : ℝ) / Real.log (X : ℝ) := Real.sq_sqrt (div_pos hXpos hlog_pos).le
  have hinvS : 1 / S ≤ eps1 := by
    have h1 : (1 / S) ^ 2 ≤ eps1 ^ 2 := by
      rw [div_pow, one_pow, hS_sq, one_div_div]
      exact hlog_div_X
    have h1nn : 0 ≤ 1 / S := by positivity
    nlinarith [sq_nonneg (eps1 - 1 / S)]
  have hS_28 : 28 ≤ S := by
    have : (1 / eps1) ≤ S := by
      rw [div_le_iff₀ heps1_pos]
      have := mul_le_mul_of_nonneg_right hinvS hS_pos.le
      rw [one_div_mul_cancel hS_pos.ne'] at this
      linarith
    linarith
  let z := Nat.floor ((2 / 5 : ℝ) * S)
  have hz_11 : (11 : ℝ) ≤ (2 / 5 : ℝ) * S := by linarith
  have hz_10 : 10 ≤ z := by
    have h11 : 11 ≤ z := Nat.le_floor hz_11
    omega
  have hz_1 : 1 ≤ z := by omega
  let D := (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)
  let L : ℝ := ∑ d ∈ D, (1 / (d.totient : ℝ))
  have hsel : (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) ≤
      (z : ℝ) + (X : ℝ) / (10 * L) + 3 * (D.card : ℝ) ^ 2 := selberg_pi30_le X z hz_1
  have hL_an : Real.log ((z : ℝ) + 1) + 1 / 2 ≤ (15 / 4 : ℝ) * L := analytic_L_lower hz_10
  have hx0_pos : 0 < x0_lo := by linarith
  have hlog_log_le : Real.log (Real.log (X : ℝ)) ≤ logx0_hi - 1 + Real.log (X : ℝ) / x0_lo := by
    have htan := Real.log_le_sub_one_of_pos (div_pos hlog_pos hx0_pos)
    rw [Real.log_div hlog_pos.ne' hx0_pos.ne'] at htan
    linarith
  have hlog5_2 : Real.log (5 / 2 : ℝ) < 11 / 12 :=
    log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
  have hlog_z1 : Real.log ((2 / 5 : ℝ) * S) ≤ Real.log ((z : ℝ) + 1) := by
    refine Real.log_le_log (by positivity) ?_
    exact (Nat.lt_floor_add_one ((2 / 5 : ℝ) * S)).le
  have hlog_25S : Real.log ((2 / 5 : ℝ) * S) =
      -Real.log (5 / 2 : ℝ) + (1 / 2 : ℝ) * (Real.log (X : ℝ) - Real.log (Real.log (X : ℝ))) := by
    have h1 : (2 / 5 : ℝ) = (5 / 2 : ℝ)⁻¹ := by norm_num
    rw [Real.log_mul (by norm_num) hS_pos.ne', h1, Real.log_inv]
    have hSlog : Real.log S = (1 / 2 : ℝ) * (Real.log (X : ℝ) - Real.log (Real.log (X : ℝ))) := by
      simp only [S]
      rw [Real.log_sqrt (div_pos hXpos hlog_pos).le, Real.log_div hXpos.ne' hlog_pos.ne']
      ring
    rw [hSlog]
  let b_const := (1 / 2 : ℝ) - 11 / 12 - (logx0_hi - 1) / 2
  let L_coef := (4 / 15 : ℝ) * ((1 / 2 : ℝ) * (1 - 1 / x0_lo) + b_const / x0_lo)
  have hL_ge : L_coef * Real.log (X : ℝ) ≤ L := by
    have h15_4 : (1 / 2 : ℝ) * (1 - 1 / x0_lo) * Real.log (X : ℝ) + b_const ≤ (15 / 4 : ℝ) * L := by
      have hsub : -11 / 12 + (1 / 2 : ℝ) * (Real.log (X : ℝ) - (logx0_hi - 1 + Real.log (X : ℝ) / x0_lo)) +
          1 / 2 ≤ Real.log ((z : ℝ) + 1) + 1 / 2 := by
        linarith [hlog5_2, hlog_z1, hlog_25S, hlog_log_le]
      calc (1 / 2 : ℝ) * (1 - 1 / x0_lo) * Real.log (X : ℝ) + b_const
          = -11 / 12 + (1 / 2 : ℝ) * (Real.log (X : ℝ) - (logx0_hi - 1 + Real.log (X : ℝ) / x0_lo)) + 1 / 2 := by
            simp only [b_const]; ring
        _ ≤ Real.log ((z : ℝ) + 1) + 1 / 2 := hsub
        _ ≤ (15 / 4 : ℝ) * L := hL_an
    have hb_mul : (b_const / x0_lo) * Real.log (X : ℝ) ≤ b_const := by
      have hdiv : 1 ≤ Real.log (X : ℝ) / x0_lo := (one_le_div hx0_pos).mpr hlog_ge
      have hneg : b_const * (Real.log (X : ℝ) / x0_lo) ≤ b_const * 1 :=
        mul_le_mul_of_nonpos_left hdiv hb_neg
      simpa [div_mul_eq_mul_div, mul_div_assoc] using hneg
    have hcomb : (15 / 4 : ℝ) * L_coef * Real.log (X : ℝ) ≤ (15 / 4 : ℝ) * L := by
      have heq : (15 / 4 : ℝ) * L_coef * Real.log (X : ℝ) =
          (1 / 2 : ℝ) * (1 - 1 / x0_lo) * Real.log (X : ℝ) + (b_const / x0_lo) * Real.log (X : ℝ) := by
        simp only [L_coef]; ring
      linarith
    linarith
  have hmain_term : (X : ℝ) / (10 * L) ≤ (1 / (10 * L_coef)) * S ^ 2 := by
    have hL_pos : 0 < L := by
      have : 0 < L_coef * Real.log (X : ℝ) := mul_pos hL_pos_c hlog_pos
      linarith
    rw [hS_sq]
    have h1 : (X : ℝ) / (10 * L) ≤ (X : ℝ) / (10 * (L_coef * Real.log (X : ℝ))) :=
      div_le_div_of_nonneg_left hXpos.le (by positivity) (by linarith)
    calc (X : ℝ) / (10 * L) ≤ (X : ℝ) / (10 * (L_coef * Real.log (X : ℝ))) := h1
      _ = (1 / (10 * L_coef)) * ((X : ℝ) / Real.log (X : ℝ)) := by ring
  have hz_le : (z : ℝ) ≤ (2 / 5 : ℝ) * S := Nat.floor_le (by positivity)
  have hD_le : (D.card : ℝ) ≤ (8 / 75 : ℝ) * S + 8 := by
    have hc := card_D_le z
    have hdiv30 : ((z / 30 : ℕ) : ℝ) ≤ (z : ℝ) / 30 := by
      rw [le_div_iff₀ (by norm_num)]
      exact_mod_cast Nat.div_mul_le_self z 30
    have h1 : (D.card : ℝ) ≤ 8 * ((z : ℝ) / 30 + 1) := by
      have hcr : (D.card : ℝ) ≤ 8 * (((z / 30 : ℕ) : ℝ) + 1) := by exact_mod_cast hc
      linarith
    linarith
  have hD_nn : (0 : ℝ) ≤ (D.card : ℝ) := by positivity
  have herr_term : (z : ℝ) + 3 * (D.card : ℝ) ^ 2 ≤
      (64 / 1875 : ℝ) * S ^ 2 + (138 / 25 : ℝ) * S + 192 := by
    have hsq : (D.card : ℝ) ^ 2 ≤ ((8 / 75 : ℝ) * S + 8) ^ 2 :=
      pow_le_pow_left₀ hD_nn hD_le 2
    have hsq_exp : ((8 / 75 : ℝ) * S + 8) ^ 2 = (64 / 5625 : ℝ) * S ^ 2 + (128 / 75 : ℝ) * S + 64 := by ring
    linarith
  have hS_bound : S ≤ eps1 * S ^ 2 := by
    calc S = (1 / S) * S ^ 2 := by field_simp [hS_pos.ne']
      _ ≤ eps1 * S ^ 2 := mul_le_mul_of_nonneg_right hinvS (sq_nonneg S)
  have h1_bound : (1 : ℝ) ≤ eps1 ^ 2 * S ^ 2 := by
    have h1 : (1 / S) ^ 2 ≤ eps1 ^ 2 := pow_le_pow_left₀ (by positivity) hinvS 2
    calc (1 : ℝ) = (1 / S) ^ 2 * S ^ 2 := by field_simp [hS_pos.ne']
      _ ≤ eps1 ^ 2 * S ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg S)
  have h138 : (138 / 25 : ℝ) * S ≤ (138 / 25 : ℝ) * eps1 * S ^ 2 := by
    have := mul_le_mul_of_nonneg_left hS_bound (by norm_num : (0 : ℝ) ≤ 138 / 25)
    linarith
  have h192 : (192 : ℝ) ≤ 192 * eps1 ^ 2 * S ^ 2 := by
    have := mul_le_mul_of_nonneg_left h1_bound (by norm_num : (0 : ℝ) ≤ 192)
    linarith
  have herr_S2 : (z : ℝ) + 3 * (D.card : ℝ) ^ 2 ≤
      (64 / 1875 + (138 / 25 : ℝ) * eps1 + 192 * eps1 ^ 2) * S ^ 2 := by
    have heq : (64 / 1875 : ℝ) * S ^ 2 + (138 / 25 : ℝ) * eps1 * S ^ 2 + 192 * eps1 ^ 2 * S ^ 2 =
        (64 / 1875 + (138 / 25 : ℝ) * eps1 + 192 * eps1 ^ 2) * S ^ 2 := by ring
    linarith [herr_term, h138, h192]
  have hcomb_S2 : (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) ≤ C_target * S ^ 2 := by
    have hcomb_eq : (1 / (10 * L_coef)) * S ^ 2 +
        (64 / 1875 + (138 / 25 : ℝ) * eps1 + 192 * eps1 ^ 2) * S ^ 2 =
        (1 / (10 * L_coef) + 64 / 1875 + (138 / 25 : ℝ) * eps1 + 192 * eps1 ^ 2) * S ^ 2 := by ring
    have hstep1 : (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
        (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) ≤
        (1 / (10 * L_coef) + 64 / 1875 + (138 / 25 : ℝ) * eps1 + 192 * eps1 ^ 2) * S ^ 2 := by
      linarith [hsel, hmain_term, herr_S2, hcomb_eq]
    have hC' : 1 / (10 * L_coef) + 64 / 1875 + (138 / 25 : ℝ) * eps1 + 192 * eps1 ^ 2 ≤ C_target := hC
    exact hstep1.trans (mul_le_mul_of_nonneg_right hC' (sq_nonneg S))
  calc (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
        (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ)
      ≤ C_target * S ^ 2 := hcomb_S2
    _ = C_target * (X : ℝ) / Real.log (X : ℝ) := by rw [hS_sq]; ring

private lemma pi30_le_10_pow_7 (X : ℕ) (hX : 10 ^ 7 ≤ X) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) ≤
      (51 / 50 : ℝ) * (X : ℝ) / Real.log (X : ℝ) := by
  have hx0_lo : (161 / 10 : ℝ) ≤ Real.log ((10 ^ 7 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
  have hx0_hi : Real.log ((10 ^ 7 : ℕ) : ℝ) ≤ 371 / 23 := by
    have h53 : Real.log (10 : ℝ) < 53 / 23 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have hlogx0 : Real.log (161 / 10 : ℝ) ≤ 14 / 5 :=
    (log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le
  exact pi30_le_of_params (10 ^ 7) (by decide) X hX (161 / 10) (371 / 23) (14 / 5) (1 / 500) (51 / 50)
    (by norm_num) hx0_lo hx0_hi hlogx0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private lemma pi30_le_10_pow_8 (X : ℕ) (hX : 10 ^ 8 ≤ X) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) ≤
      (99 / 100 : ℝ) * (X : ℝ) / Real.log (X : ℝ) := by
  have hx0_lo : (92 / 5 : ℝ) ≤ Real.log ((10 ^ 8 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
  have hx0_hi : Real.log ((10 ^ 8 : ℕ) : ℝ) ≤ 424 / 23 := by
    have h53 : Real.log (10 : ℝ) < 53 / 23 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have hlogx0 : Real.log (92 / 5 : ℝ) ≤ 44 / 15 :=
    (log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le
  exact pi30_le_of_params (10 ^ 8) (by decide) X hX (92 / 5) (424 / 23) (44 / 15) (1 / 1000) (99 / 100)
    (by norm_num) hx0_lo hx0_hi hlogx0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private lemma pi30_le_10_pow_10 (X : ℕ) (hX : 10 ^ 10 ≤ X) :
    (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) ≤
      (19 / 20 : ℝ) * (X : ℝ) / Real.log (X : ℝ) := by
  have hx0_lo : (23 : ℝ) ≤ Real.log ((10 ^ 10 : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
  have hx0_hi : Real.log ((10 ^ 10 : ℕ) : ℝ) ≤ 530 / 23 := by
    have h53 : Real.log (10 : ℝ) < 53 / 23 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have hlogx0 : Real.log (23 : ℝ) ≤ 22 / 7 :=
    (log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)).le
  exact pi30_le_of_params (10 ^ 10) (by decide) X hX 23 (530 / 23) (22 / 7) (1 / 10000) (19 / 20)
    (by norm_num) hx0_lo hx0_hi hlogx0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/- ## Section 4: Prime reciprocal rank bounds and omega(n) lower bounds -/

private lemma prime_le_100_cases {q : ℕ} (hq : q.Prime) (hq100 : q ≤ 100) :
    q ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97} : Finset ℕ) := by
  have hlt : q < 101 := by omega
  interval_cases q <;> first | exact absurd hq (by decide) | decide

private lemma prime_le_97_gt16_cases {p : ℕ} (hp : p.Prime) (h17 : 17 ≤ p) (h97 : p ≤ 97) :
    p ∈ ({17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97} : Finset ℕ) := by
  have hlt : p < 98 := by omega
  interval_cases p <;> first | exact absurd hp (by decide) | decide

private lemma p30_10000_data :
    461 ≤ ((Finset.Icc 1 10000).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card ∧
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ≤ 10000 ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)) →
      ∑ p ∈ S, (1 / (p : ℝ)) ≤ (475940 : ℝ) / 1000000 := by
  let P97 : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}
  let P17_97 : Finset ℕ := {17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}
  let T := ((Finset.Icc 1 10000).filter (fun p =>
    p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)).filter (fun p =>
    p ∈ P17_97 ∨ (2 ≤ p ∧ ∀ q ∈ P97, p % q ≠ 0))
  have hP97_pr : ∀ q ∈ P97, q.Prime := by decide
  have hP97_le : ∀ q ∈ P97, q ≤ 97 := by decide
  have hP17_pr : ∀ q ∈ P17_97, q.Prime := by decide
  have hT_dec : T.card = 461 ∧ ∑ p ∈ T, (1000000 + p - 1) / p = 475940 := by decide +kernel
  have hT_eq : T = (Finset.Icc 1 10000).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)) := by
    ext p
    simp only [T, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h10k⟩, hmod⟩, hcond⟩
      refine ⟨⟨h1, h10k⟩, ?_, hmod⟩
      rcases hcond with hp17 | ⟨hp2, hdiv⟩
      · exact hP17_pr p hp17
      · by_contra hnp
        let q := p.minFac
        have hq_pr : q.Prime := Nat.minFac_prime (by omega)
        have hq_sq : q * q ≤ p := by
          have := Nat.minFac_sq_le_self (by omega) hnp
          simpa [sq] using this
        have hq_le : q ≤ 100 := by
          by_contra h101
          have : 101 ≤ q := by omega
          have : 10201 ≤ q * q := by nlinarith
          omega
        have hq_mem : q ∈ P97 := prime_le_100_cases hq_pr hq_le
        have hqm : p % q = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd p)
        exact hdiv q hq_mem hqm
    · rintro ⟨⟨h1, h10k⟩, hp, hmod⟩
      refine ⟨⟨⟨h1, h10k⟩, hmod⟩, ?_⟩
      by_cases hp97 : p ≤ 97
      · left
        exact prime_le_97_gt16_cases hp (by omega) hp97
      · right
        refine ⟨hp.two_le, fun q hq hmod0 => ?_⟩
        have hqp : q ∣ p := Nat.dvd_of_mod_eq_zero hmod0
        have hq_eq : p = q := (Nat.Prime.dvd_iff_eq hp (hP97_pr q hq).ne_one).mp hqp
        have hq_le := hP97_le q hq
        omega
  constructor
  · rw [← hT_eq]; exact le_of_eq hT_dec.1.symm
  · intro S hS
    have hsub : S ⊆ T := by
      intro p hpS
      obtain ⟨hp, hp10k, hmod⟩ := hS p hpS
      rw [hT_eq, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp.one_lt.le, hp10k⟩, hp, hmod⟩
    have hsum_le : ∑ p ∈ S, (1 / (p : ℝ)) ≤ ∑ p ∈ T, (1 / (p : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    have hT_le : ∑ p ∈ T, (1 / (p : ℝ)) ≤ (475940 : ℝ) / 1000000 := by
      have hterm : ∀ p ∈ T, (1 / (p : ℝ)) ≤ (((1000000 + p - 1) / p : ℕ) : ℝ) / 1000000 := by
        intro p hp
        have hp_pos : 0 < p := by
          rw [hT_eq, Finset.mem_filter] at hp; exact hp.2.1.pos
        have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_pos
        have hnat : 1000000 ≤ p * ((1000000 + p - 1) / p) := by
          have hlt := Nat.lt_mul_div_succ (1000000 + p - 1) hp_pos
          have heq : p * ((1000000 + p - 1) / p + 1) = p * ((1000000 + p - 1) / p) + p := by ring
          rw [heq] at hlt
          omega
        have hreal : (1000000 : ℝ) ≤ (p : ℝ) * (((1000000 + p - 1) / p : ℕ) : ℝ) := by
          exact_mod_cast hnat
        rw [div_le_div_iff₀ hpR (by norm_num)]
        linarith
      calc ∑ p ∈ T, (1 / (p : ℝ))
          ≤ ∑ p ∈ T, (((1000000 + p - 1) / p : ℕ) : ℝ) / 1000000 := Finset.sum_le_sum hterm
        _ = (∑ p ∈ T, (((1000000 + p - 1) / p : ℕ) : ℝ)) / 1000000 := (Finset.sum_div _ _ _).symm
        _ = (475940 : ℝ) / 1000000 := by
            have : (∑ p ∈ T, (((1000000 + p - 1) / p : ℕ) : ℝ)) = (475940 : ℝ) := by
              exact_mod_cast hT_dec.2
            rw [this]
    exact hsum_le.trans hT_le

private lemma sum_Ioc_split {f : ℕ → ℝ} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ j ∈ Finset.Ioc a c, f j = (∑ j ∈ Finset.Ioc a b, f j) + ∑ j ∈ Finset.Ioc b c, f j := by
  have hunion : Finset.Ioc a c = Finset.Ioc a b ∪ Finset.Ioc b c := by
    ext j; simp only [Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) :=
    Finset.disjoint_left.mpr fun j h1 h2 => by simp at h1 h2; omega
  rw [hunion, Finset.sum_union hdisj]

private lemma sum_Ioc_sub_shift_le (K a b : ℕ) (ha : K + 2 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Finset.Ioc a b, (1 / ((j : ℝ) - (K : ℝ))) ≤
      Real.log ((b : ℝ) - (K : ℝ)) - Real.log ((a : ℝ) - (K : ℝ)) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    have hsplit : Finset.Ioc a (b + 1) = insert (b + 1) (Finset.Ioc a b) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Ioc]; omega
    have hnot : b + 1 ∉ Finset.Ioc a b := by simp
    rw [hsplit, Finset.sum_insert hnot]
    have hstep : 1 / (((b + 1 : ℕ) : ℝ) - (K : ℝ)) ≤
        Real.log (((b + 1 : ℕ) : ℝ) - (K : ℝ)) - Real.log ((b : ℝ) - (K : ℝ)) := by
      have hbK : (1 : ℝ) ≤ (b : ℝ) - (K : ℝ) := by
        have : K + 2 ≤ b := ha.trans hb
        have : ((K + 2 : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast this
        push_cast at this; linarith
      have hp1 : (0 : ℝ) < ((b + 1 : ℕ) : ℝ) - (K : ℝ) := by push_cast; linarith
      have htan := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < (b : ℝ) - (K : ℝ)) hp1)
      rw [Real.log_div (by linarith) hp1.ne'] at htan
      have heq : ((b : ℝ) - (K : ℝ)) / (((b + 1 : ℕ) : ℝ) - (K : ℝ)) - 1 =
          -(1 / (((b + 1 : ℕ) : ℝ) - (K : ℝ))) := by
        push_cast; field_simp [show (b : ℝ) + 1 - (K : ℝ) ≠ 0 by linarith]; ring
      linarith
    linarith

private lemma sum_Ioc_log_log_le (c : ℝ) (hc : 1 ≤ c) (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Finset.Ioc a b, (1 / ((j : ℝ) * Real.log (c * (j : ℝ)))) ≤
      Real.log (Real.log (c * (b : ℝ))) - Real.log (Real.log (c * (a : ℝ))) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    have hsplit : Finset.Ioc a (b + 1) = insert (b + 1) (Finset.Ioc a b) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Ioc]; omega
    have hnot : b + 1 ∉ Finset.Ioc a b := by simp
    rw [hsplit, Finset.sum_insert hnot]
    have hstep : 1 / (((b + 1 : ℕ) : ℝ) * Real.log (c * ((b + 1 : ℕ) : ℝ))) ≤
        Real.log (Real.log (c * ((b + 1 : ℕ) : ℝ))) - Real.log (Real.log (c * (b : ℝ))) := by
      have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (ha.trans hb)
      have hbp : (0 : ℝ) < (b : ℝ) := by linarith
      have hbp1 : (0 : ℝ) < ((b + 1 : ℕ) : ℝ) := by positivity
      have h1 : 1 / ((b + 1 : ℕ) : ℝ) ≤ Real.log (c * ((b + 1 : ℕ) : ℝ)) - Real.log (c * (b : ℝ)) := by
        have hlogdiff : Real.log (c * ((b + 1 : ℕ) : ℝ)) - Real.log (c * (b : ℝ)) =
            Real.log ((b + 1 : ℕ) : ℝ) - Real.log (b : ℝ) := by
          rw [Real.log_mul (by linarith) hbp1.ne', Real.log_mul (by linarith) hbp.ne']
          ring
        rw [hlogdiff]
        have htan := Real.log_le_sub_one_of_pos (div_pos hbp hbp1)
        rw [Real.log_div hbp.ne' hbp1.ne'] at htan
        have heq : (b : ℝ) / ((b + 1 : ℕ) : ℝ) - 1 = -(1 / ((b + 1 : ℕ) : ℝ)) := by
          push_cast; field_simp [hbp1.ne']; ring
        linarith
      have hx_pos : 0 < Real.log (c * (b : ℝ)) := by
        have h2le : 2 ≤ c * (b : ℝ) := by nlinarith
        exact (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) h2le)
      have hy_pos : 0 < Real.log (c * ((b + 1 : ℕ) : ℝ)) := by
        have h2le : 2 ≤ c * ((b + 1 : ℕ) : ℝ) := by push_cast; nlinarith
        exact (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) h2le)
      have h2 := Real.log_le_sub_one_of_pos (div_pos hx_pos hy_pos)
      rw [Real.log_div hx_pos.ne' hy_pos.ne'] at h2
      have h3 : (Real.log (c * ((b + 1 : ℕ) : ℝ)) - Real.log (c * (b : ℝ))) /
          Real.log (c * ((b + 1 : ℕ) : ℝ)) ≤
          Real.log (Real.log (c * ((b + 1 : ℕ) : ℝ))) - Real.log (Real.log (c * (b : ℝ))) := by
        have heq : (Real.log (c * ((b + 1 : ℕ) : ℝ)) - Real.log (c * (b : ℝ))) /
            Real.log (c * ((b + 1 : ℕ) : ℝ)) =
            1 - Real.log (c * (b : ℝ)) / Real.log (c * ((b + 1 : ℕ) : ℝ)) := by
          field_simp [hy_pos.ne']
        linarith
      have h4 : 1 / (((b + 1 : ℕ) : ℝ) * Real.log (c * ((b + 1 : ℕ) : ℝ))) =
          (1 / ((b + 1 : ℕ) : ℝ)) / Real.log (c * ((b + 1 : ℕ) : ℝ)) := by ring
      rw [h4]
      exact (div_le_div_of_nonneg_right h1 hy_pos.le).trans h3
    linarith

private lemma asymp_rank_inv_le_clean (X0 : ℕ) (C : ℝ) (hC_pos : 0 < C)
    (hlogX0 : 10 * C ≤ Real.log (X0 : ℝ))
    (hpi : ∀ X, X0 ≤ X →
      (((Finset.Icc 1 X).filter (fun p => p.Prime ∧
        (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) ≤
        C * (X : ℝ) / Real.log (X : ℝ))
    {j q : ℕ} (hj_gt : (((Finset.Icc 1 X0).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) < (j : ℝ))
    (hq : j ≤ ((Finset.Icc 1 q).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card)
    (hj1 : 1 ≤ j) (hq1 : 1 ≤ q) :
    1 / (q : ℝ) ≤ C / ((j : ℝ) * Real.log (10 * (j : ℝ))) := by
  have hX0q : X0 ≤ q := by
    by_contra hlt
    have hqlt : q ≤ X0 := by omega
    have hsub : (Finset.Icc 1 q).filter (fun p => p.Prime ∧
        (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)) ⊆
        (Finset.Icc 1 X0).filter (fun p => p.Prime ∧
          (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.trans hqlt⟩, hp.2⟩
    have hcard : ((Finset.Icc 1 q).filter (fun p => p.Prime ∧
        (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card ≤
        ((Finset.Icc 1 X0).filter (fun p => p.Prime ∧
          (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card := Finset.card_le_card hsub
    have hcardR : (((Finset.Icc 1 q).filter (fun p => p.Prime ∧
        (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) < (j : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast hcard) hj_gt
    have hjR : (j : ℝ) ≤ ((Finset.Icc 1 q).filter (fun p => p.Prime ∧
        (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card := by exact_mod_cast hq
    linarith
  have hjR : (j : ℝ) ≤ C * (q : ℝ) / Real.log (q : ℝ) :=
    (by exact_mod_cast hq : (j : ℝ) ≤ _).trans (hpi q hX0q)
  have hX0_pos : (0 : ℝ) < (X0 : ℝ) := by
    by_contra h0
    have : X0 = 0 := by
      have hle : X0 ≤ 0 := by exact_mod_cast (by linarith : (X0 : ℝ) ≤ 0)
      omega
    rw [this, Nat.cast_zero, Real.log_zero] at hlogX0; linarith
  have hlogq : 10 * C ≤ Real.log (q : ℝ) := hlogX0.trans (Real.log_le_log hX0_pos (by exact_mod_cast hX0q))
  have hlogq_pos : 0 < Real.log (q : ℝ) := by linarith
  have hq_ge : (1 / C) * (j : ℝ) * Real.log (q : ℝ) ≤ (q : ℝ) := by
    have h1 := (le_div_iff₀ hlogq_pos).mp hjR
    calc (1 / C) * (j : ℝ) * Real.log (q : ℝ) = (j : ℝ) * Real.log (q : ℝ) / C := by ring
      _ ≤ (C * (q : ℝ)) / C := div_le_div_of_nonneg_right h1 hC_pos.le
      _ = (q : ℝ) := by field_simp [hC_pos.ne']
  have h10j : 10 * (j : ℝ) ≤ (q : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlogq (by positivity : 0 ≤ (1 / C) * (j : ℝ))
    have heq : (1 / C) * (j : ℝ) * (10 * C) = 10 * (j : ℝ) := by field_simp [hC_pos.ne']
    linarith
  have hjpos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj1
  have h10j_log : Real.log (10 * (j : ℝ)) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by positivity) h10j
  have h10j_pos : 0 < Real.log (10 * (j : ℝ)) := by
    have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have : 2 ≤ 10 * (j : ℝ) := by linarith
    exact (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) this)
  have hq_ge' : ((j : ℝ) * Real.log (10 * (j : ℝ))) / C ≤ (q : ℝ) := by
    have : (1 / C) * (j : ℝ) * Real.log (10 * (j : ℝ)) ≤ (1 / C) * (j : ℝ) * Real.log (q : ℝ) :=
      mul_le_mul_of_nonneg_left h10j_log (by positivity)
    have hdiv_eq : ((j : ℝ) * Real.log (10 * (j : ℝ))) / C =
        (1 / C) * (j : ℝ) * Real.log (10 * (j : ℝ)) := by ring
    linarith
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq1
  rw [div_le_div_iff₀ hq_pos (by positivity)]
  have h1 : (j : ℝ) * Real.log (10 * (j : ℝ)) ≤ (q : ℝ) * C :=
    (div_le_iff₀ hC_pos).mp hq_ge'
  linarith

private lemma selberg_tail_sum_le (X_hi E : ℕ) (hE : 10 ≤ E)
    (hXhi_ge : 10 ^ 9 ≤ X_hi) (hXhi_le : X_hi ≤ 1001 * 10 ^ (E - 3))
    {P_gt : Finset ℕ} (hP_gt : ∀ p ∈ P_gt, p.Prime ∧ 10000 < p ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))
    (hm : 461 + P_gt.card ≤ X_hi)
    {tail_log_hi : ℝ}
    (htail_log : Real.log (((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (10 * Real.log 10) ≤ tail_log_hi) :
    ∑ p ∈ P_gt, (1 / (p : ℝ)) ≤ (867685 : ℝ) / 1000000 + (19 / 20 : ℝ) * tail_log_hi := by
  let m := P_gt.card
  let q : Fin m ↪o ℕ := P_gt.orderEmbOfFin rfl
  have hsum_eq : ∑ p ∈ P_gt, (1 / (p : ℝ)) = ∑ i : Fin m, (1 / ((q i : ℕ) : ℝ)) := by
    have himg_eq : Finset.univ.image q = P_gt := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        exact Finset.orderEmbOfFin_mem P_gt rfl i
      · rw [Finset.card_image_of_injective _ q.injective, Finset.card_fin]
    rw [← himg_eq, Finset.sum_image (fun i1 _ i2 _ heq => q.injective heq)]
  have hrank : ∀ i : Fin m, 462 + (i : ℕ) ≤ ((Finset.Icc 1 (q i)).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card := fun i => by
    have hq_mem : q i ∈ P_gt := Finset.orderEmbOfFin_mem P_gt rfl i
    obtain ⟨_, hq_gt, _⟩ := hP_gt (q i) hq_mem
    let T0 := (Finset.Icc 1 10000).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))
    let Qi : Finset ℕ := (Finset.range ((i : ℕ) + 1)).attach.image
      (fun k => q ⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩)
    have hT0_sub : T0 ⊆ (Finset.Icc 1 (q i)).filter (fun p => p.Prime ∧
        (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)) := fun p hp => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.trans hq_gt.le⟩, hp.2⟩
    have hQi_sub : Qi ⊆ (Finset.Icc 1 (q i)).filter (fun p => p.Prime ∧
        (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)) := fun p hp => by
      rcases Finset.mem_image.mp hp with ⟨k, _, rfl⟩
      have hk_le : (⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩ : Fin m) ≤ i :=
        Fin.mk_le_mk.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp k.2))
      obtain ⟨hk_pr, _, hk_mod⟩ := hP_gt (q ⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩)
        (Finset.orderEmbOfFin_mem P_gt rfl _)
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hk_pr.one_lt.le, q.monotone hk_le⟩, hk_pr, hk_mod⟩
    have hdisj : Disjoint T0 Qi := Finset.disjoint_left.mpr fun p h1 h2 => by
      rw [Finset.mem_filter, Finset.mem_Icc] at h1
      rcases Finset.mem_image.mp h2 with ⟨k, _, rfl⟩
      obtain ⟨_, hk_gt, _⟩ := hP_gt (q ⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩)
        (Finset.orderEmbOfFin_mem P_gt rfl _)
      omega
    have hQi_card : Qi.card = (i : ℕ) + 1 := by
      have hinj : Function.Injective (fun k : {x // x ∈ Finset.range ((i : ℕ) + 1)} =>
          q ⟨k.1, by have := Finset.mem_range.mp k.2; omega⟩) := by
        intro k1 k2 heq
        have hfk := q.injective heq
        have hv : k1.1 = k2.1 := by simpa using congrArg Fin.val hfk
        exact Subtype.ext hv
      rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, Finset.card_range]
    have hT0_card : 461 ≤ T0.card := p30_10000_data.1
    calc 462 + (i : ℕ) = 461 + ((i : ℕ) + 1) := by ring
      _ ≤ T0.card + Qi.card := by omega
      _ = (T0 ∪ Qi).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ _ := Finset.card_le_card (Finset.union_subset hT0_sub hQi_sub)
  let ub : ℕ → ℝ := fun j =>
    if j ≤ 867 then (1 : ℝ) / 10000
    else if j ≤ 10000 then (100000 : ℝ) / (1549222 * ((j : ℝ) - 221))
    else if j ≤ 100000 then (100000 : ℝ) / (1854689 * ((j : ℝ) - 1975))
    else if j ≤ 1000000 then (100000 : ℝ) / (2151904 * ((j : ℝ) - 17628))
    else if j ≤ 10000000 then (51 / 50 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
    else if j ≤ 1000000000 then (99 / 100 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
    else (19 / 20 : ℝ) / ((j : ℝ) * Real.log (10 * (j : ℝ)))
  have hub_nn : ∀ j : ℕ, 462 ≤ j → 0 ≤ ub j := fun j hj => by
    simp only [ub]
    split_ifs <;> try positivity
    · have : (221 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 221 < j)
      have : (0 : ℝ) < (j : ℝ) - 221 := by linarith
      positivity
    · have : (1975 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 1975 < j)
      have : (0 : ℝ) < (j : ℝ) - 1975 := by linarith
      positivity
    · have : (17628 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 17628 < j)
      have : (0 : ℝ) < (j : ℝ) - 17628 := by linarith
      positivity
    all_goals
      have hj10 : (2 : ℝ) ≤ 10 * (j : ℝ) := by exact_mod_cast (by omega : 2 ≤ 10 * j)
      have := (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) hj10)
      positivity
  have hpi7_lt : (((Finset.Icc 1 (10 ^ 7)).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) < (1000001 : ℝ) := by
    have h1 := pi30_le_10_pow_7 (10 ^ 7) (le_refl _)
    have hlog : (161 / 10 : ℝ) ≤ Real.log ((10 ^ 7 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
    have h2 : (51 / 50 : ℝ) * ((10 ^ 7 : ℕ) : ℝ) / Real.log ((10 ^ 7 : ℕ) : ℝ) ≤
        (51 / 50 : ℝ) * ((10 ^ 7 : ℕ) : ℝ) / (161 / 10) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
    have h3 : (51 / 50 : ℝ) * ((10 ^ 7 : ℕ) : ℝ) / (161 / 10) < 1000001 := by norm_num
    exact (h1.trans h2).trans_lt h3
  have hpi8_lt : (((Finset.Icc 1 (10 ^ 8)).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) < (10000001 : ℝ) := by
    have h1 := pi30_le_10_pow_8 (10 ^ 8) (le_refl _)
    have hlog : (92 / 5 : ℝ) ≤ Real.log ((10 ^ 8 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
    have h2 : (99 / 100 : ℝ) * ((10 ^ 8 : ℕ) : ℝ) / Real.log ((10 ^ 8 : ℕ) : ℝ) ≤
        (99 / 100 : ℝ) * ((10 ^ 8 : ℕ) : ℝ) / (92 / 5) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
    have h3 : (99 / 100 : ℝ) * ((10 ^ 8 : ℕ) : ℝ) / (92 / 5) < 10000001 := by norm_num
    exact (h1.trans h2).trans_lt h3
  have hpi10_lt : (((Finset.Icc 1 (10 ^ 10)).filter (fun p => p.Prime ∧
      (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) < (1000000001 : ℝ) := by
    have h1 := pi30_le_10_pow_10 (10 ^ 10) (le_refl _)
    have hlog : (23 : ℝ) ≤ Real.log ((10 ^ 10 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
    have h2 : (19 / 20 : ℝ) * ((10 ^ 10 : ℕ) : ℝ) / Real.log ((10 ^ 10 : ℕ) : ℝ) ≤
        (19 / 20 : ℝ) * ((10 ^ 10 : ℕ) : ℝ) / 23 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hlog
    have h3 : (19 / 20 : ℝ) * ((10 ^ 10 : ℕ) : ℝ) / 23 < 1000000001 := by norm_num
    exact (h1.trans h2).trans_lt h3
  have hterm_le : ∀ i : Fin m, (1 / ((q i : ℕ) : ℝ)) ≤ ub (462 + (i : ℕ)) := fun i => by
    let j := 462 + (i : ℕ)
    have hj_rk := hrank i
    obtain ⟨hq_pr, hq_gt, _⟩ := hP_gt (q i) (Finset.orderEmbOfFin_mem P_gt rfl i)
    have hq_pos : (0 : ℝ) < ((q i : ℕ) : ℝ) := Nat.cast_pos.mpr hq_pr.pos
    have hfin_sel : ∀ (z c_D : ℕ) (L_lo : ℝ), 1 ≤ z → 0 < L_lo →
        ((Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30)).card = c_D →
        L_lo ≤ ∑ d ∈ (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
          (1 / (d.totient : ℝ)) →
        z + 3 * c_D ^ 2 < j →
        1 / ((q i : ℕ) : ℝ) ≤ 1 / (10 * L_lo * ((j : ℝ) - ((z : ℝ) + 3 * (c_D : ℝ) ^ 2))) := by
      intro z c_D L_lo hz1 hLlo_pos hcD hLL hjk
      have hsel := selberg_pi30_le (q i) z hz1
      rw [hcD] at hsel
      have hjR : (j : ℝ) ≤ (z : ℝ) + ((q i : ℕ) : ℝ) / (10 * L_lo) + 3 * (c_D : ℝ) ^ 2 := by
        have h1 : (j : ℝ) ≤ ((Finset.Icc 1 (q i)).filter (fun p => p.Prime ∧
            (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card := by exact_mod_cast hj_rk
        have hsum_pos : 0 < ∑ d ∈ (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
            (1 / (d.totient : ℝ)) := lt_of_lt_of_le hLlo_pos hLL
        have hdiv : ((q i : ℕ) : ℝ) / (10 * ∑ d ∈ (Finset.Icc 1 z).filter (fun d => Squarefree d ∧ Nat.Coprime d 30),
            (1 / (d.totient : ℝ))) ≤ ((q i : ℕ) : ℝ) / (10 * L_lo) :=
          div_le_div_of_nonneg_left hq_pos.le (by positivity) (by linarith)
        linarith
      have hdiff_pos : (0 : ℝ) < (j : ℝ) - ((z : ℝ) + 3 * (c_D : ℝ) ^ 2) := by
        have hlt : ((z + 3 * c_D ^ 2 : ℕ) : ℝ) < (j : ℝ) := by exact_mod_cast hjk
        push_cast at hlt
        linarith
      have hq_ge : 10 * L_lo * ((j : ℝ) - ((z : ℝ) + 3 * (c_D : ℝ) ^ 2)) ≤ ((q i : ℕ) : ℝ) := by
        have h1 : (j : ℝ) - ((z : ℝ) + 3 * (c_D : ℝ) ^ 2) ≤ ((q i : ℕ) : ℝ) / (10 * L_lo) := by
          linarith
        have := (le_div_iff₀ (by positivity : 0 < 10 * L_lo)).mp h1
        linarith
      exact one_div_le_one_div_of_le (by positivity) hq_ge
    change 1 / ((q i : ℕ) : ℝ) ≤ ub j
    dsimp only [ub]
    by_cases h1 : j ≤ 867
    · rw [if_pos h1]
      have : (10000 : ℝ) ≤ ((q i : ℕ) : ℝ) := by exact_mod_cast hq_gt.le
      exact one_div_le_one_div_of_le (by norm_num) this
    · rw [if_neg h1]
      by_cases h2 : j ≤ 10000
      · rw [if_pos h2]
        have hfin := hfin_sel 29 8 (1549222 / 1000000) (by decide) (by norm_num)
          d29_bound.1 d29_bound.2 (by omega)
        refine hfin.trans_eq ?_
        rw [show ((29 : ℕ) : ℝ) + 3 * ((8 : ℕ) : ℝ) ^ 2 = 221 by norm_num]
        have hjne : (j : ℝ) - 221 ≠ 0 := by
          have : (868 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 868 ≤ j)
          linarith
        field_simp [hjne]; try ring
      · rw [if_neg h2]
        by_cases h3 : j ≤ 100000
        · rw [if_pos h3]
          have hfin := hfin_sel 100 25 (1854689 / 1000000) (by decide) (by norm_num)
            d100_bound.1 d100_bound.2 (by omega)
          refine hfin.trans_eq ?_
          rw [show ((100 : ℕ) : ℝ) + 3 * ((25 : ℕ) : ℝ) ^ 2 = 1975 by norm_num]
          have hjne : (j : ℝ) - 1975 ≠ 0 := by
            have : (10001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 10001 ≤ j)
            linarith
          field_simp [hjne]; try ring
        · rw [if_neg h3]
          by_cases h4 : j ≤ 1000000
          · rw [if_pos h4]
            have hfin := hfin_sel 300 76 (2151904 / 1000000) (by decide) (by norm_num)
              d300_bound.1 d300_bound.2 (by omega)
            refine hfin.trans_eq ?_
            rw [show ((300 : ℕ) : ℝ) + 3 * ((76 : ℕ) : ℝ) ^ 2 = 17628 by norm_num]
            have hjne : (j : ℝ) - 17628 ≠ 0 := by
              have : (100001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 100001 ≤ j)
              linarith
            field_simp [hjne]; try ring
          · rw [if_neg h4]
            by_cases h5 : j ≤ 10000000
            · rw [if_pos h5]
              have hlog : 10 * (51 / 50 : ℝ) ≤ Real.log ((10 ^ 7 : ℕ) : ℝ) := by
                rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
              have hjgt : (((Finset.Icc 1 (10 ^ 7)).filter (fun p => p.Prime ∧
                  (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) < (j : ℝ) := by
                have : (1000001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1000001 ≤ j)
                linarith
              exact asymp_rank_inv_le_clean (10 ^ 7) (51 / 50) (by norm_num) hlog
                pi30_le_10_pow_7 hjgt hj_rk (by omega) hq_pr.pos
            · rw [if_neg h5]
              by_cases h6 : j ≤ 1000000000
              · rw [if_pos h6]
                have hlog : 10 * (99 / 100 : ℝ) ≤ Real.log ((10 ^ 8 : ℕ) : ℝ) := by
                  rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
                have hjgt : (((Finset.Icc 1 (10 ^ 8)).filter (fun p => p.Prime ∧
                    (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) < (j : ℝ) := by
                  have : (10000001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 10000001 ≤ j)
                  linarith
                exact asymp_rank_inv_le_clean (10 ^ 8) (99 / 100) (by norm_num) hlog
                  pi30_le_10_pow_8 hjgt hj_rk (by omega) hq_pr.pos
              · rw [if_neg h6]
                have hlog : 10 * (19 / 20 : ℝ) ≤ Real.log ((10 ^ 10 : ℕ) : ℝ) := by
                  rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith [log_ten_gt]
                have hjgt : (((Finset.Icc 1 (10 ^ 10)).filter (fun p => p.Prime ∧
                    (p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29))).card : ℝ) < (j : ℝ) := by
                  have : (1000000001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1000000001 ≤ j)
                  linarith
                exact asymp_rank_inv_le_clean (10 ^ 10) (19 / 20) (by norm_num) hlog
                  pi30_le_10_pow_10 hjgt hj_rk (by omega) hq_pr.pos
  have hsum_ub : ∑ i : Fin m, ub (462 + (i : ℕ)) ≤ ∑ j ∈ Finset.Ioc 461 X_hi, ub j := by
    have hbij : ∑ i : Fin m, ub (462 + (i : ℕ)) = ∑ j ∈ Finset.Ioc 461 (461 + m), ub j := by
      refine Finset.sum_bij (fun i _ => 462 + (i : ℕ)) ?_ ?_ ?_ ?_
      · intro i _; rw [Finset.mem_Ioc]; omega
      · intro i1 _ i2 _ heq; ext; omega
      · intro j hj
        rw [Finset.mem_Ioc] at hj
        refine ⟨⟨j - 462, by omega⟩, Finset.mem_univ _, by simp; omega⟩
      · intro i _; rfl
    rw [hbij]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hm) fun j hj _ => ?_
    rw [Finset.mem_Ioc] at hj
    exact hub_nn j (by omega)
  have hsub_461_867 : ∑ j ∈ Finset.Ioc 461 867, ub j = (406 : ℝ) / 10000 := by
    have hterm : ∀ j ∈ Finset.Ioc 461 867, ub j = (1 : ℝ) / 10000 := fun j hj => by
      rw [Finset.mem_Ioc] at hj; simp [ub, hj.2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ioc]
    norm_num
  have hsub_867_10k : ∑ j ∈ Finset.Ioc 867 10000, ub j ≤ (1100000 : ℝ) / 6196888 := by
    have hterm : ∀ j ∈ Finset.Ioc 867 10000, ub j = (100000 : ℝ) / 1549222 * (1 / ((j : ℝ) - 221)) := by
      intro j hj; rw [Finset.mem_Ioc] at hj
      have h1 : ¬ j ≤ 867 := by omega
      have hjne : (j : ℝ) - 221 ≠ 0 := by
        have : (868 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
        linarith
      simp [ub, h1, hj.2]; field_simp [hjne]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have htele := sum_Ioc_sub_shift_le 221 867 10000 (by decide) (by decide)
    push_cast at htele
    have hlog : Real.log ((10000 : ℝ) - 221) - Real.log ((867 : ℝ) - 221) < 11 / 4 := by
      have heq : Real.log ((10000 : ℝ) - 221) - Real.log ((867 : ℝ) - 221) = Real.log (9779 / 646) := by
        rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
      rw [heq]
      exact log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    have h1 : (100000 : ℝ) / 1549222 * (Real.log ((10000 : ℝ) - 221) - Real.log ((867 : ℝ) - 221)) ≤
        (100000 : ℝ) / 1549222 * (11 / 4) := mul_le_mul_of_nonneg_left hlog.le (by norm_num)
    have h2 : (100000 : ℝ) / 1549222 * (11 / 4) = 1100000 / 6196888 := by norm_num
    have h3 : (100000 : ℝ) / 1549222 * ∑ j ∈ Finset.Ioc (867 : ℕ) 10000, 1 / ((j : ℝ) - 221) ≤
        (100000 : ℝ) / 1549222 * (Real.log ((10000 : ℝ) - 221) - Real.log ((867 : ℝ) - 221)) :=
      mul_le_mul_of_nonneg_left htele (by norm_num)
    linarith
  have hsub_10k_100k : ∑ j ∈ Finset.Ioc 10000 100000, ub j ≤ (1300000 : ℝ) / 9273445 := by
    have hterm : ∀ j ∈ Finset.Ioc 10000 100000, ub j = (100000 : ℝ) / 1854689 * (1 / ((j : ℝ) - 1975)) := by
      intro j hj; rw [Finset.mem_Ioc] at hj
      have h1 : ¬ j ≤ 867 := by omega
      have h2 : ¬ j ≤ 10000 := by omega
      have hjne : (j : ℝ) - 1975 ≠ 0 := by
        have : (10001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
        linarith
      simp [ub, h1, h2, hj.2]; field_simp [hjne]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have htele := sum_Ioc_sub_shift_le 1975 10000 100000 (by decide) (by decide)
    push_cast at htele
    have hlog : Real.log ((100000 : ℝ) - 1975) - Real.log ((10000 : ℝ) - 1975) < 13 / 5 := by
      have heq : Real.log ((100000 : ℝ) - 1975) - Real.log ((10000 : ℝ) - 1975) =
          Real.log (98025 / 8025) := by
        rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
      rw [heq]
      exact log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    have h1 : (100000 : ℝ) / 1854689 * (Real.log ((100000 : ℝ) - 1975) - Real.log ((10000 : ℝ) - 1975)) ≤
        (100000 : ℝ) / 1854689 * (13 / 5) := mul_le_mul_of_nonneg_left hlog.le (by norm_num)
    have h2 : (100000 : ℝ) / 1854689 * (13 / 5) = 1300000 / 9273445 := by norm_num
    have h3 : (100000 : ℝ) / 1854689 * ∑ j ∈ Finset.Ioc (10000 : ℕ) 100000, 1 / ((j : ℝ) - 1975) ≤
        (100000 : ℝ) / 1854689 * (Real.log ((100000 : ℝ) - 1975) - Real.log ((10000 : ℝ) - 1975)) :=
      mul_le_mul_of_nonneg_left htele (by norm_num)
    linarith
  have hsub_100k_1M : ∑ j ∈ Finset.Ioc 100000 1000000, ub j ≤ (500000 : ℝ) / 4303808 := by
    have hterm : ∀ j ∈ Finset.Ioc 100000 1000000,
        ub j = (100000 : ℝ) / 2151904 * (1 / ((j : ℝ) - 17628)) := by
      intro j hj; rw [Finset.mem_Ioc] at hj
      have h1 : ¬ j ≤ 867 := by omega
      have h2 : ¬ j ≤ 10000 := by omega
      have h3 : ¬ j ≤ 100000 := by omega
      have hjne : (j : ℝ) - 17628 ≠ 0 := by
        have : (100001 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
        linarith
      simp [ub, h1, h2, h3, hj.2]; field_simp [hjne]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have htele := sum_Ioc_sub_shift_le 17628 100000 1000000 (by decide) (by decide)
    push_cast at htele
    have hlog : Real.log ((1000000 : ℝ) - 17628) - Real.log ((100000 : ℝ) - 17628) < 5 / 2 := by
      have heq : Real.log ((1000000 : ℝ) - 17628) - Real.log ((100000 : ℝ) - 17628) =
          Real.log (982372 / 82372) := by
        rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
      rw [heq]
      exact log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    have h1 : (100000 : ℝ) / 2151904 * (Real.log ((1000000 : ℝ) - 17628) - Real.log ((100000 : ℝ) - 17628)) ≤
        (100000 : ℝ) / 2151904 * (5 / 2) := mul_le_mul_of_nonneg_left hlog.le (by norm_num)
    have h2 : (100000 : ℝ) / 2151904 * (5 / 2) = 500000 / 4303808 := by norm_num
    have h3 : (100000 : ℝ) / 2151904 * ∑ j ∈ Finset.Ioc (100000 : ℕ) 1000000, 1 / ((j : ℝ) - 17628) ≤
        (100000 : ℝ) / 2151904 * (Real.log ((1000000 : ℝ) - 17628) - Real.log ((100000 : ℝ) - 17628)) :=
      mul_le_mul_of_nonneg_left htele (by norm_num)
    linarith
  have hsub_1M_10M : ∑ j ∈ Finset.Ioc 1000000 10000000, ub j ≤ (51 : ℝ) / 350 := by
    have hterm : ∀ j ∈ Finset.Ioc 1000000 10000000,
        ub j = (51 / 50 : ℝ) * (1 / ((j : ℝ) * Real.log (10 * (j : ℝ)))) := by
      intro j hj; rw [Finset.mem_Ioc] at hj
      have h1 : ¬ j ≤ 867 := by omega
      have h2 : ¬ j ≤ 10000 := by omega
      have h3 : ¬ j ≤ 100000 := by omega
      have h4 : ¬ j ≤ 1000000 := by omega
      simp [ub, h1, h2, h3, h4, hj.2]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have htele := sum_Ioc_log_log_le 10 (by norm_num) 1000000 10000000 (by decide) (by decide)
    have hlog : Real.log (Real.log (10 * (10000000 : ℝ))) - Real.log (Real.log (10 * (1000000 : ℝ))) ≤ 1 / 7 := by
      have ha_eq : (10 : ℝ) * 1000000 = 10 ^ 7 := by norm_num
      have hb_eq : (10 : ℝ) * 10000000 = 10 ^ 8 := by norm_num
      rw [ha_eq, hb_eq, Real.log_pow, Real.log_pow]
      have hlp : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
      rw [← Real.log_div (by positivity) (by positivity)]
      have hdiv : ((8 : ℕ) : ℝ) * Real.log 10 / (((7 : ℕ) : ℝ) * Real.log 10) = 8 / 7 := by
        push_cast; field_simp [hlp.ne']
      rw [hdiv]
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8 / 7)]
    exact (mul_le_mul_of_nonneg_left (htele.trans hlog) (by norm_num)).trans_eq (by norm_num)
  have hsub_10M_1G : ∑ j ∈ Finset.Ioc 10000000 1000000000, ub j ≤ (99 : ℝ) / 400 := by
    have hterm : ∀ j ∈ Finset.Ioc 10000000 1000000000,
        ub j = (99 / 100 : ℝ) * (1 / ((j : ℝ) * Real.log (10 * (j : ℝ)))) := by
      intro j hj; rw [Finset.mem_Ioc] at hj
      have h1 : ¬ j ≤ 867 := by omega
      have h2 : ¬ j ≤ 10000 := by omega
      have h3 : ¬ j ≤ 100000 := by omega
      have h4 : ¬ j ≤ 1000000 := by omega
      have h5 : ¬ j ≤ 10000000 := by omega
      simp [ub, h1, h2, h3, h4, h5, hj.2]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have htele := sum_Ioc_log_log_le 10 (by norm_num) 10000000 1000000000 (by decide) (by decide)
    have hlog : Real.log (Real.log (10 * (1000000000 : ℝ))) - Real.log (Real.log (10 * (10000000 : ℝ))) ≤ 1 / 4 := by
      have ha_eq : (10 : ℝ) * 10000000 = 10 ^ 8 := by norm_num
      have hb_eq : (10 : ℝ) * 1000000000 = 10 ^ 10 := by norm_num
      rw [ha_eq, hb_eq, Real.log_pow, Real.log_pow]
      have hlp : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
      rw [← Real.log_div (by positivity) (by positivity)]
      have hdiv : ((10 : ℕ) : ℝ) * Real.log 10 / (((8 : ℕ) : ℝ) * Real.log 10) = 5 / 4 := by
        push_cast; field_simp [hlp.ne']; norm_num
      rw [hdiv]
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]
    exact (mul_le_mul_of_nonneg_left (htele.trans hlog) (by norm_num)).trans_eq (by norm_num)
  have hsub_1G_Xhi : ∑ j ∈ Finset.Ioc 1000000000 X_hi, ub j ≤ (19 / 20 : ℝ) * tail_log_hi := by
    have hterm : ∀ j ∈ Finset.Ioc 1000000000 X_hi,
        ub j = (19 / 20 : ℝ) * (1 / ((j : ℝ) * Real.log (10 * (j : ℝ)))) := by
      intro j hj; rw [Finset.mem_Ioc] at hj
      have h1 : ¬ j ≤ 867 := by omega
      have h2 : ¬ j ≤ 10000 := by omega
      have h3 : ¬ j ≤ 100000 := by omega
      have h4 : ¬ j ≤ 1000000 := by omega
      have h5 : ¬ j ≤ 10000000 := by omega
      have h6 : ¬ j ≤ 1000000000 := by omega
      simp [ub, h1, h2, h3, h4, h5, h6]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have htele := sum_Ioc_log_log_le 10 (by norm_num) 1000000000 X_hi (by decide) hXhi_ge
    have h10X_le : Real.log (10 * (X_hi : ℝ)) ≤ ((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000 := by
      have hle_R : (10 : ℝ) * (X_hi : ℝ) ≤ (1001 / 1000 : ℝ) * (10 : ℝ) ^ (E + 1) := by
        have h1 : (X_hi : ℝ) ≤ (1001 : ℝ) * (10 : ℝ) ^ (E - 3) := by exact_mod_cast hXhi_le
        have hE1 : (10 : ℝ) * (1001 : ℝ) * (10 : ℝ) ^ (E - 3) =
            (1001 / 1000 : ℝ) * (10 : ℝ) ^ (E + 1) := by
          have hpow : (10 : ℝ) ^ (E + 1) = (10 : ℝ) ^ (E - 3) * (10 : ℝ) ^ 4 := by
            rw [← pow_add, show E - 3 + 4 = E + 1 by omega]
          rw [hpow]; ring
        linarith
      have hlog_le : Real.log (10 * (X_hi : ℝ)) ≤ Real.log ((1001 / 1000 : ℝ) * (10 : ℝ) ^ (E + 1)) :=
        Real.log_le_log (by
          have : (0 : ℝ) < (X_hi : ℝ) := by exact_mod_cast (by omega : 0 < X_hi)
          positivity) hle_R
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog_le
      have h1001 : Real.log (1001 / 1000 : ℝ) ≤ 1 / 1000 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1001 / 1000)]
      rw [Real.log_mul (by norm_num) (by exact_mod_cast (by omega : X_hi ≠ 0))]
      linarith
    have hlog10_eq : Real.log (Real.log (10 * (1000000000 : ℝ))) = Real.log (10 * Real.log 10) := by
      have : (10 : ℝ) * 1000000000 = (10 : ℝ) ^ 10 := by norm_num
      rw [this, Real.log_pow]; norm_num
    have hlog_top : Real.log (Real.log (10 * (X_hi : ℝ))) ≤
        Real.log (((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) := by
      refine Real.log_le_log ?_ h10X_le
      have : 2 ≤ (10 : ℝ) * (X_hi : ℝ) := by exact_mod_cast (by omega : 2 ≤ 10 * X_hi)
      exact (Real.log_pos (by norm_num)).trans_le (Real.log_le_log (by norm_num) this)
    have hdiff : Real.log (Real.log (10 * (X_hi : ℝ))) - Real.log (Real.log (10 * (1000000000 : ℝ))) ≤ tail_log_hi := by
      linarith [hlog10_eq, hlog_top, htail_log]
    exact mul_le_mul_of_nonneg_left (htele.trans hdiff) (by norm_num)
  have hcomb : ∑ j ∈ Finset.Ioc 461 X_hi, ub j ≤ (867685 : ℝ) / 1000000 + (19 / 20 : ℝ) * tail_log_hi := by
    rw [sum_Ioc_split (by decide : 461 ≤ 867) (by omega : 867 ≤ X_hi)]
    rw [sum_Ioc_split (by decide : 867 ≤ 10000) (by omega : 10000 ≤ X_hi)]
    rw [sum_Ioc_split (by decide : 10000 ≤ 100000) (by omega : 100000 ≤ X_hi)]
    rw [sum_Ioc_split (by decide : 100000 ≤ 1000000) (by omega : 1000000 ≤ X_hi)]
    rw [sum_Ioc_split (by decide : 1000000 ≤ 10000000) (by omega : 10000000 ≤ X_hi)]
    rw [sum_Ioc_split (by decide : 10000000 ≤ 1000000000) hXhi_ge]
    have hnum_sum : (406 : ℝ) / 10000 + 1100000 / 6196888 + 1300000 / 9273445 +
        500000 / 4303808 + 51 / 350 + 99 / 400 ≤ 867685 / 1000000 := by norm_num
    linarith [hsub_461_867, hsub_867_10k, hsub_10k_100k, hsub_100k_1M, hsub_1M_10M,
      hsub_10M_1G, hsub_1G_Xhi, hnum_sum]
  calc ∑ p ∈ P_gt, (1 / (p : ℝ)) = ∑ i : Fin m, (1 / ((q i : ℕ) : ℝ)) := hsum_eq
    _ ≤ ∑ i : Fin m, ub (462 + (i : ℕ)) := Finset.sum_le_sum fun i _ => hterm_le i
    _ ≤ ∑ j ∈ Finset.Ioc 461 X_hi, ub j := hsum_ub
    _ ≤ (867685 : ℝ) / 1000000 + (19 / 20 : ℝ) * tail_log_hi := hcomb

private lemma card_ge_of_sum_gt {n k E : ℕ} (hn0 : n ≠ 0) (h3 : 3 ∣ n) (h5 : 5 ∣ n)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)
    (hsum : (k : ℝ) < ∑ p ∈ n.primeFactors, (1 / (p : ℝ)))
    (hE : 10 ≤ E) {tail_log_hi : ℝ}
    (htail_log : Real.log (((E + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (10 * Real.log 10) ≤ tail_log_hi)
    (hcontra : (1876959 : ℝ) / 1000000 + (19 / 20 : ℝ) * tail_log_hi ≤ (k : ℝ)) :
    10 ^ E ≤ n.primeFactors.card := by
  by_contra hlt
  have hcard_lt : n.primeFactors.card < 10 ^ E := by omega
  let P17 := n.primeFactors.filter (fun p => p % 30 = 17)
  let P23 := n.primeFactors.filter (fun p => p % 30 = 23)
  let P29 := n.primeFactors.filter (fun p => p % 30 = 29)
  let P := n.primeFactors.filter (fun p => p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)
  have hpart := primeFactors_partition_30 hn0 h3 h5 hprimes
  have hP_eq : P = P17 ∪ (P23 ∪ P29) := by
    ext p; simp only [P, P17, P23, P29, Finset.mem_union, Finset.mem_filter]; tauto
  have hnot3 : 3 ∉ insert 5 P := by
    rw [hP_eq]; simp [P17, P23, P29]
  have hnot5 : 5 ∉ P := by
    rw [hP_eq]; simp [P17, P23, P29]
  rw [← hP_eq] at hpart
  have hsum_split : ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) =
      (8 / 15 : ℝ) + ∑ p ∈ P, (1 / (p : ℝ)) := by
    rw [hpart, Finset.sum_insert hnot3, Finset.sum_insert hnot5]
    norm_num; ring
  have hcard_split : n.primeFactors.card = 2 + P.card := by
    rw [hpart, Finset.card_insert_of_notMem hnot3, Finset.card_insert_of_notMem hnot5]
    ring
  let P_le := P.filter (fun p => p ≤ 10000)
  let P_gt := P.filter (fun p => 10000 < p)
  have hP_split : P = P_le ∪ P_gt := by
    ext p
    simp only [P_le, P_gt, Finset.mem_union, Finset.mem_filter]
    by_cases hp : p ≤ 10000
    · simp [hp, show ¬ 10000 < p by omega]
    · simp [hp, show 10000 < p by omega]
  have hP_disj : Disjoint P_le P_gt := Finset.disjoint_left.mpr fun p h1 h2 => by
    simp [P_le, P_gt] at h1 h2; omega
  have hsum_P : ∑ p ∈ P, (1 / (p : ℝ)) =
      (∑ p ∈ P_le, (1 / (p : ℝ))) + ∑ p ∈ P_gt, (1 / (p : ℝ)) := by
    rw [hP_split, Finset.sum_union hP_disj]
  have hPle_sum : ∑ p ∈ P_le, (1 / (p : ℝ)) ≤ (475940 : ℝ) / 1000000 :=
    p30_10000_data.2 P_le fun p hp => by
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      exact ⟨Nat.prime_of_mem_primeFactors hp.1.1, hp.2, hp.1.2⟩
  let X_hi := 1001 * 10 ^ (E - 3)
  have hXhi_ge : 10 ^ 9 ≤ X_hi := by
    have hpow : 10 ^ 7 ≤ 10 ^ (E - 3) := Nat.pow_le_pow_right (by decide) (by omega)
    calc 10 ^ 9 = 100 * 10 ^ 7 := by norm_num
      _ ≤ 1001 * 10 ^ 7 := by omega
      _ ≤ 1001 * 10 ^ (E - 3) := Nat.mul_le_mul_left 1001 hpow
  have hm_le : 461 + P_gt.card ≤ X_hi := by
    have hPgt_le : P_gt.card ≤ P.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hpow7 : 10 ^ 7 ≤ 10 ^ (E - 3) := Nat.pow_le_pow_right (by decide) (by omega)
    have h461 : 461 ≤ 10 ^ (E - 3) := by omega
    have hE_eq : 10 ^ E = 1000 * 10 ^ (E - 3) := by
      rw [show 1000 = 10 ^ 3 by decide, ← pow_add, show 3 + (E - 3) = E by omega]
    calc 461 + P_gt.card ≤ 10 ^ (E - 3) + 10 ^ E := by omega
      _ = 1001 * 10 ^ (E - 3) := by rw [hE_eq]; ring
  have hPgt_sum := selberg_tail_sum_le X_hi E hE hXhi_ge (le_refl _) (fun p hp => by
    rw [Finset.mem_filter, Finset.mem_filter] at hp
    exact ⟨Nat.prime_of_mem_primeFactors hp.1.1, hp.2, hp.1.2⟩) hm_le htail_log
  linarith [hsum, hsum_split, hsum_P, hPle_sum, hPgt_sum, hcontra]

private lemma card_ge_k2 {n : ℕ} (hn0 : n ≠ 0) (h3 : 3 ∣ n) (h5 : 5 ∣ n)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 2) :
    10 ^ 10 ≤ n.primeFactors.card := by
  have hreal := sum_real_gt_k_loc hn0 hsum
  have hlog : Real.log (((10 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (10 * Real.log 10) ≤
      (2301 : ℝ) / 23000 := by
    have hlp : (23 / 10 : ℝ) < Real.log 10 := log_ten_gt
    have hnum_pos : 0 < (10 : ℝ) * Real.log 10 := by linarith
    have h1 : Real.log (((10 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (10 * Real.log 10) =
        Real.log ((((10 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) / (10 * Real.log 10)) := by
      rw [← Real.log_div (by linarith) hnum_pos.ne']
    rw [h1]
    have htan := Real.log_le_sub_one_of_pos
      (div_pos (by linarith : 0 < ((10 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) hnum_pos)
    have hbound : (((10 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) / (10 * Real.log 10) - 1 ≤
        2301 / 23000 := by
      have heq : (((10 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) / (10 * Real.log 10) - 1 =
          1 / 10 + (1 / 1000) / (10 * Real.log 10) := by
        push_cast; field_simp [hnum_pos.ne']; ring
      have hdiv : (1 / 1000 : ℝ) / (10 * Real.log 10) ≤ (1 / 1000) / (10 * (23 / 10)) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      linarith
    linarith
  exact card_ge_of_sum_gt hn0 h3 h5 hprimes (by push_cast at hreal ⊢; exact hreal) (le_refl 10) hlog (by norm_num)

private lemma card_ge_k4 {n : ℕ} (hn0 : n ≠ 0) (h3 : 3 ∣ n) (h5 : 5 ∣ n)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 4) :
    10 ^ 80 ≤ n.primeFactors.card := by
  have hreal := sum_real_gt_k_loc hn0 hsum
  have hlog : Real.log (((80 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (10 * Real.log 10) ≤
      (21 : ℝ) / 10 := by
    have hlp : (23 / 10 : ℝ) < Real.log 10 := log_ten_gt
    have hnum_pos : 0 < (10 : ℝ) * Real.log 10 := by linarith
    rw [← Real.log_div (by linarith) hnum_pos.ne']
    have hratio : (((80 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) / (10 * Real.log 10) < 187 / 23 := by
      have heq : (((80 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) / (10 * Real.log 10) =
          81 / 10 + (1 / 1000) / (10 * Real.log 10) := by
        push_cast; field_simp [hnum_pos.ne']
      have hdiv : (1 / 1000 : ℝ) / (10 * Real.log 10) < (1 / 1000) / (10 * (23 / 10)) :=
        div_lt_div_of_pos_left (by norm_num) (by norm_num) (by linarith)
      linarith
    have hlog1 := Real.log_lt_log (div_pos (by linarith) hnum_pos) hratio
    have hlog2 : Real.log (187 / 23 : ℝ) < 21 / 10 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    linarith
  exact card_ge_of_sum_gt hn0 h3 h5 hprimes (by push_cast at hreal ⊢; exact hreal) (by decide) hlog (by norm_num)

private lemma card_ge_k6 {n k : ℕ} (hn0 : n ≠ 0) (h3 : 3 ∣ n) (h5 : 5 ∣ n)
    (hprimes : ∀ p ∈ n.primeFactors, p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29)
    (hk6 : 6 ≤ k)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    10 ^ 650 ≤ n.primeFactors.card := by
  have hreal := sum_real_gt_k_loc hn0 hsum
  have hk_real : (6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk6
  have hreal6 : (6 : ℝ) < ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) := lt_of_le_of_lt hk_real hreal
  have hlog : Real.log (((650 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) - Real.log (10 * Real.log 10) ≤
      (42 : ℝ) / 10 := by
    have hlp : (23 / 10 : ℝ) < Real.log 10 := log_ten_gt
    have hnum_pos : 0 < (10 : ℝ) * Real.log 10 := by linarith
    rw [← Real.log_div (by linarith) hnum_pos.ne']
    have hratio : (((650 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) / (10 * Real.log 10) < 1498 / 23 := by
      have heq : (((650 + 1 : ℕ) : ℝ) * Real.log 10 + 1 / 1000) / (10 * Real.log 10) =
          651 / 10 + (1 / 1000) / (10 * Real.log 10) := by
        push_cast; field_simp [hnum_pos.ne']
      have hdiv : (1 / 1000 : ℝ) / (10 * Real.log 10) < (1 / 1000) / (10 * (23 / 10)) :=
        div_lt_div_of_pos_left (by norm_num) (by norm_num) (by linarith)
      linarith
    have hlog1 := Real.log_lt_log (div_pos (by linarith) hnum_pos) hratio
    have hlog2 : Real.log (1498 / 23 : ℝ) < 42 / 10 :=
      log_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
    linarith
  exact card_ge_of_sum_gt hn0 h3 h5 hprimes hreal6 (by decide) hlog (by norm_num)

/- ## Section 5: Reduction hypotheses and main theorem -/

def H1 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → 3 ∣ n → 5 ∣ n →
    n % 900 = 705 →
    10 ^ 10 ≤ n.primeFactors.card →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    4 ≤ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (∀ p ∈ n.primeFactors, p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    n.primeFactors.card % 8 = 3 →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 3 →
    n % 27 = (9 * (n.primeFactors.card + 1) + 3) % 27 →
    ((n.primeFactors.filter (fun p => p % 30 = 17)).card +
      3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
      2 * (n.primeFactors.filter (fun p => p % 30 = 29)).card) % 4 = 1 →
    2 ∣ (n.primeFactors.filter (fun p => p % 30 = 29)).card →
    n % 125 = (25 * (2 * (n.primeFactors.filter (fun p => p % 30 = 17)).card +
      3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
      (n.primeFactors.filter (fun p => p % 30 = 29)).card) + 5) % 125 →
    ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 2 →
    False

def H2 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → 3 ∣ n → 5 ∣ n →
    n % 900 = 705 →
    10 ^ 80 ≤ n.primeFactors.card →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    4 ≤ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (∀ p ∈ n.primeFactors, p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    n.primeFactors.card % 8 = 5 →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 1 →
    n % 27 = (9 * (n.primeFactors.card + 3) + 3) % 27 →
    ((n.primeFactors.filter (fun p => p % 30 = 17)).card +
      3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
      2 * (n.primeFactors.filter (fun p => p % 30 = 29)).card) % 4 = 1 →
    2 ∣ (n.primeFactors.filter (fun p => p % 30 = 29)).card →
    n % 125 = (25 * (2 * (n.primeFactors.filter (fun p => p % 30 = 17)).card +
      3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
      (n.primeFactors.filter (fun p => p % 30 = 29)).card + 2) + 5) % 125 →
    ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 4 →
    False

def H3 : Prop :=
  ∀ n k : ℕ, n.Composite → Squarefree n → Odd n → 3 ∣ n → 5 ∣ n →
    n % 900 = 705 →
    10 ^ 650 ≤ n.primeFactors.card →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    4 ≤ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (∀ p ∈ n.primeFactors, p = 3 ∨ p = 5 ∨ p % 30 = 17 ∨ p % 30 = 23 ∨ p % 30 = 29) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    6 ≤ k → 2 ∣ k →
    n.primeFactors.card % 8 = (k + 1) % 8 →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = (k + 1) % 4 →
    n % 27 = (9 * (k + n.primeFactors.card - 1) + 3) % 27 →
    ((n.primeFactors.filter (fun p => p % 30 = 17)).card +
      3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
      2 * (n.primeFactors.filter (fun p => p % 30 = 29)).card) % 4 = 1 →
    2 ∣ (n.primeFactors.filter (fun p => p % 30 = 29)).card →
    n % 125 = (25 * (k + 2 * (n.primeFactors.filter (fun p => p % 30 = 17)).card +
      3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
      (n.primeFactors.filter (fun p => p % 30 = 29)).card + 3) + 5) % 125 →
    ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ) →
    False

theorem main : H1 → H2 → H3 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1.H1 := by
  intro hH1 hH2 hH3 n hnComp hnSqf hnOdd h3 h5 h900 hcard h4r3 h4le hprimes hdvd hnorm hk
  rcases hk with ⟨k, hk2, hk_even, hcard8, hr1_4, hn27, hsum⟩
  have hn0 : n ≠ 0 := by omega
  have hmod4 := five_tail_count_mod_4 hnSqf h3 h5 h900 hprimes
  have hc29 := two_dvd_c29_of_card_odd h3 h5 h900 hprimes hk_even hcard8 hmod4
  have h125 := mod_125_of_three_five_dvd hnSqf h3 h5 h900 hprimes hsum
  have hcases : k = 2 ∨ k = 4 ∨ 6 ≤ k := by
    rcases hk_even with ⟨m, rfl⟩
    omega
  rcases hcases with rfl | rfl | hk6
  · have h10 := card_ge_k2 hn0 h3 h5 hprimes (by simpa using hsum)
    have hcard8' : n.primeFactors.card % 8 = 3 := by simpa using hcard8
    have hr1_4' : (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 3 := by simpa using hr1_4
    have hn27' : n % 27 = (9 * (n.primeFactors.card + 1) + 3) % 27 := by
      have : 2 + n.primeFactors.card - 1 = n.primeFactors.card + 1 := by omega
      rwa [this] at hn27
    have h125' : n % 125 = (25 * (2 * (n.primeFactors.filter (fun p => p % 30 = 17)).card +
        3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
        (n.primeFactors.filter (fun p => p % 30 = 29)).card) + 5) % 125 := by
      rw [h125]
      have : 2 + 2 * (n.primeFactors.filter (fun p => p % 30 = 17)).card +
          3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
          (n.primeFactors.filter (fun p => p % 30 = 29)).card + 3 =
          (2 * (n.primeFactors.filter (fun p => p % 30 = 17)).card +
          3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
          (n.primeFactors.filter (fun p => p % 30 = 29)).card) + 5 := by omega
      rw [this]; omega
    exact hH1 n hnComp hnSqf hnOdd h3 h5 h900 h10 h4r3 h4le hprimes hdvd hnorm
      hcard8' hr1_4' hn27' hmod4 hc29 h125' (by simpa using hsum)
  · have h80 := card_ge_k4 hn0 h3 h5 hprimes (by simpa using hsum)
    have hcard8' : n.primeFactors.card % 8 = 5 := by simpa using hcard8
    have hr1_4' : (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 1 := by simpa using hr1_4
    have hn27' : n % 27 = (9 * (n.primeFactors.card + 3) + 3) % 27 := by
      have : 4 + n.primeFactors.card - 1 = n.primeFactors.card + 3 := by omega
      rwa [this] at hn27
    have h125' : n % 125 = (25 * (2 * (n.primeFactors.filter (fun p => p % 30 = 17)).card +
        3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
        (n.primeFactors.filter (fun p => p % 30 = 29)).card + 2) + 5) % 125 := by
      rw [h125]
      have : 4 + 2 * (n.primeFactors.filter (fun p => p % 30 = 17)).card +
          3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
          (n.primeFactors.filter (fun p => p % 30 = 29)).card + 3 =
          (2 * (n.primeFactors.filter (fun p => p % 30 = 17)).card +
          3 * (n.primeFactors.filter (fun p => p % 30 = 23)).card +
          (n.primeFactors.filter (fun p => p % 30 = 29)).card + 2) + 5 := by omega
      rw [this]; omega
    exact hH2 n hnComp hnSqf hnOdd h3 h5 h900 h80 h4r3 h4le hprimes hdvd hnorm
      hcard8' hr1_4' hn27' hmod4 hc29 h125' (by simpa using hsum)
  · have h650 := card_ge_k6 hn0 h3 h5 hprimes hk6 hsum
    exact hH3 n k hnComp hnSqf hnOdd h3 h5 h900 h650 h4r3 h4le hprimes hdvd hnorm
      hk6 hk_even hcard8 hr1_4 hn27 hmod4 hc29 h125 hsum

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H1_R1_H1_R1

