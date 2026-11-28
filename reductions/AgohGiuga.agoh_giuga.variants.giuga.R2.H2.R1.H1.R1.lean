import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1

/-!
# The factor five in the primary Giuga case

The cofactor of five constrains the prime residue counts modulo five.
The primary reciprocal identity and the product of the prime factors
give a mod-eight count restriction. The remaining cases separate
according to the residue of the original integer modulo eight.
-/

open scoped BigOperators

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1_H1_R1

private lemma minus_one_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p ∈ n.primeFactors)
    (h : p * (p - 1) ∣ n / p - 1) : p - 1 ∣ n - 1 := by
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpdvd := Nat.dvd_of_mem_primeFactors hp
  have hquot : 0 < n / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpdvd) hpprime.pos
  have hd : p - 1 ∣ n / p - 1 := (dvd_mul_left (p - 1) p).trans h
  obtain ⟨a, ha⟩ := hd
  have hreal : n / p = (p - 1) * a + 1 := by omega
  have hmul : n = (p - 1) * (n / p + a) + 1 := calc
    n = p * (n / p) := (Nat.mul_div_cancel' hpdvd).symm
    _ = ((p - 1) + 1) * (n / p) := by rw [Nat.sub_add_cancel hpprime.one_lt.le]
    _ = (p - 1) * (n / p) + n / p := by rw [add_mul, one_mul]
    _ = _ := by rw [show (p - 1) * (n / p + a) = (p - 1) * (n / p) + (p - 1) * a by ring]; omega
  exact ⟨n / p + a, by omega⟩

private lemma five_cofactor_mod {n : ℕ} (hn : n ≠ 0) (h5 : 5 ∣ n)
    (hd : 5 * (5 - 1) ∣ n / 5 - 1) : (n / 5) % 20 = 1 ∧ n % 100 = 5 := by
  have hquot : 0 < n / 5 := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h5) (by decide)
  have hmul := Nat.div_mul_cancel h5
  obtain ⟨a, ha⟩ := (show 20 ∣ n / 5 - 1 from hd)
  omega

private lemma mod_three_of_even_card {n : ℕ} (hn : Squarefree n) (hn3 : ¬ 3 ∣ n)
    (heven : Even n.primeFactors.card)
    (hd : ∀ p ∈ n.primeFactors, p * (p - 1) ∣ n / p - 1) : n % 3 = 1 := by
  by_cases h : ∃ p ∈ n.primeFactors, p % 3 = 1
  · obtain ⟨p, hp, hmod⟩ := h
    have h3 : 3 ∣ p - 1 := Nat.dvd_of_mod_eq_zero (by omega)
    have hz := Nat.mod_eq_zero_of_dvd (h3.trans (minus_one_dvd hn.ne_zero hp (hd p hp)))
    have hnpos := Nat.pos_of_ne_zero hn.ne_zero
    omega
  · have hs (p : ℕ) (hp : p ∈ n.primeFactors) : p ≡ 2 [MOD 3] := by
      have h0 : p % 3 ≠ 0 := fun hz => hn3
        ((Nat.dvd_of_mod_eq_zero hz).trans (Nat.dvd_of_mem_primeFactors hp))
      have h1 : p % 3 ≠ 1 := fun hz => h ⟨p, hp, hz⟩
      change p % 3 = 2
      omega
    have hprod : (∏ p ∈ n.primeFactors, p) ≡ 2 ^ n.primeFactors.card [MOD 3] := by
      simpa only [Finset.prod_const] using Nat.ModEq.prod hs
    obtain ⟨k, hk⟩ := heven
    have hpow : 2 ^ n.primeFactors.card ≡ 1 [MOD 3] := by
      rw [show n.primeFactors.card = 2 * k by omega, pow_mul]
      simpa only [one_pow] using (show (2 : ℕ) ^ 2 ≡ 1 [MOD 3] by decide).pow k
    rw [OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1.prod_primeFactors_of_sqf hn hn.ne_zero] at hprod
    exact hprod.trans hpow

private lemma two_order_four (e : ℕ) (he : 2 ^ e ≡ 1 [MOD 5]) : e % 4 = 0 := by
  have hperiod : 2 ^ (4 * (e / 4)) ≡ 1 [MOD 5] := by
    rw [pow_mul]
    simpa only [one_pow] using (show (2 : ℕ) ^ 4 ≡ 1 [MOD 5] by decide).pow (e / 4)
  have hreduce : 2 ^ e ≡ 2 ^ (e % 4) [MOD 5] := by
    conv_lhs => rw [← Nat.mod_add_div e 4, pow_add]
    simpa only [mul_one] using hperiod.mul_left (2 ^ (e % 4))
  have hsmall := hreduce.symm.trans he
  have hlt : e % 4 < 4 := Nat.mod_lt _ (by decide)
  change (2 ^ (e % 4)) % 5 = 1 at hsmall
  interval_cases h : e % 4 <;> first | rfl | norm_num [h] at hsmall

private lemma count_residues_five (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p % 5)
    (hsodd : s.card % 2 = 1) (hprod : (∏ p ∈ s, p) % 5 = 1) :
    let a := (s.filter (fun p => p % 5 = 2)).card
    let b := (s.filter (fun p => p % 5 = 3)).card
    let c := (s.filter (fun p => p % 5 = 4)).card
    c % 2 = 1 ∧ (a + 3 * b) % 4 = 2 ∧ 2 ≤ a + b := by
  let a := (s.filter (fun p => p % 5 = 2)).card
  let b := (s.filter (fun p => p % 5 = 3)).card
  let c := (s.filter (fun p => p % 5 = 4)).card
  let f (p : ℕ) := (if p % 5 = 2 then 1 else 0) +
    3 * (if p % 5 = 3 then 1 else 0) + 2 * (if p % 5 = 4 then 1 else 0)
  have hf : (∑ p ∈ s, f p) = a + 3 * b + 2 * c := by
    simp only [f, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id, a, b, c]
  have hres (p : ℕ) (hp : p ∈ s) : p ≡ 2 ^ f p [MOD 5] := by
    have h := hs p hp
    have hh : p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
    rcases hh with hz | hz | hz <;> norm_num [Nat.ModEq, f, hz]
  have hp := Nat.ModEq.prod hres
  rw [Finset.prod_pow_eq_pow_sum, hf] at hp
  have hE := two_order_four (a + 3 * b + 2 * c)
    (hp.symm.trans (show (∏ p ∈ s, p) ≡ 1 [MOD 5] from hprod))
  have hc : s.card = a + b + c := by
    have hunit : ∀ p ∈ s,
        (1 : ℕ) = (if p % 5 = 2 then 1 else 0) +
          (if p % 5 = 3 then 1 else 0) + (if p % 5 = 4 then 1 else 0) := by
      intro p hp
      have hh := hs p hp
      have hcases : p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
      rcases hcases with h | h | h <;> norm_num [h]
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_add_distrib,
      Finset.sum_boole, Nat.cast_id, a, b, c] using Finset.sum_congr rfl hunit
  change c % 2 = 1 ∧ (a + 3 * b) % 4 = 2 ∧ 2 ≤ a + b
  omega

private lemma odd_square_mod_eight {a : ℕ} (ha : Odd a) : a * a ≡ 1 [MOD 8] := by
  have ha2 := Nat.odd_iff.mp ha
  have hc : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  change (a * a) % 8 = 1
  rcases hc with h | h | h | h <;> rw [Nat.mul_mod, h]

private lemma five_power_mod_eight (t : ℕ) : 5 ^ t ≡ (1 + 4 * t) [MOD 8] := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [pow_succ]
    refine (ih.mul_right 5).trans ?_
    have h : (1 + 4 * t) * 5 = (1 + 4 * (t + 1)) + 8 * (2 * t) := by ring
    change ((1 + 4 * t) * 5) % 8 = (1 + 4 * (t + 1)) % 8
    rw [h, Nat.add_mul_mod_self_left]

private lemma odd_sum_and_prod_mod_eight (s : Finset ℕ) (hs : ∀ p ∈ s, Odd p) :
    let r := (s.filter (fun p => p % 4 = 3)).card
    let t := (s.filter (fun p => 5 ≤ p % 8)).card
    (∑ p ∈ s, p) ≡ (s.card + 2 * r + 4 * t) [MOD 8] ∧
    (∏ p ∈ s, p) ≡ (3 ^ r * 5 ^ t) [MOD 8] := by
  let f (p : ℕ) := if p % 4 = 3 then 1 else 0
  let g (p : ℕ) := if 5 ≤ p % 8 then 1 else 0
  have hloc (p : ℕ) (hp : p ∈ s) :
      (p ≡ (1 + 2 * f p + 4 * g p) [MOD 8]) ∧
      (p ≡ (3 ^ f p * 5 ^ g p) [MOD 8]) := by
    have h2 := Nat.odd_iff.mp (hs p hp)
    have hc : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
    have hm := Nat.mod_mod_of_dvd p (by decide : 4 ∣ 8)
    rcases hc with h | h | h | h
    · have h4 : p % 4 = 1 := by omega
      norm_num [Nat.ModEq, f, g, h, h4]
    · have h4 : p % 4 = 3 := by omega
      norm_num [Nat.ModEq, f, g, h, h4]
    · have h4 : p % 4 = 1 := by omega
      norm_num [Nat.ModEq, f, g, h, h4]
    · have h4 : p % 4 = 3 := by omega
      norm_num [Nat.ModEq, f, g, h, h4]
  have hsum := Nat.ModEq.sum (fun p hp => (hloc p hp).1)
  have hprod := Nat.ModEq.prod (fun p hp => (hloc p hp).2)
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum] at hprod
  exact ⟨by
    simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Finset.mul_sum, f, g, Finset.sum_boole, Nat.cast_id] using hsum,
    by simpa only [f, g, Finset.sum_boole, Nat.cast_id] using hprod⟩

private lemma card_mod_eight {n : ℕ} (hn : Squarefree n) (hodd : Odd n)
    (hr : 4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card)
    (hsum : (∑ p ∈ n.primeFactors, (1 / (p : ℚ))) - 1 / (n : ℚ) = 1) :
    n.primeFactors.card % 8 = 2 := by
  let s := n.primeFactors
  let r := (s.filter (fun p => p % 4 = 3)).card
  let t := (s.filter (fun p => 5 ≤ p % 8)).card
  have ho (p : ℕ) (hp : p ∈ s) : Odd p := by
    rw [Nat.odd_iff]
    by_contra h
    have hz : p % 2 = 0 := by omega
    have hnz := Nat.mod_eq_zero_of_dvd
      ((Nat.dvd_of_mod_eq_zero hz).trans (Nat.dvd_of_mem_primeFactors hp))
    have hno := Nat.odd_iff.mp hodd
    omega
  obtain ⟨hpsum, hpprod⟩ := odd_sum_and_prod_mod_eight s ho
  change (∑ p ∈ s, p) ≡ (s.card + 2 * r + 4 * t) [MOD 8] at hpsum
  change (∏ p ∈ s, p) ≡ (3 ^ r * 5 ^ t) [MOD 8] at hpprod
  have h3 : 3 ^ r ≡ 1 [MOD 8] := by
    obtain ⟨j, hj⟩ := hr
    change r = 4 * j at hj
    rw [hj, pow_mul]
    simpa only [one_pow] using (show (3 : ℕ) ^ 4 ≡ 1 [MOD 8] by decide).pow j
  rw [show (∏ p ∈ s, p) = n from
    OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1.prod_primeFactors_of_sqf hn hn.ne_zero] at hpprod
  have hn8 : n ≡ (1 + 4 * t) [MOD 8] :=
    hpprod.trans (by simpa only [one_mul] using
      (h3.mul_right (5 ^ t)).trans ((Nat.ModEq.refl 1).mul (five_power_mod_eight t)))
  have hdiv (p : ℕ) (hp : p ∈ s) : n / p ≡ n * p [MOD 8] := by
    have h := (odd_square_mod_eight (ho p hp)).mul_left (n / p)
    rw [← mul_assoc, Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp), mul_one] at h
    exact h.symm
  have hsumdiv := Nat.ModEq.sum hdiv
  rw [show (∑ p ∈ s, n / p) = n + 1 from
    OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1.sum_div_eq_add_one hn.ne_zero hsum,
    ← Finset.mul_sum] at hsumdiv
  have hn2 := odd_square_mod_eight hodd
  have hrecover : (∑ p ∈ s, p) ≡ (n + 1) [MOD 8] := by
    have hh := hsumdiv.mul_left n
    rw [show n * (n + 1) = n + n * n by ring, ← mul_assoc] at hh
    have hleft := (Nat.ModEq.refl n).add hn2
    have hright := hn2.mul_right (∑ p ∈ s, p)
    rw [one_mul] at hright
    exact hright.symm.trans (hh.symm.trans hleft)
  have h := hpsum.symm.trans (hrecover.trans (hn8.add_right 1))
  change (s.card + 2 * r + 4 * t) % 8 = ((1 + 4 * t) + 1) % 8 at h
  change 4 ∣ r at hr
  change s.card % 8 = 2
  omega

private lemma residue_mod_six_hundred {n : ℕ} (h : n % 300 = 205) :
    n % 600 = 205 ∨ n % 600 = 505 := by
  have hmod := Nat.mod_mod_of_dvd n (by decide : 300 ∣ 600)
  omega

private lemma no_one_mod_eight {n p : ℕ} (hn0 : n ≠ 0) (hn8 : n % 8 = 5)
    (hp : p ∈ n.primeFactors) (hd : p * (p - 1) ∣ n / p - 1) : p % 8 ≠ 1 := by
  intro h
  have h8 : 8 ∣ p - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have hh := Nat.mod_eq_zero_of_dvd (h8.trans (minus_one_dvd hn0 hp hd))
  have hnpos := Nat.pos_of_ne_zero hn0
  omega

private lemma odd_card_of_add_one {a b : ℕ} (h : a + 1 = b) (hb : b % 4 = 2) :
    a % 2 = 1 := by omega

/-- The residue of n modulo eight is five, so no prime divisor is one modulo eight. -/
def H1 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) → 5 ∣ n →
    n % 600 = 205 →
    n.primeFactors.card % 8 = 2 → 66 ≤ n.primeFactors.card →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 2 →
    (∀ p ∈ n.primeFactors, 5 ≤ p ∧ p % 5 ≠ 1 ∧ p % 8 ≠ 1) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) →
    (let s := n.primeFactors.erase 5
     let a := (s.filter (fun p => p % 5 = 2)).card
     let b := (s.filter (fun p => p % 5 = 3)).card
     let c := (s.filter (fun p => p % 5 = 4)).card
     c % 2 = 1 ∧ (a + 3 * b) % 4 = 2 ∧ 2 ≤ a + b) →
    False

/-- The residue of n modulo eight is one, with the same constraints on the cofactor of five. -/
def H2 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) → 5 ∣ n →
    n % 600 = 505 →
    n.primeFactors.card % 8 = 2 → 66 ≤ n.primeFactors.card →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 2 →
    (∀ p ∈ n.primeFactors, 5 ≤ p ∧ p % 5 ≠ 1) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) →
    (let s := n.primeFactors.erase 5
     let a := (s.filter (fun p => p % 5 = 2)).card
     let b := (s.filter (fun p => p % 5 = 3)).card
     let c := (s.filter (fun p => p % 5 = 4)).card
     c % 2 = 1 ∧ (a + 3 * b) % 4 = 2 ∧ 2 ≤ a + b) →
    False

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1.H1 := by
  intro h1 h2 n hncomp hsq hodd hn3 hn5 _ hcard hlarge _ hr3 hr1 hres hd hnorm hsum
  have hn0 := hsq.ne_zero
  have hp5 : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_five, hn5, hn0⟩
  obtain ⟨hm20, hn100⟩ := five_cofactor_mod hn0 hn5 (hd 5 hp5)
  have hnmod3 := mod_three_of_even_card hsq hn3 (Nat.even_iff.mpr (by omega)) hd
  have hn300 : n % 300 = 205 := by omega
  have hcard8 := card_mod_eight hsq hodd hr3 hsum
  let s := n.primeFactors.erase 5
  have hmainprod :=
    OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1.prod_primeFactors_of_sqf hsq hn0
  have hmul : 5 * (∏ p ∈ s, p) = n := (Finset.mul_prod_erase _ (fun p => p) hp5).trans hmainprod
  have hcof : (∏ p ∈ s, p) = n / 5 :=
    Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5) (hmul.trans (Nat.mul_div_cancel' hn5).symm)
  have hprod : (∏ p ∈ s, p) % 5 = 1 := by
    rw [hcof, ← Nat.mod_mod_of_dvd (n / 5) (by decide : 5 ∣ 20), hm20]
  have hres' (p : ℕ) (hp : p ∈ s) : 2 ≤ p % 5 := by
    have hpN := Finset.mem_of_mem_erase hp
    have hprime := Nat.prime_of_mem_primeFactors hpN
    have hn1 := (hres p hpN).2
    have hn0 : p % 5 ≠ 0 := fun h => Finset.ne_of_mem_erase hp
      (((Nat.dvd_prime_two_le hprime (by decide : 2 ≤ 5)).mp (Nat.dvd_of_mod_eq_zero h)).symm)
    omega
  have hs_card : s.card + 1 = n.primeFactors.card := Finset.card_erase_add_one hp5
  have hcount := count_residues_five s hres' (odd_card_of_add_one hs_card hcard) hprod
  rcases residue_mod_six_hundred hn300 with h | h
  · have hn8 : n % 8 = 5 := by
      have hmod := Nat.mod_mod_of_dvd n (by decide : 8 ∣ 600)
      rw [h] at hmod
      exact hmod.symm
    exact h1 n hncomp hsq hodd hn3 hn5 h hcard8 hlarge hr3 hr1
      (fun p hp => ⟨(hres p hp).1, (hres p hp).2, no_one_mod_eight hn0 hn8 hp (hd p hp)⟩)
      hd hnorm hsum hcount
  · exact h2 n hncomp hsq hodd hn3 hn5 h hcard8 hlarge hr3 hr1 hres hd hnorm hsum hcount

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1_H1_R1
