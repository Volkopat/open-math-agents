import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1

/-!
# Reduction of the index-one Giuga step with all prime factors at least seven

The factor count is two modulo eight and is at least 218. The two cases
are distinguished by the residue of the number modulo 24. In the second
case, prime divisors that are one modulo eight are excluded.
-/

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1_H2_R1

open OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1

private lemma odd_sq_mod_eight {a : ℕ} (ha : Odd a) : (a : ZMod 8) ^ 2 = 1 := by
  have h := Nat.odd_iff.mp ha
  have cases_a : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  rw [← ZMod.natCast_mod a 8]
  rcases cases_a with h | h | h | h <;> rw [h] <;> decide

private lemma cross_mod_eight {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    ((a : ZMod 8) - 1) * ((b : ZMod 8) - 1) =
      if a % 4 = 3 ∧ b % 4 = 3 then 4 else 0 := by
  have ha_odd := Nat.odd_iff.mp ha
  have hb_odd := Nat.odd_iff.mp hb
  have cases_a : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  have cases_b : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by omega
  have ha4 : a % 4 = a % 8 % 4 := by omega
  have hb4 : b % 4 = b % 8 % 4 := by omega
  rw [← ZMod.natCast_mod a 8, ← ZMod.natCast_mod b 8, ha4, hb4]
  rcases cases_a with h | h | h | h <;> rcases cases_b with k | k | k | k <;>
    rw [h, k] <;> decide

private lemma correction_succ (r : ℕ) :
    (if 2 ≤ (r + 1) % 4 then (4 : ZMod 8) else 0) =
      (if 2 ≤ r % 4 then 4 else 0) + (if r % 2 = 1 then 4 else 0) := by
  have hs : (r + 1) % 4 = (r % 4 + 1) % 4 := by omega
  have hp : r % 2 = r % 4 % 2 := by omega
  have hr : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rw [hs, hp]
  rcases hr with h | h | h | h <;> rw [h] <;> decide

private lemma prod_add_card_mod_eight (s : Finset ℕ) (hodd : ∀ p ∈ s, Odd p) :
    (∏ p ∈ s, (p : ZMod 8)) + (s.card : ZMod 8) =
      1 + (∑ p ∈ s, (p : ZMod 8)) +
        if 2 ≤ (s.filter (fun p => p % 4 = 3)).card % 4 then 4 else 0 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    let r := (s.filter (fun p => p % 4 = 3)).card
    let b := ∏ p ∈ s, p
    have hs : ∀ p ∈ s, Odd p := fun p hp => hodd p (Finset.mem_cons_of_mem hp)
    have haodd : Odd a := hodd a (Finset.mem_cons_self a s)
    have hb4 : b % 4 = if r % 2 = 0 then 1 else 3 := prod_mod_four_of_odd s hs
    have hbodd : Odd b := by
      apply Nat.odd_iff.mpr
      split_ifs at hb4 <;> omega
    have hb3 : b % 4 = 3 ↔ r % 2 = 1 := by
      split_ifs at hb4 <;> omega
    have hcast : (b : ZMod 8) = ∏ p ∈ s, (p : ZMod 8) := Nat.cast_prod _ _
    have hcross := cross_mod_eight haodd hbodd
    simp only [hb3, hcast] at hcross
    have heq :
        (a : ZMod 8) * (∏ p ∈ s, (p : ZMod 8)) + ((s.card : ZMod 8) + 1) =
          ((∏ p ∈ s, (p : ZMod 8)) + (s.card : ZMod 8)) + (a : ZMod 8) +
            (((a : ZMod 8) - 1) * ((∏ p ∈ s, (p : ZMod 8)) - 1)) := by ring
    rw [Finset.prod_cons, Finset.sum_cons, Finset.card_cons, Nat.cast_add, Nat.cast_one,
      heq, ih hs, hcross, Finset.filter_cons]
    by_cases h : a % 4 = 3
    · rw [if_pos h, Finset.card_cons, correction_succ]
      simp only [h, true_and]
      change 1 + (∑ p ∈ s, (p : ZMod 8)) + (if 2 ≤ r % 4 then 4 else 0) + (a : ZMod 8) +
        (if r % 2 = 1 then (4 : ZMod 8) else 0) = _
      ring
    · rw [if_neg h]
      simp only [h, false_and, if_false, add_zero]
      ring

/-- The index-one equation sharpens the upstream factor-count restriction modulo eight. -/
lemma card_mod_eight {n : ℕ} (hsqf : Squarefree n) (hnodd : Odd n)
    (hfour : 4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) :
    n.primeFactors.card % 8 = 2 := by
  have hodd : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    have hfactor := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
    have hnmod := Nat.odd_iff.mp hnodd
    have hpmod := congrArg (· % 2) hfactor
    rw [Nat.mul_mod, hnmod] at hpmod
    apply Nat.odd_iff.mpr
    by_contra h
    have hpzero : p % 2 = 0 := by omega
    simp [hpzero] at hpmod
  have hcofactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      ((n / p : ℕ) : ZMod 8) = (n : ZMod 8) * (p : ZMod 8) := by
    have hmul := congrArg (fun a : ℕ => (a : ZMod 8))
      (Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp))
    push_cast at hmul
    calc
      ((n / p : ℕ) : ZMod 8) = ((n / p : ℕ) : ZMod 8) * (p : ZMod 8) ^ 2 := by
        rw [odd_sq_mod_eight (hodd p hp), mul_one]
      _ = (n : ZMod 8) * (p : ZMod 8) := by rw [pow_two, ← mul_assoc, hmul]
  have hsumZ := congrArg (fun a : ℕ => (a : ZMod 8)) (sum_div_eq_add_one hsqf.ne_zero hsum)
  push_cast at hsumZ
  rw [Finset.sum_congr rfl hcofactor, ← Finset.mul_sum] at hsumZ
  have hsumP : (∑ p ∈ n.primeFactors, (p : ZMod 8)) = (n : ZMod 8) + 1 := by
    calc
      _ = (n : ZMod 8) ^ 2 * (∑ p ∈ n.primeFactors, (p : ZMod 8)) := by
        rw [odd_sq_mod_eight hnodd, one_mul]
      _ = (n : ZMod 8) * ((n : ZMod 8) + 1) := by rw [pow_two, mul_assoc, hsumZ]
      _ = _ := by rw [mul_add, mul_one, ← pow_two, odd_sq_mod_eight hnodd, add_comm]
  have hprod : (∏ p ∈ n.primeFactors, (p : ZMod 8)) = (n : ZMod 8) := by
    rw [← Nat.cast_prod, prod_primeFactors_of_sqf hsqf hsqf.ne_zero]
  have hkey := prod_add_card_mod_eight n.primeFactors hodd
  rw [hprod, hsumP, Nat.mod_eq_zero_of_dvd hfour] at hkey
  have hcard : (n.primeFactors.card : ZMod 8) = 2 := by
    apply add_left_cancel (a := (n : ZMod 8))
    calc
      _ = 1 + ((n : ZMod 8) + 1) + (if 2 ≤ (0 : ℕ) then 4 else 0) := hkey
      _ = _ := by norm_num; ring
  have htwo : (2 : ZMod 8).val = 2 := by decide
  simpa only [ZMod.val_natCast, htwo] using congrArg ZMod.val hcard

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private lemma candidate_certificate (has7 has11 : Bool) :
    ∃ (B : ℕ) (T : Finset ℕ), 0 < B ∧
      (∀ p ∈ T, 0 < p) ∧ (∀ p ∈ T, p ≤ B) ∧
      (∀ p : ℕ, 7 ≤ p → p ≤ B → p.Prime →
        (if has7 then ¬ (7 ∣ p - 1) else p ≠ 7) →
        (if has11 then ¬ (11 ∣ p - 1) else p ≠ 11) → p ∈ T) ∧
      T.card = 214 ∧ ∑ p ∈ T, (1000000 + p - 1) / p < 1000000 := by
  let small : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41}
  have hsmall : ∀ q ∈ small, q.Prime := by decide
  let candidates (B : ℕ) := (Finset.Icc 7 B).filter fun p =>
    (p ∈ small ∨ ∀ q ∈ small, p % q ≠ 0) ∧
      (if has7 then ¬ (7 ∣ p - 1) else p ≠ 7) ∧
      (if has11 then ¬ (11 ∣ p - 1) else p ≠ 11)
  have hcert : ∃ B : ℕ, 0 < B ∧
      (candidates B).card = 214 ∧
      ∑ p ∈ candidates B, (1000000 + p - 1) / p < 1000000 := by
    cases has7 <;> cases has11
    · exact ⟨1367, by decide, by decide⟩
    · exact ⟨1523, by decide, by decide⟩
    · exact ⟨1627, by decide, by decide⟩
    · exact ⟨1847, by decide, by decide⟩
  obtain ⟨B, hB, hcard, hsum⟩ := hcert
  refine ⟨B, candidates B, hB, ?_, ?_, ?_, hcard, hsum⟩
  · intro p hp
    have hp7 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    omega
  · exact fun p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp7 hpB hp h7 h11
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp7, hpB⟩, ?_, h7, h11⟩
    by_cases hmem : p ∈ small
    · exact Or.inl hmem
    · refine Or.inr fun q hq hmod => ?_
      rcases hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero hmod) with h | h
      · exact (hsmall q hq).ne_one h
      · exact hmem (h ▸ hq)

lemma card_gt_214_of_normal {n : ℕ} (hn : 0 < n)
    (hmin : ∀ p ∈ n.primeFactors, 7 ≤ p)
    (hnormal : ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ q - 1))
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) :
    214 < n.primeFactors.card := by
  let has7 := decide (7 ∈ n.primeFactors)
  let has11 := decide (11 ∈ n.primeFactors)
  obtain ⟨B, T, hB, hpos, hle, hfilter, hcard, hsumT⟩ := candidate_certificate has7 has11
  have hcover (p : ℕ) (hp : p ∈ n.primeFactors) (hpB : p ≤ B) : p ∈ T := by
    refine hfilter p (hmin p hp) hpB (Nat.prime_of_mem_primeFactors hp) ?_ ?_
    · change if decide (7 ∈ n.primeFactors) then ¬ (7 ∣ p - 1) else p ≠ 7
      by_cases h7 : 7 ∈ n.primeFactors
      · simpa [h7] using hnormal 7 h7 p hp
      · simpa [h7] using (fun h : p = 7 => h7 (h ▸ hp))
    · change if decide (11 ∈ n.primeFactors) then ¬ (11 ∣ p - 1) else p ≠ 11
      by_cases h11 : 11 ∈ n.primeFactors
      · simpa [h11] using hnormal 11 h11 p hp
      · simpa [h11] using (fun h : p = 11 => h11 (h ▸ hp))
  have hsum_gt : (1 : ℚ) < ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) :=
    OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2.sum_inv_gt_one_of_reciprocal_eq
      (k := 1) hn (by decide) (by simpa using hsum)
  rw [← hcard]
  exact OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2.card_gt_of_sum_inv_gt_one
    (M := 1000000) hB (by decide) hpos hle hcover hsum_gt hsumT

lemma card_ge_218 {n : ℕ} (hsqf : Squarefree n) (hnodd : Odd n)
    (hfour : 4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card)
    (hmin : ∀ p ∈ n.primeFactors, 7 ≤ p)
    (hnormal : ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ q - 1))
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) :
    218 ≤ n.primeFactors.card := by
  have hgt := card_gt_214_of_normal (Nat.pos_of_ne_zero hsqf.ne_zero) hmin hnormal hsum
  have hmod := card_mod_eight hsqf hnodd hfour hsum
  omega

private lemma mod_eq_one_of_factor {n p m : ℕ} (hn : 0 < n) (hm : 1 < m)
    (hp : p ∈ n.primeFactors) (hpmod : p % m = 1)
    (hdiv : p * (p - 1) ∣ n / p - 1) : n % m = 1 := by
  have hpDvd := Nat.dvd_of_mem_primeFactors hp
  have hpPos := Nat.pos_of_mem_primeFactors hp
  have hcoPos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpDvd) hpPos
  have hdecomp := Nat.mod_add_div p m
  have hmp : m ∣ p - 1 := ⟨p / m, by omega⟩
  obtain ⟨k, hk⟩ := hmp.trans ((dvd_mul_left (p - 1) p).trans hdiv)
  have hco : (n / p) % m = 1 := by
    rw [show n / p = m * k + 1 by omega, Nat.add_mod, Nat.mul_mod_right, zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt hm]
  calc
    n % m = (n / p * p) % m := congrArg (· % m) (Nat.div_mul_cancel hpDvd).symm
    _ = 1 := by rw [Nat.mul_mod, hco, hpmod, mul_one, Nat.mod_eq_of_lt hm]

-- uses note #69377
private lemma n_mod_three {n : ℕ} (hsqf : Squarefree n) (hn3 : ¬ (3 ∣ n))
    (hcard : Even n.primeFactors.card)
    (hdiv : ∀ p ∈ n.primeFactors, p * (p - 1) ∣ n / p - 1) : n % 3 = 1 := by
  by_contra h
  have hall (p : ℕ) (hp : p ∈ n.primeFactors) : (p : ZMod 3) = -1 := by
    have hp0 : ¬ (3 ∣ p) := fun h3 => hn3 (h3.trans (Nat.dvd_of_mem_primeFactors hp))
    have hp1 : p % 3 ≠ 1 := fun h1 =>
      h (mod_eq_one_of_factor (Nat.pos_of_ne_zero hsqf.ne_zero) (by decide) hp h1 (hdiv p hp))
    have hp2 : p % 3 = 2 := by omega
    rw [← ZMod.natCast_mod p 3, hp2]
    decide
  have hn : (n : ZMod 3) = 1 := by
    calc
      _ = ∏ p ∈ n.primeFactors, (p : ZMod 3) := by
        rw [← Nat.cast_prod, prod_primeFactors_of_sqf hsqf hsqf.ne_zero]
      _ = (-1 : ZMod 3) ^ n.primeFactors.card := by
        rw [Finset.prod_congr rfl hall, Finset.prod_const]
      _ = _ := hcard.neg_one_pow
  have hone : (1 : ZMod 3).val = 1 := by decide
  exact h (by simpa only [ZMod.val_natCast, hone] using congrArg ZMod.val hn)

def H1 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → ¬ (5 ∣ n) → n % 24 = 1 →
    n.primeFactors.card % 8 = 2 → 218 ≤ n.primeFactors.card →
    (∃ p ∈ n.primeFactors, p % 4 = 1) →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 2 →
    (∀ p ∈ n.primeFactors, 7 ≤ p) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ n / p - 1) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ q - 1)) →
    (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) →
    False

def H2 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → ¬ (5 ∣ n) → n % 24 = 13 →
    (∀ p ∈ n.primeFactors, p % 8 ≠ 1) →
    n.primeFactors.card % 8 = 2 → 218 ≤ n.primeFactors.card →
    (∃ p ∈ n.primeFactors, p % 4 = 1) →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 2 →
    (∀ p ∈ n.primeFactors, 7 ≤ p) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ n / p - 1) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ q - 1)) →
    (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) →
    False

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1.H2 := by
  intro h1 h2 n hcomp hsqf hodd hn3 hn5 hn4 _ _ hsome hr3 hr1 hmin hdiv hnormal hsum
  have hcard8 := card_mod_eight hsqf hodd hr3 hsum
  have hcard := card_ge_218 hsqf hodd hr3 hmin hnormal hsum
  have hneven : Even n.primeFactors.card := Nat.even_iff.mpr (by omega)
  have hnmod3 := n_mod_three hsqf hn3 hneven hdiv
  have hn24 : n % 24 = 1 ∨ n % 24 = 13 := by omega
  rcases hn24 with h | h
  · exact h1 n hcomp hsqf hn5 h hcard8 hcard hsome hr3 hr1 hmin hdiv hnormal hsum
  · have hforbid : ∀ p ∈ n.primeFactors, p % 8 ≠ 1 := by
      intro p hp hp8
      have hn8 := mod_eq_one_of_factor (Nat.pos_of_ne_zero hsqf.ne_zero)
        (by decide) hp hp8 (hdiv p hp)
      omega
    exact h2 n hcomp hsqf hn5 h hforbid hcard8 hcard hsome hr3 hr1 hmin hdiv hnormal hsum

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1_H2_R1
