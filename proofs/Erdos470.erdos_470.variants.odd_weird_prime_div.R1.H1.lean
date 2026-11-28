import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1
import Mathlib


open Finset

theorem deficient_iff_index_lt_two (n : ℕ) (hn : n ≠ 0) :
    n.Deficient ↔ n.abundancyIndex < 2 := by
  rw [Nat.abundancyIndex, div_lt_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)]
  norm_cast
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
  unfold Nat.Deficient
  omega

theorem deficient_of_dvd {m n : ℕ} (hn : n.Deficient) (hm : m ∣ n) :
    m.Deficient := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn.pos
  have hm0 : m ≠ 0 := by intro hm0; subst m; simp at hm; exact hn0 hm
  rw [deficient_iff_index_lt_two m hm0]
  exact lt_of_le_of_lt (Nat.abundancyIndex_le_of_dvd hn0 hm)
    ((deficient_iff_index_lt_two n hn0).mp hn)

theorem index_mul_of_coprime (a b : ℕ) (h : a.Coprime b) :
    (a * b).abundancyIndex = a.abundancyIndex * b.abundancyIndex := by
  simp only [Nat.abundancyIndex, Nat.Coprime.sum_divisors_mul h, Nat.cast_mul]
  ring

theorem prime_power_index_lt (p e : ℕ) (hp : p.Prime) :
    (p ^ e).abundancyIndex < (p : ℚ) / ((p : ℚ) - 1) := by
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hpow : (0 : ℚ) < (p : ℚ) ^ e := pow_pos (by linarith) _
  rw [Nat.abundancyIndex, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  apply (div_lt_div_iff₀ hpow (by linarith : (0 : ℚ) < (p : ℚ) - 1)).2
  have hgeom := geom_sum_mul (p : ℚ) (e + 1)
  rw [pow_succ] at hgeom
  linarith

theorem abundant_prime_factor_gap_bound (c p e : ℕ) (hp : p.Prime)
    (hcop : c.Coprime (p ^ e)) (ha : (c * p ^ e).Abundant)
    (delta : ℚ) (_hd : 0 < delta) (hc : c.abundancyIndex ≤ 2 - delta) :
    delta * p < 2 := by
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hnonneg : 0 ≤ c.abundancyIndex := by
    unfold Nat.abundancyIndex
    positivity
  have hfac := prime_power_index_lt p e hp
  have hprod := mul_le_mul_of_nonneg_left (le_of_lt hfac) hnonneg
  have hab : 2 < c.abundancyIndex * (p ^ e).abundancyIndex := by
    rw [← index_mul_of_coprime c (p ^ e) hcop]
    exact Nat.abundant_iff_two_lt_abundancyIndex.mp ha
  have hquot : 2 < c.abundancyIndex * ((p : ℚ) / ((p : ℚ) - 1)) := lt_of_lt_of_le hab hprod
  have hquot' : 2 * ((p : ℚ) - 1) < c.abundancyIndex * p := by
    rw [← mul_div_assoc] at hquot
    exact (lt_div_iff₀ (by linarith : (0 : ℚ) < (p : ℚ) - 1)).mp hquot
  nlinarith

theorem numeric_prime_bound (p : ℕ)
    (h : (2798 / 51134034375 : ℚ) * p < 2) : p ≤ 36550417 := by
  by_contra hn
  have hp : (36550418 : ℚ) ≤ p := by exact_mod_cast (by omega : 36550418 ≤ p)
  norm_num at h
  nlinarith

theorem prime_bound_of_core_gap (m p : ℕ) (ha : m.Abundant)
    (hp : p ∈ m.primeFactors)
    (hgap : (ordCompl[p] m).abundancyIndex ≤ 2 - (2798 / 51134034375 : ℚ)) :
    p ≤ 36550417 := by
  obtain ⟨hpp, hpd, hm0⟩ := Nat.mem_primeFactors.mp hp
  have hdecomp : ordCompl[p] m * p ^ (m.factorization p) = m := by
    simpa [mul_comm] using Nat.ordProj_mul_ordCompl_eq_self m p
  have hcop : (ordCompl[p] m).Coprime (p ^ m.factorization p) :=
    (Nat.coprime_ordCompl hpp hm0).symm.pow_right _
  apply numeric_prime_bound p
  apply abundant_prime_factor_gap_bound (ordCompl[p] m) p (m.factorization p) hpp hcop
  · simpa [hdecomp] using ha
  · norm_num
  · exact hgap

theorem core_properties (m p : ℕ) (ho : Odd m) (hp : p ∈ m.primeFactors)
    (hcard : m.primeFactors.card ≤ 5)
    (hdef : ∀ d ∈ m.properDivisors, d.Deficient) :
    Odd (ordCompl[p] m) ∧ (ordCompl[p] m).Deficient ∧
      (ordCompl[p] m).primeFactors.card ≤ 4 := by
  obtain ⟨hpp, hpd, hm0⟩ := Nat.mem_primeFactors.mp hp
  have hdiv := Nat.ordCompl_dvd m p
  have hne : ordCompl[p] m ≠ m := by
    intro heq
    exact (Nat.ordCompl_eq_self_iff_zero_or_not_dvd m hpp).mp heq |>.elim hm0 (fun h => h hpd)
  have hlt : ordCompl[p] m < m := lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdiv) hne
  refine ⟨ho.of_dvd_nat hdiv, hdef _ (Nat.mem_properDivisors.mpr ⟨hdiv, hlt⟩), ?_⟩
  have hsub : (ordCompl[p] m).primeFactors ⊆ m.primeFactors.erase p := by
    intro q hq
    rw [Finset.mem_erase]
    have hqdata := Nat.mem_primeFactors.mp hq
    refine ⟨?_, Nat.mem_primeFactors.mpr ⟨hqdata.1, dvd_trans hqdata.2.1 hdiv, hm0⟩⟩
    intro heq
    subst q
    exact Nat.not_dvd_ordCompl hpp hm0 hqdata.2.1
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hp] at hc
  omega

theorem prime_bounds_from_core_gap (m : ℕ) (ho : Odd m) (ha : m.Abundant)
    (hcard : m.primeFactors.card ≤ 5)
    (hdef : ∀ d ∈ m.properDivisors, d.Deficient)
    (hgap : ∀ c : ℕ, Odd c → c.Deficient → c.primeFactors.card ≤ 4 →
      c.abundancyIndex ≤ 2 - (2798 / 51134034375 : ℚ)) :
    ∀ p ∈ m.primeFactors, p ≤ 36550417 := by
  intro p hp
  obtain ⟨ho', hd', hc'⟩ := core_properties m p ho hp hcard hdef
  exact prime_bound_of_core_gap m p ha hp (hgap _ ho' hd' hc')


theorem prime_power_index_mono (p a b : ℕ) (hp : p.Prime) (h : a ≤ b) :
    (p ^ a).abundancyIndex ≤ (p ^ b).abundancyIndex := by
  apply Nat.abundancyIndex_le_of_dvd (pow_ne_zero _ hp.ne_zero)
  exact pow_dvd_pow p h

theorem prime_power_index_box (p e cap : ℕ) (hp : p.Prime) :
    (p ^ min e cap).abundancyIndex ≤ (p ^ e).abundancyIndex ∧
    (p ^ e).abundancyIndex < (p : ℚ) / ((p : ℚ) - 1) := by
  exact ⟨prime_power_index_mono p (min e cap) e hp (min_le_left _ _),
    prime_power_index_lt p e hp⟩

theorem prime_power_index_formula (p e : ℕ) (hp : p.Prime) :
    (p ^ e).abundancyIndex = (((p : ℚ) ^ (e + 1)) - 1) /
      (((p : ℚ) - 1) * (p : ℚ) ^ e) := by
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hpow : (0 : ℚ) < (p : ℚ) ^ e := pow_pos (by linarith) _
  rw [Nat.abundancyIndex, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  have hgeom := geom_sum_mul (p : ℚ) (e + 1)
  have hpne : (p : ℚ) - 1 ≠ 0 := by linarith
  field_simp
  nlinarith

def indexBoxUpper (p e cap : ℕ) : ℚ :=
  if e < cap then (p ^ e).abundancyIndex else (p : ℚ) / ((p : ℚ) - 1)

theorem indexBoxUpper_valid (p e cap : ℕ) (hp : p.Prime) :
    (p ^ e).abundancyIndex ≤ indexBoxUpper p (min e cap) cap := by
  unfold indexBoxUpper
  split_ifs with h
  · rw [min_eq_left (by omega : e ≤ cap)]
  · exact le_of_lt (prime_power_index_lt p e hp)

theorem index_prod_prime_powers (s : Finset ℕ) (e : ℕ → ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p ^ e p).abundancyIndex = ∏ p ∈ s, (p ^ e p).abundancyIndex := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Nat.abundancyIndex]
  | @insert p s hp ih =>
    have hprime : p.Prime := hs p (Finset.mem_insert_self _ _)
    have hs' : ∀ q ∈ s, q.Prime := by
      intro q hq; exact hs q (Finset.mem_insert_of_mem hq)
    have hcop : (p ^ e p).Coprime (∏ q ∈ s, q ^ e q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hne : p ≠ q := by intro heq; subst q; exact hp hq
      have hc : p.Coprime q := hprime.coprime_iff_not_dvd.mpr (by
        intro hdvd
        exact hne ((Nat.prime_dvd_prime_iff_eq hprime (hs' q hq)).mp hdvd))
      exact (hc.pow_left _).pow_right _
    simp only [Finset.prod_insert hp]
    rw [index_mul_of_coprime _ _ hcop, ih hs']

theorem index_factorization (n : ℕ) (hn : n ≠ 0) :
    n.abundancyIndex = ∏ p ∈ n.primeFactors,
      (p ^ n.factorization p).abundancyIndex := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  apply index_prod_prime_powers
  exact fun p hp => Nat.prime_of_mem_primeFactors hp

theorem index_factorization_upper (n : ℕ) (hn : n ≠ 0) :
    n.abundancyIndex ≤ ∏ p ∈ n.primeFactors, (p : ℚ) / ((p : ℚ) - 1) := by
  rw [index_factorization n hn]
  apply Finset.prod_le_prod
  · intro p hp
    unfold Nat.abundancyIndex
    positivity
  · intro p hp
    exact le_of_lt (prime_power_index_lt p (n.factorization p) (Nat.prime_of_mem_primeFactors hp))

theorem prime_ratio_antitone (p k : ℕ) (hk : 1 < k) (hpk : k ≤ p) :
    (p : ℚ) / ((p : ℚ) - 1) ≤ (k : ℚ) / ((k : ℚ) - 1) := by
  have hkq : (1 : ℚ) < k := by exact_mod_cast hk
  have hpq : (k : ℚ) ≤ p := by exact_mod_cast hpk
  apply (div_le_div_iff₀ (by linarith : (0 : ℚ) < (p : ℚ) - 1)
    (by linarith : (0 : ℚ) < (k : ℚ) - 1)).2
  nlinarith

theorem prime_ratio_prod_bound (s : Finset ℕ) (k cap : ℕ) (hk : 1 < k)
    (hcard : s.card ≤ cap) (hsmall : ∀ p ∈ s, k ≤ p) :
    (∏ p ∈ s, (p : ℚ) / ((p : ℚ) - 1)) ≤
      ((k : ℚ) / ((k : ℚ) - 1)) ^ cap := by
  have hkq : (1 : ℚ) < k := by exact_mod_cast hk
  have hratio : (1 : ℚ) ≤ (k : ℚ) / ((k : ℚ) - 1) := by
    apply (le_div_iff₀ (by linarith : (0 : ℚ) < (k : ℚ) - 1)).2
    linarith
  calc
    (∏ p ∈ s, (p : ℚ) / ((p : ℚ) - 1)) ≤
        ∏ _p ∈ s, ((k : ℚ) / ((k : ℚ) - 1)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have : (1 : ℚ) < p := by exact_mod_cast (lt_of_lt_of_le hk (hsmall p hp))
        positivity
      · intro p hp
        exact prime_ratio_antitone p k hk (hsmall p hp)
    _ = ((k : ℚ) / ((k : ℚ) - 1)) ^ s.card := by simp only [Finset.prod_const]
    _ ≤ ((k : ℚ) / ((k : ℚ) - 1)) ^ cap := pow_le_pow_right₀ hratio hcard

theorem odd_prime_ge_seven (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (h3 : p ≠ 3) (h5 : p ≠ 5) : 7 ≤ p := by
  by_contra hn
  have hlt : p < 7 := by omega
  interval_cases p <;> norm_num [Nat.prime_def_lt] at *

theorem near_two_core_has_three (n : ℕ) (hn : n ≠ 0) (ho : Odd n)
    (hcard : n.primeFactors.card ≤ 4)
    (hnear : 2 - (2798 / 51134034375 : ℚ) < n.abundancyIndex) :
    3 ∈ n.primeFactors := by
  by_contra h3
  have hub := index_factorization_upper n hn
  by_cases h5 : 5 ∈ n.primeFactors
  · have hcard' : (n.primeFactors.erase 5).card ≤ 3 := by
      rw [Finset.card_erase_of_mem h5]; omega
    have hsmall : ∀ p ∈ n.primeFactors.erase 5, 7 ≤ p := by
      intro p hp
      have hmem := (Finset.mem_erase.mp hp).2
      have hp3 : p ≠ 3 := by intro heq; subst p; exact h3 hmem
      have hp5 : p ≠ 5 := (Finset.mem_erase.mp hp).1
      exact odd_prime_ge_seven p (Nat.prime_of_mem_primeFactors hmem)
        (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hmem)) hp3 hp5
    have hprod := prime_ratio_prod_bound (n.primeFactors.erase 5) 7 3 (by decide) hcard' hsmall
    have hsplit : (∏ p ∈ n.primeFactors, (p : ℚ) / ((p : ℚ) - 1)) =
        (5 : ℚ)/4 * ∏ p ∈ n.primeFactors.erase 5, (p : ℚ) / ((p : ℚ) - 1) := by
      rw [← Finset.mul_prod_erase _ _ h5]
      norm_num
    rw [hsplit] at hub
    have hv : ((7 : ℚ) / (7 - 1)) ^ 3 = (343 : ℚ) / 216 := by norm_num
    norm_num only [Nat.cast_ofNat] at hprod
    linarith
  · have hsmall : ∀ p ∈ n.primeFactors, 7 ≤ p := by
      intro p hp
      have hp3 : p ≠ 3 := by intro heq; subst p; exact h3 hp
      have hp5 : p ≠ 5 := by intro heq; subst p; exact h5 hp
      exact odd_prime_ge_seven p (Nat.prime_of_mem_primeFactors hp)
        (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)) hp3 hp5
    have hprod := prime_ratio_prod_bound n.primeFactors 7 4 (by decide) hcard hsmall
    have hv : ((7 : ℚ) / (7 - 1)) ^ 4 = (2401 : ℚ) / 1296 := by norm_num
    norm_num only [Nat.cast_ofNat] at hprod
    linarith

theorem odd_prime_ge_eleven (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (h3 : p ≠ 3) (h5 : p ≠ 5) (h7 : p ≠ 7) : 11 ≤ p := by
  by_contra hn
  have hlt : p < 11 := by omega
  interval_cases p <;> norm_num [Nat.prime_def_lt] at *
  all_goals obtain ⟨k, hk⟩ := ho; omega

theorem near_two_core_has_five_or_seven (n : ℕ) (hn : n ≠ 0) (ho : Odd n)
    (hcard : n.primeFactors.card ≤ 4)
    (hnear : 2 - (2798 / 51134034375 : ℚ) < n.abundancyIndex) :
    5 ∈ n.primeFactors ∨ 7 ∈ n.primeFactors := by
  by_contra hc
  push Not at hc
  obtain ⟨h5, h7⟩ := hc
  have h3 := near_two_core_has_three n hn ho hcard hnear
  have hub := index_factorization_upper n hn
  have hcard' : (n.primeFactors.erase 3).card ≤ 3 := by
    rw [Finset.card_erase_of_mem h3]; omega
  have hsmall : ∀ p ∈ n.primeFactors.erase 3, 11 ≤ p := by
    intro p hp
    have hmem := (Finset.mem_erase.mp hp).2
    have hp3 : p ≠ 3 := (Finset.mem_erase.mp hp).1
    have hp5 : p ≠ 5 := by intro heq; subst p; exact h5 hmem
    have hp7 : p ≠ 7 := by intro heq; subst p; exact h7 hmem
    exact odd_prime_ge_eleven p (Nat.prime_of_mem_primeFactors hmem)
      (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hmem)) hp3 hp5 hp7
  have hprod := prime_ratio_prod_bound (n.primeFactors.erase 3) 11 3 (by decide) hcard' hsmall
  have hsplit : (∏ p ∈ n.primeFactors, (p : ℚ) / ((p : ℚ) - 1)) =
      (3 : ℚ)/2 * ∏ p ∈ n.primeFactors.erase 3, (p : ℚ) / ((p : ℚ) - 1) := by
    rw [← Finset.mul_prod_erase _ _ h3]
    norm_num
  rw [hsplit] at hub
  norm_num only [Nat.cast_ofNat] at hprod
  linarith

theorem near_two_requires_third (n a b k : ℕ) (hn : n ≠ 0)
    (ha : a ∈ n.primeFactors) (hb : b ∈ n.primeFactors) (hab : a ≠ b)
    (hk : 1 < k) (hcard : n.primeFactors.card ≤ 4)
    (hnear : 2 - (2798 / 51134034375 : ℚ) < n.abundancyIndex)
    (hbound : ((a : ℚ) / ((a : ℚ) - 1)) * ((b : ℚ) / ((b : ℚ) - 1)) *
      ((k : ℚ) / ((k : ℚ) - 1)) ^ 2 ≤ 2 - (2798 / 51134034375 : ℚ)) :
    ∃ p ∈ n.primeFactors, p ≠ a ∧ p ≠ b ∧ p < k := by
  classical
  by_contra hex
  have hb' : b ∈ n.primeFactors.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  let rest := (n.primeFactors.erase a).erase b
  have hsmall : ∀ p ∈ rest, k ≤ p := by
    intro p hp
    have hp' := Finset.mem_erase.mp hp
    have hp'' := Finset.mem_erase.mp hp'.2
    by_contra h
    exact hex ⟨p, hp''.2, hp''.1, hp'.1, by omega⟩
  have hrestcard : rest.card ≤ 2 := by
    dsimp [rest]
    rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
    omega
  have hrest := prime_ratio_prod_bound rest k 2 hk hrestcard hsmall
  have hdecomp : (∏ p ∈ n.primeFactors, (p : ℚ) / ((p : ℚ) - 1)) =
      ((a : ℚ) / ((a : ℚ) - 1)) * (((b : ℚ) / ((b : ℚ) - 1)) *
      ∏ p ∈ rest, (p : ℚ) / ((p : ℚ) - 1)) := by
    rw [← Finset.mul_prod_erase _ _ ha, ← Finset.mul_prod_erase _ _ hb']
  have hapos : 0 ≤ (a : ℚ) / ((a : ℚ) - 1) := by
    have hp := (Nat.prime_of_mem_primeFactors ha).one_lt
    have : (1 : ℚ) < a := by exact_mod_cast hp
    positivity
  have hbpos : 0 ≤ (b : ℚ) / ((b : ℚ) - 1) := by
    have hp := (Nat.prime_of_mem_primeFactors hb).one_lt
    have : (1 : ℚ) < b := by exact_mod_cast hp
    positivity
  have hub := index_factorization_upper n hn
  rw [hdecomp] at hub
  have hx := mul_le_mul_of_nonneg_left hrest (mul_nonneg hapos hbpos)
  nlinarith

theorem near_two_three_five_third (n : ℕ) (hn : n ≠ 0)
    (h3 : 3 ∈ n.primeFactors) (h5 : 5 ∈ n.primeFactors)
    (hcard : n.primeFactors.card ≤ 4)
    (hnear : 2 - (2798 / 51134034375 : ℚ) < n.abundancyIndex) :
    ∃ p ∈ n.primeFactors, p ≠ 3 ∧ p ≠ 5 ∧ p < 32 := by
  apply near_two_requires_third n 3 5 32 hn h3 h5 (by decide) (by decide) hcard hnear
  norm_num

theorem near_two_three_seven_third (n : ℕ) (hn : n ≠ 0)
    (h3 : 3 ∈ n.primeFactors) (h7 : 7 ∈ n.primeFactors)
    (hcard : n.primeFactors.card ≤ 4)
    (hnear : 2 - (2798 / 51134034375 : ℚ) < n.abundancyIndex) :
    ∃ p ∈ n.primeFactors, p ≠ 3 ∧ p ≠ 7 ∧ p < 17 := by
  apply near_two_requires_third n 3 7 17 hn h3 h7 (by decide) (by decide) hcard hnear
  norm_num

theorem small_odd_prime_list (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (h3 : p ≠ 3) (h5 : p ≠ 5) (h32 : p < 32) :
    p ∈ ({7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ) := by
  interval_cases p <;> norm_num [Nat.prime_def_lt] at *

theorem very_small_odd_prime_list (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (h3 : p ≠ 3) (h5 : p ≠ 5) (h7 : p ≠ 7) (h17 : p < 17) :
    p ∈ ({11, 13} : Finset ℕ) := by
  interval_cases p <;> norm_num [Nat.prime_def_lt] at *

theorem near_two_core_prime_patterns (n : ℕ) (hn : n ≠ 0) (ho : Odd n)
    (hcard : n.primeFactors.card ≤ 4)
    (hnear : 2 - (2798 / 51134034375 : ℚ) < n.abundancyIndex) :
    3 ∈ n.primeFactors ∧
      ((5 ∈ n.primeFactors ∧ ∃ p ∈ n.primeFactors,
          p ∈ ({7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ)) ∨
       (7 ∈ n.primeFactors ∧ ∃ p ∈ n.primeFactors, p ∈ ({11, 13} : Finset ℕ))) := by
  have h3 := near_two_core_has_three n hn ho hcard hnear
  refine ⟨h3, ?_⟩
  by_cases h5 : 5 ∈ n.primeFactors
  · left
    obtain ⟨p, hp, hp3, hp5, hplt⟩ := near_two_three_five_third n hn h3 h5 hcard hnear
    exact ⟨h5, p, hp, small_odd_prime_list p (Nat.prime_of_mem_primeFactors hp)
      (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)) hp3 hp5 hplt⟩
  · right
    have h7 := (near_two_core_has_five_or_seven n hn ho hcard hnear).resolve_left h5
    obtain ⟨p, hp, hp3, hp7, hplt⟩ := near_two_three_seven_third n hn h3 h7 hcard hnear
    have hp5 : p ≠ 5 := by intro heq; subst p; exact h5 hp
    exact ⟨h7, p, hp, very_small_odd_prime_list p (Nat.prime_of_mem_primeFactors hp)
      (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)) hp3 hp5 hp7 hplt⟩

theorem near_two_requires_fourth (n a b c k : ℕ) (hn : n ≠ 0)
    (ha : a ∈ n.primeFactors) (hb : b ∈ n.primeFactors) (hc : c ∈ n.primeFactors)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hk : 1 < k) (hcard : n.primeFactors.card ≤ 4)
    (hnear : 2 - (2798 / 51134034375 : ℚ) < n.abundancyIndex)
    (hbound : ((a : ℚ) / ((a : ℚ) - 1)) * ((b : ℚ) / ((b : ℚ) - 1)) *
      ((c : ℚ) / ((c : ℚ) - 1)) * ((k : ℚ) / ((k : ℚ) - 1)) ≤
      2 - (2798 / 51134034375 : ℚ)) :
    ∃ p ∈ n.primeFactors, p ≠ a ∧ p ≠ b ∧ p ≠ c ∧ p < k := by
  classical
  by_contra hex
  have hb' : b ∈ n.primeFactors.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have hc' : c ∈ (n.primeFactors.erase a).erase b :=
    Finset.mem_erase.mpr ⟨Ne.symm hbc, Finset.mem_erase.mpr ⟨Ne.symm hac, hc⟩⟩
  let rest := ((n.primeFactors.erase a).erase b).erase c
  have hsmall : ∀ p ∈ rest, k ≤ p := by
    intro p hp
    have h1 := Finset.mem_erase.mp hp
    have h2 := Finset.mem_erase.mp h1.2
    have h3 := Finset.mem_erase.mp h2.2
    by_contra h
    exact hex ⟨p, h3.2, h3.1, h2.1, h1.1, by omega⟩
  have hrestcard : rest.card ≤ 1 := by
    dsimp [rest]
    rw [Finset.card_erase_of_mem hc', Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
    omega
  have hrest := prime_ratio_prod_bound rest k 1 hk hrestcard hsmall
  have hdecomp : (∏ p ∈ n.primeFactors, (p : ℚ) / ((p : ℚ) - 1)) =
      ((a : ℚ) / ((a : ℚ) - 1)) * (((b : ℚ) / ((b : ℚ) - 1)) *
      (((c : ℚ) / ((c : ℚ) - 1)) * ∏ p ∈ rest, (p : ℚ) / ((p : ℚ) - 1))) := by
    rw [← Finset.mul_prod_erase _ _ ha, ← Finset.mul_prod_erase _ _ hb',
      ← Finset.mul_prod_erase _ _ hc']
  have hpos : ∀ p ∈ n.primeFactors, 0 ≤ (p : ℚ) / ((p : ℚ) - 1) := by
    intro p hp
    have hprime := (Nat.prime_of_mem_primeFactors hp).one_lt
    have : (1 : ℚ) < p := by exact_mod_cast hprime
    positivity
  have hub := index_factorization_upper n hn
  rw [hdecomp] at hub
  simp only [pow_one] at hrest
  have hx := mul_le_mul_of_nonneg_left hrest (mul_nonneg (mul_nonneg (hpos a ha) (hpos b hb)) (hpos c hc))
  nlinarith

theorem small_odd_prime_list_no31 (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (h3 : p ≠ 3) (h5 : p ≠ 5) (h31 : p ≠ 31) (h37 : p < 37) :
    p ∈ ({7, 11, 13, 17, 19, 23, 29} : Finset ℕ) := by
  interval_cases p <;> norm_num [Nat.prime_def_lt] at *

theorem near_two_core_prime_patterns_sharp (n : ℕ) (hn : n ≠ 0) (ho : Odd n)
    (hcard : n.primeFactors.card ≤ 4)
    (hnear : 2 - (2798 / 51134034375 : ℚ) < n.abundancyIndex) :
    3 ∈ n.primeFactors ∧
      ((5 ∈ n.primeFactors ∧ ∃ p ∈ n.primeFactors,
          p ∈ ({7, 11, 13, 17, 19, 23, 29} : Finset ℕ)) ∨
       (7 ∈ n.primeFactors ∧ ∃ p ∈ n.primeFactors, p ∈ ({11, 13} : Finset ℕ))) := by
  obtain ⟨h3, hpats⟩ := near_two_core_prime_patterns n hn ho hcard hnear
  refine ⟨h3, ?_⟩
  rcases hpats with ⟨h5, p, hp, hplist⟩ | h7
  · left
    refine ⟨h5, ?_⟩
    by_cases h31 : p = 31
    · subst p
      have hbound : ((3 : ℚ) / (3 - 1)) * ((5 : ℚ) / (5 - 1)) *
          ((31 : ℚ) / (31 - 1)) * ((37 : ℚ) / (37 - 1)) ≤
          2 - (2798 / 51134034375 : ℚ) := by norm_num
      obtain ⟨q, hq, hq3, hq5, hq31, hqlt⟩ :=
        near_two_requires_fourth n 3 5 31 37 hn h3 h5 hp (by decide) (by decide)
          (by decide) (by decide) hcard hnear hbound
      exact ⟨q, hq, small_odd_prime_list_no31 q (Nat.prime_of_mem_primeFactors hq)
        (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hq)) hq3 hq5 hq31 hqlt⟩
    · refine ⟨p, hp, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hplist ⊢
      tauto
  · exact Or.inr h7

theorem finset_three_plus_one {s : Finset ℕ} {a b c : ℕ}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcard : s.card ≤ 4) :
    s = {a,b,c} ∨ ∃ q, q ∉ ({a,b,c} : Finset ℕ) ∧ s = {a,b,c,q} := by
  classical
  let base : Finset ℕ := {a,b,c}
  have hbase : base ⊆ s := by
    intro x hx
    simp only [base, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hbasecard : base.card = 3 := by simp [base, hab, hac, hbc]
  have hrestcard : (s \ base).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset hbase, hbasecard]
    omega
  by_cases he : s \ base = ∅
  · left
    ext x
    constructor
    · intro hx
      by_contra hn
      have : x ∈ s \ base := Finset.mem_sdiff.mpr ⟨hx, hn⟩
      rw [he] at this
      simp at this
    · intro hx; exact hbase hx
  · right
    have hpositive : 0 < (s \ base).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    have hcardone : (s \ base).card = 1 := by omega
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcardone
    have hqmem : q ∈ s \ base := by rw [hq]; simp
    refine ⟨q, (Finset.mem_sdiff.mp hqmem).2, ?_⟩
    ext x
    constructor
    · intro hx
      by_cases hxbase : x ∈ base
      · simp only [base, Finset.mem_insert, Finset.mem_singleton] at hxbase
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · have hxs : x ∈ s \ base := Finset.mem_sdiff.mpr ⟨hx,hxbase⟩
        rw [hq] at hxs
        simp only [Finset.mem_singleton] at hxs
        simp [hxs]
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        first | assumption | exact (Finset.mem_sdiff.mp hqmem).1

theorem exists_min_other (s : Finset ℕ) (a b p : ℕ) (hp : p ∈ s)
    (hpa : p ≠ a) (hpb : p ≠ b) :
    ∃ c ∈ s, c ≠ a ∧ c ≠ b ∧ c ≤ p ∧
      ∀ q ∈ s, q ≠ a → q ≠ b → c ≤ q := by
  classical
  let rest := (s.erase a).erase b
  have hpin : p ∈ rest := by simp [rest, hp, hpa, hpb]
  have hr : rest.Nonempty := ⟨p, hpin⟩
  let c := rest.min' hr
  have hcin : c ∈ rest := Finset.min'_mem rest hr
  have hcdata := Finset.mem_erase.mp hcin
  have hcdata' := Finset.mem_erase.mp hcdata.2
  refine ⟨c, hcdata'.2, hcdata'.1, hcdata.1, Finset.min'_le rest p hpin, ?_⟩
  intro q hq hqa hqb
  apply Finset.min'_le
  simp [rest, hq, hqa, hqb]

theorem near_two_core_ordered_patterns (n : ℕ) (hn : n ≠ 0) (ho : Odd n)
    (hcard : n.primeFactors.card ≤ 4)
    (hnear : 2 - (2798 / 51134034375 : ℚ) < n.abundancyIndex) :
    3 ∈ n.primeFactors ∧
      ((5 ∈ n.primeFactors ∧ ∃ p ∈ n.primeFactors,
          p ∈ ({7, 11, 13, 17, 19, 23, 29} : Finset ℕ) ∧
          ∀ q ∈ n.primeFactors, q ≠ 3 → q ≠ 5 → p ≤ q) ∨
       (7 ∈ n.primeFactors ∧ 5 ∉ n.primeFactors ∧ ∃ p ∈ n.primeFactors,
          p ∈ ({11, 13} : Finset ℕ) ∧
          ∀ q ∈ n.primeFactors, q ≠ 3 → q ≠ 7 → p ≤ q)) := by
  obtain ⟨h3, hpats⟩ := near_two_core_prime_patterns_sharp n hn ho hcard hnear
  refine ⟨h3, ?_⟩
  rcases hpats with ⟨h5, p, hp, hplist⟩ | ⟨h7, p, hp, hplist⟩
  · left
    have hp3 : p ≠ 3 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hplist; omega
    have hp5 : p ≠ 5 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hplist; omega
    obtain ⟨c, hc, hc3, hc5, hcp, hcmin⟩ := exists_min_other n.primeFactors 3 5 p hp hp3 hp5
    have hc_lt : c < 37 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hplist; omega
    have hc31 : c ≠ 31 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hplist; omega
    exact ⟨h5, c, hc, small_odd_prime_list_no31 c (Nat.prime_of_mem_primeFactors hc)
      (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hc)) hc3 hc5 hc31 hc_lt, hcmin⟩
  · by_cases h5 : 5 ∈ n.primeFactors
    · have hp3 : p ≠ 3 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hplist; omega
      have hp5 : p ≠ 5 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hplist; omega
      obtain ⟨c, hc, hc3, hc5, hcp, hcmin⟩ := exists_min_other n.primeFactors 3 5 p hp hp3 hp5
      have hc_lt : c < 37 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hplist; omega
      have hc31 : c ≠ 31 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hplist; omega
      exact Or.inl ⟨h5, c, hc, small_odd_prime_list_no31 c (Nat.prime_of_mem_primeFactors hc)
        (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hc)) hc3 hc5 hc31 hc_lt, hcmin⟩
    · right
      have hp3 : p ≠ 3 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hplist; omega
      have hp7 : p ≠ 7 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hplist; omega
      obtain ⟨c, hc, hc3, hc7, hcp, hcmin⟩ := exists_min_other n.primeFactors 3 7 p hp hp3 hp7
      have hc_lt : c < 17 := by simp only [Finset.mem_insert, Finset.mem_singleton] at hplist; omega
      have hc5 : c ≠ 5 := by intro heq; subst c; exact h5 hc
      exact ⟨h7, h5, c, hc, very_small_odd_prime_list c (Nat.prime_of_mem_primeFactors hc)
        (ho.of_dvd_nat (Nat.dvd_of_mem_primeFactors hc)) hc3 hc5 hc7 hc_lt, hcmin⟩

theorem index_of_three_factors (n a b c : ℕ) (hn : n ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : n.primeFactors = {a,b,c}) :
    n.abundancyIndex = (a ^ n.factorization a).abundancyIndex *
      (b ^ n.factorization b).abundancyIndex * (c ^ n.factorization c).abundancyIndex := by
  rw [index_factorization n hn, hs]
  simp [hab, hac, hbc, mul_assoc]

theorem index_of_four_factors (n a b c q : ℕ) (hn : n ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haq : a ≠ q) (hbq : b ≠ q) (hcq : c ≠ q)
    (hs : n.primeFactors = {a,b,c,q}) :
    n.abundancyIndex = (a ^ n.factorization a).abundancyIndex *
      (b ^ n.factorization b).abundancyIndex * (c ^ n.factorization c).abundancyIndex *
      (q ^ n.factorization q).abundancyIndex := by
  rw [index_factorization n hn, hs]
  simp [hab, hac, hbc, haq, hbq, hcq, mul_assoc]

theorem index_le_two_pow_card (n : ℕ) (hn : n ≠ 0) :
    n.abundancyIndex ≤ (2 : ℚ) ^ n.primeFactors.card := by
  have hub := index_factorization_upper n hn
  have hprod := prime_ratio_prod_bound n.primeFactors 2 n.primeFactors.card
    (by decide) (le_refl _) (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  norm_num only [Nat.cast_ofNat] at hprod
  linarith

theorem core_index_le_32 (m p : ℕ) (ho : Odd m) (hp : p ∈ m.primeFactors)
    (hcard : m.primeFactors.card ≤ 5)
    (hdef : ∀ d ∈ m.properDivisors, d.Deficient) :
    (ordCompl[p] m).abundancyIndex ≤ 32 := by
  obtain ⟨_, hd, hc⟩ := core_properties m p ho hp hcard hdef
  have hn : ordCompl[p] m ≠ 0 := Nat.ne_of_gt hd.pos
  have hbound := index_le_two_pow_card (ordCompl[p] m) hn
  have hexp : (2 : ℚ) ^ (ordCompl[p] m).primeFactors.card ≤ 2 ^ 4 :=
    pow_le_pow_right₀ (by norm_num) hc
  norm_num at hexp
  linarith

abbrev Frac := ℕ × ℕ
def mulF (x y : Frac) : Frac := (x.1*y.1, x.2*y.2)
def lowF (p a : ℕ) : Frac := (p^(a+1)-1, (p-1)*p^a)
def highF (p a : ℕ) : Frac := if a = 15 then (p,p-1) else lowF p a
def maxRest (ps : List ℕ) : Frac := ps.foldl (fun f p => mulF f (p,p-1)) (1,1)
def minRest (ps : List ℕ) : Frac := ps.foldl (fun f p => mulF f (p+1,p)) (1,1)
def safe (l u : Frac) : Bool := 2*l.2 ≤ l.1 || u.1*51134034375 ≤ u.2*(2*51134034375-2798)
def certQ (last : ℕ) (l u : Frac) : Bool :=
 if 2*l.2 ≤ l.1 then true else
 let qmin := max (last+1) (l.1 / (2*l.2-l.1) + 1)
 let coeff := u.2*(2*51134034375-2798) - u.1*51134034375
 let qmax := if coeff = 0 then 387 else min 387 ((u.2*(2*51134034375-2798)-1) / coeff)
 (List.range (qmax+1-qmin)).all fun i =>
   let q := qmin+i
   if Nat.Prime q then
     (List.range 15).all fun j => safe (mulF l (lowF q (j+1))) (mulF u (highF q (j+1)))
   else true

def certTriple : List ℕ → ℕ → Frac → Frac → Bool
| [], last, l, u => certQ last l u
| p::ps, last, l, u =>
  if safe (mulF l (minRest (p::ps))) (mulF (mulF u (maxRest (p::ps))) (last+1,last)) then true
  else (List.range 15).all fun i => certTriple ps last (mulF l (lowF p (i+1))) (mulF u (highF p (i+1)))

def fullcert : Bool := [[3,5,7],[3,5,11],[3,5,13],[3,5,17],[3,5,19],[3,5,23],[3,5,29],[3,7,11],[3,7,13]].all fun ps =>
 match ps with | [_,_,c] => certTriple ps c (1,1) (1,1) | _ => false

def certBound : List ℕ → Frac → Frac → Bool
| [], l, u => safe l (mulF u (388,387))
| p::ps, l, u =>
  if safe (mulF l (minRest (p::ps))) (mulF (mulF u (maxRest (p::ps))) (388,387)) then true
  else (List.range 15).all fun i => certBound ps (mulF l (lowF p (i+1))) (mulF u (highF p (i+1)))

def valueF (x : Frac) : ℚ := (x.1 : ℚ) / x.2

theorem safe_sound (l u : Frac) (hl : 0 < l.2) (hu : 0 < u.2)
    (h : safe l u = true) : 2 ≤ valueF l ∨ valueF u ≤ 2 - 2798 / 51134034375 := by
  simp only [safe, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · left
    rw [valueF, le_div_iff₀ (by exact_mod_cast hl)]
    exact_mod_cast h
  · right
    rw [valueF, div_le_iff₀ (by exact_mod_cast hu)]
    norm_num at h
    have hh : (u.1 : ℚ) * 51134034375 ≤ u.2 * 102268065952 := by
      exact_mod_cast h
    norm_num at hh ⊢
    linarith

theorem valueF_mul (l u : Frac) : valueF (mulF l u) = valueF l * valueF u := by
  simp only [valueF, mulF, Nat.cast_mul]
  ring

theorem valueF_pos (f : Frac) (hn : 0 < f.1) (hd : 0 < f.2) : 0 < valueF f := by
  unfold valueF
  positivity

theorem fold_mulF (f : ℕ → Frac) (xs : List ℕ) (a : Frac) :
    xs.foldl (fun b x => mulF b (f x)) a =
      mulF a (xs.foldl (fun b x => mulF b (f x)) (1,1)) := by
  induction xs generalizing a with
  | nil => simp [mulF]
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih (mulF a (f p)), ih (mulF (1,1) (f p))]
    simp [mulF, mul_assoc]

theorem minRest_cons (p : ℕ) (ps : List ℕ) :
    minRest (p :: ps) = mulF (p+1,p) (minRest ps) := by
  simp only [minRest, List.foldl_cons]
  rw [fold_mulF]
  simp [mulF]

theorem maxRest_cons (p : ℕ) (ps : List ℕ) :
    maxRest (p :: ps) = mulF (p,p-1) (maxRest ps) := by
  simp only [maxRest, List.foldl_cons]
  rw [fold_mulF]
  simp [mulF]

def BasicBox (p : ℕ) (x : ℚ) : Prop :=
  1 < p ∧ valueF (p+1,p) ≤ x ∧ x ≤ valueF (p,p-1)

theorem rest_den_pos (ps : List ℕ) (h : ∀ p ∈ ps, 1 < p) :
    0 < (minRest ps).2 ∧ 0 < (maxRest ps).2 := by
  induction ps with
  | nil => simp [minRest, maxRest]
  | cons p ps ih =>
    have hp : 1 < p := h p (by simp)
    have hs : ∀ q ∈ ps, 1 < q := by intro q hq; exact h q (by simp [hq])
    obtain ⟨hmin,hmax⟩ := ih hs
    rw [minRest_cons, maxRest_cons]
    simp only [mulF, Prod.snd]
    exact ⟨Nat.mul_pos (by omega) hmin, Nat.mul_pos (by omega) hmax⟩

theorem rest_bounds (ps : List ℕ) (xs : List ℚ)
    (h : List.Forall₂ BasicBox ps xs) :
    valueF (minRest ps) ≤ xs.prod ∧ xs.prod ≤ valueF (maxRest ps) := by
  induction h with
  | nil => norm_num [minRest, maxRest, valueF]
  | @cons p x ps xs hp hs ih =>
    obtain ⟨hp1,hlo,hhi⟩ := hp
    have hpq : (1 : ℚ) < p := by exact_mod_cast hp1
    have hminpos : 0 ≤ valueF (p+1,p) := by unfold valueF; positivity
    have hmaxpos : 0 ≤ valueF (p,p-1) := by
      unfold valueF; norm_cast; positivity
    have hxpos : 0 ≤ x := le_trans hminpos hlo
    have hpspos : 0 ≤ xs.prod := le_trans (by
      unfold valueF; positivity) ih.1
    rw [minRest_cons, maxRest_cons, valueF_mul, valueF_mul]
    simp only [List.prod_cons]
    constructor
    · exact mul_le_mul hlo ih.1 (by unfold valueF; positivity) hxpos
    · exact mul_le_mul hhi ih.2 hpspos hmaxpos

def FullBox (p : ℕ) (x : ℚ) : Prop :=
  BasicBox p x ∧ ∃ a : ℕ, 1 ≤ a ∧ a ≤ 15 ∧
    valueF (lowF p a) ≤ x ∧ x ≤ valueF (highF p a)

theorem lowF_den (p a : ℕ) (hp : 1 < p) : 0 < (lowF p a).2 := by
  simp only [lowF, Prod.snd]
  exact Nat.mul_pos (by omega) (pow_pos (by omega) _)

theorem highF_den (p a : ℕ) (hp : 1 < p) : 0 < (highF p a).2 := by
  unfold highF
  split_ifs
  · simp; omega
  · exact lowF_den p a hp

theorem valueF_nonneg (f : Frac) : 0 ≤ valueF f := by
  unfold valueF
  positivity

theorem boxes_prime (ps : List ℕ) (xs : List ℚ) (h : List.Forall₂ BasicBox ps xs) :
    ∀ p ∈ ps, 1 < p := by
  induction h with
  | nil => simp
  | cons hhead htail ih =>
    intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hhead.1
    · exact ih p hp

theorem certBound_sound (ps : List ℕ) (l u : Frac) (xs : List ℚ)
    (hl : 0 < l.2) (hu : 0 < u.2) (hboxes : List.Forall₂ FullBox ps xs)
    (hcert : certBound ps l u = true) (t : ℚ) (htlo : 1 ≤ t)
    (hthi : t ≤ (388 : ℚ) / 387) :
    2 ≤ valueF l * xs.prod * t ∨
      valueF u * xs.prod * t ≤ 2 - 2798 / 51134034375 := by
  induction hboxes generalizing l u with
  | nil =>
    simp only [certBound] at hcert
    have hs := safe_sound l (mulF u (388,387)) hl (by simp [mulF]; omega) hcert
    simp only [valueF_mul] at hs
    simp only [List.prod_nil, mul_one]
    have hnonl := valueF_nonneg l
    have hnonu := valueF_nonneg u
    have hf : valueF (388,387) = (388 : ℚ) / 387 := by norm_num [valueF]
    rw [hf] at hs
    rcases hs with hs | hs
    · left; nlinarith
    · right; nlinarith
  | @cons p x ps xs hp hrest ih =>
    obtain ⟨hbasic, a, ha1, ha15, hlo, hhi⟩ := hp
    have hp1 := hbasic.1
    have hbasicrest : List.Forall₂ BasicBox ps xs := hrest.imp (fun _ _ h => h.1)
    have hb := rest_bounds (p :: ps) (x :: xs) (List.Forall₂.cons hbasic hbasicrest)
    have hden := rest_den_pos (p :: ps)
      (boxes_prime (p :: ps) (x :: xs) (List.Forall₂.cons hbasic hbasicrest))
    simp only [certBound] at hcert
    split_ifs at hcert with hs
    · have hsafe := safe_sound (mulF l (minRest (p :: ps)))
          (mulF (mulF u (maxRest (p :: ps))) (388,387))
          (by simp only [mulF]; exact Nat.mul_pos hl hden.1)
          (by simp only [mulF]; exact Nat.mul_pos (Nat.mul_pos hu hden.2) (by decide)) hs
      simp only [valueF_mul] at hsafe
      have hf : valueF (388,387) = (388 : ℚ) / 387 := by norm_num [valueF]
      rw [hf] at hsafe
      have hprodpos : 0 ≤ (x :: xs).prod := le_trans (valueF_nonneg _) hb.1
      have hpl := mul_le_mul_of_nonneg_left hb.1 (valueF_nonneg l)
      have hpu := mul_le_mul_of_nonneg_left hb.2 (valueF_nonneg u)
      have htl := mul_le_mul_of_nonneg_left htlo (mul_nonneg (valueF_nonneg l) hprodpos)
      have htu := mul_le_mul_of_nonneg_left hthi (mul_nonneg (valueF_nonneg u) (valueF_nonneg (maxRest (p :: ps))))
      rcases hsafe with hs | hs
      · left; nlinarith
      · right
        have hmid := mul_le_mul_of_nonneg_right hpu (by linarith : 0 ≤ t)
        nlinarith
    · have ha_mem : a - 1 ∈ List.range 15 := List.mem_range.mpr (by omega)
      have hall := (List.all_eq_true.mp hcert) (a - 1) ha_mem
      have haeq : a - 1 + 1 = a := by omega
      rw [haeq] at hall
      have hrec := ih (mulF l (lowF p a)) (mulF u (highF p a))
        (by simp only [mulF]; exact Nat.mul_pos hl (lowF_den p a hp1))
        (by simp only [mulF]; exact Nat.mul_pos hu (highF_den p a hp1)) hall
      simp only [valueF_mul] at hrec
      have hxs : 0 ≤ xs.prod := by
        have hb' := rest_bounds ps xs hbasicrest
        exact le_trans (valueF_nonneg _) hb'.1
      have htl : 0 ≤ t := by linarith
      have hmullo := mul_le_mul_of_nonneg_left hlo (valueF_nonneg l)
      have hmulhi := mul_le_mul_of_nonneg_left hhi (valueF_nonneg u)
      have hmultlo := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmullo hxs) htl
      have hmulthi := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmulhi hxs) htl
      simp only [List.prod_cons]
      rcases hrec with hrec | hrec
      · left; nlinarith
      · right; nlinarith

theorem qmin_sound (n d q : ℕ) (h : n < q * (2*d-n)) :
    n / (2*d-n) + 1 ≤ q := by
  have hdiv : n / (2*d-n) < q := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using h)
  omega

theorem qmax_sound (a coeff q : ℕ) (hc : 0 < coeff) (h : q*coeff < a) :
    q ≤ (a-1)/coeff := by
  apply (Nat.le_div_iff_mul_le hc).2
  omega

theorem qmin_cross (n d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (h : (n : ℚ) / d * (1 + 1 / q) < 2) :
    n < q * (2*d-n) := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hqq : (0 : ℚ) < q := by exact_mod_cast hq
  have hc : (n : ℚ) * (q+1) < 2 * d * q := by
    have hh := (div_lt_iff₀ (mul_pos hdq hqq)).mp (show (n : ℚ) * (q+1) / (d*q) < 2 by
      convert h using 1 <;> field_simp <;> ring)
    simpa [mul_assoc] using hh
  have hnat : n * (q+1) < 2*d*q := by exact_mod_cast hc
  have hn2d : n < 2*d := by nlinarith
  rw [Nat.mul_sub_left_distrib]
  have hle : q*n ≤ q*(2*d) := Nat.mul_le_mul_left q (by omega)
  have heq := Nat.sub_add_cancel hle
  nlinarith

theorem qmax_cross (a b n d q : ℕ) (hb : 0 < b) (hd : 0 < d) (hq : 1 < q)
    (hcoeff : n*b < a*d)
    (h : (a : ℚ) / b < (n : ℚ) / d * (q / ((q : ℚ) - 1))) :
    q * (a*d-n*b) < a*d := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hqq : (1 : ℚ) < q := by exact_mod_cast hq
  have hc : (a : ℚ) * d * (q-1) < n*b*q := by
    have h' : (a : ℚ) / b < ((n : ℚ) * q) / (d * ((q : ℚ)-1)) := by
      convert h using 1 <;> field_simp <;> ring
    have h2 := (lt_div_iff₀ (mul_pos hdq (by linarith : (0 : ℚ) < (q : ℚ)-1))).mp h'
    rw [div_mul_eq_mul_div] at h2
    have h3 := (div_lt_iff₀ hbq).mp h2
    nlinarith
  have hcoeffq : (n : ℚ)*b ≤ (a : ℚ)*d := by exact_mod_cast le_of_lt hcoeff
  have hfinal : (q : ℚ) * ((a : ℚ)*d-n*b) < a*d := by nlinarith
  have : (↑(q * (a*d-n*b)) : ℚ) < ↑(a*d) := by
    simpa [Nat.cast_sub (le_of_lt hcoeff)] using hfinal
  exact_mod_cast this

theorem certQ_sound (last q : ℕ) (l u : Frac) (x : ℚ)
    (hl : 0 < l.2) (hu : 0 < u.2) (hq : q.Prime) (hqlo : last < q) (hqhi : q ≤ 387)
    (hbox : FullBox q x) (hcert : certQ last l u = true) :
    2 ≤ valueF l * x ∨ valueF u * x ≤ 2 - 2798 / 51134034375 := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨hlow, hupp⟩ := hcontra
  obtain ⟨⟨hq1, hbaselo, hbasehi⟩, a, ha1, ha15, hlo, hhi⟩ := hbox
  have hqpos : 0 < q := hq.pos
  have hqx : (1 : ℚ) ≤ x := by
    have : (1 : ℚ) ≤ valueF (q+1,q) := by
      unfold valueF
      have hq' : (0 : ℚ) < q := by exact_mod_cast hqpos
      rw [le_div_iff₀ hq']
      push_cast
      linarith
    linarith
  have hl2 : l.1 < 2*l.2 := by
    have hv : valueF l < 2 := by
      have := mul_le_mul_of_nonneg_left hqx (valueF_nonneg l)
      nlinarith
    unfold valueF at hv
    have hv' := (div_lt_iff₀ (by exact_mod_cast hl : (0 : ℚ) < l.2)).mp hv
    exact_mod_cast hv'
  have hlcross : valueF l * (1 + 1 / (q : ℚ)) < 2 := by
    have hqv : valueF (q+1,q) = 1 + 1 / (q : ℚ) := by
      unfold valueF
      have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
      push_cast
      field_simp
    rw [hqv] at hbaselo
    have := mul_le_mul_of_nonneg_left hbaselo (valueF_nonneg l)
    linarith
  have hqmin := qmin_sound l.1 l.2 q (qmin_cross l.1 l.2 q hl hqpos hlcross)
  let coeff := u.2 * (2 * 51134034375 - 2798) - u.1 * 51134034375
  let limit := if coeff = 0 then 387 else min 387 ((u.2 * (2*51134034375-2798)-1) / coeff)
  have hqmax : q ≤ limit := by
    dsimp [limit]
    split_ifs with hc
    · exact hqhi
    · apply Nat.le_min.mpr
      refine ⟨hqhi, ?_⟩
      have hcpos : 0 < coeff := Nat.pos_of_ne_zero hc
      have hcoeff : u.1 * 51134034375 < 102268065952 * u.2 := by
        dsimp [coeff] at hcpos
        omega
      have hupper' : (102268065952 : ℚ) / 51134034375 <
          (u.1 : ℚ) / u.2 * ((q : ℚ) / ((q : ℚ) - 1)) := by
        have hh := mul_le_mul_of_nonneg_left hbasehi (valueF_nonneg u)
        simp only [valueF, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one] at hh
        unfold valueF at hupp
        norm_num at hupp ⊢
        linarith
      have hcross := qmax_cross 102268065952 51134034375 u.1 u.2 q
        (by decide) hu hq1 hcoeff hupper'
      have hcoeffeq : 102268065952 * u.2 - u.1 * 51134034375 = coeff := by
        dsimp [coeff]
        omega
      rw [hcoeffeq] at hcross
      have heq : 102268065952 * u.2 = u.2 * (2 * 51134034375 - 2798) := by omega
      rw [heq] at hcross
      exact qmax_sound _ coeff q hcpos hcross
  have hrange : q - max (last + 1) (l.1 / (2*l.2-l.1) + 1) ∈
      List.range (limit + 1 - max (last + 1) (l.1 / (2*l.2-l.1) + 1)) := by
    apply List.mem_range.mpr
    have : max (last + 1) (l.1 / (2*l.2-l.1) + 1) ≤ q := max_le (by omega) hqmin
    omega
  unfold certQ at hcert
  simp only [if_neg (by omega : ¬ 2 * l.2 ≤ l.1)] at hcert
  change (List.range (limit + 1 - max (last+1) (l.1 / (2*l.2-l.1)+1))).all _ = true at hcert
  have hentry := (List.all_eq_true.mp hcert) _ hrange
  have hminq : max (last+1) (l.1 / (2*l.2-l.1)+1) +
      (q - max (last+1) (l.1 / (2*l.2-l.1)+1)) = q := by omega
  simp only [hminq, if_pos hq] at hentry
  have ha_mem : a - 1 ∈ List.range 15 := List.mem_range.mpr (by omega)
  have hsafe := (List.all_eq_true.mp hentry) (a-1) ha_mem
  have haeq : a - 1 + 1 = a := by omega
  rw [haeq] at hsafe
  have hh := safe_sound (mulF l (lowF q a)) (mulF u (highF q a))
    (by simp only [mulF]; exact Nat.mul_pos hl (lowF_den q a hq1))
    (by simp only [mulF]; exact Nat.mul_pos hu (highF_den q a hq1)) hsafe
  simp only [valueF_mul] at hh
  have hll := mul_le_mul_of_nonneg_left hlo (valueF_nonneg l)
  have huu := mul_le_mul_of_nonneg_left hhi (valueF_nonneg u)
  rcases hh with hh | hh <;> linarith

theorem certTriple_sound (ps : List ℕ) (last : ℕ) (l u : Frac) (xs : List ℚ)
    (hl : 0 < l.2) (hu : 0 < u.2) (hboxes : List.Forall₂ FullBox ps xs)
    (q : ℕ) (hq : q.Prime) (hqlo : last < q) (hqhi : q ≤ 387)
    (hx : ℚ) (hqbox : FullBox q hx) (hlast : 0 < last)
    (hxtail : 1 ≤ hx) (hxtailhi : hx ≤ valueF (last+1,last))
    (hcert : certTriple ps last l u = true) :
    2 ≤ valueF l * xs.prod * hx ∨
      valueF u * xs.prod * hx ≤ 2 - 2798 / 51134034375 := by
  induction hboxes generalizing l u with
  | nil =>
    simp only [certTriple] at hcert
    simpa only [List.prod_nil, mul_one] using certQ_sound last q l u hx hl hu hq hqlo hqhi hqbox hcert
  | @cons p x ps xs hp hrest ih =>
    obtain ⟨hbasic, a, ha1, ha15, hlo, hhi⟩ := hp
    have hp1 := hbasic.1
    have hbasicrest : List.Forall₂ BasicBox ps xs := hrest.imp (fun _ _ h => h.1)
    have hb := rest_bounds (p :: ps) (x :: xs) (List.Forall₂.cons hbasic hbasicrest)
    have hden := rest_den_pos (p :: ps)
      (boxes_prime (p :: ps) (x :: xs) (List.Forall₂.cons hbasic hbasicrest))
    simp only [certTriple] at hcert
    split_ifs at hcert with hs
    · have hsafe := safe_sound (mulF l (minRest (p :: ps)))
          (mulF (mulF u (maxRest (p :: ps))) (last+1,last))
          (by simp only [mulF]; exact Nat.mul_pos hl hden.1)
          (by simp only [mulF]; exact Nat.mul_pos (Nat.mul_pos hu hden.2) hlast) hs
      simp only [valueF_mul] at hsafe
      have hprodpos : 0 ≤ (x :: xs).prod := le_trans (valueF_nonneg _) hb.1
      have hpl := mul_le_mul_of_nonneg_left hb.1 (valueF_nonneg l)
      have hpu := mul_le_mul_of_nonneg_left hb.2 (valueF_nonneg u)
      have htl := mul_le_mul_of_nonneg_left hxtail (mul_nonneg (valueF_nonneg l) hprodpos)
      have htu := mul_le_mul_of_nonneg_left hxtailhi
        (mul_nonneg (valueF_nonneg u) (valueF_nonneg (maxRest (p :: ps))))
      rcases hsafe with hs | hs
      · left; nlinarith
      · right
        have hmid := mul_le_mul_of_nonneg_right hpu (by linarith : 0 ≤ hx)
        nlinarith
    · have ha_mem : a - 1 ∈ List.range 15 := List.mem_range.mpr (by omega)
      have hall := (List.all_eq_true.mp hcert) (a - 1) ha_mem
      have haeq : a - 1 + 1 = a := by omega
      rw [haeq] at hall
      have hrec := ih (mulF l (lowF p a)) (mulF u (highF p a))
        (by simp only [mulF]; exact Nat.mul_pos hl (lowF_den p a hp1))
        (by simp only [mulF]; exact Nat.mul_pos hu (highF_den p a hp1)) hall
      simp only [valueF_mul] at hrec
      have hxs : 0 ≤ xs.prod := by
        have hb' := rest_bounds ps xs hbasicrest
        exact le_trans (valueF_nonneg _) hb'.1
      have htl : 0 ≤ hx := by linarith
      have hmullo := mul_le_mul_of_nonneg_left hlo (valueF_nonneg l)
      have hmulhi := mul_le_mul_of_nonneg_left hhi (valueF_nonneg u)
      have hmultlo := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmullo hxs) htl
      have hmulthi := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmulhi hxs) htl
      simp only [List.prod_cons]
      rcases hrec with hrec | hrec
      · left; nlinarith
      · right; nlinarith

theorem valueF_lowF_eq (p a : ℕ) (hp : p.Prime) :
    valueF (lowF p a) = (p ^ a).abundancyIndex := by
  rw [prime_power_index_formula p a hp]
  have hpow : 1 ≤ p ^ (a+1) := by exact Nat.one_le_pow _ _ hp.pos
  have hp1 : 1 ≤ p := hp.one_le
  simp [valueF, lowF, Nat.cast_sub hpow, Nat.cast_sub hp1]

theorem prime_index_boxes (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    1 ≤ min e 15 ∧ min e 15 ≤ 15 ∧
    valueF (lowF p (min e 15)) ≤ (p^e).abundancyIndex ∧
    (p^e).abundancyIndex ≤ valueF (highF p (min e 15)) := by
  have hmin1 : 1 ≤ min e 15 := by omega
  have hmin15 : min e 15 ≤ 15 := min_le_right _ _
  refine ⟨hmin1, hmin15, ?_, ?_⟩
  · rw [valueF_lowF_eq p (min e 15) hp]
    exact prime_power_index_mono p (min e 15) e hp (min_le_left _ _)
  · by_cases he15 : e < 15
    · have hm : min e 15 = e := min_eq_left (by omega)
      rw [hm]
      simp only [highF, if_neg (by omega : e ≠ 15)]
      exact le_of_eq (valueF_lowF_eq p e hp).symm
    · have hm : min e 15 = 15 := min_eq_right (by omega)
      rw [hm]
      have hp1 : 1 ≤ p := hp.one_le
      simpa [highF, valueF, Nat.cast_sub hp1] using le_of_lt (prime_power_index_lt p e hp)

theorem lowF_den_pos (p a : ℕ) (hp : p.Prime) : 0 < (lowF p a).2 := by
  simp only [lowF]
  exact Nat.mul_pos (by have := hp.one_lt; omega) (pow_pos hp.pos _)

theorem highF_den_pos (p a : ℕ) (hp : p.Prime) : 0 < (highF p a).2 := by
  unfold highF
  split_ifs
  · simp only
    have := hp.one_lt
    omega
  · exact lowF_den_pos p a hp

theorem index_min_factor (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    valueF (p+1,p) ≤ (p^e).abundancyIndex := by
  calc
    valueF (p+1,p) = (p^1).abundancyIndex := by
      rw [prime_power_index_formula p 1 hp]
      have hpq : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
      simp only [valueF, Nat.cast_add, Nat.cast_one, pow_one, Nat.reduceAdd]
      have hne : (p : ℚ) - 1 ≠ 0 := by linarith
      field_simp [hne]
      ring
    _ ≤ (p^e).abundancyIndex := prime_power_index_mono p 1 e hp (by omega)

theorem index_max_factor (p e : ℕ) (hp : p.Prime) :
    (p^e).abundancyIndex ≤ valueF (p,p-1) := by
  have hp1 : 1 ≤ p := hp.one_le
  simpa [valueF, Nat.cast_sub hp1] using le_of_lt (prime_power_index_lt p e hp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bound_5_7 : certBound [3,5,7] (1,1) (1,1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bound_5_11 : certBound [3,5,11] (1,1) (1,1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bound_5_13 : certBound [3,5,13] (1,1) (1,1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bound_5_17 : certBound [3,5,17] (1,1) (1,1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bound_5_19 : certBound [3,5,19] (1,1) (1,1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bound_5_23 : certBound [3,5,23] (1,1) (1,1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bound_5_29 : certBound [3,5,29] (1,1) (1,1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bound_7_11 : certBound [3,7,11] (1,1) (1,1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem bound_7_13 : certBound [3,7,13] (1,1) (1,1) = true := by decide


theorem prime_fullBox (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    FullBox p ((p^e).abundancyIndex) := by
  obtain ⟨h1,h2,h3,h4⟩ := prime_index_boxes p e hp he
  exact ⟨⟨hp.one_lt, index_min_factor p e hp he, index_max_factor p e hp⟩,
     min e 15,h1,h2,h3,h4⟩

theorem bounded_q_factor (p e : ℕ) (hp : p.Prime) (he : 0 < e) (hlarge : 388 ≤ p) :
    1 ≤ (p^e).abundancyIndex ∧ (p^e).abundancyIndex ≤ (388 : ℚ) / 387 := by
  constructor
  · have h := index_min_factor p e hp he
    have hpq : (0 : ℚ) < p := by exact_mod_cast hp.pos
    unfold valueF at h
    have : 1 ≤ ((p : ℚ) + 1)/p := by
      rw [le_div_iff₀ hpq]
      linarith
    exact le_trans this (by simpa using h)
  · exact le_trans (le_of_lt (prime_power_index_lt p e hp))
      (by have h := prime_ratio_antitone p 388 (by decide) hlarge; norm_num at h ⊢; exact h)


theorem certified_fourth_bound (a b c q ea eb ec eq : ℕ)
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hq : q.Prime)
    (hea : 0 < ea) (heb : 0 < eb) (hec : 0 < ec) (heq : 0 < eq)
    (hcert : certBound [a,b,c] (1,1) (1,1) = true)
    (hdef : (a^ea).abundancyIndex * (b^eb).abundancyIndex *
        (c^ec).abundancyIndex * (q^eq).abundancyIndex < 2)
    (hnear : 2 - 2798 / 51134034375 < (a^ea).abundancyIndex *
       (b^eb).abundancyIndex * (c^ec).abundancyIndex * (q^eq).abundancyIndex) :
    q < 388 := by
  by_contra hn
  have hqbig : 388 ≤ q := by omega
  have hbox : List.Forall₂ FullBox [a,b,c]
      [(a^ea).abundancyIndex,(b^eb).abundancyIndex,(c^ec).abundancyIndex] := by
    exact .cons (prime_fullBox a ea ha hea) (.cons (prime_fullBox b eb hb heb)
      (.cons (prime_fullBox c ec hc hec) .nil))
  obtain ⟨hlo,hhi⟩ := bounded_q_factor q eq hq heq hqbig
  have h := certBound_sound [a,b,c] (1,1) (1,1) _ (by decide) (by decide) hbox hcert
    (q^eq).abundancyIndex hlo hhi
  norm_num [valueF, List.prod_cons, List.prod_nil, mul_assoc] at h
  rcases h with h | h <;> linarith

theorem certified_triple_impossible (a b c ea eb ec : ℕ)
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hea : 0 < ea) (heb : 0 < eb) (hec : 0 < ec)
    (hcert : certBound [a,b,c] (1,1) (1,1) = true)
    (hdef : (a^ea).abundancyIndex * (b^eb).abundancyIndex * (c^ec).abundancyIndex < 2)
    (hnear : 2 - 2798 / 51134034375 <
      (a^ea).abundancyIndex * (b^eb).abundancyIndex * (c^ec).abundancyIndex) : False := by
  have hbox : List.Forall₂ FullBox [a,b,c]
      [(a^ea).abundancyIndex,(b^eb).abundancyIndex,(c^ec).abundancyIndex] := by
    exact .cons (prime_fullBox a ea ha hea) (.cons (prime_fullBox b eb hb heb)
      (.cons (prime_fullBox c ec hc hec) .nil))
  have h := certBound_sound [a,b,c] (1,1) (1,1) _ (by decide) (by decide) hbox hcert
    1 (by norm_num) (by norm_num)
  norm_num [valueF, List.prod_cons, List.prod_nil, mul_assoc] at h
  rcases h with h | h <;> linarith

theorem certified_core_has_bounded_fourth (n a b c : ℕ) (hn : n ≠ 0)
    (ha : a ∈ n.primeFactors) (hb : b ∈ n.primeFactors) (hc : c ∈ n.primeFactors)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcard : n.primeFactors.card ≤ 4)
    (hcert : certBound [a,b,c] (1,1) (1,1) = true)
    (hdef : n.abundancyIndex < 2)
    (hnear : 2 - 2798 / 51134034375 < n.abundancyIndex) :
    ∃ q, q ∈ n.primeFactors ∧ q ∉ ({a,b,c} : Finset ℕ) ∧ q < 388 ∧ n.primeFactors = {a,b,c,q} := by
  have hpa := Nat.prime_of_mem_primeFactors ha
  have hpb := Nat.prime_of_mem_primeFactors hb
  have hpc := Nat.prime_of_mem_primeFactors hc
  have hea := hpa.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors ha)
  have heb := hpb.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hb)
  have hec := hpc.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hc)
  rcases finset_three_plus_one ha hb hc hab hac hbc hcard with hs | ⟨q,hqn,hs⟩
  · have hi := index_of_three_factors n a b c hn hab hac hbc hs
    rw [hi] at hnear hdef
    exact False.elim (certified_triple_impossible a b c _ _ _ hpa hpb hpc hea heb hec hcert hdef hnear)
  · have hq : q ∈ n.primeFactors := by rw [hs]; simp
    have hpq := Nat.prime_of_mem_primeFactors hq
    have heq := hpq.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hq)
    have haqn : a ≠ q := by intro h; subst q; exact hqn (by simp)
    have hbqn : b ≠ q := by intro h; subst q; exact hqn (by simp)
    have hcqn : c ≠ q := by intro h; subst q; exact hqn (by simp)
    have hi := index_of_four_factors n a b c q hn hab hac hbc haqn hbqn hcqn hs
    rw [hi] at hnear hdef
    exact ⟨q,hq,hqn,certified_fourth_bound a b c q _ _ _ _ hpa hpb hpc hpq hea heb hec heq hcert hdef hnear,hs⟩

theorem certBound_patterns (b c : ℕ)
    (h : (b = 5 ∧ c ∈ ({7,11,13,17,19,23,29} : Finset ℕ)) ∨
         (b = 7 ∧ c ∈ ({11,13} : Finset ℕ))) :
    certBound [3,b,c] (1,1) (1,1) = true := by
  rcases h with ⟨rfl,hc⟩ | ⟨rfl,hc⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound_5_7
    · exact bound_5_11
    · exact bound_5_13
    · exact bound_5_17
    · exact bound_5_19
    · exact bound_5_23
    · exact bound_5_29
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact bound_7_11
    · exact bound_7_13

theorem near_two_core_bounded_patterns (n : ℕ) (hn : n ≠ 0) (ho : Odd n)
    (hcard : n.primeFactors.card ≤ 4) (hdef : n.abundancyIndex < 2)
    (hnear : 2 - (2798 / 51134034375 : ℚ) < n.abundancyIndex) :
    ∃ b c q, ((b = 5 ∧ c ∈ ({7,11,13,17,19,23,29} : Finset ℕ)) ∨
       (b = 7 ∧ c ∈ ({11,13} : Finset ℕ))) ∧
       q < 388 ∧ q ≠ 3 ∧ q ≠ b ∧ q ≠ c ∧ c < q ∧
       n.primeFactors = {3,b,c,q} := by
  obtain ⟨h3,hpat⟩ := near_two_core_ordered_patterns n hn ho hcard hnear
  have handle (b c : ℕ) (hb : b ∈ n.primeFactors) (hc : c ∈ n.primeFactors)
      (hpat : (b = 5 ∧ c ∈ ({7,11,13,17,19,23,29} : Finset ℕ)) ∨
              (b = 7 ∧ c ∈ ({11,13} : Finset ℕ)))
      (hord : ∀ q ∈ n.primeFactors, q ≠ 3 → q ≠ b → c ≤ q) :
      ∃ b c q, ((b = 5 ∧ c ∈ ({7,11,13,17,19,23,29} : Finset ℕ)) ∨
       (b = 7 ∧ c ∈ ({11,13} : Finset ℕ))) ∧
       q < 388 ∧ q ≠ 3 ∧ q ≠ b ∧ q ≠ c ∧ c < q ∧
       n.primeFactors = {3,b,c,q} := by
    have hbc : b ≠ c := by
      rcases hpat with ⟨rfl,hc⟩ | ⟨rfl,hc⟩ <;>
       simp only [Finset.mem_insert, Finset.mem_singleton] at hc <;> omega
    have h3b : 3 ≠ b := by rcases hpat with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
    have h3c : 3 ≠ c := by
      rcases hpat with ⟨_,hc⟩ | ⟨_,hc⟩ <;>
       simp only [Finset.mem_insert, Finset.mem_singleton] at hc <;> omega
    obtain ⟨q,hq,hqnot,hqlt,hset⟩ := certified_core_has_bounded_fourth n 3 b c hn h3 hb hc
      h3b h3c hbc hcard (certBound_patterns b c hpat) hdef hnear
    have hq3 : q ≠ 3 := by intro h; subst q; exact hqnot (by simp)
    have hqb : q ≠ b := by intro h; subst q; exact hqnot (by simp)
    have hqc : q ≠ c := by intro h; subst q; exact hqnot (by simp)
    exact ⟨b,c,q,hpat,hqlt,hq3,hqb,hqc,by have := hord q hq hq3 hqb; omega,hset⟩
  rcases hpat with ⟨h5,c,hc,hcp,hord⟩ | ⟨h7,_,c,hc,hcp,hord⟩
  · exact handle 5 c h5 hc (Or.inl ⟨rfl,hcp⟩) hord
  · exact handle 7 c h7 hc (Or.inr ⟨rfl,hcp⟩) hord

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_1 : certTriple [5,7] 7 (lowF 3 1) (highF 3 1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_2 : certTriple [5,7] 7 (lowF 3 2) (highF 3 2) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_3 : certTriple [5,7] 7 (lowF 3 3) (highF 3 3) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_4 : certTriple [5,7] 7 (lowF 3 4) (highF 3 4) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_5 : certTriple [5,7] 7 (lowF 3 5) (highF 3 5) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_6 : certTriple [5,7] 7 (lowF 3 6) (highF 3 6) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_7 : certTriple [5,7] 7 (lowF 3 7) (highF 3 7) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_8 : certTriple [5,7] 7 (lowF 3 8) (highF 3 8) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_9 : certTriple [5,7] 7 (lowF 3 9) (highF 3 9) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_10 : certTriple [5,7] 7 (lowF 3 10) (highF 3 10) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_11 : certTriple [5,7] 7 (lowF 3 11) (highF 3 11) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_12 : certTriple [5,7] 7 (lowF 3 12) (highF 3 12) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_13 : certTriple [5,7] 7 (lowF 3 13) (highF 3 13) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_14 : certTriple [5,7] 7 (lowF 3 14) (highF 3 14) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_7_15 : certTriple [5,7] 7 (lowF 3 15) (highF 3 15) = true := by decide
theorem cert_3_5_7_all : certTriple [3,5,7] 7 (1,1) (1,1) = true := by
  rw [certTriple]
  split_ifs with h
  · rfl
  · simp only [List.all_eq_true, List.mem_range]
    intro i hi
    interval_cases i
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_1
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_2
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_3
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_4
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_5
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_6
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_7
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_8
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_9
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_10
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_11
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_12
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_13
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_14
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_7_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_1 : certTriple [5,11] 11 (lowF 3 1) (highF 3 1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_2 : certTriple [5,11] 11 (lowF 3 2) (highF 3 2) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_3 : certTriple [5,11] 11 (lowF 3 3) (highF 3 3) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_4 : certTriple [5,11] 11 (lowF 3 4) (highF 3 4) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_5 : certTriple [5,11] 11 (lowF 3 5) (highF 3 5) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_6 : certTriple [5,11] 11 (lowF 3 6) (highF 3 6) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_7 : certTriple [5,11] 11 (lowF 3 7) (highF 3 7) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_8 : certTriple [5,11] 11 (lowF 3 8) (highF 3 8) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_9 : certTriple [5,11] 11 (lowF 3 9) (highF 3 9) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_10 : certTriple [5,11] 11 (lowF 3 10) (highF 3 10) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_11 : certTriple [5,11] 11 (lowF 3 11) (highF 3 11) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_12 : certTriple [5,11] 11 (lowF 3 12) (highF 3 12) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_13 : certTriple [5,11] 11 (lowF 3 13) (highF 3 13) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_14 : certTriple [5,11] 11 (lowF 3 14) (highF 3 14) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_11_15 : certTriple [5,11] 11 (lowF 3 15) (highF 3 15) = true := by decide
theorem cert_3_5_11_all : certTriple [3,5,11] 11 (1,1) (1,1) = true := by
  rw [certTriple]
  split_ifs with h
  · rfl
  · simp only [List.all_eq_true, List.mem_range]
    intro i hi
    interval_cases i
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_1
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_2
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_3
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_4
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_5
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_6
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_7
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_8
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_9
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_10
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_11
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_12
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_13
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_14
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_11_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_1 : certTriple [5,13] 13 (lowF 3 1) (highF 3 1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_2 : certTriple [5,13] 13 (lowF 3 2) (highF 3 2) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_3 : certTriple [5,13] 13 (lowF 3 3) (highF 3 3) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_4 : certTriple [5,13] 13 (lowF 3 4) (highF 3 4) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_5 : certTriple [5,13] 13 (lowF 3 5) (highF 3 5) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_6 : certTriple [5,13] 13 (lowF 3 6) (highF 3 6) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_7 : certTriple [5,13] 13 (lowF 3 7) (highF 3 7) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_8 : certTriple [5,13] 13 (lowF 3 8) (highF 3 8) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_9 : certTriple [5,13] 13 (lowF 3 9) (highF 3 9) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_10 : certTriple [5,13] 13 (lowF 3 10) (highF 3 10) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_11 : certTriple [5,13] 13 (lowF 3 11) (highF 3 11) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_12 : certTriple [5,13] 13 (lowF 3 12) (highF 3 12) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_13 : certTriple [5,13] 13 (lowF 3 13) (highF 3 13) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_14 : certTriple [5,13] 13 (lowF 3 14) (highF 3 14) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_13_15 : certTriple [5,13] 13 (lowF 3 15) (highF 3 15) = true := by decide
theorem cert_3_5_13_all : certTriple [3,5,13] 13 (1,1) (1,1) = true := by
  rw [certTriple]
  split_ifs with h
  · rfl
  · simp only [List.all_eq_true, List.mem_range]
    intro i hi
    interval_cases i
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_1
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_2
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_3
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_4
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_5
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_6
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_7
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_8
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_9
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_10
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_11
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_12
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_13
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_14
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_13_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_1 : certTriple [5,17] 17 (lowF 3 1) (highF 3 1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_2 : certTriple [5,17] 17 (lowF 3 2) (highF 3 2) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_3 : certTriple [5,17] 17 (lowF 3 3) (highF 3 3) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_4 : certTriple [5,17] 17 (lowF 3 4) (highF 3 4) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_5 : certTriple [5,17] 17 (lowF 3 5) (highF 3 5) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_6 : certTriple [5,17] 17 (lowF 3 6) (highF 3 6) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_7 : certTriple [5,17] 17 (lowF 3 7) (highF 3 7) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_8 : certTriple [5,17] 17 (lowF 3 8) (highF 3 8) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_9 : certTriple [5,17] 17 (lowF 3 9) (highF 3 9) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_10 : certTriple [5,17] 17 (lowF 3 10) (highF 3 10) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_11 : certTriple [5,17] 17 (lowF 3 11) (highF 3 11) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_12 : certTriple [5,17] 17 (lowF 3 12) (highF 3 12) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_13 : certTriple [5,17] 17 (lowF 3 13) (highF 3 13) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_14 : certTriple [5,17] 17 (lowF 3 14) (highF 3 14) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_17_15 : certTriple [5,17] 17 (lowF 3 15) (highF 3 15) = true := by decide
theorem cert_3_5_17_all : certTriple [3,5,17] 17 (1,1) (1,1) = true := by
  rw [certTriple]
  split_ifs with h
  · rfl
  · simp only [List.all_eq_true, List.mem_range]
    intro i hi
    interval_cases i
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_1
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_2
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_3
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_4
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_5
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_6
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_7
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_8
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_9
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_10
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_11
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_12
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_13
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_14
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_17_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_1 : certTriple [5,19] 19 (lowF 3 1) (highF 3 1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_2 : certTriple [5,19] 19 (lowF 3 2) (highF 3 2) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_3 : certTriple [5,19] 19 (lowF 3 3) (highF 3 3) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_4 : certTriple [5,19] 19 (lowF 3 4) (highF 3 4) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_5 : certTriple [5,19] 19 (lowF 3 5) (highF 3 5) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_6 : certTriple [5,19] 19 (lowF 3 6) (highF 3 6) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_7 : certTriple [5,19] 19 (lowF 3 7) (highF 3 7) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_8 : certTriple [5,19] 19 (lowF 3 8) (highF 3 8) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_9 : certTriple [5,19] 19 (lowF 3 9) (highF 3 9) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_10 : certTriple [5,19] 19 (lowF 3 10) (highF 3 10) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_11 : certTriple [5,19] 19 (lowF 3 11) (highF 3 11) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_12 : certTriple [5,19] 19 (lowF 3 12) (highF 3 12) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_13 : certTriple [5,19] 19 (lowF 3 13) (highF 3 13) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_14 : certTriple [5,19] 19 (lowF 3 14) (highF 3 14) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_19_15 : certTriple [5,19] 19 (lowF 3 15) (highF 3 15) = true := by decide
theorem cert_3_5_19_all : certTriple [3,5,19] 19 (1,1) (1,1) = true := by
  rw [certTriple]
  split_ifs with h
  · rfl
  · simp only [List.all_eq_true, List.mem_range]
    intro i hi
    interval_cases i
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_1
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_2
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_3
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_4
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_5
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_6
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_7
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_8
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_9
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_10
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_11
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_12
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_13
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_14
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_19_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_1 : certTriple [5,23] 23 (lowF 3 1) (highF 3 1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_2 : certTriple [5,23] 23 (lowF 3 2) (highF 3 2) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_3 : certTriple [5,23] 23 (lowF 3 3) (highF 3 3) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_4 : certTriple [5,23] 23 (lowF 3 4) (highF 3 4) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_5 : certTriple [5,23] 23 (lowF 3 5) (highF 3 5) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_6 : certTriple [5,23] 23 (lowF 3 6) (highF 3 6) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_7 : certTriple [5,23] 23 (lowF 3 7) (highF 3 7) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_8 : certTriple [5,23] 23 (lowF 3 8) (highF 3 8) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_9 : certTriple [5,23] 23 (lowF 3 9) (highF 3 9) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_10 : certTriple [5,23] 23 (lowF 3 10) (highF 3 10) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_11 : certTriple [5,23] 23 (lowF 3 11) (highF 3 11) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_12 : certTriple [5,23] 23 (lowF 3 12) (highF 3 12) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_13 : certTriple [5,23] 23 (lowF 3 13) (highF 3 13) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_14 : certTriple [5,23] 23 (lowF 3 14) (highF 3 14) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_23_15 : certTriple [5,23] 23 (lowF 3 15) (highF 3 15) = true := by decide
theorem cert_3_5_23_all : certTriple [3,5,23] 23 (1,1) (1,1) = true := by
  rw [certTriple]
  split_ifs with h
  · rfl
  · simp only [List.all_eq_true, List.mem_range]
    intro i hi
    interval_cases i
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_1
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_2
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_3
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_4
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_5
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_6
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_7
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_8
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_9
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_10
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_11
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_12
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_13
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_14
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_23_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_1 : certTriple [5,29] 29 (lowF 3 1) (highF 3 1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_2 : certTriple [5,29] 29 (lowF 3 2) (highF 3 2) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_3 : certTriple [5,29] 29 (lowF 3 3) (highF 3 3) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_4 : certTriple [5,29] 29 (lowF 3 4) (highF 3 4) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_5 : certTriple [5,29] 29 (lowF 3 5) (highF 3 5) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_6 : certTriple [5,29] 29 (lowF 3 6) (highF 3 6) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_7 : certTriple [5,29] 29 (lowF 3 7) (highF 3 7) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_8 : certTriple [5,29] 29 (lowF 3 8) (highF 3 8) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_9 : certTriple [5,29] 29 (lowF 3 9) (highF 3 9) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_10 : certTriple [5,29] 29 (lowF 3 10) (highF 3 10) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_11 : certTriple [5,29] 29 (lowF 3 11) (highF 3 11) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_12 : certTriple [5,29] 29 (lowF 3 12) (highF 3 12) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_13 : certTriple [5,29] 29 (lowF 3 13) (highF 3 13) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_14 : certTriple [5,29] 29 (lowF 3 14) (highF 3 14) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_5_29_15 : certTriple [5,29] 29 (lowF 3 15) (highF 3 15) = true := by decide
theorem cert_3_5_29_all : certTriple [3,5,29] 29 (1,1) (1,1) = true := by
  rw [certTriple]
  split_ifs with h
  · rfl
  · simp only [List.all_eq_true, List.mem_range]
    intro i hi
    interval_cases i
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_1
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_2
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_3
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_4
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_5
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_6
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_7
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_8
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_9
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_10
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_11
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_12
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_13
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_14
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_5_29_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_1 : certTriple [7,11] 11 (lowF 3 1) (highF 3 1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_2 : certTriple [7,11] 11 (lowF 3 2) (highF 3 2) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_3 : certTriple [7,11] 11 (lowF 3 3) (highF 3 3) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_4 : certTriple [7,11] 11 (lowF 3 4) (highF 3 4) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_5 : certTriple [7,11] 11 (lowF 3 5) (highF 3 5) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_6 : certTriple [7,11] 11 (lowF 3 6) (highF 3 6) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_7 : certTriple [7,11] 11 (lowF 3 7) (highF 3 7) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_8 : certTriple [7,11] 11 (lowF 3 8) (highF 3 8) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_9 : certTriple [7,11] 11 (lowF 3 9) (highF 3 9) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_10 : certTriple [7,11] 11 (lowF 3 10) (highF 3 10) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_11 : certTriple [7,11] 11 (lowF 3 11) (highF 3 11) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_12 : certTriple [7,11] 11 (lowF 3 12) (highF 3 12) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_13 : certTriple [7,11] 11 (lowF 3 13) (highF 3 13) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_14 : certTriple [7,11] 11 (lowF 3 14) (highF 3 14) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_11_15 : certTriple [7,11] 11 (lowF 3 15) (highF 3 15) = true := by decide
theorem cert_3_7_11_all : certTriple [3,7,11] 11 (1,1) (1,1) = true := by
  rw [certTriple]
  split_ifs with h
  · rfl
  · simp only [List.all_eq_true, List.mem_range]
    intro i hi
    interval_cases i
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_1
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_2
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_3
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_4
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_5
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_6
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_7
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_8
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_9
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_10
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_11
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_12
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_13
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_14
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_11_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_1 : certTriple [7,13] 13 (lowF 3 1) (highF 3 1) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_2 : certTriple [7,13] 13 (lowF 3 2) (highF 3 2) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_3 : certTriple [7,13] 13 (lowF 3 3) (highF 3 3) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_4 : certTriple [7,13] 13 (lowF 3 4) (highF 3 4) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_5 : certTriple [7,13] 13 (lowF 3 5) (highF 3 5) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_6 : certTriple [7,13] 13 (lowF 3 6) (highF 3 6) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_7 : certTriple [7,13] 13 (lowF 3 7) (highF 3 7) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_8 : certTriple [7,13] 13 (lowF 3 8) (highF 3 8) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_9 : certTriple [7,13] 13 (lowF 3 9) (highF 3 9) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_10 : certTriple [7,13] 13 (lowF 3 10) (highF 3 10) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_11 : certTriple [7,13] 13 (lowF 3 11) (highF 3 11) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_12 : certTriple [7,13] 13 (lowF 3 12) (highF 3 12) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_13 : certTriple [7,13] 13 (lowF 3 13) (highF 3 13) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_14 : certTriple [7,13] 13 (lowF 3 14) (highF 3 14) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert_3_7_13_15 : certTriple [7,13] 13 (lowF 3 15) (highF 3 15) = true := by decide
theorem cert_3_7_13_all : certTriple [3,7,13] 13 (1,1) (1,1) = true := by
  rw [certTriple]
  split_ifs with h
  · rfl
  · simp only [List.all_eq_true, List.mem_range]
    intro i hi
    interval_cases i
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_1
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_2
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_3
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_4
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_5
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_6
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_7
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_8
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_9
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_10
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_11
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_12
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_13
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_14
    · simpa only [Nat.reduceAdd, mulF, one_mul] using cert_3_7_13_15

theorem certTriple_patterns (b c : ℕ)
    (h : (b = 5 ∧ c ∈ ({7,11,13,17,19,23,29} : Finset ℕ)) ∨
         (b = 7 ∧ c ∈ ({11,13} : Finset ℕ))) :
    certTriple [3,b,c] c (1,1) (1,1) = true := by
  rcases h with ⟨rfl,hc⟩ | ⟨rfl,hc⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_3_5_7_all
    · exact cert_3_5_11_all
    · exact cert_3_5_13_all
    · exact cert_3_5_17_all
    · exact cert_3_5_19_all
    · exact cert_3_5_23_all
    · exact cert_3_5_29_all
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact cert_3_7_11_all
    · exact cert_3_7_13_all

theorem odd_four_core_gap (n : ℕ) (hn : n ≠ 0) (ho : Odd n)
    (hcard : n.primeFactors.card ≤ 4) (hdef : n.abundancyIndex < 2) :
    n.abundancyIndex ≤ 2 - (2798 / 51134034375 : ℚ) := by
  by_contra hnnear
  have hnear : 2 - (2798 / 51134034375 : ℚ) < n.abundancyIndex := lt_of_not_ge hnnear
  obtain ⟨b,c,q,hpat,hqhi,hq3,hqb,hqc,hcq,hs⟩ := near_two_core_bounded_patterns n hn ho hcard hdef hnear
  have h3 : 3 ∈ n.primeFactors := by rw [hs]; simp
  have hb : b ∈ n.primeFactors := by rw [hs]; simp
  have hc : c ∈ n.primeFactors := by rw [hs]; simp
  have hq : q ∈ n.primeFactors := by rw [hs]; simp
  have hp3 := Nat.prime_of_mem_primeFactors h3
  have hpb := Nat.prime_of_mem_primeFactors hb
  have hpc := Nat.prime_of_mem_primeFactors hc
  have hpq := Nat.prime_of_mem_primeFactors hq
  have he3 := hp3.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors h3)
  have heb := hpb.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hb)
  have hec := hpc.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hc)
  have heq := hpq.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hq)
  have h3b : 3 ≠ b := by rcases hpat with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  have h3c : 3 ≠ c := by rcases hpat with ⟨_,hc⟩ | ⟨_,hc⟩ <;>
    simp only [Finset.mem_insert,Finset.mem_singleton] at hc <;> omega
  have hbc : b ≠ c := by rcases hpat with ⟨rfl,hc⟩ | ⟨rfl,hc⟩ <;>
    simp only [Finset.mem_insert,Finset.mem_singleton] at hc <;> omega
  have hcpos : 0 < c := hpc.pos
  have hbox : List.Forall₂ FullBox [3,b,c]
      [(3^n.factorization 3).abundancyIndex,(b^n.factorization b).abundancyIndex,
       (c^n.factorization c).abundancyIndex] := by
    exact .cons (prime_fullBox 3 _ hp3 he3) (.cons (prime_fullBox b _ hpb heb)
      (.cons (prime_fullBox c _ hpc hec) .nil))
  have hqbox := prime_fullBox q (n.factorization q) hpq heq
  have htail : 1 ≤ (q^n.factorization q).abundancyIndex := by
    have h := index_min_factor q _ hpq heq
    have hpq0 : (0 : ℚ) < q := by exact_mod_cast hpq.pos
    have : 1 ≤ ((q : ℚ)+1)/q := by rw [le_div_iff₀ hpq0]; linarith
    exact le_trans this (by simpa [valueF] using h)
  have htailhi : (q^n.factorization q).abundancyIndex ≤ valueF (c+1,c) := by
    have hc1 : 1 < c+1 := by omega
    have hqbig : c+1 ≤ q := by omega
    have hh := le_trans (le_of_lt (prime_power_index_lt q (n.factorization q) hpq))
      (prime_ratio_antitone q (c+1) hc1 hqbig)
    have hc0 : 1 ≤ c+1 := by omega
    simpa [valueF, Nat.cast_sub hc0] using hh
  have h := certTriple_sound [3,b,c] c (1,1) (1,1) _ (by decide) (by decide) hbox
    q hpq hcq (by omega) _ hqbox hcpos htail htailhi (certTriple_patterns b c hpat)
  have hi := index_of_four_factors n 3 b c q hn h3b h3c hbc (Ne.symm hq3)
    (Ne.symm hqb) (Ne.symm hqc) hs
  rw [hi] at hnear hdef
  norm_num [valueF, List.prod_cons, List.prod_nil, mul_assoc] at h
  rcases h with h | h <;> linarith

def Growth (B : ℕ) : List ℕ → Prop
  | [] => True
  | x :: xs => x ≤ B * xs.prod ∧ Growth B xs

theorem product_le_growth (B : ℕ) (xs : List ℕ) (h : Growth B xs) :
    xs.prod ≤ B ^ (2 ^ xs.length - 1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rcases h with ⟨hx, ht⟩
    have hs := ih ht
    have hn : 1 ≤ 2 ^ xs.length := by exact Nat.one_le_pow _ _ (by omega)
    have hexp : 2 ^ (xs.length + 1) - 1 = 1 + 2 * (2 ^ xs.length - 1) := by
      rw [pow_succ]
      omega
    simp only [List.prod_cons, List.length_cons]
    calc
      x * xs.prod ≤ (B * xs.prod) * xs.prod := Nat.mul_le_mul_right _ hx
      _ ≤ (B * (B ^ (2 ^ xs.length - 1))) * (B ^ (2 ^ xs.length - 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hs) hs
      _ = B ^ (2 ^ (xs.length + 1) - 1) := by
        rw [hexp, pow_add, Nat.mul_comm 2 (2 ^ xs.length - 1), pow_mul]
        simp [pow_two, Nat.mul_assoc]

theorem lift_pow_bound (n a b : ℕ) (h : n ≤ 10 ^ a) (hab : a ≤ b) : n ≤ 10 ^ b :=
  le_trans h (Nat.pow_le_pow_right (by decide : 0 < 10) hab)

theorem growth_size_bound (xs : List ℕ) (h : Growth (192 * 36550417 ^ 5) xs)
    (hlen : xs.length ≤ 5) : xs.prod ≤ 10 ^ 540879392320 := by
  have hb : 192 * 36550417 ^ 5 ≤ 10 ^ 41 := by norm_num
  have he : 2 ^ xs.length - 1 ≤ 31 := by
    have hp : 2 ^ xs.length ≤ 2 ^ 5 := Nat.pow_le_pow_right (by omega) hlen
    norm_num at hp
    omega
  apply lift_pow_bound xs.prod 1271 540879392320 ?_ (by decide)
  calc
    xs.prod ≤ (192 * 36550417 ^ 5) ^ (2 ^ xs.length - 1) := product_le_growth _ _ h
    _ ≤ (10 ^ 41) ^ (2 ^ xs.length - 1) := Nat.pow_le_pow_left hb _
    _ ≤ (10 ^ 41) ^ 31 := Nat.pow_le_pow_right (by positivity) he
    _ = 10 ^ 1271 := by rw [← pow_mul]

theorem rational_gap (a d : ℕ) (hd : 0 < d) (h : (2 : ℚ) < a / (d : ℚ)) :
    1 / (d : ℚ) ≤ a / (d : ℚ) - 2 := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have ha : 2 * d < a := by
    have ht := (lt_div_iff₀ hdq).mp h
    exact_mod_cast ht
  have ha' : 2 * d + 1 ≤ a := by omega
  have haq : (2 : ℚ) * d + 1 ≤ a := by exact_mod_cast ha'
  apply (div_le_iff₀ hdq).2
  field_simp
  linarith

theorem gap_forces_power_bound (a d x : ℕ) (hd : 0 < d) (hx : 0 < x)
    (h : (2 : ℚ) < a / (d : ℚ))
    (hu : a / (d : ℚ) - 2 < 192 / (x : ℚ)) : x < 192 * d := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hxq : (0 : ℚ) < x := by exact_mod_cast hx
  have hgap := rational_gap a d hd h
  have hle : 1 / (d : ℚ) < 192 / (x : ℚ) := lt_of_le_of_lt hgap hu
  have hm := (div_lt_div_iff₀ hdq hxq).mp hle
  norm_num at hm
  exact_mod_cast hm

/-- Telescoping error for products of at most five factors, each bounded by two. -/
theorem list_product_gap (l : List (ℚ × ℚ)) (eps : ℚ) (he : 0 ≤ eps)
    (hl : ∀ z ∈ l, 0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ 2 ∧ z.2 - z.1 ≤ eps) :
    0 ≤ (l.map Prod.fst).prod ∧ (l.map Prod.fst).prod ≤ 2 ^ l.length ∧
    0 ≤ (l.map Prod.snd).prod ∧ (l.map Prod.snd).prod ≤ 2 ^ l.length ∧
    (l.map Prod.snd).prod - (l.map Prod.fst).prod ≤ l.length * 2 ^ l.length * eps := by
  induction l with
  | nil => simp [he]
  | cons z zs ih =>
    have hz := hl z (by simp)
    have hzs : ∀ z ∈ zs, 0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ 2 ∧ z.2 - z.1 ≤ eps := by
      intro q hq; exact hl q (by simp [hq])
    rcases ih hzs with ⟨ha0, ha2, hb0, hb2, hd⟩
    have hz0 : 0 ≤ z.2 := le_trans hz.1 hz.2.1
    have ha2' : 0 ≤ (2 : ℚ) ^ zs.length := by positivity
    have hsum : 0 ≤ ((zs.length : ℚ) * 2 ^ zs.length * eps) := by positivity
    have hmul : z.2 * (zs.map Prod.snd).prod - z.1 * (zs.map Prod.fst).prod ≤
        2 * ((zs.length : ℚ) * 2 ^ zs.length * eps) + eps * 2 ^ zs.length := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hz.2.2.1) (sub_nonneg.mpr hd),
        mul_nonneg (sub_nonneg.mpr hz.2.2.2) (sub_nonneg.mpr ha2),
        mul_nonneg (sub_nonneg.mpr ha2) he]
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
      pow_succ]
    constructor
    · exact mul_nonneg hz.1 ha0
    constructor
    · nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr ha2), mul_nonneg ha2' (sub_nonneg.mpr (le_trans hz.2.1 hz.2.2.1))]
    constructor
    · exact mul_nonneg hz0 hb0
    constructor
    · nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hb2), mul_nonneg ha2' (sub_nonneg.mpr hz.2.2.1)]
    · have hn : (0 : ℚ) ≤ zs.length := by positivity
      nlinarith [mul_nonneg hn (mul_nonneg ha2' he)]

theorem list_product_gap_five (l : List (ℚ × ℚ)) (eps : ℚ) (he : 0 ≤ eps)
    (hn : l.length ≤ 5)
    (hl : ∀ z ∈ l, 0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ 2 ∧ z.2 - z.1 ≤ eps) :
    (l.map Prod.snd).prod - (l.map Prod.fst).prod ≤ 160 * eps := by
  have hg := (list_product_gap l eps he hl).2.2.2.2
  have hnq : (l.length : ℚ) ≤ 5 := by exact_mod_cast hn
  have hp : (2 : ℚ) ^ l.length ≤ 32 := by
    have hp' : 2 ^ l.length ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hn
    norm_num at hp'
    exact_mod_cast hp'
  have hpos : (0 : ℚ) ≤ (2 : ℚ) ^ l.length := by positivity
  have hlen : (0 : ℚ) ≤ l.length := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hnq) (mul_nonneg hpos he),
    mul_nonneg (sub_nonneg.mpr hp) he]

theorem index_prime_power_formula (p e : ℕ) (hp : p.Prime) :
    (p ^ e).abundancyIndex = ((p : ℚ) ^ (e + 1) - 1) / (((p : ℚ) - 1) * (p : ℚ) ^ e) := by
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℚ) ≠ 0 := by linarith
  have hpm : (p : ℚ) - 1 ≠ 0 := by linarith
  rw [Nat.abundancyIndex, ← ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply_prime_pow hp]
  push_cast
  have hgeom := geom_sum_mul (p : ℚ) (e + 1)
  field_simp
  nlinarith

theorem index_prime_power_step (p e : ℕ) (hp : p.Prime) :
    (p ^ (e+1)).abundancyIndex - (p ^ e).abundancyIndex = 1 / (p : ℚ) ^ (e+1) := by
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℚ) ≠ 0 := by linarith
  have hpm : (p : ℚ) - 1 ≠ 0 := by linarith
  rw [index_prime_power_formula p (e+1) hp, index_prime_power_formula p e hp]
  rw [pow_succ, pow_succ (p : ℚ) e]
  field_simp
  ring

theorem prime_power_ceiling_gap (p e : ℕ) (hp : p.Prime) :
    (p : ℚ) / ((p : ℚ) - 1) - (p ^ e).abundancyIndex =
      1 / (((p : ℚ) - 1) * (p : ℚ) ^ e) := by
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℚ) ≠ 0 := by linarith
  have hpm : (p : ℚ) - 1 ≠ 0 := by linarith
  rw [index_prime_power_formula p e hp, pow_succ]
  field_simp
  ring

theorem prime_power_ceiling_gap_le (p e : ℕ) (hp : p.Prime) :
    (p : ℚ) / ((p : ℚ) - 1) - (p ^ e).abundancyIndex ≤ 1 / (p : ℚ) ^ e := by
  rw [prime_power_ceiling_gap p e hp]
  have hpq : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℚ) < p := by linarith
  have hpe : 0 < (p : ℚ) ^ e := pow_pos hp0 _
  apply (div_le_div_iff₀ (mul_pos (by linarith) hpe) hpe).2
  nlinarith

theorem rational_gap_implies_growth (a d x prevprod P : ℕ)
    (hd : 0 < d) (hx : 0 < x)
    (habove : (2 : ℚ) < a / (d : ℚ))
    (I : ℚ) (htail : a / (d : ℚ) - I ≤ 160 / (x : ℚ))
    (hprimitive : I - 2 < 32 / (x : ℚ))
    (hden : d ≤ P ^ 5 * prevprod) :
    x ≤ (192 * P ^ 5) * prevprod := by
  have hid : 160 / (x : ℚ) + 32 / (x : ℚ) = 192 / (x : ℚ) := by ring
  have hu : a / (d : ℚ) - 2 < 192 / (x : ℚ) := by linarith
  have hpow := gap_forces_power_bound a d x hd hx habove hu
  calc
    x ≤ 192 * d := le_of_lt hpow
    _ ≤ 192 * (P ^ 5 * prevprod) := Nat.mul_le_mul_left _ hden
    _ = (192 * P ^ 5) * prevprod := by ring

theorem prime_ceiling_le_two (p : ℕ) (hp : p.Prime) :
    (p : ℚ) / ((p : ℚ) - 1) ≤ 2 := by
  have hpq : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  apply (div_le_iff₀ (by linarith : (0 : ℚ) < (p : ℚ) - 1)).2
  linarith

theorem index_prime_power_nonneg (p e : ℕ) : 0 ≤ (p ^ e).abundancyIndex := by
  unfold Nat.abundancyIndex
  positivity

theorem index_prime_power_le_ceiling (p e : ℕ) (hp : p.Prime) :
    (p ^ e).abundancyIndex ≤ (p : ℚ) / ((p : ℚ) - 1) := by
  have hpq : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℚ) < p := by linarith
  have hg := prime_power_ceiling_gap p e hp
  have hpositive : (0 : ℚ) ≤ 1 / (((p : ℚ) - 1) * (p : ℚ) ^ e) := by
    apply div_nonneg (by norm_num)
    exact mul_nonneg (by linarith) (le_of_lt (pow_pos hp0 _))
  linarith

theorem index_mul_coprime_size (a b : ℕ) (h : a.Coprime b) :
    (a * b).abundancyIndex = a.abundancyIndex * b.abundancyIndex := by
  simp only [Nat.abundancyIndex, Nat.Coprime.sum_divisors_mul h, Nat.cast_mul]
  ring

theorem primitive_excess_bound (c p e : ℕ) (hp : p.Prime) (hcop : c.Coprime p)
    (hdef : (c * p ^ e).abundancyIndex < 2) (hcore : c.abundancyIndex ≤ 32) :
    (c * p ^ (e+1)).abundancyIndex - 2 < 32 / (p : ℚ) ^ (e+1) := by
  have hpow : (0 : ℚ) < (p : ℚ) ^ (e+1) := by
    apply pow_pos
    exact_mod_cast hp.pos
  rw [index_mul_coprime_size _ _ (hcop.pow_right _)] at hdef ⊢
  have hstep := index_prime_power_step p e hp
  have hid : c.abundancyIndex * (p ^ (e + 1)).abundancyIndex -
      c.abundancyIndex * (p ^ e).abundancyIndex = c.abundancyIndex / (p : ℚ) ^ (e+1) := by
    rw [← mul_sub, hstep]
    ring
  have hle : c.abundancyIndex / (p : ℚ) ^ (e+1) ≤ 32 / (p : ℚ) ^ (e+1) :=
    div_le_div_of_nonneg_right hcore (le_of_lt hpow)
  linarith

theorem growth_of_suffixes (B : ℕ) (l : List (ℕ × ℕ))
    (h : ∀ pre q post, l = pre ++ q :: post → q.2 ≤ B * (post.map Prod.snd).prod) :
    Growth B (l.map Prod.snd) := by
  induction l with
  | nil => trivial
  | cons q qs ih =>
    simp only [List.map_cons, Growth]
    constructor
    · exact h [] q qs rfl
    · apply ih
      intro pre q' post heq
      apply h (q :: pre) q' post
      simp only [List.cons_append]
      exact congrArg (List.cons q) heq


/-- Prime factors, paired with their full prime powers, sorted from large to small. -/
noncomputable def sortedPrimePowers (n : ℕ) : List (ℕ × ℕ) :=
  (n.primeFactors.toList.map fun p => (p, p ^ n.factorization p)).mergeSort
    (fun a b => decide (b.2 ≤ a.2))

theorem sortedPrimePowers_sorted (n : ℕ) :
    (sortedPrimePowers n).Pairwise (fun a b => b.2 ≤ a.2) := by
  unfold sortedPrimePowers
  have htrans : ∀ (a b c : ℕ × ℕ), decide (b.2 ≤ a.2) = true →
      decide (c.2 ≤ b.2) = true → decide (c.2 ≤ a.2) = true := by
    intro a b c h1 h2
    simp only [decide_eq_true_eq] at *
    exact le_trans h2 h1
  have htotal : ∀ (a b : ℕ × ℕ), (decide (b.2 ≤ a.2) || decide (a.2 ≤ b.2)) = true := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total b.2 a.2
  simpa only [decide_eq_true_eq] using List.pairwise_mergeSort htrans htotal
    (n.primeFactors.toList.map fun p => (p, p ^ n.factorization p))

theorem sortedPrimePowers_mem_iff (n : ℕ) (q : ℕ × ℕ) :
    q ∈ sortedPrimePowers n ↔ q.1 ∈ n.primeFactors ∧ q.2 = q.1 ^ n.factorization q.1 := by
  unfold sortedPrimePowers
  rw [(List.mergeSort_perm _ _).mem_iff]
  simp only [List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp, rfl⟩
  · rintro ⟨hp, hq⟩
    exact ⟨q.1, hp, Prod.ext rfl hq.symm⟩

theorem sortedPrimePowers_length (n : ℕ) : (sortedPrimePowers n).length = n.primeFactors.card := by
  unfold sortedPrimePowers
  rw [(List.mergeSort_perm _ _).length_eq]
  simp

theorem sortedPrimePowers_prod (n : ℕ) (hn : n ≠ 0) :
    ((sortedPrimePowers n).map Prod.snd).prod = n := by
  unfold sortedPrimePowers
  rw [((List.mergeSort_perm _ _).map Prod.snd).prod_eq]
  simp only [List.map_map, Function.comp_def]
  rw [Finset.prod_map_toList]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm

theorem sortedPrimePowers_index (n : ℕ)
    (hindex : n.abundancyIndex = ∏ p ∈ n.primeFactors, (p ^ n.factorization p).abundancyIndex) :
    ((sortedPrimePowers n).map fun q => q.2.abundancyIndex).prod = n.abundancyIndex := by
  unfold sortedPrimePowers
  have hperm := List.mergeSort_perm (n.primeFactors.toList.map fun p => (p, p ^ n.factorization p))
    (fun (a b : ℕ × ℕ) => decide (b.2 ≤ a.2))
  rw [(hperm.map (fun q : ℕ × ℕ => q.2.abundancyIndex)).prod_eq]
  simp only [List.map_map, Function.comp_def]
  rw [Finset.prod_map_toList]
  exact hindex.symm

theorem sortedPrimePowers_properties (n : ℕ) (q : ℕ × ℕ) (hq : q ∈ sortedPrimePowers n) :
    q.1.Prime ∧ 0 < n.factorization q.1 ∧ 0 < q.2 ∧ q.2 = q.1 ^ n.factorization q.1 := by
  have ⟨hp, heq⟩ := (sortedPrimePowers_mem_iff n q).mp hq
  have ⟨hprime, hdvd, hn⟩ := Nat.mem_primeFactors.mp hp
  exact ⟨hprime, hprime.factorization_pos_of_dvd hn hdvd, heq ▸ pow_pos hprime.pos _, heq⟩

theorem previous_prime_power_proper (n p : ℕ) (hp : p ∈ n.primeFactors) :
    let c := ordCompl[p] n
    let e := n.factorization p - 1
    c * p ^ e ∈ n.properDivisors ∧ n / p = c * p ^ e ∧ c.Coprime p := by
  have ⟨hprime, hdvd, hn⟩ := Nat.mem_primeFactors.mp hp
  have hfac : 0 < n.factorization p := hprime.factorization_pos_of_dvd hn hdvd
  let c := ordCompl[p] n
  let e := n.factorization p - 1
  have he : e + 1 = n.factorization p := Nat.sub_add_cancel hfac
  have hprod : (c * p ^ e) * p = n := by
    calc
      (c * p ^ e) * p = p ^ n.factorization p * c := by rw [← he, pow_succ]; ring
      _ = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcpos : 0 < c := Nat.ordCompl_pos p hn
  have hprevpos : 0 < c * p ^ e := mul_pos hcpos (pow_pos hprime.pos _)
  have hlt : c * p ^ e < n := by
    rw [← hprod]
    nlinarith [hprime.two_le]
  have hpdiv : n / p = c * p ^ e := by
    rw [← hprod, Nat.mul_comm, Nat.mul_div_cancel_left _ hprime.pos]
  refine ⟨Nat.mem_properDivisors.mpr ⟨?_, hlt⟩, hpdiv, (Nat.coprime_ordCompl hprime hn).symm⟩
  exact ⟨p, hprod.symm⟩

theorem previous_prime_power_deficient (n p : ℕ) (hp : p ∈ n.primeFactors)
    (hdef : ∀ d ∈ n.properDivisors, d.Deficient) :
    (ordCompl[p] n * p ^ (n.factorization p - 1)).Deficient := by
  exact hdef _ (previous_prime_power_proper n p hp).1

theorem primitive_excess_any_factor (m p : ℕ) (ho : Odd m) (hp : p ∈ m.primeFactors)
    (hcard : m.primeFactors.card ≤ 5)
    (hdef : ∀ d ∈ m.properDivisors, d.Deficient) :
    m.abundancyIndex - 2 < 32 / (p : ℚ) ^ m.factorization p := by
  obtain ⟨hpp, hpd, hm0⟩ := Nat.mem_primeFactors.mp hp
  have hpos : 0 < m.factorization p := hpp.factorization_pos_of_dvd hm0 hpd
  have hprev := previous_prime_power_deficient m p hp hdef
  have hprev0 : ordCompl[p] m * p ^ (m.factorization p - 1) ≠ 0 := Nat.ne_of_gt hprev.pos
  have hprevindex := (deficient_iff_index_lt_two _ hprev0).mp hprev
  have hcop : (ordCompl[p] m).Coprime p := (Nat.coprime_ordCompl hpp hm0).symm
  have hcore := core_index_le_32 m p ho hp hcard hdef
  have h := primitive_excess_bound (ordCompl[p] m) p (m.factorization p - 1) hpp hcop hprevindex hcore
  have he : m.factorization p - 1 + 1 = m.factorization p := by omega
  rw [he] at h
  have hdecomp : ordCompl[p] m * p ^ m.factorization p = m := by
    simpa [mul_comm] using Nat.ordProj_mul_ordCompl_eq_self m p
  simpa [hdecomp] using h
theorem list_prod_pair_le (l : List (ℚ × ℚ))
    (hl : ∀ z ∈ l, 0 ≤ z.1 ∧ z.1 ≤ z.2) :
    (l.map Prod.fst).prod ≤ (l.map Prod.snd).prod := by
  induction l with
  | nil => simp
  | cons z zs ih =>
    have hz := hl z (by simp)
    have ht : ∀ z ∈ zs, 0 ≤ z.1 ∧ z.1 ≤ z.2 := by
      intro q hq; exact hl q (by simp [hq])
    have hp := ih ht
    have hpos : 0 ≤ (zs.map Prod.fst).prod := by
      apply List.prod_nonneg
      simp only [List.mem_map]
      rintro x ⟨z, hz, rfl⟩
      exact (ht z hz).1
    simp only [List.map_cons, List.prod_cons]
    exact mul_le_mul hz.2 hp hpos (le_trans hz.1 hz.2)

def capPairs (pre : List (ℕ × ℕ)) (q : ℕ × ℕ) (post : List (ℕ × ℕ)) : List (ℚ × ℚ) :=
  ((pre ++ [q]).map fun z => (z.2.abundancyIndex, (z.1 : ℚ) / (z.1 - 1))) ++
    (post.map fun z => (z.2.abundancyIndex, z.2.abundancyIndex))

theorem capPairs_first (pre : List (ℕ × ℕ)) (q : ℕ × ℕ) (post : List (ℕ × ℕ)) :
    ((capPairs pre q post).map Prod.fst).prod =
      (((pre ++ q :: post).map fun z => z.2.abundancyIndex)).prod := by
  simp [capPairs, List.map_append, List.map_map, List.prod_append, Function.comp_def]

theorem capPairs_valid (n : ℕ) (pre : List (ℕ × ℕ)) (q : ℕ × ℕ) (post : List (ℕ × ℕ))
    (hlist : sortedPrimePowers n = pre ++ q :: post) :
    ∀ z ∈ capPairs pre q post, 0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ 2 ∧ z.2 - z.1 ≤ 1 / (q.2 : ℚ) := by
  have hqmem : q ∈ sortedPrimePowers n := by rw [hlist]; simp
  have hqpos : 0 < q.2 := (sortedPrimePowers_properties n q hqmem).2.2.1
  have hqposq : (0 : ℚ) < q.2 := by exact_mod_cast hqpos
  have hpre : ∀ z ∈ pre, q.2 ≤ z.2 := by
    have hs := sortedPrimePowers_sorted n
    rw [hlist, List.pairwise_append] at hs
    intro z hz
    exact hs.2.2 z hz q (by simp)
  intro z hz
  simp only [capPairs, List.mem_append, List.mem_map, List.mem_singleton] at hz
  rcases hz with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · have hymem : y ∈ sortedPrimePowers n := by
      rw [hlist]
      simp only [List.mem_append, List.mem_cons]
      rcases hy with hy | rfl
      · exact Or.inl hy
      · exact Or.inr (Or.inl rfl)
    have ⟨hp, _, _, hyeq⟩ := sortedPrimePowers_properties n y hymem
    have hle : q.2 ≤ y.2 := by
      rcases hy with hy | heq
      · exact hpre y hy
      · subst y; exact le_rfl
    have hleq : (q.2 : ℚ) ≤ y.2 := by exact_mod_cast hle
    have hgap := prime_power_ceiling_gap_le y.1 (n.factorization y.1) hp
    simp only [← Nat.cast_pow, ← hyeq] at hgap
    refine ⟨?_, ?_, prime_ceiling_le_two y.1 hp, ?_⟩
    · simpa [hyeq] using index_prime_power_nonneg y.1 (n.factorization y.1)
    · simpa [hyeq] using index_prime_power_le_ceiling y.1 (n.factorization y.1) hp
    · exact le_trans hgap (one_div_le_one_div_of_le hqposq hleq)
  · have hymem : y ∈ sortedPrimePowers n := by rw [hlist]; simp [hy]
    have ⟨hp, _, _, hy⟩ := sortedPrimePowers_properties n y hymem
    have hy0 : 0 ≤ y.2.abundancyIndex := by unfold Nat.abundancyIndex; positivity
    have hy2 : y.2.abundancyIndex ≤ 2 := by
      have h := le_trans (index_prime_power_le_ceiling y.1 (n.factorization y.1) hp) (prime_ceiling_le_two y.1 hp)
      simpa [hy] using h
    refine ⟨hy0, le_rfl, hy2, ?_⟩
    simp only [sub_self]
    positivity

theorem capPairs_length (pre : List (ℕ × ℕ)) (q : ℕ × ℕ) (post : List (ℕ × ℕ)) :
    (capPairs pre q post).length = (pre ++ q :: post).length := by
  simp [capPairs]

theorem capPairs_estimates (n : ℕ) (pre : List (ℕ × ℕ)) (q : ℕ × ℕ) (post : List (ℕ × ℕ))
    (hlist : sortedPrimePowers n = pre ++ q :: post) (hcard : n.primeFactors.card ≤ 5)
    (hindex : n.abundancyIndex = ∏ p ∈ n.primeFactors, (p ^ n.factorization p).abundancyIndex)
    (hab : 2 < n.abundancyIndex) :
    2 < ((capPairs pre q post).map Prod.snd).prod ∧
    ((capPairs pre q post).map Prod.snd).prod - n.abundancyIndex ≤ 160 / (q.2 : ℚ) := by
  have hqmem : q ∈ sortedPrimePowers n := by rw [hlist]; simp
  have hqpos : 0 < q.2 := (sortedPrimePowers_properties n q hqmem).2.2.1
  have hqposq : (0 : ℚ) < q.2 := by exact_mod_cast hqpos
  have hlen : (capPairs pre q post).length ≤ 5 := by
    rw [capPairs_length, ← hlist, sortedPrimePowers_length]
    exact hcard
  have hvalid := capPairs_valid n pre q post hlist
  have hfirst : ((capPairs pre q post).map Prod.fst).prod = n.abundancyIndex := by
    rw [capPairs_first, ← hlist]
    exact sortedPrimePowers_index n hindex
  have hle := list_prod_pair_le (capPairs pre q post) (fun z hz => ⟨(hvalid z hz).1, (hvalid z hz).2.1⟩)
  have hgap := list_product_gap_five (capPairs pre q post) (1 / (q.2 : ℚ))
    (by positivity) hlen hvalid
  rw [hfirst] at hle hgap
  constructor
  · linarith
  · convert hgap using 1 <;> ring

def capFractions (pre : List (ℕ × ℕ)) (q : ℕ × ℕ) (post : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  ((pre ++ [q]).map fun z => (z.1, z.1 - 1)) ++
    (post.map fun z => (∑ d ∈ z.2.divisors, d, z.2))

theorem list_product_fractions (l : List (ℕ × ℕ)) :
    (l.map fun z => (z.1 : ℚ) / z.2).prod =
      ((l.map Prod.fst).prod : ℚ) / ((l.map Prod.snd).prod : ℚ) := by
  induction l with
  | nil => simp
  | cons z zs ih =>
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
    rw [ih]
    ring

theorem capFractions_value (n : ℕ) (pre : List (ℕ × ℕ)) (q : ℕ × ℕ) (post : List (ℕ × ℕ))
    (hlist : sortedPrimePowers n = pre ++ q :: post) :
    ((capPairs pre q post).map Prod.snd).prod =
      (((capFractions pre q post).map Prod.fst).prod : ℚ) /
      (((capFractions pre q post).map Prod.snd).prod : ℚ) := by
  rw [← list_product_fractions]
  have hcast : ∀ y ∈ pre ++ [q], (y.1 : ℚ) - 1 = ((y.1 - 1 : ℕ) : ℚ) := by
    intro y hy
    have hy' : y ∈ sortedPrimePowers n := by
      rw [hlist]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      rcases hy with hy | rfl
      · exact Or.inl hy
      · exact Or.inr (Or.inl rfl)
    have hp := (sortedPrimePowers_properties n y hy').1
    rw [Nat.cast_sub (by have := hp.two_le; omega : 1 ≤ y.1)]
    norm_num
  have hpre : (pre.map fun x => (x.1 : ℚ) / ((x.1 : ℚ) - 1)) =
      (pre.map fun x => (x.1 : ℚ) / ((x.1 - 1 : ℕ) : ℚ)) := by
    apply List.map_congr_left
    intro y hy
    rw [hcast y (by simp [hy])]
  have hq := hcast q (by simp)
  simp only [capPairs, capFractions, List.map_append, List.prod_append, List.map_map, Function.comp_def,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [hpre, hq]
  rfl

theorem list_prod_le_pow (l : List ℕ) (P : ℕ) (hl : ∀ x ∈ l, x ≤ P) :
    l.prod ≤ P ^ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := hl x (by simp)
    have ht : ∀ y ∈ xs, y ≤ P := by intro y hy; exact hl y (by simp [hy])
    simp only [List.prod_cons, List.length_cons, pow_succ]
    calc
      x * xs.prod ≤ P * P ^ xs.length := Nat.mul_le_mul hx (ih ht)
      _ = P ^ xs.length * P := Nat.mul_comm _ _

theorem capFractions_denom (n P : ℕ) (pre : List (ℕ × ℕ)) (q : ℕ × ℕ) (post : List (ℕ × ℕ))
    (hlist : sortedPrimePowers n = pre ++ q :: post) (hcard : n.primeFactors.card ≤ 5)
    (hP : 1 ≤ P) (hprime : ∀ p ∈ n.primeFactors, p ≤ P) :
    0 < ((capFractions pre q post).map Prod.snd).prod ∧
    ((capFractions pre q post).map Prod.snd).prod ≤ P ^ 5 * (post.map Prod.snd).prod := by
  have hsatpos : ∀ y ∈ pre ++ [q], 0 < y.1 - 1 := by
    intro y hy
    have hymem : y ∈ sortedPrimePowers n := by
      rw [hlist]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      rcases hy with hy | rfl
      · exact Or.inl hy
      · exact Or.inr (Or.inl rfl)
    have hp := (sortedPrimePowers_properties n y hymem).1
    have := hp.two_le
    omega
  have hpostpos : ∀ y ∈ post, 0 < y.2 := by
    intro y hy
    apply (sortedPrimePowers_properties n y ?_).2.2.1
    rw [hlist]
    simp [hy]
  have hsatbound : ∀ y ∈ pre ++ [q], y.1 - 1 ≤ P := by
    intro y hy
    have hymem : y ∈ sortedPrimePowers n := by
      rw [hlist]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      rcases hy with hy | rfl
      · exact Or.inl hy
      · exact Or.inr (Or.inl rfl)
    have hp := (sortedPrimePowers_mem_iff n y).mp hymem |>.1
    exact le_trans (Nat.sub_le _ _) (hprime y.1 hp)
  have hsatlen : (pre ++ [q]).length ≤ 5 := by
    have hlen := sortedPrimePowers_length n
    rw [hlist] at hlen
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
    omega
  have hbound := list_prod_le_pow ((pre ++ [q]).map fun y => y.1 - 1) P (by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hsatbound y hy)
  simp only [List.length_map] at hbound
  have hexp : P ^ (pre ++ [q]).length ≤ P ^ 5 := Nat.pow_le_pow_right (by omega) hsatlen
  have hsprod : ((pre ++ [q]).map fun y => y.1 - 1).prod ≤ P ^ 5 := le_trans hbound hexp
  have hspos : 0 < ((pre ++ [q]).map fun y => y.1 - 1).prod := by
    apply List.prod_pos
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hsatpos y hy
  have htpos : 0 < (post.map Prod.snd).prod := by
    apply List.prod_pos
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hpostpos y hy
  simp only [List.map_append, List.prod_append] at hspos hsprod
  simp only [capFractions, List.map_append, List.prod_append, List.map_map, Function.comp_def]
  exact ⟨mul_pos hspos htpos, Nat.mul_le_mul_right _ hsprod⟩

theorem sorted_power_growth (n P : ℕ) (hcard : n.primeFactors.card ≤ 5)
    (hP : 1 ≤ P) (hprime : ∀ p ∈ n.primeFactors, p ≤ P)
    (hindex : n.abundancyIndex = ∏ p ∈ n.primeFactors, (p ^ n.factorization p).abundancyIndex)
    (hab : 2 < n.abundancyIndex)
    (hexcess : ∀ q ∈ sortedPrimePowers n, n.abundancyIndex - 2 < 32 / (q.2 : ℚ)) :
    Growth (192 * P ^ 5) ((sortedPrimePowers n).map Prod.snd) := by
  apply growth_of_suffixes
  intro pre q post hlist
  have hqmem : q ∈ sortedPrimePowers n := by rw [hlist]; simp
  have hqpos : 0 < q.2 := (sortedPrimePowers_properties n q hqmem).2.2.1
  have hd := capFractions_denom n P pre q post hlist hcard hP hprime
  have hv := capFractions_value n pre q post hlist
  have ha := capPairs_estimates n pre q post hlist hcard hindex hab
  rw [hv] at ha
  exact rational_gap_implies_growth _ _ q.2 _ P hd.1 hqpos ha.1 n.abundancyIndex ha.2
    (hexcess q hqmem) hd.2

theorem size_bound_from_prime_excess (n : ℕ) (hn : n ≠ 0)
    (hcard : n.primeFactors.card ≤ 5)
    (hprime : ∀ p ∈ n.primeFactors, p ≤ 36550417)
    (hindex : n.abundancyIndex = ∏ p ∈ n.primeFactors, (p ^ n.factorization p).abundancyIndex)
    (hab : 2 < n.abundancyIndex)
    (hexcess : ∀ q ∈ sortedPrimePowers n, n.abundancyIndex - 2 < 32 / (q.2 : ℚ)) :
    n ≤ 10 ^ 540879392320 := by
  have hg := sorted_power_growth n 36550417 hcard (by decide) hprime hindex hab hexcess
  have hl : ((sortedPrimePowers n).map Prod.snd).length ≤ 5 := by
    simpa [sortedPrimePowers_length] using hcard
  have hb := growth_size_bound ((sortedPrimePowers n).map Prod.snd) hg hl
  rw [sortedPrimePowers_prod n hn] at hb
  exact hb


theorem primitive_abundant_size_bound (n : ℕ) (ho : Odd n) (hab : n.Abundant)
    (hcard : n.primeFactors.card ≤ 5)
    (hdef : ∀ d ∈ n.properDivisors, d.Deficient)
    (hprime : ∀ p ∈ n.primeFactors, p ≤ 36550417) :
    n ≤ 10 ^ 540879392320 := by
  have hn : n ≠ 0 := Nat.ne_of_gt hab.pos
  apply size_bound_from_prime_excess n hn hcard hprime (index_factorization n hn)
    (Nat.abundant_iff_two_lt_abundancyIndex.mp hab)
  intro q hq
  have ⟨hp, he⟩ := (sortedPrimePowers_mem_iff n q).mp hq
  have h := primitive_excess_any_factor n q.1 ho hp hcard hdef
  simpa [he] using h


theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R1.H1 := by
  intro m ho ha hc hd
  have hp := prime_bounds_from_core_gap m ho ha hc hd (by
    intro c hco hcd hcc
    exact odd_four_core_gap c (Nat.ne_of_gt hcd.pos) hco hcc
      ((deficient_iff_index_lt_two c (Nat.ne_of_gt hcd.pos)).mp hcd))
  exact ⟨primitive_abundant_size_bound m ho ha hc hd hp, hp⟩
