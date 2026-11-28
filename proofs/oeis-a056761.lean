import OMAStatements.S_oeis_a056761

namespace OMA.A056761

open Finset OMA.S_oeis_a056761

def allowedPrimes : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}

def exponentCap (p : ℕ) : ℕ :=
  if p = 3 then 5 else if p = 5 then 3 else if p = 7 ∨ p = 11 then 2 else 1

private def ratio (p e : ℕ) : ℚ := ((e : ℚ) + 1) ^ 3 / (p : ℚ) ^ e

private def cap (p : ℕ) : ℚ :=
  if p = 3 then 3 else if p = 5 then 8 / 5 else if p = 7 then 8 / 7 else 1

private def multiplier : ℚ := 192 / 35

private lemma cap_pos (p : ℕ) : 0 < cap p := by
  unfold cap
  split_ifs <;> norm_num

private lemma ratio_nonneg (p e : ℕ) : 0 ≤ ratio p e := by
  unfold ratio
  positivity

private lemma ratio_decrease {p e : ℕ} (hp : 0 < p) (a : ℚ)
    (h : (e : ℚ) + 2 ≤ a * ((e : ℚ) + 1)) (ha : a ^ 3 ≤ (p : ℚ)) :
    ratio p (e + 1) ≤ ratio p e := by
  have hp' : 0 < (p : ℚ) := by exact_mod_cast hp
  have he : 0 ≤ (e : ℚ) + 2 := by positivity
  have hpow : ((e : ℚ) + 2) ^ 3 ≤ (p : ℚ) * ((e : ℚ) + 1) ^ 3 := calc
    _ ≤ (a * ((e : ℚ) + 1)) ^ 3 := pow_le_pow_left₀ he h _
    _ = a ^ 3 * ((e : ℚ) + 1) ^ 3 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right ha (by positivity)
  have hden : 0 < (p : ℚ) ^ e := pow_pos hp' _
  unfold ratio
  push_cast
  rw [show (p : ℚ) ^ (e + 1) = (p : ℚ) ^ e * p from pow_succ _ _]
  apply (div_le_div_iff₀ (mul_pos hden hp') hden).mpr
  rw [add_assoc]
  norm_num
  calc
    ((e : ℚ) + 2) ^ 3 * (p : ℚ) ^ e
        ≤ ((p : ℚ) * ((e : ℚ) + 1) ^ 3) * (p : ℚ) ^ e :=
      mul_le_mul_of_nonneg_right hpow hden.le
    _ = _ := by ring

private lemma ratio_decrease_three {e : ℕ} (he : 2 ≤ e) :
    ratio 3 (e + 1) ≤ ratio 3 e := by
  have he' : (2 : ℚ) ≤ e := by exact_mod_cast he
  exact ratio_decrease (by decide) (4 / 3) (by linarith) (by norm_num)

private lemma ratio_decrease_five {p e : ℕ} (hp : 5 ≤ p) (he : 1 ≤ e) :
    ratio p (e + 1) ≤ ratio p e := by
  have hp' : (5 : ℚ) ≤ p := by exact_mod_cast hp
  have he' : (1 : ℚ) ≤ e := by exact_mod_cast he
  exact ratio_decrease (by omega) (3 / 2) (by linarith) (by linarith)

private lemma ratio_decrease_eight {p : ℕ} (hp : 8 ≤ p) (e : ℕ) :
    ratio p (e + 1) ≤ ratio p e := by
  have hp' : (8 : ℚ) ≤ p := by exact_mod_cast hp
  have he' : (0 : ℚ) ≤ e := by positivity
  exact ratio_decrease (by omega) 2 (by linarith) (by linarith)

private lemma ratio_from {p a b : ℕ} (hab : a ≤ b)
    (step : ∀ k, a ≤ k → ratio p (k+1) ≤ ratio p k) :
    ratio p b ≤ ratio p a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => simp
  | succ d ih => exact (step (a+d) (by omega)).trans (ih (by omega))

private lemma ratio_le_cap {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) (e : ℕ) :
    ratio p e ≤ cap p := by
  by_cases hlarge : 8 ≤ p
  · have he := ratio_from (Nat.zero_le e) (fun k _ => ratio_decrease_eight hlarge k)
    have hcap : cap p = 1 := by unfold cap; split_ifs <;> first | rfl | omega
    simpa [hcap, show ratio p 0 = 1 by simp [ratio]] using he
  · have hp2 := hp.two_le
    interval_cases p
    · contradiction
    · by_cases he : 2 ≤ e
      · exact (ratio_from he (fun _ hk => ratio_decrease_three hk)).trans (by norm_num [ratio, cap])
      · interval_cases e <;> norm_num [ratio, cap]
    · have : ¬Nat.Prime 4 := by decide
      contradiction
    · by_cases he : 1 ≤ e
      · exact (ratio_from he (fun _ hk => ratio_decrease_five (by decide : 5 ≤ 5) hk)).trans
          (by norm_num [ratio, cap])
      · interval_cases e
        norm_num [ratio, cap]
    · have : ¬Nat.Prime 6 := by decide
      contradiction
    · by_cases he : 1 ≤ e
      · exact (ratio_from he (fun _ hk => ratio_decrease_five (by decide : 5 ≤ 7) hk)).trans
          (by norm_num [ratio, cap])
      · interval_cases e
        norm_num [ratio, cap]

private lemma ratio_of_excludes_small_primes {n : ℕ} (h : IsA056761 n) :
    ∀ p ∈ n.primeFactors, p.Prime ∧ p ≠ 2 := by
  intro p hp
  obtain ⟨hpr, hd, _⟩ := Nat.mem_primeFactors.mp hp
  exact ⟨hpr, fun he => h.1.not_two_dvd_nat (he ▸ hd)⟩

private lemma factorization_zero_of_not_mem {n p : ℕ} (hp : p ∉ n.primeFactors) :
    n.factorization p = 0 := by
  rw [← Nat.support_factorization] at hp
  exact Finsupp.notMem_support_iff.mp hp

private lemma ratio_product {n : ℕ} (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, ratio p (n.factorization p)) =
      (n.divisors.card : ℚ) ^ 3 / (n : ℚ) := by
  calc
    _ = (∏ p ∈ n.primeFactors, ((n.factorization p : ℚ) + 1)) ^ 3 /
        ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
      simp only [ratio, Finset.prod_div_distrib, Finset.prod_pow]
    _ = _ := by
      have hNum : (∏ p ∈ n.primeFactors, ((n.factorization p : ℚ) + 1)) =
          (n.divisors.card : ℚ) := by exact_mod_cast (Nat.card_divisors hn).symm
      have hDen : (∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p) = (n : ℚ) := by
        exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
      rw [hNum, hDen]

private lemma partial_ratio {n : ℕ} (hgood : IsA056761 n) :
    ∀ p ∈ n.primeFactors, 1 < multiplier * (ratio p (n.factorization p) / cap p) := by
  let small : Finset ℕ := {3, 5, 7}
  let S := n.primeFactors ∪ small
  let normalized (p : ℕ) := ratio p (n.factorization p) / cap p
  have hs : small ⊆ S := Finset.subset_union_right
  have hFactors : n.primeFactors ⊆ S := Finset.subset_union_left
  have hPrime (p : ℕ) (hp : p ∈ S) : p.Prime ∧ p ≠ 2 := by
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ratio_of_excludes_small_primes hgood p hp
    · simp only [small, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> decide
  have hn : n ≠ 0 := by
    intro he
    exact hgood.1.not_two_dvd_nat (he.symm ▸ dvd_zero 2)
  have hP : 1 < ∏ p ∈ S, ratio p (n.factorization p) := by
    have he : (∏ p ∈ n.primeFactors, ratio p (n.factorization p)) =
        ∏ p ∈ S, ratio p (n.factorization p) := Finset.prod_subset hFactors (fun p _ hp => by
          rw [factorization_zero_of_not_mem hp]
          simp [ratio])
    rw [← he, ratio_product hn]
    exact (lt_div_iff₀ (by positivity : 0 < (n : ℚ))).mpr (by
      simpa using (show (n : ℚ) < (n.divisors.card : ℚ)^3 by exact_mod_cast hgood.2))
  have hCap : (∏ p ∈ S, cap p) = multiplier := by
    rw [← Finset.prod_subset hs (fun p _ hp => by
      simp only [small, Finset.mem_insert, Finset.mem_singleton, not_or] at hp
      simp [cap, hp.1, hp.2.1, hp.2.2])]
    unfold small
    norm_num [cap, multiplier, Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton]
  have hNorm : (∏ p ∈ S, ratio p (n.factorization p)) =
      multiplier * (∏ p ∈ S, normalized p) := by
    rw [← hCap, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    dsimp [normalized]
    have hcap := (cap_pos p).ne'
    field_simp
  have hNonneg (p : ℕ) : 0 ≤ normalized p := div_nonneg (ratio_nonneg _ _) (cap_pos _).le
  have hLeOne (p : ℕ) (hp : p ∈ S) : normalized p ≤ 1 :=
    (div_le_iff₀ (cap_pos p)).mpr (by
      simpa using ratio_le_cap (hPrime p hp).1 (hPrime p hp).2 (n.factorization p))
  intro p hp
  have hpS := hFactors hp
  have hprodp : ∏ q ∈ S, normalized q ≤ normalized p := by
    rw [← Finset.mul_prod_erase S normalized hpS]
    apply mul_le_of_le_one_right (hNonneg p)
    exact Finset.prod_le_one (fun q _ => hNonneg q)
      (fun q hq => hLeOne q (Finset.mem_of_mem_erase hq))
  rw [hNorm] at hP
  exact hP.trans_le (mul_le_mul_of_nonneg_left hprodp (by norm_num [multiplier]))


private lemma ratio_anti_prime {p q e : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    ratio q e ≤ ratio p e := by
  have hp' : 0 < (p : ℚ) := by exact_mod_cast hp
  have hqp' : (p : ℚ) ≤ q := by exact_mod_cast hpq
  unfold ratio
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos hp' e)
    (pow_le_pow_left₀ hp'.le hqp' e)

private lemma no_large_prime {n p : ℕ} (h : IsA056761 n) (hp : p ∈ n.primeFactors) :
    p < 44 := by
  by_contra! hlarge
  have he : 1 ≤ n.factorization p := by
    rw [← Nat.support_factorization] at hp
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  have hcap : cap p = 1 := by unfold cap; split_ifs <;> first | rfl | omega
  have hr := ratio_from he (fun k _ => ratio_decrease_eight (by omega : 8 ≤ p) k)
  have h44 : ratio p (n.factorization p) ≤ ratio 44 1 :=
    hr.trans (ratio_anti_prime (by decide) hlarge)
  have hbound : multiplier * (ratio p (n.factorization p) / cap p) ≤ 1 := by
    rw [hcap, div_one]
    calc
      _ ≤ multiplier * ratio 44 1 := mul_le_mul_of_nonneg_left h44 (by norm_num [multiplier])
      _ ≤ _ := by norm_num [multiplier, ratio]
  exact (not_lt_of_ge hbound) (partial_ratio h p hp)

private lemma small_prime_table : ∀ p : Fin 44,
    3 ≤ p.val → p.val.Prime → p.val ∈ allowedPrimes := by
  decide +kernel

private lemma cap_from_ratio {n p k : ℕ} (h : IsA056761 n) (hp : p ∈ n.primeFactors)
    (hstep : ∀ e, k+1 ≤ e → ratio p (e+1) ≤ ratio p e)
    (hmax : multiplier * (ratio p (k+1) / cap p) ≤ 1) :
    n.factorization p ≤ k := by
  by_contra! hn
  have hle : ratio p (n.factorization p) ≤ ratio p (k+1) := ratio_from (by omega) hstep
  have hcmp := div_le_div_of_nonneg_right hle (cap_pos p).le
  have hm := mul_le_mul_of_nonneg_left hcmp (by norm_num [multiplier] : 0 ≤ multiplier)
  exact (not_lt_of_ge (hm.trans hmax)) (partial_ratio h p hp)

private lemma prime_profile_cap {n : ℕ} (h : IsA056761 n) {p : ℕ}
    (hp : p ∈ n.primeFactors) (ha : p ∈ allowedPrimes) :
    n.factorization p ≤ exponentCap p := by
  by_cases h3 : p = 3
  · subst p
    change n.factorization 3 ≤ 5
    exact cap_from_ratio h hp (fun e he => ratio_decrease_three (by omega))
      (by norm_num [multiplier, ratio, cap])
  by_cases h5 : p = 5
  · subst p
    change n.factorization 5 ≤ 3
    exact cap_from_ratio h hp (fun e he => ratio_decrease_five (by decide) (by omega))
      (by norm_num [multiplier, ratio, cap])
  by_cases h7 : p = 7
  · subst p
    change n.factorization 7 ≤ 2
    exact cap_from_ratio h hp (fun e he => ratio_decrease_five (by decide) (by omega))
      (by norm_num [multiplier, ratio, cap])
  by_cases h11 : p = 11
  · subst p
    change n.factorization 11 ≤ 2
    exact cap_from_ratio h hp (fun e _ => ratio_decrease_eight (by decide) e)
      (by norm_num [multiplier, ratio, cap])
  have h13 : 13 ≤ p := by
    simp only [allowedPrimes, Finset.mem_insert, Finset.mem_singleton] at ha
    omega
  simp only [exponentCap, if_neg h3, if_neg h5, if_neg (not_or.mpr ⟨h7, h11⟩)]
  apply cap_from_ratio h hp (fun e _ => ratio_decrease_eight (by omega) e)
  have hc : cap p = 1 := by simp [cap, h3, h5, h7]
  rw [hc, div_one]
  calc
    _ ≤ multiplier * ratio 13 2 :=
      mul_le_mul_of_nonneg_left (ratio_anti_prime (by decide) h13) (by norm_num [multiplier])
    _ ≤ 1 := by norm_num [multiplier, ratio]

theorem profile_bounds {n : ℕ} (h : IsA056761 n) :
    n.primeFactors ⊆ allowedPrimes ∧ ∀ p ∈ allowedPrimes, n.factorization p ≤ exponentCap p := by
  constructor
  · intro p hp
    obtain ⟨hpr, htwo⟩ := ratio_of_excludes_small_primes h p hp
    have h3 : 3 ≤ p := by have := hpr.two_le; omega
    exact small_prime_table ⟨p, no_large_prime h hp⟩ h3 hpr
  · intro p hp
    by_cases hdiv : p ∈ n.primeFactors
    · exact prime_profile_cap h hdiv hp
    · rw [factorization_zero_of_not_mem hdiv]
      exact Nat.zero_le _

end OMA.A056761

/-! Enumerating bounded odd-prime profiles with the divisor count carried through the product. -/

namespace OMA.A056761

open Finset

def primeCaps : List (ℕ × ℕ) :=
  [(3,5),(5,3),(7,2),(11,2),(13,1),(17,1),(19,1),(23,1),(29,1),(31,1),(37,1),(41,1),(43,1)]

def entries : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(1,1)]
  | (p,c) :: ps => (List.range (c + 1)).flatMap fun e =>
      (entries ps).map fun q => (p ^ e * q.1, (e + 1) * q.2)

def accepted : Finset ℕ :=
  (((entries primeCaps).filter fun q => q.1 < q.2 ^ 3).map Prod.fst).toFinset

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem accepted_card : accepted.card = 267 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem accepted_max : accepted.max = (883575 : ℕ) := by
  decide +kernel

end OMA.A056761

/-! Soundness and completeness of the finite divisor-count enumeration. -/

namespace OMA.A056761

open Finset

private theorem entries_sound {ps : List (ℕ × ℕ)}
    (hPrime : ∀ q ∈ ps, q.1.Prime ∧ Odd q.1) (hDistinct : (ps.map Prod.fst).Nodup)
    {n d : ℕ} (hm : (n,d) ∈ entries ps) :
    n ≠ 0 ∧ Odd n ∧ d = n.divisors.card ∧ n.primeFactors ⊆ (ps.map Prod.fst).toFinset := by
  induction ps generalizing n d with
  | nil =>
    simp only [entries, List.mem_singleton, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩
    simp
  | cons q ps ih =>
    rcases q with ⟨p, c⟩
    obtain ⟨hp, hpOdd⟩ := hPrime (p,c) (by simp)
    have hTail (q : ℕ × ℕ) (hq : q ∈ ps) := hPrime q (List.mem_cons_of_mem _ hq)
    obtain ⟨hpOut, hNodup⟩ := List.nodup_cons.mp hDistinct
    simp only [entries, List.mem_flatMap, List.mem_map] at hm
    obtain ⟨e, _, ⟨a,b⟩, hab, he⟩ := hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    obtain ⟨ha, haOdd, hb, hSupport⟩ := ih hTail hNodup hab
    have hpPow : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hPowSupport : (p ^ e).primeFactors ⊆ {p} := by
      by_cases he : e = 0
      · simp [he]
      · rw [Nat.primeFactors_prime_pow he hp]
    have hCoprime : (p ^ e).Coprime a := by
      apply (Nat.disjoint_primeFactors hpPow ha).mp
      apply Finset.disjoint_left.mpr
      intro r hr hra
      have hrp : r = p := Finset.mem_singleton.mp (hPowSupport hr)
      exact hpOut (List.mem_toFinset.mp (hrp ▸ hSupport hra))
    have hPowCount : (p ^ e).divisors.card = e + 1 := by
      rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
    refine ⟨mul_ne_zero hpPow ha, (hpOdd.pow).mul haOdd, ?_, ?_⟩
    · rw [hCoprime.card_divisors_mul, hPowCount, hb]
    · rw [Nat.primeFactors_mul hpPow ha, List.map_cons, List.toFinset_cons]
      apply Finset.union_subset
      · exact hPowSupport.trans (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
      · exact hSupport.trans (Finset.subset_insert _ _)

private theorem prod_pair_mem (f : ℕ → ℕ) {ps : List (ℕ × ℕ)}
    (hBound : ∀ q ∈ ps, f q.1 ≤ q.2) (hDistinct : (ps.map Prod.fst).Nodup) :
    ((∏ p ∈ (ps.map Prod.fst).toFinset, p ^ f p),
      ∏ p ∈ (ps.map Prod.fst).toFinset, (f p + 1)) ∈ entries ps := by
  induction ps with
  | nil => simp [entries]
  | cons q ps ih =>
    rcases q with ⟨p, c⟩
    obtain ⟨hpOut, hNodup⟩ := List.nodup_cons.mp hDistinct
    have hpNot : p ∉ (ps.map Prod.fst).toFinset := fun hp => hpOut (List.mem_toFinset.mp hp)
    have hTail (q : ℕ × ℕ) (hq : q ∈ ps) := hBound q (List.mem_cons_of_mem _ hq)
    have hpCap : f p ≤ c := hBound (p,c) (by simp)
    simp only [List.map_cons, List.toFinset_cons, Finset.prod_insert hpNot,
      entries, List.mem_flatMap, List.mem_map]
    refine ⟨f p, List.mem_range.mpr (by omega), _, ih hTail hNodup, rfl⟩

private theorem table_Prime_and_odd (q : ℕ × ℕ) (hq : q ∈ primeCaps) :
    q.1.Prime ∧ Odd q.1 := by
  have h : primeCaps.all (fun r => decide (r.1.Prime ∧ Odd r.1)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h q hq)

private theorem table_nodup : (primeCaps.map Prod.fst).Nodup := by decide +kernel

private theorem mem_accepted {n : ℕ} :
    n ∈ accepted ↔ ∃ d : ℕ, (n,d) ∈ entries primeCaps ∧ n < d ^ 3 := by
  simp only [accepted, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨_, d⟩, he, rfl⟩
    exact ⟨d, he⟩
  · rintro ⟨d, hm, hlt⟩
    exact ⟨(n,d), ⟨hm, hlt⟩, rfl⟩

theorem accepted_sound {n : ℕ} (hn : n ∈ accepted) :
    OMA.S_oeis_a056761.IsA056761 n := by
  obtain ⟨d, hd, hlt⟩ := mem_accepted.mp hn
  obtain ⟨_, hOdd, rfl, _⟩ := entries_sound table_Prime_and_odd table_nodup hd
  exact ⟨hOdd, hlt⟩

theorem accepted_complete {n : ℕ} (h : OMA.S_oeis_a056761.IsA056761 n)
    (hSup : n.primeFactors ⊆ (primeCaps.map Prod.fst).toFinset)
    (hBound : ∀ q ∈ primeCaps, n.factorization q.1 ≤ q.2) :
    n ∈ accepted := by
  have hn : n ≠ 0 := by
    intro he
    subst n
    simp [OMA.S_oeis_a056761.IsA056761] at h
  have hz (p : ℕ) (hp : p ∉ n.primeFactors) : n.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp hp
  have hpVal : (∏ p ∈ (primeCaps.map Prod.fst).toFinset, p ^ n.factorization p) = n :=
    (Finset.prod_subset hSup (fun p _ hp => by simp [hz p hp])).symm.trans
      (Nat.prod_primeFactors_pow_factorization hn).symm
  have hpCount : (∏ p ∈ (primeCaps.map Prod.fst).toFinset, (n.factorization p + 1)) =
      n.divisors.card :=
    (Finset.prod_subset hSup (fun p _ hp => by simp [hz p hp])).symm.trans
      (Nat.card_divisors hn).symm
  have hmem := prod_pair_mem n.factorization hBound table_nodup
  rw [hpVal, hpCount] at hmem
  exact mem_accepted.mpr ⟨n.divisors.card, hmem, h.2⟩

theorem solve_of_profiles
    (hProfiles : ∀ n : ℕ, OMA.S_oeis_a056761.IsA056761 n →
      n.primeFactors ⊆ (primeCaps.map Prod.fst).toFinset ∧
      ∀ q ∈ primeCaps, n.factorization q.1 ≤ q.2) :
    type_of% @OMA.S_oeis_a056761.main := by
  have hIff (n : ℕ) : n ∈ accepted ↔ OMA.S_oeis_a056761.IsA056761 n :=
    ⟨accepted_sound, fun h => accepted_complete h (hProfiles n h).1 (hProfiles n h).2⟩
  refine ⟨accepted_sound (Finset.mem_of_max accepted_max), ?_, ?_⟩
  · intro n hn
    exact Finset.le_max_of_eq ((hIff n).mpr hn) accepted_max
  · have he : {n : ℕ | OMA.S_oeis_a056761.IsA056761 n} = (accepted : Set ℕ) := by
      ext n
      exact (hIff n).symm
    rw [he, Set.ncard_coe_finset, accepted_card]

end OMA.A056761

open OMA.A056761 in
theorem OMA.solution : type_of% @OMA.S_oeis_a056761.main := by
  apply solve_of_profiles
  intro n h
  obtain ⟨hPrimes, hExponents⟩ := profile_bounds h
  have hTable : (primeCaps.map Prod.fst).toFinset = allowedPrimes := by decide +kernel
  have hCap : primeCaps.all (fun q => decide (exponentCap q.1 = q.2)) = true := by
    decide +kernel
  refine ⟨hTable.symm ▸ hPrimes, ?_⟩
  intro q hq
  have hqp : q.1 ∈ allowedPrimes := by
    rw [← hTable]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨q, hq, rfl⟩)
  exact (hExponents q.1 hqp).trans_eq (of_decide_eq_true (List.all_eq_true.mp hCap q hq))
