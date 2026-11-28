import FormalConjectures.Wikipedia.DescartesNumber
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.MaxPowDiv

/-!
A kernel-checked version of the Descartes factorization bound of
[László Tóth](https://cmst.eu/articles/on-the-density-of-spoof-odd-perfect-numbers/).

An odd spoof prime makes the divisor sum odd, so the other factor is a square.
A geometric-series bound for the divisor sum restricts the square root to
multiples of a short list of products of small primes. The remaining cases use
exact divisor sums from prime-power factorization.
-/

open Finset
open scoped ArithmeticFunction.sigma

namespace OMA.DescartesSearch

private def trialProduct : ℕ := 19590340644999083431262508198206381046123972390589368223882605328968666316379870661851951648789482321596229559115436019149189529725215266728292282990852649023362731392404017939142010958261393634959471483757196721672243410067118516227661133135192488848989914892157188308679896875137439519338903968094905549750386407106033836586660683539201011635917900039904495065203299749542985993134669814805318474080581207891125910

private def check (ok : ℕ → Bool) (lo n : ℕ) : Bool :=
  if n = 0 then true
  else if n = 1 then ok lo
  else check ok lo (n/2) && check ok (lo+n/2) (n-n/2)
termination_by n
decreasing_by all_goals omega

private theorem check_sound (ok : ℕ → Bool) (lo len : ℕ) (h : check ok lo len = true)
    {i : ℕ} (hlo : lo ≤ i) (hhi : i < lo+len) : ok i = true := by
  rw [check] at h
  split_ifs at h with h0 h1
  · omega
  · have : i = lo := by omega
    simpa [this] using h
  · rw [Bool.and_eq_true] at h
    by_cases hleft : i < lo+len/2
    · exact check_sound ok lo (len/2) h.1 hlo hleft
    · exact check_sound ok (lo+len/2) (len-len/2) h.2 (by omega) (by omega)
termination_by len
decreasing_by all_goals omega

private def passesTrialProduct (p : ℕ) : Bool :=
  (p < 2) || (p.minFac != p) || (trialProduct % p == 0)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem trial_certificate : check passesTrialProduct 0 1001 = true := by decide +kernel

private theorem prime_dvd_trialProduct (p : ℕ) (hp : p.Prime) (hle : p ≤ 1000) :
    p ∣ trialProduct := by
  have hc := check_sound _ 0 1001 trial_certificate (Nat.zero_le p) (by omega)
  have hn : ¬ p < 2 := Nat.not_lt_of_ge hp.two_le
  simpa [passesTrialProduct,hn,hp.minFac_eq, Nat.dvd_iff_mod_eq_zero] using hc

private def candidatePrime (n : ℕ) : ℕ :=
  let g := Nat.gcd n trialProduct
  if g = 1 then n else g.minFac

private theorem candidatePrime_spec {n : ℕ} (hn : 1 < n) (hbound : n ≤ 1000000) :
    (candidatePrime n).Prime ∧ candidatePrime n ∣ n := by
  unfold candidatePrime
  dsimp only
  split_ifs with hg
  · refine ⟨?_, dvd_refl _⟩
    by_contra hnp
    have hndvd := Nat.minFac_dvd n
    have hp := Nat.minFac_prime (show n ≠ 1 by omega)
    have hs := Nat.minFac_sq_le_self (show 0 < n by omega) hnp
    have hle : n.minFac ≤ 1000 := by
      by_contra! hc
      have hsq := Nat.pow_le_pow_left hc 2
      norm_num at hsq
      omega
    have hd := Nat.dvd_gcd hndvd (prime_dvd_trialProduct n.minFac hp hle)
    rw [hg] at hd
    exact hp.not_dvd_one hd
  · exact ⟨Nat.minFac_prime hg, (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)⟩

private def geom (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 1 + p * geom p k

private theorem geom_eq (p k : ℕ) : geom p k = ∑ i ∈ range k,p^i := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
    rw [geom, ih, sum_range_succ', pow_zero, Nat.add_comm 1, mul_sum]
    congr 1
    apply sum_congr rfl
    intro i hi
    rw [pow_succ, mul_comm]

private def fastSigmaSq : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel+1, n =>
    if n ≤ 1 then 1
    else
      let p := candidatePrime n
      let a := p.maxPowDvdDiv n
      geom p (2*a.1+1) * fastSigmaSq fuel a.2

private theorem fastSigmaSq_spec (fuel n : ℕ) (hn : 0 < n)
    (hpow : n ≤ 2^fuel) (hbound : n ≤ 1000000) : fastSigmaSq fuel n = σ 1 (n^2) := by
  induction fuel generalizing n with
  | zero =>
    have h : n = 1 := by simp only [pow_zero] at hpow; omega
    simp [h,fastSigmaSq]
  | succ k ih =>
    by_cases ht : n ≤ 1
    · have h : n = 1 := by omega
      simp [h,fastSigmaSq]
    · have hnt : 1 < n := by omega
      let p := candidatePrime n
      have ⟨hp,hpd⟩ := candidatePrime_spec hnt hbound
      let e := padicValNat p n
      let q := Nat.divMaxPow n p
      have he : 1 ≤ e :=
        (Nat.pow_dvd_iff_le_padicValNat hp.ne_one hn.ne').mp (by simpa using hpd)
      have hq : p^e*q = n := Nat.pow_padicValNat_mul_divMaxPow p n
      have hq0 : 0 < q := by
        apply Nat.pos_of_ne_zero
        intro h
        rw [h,mul_zero] at hq
        omega
      have hqc : ¬ p ∣ q := Nat.not_dvd_divMaxPow hp.one_lt hn.ne'
      have hqle : q ≤ 2^k := by
        have hpe : 2 ≤ p^e := hp.two_le.trans (Nat.le_pow (by omega : 0 < e))
        have hm := Nat.mul_le_mul_right q hpe
        rw [hq] at hm
        rw [pow_succ,Nat.mul_comm] at hpow
        omega
      have hqb : q ≤ 1000000 := (Nat.le_of_dvd hn ⟨p^e,by rw [mul_comm,hq]⟩).trans hbound
      have hc : (p^(2*e)).Coprime (q^2) :=
        ((hp.coprime_iff_not_dvd.mpr hqc).pow_left _).pow_right _
      rw [fastSigmaSq, if_neg ht]
      change geom p (2*e+1) * fastSigmaSq k q = σ 1 (n^2)
      rw [geom_eq, ih q hq0 hqle hqb, ← hq, mul_pow, ← pow_mul, Nat.mul_comm e 2,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc,
        ArithmeticFunction.sigma_one_apply_prime_pow hp]

private def passes (n : ℕ) : Bool :=
  let s := fastSigmaSq 20 n
  let d := 2*n^2-s
  (n == 1) || (n == 3003) || (d == 0) || (s % d != 0)

private theorem sigma_odd_of_factorization {m w : ℕ} (h : DescartesNumber.IsDescartesFactorization m w) :
    Odd (σ 1 m) := by
  obtain ⟨hm,hw⟩ := Nat.odd_mul.mp h.2.1
  have hc : w.Coprime (w+1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hd : w ∣ σ 1 m := hc.dvd_of_dvd_mul_right ⟨2*m,by simpa [mul_comm w] using h.2.2.2⟩
  obtain ⟨k,hk⟩ := hd
  have hw0 : 0 < w := by obtain ⟨v,hv⟩ := hw; omega
  obtain ⟨v,hv⟩ : Even (w+1) := by obtain ⟨v,hv⟩ := hw; exact ⟨v+1,by omega⟩
  have he : w * (k*(v+v)) = w*(2*m) := by
    calc
      _ = σ 1 m * (w+1) := by rw [hk,hv]; ring
      _ = _ := by rw [h.2.2.2]; ring
  have he' := Nat.eq_of_mul_eq_mul_left hw0 he
  have hm' : m = k*v := by
    have hterm : k*(v+v) = 2*(k*v) := by ring
    omega
  rw [hk]
  exact hw.mul ((Nat.odd_mul.mp (hm' ▸ hm)).1)

private theorem exists_odd_square_of_sigma {m : ℕ} (hm : Odd m) (hs : Odd (σ 1 m)) :
    ∃ r : ℕ, Odd r ∧ m = r^2 := by
  have hm0 : m ≠ 0 := by obtain ⟨v,hv⟩ := hm; omega
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0] at hs
  simp only [mul_one] at hs
  have he (p : ℕ) (hp : p ∈ m.primeFactors) : Even (m.factorization p) := by
    let a := m.factorization p
    let F := fun p : ℕ => ∑ i ∈ range (m.factorization p + 1), p^i
    have hF : Odd (F p) := by
      by_contra! hb
      have h2 : 2 ∣ F p := even_iff_two_dvd.mp ((Nat.not_odd_iff_even).mp hb)
      exact (Nat.not_even_iff_odd.mpr hs)
        (even_iff_two_dvd.mpr (h2.trans (Finset.dvd_prod_of_mem F hp)))
    have hodd : Odd p := hm.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have ha : Odd (a+1) := by
      change Odd (∑ i ∈ range (a+1),p^i) at hF
      rw [Finset.odd_sum_iff_odd_card_odd] at hF
      have hall : ∀ i ∈ range (a+1), Odd (p^i) := fun _ _ => hodd.pow
      simpa only [Finset.filter_true_of_mem hall, Finset.card_range] using hF
    obtain ⟨j,hj⟩ := ha
    exact ⟨j,by omega⟩
  refine ⟨∏ p ∈ m.primeFactors,p^(m.factorization p/2), ?_, ?_⟩
  · have hq : (∏ p ∈ m.primeFactors,p^(m.factorization p/2)) ∣ m := by
      conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hm0]
      exact prod_dvd_prod_of_dvd _ _ (fun _ _ => pow_dvd_pow _ (Nat.div_le_self _ _))
    exact hm.of_dvd_nat hq
  · rw [← Finset.prod_pow]
    calc
      m = ∏ p ∈ m.primeFactors,p^m.factorization p := Nat.prod_primeFactors_pow_factorization hm0
      _ = _ := by
        apply prod_congr rfl
        intro p hp
        rw [← pow_mul, show m.factorization p / 2 * 2 = m.factorization p by
          obtain ⟨k,hk⟩ := he p hp
          omega]

private theorem bound_weight {n : ℕ} (hn : 0 < n) :
    σ 1 n * (∏ p ∈ n.primeFactors,(p-1)) ≤ n * (∏ p ∈ n.primeFactors,p) := by
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn.ne',
    ← Finset.prod_mul_distrib]
  conv_rhs =>
    lhs
    rw [Nat.prod_primeFactors_pow_factorization hn.ne']
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hx : p-1+1 = p := by have := hprime.one_lt; omega
  have hsub := geom_sum_mul_add (p-1) (n.factorization p + 1)
  rw [hx] at hsub
  simp only [mul_one,pow_succ _ (n.factorization p)] at hsub ⊢
  omega

private theorem ratio_ge_nine_fifths {m w : ℕ} (h : DescartesNumber.IsDescartesFactorization m w) :
    9*m ≤ 5*σ 1 m := by
  have hwodd := (Nat.odd_mul.mp h.2.1).2
  have hw9 : 9 ≤ w := by
    by_contra! hw
    have hv : ∀ u : Fin 9, ¬ (u.val.Composite ∧ Odd u.val) := by decide
    exact hv ⟨w,hw⟩ ⟨h.1,hwodd⟩
  have he := h.2.2.2
  have hσ : σ 1 m ≤ 2*m := by
    by_contra! hlt
    have hp := Nat.mul_lt_mul_of_pos_right hlt (by omega : 0 < w)
    have hq : σ 1 m * w ≤ σ 1 m * (w+1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hd : (2*m-σ 1 m)*w = σ 1 m := by
    rw [Nat.sub_mul, Nat.mul_succ] at *
    omega
  have hmul := Nat.mul_le_mul_left (2*m-σ 1 m) hw9
  rw [hd] at hmul
  omega

private def smallPrimes : List ℕ := [3,5,7,11,13,17,19,23,29,31]
private def searchBases : List ℕ := [15,21,429,561,663,85085,627,741,95095,759,897,115115,22287,957,871131]

private def admissible (P D k : ℕ) : Bool :=
  !(P * 32^k ≤ 1000000 && 9*D*31^k ≤ 5*P*32^k) || searchBases.any (fun b => P%b==0)

private def checkMasks : List ℕ → ℕ → ℕ → Bool
  | [], P, D => admissible P D 0 && admissible P D 1 && admissible P D 2 && admissible P D 3
  | p::ps, P, D => checkMasks ps P D && checkMasks ps (P*p) (D*(p-1))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem mask_certificate : checkMasks smallPrimes 1 1 = true := by decide +kernel

private theorem mask_sound (ps : List ℕ) (P D : ℕ) (hnd : ps.Nodup)
    (h : checkMasks ps P D = true) (S : Finset ℕ) (hS : S ⊆ ps.toFinset)
    (k : ℕ) (hk : k ≤ 3) : admissible (P * ∏ p ∈ S,p) (D * ∏ p ∈ S,(p-1)) k = true := by
  classical
  induction ps generalizing P D S with
  | nil =>
    have hs : S = ∅ := Finset.subset_empty.mp (by simpa using hS)
    subst S
    simp only [prod_empty,mul_one]
    simp only [checkMasks,Bool.and_eq_true] at h
    obtain rfl | rfl | rfl | rfl : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    · exact h.1.1.1
    · exact h.1.1.2
    · exact h.1.2
    · exact h.2
  | cons p ps ih =>
    have ⟨hp,hps⟩ := List.nodup_cons.mp hnd
    simp only [checkMasks,Bool.and_eq_true] at h
    by_cases hpm : p ∈ S
    · have hsub : S.erase p ⊆ ps.toFinset := by
        intro q hq
        have hqS := hS (Finset.mem_of_mem_erase hq)
        simpa only [List.mem_toFinset, List.mem_cons,
          show q ≠ p from Finset.ne_of_mem_erase hq, false_or] using hqS
      rw [← Finset.insert_erase hpm,prod_insert (Finset.notMem_erase p S),
        prod_insert (Finset.notMem_erase p S),← mul_assoc,← mul_assoc]
      exact ih (P*p) (D*(p-1)) hps h.2 (S.erase p) hsub
    · have hsub : S ⊆ ps.toFinset := by
        intro q hq
        have hqS := hS hq
        have hqp : q ≠ p := fun hc => hpm (hc ▸ hq)
        simpa only [List.mem_toFinset,List.mem_cons,hqp,false_or] using hqS
      exact ih P D hps h.1 S hsub

private theorem prune {r : ℕ} (hr : Odd r) (hle : r ≤ 1000000)
    (hs : 9*r^2 ≤ 5*σ 1 (r^2)) : ∃ b ∈ searchBases, b ∣ r := by
  classical
  let S := r.primeFactors.filter (fun p => p≤31)
  let T := r.primeFactors.filter (fun p => ¬ p≤31)
  have hS : S ⊆ smallPrimes.toFinset := by
    intro p hp
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
    have hp2 : 2 < p := by
      have he := hr.of_dvd_nat (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)
      have := hpr.two_le
      rw [Nat.odd_iff] at he
      omega
    have hup := (mem_filter.mp hp).2
    have hi : ∀ p : Fin 32, 2 < p.val → p.val.Prime → p.val ∈ smallPrimes.toFinset := by decide +kernel
    exact hi ⟨p,by omega⟩ hp2 hpr
  have hr0 : 0 < r := by obtain ⟨v,hv⟩ := hr; omega
  have he := bound_weight (show 0 < r^2 by positivity)
  rw [Nat.primeFactors_pow _ (by decide : 2 ≠ 0)] at he
  have hrad : (∏ p ∈ r.primeFactors,p) ∣ r := Nat.prod_primeFactors_dvd _
  have hD : 9*(∏ p ∈ r.primeFactors,(p-1)) ≤ 5*(∏ p ∈ r.primeFactors,p) := by
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < r^2 by positivity)
    calc
      _ = (9*r^2)*(∏ p ∈ r.primeFactors,(p-1)) := by ring
      _ ≤ (5*σ 1 (r^2))*(∏ p ∈ r.primeFactors,(p-1)) := Nat.mul_le_mul_right _ hs
      _ = 5*(σ 1 (r^2) * (∏ p ∈ r.primeFactors,(p-1))) := by ring
      _ ≤ 5*(r^2*(∏ p ∈ r.primeFactors,p)) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  have hsplit (f : ℕ → ℕ) : (∏ p ∈ S,f p) * (∏ p ∈ T,f p) = ∏ p ∈ r.primeFactors,f p :=
    prod_filter_mul_prod_filter_not _ _ _
  rw [← hsplit (fun p => p),← hsplit (fun p => (p-1))] at hD
  rw [← hsplit (fun p => p)] at hrad
  have hPbound : (∏ p ∈ S,p)*32^T.card ≤ 1000000 := by
    refine (Nat.mul_le_mul_left _
      (show 32^T.card ≤ ∏ p ∈ T,p from ?_)).trans ((Nat.le_of_dvd hr0 hrad).trans hle)
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod' fun p hp => by have := (mem_filter.mp hp).2; omega
  have hP0 : 0 < ∏ p ∈ S,p := by
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos
  have hk : T.card ≤ 3 := by
    by_contra! hc
    have hq : 32^4 ≤ 32^T.card := Nat.pow_le_pow_right (by decide) (by omega)
    have : 32^T.card ≤ (∏ p ∈ S,p)*32^T.card :=
      by simpa using Nat.mul_le_mul_right (32^T.card) hP0
    have := hq.trans (this.trans hPbound)
    norm_num at this
  have hq : (∏ p ∈ T,p) * 31^T.card ≤ (∏ p ∈ T,(p-1))*32^T.card := by
    rw [← Finset.prod_const,← Finset.prod_const,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro p hp
    have := (mem_filter.mp hp).2
    omega
  have hT0 : 0 < ∏ p ∈ T,(p-1) := by
    apply Finset.prod_pos
    intro p hp
    have := (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le
    omega
  have hineq : 9*(∏ p ∈ S,(p-1))*31^T.card ≤ 5*(∏ p ∈ S,p)*32^T.card := by
    refine Nat.le_of_mul_le_mul_right ?_ hT0
    calc
      _ = (9*((∏ p ∈ S,(p-1))*(∏ p ∈ T,(p-1))))*31^T.card := by ring
      _ ≤ (5*((∏ p ∈ S,p)*(∏ p ∈ T,p)))*31^T.card := Nat.mul_le_mul_right _ hD
      _ = (5*(∏ p ∈ S,p))*((∏ p ∈ T,p)*31^T.card) := by ring
      _ ≤ (5*(∏ p ∈ S,p))*((∏ p ∈ T,(p-1))*32^T.card) := Nat.mul_le_mul_left _ hq
      _ = _ := by ring
  have hcert := mask_sound smallPrimes 1 1 (by decide) mask_certificate S hS T.card hk
  simp only [one_mul,admissible,decide_eq_true hPbound,decide_eq_true hineq,
    Bool.true_and,Bool.not_true,Bool.false_or,List.any_eq_true,
    beq_iff_eq,← Nat.dvd_iff_mod_eq_zero] at hcert
  obtain ⟨b,hb,hbd⟩ := hcert
  exact ⟨b,hb,hbd.trans ((dvd_mul_right _ _).trans hrad)⟩

private theorem deficit_mul {m w : ℕ} (h : DescartesNumber.IsDescartesFactorization m w) :
    (2*m-σ 1 m)*w = σ 1 m := by
  have he := h.2.2.2
  have hw : 0 < w := h.1.1.trans' (by decide)
  have hσ : σ 1 m ≤ 2*m := by
    by_contra! hlt
    have hp := Nat.mul_lt_mul_of_pos_right hlt hw
    have hq : σ 1 m * w ≤ σ 1 m * (w+1) := Nat.mul_le_mul_left _ (by omega)
    omega
  rw [Nat.sub_mul]
  rw [Nat.mul_succ] at he
  omega

theorem lower_of_checked
    (progressions : ∀ b ∈ searchBases, ∀ i : ℕ, b*(2*i+1) ≤ 1000000 → passes (b*(2*i+1)) = true)
    (m w : ℕ) (h : DescartesNumber.IsDescartesFactorization m w)
    (hne : m * w ≠ DescartesNumber.descartesExample) : 10^12 < m := by
  by_contra! hbound
  have hm := (Nat.odd_mul.mp h.2.1).1
  obtain ⟨r,hr,rfl⟩ := exists_odd_square_of_sigma hm (sigma_odd_of_factorization h)
  have hrb : r ≤ 1000000 := by
    by_contra! hnot
    have hp : 1000001^2 ≤ r^2 := Nat.pow_le_pow_left hnot 2
    norm_num at hp hbound
    omega
  have hr0 : 0 < r := by obtain ⟨i,hi⟩ := hr; omega
  obtain ⟨b,hb,t,hrt⟩ := prune hr hrb (ratio_ge_nine_fifths h)
  obtain ⟨i,hi⟩ := (Nat.odd_mul.mp (show Odd (b*t) from hrt ▸ hr)).2
  have hre : r = b*(2*i+1) := by rw [hrt,hi]
  have hcheck : passes r = true := by
    rw [hre]
    exact progressions b hb i (hre ▸ hrb)
  have hσ := fastSigmaSq_spec 20 r hr0 (by exact hrb.trans (by decide)) hrb
  have hd := deficit_mul h
  have hpos := ArithmeticFunction.sigma_pos 1 (r^2) (pow_ne_zero 2 hr0.ne')
  have hd0 : 2*r^2-σ 1 (r^2) ≠ 0 := by
    intro he
    rw [he,zero_mul] at hd
    omega
  have hmod : σ 1 (r^2) % (2*r^2-σ 1 (r^2)) = 0 :=
    Nat.mod_eq_zero_of_dvd ⟨w,hd.symm⟩
  have hroots : r = 1 ∨ r = 3003 := by
    simpa [passes,hσ,hd0,hmod] using hcheck
  rcases hroots with rfl | rfl
  · have hw1 : w = 1 := by simpa using hd
    exact (Nat.ne_of_gt h.1.1) hw1
  · have hs : σ 1 (3003^2) = 18035199 := by
      rw [← fastSigmaSq_spec 20 3003 (by decide) (by decide) (by decide)]
      decide +kernel
    rw [hs] at hd
    norm_num at hd
    have hw : w = 22021 := by omega
    apply hne
    rw [hw]
    decide

private def ok (c : ℕ × ℕ) : Bool :=
  check (fun i => decide (1000000 < c.1*(2*i+1)) || passes (c.1*(2*i+1))) (2048*c.2) 2048

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t0 : ok (15,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t1 : ok (15,1) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t2 : ok (15,2) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t3 : ok (15,3) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t4 : ok (15,4) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t5 : ok (15,5) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t6 : ok (15,6) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t7 : ok (15,7) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t8 : ok (15,8) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t9 : ok (15,9) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t10 : ok (15,10) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t11 : ok (15,11) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t12 : ok (15,12) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t13 : ok (15,13) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t14 : ok (15,14) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t15 : ok (15,15) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t16 : ok (15,16) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t17 : ok (21,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t18 : ok (21,1) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t19 : ok (21,2) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t20 : ok (21,3) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t21 : ok (21,4) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t22 : ok (21,5) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t23 : ok (21,6) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t24 : ok (21,7) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t25 : ok (21,8) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t26 : ok (21,9) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t27 : ok (21,10) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t28 : ok (21,11) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t29 : ok (429,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t30 : ok (561,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t31 : ok (663,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t32 : ok (85085,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t33 : ok (627,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t34 : ok (741,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t35 : ok (95095,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t36 : ok (759,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t37 : ok (897,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t38 : ok (115115,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t39 : ok (22287,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t40 : ok (957,0) = true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem t41 : ok (871131,0) = true := by decide +kernel

private def C : List (ℕ × ℕ) := [(15,0),(15,1),(15,2),(15,3),(15,4),(15,5),(15,6),(15,7),(15,8),(15,9),(15,10),(15,11),(15,12),(15,13),(15,14),(15,15),(15,16),(21,0),(21,1),(21,2),(21,3),(21,4),(21,5),(21,6),(21,7),(21,8),(21,9),(21,10),(21,11),(429,0),(561,0),(663,0),(85085,0),(627,0),(741,0),(95095,0),(759,0),(897,0),(115115,0),(22287,0),(957,0),(871131,0)]

private theorem allC : ∀ c ∈ C, ok c = true := by
  simp only [C, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28,t29,t30,t31,t32,t33,t34,t35,t36,t37,t38,t39,t40,t41⟩

private theorem inC : ∀ b ∈ searchBases, 0 < b ∧ ∀ k ≤ 1000000/b/4096, (b,k) ∈ C := by decide +kernel

private theorem progression_check (b : ℕ) (hb : b ∈ searchBases) (i : ℕ)
    (hi : b*(2*i+1) ≤ 1000000) : passes (b*(2*i+1)) = true := by
  obtain ⟨h0, h⟩ := inC b hb
  have := (Nat.le_div_iff_mul_le h0).2 (Nat.mul_comm b _ ▸ hi)
  have hc := check_sound _ _ _ (allC _ (h (i/2048) (by omega))) (i := i) (by omega) (by omega)
  simpa [not_lt.mpr hi] using hc

end OMA.DescartesSearch

theorem OMA.solution : type_of% @DescartesNumber.descartes_non_example_factor_gt_ten_pow_twelve :=
  OMA.DescartesSearch.lower_of_checked OMA.DescartesSearch.progression_check