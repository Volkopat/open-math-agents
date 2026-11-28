import OMAReductions.R_Erdos387_erdos_387_R1
import Mathlib

/-!
# Proof of `Erdos387.erdos_387.R1.H1`

Constructs arbitrarily large `k` with a congruence class `n ≡ a [MOD M]` and a factorization
`∏ i : Fin k, g i = k!` with every `g i ≥ B`, `g i ∣ n - i`, and no prime `p ≤ k` dividing
`n.choose k`, via Kummer's theorem, Chinese Remainder Theorem, a 2-dimensional Selberg sieve,
Rankin's smooth-number bound, and a weighted restricted prime covering.
-/


/-
# Reduction of `Erdos387.erdos_387.R1.H1` to weighted restricted prime coverings

Given a weight-`B` restricted prime cover `(R, a)` for `k ≥ 3`, uses Kummer's theorem
(`Nat.factorization_choose`) and `Nat.chineseRemainderOfFinset` to construct the
progression modulus `M`, residue `α`, and factorization `g : Fin k → ℕ` satisfying
`OMA.R_Erdos387_erdos_387_R1.H1`.
-/

namespace OMA.Erdos387S1

open Finset Nat
open scoped BigOperators

/-- A weight-`B` restricted prime cover for `k`: a set `R` of primes `≤ k` with residue
    classes `a p ∈ (k % p, p)` such that every `j ∈ {1, ..., k}` has product of its
    `R`-free part and all covering primes `p ∈ R` (`j ≡ a p [MOD p]`) at least `B`. -/
def HasCoverB (B k : ℕ) : Prop :=
  3 ≤ k ∧ ∃ (R : Finset ℕ) (a : ℕ → ℕ),
    (∀ p ∈ R, p.Prime ∧ p ≤ k ∧ k % p < a p ∧ a p < p) ∧
    (∀ j, 1 ≤ j → j ≤ k →
      B ≤ (∏ p ∈ ((range (k + 1)).filter Nat.Prime) \ R, p ^ (j.factorization p)) *
          (∏ p ∈ R.filter (fun p => j ≡ a p [MOD p]), p))

lemma prod_dvd_of_pairwise_coprime {ι : Type*} (s : Finset ι) (f : ι → ℕ) (m : ℕ)
    (hcop : (s : Set ι).Pairwise (fun x y => Nat.Coprime (f x) (f y)))
    (hdvd : ∀ x ∈ s, f x ∣ m) : (∏ x ∈ s, f x) ∣ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha]
    have hcop_s : (s : Set ι).Pairwise (fun x y => Nat.Coprime (f x) (f y)) :=
      hcop.mono (by simp)
    have h1 : f a ∣ m := hdvd a (mem_insert_self a s)
    have h2 : (∏ x ∈ s, f x) ∣ m := ih hcop_s (fun x hx => hdvd x (mem_insert_of_mem hx))
    have hca : Nat.Coprime (f a) (∏ x ∈ s, f x) :=
      Nat.coprime_prod_right_iff.mpr fun x hx =>
        hcop (mem_insert_self a s) (mem_insert_of_mem hx) (fun h => ha (h ▸ hx))
    exact hca.mul_dvd_of_dvd_of_dvd h1 h2

/-- If `k % p ≤ a < p`, then `r = (k / p) * p + a` has `v_p (r.choose k) = 0`. -/
lemma choose_factorization_eq_zero_of_digit {k p a : ℕ} (hp : p.Prime)
    (hka : k % p ≤ a) (hap : a < p) :
    let r := (k / p) * p + a
    (r.choose k).factorization p = 0 := by
  intro r
  have hkr : k ≤ r := by
    have hdiv := Nat.div_add_mod k p
    dsimp only [r]
    nlinarith
  have hrk : r - k = a - k % p := by
    have hdiv := Nat.div_add_mod k p
    rw [mul_comm] at hdiv
    dsimp only [r]
    omega
  rw [Nat.factorization_choose hp hkr (Nat.lt_add_one _)]
  rw [Finset.card_eq_zero, filter_eq_empty_iff]
  intro t ht
  rw [mem_Ico] at ht
  rw [not_le]
  have hpt_pos : 0 < p ^ t := pow_pos hp.pos t
  have hp_le_pt : p ≤ p ^ t := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ t := Nat.pow_le_pow_right hp.pos ht.1
  have hrk_lt : r - k < p ^ t := by omega
  rw [Nat.mod_eq_of_lt hrk_lt, hrk]
  have hp_dvd_pt : p ∣ p ^ t := dvd_pow_self p (by omega)
  have hmod_mod : (k % p ^ t) % p = k % p := Nat.mod_mod_of_dvd k hp_dvd_pt
  have hdiv_pt : p ^ t = (p ^ (t - 1)) * p := by
    rw [← pow_succ, Nat.sub_add_cancel ht.1]
  have hq_lt : (k % p ^ t) / p < p ^ (t - 1) := by
    rw [Nat.div_lt_iff_lt_mul hp.pos, ← hdiv_pt]
    exact Nat.mod_lt k hpt_pos
  have hkm : k % p ^ t = ((k % p ^ t) / p) * p + k % p := by
    rw [← hmod_mod, mul_comm]
    exact (Nat.div_add_mod (k % p ^ t) p).symm
  have hle_pow : ((k % p ^ t) / p + 1) * p ≤ p ^ t := by
    conv_rhs => rw [hdiv_pt]
    exact Nat.mul_le_mul_right p hq_lt
  rw [add_mul, one_mul] at hle_pow
  omega

/-- From a weight-`B` cover for `k`, construct the CRT progression and factorization
    `g : Fin k → ℕ` required by `OMA.R_Erdos387_erdos_387_R1.H1`. -/
theorem h1_witness_of_hasCoverB {B k : ℕ} (hcov : HasCoverB B k) :
    ∃ a : ℕ, ∃ g : Fin k → ℕ,
      let M := ∏ p ∈ (range (k + 1)).filter Nat.Prime, p ^ (Nat.log p k + 1)
      (∀ i, B ≤ g i) ∧ (∏ i, g i) = k.factorial ∧ ∀ n > k, n ≡ a [MOD M] →
        (∀ i : Fin k, g i ∣ n - i) ∧ ∀ p : ℕ, p.Prime → p ≤ k → ¬ p ∣ n.choose k := by
  classical
  obtain ⟨hk3, R, b, hb_prop, hb_cov⟩ := hcov
  set P : Finset ℕ := (range (k + 1)).filter Nat.Prime
  have hP_prime : ∀ p ∈ P, p.Prime := fun p hp => (mem_filter.mp hp).2
  have hP_le : ∀ p ∈ P, p ≤ k := fun p hp => Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
  have hR_sub : R ⊆ P := by
    intro p hp
    have ⟨hpr, hle, _, _⟩ := hb_prop p hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hle), hpr⟩
  let a' : ℕ → ℕ := fun p => if p ∈ R then p + k % p - b p else k % p
  let r : ℕ → ℕ := fun p => (k / p) * p + a' p
  let e : ℕ → ℕ := fun p => Nat.log p k + 1
  have ha'_bounds : ∀ p ∈ P, k % p ≤ a' p ∧ a' p < p := by
    intro p hp
    have hpr := hP_prime p hp
    dsimp only [a']
    split_ifs with hpR
    · have ⟨_, _, h1, h2⟩ := hb_prop p hpR
      omega
    · exact ⟨le_rfl, Nat.mod_lt k hpr.pos⟩
  have hr_eq_k : ∀ p, p ∉ R → r p = k := by
    intro p hpR
    dsimp only [r, a']
    rw [if_neg hpR, mul_comm]
    exact Nat.div_add_mod k p
  have hr_ge : ∀ p ∈ P, k ≤ r p := by
    intro p hp
    have h1 := (ha'_bounds p hp).1
    have hdiv := Nat.div_add_mod k p
    dsimp only [r]
    nlinarith
  have hr_lt : ∀ p ∈ P, r p < p ^ e p := by
    intro p hp
    have hpr := hP_prime p hp
    have h2 := (ha'_bounds p hp).2
    have hklt : k < p ^ (Nat.log p k + 1) := Nat.lt_pow_succ_log_self hpr.one_lt k
    dsimp only [r, e]
    rw [pow_succ] at hklt ⊢
    have hq : k / p < p ^ Nat.log p k := (Nat.div_lt_iff_lt_mul hpr.pos).mpr hklt
    have hq1 : (k / p + 1) * p ≤ p ^ Nat.log p k * p := Nat.mul_le_mul_right p hq
    rw [add_mul, one_mul] at hq1
    omega
  have hr_choose : ∀ p ∈ P, ((r p).choose k).factorization p = 0 := by
    intro p hp
    have h1 := ha'_bounds p hp
    exact choose_factorization_eq_zero_of_digit (hP_prime p hp) h1.1 h1.2
  have hs_ne : ∀ p ∈ P, p ^ e p ≠ 0 := fun p hp => pow_ne_zero _ (hP_prime p hp).ne_zero
  have hs_cop : (P : Set ℕ).Pairwise (Function.onFun Nat.Coprime fun p => p ^ e p) := by
    intro p hp q hq hpq
    change Nat.Coprime (p ^ e p) (q ^ e q)
    exact ((Nat.coprime_primes (hP_prime p hp) (hP_prime q hq)).mpr hpq).pow _ _
  let α_sub := Nat.chineseRemainderOfFinset r (fun p => p ^ e p) P hs_ne hs_cop
  let α : ℕ := α_sub.val
  let g : Fin k → ℕ := fun i => ∏ p ∈ P, p ^ ((r p - i.val).factorization p)
  refine ⟨α, g, ?_, ?_, ?_⟩
  · -- Part 1: ∀ i : Fin k, B ≤ g i
    intro i
    let j : ℕ := k - i.val
    have hj1 : 1 ≤ j := by dsimp only [j]; omega
    have hjk : j ≤ k := Nat.sub_le k i.val
    have hB_le := hb_cov j hj1 hjk
    have hg_pos : 0 < g i := prod_pos fun p hp => pow_pos (hP_prime p hp).pos _
    let S1 := P \ R
    let S2 := R.filter (fun p => j ≡ b p [MOD p])
    have hdisj : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      exact (mem_sdiff.mp hp1).2 (mem_filter.mp hp2).1
    have hsub_u : S1 ∪ S2 ⊆ P := by
      intro p hp
      rcases mem_union.mp hp with h1 | h2
      · exact (mem_sdiff.mp h1).1
      · exact hR_sub (mem_filter.mp h2).1
    have hdvd_S1 : (∏ p ∈ S1, p ^ (j.factorization p)) =
        ∏ p ∈ S1, p ^ ((r p - i.val).factorization p) := by
      refine prod_congr rfl fun p hp => ?_
      rw [hr_eq_k p (mem_sdiff.mp hp).2]
    have hdvd_S2 : (∏ p ∈ S2, p) ∣ ∏ p ∈ S2, p ^ ((r p - i.val).factorization p) := by
      refine Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_
      have hpR : p ∈ R := (mem_filter.mp hp).1
      have hcong : j ≡ b p [MOD p] := (mem_filter.mp hp).2
      have hpP : p ∈ P := hR_sub hpR
      have hpr := hP_prime p hpP
      have ⟨_, _, hkb, hbp⟩ := hb_prop p hpR
      have hri_pos : 0 < r p - i.val := by have := hr_ge p hpP; omega
      have hp_dvd_ri : p ∣ r p - i.val := by
        have h1 : r p ≡ a' p [MOD p] := by
          dsimp only [r]
          change ((k / p) * p + a' p) % p = a' p % p
          rw [Nat.mul_add_mod_self_right]
        have h2 : i.val ≡ a' p [MOD p] := by
          dsimp only [a']
          rw [if_pos hpR]
          have hadd : j + i.val = k := Nat.sub_add_cancel i.isLt.le
          have h3 : j + i.val ≡ b p + i.val [MOD p] := Nat.ModEq.add_right i.val hcong
          rw [hadd] at h3
          have h4 : (p + k % p - b p) + b p = p + k % p := by omega
          have h5 : b p + (p + k % p - b p) ≡ k [MOD p] := by
            rw [add_comm, h4]
            change (p + k % p) % p = k % p
            rw [Nat.add_mod_left, Nat.mod_mod]
          exact Nat.ModEq.add_left_cancel' (b p) (h3.symm.trans h5.symm)
        exact (Nat.modEq_iff_dvd' (by have := hr_ge p hpP; omega)).mp (h2.trans h1.symm)
      have hfac_pos : 1 ≤ (r p - i.val).factorization p :=
        Nat.Prime.factorization_pos_of_dvd hpr hri_pos.ne' hp_dvd_ri
      simpa using Nat.pow_dvd_pow p hfac_pos
    have hprod_dvd : (∏ p ∈ S1, p ^ (j.factorization p)) * (∏ p ∈ S2, p) ∣ g i := by
      rw [hdvd_S1]
      calc (∏ p ∈ S1, p ^ ((r p - i.val).factorization p)) * (∏ p ∈ S2, p)
          ∣ (∏ p ∈ S1, p ^ ((r p - i.val).factorization p)) *
              (∏ p ∈ S2, p ^ ((r p - i.val).factorization p)) := mul_dvd_mul_left _ hdvd_S2
        _ = ∏ p ∈ S1 ∪ S2, p ^ ((r p - i.val).factorization p) := (Finset.prod_union hdisj).symm
        _ ∣ ∏ p ∈ P, p ^ ((r p - i.val).factorization p) := Finset.prod_dvd_prod_of_subset _ _ _ hsub_u
    exact hB_le.trans (Nat.le_of_dvd hg_pos hprod_dvd)
  · -- Part 2: (∏ i, g i) = k.factorial
    dsimp only [g]
    rw [Finset.prod_comm]
    have hinner : ∀ p ∈ P,
        (∏ i : Fin k, p ^ ((r p - i.val).factorization p)) = p ^ (k.factorial.factorization p) := by
      intro p hp
      rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => (r p - i).factorization p)]
      congr 1
      have hne : ∀ i ∈ range k, r p - i ≠ 0 := by
        intro i hi; have := hr_ge p hp; have := mem_range.mp hi; omega
      have hprod_fac := Nat.factorization_prod hne
      have hsum_eq : ∑ i ∈ range k, (r p - i).factorization p =
          (∏ i ∈ range k, (r p - i)).factorization p := by
        rw [hprod_fac, Finsupp.finsetSum_apply]
      rw [hsum_eq, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose]
      have hch_ne : (r p).choose k ≠ 0 := Nat.choose_ne_zero (hr_ge p hp)
      rw [Nat.factorization_mul k.factorial_ne_zero hch_ne, Finsupp.coe_add, Pi.add_apply,
        hr_choose p hp, add_zero]
    rw [Finset.prod_congr rfl hinner]
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self k.factorial_ne_zero]
    rw [Finsupp.prod]
    symm
    apply Finset.prod_subset
    · intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.Prime.dvd_factorial hp.1).mp hp.2.1)), hp.1⟩
    · intro p _ hp_nmem
      rw [Finsupp.mem_support_iff, Classical.not_not] at hp_nmem
      simp [hp_nmem]
  · -- Part 3: ∀ n > k, n ≡ α [MOD M] → (∀ i, g i ∣ n - i) ∧ ∀ p, p.Prime → p ≤ k → ¬ p ∣ n.choose k
    intro n hkn hnα
    have hn_mod_p : ∀ p ∈ P, n ≡ r p [MOD p ^ e p] := by
      intro p hp
      have hdvd : p ^ e p ∣ ∏ q ∈ P, q ^ e q := dvd_prod_of_mem (fun q => q ^ e q) hp
      exact (hnα.of_dvd hdvd).trans (α_sub.prop p hp)
    have hfac_eq : ∀ p ∈ P, ∀ i < k, (n - i).factorization p = (r p - i).factorization p := by
      intro p hp i hik
      have hpr := hP_prime p hp
      have hmod_pe := hn_mod_p p hp
      have hri_pos : 0 < r p - i := by have := hr_ge p hp; omega
      have hni_pos : 0 < n - i := by omega
      have hri_lt : r p - i < p ^ e p := lt_of_le_of_lt (Nat.sub_le _ _) (hr_lt p hp)
      set v := (r p - i).factorization p
      have hv_lt : v < e p := by
        by_contra! hge
        have h1 : p ^ e p ∣ p ^ v := Nat.pow_dvd_pow p hge
        have h2 : p ^ v ∣ r p - i := Nat.ordProj_dvd (r p - i) p
        have h3 := Nat.le_of_dvd hri_pos (h1.trans h2)
        omega
      have hsub_mod : n - i ≡ r p - i [MOD p ^ e p] := by
        apply Nat.ModEq.add_right_cancel' i
        rw [Nat.sub_add_cancel (le_of_lt (hik.trans hkn)),
          Nat.sub_add_cancel (le_of_lt (lt_of_lt_of_le hik (hr_ge p hp)))]
        exact hmod_pe
      have hdvd_v : p ^ v ∣ n - i := by
        have h1 : p ^ v ∣ p ^ e p := Nat.pow_dvd_pow p hv_lt.le
        have h2 : n - i ≡ r p - i [MOD p ^ v] := hsub_mod.of_dvd h1
        have h3 : p ^ v ∣ r p - i := Nat.ordProj_dvd (r p - i) p
        exact Nat.dvd_iff_mod_eq_zero.mpr (Eq.trans h2 (Nat.dvd_iff_mod_eq_zero.mp h3))
      have hndvd_v1 : ¬ p ^ (v + 1) ∣ n - i := by
        intro hd
        have h1 : p ^ (v + 1) ∣ p ^ e p := Nat.pow_dvd_pow p hv_lt
        have h2 : n - i ≡ r p - i [MOD p ^ (v + 1)] := hsub_mod.of_dvd h1
        have h3 : p ^ (v + 1) ∣ r p - i :=
          Nat.dvd_iff_mod_eq_zero.mpr (Eq.trans h2.symm (Nat.dvd_iff_mod_eq_zero.mp hd))
        exact Nat.pow_succ_factorization_not_dvd hri_pos.ne' hpr h3
      have hle1 : v ≤ (n - i).factorization p :=
        (hpr.pow_dvd_iff_le_factorization hni_pos.ne').mp hdvd_v
      have hle2 : ¬ v + 1 ≤ (n - i).factorization p := fun h =>
        hndvd_v1 ((hpr.pow_dvd_iff_le_factorization hni_pos.ne').mpr h)
      omega
    constructor
    · intro i
      apply prod_dvd_of_pairwise_coprime P (fun p => p ^ ((r p - i.val).factorization p))
      · intro p hp q hq hpq
        exact ((Nat.coprime_primes (hP_prime p hp) (hP_prime q hq)).mpr hpq).pow _ _
      · intro p hp
        rw [← hfac_eq p hp i.val i.isLt]
        exact Nat.ordProj_dvd (n - i.val) p
    · intro p hpr hpk hdvd_ch
      have hpP : p ∈ P := mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hpk), hpr⟩
      have hch_pos : n.choose k ≠ 0 := Nat.choose_ne_zero hkn.le
      have hfac_ch_pos : 0 < (n.choose k).factorization p :=
        Nat.Prime.factorization_pos_of_dvd hpr hch_pos hdvd_ch
      have hne_n : ∀ i ∈ range k, n - i ≠ 0 := by intro i hi; have := mem_range.mp hi; omega
      have hne_r : ∀ i ∈ range k, r p - i ≠ 0 := by
        intro i hi; have := mem_range.mp hi; have := hr_ge p hpP; omega
      have hsum_n : (∏ i ∈ range k, (n - i)).factorization p =
          (∏ i ∈ range k, (r p - i)).factorization p := by
        rw [Nat.factorization_prod hne_n, Nat.factorization_prod hne_r,
          Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
        exact Finset.sum_congr rfl fun i hi => hfac_eq p hpP i (mem_range.mp hi)
      rw [← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
        Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
        Nat.factorization_mul k.factorial_ne_zero hch_pos,
        Nat.factorization_mul k.factorial_ne_zero (Nat.choose_ne_zero (hr_ge p hpP)),
        Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply,
        hr_choose p hpP, add_zero] at hsum_n
      omega

end OMA.Erdos387S1

/-
# Analytic tools for `Erdos387.erdos_387.R1.H1`

1. Elementary Mertens prime-reciprocal upper bound (`mertens_inv_prime_le`).
2. Rankin's trick smooth-number upper bound (`smooth_count_rankin`).
3. General Selberg upper bound via `BoundingSieve` (`selberg_upper_bound`).
4. Telescoping square-root bound for `∏_{p ∣ m, p > 2} p / (p - 1)`.
5. 2-dimensional Selberg sieve upper bound for linear prime pairs `q, a * q + c`
   (`two_dim_prime_pair_bound`).
-/

namespace OMA.Erdos387S2

open Finset Real Nat ArithmeticFunction BoundingSieve
open scoped Classical BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

/- ### Section 1: Elementary harmonic, Mertens, and smooth-number bounds -/

/-- Harmonic sum lower bound: `log (N + 1) ≤ ∑_{k=1}^N 1/k`. -/
lemma log_succ_le_harmonic (N : ℕ) :
    Real.log ((N + 1 : ℕ) : ℝ) ≤ ∑ k ∈ Icc 1 N, (1 : ℝ) / (k : ℝ) := by
  induction N with
  | zero => simp
  | succ m ih =>
    have hIcc : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    rw [hIcc, sum_insert (by simp)]
    have hstep : Real.log ((m + 2 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) ≤
        (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
      have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hm2 : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
      rw [← Real.log_div hm2.ne' hm1.ne']
      have hlog := Real.log_le_sub_one_of_pos (div_pos hm2 hm1)
      have hval : ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = 1 / ((m + 1 : ℕ) : ℝ) := by
        push_cast; field_simp [hm1.ne']; ring
      linarith
    linarith

/-- Harmonic sum upper bound: `∑_{k=1}^M 1/k ≤ 1 + log M` for `M ≥ 1`. -/
lemma harmonic_le_one_add_log {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Icc 1 M, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log (M : ℝ) := by
  induction M with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hIcc : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
        ext x; simp only [mem_Icc, mem_insert]; omega
      rw [hIcc, sum_insert (by simp)]
      have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
        have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
        have hm1pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
        have hlog := Real.log_le_sub_one_of_pos (div_pos hmpos hm1pos)
        rw [Real.log_div hmpos.ne' hm1pos.ne'] at hlog
        have hsub : (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = -(1 / ((m + 1 : ℕ) : ℝ)) := by
          push_cast; field_simp [hm1pos.ne']; ring
        linarith
      linarith [ih hm]

/-- Divisor sum upper bound: `∑_{m=1}^M τ(m) ≤ M * (1 + log M)` for `M ≥ 1`. -/
lemma sum_tau_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ m ∈ Icc 1 M, (m.divisors.card : ℝ) ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) := by
  have hswap : ∑ m ∈ Icc 1 M, (m.divisors.card : ℝ) =
      ∑ d ∈ Icc 1 M, (((Icc 1 M).filter fun m => d ∣ m).card : ℝ) := by
    have hnat : ∑ m ∈ Icc 1 M, m.divisors.card =
        ∑ d ∈ Icc 1 M, ((Icc 1 M).filter fun m => d ∣ m).card := by
      simp_rw [Finset.card_eq_sum_ones]
      calc ∑ m ∈ Icc 1 M, ∑ _d ∈ m.divisors, 1
          = ∑ m ∈ Icc 1 M, ∑ d ∈ Icc 1 M, if d ∣ m then 1 else 0 := by
            refine sum_congr rfl fun m hm => ?_
            rw [← Finset.sum_filter]
            refine sum_congr ?_ fun _ _ => rfl
            ext d
            simp only [Nat.mem_divisors, mem_filter, mem_Icc]
            have hm1 := (mem_Icc.mp hm).1; have hm2 := (mem_Icc.mp hm).2
            exact ⟨fun ⟨hd, _⟩ => ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega),
              (Nat.le_of_dvd (by omega) hd).trans hm2⟩, hd⟩, fun ⟨_, hd⟩ => ⟨hd, by omega⟩⟩
        _ = ∑ d ∈ Icc 1 M, ∑ m ∈ Icc 1 M, if d ∣ m then 1 else 0 := Finset.sum_comm
        _ = ∑ d ∈ Icc 1 M, ∑ _m ∈ (Icc 1 M).filter (fun m => d ∣ m), 1 := by
            refine sum_congr rfl fun d _ => (Finset.sum_filter _ _).symm
    exact_mod_cast hnat
  rw [hswap]
  have hmult : ∀ d ∈ Icc 1 M, (((Icc 1 M).filter fun m => d ∣ m).card : ℝ) ≤ (M : ℝ) / (d : ℝ) := by
    intro d hd
    have hd1 := (mem_Icc.mp hd).1
    have hcard : ((Icc 1 M).filter fun m => d ∣ m).card ≤ M / d := by
      have hsub : ((Icc 1 M).filter fun m => d ∣ m) ⊆ (Icc 1 (M / d)).image (d * ·) := by
        intro m hm
        obtain ⟨hmI, hdm⟩ := mem_filter.mp hm
        obtain ⟨hm1, hm2⟩ := mem_Icc.mp hmI
        obtain ⟨q, rfl⟩ := hdm
        refine mem_image.mpr ⟨q, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
        · by_contra h0; have hq0 : q = 0 := by omega
          rw [hq0, mul_zero] at hm1; omega
        · exact (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by linarith)
      exact (card_le_card hsub).trans (card_image_le.trans (by rw [Nat.card_Icc]; exact (Nat.add_sub_cancel (M / d) 1).le))
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    rw [le_div_iff₀ hdpos]
    exact_mod_cast (Nat.mul_le_mul_right d hcard).trans (Nat.div_mul_le_self M d)
  calc ∑ d ∈ Icc 1 M, (((Icc 1 M).filter fun m => d ∣ m).card : ℝ)
      ≤ ∑ d ∈ Icc 1 M, (M : ℝ) / (d : ℝ) := sum_le_sum hmult
    _ = (M : ℝ) * ∑ d ∈ Icc 1 M, (1 : ℝ) / (d : ℝ) := by
        rw [Finset.mul_sum]; refine sum_congr rfl fun d _ => by ring
    _ ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log hM) (by positivity)

/-- Subadditivity of nonnegative sums over finite `biUnion`. -/
lemma sum_biUnion_le_sum {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (t : ι → Finset α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    linarith [sum_nonneg (s := t a ∩ s.biUnion t) fun x _ => hf x]

/-- Elementary Mertens upper bound from Chebyshev's `theta_le_log4_mul_x`:
    for `N ≥ 3`, `∑ p ∈ N.primesLE, 1 / p ≤ 4 * log (log N) + 9`. -/
theorem mertens_inv_prime_le {N : ℕ} (hN : 3 ≤ N) :
    ∑ p ∈ N.primesLE, (1 : ℝ) / (p : ℝ) ≤ 4 * Real.log (Real.log (N : ℝ)) + 9 := by
  let J := Nat.log 2 N
  have hsub : N.primesLE ⊆ ({2} : Finset ℕ) ∪
      (Icc 1 J).biUnion (fun j => (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime) := by
    intro p hp
    obtain ⟨hpN, hpr⟩ := Nat.mem_primesLE.mp hp
    rcases eq_or_lt_of_le hpr.two_le with rfl | hgt
    · exact mem_union_left _ (mem_singleton_self 2)
    · refine mem_union_right _ (mem_biUnion.mpr ⟨Nat.log 2 p, mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩)
      · exact Nat.le_log_of_pow_le (by norm_num) (by omega)
      · exact Nat.log_mono_right hpN
      · refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, hpr⟩
        · have h1 : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 hpr.ne_zero
          rcases eq_or_lt_of_le h1 with heq | hlt
          · exfalso
            have hdvd : 2 ∣ p := by
              rw [← heq]
              exact dvd_pow_self 2 (Nat.log_pos (by norm_num) (by omega)).ne'
            have := (hpr.eq_one_or_self_of_dvd 2 hdvd).resolve_left (by norm_num)
            omega
          · exact hlt
        · exact (Nat.lt_pow_succ_log_self (by norm_num) p).le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4_eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hdyadic : ∀ j ∈ Icc 1 J,
      ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
        4 * ((1 : ℝ) / (j : ℝ)) := by
    intro j hj
    have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
    have h1 : ∀ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) ≤ Real.log (p : ℝ) / ((2 ^ j : ℝ) * ((j : ℝ) * Real.log 2)) := by
      intro p hp
      have hp1 : 2 ^ j < p := (mem_Ioc.mp (mem_filter.mp hp).1).1
      have hp_ge : (2 ^ j : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1.le
      have hlogp : (j : ℝ) * Real.log 2 ≤ Real.log (p : ℝ) := by
        calc (j : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ j) := (Real.log_pow 2 j).symm
          _ ≤ Real.log (p : ℝ) := Real.log_le_log (by positivity) hp_ge
      have hppos : (0 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.pos
      rw [div_le_div_iff₀ hppos (by positivity)]
      calc 1 * ((2 ^ j : ℝ) * ((j : ℝ) * Real.log 2))
          = (2 ^ j : ℝ) * ((j : ℝ) * Real.log 2) := one_mul _
        _ ≤ (p : ℝ) * Real.log (p : ℝ) := mul_le_mul hp_ge hlogp (by positivity) (by positivity)
        _ = Real.log (p : ℝ) * (p : ℝ) := mul_comm _ _
    have hsub_le : (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime ⊆ (2 ^ (j + 1)).primesLE := by
      intro p hp
      exact Nat.mem_primesLE.mpr ⟨(mem_Ioc.mp (mem_filter.mp hp).1).2, (mem_filter.mp hp).2⟩
    calc ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
        ≤ ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime,
            Real.log (p : ℝ) / ((2 ^ j : ℝ) * ((j : ℝ) * Real.log 2)) := sum_le_sum h1
      _ = (∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, Real.log (p : ℝ)) /
            ((2 ^ j : ℝ) * ((j : ℝ) * Real.log 2)) := (Finset.sum_div _ _ _).symm
      _ ≤ (∑ p ∈ (2 ^ (j + 1)).primesLE, Real.log (Nat.cast p)) /
            ((2 ^ j : ℝ) * ((j : ℝ) * Real.log 2)) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          exact sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p : ℝ)) hsub_le fun p hp _ =>
            Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
      _ = Chebyshev.theta ((2 ^ (j + 1) : ℕ) : ℝ) / ((2 ^ j : ℝ) * ((j : ℝ) * Real.log 2)) := by
          rw [Chebyshev.theta_eq_sum_primesLE_log]
      _ ≤ (Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ)) / ((2 ^ j : ℝ) * ((j : ℝ) * Real.log 2)) :=
          div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by positivity)) (by positivity)
      _ = 4 * ((1 : ℝ) / (j : ℝ)) := by
          push_cast; rw [pow_succ, hlog4_eq]
          field_simp [hlog2.ne', hjpos.ne', (show (2 : ℝ) ^ j ≠ 0 by positivity)]; ring
  have hJ1 : 1 ≤ J := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hJ_le : (J : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    have h1 : ((2 : ℝ) ^ J) ≤ (N : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have h2 := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at h2
  have hlogJ : Real.log (J : ℝ) ≤ Real.log (Real.log (N : ℝ)) + 1 := by
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have h1 : Real.log (J : ℝ) ≤ Real.log (Real.log (N : ℝ) / Real.log 2) :=
      Real.log_le_log (by exact_mod_cast hJ1) hJ_le
    rw [Real.log_div hlogN.ne' hlog2.ne'] at h1
    have hlog2_ge : Real.exp (-1) ≤ Real.log 2 := by
      have : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith [Real.exp_one_gt_d9]
      linarith [Real.log_two_gt_d9]
    have hloglog2 : -1 ≤ Real.log (Real.log 2) := by
      have := Real.log_le_log (Real.exp_pos (-1)) hlog2_ge
      rwa [Real.log_exp] at this
    linarith
  have hunion_le : ∑ p ∈ ({2} : Finset ℕ) ∪
      (Icc 1 J).biUnion (fun j => (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime), (1 : ℝ) / (p : ℝ) ≤
      (1 : ℝ) / 2 + ∑ j ∈ Icc 1 J,
        ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
    have h := Finset.sum_union_inter (s₁ := ({2} : Finset ℕ))
      (s₂ := (Icc 1 J).biUnion (fun j => (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime))
      (f := fun p : ℕ => (1 : ℝ) / (p : ℝ))
    have hnn : 0 ≤ ∑ p ∈ ({2} : Finset ℕ) ∩
        (Icc 1 J).biUnion (fun j => (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime), (1 : ℝ) / (p : ℝ) :=
      sum_nonneg fun _ _ => by positivity
    have hbi := sum_biUnion_le_sum (Icc 1 J)
      (fun j => (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime) (fun p => (1 : ℝ) / (p : ℝ)) (fun _ => by positivity)
    have h2eq : ∑ p ∈ ({2} : Finset ℕ), (1 : ℝ) / (p : ℝ) = 1 / 2 := by simp
    linarith
  calc ∑ p ∈ N.primesLE, (1 : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ ({2} : Finset ℕ) ∪
          (Icc 1 J).biUnion (fun j => (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime), (1 : ℝ) / (p : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ 1 / 2 + ∑ j ∈ Icc 1 J, 4 * ((1 : ℝ) / (j : ℝ)) :=
        hunion_le.trans (add_le_add le_rfl (sum_le_sum hdyadic))
    _ = 1 / 2 + 4 * ∑ j ∈ Icc 1 J, (1 : ℝ) / (j : ℝ) := by rw [← Finset.mul_sum]
    _ ≤ 1 / 2 + 4 * (1 + Real.log (J : ℝ)) := by linarith [harmonic_le_one_add_log hJ1]
    _ ≤ 4 * Real.log (Real.log (N : ℝ)) + 9 := by linarith

/-- Finite Euler-product upper bound: for any finite set of primes `S`, any `σ > 0`, and any `X ≥ 1`,
    the sum of `(m : ℝ)^(-σ)` over `m ∈ Icc 1 X` whose prime factors all lie in `S` is bounded by
    `∏ p ∈ S, (1 - (p : ℝ)^(-σ))⁻¹`. -/
lemma sum_smooth_rpow_le_euler (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {σ : ℝ} (hσ : 0 < σ) (X : ℕ) :
    ∑ m ∈ (Icc 1 X).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∈ S), (m : ℝ) ^ (-σ) ≤
      ∏ p ∈ S, (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  induction S using Finset.induction_on generalizing X with
  | empty =>
    have hsub : (Icc 1 X).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∈ (∅ : Finset ℕ)) ⊆ {1} := by
      intro m hm
      obtain ⟨hmI, hmp⟩ := mem_filter.mp hm
      have hm1 := (mem_Icc.mp hmI).1
      rw [mem_singleton]
      by_contra hne
      obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hne
      exact Finset.notMem_empty p (hmp p hp hpm)
    calc ∑ m ∈ (Icc 1 X).filter _, (m : ℝ) ^ (-σ)
        ≤ ∑ m ∈ ({1} : Finset ℕ), (m : ℝ) ^ (-σ) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
      _ = 1 := by simp
      _ = ∏ p ∈ (∅ : Finset ℕ), (1 - (p : ℝ) ^ (-σ))⁻¹ := by simp
  | @insert q S hq ih =>
    have hqp : q.Prime := hS q (mem_insert_self q S)
    have hS' : ∀ p ∈ S, p.Prime := fun p hp => hS p (mem_insert_of_mem hp)
    rw [prod_insert hq]
    let A := (Icc 1 X).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∈ insert q S)
    let B := (Icc 1 X).filter (fun u => ∀ p, p.Prime → p ∣ u → p ∈ S)
    let E := Nat.log q X + 1
    -- Every m ∈ A factors uniquely as q^a * u with a ∈ range E and u ∈ B!
    have hsub : A ⊆ ((range E) ×ˢ B).image (fun p => q ^ p.1 * p.2) := by
      intro m hm
      obtain ⟨hmI, hmp⟩ := mem_filter.mp hm
      have hm1 := (mem_Icc.mp hmI).1; have hmX := (mem_Icc.mp hmI).2
      let a := m.factorization q
      let u := m / q ^ a
      have hqa_dvd : q ^ a ∣ m := Nat.ordProj_dvd m q
      have hmul : q ^ a * u = m := Nat.mul_div_cancel' hqa_dvd
      have ha_lt : a < E := by
        dsimp only [E]
        have h1 : q ^ a ≤ X := (Nat.le_of_dvd (by omega) hqa_dvd).trans hmX
        exact Nat.lt_succ_of_le (Nat.le_log_of_pow_le hqp.one_lt h1)
      have hu_pos : 1 ≤ u := Nat.div_pos (Nat.le_of_dvd (by omega) hqa_dvd) (pow_pos hqp.pos a)
      have hu_le : u ≤ X := (Nat.div_le_self m _).trans hmX
      have hu_S : ∀ p, p.Prime → p ∣ u → p ∈ S := by
        intro p hp hpu
        have hpm : p ∣ m := by rw [← hmul]; exact dvd_mul_of_dvd_right hpu _
        rcases mem_insert.mp (hmp p hp hpm) with hpq | hpS
        · exfalso
          rw [hpq] at hpu
          have hq1 : q ^ (a + 1) ∣ m := by
            rw [← hmul, pow_succ]
            exact mul_dvd_mul_left (q ^ a) hpu
          exact Nat.pow_succ_factorization_not_dvd (by omega : m ≠ 0) hqp hq1
        · exact hpS
      exact mem_image.mpr ⟨(a, u), mem_product.mpr ⟨mem_range.mpr ha_lt, mem_filter.mpr ⟨mem_Icc.mpr ⟨hu_pos, hu_le⟩, hu_S⟩⟩, hmul⟩
    have hgeom : ∑ a ∈ range E, ((q : ℝ) ^ (-σ)) ^ a ≤ (1 - (q : ℝ) ^ (-σ))⁻¹ := by
      have hq_pos : (0 : ℝ) < q := by exact_mod_cast hqp.pos
      have hr_pos : 0 < (q : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hq_pos (-σ)
      have hr_lt1 : (q : ℝ) ^ (-σ) < 1 := by
        rw [Real.rpow_neg hq_pos.le, inv_lt_one_iff₀]
        right
        calc (1 : ℝ) = (q : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
          _ < (q : ℝ) ^ σ := Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hqp.one_lt) hσ
      rw [geom_sum_eq hr_lt1.ne, inv_eq_one_div]
      have h1 : (((q : ℝ) ^ (-σ)) ^ E - 1) / ((q : ℝ) ^ (-σ) - 1) =
          (1 - ((q : ℝ) ^ (-σ)) ^ E) / (1 - (q : ℝ) ^ (-σ)) := by
        field_simp [sub_ne_zero.mpr hr_lt1.ne, sub_ne_zero.mpr hr_lt1.ne']; ring
      rw [h1]
      exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr_pos.le E]) (by linarith)
    calc ∑ m ∈ A, (m : ℝ) ^ (-σ)
        ≤ ∑ m ∈ ((range E) ×ˢ B).image (fun p : ℕ × ℕ => q ^ p.1 * p.2), (m : ℝ) ^ (-σ) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
      _ ≤ ∑ x ∈ (range E) ×ˢ B, ((q ^ x.1 * x.2 : ℕ) : ℝ) ^ (-σ) :=
          Finset.sum_image_le_of_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
      _ = (∑ a ∈ range E, ((q : ℝ) ^ (-σ)) ^ a) * (∑ u ∈ B, (u : ℝ) ^ (-σ)) := by
          rw [Finset.sum_product, Finset.sum_mul]
          refine sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine sum_congr rfl fun u _ => ?_
          rw [Nat.cast_mul, Nat.cast_pow, Real.mul_rpow (by positivity) (Nat.cast_nonneg _),
            ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
            ← Real.rpow_natCast ((q : ℝ) ^ (-σ)) a, ← Real.rpow_mul (Nat.cast_nonneg _)]
          congr 1; ring
      _ ≤ (1 - (q : ℝ) ^ (-σ))⁻¹ * (∏ p ∈ S, (1 - (p : ℝ) ^ (-σ))⁻¹) := by
          have hq1 : 0 < 1 - (q : ℝ) ^ (-σ) := by
            have hq_pos : (0 : ℝ) < q := by exact_mod_cast hqp.pos
            have : (q : ℝ) ^ (-σ) < 1 := by
              rw [Real.rpow_neg hq_pos.le, inv_lt_one_iff₀]; right
              calc (1 : ℝ) = (q : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
                _ < (q : ℝ) ^ σ := Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hqp.one_lt) hσ
            linarith
          exact mul_le_mul hgeom (ih hS' X) (sum_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)

/-- Rankin's trick smooth-number upper bound: for `X ≥ 100` and `Y ≥ 16`,
    the number of `Y`-smooth integers in `[1, X]` is at most
    `X * exp (-(log X) / (2 * log Y) + 16 * log (log Y) + 40)`. -/
theorem smooth_count_rankin {X Y : ℕ} (hX : 100 ≤ X) (hY : 16 ≤ Y) :
    (((Icc 1 X).filter (fun m => ∀ p, p.Prime → p ∣ m → p ≤ Y)).card : ℝ) ≤
      (X : ℝ) * Real.exp (-(Real.log (X : ℝ)) / (2 * Real.log (Y : ℝ)) +
        16 * Real.log (Real.log (Y : ℝ)) + 40) := by
  have hXpos : (0 : ℝ) < X := by positivity
  have hYpos : (0 : ℝ) < Y := by positivity
  have hlogY : 2 ≤ Real.log (Y : ℝ) := by
    have : Real.exp 2 ≤ (Y : ℝ) := by
      have : Real.exp 2 = (Real.exp 1) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      have h1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      have h2 : (Real.exp 1) ^ 2 ≤ 9 := by nlinarith [Real.exp_pos 1]
      have hY16 : (16 : ℝ) ≤ Y := by exact_mod_cast hY
      linarith
    have := Real.log_le_log (Real.exp_pos 2) this
    rwa [Real.log_exp] at this
  have hlogY_pos : 0 < Real.log (Y : ℝ) := by linarith
  let ε : ℝ := 1 / (2 * Real.log (Y : ℝ))
  let σ : ℝ := 1 - ε
  have hε_pos : 0 < ε := by positivity
  have hε_le : ε ≤ 1 / 4 := by
    dsimp only [ε]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hσ_pos : 0 < σ := by dsimp only [σ]; linarith
  have hσ_ge : (1 / 2 : ℝ) ≤ σ := by dsimp only [σ]; linarith
  have hsmooth_eq : (Icc 1 X).filter (fun m => ∀ p, p.Prime → p ∣ m → p ≤ Y) =
      (Icc 1 X).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∈ Y.primesLE) := by
    ext m; simp only [mem_filter, Nat.mem_primesLE]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun p hp hd => ⟨h2 p hp hd, hp⟩⟩,
           fun ⟨h1, h2⟩ => ⟨h1, fun p hp hd => (h2 p hp hd).1⟩⟩
  -- Rankin step: 1 ≤ (X / m)^σ = X^σ * m^(-σ) for every m ∈ Icc 1 X
  have hrankin : (((Icc 1 X).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∈ Y.primesLE)).card : ℝ) ≤
      (X : ℝ) ^ σ * ∑ m ∈ (Icc 1 X).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∈ Y.primesLE), (m : ℝ) ^ (-σ) := by
    rw [Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum]
    refine sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (mem_Icc.mp (mem_filter.mp hm).1).1
    have hmX : m ≤ X := (mem_Icc.mp (mem_filter.mp hm).1).2
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    simp only [Nat.cast_one]
    rw [Real.rpow_neg hmpos.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hmpos _)]
    exact Real.rpow_le_rpow hmpos.le (by exact_mod_cast hmX) hσ_pos.le
  -- Bound the Euler product ∏_{p ≤ Y} (1 - p^(-σ))⁻¹
  have heuler : ∏ p ∈ Y.primesLE, (1 - (p : ℝ) ^ (-σ))⁻¹ ≤
      Real.exp (16 * Real.log (Real.log (Y : ℝ)) + 40) := by
    -- For every p ∈ Y.primesLE: p^ε ≤ Y^ε = exp(1/2) ≤ 2, so p^(-σ) = p^ε / p ≤ 2 / p.
    have hp_eps : ∀ p ∈ Y.primesLE, (p : ℝ) ^ (-σ) ≤ 2 / (p : ℝ) := by
      intro p hp
      have hpr := Nat.prime_of_mem_primesLE hp
      have hpY : (p : ℝ) ≤ Y := by exact_mod_cast Nat.le_of_mem_primesLE hp
      have hppos : (0 : ℝ) < p := by exact_mod_cast hpr.pos
      have h1 : (p : ℝ) ^ ε ≤ 2 := by
        calc (p : ℝ) ^ ε ≤ (Y : ℝ) ^ ε := Real.rpow_le_rpow hppos.le hpY hε_pos.le
          _ = Real.exp (ε * Real.log (Y : ℝ)) := by rw [Real.rpow_def_of_pos hYpos, mul_comm]
          _ = Real.exp (1 / 2) := by
              congr 1; dsimp only [ε]; field_simp [hlogY_pos.ne']
          _ ≤ 2 := by
              have hsq : (Real.exp (1 / 2)) ^ 2 ≤ 2 ^ 2 := by
                rw [← Real.exp_nat_mul]; norm_num; linarith [Real.exp_one_lt_d9]
              nlinarith [Real.exp_pos (1 / 2)]
      have h2 : (p : ℝ) ^ (-σ) = (p : ℝ) ^ ε / (p : ℝ) := by
        dsimp only [σ]
        rw [show -(1 - ε) = ε - 1 by ring, Real.rpow_sub hppos, Real.rpow_one]
      rw [h2]
      exact div_le_div_of_nonneg_right h1 hppos.le
    -- Split Y.primesLE into {p ≤ 4} and {p ≥ 5}
    let S1 := Y.primesLE.filter (· ≤ 4)
    let S2 := Y.primesLE.filter (fun p => ¬ p ≤ 4)
    have hsplit : ∏ p ∈ Y.primesLE, (1 - (p : ℝ) ^ (-σ))⁻¹ =
        (∏ p ∈ S1, (1 - (p : ℝ) ^ (-σ))⁻¹) * (∏ p ∈ S2, (1 - (p : ℝ) ^ (-σ))⁻¹) :=
      (Finset.prod_filter_mul_prod_filter_not Y.primesLE (· ≤ 4) _).symm
    rw [hsplit]
    have hS1 : ∏ p ∈ S1, (1 - (p : ℝ) ^ (-σ))⁻¹ ≤ Real.exp 4 := by
      have hsub1 : S1 ⊆ ({2, 3} : Finset ℕ) := by
        intro p hp
        obtain ⟨hpY, hp4⟩ := mem_filter.mp hp
        have hpr := Nat.prime_of_mem_primesLE hpY
        have h2 := hpr.two_le
        have : p = 2 ∨ p = 3 := by
          rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4) with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
          · exfalso; norm_num at hpr
        simp [this]
      have hfac : ∀ p ∈ S1, (1 - (p : ℝ) ^ (-σ))⁻¹ ≤ 4 := by
        intro p hp
        have hpr := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
        have hppos : (0 : ℝ) < p := by exact_mod_cast hpr.pos
        have h1 : (p : ℝ) ^ (-σ) ≤ 3 / 4 := by
          have h2 : (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
            rw [Real.rpow_neg hppos.le, Real.rpow_neg (by norm_num)]
            refine inv_anti₀ (by positivity) ?_
            calc (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ (p : ℝ) ^ ((1 : ℝ) / 2) :=
                  Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hpr.two_le) (by norm_num)
              _ ≤ (p : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpr.one_le) hσ_ge
          have h3 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
            rw [Real.rpow_neg (by norm_num), inv_le_comm₀ (by positivity) (by norm_num)]
            have hsq : ((4 / 3 : ℝ) ^ 2) ≤ ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 := by
              rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num)]; norm_num
            nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (1 / 2)]
          linarith
        have hpos : 0 < 1 - (p : ℝ) ^ (-σ) := by linarith
        rw [inv_le_comm₀ hpos (by norm_num)]; linarith
      have hcard1 : S1.card ≤ 2 := (card_le_card hsub1).trans (by decide)
      calc ∏ p ∈ S1, (1 - (p : ℝ) ^ (-σ))⁻¹
          ≤ ∏ _p ∈ S1, (4 : ℝ) := prod_le_prod (fun p hp => by
            have hpr := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
            have : (p : ℝ) ^ (-σ) < 1 := by
              rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]; right
              calc (1 : ℝ) = (p : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
                _ < (p : ℝ) ^ σ := Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hpr.one_lt) hσ_pos
            exact inv_nonneg.mpr (by linarith)) hfac
        _ = (4 : ℝ) ^ S1.card := by simp
        _ ≤ (4 : ℝ) ^ (2 : ℕ) := pow_le_pow_right₀ (by norm_num) hcard1
        _ ≤ Real.exp 4 := by
            have h1 : (2 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 :=
              pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 4
            rw [← Real.exp_nat_mul] at h1; norm_num at h1 ⊢; linarith
    have hS2 : ∏ p ∈ S2, (1 - (p : ℝ) ^ (-σ))⁻¹ ≤ Real.exp (16 * Real.log (Real.log (Y : ℝ)) + 36) := by
      have hfac2 : ∀ p ∈ S2, (1 - (p : ℝ) ^ (-σ))⁻¹ ≤ Real.exp (4 / (p : ℝ)) := by
        intro p hp
        have hpY := (mem_filter.mp hp).1
        have hp5 : 5 ≤ p := by have := (mem_filter.mp hp).2; omega
        have hpR5 : (5 : ℝ) ≤ p := by exact_mod_cast hp5
        have hp_le := hp_eps p hpY
        have hx_le : (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
          have : 2 / (p : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
          linarith
        have hpos : 0 < 1 - (p : ℝ) ^ (-σ) := by linarith
        have h1 : (1 - (p : ℝ) ^ (-σ))⁻¹ ≤ 1 + 2 * (p : ℝ) ^ (-σ) := by
          rw [inv_le_iff_one_le_mul₀ hpos]
          nlinarith [Real.rpow_nonneg (Nat.cast_nonneg p) (-σ)]
        have h2 : 1 + 2 * (p : ℝ) ^ (-σ) ≤ 1 + 4 / (p : ℝ) := by
          have : 2 * (2 / (p : ℝ)) = 4 / (p : ℝ) := by ring
          linarith
        exact (h1.trans h2).trans (by linarith [Real.add_one_le_exp (4 / (p : ℝ))])
      calc ∏ p ∈ S2, (1 - (p : ℝ) ^ (-σ))⁻¹
          ≤ ∏ p ∈ S2, Real.exp (4 / (p : ℝ)) := prod_le_prod (fun p hp => by
            have hpr := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
            have : (p : ℝ) ^ (-σ) < 1 := by
              rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]; right
              calc (1 : ℝ) = (p : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
                _ < (p : ℝ) ^ σ := Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hpr.one_lt) hσ_pos
            exact inv_nonneg.mpr (by linarith)) hfac2
        _ = Real.exp (∑ p ∈ S2, 4 / (p : ℝ)) := (Real.exp_sum _ _).symm
        _ ≤ Real.exp (∑ p ∈ Y.primesLE, 4 / (p : ℝ)) :=
            Real.exp_le_exp.mpr (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity)
        _ = Real.exp (4 * ∑ p ∈ Y.primesLE, (1 : ℝ) / (p : ℝ)) := by
            congr 1; rw [Finset.mul_sum]; refine sum_congr rfl fun _ _ => by ring
        _ ≤ Real.exp (16 * Real.log (Real.log (Y : ℝ)) + 36) := by
            apply Real.exp_le_exp.mpr
            linarith [mertens_inv_prime_le (by omega : 3 ≤ Y)]
    calc (∏ p ∈ S1, (1 - (p : ℝ) ^ (-σ))⁻¹) * (∏ p ∈ S2, (1 - (p : ℝ) ^ (-σ))⁻¹)
        ≤ Real.exp 4 * Real.exp (16 * Real.log (Real.log (Y : ℝ)) + 36) :=
          mul_le_mul hS1 hS2 (prod_nonneg fun p hp => by
            have hpr := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
            have : (p : ℝ) ^ (-σ) < 1 := by
              rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]; right
              calc (1 : ℝ) = (p : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
                _ < (p : ℝ) ^ σ := Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hpr.one_lt) hσ_pos
            exact inv_nonneg.mpr (by linarith)) (Real.exp_pos 4).le
      _ = Real.exp (16 * Real.log (Real.log (Y : ℝ)) + 40) := by rw [← Real.exp_add]; congr 1; ring
  have hXσ : (X : ℝ) ^ σ = (X : ℝ) * Real.exp (-(Real.log (X : ℝ)) / (2 * Real.log (Y : ℝ))) := by
    dsimp only [σ, ε]
    rw [Real.rpow_sub hXpos, Real.rpow_one, Real.rpow_def_of_pos hXpos, div_eq_mul_inv, ← Real.exp_neg]
    congr 2; ring
  rw [hsmooth_eq]
  calc (((Icc 1 X).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∈ Y.primesLE)).card : ℝ)
      ≤ (X : ℝ) ^ σ * ∑ m ∈ (Icc 1 X).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∈ Y.primesLE), (m : ℝ) ^ (-σ) :=
        hrankin
    _ ≤ (X : ℝ) ^ σ * (∏ p ∈ Y.primesLE, (1 - (p : ℝ) ^ (-σ))⁻¹) :=
        mul_le_mul_of_nonneg_left (sum_smooth_rpow_le_euler Y.primesLE (fun p hp => Nat.prime_of_mem_primesLE hp) hσ_pos X)
          (Real.rpow_nonneg hXpos.le σ)
    _ ≤ (X : ℝ) ^ σ * Real.exp (16 * Real.log (Real.log (Y : ℝ)) + 40) :=
        mul_le_mul_of_nonneg_left heuler (Real.rpow_nonneg hXpos.le σ)
    _ = (X : ℝ) * Real.exp (-(Real.log (X : ℝ)) / (2 * Real.log (Y : ℝ)) +
          16 * Real.log (Real.log (Y : ℝ)) + 40) := by
        rw [hXσ, mul_assoc, ← Real.exp_add]; congr 2; ring

/- ### Section 2: General Selberg upper bound via `BoundingSieve` -/

/-- General Selberg upper bound: for any `s : BoundingSieve` and level `Z ≥ 1`, letting
    `D = (divisors s.prodPrimes).filter (· ≤ Z)` and `S_sel = ∑ l ∈ D, s.selbergTerms l`,
    if `|s.rem (d1.lcm d2)| ≤ R d1 * R d2` for all `d1, d2 ∈ D` (with `0 ≤ R d`), then
    `s.siftedSum ≤ s.totalMass / S_sel + (∑ d ∈ D, R d) ^ 2`. -/
theorem selberg_upper_bound (s : BoundingSieve) {Z : ℕ} (hZ : 1 ≤ Z)
    (R : ℕ → ℝ) (_hR_nn : ∀ d, 0 ≤ R d)
    (hrem : ∀ d1 ∈ (divisors s.prodPrimes).filter (· ≤ Z),
            ∀ d2 ∈ (divisors s.prodPrimes).filter (· ≤ Z),
              |s.rem (d1.lcm d2)| ≤ R d1 * R d2) :
    s.siftedSum ≤
      s.totalMass / (∑ l ∈ (divisors s.prodPrimes).filter (· ≤ Z), s.selbergTerms l) +
      (∑ d ∈ (divisors s.prodPrimes).filter (· ≤ Z), R d) ^ 2 := by
  classical
  let P := s.prodPrimes
  have hP0 : P ≠ 0 := s.prodPrimes_ne_zero
  let D := (divisors P).filter (· ≤ Z)
  let S_sel : ℝ := ∑ l ∈ D, s.selbergTerms l
  have h1D : 1 ∈ D := mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hP0, hZ⟩
  have hS_pos : 0 < S_sel := by
    have h1 : 0 < s.selbergTerms 1 := s.selbergTerms_pos (one_dvd P)
    have hle : s.selbergTerms 1 ≤ S_sel :=
      Finset.single_le_sum (fun l hl => (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hl).1)).le) h1D
    linarith
  let y : ℕ → ℝ := fun l => if l ∈ D then s.selbergTerms l / S_sel else 0
  let w : ℕ → ℝ := fun d =>
    if d ∈ D then ((μ d : ℝ) / s.nu d) * ∑ l ∈ D.filter (d ∣ ·), y l else 0
  have hw1 : w 1 = 1 := by
    dsimp only [w]
    rw [if_pos h1D, ArithmeticFunction.moebius_apply_one, Int.cast_one, s.nu_mult.map_one, div_one, one_mul]
    have hfilt : D.filter (1 ∣ ·) = D := by ext l; simp
    rw [hfilt]
    have hsum : ∑ l ∈ D, y l = ∑ l ∈ D, s.selbergTerms l / S_sel :=
      sum_congr rfl fun l hl => if_pos hl
    rw [hsum, ← Finset.sum_div, div_self hS_pos.ne']
  -- Key Möbius identity: for every l ∣ P, ∑_{d ∣ P, l ∣ d} nu d * w d = μ l * y l
  have hdiag : ∀ l ∈ divisors P,
      (∑ d ∈ divisors P, if l ∣ d then s.nu d * w d else 0) = (μ l : ℝ) * y l := by
    intro l hl
    have hlP : l ∣ P := Nat.dvd_of_mem_divisors hl
    have hl_sq : Squarefree l := s.squarefree_of_dvd_prodPrimes hlP
    have hl_pos : 0 < l := Nat.pos_of_ne_zero hl_sq.ne_zero
    have h1 : (∑ d ∈ divisors P, if l ∣ d then s.nu d * w d else 0) =
        ∑ d ∈ D.filter (l ∣ ·), s.nu d * w d := by
      rw [← Finset.sum_filter]
      symm
      refine Finset.sum_subset
        (fun d hd => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hd).1).1, (mem_filter.mp hd).2⟩) ?_
      intro d hd hd_not
      have hd_notD : d ∉ D := fun hdD => hd_not (mem_filter.mpr ⟨hdD, (mem_filter.mp hd).2⟩)
      dsimp only [w]; rw [if_neg hd_notD, mul_zero]
    rw [h1]
    have h2 : ∑ d ∈ D.filter (l ∣ ·), s.nu d * w d =
        ∑ d ∈ D.filter (l ∣ ·), (μ d : ℝ) * ∑ m ∈ D.filter (d ∣ ·), y m := by
      refine sum_congr rfl fun d hd => ?_
      have hdD : d ∈ D := (mem_filter.mp hd).1
      have hdP : d ∣ P := Nat.dvd_of_mem_divisors (mem_filter.mp hdD).1
      dsimp only [w]; rw [if_pos hdD]
      have hnu : s.nu d ≠ 0 := s.nu_ne_zero hdP
      field_simp [hnu]
    rw [h2]
    -- Swap sums over d and m:
    have hswap : (∑ d ∈ D.filter (l ∣ ·), (μ d : ℝ) * ∑ m ∈ D.filter (d ∣ ·), y m) =
        ∑ m ∈ D.filter (l ∣ ·), y m * ∑ d ∈ m.divisors.filter (l ∣ ·), (μ d : ℝ) := by
      calc ∑ d ∈ D.filter (l ∣ ·), (μ d : ℝ) * ∑ m ∈ D.filter (d ∣ ·), y m
          = ∑ d ∈ D.filter (l ∣ ·), ∑ m ∈ D.filter (l ∣ ·), if d ∣ m then (μ d : ℝ) * y m else 0 := by
            refine sum_congr rfl fun d hd => ?_
            have hld : l ∣ d := (mem_filter.mp hd).2
            rw [Finset.mul_sum, ← Finset.sum_filter]
            refine sum_congr ?_ fun _ _ => rfl
            ext m; simp only [mem_filter]
            exact ⟨fun ⟨hmD, hdm⟩ => ⟨⟨hmD, hld.trans hdm⟩, hdm⟩, fun ⟨⟨hmD, _⟩, hdm⟩ => ⟨hmD, hdm⟩⟩
        _ = ∑ m ∈ D.filter (l ∣ ·), ∑ d ∈ D.filter (l ∣ ·), if d ∣ m then (μ d : ℝ) * y m else 0 := Finset.sum_comm
        _ = ∑ m ∈ D.filter (l ∣ ·), y m * ∑ d ∈ m.divisors.filter (l ∣ ·), (μ d : ℝ) := by
            refine sum_congr rfl fun m hm => ?_
            have hmD : m ∈ D := (mem_filter.mp hm).1
            have hmP : m ∣ P := Nat.dvd_of_mem_divisors (mem_filter.mp hmD).1
            have hmZ : m ≤ Z := (mem_filter.mp hmD).2
            have hm0 : m ≠ 0 := ne_zero_of_dvd_ne_zero hP0 hmP
            rw [← Finset.sum_filter, Finset.mul_sum]
            have hset : (D.filter (l ∣ ·)).filter (· ∣ m) = m.divisors.filter (l ∣ ·) := by
              ext d; simp only [mem_filter, Nat.mem_divisors, D]
              constructor
              · rintro ⟨⟨⟨_, _⟩, hld⟩, hdm⟩; exact ⟨⟨hdm, hm0⟩, hld⟩
              · rintro ⟨⟨hdm, _⟩, hld⟩
                exact ⟨⟨⟨⟨hdm.trans hmP, hP0⟩, (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdm).trans hmZ⟩, hld⟩, hdm⟩
            rw [hset]
            exact sum_congr rfl fun _ _ => mul_comm _ _
    rw [hswap]
    have hinner : ∀ m ∈ D.filter (l ∣ ·),
        ∑ d ∈ m.divisors.filter (l ∣ ·), (μ d : ℝ) = if m = l then (μ l : ℝ) else 0 := by
      intro m hm
      have hmD : m ∈ D := (mem_filter.mp hm).1
      have hlm : l ∣ m := (mem_filter.mp hm).2
      have hmP : m ∣ P := Nat.dvd_of_mem_divisors (mem_filter.mp hmD).1
      have hm_sq : Squarefree m := s.squarefree_of_dvd_prodPrimes hmP
      have hm0 : m ≠ 0 := hm_sq.ne_zero
      let k := m / l
      have hlk : l * k = m := Nat.mul_div_cancel' hlm
      have hcop : Nat.Coprime l k := (Nat.squarefree_mul_iff.mp (hlk.symm ▸ hm_sq)).1
      have hbij : ∑ d ∈ m.divisors.filter (l ∣ ·), (μ d : ℝ) = ∑ t ∈ k.divisors, (μ (l * t) : ℝ) := by
        refine Finset.sum_bij (fun d _ => d / l) ?_ ?_ ?_ ?_
        · intro d hd
          obtain ⟨hdm, hld⟩ := mem_filter.mp hd
          have hdm' := (Nat.mem_divisors.mp hdm).1
          have htk : d / l ∣ k := (mul_dvd_mul_iff_left hl_pos.ne').mp (by rw [Nat.mul_div_cancel' hld, hlk]; exact hdm')
          exact Nat.mem_divisors.mpr ⟨htk, by intro hk0; rw [hk0, mul_zero] at hlk; exact hm0 hlk.symm⟩
        · intro d1 hd1 d2 hd2 heq
          have h1 := Nat.mul_div_cancel' (mem_filter.mp hd1).2
          have h2 := Nat.mul_div_cancel' (mem_filter.mp hd2).2
          rw [← h1, ← h2, heq]
        · intro t ht
          have htk := (Nat.mem_divisors.mp ht).1
          refine ⟨l * t, mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨by rw [← hlk]; exact mul_dvd_mul_left l htk, hm0⟩, dvd_mul_right l t⟩,
            Nat.mul_div_cancel_left t hl_pos⟩
        · intro d hd; rw [Nat.mul_div_cancel' (mem_filter.mp hd).2]
      rw [hbij]
      have hmul_mu : ∀ t ∈ k.divisors, (μ (l * t) : ℝ) = (μ l : ℝ) * (μ t : ℝ) := by
        intro t ht
        have hlt_cop : Nat.Coprime l t := hcop.coprime_dvd_right (Nat.mem_divisors.mp ht).1
        have := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hlt_cop
        exact_mod_cast this
      rw [sum_congr rfl hmul_mu, ← Finset.mul_sum]
      have hmob : ∑ t ∈ k.divisors, (μ t : ℝ) = if k = 1 then 1 else 0 := by
        have h : ((μ : ArithmeticFunction ℤ) * (ζ : ArithmeticFunction ℤ)) k = (1 : ArithmeticFunction ℤ) k :=
          congrArg (fun F => F k) ArithmeticFunction.moebius_mul_coe_zeta
        rw [ArithmeticFunction.coe_mul_zeta_apply] at h
        have hR : ∑ t ∈ k.divisors, (μ t : ℝ) = (((1 : ArithmeticFunction ℤ) k : ℤ) : ℝ) := by exact_mod_cast h
        rw [hR]
        by_cases hk1 : k = 1
        · rw [hk1]; simp
        · simp [hk1, ArithmeticFunction.one_apply_ne hk1]
      rw [hmob]
      have hiff : m = l ↔ k = 1 := by
        constructor
        · intro hml; subst hml; exact Nat.div_self hl_pos
        · intro hk1; rw [← hlk, hk1, mul_one]
      by_cases hml : m = l
      · have hk1 : k = 1 := hiff.mp hml
        simp [hml, hk1]
      · have hk1 : k ≠ 1 := fun h => hml (hiff.mpr h)
        simp [hml, hk1]
    rw [sum_congr rfl (fun m hm => by rw [hinner m hm])]
    by_cases hlD : l ∈ D
    · have hl_mem : l ∈ D.filter (l ∣ ·) := mem_filter.mpr ⟨hlD, dvd_rfl⟩
      rw [Finset.sum_eq_single l]
      · simp; ring
      · intro m _ hml; simp [hml]
      · intro hnot; exact False.elim (hnot hl_mem)
    · have hzero : ∀ m ∈ D.filter (l ∣ ·), y m * (if m = l then (μ l : ℝ) else 0) = 0 := by
        intro m hm
        have hmne : m ≠ l := fun h => hlD (h ▸ (mem_filter.mp hm).1)
        simp [hmne]
      rw [Finset.sum_eq_zero hzero]
      dsimp only [y]; rw [if_neg hlD, mul_zero]
  -- Evaluate mainSum (lambdaSquared w) = 1 / S_sel
  have hmain : s.mainSum (lambdaSquared w) = 1 / S_sel := by
    rw [s.mainSum_lambdaSquared_eq_sum_mul_sum_sq w]
    have hrew : ∑ l ∈ divisors P, (s.selbergTerms l)⁻¹ *
          (∑ d ∈ divisors P, if l ∣ d then s.nu d * w d else 0) ^ 2 =
        ∑ l ∈ divisors P, (s.selbergTerms l)⁻¹ * ((μ l : ℝ) * y l) ^ 2 :=
      sum_congr rfl fun l hl => by rw [hdiag l hl]
    rw [hrew]
    have hmu_sq : ∀ l ∈ divisors P, ((μ l : ℝ) * y l) ^ 2 = (y l) ^ 2 := by
      intro l hl
      have hsq : Squarefree l := s.squarefree_of_dvd_prodPrimes (Nat.dvd_of_mem_divisors hl)
      rw [mul_pow, ArithmeticFunction.moebius_apply_of_squarefree hsq]
      have : (((-1 : ℤ) ^ cardFactors l : ℤ) : ℝ) ^ 2 = 1 := by
        push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [this, one_mul]
    rw [sum_congr rfl fun l hl => by rw [hmu_sq l hl]]
    have hD_sub : D ⊆ divisors P := filter_subset _ _
    have hsum_D : ∑ l ∈ divisors P, (s.selbergTerms l)⁻¹ * (y l) ^ 2 =
        ∑ l ∈ D, s.selbergTerms l / S_sel ^ 2 := by
      rw [← Finset.sum_subset hD_sub (fun l _ hlD => by dsimp only [y]; rw [if_neg hlD]; simp)]
      refine sum_congr rfl fun l hlD => ?_
      dsimp only [y]; rw [if_pos hlD]
      have hg0 : s.selbergTerms l ≠ 0 := (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hlD).1)).ne'
      field_simp [hg0, hS_pos.ne']
    rw [hsum_D, ← Finset.sum_div]
    change S_sel / S_sel ^ 2 = 1 / S_sel
    field_simp [hS_pos.ne']
  -- Prove |w d| ≤ 1 for all d
  have hw_abs : ∀ d, |w d| ≤ 1 := by
    intro d
    dsimp only [w]
    split_ifs with hdD
    · have hdP : d ∣ P := Nat.dvd_of_mem_divisors (mem_filter.mp hdD).1
      have hdZ : d ≤ Z := (mem_filter.mp hdD).2
      have hd_sq : Squarefree d := s.squarefree_of_dvd_prodPrimes hdP
      have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_sq.ne_zero
      have hnu_pos : 0 < s.nu d := s.nu_pos_of_dvd_prodPrimes hdP
      have hmu_abs : |(μ d : ℝ)| = 1 := by
        rw [ArithmeticFunction.moebius_apply_of_squarefree hd_sq]; push_cast; simp
      have hsum_nn : 0 ≤ ∑ l ∈ D.filter (d ∣ ·), y l := sum_nonneg fun l hl => by
        dsimp only [y]; rw [if_pos (mem_filter.mp hl).1]
        exact div_nonneg (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp (mem_filter.mp hl).1).1)).le hS_pos.le
      rw [abs_mul, abs_div, hmu_abs, abs_of_pos hnu_pos, abs_of_nonneg hsum_nn]
      have hsum_eq : ∑ l ∈ D.filter (d ∣ ·), y l =
          (s.selbergTerms d / S_sel) * ∑ m ∈ ((divisors P).filter (fun m => Nat.Coprime m d ∧ m ≤ Z / d)), s.selbergTerms m := by
        have h1 : ∑ l ∈ D.filter (d ∣ ·), y l =
            (∑ l ∈ D.filter (d ∣ ·), s.selbergTerms l) / S_sel := by
          rw [Finset.sum_div]; refine sum_congr rfl fun l hl => by dsimp only [y]; rw [if_pos (mem_filter.mp hl).1]
        rw [h1]
        have hbij : ∑ l ∈ D.filter (d ∣ ·), s.selbergTerms l =
            s.selbergTerms d * ∑ m ∈ (divisors P).filter (fun m => Nat.Coprime m d ∧ m ≤ Z / d), s.selbergTerms m := by
          rw [Finset.mul_sum]
          refine Finset.sum_bij (fun l _ => l / d) ?_ ?_ ?_ ?_
          · intro l hl
            obtain ⟨hlD, hdl⟩ := mem_filter.mp hl
            obtain ⟨hlP', hlZ⟩ := mem_filter.mp hlD
            have hlP : l ∣ P := Nat.dvd_of_mem_divisors hlP'
            have hl_sq : Squarefree l := s.squarefree_of_dvd_prodPrimes hlP
            have hmul : d * (l / d) = l := Nat.mul_div_cancel' hdl
            have hcop : Nat.Coprime d (l / d) := (Nat.squarefree_mul_iff.mp (hmul.symm ▸ hl_sq)).1
            refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd hdl).trans hlP, hP0⟩, hcop.symm, ?_⟩
            exact (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm, hmul]; exact hlZ)
          · intro l1 hl1 l2 hl2 heq
            have h1 := Nat.mul_div_cancel' (mem_filter.mp hl1).2
            have h2 := Nat.mul_div_cancel' (mem_filter.mp hl2).2
            rw [← h1, ← h2, heq]
          · intro m hm
            obtain ⟨hmP', hcop, hmZd⟩ := mem_filter.mp hm
            have hmP : m ∣ P := Nat.dvd_of_mem_divisors hmP'
            have hdmP : d * m ∣ P := hcop.symm.mul_dvd_of_dvd_of_dvd hdP hmP
            have hdmZ : d * m ≤ Z := by
              have := (Nat.le_div_iff_mul_le hd_pos).mp hmZd; linarith
            exact ⟨d * m, mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdmP, hP0⟩, hdmZ⟩, dvd_mul_right d m⟩,
              Nat.mul_div_cancel_left m hd_pos⟩
          · intro l hl
            obtain ⟨hlD, hdl⟩ := mem_filter.mp hl
            have hl_sq : Squarefree l := s.squarefree_of_dvd_prodPrimes (Nat.dvd_of_mem_divisors (mem_filter.mp hlD).1)
            have hmul : d * (l / d) = l := Nat.mul_div_cancel' hdl
            have hcop : Nat.Coprime d (l / d) := (Nat.squarefree_mul_iff.mp (hmul.symm ▸ hl_sq)).1
            conv_lhs => rw [← hmul]
            exact s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop
        rw [hbij]; ring
      rw [hsum_eq]
      -- Use sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv:
      -- (selbergTerms d / nu d) = ∑ k ∣ d, selbergTerms k
      have hdiv_g : s.selbergTerms d / s.nu d = ∑ k ∈ d.divisors, s.selbergTerms k := by
        have h := (s.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP).symm
        rw [div_eq_mul_inv, h, ← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP0 hdP]
      have hprod_le : (∑ k ∈ d.divisors, s.selbergTerms k) *
          (∑ m ∈ (divisors P).filter (fun m => Nat.Coprime m d ∧ m ≤ Z / d), s.selbergTerms m) ≤ S_sel := by
        let Mset := (divisors P).filter (fun m => Nat.Coprime m d ∧ m ≤ Z / d)
        rw [Finset.sum_mul]
        have hrew2 : (∑ k ∈ d.divisors, s.selbergTerms k * ∑ m ∈ Mset, s.selbergTerms m) =
            ∑ x ∈ d.divisors ×ˢ Mset, s.selbergTerms (x.1 * x.2) := by
          rw [Finset.sum_product]
          refine sum_congr rfl fun k hk => ?_
          rw [Finset.mul_sum]
          refine sum_congr rfl fun m hm => ?_
          have hkd : k ∣ d := Nat.dvd_of_mem_divisors hk
          have hcop : Nat.Coprime k m := ((mem_filter.mp hm).2.1.symm).coprime_dvd_left hkd
          exact (s.selbergTerms_isMultiplicative.map_mul_of_coprime hcop).symm
        rw [hrew2]
        have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) ((d.divisors ×ˢ Mset : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
          intro x hx y hy heq
          obtain ⟨hxk, hxm⟩ := mem_product.mp (Finset.mem_coe.mp hx)
          obtain ⟨hyk, hym⟩ := mem_product.mp (Finset.mem_coe.mp hy)
          have hkd1 : x.1 ∣ d := Nat.dvd_of_mem_divisors hxk
          have hkd2 : y.1 ∣ d := Nat.dvd_of_mem_divisors hyk
          have hcm1 : Nat.Coprime x.2 d := (mem_filter.mp hxm).2.1
          have hcm2 : Nat.Coprime y.2 d := (mem_filter.mp hym).2.1
          have hgcd1 : Nat.gcd (x.1 * x.2) d = x.1 := by
            rw [Nat.Coprime.gcd_mul_right_cancel x.1 hcm1, Nat.gcd_eq_left hkd1]
          have hgcd2 : Nat.gcd (y.1 * y.2) d = y.1 := by
            rw [Nat.Coprime.gcd_mul_right_cancel y.1 hcm2, Nat.gcd_eq_left hkd2]
          dsimp only at heq
          have hx1 : x.1 = y.1 := by rw [← hgcd1, heq, hgcd2]
          have hx1_pos : 0 < x.1 := Nat.pos_of_dvd_of_pos hkd1 hd_pos
          have hx2 : x.2 = y.2 := Nat.eq_of_mul_eq_mul_left hx1_pos (by rw [← hx1] at heq; exact heq)
          exact Prod.ext hx1 hx2
        have hmaps : (d.divisors ×ˢ Mset).image (fun x => x.1 * x.2) ⊆ D := by
          intro n hn
          obtain ⟨⟨k, m⟩, hkm, rfl⟩ := mem_image.mp hn
          obtain ⟨hk, hm⟩ := mem_product.mp hkm
          have hkd : k ∣ d := Nat.dvd_of_mem_divisors hk
          obtain ⟨hmP', hcop, hmZd⟩ := mem_filter.mp hm
          have hmP : m ∣ P := Nat.dvd_of_mem_divisors hmP'
          have hkmP : k * m ∣ P := ((hcop.symm).coprime_dvd_left hkd).mul_dvd_of_dvd_of_dvd (hkd.trans hdP) hmP
          have hk_le : k ≤ d := Nat.le_of_dvd hd_pos hkd
          have hkmZ : k * m ≤ Z := by
            calc k * m ≤ d * m := Nat.mul_le_mul_right m hk_le
              _ ≤ d * (Z / d) := Nat.mul_le_mul_left d hmZd
              _ ≤ Z := Nat.mul_div_le Z d
          exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hkmP, hP0⟩, hkmZ⟩
        calc ∑ x ∈ d.divisors ×ˢ Mset, s.selbergTerms (x.1 * x.2)
            = ∑ n ∈ (d.divisors ×ˢ Mset).image (fun x => x.1 * x.2), s.selbergTerms n :=
              (Finset.sum_image (f := s.selbergTerms) hinj).symm
          _ ≤ ∑ n ∈ D, s.selbergTerms n := sum_le_sum_of_subset_of_nonneg hmaps
              fun n hn _ => (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hn).1)).le
      have hlhs_eq : 1 / s.nu d * (s.selbergTerms d / S_sel *
            ∑ m ∈ (divisors P).filter (fun m => Nat.Coprime m d ∧ m ≤ Z / d), s.selbergTerms m) =
          (s.selbergTerms d / s.nu d *
            ∑ m ∈ (divisors P).filter (fun m => Nat.Coprime m d ∧ m ≤ Z / d), s.selbergTerms m) / S_sel := by ring
      rw [hlhs_eq, hdiv_g, div_le_one hS_pos]
      exact hprod_le
    · simp
  -- Bound errSum (lambdaSquared w) ≤ (∑ d ∈ D, R d) ^ 2
  have herr : s.errSum (lambdaSquared w) ≤ (∑ d ∈ D, R d) ^ 2 := by
    rw [errSum]
    have hstep1 : ∀ d ∈ divisors P,
        |lambdaSquared w d| * |s.rem d| ≤
          ∑ d1 ∈ D, ∑ d2 ∈ D, if d = d1.lcm d2 then |w d1| * |w d2| * |s.rem (d1.lcm d2)| else 0 := by
      intro d hd
      rw [lambdaSquared]
      have htri : |∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = d1.lcm d2 then w d1 * w d2 else 0| ≤
          ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, |if d = d1.lcm d2 then w d1 * w d2 else 0| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _)
      have hmul := mul_le_mul_of_nonneg_right htri (abs_nonneg (s.rem d))
      refine hmul.trans ?_
      rw [Finset.sum_mul]
      have hrew_in : (∑ d1 ∈ d.divisors, (∑ d2 ∈ d.divisors, |if d = d1.lcm d2 then w d1 * w d2 else 0|) * |s.rem d|) =
          ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = d1.lcm d2 then |w d1| * |w d2| * |s.rem (d1.lcm d2)| else 0 := by
        refine sum_congr rfl fun d1 _ => ?_
        rw [Finset.sum_mul]
        refine sum_congr rfl fun d2 _ => ?_
        split_ifs with heq
        · rw [heq, abs_mul]
        · simp
      rw [hrew_in]
      -- Terms with d1 ∉ D or d2 ∉ D vanish since w d1 = 0 or w d2 = 0
      have hdP : d ∣ P := Nat.dvd_of_mem_divisors hd
      have hsub1 : ∀ d1 ∈ d.divisors,
          (∑ d2 ∈ d.divisors, if d = d1.lcm d2 then |w d1| * |w d2| * |s.rem (d1.lcm d2)| else 0) ≤
          ∑ d2 ∈ D, if d = d1.lcm d2 then |w d1| * |w d2| * |s.rem (d1.lcm d2)| else 0 := by
        intro d1 _
        have h1 : (∑ d2 ∈ d.divisors, if d = d1.lcm d2 then |w d1| * |w d2| * |s.rem (d1.lcm d2)| else 0) =
            ∑ d2 ∈ d.divisors.filter (· ∈ D), if d = d1.lcm d2 then |w d1| * |w d2| * |s.rem (d1.lcm d2)| else 0 := by
          symm; refine Finset.sum_filter_of_ne fun d2 _ hne => ?_
          by_contra hnot; exact hne (by dsimp only [w]; rw [if_neg hnot]; simp)
        rw [h1]
        exact sum_le_sum_of_subset_of_nonneg (fun x hx => (mem_filter.mp hx).2) fun _ _ _ => by split_ifs <;> positivity
      calc (∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, (if d = d1.lcm d2 then |w d1| * |w d2| * |s.rem (d1.lcm d2)| else 0))
          ≤ ∑ d1 ∈ d.divisors, ∑ d2 ∈ D, (if d = d1.lcm d2 then |w d1| * |w d2| * |s.rem (d1.lcm d2)| else 0) :=
            sum_le_sum hsub1
        _ = ∑ d1 ∈ d.divisors.filter (· ∈ D), ∑ d2 ∈ D, (if d = d1.lcm d2 then |w d1| * |w d2| * |s.rem (d1.lcm d2)| else 0) := by
            symm; refine Finset.sum_filter_of_ne fun d1 _ hne => ?_
            by_contra hnot
            exact hne (Finset.sum_eq_zero fun d2 _ => by dsimp only [w]; rw [if_neg hnot]; simp)
        _ ≤ ∑ d1 ∈ D, ∑ d2 ∈ D, (if d = d1.lcm d2 then |w d1| * |w d2| * |s.rem (d1.lcm d2)| else 0) :=
            sum_le_sum_of_subset_of_nonneg (fun x hx => (mem_filter.mp hx).2) fun _ _ _ =>
              sum_nonneg fun _ _ => by split_ifs <;> positivity
    calc ∑ d ∈ divisors P, |lambdaSquared w d| * |s.rem d|
        ≤ ∑ d ∈ divisors P, ∑ d1 ∈ D, ∑ d2 ∈ D, if d = d1.lcm d2 then |w d1| * |w d2| * |s.rem (d1.lcm d2)| else 0 :=
          sum_le_sum hstep1
      _ = ∑ d1 ∈ D, ∑ d2 ∈ D, ∑ d ∈ divisors P, if d = d1.lcm d2 then |w d1| * |w d2| * |s.rem (d1.lcm d2)| else 0 := by
          rw [Finset.sum_comm]
          refine sum_congr rfl fun d1 _ => Finset.sum_comm
      _ = ∑ d1 ∈ D, ∑ d2 ∈ D, |w d1| * |w d2| * |s.rem (d1.lcm d2)| := by
          refine sum_congr rfl fun d1 hd1 => sum_congr rfl fun d2 hd2 => ?_
          have hlcm : d1.lcm d2 ∈ divisors P := Nat.mem_divisors.mpr
            ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors (mem_filter.mp hd1).1) (Nat.dvd_of_mem_divisors (mem_filter.mp hd2).1), hP0⟩
          rw [Finset.sum_ite_eq_of_mem' (divisors P) (d1.lcm d2) _ hlcm]
      _ ≤ ∑ d1 ∈ D, ∑ d2 ∈ D, R d1 * R d2 := by
          refine sum_le_sum fun d1 hd1 => sum_le_sum fun d2 hd2 => ?_
          have h1 : |w d1| * |w d2| ≤ 1 := by
            calc |w d1| * |w d2| ≤ 1 * 1 := mul_le_mul (hw_abs d1) (hw_abs d2) (abs_nonneg _) zero_le_one
              _ = 1 := one_mul 1
          calc |w d1| * |w d2| * |s.rem (d1.lcm d2)|
              ≤ 1 * (R d1 * R d2) := mul_le_mul h1 (hrem d1 hd1 d2 hd2) (abs_nonneg _) zero_le_one
            _ = R d1 * R d2 := one_mul _
      _ = (∑ d ∈ D, R d) ^ 2 := by
          rw [sq, Finset.sum_mul]
          exact sum_congr rfl fun _ _ => (Finset.mul_sum _ _ _).symm
  have hsift := s.siftedSum_le_mainSum_errSum_of_upperMoebius (lambdaSquared w) (upperMoebius_lambdaSquared w hw1)
  rw [hmain, mul_one_div] at hsift
  linarith

/- ### Section 3: Telescoping square-root bound & 2D Selberg sieve for prime pairs -/

/-- For any positive integer `m`, `∏_{p ∣ m, p > 2} p / (p - 1) ≤ √(2 * Nat.log 2 m + 3)`. -/
lemma telescoping_odd_prime_prod {m : ℕ} (hm : 1 ≤ m) :
    ∏ p ∈ m.primeFactors.filter (2 < ·), (p : ℝ) / ((p : ℝ) - 1) ≤
      Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3) := by
  let S := m.primeFactors.filter (2 < ·)
  let r := S.card
  -- Sort S into strictly increasing order: S.orderEmbOfFin rfl
  let f : Fin r ↪o ℕ := S.orderEmbOfFin rfl
  have hf_ge : ∀ i : Fin r, 2 * i.val + 3 ≤ f i := by
    intro ⟨i, hi⟩
    induction i with
    | zero =>
      have hmem : f ⟨0, hi⟩ ∈ S := S.orderEmbOfFin_mem rfl ⟨0, hi⟩
      have hgt2 : 2 < f ⟨0, hi⟩ := (mem_filter.mp hmem).2
      dsimp only; omega
    | succ j ih =>
      have hj : j < r := Nat.lt_of_succ_lt hi
      have hprev := ih hj
      have hlt : f ⟨j, hj⟩ < f ⟨j + 1, hi⟩ := f.strictMono (by exact Nat.lt_succ_self j)
      -- Both are odd primes, so their difference is at least 2!
      have hp1 : (f ⟨j, hj⟩).Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp (S.orderEmbOfFin_mem rfl ⟨j, hj⟩)).1
      have hp2 : (f ⟨j + 1, hi⟩).Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp (S.orderEmbOfFin_mem rfl ⟨j + 1, hi⟩)).1
      have hgt1 : 2 < f ⟨j, hj⟩ := (mem_filter.mp (S.orderEmbOfFin_mem rfl ⟨j, hj⟩)).2
      have hgt2 : 2 < f ⟨j + 1, hi⟩ := (mem_filter.mp (S.orderEmbOfFin_mem rfl ⟨j + 1, hi⟩)).2
      have hodd1 := hp1.odd_of_ne_two (by omega)
      have hodd2 := hp2.odd_of_ne_two (by omega)
      rcases hodd1 with ⟨a, ha⟩; rcases hodd2 with ⟨b, hb⟩
      dsimp only at hprev ⊢; omega
  have hprod_eq : ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) = ∏ i : Fin r, (f i : ℝ) / ((f i : ℝ) - 1) := by
    symm
    refine Finset.prod_bij (fun i _ => f i) (fun i _ => S.orderEmbOfFin_mem rfl i)
      (fun _ _ _ _ h => f.injective h) ?_ (fun _ _ => rfl)
    intro p hp
    have hmem : p ∈ Set.range f := by rw [Finset.range_orderEmbOfFin]; exact hp
    obtain ⟨i, rfl⟩ := hmem
    exact ⟨i, mem_univ i, rfl⟩
  have hsq_le : (∏ i : Fin r, (f i : ℝ) / ((f i : ℝ) - 1)) ^ 2 ≤ 2 * (r : ℝ) + 1 := by
    rw [← Finset.prod_pow]
    have hstep : ∀ i : Fin r, ((f i : ℝ) / ((f i : ℝ) - 1)) ^ 2 ≤
        (2 * (i.val : ℝ) + 3) / (2 * (i.val : ℝ) + 1) := by
      intro i
      have hge : (2 * (i.val : ℝ) + 3) ≤ (f i : ℝ) := by exact_mod_cast hf_ge i
      have h1 : (f i : ℝ) / ((f i : ℝ) - 1) ≤ (2 * (i.val : ℝ) + 3) / (2 * (i.val : ℝ) + 2) := by
        rw [div_le_div_iff₀ (by linarith) (by positivity)]
        nlinarith
      have h2 : ((2 * (i.val : ℝ) + 3) / (2 * (i.val : ℝ) + 2)) ^ 2 ≤
          (2 * (i.val : ℝ) + 3) / (2 * (i.val : ℝ) + 1) := by
        rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hnn : 0 ≤ (f i : ℝ) / ((f i : ℝ) - 1) := div_nonneg (by linarith) (by linarith)
      exact (pow_le_pow_left₀ hnn h1 2).trans h2
    have htel : ∀ n : ℕ, ∏ j ∈ range n, ((2 * (j : ℝ) + 3) / (2 * (j : ℝ) + 1)) = 2 * (n : ℝ) + 1 := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        rw [Finset.prod_range_succ, ih]
        push_cast
        have hpos : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
        field_simp [hpos]; ring
    calc ∏ i : Fin r, ((f i : ℝ) / ((f i : ℝ) - 1)) ^ 2
        ≤ ∏ i : Fin r, (2 * (i.val : ℝ) + 3) / (2 * (i.val : ℝ) + 1) :=
          prod_le_prod (fun _ _ => sq_nonneg _) (fun i _ => hstep i)
      _ = ∏ j ∈ range r, (2 * (j : ℝ) + 3) / (2 * (j : ℝ) + 1) :=
          Fin.prod_univ_eq_prod_range (fun j => (2 * (j : ℝ) + 3) / (2 * (j : ℝ) + 1)) r
      _ = 2 * (r : ℝ) + 1 := htel r
  have hr_le : r ≤ Nat.log 2 m := by
    have h2r : 2 ^ r ≤ m := by
      calc 2 ^ r = ∏ _p ∈ S, 2 := by simp [r]
        _ ≤ ∏ p ∈ S, p := prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le
        _ ≤ ∏ p ∈ m.primeFactors, p :=
            Finset.prod_le_prod_of_subset_of_one_le' (filter_subset _ _) fun p hp _ =>
              (Nat.prime_of_mem_primeFactors hp).one_le
        _ ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
    exact Nat.le_log_of_pow_le (by norm_num) h2r
  rw [hprod_eq, Real.le_sqrt (prod_nonneg fun i _ => by
    have h3 : 3 ≤ f i := by have := hf_ge i; omega
    have h3R : (3 : ℝ) ≤ f i := by exact_mod_cast h3
    exact div_nonneg (by linarith) (by linarith)) (by positivity)]
  have hrR : (r : ℝ) ≤ (Nat.log 2 m : ℝ) := by exact_mod_cast hr_le
  linarith

/-- Lower bound on `∑_{n ≤ w, gcd(n, M) = 1} 1/n` via Euler-product factorization over `M.primeFactors`. -/
lemma sum_coprime_inv_ge {M w : ℕ} (hM : 1 ≤ M) (_hw : 1 ≤ w) :
    Real.log ((w + 1 : ℕ) : ℝ) ≤
      (∏ p ∈ M.primeFactors, (p : ℝ) / ((p : ℝ) - 1)) *
        ∑ u ∈ (Icc 1 w).filter (fun u => Nat.Coprime u M), (1 : ℝ) / (u : ℝ) := by
  let S := M.primeFactors
  let A := (Icc 1 w).filter (fun d => ∀ p, p.Prime → p ∣ d → p ∈ S)
  let B := (Icc 1 w).filter (fun u => Nat.Coprime u M)
  have hsub : Icc 1 w ⊆ (A ×ˢ B).image (fun p => p.1 * p.2) := by
    intro n hn
    obtain ⟨hn1, hnw⟩ := mem_Icc.mp hn
    let d := ∏ p ∈ S, p ^ (n.factorization p)
    let u := n / d
    have hd_dvd : d ∣ n := by
      have haux : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) → ∏ p ∈ T, p ^ (n.factorization p) ∣ n := by
        intro T
        induction T using Finset.induction_on with
        | empty => intro _; simp
        | @insert a s ha ih =>
          intro hT
          rw [prod_insert ha]
          have h1' : a ^ n.factorization a ∣ n := Nat.ordProj_dvd n a
          have h2' : ∏ p ∈ s, p ^ n.factorization p ∣ n := ih (fun p hp => hT p (mem_insert_of_mem hp))
          have hca : Nat.Coprime (a ^ n.factorization a) (∏ p ∈ s, p ^ n.factorization p) :=
            Nat.coprime_prod_right_iff.mpr fun p hp =>
              ((Nat.coprime_primes (hT a (mem_insert_self a s)) (hT p (mem_insert_of_mem hp))).mpr
                (fun h => ha (h ▸ hp))).pow _ _
          exact hca.mul_dvd_of_dvd_of_dvd h1' h2'
      exact haux S (fun p hp => Nat.prime_of_mem_primeFactors hp)
    have hmul : d * u = n := Nat.mul_div_cancel' hd_dvd
    have hd_pos : 1 ≤ d := prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
    have hu_pos : 1 ≤ u := Nat.div_pos (Nat.le_of_dvd (by omega) hd_dvd) hd_pos
    have hd_S : ∀ p, p.Prime → p ∣ d → p ∈ S := by
      intro p hp hpd
      obtain ⟨q, hqS, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpd
      have hqp := Nat.prime_of_mem_primeFactors hqS
      have := (Nat.prime_dvd_prime_iff_eq hp hqp).mp (hp.dvd_of_dvd_pow hpq)
      exact this ▸ hqS
    have hu_cop : Nat.Coprime u M := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
      have hpu : p ∣ u := hpg.trans (Nat.gcd_dvd_left u M)
      have hpM : p ∣ M := hpg.trans (Nat.gcd_dvd_right u M)
      have hpS : p ∈ S := Nat.mem_primeFactors.mpr ⟨hp, hpM, by omega⟩
      have hpow : p ^ (n.factorization p) ∣ d := dvd_prod_of_mem (fun q => q ^ n.factorization q) hpS
      have hpow1 : p ^ (n.factorization p + 1) ∣ d * u := by
        rw [pow_succ]; exact mul_dvd_mul hpow hpu
      rw [hmul] at hpow1
      exact Nat.pow_succ_factorization_not_dvd (by omega : n ≠ 0) hp hpow1
    exact mem_image.mpr ⟨(d, u), mem_product.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hd_pos, (Nat.le_of_dvd (by omega) hd_dvd).trans hnw⟩, hd_S⟩,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨hu_pos, (Nat.div_le_self n d).trans hnw⟩, hu_cop⟩⟩, hmul⟩
  have hA_le : ∑ d ∈ A, (1 : ℝ) / (d : ℝ) ≤ ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := by
    have h1 := sum_smooth_rpow_le_euler S (fun p hp => Nat.prime_of_mem_primeFactors hp) zero_lt_one w
    have hrew1 : ∑ d ∈ A, (1 : ℝ) / (d : ℝ) = ∑ d ∈ A, (d : ℝ) ^ (-(1 : ℝ)) := by
      refine sum_congr rfl fun d _ => by rw [Real.rpow_neg_one, one_div]
    have hrew2 : ∏ p ∈ S, (1 - (p : ℝ) ^ (-(1 : ℝ)))⁻¹ = ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := by
      refine prod_congr rfl fun p hp => ?_
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      rw [Real.rpow_neg_one]; field_simp [show (p : ℝ) ≠ 0 by linarith, show (p : ℝ) - 1 ≠ 0 by linarith]
    rw [hrew1, ← hrew2]; exact h1
  calc Real.log ((w + 1 : ℕ) : ℝ)
      ≤ ∑ n ∈ Icc 1 w, (1 : ℝ) / (n : ℝ) := log_succ_le_harmonic w
    _ ≤ ∑ n ∈ (A ×ˢ B).image (fun p : ℕ × ℕ => p.1 * p.2), (1 : ℝ) / (n : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ x ∈ A ×ˢ B, (1 : ℝ) / ((x.1 * x.2 : ℕ) : ℝ) :=
        Finset.sum_image_le_of_nonneg fun _ _ => by positivity
    _ = (∑ d ∈ A, (1 : ℝ) / (d : ℝ)) * (∑ u ∈ B, (1 : ℝ) / (u : ℝ)) := by
        rw [Finset.sum_product, Finset.sum_mul]
        refine sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum]
        refine sum_congr rfl fun u _ => by push_cast; ring
    _ ≤ (∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1)) * (∑ u ∈ B, (1 : ℝ) / (u : ℝ)) :=
        mul_le_mul_of_nonneg_right hA_le (sum_nonneg fun _ _ => by positivity)

set_option maxHeartbeats 1200000 in
/-- 2-dimensional Selberg sieve upper bound for linear prime pairs `(q, a * q + c)`:
    for `a ≥ 1`, `c ≠ 0`, `Nat.Coprime a c.natAbs`, and `X ≥ 10000`,
    `# {q ∈ Icc 1 X : q.Prime ∧ 0 < a * q + c ∧ (a * q + c).toNat.Prime}`
    is at most `600 * √(2 * Nat.log 2 (a * c.natAbs) + 3) * X / (log X)^2 + X^(1/2) * (1 + log X)^2 + 4 * X^(1/4)`. -/
theorem two_dim_prime_pair_bound {a X : ℕ} {c : ℤ} (ha : 1 ≤ a) (hc : c ≠ 0)
    (hcop : Nat.Coprime a c.natAbs) (hX : 10000 ≤ X) :
    (((Icc 1 X).filter (fun q : ℕ => q.Prime ∧ 0 < (a : ℤ) * (q : ℤ) + c ∧
        ((a : ℤ) * (q : ℤ) + c).toNat.Prime)).card : ℝ) ≤
      600 * Real.sqrt (2 * (Nat.log 2 (a * c.natAbs) : ℝ) + 3) * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 +
      (X : ℝ) ^ ((1 : ℝ) / 2) * (1 + Real.log (X : ℝ)) ^ 2 + 4 * (X : ℝ) ^ ((1 : ℝ) / 4) := by
  classical
  have hXpos : (0 : ℝ) < X := by positivity
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  let m : ℕ := a * c.natAbs
  have hm_pos : 1 ≤ m := Nat.mul_pos ha (Int.natAbs_pos.mpr hc)
  let Z : ℕ := Nat.floor ((X : ℝ) ^ ((1 : ℝ) / 4))
  have hX14_ge : (10 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : (10000 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have h2 := Real.rpow_le_rpow (by norm_num) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h3 : (10000 : ℝ) ^ ((1 : ℝ) / 4) = 10 := by
      rw [show (10000 : ℝ) = (10 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  have hZ_ge10 : 10 ≤ Z := Nat.le_floor hX14_ge
  have hZ_le : (Z : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 4) := Nat.floor_le (by positivity)
  -- Support: Q0 = {q ∈ Icc 1 X : 0 < a * q + c} (actually an interval Icc L X!)
  let L : ℕ := if 0 ≤ c then 1 else c.natAbs / a + 1
  have hQ0_eq : (Icc 1 X).filter (fun q : ℕ => 0 < (a : ℤ) * (q : ℤ) + c) = Icc L X := by
    ext q; simp only [mem_filter, mem_Icc, L]
    split_ifs with hc0
    · constructor
      · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, by positivity⟩
    · have hc_neg : c = -((c.natAbs : ℤ)) := by omega
      constructor
      · rintro ⟨⟨h1, h2⟩, hpos⟩
        refine ⟨?_, h2⟩
        have hlt : c.natAbs < a * q := by omega
        have hle : c.natAbs / a < q := (Nat.div_lt_iff_lt_mul ha).mpr (by rw [mul_comm]; exact hlt)
        omega
      · rintro ⟨h1, h2⟩
        have hq1 : 1 ≤ q := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) h1
        have hgt : c.natAbs < a * q := by
          have hdm := Nat.div_add_mod c.natAbs a
          have hrem := Nat.mod_lt c.natAbs ha
          nlinarith
        exact ⟨⟨hq1, h2⟩, by omega⟩
  -- Handle empty interval L > X trivially
  by_cases hLX : X < L
  · have hemp : (Icc 1 X).filter (fun q : ℕ => q.Prime ∧ 0 < (a : ℤ) * (q : ℤ) + c ∧
        ((a : ℤ) * (q : ℤ) + c).toNat.Prime) = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro q hq
      have hmem : q ∈ Icc L X := hQ0_eq ▸ mem_filter.mpr ⟨(mem_filter.mp hq).1, (mem_filter.mp hq).2.2.1⟩
      have := mem_Icc.mp hmem; omega
    rw [hemp, card_empty, Nat.cast_zero]
    positivity
  push Not at hLX
  have hL1 : 1 ≤ L := by dsimp only [L]; split_ifs <;> exact Nat.succ_le_succ (Nat.zero_le _)
  -- Map f(q) = q * (a * q + c).toNat is strictly increasing on Icc L X, hence injective!
  let f : ℕ → ℕ := fun q => q * ((a : ℤ) * (q : ℤ) + c).toNat
  have hpos_on : ∀ q ∈ Icc L X, 0 < (a : ℤ) * (q : ℤ) + c := by
    intro q hq
    have hq' : q ∈ (Icc 1 X).filter (fun q : ℕ => 0 < (a : ℤ) * (q : ℤ) + c) := by rwa [hQ0_eq]
    exact (mem_filter.mp hq').2
  have hf_inj : Set.InjOn f (Icc L X : Set ℕ) := by
    intro q1 hq1 q2 hq2 heq
    have h1 := hpos_on q1 hq1; have h2 := hpos_on q2 hq2
    have hq1_pos : 0 < q1 := by have := (mem_Icc.mp hq1).1; omega
    have hq2_pos : 0 < q2 := by have := (mem_Icc.mp hq2).1; omega
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hval : ((a : ℤ) * (q1 : ℤ) + c).toNat < ((a : ℤ) * (q2 : ℤ) + c).toNat := by
        have : (a : ℤ) * (q1 : ℤ) + c < (a : ℤ) * (q2 : ℤ) + c := by nlinarith
        omega
      have : f q1 < f q2 := Nat.mul_lt_mul'' hlt hval
      omega
    · have hval : ((a : ℤ) * (q2 : ℤ) + c).toNat < ((a : ℤ) * (q1 : ℤ) + c).toNat := by
        have : (a : ℤ) * (q2 : ℤ) + c < (a : ℤ) * (q1 : ℤ) + c := by nlinarith
        omega
      have : f q2 < f q1 := Nat.mul_lt_mul'' hgt hval
      omega
  -- Odd primes ≤ Z
  let Pset : Finset ℕ := (Icc 3 Z).filter Nat.Prime
  let P : ℕ := ∏ p ∈ Pset, p
  have hP_sq : Squarefree P := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hpp
    -- Product of distinct primes is squarefree
    have hprime_prod : ∀ (T : Finset ℕ), (∀ q ∈ T, q.Prime) → Squarefree (∏ q ∈ T, q) := by
      intro T hT
      induction T using Finset.induction_on with
      | empty => simp
      | @insert x s hx ih =>
        rw [prod_insert hx]
        have hx_pr : x.Prime := hT x (mem_insert_self x s)
        have hs_sq := ih (fun q hq => hT q (mem_insert_of_mem hq))
        have hcop_xs : Nat.Coprime x (∏ q ∈ s, q) :=
          Nat.coprime_prod_right_iff.mpr fun q hq =>
            (Nat.coprime_primes hx_pr (hT q (mem_insert_of_mem hq))).mpr (fun h => hx (h ▸ hq))
        exact Nat.squarefree_mul_iff.mpr ⟨hcop_xs, hx_pr.squarefree, hs_sq⟩
    exact (Nat.squarefree_iff_prime_squarefree.mp (hprime_prod Pset fun q hq => (mem_filter.mp hq).2) p hp) hpp
  -- Define multiplicative ν(p) = 1/p if p ∣ m, 2/p if p ∤ m (for odd primes; 1/2 at 2)
  let nu : ArithmeticFunction ℝ :=
    ArithmeticFunction.prodPrimeFactors (fun p => if p = 2 then 1 / 2 else if p ∣ m then 1 / (p : ℝ) else 2 / (p : ℝ))
  have hnu_mult : nu.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · simp [nu, ArithmeticFunction.prodPrimeFactors_apply]
    · intro x y hxy
      by_cases hx0 : x = 0
      · subst hx0; simp [nu]
      by_cases hy0 : y = 0
      · subst hy0; simp [nu]
      simp only [nu, ArithmeticFunction.prodPrimeFactors_apply (mul_ne_zero hx0 hy0),
        ArithmeticFunction.prodPrimeFactors_apply hx0, ArithmeticFunction.prodPrimeFactors_apply hy0]
      rw [Nat.primeFactors_mul hx0 hy0, Finset.prod_union hxy.disjoint_primeFactors]
  have hnu_prime : ∀ p : ℕ, p.Prime →
      nu p = if p = 2 then 1 / 2 else if p ∣ m then 1 / (p : ℝ) else 2 / (p : ℝ) := by
    intro p hp
    dsimp only [nu]
    rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors, Finset.prod_singleton]
  have hP_prime_mem : ∀ p : ℕ, p.Prime → p ∣ P → 3 ≤ p ∧ p ≤ Z := by
    intro p hp hpP
    obtain ⟨q, hqP, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpP
    have hq_pr := (mem_filter.mp hqP).2
    have heq := (Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hpq
    subst heq; exact mem_Icc.mp (mem_filter.mp hqP).1
  -- Build the BoundingSieve instance
  let totalLen : ℕ := X - L + 1
  let bs : BoundingSieve := {
    support := (Icc L X).image f
    prodPrimes := P
    prodPrimes_squarefree := hP_sq
    weights := fun _ => 1
    weights_nonneg := fun _ => zero_le_one
    totalMass := (totalLen : ℝ)
    nu := nu
    nu_mult := hnu_mult
    nu_pos_of_prime := fun p hp hpP => by
      have ⟨hp3, _⟩ := hP_prime_mem p hp hpP
      rw [hnu_prime p hp, if_neg (by omega)]; split_ifs <;> positivity
    nu_lt_one_of_prime := fun p hp hpP => by
      have ⟨hp3, _⟩ := hP_prime_mem p hp hpP
      rw [hnu_prime p hp, if_neg (by omega)]
      have hpR3 : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      split_ifs <;> rw [div_lt_one (by linarith)] <;> linarith
  }
  -- Step 1: Bound the remainder |bs.rem d| ≤ d.divisors.card for squarefree d ∣ P!
  -- First, for every odd prime p ∣ P, count solutions of p ∣ f(q) in Fin p (= ZMod p):
  have hmod_count_prime : ∀ p : ℕ, p.Prime → 3 ≤ p →
      ((range p).filter (fun r : ℕ => (p : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c))).card =
        if p ∣ m then 1 else 2 := by
    intro p hp hp3
    have : Fact p.Prime := ⟨hp⟩
    have hiff : ∀ r ∈ range p, (p : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c) ↔
        r = 0 ∨ ((a : ZMod p) * (r : ZMod p) + (c : ZMod p) = 0) := by
      intro r hr
      have hrp : r < p := mem_range.mp hr
      rw [Int.prime_iff_natAbs_prime.mpr (by simpa using hp) |>.dvd_mul]
      constructor
      · rintro (h1 | h2)
        · left
          have : p ∣ r := Int.natCast_dvd_natCast.mp h1
          exact Nat.eq_zero_of_dvd_of_lt this hrp
        · right
          have h0 : (((a : ℤ) * (r : ℤ) + c : ℤ) : ZMod p) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h2
          push_cast at h0; exact h0
      · rintro (rfl | h2)
        · left; simp
        · right
          apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
          push_cast; exact h2
    split_ifs with hpm
    · -- p ∣ m = a * c.natAbs: only r = 0 works!
      have hfilt : (range p).filter (fun r : ℕ => (p : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c)) = {0} := by
        ext r; simp only [mem_filter, mem_singleton]
        constructor
        · intro ⟨hr, hd⟩
          rcases (hiff r hr).mp hd with rfl | h2
          · rfl
          · rcases hp.dvd_mul.mp hpm with hpa | hpc
            · exfalso
              have ha0 : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff a p).mpr hpa
              rw [ha0, zero_mul, zero_add] at h2
              have hpc' : (p : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h2
              have hpc_nat : p ∣ c.natAbs := Int.natCast_dvd.mp hpc'
              have := Nat.dvd_gcd hpa hpc_nat
              rw [hcop.gcd_eq_one] at this
              exact hp.not_dvd_one this
            · have hc0 : (c : ZMod p) = 0 :=
                (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mpr (Int.natCast_dvd.mpr hpc)
              have hpa : ¬ p ∣ a := fun h => hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h hpc)
              have ha_ne : (a : ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff a p).mp hpa
              rw [hc0, add_zero] at h2
              have hr0 : (r : ZMod p) = 0 := (mul_eq_zero.mp h2).resolve_left ha_ne
              exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff r p).mp hr0) (mem_range.mp hr)
        · rintro rfl; exact ⟨mem_range.mpr hp.pos, by simp⟩
      rw [hfilt, card_singleton]
    · -- p ∤ m: exactly 2 solutions: r = 0 and r = (-(c : ZMod p) * (a : ZMod p)⁻¹).val
      have hpa : ¬ p ∣ a := fun h => hpm (dvd_mul_of_dvd_left h _)
      have hpc : ¬ p ∣ c.natAbs := fun h => hpm (dvd_mul_of_dvd_right h _)
      have ha_ne : (a : ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff a p).mp hpa
      have hc_ne : (c : ZMod p) ≠ 0 := fun h => hpc (Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h))
      let z0 : ZMod p := -(c : ZMod p) * (a : ZMod p)⁻¹
      have hz0_ne : z0 ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hc_ne) (inv_ne_zero ha_ne)
      let r1 : ℕ := z0.val
      have hr1_lt : r1 < p := z0.val_lt
      have hr1_ne0 : r1 ≠ 0 := fun h => hz0_ne (by rw [← ZMod.natCast_zmod_val z0]; simp [r1, h])
      have hfilt : (range p).filter (fun r : ℕ => (p : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c)) = {0, r1} := by
        ext r; simp only [mem_filter, mem_insert, mem_singleton]
        constructor
        · intro ⟨hr, hd⟩
          rcases (hiff r hr).mp hd with rfl | h2
          · exact Or.inl rfl
          · right
            have hrz : (r : ZMod p) = z0 := by
              dsimp only [z0]
              have h1 : (a : ZMod p) * (r : ZMod p) = -(c : ZMod p) := eq_neg_of_add_eq_zero_left h2
              calc (r : ZMod p) = (a : ZMod p)⁻¹ * ((a : ZMod p) * (r : ZMod p)) := by rw [← mul_assoc, inv_mul_cancel₀ ha_ne, one_mul]
                _ = -(c : ZMod p) * (a : ZMod p)⁻¹ := by rw [h1, mul_comm]
            have hval := congrArg ZMod.val hrz
            rwa [ZMod.val_natCast_of_lt (mem_range.mp hr)] at hval
        · rintro (rfl | hr1)
          · exact ⟨mem_range.mpr hp.pos, by simp⟩
          · rw [hr1]
            refine ⟨mem_range.mpr hr1_lt, (hiff r1 (mem_range.mpr hr1_lt)).mpr (Or.inr ?_)⟩
            have h1 : (r1 : ZMod p) = z0 := ZMod.natCast_zmod_val z0
            rw [h1]; dsimp only [z0]
            rw [mul_comm (-(c : ZMod p)), ← mul_assoc, mul_inv_cancel₀ ha_ne, one_mul, neg_add_cancel]
      rw [hfilt, card_pair hr1_ne0.symm]
  -- By CRT induction, for any squarefree d ∣ P, #{r ∈ range d : (d : ℤ) ∣ r * (a * r + c)} = d * nu d
  have hmod_count_dvd : ∀ d : ℕ, d ∣ P →
      (((range d).filter (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c))).card : ℝ) =
        (d : ℝ) * nu d := by
    intro d hdP
    have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP hP_sq
    have hd_eq : d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hd_sq).symm
    -- Induct on d.primeFactors
    have haux : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ 3 ≤ p) →
        let D' := ∏ p ∈ S, p
        (((range D').filter (fun r : ℕ => (D' : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c))).card : ℝ) =
          (D' : ℝ) * nu D' := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _; simp [hnu_mult.map_one]
      | @insert p s hp ih =>
        intro hS
        have ⟨hpr, hp3⟩ := hS p (mem_insert_self p s)
        have hs_pr : ∀ q ∈ s, q.Prime ∧ 3 ≤ q := fun q hq => hS q (mem_insert_of_mem hq)
        set D0 := ∏ q ∈ s, q
        have hcop_pD0 : Nat.Coprime p D0 :=
          Nat.coprime_prod_right_iff.mpr fun q hq =>
            (Nat.coprime_primes hpr (hs_pr q hq).1).mpr (fun h => hp (h ▸ hq))
        have hD0_pos : 0 < D0 := prod_pos fun q hq => (hs_pr q hq).1.pos
        have hprod_eq : ∏ q ∈ insert p s, q = p * D0 := prod_insert hp
        dsimp only
        rw [hprod_eq]
        -- Bijection via CRT between solutions mod (p * D0) and pairs of solutions mod p and mod D0
        let Sp := (range p).filter (fun r : ℕ => (p : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c))
        let SD := (range D0).filter (fun r : ℕ => (D0 : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c))
        let Sboth := (range (p * D0)).filter (fun r : ℕ => ((p * D0 : ℕ) : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c))
        have hcard_prod : Sboth.card = Sp.card * SD.card := by
          rw [← Finset.card_product]
          refine Finset.card_bij (fun r _ => (r % p, r % D0)) ?_ ?_ ?_
          · intro r hr
            obtain ⟨hr_lt, hr_dvd⟩ := mem_filter.mp hr
            have hd1 : (p : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c) :=
              dvd_trans (by exact_mod_cast dvd_mul_right p D0) hr_dvd
            have hd2 : (D0 : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c) :=
              dvd_trans (by exact_mod_cast dvd_mul_left D0 p) hr_dvd
            have hcong_p : ((r % p : ℕ) : ℤ) ≡ (r : ℤ) [ZMOD p] :=
              Int.natCast_modEq_iff.mpr (Nat.mod_modEq r p)
            have hcong_D : ((r % D0 : ℕ) : ℤ) ≡ (r : ℤ) [ZMOD D0] :=
              Int.natCast_modEq_iff.mpr (Nat.mod_modEq r D0)
            have hp_sol : (p : ℤ) ∣ ((r % p : ℕ) : ℤ) * ((a : ℤ) * ((r % p : ℕ) : ℤ) + c) := by
              have h1 := ((hcong_p.mul_left (a : ℤ)).add_right c).mul_left ((r % p : ℕ) : ℤ)
              have h2 := hcong_p.mul_right ((a : ℤ) * (r : ℤ) + c)
              exact (Int.modEq_zero_iff_dvd.mp ((h1.trans h2).trans (Int.modEq_zero_iff_dvd.mpr hd1)))
            have hD_sol : (D0 : ℤ) ∣ ((r % D0 : ℕ) : ℤ) * ((a : ℤ) * ((r % D0 : ℕ) : ℤ) + c) := by
              have h1 := ((hcong_D.mul_left (a : ℤ)).add_right c).mul_left ((r % D0 : ℕ) : ℤ)
              have h2 := hcong_D.mul_right ((a : ℤ) * (r : ℤ) + c)
              exact (Int.modEq_zero_iff_dvd.mp ((h1.trans h2).trans (Int.modEq_zero_iff_dvd.mpr hd2)))
            exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt r hpr.pos), hp_sol⟩,
              mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt r hD0_pos), hD_sol⟩⟩
          · intro r1 hr1 r2 hr2 heq
            have hp1 : r1 ≡ r2 [MOD p] := congrArg Prod.fst heq
            have hD1 : r1 ≡ r2 [MOD D0] := congrArg Prod.snd heq
            have hboth : r1 ≡ r2 [MOD p * D0] := (Nat.modEq_and_modEq_iff_modEq_mul hcop_pD0).mp ⟨hp1, hD1⟩
            change r1 % (p * D0) = r2 % (p * D0) at hboth
            rwa [Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hr1).1),
              Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hr2).1)] at hboth
          · intro ⟨r1, r2⟩ hpair
            obtain ⟨hr1, hr2⟩ := mem_product.mp hpair
            let crt := Nat.chineseRemainder hcop_pD0 r1 r2
            let r := crt.val % (p * D0)
            have hr_lt : r < p * D0 := Nat.mod_lt _ (Nat.mul_pos hpr.pos hD0_pos)
            have hrmodp : r % p = r1 := by
              have h1 : r ≡ crt.val [MOD p] := (Nat.mod_modEq crt.val (p * D0)).of_dvd (dvd_mul_right p D0)
              have h2 : r ≡ r1 [MOD p] := h1.trans crt.prop.1
              change r % p = r1 % p at h2
              rwa [Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hr1).1)] at h2
            have hrmodD : r % D0 = r2 := by
              have h1 : r ≡ crt.val [MOD D0] := (Nat.mod_modEq crt.val (p * D0)).of_dvd (dvd_mul_left D0 p)
              have h2 : r ≡ r2 [MOD D0] := h1.trans crt.prop.2
              change r % D0 = r2 % D0 at h2
              rwa [Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hr2).1)] at h2
            have hcong_p : (r : ℤ) ≡ (r1 : ℤ) [ZMOD p] :=
              Int.natCast_modEq_iff.mpr (by rw [← hrmodp]; exact (Nat.mod_modEq r p).symm)
            have hcong_D : (r : ℤ) ≡ (r2 : ℤ) [ZMOD D0] :=
              Int.natCast_modEq_iff.mpr (by rw [← hrmodD]; exact (Nat.mod_modEq r D0).symm)
            have hp_sol : (p : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c) := by
              have h1 := ((hcong_p.mul_left (a : ℤ)).add_right c).mul_left (r : ℤ)
              have h2 := hcong_p.mul_right ((a : ℤ) * (r1 : ℤ) + c)
              exact Int.modEq_zero_iff_dvd.mp ((h1.trans h2).trans (Int.modEq_zero_iff_dvd.mpr (mem_filter.mp hr1).2))
            have hD_sol : (D0 : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c) := by
              have h1 := ((hcong_D.mul_left (a : ℤ)).add_right c).mul_left (r : ℤ)
              have h2 := hcong_D.mul_right ((a : ℤ) * (r2 : ℤ) + c)
              exact Int.modEq_zero_iff_dvd.mp ((h1.trans h2).trans (Int.modEq_zero_iff_dvd.mpr (mem_filter.mp hr2).2))
            have hcopZ : IsCoprime (p : ℤ) (D0 : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop_pD0
            have hboth_dvd : ((p * D0 : ℕ) : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c) := by
              rw [Nat.cast_mul]; exact hcopZ.mul_dvd hp_sol hD_sol
            exact ⟨r, mem_filter.mpr ⟨mem_range.mpr hr_lt, hboth_dvd⟩, Prod.ext hrmodp hrmodD⟩
        change (Sboth.card : ℝ) = ((p * D0 : ℕ) : ℝ) * nu (p * D0)
        rw [hcard_prod, Nat.cast_mul, hnu_mult.map_mul_of_coprime hcop_pD0, Nat.cast_mul, ih hs_pr]
        have hp_card : (Sp.card : ℝ) = (p : ℝ) * nu p := by
          have hp_ne2 : p ≠ 2 := by omega
          dsimp only [Sp]; rw [hmod_count_prime p hpr hp3, hnu_prime p hpr, if_neg hp_ne2]
          have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
          split_ifs <;> push_cast <;> field_simp [hp0]
        rw [hp_card]; ring
    rw [hd_eq]
    exact haux d.primeFactors fun p hp =>
      ⟨Nat.prime_of_mem_primeFactors hp, (hP_prime_mem p (Nat.prime_of_mem_primeFactors hp)
        ((Nat.dvd_of_mem_primeFactors hp).trans hdP)).1⟩
  -- Count solutions in Icc L X for any d ∣ P: |bs.rem d| ≤ d * nu d ≤ d.divisors.card
  have hrem_bd : ∀ d : ℕ, d ∣ P → |bs.rem d| ≤ (d.divisors.card : ℝ) := by
    intro d hdP
    have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP hP_sq
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_sq.ne_zero
    let Sols := (range d).filter (fun r : ℕ => (d : ℤ) ∣ (r : ℤ) * ((a : ℤ) * (r : ℤ) + c))
    have hmult_eq : bs.multSum d = (((Icc L X).filter (fun q => q % d ∈ Sols)).card : ℝ) := by
      dsimp only [bs, BoundingSieve.multSum]
      rw [Finset.sum_image hf_inj, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 2; ext q; simp only [mem_filter, Sols, mem_range]
      constructor
      · rintro ⟨hq, hfq⟩
        refine ⟨hq, Nat.mod_lt q hd_pos, ?_⟩
        have hpos_q := hpos_on q hq
        have hfqZ : (d : ℤ) ∣ (q : ℤ) * ((a : ℤ) * (q : ℤ) + c) := by
          have h1 : ((f q : ℕ) : ℤ) = (q : ℤ) * ((a : ℤ) * (q : ℤ) + c) := by
            dsimp only [f]; rw [Nat.cast_mul, Int.toNat_of_nonneg hpos_q.le]
          rw [← h1]; exact Int.natCast_dvd_natCast.mpr hfq
        have hcong : ((q % d : ℕ) : ℤ) ≡ (q : ℤ) [ZMOD d] :=
          Int.natCast_modEq_iff.mpr (Nat.mod_modEq q d)
        have h1 := ((hcong.mul_left (a : ℤ)).add_right c).mul_left ((q % d : ℕ) : ℤ)
        have h2 := hcong.mul_right ((a : ℤ) * (q : ℤ) + c)
        exact Int.modEq_zero_iff_dvd.mp ((h1.trans h2).trans (Int.modEq_zero_iff_dvd.mpr hfqZ))
      · rintro ⟨hq, _, hdvd⟩
        refine ⟨hq, ?_⟩
        have hpos_q := hpos_on q hq
        have hcong : (q : ℤ) ≡ ((q % d : ℕ) : ℤ) [ZMOD d] :=
          Int.natCast_modEq_iff.mpr (Nat.mod_modEq q d).symm
        have h1 := ((hcong.mul_left (a : ℤ)).add_right c).mul_left (q : ℤ)
        have h2 := hcong.mul_right ((a : ℤ) * ((q % d : ℕ) : ℤ) + c)
        have hfqZ : (d : ℤ) ∣ (q : ℤ) * ((a : ℤ) * (q : ℤ) + c) :=
          Int.modEq_zero_iff_dvd.mp ((h1.trans h2).trans (Int.modEq_zero_iff_dvd.mpr hdvd))
        have h1' : ((f q : ℕ) : ℤ) = (q : ℤ) * ((a : ℤ) * (q : ℤ) + c) := by
          dsimp only [f]; rw [Nat.cast_mul, Int.toNat_of_nonneg hpos_q.le]
        rw [← h1'] at hfqZ
        exact Int.natCast_dvd_natCast.mp hfqZ
    -- For each residue r ∈ Sols, #{q ∈ Icc L X : q % d = r} is within 1 of totalLen / d
    have hres_count : ∀ r ∈ Sols,
        ((totalLen / d : ℕ) : ℝ) ≤ (((Icc L X).filter (fun q => q % d = r)).card : ℝ) ∧
        (((Icc L X).filter (fun q => q % d = r)).card : ℝ) ≤ ((totalLen / d + 1 : ℕ) : ℝ) := by
      intro r hr
      have hrd : r < d := mem_range.mp (mem_filter.mp hr).1
      -- Partition Icc L X into totalLen / d complete blocks of size d plus a tail of size totalLen % d < d
      let Q := totalLen / d
      let s0 := (Icc L X).filter (fun q => q % d = r)
      have hlo : Q ≤ s0.card := by
        -- Each block [L + t*d, L + (t+1)*d) for t ∈ range Q has a unique element ≡ r [MOD d]
        let pick : ℕ → ℕ := fun t => L + t * d + (r + d - (L + t * d) % d) % d
        have hmaps : ∀ t ∈ range Q, pick t ∈ s0 := by
          intro t ht
          have htQ : t < Q := mem_range.mp ht
          have hrem_lt : (r + d - (L + t * d) % d) % d < d := Nat.mod_lt _ hd_pos
          have hlt_X : pick t ≤ X := by
            have h1 : (t + 1) * d ≤ Q * d := Nat.mul_le_mul_right d htQ
            have h2 : Q * d ≤ totalLen := Nat.div_mul_le_self totalLen d
            have h3 : t * d + d ≤ totalLen := by linarith
            dsimp only [pick, totalLen] at h3 ⊢
            omega
          have hmod : pick t % d = r := by
            dsimp only [pick]
            have hmod_le : (L + t * d) % d < d := Nat.mod_lt _ hd_pos
            calc (L + t * d + (r + d - (L + t * d) % d) % d) % d
                = ((L + t * d) % d + ((r + d - (L + t * d) % d) % d) % d) % d := Nat.add_mod _ _ _
              _ = ((L + t * d) % d + (r + d - (L + t * d) % d) % d) % d := by rw [Nat.mod_mod]
              _ = (((L + t * d) % d) % d + (r + d - (L + t * d) % d) % d) % d := by rw [Nat.mod_mod]
              _ = ((L + t * d) % d + (r + d - (L + t * d) % d)) % d := (Nat.add_mod _ _ _).symm
              _ = (r + d) % d := by congr 1; omega
              _ = r := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hrd]
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by dsimp only [pick]; omega, hlt_X⟩, hmod⟩
        have hinj : Set.InjOn pick (range Q : Set ℕ) := by
          intro t1 _ t2 _ heq
          dsimp only [pick] at heq
          have h1 : (r + d - (L + t1 * d) % d) % d < d := Nat.mod_lt _ hd_pos
          have h2 : (r + d - (L + t2 * d) % d) % d < d := Nat.mod_lt _ hd_pos
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hmul : (t1 + 1) * d ≤ t2 * d := Nat.mul_le_mul_right d hlt
            have hmul' : t1 * d + d ≤ t2 * d := by linarith
            omega
          · have hmul : (t2 + 1) * d ≤ t1 * d := Nat.mul_le_mul_right d hgt
            have hmul' : t2 * d + d ≤ t1 * d := by linarith
            omega
        calc Q = (range Q).card := (card_range Q).symm
          _ = ((range Q).image pick).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ s0.card := card_le_card (Finset.image_subset_iff.mpr hmaps)
      have hhi : s0.card ≤ Q + 1 := by
        have hmaps : ∀ q ∈ s0, (q - L) / d ∈ range (Q + 1) := by
          intro q hq
          have hqI := mem_Icc.mp (mem_filter.mp hq).1
          rw [mem_range]
          have : q - L < totalLen := by dsimp only [totalLen]; omega
          have : (q - L) / d ≤ Q := Nat.div_le_div_right this.le
          omega
        have hinj : Set.InjOn (fun q => (q - L) / d) (s0 : Set ℕ) := by
          intro q1 hq1 q2 hq2 heq
          have hI1 := mem_Icc.mp (mem_filter.mp hq1).1
          have hI2 := mem_Icc.mp (mem_filter.mp hq2).1
          have hm1 : q1 % d = r := (mem_filter.mp hq1).2
          have hm2 : q2 % d = r := (mem_filter.mp hq2).2
          have hdiv1 := Nat.div_add_mod (q1 - L) d
          have hdiv2 := Nat.div_add_mod (q2 - L) d
          have hmod_eq : (q1 - L) % d = (q2 - L) % d := by
            have hc : q1 ≡ q2 [MOD d] := by change q1 % d = q2 % d; rw [hm1, hm2]
            have hc' : q1 - L ≡ q2 - L [MOD d] := by
              apply Nat.ModEq.add_right_cancel' L
              rw [Nat.sub_add_cancel hI1.1, Nat.sub_add_cancel hI2.1]; exact hc
            exact hc'
          dsimp only at heq
          have hsub_eq : q1 - L = q2 - L := by rw [← hdiv1, ← hdiv2, heq, hmod_eq]
          omega
        calc s0.card = (s0.image (fun q => (q - L) / d)).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ (range (Q + 1)).card := card_le_card (Finset.image_subset_iff.mpr hmaps)
          _ = Q + 1 := card_range _
      exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
    have hfib : (((Icc L X).filter (fun q => q % d ∈ Sols)).card : ℝ) =
        ∑ r ∈ Sols, (((Icc L X).filter (fun q => q % d = r)).card : ℝ) := by
      have hnat : ((Icc L X).filter (fun q => q % d ∈ Sols)).card =
          ∑ r ∈ Sols, ((Icc L X).filter (fun q => q % d = r)).card := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to (g := fun q => q % d) (t := Sols)
          (fun q hq => (mem_filter.mp hq).2)]
        refine sum_congr rfl fun r hr => ?_
        rw [Finset.card_eq_sum_ones]
        refine sum_congr ?_ fun _ _ => rfl
        ext q; simp only [mem_filter]
        exact ⟨fun ⟨⟨hq, _⟩, heq⟩ => ⟨hq, heq⟩, fun ⟨hq, heq⟩ => ⟨⟨hq, heq ▸ hr⟩, heq⟩⟩
      exact_mod_cast hnat
    have hsol_card : (Sols.card : ℝ) = (d : ℝ) * nu d := hmod_count_dvd d hdP
    have hQ_lo : (totalLen : ℝ) / (d : ℝ) - 1 ≤ ((totalLen / d : ℕ) : ℝ) := by
      have hdm : d * (totalLen / d) + totalLen % d = totalLen := Nat.div_add_mod totalLen d
      have hrem_lt : totalLen % d < d := Nat.mod_lt totalLen hd_pos
      have hdposR : (0 : ℝ) < d := by exact_mod_cast hd_pos
      have h1 : (totalLen : ℝ) < (d : ℝ) * (((totalLen / d : ℕ) : ℝ) + 1) := by
        have : totalLen < d * (totalLen / d + 1) := by nlinarith
        exact_mod_cast this
      rw [sub_le_iff_le_add, div_le_iff₀ hdposR]; linarith
    have hQ_hi : ((totalLen / d + 1 : ℕ) : ℝ) ≤ (totalLen : ℝ) / (d : ℝ) + 1 := by
      have h1 : ((totalLen / d : ℕ) : ℝ) ≤ (totalLen : ℝ) / (d : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hd_pos : (0 : ℝ) < d)]
        exact_mod_cast Nat.div_mul_le_self totalLen d
      push_cast; linarith
    have hrem_sols : |bs.rem d| ≤ (Sols.card : ℝ) := by
      dsimp only [BoundingSieve.rem]
      rw [hmult_eq, hfib]
      change |∑ r ∈ Sols, (((Icc L X).filter (fun q => q % d = r)).card : ℝ) - nu d * (totalLen : ℝ)| ≤ (Sols.card : ℝ)
      have hmain_eq : nu d * (totalLen : ℝ) = (Sols.card : ℝ) * ((totalLen : ℝ) / (d : ℝ)) := by
        rw [hsol_card]; field_simp [show (d : ℝ) ≠ 0 by positivity]
      rw [hmain_eq]
      have hsum_lo : (Sols.card : ℝ) * ((totalLen : ℝ) / (d : ℝ) - 1) ≤
          ∑ r ∈ Sols, (((Icc L X).filter (fun q => q % d = r)).card : ℝ) := by
        calc (Sols.card : ℝ) * ((totalLen : ℝ) / (d : ℝ) - 1)
            = ∑ _r ∈ Sols, ((totalLen : ℝ) / (d : ℝ) - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ _ := sum_le_sum fun r hr => hQ_lo.trans (hres_count r hr).1
      have hsum_hi : ∑ r ∈ Sols, (((Icc L X).filter (fun q => q % d = r)).card : ℝ) ≤
          (Sols.card : ℝ) * ((totalLen : ℝ) / (d : ℝ) + 1) := by
        calc _ ≤ ∑ _r ∈ Sols, ((totalLen : ℝ) / (d : ℝ) + 1) := sum_le_sum fun r hr => (hres_count r hr).2.trans hQ_hi
          _ = (Sols.card : ℝ) * ((totalLen : ℝ) / (d : ℝ) + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
      rw [abs_le]; constructor <;> nlinarith
    have hsol_le_tau : (Sols.card : ℝ) ≤ (d.divisors.card : ℝ) := by
      -- Since d is squarefree, d.divisors.card = 2^(d.primeFactors.card), and d * nu d = ∏_{p ∣ d} (1 or 2) ≤ 2^(d.primeFactors.card)!
      rw [hsol_card]
      have hd_eq : d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hd_sq).symm
      have hprod_nu_eq : nu d = ∏ p ∈ d.primeFactors, nu p := by
        dsimp only [nu]
        rw [ArithmeticFunction.prodPrimeFactors_apply hd_sq.ne_zero]
        exact prod_congr rfl fun p hp => (hnu_prime p (Nat.prime_of_mem_primeFactors hp)).symm
      have hprod_nu : (d : ℝ) * nu d = ∏ p ∈ d.primeFactors, ((p : ℝ) * nu p) := by
        calc (d : ℝ) * nu d
            = ((∏ p ∈ d.primeFactors, p : ℕ) : ℝ) * ∏ p ∈ d.primeFactors, nu p :=
              congrArg₂ (· * ·) (by exact_mod_cast hd_eq) hprod_nu_eq
          _ = (∏ p ∈ d.primeFactors, (p : ℝ)) * ∏ p ∈ d.primeFactors, nu p := by rw [Nat.cast_prod]
          _ = ∏ p ∈ d.primeFactors, ((p : ℝ) * nu p) := (Finset.prod_mul_distrib).symm
      have hle2 : ∏ p ∈ d.primeFactors, ((p : ℝ) * nu p) ≤ (2 : ℝ) ^ d.primeFactors.card := by
        calc ∏ p ∈ d.primeFactors, ((p : ℝ) * nu p)
            ≤ ∏ _p ∈ d.primeFactors, (2 : ℝ) := by
              refine prod_le_prod (fun p hp => mul_nonneg (Nat.cast_nonneg _)
                (bs.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans hdP)).le) ?_
              intro p hp
              have hpr := Nat.prime_of_mem_primeFactors hp
              have ⟨hp3, _⟩ := hP_prime_mem p hpr ((Nat.dvd_of_mem_primeFactors hp).trans hdP)
              rw [hnu_prime p hpr, if_neg (by omega)]
              have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
              split_ifs <;> field_simp [hp0] <;> norm_num
          _ = (2 : ℝ) ^ d.primeFactors.card := by simp
      have htau_eq : d.divisors.card = 2 ^ d.primeFactors.card := by
        rw [Nat.card_divisors hd_sq.ne_zero]
        have h1 : ∀ p ∈ d.primeFactors, d.factorization p + 1 = 2 := by
          intro p hp
          have hpr := Nat.prime_of_mem_primeFactors hp
          have hpos : 1 ≤ d.factorization p := Nat.Prime.factorization_pos_of_dvd hpr hd_sq.ne_zero (Nat.dvd_of_mem_primeFactors hp)
          have hle1 : d.factorization p ≤ 1 := by
            by_contra hgt
            have h2 : p * p ∣ d := by
              rw [← sq]; exact (Nat.pow_dvd_pow p (by omega : 2 ≤ d.factorization p)).trans (Nat.ordProj_dvd d p)
            exact hpr.ne_one (Nat.isUnit_iff.mp (hd_sq p h2))
          omega
        rw [Finset.prod_congr rfl h1]; simp
      rw [hprod_nu, htau_eq]; exact_mod_cast hle2
    exact hrem_sols.trans hsol_le_tau
  -- Step 2: Apply selberg_upper_bound with R d = d.divisors.card
  let D := (divisors P).filter (· ≤ Z)
  have hrem_lcm : ∀ d1 ∈ D, ∀ d2 ∈ D, |bs.rem (d1.lcm d2)| ≤ (d1.divisors.card : ℝ) * (d2.divisors.card : ℝ) := by
    intro d1 hd1 d2 hd2
    have h1P := Nat.dvd_of_mem_divisors (mem_filter.mp hd1).1
    have h2P := Nat.dvd_of_mem_divisors (mem_filter.mp hd2).1
    have hlP : d1.lcm d2 ∣ P := Nat.lcm_dvd h1P h2P
    refine (hrem_bd (d1.lcm d2) hlP).trans ?_
    -- τ(lcm d1 d2) ≤ τ(d1 * d2) ≤ τ(d1) * τ(d2) (for squarefree d1, d2)
    have h1sq := Squarefree.squarefree_of_dvd h1P hP_sq
    have h2sq := Squarefree.squarefree_of_dvd h2P hP_sq
    have hlsq := Squarefree.squarefree_of_dvd hlP hP_sq
    have hcard_l : (d1.lcm d2).divisors.card = 2 ^ (d1.lcm d2).primeFactors.card := by
      rw [Nat.card_divisors hlsq.ne_zero]
      have h1 : ∀ p ∈ (d1.lcm d2).primeFactors, (d1.lcm d2).factorization p + 1 = 2 := by
        intro p hp; have hpr := Nat.prime_of_mem_primeFactors hp
        have hpos : 1 ≤ (d1.lcm d2).factorization p := Nat.Prime.factorization_pos_of_dvd hpr hlsq.ne_zero (Nat.dvd_of_mem_primeFactors hp)
        have hle1 : (d1.lcm d2).factorization p ≤ 1 := by
          by_contra hgt
          exact hpr.ne_one (Nat.isUnit_iff.mp (hlsq p (by rw [← sq]; exact (Nat.pow_dvd_pow p (by omega : 2 ≤ _)).trans (Nat.ordProj_dvd _ p))))
        omega
      rw [Finset.prod_congr rfl h1]; simp
    have hcard_1 : d1.divisors.card = 2 ^ d1.primeFactors.card := by
      rw [Nat.card_divisors h1sq.ne_zero]
      have h1 : ∀ p ∈ d1.primeFactors, d1.factorization p + 1 = 2 := by
        intro p hp; have hpr := Nat.prime_of_mem_primeFactors hp
        have hpos : 1 ≤ d1.factorization p := Nat.Prime.factorization_pos_of_dvd hpr h1sq.ne_zero (Nat.dvd_of_mem_primeFactors hp)
        have hle1 : d1.factorization p ≤ 1 := by
          by_contra hgt
          exact hpr.ne_one (Nat.isUnit_iff.mp (h1sq p (by rw [← sq]; exact (Nat.pow_dvd_pow p (by omega : 2 ≤ _)).trans (Nat.ordProj_dvd _ p))))
        omega
      rw [Finset.prod_congr rfl h1]; simp
    have hcard_2 : d2.divisors.card = 2 ^ d2.primeFactors.card := by
      rw [Nat.card_divisors h2sq.ne_zero]
      have h1 : ∀ p ∈ d2.primeFactors, d2.factorization p + 1 = 2 := by
        intro p hp; have hpr := Nat.prime_of_mem_primeFactors hp
        have hpos : 1 ≤ d2.factorization p := Nat.Prime.factorization_pos_of_dvd hpr h2sq.ne_zero (Nat.dvd_of_mem_primeFactors hp)
        have hle1 : d2.factorization p ≤ 1 := by
          by_contra hgt
          exact hpr.ne_one (Nat.isUnit_iff.mp (h2sq p (by rw [← sq]; exact (Nat.pow_dvd_pow p (by omega : 2 ≤ _)).trans (Nat.ordProj_dvd _ p))))
        omega
      rw [Finset.prod_congr rfl h1]; simp
    have hpf_sub : (d1.lcm d2).primeFactors ⊆ d1.primeFactors ∪ d2.primeFactors := by
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ d1 * d2 := (Nat.dvd_of_mem_primeFactors hp).trans (Nat.lcm_dvd_mul d1 d2)
      rcases hpr.dvd_mul.mp hpd with h1 | h2
      · exact mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hpr, h1, h1sq.ne_zero⟩)
      · exact mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hpr, h2, h2sq.ne_zero⟩)
    have hpf_le : (d1.lcm d2).primeFactors.card ≤ d1.primeFactors.card + d2.primeFactors.card :=
      (card_le_card hpf_sub).trans (card_union_le _ _)
    have hnat : (d1.lcm d2).divisors.card ≤ d1.divisors.card * d2.divisors.card := by
      rw [hcard_l, hcard_1, hcard_2, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) hpf_le
    exact_mod_cast hnat
  have hsel := selberg_upper_bound bs (by omega : 1 ≤ Z) (fun d => (d.divisors.card : ℝ))
    (fun _ => Nat.cast_nonneg _) hrem_lcm
  -- Step 3: Lower-bound S_sel = ∑ r ∈ D, bs.selbergTerms r using A * B ≤ S_sel!
  let w : ℕ := Nat.sqrt Z
  have hw_pos : 3 ≤ w := Nat.le_sqrt.mpr (by omega)
  have hw_sq : w * w ≤ Z := Nat.sqrt_le Z
  let Uset := (Icc 1 w).filter (fun u => Nat.Coprime u 2)
  let Vset := (Icc 1 w).filter (fun v => Nat.Coprime v (2 * m))
  have hAB_le_S : (∑ u ∈ Uset, (1 : ℝ) / (u : ℝ)) * (∑ v ∈ Vset, (1 : ℝ) / (v : ℝ)) ≤
      ∑ r ∈ D, bs.selbergTerms r := by
    let rad : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors, p
    have hmaps : ∀ x ∈ Uset ×ˢ Vset, rad (x.1 * x.2) ∈ D := by
      intro ⟨u, v⟩ huv
      obtain ⟨hu, hv⟩ := mem_product.mp huv
      have hu1 := (mem_Icc.mp (mem_filter.mp hu).1).1; have huw := (mem_Icc.mp (mem_filter.mp hu).1).2
      have hv1 := (mem_Icc.mp (mem_filter.mp hv).1).1; have hvw := (mem_Icc.mp (mem_filter.mp hv).1).2
      have hu_odd := (mem_filter.mp hu).2
      have hv_odd : Nat.Coprime v 2 := (mem_filter.mp hv).2.coprime_dvd_right (dvd_mul_right 2 m)
      have huv_pos : 1 ≤ u * v := Nat.mul_pos hu1 hv1
      have huv_le : u * v ≤ Z := (Nat.mul_le_mul huw hvw).trans hw_sq
      have hrad_le : rad (u * v) ≤ Z := (Nat.le_of_dvd huv_pos (Nat.prod_primeFactors_dvd (u * v))).trans huv_le
      have hrad_dvd_P : rad (u * v) ∣ P := by
        have hsub_pf : (u * v).primeFactors ⊆ Pset := by
          intro p hp
          have hpr := Nat.prime_of_mem_primeFactors hp
          have hple : p ≤ Z := (Nat.le_of_dvd huv_pos (Nat.dvd_of_mem_primeFactors hp)).trans huv_le
          have hp_ne2 : p ≠ 2 := by
            intro h2; subst h2
            have h2uv := Nat.dvd_of_mem_primeFactors hp
            rcases Nat.prime_two.dvd_mul.mp h2uv with h2u | h2v
            · exact Nat.prime_two.not_dvd_one (hu_odd.gcd_eq_one ▸ Nat.dvd_gcd h2u dvd_rfl)
            · exact Nat.prime_two.not_dvd_one (hv_odd.gcd_eq_one ▸ Nat.dvd_gcd h2v dvd_rfl)
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by have := hpr.two_le; omega, hple⟩, hpr⟩
        exact Finset.prod_dvd_prod_of_subset _ _ _ hsub_pf
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hrad_dvd_P, bs.prodPrimes_ne_zero⟩, hrad_le⟩
    -- Group pairs (u, v) by r = rad (u * v)
    have hprod_sum : (∑ u ∈ Uset, (1 : ℝ) / (u : ℝ)) * (∑ v ∈ Vset, (1 : ℝ) / (v : ℝ)) =
        ∑ r ∈ D, ∑ x ∈ (Uset ×ˢ Vset).filter (fun x => rad (x.1 * x.2) = r),
          (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ)) := by
      rw [Finset.sum_mul]
      have h1 : (∑ u ∈ Uset, (1 : ℝ) / (u : ℝ) * ∑ v ∈ Vset, (1 : ℝ) / (v : ℝ)) =
          ∑ x ∈ Uset ×ˢ Vset, (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ)) := by
        rw [Finset.sum_product]
        refine sum_congr rfl fun u _ => by rw [Finset.mul_sum]; refine sum_congr rfl fun v _ => by ring
      rw [h1, Finset.sum_fiberwise_of_maps_to hmaps]
    rw [hprod_sum]
    refine sum_le_sum fun r hr => ?_
    have hrP : r ∣ P := Nat.dvd_of_mem_divisors (mem_filter.mp hr).1
    have hr_sq : Squarefree r := Squarefree.squarefree_of_dvd hrP hP_sq
    -- Bound fiber sum over rad(u * v) = r by ∏_{p ∣ r} g(p) = bs.selbergTerms r!
    have hfiber_le : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ 3 ≤ p) →
        ∑ x ∈ (Uset ×ˢ Vset).filter (fun x => (x.1 * x.2).primeFactors = S),
          (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ)) ≤
        ∏ p ∈ S, (bs.nu p / (1 - bs.nu p)) := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro _
        have hsub : (Uset ×ˢ Vset).filter (fun x => (x.1 * x.2).primeFactors = ∅) ⊆ {(1, 1)} := by
          intro ⟨u, v⟩ h
          obtain ⟨huv, hpf⟩ := mem_filter.mp h
          have hu1 := (mem_Icc.mp (mem_filter.mp (mem_product.mp huv).1).1).1
          have hv1 := (mem_Icc.mp (mem_filter.mp (mem_product.mp huv).2).1).1
          have huv1 : u * v = 1 := by
            by_contra hne
            obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
            have : p ∈ (u * v).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, by positivity⟩
            rw [hpf] at this; exact Finset.notMem_empty p this
          have : u = 1 ∧ v = 1 := mul_eq_one.mp huv1
          simp [this.1, this.2]
        calc ∑ x ∈ (Uset ×ˢ Vset).filter _, (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))
            ≤ ∑ x ∈ ({(1, 1)} : Finset (ℕ × ℕ)), (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ)) :=
              sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
          _ = 1 := by simp
          _ = ∏ p ∈ (∅ : Finset ℕ), (bs.nu p / (1 - bs.nu p)) := by simp
      | @insert q S hq ih =>
        intro hS
        have ⟨hqp, hq3⟩ := hS q (mem_insert_self q S)
        have hS' : ∀ p ∈ S, p.Prime ∧ 3 ≤ p := fun p hp => hS p (mem_insert_of_mem hp)
        rw [prod_insert hq]
        let F := (Uset ×ˢ Vset).filter (fun x => (x.1 * x.2).primeFactors = insert q S)
        let F' := (Uset ×ˢ Vset).filter (fun x => (x.1 * x.2).primeFactors = S)
        let E := Nat.log q w + 1
        let Pairs : Finset (ℕ × ℕ) :=
          if q ∣ m then (Ico 1 E) ×ˢ ({0} : Finset ℕ)
          else ((range E) ×ˢ (range E)).filter (fun e => 1 ≤ e.1 + e.2)
        have hsub : F ⊆ (Pairs ×ˢ F').image (fun z => (q ^ z.1.1 * z.2.1, q ^ z.1.2 * z.2.2)) := by
          intro ⟨u, v⟩ huv
          obtain ⟨hmem, hpf⟩ := mem_filter.mp huv
          obtain ⟨hu, hv⟩ := mem_product.mp hmem
          have hu1 := (mem_Icc.mp (mem_filter.mp hu).1).1; have huw := (mem_Icc.mp (mem_filter.mp hu).1).2
          have hv1 := (mem_Icc.mp (mem_filter.mp hv).1).1; have hvw := (mem_Icc.mp (mem_filter.mp hv).1).2
          let e1 := u.factorization q
          let e2 := v.factorization q
          let u' := u / q ^ e1
          let v' := v / q ^ e2
          have hqu : q ^ e1 * u' = u := Nat.mul_div_cancel' (Nat.ordProj_dvd u q)
          have hqv : q ^ e2 * v' = v := Nat.mul_div_cancel' (Nat.ordProj_dvd v q)
          have he1_lt : e1 < E := Nat.lt_succ_of_le (Nat.le_log_of_pow_le hqp.one_lt
            ((Nat.le_of_dvd hu1 (Nat.ordProj_dvd u q)).trans huw))
          have he2_lt : e2 < E := Nat.lt_succ_of_le (Nat.le_log_of_pow_le hqp.one_lt
            ((Nat.le_of_dvd hv1 (Nat.ordProj_dvd v q)).trans hvw))
          have he_pos : 1 ≤ e1 + e2 := by
            have hq_mem : q ∈ (u * v).primeFactors := by rw [hpf]; exact mem_insert_self q S
            have hq_uv : q ∣ u * v := Nat.dvd_of_mem_primeFactors hq_mem
            have hfac : 1 ≤ (u * v).factorization q := Nat.Prime.factorization_pos_of_dvd hqp (by positivity) hq_uv
            rw [Nat.factorization_mul (by omega) (by omega), Finsupp.coe_add, Pi.add_apply] at hfac
            exact hfac
          have hpe_mem : (e1, e2) ∈ Pairs := by
            dsimp only [Pairs]
            split_ifs with hqm
            · have he2_zero : e2 = 0 := by
                have hq_ndvd_v : ¬ q ∣ v := fun hqv' => hqp.not_dvd_one
                  (((mem_filter.mp hv).2).gcd_eq_one ▸ Nat.dvd_gcd hqv' (dvd_mul_of_dvd_right hqm 2))
                exact Nat.factorization_eq_zero_of_not_dvd hq_ndvd_v
              exact mem_product.mpr ⟨mem_Ico.mpr ⟨by omega, he1_lt⟩, mem_singleton.mpr he2_zero⟩
            · exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr he1_lt, mem_range.mpr he2_lt⟩, he_pos⟩
          have hu'_pos : 1 ≤ u' := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd u q)) (pow_pos hqp.pos _)
          have hv'_pos : 1 ≤ v' := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd v q)) (pow_pos hqp.pos _)
          have hu'_U : u' ∈ Uset := mem_filter.mpr ⟨mem_Icc.mpr ⟨hu'_pos, (Nat.div_le_self u _).trans huw⟩,
            (mem_filter.mp hu).2.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.ordProj_dvd u q))⟩
          have hv'_V : v' ∈ Vset := mem_filter.mpr ⟨mem_Icc.mpr ⟨hv'_pos, (Nat.div_le_self v _).trans hvw⟩,
            (mem_filter.mp hv).2.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.ordProj_dvd v q))⟩
          have hq_ndvd_u'v' : ¬ q ∣ u' * v' := by
            intro hq_dvd
            rcases hqp.dvd_mul.mp hq_dvd with h1 | h2
            · have hpow : q ^ (e1 + 1) ∣ u := by rw [← hqu, pow_succ]; exact mul_dvd_mul_left _ h1
              exact Nat.pow_succ_factorization_not_dvd (by omega : u ≠ 0) hqp hpow
            · have hpow : q ^ (e2 + 1) ∣ v := by rw [← hqv, pow_succ]; exact mul_dvd_mul_left _ h2
              exact Nat.pow_succ_factorization_not_dvd (by omega : v ≠ 0) hqp hpow
          have hpf' : (u' * v').primeFactors = S := by
            ext p
            have huv_eq : u * v = q ^ (e1 + e2) * (u' * v') := by
              rw [← hqu, ← hqv, pow_add]; ring
            constructor
            · intro hp'
              have hpr := Nat.prime_of_mem_primeFactors hp'
              have hpd := Nat.dvd_of_mem_primeFactors hp'
              have hpne : p ≠ q := fun h => hq_ndvd_u'v' (h ▸ hpd)
              have hpm : p ∈ insert q S := by
                rw [← hpf]; exact Nat.mem_primeFactors.mpr ⟨hpr, by rw [huv_eq]; exact dvd_mul_of_dvd_right hpd _, by positivity⟩
              exact (mem_insert.mp hpm).resolve_left hpne
            · intro hpS
              have hpm : p ∈ (u * v).primeFactors := by rw [hpf]; exact mem_insert_of_mem hpS
              have hpr := Nat.prime_of_mem_primeFactors hpm
              have hpd := Nat.dvd_of_mem_primeFactors hpm
              have hpne : p ≠ q := fun h => hq (h ▸ hpS)
              rw [huv_eq] at hpd
              rcases hpr.dvd_mul.mp hpd with h1 | h2
              · exfalso; exact hpne ((Nat.prime_dvd_prime_iff_eq hpr hqp).mp (hpr.dvd_of_dvd_pow h1))
              · exact Nat.mem_primeFactors.mpr ⟨hpr, h2, by positivity⟩
          exact mem_image.mpr ⟨((e1, e2), (u', v')),
            mem_product.mpr ⟨hpe_mem, mem_filter.mpr ⟨mem_product.mpr ⟨hu'_U, hv'_V⟩, hpf'⟩⟩, Prod.ext hqu hqv⟩
        have hPairs_le : ∑ e ∈ Pairs, (1 : ℝ) / ((q : ℝ) ^ (e.1 + e.2)) ≤ bs.nu q / (1 - bs.nu q) := by
          have hqR3 : (3 : ℝ) ≤ q := by exact_mod_cast hq3
          have hq_inv_lt1 : (q : ℝ)⁻¹ < 1 := by rw [inv_lt_one_iff₀]; right; linarith
          have hgeom1 : ∀ n : ℕ, ∑ k ∈ range n, ((q : ℝ)⁻¹) ^ k ≤ (q : ℝ) / ((q : ℝ) - 1) := by
            intro n
            rw [geom_sum_eq hq_inv_lt1.ne]
            have h1 : (((q : ℝ)⁻¹) ^ n - 1) / ((q : ℝ)⁻¹ - 1) = (1 - ((q : ℝ)⁻¹) ^ n) / (1 - (q : ℝ)⁻¹) := by
              have hs1 : (q : ℝ)⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr hq_inv_lt1.ne
              have hs2 : 1 - (q : ℝ)⁻¹ ≠ 0 := sub_ne_zero.mpr hq_inv_lt1.ne'
              rw [div_eq_div_iff hs1 hs2]; ring
            rw [h1]
            have h2 : 1 / (1 - (q : ℝ)⁻¹) = (q : ℝ) / ((q : ℝ) - 1) := by
              field_simp [show (q : ℝ) ≠ 0 by linarith, show (q : ℝ) - 1 ≠ 0 by linarith]
            rw [← h2]
            exact div_le_div_of_nonneg_right (by linarith [pow_nonneg (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ q)) n]) (by linarith)
          dsimp only [Pairs, bs]
          have hq_ne2 : q ≠ 2 := by omega
          rw [hnu_prime q hqp, if_neg hq_ne2]
          split_ifs with hqm
          · have hrew : ∑ e ∈ (Ico 1 E) ×ˢ ({0} : Finset ℕ), (1 : ℝ) / ((q : ℝ) ^ (e.1 + e.2)) =
                (q : ℝ)⁻¹ * ∑ k ∈ range (E - 1), ((q : ℝ)⁻¹) ^ k := by
              rw [Finset.sum_product, Finset.mul_sum]
              have hIco : Ico 1 E = (range (E - 1)).image (· + 1) := by
                ext k; simp only [mem_Ico, mem_image, mem_range]
                constructor
                · intro ⟨h1, h2⟩; exact ⟨k - 1, by omega, by omega⟩
                · rintro ⟨j, hj, rfl⟩; omega
              rw [hIco, Finset.sum_image (fun _ _ _ _ h => by omega)]
              refine sum_congr rfl fun k _ => ?_
              simp only [Finset.sum_singleton, add_zero, _root_.pow_succ', inv_pow]; field_simp [show (q : ℝ) ≠ 0 by linarith]
            rw [hrew]
            calc (q : ℝ)⁻¹ * ∑ k ∈ range (E - 1), ((q : ℝ)⁻¹) ^ k
                ≤ (q : ℝ)⁻¹ * ((q : ℝ) / ((q : ℝ) - 1)) := mul_le_mul_of_nonneg_left (hgeom1 (E - 1)) (by positivity)
              _ = 1 / (q : ℝ) / (1 - 1 / (q : ℝ)) := by
                  field_simp [show (q : ℝ) ≠ 0 by linarith, show (q : ℝ) - 1 ≠ 0 by linarith]
          · -- ∑_{e1, e2 < E, e1 + e2 ≥ 1} q^{-(e1 + e2)} = (∑ q^{-k})^2 - 1 ≤ (q/(q-1))^2 - 1 = (2q-1)/(q-1)^2 ≤ 2/(q-2)
            have h0_mem : (0, 0) ∈ (range E) ×ˢ (range E) := mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩
            have hsplit : ∑ e ∈ ((range E) ×ˢ (range E)).filter (fun e => 1 ≤ e.1 + e.2), (1 : ℝ) / ((q : ℝ) ^ (e.1 + e.2)) =
                (∑ k ∈ range E, ((q : ℝ)⁻¹) ^ k) ^ 2 - 1 := by
              have hfilt : ((range E) ×ˢ (range E)).filter (fun e => 1 ≤ e.1 + e.2) =
                  ((range E) ×ˢ (range E)).erase (0, 0) := by
                ext ⟨a1, a2⟩; simp only [mem_filter, mem_erase, ne_eq, Prod.mk.injEq]
                exact ⟨fun ⟨h1, h2⟩ => ⟨by omega, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, by omega⟩⟩
              rw [hfilt, Finset.sum_erase_eq_sub h0_mem]
              have hfull : ∑ e ∈ (range E) ×ˢ (range E), (1 : ℝ) / ((q : ℝ) ^ (e.1 + e.2)) =
                  (∑ k ∈ range E, ((q : ℝ)⁻¹) ^ k) ^ 2 := by
                rw [sq, Finset.sum_product, Finset.sum_mul]
                refine sum_congr rfl fun k1 _ => ?_
                rw [Finset.mul_sum]
                refine sum_congr rfl fun k2 _ => by rw [pow_add, inv_pow, inv_pow]; ring
              rw [hfull]; simp
            rw [hsplit]
            have hsq := pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) (hgeom1 E) 2
            have hcomp : ((q : ℝ) / ((q : ℝ) - 1)) ^ 2 - 1 ≤ 2 / (q : ℝ) / (1 - 2 / (q : ℝ)) := by
              have h1 : ((q : ℝ) / ((q : ℝ) - 1)) ^ 2 - 1 = (2 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2 := by
                field_simp [show (q : ℝ) - 1 ≠ 0 by linarith]; ring
              have h2 : 2 / (q : ℝ) / (1 - 2 / (q : ℝ)) = 2 / ((q : ℝ) - 2) := by
                field_simp [show (q : ℝ) ≠ 0 by linarith, show (q : ℝ) - 2 ≠ 0 by linarith]
              rw [h1, h2, div_le_div_iff₀ (pow_pos (by linarith : (0 : ℝ) < (q : ℝ) - 1) 2) (by linarith)]
              nlinarith
            linarith
        calc ∑ x ∈ F, (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))
            ≤ ∑ x ∈ (Pairs ×ˢ F').image (fun z : (ℕ × ℕ) × (ℕ × ℕ) => (q ^ z.1.1 * z.2.1, q ^ z.1.2 * z.2.2)),
                (1 : ℝ) / ((Nat.cast x.1 : ℝ) * (Nat.cast x.2 : ℝ)) :=
              sum_le_sum_of_subset_of_nonneg (f := fun x : ℕ × ℕ => (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))) hsub fun _ _ _ => by positivity
          _ ≤ ∑ z ∈ Pairs ×ˢ F', (1 : ℝ) / (((q ^ z.1.1 * z.2.1 : ℕ) : ℝ) * ((q ^ z.1.2 * z.2.2 : ℕ) : ℝ)) :=
              Finset.sum_image_le_of_nonneg (f := fun x : ℕ × ℕ => (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))) fun _ _ => by positivity
          _ = (∑ e ∈ Pairs, (1 : ℝ) / ((q : ℝ) ^ (e.1 + e.2))) *
                (∑ x ∈ F', (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))) := by
              rw [Finset.sum_product, Finset.sum_mul]
              refine sum_congr rfl fun e _ => ?_
              rw [Finset.mul_sum]
              refine sum_congr rfl fun x _ => by push_cast; rw [pow_add]; ring
          _ ≤ (bs.nu q / (1 - bs.nu q)) * (∏ p ∈ S, (bs.nu p / (1 - bs.nu p))) := by
              have hnuq_pos : 0 < bs.nu q := by
                dsimp only [bs]; rw [hnu_prime q hqp, if_neg (by omega)]; split_ifs <;> positivity
              have hnuq_lt1 : bs.nu q < 1 := by
                dsimp only [bs]; rw [hnu_prime q hqp, if_neg (by omega)]
                have hqR3 : (3 : ℝ) ≤ q := by exact_mod_cast hq3
                split_ifs <;> rw [div_lt_one (by linarith)] <;> linarith
              exact mul_le_mul hPairs_le (ih hS') (sum_nonneg fun _ _ => by positivity)
                (div_nonneg hnuq_pos.le (by linarith))
    have hfilt_eq : (Uset ×ˢ Vset).filter (fun x => rad (x.1 * x.2) = r) =
        (Uset ×ˢ Vset).filter (fun x => (x.1 * x.2).primeFactors = r.primeFactors) := by
      ext ⟨u, v⟩; simp only [mem_filter]
      refine ⟨fun ⟨huv, hrad⟩ => ⟨huv, ?_⟩, fun ⟨huv, hpf⟩ => ⟨huv, ?_⟩⟩
      · have hu1 := (mem_Icc.mp (mem_filter.mp (mem_product.mp huv).1).1).1
        have hv1 := (mem_Icc.mp (mem_filter.mp (mem_product.mp huv).2).1).1
        -- rad (u * v) = r ⇒ primeFactors (rad (u * v)) = r.primeFactors, and rad has the same primeFactors!
        have hpf_rad : (rad (u * v)).primeFactors = (u * v).primeFactors := by
          ext p; simp only [Nat.mem_primeFactors, ne_eq, rad]
          have hprod_ne : ∏ q ∈ (u * v).primeFactors, q ≠ 0 :=
            (prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos).ne'
          constructor
          · rintro ⟨hp, hpd, _⟩
            obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpd
            have := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq)).mp hpq
            exact this ▸ Nat.mem_primeFactors.mp hq
          · rintro ⟨hp, hpd, _⟩
            exact ⟨hp, dvd_prod_of_mem (fun q => q) (Nat.mem_primeFactors.mpr ⟨hp, hpd, by positivity⟩), hprod_ne⟩
        rw [← hpf_rad, hrad]
      · dsimp only [rad]; rw [hpf]; exact Nat.prod_primeFactors_of_squarefree hr_sq
    rw [hfilt_eq]
    have hsel_eq : ∏ p ∈ r.primeFactors, (bs.nu p / (1 - bs.nu p)) = bs.selbergTerms r := by
      rw [bs.selbergTerms_apply, ← bs.prod_primeFactors_nu hrP, ← Finset.prod_mul_distrib]
      exact prod_congr rfl fun _ _ => div_eq_mul_inv _ _
    rw [← hsel_eq]
    exact hfiber_le r.primeFactors fun p hp =>
      ⟨Nat.prime_of_mem_primeFactors hp, (hP_prime_mem p (Nat.prime_of_mem_primeFactors hp)
        ((Nat.dvd_of_mem_primeFactors hp).trans hrP)).1⟩
  -- Step 4: Lower-bound A * B via sum_coprime_inv_ge + telescoping_odd_prime_prod
  have hS_lower : (Real.log (X : ℝ)) ^ 2 / (600 * Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3)) ≤
      ∑ r ∈ D, bs.selbergTerms r := by
    have hw_ge_X10 : (X : ℝ) ^ ((1 : ℝ) / 10) ≤ ((w + 1 : ℕ) : ℝ) := by
      have hZ_gt : (X : ℝ) ^ ((1 : ℝ) / 4) - 1 < (Z : ℝ) := Nat.sub_one_lt_floor _
      have hZ_ge : (9 / 10 : ℝ) * (X : ℝ) ^ ((1 : ℝ) / 4) ≤ (Z : ℝ) := by linarith
      have hX20 : (10 / 9 : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 20) := by
        have hp : (10 / 9 : ℝ) ^ (20 : ℕ) ≤ (10000 : ℝ) := by norm_num
        have h1 : (10 / 9 : ℝ) ^ (20 : ℕ) ≤ (X : ℝ) := hp.trans (by exact_mod_cast hX)
        have hr := Real.rpow_le_rpow (by positivity) h1 (show (0 : ℝ) ≤ 1 / 20 by norm_num)
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at hr
        norm_num at hr; exact hr
      have hX15_le_Z : (X : ℝ) ^ ((1 : ℝ) / 5) ≤ (Z : ℝ) := by
        have h1 : (X : ℝ) ^ ((1 : ℝ) / 5) ≤ (9 / 10 : ℝ) * (X : ℝ) ^ ((1 : ℝ) / 4) := by
          have hmul := mul_le_mul_of_nonneg_right hX20 (Real.rpow_nonneg hXpos.le ((1 : ℝ) / 5))
          rw [← Real.rpow_add hXpos] at hmul; norm_num at hmul; linarith
        linarith
      have hsq : ((X : ℝ) ^ ((1 : ℝ) / 10)) ^ 2 ≤ (((w + 1 : ℕ) : ℝ)) ^ 2 := by
        have hlt : (Z : ℝ) < (((w + 1 : ℕ) : ℝ)) ^ 2 := by
          rw [sq]; exact_mod_cast Nat.lt_succ_sqrt Z
        have hlhs : ((X : ℝ) ^ ((1 : ℝ) / 10)) ^ 2 = (X : ℝ) ^ ((1 : ℝ) / 5) := by
          rw [← Real.rpow_natCast ((X : ℝ) ^ _), ← Real.rpow_mul hXpos.le]; norm_num
        linarith
      nlinarith [Real.rpow_nonneg hXpos.le ((1 : ℝ) / 10), show (0 : ℝ) ≤ ((w + 1 : ℕ) : ℝ) by positivity]
    have hlogw : Real.log (X : ℝ) / 10 ≤ Real.log ((w + 1 : ℕ) : ℝ) := by
      have h1 := Real.log_le_log (Real.rpow_pos_of_pos hXpos _) hw_ge_X10
      rw [Real.log_rpow hXpos] at h1; linarith
    have hA_lo : Real.log (X : ℝ) / 20 ≤ ∑ u ∈ Uset, (1 : ℝ) / (u : ℝ) := by
      have h1 := sum_coprime_inv_ge (M := 2) (w := w) (by norm_num) (by omega)
      have hpf2 : ∏ p ∈ (2 : ℕ).primeFactors, (p : ℝ) / ((p : ℝ) - 1) = 2 := by
        rw [Nat.prime_two.primeFactors, Finset.prod_singleton]; norm_num
      rw [hpf2] at h1
      change Real.log ((w + 1 : ℕ) : ℝ) ≤ 2 * ∑ u ∈ Uset, (1 : ℝ) / (u : ℝ) at h1
      linarith
    have hB_lo : Real.log (X : ℝ) / (20 * Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3)) ≤
        ∑ v ∈ Vset, (1 : ℝ) / (v : ℝ) := by
      have h1 := sum_coprime_inv_ge (M := 2 * m) (w := w) (by omega) (by omega)
      have hpf_2m : (2 * m).primeFactors = insert 2 (m.primeFactors.filter (2 < ·)) := by
        ext p; simp only [Nat.mem_primeFactors, ne_eq, mem_insert, mem_filter]
        constructor
        · rintro ⟨hp, hd, _⟩
          by_cases hp2 : p = 2
          · exact Or.inl hp2
          · right
            have hpm : p ∣ m := (hp.dvd_mul.mp hd).resolve_left
              (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
            exact ⟨⟨hp, hpm, by omega⟩, by have := hp.two_le; omega⟩
        · rintro (rfl | ⟨⟨hp, hpm, _⟩, _⟩)
          · exact ⟨Nat.prime_two, dvd_mul_right 2 m, by omega⟩
          · exact ⟨hp, dvd_mul_of_dvd_right hpm 2, by omega⟩
      have hprod_2m : ∏ p ∈ (2 * m).primeFactors, (p : ℝ) / ((p : ℝ) - 1) ≤
          2 * Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3) := by
        rw [hpf_2m, Finset.prod_insert (by simp)]
        have h2eq : ((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1) = 2 := by norm_num
        rw [h2eq]
        exact mul_le_mul_of_nonneg_left (telescoping_odd_prime_prod hm_pos) (by norm_num)
      have hV_nn : 0 ≤ ∑ v ∈ Vset, (1 : ℝ) / (v : ℝ) := sum_nonneg fun _ _ => by positivity
      have h2 : Real.log ((w + 1 : ℕ) : ℝ) ≤
          (2 * Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3)) * ∑ v ∈ Vset, (1 : ℝ) / (v : ℝ) :=
        h1.trans (mul_le_mul_of_nonneg_right hprod_2m hV_nn)
      have hsq_pos : 0 < Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3) := Real.sqrt_pos.mpr (by positivity)
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hmul := mul_le_mul hA_lo hB_lo (by positivity) (sum_nonneg fun _ _ => by positivity)
    have h400 : Real.log (X : ℝ) / 20 * (Real.log (X : ℝ) / (20 * Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3))) =
        (Real.log (X : ℝ)) ^ 2 / (400 * Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3)) := by ring
    rw [h400] at hmul
    have h600 : (Real.log (X : ℝ)) ^ 2 / (600 * Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3)) ≤
        (Real.log (X : ℝ)) ^ 2 / (400 * Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3)) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (by nlinarith [Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * (Nat.log 2 m : ℝ) + 3)])
    exact (h600.trans hmul).trans hAB_le_S
  -- Step 5: Connect the prime-pair count to bs.siftedSum + 2 * Z and conclude!
  let Targets := (Icc 1 X).filter (fun q : ℕ => q.Prime ∧ 0 < (a : ℤ) * (q : ℤ) + c ∧
      ((a : ℤ) * (q : ℤ) + c).toNat.Prime)
  let T_small1 := Targets.filter (fun q : ℕ => q ≤ Z)
  let T_small2 := Targets.filter (fun q : ℕ => ((a : ℤ) * (q : ℤ) + c).toNat ≤ Z)
  let T_big := Targets.filter (fun q : ℕ => Z < q ∧ Z < ((a : ℤ) * (q : ℤ) + c).toNat)
  have hT_sub : Targets ⊆ T_small1 ∪ T_small2 ∪ T_big := by
    intro q hq
    by_cases h1 : q ≤ Z
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hq, h1⟩))
    · by_cases h2 : ((a : ℤ) * (q : ℤ) + c).toNat ≤ Z
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hq, h2⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hq, by omega, by omega⟩)
  have hcard_s1 : T_small1.card ≤ Z := by
    have hsub : T_small1 ⊆ Icc 1 Z := fun q hq =>
      mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp (mem_filter.mp hq).1).1).1, (mem_filter.mp hq).2⟩
    exact (card_le_card hsub).trans (by rw [Nat.card_Icc]; exact (Nat.add_sub_cancel Z 1).le)
  have hcard_s2 : T_small2.card ≤ Z := by
    let g2 : ℕ → ℕ := fun q => ((a : ℤ) * (q : ℤ) + c).toNat
    have hinj2 : Set.InjOn g2 (T_small2 : Set ℕ) := by
      intro q1 hq1 q2 hq2 heq
      have hp1 := (mem_filter.mp (mem_filter.mp hq1).1).2.2.1
      have hp2 := (mem_filter.mp (mem_filter.mp hq2).1).2.2.1
      have hZ : (a : ℤ) * (q1 : ℤ) + c = (a : ℤ) * (q2 : ℤ) + c := by
        dsimp only [g2] at heq; omega
      have ha0 : (a : ℤ) ≠ 0 := by omega
      have : (q1 : ℤ) = (q2 : ℤ) := mul_left_cancel₀ ha0 (by linarith)
      exact_mod_cast this
    have hmaps2 : T_small2.image g2 ⊆ Icc 1 Z := by
      intro y hy
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hy
      have hpos := (mem_filter.mp (mem_filter.mp hq).1).2.2.1
      have hle := (mem_filter.mp hq).2
      exact mem_Icc.mpr ⟨by dsimp only [g2]; omega, hle⟩
    calc T_small2.card = (T_small2.image g2).card := (Finset.card_image_of_injOn hinj2).symm
      _ ≤ (Icc 1 Z).card := card_le_card hmaps2
      _ = Z := by rw [Nat.card_Icc]; exact Nat.add_sub_cancel Z 1
  have hcard_big : (T_big.card : ℝ) ≤ bs.siftedSum := by
    have hTbig_sub_LX : T_big ⊆ Icc L X := by
      intro q hq
      have hqt := (mem_filter.mp hq).1
      exact hQ0_eq ▸ mem_filter.mpr ⟨(mem_filter.mp hqt).1, (mem_filter.mp hqt).2.2.1⟩
    have hcop_big : ∀ q ∈ T_big, Nat.Coprime P (f q) := by
      intro q hq
      obtain ⟨hqt, hqZ, hvalZ⟩ := mem_filter.mp hq
      obtain ⟨_, hqpr, _, hvalpr⟩ := mem_filter.mp hqt
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
      have hpP : p ∣ P := hpg.trans (Nat.gcd_dvd_left P (f q))
      have hpf : p ∣ f q := hpg.trans (Nat.gcd_dvd_right P (f q))
      have ⟨_, hpZ⟩ := hP_prime_mem p hp hpP
      rcases hp.dvd_mul.mp hpf with h1 | h2
      · have := (Nat.prime_dvd_prime_iff_eq hp hqpr).mp h1; omega
      · have := (Nat.prime_dvd_prime_iff_eq hp hvalpr).mp h2; omega
    have hsub_sift : T_big.image f ⊆ bs.support.filter (Nat.Coprime P) := by
      intro n hn
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hn
      exact mem_filter.mpr ⟨mem_image_of_mem f (hTbig_sub_LX hq), hcop_big q hq⟩
    have hcard_nat : T_big.card ≤ (bs.support.filter (Nat.Coprime P)).card := by
      rw [← Finset.card_image_of_injOn (hf_inj.mono hTbig_sub_LX)]
      exact card_le_card hsub_sift
    have hsift_eq : bs.siftedSum = ((bs.support.filter (Nat.Coprime P)).card : ℝ) := by
      dsimp only [bs, BoundingSieve.siftedSum]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsift_eq]; exact_mod_cast hcard_nat
  have hmain_bd : bs.totalMass / (∑ r ∈ D, bs.selbergTerms r) ≤
      600 * Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3) * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 := by
    have htot_le : bs.totalMass ≤ (X : ℝ) := by
      dsimp only [bs, totalLen]; exact_mod_cast (by omega : X - L + 1 ≤ X)
    have hS_pos : 0 < (Real.log (X : ℝ)) ^ 2 / (600 * Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3)) := by positivity
    calc bs.totalMass / (∑ r ∈ D, bs.selbergTerms r)
        ≤ (X : ℝ) / ((Real.log (X : ℝ)) ^ 2 / (600 * Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3))) :=
          div_le_div₀ hXpos.le htot_le hS_pos hS_lower
      _ = 600 * Real.sqrt (2 * (Nat.log 2 m : ℝ) + 3) * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 := by
          field_simp [hlogX_pos.ne', (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * (Nat.log 2 m : ℝ) + 3)).ne']
  have herr_bd : (∑ d ∈ D, (d.divisors.card : ℝ)) ^ 2 ≤ (X : ℝ) ^ ((1 : ℝ) / 2) * (1 + Real.log (X : ℝ)) ^ 2 := by
    have hD_sub : D ⊆ Icc 1 Z := by
      intro d hd
      obtain ⟨hdP, hdZ⟩ := mem_filter.mp hd
      have hd_pos : 0 < d := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero bs.prodPrimes_ne_zero (Nat.dvd_of_mem_divisors hdP))
      exact mem_Icc.mpr ⟨hd_pos, hdZ⟩
    have hsum_le : ∑ d ∈ D, (d.divisors.card : ℝ) ≤ (X : ℝ) ^ ((1 : ℝ) / 4) * (1 + Real.log (X : ℝ)) := by
      have hlogZ : Real.log (Z : ℝ) ≤ Real.log (X : ℝ) := by
        apply Real.log_le_log (by exact_mod_cast (by omega : 0 < Z))
        have : (X : ℝ) ^ ((1 : ℝ) / 4) ≤ (X : ℝ) := by
          conv_rhs => rw [← Real.rpow_one (X : ℝ)]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ X)) (by norm_num)
        linarith
      calc ∑ d ∈ D, (d.divisors.card : ℝ)
          ≤ ∑ d ∈ Icc 1 Z, (d.divisors.card : ℝ) := sum_le_sum_of_subset_of_nonneg hD_sub fun _ _ _ => Nat.cast_nonneg _
        _ ≤ (Z : ℝ) * (1 + Real.log (Z : ℝ)) := sum_tau_le (by omega)
        _ ≤ (X : ℝ) ^ ((1 : ℝ) / 4) * (1 + Real.log (X : ℝ)) :=
            mul_le_mul hZ_le (by linarith) (by positivity) (by positivity)
    calc (∑ d ∈ D, (d.divisors.card : ℝ)) ^ 2
        ≤ ((X : ℝ) ^ ((1 : ℝ) / 4) * (1 + Real.log (X : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (sum_nonneg fun _ _ => Nat.cast_nonneg _) hsum_le 2
      _ = ((X : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 * (1 + Real.log (X : ℝ)) ^ 2 := mul_pow _ _ 2
      _ = (X : ℝ) ^ ((1 : ℝ) / 2) * (1 + Real.log (X : ℝ)) ^ 2 := by
          congr 1; rw [← Real.rpow_natCast ((X : ℝ) ^ _), ← Real.rpow_mul hXpos.le]; norm_num
  have hT_card_nat : Targets.card ≤ T_small1.card + T_small2.card + T_big.card :=
    (card_le_card hT_sub).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  have hT_card_R : (Targets.card : ℝ) ≤ (Z : ℝ) + (Z : ℝ) + (T_big.card : ℝ) := by
    have h1 : (Targets.card : ℝ) ≤ (T_small1.card : ℝ) + (T_small2.card : ℝ) + (T_big.card : ℝ) := by
      exact_mod_cast hT_card_nat
    have h2 : (T_small1.card : ℝ) ≤ Z := by exact_mod_cast hcard_s1
    have h3 : (T_small2.card : ℝ) ≤ Z := by exact_mod_cast hcard_s2
    linarith
  linarith [hT_card_R, hcard_big, hsel, hmain_bd, herr_bd, hZ_le]

end OMA.Erdos387S2

/-
# Existence of weight-`B` restricted prime coverings for `Erdos387.erdos_387.R1.H1`

For any fixed `B ≥ 3`, chooses a fixed prime `Q ≥ max (100 * B) 1000`, sets
`Y = ⌊exp ((log K)^(3/5))⌋₊` for sufficiently large `K`, picks a pigeonhole prime
residue class `r₀ ∈ {1, ..., Q - 1}` via Chebyshev's bounds, removes five negligible
bad sets `E0, ..., E4` using Rankin's smooth-number bound and the 2-dimensional
Selberg sieve, and constructs a weight-`B` cover `HasCoverB B k` for some `k ∈ (K, 10 K]`.
-/

namespace OMA.Erdos387S3

open Finset Filter Real Nat OMA.Erdos387S1 OMA.Erdos387S2
open scoped Classical BigOperators

/-- Telescoping upper bound `∑_{q ∈ Ioc A B} 1 / q^2 ≤ 1 / A` for `1 ≤ A`. -/
private lemma sum_Ioc_inv_sq_le {A B : ℕ} (hA : 1 ≤ A) :
    ∑ q ∈ Ioc A B, (1 : ℝ) / ((q : ℝ) ^ 2) ≤ 1 / (A : ℝ) := by
  by_cases hAB : B ≤ A
  · have : Ioc A B = ∅ := Ioc_eq_empty (by omega)
    rw [this, sum_empty]; positivity
  push Not at hAB
  have hterm : ∀ q ∈ Ioc A B, (1 : ℝ) / ((q : ℝ) ^ 2) ≤ 1 / ((q - 1 : ℕ) : ℝ) - 1 / (q : ℝ) := by
    intro q hq
    have hq2 : 2 ≤ q := by have := (mem_Ioc.mp hq).1; omega
    have hq2R : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    have hqpos : (0 : ℝ) < q := by linarith
    have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    rw [hcast]
    have h1 : 1 / ((q : ℝ) - 1) - 1 / (q : ℝ) = 1 / ((q : ℝ) * ((q : ℝ) - 1)) := by
      field_simp [hqpos.ne', show (q : ℝ) - 1 ≠ 0 by linarith]; ring
    rw [h1]
    exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
  have htele : ∀ n : ℕ, A ≤ n →
      ∑ q ∈ Ioc A n, (1 / ((q - 1 : ℕ) : ℝ) - 1 / (q : ℝ)) = 1 / (A : ℝ) - 1 / (n : ℝ) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ m ih =>
      intro hAm
      rcases eq_or_lt_of_le hAm with rfl | hlt
      · simp
      · have hAm' : A ≤ m := by omega
        have hIoc : Ioc A (m + 1) = insert (m + 1) (Ioc A m) := by
          ext x; simp only [mem_Ioc, mem_insert]; omega
        rw [hIoc, sum_insert (by simp), ih hAm', Nat.add_sub_cancel]
        ring
  calc ∑ q ∈ Ioc A B, (1 : ℝ) / ((q : ℝ) ^ 2)
      ≤ ∑ q ∈ Ioc A B, (1 / ((q - 1 : ℕ) : ℝ) - 1 / (q : ℝ)) := sum_le_sum hterm
    _ = 1 / (A : ℝ) - 1 / (B : ℝ) := htele B hAB.le
    _ ≤ 1 / (A : ℝ) := by linarith [show (0 : ℝ) ≤ 1 / (B : ℝ) by positivity]

/-- Counting multiples in `Icc 1 N` congruent to `c` modulo `d`: at most `N / d + 1`. -/
private lemma card_Icc_modEq_le (N d c : ℕ) (_hd : 0 < d) :
    ((Icc 1 N).filter (fun k => k ≡ c [MOD d])).card ≤ N / d + 1 := by
  let S := (Icc 1 N).filter (fun k => k ≡ c [MOD d])
  have hinj : Set.InjOn (fun k => k / d) (S : Set ℕ) := by
    intro k1 hk1 k2 hk2 heq
    have hm1 : k1 % d = c % d := (mem_filter.mp hk1).2
    have hm2 : k2 % d = c % d := (mem_filter.mp hk2).2
    have h1 := Nat.div_add_mod k1 d
    have h2 := Nat.div_add_mod k2 d
    dsimp only at heq
    rw [← h1, ← h2, heq, hm1, hm2]
  have hmaps : S.image (fun k => k / d) ⊆ range (N / d + 1) := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hq
    rw [mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp hk).1).2)
  calc S.card = (S.image (fun k => k / d)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (range (N / d + 1)).card := card_le_card hmaps
    _ = N / d + 1 := card_range _

/-- Counting tuples of exponents `(e_d : d ∈ D)` with `∑ e_d ≤ E`: at most `(D.card + 1) ^ E`. -/
private lemma card_exponent_tuples_le {ι : Type*} (D : Finset ι) (E : ℕ) :
    (((Finset.univ : Finset (D → Fin (E + 1))).filter
        (fun e => ∑ d : D, (e d).val ≤ E)).card) ≤ (D.card + 1) ^ E := by
  induction E with
  | zero =>
    have hsub : ((Finset.univ : Finset (D → Fin 1)).filter (fun e => ∑ d : D, (e d).val ≤ 0)).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro e1 _ e2 _; funext d; exact Subsingleton.elim (e1 d) (e2 d)
    rw [pow_zero]; exact hsub
  | succ E ih =>
    let S := (Finset.univ : Finset (D → Fin (E + 2))).filter (fun e => ∑ d : D, (e d).val ≤ E + 1)
    let S0 := (Finset.univ : Finset (D → Fin (E + 1))).filter (fun e => ∑ d : D, (e d).val ≤ E)
    let inc : Option D → (D → Fin (E + 1)) → (D → Fin (E + 2)) := fun o e d =>
      match o with
      | none => ⟨(e d).val, by omega⟩
      | some d0 => if d = d0 then ⟨(e d).val + 1, by omega⟩ else ⟨(e d).val, by omega⟩
    have hsub : S ⊆ ((Finset.univ : Finset (Option D)) ×ˢ S0).image (fun p => inc p.1 p.2) := by
      intro e he
      have hsum : ∑ d : D, (e d).val ≤ E + 1 := (mem_filter.mp he).2
      by_cases hle : ∑ d : D, (e d).val ≤ E
      · let e0 : D → Fin (E + 1) := fun d =>
          ⟨(e d).val, Nat.lt_succ_of_le ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ d)).trans hle)⟩
        have he0 : e0 ∈ S0 := mem_filter.mpr ⟨mem_univ _, by simpa [e0] using hle⟩
        refine mem_image.mpr ⟨(none, e0), mem_product.mpr ⟨mem_univ _, he0⟩, ?_⟩
        ext d; simp [inc, e0]
      · have hpos : 0 < ∑ d : D, (e d).val := by omega
        obtain ⟨d0, _, hd0_pos⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
        let e0 : D → Fin (E + 1) := fun d =>
          if hdd : d = d0 then ⟨(e d).val - 1, by
            have := Finset.single_le_sum (f := fun x => (e x).val) (fun _ _ => Nat.zero_le _) (mem_univ d)
            have hne0 : (e d).val ≠ 0 := hdd ▸ hd0_pos
            omega⟩
          else ⟨(e d).val, by
            have h2 := Finset.add_sum_erase (s := (Finset.univ : Finset D)) (f := fun x => (e x).val) (mem_univ d0)
            have h3 := Finset.single_le_sum (s := Finset.univ.erase d0) (f := fun x => (e x).val)
              (fun _ _ => Nat.zero_le _) (mem_erase.mpr ⟨hdd, mem_univ d⟩)
            omega⟩
        have hsum0 : ∑ d : D, (e0 d).val ≤ E := by
          have h1 : ∑ d : D, (e d).val = (e d0).val + ∑ d ∈ Finset.univ.erase d0, (e d).val :=
            (Finset.add_sum_erase _ _ (mem_univ d0)).symm
          have h2 : ∑ d : D, (e0 d).val = (e0 d0).val + ∑ d ∈ Finset.univ.erase d0, (e0 d).val :=
            (Finset.add_sum_erase _ _ (mem_univ d0)).symm
          have h3 : ∑ d ∈ Finset.univ.erase d0, (e0 d).val = ∑ d ∈ Finset.univ.erase d0, (e d).val := by
            refine sum_congr rfl fun d hd => ?_
            have hne : d ≠ d0 := (mem_erase.mp hd).1
            simp [e0, hne]
          have h4 : (e0 d0).val = (e d0).val - 1 := by simp [e0]
          omega
        have he0 : e0 ∈ S0 := mem_filter.mpr ⟨mem_univ _, hsum0⟩
        refine mem_image.mpr ⟨(some d0, e0), mem_product.mpr ⟨mem_univ _, he0⟩, ?_⟩
        ext d
        by_cases hdd : d = d0
        · subst hdd; dsimp only [inc, e0]; rw [if_pos rfl, Fin.val_mk, dif_pos rfl, Fin.val_mk]; omega
        · dsimp only [inc, e0]; rw [if_neg hdd, Fin.val_mk, dif_neg hdd, Fin.val_mk]
    calc S.card ≤ (((Finset.univ : Finset (Option D)) ×ˢ S0).image (fun p => inc p.1 p.2)).card := card_le_card hsub
      _ ≤ ((Finset.univ : Finset (Option D)) ×ˢ S0).card := card_image_le
      _ = (D.card + 1) * S0.card := by rw [card_product, Finset.card_univ, Fintype.card_option, Fintype.card_coe]
      _ ≤ (D.card + 1) * (D.card + 1) ^ E := Nat.mul_le_mul_left _ ih
      _ = (D.card + 1) ^ (E + 1) := (_root_.pow_succ' _ _).symm

/-- Shared parameter bundle for the fixed-`B` covering construction. -/
private structure CoverCtx where
  B : ℕ
  Q : ℕ
  K : ℕ
  Y : ℕ
  r₀ : ℕ
  hB : 3 ≤ B
  hQp : Q.Prime
  hQ100B : 100 * B ≤ Q
  hQ1000 : 1000 ≤ Q
  hKbig : max 1000000 (100 * Q ^ 2) ≤ K
  hL10 : 10000 ≤ Real.log (K : ℝ)
  hL2 : (1000000 : ℝ) * (Q : ℝ) ^ 4 * (B : ℝ) ^ 3 ≤ (Real.log (K : ℝ)) ^ ((1 : ℝ) / 10)
  hL3 : Real.log (10000 * (Q : ℝ) * (B : ℝ)) + 100 ≤ (1 / 10 : ℝ) * (Real.log (K : ℝ)) ^ ((3 : ℝ) / 5)
  hL4 : 10 * (Real.log (K : ℝ)) ^ ((3 : ℝ) / 5) + 10 * Real.log (Real.log (K : ℝ)) + 100 ≤ Real.log (K : ℝ) / 4
  hL5 : Real.log (B : ℝ) + Real.log (2 * Real.log (K : ℝ) + 1) +
        4 * (Real.log (K : ℝ)) ^ ((2 : ℝ) / 5) * Real.log (3 * (B : ℝ) * (Real.log (K : ℝ)) ^ ((3 : ℝ) / 5) + 1) ≤
        (1 / 4 : ℝ) * (Real.log (K : ℝ)) ^ ((3 : ℝ) / 5)
  hL6 : 16 * Real.log (2 * (Real.log (K : ℝ)) ^ ((3 : ℝ) / 5)) + 40 + 10 * Real.log (Real.log (K : ℝ)) ≤
        (1 / 4 : ℝ) * (Real.log (K : ℝ)) ^ ((2 : ℝ) / 5)
  hY_le_exp : (Y : ℝ) ≤ Real.exp ((Real.log (K : ℝ)) ^ ((3 : ℝ) / 5))
  hY_ge_half : Real.exp ((Real.log (K : ℝ)) ^ ((3 : ℝ) / 5)) / 2 ≤ (Y : ℝ)
  hY_ge_1000QB : 1000 * Q * B ≤ Y
  hY_ge_1000Q : 1000 * Q ≤ Y
  hY_ge_1000 : 1000 ≤ Y
  hY_le_K14 : (Y : ℝ) ^ 4 ≤ (K : ℝ)
  hY_small : 1000 * Q * B * Y ≤ K
  hY_le_K : 1000 * Y ≤ K
  hlogY_lo : (1 / 2 : ℝ) * (Real.log (K : ℝ)) ^ ((3 : ℝ) / 5) ≤ Real.log (Y : ℝ)
  hlogY_hi : Real.log (Y : ℝ) ≤ (Real.log (K : ℝ)) ^ ((3 : ℝ) / 5)
  hr₀_ge1 : 1 ≤ r₀
  hr₀_ltQ : r₀ < Q
  hr₀_card : (K : ℝ) / (4 * (Q : ℝ) * Real.log (K : ℝ)) ≤
    (((Ioc K (10 * K)).filter (fun p => p.Prime ∧ p % Q = r₀)).card : ℝ)

private noncomputable abbrev CoverCtx.L (c : CoverCtx) : ℝ := Real.log (c.K : ℝ)
private def CoverCtx.Kset (c : CoverCtx) : Finset ℕ := (Ioc c.K (10 * c.K)).filter (fun k => c.Q ∣ k ∧ ¬ c.Q ^ 2 ∣ k)
private def CoverCtx.Pnear (c : CoverCtx) (k : ℕ) : Finset ℕ := (Ioo (k - c.Y / 2) k).filter (fun p => p.Prime ∧ p % c.Q = c.r₀)
private def CoverCtx.Dset (c : CoverCtx) : Finset ℕ := (Icc 1 c.Y).filter (fun d => d % c.Q ≠ c.r₀ ∧ d / c.Q ^ (d.factorization c.Q) < c.B)
private noncomputable def CoverCtx.E0 (c : CoverCtx) : Finset ℕ := c.Kset.filter (fun k => ∃ t ∈ Icc 1 (c.Y + 1), (k - t + 1) / c.Q ^ ((k - t + 1).factorization c.Q) < c.B)
private lemma CoverCtx.mem_E0 (c : CoverCtx) {k : ℕ} :
    k ∈ c.E0 ↔ k ∈ c.Kset ∧ ∃ t ∈ Icc 1 (c.Y + 1), (k - t + 1) / c.Q ^ ((k - t + 1).factorization c.Q) < c.B := by
  dsimp only [CoverCtx.E0]
  exact @Finset.mem_filter _ _ (Classical.decPred _) _ _
private noncomputable def CoverCtx.E1 (c : CoverCtx) : Finset ℕ := c.Kset.filter (fun k => ∃ d ∈ c.Dset, ∃ q, q.Prime ∧ 2 * c.Y < q ∧ q ^ 2 ∣ k - d + 1)
private noncomputable def CoverCtx.E2 (c : CoverCtx) : Finset ℕ := c.Kset.filter (fun k => ∃ d ∈ c.Dset, ∀ q, q.Prime → q ∣ k - d + 1 → q ≤ 2 * c.Y)
private noncomputable def CoverCtx.E3 (c : CoverCtx) : Finset ℕ := c.Kset.filter (fun k => ∃ d ∈ c.Dset, ∃ q, q.Prime ∧ (k - c.Y) / (c.Q * c.B) < q ∧ q ∣ k - d + 1)
private noncomputable def CoverCtx.E4 (c : CoverCtx) : Finset ℕ := c.Kset.filter (fun k => (c.Pnear k).card ≤ Nat.floor (Real.sqrt (c.Y : ℝ)))

private lemma CoverCtx.hKpos (c : CoverCtx) : (0 : ℝ) < c.K := by
  exact_mod_cast (by have := (le_max_left 1000000 (100 * c.Q ^ 2)).trans c.hKbig; omega : 0 < c.K)

private lemma CoverCtx.hQpos (c : CoverCtx) : (0 : ℝ) < c.Q := by
  exact_mod_cast (by have := c.hQ1000; omega : 0 < c.Q)

private lemma CoverCtx.hBpos (c : CoverCtx) : (0 : ℝ) < c.B := by
  exact_mod_cast (by have := c.hB; omega : 0 < c.B)

private lemma CoverCtx.hYpos (c : CoverCtx) : (0 : ℝ) < c.Y := by
  exact_mod_cast (by have := c.hY_ge_1000; omega : 0 < c.Y)

private lemma CoverCtx.hLpos (c : CoverCtx) : 0 < c.L := by
  dsimp only [CoverCtx.L]; linarith [c.hL10]

private lemma CoverCtx.hL35_ge (c : CoverCtx) : (1000 : ℝ) ≤ c.L ^ ((3 : ℝ) / 5) := by
  have h1 : (1000 : ℝ) ≤ c.L ^ ((1 : ℝ) / 10) := by
    have : (1000000 : ℝ) ≤ (1000000 : ℝ) * (c.Q : ℝ) ^ 4 * (c.B : ℝ) ^ 3 := by
      have h1' : (1 : ℝ) ≤ (c.Q : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (by have := c.hQ1000; omega : 1 ≤ c.Q))
      have h2' : (1 : ℝ) ≤ (c.B : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast (by have := c.hB; omega : 1 ≤ c.B))
      nlinarith
    linarith [c.hL2]
  exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by linarith [c.hL10]) (by norm_num))

private lemma CoverCtx.hlogQ_ge2 (c : CoverCtx) : (2 : ℝ) ≤ Real.log (c.Q : ℝ) := by
  have : Real.exp 2 ≤ (c.Q : ℝ) := by
    have h1 : Real.exp 2 = (Real.exp 1) ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : (Real.exp 1) ^ 2 ≤ 9 := by nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
    have hQ1000R : (1000 : ℝ) ≤ c.Q := by exact_mod_cast c.hQ1000
    linarith
  have := Real.log_le_log (Real.exp_pos 2) this; rwa [Real.log_exp] at this

private lemma CoverCtx.hlog10_le4 : Real.log 10 ≤ 4 := by
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    have := pow_le_pow_left₀ (by norm_num) h2e 4
    norm_num at this; exact this
  have h10 : (10 : ℝ) ≤ Real.exp 4 := by linarith
  have := Real.log_le_log (by norm_num) h10
  rwa [Real.log_exp] at this

private lemma CoverCtx.hPnear_le_Y (c : CoverCtx) (k : ℕ) : ((c.Pnear k).card : ℝ) ≤ (c.Y : ℝ) := by
  have hnat : (c.Pnear k).card ≤ c.Y := by
    calc (c.Pnear k).card ≤ (Ioo (k - c.Y / 2) k).card := card_le_card (filter_subset _ _)
      _ ≤ c.Y := by rw [Nat.card_Ioo]; omega
  exact_mod_cast hnat

private lemma CoverCtx.hDset_card (c : CoverCtx) : (c.Dset.card : ℝ) ≤ 2 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) := by
  have hQpos := c.hQpos; have hLpos := c.hLpos; have hYpos := c.hYpos
  have hsub : c.Dset ⊆ ((Ico 1 c.B) ×ˢ (range (Nat.log c.Q c.Y + 1))).image (fun p : ℕ × ℕ => p.1 * c.Q ^ p.2) := by
    intro d hd
    obtain ⟨hdI, _, hzu⟩ := mem_filter.mp hd
    have hd1 := (mem_Icc.mp hdI).1; have hdY := (mem_Icc.mp hdI).2
    let a := d.factorization c.Q
    let u := d / c.Q ^ a
    have hQa_dvd : c.Q ^ a ∣ d := Nat.ordProj_dvd d c.Q
    have hmul : u * c.Q ^ a = d := by rw [mul_comm]; exact Nat.mul_div_cancel' hQa_dvd
    have hu1 : 1 ≤ u := Nat.div_pos (Nat.le_of_dvd hd1 hQa_dvd) (pow_pos c.hQp.pos a)
    have ha_le : a ≤ Nat.log c.Q c.Y := Nat.le_log_of_pow_le c.hQp.one_lt ((Nat.le_of_dvd hd1 hQa_dvd).trans hdY)
    exact mem_image.mpr ⟨(u, a), mem_product.mpr ⟨mem_Ico.mpr ⟨hu1, hzu⟩, mem_range.mpr (Nat.lt_succ_of_le ha_le)⟩, hmul⟩
  have hcard_nat : c.Dset.card ≤ c.B * (Nat.log c.Q c.Y + 1) := by
    calc c.Dset.card ≤ (((Ico 1 c.B) ×ˢ (range (Nat.log c.Q c.Y + 1))).image (fun p : ℕ × ℕ => p.1 * c.Q ^ p.2)).card :=
          card_le_card hsub
      _ ≤ ((Ico 1 c.B) ×ˢ (range (Nat.log c.Q c.Y + 1))).card := card_image_le
      _ = (c.B - 1) * (Nat.log c.Q c.Y + 1) := by rw [card_product, Nat.card_Ico, card_range]
      _ ≤ c.B * (Nat.log c.Q c.Y + 1) := Nat.mul_le_mul_right _ (Nat.sub_le c.B 1)
  have hlogQY : (Nat.log c.Q c.Y : ℝ) ≤ Real.log (c.Y : ℝ) / Real.log (c.Q : ℝ) := by
    have hlogQ : 0 < Real.log (c.Q : ℝ) := Real.log_pos (by exact_mod_cast c.hQp.one_lt)
    rw [le_div_iff₀ hlogQ]
    have h1 : ((c.Q : ℝ) ^ Nat.log c.Q c.Y) ≤ (c.Y : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self c.Q (by have := c.hY_ge_1000; omega)
    have h2 := Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at h2
  have hlogQY_le : (Nat.log c.Q c.Y : ℝ) + 1 ≤ 2 * c.L ^ ((3 : ℝ) / 5) := by
    have h1 : Real.log (c.Y : ℝ) / Real.log (c.Q : ℝ) ≤ c.L ^ ((3 : ℝ) / 5) / 2 :=
      div_le_div₀ (by positivity) c.hlogY_hi (by norm_num) c.hlogQ_ge2
    linarith [c.hL35_ge]
  have hcast : (c.Dset.card : ℝ) ≤ (c.B : ℝ) * ((Nat.log c.Q c.Y : ℝ) + 1) := by exact_mod_cast hcard_nat
  nlinarith [c.hBpos]

private lemma CoverCtx.hDset_mod1 (c : CoverCtx) : ∀ d ∈ c.Dset, d ≠ 1 → d % c.Q ≠ 1 := by
  intro d hd hd1
  obtain ⟨_, _, hzu⟩ := mem_filter.mp hd
  let a := d.factorization c.Q
  let u := d / c.Q ^ a
  have hmul : u * c.Q ^ a = d := by rw [mul_comm]; exact Nat.mul_div_cancel' (Nat.ordProj_dvd d c.Q)
  rcases Nat.eq_zero_or_pos a with ha0 | ha_pos
  · rw [ha0, pow_zero, mul_one] at hmul
    have hu_ltB : u < c.B := hzu
    have hu_ltQ : u < c.Q := by have := c.hQ100B; omega
    have hu_ne1 : u ≠ 1 := by omega
    rw [← hmul, Nat.mod_eq_of_lt hu_ltQ]; exact hu_ne1
  · have hQd : c.Q ∣ d := by rw [← hmul]; exact dvd_mul_of_dvd_right (dvd_pow_self c.Q ha_pos.ne') u
    rw [Nat.mod_eq_zero_of_dvd hQd]; norm_num

/-- Raw supply lower bound: `∑ k ∈ c.Kset, (c.Pnear k).card ≥ K * Y / (20 * Q^2 * L)`. -/
private lemma CoverCtx.hRaw (c : CoverCtx) :
    (c.K : ℝ) * (c.Y : ℝ) / (20 * (c.Q : ℝ) ^ 2 * c.L) ≤ ∑ k ∈ c.Kset, ((c.Pnear k).card : ℝ) := by
  have hKpos := c.hKpos; have hQpos := c.hQpos; have hYpos := c.hYpos; have hLpos := c.hLpos
  let P_mid := (Ioc c.K (10 * c.K - c.Y)).filter (fun p => p.Prime ∧ p % c.Q = c.r₀)
  have hPmid_card : (c.K : ℝ) / (4 * (c.Q : ℝ) * c.L) - (c.Y : ℝ) ≤ (P_mid.card : ℝ) := by
    have hsub : (Ioc c.K (10 * c.K)).filter (fun p => p.Prime ∧ p % c.Q = c.r₀) ⊆
        P_mid ∪ Ioc (10 * c.K - c.Y) (10 * c.K) := by
      intro p hp
      obtain ⟨hpI, hpr⟩ := mem_filter.mp hp
      obtain ⟨h1, h2⟩ := mem_Ioc.mp hpI
      by_cases hle : p ≤ 10 * c.K - c.Y
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨h1, hle⟩, hpr⟩)
      · exact mem_union_right _ (mem_Ioc.mpr ⟨by omega, h2⟩)
    have hcard_tail : (Ioc (10 * c.K - c.Y) (10 * c.K)).card ≤ c.Y := by rw [Nat.card_Ioc]; omega
    have hcard_nat : ((Ioc c.K (10 * c.K)).filter (fun p => p.Prime ∧ p % c.Q = c.r₀)).card ≤ P_mid.card + c.Y :=
      (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left hcard_tail _))
    have hcard_R : (((Ioc c.K (10 * c.K)).filter (fun p => p.Prime ∧ p % c.Q = c.r₀)).card : ℝ) ≤
        (P_mid.card : ℝ) + (c.Y : ℝ) := by exact_mod_cast hcard_nat
    linarith [c.hr₀_card]
  have hh_count : ∀ p ∈ P_mid, (c.Y : ℝ) / (3 * (c.Q : ℝ)) ≤
      (((Ioo 0 (c.Y / 2)).filter (fun h => c.Q ∣ p + h ∧ ¬ c.Q ^ 2 ∣ p + h)).card : ℝ) := by
    intro p hp
    have hp_mod : p % c.Q = c.r₀ := (mem_filter.mp hp).2.2
    let M : ℕ := (c.Y / 2 - c.Q) / c.Q
    let Hgood := (range M).filter (fun t => ¬ c.Q ^ 2 ∣ p + ((c.Q - c.r₀) + t * c.Q))
    have hQ_le_Y2 : c.Q ≤ c.Y / 2 := by have := c.hY_ge_1000Q; omega
    have hmaps : Hgood.image (fun t => (c.Q - c.r₀) + t * c.Q) ⊆
        (Ioo 0 (c.Y / 2)).filter (fun h => c.Q ∣ p + h ∧ ¬ c.Q ^ 2 ∣ p + h) := by
      intro h hh
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hh
      obtain ⟨htM, hndvd⟩ := mem_filter.mp ht
      have htlt : t < M := mem_range.mp htM
      have hlt_Y2 : (c.Q - c.r₀) + t * c.Q < c.Y / 2 := by
        have h1 : t * c.Q + c.Q ≤ M * c.Q := by
          have := Nat.mul_le_mul_right c.Q (Nat.succ_le_of_lt htlt); linarith
        have h2 : M * c.Q ≤ c.Y / 2 - c.Q := Nat.div_mul_le_self (c.Y / 2 - c.Q) c.Q
        have := c.hr₀_ge1; have := c.hr₀_ltQ; omega
      have hQdvd : c.Q ∣ p + ((c.Q - c.r₀) + t * c.Q) := by
        have hdm := Nat.div_add_mod p c.Q
        rw [hp_mod] at hdm
        have : p + ((c.Q - c.r₀) + t * c.Q) = c.Q * (p / c.Q + 1 + t) := by
          have : c.r₀ + (c.Q - c.r₀) = c.Q := by have := c.hr₀_ltQ; omega
          nlinarith
        exact ⟨p / c.Q + 1 + t, this⟩
      exact mem_filter.mpr ⟨mem_Ioo.mpr ⟨by have := c.hr₀_ltQ; omega, hlt_Y2⟩, hQdvd, hndvd⟩
    have hinj : Set.InjOn (fun t => (c.Q - c.r₀) + t * c.Q) (Hgood : Set ℕ) := by
      intro t1 _ t2 _ heq
      dsimp only at heq
      have : t1 * c.Q = t2 * c.Q := by omega
      exact Nat.eq_of_mul_eq_mul_right c.hQp.pos this
    let Hbad := (range M).filter (fun t => c.Q ^ 2 ∣ p + ((c.Q - c.r₀) + t * c.Q))
    have hbad_card : Hbad.card ≤ M / c.Q + 1 := by
      by_cases hne : Hbad.Nonempty
      · obtain ⟨t0, ht0⟩ := hne
        have ht0_dvd : c.Q ^ 2 ∣ p + ((c.Q - c.r₀) + t0 * c.Q) := (mem_filter.mp ht0).2
        have hmod_all : ∀ t ∈ Hbad, t ≡ t0 [MOD c.Q] := by
          intro t ht
          have ht_dvd := (mem_filter.mp ht).2
          rcases le_total t0 t with hle | hle
          · have hsub : c.Q ^ 2 ∣ (t - t0) * c.Q := by
              have hdiff : (p + ((c.Q - c.r₀) + t * c.Q)) - (p + ((c.Q - c.r₀) + t0 * c.Q)) = (t - t0) * c.Q := by
                rw [Nat.sub_mul]; omega
              rw [← hdiff]; exact Nat.dvd_sub ht_dvd ht0_dvd
            rw [sq] at hsub
            have hQt : c.Q ∣ t - t0 := (mul_dvd_mul_iff_right c.hQp.ne_zero).mp hsub
            exact ((Nat.modEq_iff_dvd' hle).mpr hQt).symm
          · have hsub : c.Q ^ 2 ∣ (t0 - t) * c.Q := by
              have hdiff : (p + ((c.Q - c.r₀) + t0 * c.Q)) - (p + ((c.Q - c.r₀) + t * c.Q)) = (t0 - t) * c.Q := by
                rw [Nat.sub_mul]; omega
              rw [← hdiff]; exact Nat.dvd_sub ht0_dvd ht_dvd
            rw [sq] at hsub
            have hQt : c.Q ∣ t0 - t := (mul_dvd_mul_iff_right c.hQp.ne_zero).mp hsub
            exact (Nat.modEq_iff_dvd' hle).mpr hQt
        have hinj_b : Set.InjOn (fun t => t / c.Q) (Hbad : Set ℕ) := by
          intro t1 ht1 t2 ht2 heq
          have hm1 : t1 % c.Q = t0 % c.Q := hmod_all t1 ht1
          have hm2 : t2 % c.Q = t0 % c.Q := hmod_all t2 ht2
          have h1 := Nat.div_add_mod t1 c.Q
          have h2 := Nat.div_add_mod t2 c.Q
          dsimp only at heq
          rw [← h1, ← h2, heq, hm1, hm2]
        have hmaps_b : Hbad.image (fun t => t / c.Q) ⊆ range (M / c.Q + 1) := by
          intro q hq
          obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
          rw [mem_range]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp (mem_filter.mp ht).1).le)
        calc Hbad.card = (Hbad.image (fun t => t / c.Q)).card := (Finset.card_image_of_injOn hinj_b).symm
          _ ≤ (range (M / c.Q + 1)).card := card_le_card hmaps_b
          _ = M / c.Q + 1 := card_range _
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, card_empty]; exact Nat.zero_le _
    have hcard_split : Hgood.card + Hbad.card = M := by
      have hdisj : Disjoint Hgood Hbad := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h1 h2
      have hunion : Hgood ∪ Hbad = range M := by
        ext t; simp only [Hgood, Hbad, mem_union, mem_filter]
        exact ⟨fun h => h.elim And.left And.left, fun ht => (em _).elim (fun h => Or.inr ⟨ht, h⟩) (fun h => Or.inl ⟨ht, h⟩)⟩
      rw [← Finset.card_union_of_disjoint hdisj, hunion, card_range]
    have hM_ge : (c.Y : ℝ) / (2 * (c.Q : ℝ)) - 3 ≤ (M : ℝ) := by
      have hdm : c.Q * M + (c.Y / 2 - c.Q) % c.Q = c.Y / 2 - c.Q := Nat.div_add_mod (c.Y / 2 - c.Q) c.Q
      have hrem : (c.Y / 2 - c.Q) % c.Q < c.Q := Nat.mod_lt (c.Y / 2 - c.Q) c.hQp.pos
      have hY2_dm : 2 * (c.Y / 2) + c.Y % 2 = c.Y := Nat.div_add_mod c.Y 2
      have hY2_rem : c.Y % 2 < 2 := Nat.mod_lt c.Y (by norm_num : 0 < 2)
      have h1 : c.Y ≤ 2 * (c.Q * M + 2 * c.Q + 1) := by omega
      have h1R : (c.Y : ℝ) ≤ 2 * ((c.Q : ℝ) * (M : ℝ) + 2 * (c.Q : ℝ) + 1) := by exact_mod_cast h1
      rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
      have hQ1000R : (1000 : ℝ) ≤ c.Q := by exact_mod_cast c.hQ1000
      nlinarith
    have hMQ_le : ((M / c.Q : ℕ) : ℝ) ≤ (M : ℝ) / (c.Q : ℝ) := by
      rw [le_div_iff₀ hQpos]; exact_mod_cast Nat.div_mul_le_self M c.Q
    have hcard_good_R : (M : ℝ) - ((M : ℝ) / (c.Q : ℝ) + 1) ≤ (Hgood.card : ℝ) := by
      have h1 : (M : ℝ) ≤ (Hgood.card : ℝ) + ((M / c.Q : ℕ) : ℝ) + 1 := by
        have : M ≤ Hgood.card + (M / c.Q + 1) := by omega
        exact_mod_cast this
      linarith
    have hHgood_le_target : (Hgood.card : ℝ) ≤
        (((Ioo 0 (c.Y / 2)).filter (fun h => c.Q ∣ p + h ∧ ¬ c.Q ^ 2 ∣ p + h)).card : ℝ) := by
      have hnat : Hgood.card ≤ ((Ioo 0 (c.Y / 2)).filter (fun h => c.Q ∣ p + h ∧ ¬ c.Q ^ 2 ∣ p + h)).card := by
        rw [← Finset.card_image_of_injOn hinj]; exact card_le_card hmaps
      exact_mod_cast hnat
    have hQ1000R : (1000 : ℝ) ≤ c.Q := by exact_mod_cast c.hQ1000
    have hY_ge1000Q : 1000 * (c.Q : ℝ) ≤ (c.Y : ℝ) := by exact_mod_cast c.hY_ge_1000Q
    have h1 : (M : ℝ) - ((M : ℝ) / (c.Q : ℝ) + 1) = (M : ℝ) * (1 - 1 / (c.Q : ℝ)) - 1 := by ring
    have h2 : (999 / 1000 : ℝ) ≤ 1 - 1 / (c.Q : ℝ) := by
      have : 1 / (c.Q : ℝ) ≤ 1 / 1000 := one_div_le_one_div_of_le (by norm_num) hQ1000R
      linarith
    have h3 : (c.Y : ℝ) / (3 * (c.Q : ℝ)) ≤ ((c.Y : ℝ) / (2 * (c.Q : ℝ)) - 3) * (999 / 1000) - 1 := by
      have : (1000 : ℝ) ≤ (c.Y : ℝ) / (c.Q : ℝ) := (le_div_iff₀ hQpos).mpr (by linarith)
      have hA : (c.Y : ℝ) / (3 * (c.Q : ℝ)) = (1 / 3 : ℝ) * ((c.Y : ℝ) / (c.Q : ℝ)) := by ring
      have hB' : (c.Y : ℝ) / (2 * (c.Q : ℝ)) = (1 / 2 : ℝ) * ((c.Y : ℝ) / (c.Q : ℝ)) := by ring
      rw [hA, hB']; linarith
    have h4 : ((c.Y : ℝ) / (2 * (c.Q : ℝ)) - 3) * (999 / 1000) - 1 ≤ (M : ℝ) * (1 - 1 / (c.Q : ℝ)) - 1 := by
      have := mul_le_mul hM_ge h2 (by norm_num) (Nat.cast_nonneg M); linarith
    linarith
  let Pairs_kp := c.Kset.sigma (fun k => c.Pnear k)
  let Pairs_ph := P_mid.sigma (fun p => (Ioo 0 (c.Y / 2)).filter (fun h => c.Q ∣ p + h ∧ ¬ c.Q ^ 2 ∣ p + h))
  have hinj_pair : Set.InjOn (fun x : (p : ℕ) × ℕ => (⟨x.1 + x.2, x.1⟩ : (k : ℕ) × ℕ)) (Pairs_ph : Set ((p : ℕ) × ℕ)) := by
    intro x _ y _ heq
    have h2 : x.1 = y.1 := congrArg Sigma.snd heq
    have h1 : x.1 + x.2 = y.1 + y.2 := congrArg Sigma.fst heq
    exact Sigma.ext h2 (heq_of_eq (by omega))
  have hmaps_pair : Pairs_ph.image (fun x : (p : ℕ) × ℕ => (⟨x.1 + x.2, x.1⟩ : (k : ℕ) × ℕ)) ⊆ Pairs_kp := by
    intro z hz
    obtain ⟨⟨p, h⟩, hph, rfl⟩ := mem_image.mp hz
    obtain ⟨hp, hh⟩ := mem_sigma.mp hph
    dsimp only at hp hh ⊢
    obtain ⟨hpI, hpr, hpmod⟩ := mem_filter.mp hp
    obtain ⟨hhI, hQd, hQ2d⟩ := mem_filter.mp hh
    have hp1 := (mem_Ioc.mp hpI).1; have hp2 := (mem_Ioc.mp hpI).2
    have hh1 := (mem_Ioo.mp hhI).1; have hh2 := (mem_Ioo.mp hhI).2
    have hYK := c.hY_le_K
    rw [mem_sigma]; dsimp only
    exact ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, hQd, hQ2d⟩,
      mem_filter.mpr ⟨mem_Ioo.mpr ⟨by omega, by omega⟩, hpr, hpmod⟩⟩
  have hcard_le_sum : (Pairs_ph.card : ℝ) ≤ ∑ k ∈ c.Kset, ((c.Pnear k).card : ℝ) := by
    have hnat : Pairs_ph.card ≤ ∑ k ∈ c.Kset, (c.Pnear k).card := by
      rw [← Finset.card_sigma, ← Finset.card_image_of_injOn hinj_pair]
      exact card_le_card hmaps_pair
    exact_mod_cast hnat
  have hPairs_ph_ge : ((c.K : ℝ) / (4 * (c.Q : ℝ) * c.L) - (c.Y : ℝ)) * ((c.Y : ℝ) / (3 * (c.Q : ℝ))) ≤ (Pairs_ph.card : ℝ) := by
    have hsum_eq : (Pairs_ph.card : ℝ) = ∑ p ∈ P_mid,
        (((Ioo 0 (c.Y / 2)).filter (fun h => c.Q ∣ p + h ∧ ¬ c.Q ^ 2 ∣ p + h)).card : ℝ) := by
      rw [Finset.card_sigma, Nat.cast_sum]
    rw [hsum_eq]
    calc ((c.K : ℝ) / (4 * (c.Q : ℝ) * c.L) - (c.Y : ℝ)) * ((c.Y : ℝ) / (3 * (c.Q : ℝ)))
        ≤ (P_mid.card : ℝ) * ((c.Y : ℝ) / (3 * (c.Q : ℝ))) := mul_le_mul_of_nonneg_right hPmid_card (by positivity)
      _ = ∑ _p ∈ P_mid, ((c.Y : ℝ) / (3 * (c.Q : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum hh_count
  have hY_le_KQL : (c.Y : ℝ) ≤ (c.K : ℝ) / (20 * (c.Q : ℝ) * c.L) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (c.Y : ℝ) * (20 * (c.Q : ℝ) * c.L) ≤
        Real.exp (c.L ^ ((3 : ℝ) / 5) + Real.log (20 * (c.Q : ℝ)) + Real.log c.L) := by
      calc (c.Y : ℝ) * (20 * (c.Q : ℝ) * c.L)
          ≤ Real.exp (c.L ^ ((3 : ℝ) / 5)) * Real.exp (Real.log (20 * (c.Q : ℝ)) + Real.log c.L) := by
            rw [Real.exp_add, Real.exp_log (by positivity), Real.exp_log hLpos]
            exact mul_le_mul_of_nonneg_right c.hY_le_exp (by positivity)
        _ = Real.exp (c.L ^ ((3 : ℝ) / 5) + Real.log (20 * (c.Q : ℝ)) + Real.log c.L) := by
            rw [← Real.exp_add]; congr 1; ring
    have h2 : c.L ^ ((3 : ℝ) / 5) + Real.log (20 * (c.Q : ℝ)) + Real.log c.L ≤ c.L := by
      have hB1 : (1 : ℝ) ≤ c.B := by exact_mod_cast (by have := c.hB; omega : 1 ≤ c.B)
      have hlog20Q : Real.log (20 * (c.Q : ℝ)) ≤ Real.log (10000 * (c.Q : ℝ) * (c.B : ℝ)) :=
        Real.log_le_log (by positivity) (by nlinarith)
      have hlogL_nn : 0 ≤ Real.log c.L := Real.log_nonneg (by linarith [c.hL10])
      linarith [c.hL3, c.hL4, c.hL35_ge, c.hL10, hlogL_nn]
    calc (c.Y : ℝ) * (20 * (c.Q : ℝ) * c.L)
        ≤ Real.exp (c.L ^ ((3 : ℝ) / 5) + Real.log (20 * (c.Q : ℝ)) + Real.log c.L) := h1
      _ ≤ Real.exp c.L := Real.exp_le_exp.mpr h2
      _ = (c.K : ℝ) := Real.exp_log hKpos
  have hfinal_raw : (c.K : ℝ) * (c.Y : ℝ) / (20 * (c.Q : ℝ) ^ 2 * c.L) ≤
      ((c.K : ℝ) / (4 * (c.Q : ℝ) * c.L) - (c.Y : ℝ)) * ((c.Y : ℝ) / (3 * (c.Q : ℝ))) := by
    have h1 : (c.K : ℝ) / (5 * (c.Q : ℝ) * c.L) ≤ (c.K : ℝ) / (4 * (c.Q : ℝ) * c.L) - (c.Y : ℝ) := by
      have : (c.K : ℝ) / (4 * (c.Q : ℝ) * c.L) - (c.K : ℝ) / (20 * (c.Q : ℝ) * c.L) =
          (c.K : ℝ) / (5 * (c.Q : ℝ) * c.L) := by field_simp [hQpos.ne', hLpos.ne']; ring
      linarith
    calc (c.K : ℝ) * (c.Y : ℝ) / (20 * (c.Q : ℝ) ^ 2 * c.L)
        ≤ (c.K : ℝ) * (c.Y : ℝ) / (15 * (c.Q : ℝ) ^ 2 * c.L) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [pow_pos hQpos 2])
      _ = ((c.K : ℝ) / (5 * (c.Q : ℝ) * c.L)) * ((c.Y : ℝ) / (3 * (c.Q : ℝ))) := by
          field_simp [hQpos.ne', hLpos.ne']; ring
      _ ≤ ((c.K : ℝ) / (4 * (c.Q : ℝ) * c.L) - (c.Y : ℝ)) * ((c.Y : ℝ) / (3 * (c.Q : ℝ))) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
  linarith

private lemma CoverCtx.hE0_bd (c : CoverCtx) :
    ∑ k ∈ c.E0, ((c.Pnear k).card : ℝ) ≤ (c.K : ℝ) * (c.Y : ℝ) / (200 * (c.Q : ℝ) ^ 2 * c.L) := by
  have hKpos := c.hKpos; have hQpos := c.hQpos; have hBpos := c.hBpos; have hYpos := c.hYpos; have hLpos := c.hLpos
  have hE0_sub : c.E0 ⊆ ((Icc 1 (c.Y + 1)) ×ˢ ((Ico 1 c.B) ×ˢ (range (Nat.log c.Q (10 * c.K) + 1)))).image
      (fun x : ℕ × (ℕ × ℕ) => x.2.1 * c.Q ^ x.2.2 + x.1 - 1) := by
    intro k hk
    obtain ⟨hkK, t, ht, hzu⟩ := c.mem_E0.mp hk
    have hk1 := (mem_Ioc.mp (mem_filter.mp hkK).1).1; have hk10 := (mem_Ioc.mp (mem_filter.mp hkK).1).2
    have ht1 := (mem_Icc.mp ht).1; have htY := (mem_Icc.mp ht).2
    have hYK := c.hY_le_K
    let m := k - t + 1
    have hm1 : 1 ≤ m := by dsimp only [m]; omega
    have hm10 : m ≤ 10 * c.K := by dsimp only [m]; omega
    let a := m.factorization c.Q
    let u := m / c.Q ^ a
    have hmul : u * c.Q ^ a = m := by rw [mul_comm]; exact Nat.mul_div_cancel' (Nat.ordProj_dvd m c.Q)
    have hu1 : 1 ≤ u := Nat.div_pos (Nat.le_of_dvd hm1 (Nat.ordProj_dvd m c.Q)) (pow_pos c.hQp.pos a)
    have ha_le : a ≤ Nat.log c.Q (10 * c.K) := Nat.le_log_of_pow_le c.hQp.one_lt ((Nat.le_of_dvd hm1 (Nat.ordProj_dvd m c.Q)).trans hm10)
    refine mem_image.mpr ⟨(t, (u, a)), mem_product.mpr ⟨ht, mem_product.mpr ⟨mem_Ico.mpr ⟨hu1, hzu⟩,
      mem_range.mpr (Nat.lt_succ_of_le ha_le)⟩⟩, ?_⟩
    dsimp only [m] at hmul; rw [hmul]; omega
  have hE0_card : (c.E0.card : ℝ) ≤ 2 * (c.Y : ℝ) * (c.B : ℝ) * (2 * c.L) := by
    have hnat : c.E0.card ≤ (c.Y + 1) * (c.B * (Nat.log c.Q (10 * c.K) + 1)) := by
      calc c.E0.card ≤ (((Icc 1 (c.Y + 1)) ×ˢ ((Ico 1 c.B) ×ˢ (range (Nat.log c.Q (10 * c.K) + 1)))).image _).card :=
            card_le_card hE0_sub
        _ ≤ ((Icc 1 (c.Y + 1)) ×ˢ ((Ico 1 c.B) ×ˢ (range (Nat.log c.Q (10 * c.K) + 1)))).card := card_image_le
        _ = (c.Y + 1) * ((c.B - 1) * (Nat.log c.Q (10 * c.K) + 1)) := by
            rw [card_product, card_product, Nat.card_Icc, Nat.add_sub_cancel, Nat.card_Ico, card_range]
        _ ≤ (c.Y + 1) * (c.B * (Nat.log c.Q (10 * c.K) + 1)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.sub_le c.B 1))
    have hlog10 : (Nat.log c.Q (10 * c.K) : ℝ) + 1 ≤ 2 * c.L := by
      have h1 : (Nat.log c.Q (10 * c.K) : ℝ) * Real.log (c.Q : ℝ) ≤ Real.log ((10 * c.K : ℕ) : ℝ) := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_log_le_self c.Q (by have := (le_max_left 1000000 (100 * c.Q ^ 2)).trans c.hKbig; omega))
      have h2 : Real.log ((10 * c.K : ℕ) : ℝ) ≤ c.L + 4 := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hKpos.ne']
        linarith [CoverCtx.hlog10_le4]
      nlinarith [c.hlogQ_ge2, c.hL10, Nat.cast_nonneg (α := ℝ) (Nat.log c.Q (10 * c.K))]
    have hcast : (c.E0.card : ℝ) ≤ ((c.Y : ℝ) + 1) * ((c.B : ℝ) * ((Nat.log c.Q (10 * c.K) : ℝ) + 1)) := by
      exact_mod_cast hnat
    have hY1 : (c.Y : ℝ) + 1 ≤ 2 * (c.Y : ℝ) := by
      have : (1 : ℝ) ≤ c.Y := by exact_mod_cast (by have := c.hY_ge_1000; omega : 1 ≤ c.Y)
      linarith
    nlinarith [mul_le_mul hY1 (mul_le_mul_of_nonneg_left hlog10 hBpos.le) (by positivity) (by positivity)]
  calc ∑ k ∈ c.E0, ((c.Pnear k).card : ℝ)
      ≤ ∑ _k ∈ c.E0, (c.Y : ℝ) := sum_le_sum fun k _ => c.hPnear_le_Y k
    _ = (c.E0.card : ℝ) * (c.Y : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (c.Y : ℝ) * (c.B : ℝ) * (2 * c.L)) * (c.Y : ℝ) := mul_le_mul_of_nonneg_right hE0_card hYpos.le
    _ ≤ (c.K : ℝ) * (c.Y : ℝ) / (200 * (c.Q : ℝ) ^ 2 * c.L) := by
        rw [le_div_iff₀ (by positivity)]
        have h1 : 2 * (c.Y : ℝ) * (c.B : ℝ) * (2 * c.L) * (c.Y : ℝ) * (200 * (c.Q : ℝ) ^ 2 * c.L) =
            (800 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) * c.L ^ 2 * (c.Y : ℝ)) * (c.Y : ℝ) := by ring
        rw [h1]
        have h2 : 800 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) * c.L ^ 2 * (c.Y : ℝ) ≤ (c.K : ℝ) := by
          have hlog_bd : Real.log (800 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) * c.L ^ 2 * (c.Y : ℝ)) ≤ c.L := by
            rw [Real.log_mul (by positivity) hYpos.ne', Real.log_mul (by positivity) (pow_pos hLpos 2).ne',
              Real.log_pow]
            have h800 : 800 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) ≤ (10000 * (c.Q : ℝ) * (c.B : ℝ)) ^ 2 := by
              have hQ1 : (1 : ℝ) ≤ c.Q := by exact_mod_cast (by have := c.hQ1000; omega : 1 ≤ c.Q)
              have hB1 : (1 : ℝ) ≤ c.B := by exact_mod_cast (by have := c.hB; omega : 1 ≤ c.B)
              nlinarith
            have hlog800 : Real.log (800 * (c.Q : ℝ) ^ 2 * (c.B : ℝ)) ≤ 2 * Real.log (10000 * (c.Q : ℝ) * (c.B : ℝ)) := by
              calc Real.log (800 * (c.Q : ℝ) ^ 2 * (c.B : ℝ))
                  ≤ Real.log ((10000 * (c.Q : ℝ) * (c.B : ℝ)) ^ 2) := Real.log_le_log (by positivity) h800
                _ = 2 * Real.log (10000 * (c.Q : ℝ) * (c.B : ℝ)) := by rw [Real.log_pow]; norm_num
            push_cast; linarith [c.hL3, c.hL4, c.hlogY_hi, c.hL35_ge]
          calc 800 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) * c.L ^ 2 * (c.Y : ℝ)
              = Real.exp (Real.log (800 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) * c.L ^ 2 * (c.Y : ℝ))) := (Real.exp_log (by positivity)).symm
            _ ≤ Real.exp c.L := Real.exp_le_exp.mpr hlog_bd
            _ = (c.K : ℝ) := Real.exp_log hKpos
        exact mul_le_mul_of_nonneg_right h2 hYpos.le

private lemma CoverCtx.hE1_bd (c : CoverCtx) :
    ∑ k ∈ c.E1, ((c.Pnear k).card : ℝ) ≤ (c.K : ℝ) * (c.Y : ℝ) / (200 * (c.Q : ℝ) ^ 2 * c.L) := by
  have hKpos := c.hKpos; have hQpos := c.hQpos; have hBpos := c.hBpos; have hYpos := c.hYpos; have hLpos := c.hLpos
  let Qmax := Nat.sqrt (10 * c.K)
  have hE1_sub : c.E1 ⊆ c.Dset.biUnion (fun d => (Ioc (2 * c.Y) Qmax).biUnion (fun q =>
      (Icc 1 (10 * c.K)).filter (fun k => k ≡ d - 1 [MOD q ^ 2]))) := by
    intro k hk
    obtain ⟨hkK, d, hd, q, _, hq2Y, hq2dvd⟩ := mem_filter.mp hk
    have hk1 := (mem_Ioc.mp (mem_filter.mp hkK).1).1; have hk10 := (mem_Ioc.mp (mem_filter.mp hkK).1).2
    have hd1 := (mem_Icc.mp (mem_filter.mp hd).1).1; have hdY := (mem_Icc.mp (mem_filter.mp hd).1).2
    have hYK := c.hY_le_K
    have hqle : q ≤ Qmax := Nat.le_sqrt.mpr (by
      have h1 : q ^ 2 ≤ k - d + 1 := Nat.le_of_dvd (by omega) hq2dvd
      rw [sq] at h1; omega)
    refine mem_biUnion.mpr ⟨d, hd, mem_biUnion.mpr ⟨q, mem_Ioc.mpr ⟨hq2Y, hqle⟩,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hk10⟩, ?_⟩⟩⟩
    have hsub_eq : k - (d - 1) = k - d + 1 := by omega
    exact ((Nat.modEq_iff_dvd' (by omega)).mpr (hsub_eq.symm ▸ hq2dvd)).symm
  have hE1_card : (c.E1.card : ℝ) ≤ (c.Dset.card : ℝ) * (5 * (c.K : ℝ) / (c.Y : ℝ) + Real.sqrt (10 * (c.K : ℝ))) := by
    have h1 : (c.E1.card : ℝ) ≤ ∑ d ∈ c.Dset, ∑ q ∈ Ioc (2 * c.Y) Qmax, ((10 * c.K : ℝ) / ((q : ℝ) ^ 2) + 1) := by
      calc (c.E1.card : ℝ)
          ≤ ∑ d ∈ c.Dset, ∑ q ∈ Ioc (2 * c.Y) Qmax,
              (((Icc 1 (10 * c.K)).filter (fun k => k ≡ d - 1 [MOD q ^ 2])).card : ℝ) := by
            have hnat : c.E1.card ≤ ∑ d ∈ c.Dset, ∑ q ∈ Ioc (2 * c.Y) Qmax,
                ((Icc 1 (10 * c.K)).filter (fun k => k ≡ d - 1 [MOD q ^ 2])).card :=
              (card_le_card hE1_sub).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le))
            exact_mod_cast hnat
        _ ≤ ∑ d ∈ c.Dset, ∑ q ∈ Ioc (2 * c.Y) Qmax, ((10 * c.K : ℝ) / ((q : ℝ) ^ 2) + 1) := by
            refine sum_le_sum fun d _ => sum_le_sum fun q hq => ?_
            have hqpos : 0 < q ^ 2 := pow_pos (by have := (mem_Ioc.mp hq).1; omega) 2
            have hqposR : (0 : ℝ) < (q : ℝ) ^ 2 := by exact_mod_cast hqpos
            have hc := card_Icc_modEq_le (10 * c.K) (q ^ 2) (d - 1) hqpos
            have hcR : (((Icc 1 (10 * c.K)).filter (fun k => k ≡ d - 1 [MOD q ^ 2])).card : ℝ) ≤
                ((10 * c.K / q ^ 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hc
            have hdiv : ((10 * c.K / q ^ 2 : ℕ) : ℝ) ≤ (10 * c.K : ℝ) / ((q : ℝ) ^ 2) := by
              rw [le_div_iff₀ hqposR]
              exact_mod_cast Nat.div_mul_le_self (10 * c.K) (q ^ 2)
            linarith
    have hinner : ∑ q ∈ Ioc (2 * c.Y) Qmax, ((10 * c.K : ℝ) / ((q : ℝ) ^ 2) + 1) ≤
        5 * (c.K : ℝ) / (c.Y : ℝ) + Real.sqrt (10 * (c.K : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hsum1 : ∑ q ∈ Ioc (2 * c.Y) Qmax, (10 * c.K : ℝ) / ((q : ℝ) ^ 2) ≤ 5 * (c.K : ℝ) / (c.Y : ℝ) := by
        have hrew : ∑ q ∈ Ioc (2 * c.Y) Qmax, (10 * c.K : ℝ) / ((q : ℝ) ^ 2) =
            (10 * (c.K : ℝ)) * ∑ q ∈ Ioc (2 * c.Y) Qmax, (1 : ℝ) / ((q : ℝ) ^ 2) := by
          rw [Finset.mul_sum]; refine sum_congr rfl fun _ _ => by ring
        rw [hrew]
        calc (10 * (c.K : ℝ)) * ∑ q ∈ Ioc (2 * c.Y) Qmax, (1 : ℝ) / ((q : ℝ) ^ 2)
            ≤ (10 * (c.K : ℝ)) * (1 / ((2 * c.Y : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le (by have := c.hY_ge_1000; omega)) (by positivity)
          _ = 5 * (c.K : ℝ) / (c.Y : ℝ) := by push_cast; field_simp [hYpos.ne']; ring
      have hcardQ : ((Ioc (2 * c.Y) Qmax).card : ℝ) ≤ Real.sqrt (10 * (c.K : ℝ)) := by
        have h1 : (Ioc (2 * c.Y) Qmax).card ≤ Qmax := by rw [Nat.card_Ioc]; omega
        have h2 : (Qmax : ℝ) ≤ Real.sqrt (10 * (c.K : ℝ)) := by
          rw [Real.le_sqrt (Nat.cast_nonneg _) (by positivity), sq]
          exact_mod_cast Nat.sqrt_le (10 * c.K)
        exact (by exact_mod_cast h1 : ((Ioc (2 * c.Y) Qmax).card : ℝ) ≤ Qmax).trans h2
      linarith
    calc (c.E1.card : ℝ) ≤ ∑ _d ∈ c.Dset, (5 * (c.K : ℝ) / (c.Y : ℝ) + Real.sqrt (10 * (c.K : ℝ))) :=
          h1.trans (sum_le_sum fun _ _ => hinner)
      _ = (c.Dset.card : ℝ) * (5 * (c.K : ℝ) / (c.Y : ℝ) + Real.sqrt (10 * (c.K : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hsqrt_le : Real.sqrt (10 * (c.K : ℝ)) ≤ 5 * (c.K : ℝ) / (c.Y : ℝ) := by
    rw [le_div_iff₀ hYpos]
    have hsq : (Real.sqrt (10 * (c.K : ℝ)) * (c.Y : ℝ)) ^ 2 ≤ (5 * (c.K : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hY2_le : (c.Y : ℝ) ^ 2 ≤ (c.K : ℝ) := by
        have hY1 : (1 : ℝ) ≤ c.Y := by exact_mod_cast (by have := c.hY_ge_1000; omega : 1 ≤ c.Y)
        exact (pow_le_pow_right₀ hY1 (by omega : 2 ≤ 4)).trans c.hY_le_K14
      nlinarith
    nlinarith [Real.sqrt_nonneg (10 * (c.K : ℝ))]
  calc ∑ k ∈ c.E1, ((c.Pnear k).card : ℝ)
      ≤ ∑ _k ∈ c.E1, (c.Y : ℝ) := sum_le_sum fun k _ => c.hPnear_le_Y k
    _ = (c.E1.card : ℝ) * (c.Y : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (c.Dset.card : ℝ) * (10 * (c.K : ℝ) / (c.Y : ℝ)) * (c.Y : ℝ) := by
        have : (c.E1.card : ℝ) ≤ (c.Dset.card : ℝ) * (10 * (c.K : ℝ) / (c.Y : ℝ)) := by
          have h10 : 5 * (c.K : ℝ) / (c.Y : ℝ) + 5 * (c.K : ℝ) / (c.Y : ℝ) = 10 * (c.K : ℝ) / (c.Y : ℝ) := by ring
          nlinarith [hE1_card, hsqrt_le, Nat.cast_nonneg (α := ℝ) c.Dset.card]
        exact mul_le_mul_of_nonneg_right this hYpos.le
    _ = (c.Dset.card : ℝ) * (10 * (c.K : ℝ)) := by field_simp [hYpos.ne']
    _ ≤ (2 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5)) * (10 * (c.K : ℝ)) := mul_le_mul_of_nonneg_right c.hDset_card (by positivity)
    _ ≤ (c.K : ℝ) * (c.Y : ℝ) / (200 * (c.Q : ℝ) ^ 2 * c.L) := by
        rw [le_div_iff₀ (by positivity)]
        have h1 : 2 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) * (10 * (c.K : ℝ)) * (200 * (c.Q : ℝ) ^ 2 * c.L) =
            (c.K : ℝ) * (4000 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) * c.L) := by ring
        rw [h1]
        refine mul_le_mul_of_nonneg_left ?_ hKpos.le
        have hlog_bd : Real.log (4000 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) * c.L) ≤ Real.log (c.Y : ℝ) := by
          rw [Real.log_mul (by positivity) hLpos.ne', Real.log_mul (by positivity) (Real.rpow_pos_of_pos hLpos _).ne',
            Real.log_rpow hLpos]
          have h4000 : 4000 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) ≤ (10000 * (c.Q : ℝ) * (c.B : ℝ)) ^ 2 := by
            have hQ1 : (1 : ℝ) ≤ c.Q := by exact_mod_cast (by have := c.hQ1000; omega : 1 ≤ c.Q)
            have hB1 : (1 : ℝ) ≤ c.B := by exact_mod_cast (by have := c.hB; omega : 1 ≤ c.B)
            nlinarith
          have hlog4000 : Real.log (4000 * (c.Q : ℝ) ^ 2 * (c.B : ℝ)) ≤ 2 * Real.log (10000 * (c.Q : ℝ) * (c.B : ℝ)) := by
            calc Real.log (4000 * (c.Q : ℝ) ^ 2 * (c.B : ℝ))
                ≤ Real.log ((10000 * (c.Q : ℝ) * (c.B : ℝ)) ^ 2) := Real.log_le_log (by positivity) h4000
              _ = 2 * Real.log (10000 * (c.Q : ℝ) * (c.B : ℝ)) := by rw [Real.log_pow]; norm_num
          have hlogL_le : Real.log c.L ≤ (1 / 20 : ℝ) * c.L ^ ((3 : ℝ) / 5) := by
            have h1 : 10 * Real.log c.L ≤ (1 / 4 : ℝ) * c.L ^ ((2 : ℝ) / 5) := by
              have hnn : 0 ≤ Real.log (2 * c.L ^ ((3 : ℝ) / 5)) := Real.log_nonneg (by linarith [c.hL35_ge])
              linarith [c.hL6]
            have h2 : c.L ^ ((2 : ℝ) / 5) ≤ c.L ^ ((3 : ℝ) / 5) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith [c.hL10]) (by norm_num)
            linarith [c.hL35_ge]
          linarith [c.hL3, c.hlogY_lo, c.hL35_ge]
        calc 4000 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) * c.L
            = Real.exp (Real.log (4000 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) * c.L)) := (Real.exp_log (by positivity)).symm
          _ ≤ Real.exp (Real.log (c.Y : ℝ)) := Real.exp_le_exp.mpr hlog_bd
          _ = (c.Y : ℝ) := Real.exp_log hYpos

private lemma CoverCtx.hE2_bd (c : CoverCtx) :
    ∑ k ∈ c.E2, ((c.Pnear k).card : ℝ) ≤ (c.K : ℝ) * (c.Y : ℝ) / (200 * (c.Q : ℝ) ^ 2 * c.L) := by
  have hKpos := c.hKpos; have hQpos := c.hQpos; have hBpos := c.hBpos; have hYpos := c.hYpos; have hLpos := c.hLpos
  let Sm := (Icc 1 (10 * c.K)).filter (fun m => ∀ q, q.Prime → q ∣ m → q ≤ 2 * c.Y)
  have hE2_sub : c.E2 ⊆ c.Dset.biUnion (fun d => Sm.image (fun m => m + d - 1)) := by
    intro k hk
    obtain ⟨hkK, d, hd, hsm⟩ := mem_filter.mp hk
    have hk1 := (mem_Ioc.mp (mem_filter.mp hkK).1).1; have hk10 := (mem_Ioc.mp (mem_filter.mp hkK).1).2
    have hd1 := (mem_Icc.mp (mem_filter.mp hd).1).1; have hdY := (mem_Icc.mp (mem_filter.mp hd).1).2
    have hYK := c.hY_le_K
    refine mem_biUnion.mpr ⟨d, hd, mem_image.mpr ⟨k - d + 1,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hsm⟩, by omega⟩⟩
  have hSm_bd : (Sm.card : ℝ) ≤ (10 * (c.K : ℝ)) / c.L ^ 10 := by
    have hK_ge100 : 100 ≤ 10 * c.K := by have := (le_max_left 1000000 (100 * c.Q ^ 2)).trans c.hKbig; omega
    have h2Y_ge16 : 16 ≤ 2 * c.Y := by have := c.hY_ge_1000; omega
    have hrank := smooth_count_rankin (X := 10 * c.K) (Y := 2 * c.Y) hK_ge100 h2Y_ge16
    have hlog2Y_pos : 0 < Real.log ((2 * c.Y : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by have := c.hY_ge_1000; omega : 1 < 2 * c.Y))
    have hlog2Y_le : Real.log ((2 * c.Y : ℕ) : ℝ) ≤ 2 * c.L ^ ((3 : ℝ) / 5) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hYpos.ne']
      linarith [Real.log_two_lt_d9, c.hlogY_hi, c.hL35_ge]
    have hlog10K_ge : c.L ≤ Real.log ((10 * c.K : ℕ) : ℝ) :=
      Real.log_le_log hKpos (by exact_mod_cast (by omega : c.K ≤ 10 * c.K))
    have hratio : (1 / 4 : ℝ) * c.L ^ ((2 : ℝ) / 5) ≤
        Real.log ((10 * c.K : ℕ) : ℝ) / (2 * Real.log ((2 * c.Y : ℕ) : ℝ)) := by
      have h1 : c.L / (4 * c.L ^ ((3 : ℝ) / 5)) ≤ Real.log ((10 * c.K : ℕ) : ℝ) / (2 * Real.log ((2 * c.Y : ℕ) : ℝ)) :=
        div_le_div₀ (by positivity) hlog10K_ge (by positivity) (by linarith)
      have h2 : c.L / (4 * c.L ^ ((3 : ℝ) / 5)) = (1 / 4 : ℝ) * c.L ^ ((2 : ℝ) / 5) := by
        have hsub : c.L / c.L ^ ((3 : ℝ) / 5) = c.L ^ ((2 : ℝ) / 5) := by
          conv_lhs => arg 1; rw [← Real.rpow_one c.L]
          rw [← Real.rpow_sub hLpos]; congr 1; norm_num
        calc c.L / (4 * c.L ^ ((3 : ℝ) / 5)) = (1 / 4 : ℝ) * (c.L / c.L ^ ((3 : ℝ) / 5)) := by ring
          _ = (1 / 4 : ℝ) * c.L ^ ((2 : ℝ) / 5) := by rw [hsub]
      linarith
    have hloglog2Y : Real.log (Real.log ((2 * c.Y : ℕ) : ℝ)) ≤ Real.log (2 * c.L ^ ((3 : ℝ) / 5)) :=
      Real.log_le_log hlog2Y_pos hlog2Y_le
    have hexp_le : Real.exp (-(Real.log ((10 * c.K : ℕ) : ℝ)) / (2 * Real.log ((2 * c.Y : ℕ) : ℝ)) +
        16 * Real.log (Real.log ((2 * c.Y : ℕ) : ℝ)) + 40) ≤ 1 / c.L ^ 10 := by
      have h1 : -(Real.log ((10 * c.K : ℕ) : ℝ)) / (2 * Real.log ((2 * c.Y : ℕ) : ℝ)) +
          16 * Real.log (Real.log ((2 * c.Y : ℕ) : ℝ)) + 40 ≤ -(10 * Real.log c.L) := by
        have hneg : -(Real.log ((10 * c.K : ℕ) : ℝ)) / (2 * Real.log ((2 * c.Y : ℕ) : ℝ)) =
            -(Real.log ((10 * c.K : ℕ) : ℝ) / (2 * Real.log ((2 * c.Y : ℕ) : ℝ))) := by ring
        linarith [c.hL6, hratio, hloglog2Y]
      calc _ ≤ Real.exp (-(10 * Real.log c.L)) := Real.exp_le_exp.mpr h1
        _ = 1 / c.L ^ 10 := by
            rw [Real.exp_neg, show (10 : ℝ) * Real.log c.L = ((10 : ℕ) : ℝ) * Real.log c.L by norm_num,
              ← Real.log_pow, Real.exp_log (pow_pos hLpos 10), one_div]
    calc (Sm.card : ℝ) ≤ ((10 * c.K : ℕ) : ℝ) * Real.exp _ := hrank
      _ ≤ ((10 * c.K : ℕ) : ℝ) * (1 / c.L ^ 10) := mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ = 10 * (c.K : ℝ) / c.L ^ 10 := by push_cast; ring
  have hE2_card : (c.E2.card : ℝ) ≤ (c.Dset.card : ℝ) * (10 * (c.K : ℝ) / c.L ^ 10) := by
    have hnat : c.E2.card ≤ c.Dset.card * Sm.card := by
      calc c.E2.card ≤ ∑ _d ∈ c.Dset, (Sm.image (fun m => m + _d - 1)).card :=
            (card_le_card hE2_sub).trans Finset.card_biUnion_le
        _ ≤ ∑ _d ∈ c.Dset, Sm.card := sum_le_sum fun _ _ => card_image_le
        _ = c.Dset.card * Sm.card := by rw [Finset.sum_const, smul_eq_mul]
    have hR : (c.E2.card : ℝ) ≤ (c.Dset.card : ℝ) * (Sm.card : ℝ) := by exact_mod_cast hnat
    exact hR.trans (mul_le_mul_of_nonneg_left hSm_bd (Nat.cast_nonneg _))
  calc ∑ k ∈ c.E2, ((c.Pnear k).card : ℝ)
      ≤ ∑ _k ∈ c.E2, (c.Y : ℝ) := sum_le_sum fun k _ => c.hPnear_le_Y k
    _ = (c.E2.card : ℝ) * (c.Y : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5)) * (10 * (c.K : ℝ) / c.L ^ 10)) * (c.Y : ℝ) :=
        mul_le_mul_of_nonneg_right (hE2_card.trans (mul_le_mul_of_nonneg_right c.hDset_card (by positivity))) hYpos.le
    _ ≤ (c.K : ℝ) * (c.Y : ℝ) / (200 * (c.Q : ℝ) ^ 2 * c.L) := by
        rw [le_div_iff₀ (by positivity)]
        have h1 : 2 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) * (10 * (c.K : ℝ) / c.L ^ 10) * (c.Y : ℝ) * (200 * (c.Q : ℝ) ^ 2 * c.L) =
            ((c.K : ℝ) * (c.Y : ℝ)) * (4000 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) / c.L ^ 9) := by
          field_simp [hLpos.ne']; ring
        rw [h1]
        have h2 : 4000 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) / c.L ^ 9 ≤ 1 := by
          rw [div_le_one (pow_pos hLpos 9)]
          have hA : 4000 * (c.Q : ℝ) ^ 2 * (c.B : ℝ) ≤ c.L ^ ((1 : ℝ) / 10) := by
            have hQ1 : (1 : ℝ) ≤ c.Q := by exact_mod_cast (by have := c.hQ1000; omega : 1 ≤ c.Q)
            have hB1 : (1 : ℝ) ≤ c.B := by exact_mod_cast (by have := c.hB; omega : 1 ≤ c.B)
            have hQ2 : (c.Q : ℝ) ^ 2 ≤ (c.Q : ℝ) ^ 4 := pow_le_pow_right₀ hQ1 (by omega)
            have hB3 : (c.B : ℝ) ≤ (c.B : ℝ) ^ 3 := by
              calc (c.B : ℝ) = (c.B : ℝ) ^ (1 : ℕ) := (pow_one _).symm
                _ ≤ (c.B : ℝ) ^ 3 := pow_le_pow_right₀ hB1 (by omega)
            nlinarith [c.hL2]
          have hB' : c.L ^ ((1 : ℝ) / 10) * c.L ^ ((3 : ℝ) / 5) ≤ c.L ^ 9 := by
            rw [← Real.rpow_add hLpos, ← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le (by linarith [c.hL10]) (by norm_num)
          nlinarith [Real.rpow_nonneg hLpos.le ((3 : ℝ) / 5)]
        nlinarith [mul_nonneg hKpos.le hYpos.le]

private lemma CoverCtx.hE4_bd (c : CoverCtx) :
    ∑ k ∈ c.E4, ((c.Pnear k).card : ℝ) ≤ (c.K : ℝ) * (c.Y : ℝ) / (200 * (c.Q : ℝ) ^ 2 * c.L) := by
  have hKpos := c.hKpos; have hQpos := c.hQpos; have hYpos := c.hYpos; have hLpos := c.hLpos
  have hKset_card : (c.Kset.card : ℝ) ≤ 10 * (c.K : ℝ) := by
    have hsub : c.Kset ⊆ Ioc c.K (10 * c.K) := filter_subset _ _
    have hnat : c.Kset.card ≤ 10 * c.K := (card_le_card hsub).trans (by rw [Nat.card_Ioc]; omega)
    exact_mod_cast hnat
  calc ∑ k ∈ c.E4, ((c.Pnear k).card : ℝ)
      ≤ ∑ _k ∈ c.E4, Real.sqrt (c.Y : ℝ) := sum_le_sum fun k hk =>
        (by exact_mod_cast (mem_filter.mp hk).2 : ((c.Pnear k).card : ℝ) ≤ (Nat.floor (Real.sqrt (c.Y : ℝ)) : ℝ)).trans
          (Nat.floor_le (Real.sqrt_nonneg _))
    _ = (c.E4.card : ℝ) * Real.sqrt (c.Y : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (10 * (c.K : ℝ)) * Real.sqrt (c.Y : ℝ) := mul_le_mul_of_nonneg_right
        ((by exact_mod_cast card_le_card (filter_subset _ _) : (c.E4.card : ℝ) ≤ c.Kset.card).trans hKset_card) (Real.sqrt_nonneg _)
    _ ≤ (c.K : ℝ) * (c.Y : ℝ) / (200 * (c.Q : ℝ) ^ 2 * c.L) := by
        rw [le_div_iff₀ (by positivity)]
        have h1 : 10 * (c.K : ℝ) * Real.sqrt (c.Y : ℝ) * (200 * (c.Q : ℝ) ^ 2 * c.L) =
            (c.K : ℝ) * ((2000 * (c.Q : ℝ) ^ 2 * c.L) * Real.sqrt (c.Y : ℝ)) := by ring
        rw [h1]
        refine mul_le_mul_of_nonneg_left ?_ hKpos.le
        have hsqrtY : 2000 * (c.Q : ℝ) ^ 2 * c.L ≤ Real.sqrt (c.Y : ℝ) := by
          rw [Real.le_sqrt (by positivity) hYpos.le]
          have hlog_bd : Real.log ((2000 * (c.Q : ℝ) ^ 2 * c.L) ^ 2) ≤ Real.log (c.Y : ℝ) := by
            rw [Real.log_pow, Real.log_mul (by positivity) hLpos.ne']
            have h2000 : 2000 * (c.Q : ℝ) ^ 2 ≤ (10000 * (c.Q : ℝ) * (c.B : ℝ)) ^ 2 := by
              have hB1 : (1 : ℝ) ≤ c.B := by exact_mod_cast (by have := c.hB; omega : 1 ≤ c.B)
              have hB2 : (1 : ℝ) ≤ (c.B : ℝ) ^ 2 := by nlinarith
              nlinarith [sq_nonneg (c.Q : ℝ)]
            have hlog2000 : Real.log (2000 * (c.Q : ℝ) ^ 2) ≤ 2 * Real.log (10000 * (c.Q : ℝ) * (c.B : ℝ)) := by
              calc Real.log (2000 * (c.Q : ℝ) ^ 2) ≤ Real.log ((10000 * (c.Q : ℝ) * (c.B : ℝ)) ^ 2) :=
                    Real.log_le_log (by positivity) h2000
                _ = 2 * Real.log (10000 * (c.Q : ℝ) * (c.B : ℝ)) := by rw [Real.log_pow]; norm_num
            have hlogL_le : Real.log c.L ≤ (1 / 20 : ℝ) * c.L ^ ((3 : ℝ) / 5) := by
              have h1 : 10 * Real.log c.L ≤ (1 / 4 : ℝ) * c.L ^ ((2 : ℝ) / 5) := by
                have hnn : 0 ≤ Real.log (2 * c.L ^ ((3 : ℝ) / 5)) := Real.log_nonneg (by linarith [c.hL35_ge])
                linarith [c.hL6]
              have h2 : c.L ^ ((2 : ℝ) / 5) ≤ c.L ^ ((3 : ℝ) / 5) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith [c.hL10]) (by norm_num)
              linarith [c.hL35_ge]
            push_cast; linarith [c.hL3, c.hlogY_lo, c.hL35_ge]
          calc (2000 * (c.Q : ℝ) ^ 2 * c.L) ^ 2
              = Real.exp (Real.log ((2000 * (c.Q : ℝ) ^ 2 * c.L) ^ 2)) := (Real.exp_log (by positivity)).symm
            _ ≤ Real.exp (Real.log (c.Y : ℝ)) := Real.exp_le_exp.mpr hlog_bd
            _ = (c.Y : ℝ) := Real.exp_log hYpos
        calc (2000 * (c.Q : ℝ) ^ 2 * c.L) * Real.sqrt (c.Y : ℝ)
            ≤ Real.sqrt (c.Y : ℝ) * Real.sqrt (c.Y : ℝ) := mul_le_mul_of_nonneg_right hsqrtY (Real.sqrt_nonneg _)
          _ = (c.Y : ℝ) := Real.mul_self_sqrt hYpos.le

set_option maxHeartbeats 600000 in
private lemma CoverCtx.hE3_bd (c : CoverCtx) :
    ∑ k ∈ c.E3, ((c.Pnear k).card : ℝ) ≤ (c.K : ℝ) * (c.Y : ℝ) / (200 * (c.Q : ℝ) ^ 2 * c.L) := by
  have hKpos := c.hKpos; have hQpos := c.hQpos; have hBpos := c.hBpos; have hYpos := c.hYpos; have hLpos := c.hLpos
  let Amax : ℕ := 2 * c.Q * c.B
  let Pairs3 := c.E3.sigma (fun k => c.Pnear k)
  let GoodQ : ℕ → ℕ → ℕ → Finset ℕ := fun a d h =>
    (Icc 1 (10 * c.K / a)).filter (fun q : ℕ => q.Prime ∧
      0 < (a : ℤ) * (q : ℤ) + ((d : ℤ) - (h : ℤ) - 1) ∧
      ((a : ℤ) * (q : ℤ) + ((d : ℤ) - (h : ℤ) - 1)).toNat.Prime)
  have hPair_sub : Pairs3 ⊆ ((Icc 1 Amax).biUnion fun a => c.Dset.biUnion fun d =>
      (Ioo 0 (c.Y / 2)).biUnion fun h => (GoodQ a d h).image fun q =>
        (⟨a * q + d - 1, a * q + d - 1 - h⟩ : (k : ℕ) × ℕ)) := by
    intro ⟨k, p⟩ hkp
    obtain ⟨hkE3, hpnear⟩ := mem_sigma.mp hkp
    dsimp only at hkE3 hpnear
    obtain ⟨hkK, d, hd, q, hqpr, hq_gt, hq_dvd⟩ := mem_filter.mp hkE3
    obtain ⟨hpI, hppr, _⟩ := mem_filter.mp hpnear
    have hk1 := (mem_Ioc.mp (mem_filter.mp hkK).1).1; have hk10 := (mem_Ioc.mp (mem_filter.mp hkK).1).2
    have hd1 := (mem_Icc.mp (mem_filter.mp hd).1).1; have hdY := (mem_Icc.mp (mem_filter.mp hd).1).2
    have hp1 := (mem_Ioo.mp hpI).1; have hp2 := (mem_Ioo.mp hpI).2
    have hYK := c.hY_le_K
    have hY1000 := c.hY_ge_1000
    let a := (k - d + 1) / q
    have haq : a * q = k - d + 1 := by rw [mul_comm]; exact Nat.mul_div_cancel' hq_dvd
    have ha1 : 1 ≤ a := Nat.div_pos (Nat.le_of_dvd (by omega) hq_dvd) hqpr.pos
    have ha_le : a ≤ Amax := by
      have h1 : (k - c.Y) / (c.Q * c.B) + 1 ≤ q := hq_gt
      have hdm : (c.Q * c.B) * ((k - c.Y) / (c.Q * c.B)) + (k - c.Y) % (c.Q * c.B) = k - c.Y :=
        Nat.div_add_mod (k - c.Y) (c.Q * c.B)
      have hBpos_nat : 0 < c.B := by have := c.hB; omega
      have hrem := Nat.mod_lt (k - c.Y) (Nat.mul_pos c.hQp.pos hBpos_nat)
      have h2 : k - c.Y < c.Q * c.B * q := by
        have hmul := Nat.mul_le_mul_left (c.Q * c.B) h1
        rw [mul_add, mul_one] at hmul; omega
      have h3 : a * (k - c.Y) < a * (c.Q * c.B * q) := Nat.mul_lt_mul_of_pos_left h2 ha1
      have h4 : a * (c.Q * c.B * q) = (c.Q * c.B) * (a * q) := by ring
      rw [h4, haq] at h3
      have h5 : k - d + 1 ≤ 2 * (k - c.Y) := by omega
      have h6 : a * (k - c.Y) < (2 * c.Q * c.B) * (k - c.Y) := by nlinarith
      have h7 := Nat.lt_of_mul_lt_mul_right h6
      dsimp only [Amax]; omega
    let h := k - p
    have hh_mem : h ∈ Ioo 0 (c.Y / 2) := mem_Ioo.mpr ⟨by dsimp only [h]; omega, by dsimp only [h]; omega⟩
    have hq_le : q ≤ 10 * c.K / a := (Nat.le_div_iff_mul_le ha1).mpr (by rw [mul_comm, haq]; omega)
    have hp_eqZ : (a : ℤ) * (q : ℤ) + ((d : ℤ) - (h : ℤ) - 1) = (p : ℤ) := by
      have haqZ : (a : ℤ) * (q : ℤ) = (k : ℤ) - (d : ℤ) + 1 := by
        have : a * q + d = k + 1 := by rw [haq]; omega
        have : (a : ℤ) * (q : ℤ) + (d : ℤ) = (k : ℤ) + 1 := by exact_mod_cast this
        linarith
      have hhZ : (h : ℤ) = (k : ℤ) - (p : ℤ) := by
        have : h + p = k := by dsimp only [h]; omega
        have : (h : ℤ) + (p : ℤ) = (k : ℤ) := by exact_mod_cast this
        linarith
      linarith
    have hq_good : q ∈ GoodQ a d h := by
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hqpr.one_le, hq_le⟩, hqpr, ?_, ?_⟩
      · rw [hp_eqZ]; exact_mod_cast hppr.pos
      · rw [hp_eqZ, Int.toNat_natCast]; exact hppr
    refine mem_biUnion.mpr ⟨a, mem_Icc.mpr ⟨ha1, ha_le⟩, mem_biUnion.mpr ⟨d, hd,
      mem_biUnion.mpr ⟨h, hh_mem, mem_image.mpr ⟨q, hq_good, ?_⟩⟩⟩⟩
    refine Sigma.ext ?_ (heq_of_eq ?_)
    · dsimp only; rw [haq]; omega
    · dsimp only; rw [haq]; dsimp only [h]; omega
  have hGoodQ_bd : ∀ a ∈ Icc 1 Amax, ∀ d ∈ c.Dset, ∀ h ∈ Ioo 0 (c.Y / 2),
      ((GoodQ a d h).card : ℝ) ≤
        (if (d : ℤ) - (h : ℤ) - 1 = 0 then 40 * (c.K : ℝ) / c.L else 0) +
        10000 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 := by
    intro a ha d hd h hh
    have ha1 := (mem_Icc.mp ha).1; have haM := (mem_Icc.mp ha).2
    have hd1 := (mem_Icc.mp (mem_filter.mp hd).1).1
    have hdY := (mem_Icc.mp (mem_filter.mp hd).1).2
    have hhY := (mem_Ioo.mp hh).2
    set c0 : ℤ := (d : ℤ) - (h : ℤ) - 1
    have hterm2_nn : 0 ≤ 10000 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 := by positivity
    split_ifs with hc0
    · by_cases ha_eq1 : a = 1
      · have hsub_pr : GoodQ a d h ⊆ (10 * c.K).primesLE := by
          intro q hq
          obtain ⟨hqI, hqpr, _, _⟩ := mem_filter.mp hq
          have hqle : q ≤ 10 * c.K := by
            have := (mem_Icc.mp hqI).2; rw [ha_eq1, Nat.div_one] at this; exact this
          exact Nat.mem_primesLE.mpr ⟨hqle, hqpr⟩
        let S_small := (10 * c.K).primesLE.filter (fun q => q ≤ Nat.sqrt (10 * c.K))
        let S_big := (10 * c.K).primesLE.filter (fun q => Nat.sqrt (10 * c.K) < q)
        have hsplit : (10 * c.K).primesLE.card = S_small.card + S_big.card := by
          have hdisj : Disjoint S_small S_big := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
          have hunion : S_small ∪ S_big = (10 * c.K).primesLE := by
            ext q; simp only [S_small, S_big, mem_union, mem_filter]
            exact ⟨fun h => h.elim And.left And.left, fun hq => by
              by_cases hle : q ≤ Nat.sqrt (10 * c.K)
              · exact Or.inl ⟨hq, hle⟩
              · exact Or.inr ⟨hq, by omega⟩⟩
          rw [← hunion, Finset.card_union_of_disjoint hdisj]
        have hsmall_le : (S_small.card : ℝ) ≤ Real.sqrt (10 * (c.K : ℝ)) := by
          have h1 : S_small ⊆ Icc 1 (Nat.sqrt (10 * c.K)) := by
            intro q hq
            obtain ⟨hqp, hqle⟩ := mem_filter.mp hq
            exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hqp).one_le, hqle⟩
          have h2 : S_small.card ≤ Nat.sqrt (10 * c.K) :=
            (card_le_card h1).trans (by rw [Nat.card_Icc]; omega)
          have h3 : (Nat.sqrt (10 * c.K) : ℝ) ≤ Real.sqrt (10 * (c.K : ℝ)) := by
            rw [Real.le_sqrt (Nat.cast_nonneg _) (by positivity), sq]
            exact_mod_cast Nat.sqrt_le (10 * c.K)
          exact (by exact_mod_cast h2 : (S_small.card : ℝ) ≤ Nat.sqrt (10 * c.K)).trans h3
        have hbig_le : (S_big.card : ℝ) ≤ 28 * (c.K : ℝ) / c.L := by
          have hlog_ge : ∀ q ∈ S_big, c.L / 2 ≤ Real.log (q : ℝ) := by
            intro q hq
            have hqgt : Nat.sqrt (10 * c.K) < q := (mem_filter.mp hq).2
            have hqsq : 10 * c.K < q ^ 2 := Nat.sqrt_lt'.mp hqgt
            have hqsqR : (c.K : ℝ) ≤ (q : ℝ) ^ 2 := by exact_mod_cast (by omega : c.K ≤ q ^ 2)
            have h1 := Real.log_le_log hKpos hqsqR
            rw [Real.log_pow] at h1; push_cast at h1; linarith
          have hsum_ge : (S_big.card : ℝ) * (c.L / 2) ≤ ∑ q ∈ (10 * c.K).primesLE, Real.log (Nat.cast q) := by
            calc (S_big.card : ℝ) * (c.L / 2) = ∑ _q ∈ S_big, (c.L / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ ∑ q ∈ S_big, Real.log (q : ℝ) := sum_le_sum hlog_ge
              _ ≤ ∑ q ∈ (10 * c.K).primesLE, Real.log (Nat.cast q) :=
                  sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p : ℝ)) (filter_subset _ _) fun p hp _ =>
                    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
          have htheta : ∑ q ∈ (10 * c.K).primesLE, Real.log (Nat.cast q) ≤ 14 * (c.K : ℝ) := by
            have h1 : ∑ q ∈ (10 * c.K).primesLE, Real.log (Nat.cast q) = Chebyshev.theta ((10 * c.K : ℕ) : ℝ) := by
              rw [Chebyshev.theta_eq_sum_primesLE_log]
            rw [h1]
            have h2 : Chebyshev.theta ((10 * c.K : ℕ) : ℝ) ≤ Real.log 4 * ((10 * c.K : ℕ) : ℝ) :=
              Chebyshev.theta_le_log4_mul_x (by positivity)
            have hlog4 : Real.log 4 ≤ (14 / 10 : ℝ) := by
              have : Real.log 4 = 2 * Real.log 2 := by
                rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
              linarith [Real.log_two_lt_d9]
            rw [Nat.cast_mul, Nat.cast_ofNat] at h2 ⊢; nlinarith
          rw [le_div_iff₀ hLpos]; linarith
        have hsqrt_le_KL : Real.sqrt (10 * (c.K : ℝ)) ≤ 12 * (c.K : ℝ) / c.L := by
          rw [le_div_iff₀ hLpos]
          have hsq : (Real.sqrt (10 * (c.K : ℝ)) * c.L) ^ 2 ≤ (12 * (c.K : ℝ)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
            have hL2K : c.L ^ 2 ≤ (c.K : ℝ) := by
              have h1 : Real.log (c.L ^ 2) ≤ c.L := by
                rw [Real.log_pow]; push_cast; linarith [c.hL4, c.hL35_ge]
              calc c.L ^ 2 = Real.exp (Real.log (c.L ^ 2)) := (Real.exp_log (pow_pos hLpos 2)).symm
                _ ≤ Real.exp c.L := Real.exp_le_exp.mpr h1
                _ = (c.K : ℝ) := Real.exp_log hKpos
            nlinarith
          nlinarith [Real.sqrt_nonneg (10 * (c.K : ℝ))]
        have hcard_le : ((GoodQ a d h).card : ℝ) ≤ ((10 * c.K).primesLE.card : ℝ) := by
          exact_mod_cast card_le_card hsub_pr
        have hsplitR : ((10 * c.K).primesLE.card : ℝ) = (S_small.card : ℝ) + (S_big.card : ℝ) := by
          exact_mod_cast hsplit
        have h40 : 28 * (c.K : ℝ) / c.L + 12 * (c.K : ℝ) / c.L = 40 * (c.K : ℝ) / c.L := by ring
        linarith
      · have hemp : GoodQ a d h = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro q hq
          obtain ⟨_, hqpr, _, hprodpr⟩ := mem_filter.mp hq
          have hval : ((a : ℤ) * (q : ℤ) + c0).toNat = a * q := by rw [hc0, add_zero]; exact_mod_cast rfl
          rw [hval] at hprodpr
          rcases hprodpr.eq_one_or_self_of_dvd a (dvd_mul_right a q) with h1 | h2
          · omega
          · have : a * 1 = a * q := by linarith
            have := Nat.eq_of_mul_eq_mul_left ha1 this
            have := hqpr.two_le; omega
        rw [hemp, card_empty, Nat.cast_zero]; positivity
    · rw [zero_add]
      by_cases hcop : Nat.Coprime a c0.natAbs
      · let Xa := 10 * c.K / a
        have hXa_ge : 10000 ≤ Xa := by
          have h1 : 10000 * Amax ≤ 10 * c.K := by
            have : Amax = 2 * c.Q * c.B := rfl
            have := c.hY_ge_1000QB; have := c.hY_small; nlinarith
          exact (Nat.le_div_iff_mul_le ha1).mpr (le_trans (Nat.mul_le_mul_left 10000 haM) h1)
        have h2d := two_dim_prime_pair_bound ha1 hc0 hcop hXa_ge
        have hXapos : (0 : ℝ) < Xa := by exact_mod_cast (by omega : 0 < Xa)
        have hXa_le : (Xa : ℝ) ≤ 10 * (c.K : ℝ) / (a : ℝ) := by
          rw [le_div_iff₀ (by exact_mod_cast ha1 : (0 : ℝ) < a)]
          exact_mod_cast Nat.div_mul_le_self (10 * c.K) a
        have hXa_ge_K12 : (c.K : ℝ) ^ ((1 : ℝ) / 2) ≤ (Xa : ℝ) := by
          have ha_le_Y : (a : ℝ) ≤ (c.Y : ℝ) := by
            have : Amax ≤ c.Y := by dsimp only [Amax]; have := c.hY_ge_1000QB; nlinarith
            exact_mod_cast (haM.trans this)
          have hY_le_K12 : (c.Y : ℝ) ≤ (c.K : ℝ) ^ ((1 : ℝ) / 2) := by
            have h1 := Real.rpow_le_rpow (by positivity) c.hY_le_K14 (by norm_num : (0 : ℝ) ≤ 1 / 2)
            rw [← Real.rpow_natCast (c.Y : ℝ), ← Real.rpow_mul hYpos.le] at h1
            norm_num at h1
            have hY1 : (1 : ℝ) ≤ c.Y := by exact_mod_cast (by have := c.hY_ge_1000; omega : 1 ≤ c.Y)
            nlinarith
          have hprod_le : (a : ℝ) * (c.K : ℝ) ^ ((1 : ℝ) / 2) ≤ (c.K : ℝ) := by
            have h1 : (c.K : ℝ) ^ ((1 : ℝ) / 2) * (c.K : ℝ) ^ ((1 : ℝ) / 2) = (c.K : ℝ) := by
              rw [← Real.rpow_add hKpos]; norm_num
            calc (a : ℝ) * (c.K : ℝ) ^ ((1 : ℝ) / 2)
                ≤ (c.K : ℝ) ^ ((1 : ℝ) / 2) * (c.K : ℝ) ^ ((1 : ℝ) / 2) :=
                  mul_le_mul_of_nonneg_right (ha_le_Y.trans hY_le_K12) (by positivity)
              _ = (c.K : ℝ) := h1
          have haXa_ge : (c.K : ℝ) ≤ (a : ℝ) * (Xa : ℝ) := by
            have hdm := Nat.div_add_mod (10 * c.K) a
            have hrem := Nat.mod_lt (10 * c.K) ha1
            have h1 : 10 * c.K ≤ a * (Xa + 1) := by dsimp only [Xa]; nlinarith
            have h2 : a * (Xa + 1) ≤ 2 * (a * Xa) := by nlinarith
            have h3 : c.K ≤ a * Xa := by omega
            exact_mod_cast h3
          exact le_of_mul_le_mul_left (hprod_le.trans haXa_ge) (by exact_mod_cast ha1 : (0 : ℝ) < a)
        have hlogXa_ge : c.L / 2 ≤ Real.log (Xa : ℝ) := by
          have h1 := Real.log_le_log (Real.rpow_pos_of_pos hKpos _) hXa_ge_K12
          rw [Real.log_rpow hKpos] at h1; linarith
        have hlogXa_le : Real.log (Xa : ℝ) ≤ 2 * c.L := by
          have h1 : (Xa : ℝ) ≤ 10 * (c.K : ℝ) := by exact_mod_cast Nat.div_le_self (10 * c.K) a
          have h2 := Real.log_le_log hXapos h1
          rw [Real.log_mul (by norm_num) hKpos.ne'] at h2
          linarith [CoverCtx.hlog10_le4, c.hL10]
        have hsqrt_m_le : Real.sqrt (2 * (Nat.log 2 (a * c0.natAbs) : ℝ) + 3) ≤ 3 * c.L ^ ((3 : ℝ) / 10) := by
          rw [Real.sqrt_le_left (by positivity)]
          have hsq : (3 * c.L ^ ((3 : ℝ) / 10)) ^ 2 = 9 * c.L ^ ((3 : ℝ) / 5) := by
            rw [mul_pow, ← Real.rpow_natCast (c.L ^ _), ← Real.rpow_mul hLpos.le]; norm_num
          rw [hsq]
          have hc_le_Y : c0.natAbs ≤ 2 * c.Y := by dsimp only [c0]; omega
          have ha_le_Y_nat : a ≤ c.Y := by
            have : Amax ≤ c.Y := by dsimp only [Amax]; have := c.hY_ge_1000QB; nlinarith
            exact haM.trans this
          have hm_le : (a * c0.natAbs : ℝ) ≤ 2 * (c.Y : ℝ) ^ 2 := by
            have h1 : a * c0.natAbs ≤ c.Y * (2 * c.Y) := Nat.mul_le_mul ha_le_Y_nat hc_le_Y
            have h1R : ((a * c0.natAbs : ℕ) : ℝ) ≤ ((c.Y * (2 * c.Y) : ℕ) : ℝ) := by exact_mod_cast h1
            push_cast at h1R; linarith
          have hm_pos : 1 ≤ a * c0.natAbs := Nat.mul_pos ha1 (Int.natAbs_pos.mpr hc0)
          have hlog2m : (Nat.log 2 (a * c0.natAbs) : ℝ) ≤ 4 * c.L ^ ((3 : ℝ) / 5) + 2 := by
            have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
            have h1 : (Nat.log 2 (a * c0.natAbs) : ℝ) * Real.log 2 ≤ Real.log ((a * c0.natAbs : ℕ) : ℝ) := by
              rw [← Real.log_pow]
              exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_log_le_self 2 (by omega))
            have h2 : Real.log ((a * c0.natAbs : ℕ) : ℝ) ≤ 2 * c.L ^ ((3 : ℝ) / 5) + 1 := by
              calc Real.log ((a * c0.natAbs : ℕ) : ℝ)
                  ≤ Real.log (2 * (c.Y : ℝ) ^ 2) := Real.log_le_log (by exact_mod_cast hm_pos) (by push_cast; exact hm_le)
                _ = Real.log 2 + 2 * Real.log (c.Y : ℝ) := by
                    rw [Real.log_mul (by norm_num) (pow_pos hYpos 2).ne', Real.log_pow]; push_cast; ring
                _ ≤ 2 * c.L ^ ((3 : ℝ) / 5) + 1 := by linarith [Real.log_two_lt_d9, c.hlogY_hi]
            nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 (a * c0.natAbs))]
          linarith [c.hL35_ge]
        have hterm1 : 600 * Real.sqrt (2 * (Nat.log 2 (a * c0.natAbs) : ℝ) + 3) * (Xa : ℝ) / (Real.log (Xa : ℝ)) ^ 2 ≤
            7200 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 := by
          have hnum : 600 * Real.sqrt (2 * (Nat.log 2 (a * c0.natAbs) : ℝ) + 3) * (Xa : ℝ) ≤
              1800 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) := by
            calc 600 * Real.sqrt (2 * (Nat.log 2 (a * c0.natAbs) : ℝ) + 3) * (Xa : ℝ)
                ≤ 600 * (3 * c.L ^ ((3 : ℝ) / 10)) * (10 * (c.K : ℝ) / (a : ℝ)) :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hsqrt_m_le (by norm_num)) hXa_le hXapos.le (by positivity)
              _ = 1800 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) := by ring
          have hden : (c.L / 2) ^ 2 ≤ (Real.log (Xa : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hlogXa_ge 2
          calc 600 * Real.sqrt (2 * (Nat.log 2 (a * c0.natAbs) : ℝ) + 3) * (Xa : ℝ) / (Real.log (Xa : ℝ)) ^ 2
              ≤ (1800 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ))) / ((c.L / 2) ^ 2) :=
                div_le_div₀ (by positivity) hnum (by positivity) hden
            _ = 7200 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 := by ring
        have hterm_err : (Xa : ℝ) ^ ((1 : ℝ) / 2) * (1 + Real.log (Xa : ℝ)) ^ 2 + 4 * (Xa : ℝ) ^ ((1 : ℝ) / 4) ≤
            2800 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 := by
          have hXa14 : (Xa : ℝ) ^ ((1 : ℝ) / 4) ≤ (Xa : ℝ) ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ Xa)) (by norm_num)
          have hlog_sq : (1 + Real.log (Xa : ℝ)) ^ 2 ≤ 9 * c.L ^ 2 := by
            have h1 : 1 + Real.log (Xa : ℝ) ≤ 3 * c.L := by linarith [c.hL10]
            have h2 := pow_le_pow_left₀ (by linarith) h1 2
            linarith
          have herr1 : (Xa : ℝ) ^ ((1 : ℝ) / 2) * (1 + Real.log (Xa : ℝ)) ^ 2 + 4 * (Xa : ℝ) ^ ((1 : ℝ) / 4) ≤
              13 * c.L ^ 2 * (Xa : ℝ) ^ ((1 : ℝ) / 2) := by
            have hL2_ge1 : (1 : ℝ) ≤ c.L ^ 2 := by nlinarith [c.hL10]
            nlinarith [Real.rpow_nonneg hXapos.le ((1 : ℝ) / 2)]
          have hL4_le_Xa12 : c.L ^ 4 ≤ (Xa : ℝ) ^ ((1 : ℝ) / 2) := by
            have hL4_le_Y : c.L ^ 4 ≤ (c.Y : ℝ) := by
              have hlogL4 : Real.log (c.L ^ 4) ≤ Real.log (c.Y : ℝ) := by
                rw [Real.log_pow]; push_cast
                have h1 : 10 * Real.log c.L ≤ (1 / 4 : ℝ) * c.L ^ ((2 : ℝ) / 5) := by
                  have hnn : 0 ≤ Real.log (2 * c.L ^ ((3 : ℝ) / 5)) := Real.log_nonneg (by linarith [c.hL35_ge])
                  linarith [c.hL6]
                have h2 : c.L ^ ((2 : ℝ) / 5) ≤ c.L ^ ((3 : ℝ) / 5) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith [c.hL10]) (by norm_num)
                linarith [c.hlogY_lo, c.hL35_ge]
              calc c.L ^ 4 = Real.exp (Real.log (c.L ^ 4)) := (Real.exp_log (pow_pos hLpos 4)).symm
                _ ≤ Real.exp (Real.log (c.Y : ℝ)) := Real.exp_le_exp.mpr hlogL4
                _ = (c.Y : ℝ) := Real.exp_log hYpos
            have hY_le_K14 : (c.Y : ℝ) ≤ (c.K : ℝ) ^ ((1 : ℝ) / 4) := by
              have h1 := Real.rpow_le_rpow (by positivity) c.hY_le_K14 (by norm_num : (0 : ℝ) ≤ 1 / 4)
              rw [← Real.rpow_natCast (c.Y : ℝ), ← Real.rpow_mul hYpos.le] at h1
              norm_num at h1; exact h1
            have hK14_le : (c.K : ℝ) ^ ((1 : ℝ) / 4) ≤ (Xa : ℝ) ^ ((1 : ℝ) / 2) := by
              have h1 := Real.rpow_le_rpow (by positivity) hXa_ge_K12 (by norm_num : (0 : ℝ) ≤ 1 / 2)
              rw [← Real.rpow_mul hKpos.le] at h1; norm_num at h1; exact h1
            exact hL4_le_Y.trans (hY_le_K14.trans hK14_le)
          have hXa12_le : (Xa : ℝ) ^ ((1 : ℝ) / 2) ≤ (Xa : ℝ) / c.L ^ 4 := by
            rw [le_div_iff₀ (pow_pos hLpos 4)]
            have hsq : (Xa : ℝ) ^ ((1 : ℝ) / 2) * (Xa : ℝ) ^ ((1 : ℝ) / 2) = (Xa : ℝ) := by
              rw [← Real.rpow_add hXapos]; norm_num
            calc (Xa : ℝ) ^ ((1 : ℝ) / 2) * c.L ^ 4
                ≤ (Xa : ℝ) ^ ((1 : ℝ) / 2) * (Xa : ℝ) ^ ((1 : ℝ) / 2) :=
                  mul_le_mul_of_nonneg_left hL4_le_Xa12 (by positivity)
              _ = (Xa : ℝ) := hsq
          have h13 : 13 * c.L ^ 2 * (Xa : ℝ) ^ ((1 : ℝ) / 2) ≤ 13 * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 := by
            calc 13 * c.L ^ 2 * (Xa : ℝ) ^ ((1 : ℝ) / 2)
                ≤ 13 * c.L ^ 2 * ((Xa : ℝ) / c.L ^ 4) := mul_le_mul_of_nonneg_left hXa12_le (by positivity)
              _ = 13 * (Xa : ℝ) / c.L ^ 2 := by field_simp [hLpos.ne']
              _ ≤ 13 * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 :=
                  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hXa_le (by norm_num)) (by positivity)
          have hL310 : (1 : ℝ) ≤ c.L ^ ((3 : ℝ) / 10) := Real.one_le_rpow (by linarith [c.hL10]) (by norm_num)
          have hfinal : 13 * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 ≤
              2800 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 := by
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          exact herr1.trans (h13.trans hfinal)
        have hsum_eq : 7200 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 +
            2800 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 =
            10000 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 := by ring
        linarith
      · have hcard1 : (GoodQ a d h).card ≤ 1 := by
          refine Finset.card_le_one.mpr ?_
          intro q1 hq1 q2 hq2
          obtain ⟨_, _, hp1, hpr1⟩ := mem_filter.mp hq1
          obtain ⟨_, _, hp2, hpr2⟩ := mem_filter.mp hq2
          let g := Nat.gcd a c0.natAbs
          have hg_gt1 : 1 < g := by
            have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ ha1
            have hg1 : g ≠ 1 := hcop
            omega
          have hg_dvd1 : g ∣ ((a : ℤ) * (q1 : ℤ) + c0).toNat := by
            have h1 : (g : ℤ) ∣ (a : ℤ) * (q1 : ℤ) + c0 :=
              dvd_add (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)) _)
                (Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _))
            rw [← Int.toNat_of_nonneg hp1.le] at h1
            exact Int.natCast_dvd_natCast.mp h1
          have hg_dvd2 : g ∣ ((a : ℤ) * (q2 : ℤ) + c0).toNat := by
            have h2 : (g : ℤ) ∣ (a : ℤ) * (q2 : ℤ) + c0 :=
              dvd_add (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)) _)
                (Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _))
            rw [← Int.toNat_of_nonneg hp2.le] at h2
            exact Int.natCast_dvd_natCast.mp h2
          have heq1 : ((a : ℤ) * (q1 : ℤ) + c0).toNat = g :=
            ((hpr1.eq_one_or_self_of_dvd g hg_dvd1).resolve_left (by omega)).symm
          have heq2 : ((a : ℤ) * (q2 : ℤ) + c0).toNat = g :=
            ((hpr2.eq_one_or_self_of_dvd g hg_dvd2).resolve_left (by omega)).symm
          have hZ : (a : ℤ) * (q1 : ℤ) + c0 = (a : ℤ) * (q2 : ℤ) + c0 := by omega
          have ha0 : (a : ℤ) ≠ 0 := by omega
          have : (q1 : ℤ) = (q2 : ℤ) := mul_left_cancel₀ ha0 (by linarith)
          exact_mod_cast this
        have h1R : ((GoodQ a d h).card : ℝ) ≤ 1 := by exact_mod_cast hcard1
        have hge1 : (1 : ℝ) ≤ 10000 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 := by
          have h1 : (a : ℝ) * c.L ^ 2 ≤ 10 * (c.K : ℝ) := by
            have haR : (a : ℝ) ≤ (c.Y : ℝ) := by
              have : Amax ≤ c.Y := by dsimp only [Amax]; have := c.hY_ge_1000QB; nlinarith
              exact_mod_cast (haM.trans this)
            have hL2Y : c.L ^ 2 ≤ (c.Y : ℝ) := by
              have : Real.log (c.L ^ 2) ≤ Real.log (c.Y : ℝ) := by
                rw [Real.log_pow]; push_cast
                have : 10 * Real.log c.L ≤ (1 / 4 : ℝ) * c.L ^ ((2 : ℝ) / 5) := by
                  have hnn : 0 ≤ Real.log (2 * c.L ^ ((3 : ℝ) / 5)) := Real.log_nonneg (by linarith [c.hL35_ge])
                  linarith [c.hL6]
                have : c.L ^ ((2 : ℝ) / 5) ≤ c.L ^ ((3 : ℝ) / 5) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith [c.hL10]) (by norm_num)
                linarith [c.hlogY_lo, c.hL35_ge]
              calc c.L ^ 2 = Real.exp (Real.log (c.L ^ 2)) := (Real.exp_log (pow_pos hLpos 2)).symm
                _ ≤ Real.exp (Real.log (c.Y : ℝ)) := Real.exp_le_exp.mpr this
                _ = (c.Y : ℝ) := Real.exp_log hYpos
            have hY2K : (c.Y : ℝ) ^ 2 ≤ (c.K : ℝ) := by
              have hY1 : (1 : ℝ) ≤ c.Y := by exact_mod_cast (by have := c.hY_ge_1000; omega : 1 ≤ c.Y)
              exact (pow_le_pow_right₀ hY1 (by omega : 2 ≤ 4)).trans c.hY_le_K14
            nlinarith
          have h2 : (1 : ℝ) ≤ 10 * (c.K : ℝ) / (a : ℝ) / c.L ^ 2 := by
            rw [one_le_div (pow_pos hLpos 2), le_div_iff₀ (by exact_mod_cast ha1 : (0 : ℝ) < a)]; linarith
          have h3 : (1 : ℝ) ≤ 10000 * c.L ^ ((3 : ℝ) / 10) := by
            have : (1 : ℝ) ≤ c.L ^ ((3 : ℝ) / 10) := Real.one_le_rpow (by linarith [c.hL10]) (by norm_num)
            linarith
          have heq : 10000 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 =
              (10000 * c.L ^ ((3 : ℝ) / 10)) * (10 * (c.K : ℝ) / (a : ℝ) / c.L ^ 2) := by ring
          rw [heq]; nlinarith
        linarith
  have hPairs3_le : (Pairs3.card : ℝ) ≤
      ∑ a ∈ Icc 1 Amax, ∑ d ∈ c.Dset, ∑ h ∈ Ioo 0 (c.Y / 2), ((GoodQ a d h).card : ℝ) := by
    have hnat : Pairs3.card ≤ ∑ a ∈ Icc 1 Amax, ∑ d ∈ c.Dset, ∑ h ∈ Ioo 0 (c.Y / 2), (GoodQ a d h).card := by
      calc Pairs3.card
          ≤ ∑ a ∈ Icc 1 Amax, (c.Dset.biUnion fun d => (Ioo 0 (c.Y / 2)).biUnion fun h =>
              (GoodQ a d h).image fun q => (⟨a * q + d - 1, a * q + d - 1 - h⟩ : (k : ℕ) × ℕ)).card :=
            (card_le_card hPair_sub).trans Finset.card_biUnion_le
        _ ≤ ∑ a ∈ Icc 1 Amax, ∑ d ∈ c.Dset, ((Ioo 0 (c.Y / 2)).biUnion fun h =>
              (GoodQ a d h).image fun q => (⟨a * q + d - 1, a * q + d - 1 - h⟩ : (k : ℕ) × ℕ)).card :=
            sum_le_sum fun _ _ => Finset.card_biUnion_le
        _ ≤ ∑ a ∈ Icc 1 Amax, ∑ d ∈ c.Dset, ∑ h ∈ Ioo 0 (c.Y / 2),
              ((GoodQ a d h).image fun q => (⟨a * q + d - 1, a * q + d - 1 - h⟩ : (k : ℕ) × ℕ)).card :=
            sum_le_sum fun _ _ => sum_le_sum fun _ _ => Finset.card_biUnion_le
        _ ≤ ∑ a ∈ Icc 1 Amax, ∑ d ∈ c.Dset, ∑ h ∈ Ioo 0 (c.Y / 2), (GoodQ a d h).card :=
            sum_le_sum fun _ _ => sum_le_sum fun _ _ => sum_le_sum fun _ _ => card_image_le
    exact_mod_cast hnat
  have hsum_part1 : ∑ a ∈ Icc 1 Amax, ∑ d ∈ c.Dset, ∑ h ∈ Ioo 0 (c.Y / 2),
      (if (d : ℤ) - (h : ℤ) - 1 = 0 then 40 * (c.K : ℝ) / c.L else 0) ≤
      (c.K : ℝ) * (c.Y : ℝ) / (400 * (c.Q : ℝ) ^ 2 * c.L) := by
    have hinner : ∀ d ∈ c.Dset, ∑ h ∈ Ioo 0 (c.Y / 2),
        (if (d : ℤ) - (h : ℤ) - 1 = 0 then 40 * (c.K : ℝ) / c.L else 0) ≤ 40 * (c.K : ℝ) / c.L := by
      intro d _
      by_cases hmem : d - 1 ∈ Ioo 0 (c.Y / 2)
      · rw [Finset.sum_eq_single (d - 1)]
        · split_ifs
          · exact le_rfl
          · positivity
        · intro h _ hne
          have hcond : (d : ℤ) - (h : ℤ) - 1 ≠ 0 := by omega
          simp [hcond]
        · intro hnot; exact False.elim (hnot hmem)
      · rw [Finset.sum_eq_zero]
        · positivity
        · intro h hh
          have hcond : (d : ℤ) - (h : ℤ) - 1 ≠ 0 := by
            intro h0
            have heq : h = d - 1 := by omega
            exact hmem (heq ▸ hh)
          simp [hcond]
    have h1 : ∑ a ∈ Icc 1 Amax, ∑ d ∈ c.Dset, ∑ h ∈ Ioo 0 (c.Y / 2),
        (if (d : ℤ) - (h : ℤ) - 1 = 0 then 40 * (c.K : ℝ) / c.L else 0) ≤
        (Amax : ℝ) * (c.Dset.card : ℝ) * (40 * (c.K : ℝ) / c.L) := by
      calc _ ≤ ∑ _a ∈ Icc 1 Amax, ∑ _d ∈ c.Dset, (40 * (c.K : ℝ) / c.L) :=
            sum_le_sum fun _ _ => sum_le_sum hinner
        _ = (Amax : ℝ) * (c.Dset.card : ℝ) * (40 * (c.K : ℝ) / c.L) := by
            simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]; ring
    have h2 : (Amax : ℝ) * (c.Dset.card : ℝ) * (40 * (c.K : ℝ) / c.L) ≤
        (160 * (c.Q : ℝ) * (c.B : ℝ) ^ 2 * c.L ^ ((3 : ℝ) / 5)) * ((c.K : ℝ) / c.L) := by
      have hAmaxR : (Amax : ℝ) = 2 * (c.Q : ℝ) * (c.B : ℝ) := by dsimp only [Amax]; push_cast; ring
      rw [hAmaxR]
      calc (2 * (c.Q : ℝ) * (c.B : ℝ)) * (c.Dset.card : ℝ) * (40 * (c.K : ℝ) / c.L)
          ≤ (2 * (c.Q : ℝ) * (c.B : ℝ)) * (2 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5)) * (40 * (c.K : ℝ) / c.L) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left c.hDset_card (by positivity)) (by positivity)
        _ = (160 * (c.Q : ℝ) * (c.B : ℝ) ^ 2 * c.L ^ ((3 : ℝ) / 5)) * ((c.K : ℝ) / c.L) := by ring
    have h3 : 64000 * (c.Q : ℝ) ^ 3 * (c.B : ℝ) ^ 2 * c.L ^ ((3 : ℝ) / 5) ≤ (c.Y : ℝ) := by
      have hlog_bd : Real.log (64000 * (c.Q : ℝ) ^ 3 * (c.B : ℝ) ^ 2 * c.L ^ ((3 : ℝ) / 5)) ≤ Real.log (c.Y : ℝ) := by
        rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hLpos _).ne', Real.log_rpow hLpos]
        have h64 : 64000 * (c.Q : ℝ) ^ 3 * (c.B : ℝ) ^ 2 ≤ (10000 * (c.Q : ℝ) * (c.B : ℝ)) ^ 3 := by
          have hB1 : (1 : ℝ) ≤ c.B := by exact_mod_cast (by have := c.hB; omega : 1 ≤ c.B)
          have hB2 : (c.B : ℝ) ^ 2 ≤ (c.B : ℝ) ^ 3 := pow_le_pow_right₀ hB1 (by omega)
          nlinarith [pow_pos hQpos 3]
        have hlog64 : Real.log (64000 * (c.Q : ℝ) ^ 3 * (c.B : ℝ) ^ 2) ≤ 3 * Real.log (10000 * (c.Q : ℝ) * (c.B : ℝ)) := by
          calc Real.log (64000 * (c.Q : ℝ) ^ 3 * (c.B : ℝ) ^ 2)
              ≤ Real.log ((10000 * (c.Q : ℝ) * (c.B : ℝ)) ^ 3) := Real.log_le_log (by positivity) h64
            _ = 3 * Real.log (10000 * (c.Q : ℝ) * (c.B : ℝ)) := by rw [Real.log_pow]; norm_num
        have hlogL_le : Real.log c.L ≤ (1 / 20 : ℝ) * c.L ^ ((3 : ℝ) / 5) := by
          have h1 : 10 * Real.log c.L ≤ (1 / 4 : ℝ) * c.L ^ ((2 : ℝ) / 5) := by
            have hnn : 0 ≤ Real.log (2 * c.L ^ ((3 : ℝ) / 5)) := Real.log_nonneg (by linarith [c.hL35_ge])
            linarith [c.hL6]
          have h2 : c.L ^ ((2 : ℝ) / 5) ≤ c.L ^ ((3 : ℝ) / 5) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [c.hL10]) (by norm_num)
          linarith [c.hL35_ge]
        linarith [c.hL3, c.hlogY_lo, c.hL35_ge]
      calc 64000 * (c.Q : ℝ) ^ 3 * (c.B : ℝ) ^ 2 * c.L ^ ((3 : ℝ) / 5)
          = Real.exp (Real.log (64000 * (c.Q : ℝ) ^ 3 * (c.B : ℝ) ^ 2 * c.L ^ ((3 : ℝ) / 5))) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (Real.log (c.Y : ℝ)) := Real.exp_le_exp.mpr hlog_bd
        _ = (c.Y : ℝ) := Real.exp_log hYpos
    have h4 : (160 * (c.Q : ℝ) * (c.B : ℝ) ^ 2 * c.L ^ ((3 : ℝ) / 5)) * ((c.K : ℝ) / c.L) ≤
        (c.K : ℝ) * (c.Y : ℝ) / (400 * (c.Q : ℝ) ^ 2 * c.L) := by
      rw [le_div_iff₀ (by positivity)]
      have heq : (160 * (c.Q : ℝ) * (c.B : ℝ) ^ 2 * c.L ^ ((3 : ℝ) / 5)) * ((c.K : ℝ) / c.L) * (400 * (c.Q : ℝ) ^ 2 * c.L) =
          (c.K : ℝ) * (64000 * (c.Q : ℝ) ^ 3 * (c.B : ℝ) ^ 2 * c.L ^ ((3 : ℝ) / 5)) := by
        field_simp [hLpos.ne']; ring
      rw [heq]; exact mul_le_mul_of_nonneg_left h3 hKpos.le
    exact h1.trans (h2.trans h4)
  have hsum_part2 : ∑ a ∈ Icc 1 Amax, ∑ _d ∈ c.Dset, ∑ _h ∈ Ioo 0 (c.Y / 2),
      10000 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 ≤
      (c.K : ℝ) * (c.Y : ℝ) / (400 * (c.Q : ℝ) ^ 2 * c.L) := by
    have hrew : ∑ a ∈ Icc 1 Amax, ∑ _d ∈ c.Dset, ∑ _h ∈ Ioo 0 (c.Y / 2),
        10000 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2 =
        (c.Dset.card : ℝ) * ((Ioo 0 (c.Y / 2)).card : ℝ) * (100000 * c.L ^ ((3 : ℝ) / 10) * (c.K : ℝ) / c.L ^ 2) *
        (∑ a ∈ Icc 1 Amax, (1 : ℝ) / (a : ℝ)) := by
      rw [Finset.mul_sum]
      refine sum_congr rfl fun a _ => by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    rw [hrew]
    have hharm : ∑ a ∈ Icc 1 Amax, (1 : ℝ) / (a : ℝ) ≤ 2 * (c.Q : ℝ) * (c.B : ℝ) := by
      calc ∑ a ∈ Icc 1 Amax, (1 : ℝ) / (a : ℝ)
          ≤ ∑ _a ∈ Icc 1 Amax, (1 : ℝ) := sum_le_sum fun a ha => by
            have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (mem_Icc.mp ha).1
            exact div_le_one_of_le₀ ha1 (by positivity)
        _ = (Amax : ℝ) := by simp [Nat.card_Icc]
        _ = 2 * (c.Q : ℝ) * (c.B : ℝ) := by dsimp only [Amax]; push_cast; ring
    have hIoo_le : ((Ioo 0 (c.Y / 2)).card : ℝ) ≤ (c.Y : ℝ) / 2 := by
      have h1 : (Ioo 0 (c.Y / 2)).card ≤ c.Y / 2 := by rw [Nat.card_Ioo]; omega
      have h2 : ((c.Y / 2 : ℕ) : ℝ) ≤ (c.Y : ℝ) / 2 := by
        rw [le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self c.Y 2
      exact (by exact_mod_cast h1 : ((Ioo 0 (c.Y / 2)).card : ℝ) ≤ (c.Y / 2 : ℕ)).trans h2
    have hprod_le : (c.Dset.card : ℝ) * ((Ioo 0 (c.Y / 2)).card : ℝ) *
        (100000 * c.L ^ ((3 : ℝ) / 10) * (c.K : ℝ) / c.L ^ 2) * (∑ a ∈ Icc 1 Amax, (1 : ℝ) / (a : ℝ)) ≤
        (200000 * (c.Q : ℝ) * (c.B : ℝ) ^ 2 * c.L ^ ((9 : ℝ) / 10) / c.L ^ 2) * ((c.K : ℝ) * (c.Y : ℝ)) := by
      have hL910 : c.L ^ ((3 : ℝ) / 5) * c.L ^ ((3 : ℝ) / 10) = c.L ^ ((9 : ℝ) / 10) := by
        rw [← Real.rpow_add hLpos]; congr 1; norm_num
      calc _ ≤ (2 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5)) * ((c.Y : ℝ) / 2) *
              (100000 * c.L ^ ((3 : ℝ) / 10) * (c.K : ℝ) / c.L ^ 2) * (2 * (c.Q : ℝ) * (c.B : ℝ)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul c.hDset_card hIoo_le (by positivity) (by positivity))
              (by positivity)) hharm (sum_nonneg fun _ _ => by positivity) (by positivity)
        _ = (200000 * (c.Q : ℝ) * (c.B : ℝ) ^ 2 * (c.L ^ ((3 : ℝ) / 5) * c.L ^ ((3 : ℝ) / 10)) / c.L ^ 2) * ((c.K : ℝ) * (c.Y : ℝ)) := by ring
        _ = (200000 * (c.Q : ℝ) * (c.B : ℝ) ^ 2 * c.L ^ ((9 : ℝ) / 10) / c.L ^ 2) * ((c.K : ℝ) * (c.Y : ℝ)) := by rw [hL910]
    have hcoef : 200000 * (c.Q : ℝ) * (c.B : ℝ) ^ 2 * c.L ^ ((9 : ℝ) / 10) / c.L ^ 2 ≤ 1 / (400 * (c.Q : ℝ) ^ 2 * c.L) := by
      rw [div_le_div_iff₀ (pow_pos hLpos 2) (by positivity)]
      have h1 : 200000 * (c.Q : ℝ) * (c.B : ℝ) ^ 2 * c.L ^ ((9 : ℝ) / 10) * (400 * (c.Q : ℝ) ^ 2 * c.L) =
          (80000000 * (c.Q : ℝ) ^ 3 * (c.B : ℝ) ^ 2) * (c.L ^ ((9 : ℝ) / 10) * c.L) := by ring
      rw [h1, one_mul]
      have hA : 80000000 * (c.Q : ℝ) ^ 3 * (c.B : ℝ) ^ 2 ≤ c.L ^ ((1 : ℝ) / 10) := by
        have hQ1000R : (1000 : ℝ) ≤ c.Q := by exact_mod_cast c.hQ1000
        have hB3R : (3 : ℝ) ≤ c.B := by exact_mod_cast c.hB
        have h1' : 80000000 * (c.Q : ℝ) ^ 3 * (c.B : ℝ) ^ 2 ≤ 1000000 * (c.Q : ℝ) ^ 4 * (c.B : ℝ) ^ 3 := by
          have : (80 : ℝ) ≤ (c.Q : ℝ) * (c.B : ℝ) := by nlinarith
          have hnn : 0 ≤ 1000000 * (c.Q : ℝ) ^ 3 * (c.B : ℝ) ^ 2 := by positivity
          nlinarith
        linarith [c.hL2]
      have hB' : c.L ^ ((1 : ℝ) / 10) * (c.L ^ ((9 : ℝ) / 10) * c.L) = c.L ^ 2 := by
        calc c.L ^ ((1 : ℝ) / 10) * (c.L ^ ((9 : ℝ) / 10) * c.L)
            = (c.L ^ ((1 : ℝ) / 10) * c.L ^ ((9 : ℝ) / 10)) * c.L := by ring
          _ = c.L ^ ((1 : ℝ) / 10 + (9 : ℝ) / 10) * c.L := by rw [← Real.rpow_add hLpos]
          _ = c.L ^ (1 : ℝ) * c.L := by norm_num
          _ = c.L ^ 2 := by rw [Real.rpow_one, sq]
      calc (80000000 * (c.Q : ℝ) ^ 3 * (c.B : ℝ) ^ 2) * (c.L ^ ((9 : ℝ) / 10) * c.L)
          ≤ c.L ^ ((1 : ℝ) / 10) * (c.L ^ ((9 : ℝ) / 10) * c.L) :=
            mul_le_mul_of_nonneg_right hA (by positivity)
        _ = c.L ^ 2 := hB'
    calc _ ≤ (200000 * (c.Q : ℝ) * (c.B : ℝ) ^ 2 * c.L ^ ((9 : ℝ) / 10) / c.L ^ 2) * ((c.K : ℝ) * (c.Y : ℝ)) := hprod_le
      _ ≤ (1 / (400 * (c.Q : ℝ) ^ 2 * c.L)) * ((c.K : ℝ) * (c.Y : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = (c.K : ℝ) * (c.Y : ℝ) / (400 * (c.Q : ℝ) ^ 2 * c.L) := by ring
  have hsum_E3_eq : ∑ k ∈ c.E3, ((c.Pnear k).card : ℝ) = (Pairs3.card : ℝ) := by
    dsimp only [Pairs3]; rw [Finset.card_sigma, Nat.cast_sum]
  have hsum_split : ∑ a ∈ Icc 1 Amax, ∑ d ∈ c.Dset, ∑ h ∈ Ioo 0 (c.Y / 2), ((GoodQ a d h).card : ℝ) ≤
      (∑ a ∈ Icc 1 Amax, ∑ d ∈ c.Dset, ∑ h ∈ Ioo 0 (c.Y / 2),
        (if (d : ℤ) - (h : ℤ) - 1 = 0 then 40 * (c.K : ℝ) / c.L else 0)) +
      (∑ a ∈ Icc 1 Amax, ∑ d ∈ c.Dset, ∑ h ∈ Ioo 0 (c.Y / 2),
        10000 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2) := by
    calc _ ≤ ∑ a ∈ Icc 1 Amax, ∑ d ∈ c.Dset, ∑ h ∈ Ioo 0 (c.Y / 2),
            ((if (d : ℤ) - (h : ℤ) - 1 = 0 then 40 * (c.K : ℝ) / c.L else 0) +
              10000 * c.L ^ ((3 : ℝ) / 10) * (10 * (c.K : ℝ) / (a : ℝ)) / c.L ^ 2) :=
          sum_le_sum fun a ha => sum_le_sum fun d hd => sum_le_sum fun h hh => hGoodQ_bd a ha d hd h hh
      _ = _ := by simp only [Finset.sum_add_distrib]
  have h200 : (c.K : ℝ) * (c.Y : ℝ) / (400 * (c.Q : ℝ) ^ 2 * c.L) +
      (c.K : ℝ) * (c.Y : ℝ) / (400 * (c.Q : ℝ) ^ 2 * c.L) = (c.K : ℝ) * (c.Y : ℝ) / (200 * (c.Q : ℝ) ^ 2 * c.L) := by ring
  linarith [hsum_E3_eq, hPairs3_le, hsum_split, hsum_part1, hsum_part2, h200]

set_option maxHeartbeats 600000 in
/-- Extract a good `k ∈ c.Kset \ (E0 ∪ E1 ∪ E2 ∪ E3 ∪ E4)` and build `HasCoverB c.B k`. -/
private lemma CoverCtx.exists_cover (c : CoverCtx) :
    ∃ k ∈ Ioc c.K (10 * c.K), HasCoverB c.B k := by
  have hKpos := c.hKpos; have hQpos := c.hQpos; have hBpos := c.hBpos; have hYpos := c.hYpos; have hLpos := c.hLpos
  let Ebad := c.E0 ∪ (c.E1 ∪ (c.E2 ∪ (c.E3 ∪ c.E4)))
  have hEbad_bd : ∑ k ∈ Ebad, ((c.Pnear k).card : ℝ) ≤ (c.K : ℝ) * (c.Y : ℝ) / (40 * (c.Q : ℝ) ^ 2 * c.L) := by
    have hsum_union : ∀ s₁ s₂ : Finset ℕ,
        ∑ k ∈ s₁ ∪ s₂, ((c.Pnear k).card : ℝ) ≤
          (∑ k ∈ s₁, ((c.Pnear k).card : ℝ)) + (∑ k ∈ s₂, ((c.Pnear k).card : ℝ)) := by
      intro s₁ s₂
      have h := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := fun k => ((c.Pnear k).card : ℝ))
      have hnn : 0 ≤ ∑ k ∈ s₁ ∩ s₂, ((c.Pnear k).card : ℝ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
      linarith
    have h1 : ∑ k ∈ Ebad, ((c.Pnear k).card : ℝ) ≤
        (∑ k ∈ c.E0, ((c.Pnear k).card : ℝ)) + (∑ k ∈ c.E1, ((c.Pnear k).card : ℝ)) +
        (∑ k ∈ c.E2, ((c.Pnear k).card : ℝ)) + (∑ k ∈ c.E3, ((c.Pnear k).card : ℝ)) +
        (∑ k ∈ c.E4, ((c.Pnear k).card : ℝ)) := by
      have hu1 := hsum_union c.E0 (c.E1 ∪ (c.E2 ∪ (c.E3 ∪ c.E4)))
      have hu2 := hsum_union c.E1 (c.E2 ∪ (c.E3 ∪ c.E4))
      have hu3 := hsum_union c.E2 (c.E3 ∪ c.E4)
      have hu4 := hsum_union c.E3 c.E4
      dsimp only [Ebad]; linarith
    have h5 : 5 * ((c.K : ℝ) * (c.Y : ℝ) / (200 * (c.Q : ℝ) ^ 2 * c.L)) =
        (c.K : ℝ) * (c.Y : ℝ) / (40 * (c.Q : ℝ) ^ 2 * c.L) := by ring
    linarith [h1, c.hE0_bd, c.hE1_bd, c.hE2_bd, c.hE3_bd, c.hE4_bd, h5]
  have hgood_ne : (c.Kset \ Ebad).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
    have hle : ∑ k ∈ c.Kset, ((c.Pnear k).card : ℝ) ≤ ∑ k ∈ Ebad, ((c.Pnear k).card : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hemp fun _ _ _ => Nat.cast_nonneg _
    have hpos_rhs : 0 < (c.K : ℝ) * (c.Y : ℝ) / (40 * (c.Q : ℝ) ^ 2 * c.L) := by positivity
    have h2 : (c.K : ℝ) * (c.Y : ℝ) / (20 * (c.Q : ℝ) ^ 2 * c.L) =
        2 * ((c.K : ℝ) * (c.Y : ℝ) / (40 * (c.Q : ℝ) ^ 2 * c.L)) := by ring
    linarith [c.hRaw, hEbad_bd, hle, hpos_rhs, h2]
  obtain ⟨k, hk_good⟩ := hgood_ne
  obtain ⟨hkK, hk_not_bad⟩ := mem_sdiff.mp hk_good
  obtain ⟨hkI, hQ_dvd_k, hQ2_ndvd_k⟩ := mem_filter.mp hkK
  have hk_gt_K : c.K < k := (mem_Ioc.mp hkI).1
  have hk_le_10K : k ≤ 10 * c.K := (mem_Ioc.mp hkI).2
  have hYK := c.hY_le_K
  have hY1000 := c.hY_ge_1000
  have hY1000Q := c.hY_ge_1000Q
  have hQ100B := c.hQ100B
  have hQ1000 := c.hQ1000
  have hB3 := c.hB
  have hk_not_E0 : k ∉ c.E0 := fun h => hk_not_bad (mem_union_left _ h)
  have hk_not_E1 : k ∉ c.E1 := fun h => hk_not_bad (mem_union_right _ (mem_union_left _ h))
  have hk_not_E2 : k ∉ c.E2 := fun h => hk_not_bad (mem_union_right _ (mem_union_right _ (mem_union_left _ h)))
  have hk_not_E3 : k ∉ c.E3 := fun h => hk_not_bad (mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_left _ h))))
  have hk_not_E4 : k ∉ c.E4 := fun h => hk_not_bad (mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_right _ h))))
  have hqd_exists : ∀ d ∈ c.Dset, ∃ q, q.Prime ∧ 2 * c.Y < q ∧ q ≤ (k - c.Y) / (c.Q * c.B) ∧
      q ∣ k - d + 1 ∧ ¬ q ^ 2 ∣ k - d + 1 := by
    intro d hd
    have hnot_all_small : ¬ ∀ q, q.Prime → q ∣ k - d + 1 → q ≤ 2 * c.Y := fun hall =>
      hk_not_E2 (mem_filter.mpr ⟨hkK, d, hd, hall⟩)
    push Not at hnot_all_small
    obtain ⟨q, hqpr, hq_dvd, hq_gt2Y⟩ := hnot_all_small
    have hq_nsq : ¬ q ^ 2 ∣ k - d + 1 := fun hsq =>
      hk_not_E1 (mem_filter.mpr ⟨hkK, d, hd, q, hqpr, hq_gt2Y, hsq⟩)
    have hq_le : q ≤ (k - c.Y) / (c.Q * c.B) := by
      by_contra hgt; push Not at hgt
      exact hk_not_E3 (mem_filter.mpr ⟨hkK, d, hd, q, hqpr, hgt, hq_dvd⟩)
    exact ⟨q, hqpr, hq_gt2Y, hq_le, hq_dvd, hq_nsq⟩
  let q_fn : ℕ → ℕ := fun d => if hd : d ∈ c.Dset then Classical.choose (hqd_exists d hd) else 0
  have hq_spec : ∀ d ∈ c.Dset, (q_fn d).Prime ∧ 2 * c.Y < q_fn d ∧ q_fn d ≤ (k - c.Y) / (c.Q * c.B) ∧
      q_fn d ∣ k - d + 1 ∧ ¬ (q_fn d) ^ 2 ∣ k - d + 1 := by
    intro d hd; simp only [q_fn, dif_pos hd]; exact Classical.choose_spec (hqd_exists d hd)
  have hq_inj : Set.InjOn q_fn (c.Dset : Set ℕ) := by
    intro d1 hd1 d2 hd2 heq
    have hd1Y := (mem_Icc.mp (mem_filter.mp hd1).1).2
    have hd2Y := (mem_Icc.mp (mem_filter.mp hd2).1).2
    have hd1_1 := (mem_Icc.mp (mem_filter.mp hd1).1).1
    have hd2_1 := (mem_Icc.mp (mem_filter.mp hd2).1).1
    have ⟨_, h2Y, _, hdvd1, _⟩ := hq_spec d1 hd1
    have ⟨_, _, _, hdvd2, _⟩ := hq_spec d2 hd2
    rw [← heq] at hdvd2
    rcases le_total d1 d2 with hle | hle
    · have hsub : q_fn d1 ∣ d2 - d1 := by
        have hdiff : (k - d1 + 1) - (k - d2 + 1) = d2 - d1 := by omega
        rw [← hdiff]; exact Nat.dvd_sub hdvd1 hdvd2
      rcases Nat.eq_zero_or_pos (d2 - d1) with h0 | hpos
      · omega
      · have := Nat.le_of_dvd hpos hsub; omega
    · have hsub : q_fn d1 ∣ d1 - d2 := by
        have hdiff : (k - d2 + 1) - (k - d1 + 1) = d1 - d2 := by omega
        rw [← hdiff]; exact Nat.dvd_sub hdvd2 hdvd1
      rcases Nat.eq_zero_or_pos (d1 - d2) with h0 | hpos
      · omega
      · have := Nat.le_of_dvd hpos hsub; omega
  let Pk : Finset ℕ := (range (k + 1)).filter Nat.Prime
  have hprod_Pk : ∀ j, 1 ≤ j → j ≤ k → ∏ p ∈ Pk, p ^ (j.factorization p) = j := by
    intro j hj1 hjk
    have hj0 : j ≠ 0 := by omega
    have hsub : j.factorization.support ⊆ Pk := by
      intro p hp
      have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)
      have hp_dvd : p ∣ j := Nat.dvd_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_dvd (by omega) hp_dvd).trans hjk)), hp_pr⟩
    calc ∏ p ∈ Pk, p ^ (j.factorization p)
        = ∏ p ∈ j.factorization.support, p ^ (j.factorization p) := by
          symm; refine Finset.prod_subset hsub fun p _ hpnot => ?_
          rw [Finsupp.notMem_support_iff.mp hpnot, pow_zero]
      _ = j := Nat.prod_factorization_pow_eq_self hj0
  let Qimg : Finset ℕ := c.Dset.image q_fn
  let S : Finset ℕ := insert c.Q Qimg
  have hS_sub_Pk : S ⊆ Pk := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hpq
    · exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (by omega)), c.hQp⟩
    · obtain ⟨d, hd, rfl⟩ := mem_image.mp hpq
      have ⟨hpr, _, hle, _, _⟩ := hq_spec d hd
      have hle_k : q_fn d ≤ k := hle.trans ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hle_k), hpr⟩
  have hQ_not_Qimg : c.Q ∉ Qimg := by
    intro hmem
    obtain ⟨d, hd, heq⟩ := mem_image.mp hmem
    have ⟨_, h2Y, _, _, _⟩ := hq_spec d hd
    omega
  let zS : ℕ → ℕ := fun j => ∏ p ∈ Pk \ S, p ^ (j.factorization p)
  have hj_decomp : ∀ j, 1 ≤ j → j ≤ k → zS j * (∏ p ∈ S, p ^ (j.factorization p)) = j := by
    intro j hj1 hjk
    dsimp only [zS]
    rw [Finset.prod_sdiff hS_sub_Pk]
    exact hprod_Pk j hj1 hjk
  let U : Finset ℕ := (Icc 1 k).filter (fun j =>
    zS j < c.B ∧ ¬ j ≡ c.r₀ [MOD c.Q] ∧ ∀ d ∈ c.Dset, ¬ j ≡ d [MOD q_fn d])
  have hU_gt_Y : ∀ j ∈ U, c.Y < j := by
    intro j hj
    obtain ⟨hjI, hjz, hjQ, hjD⟩ := mem_filter.mp hj
    have hj1 := (mem_Icc.mp hjI).1; have hjk := (mem_Icc.mp hjI).2
    by_contra hle; push Not at hle
    have hprod_Qimg : ∏ p ∈ Qimg, p ^ (j.factorization p) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      obtain ⟨d, hd, rfl⟩ := mem_image.mp hp
      have ⟨_, h2Y, _, _, _⟩ := hq_spec d hd
      have hndvd : ¬ q_fn d ∣ j := fun hdvd => by have := Nat.le_of_dvd (by omega) hdvd; omega
      rw [Nat.factorization_eq_zero_of_not_dvd hndvd, pow_zero]
    have hprod_S : ∏ p ∈ S, p ^ (j.factorization p) = c.Q ^ (j.factorization c.Q) := by
      dsimp only [S]; rw [Finset.prod_insert hQ_not_Qimg, hprod_Qimg, mul_one]
    have hj_eq : zS j * c.Q ^ (j.factorization c.Q) = j := by
      rw [← hprod_S]; exact hj_decomp j hj1 hjk
    have hzS_eq : j / c.Q ^ (j.factorization c.Q) = zS j := by
      conv_lhs => arg 1; rw [← hj_eq]
      exact Nat.mul_div_cancel _ (pow_pos c.hQp.pos _)
    have hj_mod : j % c.Q ≠ c.r₀ := by
      intro hmod; apply hjQ
      change j % c.Q = c.r₀ % c.Q
      rw [hmod, Nat.mod_eq_of_lt c.hr₀_ltQ]
    have hj_Dset : j ∈ c.Dset := mem_filter.mpr ⟨mem_Icc.mpr ⟨hj1, hle⟩, hj_mod, hzS_eq.symm ▸ hjz⟩
    exact hjD j hj_Dset rfl
  have hU_le_kY : ∀ j ∈ U, j ≤ k - c.Y := by
    intro j hj
    obtain ⟨hjI, hjz, _, _⟩ := mem_filter.mp hj
    have hj1 := (mem_Icc.mp hjI).1; have hjk := (mem_Icc.mp hjI).2
    by_contra hgt; push Not at hgt
    let t := k - j + 1
    have ht1 : 1 ≤ t := by dsimp only [t]; omega
    have htY : t ≤ c.Y := by dsimp only [t]; omega
    have hj_eq_t : j = k - t + 1 := by dsimp only [t]; omega
    have hd_eq_t : ∀ d ∈ c.Dset, q_fn d ∣ j → d = t := by
      intro d hd hqdvd
      have hd1 := (mem_Icc.mp (mem_filter.mp hd).1).1; have hdY := (mem_Icc.mp (mem_filter.mp hd).1).2
      have ⟨_, h2Y, _, hq_kd, _⟩ := hq_spec d hd
      rw [hj_eq_t] at hqdvd
      rcases le_total d t with hle | hle
      · have hsub : q_fn d ∣ t - d := by
          have hdiff : (k - d + 1) - (k - t + 1) = t - d := by omega
          rw [← hdiff]; exact Nat.dvd_sub hq_kd hqdvd
        rcases Nat.eq_zero_or_pos (t - d) with h0 | hpos
        · omega
        · have := Nat.le_of_dvd hpos hsub; omega
      · have hsub : q_fn d ∣ d - t := by
          have hdiff : (k - t + 1) - (k - d + 1) = d - t := by omega
          rw [← hdiff]; exact Nat.dvd_sub hqdvd hq_kd
        rcases Nat.eq_zero_or_pos (d - t) with h0 | hpos
        · omega
        · have := Nat.le_of_dvd hpos hsub; omega
    by_cases htD : t ∈ c.Dset
    · have hprod_Qimg : ∏ p ∈ Qimg, p ^ (j.factorization p) ∣ q_fn t := by
        have hqt_mem : q_fn t ∈ Qimg := mem_image_of_mem q_fn htD
        rw [Finset.prod_eq_single (q_fn t)]
        · have ⟨_, _, _, _, hnsq⟩ := hq_spec t htD
          have hv : j.factorization (q_fn t) ≤ 1 := by
            by_contra h2; push Not at h2
            have hpow2 : (q_fn t) ^ 2 ∣ j := (Nat.pow_dvd_pow (q_fn t) h2).trans (Nat.ordProj_dvd j (q_fn t))
            exact hnsq (hj_eq_t ▸ hpow2)
          exact (Nat.pow_dvd_pow (q_fn t) hv).trans (by rw [pow_one])
        · intro p hp hne
          obtain ⟨d, hd, rfl⟩ := mem_image.mp hp
          have hndvd : ¬ q_fn d ∣ j := fun hdvd => hne (congrArg q_fn (hd_eq_t d hd hdvd))
          rw [Nat.factorization_eq_zero_of_not_dvd hndvd, pow_zero]
        · intro hnot; exact False.elim (hnot hqt_mem)
      have hvQ : j.factorization c.Q ≤ 1 := by
        by_cases ht1_eq : t = 1
        · have hjk_eq : j = k := by omega
          by_contra h2; push Not at h2
          have hpow2 : c.Q ^ 2 ∣ k := hjk_eq ▸ ((Nat.pow_dvd_pow c.Q h2).trans (Nat.ordProj_dvd j c.Q))
          exact hQ2_ndvd_k hpow2
        · have hmod1 := c.hDset_mod1 t htD ht1_eq
          have hndvdQ : ¬ c.Q ∣ j := by
            intro hQj
            have hQt1 : c.Q ∣ t - 1 := by
              have : t - 1 = k - j := by omega
              rw [this]; exact Nat.dvd_sub hQ_dvd_k hQj
            have hmod : t % c.Q = 1 % c.Q := ((Nat.modEq_iff_dvd' ht1).mpr hQt1).symm
            rw [Nat.mod_eq_of_lt c.hQp.one_lt] at hmod
            exact hmod1 hmod
          rw [Nat.factorization_eq_zero_of_not_dvd hndvdQ]; omega
      have hprod_S_le : ∏ p ∈ S, p ^ (j.factorization p) ≤ c.Q * q_fn t := by
        dsimp only [S]
        rw [Finset.prod_insert hQ_not_Qimg]
        have h1 : c.Q ^ (j.factorization c.Q) ≤ c.Q := by
          calc c.Q ^ (j.factorization c.Q) ≤ c.Q ^ 1 := Nat.pow_le_pow_right c.hQp.pos hvQ
            _ = c.Q := pow_one c.Q
        have h2 : ∏ p ∈ Qimg, p ^ (j.factorization p) ≤ q_fn t :=
          Nat.le_of_dvd (hq_spec t htD).1.pos hprod_Qimg
        exact Nat.mul_le_mul h1 h2
      have hB_mul : c.B * (∏ p ∈ S, p ^ (j.factorization p)) ≤ k - c.Y := by
        calc c.B * (∏ p ∈ S, p ^ (j.factorization p))
            ≤ c.B * (c.Q * q_fn t) := Nat.mul_le_mul_left c.B hprod_S_le
          _ = (c.Q * c.B) * q_fn t := by ring
          _ ≤ (c.Q * c.B) * ((k - c.Y) / (c.Q * c.B)) := Nat.mul_le_mul_left _ (hq_spec t htD).2.2.1
          _ ≤ k - c.Y := Nat.mul_div_le (k - c.Y) (c.Q * c.B)
      have hj_dec := hj_decomp j hj1 hjk
      have hlt : c.B * (∏ p ∈ S, p ^ (j.factorization p)) < zS j * (∏ p ∈ S, p ^ (j.factorization p)) := by omega
      have := Nat.lt_of_mul_lt_mul_right hlt
      omega
    · have hprod_Qimg : ∏ p ∈ Qimg, p ^ (j.factorization p) = 1 := by
        refine Finset.prod_eq_one fun p hp => ?_
        obtain ⟨d, hd, rfl⟩ := mem_image.mp hp
        have hndvd : ¬ q_fn d ∣ j := fun hdvd => htD (hd_eq_t d hd hdvd ▸ hd)
        rw [Nat.factorization_eq_zero_of_not_dvd hndvd, pow_zero]
      have hprod_S : ∏ p ∈ S, p ^ (j.factorization p) = c.Q ^ (j.factorization c.Q) := by
        dsimp only [S]; rw [Finset.prod_insert hQ_not_Qimg, hprod_Qimg, mul_one]
      have hj_eq : zS j * c.Q ^ (j.factorization c.Q) = j := by
        rw [← hprod_S]; exact hj_decomp j hj1 hjk
      have hzS_eq : (k - t + 1) / c.Q ^ ((k - t + 1).factorization c.Q) = zS j := by
        rw [← hj_eq_t]
        conv_lhs => arg 1; rw [← hj_eq]
        exact Nat.mul_div_cancel _ (pow_pos c.hQp.pos _)
      have hgeB : c.B ≤ (k - t + 1) / c.Q ^ ((k - t + 1).factorization c.Q) := by
        by_contra hlt; push Not at hlt
        exact hk_not_E0 (c.mem_E0.mpr ⟨hkK, t, mem_Icc.mpr ⟨ht1, by omega⟩, hlt⟩)
      omega
  have hU_card_le : U.card ≤ Nat.floor (Real.sqrt (c.Y : ℝ)) := by
    let E : ℕ := Nat.log (2 * c.Y) k
    let Tup := (Finset.univ : Finset (c.Dset → Fin (E + 1))).filter (fun e => ∑ d : c.Dset, (e d).val ≤ E)
    have hU_sub : U ⊆ ((Ico 1 c.B) ×ˢ ((range (Nat.log c.Q k + 1)) ×ˢ Tup)).image
        (fun x => x.1 * c.Q ^ x.2.1 * ∏ d : c.Dset, (q_fn d.val) ^ (x.2.2 d).val) := by
      intro j hj
      obtain ⟨hjI, hjz, _, _⟩ := mem_filter.mp hj
      have hj1 := (mem_Icc.mp hjI).1; have hjk := (mem_Icc.mp hjI).2
      have hz_pos : 1 ≤ zS j := Nat.succ_le_of_lt
        (Finset.prod_pos fun p hp => pow_pos (mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.pos _)
      have ha_le : j.factorization c.Q ≤ Nat.log c.Q k :=
        Nat.le_log_of_pow_le c.hQp.one_lt ((Nat.le_of_dvd (by omega) (Nat.ordProj_dvd j c.Q)).trans hjk)
      have hprod_Qimg_eq : ∏ p ∈ Qimg, p ^ (j.factorization p) = ∏ d : c.Dset, (q_fn d.val) ^ (j.factorization (q_fn d.val)) := by
        dsimp only [Qimg]
        rw [Finset.prod_image hq_inj, ← Finset.prod_coe_sort c.Dset]
      have hsum_e_le : ∑ d : c.Dset, j.factorization (q_fn d.val) ≤ E := by
        have hpow_le : (2 * c.Y) ^ (∑ d : c.Dset, j.factorization (q_fn d.val)) ≤ k := by
          calc (2 * c.Y) ^ (∑ d : c.Dset, j.factorization (q_fn d.val))
              = ∏ d : c.Dset, (2 * c.Y) ^ (j.factorization (q_fn d.val)) := (Finset.prod_pow_eq_pow_sum _ _ _).symm
            _ ≤ ∏ d : c.Dset, (q_fn d.val) ^ (j.factorization (q_fn d.val)) :=
                Finset.prod_le_prod' fun d _ => Nat.pow_le_pow_left (hq_spec d.val d.2).2.1.le _
            _ = ∏ p ∈ Qimg, p ^ (j.factorization p) := hprod_Qimg_eq.symm
            _ ≤ ∏ p ∈ S, p ^ (j.factorization p) := by
                dsimp only [S]; rw [Finset.prod_insert hQ_not_Qimg]
                exact Nat.le_mul_of_pos_left _ (pow_pos c.hQp.pos _)
            _ ≤ zS j * (∏ p ∈ S, p ^ (j.factorization p)) := Nat.le_mul_of_pos_left _ hz_pos
            _ = j := hj_decomp j hj1 hjk
            _ ≤ k := hjk
        exact Nat.le_log_of_pow_le (by omega) hpow_le
      let ef : c.Dset → Fin (E + 1) := fun d =>
        ⟨j.factorization (q_fn d.val), Nat.lt_succ_of_le
          ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ d)).trans hsum_e_le)⟩
      have hef : ef ∈ Tup := mem_filter.mpr ⟨mem_univ _, by simpa [ef] using hsum_e_le⟩
      refine mem_image.mpr ⟨(zS j, (j.factorization c.Q, ef)),
        mem_product.mpr ⟨mem_Ico.mpr ⟨hz_pos, hjz⟩, mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ha_le), hef⟩⟩, ?_⟩
      dsimp only [ef]
      calc zS j * c.Q ^ j.factorization c.Q * ∏ d : c.Dset, (q_fn d.val) ^ j.factorization (q_fn d.val)
          = zS j * (c.Q ^ j.factorization c.Q * ∏ p ∈ Qimg, p ^ j.factorization p) := by rw [← hprod_Qimg_eq]; ring
        _ = zS j * ∏ p ∈ S, p ^ j.factorization p := by dsimp only [S]; rw [Finset.prod_insert hQ_not_Qimg]
        _ = j := hj_decomp j hj1 hjk
    have hTup_card : Tup.card ≤ (c.Dset.card + 1) ^ E := by
      dsimp only [Tup]; convert card_exponent_tuples_le c.Dset E
    have hU_nat : U.card ≤ c.B * (Nat.log c.Q k + 1) * (c.Dset.card + 1) ^ E := by
      calc U.card
          ≤ (((Ico 1 c.B) ×ˢ ((range (Nat.log c.Q k + 1)) ×ˢ Tup)).image _).card := card_le_card hU_sub
        _ ≤ ((Ico 1 c.B) ×ˢ ((range (Nat.log c.Q k + 1)) ×ˢ Tup)).card := card_image_le
        _ = (c.B - 1) * ((Nat.log c.Q k + 1) * Tup.card) := by rw [card_product, card_product, Nat.card_Ico, card_range]
        _ ≤ c.B * ((Nat.log c.Q k + 1) * (c.Dset.card + 1) ^ E) :=
            Nat.mul_le_mul (Nat.sub_le c.B 1) (Nat.mul_le_mul_left _ hTup_card)
        _ = c.B * (Nat.log c.Q k + 1) * (c.Dset.card + 1) ^ E := by ring
    have hlogk_le : Real.log (k : ℝ) ≤ c.L + 4 := by
      calc Real.log (k : ℝ) ≤ Real.log ((10 * c.K : ℕ) : ℝ) :=
            Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by exact_mod_cast hk_le_10K)
        _ = Real.log 10 + c.L := by rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hKpos.ne']
        _ ≤ c.L + 4 := by linarith [CoverCtx.hlog10_le4]
    have hlogQk : (Nat.log c.Q k : ℝ) + 1 ≤ 2 * c.L + 1 := by
      have h1 : (Nat.log c.Q k : ℝ) * Real.log (c.Q : ℝ) ≤ Real.log (k : ℝ) := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_log_le_self c.Q (by omega))
      nlinarith [c.hlogQ_ge2, hlogk_le, c.hL10, Nat.cast_nonneg (α := ℝ) (Nat.log c.Q k)]
    have hE_le : (E : ℝ) ≤ 4 * c.L ^ ((2 : ℝ) / 5) := by
      have hlog2Y_ge : (1 / 2 : ℝ) * c.L ^ ((3 : ℝ) / 5) ≤ Real.log ((2 * c.Y : ℕ) : ℝ) :=
        c.hlogY_lo.trans (Real.log_le_log hYpos (by exact_mod_cast (by omega : c.Y ≤ 2 * c.Y)))
      have h1 : (E : ℝ) * Real.log ((2 * c.Y : ℕ) : ℝ) ≤ Real.log (k : ℝ) := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_log_le_self (2 * c.Y) (by omega))
      have h2 : Real.log (k : ℝ) ≤ 2 * c.L := by linarith [hlogk_le, c.hL10]
      have h3 : (E : ℝ) * ((1 / 2 : ℝ) * c.L ^ ((3 : ℝ) / 5)) ≤ 2 * c.L :=
        (mul_le_mul_of_nonneg_left hlog2Y_ge (Nat.cast_nonneg E)).trans (h1.trans h2)
      have h4 : (4 * c.L ^ ((2 : ℝ) / 5)) * ((1 / 2 : ℝ) * c.L ^ ((3 : ℝ) / 5)) = 2 * c.L := by
        calc _ = 2 * (c.L ^ ((2 : ℝ) / 5) * c.L ^ ((3 : ℝ) / 5)) := by ring
          _ = 2 * c.L ^ ((2 : ℝ) / 5 + (3 : ℝ) / 5) := by rw [← Real.rpow_add hLpos]
          _ = 2 * c.L := by norm_num
      exact le_of_mul_le_mul_right (h3.trans_eq h4.symm) (by positivity)
    have hU_exp : (U.card : ℝ) ≤ Real.exp ((1 / 4 : ℝ) * c.L ^ ((3 : ℝ) / 5)) := by
      have hU_R : (U.card : ℝ) ≤ (c.B : ℝ) * ((Nat.log c.Q k : ℝ) + 1) * ((c.Dset.card : ℝ) + 1) ^ E := by
        exact_mod_cast hU_nat
      have hbase_le : (c.Dset.card : ℝ) + 1 ≤ 3 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) + 1 := by
        nlinarith [c.hDset_card, c.hBpos, Real.rpow_nonneg hLpos.le ((3 : ℝ) / 5)]
      have hbase_pos : 0 < 3 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) + 1 := by positivity
      have hlog_bd : Real.log ((c.B : ℝ) * (2 * c.L + 1) * (3 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) + 1) ^ E) ≤
          (1 / 4 : ℝ) * c.L ^ ((3 : ℝ) / 5) := by
        rw [Real.log_mul (by positivity) (pow_pos hbase_pos E).ne',
          Real.log_mul hBpos.ne' (by positivity), Real.log_pow]
        have hlog_base_nn : 0 ≤ Real.log (3 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) + 1) :=
          Real.log_nonneg (by linarith [show (0 : ℝ) ≤ 3 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) by positivity])
        have hmul_le := mul_le_mul_of_nonneg_right hE_le hlog_base_nn
        linarith [c.hL5]
      calc (U.card : ℝ)
          ≤ (c.B : ℝ) * (2 * c.L + 1) * (3 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) + 1) ^ E := by
            refine hU_R.trans (mul_le_mul (mul_le_mul_of_nonneg_left hlogQk hBpos.le)
              (pow_le_pow_left₀ (by positivity) hbase_le E) (by positivity) (by positivity))
        _ = Real.exp (Real.log ((c.B : ℝ) * (2 * c.L + 1) * (3 * (c.B : ℝ) * c.L ^ ((3 : ℝ) / 5) + 1) ^ E)) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp ((1 / 4 : ℝ) * c.L ^ ((3 : ℝ) / 5)) := Real.exp_le_exp.mpr hlog_bd
    have hexp_le_sqrt : Real.exp ((1 / 4 : ℝ) * c.L ^ ((3 : ℝ) / 5)) ≤ Real.sqrt (c.Y : ℝ) := by
      rw [Real.le_sqrt (Real.exp_pos _).le hYpos.le, sq, ← Real.exp_add]
      have h1 : Real.exp ((1 / 4 : ℝ) * c.L ^ ((3 : ℝ) / 5) + (1 / 4 : ℝ) * c.L ^ ((3 : ℝ) / 5)) =
          Real.exp ((1 / 2 : ℝ) * c.L ^ ((3 : ℝ) / 5)) := by congr 1; ring
      rw [h1]
      calc Real.exp ((1 / 2 : ℝ) * c.L ^ ((3 : ℝ) / 5))
          ≤ Real.exp (Real.log (c.Y : ℝ)) := Real.exp_le_exp.mpr c.hlogY_lo
        _ = (c.Y : ℝ) := Real.exp_log hYpos
    exact Nat.le_floor (hU_exp.trans hexp_le_sqrt)
  have hPnear_gt : Nat.floor (Real.sqrt (c.Y : ℝ)) < (c.Pnear k).card := by
    by_contra hle; push Not at hle
    exact hk_not_E4 (mem_filter.mpr ⟨hkK, hle⟩)
  obtain ⟨Psub, hPsub_sub, hPsub_card⟩ := Finset.exists_subset_card_eq (hU_card_le.trans hPnear_gt.le)
  have hcard_eq : Fintype.card U = Fintype.card Psub := by
    simp only [Fintype.card_coe]; exact hPsub_card.symm
  let e : U ≃ Psub := Fintype.equivOfCardEq hcard_eq
  have hPsub_gt : ∀ p ∈ Psub, k - c.Y / 2 < p ∧ p < k ∧ p.Prime ∧ p % c.Q = c.r₀ := by
    intro p hp
    obtain ⟨hpI, hppr, hpmod⟩ := mem_filter.mp (hPsub_sub hp)
    exact ⟨(mem_Ioo.mp hpI).1, (mem_Ioo.mp hpI).2, hppr, hpmod⟩
  have hQimg_lt : ∀ p ∈ Qimg, p < k - c.Y / 2 := by
    intro p hp
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hp
    have hle := (hq_spec d hd).2.2.1
    have h1 : (k - c.Y) / (c.Q * c.B) ≤ (k - c.Y) / 2 := Nat.div_le_div_left (by nlinarith) (by norm_num)
    omega
  have hPsub_disj_S : Disjoint S Psub := by
    rw [Finset.disjoint_left]; intro p hpS hpP
    have h1 := (hPsub_gt p hpP).1
    rcases mem_insert.mp hpS with rfl | hpQ
    · omega
    · have := hQimg_lt p hpQ; omega
  let R : Finset ℕ := S ∪ Psub
  let a : ℕ → ℕ := fun p =>
    if p = c.Q then c.r₀
    else if hq : p ∈ Qimg then Classical.choose (mem_image.mp hq)
    else if hp : p ∈ Psub then (e.symm ⟨p, hp⟩).val
    else 0
  have ha_Q : a c.Q = c.r₀ := by simp [a]
  have ha_qfn : ∀ d ∈ c.Dset, a (q_fn d) = d := by
    intro d hd
    have hmem : q_fn d ∈ Qimg := mem_image_of_mem q_fn hd
    have hneQ : q_fn d ≠ c.Q := fun h => hQ_not_Qimg (h ▸ hmem)
    simp only [a, if_neg hneQ, dif_pos hmem]
    have hspec := Classical.choose_spec (mem_image.mp hmem)
    exact hq_inj hspec.1 hd hspec.2
  have ha_Psub : ∀ p (hp : p ∈ Psub), a p = (e.symm ⟨p, hp⟩).val := by
    intro p hp
    have hnotS : p ∉ S := Finset.disjoint_right.mp hPsub_disj_S hp
    have hneQ : p ≠ c.Q := fun h => hnotS (h ▸ mem_insert_self c.Q Qimg)
    have hnotQ : p ∉ Qimg := fun h => hnotS (mem_insert_of_mem h)
    simp [a, hneQ, hnotQ, hp]
  refine ⟨k, hkI, by omega, R, a, ?_, ?_⟩
  · intro p hpR
    rcases mem_union.mp hpR with hpS | hpP
    · rcases mem_insert.mp hpS with rfl | hpQ
      · refine ⟨c.hQp, by omega, ?_, ?_⟩
        · rw [ha_Q, Nat.mod_eq_zero_of_dvd hQ_dvd_k]; exact c.hr₀_ge1
        · rw [ha_Q]; exact c.hr₀_ltQ
      · obtain ⟨d, hd, rfl⟩ := mem_image.mp hpQ
        have ⟨hpr, h2Y, hle, hdvd, _⟩ := hq_spec d hd
        have hd1 := (mem_Icc.mp (mem_filter.mp hd).1).1
        have hdY := (mem_Icc.mp (mem_filter.mp hd).1).2
        have hmod : k % q_fn d = d - 1 := by
          have hsub : k - (d - 1) = k - d + 1 := by omega
          have hmeq : k ≡ d - 1 [MOD q_fn d] := ((Nat.modEq_iff_dvd' (by omega)).mpr (hsub.symm ▸ hdvd)).symm
          change k % q_fn d = (d - 1) % q_fn d at hmeq
          rw [hmeq, Nat.mod_eq_of_lt (by omega)]
        rw [ha_qfn d hd, hmod]
        have hle_k : q_fn d ≤ k := hle.trans ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))
        exact ⟨hpr, hle_k, by omega, by omega⟩
    · have ⟨hgt, hlt, hpr, _⟩ := hPsub_gt p hpP
      rw [ha_Psub p hpP]
      set j := (e.symm ⟨p, hpP⟩).val
      have hjU : j ∈ U := (e.symm ⟨p, hpP⟩).2
      have hj_gtY := hU_gt_Y j hjU
      have hj_lekY := hU_le_kY j hjU
      have hmod : k % p = k - p := by
        calc k % p = (k - p + p * 1) % p := by congr 1; omega
          _ = (k - p) % p := Nat.add_mul_mod_self_left (k - p) p 1
          _ = k - p := Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      exact ⟨hpr, hlt.le, by omega, by omega⟩
  · intro j hj1 hjk
    have hprod1_pos : 1 ≤ ∏ p ∈ Pk \ R, p ^ (j.factorization p) :=
      Nat.succ_le_of_lt (Finset.prod_pos fun p hp => pow_pos (mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.pos _)
    have hprod2_pos : 1 ≤ ∏ p ∈ R.filter (fun p => j ≡ a p [MOD p]), p :=
      Nat.succ_le_of_lt (Finset.prod_pos fun p hp => by
        have hpR := (mem_filter.mp hp).1
        rcases mem_union.mp hpR with hpS | hpP
        · exact (mem_filter.mp (hS_sub_Pk hpS)).2.pos
        · exact (hPsub_gt p hpP).2.2.1.pos)
    by_cases hjQ : j ≡ c.r₀ [MOD c.Q]
    · have hQ_in : c.Q ∈ R.filter (fun p => j ≡ a p [MOD p]) :=
        mem_filter.mpr ⟨mem_union_left _ (mem_insert_self c.Q Qimg), ha_Q.symm ▸ hjQ⟩
      have hle2 : c.Q ≤ ∏ p ∈ R.filter (fun p => j ≡ a p [MOD p]), p :=
        Nat.le_of_dvd hprod2_pos (Finset.dvd_prod_of_mem _ hQ_in)
      calc c.B ≤ c.Q := by omega
        _ = 1 * c.Q := (one_mul c.Q).symm
        _ ≤ _ := Nat.mul_le_mul hprod1_pos hle2
    · by_cases hjD : ∃ d ∈ c.Dset, j ≡ d [MOD q_fn d]
      · obtain ⟨d, hd, hjd⟩ := hjD
        have hq_in : q_fn d ∈ R.filter (fun p => j ≡ a p [MOD p]) :=
          mem_filter.mpr ⟨mem_union_left _ (mem_insert_of_mem (mem_image_of_mem q_fn hd)), (ha_qfn d hd).symm ▸ hjd⟩
        have hle2 : q_fn d ≤ ∏ p ∈ R.filter (fun p => j ≡ a p [MOD p]), p :=
          Nat.le_of_dvd hprod2_pos (Finset.dvd_prod_of_mem _ hq_in)
        have h2Y := (hq_spec d hd).2.1
        calc c.B ≤ q_fn d := by omega
          _ = 1 * q_fn d := (one_mul _).symm
          _ ≤ _ := Nat.mul_le_mul hprod1_pos hle2
      · push Not at hjD
        by_cases hjz : zS j < c.B
        · have hjU : j ∈ U := mem_filter.mpr ⟨mem_Icc.mpr ⟨hj1, hjk⟩, hjz, hjQ, hjD⟩
          let psub := e ⟨j, hjU⟩
          have hp_in : psub.val ∈ R.filter (fun p => j ≡ a p [MOD p]) := by
            refine mem_filter.mpr ⟨mem_union_right _ psub.2, ?_⟩
            rw [ha_Psub psub.val psub.2]
            have hsymm : (e.symm psub).val = j := by simp [psub]
            rw [hsymm]
          have hle2 : psub.val ≤ ∏ p ∈ R.filter (fun p => j ≡ a p [MOD p]), p :=
            Nat.le_of_dvd hprod2_pos (Finset.dvd_prod_of_mem _ hp_in)
          have hgt := (hPsub_gt psub.val psub.2).1
          calc c.B ≤ psub.val := by omega
            _ = 1 * psub.val := (one_mul _).symm
            _ ≤ _ := Nat.mul_le_mul hprod1_pos hle2
        · push Not at hjz
          have hno_Psub_dvd : ∀ p ∈ Psub, ¬ p ∣ j := by
            intro p hp hdvd
            have ⟨hgt, _, _, hpmod⟩ := hPsub_gt p hp
            obtain ⟨m, hm⟩ := hdvd
            have hm1 : m = 1 := by
              have hmpos : 1 ≤ m := by
                rcases Nat.eq_zero_or_pos m with rfl | hpos
                · simp at hm; omega
                · exact hpos
              by_contra hne
              have hm2 : 2 ≤ m := by omega
              have h2p : 2 * p ≤ j := by rw [hm]; nlinarith
              omega
            rw [hm1, mul_one] at hm
            apply hjQ
            change j % c.Q = c.r₀ % c.Q
            rw [hm, hpmod, Nat.mod_eq_of_lt c.hr₀_ltQ]
          have hprod_eq : ∏ p ∈ Pk \ R, p ^ (j.factorization p) = zS j := by
            dsimp only [zS, R]
            refine Finset.prod_subset (Finset.sdiff_subset_sdiff Subset.rfl Finset.subset_union_left) fun p hpS hpnot => ?_
            have hpPk := (Finset.mem_sdiff.mp hpS).1
            have hpP : p ∈ Psub := by
              by_contra hnot
              exact hpnot (Finset.mem_sdiff.mpr ⟨hpPk, fun h => (mem_union.mp h).elim (Finset.mem_sdiff.mp hpS).2 hnot⟩)
            rw [Nat.factorization_eq_zero_of_not_dvd (hno_Psub_dvd p hpP), pow_zero]
          calc c.B ≤ zS j := hjz
            _ = zS j * 1 := (mul_one _).symm
            _ ≤ _ := Nat.mul_le_mul (hprod_eq.symm ▸ le_rfl) hprod2_pos

set_option maxHeartbeats 600000 in
/-- For fixed `B ≥ 3` and prime `Q ≥ max (100 * B) 1000`, all sufficiently large `K` admit
    a weight-`B` restricted prime cover for some `k ∈ Ioc K (10 * K)`. -/
private lemma eventually_exists_hasCoverB {B Q : ℕ} (hB : 3 ≤ B) (hQp : Q.Prime)
    (hQ_big : max (100 * B) 1000 ≤ Q) :
    ∀ᶠ K : ℕ in atTop, ∃ k ∈ Ioc K (10 * K), HasCoverB B k := by
  have hQ100B : 100 * B ≤ Q := (le_max_left _ _).trans hQ_big
  have hQ1000 : 1000 ≤ Q := (le_max_right _ _).trans hQ_big
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hL_top : Tendsto (fun K : ℕ => Real.log (K : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcheb_ev : ∀ᶠ K : ℕ in atTop, 2 * (K : ℝ) ≤ Chebyshev.theta ((10 * K : ℕ) : ℝ) - Chebyshev.theta (K : ℝ) := by
    have hlogK_o : Tendsto (fun K : ℕ => (Real.log ((10 * K + 1 : ℕ) : ℝ) +
        2 * Real.sqrt ((10 * K : ℕ) : ℝ) * Real.log ((10 * K : ℕ) : ℝ)) / (K : ℝ)) atTop (nhds 0) := by
      have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ ((1 : ℝ) / 4)) atTop (nhds 0) := by
        simpa using (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).tendsto_div_nhds_zero
      have ht10 : Tendsto (fun K : ℕ => 10 * (K : ℝ) + 1) atTop atTop :=
        Tendsto.atTop_add (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop) tendsto_const_nhds
      have hinv : Tendsto (fun K : ℕ => 100 / (K : ℝ) ^ ((1 : ℝ) / 4)) atTop (nhds 0) := by
        simpa using tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop)
      refine squeeze_zero_norm' ?_ hinv
      filter_upwards [ht10.eventually (h1.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))),
        eventually_ge_atTop 100] with K hlog hK100
      have hKpos : (0 : ℝ) < K := by positivity
      have h10K : (10 * (K : ℝ) + 1) ^ ((1 : ℝ) / 4) ≤ 2 * (K : ℝ) ^ ((1 : ℝ) / 4) := by
        have h11 : 10 * (K : ℝ) + 1 ≤ 16 * (K : ℝ) := by
          have hK100R : (100 : ℝ) ≤ K := by exact_mod_cast hK100
          linarith
        calc (10 * (K : ℝ) + 1) ^ ((1 : ℝ) / 4) ≤ (16 * (K : ℝ)) ^ ((1 : ℝ) / 4) :=
              Real.rpow_le_rpow (by positivity) h11 (by norm_num)
          _ = (16 : ℝ) ^ ((1 : ℝ) / 4) * (K : ℝ) ^ ((1 : ℝ) / 4) := Real.mul_rpow (by norm_num) hKpos.le
          _ = 2 * (K : ℝ) ^ ((1 : ℝ) / 4) := by
              congr 1; rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
                ← Real.rpow_mul (by norm_num)]; norm_num
      have hlog_le : Real.log ((10 * K + 1 : ℕ) : ℝ) ≤ 2 * (K : ℝ) ^ ((1 : ℝ) / 4) := by
        have hlt := (div_lt_iff₀ (by positivity)).mp hlog
        push_cast; linarith
      have hlog10_le : Real.log ((10 * K : ℕ) : ℝ) ≤ 2 * (K : ℝ) ^ ((1 : ℝ) / 4) :=
        (Real.log_le_log (by positivity) (by push_cast; linarith)).trans hlog_le
      have hsqrt_le : Real.sqrt ((10 * K : ℕ) : ℝ) ≤ 4 * (K : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (K : ℝ)]
        have hsq10 : Real.sqrt 10 ≤ 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
        exact mul_le_mul_of_nonneg_right hsq10 (by positivity)
      rw [Real.norm_of_nonneg (by positivity)]
      rw [div_le_div_iff₀ hKpos (by positivity)]
      have hpow1 : (K : ℝ) ^ ((1 : ℝ) / 4) * (K : ℝ) ^ ((1 : ℝ) / 4) ≤ (K : ℝ) := by
        rw [← Real.rpow_add hKpos]; norm_num
        conv_rhs => rw [← Real.rpow_one (K : ℝ)]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ K)) (by norm_num)
      have hpow2 : (K : ℝ) ^ ((1 : ℝ) / 2) * (K : ℝ) ^ ((1 : ℝ) / 4) * (K : ℝ) ^ ((1 : ℝ) / 4) = (K : ℝ) := by
        rw [← Real.rpow_add hKpos, ← Real.rpow_add hKpos]; norm_num
      have hprod : 2 * Real.sqrt ((10 * K : ℕ) : ℝ) * Real.log ((10 * K : ℕ) : ℝ) ≤
          16 * ((K : ℝ) ^ ((1 : ℝ) / 2) * (K : ℝ) ^ ((1 : ℝ) / 4)) := by
        calc 2 * Real.sqrt ((10 * K : ℕ) : ℝ) * Real.log ((10 * K : ℕ) : ℝ)
            ≤ 2 * (4 * (K : ℝ) ^ ((1 : ℝ) / 2)) * (2 * (K : ℝ) ^ ((1 : ℝ) / 4)) := by
              have hnn : 0 ≤ Real.log ((10 * K : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 10 * K))
              exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)) hlog10_le hnn (by positivity)
          _ = 16 * ((K : ℝ) ^ ((1 : ℝ) / 2) * (K : ℝ) ^ ((1 : ℝ) / 4)) := by ring
      nlinarith [Real.rpow_nonneg hKpos.le ((1 : ℝ) / 4)]
    filter_upwards [hlogK_o.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 10)),
      eventually_ge_atTop 100] with K herr hK100
    have hKpos : (0 : ℝ) < K := by positivity
    have hlo := Chebyshev.theta_ge (10 * K)
    have hhi := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ K by positivity)
    have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
    have herr' : Real.log ((10 * K + 1 : ℕ) : ℝ) +
        2 * Real.sqrt ((10 * K : ℕ) : ℝ) * Real.log ((10 * K : ℕ) : ℝ) < (1 / 10 : ℝ) * (K : ℝ) :=
      (div_lt_iff₀ hKpos).mp herr
    have h10R : ((10 * K : ℕ) : ℝ) = 10 * (K : ℝ) := by push_cast; ring
    have h10p1 : ((10 * K + 1 : ℕ) : ℝ) = 10 * (K : ℝ) + 1 := by push_cast; ring
    rw [h10R] at hlo
    rw [h10p1, h10R] at herr'
    have hlog2_lo : (69 / 100 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog2_hi : Real.log 2 < (70 / 100 : ℝ) := by linarith [Real.log_two_lt_d9]
    rw [h10R]
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  have hL_ev : ∀ᶠ L : ℝ in atTop,
      10000 ≤ L ∧
      (1000000 : ℝ) * (Q : ℝ) ^ 4 * (B : ℝ) ^ 3 ≤ L ^ ((1 : ℝ) / 10) ∧
      Real.log (10000 * (Q : ℝ) * (B : ℝ)) + 100 ≤ (1 / 10 : ℝ) * L ^ ((3 : ℝ) / 5) ∧
      10 * L ^ ((3 : ℝ) / 5) + 10 * Real.log L + 100 ≤ L / 4 ∧
      Real.log (B : ℝ) + Real.log (2 * L + 1) +
        4 * L ^ ((2 : ℝ) / 5) * Real.log (3 * (B : ℝ) * L ^ ((3 : ℝ) / 5) + 1) ≤ (1 / 4 : ℝ) * L ^ ((3 : ℝ) / 5) ∧
      16 * Real.log (2 * L ^ ((3 : ℝ) / 5)) + 40 + 10 * Real.log L ≤ (1 / 4 : ℝ) * L ^ ((2 : ℝ) / 5) := by
    have hlog_div : Tendsto (fun L : ℝ => Real.log L / L ^ ((1 : ℝ) / 10)) atTop (nhds 0) := by
      simpa using (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).tendsto_div_nhds_zero
    have hr10 : Tendsto (fun L : ℝ => L ^ ((1 : ℝ) / 10)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    have hr35 : Tendsto (fun L : ℝ => L ^ ((3 : ℝ) / 5)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    filter_upwards [
      eventually_ge_atTop (10000 : ℝ),
      hr10.eventually (eventually_ge_atTop (1000000 * (Q : ℝ) ^ 4 * (B : ℝ) ^ 3)),
      hr10.eventually (eventually_ge_atTop (10000 : ℝ)),
      hr35.eventually (eventually_ge_atTop (10 * (Real.log (10000 * (Q : ℝ) * (B : ℝ)) + 100))),
      hlog_div.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 1000))
    ] with L hL10 hL2 hL10_ge10000 hL3' hlog_small
    have hLpos : 0 < L := by linarith
    have hL3 : Real.log (10000 * (Q : ℝ) * (B : ℝ)) + 100 ≤ (1 / 10 : ℝ) * L ^ ((3 : ℝ) / 5) := by linarith
    have hlogL_lt : Real.log L < L ^ ((1 : ℝ) / 10) / 1000 := by
      have := (div_lt_iff₀ (Real.rpow_pos_of_pos hLpos _)).mp hlog_small; linarith
    set x := L ^ ((1 : ℝ) / 10)
    have hx_pos : 0 < x := Real.rpow_pos_of_pos hLpos _
    have hL_eq : L = x ^ (10 : ℕ) := by
      dsimp only [x]; rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; norm_num
    have hL35 : L ^ ((3 : ℝ) / 5) = x ^ (6 : ℕ) := by
      dsimp only [x]; rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; norm_num
    have hL25 : L ^ ((2 : ℝ) / 5) = x ^ (4 : ℕ) := by
      dsimp only [x]; rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; norm_num
    have hx_ge10 : (10000 : ℝ) ≤ x := hL10_ge10000
    have hlogL_le_x : Real.log L ≤ x / 1000 := hlogL_lt.le
    refine ⟨hL10, hL2, hL3, ?_, ?_, ?_⟩
    · rw [hL35, hL_eq]
      have hx4 : (1000 : ℝ) ≤ x ^ (4 : ℕ) := by
        have := pow_le_pow_left₀ (by norm_num) hx_ge10 4; norm_num at this; linarith
      have hx6 : (1 : ℝ) ≤ x ^ (6 : ℕ) := by
        have := pow_le_pow_left₀ (by norm_num) (by linarith : (1 : ℝ) ≤ x) 6; norm_num at this; linarith
      have hx10 : x ^ (10 : ℕ) = x ^ (4 : ℕ) * x ^ (6 : ℕ) := by ring
      have hx10_ge : 1000 * x ^ (6 : ℕ) ≤ x ^ (10 : ℕ) := by
        rw [hx10]; exact mul_le_mul_of_nonneg_right hx4 (by positivity)
      have h1x : x ≤ x ^ (6 : ℕ) := by
        have : x ^ (1 : ℕ) ≤ x ^ (6 : ℕ) := pow_le_pow_right₀ (by linarith) (by omega)
        simpa using this
      have hlogx10 : Real.log (x ^ (10 : ℕ)) ≤ x / 1000 := by rw [← hL_eq]; exact hlogL_le_x
      linarith
    · rw [hL25, hL35]
      have hlogB : Real.log (B : ℝ) ≤ x := by
        have hB_le_x : (B : ℝ) ≤ x := by
          have h1 : (1 : ℝ) ≤ (Q : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ Q))
          have h2 : (B : ℝ) ≤ (B : ℝ) ^ 3 := by
            calc (B : ℝ) = (B : ℝ) ^ (1 : ℕ) := (pow_one _).symm
              _ ≤ (B : ℝ) ^ 3 := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ B)) (by omega)
          nlinarith [hL2]
        exact (Real.log_le_sub_one_of_pos hBpos).trans (by linarith)
      have h2L1 : Real.log (2 * L + 1) ≤ 2 * Real.log L := by
        have hle : 2 * L + 1 ≤ L ^ 2 := by nlinarith
        calc Real.log (2 * L + 1) ≤ Real.log (L ^ 2) := Real.log_le_log (by positivity) hle
          _ = 2 * Real.log L := by rw [Real.log_pow]; norm_num
      have harg_le : 3 * (B : ℝ) * x ^ (6 : ℕ) + 1 ≤ L := by
        rw [hL_eq]
        have h3B : 3 * (B : ℝ) ≤ x := by
          have h1 : (1 : ℝ) ≤ (Q : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ Q))
          have h2 : (B : ℝ) ≤ (B : ℝ) ^ 3 := by
            calc (B : ℝ) = (B : ℝ) ^ (1 : ℕ) := (pow_one _).symm
              _ ≤ (B : ℝ) ^ 3 := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ B)) (by omega)
          nlinarith [hL2]
        have hx7 : 3 * (B : ℝ) * x ^ (6 : ℕ) ≤ x ^ (7 : ℕ) := by
          calc 3 * (B : ℝ) * x ^ (6 : ℕ) ≤ x * x ^ (6 : ℕ) := mul_le_mul_of_nonneg_right h3B (by positivity)
            _ = x ^ (7 : ℕ) := by ring
        have hx3 : (2 : ℝ) ≤ x ^ (3 : ℕ) := by
          have := pow_le_pow_left₀ (by norm_num) hx_ge10 3; norm_num at this; linarith
        have hx7ge : (1 : ℝ) ≤ x ^ (7 : ℕ) := by
          have := pow_le_pow_left₀ (by norm_num) (by linarith : (1 : ℝ) ≤ x) 7; norm_num at this; linarith
        have hx10 : x ^ (10 : ℕ) = x ^ (3 : ℕ) * x ^ (7 : ℕ) := by ring
        nlinarith
      have hlog_arg : Real.log (3 * (B : ℝ) * x ^ (6 : ℕ) + 1) ≤ Real.log L :=
        Real.log_le_log (by positivity) harg_le
      have hterm3 : 4 * x ^ (4 : ℕ) * Real.log (3 * (B : ℝ) * x ^ (6 : ℕ) + 1) ≤ 4 * x ^ (4 : ℕ) * (x / 1000) :=
        mul_le_mul_of_nonneg_left (hlog_arg.trans hlogL_le_x) (by positivity)
      have hx5 : x ^ (5 : ℕ) ≤ x ^ (6 : ℕ) / 10000 := by
        rw [le_div_iff₀ (by norm_num)]; nlinarith [show x ^ (6 : ℕ) = x * x ^ (5 : ℕ) by ring, pow_pos hx_pos 5]
      have hx1 : x ≤ x ^ (6 : ℕ) / 10000 := by
        have h1 : x ^ (1 : ℕ) ≤ x ^ (5 : ℕ) := pow_le_pow_right₀ (by linarith) (by omega)
        simp only [pow_one] at h1; linarith
      have h45 : 4 * x ^ (4 : ℕ) * (x / 1000) = (4 / 1000) * x ^ (5 : ℕ) := by ring
      linarith
    · rw [hL35, hL25]
      have h2x6 : 2 * x ^ (6 : ℕ) ≤ L := by
        rw [hL_eq]
        have hx4 : (2 : ℝ) ≤ x ^ (4 : ℕ) := by
          have := pow_le_pow_left₀ (by norm_num) hx_ge10 4; norm_num at this; linarith
        have hx10 : x ^ (10 : ℕ) = x ^ (4 : ℕ) * x ^ (6 : ℕ) := by ring
        nlinarith [pow_pos hx_pos 6]
      have hlog2x6 : Real.log (2 * x ^ (6 : ℕ)) ≤ Real.log L := Real.log_le_log (by positivity) h2x6
      have hx3 : (10000 : ℝ) ≤ x ^ (3 : ℕ) := by
        have := pow_le_pow_left₀ (by norm_num) hx_ge10 3; norm_num at this; linarith
      have hx4_eq : x ^ (4 : ℕ) = x * x ^ (3 : ℕ) := by ring
      nlinarith [hlog2x6, hlogL_le_x, hx3, hx4_eq]
  filter_upwards [hcheb_ev, hL_top.eventually hL_ev, eventually_ge_atTop (max 1000000 (100 * Q ^ 2))]
    with K hcheb hLall hKbig
  obtain ⟨hL10, hL2, hL3, hL4, hL5, hL6⟩ := hLall
  let L : ℝ := Real.log (K : ℝ)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by have := (le_max_left 1000000 (100 * Q ^ 2)).trans hKbig; omega : 0 < K)
  have hLpos : 0 < L := by linarith
  have hL35_ge : (1000 : ℝ) ≤ L ^ ((3 : ℝ) / 5) := by
    have h1 : (1000 : ℝ) ≤ L ^ ((1 : ℝ) / 10) := by
      have : (1000000 : ℝ) ≤ (1000000 : ℝ) * (Q : ℝ) ^ 4 * (B : ℝ) ^ 3 := by
        have h1' : (1 : ℝ) ≤ (Q : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ Q))
        have h2' : (1 : ℝ) ≤ (B : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ B))
        nlinarith
      linarith
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  let Y : ℕ := Nat.floor (Real.exp (L ^ ((3 : ℝ) / 5)))
  have hY_le_exp : (Y : ℝ) ≤ Real.exp (L ^ ((3 : ℝ) / 5)) := Nat.floor_le (Real.exp_pos _).le
  have hY_ge_half : Real.exp (L ^ ((3 : ℝ) / 5)) / 2 ≤ (Y : ℝ) := by
    have hgt : Real.exp (L ^ ((3 : ℝ) / 5)) - 1 < (Y : ℝ) := Nat.sub_one_lt_floor _
    have hexp2 : (2 : ℝ) ≤ Real.exp (L ^ ((3 : ℝ) / 5)) := by
      have : Real.exp 1 ≤ Real.exp (L ^ ((3 : ℝ) / 5)) := Real.exp_le_exp.mpr (by linarith)
      linarith [Real.exp_one_gt_d9]
    linarith
  have hY_ge_1000QB : 1000 * Q * B ≤ Y := by
    have h1 : 10000 * (Q : ℝ) * (B : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * L ^ ((3 : ℝ) / 5)) := by
      have hlog : Real.log (10000 * (Q : ℝ) * (B : ℝ)) ≤ (1 / 10 : ℝ) * L ^ ((3 : ℝ) / 5) := by linarith
      calc 10000 * (Q : ℝ) * (B : ℝ) = Real.exp (Real.log (10000 * (Q : ℝ) * (B : ℝ))) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp ((1 / 10 : ℝ) * L ^ ((3 : ℝ) / 5)) := Real.exp_le_exp.mpr hlog
    have h2 : Real.exp ((1 / 10 : ℝ) * L ^ ((3 : ℝ) / 5)) ≤ Real.exp (L ^ ((3 : ℝ) / 5)) / 2 := by
      have h3 : (2 : ℝ) ≤ Real.exp ((9 / 10 : ℝ) * L ^ ((3 : ℝ) / 5)) := by
        have : Real.exp 1 ≤ Real.exp ((9 / 10 : ℝ) * L ^ ((3 : ℝ) / 5)) := Real.exp_le_exp.mpr (by linarith)
        linarith [Real.exp_one_gt_d9]
      rw [le_div_iff₀ (by norm_num)]
      calc Real.exp ((1 / 10 : ℝ) * L ^ ((3 : ℝ) / 5)) * 2
          ≤ Real.exp ((1 / 10 : ℝ) * L ^ ((3 : ℝ) / 5)) * Real.exp ((9 / 10 : ℝ) * L ^ ((3 : ℝ) / 5)) :=
            mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        _ = Real.exp (L ^ ((3 : ℝ) / 5)) := by rw [← Real.exp_add]; congr 1; ring
    exact_mod_cast (show 1000 * (Q : ℝ) * (B : ℝ) ≤ (Y : ℝ) by linarith)
  have hY_ge_1000Q : 1000 * Q ≤ Y := le_trans (by nlinarith) hY_ge_1000QB
  have hY_ge_1000 : 1000 ≤ Y := le_trans (by nlinarith) hY_ge_1000QB
  have hY_pos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hY_le_K14 : (Y : ℝ) ^ 4 ≤ (K : ℝ) := by
    have h1 : (Y : ℝ) ^ 4 ≤ Real.exp (4 * L ^ ((3 : ℝ) / 5)) := by
      calc (Y : ℝ) ^ 4 ≤ (Real.exp (L ^ ((3 : ℝ) / 5))) ^ 4 := pow_le_pow_left₀ (by positivity) hY_le_exp 4
        _ = Real.exp (4 * L ^ ((3 : ℝ) / 5)) := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : Real.exp (4 * L ^ ((3 : ℝ) / 5)) ≤ (K : ℝ) := by
      have h4leL : 4 * L ^ ((3 : ℝ) / 5) ≤ L := by
        have hlogL_nn : 0 ≤ Real.log L := Real.log_nonneg (by linarith [hL10])
        dsimp only [L] at hlogL_nn ⊢
        linarith [hL4, hL35_ge]
      calc Real.exp (4 * L ^ ((3 : ℝ) / 5)) ≤ Real.exp L := Real.exp_le_exp.mpr h4leL
        _ = (K : ℝ) := Real.exp_log hKpos
    linarith
  have hY_small : 1000 * Q * B * Y ≤ K := by
    have h1 : (1000 * (Q : ℝ) * (B : ℝ)) * (Y : ℝ) ≤ (Y : ℝ) ^ 4 := by
      have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast (by omega : 1 ≤ Y)
      have hY2 : (Y : ℝ) ^ 2 ≤ (Y : ℝ) ^ 4 := pow_le_pow_right₀ hY1 (by omega)
      have hQB : 1000 * (Q : ℝ) * (B : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY_ge_1000QB
      nlinarith [sq (Y : ℝ)]
    exact_mod_cast (h1.trans hY_le_K14)
  have hY_le_K : 1000 * Y ≤ K := by
    have h1 : 1000 * Y ≤ 1000 * Q * B * Y := by
      have hQB1 : 1 ≤ Q * B := by nlinarith
      nlinarith
    exact h1.trans hY_small
  have hlogY_lo : (1 / 2 : ℝ) * L ^ ((3 : ℝ) / 5) ≤ Real.log (Y : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hY_ge_half
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h1
    linarith [Real.log_two_lt_d9]
  have hlogY_hi : Real.log (Y : ℝ) ≤ L ^ ((3 : ℝ) / 5) := by
    have h1 := Real.log_le_log hY_pos hY_le_exp
    rwa [Real.log_exp] at h1
  -- Pigeonhole residue class r₀ ∈ Icc 1 (Q - 1)
  have hr0_exists : ∃ r₀ ∈ Icc 1 (Q - 1),
      (K : ℝ) / (4 * (Q : ℝ) * L) ≤ (((Ioc K (10 * K)).filter (fun p => p.Prime ∧ p % Q = r₀)).card : ℝ) := by
    let P10 := (Ioc K (10 * K)).filter Nat.Prime
    have hP10_card : (K : ℝ) / (2 * L) ≤ (P10.card : ℝ) := by
      have hsum_eq : Chebyshev.theta ((10 * K : ℕ) : ℝ) - Chebyshev.theta (K : ℝ) =
          ∑ p ∈ P10, Real.log (p : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
        have hunion : (10 * K).primesLE = K.primesLE ∪ P10 := by
          ext p; simp only [Nat.mem_primesLE, mem_union, P10, mem_filter, mem_Ioc]
          constructor
          · rintro ⟨hp10, hpr⟩
            by_cases hpK : p ≤ K
            · exact Or.inl ⟨hpK, hpr⟩
            · exact Or.inr ⟨⟨by omega, hp10⟩, hpr⟩
          · rintro (⟨hpK, hpr⟩ | ⟨⟨_, hp10⟩, hpr⟩)
            · exact ⟨by omega, hpr⟩
            · exact ⟨hp10, hpr⟩
        have hdisj : Disjoint K.primesLE P10 := by
          rw [Finset.disjoint_left]; intro p hp1 hp2
          have := (Nat.mem_primesLE.mp hp1).1
          have := (mem_Ioc.mp (mem_filter.mp hp2).1).1; omega
        rw [hunion, Finset.sum_union hdisj]; ring
      have hlog10 : Real.log ((10 * K : ℕ) : ℝ) ≤ 2 * L := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hKpos.ne']
        linarith [CoverCtx.hlog10_le4, hL10]
      have hsum_le : ∑ p ∈ P10, Real.log (p : ℝ) ≤ (P10.card : ℝ) * (2 * L) := by
        calc ∑ p ∈ P10, Real.log (p : ℝ)
            ≤ ∑ _p ∈ P10, (2 * L) := sum_le_sum fun p hp =>
              (Real.log_le_log (Nat.cast_pos.mpr (mem_filter.mp hp).2.pos)
                (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2)).trans hlog10
          _ = (P10.card : ℝ) * (2 * L) := by rw [Finset.sum_const, nsmul_eq_mul]
      rw [div_le_iff₀ (by positivity)]
      linarith [hcheb, hsum_eq, hsum_le]
    have hmaps_r : ∀ p ∈ P10, p % Q ∈ Icc 1 (Q - 1) := by
      intro p hp
      have hpK := (mem_Ioc.mp (mem_filter.mp hp).1).1
      have hpr := (mem_filter.mp hp).2
      have hlt := Nat.mod_lt p hQp.pos
      have hne0 : p % Q ≠ 0 := by
        intro h0
        have hQp_dvd : Q ∣ p := Nat.dvd_of_mod_eq_zero h0
        have heq := (Nat.prime_dvd_prime_iff_eq hQp hpr).mp hQp_dvd
        have hK_gt_Q : Q < K := by
          have := (le_max_right 1000000 (100 * Q ^ 2)).trans hKbig
          nlinarith
        omega
      exact mem_Icc.mpr ⟨by omega, by omega⟩
    have hfib : (P10.card : ℝ) = ∑ r ∈ Icc 1 (Q - 1),
        (((Ioc K (10 * K)).filter (fun p => p.Prime ∧ p % Q = r)).card : ℝ) := by
      have hnat : P10.card = ∑ r ∈ Icc 1 (Q - 1), ((Ioc K (10 * K)).filter (fun p => p.Prime ∧ p % Q = r)).card := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to hmaps_r]
        refine sum_congr rfl fun r _ => ?_
        rw [Finset.card_eq_sum_ones]
        refine sum_congr ?_ fun _ _ => rfl
        ext p; simp only [P10, mem_filter]; tauto
      exact_mod_cast hnat
    by_contra! hall
    have hsum_lt : ∑ r ∈ Icc 1 (Q - 1), (((Ioc K (10 * K)).filter (fun p => p.Prime ∧ p % Q = r)).card : ℝ) <
        ((Q - 1 : ℕ) : ℝ) * ((K : ℝ) / (4 * (Q : ℝ) * L)) := by
      have hne : (Icc 1 (Q - 1)).Nonempty := ⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
      calc ∑ r ∈ Icc 1 (Q - 1), (((Ioc K (10 * K)).filter (fun p => p.Prime ∧ p % Q = r)).card : ℝ)
          < ∑ _r ∈ Icc 1 (Q - 1), ((K : ℝ) / (4 * (Q : ℝ) * L)) := sum_lt_sum_of_nonempty hne hall
        _ = ((Icc 1 (Q - 1)).card : ℝ) * ((K : ℝ) / (4 * (Q : ℝ) * L)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((Q - 1 : ℕ) : ℝ) * ((K : ℝ) / (4 * (Q : ℝ) * L)) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
    have hQ1_le : ((Q - 1 : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast Nat.sub_le Q 1
    have h4_le : ((Q - 1 : ℕ) : ℝ) * ((K : ℝ) / (4 * (Q : ℝ) * L)) ≤ (K : ℝ) / (4 * L) := by
      calc ((Q - 1 : ℕ) : ℝ) * ((K : ℝ) / (4 * (Q : ℝ) * L))
          ≤ (Q : ℝ) * ((K : ℝ) / (4 * (Q : ℝ) * L)) := mul_le_mul_of_nonneg_right hQ1_le (by positivity)
        _ = (K : ℝ) / (4 * L) := by field_simp [hQpos.ne']
    have hposKL : 0 < (K : ℝ) / (4 * L) := by positivity
    have h24 : (K : ℝ) / (2 * L) = 2 * ((K : ℝ) / (4 * L)) := by ring
    linarith [hP10_card, hfib, hsum_lt, h4_le, hposKL, h24]
  obtain ⟨r₀, hr₀_mem, hr₀_card⟩ := hr0_exists
  let ctx : CoverCtx := {
    B := B, Q := Q, K := K, Y := Y, r₀ := r₀,
    hB := hB, hQp := hQp, hQ100B := hQ100B, hQ1000 := hQ1000, hKbig := hKbig,
    hL10 := hL10, hL2 := hL2, hL3 := hL3, hL4 := hL4, hL5 := hL5, hL6 := hL6,
    hY_le_exp := hY_le_exp, hY_ge_half := hY_ge_half,
    hY_ge_1000QB := hY_ge_1000QB, hY_ge_1000Q := hY_ge_1000Q, hY_ge_1000 := hY_ge_1000,
    hY_le_K14 := hY_le_K14, hY_small := hY_small, hY_le_K := hY_le_K,
    hlogY_lo := hlogY_lo, hlogY_hi := hlogY_hi,
    hr₀_ge1 := (mem_Icc.mp hr₀_mem).1,
    hr₀_ltQ := by have := (mem_Icc.mp hr₀_mem).2; omega,
    hr₀_card := hr₀_card
  }
  exact ctx.exists_cover

theorem H1_proved : OMA.R_Erdos387_erdos_387_R1.H1 := by
  intro B K₀ hB
  obtain ⟨Q, hQ_ge, hQp⟩ := Nat.exists_infinite_primes (max (100 * B) 1000)
  obtain ⟨K, hK_ge, k, hkI, hcov⟩ :=
    ((eventually_ge_atTop (max 3 K₀)).and (eventually_exists_hasCoverB hB hQp hQ_ge)).exists
  have hk_ge : max 3 K₀ ≤ k := le_trans hK_ge (mem_Ioc.mp hkI).1.le
  obtain ⟨a, g, hg⟩ := h1_witness_of_hasCoverB hcov
  exact ⟨k, hk_ge, a, g, hg⟩

end OMA.Erdos387S3

theorem OMA.solution : OMA.R_Erdos387_erdos_387_R1.H1 :=
  OMA.Erdos387S3.H1_proved

