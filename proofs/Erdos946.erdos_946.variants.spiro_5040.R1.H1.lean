import OMAReductions.R_Erdos946_erdos_946_variants_spiro_5040_R1
import Mathlib

/-!
# Dimension-eight Selberg weighted sieve for Spiro's 5040 theorem

We prove `OMA.R_Erdos946_erdos_946_variants_spiro_5040_R1.H1` using a one-dimensional
Selberg weighted sieve on the product `F(n) = ∏_{q ∈ P} (q * n + 1)` with
`P = {11, 17, 23, 29, 41, 47, 53, 59}`, parameters `k = 400`, `X = B^400`,
`R = B^100`, `y = B^180`, and linear Selberg weights `z(r) = μ(r) * (1 - log r / log R)`.
-/

namespace Erdos946Spiro

open Finset Filter Real ArithmeticFunction
open scoped Classical

noncomputable section

/- Section 1: Spiro's Eight Linear Forms, Local Root Counts, and CRT -/

private def P : Finset ℕ := {11, 17, 23, 29, 41, 47, 53, 59}

private def F (n : ℕ) : ℕ := ∏ q ∈ P, (q * n + 1)

private lemma P_card : P.card = 8 := by decide

private lemma P_spec : ∀ q ∈ P, q.Prime ∧ q ≤ 59 ∧ 11 ≤ q := by
  intro q hq
  simp only [P, mem_insert, mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma P_diff_dvd_5040 : ∀ q ∈ P, ∀ t ∈ P, q < t → t - q ∣ 5040 := by
  intro q hq t ht
  simp only [P, mem_insert, mem_singleton] at hq ht
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma P_diff_le_48 : ∀ q ∈ P, ∀ t ∈ P, q < t → t - q ≤ 48 := by
  intro q hq t ht
  simp only [P, mem_insert, mem_singleton] at hq ht
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma F_pos (n : ℕ) : 0 < F n := by
  unfold F
  exact Finset.prod_pos fun q _ => Nat.succ_pos _

private lemma F_zero : F 0 = 1 := by decide

private lemma F_le_of_le {n X : ℕ} (hX : 1 ≤ X) (hn : n ≤ 2 * X) :
    F n ≤ (119 * X) ^ 8 := by
  unfold F
  calc ∏ q ∈ P, (q * n + 1)
      ≤ ∏ _q ∈ P, (119 * X) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro q hq
        have hq59 : q ≤ 59 := (P_spec q hq).2.1
        nlinarith
    _ = (119 * X) ^ P.card := Finset.prod_const _
    _ = (119 * X) ^ 8 := by rw [P_card]

private lemma prime_dvd_F_iff {p n : ℕ} (hp : p.Prime) :
    p ∣ F n ↔ ∃ q ∈ P, p ∣ q * n + 1 := by
  unfold F
  rw [hp.prime.dvd_finsetProd_iff]

private lemma pairwise_coprime_of_rough {B n : ℕ} (hB : 5040 ≤ B)
    (hrough : ∀ p ∈ (F n).primeFactors, B < p) :
    ∀ q ∈ P, ∀ t ∈ P, q ≠ t → Nat.Coprime (q * n + 1) (t * n + 1) := by
  intro q hq t ht hne
  apply Nat.coprime_of_dvd
  intro p hp hqp htp
  have hpF : p ∈ (F n).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hp, (prime_dvd_F_iff hp).mpr ⟨q, hq, hqp⟩, (F_pos n).ne'⟩
  have hpB : 5040 < p := lt_of_le_of_lt hB (hrough p hpF)
  have hnotn : ¬ p ∣ n := by
    intro hpn
    have : p ∣ q * n := dvd_mul_of_dvd_right hpn q
    have : p ∣ 1 := (Nat.dvd_add_right this).mp hqp
    exact hp.not_dvd_one this
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hsub : (t - q) * n + (q * n + 1) = t * n + 1 := by
      have : (t - q) + q = t := Nat.sub_add_cancel hlt.le
      nlinarith
    have hd : p ∣ (t - q) * n := (Nat.dvd_add_left hqp).mp (hsub.symm ▸ htp)
    have hdtq : p ∣ t - q := (hp.dvd_mul.mp hd).resolve_right hnotn
    have hd5040 : p ∣ 5040 := hdtq.trans (P_diff_dvd_5040 q hq t ht hlt)
    exact (Nat.le_of_dvd (by decide) hd5040).not_gt hpB
  · have hsub : (q - t) * n + (t * n + 1) = q * n + 1 := by
      have : (q - t) + t = q := Nat.sub_add_cancel hgt.le
      nlinarith
    have hd : p ∣ (q - t) * n := (Nat.dvd_add_left htp).mp (hsub.symm ▸ hqp)
    have hdqt : p ∣ q - t := (hp.dvd_mul.mp hd).resolve_right hnotn
    have hd5040 : p ∣ 5040 := hdqt.trans (P_diff_dvd_5040 t ht q hq hgt)
    exact (Nat.le_of_dvd (by decide) hd5040).not_gt hpB

private lemma sum_primeFactors_card_eq_F {B n : ℕ} (hB : 5040 ≤ B)
    (hrough : ∀ p ∈ (F n).primeFactors, B < p) :
    ∑ q ∈ P, (q * n + 1).primeFactors.card = (F n).primeFactors.card := by
  have hcop := pairwise_coprime_of_rough hB hrough
  have hbiUnion : (F n).primeFactors = P.biUnion (fun q => (q * n + 1).primeFactors) := by
    ext p
    simp only [Nat.mem_primeFactors, Finset.mem_biUnion, (F_pos n).ne', ne_eq, not_false_eq_true,
      and_true, Nat.succ_ne_zero]
    constructor
    · rintro ⟨hp, hd⟩
      obtain ⟨q, hq, hqd⟩ := (prime_dvd_F_iff hp).mp hd
      exact ⟨q, hq, hp, hqd⟩
    · rintro ⟨q, hq, hp, hqd⟩
      exact ⟨hp, (prime_dvd_F_iff hp).mpr ⟨q, hq, hqd⟩⟩
  rw [hbiUnion, Finset.card_biUnion]
  intro q hq t ht hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro p hpq hpt
  rw [Nat.mem_primeFactors] at hpq hpt
  have h1 : p ∣ Nat.gcd (q * n + 1) (t * n + 1) := Nat.dvd_gcd hpq.2.1 hpt.2.1
  rw [(hcop q hq t ht hne).gcd_eq_one] at h1
  exact hpq.1.not_dvd_one h1

/-- Number of roots of `F(a) ≡ 0 (mod p)` in `{0, ..., p - 1}`. -/
private def omegaP (p : ℕ) : ℕ :=
  ((Finset.range p).filter (fun a => p ∣ F a)).card

private lemma exists_unique_root_mod_prime {p q : ℕ} (hp : p.Prime) (hq : ¬ p ∣ q) :
    ∃! a, a < p ∧ p ∣ q * a + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro h
    exact hq ((ZMod.natCast_eq_zero_iff q p).mp h)
  let x : ZMod p := -(q : ZMod p)⁻¹
  refine ⟨x.val, ⟨x.val_lt, ?_⟩, ?_⟩
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    simp [x, mul_neg, mul_inv_cancel₀ hq0]
  · intro a ⟨ha, hda⟩
    have ha0 : ((q * a + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hda
    push_cast at ha0
    have ha_eq : (a : ZMod p) = x := by
      have h1 : (q : ZMod p) * (a : ZMod p) = -1 := eq_neg_of_add_eq_zero_left ha0
      calc (a : ZMod p) = (q : ZMod p)⁻¹ * ((q : ZMod p) * (a : ZMod p)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
        _ = (q : ZMod p)⁻¹ * (-1) := by rw [h1]
        _ = x := by simp [x]
    have hval := congrArg ZMod.val ha_eq
    rwa [ZMod.val_natCast_of_lt ha] at hval

private lemma omegaP_lt_self {p : ℕ} (hp : p.Prime) : omegaP p < p := by
  unfold omegaP
  have hss : (Finset.range p).filter (fun a => p ∣ F a) ⊂ Finset.range p := by
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    refine ⟨0, Finset.mem_range.mpr hp.pos, ?_⟩
    simp [F_zero, hp.not_dvd_one]
  simpa using Finset.card_lt_card hss

private lemma omegaP_pos {p : ℕ} (hp : p.Prime) : 0 < omegaP p := by
  -- At least one of 11, 17 is not divisible by p
  have hq_exists : ∃ q ∈ P, ¬ p ∣ q := by
    by_cases h11 : p ∣ 11
    · refine ⟨17, by decide, fun h17 => ?_⟩
      have h6 : p ∣ 6 := by
        have : 11 + 6 = 17 := rfl
        exact (Nat.dvd_add_right h11).mp (this.symm ▸ h17)
      have h1 : p ∣ 1 := by
        have h11_le : p ≤ 11 := Nat.le_of_dvd (by decide) h11
        have h6_le : p ≤ 6 := Nat.le_of_dvd (by decide) h6
        have hp2 := hp.two_le
        interval_cases p <;> simp_all
      exact hp.not_dvd_one h1
    · exact ⟨11, by decide, h11⟩
  obtain ⟨q, hq, hndvd⟩ := hq_exists
  obtain ⟨a, ⟨ha, hda⟩, _⟩ := exists_unique_root_mod_prime hp hndvd
  unfold omegaP
  exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr ha, (prime_dvd_F_iff hp).mpr ⟨q, hq, hda⟩⟩⟩

private lemma omegaP_le_eight {p : ℕ} (hp : p.Prime) : omegaP p ≤ 8 := by
  unfold omegaP
  have hsub : (Finset.range p).filter (fun a => p ∣ F a) ⊆
      P.biUnion (fun q => (Finset.range p).filter (fun a => p ∣ q * a + 1)) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨q, hq, hqd⟩ := (prime_dvd_F_iff hp).mp ha.2
    exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_filter.mpr ⟨ha.1, hqd⟩⟩
  calc ((Finset.range p).filter (fun a => p ∣ F a)).card
      ≤ (P.biUnion (fun q => (Finset.range p).filter (fun a => p ∣ q * a + 1))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ q ∈ P, ((Finset.range p).filter (fun a => p ∣ q * a + 1)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ P, 1 := by
        apply Finset.sum_le_sum
        intro q _
        by_cases hqp : p ∣ q
        · have hempty : (Finset.range p).filter (fun a => p ∣ q * a + 1) = ∅ := by
            ext a
            simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
            intro _ hd
            exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_left hqp a)).mp hd)
          simp [hempty]
        · obtain ⟨a0, ⟨ha0, hda0⟩, huniq⟩ := exists_unique_root_mod_prime hp hqp
          have heq : (Finset.range p).filter (fun a => p ∣ q * a + 1) = {a0} := by
            ext a
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
            exact ⟨fun h => huniq a h, fun h => h ▸ ⟨ha0, hda0⟩⟩
          simp [heq]
    _ = 8 := by simp [P_card]

private lemma omegaP_eq_eight {p : ℕ} (hp : p.Prime) (hp59 : 59 < p) : omegaP p = 8 := by
  unfold omegaP
  have heq : (Finset.range p).filter (fun a => p ∣ F a) =
      P.biUnion (fun q => (Finset.range p).filter (fun a => p ∣ q * a + 1)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨ha, hd⟩
      obtain ⟨q, hq, hqd⟩ := (prime_dvd_F_iff hp).mp hd
      exact ⟨q, hq, ha, hqd⟩
    · rintro ⟨q, hq, ha, hqd⟩
      exact ⟨ha, (prime_dvd_F_iff hp).mpr ⟨q, hq, hqd⟩⟩
  rw [heq, Finset.card_biUnion]
  · have h1 : ∀ q ∈ P, ((Finset.range p).filter (fun a => p ∣ q * a + 1)).card = 1 := by
      intro q hq
      have hndvd : ¬ p ∣ q := by
        intro hd
        have := Nat.le_of_dvd (P_spec q hq).1.pos hd
        have := (P_spec q hq).2.1
        omega
      obtain ⟨a0, ⟨ha0, hda0⟩, huniq⟩ := exists_unique_root_mod_prime hp hndvd
      have hs : (Finset.range p).filter (fun a => p ∣ q * a + 1) = {a0} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        exact ⟨fun h => huniq a h, fun h => h ▸ ⟨ha0, hda0⟩⟩
      simp [hs]
    rw [Finset.sum_congr rfl h1]
    simp [P_card]
  · intro q hq t ht hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a haq hat
    rw [Finset.mem_filter] at haq hat
    have hnot : ¬ p ∣ a := by
      intro hpa
      exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_right hpa q)).mp haq.2)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsub : (t - q) * a + (q * a + 1) = t * a + 1 := by
        have : (t - q) + q = t := Nat.sub_add_cancel hlt.le
        nlinarith
      have hd : p ∣ (t - q) * a := (Nat.dvd_add_left haq.2).mp (hsub.symm ▸ hat.2)
      have hdtq : p ∣ t - q := (hp.dvd_mul.mp hd).resolve_right hnot
      have hle48 : t - q ≤ 48 := P_diff_le_48 q hq t ht hlt
      have hpos : 0 < t - q := Nat.sub_pos_of_lt hlt
      have := Nat.le_of_dvd hpos hdtq
      omega
    · have hsub : (q - t) * a + (t * a + 1) = q * a + 1 := by
        have : (q - t) + t = q := Nat.sub_add_cancel hgt.le
        nlinarith
      have hd : p ∣ (q - t) * a := (Nat.dvd_add_left hat.2).mp (hsub.symm ▸ haq.2)
      have hdqt : p ∣ q - t := (hp.dvd_mul.mp hd).resolve_right hnot
      have hle48 : q - t ≤ 48 := P_diff_le_48 t ht q hq hgt
      have hpos : 0 < q - t := Nat.sub_pos_of_lt hgt
      have := Nat.le_of_dvd hpos hdqt
      omega

/-- Multiplicative root count `ω(d)` for squarefree `d`. -/
private def omegaD (d : ℕ) : ℕ :=
  ∏ p ∈ d.primeFactors, omegaP p

private lemma omegaD_one : omegaD 1 = 1 := by
  simp [omegaD]

private lemma omegaD_prime {p : ℕ} (hp : p.Prime) : omegaD p = omegaP p := by
  simp [omegaD, hp.primeFactors]

private lemma omegaD_pos (d : ℕ) : 0 < omegaD d := by
  unfold omegaD
  exact Finset.prod_pos fun p hp => omegaP_pos (Nat.prime_of_mem_primeFactors hp)

private lemma omegaD_mul_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    omegaD (a * b) = omegaD a * omegaD b := by
  unfold omegaD
  rw [hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors]

private lemma omegaD_le_pow (d : ℕ) : omegaD d ≤ 8 ^ d.primeFactors.card := by
  unfold omegaD
  calc ∏ p ∈ d.primeFactors, omegaP p
      ≤ ∏ _p ∈ d.primeFactors, 8 :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p hp =>
          omegaP_le_eight (Nat.prime_of_mem_primeFactors hp)
    _ = 8 ^ d.primeFactors.card := Finset.prod_const _

private lemma omegaD_le_const_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, Squarefree d → (omegaD d : ℝ) ≤ C * (d : ℝ) ^ ((1 : ℝ) / 100) := by
  let S : Finset ℕ := (Finset.range (8 ^ 100 + 1)).filter Nat.Prime
  let C : ℝ := (8 : ℝ) ^ S.card
  refine ⟨C, by positivity, fun d hd => ?_⟩
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hd_prod : d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hd).symm
  have h1 : (omegaD d : ℝ) = ∏ p ∈ d.primeFactors, (omegaP p : ℝ) := by
    unfold omegaD; push_cast; rfl
  have h2 : (d : ℝ) ^ ((1 : ℝ) / 100) = ∏ p ∈ d.primeFactors, (p : ℝ) ^ ((1 : ℝ) / 100) := by
    conv_lhs => rw [hd_prod]
    push_cast
    rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
  rw [h1, h2]
  have hsplit : ∏ p ∈ d.primeFactors, (omegaP p : ℝ) =
      (∏ p ∈ d.primeFactors.filter (· ∈ S), (omegaP p : ℝ)) *
      (∏ p ∈ d.primeFactors.filter (· ∉ S), (omegaP p : ℝ)) :=
    (Finset.prod_filter_mul_prod_filter_not d.primeFactors (· ∈ S) _).symm
  rw [hsplit]
  have hsmall : ∏ p ∈ d.primeFactors.filter (· ∈ S), (omegaP p : ℝ) ≤ C := by
    calc ∏ p ∈ d.primeFactors.filter (· ∈ S), (omegaP p : ℝ)
        ≤ ∏ _p ∈ d.primeFactors.filter (· ∈ S), (8 : ℝ) := by
          apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
          intro p hp
          exact_mod_cast omegaP_le_eight (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      _ = (8 : ℝ) ^ (d.primeFactors.filter (· ∈ S)).card := Finset.prod_const _
      _ ≤ (8 : ℝ) ^ S.card := by
          have hcard_le : (d.primeFactors.filter (· ∈ S)).card ≤ S.card :=
            Finset.card_le_card fun p hp => (Finset.mem_filter.mp hp).2
          exact pow_le_pow_right₀ (by norm_num) hcard_le
  have hlarge : ∏ p ∈ d.primeFactors.filter (· ∉ S), (omegaP p : ℝ) ≤
      ∏ p ∈ d.primeFactors.filter (· ∉ S), (p : ℝ) ^ ((1 : ℝ) / 100) := by
    apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
    intro p hp
    obtain ⟨hpf, hnotS⟩ := Finset.mem_filter.mp hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hpf
    have hgt : 8 ^ 100 < p := by
      by_contra! hle
      exact hnotS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hle), hprime⟩)
    have h8le : (8 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 100) := by
      have hpow : (8 : ℝ) ^ (100 : ℕ) ≤ (p : ℝ) := by exact_mod_cast hgt.le
      calc (8 : ℝ) = ((8 : ℝ) ^ (100 : ℕ)) ^ ((1 : ℝ) / 100) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ (p : ℝ) ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow (by positivity) hpow (by norm_num)
    exact (Nat.cast_le.mpr (omegaP_le_eight hprime)).trans h8le
  have hge1 : 1 ≤ ∏ p ∈ d.primeFactors.filter (· ∈ S), (p : ℝ) ^ ((1 : ℝ) / 100) := by
    apply Finset.one_le_prod
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    exact Real.one_le_rpow (by exact_mod_cast hprime.one_le) (by norm_num)
  have hprod_split : ∏ p ∈ d.primeFactors, (p : ℝ) ^ ((1 : ℝ) / 100) =
      (∏ p ∈ d.primeFactors.filter (· ∈ S), (p : ℝ) ^ ((1 : ℝ) / 100)) *
      (∏ p ∈ d.primeFactors.filter (· ∉ S), (p : ℝ) ^ ((1 : ℝ) / 100)) :=
    (Finset.prod_filter_mul_prod_filter_not d.primeFactors (· ∈ S) _).symm
  rw [hprod_split]
  have hCnn : (0 : ℝ) ≤ C := by positivity
  have hnn : 0 ≤ ∏ p ∈ d.primeFactors.filter (· ∉ S), (p : ℝ) ^ ((1 : ℝ) / 100) :=
    Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (∏ p ∈ d.primeFactors.filter (· ∈ S), (omegaP p : ℝ)) *
        (∏ p ∈ d.primeFactors.filter (· ∉ S), (omegaP p : ℝ))
      ≤ C * (∏ p ∈ d.primeFactors.filter (· ∉ S), (p : ℝ) ^ ((1 : ℝ) / 100)) :=
        mul_le_mul hsmall hlarge (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) hCnn
    _ = C * (1 * (∏ p ∈ d.primeFactors.filter (· ∉ S), (p : ℝ) ^ ((1 : ℝ) / 100))) := by ring
    _ ≤ C * ((∏ p ∈ d.primeFactors.filter (· ∈ S), (p : ℝ) ^ ((1 : ℝ) / 100)) *
        (∏ p ∈ d.primeFactors.filter (· ∉ S), (p : ℝ) ^ ((1 : ℝ) / 100))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hge1 hnn) hCnn

private lemma F_mod_dvd_iff {d a b : ℕ} (hab : a % d = b % d) : d ∣ F a ↔ d ∣ F b := by
  have hcong : F a ≡ F b [MOD d] := by
    unfold F
    have hterm : ∀ q : ℕ, q * a + 1 ≡ q * b + 1 [MOD d] := fun q =>
      ((Nat.ModEq.refl q).mul hab).add_right 1
    generalize P = S
    induction S using Finset.induction_on with
    | empty => simp [Nat.ModEq.refl]
    | @insert q s hq ih =>
      rw [Finset.prod_insert hq, Finset.prod_insert hq]
      exact (hterm q).mul ih
  exact Nat.ModEq.dvd_iff hcong dvd_rfl

private lemma card_roots_mod_squarefree {d : ℕ} (hd : Squarefree d) :
    ((Finset.range d).filter (fun a => d ∣ F a)).card = omegaD d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd1 : d = 1
    · subst hd1
      simp [omegaD_one]
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
    have hd_gt1 : 1 < d := by omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd_gt1.ne'
    obtain ⟨m, rfl⟩ := hpd
    have hcop : Nat.Coprime p m := by
      rw [hp.coprime_iff_not_dvd]
      intro hpm
      exact hp.not_isUnit (hd p ⟨m / p, by
        have := Nat.mul_div_cancel' hpm
        nlinarith⟩)
    have hm_sf : Squarefree m := hd.squarefree_of_dvd (dvd_mul_left m p)
    have hm_lt : m < p * m := by
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_sf.ne_zero
      nlinarith [hp.one_lt]
    rw [omegaD_mul_of_coprime hcop, omegaD_prime hp, ← ih m hm_lt hm_sf]
    -- Bijection via CRT between range (p * m) and range p × range m
    let Sp := (Finset.range p).filter (fun a => p ∣ F a)
    let Sm := (Finset.range m).filter (fun a => m ∣ F a)
    let Spm := (Finset.range (p * m)).filter (fun a => p * m ∣ F a)
    change Spm.card = Sp.card * Sm.card
    rw [← Finset.card_product]
    apply Finset.card_bij (fun a _ => (a % p, a % m))
    · intro a ha
      rw [Finset.mem_filter, Finset.mem_range] at ha
      rw [Finset.mem_product]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt a hp.pos), ?_⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt a (Nat.pos_of_ne_zero hm_sf.ne_zero)), ?_⟩⟩
      · exact (F_mod_dvd_iff (Nat.mod_mod a p)).mpr ((dvd_mul_right p m).trans ha.2)
      · exact (F_mod_dvd_iff (Nat.mod_mod a m)).mpr ((dvd_mul_left m p).trans ha.2)
    · intro a ha b hb hpair
      rw [Prod.mk.injEq] at hpair
      rw [Finset.mem_filter, Finset.mem_range] at ha hb
      have hmod : a ≡ b [MOD p * m] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hpair.1, hpair.2⟩
      rw [Nat.ModEq, Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at hmod
      exact hmod
    · intro ⟨x, y⟩ hxy
      rw [Finset.mem_product] at hxy
      obtain ⟨hx, hy⟩ := hxy
      rw [Finset.mem_filter, Finset.mem_range] at hx hy
      let crt := Nat.chineseRemainder hcop x y
      let a := crt.val % (p * m)
      have ha_lt : a < p * m := Nat.mod_lt _ (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hm_sf.ne_zero))
      have hap : a % p = x := by
        have h1 : a ≡ crt.val [MOD p] := (Nat.mod_modEq crt.val (p * m)).of_dvd (dvd_mul_right p m)
        have h2 : crt.val ≡ x [MOD p] := crt.property.1
        have h3 : a ≡ x [MOD p] := h1.trans h2
        rwa [Nat.ModEq, Nat.mod_eq_of_lt hx.1] at h3
      have ham : a % m = y := by
        have h1 : a ≡ crt.val [MOD m] := (Nat.mod_modEq crt.val (p * m)).of_dvd (dvd_mul_left m p)
        have h2 : crt.val ≡ y [MOD m] := crt.property.2
        have h3 : a ≡ y [MOD m] := h1.trans h2
        rwa [Nat.ModEq, Nat.mod_eq_of_lt hy.1] at h3
      refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ?_⟩, Prod.ext hap ham⟩
      have hdp : p ∣ F a := (F_mod_dvd_iff (by rw [hap, Nat.mod_eq_of_lt hx.1])).mpr hx.2
      have hdm : m ∣ F a := (F_mod_dvd_iff (by rw [ham, Nat.mod_eq_of_lt hy.1])).mpr hy.2
      exact hcop.mul_dvd_of_dvd_of_dvd hdp hdm

private lemma count_mod_Ioc_bound (X d a : ℕ) (hd : 0 < d) (ha : a < d) :
    |(((Finset.Ioc X (2 * X)).filter (fun n => n % d = a)).card : ℝ) - (X : ℝ) / (d : ℝ)| ≤ 1 := by
  let q := X / d
  let r := X % d
  have hX : X = q * d + r := (Nat.div_add_mod' X d).symm
  have hr : r < d := Nat.mod_lt X hd
  -- Split Ioc X (2X) into Ioc X (X + q * d) and Ioc (X + q * d) (2 * X)
  let I1 := Finset.Ioc X (X + q * d)
  let I2 := Finset.Ioc (X + q * d) (2 * X)
  have hdisj : Disjoint I1 I2 := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    rw [Finset.mem_Ioc] at hn1 hn2
    omega
  have hunion : Finset.Ioc X (2 * X) = I1 ∪ I2 := by
    ext n
    simp only [I1, I2, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hcard1 : (I1.filter (fun n => n % d = a)).card = q := by
    have hbij : (I1.filter (fun n => n % d = a)).card = (Finset.range q).card := by
      apply Finset.card_bij (fun n _ => (n - (X + 1)) / d)
      · intro n hn
        rw [Finset.mem_filter, Finset.mem_Ioc] at hn
        rw [Finset.mem_range]
        have hlt : n - (X + 1) < d * q := by
          have : n ≤ X + q * d := hn.1.2
          have : q * d = d * q := mul_comm q d
          omega
        exact Nat.div_lt_of_lt_mul hlt
      · intro n1 hn1 n2 hn2 heq
        rw [Finset.mem_filter, Finset.mem_Ioc] at hn1 hn2
        have h1 := Nat.div_add_mod (n1 - (X + 1)) d
        have h2 := Nat.div_add_mod (n2 - (X + 1)) d
        have hmod_eq : (n1 - (X + 1)) % d = (n2 - (X + 1)) % d := by
          have hc : n1 ≡ n2 [MOD d] := hn1.2.trans hn2.2.symm
          have hsub1 : (n1 - (X + 1)) + (X + 1) = n1 := by omega
          have hsub2 : (n2 - (X + 1)) + (X + 1) = n2 := by omega
          exact Nat.ModEq.add_right_cancel' (X + 1) (by rwa [hsub1, hsub2])
        have hsub_eq : n1 - (X + 1) = n2 - (X + 1) := by
          calc n1 - (X + 1) = d * ((n1 - (X + 1)) / d) + (n1 - (X + 1)) % d := h1.symm
            _ = d * ((n2 - (X + 1)) / d) + (n2 - (X + 1)) % d := by rw [heq, hmod_eq]
            _ = n2 - (X + 1) := h2
        omega
      · intro k hk
        rw [Finset.mem_range] at hk
        let base := X + 1 + k * d
        let step := (a + d - base % d) % d
        let n := base + step
        have hstep_lt : step < d := Nat.mod_lt _ hd
        have hn_mod : n % d = a := by
          have hb : base % d < d := Nat.mod_lt _ hd
          have hadd : base % d + (a + d - base % d) = a + d := by omega
          calc n % d = (base % d + step % d) % d := Nat.add_mod base step d
            _ = (base % d + (a + d - base % d) % d) % d := by rw [Nat.mod_mod]
            _ = (base % d + (a + d - base % d)) % d := by rw [Nat.add_mod_mod]
            _ = (a + d) % d := by rw [hadd]
            _ = a := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt ha]
        have hn_mem : n ∈ I1.filter (fun m => m % d = a) := by
          rw [Finset.mem_filter, Finset.mem_Ioc]
          refine ⟨⟨by omega, ?_⟩, hn_mod⟩
          have hk1 : k + 1 ≤ q := hk
          have hmul_le : (k + 1) * d ≤ q * d := Nat.mul_le_mul_right d hk1
          have hkd : k * d + step < (k + 1) * d := by nlinarith
          change X + 1 + k * d + step ≤ X + q * d
          omega
        refine ⟨n, hn_mem, ?_⟩
        have hsub : n - (X + 1) = d * k + step := by
          change (X + 1 + k * d + step) - (X + 1) = d * k + step
          have : k * d = d * k := mul_comm k d
          omega
        rw [hsub, Nat.mul_add_div hd, Nat.div_eq_of_lt hstep_lt, add_zero]
    simpa using hbij
  have hcard2 : (I2.filter (fun n => n % d = a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro n1 hn1 n2 hn2
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn1 hn2
    have hdiff : n1 < X + q * d + d ∧ n2 < X + q * d + d := by omega
    have hmod : n1 ≡ n2 [MOD d] := hn1.2.trans hn2.2.symm
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hdvd : d ∣ n2 - n1 := (Nat.modEq_iff_dvd' hlt.le).mp hmod
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd
      omega
    · have hdvd : d ∣ n1 - n2 := (Nat.modEq_iff_dvd' hgt.le).mp hmod.symm
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) hdvd
      omega
  have htot : ((Finset.Ioc X (2 * X)).filter (fun n => n % d = a)).card =
      q + (I2.filter (fun n => n % d = a)).card := by
    rw [hunion, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), hcard1]
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hq_le : (q : ℝ) ≤ (X : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd_pos]
    have : q * d ≤ X := by omega
    exact_mod_cast this
  have hq_gt : (X : ℝ) / (d : ℝ) < (q : ℝ) + 1 := by
    rw [div_lt_iff₀ hd_pos]
    have : X < (q + 1) * d := by nlinarith
    exact_mod_cast this
  have hc2 : ((I2.filter (fun n => n % d = a)).card : ℝ) ≤ 1 := by exact_mod_cast hcard2
  have hc2_nn : (0 : ℝ) ≤ ((I2.filter (fun n => n % d = a)).card : ℝ) := Nat.cast_nonneg _
  rw [htot, Nat.cast_add, abs_le]
  constructor <;> linarith

private lemma count_dvd_F_Ioc (X d : ℕ) (hd : Squarefree d) :
    |(((Finset.Ioc X (2 * X)).filter (fun n => d ∣ F n)).card : ℝ) -
      (X : ℝ) * ((omegaD d : ℝ) / (d : ℝ))| ≤ (omegaD d : ℝ) := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  let Rset := (Finset.range d).filter (fun a => d ∣ F a)
  have hRcard : Rset.card = omegaD d := card_roots_mod_squarefree hd
  have hpart : ((Finset.Ioc X (2 * X)).filter (fun n => d ∣ F n)).card =
      ∑ a ∈ Rset, ((Finset.Ioc X (2 * X)).filter (fun n => n % d = a)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_biUnion, Rset, Finset.mem_range]
      constructor
      · rintro ⟨hn, hdn⟩
        exact ⟨n % d, ⟨Nat.mod_lt n hd_pos, (F_mod_dvd_iff (Nat.mod_mod n d)).mpr hdn⟩, hn, rfl⟩
      · rintro ⟨a, ⟨ha_lt, hda⟩, hn, hmod⟩
        exact ⟨hn, (F_mod_dvd_iff (hmod.trans (Nat.mod_eq_of_lt ha_lt).symm)).mpr hda⟩
    · intro a _ b _ hab
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro n hna hnb
      rw [Finset.mem_filter] at hna hnb
      exact hab (hna.2.symm.trans hnb.2)
  rw [hpart, Nat.cast_sum]
  have hmain : (X : ℝ) * ((omegaD d : ℝ) / (d : ℝ)) = ∑ _a ∈ Rset, (X : ℝ) / (d : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, hRcard]
    ring
  rw [hmain, ← Finset.sum_sub_distrib]
  calc |∑ a ∈ Rset, ((((Finset.Ioc X (2 * X)).filter (fun n => n % d = a)).card : ℝ) -
          (X : ℝ) / (d : ℝ))|
      ≤ ∑ a ∈ Rset, |(((Finset.Ioc X (2 * X)).filter (fun n => n % d = a)).card : ℝ) -
          (X : ℝ) / (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Rset, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact count_mod_Ioc_bound X d a hd_pos (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
    _ = (omegaD d : ℝ) := by simp [hRcard]

/- Section 2: Selberg Weights and Exact Diagonalization -/

private def gF (d : ℕ) : ℝ := (omegaD d : ℝ) / (d : ℝ)

private def phiG (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, (((p : ℝ) - (omegaP p : ℝ)) / (omegaP p : ℝ))

private lemma gF_one : gF 1 = 1 := by simp [gF, omegaD_one]

private lemma phiG_one : phiG 1 = 1 := by simp [phiG]

private lemma gF_prime {p : ℕ} (hp : p.Prime) : gF p = (omegaP p : ℝ) / (p : ℝ) := by
  simp [gF, omegaD_prime hp]

private lemma phiG_prime {p : ℕ} (hp : p.Prime) :
    phiG p = ((p : ℝ) - (omegaP p : ℝ)) / (omegaP p : ℝ) := by
  simp [phiG, hp.primeFactors]

private lemma gF_pos {d : ℕ} (hd : 0 < d) : 0 < gF d :=
  div_pos (Nat.cast_pos.mpr (omegaD_pos d)) (Nat.cast_pos.mpr hd)

private lemma phiG_pos (d : ℕ) : 0 < phiG d := by
  unfold phiG
  apply Finset.prod_pos
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hlt : (omegaP p : ℝ) < (p : ℝ) := Nat.cast_lt.mpr (omegaP_lt_self hprime)
  have hpos : (0 : ℝ) < (omegaP p : ℝ) := Nat.cast_pos.mpr (omegaP_pos hprime)
  exact div_pos (sub_pos.mpr hlt) hpos

private lemma gF_mul_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    gF (a * b) = gF a * gF b := by
  unfold gF
  rw [omegaD_mul_of_coprime hab, Nat.cast_mul, Nat.cast_mul]
  ring

private lemma phiG_mul_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    phiG (a * b) = phiG a * phiG b := by
  unfold phiG
  rw [hab.primeFactors_mul, Finset.prod_union hab.disjoint_primeFactors]

private lemma inv_gF_prime_eq {p : ℕ} (hp : p.Prime) :
    1 / gF p = 1 + phiG p := by
  rw [gF_prime hp, phiG_prime hp]
  have hom : (omegaP p : ℝ) ≠ 0 := (Nat.cast_pos.mpr (omegaP_pos hp)).ne'
  have hp0 : (p : ℝ) ≠ 0 := (Nat.cast_pos.mpr hp.pos).ne'
  field_simp
  ring

private lemma inv_gF_eq_sum_phiG {a : ℕ} (ha : Squarefree a) :
    1 / gF a = ∑ r ∈ a.divisors, phiG r := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    by_cases ha1 : a = 1
    · subst ha1; simp [gF_one, phiG_one]
    have ha_pos : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
    obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
    obtain ⟨m, rfl⟩ := hpa
    have hcop : Nat.Coprime p m := by
      rw [hp.coprime_iff_not_dvd]
      intro hpm
      exact hp.not_isUnit (ha p ⟨m / p, by have := Nat.mul_div_cancel' hpm; nlinarith⟩)
    have hm_sf : Squarefree m := ha.squarefree_of_dvd (dvd_mul_left m p)
    have hm_lt : m < p * m := by
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_sf.ne_zero
      nlinarith [hp.one_lt]
    rw [gF_mul_coprime hcop, ← one_div_mul_one_div, inv_gF_prime_eq hp, ih m hm_lt hm_sf]
    have hdiv_eq : ∑ r ∈ (p * m).divisors, phiG r =
        (∑ x ∈ p.divisors, phiG x) * (∑ y ∈ m.divisors, phiG y) := by
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      symm
      apply Finset.sum_bij (fun xy _ => xy.1 * xy.2)
      · intro xy hxy
        rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hxy
        rw [Nat.mem_divisors]
        exact ⟨mul_dvd_mul hxy.1.1 hxy.2.1, mul_ne_zero hxy.1.2 hxy.2.2⟩
      · intro xy1 hxy1 xy2 hxy2 heq
        rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hxy1 hxy2
        have hc1 : Nat.Coprime xy1.1 xy2.2 := (hcop.coprime_dvd_left hxy1.1.1).coprime_dvd_right hxy2.2.1
        have hc2 : Nat.Coprime xy2.1 xy1.2 := (hcop.coprime_dvd_left hxy2.1.1).coprime_dvd_right hxy1.2.1
        have h1d2 : xy1.1 ∣ xy2.1 := hc1.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right xy1.1 xy1.2)
        have h2d1 : xy2.1 ∣ xy1.1 := hc2.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right xy2.1 xy2.2)
        have hx : xy1.1 = xy2.1 := Nat.dvd_antisymm h1d2 h2d1
        have hpos : 0 < xy1.1 := Nat.pos_of_dvd_of_pos hxy1.1.1 hp.pos
        have hy : xy1.2 = xy2.2 := Nat.eq_of_mul_eq_mul_left hpos (hx ▸ heq)
        exact Prod.ext hx hy
      · intro r hr
        rw [Nat.mem_divisors] at hr
        by_cases hpr : p ∣ r
        · have hrm : r / p ∣ m := by
            obtain ⟨c, hc⟩ := hpr
            have hpm_dvd : p * c ∣ p * m := hc ▸ hr.1
            have hcm : c ∣ m := (mul_dvd_mul_iff_left hp.ne_zero).mp hpm_dvd
            rwa [hc, Nat.mul_div_cancel_left c hp.pos]
          refine ⟨(p, r / p), Finset.mem_product.mpr
            ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, hp.ne_zero⟩,
             Nat.mem_divisors.mpr ⟨hrm, hm_sf.ne_zero⟩⟩, Nat.mul_div_cancel' hpr⟩
        · have hrm : r ∣ m := (hp.coprime_iff_not_dvd.mpr hpr).symm.dvd_of_dvd_mul_left hr.1
          refine ⟨(1, r), Finset.mem_product.mpr
            ⟨Nat.mem_divisors.mpr ⟨one_dvd p, hp.ne_zero⟩,
             Nat.mem_divisors.mpr ⟨hrm, hm_sf.ne_zero⟩⟩, one_mul r⟩
      · intro xy hxy
        rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hxy
        exact (phiG_mul_coprime ((hcop.coprime_dvd_left hxy.1.1).coprime_dvd_right hxy.2.1)).symm
    rw [hdiv_eq, hp.divisors, Finset.sum_pair hp.ne_one.symm, phiG_one]

private lemma gF_lcm_eq {d1 d2 : ℕ} (h1 : Squarefree d1) (h2 : Squarefree d2) :
    gF (Nat.lcm d1 d2) = gF d1 * gF d2 * ∑ r ∈ (Nat.gcd d1 d2).divisors, phiG r := by
  have hd1_pos : 0 < d1 := Nat.pos_of_ne_zero h1.ne_zero
  have hd2_pos : 0 < d2 := Nat.pos_of_ne_zero h2.ne_zero
  let g := Nat.gcd d1 d2
  have hg_sf : Squarefree g := h1.squarefree_of_dvd (Nat.gcd_dvd_left d1 d2)
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d2 hd1_pos
  have h1' : d1 = g * (d1 / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left d1 d2)).symm
  have h2' : d2 = g * (d2 / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right d1 d2)).symm
  have hcop1 : Nat.Coprime g (d1 / g) := by
    apply Nat.coprime_of_dvd
    intro p hp hpg hpd
    have hp2 : p * p ∣ d1 := by
      rw [h1']; exact mul_dvd_mul hpg hpd
    exact hp.not_isUnit (h1 p hp2)
  have hcop2 : Nat.Coprime g (d2 / g) := by
    apply Nat.coprime_of_dvd
    intro p hp hpg hpd
    have hp2 : p * p ∣ d2 := by
      rw [h2']; exact mul_dvd_mul hpg hpd
    exact hp.not_isUnit (h2 p hp2)
  have hcop12 : Nat.Coprime (d1 / g) (d2 / g) := Nat.coprime_div_gcd_div_gcd hg_pos
  have hlcm : Nat.lcm d1 d2 = g * ((d1 / g) * (d2 / g)) := by
    have hmul : Nat.gcd d1 d2 * Nat.lcm d1 d2 = d1 * d2 := Nat.gcd_mul_lcm d1 d2
    have heq : g * Nat.lcm d1 d2 = g * (g * ((d1 / g) * (d2 / g))) := by
      calc g * Nat.lcm d1 d2 = d1 * d2 := hmul
        _ = (g * (d1 / g)) * (g * (d2 / g)) := by rw [← h1', ← h2']
        _ = g * (g * ((d1 / g) * (d2 / g))) := by ring
    exact Nat.eq_of_mul_eq_mul_left hg_pos heq
  rw [hlcm, gF_mul_coprime (hcop1.mul_right hcop2), gF_mul_coprime hcop12]
  have hsum_g : ∑ r ∈ (Nat.gcd d1 d2).divisors, phiG r = 1 / gF g := (inv_gF_eq_sum_phiG hg_sf).symm
  rw [hsum_g]
  conv_rhs => rw [h1', h2', gF_mul_coprime hcop1, gF_mul_coprime hcop2]
  have hgp : gF g ≠ 0 := (gF_pos hg_pos).ne'
  field_simp

/-- Squarefree integers in `[1, R]`. -/
private def sfLE (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter Squarefree

private def zW (R r : ℕ) : ℝ :=
  if Squarefree r ∧ r ≤ R ∧ 1 ≤ r then
    ((ArithmeticFunction.moebius r : ℤ) : ℝ) * (1 - Real.log (r : ℝ) / Real.log (R : ℝ))
  else 0

private def yW (R r : ℕ) : ℝ :=
  zW R r / phiG r

private def lam (R d : ℕ) : ℝ :=
  if Squarefree d ∧ d ≤ R ∧ 1 ≤ d then
    (1 / gF d) * ∑ r ∈ (sfLE R).filter (fun r => d ∣ r),
      ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) * yW R r
  else 0

private def selbergW (R n : ℕ) : ℝ :=
  (∑ d ∈ (sfLE R).filter (fun d => d ∣ F n), lam R d) ^ 2

private lemma lam_inversion (R r : ℕ) (hr : r ∈ sfLE R) :
    ∑ d ∈ (sfLE R).filter (fun d => r ∣ d), lam R d * gF d = yW R r := by
  have hr_sf : Squarefree r := (Finset.mem_filter.mp hr).2
  have hr_bounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
  have hinner : ∀ d ∈ (sfLE R).filter (fun d => r ∣ d),
      lam R d * gF d = ∑ m ∈ (sfLE R).filter (fun m => d ∣ m),
        ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * yW R m := by
    intro d hd
    have hd_mem := (Finset.mem_filter.mp hd).1
    have hd_sf := (Finset.mem_filter.mp hd_mem).2
    have hd_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd_mem).1
    have hgne : gF d ≠ 0 := (gF_pos (by omega)).ne'
    simp only [lam, hd_sf, hd_Icc.1, hd_Icc.2, and_self, ↓reduceIte]
    field_simp
  rw [Finset.sum_congr rfl hinner]
  -- Swap sums over d and m
  have hswap : ∑ d ∈ (sfLE R).filter (fun d => r ∣ d),
      ∑ m ∈ (sfLE R).filter (fun m => d ∣ m),
        ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * yW R m =
      ∑ m ∈ (sfLE R).filter (fun m => r ∣ m),
        (∑ d ∈ (m / r).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) * yW R m := by
    trans ∑ d ∈ sfLE R, ∑ m ∈ sfLE R,
      if r ∣ d ∧ d ∣ m then ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * yW R m else 0
    · rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hrd : r ∣ d
      · simp [hrd, Finset.sum_filter]
      · simp [hrd]
    · rw [Finset.sum_comm]
      trans ∑ m ∈ (sfLE R).filter (fun m => r ∣ m),
        ∑ d ∈ (sfLE R).filter (fun d => r ∣ d ∧ d ∣ m),
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * yW R m
      · rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun m _ => ?_
        by_cases hrm : r ∣ m
        · simp [hrm, Finset.sum_filter]
        · rw [if_neg hrm]
          refine Finset.sum_eq_zero fun d _ => ?_
          rw [if_neg]
          rintro ⟨h1, h2⟩
          exact hrm (h1.trans h2)
      · refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.sum_mul]
        have hm_mem := (Finset.mem_filter.mp hm).1
        have hrm : r ∣ m := (Finset.mem_filter.mp hm).2
        have hm_sf : Squarefree m := (Finset.mem_filter.mp hm_mem).2
        have hm_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hm_mem).1
        apply Finset.sum_bij (fun d _ => m / d)
        · intro d hd
          have hdm : d ∣ m := (Finset.mem_filter.mp hd).2.2
          have hrd : r ∣ d := (Finset.mem_filter.mp hd).2.1
          have hm_pos : 0 < m := by omega
          have hr_pos : 0 < r := by omega
          rw [Nat.mem_divisors]
          refine ⟨?_, (Nat.div_pos (Nat.le_of_dvd hm_pos hrm) hr_pos).ne'⟩
          obtain ⟨a, rfl⟩ := hrd
          obtain ⟨b, hb⟩ := hdm
          have ha_pos : 0 < a := by
            by_contra ha0; simp at ha0; subst ha0; simp at hb; omega
          have hmd : m / (r * a) = b := by
            rw [hb, Nat.mul_div_cancel_left b (Nat.mul_pos hr_pos ha_pos)]
          have hmr : m / r = a * b := by
            rw [hb, mul_assoc, Nat.mul_div_cancel_left (a * b) hr_pos]
          rw [hmd, hmr]
          exact dvd_mul_left b a
        · intro d1 hd1 d2 hd2 heq
          have hd1m := (Finset.mem_filter.mp hd1).2.2
          have hd2m := (Finset.mem_filter.mp hd2).2.2
          have hm_pos : 0 < m := by omega
          have hq1 : d1 * (m / d1) = m := Nat.mul_div_cancel' hd1m
          have hq2 : d2 * (m / d2) = m := Nat.mul_div_cancel' hd2m
          have hpos : 0 < m / d1 := Nat.div_pos (Nat.le_of_dvd hm_pos hd1m)
            (Nat.pos_of_dvd_of_pos hd1m hm_pos)
          rw [heq] at hq1
          exact Nat.eq_of_mul_eq_mul_right (heq ▸ hpos) (hq1.trans hq2.symm)
        · intro k hk
          rw [Nat.mem_divisors] at hk
          have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos hk.1 (Nat.pos_of_ne_zero hk.2)
          have hkm : k ∣ m := hk.1.trans (Nat.div_dvd_of_dvd hrm)
          refine ⟨m / k, ?_, Nat.div_div_self hkm (by omega)⟩
          rw [Finset.mem_filter]
          have hmk_dvd : m / k ∣ m := Nat.div_dvd_of_dvd hkm
          have hmk_pos : 0 < m / k := Nat.div_pos (Nat.le_of_dvd (by omega) hkm) hk_pos
          have hmk_le : m / k ≤ R := (Nat.div_le_self m k).trans hm_Icc.2
          have hr_dvd_mk : r ∣ m / k := by
            obtain ⟨c, hc⟩ := hk.1
            refine ⟨c, ?_⟩
            have h1 : r * (m / r) = m := Nat.mul_div_cancel' hrm
            have h2 : k * (m / k) = m := Nat.mul_div_cancel' hkm
            have : k * (r * c) = k * (m / k) := by
              calc k * (r * c) = r * (k * c) := by ring
                _ = r * (m / r) := by rw [← hc]
                _ = m := h1
                _ = k * (m / k) := h2.symm
            exact (Nat.eq_of_mul_eq_mul_left hk_pos this).symm
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmk_pos, hmk_le⟩,
            hm_sf.squarefree_of_dvd hmk_dvd⟩, hr_dvd_mk, hmk_dvd⟩
        · intro _ _; rfl
  rw [hswap]
  -- Only m = r survives since ∑_{d ∣ m/r} μ(d) = [m/r = 1]
  rw [Finset.sum_eq_single r]
  · have hrr : r / r = 1 := Nat.div_self (by omega)
    simp [hrr]
  · intro m hm hmr
    have hrm : r ∣ m := (Finset.mem_filter.mp hm).2
    have hm_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1
    have hne1 : m / r ≠ 1 := by
      intro h1
      have := Nat.mul_div_cancel' hrm
      rw [h1, mul_one] at this
      exact hmr this.symm
    have hmu0 : ∑ d ∈ (m / r).divisors, (ArithmeticFunction.moebius d : ℤ) = 0 := by
      have h1 : (ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) (m / r) =
          ∑ d ∈ (m / r).divisors, (ArithmeticFunction.moebius d : ℤ) := by
        simpa using ArithmeticFunction.coe_mul_zeta_apply (f := ArithmeticFunction.moebius) (x := m / r)
      rw [← h1, ArithmeticFunction.moebius_mul_coe_zeta]
      simp [hne1]
    have hmu0R : ∑ d ∈ (m / r).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) = 0 := by
      exact_mod_cast hmu0
    rw [hmu0R, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_filter.mpr ⟨hr, dvd_rfl⟩) hnot

private lemma selberg_diag_main (R : ℕ) :
    ∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R, lam R d1 * lam R d2 * gF (Nat.lcm d1 d2) =
      ∑ r ∈ sfLE R, (zW R r) ^ 2 / phiG r := by
  have h1 : ∀ d1 ∈ sfLE R, ∀ d2 ∈ sfLE R,
      lam R d1 * lam R d2 * gF (Nat.lcm d1 d2) =
      ∑ r ∈ sfLE R, if r ∣ d1 ∧ r ∣ d2 then phiG r * (lam R d1 * gF d1) * (lam R d2 * gF d2) else 0 := by
    intro d1 hd1 d2 hd2
    have hsf1 := (Finset.mem_filter.mp hd1).2
    have hsf2 := (Finset.mem_filter.mp hd2).2
    rw [gF_lcm_eq hsf1 hsf2]
    rw [Finset.mul_sum]
    have hsub : (Nat.gcd d1 d2).divisors = (sfLE R).filter (fun r => r ∣ d1 ∧ r ∣ d2) := by
      ext r
      simp only [Nat.mem_divisors, Finset.mem_filter, sfLE, Finset.mem_Icc]
      have hd1_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd1).1
      have hg_pos : 0 < Nat.gcd d1 d2 := Nat.gcd_pos_of_pos_left d2 (by omega)
      constructor
      · rintro ⟨hrg, _⟩
        have hr1 := hrg.trans (Nat.gcd_dvd_left d1 d2)
        have hr2 := hrg.trans (Nat.gcd_dvd_right d1 d2)
        exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hr1 (by omega),
          (Nat.le_of_dvd (by omega) hr1).trans hd1_Icc.2⟩,
          hsf1.squarefree_of_dvd hr1⟩, hr1, hr2⟩
      · rintro ⟨_, hr1, hr2⟩
        exact ⟨Nat.dvd_gcd hr1 hr2, hg_pos.ne'⟩
    rw [hsub, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> ring
  calc ∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R, lam R d1 * lam R d2 * gF (Nat.lcm d1 d2)
      = ∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R,
          ∑ r ∈ sfLE R, if r ∣ d1 ∧ r ∣ d2 then phiG r * (lam R d1 * gF d1) * (lam R d2 * gF d2) else 0 := by
        refine Finset.sum_congr rfl fun d1 hd1 => Finset.sum_congr rfl fun d2 hd2 => h1 d1 hd1 d2 hd2
    _ = ∑ d1 ∈ sfLE R, ∑ r ∈ sfLE R, ∑ d2 ∈ sfLE R,
          if r ∣ d1 ∧ r ∣ d2 then phiG r * (lam R d1 * gF d1) * (lam R d2 * gF d2) else 0 := by
        refine Finset.sum_congr rfl fun d1 _ => Finset.sum_comm
    _ = ∑ r ∈ sfLE R, ∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R,
          if r ∣ d1 ∧ r ∣ d2 then phiG r * (lam R d1 * gF d1) * (lam R d2 * gF d2) else 0 :=
        Finset.sum_comm
    _ = ∑ r ∈ sfLE R, phiG r * (∑ d ∈ (sfLE R).filter (fun d => r ∣ d), lam R d * gF d) ^ 2 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [sq, Finset.sum_mul, Finset.mul_sum]
        trans ∑ d1 ∈ (sfLE R).filter (fun d => r ∣ d),
            ∑ d2 ∈ (sfLE R).filter (fun d => r ∣ d),
              phiG r * (lam R d1 * gF d1) * (lam R d2 * gF d2)
        · rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun d1 _ => ?_
          by_cases h1r : r ∣ d1
          · simp [h1r, Finset.sum_filter]
          · simp [h1r]
        · refine Finset.sum_congr rfl fun d1 _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d2 _ => by ring
    _ = ∑ r ∈ sfLE R, (zW R r) ^ 2 / phiG r := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [lam_inversion R r hr, yW]
        have hph : phiG r ≠ 0 := (phiG_pos r).ne'
        field_simp

private lemma selberg_diag_prime (R p : ℕ) (hp : p.Prime) :
    ∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R, lam R d1 * lam R d2 * gF (Nat.lcm p (Nat.lcm d1 d2)) =
      gF p * ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r := by
  let S0 := (sfLE R).filter (fun d => ¬ p ∣ d)
  let lam' (d : ℕ) : ℝ := lam R d + lam R (p * d)
  -- Collapse sum over d1, d2 ∈ sfLE R to d1', d2' ∈ S0
  have hcollapse : ∀ f : ℕ → ℝ,
      (∀ d, Squarefree d → ¬ p ∣ d → f (p * d) = f d) →
      ∑ d ∈ sfLE R, lam R d * f d = ∑ d ∈ S0, lam' d * f d := by
    intro f hf
    have hsplit := (Finset.sum_filter_add_sum_filter_not (sfLE R) (fun d => ¬ p ∣ d)
      (fun d => lam R d * f d)).symm
    rw [hsplit]
    have hsecond : ∑ d ∈ (sfLE R).filter (fun d => ¬ ¬ p ∣ d), lam R d * f d =
        ∑ d ∈ S0, lam R (p * d) * f d := by
      have hbi : ∑ d ∈ (sfLE R).filter (fun d => p ∣ d), lam R d * f d =
          ∑ d ∈ S0.filter (fun d => p * d ≤ R), lam R (p * d) * f d := by
        apply Finset.sum_bij (fun d _ => d / p)
        · intro d hd
          obtain ⟨hd_sfLE, hpd⟩ := Finset.mem_filter.mp hd
          have hd_sf := (Finset.mem_filter.mp hd_sfLE).2
          have hd_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd_sfLE).1
          have hdp_pos : 0 < d / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpd) hp.pos
          have hdp_le : d / p ≤ R := (Nat.div_le_self d p).trans hd_Icc.2
          have hndvd : ¬ p ∣ d / p := by
            intro hpp
            have : p * p ∣ d := by
              rw [← Nat.mul_div_cancel' hpd]; exact mul_dvd_mul_left p hpp
            exact hp.not_isUnit (hd_sf p this)
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdp_pos, hdp_le⟩,
              hd_sf.squarefree_of_dvd (Nat.div_dvd_of_dvd hpd)⟩, hndvd⟩, ?_⟩
          rw [Nat.mul_div_cancel' hpd]; exact hd_Icc.2
        · intro d1 hd1 d2 hd2 heq
          have h1 := (Finset.mem_filter.mp hd1).2
          have h2 := (Finset.mem_filter.mp hd2).2
          rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
        · intro d hd
          obtain ⟨hdS0, hpdR⟩ := Finset.mem_filter.mp hd
          obtain ⟨hd_sfLE, hndvd⟩ := Finset.mem_filter.mp hdS0
          have hd_sf := (Finset.mem_filter.mp hd_sfLE).2
          have hd_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd_sfLE).1
          have hcop : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hndvd
          have hpd_sf : Squarefree (p * d) :=
            (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hd_sf⟩
          refine ⟨p * d, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hp.pos hd_Icc.1, hpdR⟩, hpd_sf⟩, dvd_mul_right p d⟩,
            Nat.mul_div_cancel_left d hp.pos⟩
        · intro d hd
          obtain ⟨hd_sfLE, hpd⟩ := Finset.mem_filter.mp hd
          have hd_sf := (Finset.mem_filter.mp hd_sfLE).2
          have hndvd : ¬ p ∣ d / p := by
            intro hpp
            have : p * p ∣ d := by
              rw [← Nat.mul_div_cancel' hpd]; exact mul_dvd_mul_left p hpp
            exact hp.not_isUnit (hd_sf p this)
          rw [Nat.mul_div_cancel' hpd]
          congr 1
          have := hf (d / p) (hd_sf.squarefree_of_dvd (Nat.div_dvd_of_dvd hpd)) hndvd
          rwa [Nat.mul_div_cancel' hpd] at this
      have hsimp : (sfLE R).filter (fun d => ¬ ¬ p ∣ d) = (sfLE R).filter (fun d => p ∣ d) := by
        ext d; simp
      rw [hsimp, hbi]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hnot
      rw [Finset.mem_filter] at hnot
      have hgt : ¬ p * d ≤ R := fun hle => hnot ⟨hd, hle⟩
      simp [lam, hgt]
    rw [hsecond, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => by dsimp [lam']; ring
  -- Apply hcollapse to d1 and d2
  have hlcm_p : ∀ a b : ℕ, Squarefree a → ¬ p ∣ a →
      Nat.lcm p (Nat.lcm (p * a) b) = Nat.lcm p (Nat.lcm a b) := by
    intro a b _ _
    rw [← Nat.lcm_assoc, ← Nat.lcm_assoc]
    congr 1
    rw [Nat.lcm_eq_right (dvd_mul_right p a)]
    -- wait: lcm p (p * a) = p * a = lcm p a only when p ∤ a
    have hcop : Nat.Coprime p a := hp.coprime_iff_not_dvd.mpr ‹¬ p ∣ a›
    rw [hcop.lcm_eq_mul]
  have hstep1 : ∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R, lam R d1 * lam R d2 * gF (Nat.lcm p (Nat.lcm d1 d2)) =
      ∑ d1 ∈ S0, ∑ d2 ∈ S0, lam' d1 * lam' d2 * gF (Nat.lcm p (Nat.lcm d1 d2)) := by
    calc ∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R, lam R d1 * lam R d2 * gF (Nat.lcm p (Nat.lcm d1 d2))
        = ∑ d1 ∈ sfLE R, lam R d1 * (∑ d2 ∈ sfLE R, lam R d2 * gF (Nat.lcm p (Nat.lcm d1 d2))) := by
          refine Finset.sum_congr rfl fun d1 _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d2 _ => by ring
      _ = ∑ d1 ∈ S0, lam' d1 * (∑ d2 ∈ sfLE R, lam R d2 * gF (Nat.lcm p (Nat.lcm d1 d2))) := by
          apply hcollapse
          intro d1 hsf1 hnd1
          refine Finset.sum_congr rfl fun d2 _ => ?_
          rw [hlcm_p d1 d2 hsf1 hnd1]
      _ = ∑ d1 ∈ S0, lam' d1 * (∑ d2 ∈ S0, lam' d2 * gF (Nat.lcm p (Nat.lcm d1 d2))) := by
          refine Finset.sum_congr rfl fun d1 _ => ?_
          congr 1
          apply hcollapse
          intro d2 hsf2 hnd2
          rw [Nat.lcm_comm d1 (p * d2), hlcm_p d2 d1 hsf2 hnd2, Nat.lcm_comm d2 d1]
      _ = ∑ d1 ∈ S0, ∑ d2 ∈ S0, lam' d1 * lam' d2 * gF (Nat.lcm p (Nat.lcm d1 d2)) := by
          refine Finset.sum_congr rfl fun d1 _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d2 _ => by ring
  rw [hstep1]
  -- For d1, d2 ∈ S0, p ∤ lcm d1 d2, so gF (lcm p (lcm d1 d2)) = gF p * gF (lcm d1 d2)
  have hstep2 : ∑ d1 ∈ S0, ∑ d2 ∈ S0, lam' d1 * lam' d2 * gF (Nat.lcm p (Nat.lcm d1 d2)) =
      gF p * ∑ d1 ∈ S0, ∑ d2 ∈ S0, lam' d1 * lam' d2 * gF (Nat.lcm d1 d2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d1 hd1 => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d2 hd2 => ?_
    have hnd1 := (Finset.mem_filter.mp hd1).2
    have hnd2 := (Finset.mem_filter.mp hd2).2
    have hnd_lcm : ¬ p ∣ Nat.lcm d1 d2 := by
      intro hd
      have hmul : p ∣ d1 * d2 := hd.trans (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
      rcases hp.dvd_mul.mp hmul with h1 | h2
      · exact hnd1 h1
      · exact hnd2 h2
    have hcop : Nat.Coprime p (Nat.lcm d1 d2) := hp.coprime_iff_not_dvd.mpr hnd_lcm
    rw [hcop.lcm_eq_mul, gF_mul_coprime hcop]
    ring
  rw [hstep2]
  congr 1
  -- Diagonalize on S0
  have hdiag : ∑ d1 ∈ S0, ∑ d2 ∈ S0, lam' d1 * lam' d2 * gF (Nat.lcm d1 d2) =
      ∑ r ∈ S0, phiG r * (∑ d ∈ S0.filter (fun d => r ∣ d), lam' d * gF d) ^ 2 := by
    have hterm : ∀ d1 ∈ S0, ∀ d2 ∈ S0,
        lam' d1 * lam' d2 * gF (Nat.lcm d1 d2) =
        ∑ r ∈ S0, if r ∣ d1 ∧ r ∣ d2 then phiG r * (lam' d1 * gF d1) * (lam' d2 * gF d2) else 0 := by
      intro d1 hd1 d2 hd2
      have hsf1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hd1).1).2
      have hsf2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hd2).1).2
      have hnd1 := (Finset.mem_filter.mp hd1).2
      have hd1_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd1).1).1
      rw [gF_lcm_eq hsf1 hsf2, Finset.mul_sum]
      have hsub : (Nat.gcd d1 d2).divisors = S0.filter (fun r => r ∣ d1 ∧ r ∣ d2) := by
        ext r
        simp only [Nat.mem_divisors, Finset.mem_filter, S0, sfLE, Finset.mem_Icc]
        have hg_pos : 0 < Nat.gcd d1 d2 := Nat.gcd_pos_of_pos_left d2 (by omega)
        constructor
        · rintro ⟨hrg, _⟩
          have hr1 := hrg.trans (Nat.gcd_dvd_left d1 d2)
          have hr2 := hrg.trans (Nat.gcd_dvd_right d1 d2)
          exact ⟨⟨⟨⟨Nat.pos_of_dvd_of_pos hr1 (by omega),
            (Nat.le_of_dvd (by omega) hr1).trans hd1_Icc.2⟩,
            hsf1.squarefree_of_dvd hr1⟩, fun hpr => hnd1 (hpr.trans hr1)⟩, hr1, hr2⟩
        · rintro ⟨_, hr1, hr2⟩
          exact ⟨Nat.dvd_gcd hr1 hr2, hg_pos.ne'⟩
      rw [hsub, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs <;> ring
    calc ∑ d1 ∈ S0, ∑ d2 ∈ S0, lam' d1 * lam' d2 * gF (Nat.lcm d1 d2)
        = ∑ d1 ∈ S0, ∑ d2 ∈ S0, ∑ r ∈ S0,
            if r ∣ d1 ∧ r ∣ d2 then phiG r * (lam' d1 * gF d1) * (lam' d2 * gF d2) else 0 :=
          Finset.sum_congr rfl fun d1 hd1 => Finset.sum_congr rfl fun d2 hd2 => hterm d1 hd1 d2 hd2
      _ = ∑ d1 ∈ S0, ∑ r ∈ S0, ∑ d2 ∈ S0,
            if r ∣ d1 ∧ r ∣ d2 then phiG r * (lam' d1 * gF d1) * (lam' d2 * gF d2) else 0 :=
          Finset.sum_congr rfl fun d1 _ => Finset.sum_comm
      _ = ∑ r ∈ S0, ∑ d1 ∈ S0, ∑ d2 ∈ S0,
            if r ∣ d1 ∧ r ∣ d2 then phiG r * (lam' d1 * gF d1) * (lam' d2 * gF d2) else 0 :=
          Finset.sum_comm
      _ = ∑ r ∈ S0, phiG r * (∑ d ∈ S0.filter (fun d => r ∣ d), lam' d * gF d) ^ 2 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [sq, Finset.sum_mul, Finset.mul_sum]
          trans ∑ d1 ∈ S0.filter (fun d => r ∣ d), ∑ d2 ∈ S0.filter (fun d => r ∣ d),
              phiG r * (lam' d1 * gF d1) * (lam' d2 * gF d2)
          · rw [Finset.sum_filter (s := S0)]
            refine Finset.sum_congr rfl fun d1 _ => ?_
            by_cases h1r : r ∣ d1
            · simp [h1r, Finset.sum_filter (s := S0)]
            · simp [h1r]
          · refine Finset.sum_congr rfl fun d1 _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun d2 _ => by ring
  rw [hdiag]
  -- Evaluate inner sum for each r ∈ S0
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr_sfLE := (Finset.mem_filter.mp hr).1
  have hr_sf := (Finset.mem_filter.mp hr_sfLE).2
  have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr_sfLE).1
  have hr_nd := (Finset.mem_filter.mp hr).2
  have hinner : ∑ d ∈ S0.filter (fun d => r ∣ d), lam' d * gF d =
      (zW R r + zW R (p * r)) / phiG r := by
    have hadd : ∑ d ∈ S0.filter (fun d => r ∣ d), lam' d * gF d =
        (∑ d ∈ S0.filter (fun d => r ∣ d), lam R d * gF d) +
        (∑ d ∈ S0.filter (fun d => r ∣ d), lam R (p * d) * gF d) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => by dsimp [lam']; ring
    rw [hadd]
    have hcop_r : Nat.Coprime p r := hp.coprime_iff_not_dvd.mpr hr_nd
    have hsum_pr_all : ∑ m ∈ (sfLE R).filter (fun m => p * r ∣ m), lam R m * gF m = yW R (p * r) := by
      by_cases hprR : p * r ≤ R
      · have hpr_mem : p * r ∈ sfLE R :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hp.pos hr_Icc.1, hprR⟩,
            (Nat.squarefree_mul hcop_r).mpr ⟨hp.squarefree, hr_sf⟩⟩
        exact lam_inversion R (p * r) hpr_mem
      · have hempty : (sfLE R).filter (fun m => p * r ∣ m) = ∅ := by
          ext m
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hm hprm
          have hm_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
          have := Nat.le_of_dvd (by omega) hprm
          omega
        rw [hempty, Finset.sum_empty]
        simp [yW, zW, hprR]
    have hsum1 : ∑ d ∈ S0.filter (fun d => r ∣ d), lam R d * gF d = yW R r - yW R (p * r) := by
      have hpart := (Finset.sum_filter_add_sum_filter_not ((sfLE R).filter (fun d => r ∣ d))
        (fun d => ¬ p ∣ d) (fun d => lam R d * gF d)).symm
      rw [lam_inversion R r hr_sfLE] at hpart
      have hf1 : ((sfLE R).filter (fun d => r ∣ d)).filter (fun d => ¬ p ∣ d) =
          S0.filter (fun d => r ∣ d) := by
        ext d; simp only [S0, Finset.mem_filter]; tauto
      have hf2 : ((sfLE R).filter (fun d => r ∣ d)).filter (fun d => ¬ ¬ p ∣ d) =
          (sfLE R).filter (fun m => p * r ∣ m) := by
        ext d
        simp only [Finset.mem_filter, not_not]
        constructor
        · rintro ⟨⟨hd, hrd⟩, hpd⟩
          exact ⟨hd, hcop_r.mul_dvd_of_dvd_of_dvd hpd hrd⟩
        · rintro ⟨hd, hprd⟩
          exact ⟨⟨hd, (dvd_mul_left r p).trans hprd⟩, (dvd_mul_right p r).trans hprd⟩
      rw [hf1, hf2, hsum_pr_all] at hpart
      linarith
    have hsum2 : ∑ d ∈ S0.filter (fun d => r ∣ d), lam R (p * d) * gF d =
        (1 / gF p) * yW R (p * r) := by
      rw [← hsum_pr_all, Finset.mul_sum]
      have hdrop : ∑ d ∈ S0.filter (fun d => r ∣ d), lam R (p * d) * gF d =
          ∑ d ∈ (S0.filter (fun d => r ∣ d)).filter (fun d => p * d ≤ R), lam R (p * d) * gF d := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro d hd hnot
        rw [Finset.mem_filter] at hnot
        have hgt : ¬ p * d ≤ R := fun hle => hnot ⟨hd, hle⟩
        simp [lam, hgt]
      rw [hdrop]
      apply Finset.sum_bij (fun d _ => p * d)
      · intro d hd
        obtain ⟨hdS0r, hpdR⟩ := Finset.mem_filter.mp hd
        obtain ⟨hdS0, hrd⟩ := Finset.mem_filter.mp hdS0r
        obtain ⟨hd_sfLE, hnd⟩ := Finset.mem_filter.mp hdS0
        have hd_sf := (Finset.mem_filter.mp hd_sfLE).2
        have hd_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd_sfLE).1
        have hcop_d : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hnd
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨Nat.mul_pos hp.pos hd_Icc.1, hpdR⟩,
          (Nat.squarefree_mul hcop_d).mpr ⟨hp.squarefree, hd_sf⟩⟩,
          mul_dvd_mul_left p hrd⟩
      · intro d1 _ d2 _ heq
        exact Nat.eq_of_mul_eq_mul_left hp.pos heq
      · intro m hm
        obtain ⟨hm_sfLE, hprm⟩ := Finset.mem_filter.mp hm
        have hm_sf := (Finset.mem_filter.mp hm_sfLE).2
        have hm_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hm_sfLE).1
        have hpm : p ∣ m := (dvd_mul_right p r).trans hprm
        have hnd_mp : ¬ p ∣ m / p := by
          intro hpp
          have : p * p ∣ m := by rw [← Nat.mul_div_cancel' hpm]; exact mul_dvd_mul_left p hpp
          exact hp.not_isUnit (hm_sf p this)
        have hr_mp : r ∣ m / p := by
          obtain ⟨c, hc⟩ := hprm
          refine ⟨c, ?_⟩
          rw [hc, mul_assoc, Nat.mul_div_cancel_left (r * c) hp.pos]
        have hmp_pos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpm) hp.pos
        refine ⟨m / p, ?_, Nat.mul_div_cancel' hpm⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hmp_pos, (Nat.div_le_self m p).trans hm_Icc.2⟩,
            hm_sf.squarefree_of_dvd (Nat.div_dvd_of_dvd hpm)⟩, hnd_mp⟩, hr_mp⟩, ?_⟩
        rw [Nat.mul_div_cancel' hpm]; exact hm_Icc.2
      · intro d hd
        obtain ⟨hdS0r, _⟩ := Finset.mem_filter.mp hd
        obtain ⟨hdS0, _⟩ := Finset.mem_filter.mp hdS0r
        have hnd := (Finset.mem_filter.mp hdS0).2
        have hcop_d : Nat.Coprime p d := hp.coprime_iff_not_dvd.mpr hnd
        rw [gF_mul_coprime hcop_d]
        have hgp : gF p ≠ 0 := (gF_pos hp.pos).ne'
        field_simp
    rw [hsum1, hsum2]
    have hinv := inv_gF_prime_eq hp
    have hphi_mul : phiG (p * r) = phiG p * phiG r := phiG_mul_coprime hcop_r
    have hphip : phiG p ≠ 0 := (phiG_pos p).ne'
    have hphir : phiG r ≠ 0 := (phiG_pos r).ne'
    simp only [yW, hphi_mul]
    rw [hinv]
    field_simp
    ring
  rw [hinner]
  have hph : phiG r ≠ 0 := (phiG_pos r).ne'
  field_simp

private lemma zW_sq_eq {R r : ℕ} (hr : r ∈ sfLE R) :
    (zW R r) ^ 2 = (1 - Real.log (r : ℝ) / Real.log (R : ℝ)) ^ 2 := by
  have hr_sf := (Finset.mem_filter.mp hr).2
  have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
  simp only [zW, hr_sf, hr_Icc.1, hr_Icc.2, and_self, ↓reduceIte]
  rw [mul_pow]
  have hmu2 : ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 = 1 := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hr_sf]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hmu2, one_mul]

private lemma zW_add_sq_eq {R p r : ℕ} (hR : 2 ≤ R) (hp : p.Prime)
    (hr : r ∈ sfLE R) (hnd : ¬ p ∣ r) :
    (zW R r + zW R (p * r)) ^ 2 =
      (min (Real.log (p : ℝ) / Real.log (R : ℝ))
        (1 - Real.log (r : ℝ) / Real.log (R : ℝ))) ^ 2 := by
  have hr_sf := (Finset.mem_filter.mp hr).2
  have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr_Icc.1
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcop : Nat.Coprime p r := hp.coprime_iff_not_dvd.mpr hnd
  have hmu2 : ((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 = 1 := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hr_sf]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  by_cases hprR : p * r ≤ R
  · have hpr_sf : Squarefree (p * r) := (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hr_sf⟩
    have hpr_pos : 1 ≤ p * r := Nat.mul_pos hp.pos hr_Icc.1
    have hmu_pr : (ArithmeticFunction.moebius (p * r) : ℤ) = -(ArithmeticFunction.moebius r : ℤ) := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime hp]
      ring
    have hlog_mul : Real.log ((p * r : ℕ) : ℝ) = Real.log (p : ℝ) + Real.log (r : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul hp_pos.ne' hr_pos.ne']
    have hle : Real.log (p : ℝ) / Real.log (R : ℝ) ≤ 1 - Real.log (r : ℝ) / Real.log (R : ℝ) := by
      have hlog_le : Real.log (p : ℝ) + Real.log (r : ℝ) ≤ Real.log (R : ℝ) := by
        rw [← hlog_mul]
        exact Real.log_le_log (by positivity) (by exact_mod_cast hprR)
      rw [le_sub_iff_add_le, ← add_div, div_le_one hlogR]
      exact hlog_le
    rw [min_eq_left hle]
    simp only [zW, hr_sf, hr_Icc.1, hr_Icc.2, hpr_sf, hprR, hpr_pos, and_self, ↓reduceIte,
      hmu_pr, Int.cast_neg, hlog_mul]
    have hsimp : ((ArithmeticFunction.moebius r : ℤ) : ℝ) * (1 - Real.log (r : ℝ) / Real.log (R : ℝ)) +
        -((ArithmeticFunction.moebius r : ℤ) : ℝ) *
          (1 - (Real.log (p : ℝ) + Real.log (r : ℝ)) / Real.log (R : ℝ)) =
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) * (Real.log (p : ℝ) / Real.log (R : ℝ)) := by
      ring
    rw [hsimp, mul_pow, hmu2, one_mul]
  · have hlt : 1 - Real.log (r : ℝ) / Real.log (R : ℝ) < Real.log (p : ℝ) / Real.log (R : ℝ) := by
      have hRlt : (R : ℝ) < (p : ℝ) * (r : ℝ) := by exact_mod_cast (show R < p * r by omega)
      have hlog_lt : Real.log (R : ℝ) < Real.log (p : ℝ) + Real.log (r : ℝ) := by
        rw [← Real.log_mul hp_pos.ne' hr_pos.ne']
        exact Real.log_lt_log (by exact_mod_cast (show 0 < R by omega)) hRlt
      rw [sub_lt_iff_lt_add, ← add_div, one_lt_div hlogR]
      exact hlog_lt
    rw [min_eq_right hlt.le]
    simp only [zW, hr_sf, hr_Icc.1, hr_Icc.2, hprR, and_self, and_false, false_and, ↓reduceIte,
      add_zero]
    rw [mul_pow, hmu2, one_mul]

/-- The harmonic-like sum `H(u) = ∑_{r ≤ u, sqfree} 1 / phiG r`. -/
private def Hsum (u : ℕ) : ℝ :=
  ∑ r ∈ sfLE u, (1 : ℝ) / phiG r

private lemma Hsum_nonneg (u : ℕ) : 0 ≤ Hsum u :=
  Finset.sum_nonneg fun r _ => div_nonneg zero_le_one (phiG_pos r).le

private lemma Hsum_ge_one {u : ℕ} (hu : 1 ≤ u) : 1 ≤ Hsum u := by
  have h1 : 1 ∈ sfLE u := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hu⟩, squarefree_one⟩
  calc (1 : ℝ) = 1 / phiG 1 := by simp [phiG_one]
    _ ≤ Hsum u := Finset.single_le_sum (fun r _ => div_nonneg zero_le_one (phiG_pos r).le) h1

private lemma inv_gF_mul_phiG_le_Hsum {R d : ℕ} (hd : d ∈ sfLE R) :
    1 / (gF d * phiG d) ≤ Hsum R := by
  have hd_sf := (Finset.mem_filter.mp hd).2
  have hd_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
  have heq : 1 / (gF d * phiG d) = ∑ e ∈ d.divisors, (1 : ℝ) / phiG e := by
    have h1 := inv_gF_eq_sum_phiG hd_sf
    have hphid : phiG d ≠ 0 := (phiG_pos d).ne'
    calc 1 / (gF d * phiG d) = (1 / gF d) / phiG d := by ring
      _ = (∑ r ∈ d.divisors, phiG r) / phiG d := by rw [h1]
      _ = ∑ r ∈ d.divisors, phiG r / phiG d := Finset.sum_div _ _ _
      _ = ∑ e ∈ d.divisors, (1 : ℝ) / phiG e := by
          apply Finset.sum_bij (fun r _ => d / r)
          · intro r hr
            rw [Nat.mem_divisors] at hr ⊢
            exact ⟨Nat.div_dvd_of_dvd hr.1, hr.2⟩
          · intro r1 hr1 r2 hr2 heq
            have h1d := Nat.dvd_of_mem_divisors hr1
            have h2d := Nat.dvd_of_mem_divisors hr2
            have hd_pos : 0 < d := by omega
            have hq1 := Nat.mul_div_cancel' h1d
            have hq2 := Nat.mul_div_cancel' h2d
            have hpos : 0 < d / r1 := Nat.div_pos (Nat.le_of_dvd hd_pos h1d)
              (Nat.pos_of_dvd_of_pos h1d hd_pos)
            rw [heq] at hq1
            exact Nat.eq_of_mul_eq_mul_right (heq ▸ hpos) (hq1.trans hq2.symm)
          · intro e he
            rw [Nat.mem_divisors] at he
            exact ⟨d / e, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd he.1, he.2⟩,
              Nat.div_div_self he.1 he.2⟩
          · intro r hr
            have hrd := Nat.dvd_of_mem_divisors hr
            have hcop : Nat.Coprime r (d / r) := by
              apply Nat.coprime_of_dvd
              intro p hp hpr hpdr
              have hp2 : p * p ∣ d := by
                rw [← Nat.mul_div_cancel' hrd]; exact mul_dvd_mul hpr hpdr
              exact hp.not_isUnit (hd_sf p hp2)
            have hmul : phiG d = phiG r * phiG (d / r) := by
              conv_lhs => rw [← Nat.mul_div_cancel' hrd]
              exact phiG_mul_coprime hcop
            rw [hmul]
            have hpr : phiG r ≠ 0 := (phiG_pos r).ne'
            have hpdr : phiG (d / r) ≠ 0 := (phiG_pos (d / r)).ne'
            field_simp
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    rw [Nat.mem_divisors] at he
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.pos_of_dvd_of_pos he.1 (by omega), (Nat.le_of_dvd (by omega) he.1).trans hd_Icc.2⟩,
      hd_sf.squarefree_of_dvd he.1⟩
  · intro r _ _
    exact div_nonneg zero_le_one (phiG_pos r).le

private lemma abs_lam_le_Hsum_sq {R d : ℕ} (hR : 2 ≤ R) :
    |lam R d| ≤ (Hsum R) ^ 2 := by
  by_cases hd : d ∈ sfLE R
  · have hd_sf := (Finset.mem_filter.mp hd).2
    have hd_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
    have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
    simp only [lam, hd_sf, hd_Icc.1, hd_Icc.2, and_self, ↓reduceIte]
    rw [abs_mul, abs_of_pos (div_pos one_pos (gF_pos (by omega)))]
    have hsum_le : |∑ r ∈ (sfLE R).filter (fun r => d ∣ r),
        ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) * yW R r| ≤
        (1 / phiG d) * Hsum R := by
      calc |∑ r ∈ (sfLE R).filter (fun r => d ∣ r),
            ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) * yW R r|
          ≤ ∑ r ∈ (sfLE R).filter (fun r => d ∣ r),
            |((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) * yW R r| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ r ∈ (sfLE R).filter (fun r => d ∣ r), (1 : ℝ) / phiG r := by
            apply Finset.sum_le_sum
            intro r hr
            have hr_mem := (Finset.mem_filter.mp hr).1
            have hr_sf := (Finset.mem_filter.mp hr_mem).2
            have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr_mem).1
            rw [abs_mul, yW, abs_div, abs_of_pos (phiG_pos r)]
            have hmu_le1 : |((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)| ≤ 1 := by
              have hsf_rd : Squarefree (r / d) := hr_sf.squarefree_of_dvd
                (Nat.div_dvd_of_dvd (Finset.mem_filter.mp hr).2)
              rw [ArithmeticFunction.moebius_apply_of_squarefree hsf_rd]
              push_cast
              rw [abs_pow, abs_neg, abs_one, one_pow]
            have hz_le1 : |zW R r| ≤ 1 := by
              simp only [zW, hr_sf, hr_Icc.1, hr_Icc.2, and_self, ↓reduceIte]
              rw [abs_mul]
              have hm1 : |((ArithmeticFunction.moebius r : ℤ) : ℝ)| = 1 := by
                rw [ArithmeticFunction.moebius_apply_of_squarefree hr_sf]
                push_cast
                rw [abs_pow, abs_neg, abs_one, one_pow]
              rw [hm1, one_mul]
              have hlog_nn : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast hr_Icc.1)
              have hlog_le : Real.log (r : ℝ) ≤ Real.log (R : ℝ) :=
                Real.log_le_log (by exact_mod_cast hr_Icc.1) (by exact_mod_cast hr_Icc.2)
              have hdiv_nn : 0 ≤ Real.log (r : ℝ) / Real.log (R : ℝ) := div_nonneg hlog_nn hlogR.le
              have hdiv_le : Real.log (r : ℝ) / Real.log (R : ℝ) ≤ 1 := (div_le_one hlogR).mpr hlog_le
              rw [abs_of_nonneg (by linarith)]
              linarith
            have hmul_le : |((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)| * |zW R r| ≤ 1 := by
              nlinarith [abs_nonneg ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ), abs_nonneg (zW R r)]
            calc |((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)| * (|zW R r| / phiG r)
                = (|((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ)| * |zW R r|) / phiG r := by ring
              _ ≤ 1 / phiG r := div_le_div_of_nonneg_right hmul_le (phiG_pos r).le
        _ ≤ (1 / phiG d) * Hsum R := by
            unfold Hsum
            rw [Finset.mul_sum]
            have hbi : ∑ r ∈ (sfLE R).filter (fun r => d ∣ r), (1 : ℝ) / phiG r ≤
                ∑ m ∈ sfLE R, (1 / phiG d) * (1 / phiG m) := by
              have himg : ∑ r ∈ (sfLE R).filter (fun r => d ∣ r), (1 : ℝ) / phiG r =
                  ∑ m ∈ (sfLE R).filter (fun m => Nat.Coprime d m ∧ d * m ≤ R),
                    (1 / phiG d) * (1 / phiG m) := by
                apply Finset.sum_bij (fun r _ => r / d)
                · intro r hr
                  obtain ⟨hr_mem, hdr⟩ := Finset.mem_filter.mp hr
                  have hr_sf := (Finset.mem_filter.mp hr_mem).2
                  have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr_mem).1
                  have hcop : Nat.Coprime d (r / d) := by
                    apply Nat.coprime_of_dvd
                    intro p hp hpd hprd
                    have hp2 : p * p ∣ r := by
                      rw [← Nat.mul_div_cancel' hdr]; exact mul_dvd_mul hpd hprd
                    exact hp.not_isUnit (hr_sf p hp2)
                  have hpos : 0 < r / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdr) (by omega)
                  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
                    ⟨Finset.mem_Icc.mpr ⟨hpos, (Nat.div_le_self r d).trans hr_Icc.2⟩,
                      hr_sf.squarefree_of_dvd (Nat.div_dvd_of_dvd hdr)⟩, hcop, ?_⟩
                  rw [Nat.mul_div_cancel' hdr]; exact hr_Icc.2
                · intro r1 hr1 r2 hr2 heq
                  rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hr1).2,
                    ← Nat.mul_div_cancel' (Finset.mem_filter.mp hr2).2, heq]
                · intro m hm
                  obtain ⟨hm_mem, hcop, hdmR⟩ := Finset.mem_filter.mp hm
                  have hm_sf := (Finset.mem_filter.mp hm_mem).2
                  have hm_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hm_mem).1
                  refine ⟨d * m, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
                    ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos (by omega) hm_Icc.1, hdmR⟩,
                      (Nat.squarefree_mul hcop).mpr ⟨hd_sf, hm_sf⟩⟩, dvd_mul_right d m⟩,
                    Nat.mul_div_cancel_left m (by omega)⟩
                · intro r hr
                  obtain ⟨hr_mem, hdr⟩ := Finset.mem_filter.mp hr
                  have hr_sf := (Finset.mem_filter.mp hr_mem).2
                  have hcop : Nat.Coprime d (r / d) := by
                    apply Nat.coprime_of_dvd
                    intro p hp hpd hprd
                    have hp2 : p * p ∣ r := by
                      rw [← Nat.mul_div_cancel' hdr]; exact mul_dvd_mul hpd hprd
                    exact hp.not_isUnit (hr_sf p hp2)
                  have hmul : phiG r = phiG d * phiG (r / d) := by
                    conv_lhs => rw [← Nat.mul_div_cancel' hdr]
                    exact phiG_mul_coprime hcop
                  rw [hmul]
                  ring
              rw [himg]
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                fun m _ _ => mul_nonneg (div_nonneg zero_le_one (phiG_pos d).le)
                  (div_nonneg zero_le_one (phiG_pos m).le)
            exact hbi
    calc (1 / gF d) * |∑ r ∈ (sfLE R).filter (fun r => d ∣ r),
            ((ArithmeticFunction.moebius (r / d) : ℤ) : ℝ) * yW R r|
        ≤ (1 / gF d) * ((1 / phiG d) * Hsum R) :=
          mul_le_mul_of_nonneg_left hsum_le (div_nonneg zero_le_one (gF_pos (by omega)).le)
      _ = (1 / (gF d * phiG d)) * Hsum R := by ring
      _ ≤ Hsum R * Hsum R := mul_le_mul_of_nonneg_right (inv_gF_mul_phiG_le_Hsum hd) (Hsum_nonneg R)
      _ = (Hsum R) ^ 2 := (sq _).symm
  · have hnot : ¬ (Squarefree d ∧ d ≤ R ∧ 1 ≤ d) := by
      rintro ⟨h1, h2, h3⟩
      exact hd (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h3, h2⟩, h1⟩)
    simp only [lam, hnot, ↓reduceIte, abs_zero]
    exact sq_nonneg _

/- Section 3: Elementary Mertens / Chebyshev Prime Sums -/

private lemma pow_div_factorial_le_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ n / (n.factorial : ℝ) ≤ Real.exp x := by
  have h1 : x ^ n / (n.factorial : ℝ) ≤
      ∑ i ∈ Finset.range (n + 1), x ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum (fun i _ => div_nonneg (pow_nonneg hx i) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
  exact h1.trans (Real.sum_le_exp_of_nonneg hx (n + 1))

private lemma log_factorial_ge {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hfac_pos : (0 : ℝ) < n.factorial := by positivity
  have hbound : (n : ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp n :=
    pow_div_factorial_le_exp hn_pos.le n
  have h1 : (n : ℝ) ^ n ≤ Real.exp n * (n.factorial : ℝ) := (div_le_iff₀ hfac_pos).mp hbound
  have hlog : Real.log ((n : ℝ) ^ n) ≤ Real.log (Real.exp n * (n.factorial : ℝ)) :=
    Real.log_le_log (pow_pos hn_pos n) h1
  rw [Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hfac_pos.ne', Real.log_exp] at hlog
  linarith

private lemma log_factorial_le (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
  have hfac_le : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
  have hfac_pos : (0 : ℝ) < n.factorial := by positivity
  have hlog : Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) :=
    Real.log_le_log hfac_pos (by exact_mod_cast hfac_le)
  rwa [Real.log_pow] at hlog

private lemma log_factorial_eq_sum_primesLE (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE n, (n.factorial.factorization p : ℝ) * Real.log p := by
  have hne : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  have hprod : n.factorial = ∏ p ∈ n.factorial.primeFactors, p ^ (n.factorial.factorization p) :=
    (Nat.prod_factorization_pow_eq_self hne).symm
  have hsub : n.factorial.primeFactors ⊆ Nat.primesLE n := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨hp.1.dvd_factorial.mp hp.2.1, hp.1⟩
  have hprod2 : n.factorial = ∏ p ∈ Nat.primesLE n, p ^ (n.factorial.factorization p) := by
    conv_lhs => rw [hprod]
    apply Finset.prod_subset hsub
    intro p _ hp
    have hzero : n.factorial.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
    rw [hzero, pow_zero]
  have hcast : (n.factorial : ℝ) =
      ∏ p ∈ Nat.primesLE n, ((p : ℝ) ^ (n.factorial.factorization p)) := by
    conv_lhs => rw [hprod2]
    push_cast
    rfl
  rw [hcast, Real.log_prod]
  · refine Finset.sum_congr rfl fun p _ => by rw [Real.log_pow]
  · intro p hp
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.mem_primesLE.mp hp).2.ne_zero)

private lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
  have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by rw [Real.log_sqrt hx.le]; ring
  linarith

private lemma sum_log_div_p_mul_pred_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ C := by
  have hsum : Summable (fun m : ℕ => (4 : ℝ) * (1 / (m : ℝ) ^ ((3 : ℝ) / 2))) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left 4
  refine ⟨∑' m : ℕ, (4 : ℝ) * (1 / (m : ℝ) ^ ((3 : ℝ) / 2)),
    tsum_nonneg fun m => by positivity, fun n => ?_⟩
  have hle : ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      ∑ p ∈ Nat.primesLE n, (4 : ℝ) * (1 / (p : ℝ) ^ ((3 : ℝ) / 2)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : 2 ≤ p := (Nat.mem_primesLE.mp hp).2.two_le
    have hp_pos : (0 : ℝ) < p := by positivity
    have hp2r : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have hpred : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
    have hlog : Real.log p ≤ 2 * Real.sqrt p := log_le_two_sqrt hp_pos
    have hrpow : (p : ℝ) ^ ((3 : ℝ) / 2) = (p : ℝ) * Real.sqrt p := by
      rw [Real.sqrt_eq_rpow]
      conv_lhs => rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hp_pos, Real.rpow_one]
    calc Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ (2 * Real.sqrt p) / ((p : ℝ) * ((p : ℝ) / 2)) := by gcongr
      _ = 4 / ((p : ℝ) * Real.sqrt p) := by
          have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp_pos.le
          have hs_ne : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp_pos).ne'
          field_simp; nlinarith [hsq]
      _ = 4 * (1 / (p : ℝ) ^ ((3 : ℝ) / 2)) := by rw [hrpow]; ring
  exact hle.trans (hsum.sum_le_tsum (Nat.primesLE n) (fun m _ => by positivity))

private lemma mertens_first :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) - Real.log n| ≤ C := by
  obtain ⟨C2, hC2_nn, hC2⟩ := sum_log_div_p_mul_pred_le
  refine ⟨max (1 + C2) (Real.log 4), lt_of_lt_of_le (by linarith) (le_max_left _ _), fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < n := by positivity
  rw [abs_le]
  constructor
  · have h1 := log_factorial_ge hn
    rw [log_factorial_eq_sum_primesLE] at h1
    have h2 : ∑ p ∈ Nat.primesLE n, (n.factorial.factorization p : ℝ) * Real.log p ≤
        (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)) +
        (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro p hp
      have hp_prime := (Nat.mem_primesLE.mp hp).2
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
      have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
      have hvp_nat : (p - 1) * n.factorial.factorization p ≤ n := by
        rw [Nat.sub_one_mul_factorization_factorial hp_prime]; exact Nat.sub_le n _
      have hvp : (n.factorial.factorization p : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
        rw [le_div_iff₀ hp1_pos]
        have hcast : ((p - 1 : ℕ) : ℝ) * (n.factorial.factorization p : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hvp_nat
        rw [Nat.cast_sub hp_prime.one_le, Nat.cast_one] at hcast
        linarith
      have hfrac : (n : ℝ) / ((p : ℝ) - 1) * Real.log p =
          (n : ℝ) * (Real.log p / (p : ℝ)) +
          (n : ℝ) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by field_simp; ring
      calc (n.factorial.factorization p : ℝ) * Real.log p
          ≤ (n : ℝ) / ((p : ℝ) - 1) * Real.log p := by gcongr
        _ = _ := hfrac
    have h4 := hC2 n
    have hmax : 1 + C2 ≤ max (1 + C2) (Real.log 4) := le_max_left _ _
    nlinarith
  · have h1 := log_factorial_le n
    rw [log_factorial_eq_sum_primesLE] at h1
    have htheta : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
      rw [← Chebyshev.theta_eq_sum_primesLE_log]
      exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
    have h2 : (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)) ≤
        (∑ p ∈ Nat.primesLE n, (n.factorial.factorization p : ℝ) * Real.log p) +
        (∑ p ∈ Nat.primesLE n, Real.log p) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro p hp
      have hp_le := (Nat.mem_primesLE.mp hp).1
      have hp_prime := (Nat.mem_primesLE.mp hp).2
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
      have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
      have hdiv_le : n / p ≤ n.factorial.factorization p := by
        rw [Nat.factorization_factorial hp_prime (Nat.lt_succ_self (Nat.log p n))]
        have h1log : 1 ≤ Nat.log p n := Nat.le_log_of_pow_le hp_prime.one_lt (by simpa using hp_le)
        have hmem : 1 ∈ Finset.Ico 1 (Nat.log p n + 1) :=
          Finset.mem_Ico.mpr ⟨le_rfl, Nat.lt_succ_of_le h1log⟩
        simpa using Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) hmem
      have hfloor : (n : ℝ) / (p : ℝ) ≤ (n / p : ℕ) + 1 := by
        rw [div_le_iff₀ hp_pos]
        have hmod : n < (n / p + 1) * p := by
          have := Nat.div_add_mod n p
          have := Nat.mod_lt n hp_prime.pos
          nlinarith
        have hcast : (n : ℝ) < ((n / p + 1 : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast hmod
        push_cast at hcast; linarith
      have hbound : (n : ℝ) / (p : ℝ) ≤ (n.factorial.factorization p : ℝ) + 1 :=
        hfloor.trans (by gcongr)
      calc (n : ℝ) * (Real.log p / (p : ℝ))
          = ((n : ℝ) / (p : ℝ)) * Real.log p := by ring
        _ ≤ ((n.factorial.factorization p : ℝ) + 1) * Real.log p := by gcongr
        _ = (n.factorial.factorization p : ℝ) * Real.log p + Real.log p := by ring
    have hmax : Real.log 4 ≤ max (1 + C2) (Real.log 4) := le_max_right _ _
    nlinarith

private lemma sum_Ico_sub_succ (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (f n - f (n + 1)) = f a - f b := by
  induction b with
  | zero =>
    have ha0 : a = 0 := Nat.eq_zero_of_le_zero hab
    subst ha0; simp
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · simp
    · have hle : a ≤ b := Nat.lt_succ_iff.mp hlt
      have hIco : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hIco, Finset.sum_insert (by simp), ih hle]; ring

private lemma abel_summation_Ioc (f g : ℕ → ℝ) (a b : ℕ) (hab : a < b) :
    ∑ n ∈ Finset.Ioc a b, (f n - f (n - 1)) * g n =
      f b * g b - f a * g (a + 1) +
      ∑ n ∈ Finset.Ico (a + 1) b, f n * (g n - g (n + 1)) := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hab) with rfl | hlt
    · have hIoc : Finset.Ioc a (a + 1) = {a + 1} := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
      rw [hIoc, Finset.sum_singleton, add_tsub_cancel_right, Finset.Ico_self, Finset.sum_empty,
        add_zero]; ring
    · rw [Finset.sum_Ioc_succ_top hlt.le, ih hlt]
      have hIco : Finset.Ico (a + 1) (b + 1) = insert b (Finset.Ico (a + 1) b) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hIco, Finset.sum_insert (by simp)]
      simp only [add_tsub_cancel_right]; ring

private def Msum (n : ℕ) : ℝ := ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)

private lemma Msum_diff {n : ℕ} (hn : 1 ≤ n) :
    Msum n - Msum (n - 1) = if n.Prime then Real.log n / (n : ℝ) else 0 := by
  dsimp only [Msum]
  have hsucc : Nat.primesLE n =
      if n.Prime then insert n (Nat.primesLE (n - 1)) else Nat.primesLE (n - 1) := by
    ext p
    split_ifs with hp
    · simp only [Nat.mem_primesLE, Finset.mem_insert]
      constructor
      · rintro ⟨hle, hpp⟩
        rcases eq_or_lt_of_le hle with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨by omega, hpp⟩
      · rintro (rfl | ⟨hle, hpp⟩)
        · exact ⟨le_rfl, hp⟩
        · exact ⟨by omega, hpp⟩
    · simp only [Nat.mem_primesLE]
      constructor
      · rintro ⟨hle, hpp⟩
        have hne : p ≠ n := fun h => hp (h ▸ hpp)
        exact ⟨by omega, hpp⟩
      · rintro ⟨hle, hpp⟩
        exact ⟨by omega, hpp⟩
  rw [hsucc]
  split_ifs with hp
  · have hnot : n ∉ Nat.primesLE (n - 1) := by
      simp only [Nat.mem_primesLE, not_and]; intro h; omega
    rw [Finset.sum_insert hnot, add_sub_cancel_right]
  · rw [sub_self]

private lemma sum_primes_sdiff_eq_Ioc (a b : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, f p =
      ∑ n ∈ Finset.Ioc a b, if n.Prime then f n else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hpb, hpp⟩, hna⟩
    exact ⟨⟨by by_contra hle; exact hna ⟨by omega, hpp⟩, hpb⟩, hpp⟩
  · rintro ⟨⟨hpa, hpb⟩, hpp⟩
    exact ⟨⟨hpb, hpp⟩, fun h => by omega⟩

private lemma sum_log_sq_div_p_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 2 / (p : ℝ) ≤
        (1 / 2) * (Real.log n) ^ 2 + C * (Real.log n + 1) := by
  obtain ⟨C1, hC1_pos, hC1⟩ := mertens_first
  refine ⟨2 * C1 + (Real.log 2) ^ 2 + 1, by positivity, fun n hn => ?_⟩
  have hM : ∀ k : ℕ, 1 ≤ k → |Msum k - Real.log k| ≤ C1 := fun k hk => hC1 k hk
  have h1 : ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 2 / (p : ℝ) =
      ∑ k ∈ Finset.Ioc 1 n, (Msum k - Msum (k - 1)) * Real.log k := by
    have hsdiff : Nat.primesLE n = Nat.primesLE n \ Nat.primesLE 1 := by
      ext p; simp only [Finset.mem_sdiff, Nat.mem_primesLE, not_and]
      exact ⟨fun h => ⟨h, fun h1 _ => absurd (h.2.two_le) (by omega)⟩, fun h => h.1⟩
    rw [hsdiff, sum_primes_sdiff_eq_Ioc]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := by have := (Finset.mem_Ioc.mp hk).1; omega
    rw [Msum_diff hk1]
    split_ifs <;> ring
  rw [h1, abel_summation_Ioc Msum (fun k => Real.log k) 1 n (by omega)]
  have hM1 : Msum 1 = 0 := by
    have : Nat.primesLE 1 = ∅ := by
      ext p; simp only [Nat.mem_primesLE, Finset.notMem_empty, iff_false, not_and]
      intro h1 hp; exact absurd hp.two_le (by omega)
    simp [Msum, this]
  rw [hM1, zero_mul, sub_zero]
  have hMn : Msum n ≤ Real.log n + C1 := by have := (abs_le.mp (hM n (by omega))).2; linarith
  have hlogn_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hterm : ∀ k ∈ Finset.Ico 2 n,
      Msum k * (Real.log k - Real.log ((k + 1 : ℕ) : ℝ)) ≤
      (1 / 2) * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) +
      (1 / 2) * (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) +
      C1 * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hk_pos : (0 : ℝ) < k := by positivity
    have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      linarith
    have hlk_le : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log hk_pos (by exact_mod_cast (Nat.le_succ k))
    have hdiff_nn : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log k := sub_nonneg.mpr hlk_le
    have hdiff_le : Real.log ((k + 1 : ℕ) : ℝ) - Real.log k ≤ 1 / (k : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ)) hk_pos)
      rw [Real.log_div (by positivity) hk_pos.ne'] at h
      have hsub : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = 1 / (k : ℝ) := by push_cast; field_simp; ring
      linarith
    have hsq_le : (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) ^ 2 ≤
        1 / ((k : ℝ) - 1) - 1 / (k : ℝ) := by
      have h1 : (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) ^ 2 ≤ (1 / (k : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hdiff_nn hdiff_le 2
      have h2 : (1 / (k : ℝ)) ^ 2 ≤ 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) := by
        have heq : 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) = 1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
          field_simp; ring
        rw [heq, one_div_pow]
        apply one_div_le_one_div_of_le (mul_pos hk_pos hk1_pos)
        nlinarith
      exact h1.trans h2
    have hMk_ge : Real.log k - C1 ≤ Msum k := by
      have := (abs_le.mp (hM k (by omega))).1; linarith
    have h1 : Msum k * (Real.log k - Real.log ((k + 1 : ℕ) : ℝ)) ≤
        (Real.log k - C1) * (Real.log k - Real.log ((k + 1 : ℕ) : ℝ)) := by
      nlinarith
    have h2 : (Real.log k) * (Real.log k - Real.log ((k + 1 : ℕ) : ℝ)) =
        (1 / 2) * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) +
        (1 / 2) * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) ^ 2 := by ring
    linarith
  have hsum_le := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at hsum_le
  have htel1 : ∑ k ∈ Finset.Ico 2 n, ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) =
      (Real.log 2) ^ 2 - (Real.log n) ^ 2 := by
    simpa using sum_Ico_sub_succ (fun k => (Real.log k) ^ 2) 2 n hn
  have htel_inv : ∑ k ∈ Finset.Ico 2 n, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) =
      1 - 1 / ((n : ℝ) - 1) := by
    have := sum_Ico_sub_succ (fun k => 1 / ((k : ℝ) - 1)) 2 n hn
    have hcongr : ∑ k ∈ Finset.Ico 2 n, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) =
        ∑ k ∈ Finset.Ico 2 n, (1 / ((k : ℝ) - 1) - 1 / (((k + 1 : ℕ) : ℝ) - 1)) := by
      refine Finset.sum_congr rfl fun k _ => by push_cast; ring
    rw [hcongr, this]
    norm_num
  have htel2 : ∑ k ∈ Finset.Ico 2 n, (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) =
      Real.log n - Real.log 2 := by
    have := sum_Ico_sub_succ (fun k => -Real.log k) 2 n hn
    simpa [sub_neg_eq_add, neg_add_eq_sub] using this
  rw [htel1, htel_inv, htel2] at hsum_le
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hinv_nn : (0 : ℝ) ≤ 1 / ((n : ℝ) - 1) := by positivity
  nlinarith

private lemma sum_log_cube_div_p_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      (1 / 3) * (Real.log n) ^ 3 - C * (Real.log n + 1) ^ 2 ≤
        ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 3 / (p : ℝ) := by
  obtain ⟨C1, hC1_pos, hC1⟩ := mertens_first
  refine ⟨2 * C1 + 1, by positivity, fun n hn => ?_⟩
  have hM : ∀ k : ℕ, 1 ≤ k → |Msum k - Real.log k| ≤ C1 := fun k hk => hC1 k hk
  have h1 : ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 3 / (p : ℝ) =
      ∑ k ∈ Finset.Ioc 1 n, (Msum k - Msum (k - 1)) * (Real.log k) ^ 2 := by
    have hsdiff : Nat.primesLE n = Nat.primesLE n \ Nat.primesLE 1 := by
      ext p; simp only [Finset.mem_sdiff, Nat.mem_primesLE, not_and]
      exact ⟨fun h => ⟨h, fun h1 _ => absurd h.2.two_le (by omega)⟩, fun h => h.1⟩
    rw [hsdiff, sum_primes_sdiff_eq_Ioc]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := by have := (Finset.mem_Ioc.mp hk).1; omega
    rw [Msum_diff hk1]
    split_ifs <;> ring
  rw [h1, abel_summation_Ioc Msum (fun k => (Real.log k) ^ 2) 1 n (by omega)]
  have hM1 : Msum 1 = 0 := by
    have : Nat.primesLE 1 = ∅ := by
      ext p; simp only [Nat.mem_primesLE, Finset.notMem_empty, iff_false, not_and]
      intro h1 hp; exact absurd hp.two_le (by omega)
    simp [Msum, this]
  rw [hM1, zero_mul, sub_zero]
  have hMn : Real.log n - C1 ≤ Msum n := by
    have := (abs_le.mp (hM n (by omega))).1; linarith
  have hlogn_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hterm : ∀ k ∈ Finset.Ico 2 n,
      (2 / 3) * ((Real.log k) ^ 3 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 3) -
      C1 * ((Real.log ((k + 1 : ℕ) : ℝ)) ^ 2 - (Real.log k) ^ 2) ≤
      Msum k * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hlk_nn : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
    have hlk_le : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ k))
    have hsq_le : (Real.log k) ^ 2 ≤ (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlk_nn hlk_le 2
    have hMk_le : Msum k ≤ Real.log k + C1 := by
      have := (abs_le.mp (hM k (by omega))).2; linarith
    have hstep1 : (Real.log k + C1) * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) ≤
        Msum k * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) := by
      nlinarith
    have halg : (2 / 3) * ((Real.log k) ^ 3 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 3) ≤
        (Real.log k) * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2) := by
      have hfac : 3 * (Real.log k * ((Real.log k) ^ 2 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 2)) -
          2 * ((Real.log k) ^ 3 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 3) =
          (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) ^ 2 *
          (2 * Real.log ((k + 1 : ℕ) : ℝ) + Real.log k) := by ring
      have hnn : 0 ≤ (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) ^ 2 *
          (2 * Real.log ((k + 1 : ℕ) : ℝ) + Real.log k) := by positivity
      linarith
    linarith
  have hsum_ge := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum_ge
  have htel1 : ∑ k ∈ Finset.Ico 2 n, ((Real.log k) ^ 3 - (Real.log ((k + 1 : ℕ) : ℝ)) ^ 3) =
      (Real.log 2) ^ 3 - (Real.log n) ^ 3 := by
    simpa using sum_Ico_sub_succ (fun k => (Real.log k) ^ 3) 2 n hn
  have htel2 : ∑ k ∈ Finset.Ico 2 n, ((Real.log ((k + 1 : ℕ) : ℝ)) ^ 2 - (Real.log k) ^ 2) =
      (Real.log n) ^ 2 - (Real.log 2) ^ 2 := by
    have := sum_Ico_sub_succ (fun k => -(Real.log k) ^ 2) 2 n hn
    simpa [sub_neg_eq_add, neg_add_eq_sub] using this
  rw [htel1, htel2] at hsum_ge
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

private lemma sum_inv_p_Ioc_le :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log b / Real.log a) + C / Real.log a := by
  obtain ⟨C1, hC1_pos, hC1⟩ := mertens_first
  refine ⟨3 * C1 + 1, by positivity, fun a b ha hab => ?_⟩
  have hM : ∀ k : ℕ, 1 ≤ k → |Msum k - Real.log k| ≤ C1 := fun k hk => hC1 k hk
  have hloga_pos : 0 < Real.log a := Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [div_self hloga_pos.ne']
    positivity
  have hlogb_pos : 0 < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have h1 : ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / (p : ℝ) =
      ∑ k ∈ Finset.Ioc a b, (Msum k - Msum (k - 1)) * (1 / Real.log k) := by
    rw [sum_primes_sdiff_eq_Ioc]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk2 : 2 ≤ k := by have := (Finset.mem_Ioc.mp hk).1; omega
    have hlk_pos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    rw [Msum_diff (by omega)]
    split_ifs
    · field_simp [hlk_pos.ne']
    · ring
  rw [h1, abel_summation_Ioc Msum (fun k => 1 / Real.log k) a b hlt]
  have hlog_a1_pos : 0 < Real.log ((a + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a + 1 by omega))
  have hloga_le_a1 : Real.log a ≤ Real.log ((a + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ a)
  have hloga_le_b : Real.log a ≤ Real.log b :=
    Real.log_le_log (by positivity) (by exact_mod_cast hlt.le)
  have hMb : Msum b * (1 / Real.log b) ≤ 1 + C1 / Real.log a := by
    have hle : Msum b ≤ Real.log b + C1 := by have := (abs_le.mp (hM b (by omega))).2; linarith
    have hdiv : C1 / Real.log b ≤ C1 / Real.log a :=
      div_le_div_of_nonneg_left hC1_pos.le hloga_pos hloga_le_b
    calc Msum b * (1 / Real.log b) ≤ (Real.log b + C1) * (1 / Real.log b) := by
          exact mul_le_mul_of_nonneg_right hle (by positivity)
      _ = 1 + C1 / Real.log b := by field_simp [hlogb_pos.ne']
      _ ≤ 1 + C1 / Real.log a := by linarith
  have hMa : -(Msum a * (1 / Real.log ((a + 1 : ℕ) : ℝ))) ≤
      -(Real.log a / Real.log ((a + 1 : ℕ) : ℝ)) + C1 / Real.log a := by
    have hge : Real.log a - C1 ≤ Msum a := by have := (abs_le.mp (hM a (by omega))).1; linarith
    have hdiv : C1 / Real.log ((a + 1 : ℕ) : ℝ) ≤ C1 / Real.log a :=
      div_le_div_of_nonneg_left hC1_pos.le hloga_pos hloga_le_a1
    have hmul : (Real.log a - C1) * (1 / Real.log ((a + 1 : ℕ) : ℝ)) ≤
        Msum a * (1 / Real.log ((a + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hge (by positivity)
    have hrew : (Real.log a - C1) * (1 / Real.log ((a + 1 : ℕ) : ℝ)) =
        Real.log a / Real.log ((a + 1 : ℕ) : ℝ) - C1 / Real.log ((a + 1 : ℕ) : ℝ) := by ring
    linarith
  have hterm : ∀ k ∈ Finset.Ico (a + 1) b,
      Msum k * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
      (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log k)) +
      C1 * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
    intro k hk
    have hk2 : 2 ≤ k := by have := (Finset.mem_Ico.mp hk).1; omega
    have hlk : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    have hlk1 : 0 < Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < k + 1 by omega))
    have hle : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ k)
    have hdiff_nn : 0 ≤ 1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ) :=
      sub_nonneg.mpr (one_div_le_one_div_of_le hlk hle)
    have hMk : Msum k ≤ Real.log k + C1 := by have := (abs_le.mp (hM k (by omega))).2; linarith
    have hstep1 : Msum k * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
        (Real.log k + C1) * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hMk hdiff_nn
    have hlog_ineq : 1 - Real.log k / Real.log ((k + 1 : ℕ) : ℝ) ≤
        Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log k) := by
      have h := Real.log_le_sub_one_of_pos (div_pos hlk hlk1)
      rw [Real.log_div hlk.ne' hlk1.ne'] at h
      linarith
    have hsimp : Real.log k * (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) =
        1 - Real.log k / Real.log ((k + 1 : ℕ) : ℝ) := by field_simp [hlk.ne']
    linarith
  have hsum_le := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum_le
  have htel1 : ∑ k ∈ Finset.Ico (a + 1) b,
      (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log k)) =
      Real.log (Real.log b) - Real.log (Real.log ((a + 1 : ℕ) : ℝ)) := by
    have := sum_Ico_sub_succ (fun k => -Real.log (Real.log k)) (a + 1) b hlt
    simpa [sub_neg_eq_add, neg_add_eq_sub] using this
  have htel2 : ∑ k ∈ Finset.Ico (a + 1) b, (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) =
      1 / Real.log ((a + 1 : ℕ) : ℝ) - 1 / Real.log b := by
    simpa using sum_Ico_sub_succ (fun k => 1 / Real.log k) (a + 1) b hlt
  rw [htel1, htel2] at hsum_le
  have hll_le : Real.log (Real.log b) - Real.log (Real.log ((a + 1 : ℕ) : ℝ)) ≤
      Real.log (Real.log b / Real.log a) := by
    rw [Real.log_div hlogb_pos.ne' hloga_pos.ne']
    have : Real.log (Real.log a) ≤ Real.log (Real.log ((a + 1 : ℕ) : ℝ)) :=
      Real.log_le_log hloga_pos hloga_le_a1
    linarith
  have hdiff_a1 : 1 - Real.log a / Real.log ((a + 1 : ℕ) : ℝ) ≤ 1 / Real.log a := by
    have hlog_step : Real.log ((a + 1 : ℕ) : ℝ) - Real.log a ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (a + 1 : ℕ)) (by positivity : (0 : ℝ) < a))
      rw [Real.log_div (by positivity) (by positivity)] at h
      have hle1 : ((a + 1 : ℕ) : ℝ) / (a : ℝ) - 1 ≤ 1 := by
        push_cast
        have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
        rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
        linarith
      linarith
    calc 1 - Real.log a / Real.log ((a + 1 : ℕ) : ℝ)
        = (Real.log ((a + 1 : ℕ) : ℝ) - Real.log a) / Real.log ((a + 1 : ℕ) : ℝ) := by
          field_simp [hlog_a1_pos.ne']
      _ ≤ 1 / Real.log ((a + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right hlog_step hlog_a1_pos.le
      _ ≤ 1 / Real.log a := one_div_le_one_div_of_le hloga_pos hloga_le_a1
  have hC1_tel : C1 * (1 / Real.log ((a + 1 : ℕ) : ℝ) - 1 / Real.log b) ≤ C1 / Real.log a := by
    have h1 : 1 / Real.log ((a + 1 : ℕ) : ℝ) - 1 / Real.log b ≤ 1 / Real.log a := by
      have := one_div_le_one_div_of_le hloga_pos hloga_le_a1
      have : 0 ≤ 1 / Real.log b := by positivity
      linarith
    calc C1 * (1 / Real.log ((a + 1 : ℕ) : ℝ) - 1 / Real.log b)
        ≤ C1 * (1 / Real.log a) := mul_le_mul_of_nonneg_left h1 hC1_pos.le
      _ = C1 / Real.log a := by ring
  have hsplit3 : (3 * C1 + 1) / Real.log a =
      C1 / Real.log a + C1 / Real.log a + 1 / Real.log a + C1 / Real.log a := by ring
  linarith

private lemma sum_log_div_p_Ioc_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      Real.log b - Real.log a - C ≤
        ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ) := by
  obtain ⟨C1, hC1_pos, hC1⟩ := mertens_first
  refine ⟨2 * C1, by positivity, fun a b ha hab => ?_⟩
  have hM : ∀ k : ℕ, 1 ≤ k → |Msum k - Real.log k| ≤ C1 := fun k hk => hC1 k hk
  have hsub : Nat.primesLE a ⊆ Nat.primesLE b := by
    intro p hp; rw [Nat.mem_primesLE] at hp ⊢; exact ⟨hp.1.trans hab, hp.2⟩
  have hsdiff : ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ) = Msum b - Msum a := by
    dsimp only [Msum]
    rw [Finset.sum_sdiff_eq_sub hsub]
  rw [hsdiff]
  have hb := (abs_le.mp (hM b (by omega))).1
  have ha' := (abs_le.mp (hM a (by omega))).2
  linarith

/- Section 4: Dirichlet Convolution Asymptotic for Hsum -/

private def tau : ℕ → ℕ → ℕ
  | 0, n => if n = 1 then 1 else 0
  | m + 1, n => ∑ d ∈ n.divisors, tau m d

private lemma tau_zero_right (m : ℕ) : tau m 0 = 0 := by
  cases m <;> simp [tau]

private lemma tau_one_apply {n : ℕ} (hn : 1 ≤ n) : tau 1 n = 1 := by
  simp only [tau]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro d _ hd1; simp [hd1]
  · intro h1; exact absurd (Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩) h1

private lemma tau_eq_zeta_pow (m n : ℕ) :
    (tau m n : ℤ) = ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ m) n := by
  induction m generalizing n with
  | zero =>
    simp [tau, ArithmeticFunction.one_apply]
  | succ m ih =>
    rw [pow_succ, ArithmeticFunction.coe_mul_zeta_apply]
    simp only [tau, Nat.cast_sum]
    exact Finset.sum_congr rfl fun d _ => ih d

private lemma sum_inv_Icc_bound (u : ℕ) (hu : 1 ≤ u) :
    |∑ n ∈ Finset.Icc 1 u, (1 : ℝ) / (n : ℝ) - Real.log u| ≤ 1 := by
  rw [abs_le]
  constructor
  · -- Lower bound: log u ≤ log (u + 1) ≤ ∑_{k=1}^u 1/k
    have hstep : ∀ k ∈ Finset.Icc 1 u, Real.log ((k + 1 : ℕ) : ℝ) - Real.log k ≤ 1 / (k : ℝ) := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk_pos : (0 : ℝ) < k := by positivity
      have h := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ)) hk_pos)
      rw [Real.log_div (by positivity) hk_pos.ne'] at h
      have hsub : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = 1 / (k : ℝ) := by push_cast; field_simp; ring
      linarith
    have hsum := Finset.sum_le_sum hstep
    have hIcc_Ico : Finset.Icc 1 u = Finset.Ico 1 (u + 1) := rfl
    have htel : ∑ k ∈ Finset.Icc 1 u, (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) =
        Real.log ((u + 1 : ℕ) : ℝ) := by
      rw [hIcc_Ico]
      have := sum_Ico_sub_succ (fun k => -Real.log k) 1 (u + 1) (by omega)
      simpa [sub_neg_eq_add, neg_add_eq_sub, Real.log_one] using this
    rw [htel] at hsum
    have hlu : Real.log u ≤ Real.log ((u + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ u)
    linarith
  · -- Upper bound: ∑_{k=1}^u 1/k = 1 + ∑_{k=2}^u 1/k ≤ 1 + log u
    have hsplit : ∑ n ∈ Finset.Icc 1 u, (1 : ℝ) / (n : ℝ) =
        1 + ∑ n ∈ Finset.Icc 2 u, (1 : ℝ) / (n : ℝ) := by
      have h1 : Finset.Icc 1 u = insert 1 (Finset.Icc 2 u) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp)]
      norm_num
    rw [hsplit]
    have hstep : ∀ k ∈ Finset.Icc 2 u, (1 : ℝ) / (k : ℝ) ≤ Real.log k - Real.log ((k - 1 : ℕ) : ℝ) := by
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk_pos : (0 : ℝ) < k := by positivity
      have hk1_pos : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
      have h := Real.log_le_sub_one_of_pos (div_pos hk1_pos hk_pos)
      rw [Real.log_div hk1_pos.ne' hk_pos.ne'] at h
      have hsub : 1 - ((k - 1 : ℕ) : ℝ) / (k : ℝ) = 1 / (k : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
        field_simp; ring
      linarith
    have hsum := Finset.sum_le_sum hstep
    have htel : ∑ k ∈ Finset.Icc 2 u, (Real.log k - Real.log ((k - 1 : ℕ) : ℝ)) = Real.log u := by
      rcases eq_or_lt_of_le hu with rfl | hgt
      · simp
      · have hbi : ∑ k ∈ Finset.Icc 2 u, (Real.log k - Real.log ((k - 1 : ℕ) : ℝ)) =
            ∑ k ∈ Finset.Ico 1 u, (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) := by
          apply Finset.sum_bij (fun k _ => k - 1)
          · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_Ico]; omega
          · intro k1 hk1 k2 hk2 heq; rw [Finset.mem_Icc] at hk1 hk2; omega
          · intro k hk; rw [Finset.mem_Ico] at hk; refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro k hk; rw [Finset.mem_Icc] at hk; rw [Nat.sub_add_cancel (by omega)]
        rw [hbi]
        have := sum_Ico_sub_succ (fun k => -Real.log k) 1 u hu
        simpa [sub_neg_eq_add, neg_add_eq_sub, Real.log_one] using this
    rw [htel] at hsum
    linarith

private lemma pow_sub_pow_bounds {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) * a ^ m * (b - a) ≤ b ^ (m + 1) - a ^ (m + 1) ∧
    b ^ (m + 1) - a ^ (m + 1) ≤ ((m + 1 : ℕ) : ℝ) * b ^ m * (b - a) := by
  have hgeom : b ^ (m + 1) - a ^ (m + 1) = (b - a) * ∑ j ∈ Finset.range (m + 1), b ^ j * a ^ (m - j) := by
    simpa [mul_comm] using (geom_sum₂_mul b a (m + 1)).symm
  rw [hgeom]
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hb : 0 ≤ b := ha.trans hab
  constructor
  · have hlo : ((m + 1 : ℕ) : ℝ) * a ^ m ≤ ∑ j ∈ Finset.range (m + 1), b ^ j * a ^ (m - j) := by
      calc ((m + 1 : ℕ) : ℝ) * a ^ m
          = ∑ _j ∈ Finset.range (m + 1), a ^ m := by simp
        _ ≤ ∑ j ∈ Finset.range (m + 1), b ^ j * a ^ (m - j) := by
            apply Finset.sum_le_sum
            intro j hj
            have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            calc a ^ m = a ^ j * a ^ (m - j) := by rw [← pow_add, Nat.add_sub_cancel' hjm]
              _ ≤ b ^ j * a ^ (m - j) :=
                mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab j) (pow_nonneg ha _)
    nlinarith
  · have hhi : ∑ j ∈ Finset.range (m + 1), b ^ j * a ^ (m - j) ≤ ((m + 1 : ℕ) : ℝ) * b ^ m := by
      calc ∑ j ∈ Finset.range (m + 1), b ^ j * a ^ (m - j)
          ≤ ∑ _j ∈ Finset.range (m + 1), b ^ m := by
            apply Finset.sum_le_sum
            intro j hj
            have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            calc b ^ j * a ^ (m - j) ≤ b ^ j * b ^ (m - j) :=
                  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab _) (pow_nonneg hb _)
              _ = b ^ m := by rw [← pow_add, Nat.add_sub_cancel' hjm]
        _ = ((m + 1 : ℕ) : ℝ) * b ^ m := by simp
    nlinarith

private lemma sum_inv_mul_log_sub_pow (m u : ℕ) (hu : 1 ≤ u) :
    (Real.log u) ^ (m + 1) / ((m + 1 : ℕ) : ℝ) ≤
      ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m ∧
    ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m ≤
      (Real.log u) ^ (m + 1) / ((m + 1 : ℕ) : ℝ) + (Real.log u) ^ m := by
  have hm1_pos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  constructor
  · -- Lower bound via d ∈ Ico 1 u
    have hdrop : ∑ d ∈ Finset.Ico 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m ≤
        ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd; rw [Finset.mem_Ico] at hd; rw [Finset.mem_Icc]; omega
      · intro d hd _
        rw [Finset.mem_Icc] at hd
        have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd.1
        have hle : Real.log d ≤ Real.log u := Real.log_le_log hd_pos (by exact_mod_cast hd.2)
        exact mul_nonneg (by positivity) (pow_nonneg (sub_nonneg.mpr hle) m)
    have hterm : ∀ d ∈ Finset.Ico 1 u,
        ((Real.log u - Real.log d) ^ (m + 1) - (Real.log u - Real.log ((d + 1 : ℕ) : ℝ)) ^ (m + 1)) /
          ((m + 1 : ℕ) : ℝ) ≤
        (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m := by
      intro d hd
      rw [Finset.mem_Ico] at hd
      have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd.1
      have hd1_pos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
      have ha_nn : 0 ≤ Real.log u - Real.log ((d + 1 : ℕ) : ℝ) :=
        sub_nonneg.mpr (Real.log_le_log hd1_pos (by exact_mod_cast hd.2))
      have hab : Real.log u - Real.log ((d + 1 : ℕ) : ℝ) ≤ Real.log u - Real.log d := by
        have hle : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ d
        have := Real.log_le_log hd_pos hle
        linarith
      have hpow := (pow_sub_pow_bounds ha_nn hab m).2
      have hdiff : (Real.log u - Real.log d) - (Real.log u - Real.log ((d + 1 : ℕ) : ℝ)) ≤ 1 / (d : ℝ) := by
        have h := Real.log_le_sub_one_of_pos (div_pos hd1_pos hd_pos)
        rw [Real.log_div hd1_pos.ne' hd_pos.ne'] at h
        have hsub : ((d + 1 : ℕ) : ℝ) / (d : ℝ) - 1 = 1 / (d : ℝ) := by push_cast; field_simp; ring
        linarith
      have hbn : 0 ≤ (Real.log u - Real.log d) ^ m := pow_nonneg (ha_nn.trans hab) m
      rw [div_le_iff₀ hm1_pos]
      calc (Real.log u - Real.log d) ^ (m + 1) - (Real.log u - Real.log ((d + 1 : ℕ) : ℝ)) ^ (m + 1)
          ≤ ((m + 1 : ℕ) : ℝ) * (Real.log u - Real.log d) ^ m *
              ((Real.log u - Real.log d) - (Real.log u - Real.log ((d + 1 : ℕ) : ℝ))) := hpow
        _ ≤ ((m + 1 : ℕ) : ℝ) * (Real.log u - Real.log d) ^ m * (1 / (d : ℝ)) :=
            mul_le_mul_of_nonneg_left hdiff (mul_nonneg hm1_pos.le hbn)
        _ = (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m * ((m + 1 : ℕ) : ℝ) := by ring
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.sum_div] at hsum
    have htel : ∑ d ∈ Finset.Ico 1 u,
        ((Real.log u - Real.log d) ^ (m + 1) - (Real.log u - Real.log ((d + 1 : ℕ) : ℝ)) ^ (m + 1)) =
        (Real.log u) ^ (m + 1) := by
      have := sum_Ico_sub_succ (fun d => (Real.log u - Real.log d) ^ (m + 1)) 1 u hu
      simpa [Real.log_one, sub_zero, sub_self, zero_pow (Nat.succ_ne_zero m)] using this
    rw [htel] at hsum
    exact hsum.trans hdrop
  · -- Upper bound: split d = 1 and d ∈ Icc 2 u
    have hsplit : ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m =
        (Real.log u) ^ m + ∑ d ∈ Finset.Icc 2 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m := by
      have h1 : Finset.Icc 1 u = insert 1 (Finset.Icc 2 u) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [h1, Finset.sum_insert (by simp)]
      simp [Real.log_one]
    rw [hsplit]
    have hterm : ∀ d ∈ Finset.Icc 2 u,
        (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m ≤
        ((Real.log u - Real.log ((d - 1 : ℕ) : ℝ)) ^ (m + 1) - (Real.log u - Real.log d) ^ (m + 1)) /
          ((m + 1 : ℕ) : ℝ) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
      have hd1_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have ha_nn : 0 ≤ Real.log u - Real.log d :=
        sub_nonneg.mpr (Real.log_le_log hd_pos (by exact_mod_cast hd.2))
      have hab : Real.log u - Real.log d ≤ Real.log u - Real.log ((d - 1 : ℕ) : ℝ) := by
        have hle : ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show d - 1 ≤ d by omega)
        have := Real.log_le_log hd1_pos hle
        linarith
      have hpow := (pow_sub_pow_bounds ha_nn hab m).1
      have hdiff : 1 / (d : ℝ) ≤ (Real.log u - Real.log ((d - 1 : ℕ) : ℝ)) - (Real.log u - Real.log d) := by
        have h := Real.log_le_sub_one_of_pos (div_pos hd1_pos hd_pos)
        rw [Real.log_div hd1_pos.ne' hd_pos.ne'] at h
        have hsub : 1 - ((d - 1 : ℕ) : ℝ) / (d : ℝ) = 1 / (d : ℝ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]; field_simp; ring
        linarith
      have han : 0 ≤ (Real.log u - Real.log d) ^ m := pow_nonneg ha_nn m
      rw [le_div_iff₀ hm1_pos]
      calc (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ m * ((m + 1 : ℕ) : ℝ)
          = ((m + 1 : ℕ) : ℝ) * (Real.log u - Real.log d) ^ m * (1 / (d : ℝ)) := by ring
        _ ≤ ((m + 1 : ℕ) : ℝ) * (Real.log u - Real.log d) ^ m *
              ((Real.log u - Real.log ((d - 1 : ℕ) : ℝ)) - (Real.log u - Real.log d)) :=
            mul_le_mul_of_nonneg_left hdiff (mul_nonneg hm1_pos.le han)
        _ ≤ (Real.log u - Real.log ((d - 1 : ℕ) : ℝ)) ^ (m + 1) - (Real.log u - Real.log d) ^ (m + 1) := hpow
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.sum_div] at hsum
    have htel : ∑ d ∈ Finset.Icc 2 u,
        ((Real.log u - Real.log ((d - 1 : ℕ) : ℝ)) ^ (m + 1) - (Real.log u - Real.log d) ^ (m + 1)) =
        (Real.log u) ^ (m + 1) := by
      rcases eq_or_lt_of_le hu with rfl | hgt
      · simp [Real.log_one, zero_pow (Nat.succ_ne_zero m)]
      · have hbi : ∑ d ∈ Finset.Icc 2 u,
            ((Real.log u - Real.log ((d - 1 : ℕ) : ℝ)) ^ (m + 1) - (Real.log u - Real.log d) ^ (m + 1)) =
            ∑ k ∈ Finset.Ico 1 u,
              ((Real.log u - Real.log k) ^ (m + 1) - (Real.log u - Real.log ((k + 1 : ℕ) : ℝ)) ^ (m + 1)) := by
          apply Finset.sum_bij (fun d _ => d - 1)
          · intro d hd; rw [Finset.mem_Icc] at hd; rw [Finset.mem_Ico]; omega
          · intro d1 hd1 d2 hd2 heq; rw [Finset.mem_Icc] at hd1 hd2; omega
          · intro k hk; rw [Finset.mem_Ico] at hk; refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro d hd; rw [Finset.mem_Icc] at hd; rw [Nat.sub_add_cancel (by omega)]
        rw [hbi]
        have := sum_Ico_sub_succ (fun k => (Real.log u - Real.log k) ^ (m + 1)) 1 u hu
        simpa [Real.log_one, sub_zero, sub_self, zero_pow (Nat.succ_ne_zero m)] using this
    rw [htel] at hsum
    linarith

private lemma sum_tau_div_id (m : ℕ) (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℕ, 1 ≤ u →
      |∑ n ∈ Finset.Icc 1 u, (tau m n : ℝ) / (n : ℝ) -
        (Real.log u) ^ m / (m.factorial : ℝ)| ≤ K * (Real.log u + 1) ^ (m - 1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · refine ⟨1, one_pos, fun u hu => ?_⟩
      have hcongr : ∑ n ∈ Finset.Icc 1 u, (tau 1 n : ℝ) / (n : ℝ) =
          ∑ n ∈ Finset.Icc 1 u, (1 : ℝ) / (n : ℝ) := by
        refine Finset.sum_congr rfl fun n hn => by rw [tau_one_apply (Finset.mem_Icc.mp hn).1]; norm_num
      rw [hcongr]
      simpa using sum_inv_Icc_bound u hu
    · obtain ⟨Km, hKm_pos, hKm⟩ := ih (by omega)
      let M := m + 1
      have hM_pos : 1 ≤ M := by omega
      refine ⟨Km + 2 + ((M : ℝ) * Real.log 2 + 1) / (M.factorial : ℝ), by positivity, fun u hu => ?_⟩
      -- Double sum swap: ∑_{n=1}^u tau (M+1) n / n = ∑_{d=1}^u (1/d) * ∑_{q=1}^{u/d} tau M q / q
      have hswap : ∑ n ∈ Finset.Icc 1 u, (tau (M + 1) n : ℝ) / (n : ℝ) =
          ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) *
            (∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ)) := by
        have h1 : ∀ n ∈ Finset.Icc 1 u, (tau (M + 1) n : ℝ) / (n : ℝ) =
            ∑ d ∈ n.divisors, (1 / ((n / d : ℕ) : ℝ)) * ((tau M d : ℝ) / (d : ℝ)) := by
          intro n hn
          have hn_pos : 0 < n := (Finset.mem_Icc.mp hn).1
          simp only [tau, Nat.cast_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun q hq => ?_
          have hqn := Nat.dvd_of_mem_divisors hq
          have hq_pos : 0 < q := Nat.pos_of_dvd_of_pos hqn hn_pos
          have hmul : (n : ℝ) = (q : ℝ) * ((n / q : ℕ) : ℝ) := by
            exact_mod_cast (Nat.mul_div_cancel' hqn).symm
          rw [hmul]
          have hqp : (q : ℝ) ≠ 0 := by positivity
          have hnd : ((n / q : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.div_pos (Nat.le_of_dvd hn_pos hqn) hq_pos).ne'
          field_simp
        rw [Finset.sum_congr rfl h1]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_sigma', Finset.sum_sigma']
        apply Finset.sum_bij (fun nq _ => ⟨nq.1 / nq.2, nq.2⟩)
        · intro nq hnq
          rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hnq
          rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc]
          have hq_pos : 0 < nq.2 := Nat.pos_of_dvd_of_pos hnq.2.1 hnq.1.1
          have hd_pos : 0 < nq.1 / nq.2 := Nat.div_pos (Nat.le_of_dvd hnq.1.1 hnq.2.1) hq_pos
          have hd_le : nq.1 / nq.2 ≤ u := (Nat.div_le_self nq.1 nq.2).trans hnq.1.2
          have hq_le : nq.2 ≤ u / (nq.1 / nq.2) := by
            rw [Nat.le_div_iff_mul_le hd_pos]
            rw [Nat.mul_div_cancel' hnq.2.1]
            exact hnq.1.2
          exact ⟨⟨hd_pos, hd_le⟩, ⟨hq_pos, hq_le⟩⟩
        · intro a ha b hb heq
          rw [Finset.mem_sigma, Nat.mem_divisors] at ha hb
          have h1 : a.1 / a.2 = b.1 / b.2 := congrArg Sigma.fst heq
          have h2 : a.2 = b.2 := congrArg Sigma.snd heq
          have ha1 : a.1 = a.2 * (a.1 / a.2) := (Nat.mul_div_cancel' ha.2.1).symm
          have hb1 : b.1 = b.2 * (b.1 / b.2) := (Nat.mul_div_cancel' hb.2.1).symm
          exact Sigma.ext (by rw [ha1, hb1, h1, h2]) (by simp [h2])
        · intro dq hdq
          rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc] at hdq
          have hd_pos : 0 < dq.1 := hdq.1.1
          have hq_pos : 0 < dq.2 := hdq.2.1
          have hprod_le : dq.1 * dq.2 ≤ u := by
            rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd_pos).mp hdq.2.2
          have hprod_pos : 0 < dq.1 * dq.2 := Nat.mul_pos hd_pos hq_pos
          refine ⟨⟨dq.1 * dq.2, dq.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hprod_pos, hprod_le⟩,
            Nat.mem_divisors.mpr ⟨dvd_mul_left dq.2 dq.1, hprod_pos.ne'⟩⟩, ?_⟩
          exact Sigma.ext (Nat.mul_div_cancel dq.1 hq_pos) (by simp)
        · intro _ _; rfl
      rw [hswap]
      have hlu_nn : 0 ≤ Real.log u := Real.log_nonneg (by exact_mod_cast hu)
      have hsum_inv : ∑ d ∈ Finset.Icc 1 u, (1 : ℝ) / (d : ℝ) ≤ Real.log u + 1 := by
        have := (abs_le.mp (sum_inv_Icc_bound u hu)).2; linarith
      have hfac_pos : (0 : ℝ) < M.factorial := by positivity
      -- Bound difference between inner sum and (log u - log d)^M / M!
      have hinner_diff : ∀ d ∈ Finset.Icc 1 u,
          |∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ) -
            (Real.log u - Real.log d) ^ M / (M.factorial : ℝ)| ≤
          Km * (Real.log u + 1) ^ (M - 1) +
          ((M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ (M - 1) := by
        intro d hd
        rw [Finset.mem_Icc] at hd
        have hud_pos : 1 ≤ u / d := Nat.div_pos hd.2 hd.1
        have hud_r : (0 : ℝ) < ((u / d : ℕ) : ℝ) := Nat.cast_pos.mpr hud_pos
        have hih := hKm (u / d) hud_pos
        have hlog_ud_le : Real.log ((u / d : ℕ) : ℝ) ≤ Real.log u :=
          Real.log_le_log hud_r (by exact_mod_cast Nat.div_le_self u d)
        have hlog_ud_nn : 0 ≤ Real.log ((u / d : ℕ) : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hud_pos)
        have hih_u : |∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ) -
            (Real.log ((u / d : ℕ) : ℝ)) ^ M / (M.factorial : ℝ)| ≤
            Km * (Real.log u + 1) ^ (M - 1) :=
          hih.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) (by linarith) _) hKm_pos.le)
        -- Compare Real.log (u / d : ℕ) with Real.log u - Real.log d
        have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd.1
        have hu_pos : (0 : ℝ) < u := Nat.cast_pos.mpr hu
        have hlog_le : Real.log ((u / d : ℕ) : ℝ) ≤ Real.log u - Real.log d := by
          rw [← Real.log_div hu_pos.ne' hd_pos.ne']
          apply Real.log_le_log hud_r
          rw [le_div_iff₀ hd_pos]
          exact_mod_cast Nat.div_mul_le_self u d
        have hlog_gap : (Real.log u - Real.log d) - Real.log ((u / d : ℕ) : ℝ) ≤ Real.log 2 := by
          have h2 : (u : ℝ) ≤ 2 * ((u / d : ℕ) : ℝ) * (d : ℝ) := by
            have hnat : u < (u / d + 1) * d := by
              have := Nat.div_add_mod u d
              have := Nat.mod_lt u hd.1
              nlinarith
            have hnat2 : u / d + 1 ≤ 2 * (u / d) := by omega
            have hnat3 : u ≤ 2 * (u / d) * d := by nlinarith
            exact_mod_cast hnat3
          have hdiv2 : (u : ℝ) / (d : ℝ) ≤ 2 * ((u / d : ℕ) : ℝ) := by
            rw [div_le_iff₀ hd_pos]; linarith
          have hlg := Real.log_le_log (div_pos hu_pos hd_pos) hdiv2
          rw [Real.log_div hu_pos.ne' hd_pos.ne', Real.log_mul (by norm_num) hud_r.ne'] at hlg
          linarith
        have hpow_gap : |(Real.log ((u / d : ℕ) : ℝ)) ^ M - (Real.log u - Real.log d) ^ M| ≤
            (M : ℝ) * Real.log 2 * (Real.log u + 1) ^ (M - 1) := by
          have hMsub : M = (M - 1) + 1 := by omega
          have hpb := (pow_sub_pow_bounds hlog_ud_nn hlog_le (M - 1)).2
          rw [← hMsub] at hpb
          have hle0 : (Real.log ((u / d : ℕ) : ℝ)) ^ M ≤ (Real.log u - Real.log d) ^ M :=
            pow_le_pow_left₀ hlog_ud_nn hlog_le M
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle0)]
          have hsub_le : Real.log u - Real.log d ≤ Real.log u + 1 := by
            have : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd.1)
            linarith
          have hpow_le : (Real.log u - Real.log d) ^ (M - 1) ≤ (Real.log u + 1) ^ (M - 1) :=
            pow_le_pow_left₀ (hlog_ud_nn.trans hlog_le) hsub_le (M - 1)
          have hMnn : (0 : ℝ) ≤ M := by positivity
          calc (Real.log u - Real.log d) ^ M - (Real.log ((u / d : ℕ) : ℝ)) ^ M
              ≤ (M : ℝ) * (Real.log u - Real.log d) ^ (M - 1) *
                  ((Real.log u - Real.log d) - Real.log ((u / d : ℕ) : ℝ)) := hpb
            _ ≤ (M : ℝ) * (Real.log u + 1) ^ (M - 1) * Real.log 2 := by
                have hgap_nn : 0 ≤ (Real.log u - Real.log d) - Real.log ((u / d : ℕ) : ℝ) :=
                  sub_nonneg.mpr hlog_le
                have h1 : (M : ℝ) * (Real.log u - Real.log d) ^ (M - 1) ≤
                    (M : ℝ) * (Real.log u + 1) ^ (M - 1) :=
                  mul_le_mul_of_nonneg_left hpow_le hMnn
                exact mul_le_mul h1 hlog_gap hgap_nn (by positivity)
            _ = (M : ℝ) * Real.log 2 * (Real.log u + 1) ^ (M - 1) := by ring
        have htri : |∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ) -
            (Real.log u - Real.log d) ^ M / (M.factorial : ℝ)| ≤
            |∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ) -
              (Real.log ((u / d : ℕ) : ℝ)) ^ M / (M.factorial : ℝ)| +
            |(Real.log ((u / d : ℕ) : ℝ)) ^ M / (M.factorial : ℝ) -
              (Real.log u - Real.log d) ^ M / (M.factorial : ℝ)| := abs_sub_le _ _ _
        have hdiv_gap : |(Real.log ((u / d : ℕ) : ℝ)) ^ M / (M.factorial : ℝ) -
            (Real.log u - Real.log d) ^ M / (M.factorial : ℝ)| ≤
            ((M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ (M - 1) := by
          rw [← sub_div, abs_div, abs_of_pos hfac_pos]
          calc |(Real.log ((u / d : ℕ) : ℝ)) ^ M - (Real.log u - Real.log d) ^ M| / (M.factorial : ℝ)
              ≤ ((M : ℝ) * Real.log 2 * (Real.log u + 1) ^ (M - 1)) / (M.factorial : ℝ) :=
                div_le_div_of_nonneg_right hpow_gap hfac_pos.le
            _ = _ := by ring
        linarith
      -- Combine with sum_inv_mul_log_sub_pow M u hu
      have hmain_b := sum_inv_mul_log_sub_pow M u hu
      have hfac_succ : ((M + 1).factorial : ℝ) = ((M + 1 : ℕ) : ℝ) * (M.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hmain_err : |∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * ((Real.log u - Real.log d) ^ M / (M.factorial : ℝ)) -
          (Real.log u) ^ (M + 1) / ((M + 1).factorial : ℝ)| ≤
          (1 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by
        have hrew : ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * ((Real.log u - Real.log d) ^ M / (M.factorial : ℝ)) =
            (∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ M) / (M.factorial : ℝ) := by
          rw [Finset.sum_div]; refine Finset.sum_congr rfl fun d _ => by ring
        rw [hrew, hfac_succ, abs_le]
        have hluM : (Real.log u) ^ M ≤ (Real.log u + 1) ^ M :=
          pow_le_pow_left₀ hlu_nn (by linarith) M
        constructor
        · have h1 : (Real.log u) ^ (M + 1) / (((M + 1 : ℕ) : ℝ) * (M.factorial : ℝ)) ≤
              (∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ M) / (M.factorial : ℝ) := by
            rw [← div_div]
            exact div_le_div_of_nonneg_right hmain_b.1 hfac_pos.le
          have hnn : 0 ≤ (1 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by positivity
          linarith
        · have h1 : (∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (Real.log u - Real.log d) ^ M) / (M.factorial : ℝ) ≤
              (Real.log u) ^ (M + 1) / (((M + 1 : ℕ) : ℝ) * (M.factorial : ℝ)) +
              (Real.log u) ^ M / (M.factorial : ℝ) := by
            have := div_le_div_of_nonneg_right hmain_b.2 hfac_pos.le
            rw [add_div, div_div] at this
            exact this
          have h2 : (Real.log u) ^ M / (M.factorial : ℝ) ≤ (1 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by
            rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hluM hfac_pos.le
          linarith
      have htot_diff : |∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ)) -
          ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * ((Real.log u - Real.log d) ^ M / (M.factorial : ℝ))| ≤
          (Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by
        rw [← Finset.sum_sub_distrib]
        calc |∑ d ∈ Finset.Icc 1 u, ((1 / (d : ℝ)) * (∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ)) -
                (1 / (d : ℝ)) * ((Real.log u - Real.log d) ^ M / (M.factorial : ℝ)))|
            ≤ ∑ d ∈ Finset.Icc 1 u, |(1 / (d : ℝ)) * (∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ)) -
                (1 / (d : ℝ)) * ((Real.log u - Real.log d) ^ M / (M.factorial : ℝ))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) *
                ((Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ (M - 1)) := by
              apply Finset.sum_le_sum
              intro d hd
              rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (d : ℝ))]
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have := hinner_diff d hd
              linarith
          _ = (∑ d ∈ Finset.Icc 1 u, (1 : ℝ) / (d : ℝ)) *
                ((Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ (M - 1)) := by
              rw [← Finset.sum_mul]
          _ ≤ (Real.log u + 1) *
                ((Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ (M - 1)) := by
              exact mul_le_mul_of_nonneg_right hsum_inv (by positivity)
          _ = (Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by
              have hpowM : (Real.log u + 1) * (Real.log u + 1) ^ (M - 1) = (Real.log u + 1) ^ M := by
                rw [← pow_succ', Nat.sub_add_cancel hM_pos]
              calc (Real.log u + 1) * ((Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) *
                      (Real.log u + 1) ^ (M - 1))
                  = (Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) *
                      ((Real.log u + 1) * (Real.log u + 1) ^ (M - 1)) := by ring
                _ = (Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by
                    rw [hpowM]
      have htri := abs_sub_le
        (∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * (∑ q ∈ Finset.Icc 1 (u / d), (tau M q : ℝ) / (q : ℝ)))
        (∑ d ∈ Finset.Icc 1 u, (1 / (d : ℝ)) * ((Real.log u - Real.log d) ^ M / (M.factorial : ℝ)))
        ((Real.log u) ^ (M + 1) / ((M + 1).factorial : ℝ))
      have hM_sub : M + 1 - 1 = M := rfl
      rw [hM_sub]
      have hcomb : (Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M +
          (1 / (M.factorial : ℝ)) * (Real.log u + 1) ^ M ≤
          (Km + 2 + ((M : ℝ) * Real.log 2 + 1) / (M.factorial : ℝ)) * (Real.log u + 1) ^ M := by
        have hnn : 0 ≤ (Real.log u + 1) ^ M := by positivity
        nlinarith [show (Km + (M : ℝ) * Real.log 2 / (M.factorial : ℝ)) + 1 / (M.factorial : ℝ) =
            Km + ((M : ℝ) * Real.log 2 + 1) / (M.factorial : ℝ) by ring]
      linarith

/-- Multiplicative arithmetic functions for the Dirichlet convolution `a = c * b`. -/
private def aArith : ArithmeticFunction ℝ where
  toFun n := if Squarefree n ∧ 1 ≤ n then 1 / phiG n else 0
  map_zero' := by simp

private def mu8Z : ArithmeticFunction ℤ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ 8

private def mu8Div : ArithmeticFunction ℝ where
  toFun n := (mu8Z n : ℝ) / (n : ℝ)
  map_zero' := by simp

private def bArith : ArithmeticFunction ℝ where
  toFun n := (tau 8 n : ℝ) / (n : ℝ)
  map_zero' := by simp [tau_zero_right]

private def cArith : ArithmeticFunction ℝ := aArith * mu8Div

private lemma aArith_isMult : aArith.IsMultiplicative := by
  refine ⟨by simp [aArith, phiG_one], fun {m n} hcop => ?_⟩
  by_cases hm : Squarefree m ∧ 1 ≤ m
  · by_cases hn : Squarefree n ∧ 1 ≤ n
    · have hmn : Squarefree (m * n) ∧ 1 ≤ m * n :=
        ⟨(Nat.squarefree_mul hcop).mpr ⟨hm.1, hn.1⟩, Nat.mul_pos hm.2 hn.2⟩
      simp only [aArith, ArithmeticFunction.coe_mk, hm, hn, hmn, and_self, ↓reduceIte,
        phiG_mul_coprime hcop]
      ring
    · have hmn : ¬ (Squarefree (m * n) ∧ 1 ≤ m * n) := by
        rintro ⟨hsf, hpos⟩
        exact hn ⟨hsf.squarefree_of_dvd (dvd_mul_left n m), Nat.pos_of_mul_pos_left hpos⟩
      simp [aArith, hm, hn, hmn]
  · have hmn : ¬ (Squarefree (m * n) ∧ 1 ≤ m * n) := by
      rintro ⟨hsf, hpos⟩
      exact hm ⟨hsf.squarefree_of_dvd (dvd_mul_right m n), Nat.pos_of_mul_pos_right hpos⟩
    simp [aArith, hm, hmn]

private lemma isMult_pow {R : Type*} [CommSemiring R] {f : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (k : ℕ) : (f ^ k).IsMultiplicative := by
  induction k with
  | zero => exact ArithmeticFunction.isMultiplicative_one
  | succ k ih => rw [pow_succ]; exact ih.mul hf

private lemma mu8Z_isMult : mu8Z.IsMultiplicative :=
  isMult_pow ArithmeticFunction.isMultiplicative_moebius 8

private lemma mu8Div_isMult : mu8Div.IsMultiplicative := by
  refine ⟨by simp [mu8Div, mu8Z_isMult.map_one], fun {m n} hcop => ?_⟩
  simp only [mu8Div, ArithmeticFunction.coe_mk, mu8Z_isMult.map_mul_of_coprime hcop,
    Int.cast_mul, Nat.cast_mul]
  ring

private lemma cArith_isMult : cArith.IsMultiplicative :=
  aArith_isMult.mul mu8Div_isMult

private lemma mu8Div_mul_bArith : mu8Div * bArith = 1 := by
  ext n
  by_cases hn0 : n = 0
  · subst hn0; simp
  rw [ArithmeticFunction.mul_apply]
  have h1 : ∑ x ∈ n.divisorsAntidiagonal, mu8Div x.1 * bArith x.2 =
      ((∑ x ∈ n.divisorsAntidiagonal, mu8Z x.1 * ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 8) x.2 : ℤ) : ℝ) /
        (n : ℝ) := by
    rw [Int.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hx
    simp only [mu8Div, bArith, ArithmeticFunction.coe_mk, ← tau_eq_zeta_pow 8 x.2]
    have hmul : (x.1 : ℝ) * (x.2 : ℝ) = (n : ℝ) := by exact_mod_cast hx.1
    rw [← hmul]
    push_cast
    ring
  rw [h1]
  have hconv : ∑ x ∈ n.divisorsAntidiagonal,
      mu8Z x.1 * ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 8) x.2 =
      (1 : ArithmeticFunction ℤ) n := by
    rw [← ArithmeticFunction.mul_apply, mu8Z, ← mul_pow,
      ArithmeticFunction.moebius_mul_coe_zeta, one_pow]
  rw [hconv]
  by_cases hn1 : n = 1
  · subst hn1; simp
  · simp [hn1]

private lemma cArith_mul_bArith : cArith * bArith = aArith := by
  rw [cArith, mul_assoc, mu8Div_mul_bArith, mul_one]

private lemma moebius_pow_prime_pow (m : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) (p ^ k) =
      (-1 : ℤ) ^ k * (Nat.choose m k : ℤ) := by
  induction m generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k => simp [hp.ne_one]
  | succ m ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply]
    rw [Nat.sum_divisorsAntidiagonal (f := fun a b =>
      ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) a * ArithmeticFunction.moebius b)]
    rw [Nat.sum_divisors_prime_pow hp]
    cases k with
    | zero =>
      rw [Finset.sum_range_one]
      simp only [pow_zero, Nat.div_one, ArithmeticFunction.moebius_apply_one, mul_one,
        Nat.choose_zero_right, Nat.cast_one]
      exact (isMult_pow ArithmeticFunction.isMultiplicative_moebius m).map_one
    | succ k =>
      have hsub : ∀ i ∈ Finset.range (k + 2),
          ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) (p ^ i) *
            ArithmeticFunction.moebius (p ^ (k + 1) / p ^ i) =
          if i = k + 1 then ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) (p ^ (k + 1))
          else if i = k then -((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) (p ^ k)
          else 0 := by
        intro i hi
        have hi_le : i ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [Nat.pow_div hi_le hp.pos]
        split_ifs with h1 h2
        · subst h1; simp
        · subst h2; simp [ArithmeticFunction.moebius_apply_prime hp]
        · have hge2 : 2 ≤ k + 1 - i := by omega
          have hnsq : ¬ Squarefree (p ^ (k + 1 - i)) := by
            intro hsf
            have hp2 : p * p ∣ p ^ (k + 1 - i) := by
              rw [← sq]; exact pow_dvd_pow p hge2
            exact hp.not_isUnit (hsf p hp2)
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq, mul_zero]
      rw [Finset.sum_congr rfl hsub]
      have hsplit : Finset.range (k + 2) =
          insert (k + 1) (insert k ((Finset.range (k + 2)).filter (fun i => i < k))) := by
        ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_filter]; omega
      rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
      have hrest : ∑ i ∈ (Finset.range (k + 2)).filter (fun i => i < k),
          (if i = k + 1 then ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) (p ^ (k + 1))
           else if i = k then -((ArithmeticFunction.moebius : ArithmeticFunction ℤ) ^ m) (p ^ k)
           else 0) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hlt : i < k := (Finset.mem_filter.mp hi).2
        rw [if_neg (by omega), if_neg (by omega)]
      rw [hrest, add_zero, if_pos rfl, if_neg (by omega), if_pos rfl, ih (k + 1), ih k,
        Nat.choose_succ_succ]
      push_cast
      ring

private lemma cArith_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    cArith (p ^ k) =
      if k = 0 then 1
      else (-1 : ℝ) ^ k * (Nat.choose 8 k : ℝ) / (p : ℝ) ^ k +
        (1 / phiG p) * ((-1 : ℝ) ^ (k - 1) * (Nat.choose 8 (k - 1) : ℝ) / (p : ℝ) ^ (k - 1)) := by
  cases k with
  | zero => simp [cArith_isMult.map_one]
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [cArith, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (f := fun a b => aArith a * mu8Div b),
      Nat.sum_divisors_prime_pow hp]
    -- Only i = 0 and i = 1 survive in aArith (p^i)
    have hsplit : Finset.range (k + 2) = insert 0 (insert 1 ((Finset.range (k + 2)).filter (fun i => 2 ≤ i))) := by
      ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_filter]; omega
    rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    have hrest : ∑ i ∈ (Finset.range (k + 2)).filter (fun i => 2 ≤ i),
        aArith (p ^ i) * mu8Div (p ^ (k + 1) / p ^ i) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi2 : 2 ≤ i := (Finset.mem_filter.mp hi).2
      have hnsq : ¬ Squarefree (p ^ i) := by
        intro hsf
        exact hp.not_isUnit (hsf p (by rw [← sq]; exact pow_dvd_pow p hi2))
      simp [aArith, hnsq]
    rw [hrest, add_zero]
    have ha0 : aArith (p ^ 0) = 1 := by simp [aArith, phiG_one]
    have ha1 : aArith (p ^ 1) = 1 / phiG p := by simp [aArith, hp.squarefree, hp.one_le]
    rw [ha0, one_mul, ha1, pow_zero, Nat.div_one, pow_one,
      pow_succ, Nat.mul_div_cancel _ hp.pos]
    rw [← pow_succ]
    simp only [mu8Div, ArithmeticFunction.coe_mk, mu8Z, moebius_pow_prime_pow 8 hp]
    push_cast
    ring

private lemma cArith_prime_pow_eq_zero {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 10 ≤ k) :
    cArith (p ^ k) = 0 := by
  rw [cArith_prime_pow hp k, if_neg (by omega)]
  have h1 : Nat.choose 8 k = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have h2 : Nat.choose 8 (k - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [h1, h2]

private lemma sum_cArith_prime_pows {p : ℕ} (hp : p.Prime) :
    ∑ k ∈ Finset.range 10, cArith (p ^ k) =
      (1 + 1 / phiG p) * (1 - 1 / (p : ℝ)) ^ 8 := by
  have hbin : (1 - 1 / (p : ℝ)) ^ 8 =
      ∑ k ∈ Finset.range 9, (-1 : ℝ) ^ k * (Nat.choose 8 k : ℝ) / (p : ℝ) ^ k := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one, neg_pow, one_div_pow]
    ring
  rw [hbin, add_mul, one_mul, Finset.mul_sum, Finset.sum_range_succ']
  rw [pow_zero, cArith_isMult.map_one]
  have hterm : ∀ k ∈ Finset.range 9,
      cArith (p ^ (k + 1)) =
        (-1 : ℝ) ^ (k + 1) * (Nat.choose 8 (k + 1) : ℝ) / (p : ℝ) ^ (k + 1) +
        (1 / phiG p) * ((-1 : ℝ) ^ k * (Nat.choose 8 k : ℝ) / (p : ℝ) ^ k) := by
    intro k _
    rw [cArith_prime_pow hp (k + 1)]
    simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hlhs_shift : ∑ k ∈ Finset.range 9,
      (-1 : ℝ) ^ (k + 1) * (Nat.choose 8 (k + 1) : ℝ) / (p : ℝ) ^ (k + 1) + 1 =
      ∑ k ∈ Finset.range 9, (-1 : ℝ) ^ k * (Nat.choose 8 k : ℝ) / (p : ℝ) ^ k := by
    rw [Finset.sum_range_succ, show Nat.choose 8 9 = 0 by decide]
    simp only [Nat.cast_zero, mul_zero, zero_div, add_zero]
    conv_rhs => rw [Finset.sum_range_succ']
    simp
  linarith

private lemma cArith_prime_rpow_bound {p : ℕ} (hp : p.Prime) (hp59 : 59 < p) :
    ∑ k ∈ Finset.Icc 1 9, |cArith (p ^ k)| * ((p ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤
      50000 / (p : ℝ) ^ ((3 : ℝ) / 2) := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp60 : (60 : ℝ) ≤ p := by exact_mod_cast (show 60 ≤ p by omega)
  have hom : omegaP p = 8 := omegaP_eq_eight hp hp59
  have hphi : 1 / phiG p = 8 / ((p : ℝ) - 8) := by
    rw [phiG_prime hp, hom]; push_cast; field_simp
  have hp8_ge : (p : ℝ) / 2 ≤ (p : ℝ) - 8 := by linarith
  have hp8_pos : (0 : ℝ) < (p : ℝ) - 8 := by linarith
  have hsplit : Finset.Icc 1 9 = insert 1 (Finset.Icc 2 9) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have hk1 : |cArith (p ^ 1)| * ((p ^ 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤
      128 / (p : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [cArith_prime_pow hp 1, if_neg one_ne_zero, hphi]
    simp only [Nat.sub_self, pow_zero, pow_one, Nat.choose_one_right, Nat.choose_zero_right,
      Nat.cast_ofNat, Nat.cast_one, mul_one, div_one]
    have heq : (-1 : ℝ) * 8 / (p : ℝ) + 8 / ((p : ℝ) - 8) = 64 / ((p : ℝ) * ((p : ℝ) - 8)) := by
      field_simp; ring
    rw [heq, abs_of_pos (by positivity)]
    have h1 : 64 / ((p : ℝ) * ((p : ℝ) - 8)) ≤ 128 / (p : ℝ) ^ (2 : ℕ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hrpow : (p : ℝ) ^ ((1 : ℝ) / 4) / (p : ℝ) ^ (2 : ℕ) ≤ 1 / (p : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (p : ℝ) 2, div_le_div_iff₀ (Real.rpow_pos_of_pos hp_pos _)
        (Real.rpow_pos_of_pos hp_pos _), one_mul, ← Real.rpow_add hp_pos]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    calc 64 / ((p : ℝ) * ((p : ℝ) - 8)) * (p : ℝ) ^ ((1 : ℝ) / 4)
        ≤ 128 / (p : ℝ) ^ (2 : ℕ) * (p : ℝ) ^ ((1 : ℝ) / 4) := by gcongr
      _ = 128 * ((p : ℝ) ^ ((1 : ℝ) / 4) / (p : ℝ) ^ (2 : ℕ)) := by ring
      _ ≤ 128 * (1 / (p : ℝ) ^ ((3 : ℝ) / 2)) := by gcongr
      _ = 128 / (p : ℝ) ^ ((3 : ℝ) / 2) := by ring
  have hk29 : ∑ k ∈ Finset.Icc 2 9, |cArith (p ^ k)| * ((p ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤
      ∑ _k ∈ Finset.Icc 2 9, (5000 / (p : ℝ) ^ ((3 : ℝ) / 2)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hch1 : (Nat.choose 8 k : ℝ) ≤ 256 := by
      have : Nat.choose 8 k ≤ 2 ^ 8 := Nat.choose_le_two_pow 8 k
      exact_mod_cast this
    have hch2 : (Nat.choose 8 (k - 1) : ℝ) ≤ 256 := by
      have : Nat.choose 8 (k - 1) ≤ 2 ^ 8 := Nat.choose_le_two_pow 8 (k - 1)
      exact_mod_cast this
    rw [cArith_prime_pow hp k, if_neg (by omega), hphi]
    have habs : |(-1 : ℝ) ^ k * (Nat.choose 8 k : ℝ) / (p : ℝ) ^ k +
        8 / ((p : ℝ) - 8) * ((-1 : ℝ) ^ (k - 1) * (Nat.choose 8 (k - 1) : ℝ) / (p : ℝ) ^ (k - 1))| ≤
        5000 / (p : ℝ) ^ k := by
      have htri := abs_add_le
        ((-1 : ℝ) ^ k * (Nat.choose 8 k : ℝ) / (p : ℝ) ^ k)
        (8 / ((p : ℝ) - 8) * ((-1 : ℝ) ^ (k - 1) * (Nat.choose 8 (k - 1) : ℝ) / (p : ℝ) ^ (k - 1)))
      have ht1 : |(-1 : ℝ) ^ k * (Nat.choose 8 k : ℝ) / (p : ℝ) ^ k| ≤ 256 / (p : ℝ) ^ k := by
        rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (pow_pos hp_pos k)]
        exact div_le_div_of_nonneg_right hch1 (pow_nonneg hp_pos.le k)
      have ht2 : |8 / ((p : ℝ) - 8) * ((-1 : ℝ) ^ (k - 1) * (Nat.choose 8 (k - 1) : ℝ) / (p : ℝ) ^ (k - 1))| ≤
          4096 / (p : ℝ) ^ k := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 8 / ((p : ℝ) - 8)),
          abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (pow_pos hp_pos (k - 1))]
        have h8p : 8 / ((p : ℝ) - 8) ≤ 16 / (p : ℝ) := by
          rw [div_le_div_iff₀ hp8_pos hp_pos]; linarith
        have hpow_k : (p : ℝ) * (p : ℝ) ^ (k - 1) = (p : ℝ) ^ k := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega)]
        calc 8 / ((p : ℝ) - 8) * ((Nat.choose 8 (k - 1) : ℝ) / (p : ℝ) ^ (k - 1))
            ≤ (16 / (p : ℝ)) * (256 / (p : ℝ) ^ (k - 1)) := by gcongr
          _ = 4096 / ((p : ℝ) * (p : ℝ) ^ (k - 1)) := by ring
          _ = 4096 / (p : ℝ) ^ k := by rw [hpow_k]
      have h5000 : 256 / (p : ℝ) ^ k + 4096 / (p : ℝ) ^ k ≤ 5000 / (p : ℝ) ^ k := by
        rw [← add_div]; apply div_le_div_of_nonneg_right (by norm_num) (pow_nonneg hp_pos.le k)
      linarith
    have hrpow_k : ((p ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 4) / (p : ℝ) ^ k ≤ 1 / (p : ℝ) ^ ((3 : ℝ) / 2) := by
      push_cast
      rw [← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul hp_pos.le,
        div_le_div_iff₀ (Real.rpow_pos_of_pos hp_pos _) (Real.rpow_pos_of_pos hp_pos _),
        one_mul, ← Real.rpow_add hp_pos]
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      linarith
    calc |(-1 : ℝ) ^ k * (Nat.choose 8 k : ℝ) / (p : ℝ) ^ k +
            8 / ((p : ℝ) - 8) * ((-1 : ℝ) ^ (k - 1) * (Nat.choose 8 (k - 1) : ℝ) / (p : ℝ) ^ (k - 1))| *
            ((p ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 4)
        ≤ (5000 / (p : ℝ) ^ k) * ((p ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by gcongr
      _ = 5000 * (((p ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 4) / (p : ℝ) ^ k) := by ring
      _ ≤ 5000 * (1 / (p : ℝ) ^ ((3 : ℝ) / 2)) := by gcongr
      _ = 5000 / (p : ℝ) ^ ((3 : ℝ) / 2) := by ring
  have hcard : (Finset.Icc 2 9).card = 8 := by decide
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at hk29
  have hden : (0 : ℝ) < (p : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hp_pos _
  have h128 : 128 / (p : ℝ) ^ ((3 : ℝ) / 2) + 8 * (5000 / (p : ℝ) ^ ((3 : ℝ) / 2)) ≤
      50000 / (p : ℝ) ^ ((3 : ℝ) / 2) := by
    have : 128 / (p : ℝ) ^ ((3 : ℝ) / 2) + 8 * (5000 / (p : ℝ) ^ ((3 : ℝ) / 2)) =
        40128 / (p : ℝ) ^ ((3 : ℝ) / 2) := by ring
    rw [this]; exact div_le_div_of_nonneg_right (by norm_num) hden.le
  linarith

private lemma cArith_eq_prod_primeFactors {d : ℕ} (hd : 1 ≤ d) :
    cArith d = ∏ p ∈ d.primeFactors, cArith (p ^ (d.factorization p)) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd1 : d = 1
    · subst hd1; simp [cArith_isMult.map_one]
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
    let e := d.factorization p
    have he_pos : 0 < e := hp.factorization_pos_of_dvd (by omega) hpd
    let m := d / p ^ e
    have hpe_dvd : p ^ e ∣ d := Nat.ordProj_dvd d p
    have hd_eq : d = p ^ e * m := (Nat.mul_div_cancel' hpe_dvd).symm
    have hnd : ¬ p ∣ m := by
      intro hpm
      have hpe1 : p ^ (e + 1) ∣ d := by
        rw [hd_eq, pow_succ]; exact mul_dvd_mul_left (p ^ e) hpm
      have hle := (hp.pow_dvd_iff_le_factorization (by omega)).mp hpe1
      omega
    have hcop : Nat.Coprime (p ^ e) m := (hp.coprime_iff_not_dvd.mpr hnd).pow_left e
    have hm_pos : 1 ≤ m := Nat.div_pos (Nat.le_of_dvd (by omega) hpe_dvd) (pow_pos hp.pos e)
    have hm_lt : m < d := by
      have hpe_gt1 : 1 < p ^ e := one_lt_pow₀ hp.one_lt he_pos.ne'
      nlinarith
    rw [hd_eq, cArith_isMult.map_mul_of_coprime hcop, ih m hm_lt hm_pos]
    rw [hcop.primeFactors_mul, Finset.prod_union hcop.disjoint_primeFactors]
    have hpf_pe : (p ^ e).primeFactors = {p} := Nat.primeFactors_pow p he_pos.ne' ▸ hp.primeFactors
    rw [hpf_pe, Finset.prod_singleton]
    have hfac_p : (p ^ e * m).factorization p = e := by
      rw [Nat.factorization_mul (pow_ne_zero e hp.ne_zero) (by omega), Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_same]
      have h0 : m.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
      omega
    rw [hfac_p]
    congr 1
    refine Finset.prod_congr rfl fun q hq => ?_
    have hqp : q ≠ p := fun heq => hnd (heq ▸ Nat.dvd_of_mem_primeFactors hq)
    have hfac_q : (p ^ e * m).factorization q = m.factorization q := by
      rw [Nat.factorization_mul (pow_ne_zero e hp.ne_zero) (by omega), Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_of_ne hqp, zero_add]
    rw [hfac_q]

/-- Finite set of `N`-smooth positive integers with prime exponents `< 10`. -/
private def smoothTen (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ((∏ p ∈ Nat.primesLE N, p) ^ 9)).filter
    (fun d => (∀ p ∈ d.primeFactors, p ≤ N) ∧ (∀ p ∈ d.primeFactors, d.factorization p ≤ 9))

private lemma mem_smoothTen_iff {N d : ℕ} :
    d ∈ smoothTen N ↔ 1 ≤ d ∧ (∀ p ∈ d.primeFactors, p ≤ N ∧ d.factorization p ≤ 9) := by
  simp only [smoothTen, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd1, _⟩, h1, h2⟩
    exact ⟨hd1, fun p hp => ⟨h1 p hp, h2 p hp⟩⟩
  · rintro ⟨hd1, h⟩
    refine ⟨⟨hd1, ?_⟩, fun p hp => (h p hp).1, fun p hp => (h p hp).2⟩
    have hd_prod : d = ∏ p ∈ d.primeFactors, p ^ (d.factorization p) :=
      (Nat.prod_factorization_pow_eq_self (by omega)).symm
    have hsub : d.primeFactors ⊆ Nat.primesLE N := fun p hp =>
      Nat.mem_primesLE.mpr ⟨(h p hp).1, Nat.prime_of_mem_primeFactors hp⟩
    calc d = ∏ p ∈ d.primeFactors, p ^ (d.factorization p) := hd_prod
      _ ≤ ∏ p ∈ d.primeFactors, p ^ 9 :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p hp =>
            Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp).pos (h p hp).2
      _ = (∏ p ∈ d.primeFactors, p) ^ 9 := Finset.prod_pow _ _ _
      _ ≤ (∏ p ∈ Nat.primesLE N, p) ^ 9 := Nat.pow_le_pow_left
          (Finset.prod_le_prod_of_subset_of_one_le' hsub fun p hp _ =>
            (Nat.mem_primesLE.mp hp).2.one_le) 9

private lemma sum_smoothTen_eq_prod (N : ℕ) (f : ℕ → ℝ) (hf1 : f 1 = 1)
    (hf_mul : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b) :
    ∑ d ∈ smoothTen N, f d = ∏ p ∈ Nat.primesLE N, ∑ k ∈ Finset.range 10, f (p ^ k) := by
  -- Prove by induction on S = Nat.primesLE N
  suffices hgen : ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) →
      ∑ d ∈ (Finset.Icc 1 ((∏ p ∈ S, p) ^ 9)).filter
        (fun d => (∀ p ∈ d.primeFactors, p ∈ S ∧ d.factorization p ≤ 9)), f d =
      ∏ p ∈ S, ∑ k ∈ Finset.range 10, f (p ^ k) by
    have hS : ∀ p ∈ Nat.primesLE N, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
    have hset : smoothTen N = (Finset.Icc 1 ((∏ p ∈ Nat.primesLE N, p) ^ 9)).filter
        (fun d => (∀ p ∈ d.primeFactors, p ∈ Nat.primesLE N ∧ d.factorization p ≤ 9)) := by
      ext d
      simp only [smoothTen, Finset.mem_filter, Nat.mem_primesLE]
      constructor
      · rintro ⟨hd, h1, h2⟩
        exact ⟨hd, fun p hp => ⟨⟨h1 p hp, Nat.prime_of_mem_primeFactors hp⟩, h2 p hp⟩⟩
      · rintro ⟨hd, h⟩
        exact ⟨hd, fun p hp => (h p hp).1.1, fun p hp => (h p hp).2⟩
    rw [hset]
    exact hgen (Nat.primesLE N) hS
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    have hset : (Finset.Icc 1 ((∏ p ∈ (∅ : Finset ℕ), p) ^ 9)).filter
        (fun d => (∀ p ∈ d.primeFactors, p ∈ (∅ : Finset ℕ) ∧ d.factorization p ≤ 9)) = {1} := by
      ext d
      simp only [Finset.prod_empty, one_pow, Finset.mem_filter, Finset.mem_Icc,
        Finset.notMem_empty, false_and, imp_false, Finset.mem_singleton]
      constructor
      · intro h; omega
      · rintro rfl; simp
    rw [hset, Finset.sum_singleton, Finset.prod_empty, hf1]
  | @insert p S hpS ih =>
    intro hall
    have hp : p.Prime := hall p (Finset.mem_insert_self p S)
    have hS : ∀ q ∈ S, q.Prime := fun q hq => hall q (Finset.mem_insert_of_mem hq)
    conv_rhs => rw [Finset.prod_insert hpS, ← ih hS]
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    symm
    apply Finset.sum_bij (fun km _ => p ^ km.1 * km.2)
    · intro km hkm
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc] at hkm
      obtain ⟨hk, ⟨hm1, _⟩, hm_pf⟩ := hkm
      have hm_ndvd : ¬ p ∣ km.2 := fun hd =>
        hpS (hm_pf p (Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩)).1
      have hcop : Nat.Coprime (p ^ km.1) km.2 := (hp.coprime_iff_not_dvd.mpr hm_ndvd).pow_left km.1
      have hd_pos : 1 ≤ p ^ km.1 * km.2 := Nat.mul_pos (pow_pos hp.pos _) hm1
      have hpf_all : ∀ q ∈ (p ^ km.1 * km.2).primeFactors,
          q ∈ insert p S ∧ (p ^ km.1 * km.2).factorization q ≤ 9 := by
        intro q hq
        rw [hcop.primeFactors_mul, Finset.mem_union] at hq
        rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega), Finsupp.add_apply,
          hp.factorization_pow]
        rcases hq with hq1 | hq2
        · have hqp : q = p := by
            have hd := Nat.dvd_of_mem_primeFactors hq1
            exact ((Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hq1) hp).mp
              (Nat.Prime.dvd_of_dvd_pow (Nat.prime_of_mem_primeFactors hq1) hd))
          subst hqp
          have h0 : km.2.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hm_ndvd
          simp only [Finset.mem_insert_self, Finsupp.single_eq_same, h0, add_zero, true_and]
          omega
        · have hqp : q ≠ p := fun h => hpS (h ▸ (hm_pf q hq2).1)
          simp only [Finsupp.single_eq_of_ne hqp, zero_add]
          exact ⟨Finset.mem_insert_of_mem (hm_pf q hq2).1, (hm_pf q hq2).2⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd_pos, ?_⟩, hpf_all⟩
      have hd_prod : p ^ km.1 * km.2 =
          ∏ q ∈ (p ^ km.1 * km.2).primeFactors, q ^ ((p ^ km.1 * km.2).factorization q) :=
        (Nat.prod_factorization_pow_eq_self (by omega)).symm
      calc p ^ km.1 * km.2 = ∏ q ∈ (p ^ km.1 * km.2).primeFactors,
              q ^ ((p ^ km.1 * km.2).factorization q) := hd_prod
        _ ≤ ∏ q ∈ (p ^ km.1 * km.2).primeFactors, q ^ 9 :=
            Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun q hq =>
              Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hq).pos (hpf_all q hq).2
        _ = (∏ q ∈ (p ^ km.1 * km.2).primeFactors, q) ^ 9 := Finset.prod_pow _ _ _
        _ ≤ (∏ q ∈ insert p S, q) ^ 9 := Nat.pow_le_pow_left
            (Finset.prod_le_prod_of_subset_of_one_le'
              (fun q hq => (hpf_all q hq).1) fun q hq _ => (hall q hq).one_le) 9
    · intro a ha b hb heq
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc] at ha hb
      have ha_nd : ¬ p ∣ a.2 := fun hd =>
        hpS (ha.2.2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩)).1
      have hb_nd : ¬ p ∣ b.2 := fun hd =>
        hpS (hb.2.2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩)).1
      have hfac_eq := congrArg (fun x => x.factorization p) heq
      rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega),
        Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (by omega),
        Finsupp.add_apply, Finsupp.add_apply, hp.factorization_pow, hp.factorization_pow,
        Finsupp.single_eq_same, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd ha_nd,
        Nat.factorization_eq_zero_of_not_dvd hb_nd] at hfac_eq
      have h1 : a.1 = b.1 := by omega
      have h2 : a.2 = b.2 := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) (h1 ▸ heq)
      exact Prod.ext h1 h2
    · intro d hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, _⟩, hd_pf⟩ := hd
      let k := d.factorization p
      let m := d / p ^ k
      have hpk_dvd : p ^ k ∣ d := Nat.ordProj_dvd d p
      have hk_lt : k < 10 := by
        by_cases hpd : p ∣ d
        · have := (hd_pf p (Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩)).2; omega
        · have : k = 0 := Nat.factorization_eq_zero_of_not_dvd hpd; omega
      have hm_pos : 1 ≤ m := Nat.div_pos (Nat.le_of_dvd (by omega) hpk_dvd) (pow_pos hp.pos k)
      have hm_nd : ¬ p ∣ m := by
        intro hpm
        have hpk1 : p ^ (k + 1) ∣ d := by
          rw [← Nat.mul_div_cancel' hpk_dvd, pow_succ]; exact mul_dvd_mul_left (p ^ k) hpm
        have := (hp.pow_dvd_iff_le_factorization (by omega)).mp hpk1
        omega
      have hm_pf : ∀ q ∈ m.primeFactors, q ∈ S ∧ m.factorization q ≤ 9 := by
        intro q hq
        have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hq
        have hqd : q ∣ d := hqm.trans (Nat.div_dvd_of_dvd hpk_dvd)
        have hqp : q ≠ p := fun h => hm_nd (h ▸ hqm)
        have hq_d := hd_pf q (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq, hqd, by omega⟩)
        have hqS : q ∈ S := (Finset.mem_insert.mp hq_d.1).resolve_left hqp
        have hfac_le : m.factorization q ≤ d.factorization q :=
          Nat.factorization_le_iff_dvd (by omega) (by omega) |>.mpr (Nat.div_dvd_of_dvd hpk_dvd) q
        exact ⟨hqS, hfac_le.trans hq_d.2⟩
      have hm_le : m ≤ (∏ q ∈ S, q) ^ 9 := by
        have hm_prod : m = ∏ q ∈ m.primeFactors, q ^ (m.factorization q) :=
          (Nat.prod_factorization_pow_eq_self (by omega)).symm
        calc m = ∏ q ∈ m.primeFactors, q ^ (m.factorization q) := hm_prod
          _ ≤ ∏ q ∈ m.primeFactors, q ^ 9 :=
              Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun q hq =>
                Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hq).pos (hm_pf q hq).2
          _ = (∏ q ∈ m.primeFactors, q) ^ 9 := Finset.prod_pow _ _ _
          _ ≤ (∏ q ∈ S, q) ^ 9 := Nat.pow_le_pow_left
              (Finset.prod_le_prod_of_subset_of_one_le'
                (fun q hq => (hm_pf q hq).1) fun q hq _ => (hS q hq).one_le) 9
      refine ⟨(k, m), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hk_lt,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm_pos, hm_le⟩, hm_pf⟩⟩,
        Nat.mul_div_cancel' hpk_dvd⟩
    · intro km hkm
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_Icc] at hkm
      have hm_nd : ¬ p ∣ km.2 := fun hd =>
        hpS (hkm.2.2 p (Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩)).1
      exact (hf_mul (p ^ km.1) km.2 ((hp.coprime_iff_not_dvd.mpr hm_nd).pow_left km.1)).symm

private lemma summable_abs_cArith_rpow :
    Summable (fun d : ℕ => |cArith d| * (d : ℝ) ^ ((1 : ℝ) / 4)) := by
  let w : ℕ → ℝ := fun d => |cArith d| * (d : ℝ) ^ ((1 : ℝ) / 4)
  have hw_nn : ∀ d, 0 ≤ w d := fun d => by dsimp [w]; positivity
  have hw1 : w 1 = 1 := by simp [w, cArith_isMult.map_one]
  have hw_mul : ∀ a b, Nat.Coprime a b → w (a * b) = w a * w b := by
    intro a b hab
    simp only [w, cArith_isMult.map_mul_of_coprime hab, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
    ring
  have hsum32 : Summable (fun m : ℕ => (50000 : ℝ) / (m : ℝ) ^ ((3 : ℝ) / 2)) := by
    have h := (Real.summable_one_div_nat_rpow.mpr (show (1 : ℝ) < (3 : ℝ) / 2 by norm_num)).mul_left (50000 : ℝ)
    have heq : (fun m : ℕ => (50000 : ℝ) / (m : ℝ) ^ ((3 : ℝ) / 2)) =
        (fun m : ℕ => (50000 : ℝ) * (1 / (m : ℝ) ^ ((3 : ℝ) / 2))) := by
      ext m; ring
    rw [heq]; exact h
  let M59 : ℝ := ∏ p ∈ Nat.primesLE 59, ∑ k ∈ Finset.range 10, w (p ^ k)
  let B : ℝ := M59 * Real.exp (∑' m : ℕ, (50000 : ℝ) / (m : ℝ) ^ ((3 : ℝ) / 2))
  apply summable_of_sum_range_le hw_nn (c := B)
  intro N
  -- Every d ∈ range N with w d ≠ 0 lies in smoothTen N
  have hsub : ∑ d ∈ Finset.range N, w d ≤ ∑ d ∈ smoothTen N, w d := by
    have hfilt : ∑ d ∈ Finset.range N, w d = ∑ d ∈ (Finset.range N).filter (fun d => d ∈ smoothTen N), w d := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro d hd hnot
      rw [Finset.mem_filter] at hnot
      have hnotS : d ∉ smoothTen N := fun h => hnot ⟨hd, h⟩
      by_cases hd0 : d = 0
      · subst hd0; simp [w]
      have hd1 : 1 ≤ d := by omega
      have hlt : d < N := Finset.mem_range.mp hd
      have hex : ∃ p ∈ d.primeFactors, 10 ≤ d.factorization p := by
        by_contra! hall
        apply hnotS
        rw [mem_smoothTen_iff]
        refine ⟨hd1, fun p hp => ⟨?_, by have := hall p hp; omega⟩⟩
        exact (Nat.le_of_dvd hd1 (Nat.dvd_of_mem_primeFactors hp)).trans hlt.le
      obtain ⟨p, hp, hge10⟩ := hex
      have hc0 : cArith d = 0 := by
        rw [cArith_eq_prod_primeFactors hd1]
        exact Finset.prod_eq_zero hp (cArith_prime_pow_eq_zero (Nat.prime_of_mem_primeFactors hp) hge10)
      simp [w, hc0]
    rw [hfilt]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => (Finset.mem_filter.mp hd).2)
      fun d _ _ => hw_nn d
  rw [sum_smoothTen_eq_prod N w hw1 hw_mul] at hsub
  refine hsub.trans ?_
  -- Split primesLE N into p ≤ 59 and p > 59
  have hsplit : ∏ p ∈ Nat.primesLE N, ∑ k ∈ Finset.range 10, w (p ^ k) =
      (∏ p ∈ (Nat.primesLE N).filter (· ≤ 59), ∑ k ∈ Finset.range 10, w (p ^ k)) *
      (∏ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ 59), ∑ k ∈ Finset.range 10, w (p ^ k)) :=
    (Finset.prod_filter_mul_prod_filter_not (Nat.primesLE N) (· ≤ 59) _).symm
  rw [hsplit]
  have hterm_ge1 : ∀ p : ℕ, 1 ≤ ∑ k ∈ Finset.range 10, w (p ^ k) := by
    intro p
    have h0 : 0 ∈ Finset.range 10 := Finset.mem_range.mpr (by omega)
    calc (1 : ℝ) = w (p ^ 0) := by simp [hw1]
      _ ≤ ∑ k ∈ Finset.range 10, w (p ^ k) := Finset.single_le_sum (fun k _ => hw_nn _) h0
  have hsmall : ∏ p ∈ (Nat.primesLE N).filter (· ≤ 59), ∑ k ∈ Finset.range 10, w (p ^ k) ≤ M59 := by
    have hsub59 : (Nat.primesLE N).filter (· ≤ 59) ⊆ Nat.primesLE 59 := fun p hp => by
      rw [Finset.mem_filter, Nat.mem_primesLE] at hp
      exact Nat.mem_primesLE.mpr ⟨hp.2, hp.1.2⟩
    have hM59_eq : M59 = (∏ p ∈ (Nat.primesLE N).filter (· ≤ 59), ∑ k ∈ Finset.range 10, w (p ^ k)) *
        (∏ p ∈ Nat.primesLE 59 \ (Nat.primesLE N).filter (· ≤ 59), ∑ k ∈ Finset.range 10, w (p ^ k)) :=
      (Finset.prod_sdiff hsub59).symm.trans (mul_comm _ _)
    have hrest_ge1 : 1 ≤ ∏ p ∈ Nat.primesLE 59 \ (Nat.primesLE N).filter (· ≤ 59),
        ∑ k ∈ Finset.range 10, w (p ^ k) :=
      Finset.one_le_prod fun p _ => hterm_ge1 p
    have hnn_lhs : 0 ≤ ∏ p ∈ (Nat.primesLE N).filter (· ≤ 59), ∑ k ∈ Finset.range 10, w (p ^ k) :=
      Finset.prod_nonneg fun p _ => le_trans zero_le_one (hterm_ge1 p)
    nlinarith
  have hlarge : ∏ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ 59), ∑ k ∈ Finset.range 10, w (p ^ k) ≤
      Real.exp (∑' m : ℕ, (50000 : ℝ) / (m : ℝ) ^ ((3 : ℝ) / 2)) := by
    calc ∏ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ 59), ∑ k ∈ Finset.range 10, w (p ^ k)
        ≤ ∏ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ 59),
            Real.exp ((50000 : ℝ) / (p : ℝ) ^ ((3 : ℝ) / 2)) := by
          apply Finset.prod_le_prod (fun p _ => le_trans zero_le_one (hterm_ge1 p))
          intro p hp
          obtain ⟨hpN, hp59⟩ := Finset.mem_filter.mp hp
          have hprime := (Nat.mem_primesLE.mp hpN).2
          have h0 : Finset.range 10 = insert 0 (Finset.Icc 1 9) := by
            ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
          rw [h0, Finset.sum_insert (by simp), pow_zero, hw1]
          have hbound := cArith_prime_rpow_bound hprime (by omega)
          have hexp := Real.add_one_le_exp ((50000 : ℝ) / (p : ℝ) ^ ((3 : ℝ) / 2))
          dsimp only [w]
          linarith
      _ = Real.exp (∑ p ∈ (Nat.primesLE N).filter (fun p => ¬ p ≤ 59),
            (50000 : ℝ) / (p : ℝ) ^ ((3 : ℝ) / 2)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (∑' m : ℕ, (50000 : ℝ) / (m : ℝ) ^ ((3 : ℝ) / 2)) :=
          Real.exp_le_exp.mpr (hsum32.sum_le_tsum _ fun m _ => by positivity)
  have hM59_nn : 0 ≤ M59 := Finset.prod_nonneg fun p _ => le_trans zero_le_one (hterm_ge1 p)
  exact mul_le_mul hsmall hlarge
    (Finset.prod_nonneg fun p _ => le_trans zero_le_one (hterm_ge1 p)) hM59_nn

private lemma summable_abs_cArith : Summable (fun d : ℕ => |cArith d|) := by
  refine Summable.of_nonneg_of_le (fun d => abs_nonneg _) (fun d => ?_) summable_abs_cArith_rpow
  by_cases hd0 : d = 0
  · subst hd0; simp
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hr : (1 : ℝ) ≤ (d : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hd1 (by norm_num)
  nlinarith [abs_nonneg (cArith d)]

private lemma summable_cArith : Summable (fun d : ℕ => cArith d) :=
  summable_abs_cArith.of_abs

private lemma abs_tsum_le {f : ℕ → ℝ} (hf : Summable (fun d => |f d|)) :
    |∑' d : ℕ, f d| ≤ ∑' d : ℕ, |f d| := by
  have hfn : Summable (fun d => ‖f d‖) := by simpa only [Real.norm_eq_abs] using hf
  simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hfn

private lemma tsum_cArith_pos : 0 < ∑' d : ℕ, cArith d := by
  let c59 : ℝ := ∏ p ∈ Nat.primesLE 59, ((1 + 1 / phiG p) * (1 - 1 / (p : ℝ)) ^ 8)
  have hc59_pos : 0 < c59 := by
    apply Finset.prod_pos
    intro p hp
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have h1 : 0 < 1 + 1 / phiG p := by positivity [phiG_pos p]
    have h2 : 0 < 1 - 1 / (p : ℝ) := by
      have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      linarith
    exact mul_pos h1 (pow_pos h2 8)
  -- For every N ≥ 60, ∑_{d ∈ smoothTen N} cArith d ≥ c59
  have hlower : ∀ N : ℕ, 60 ≤ N → c59 ≤ ∑ d ∈ smoothTen N, cArith d := by
    intro N hN
    rw [sum_smoothTen_eq_prod N (fun d => cArith d) cArith_isMult.map_one
      (fun a b hab => cArith_isMult.map_mul_of_coprime hab)]
    have hcongr : ∏ p ∈ Nat.primesLE N, ∑ k ∈ Finset.range 10, cArith (p ^ k) =
        ∏ p ∈ Nat.primesLE N, ((1 + 1 / phiG p) * (1 - 1 / (p : ℝ)) ^ 8) :=
      Finset.prod_congr rfl fun p hp => sum_cArith_prime_pows (Nat.mem_primesLE.mp hp).2
    rw [hcongr]
    have hsub59 : Nat.primesLE 59 ⊆ Nat.primesLE N := fun p hp => by
      rw [Nat.mem_primesLE] at hp ⊢; exact ⟨hp.1.trans (by omega), hp.2⟩
    have hsplit_N : ∏ p ∈ Nat.primesLE N, ((1 + 1 / phiG p) * (1 - 1 / (p : ℝ)) ^ 8) =
        c59 * ∏ p ∈ Nat.primesLE N \ Nat.primesLE 59, ((1 + 1 / phiG p) * (1 - 1 / (p : ℝ)) ^ 8) :=
      (Finset.prod_sdiff hsub59).symm.trans (mul_comm _ _)
    rw [hsplit_N]
    have hrest_ge1 : 1 ≤ ∏ p ∈ Nat.primesLE N \ Nat.primesLE 59,
        ((1 + 1 / phiG p) * (1 - 1 / (p : ℝ)) ^ 8) := by
      apply Finset.one_le_prod
      intro p hp
      obtain ⟨hpN, hnot59⟩ := Finset.mem_sdiff.mp hp
      have hprime := (Nat.mem_primesLE.mp hpN).2
      have hp59 : 59 < p := by
        by_contra! hle
        exact hnot59 (Nat.mem_primesLE.mpr ⟨hle, hprime⟩)
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hp60 : (60 : ℝ) ≤ p := by exact_mod_cast (show 60 ≤ p by omega)
      have hp8_pos : (0 : ℝ) < (p : ℝ) - 8 := by linarith
      have hphi : 1 + 1 / phiG p = (p : ℝ) / ((p : ℝ) - 8) := by
        rw [phiG_prime hprime, omegaP_eq_eight hprime hp59]; push_cast; field_simp [hp8_pos.ne']; ring
      rw [hphi]
      have hbern : 1 - 8 / (p : ℝ) ≤ (1 - 1 / (p : ℝ)) ^ 8 := by
        have h := one_add_mul_le_pow (a := -(1 / (p : ℝ))) (by
          have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp_pos]; linarith
          linarith) 8
        have hrew1 : 1 + -(1 / (p : ℝ)) = 1 - 1 / (p : ℝ) := by ring
        have hrew2 : 1 + (8 : ℕ) * -(1 / (p : ℝ)) = 1 - 8 / (p : ℝ) := by push_cast; ring
        linarith
      calc (1 : ℝ) = ((p : ℝ) / ((p : ℝ) - 8)) * (1 - 8 / (p : ℝ)) := by field_simp [hp8_pos.ne', hp_pos.ne']
        _ ≤ ((p : ℝ) / ((p : ℝ) - 8)) * (1 - 1 / (p : ℝ)) ^ 8 :=
            mul_le_mul_of_nonneg_left hbern (by positivity)
    nlinarith
  -- Show ∑_{d ∈ smoothTen N} cArith d → ∑' d, cArith d as N → ∞
  have htail : ∀ N : ℕ, 60 ≤ N →
      |(∑' d : ℕ, cArith d) - ∑ d ∈ smoothTen N, cArith d| ≤
        (∑' d : ℕ, |cArith d| * (d : ℝ) ^ ((1 : ℝ) / 4)) / (N : ℝ) ^ ((1 : ℝ) / 4) := by
    intro N hN
    have hN_pos : (0 : ℝ) < N := by positivity
    have hdiff : (∑' d : ℕ, cArith d) - ∑ d ∈ smoothTen N, cArith d =
        ∑' d : ℕ, if d ∈ smoothTen N then 0 else cArith d := by
      have hsplit := summable_cArith.sum_add_tsum_compl (s := smoothTen N)
      -- Simpler: use Finset.sum_ite + tsum_sub
      have hfin : Summable (fun d : ℕ => if d ∈ smoothTen N then cArith d else 0) :=
        summable_of_ne_finset_zero (s := smoothTen N) fun d hd => if_neg hd
      have hsum_fin : ∑' d : ℕ, (if d ∈ smoothTen N then cArith d else 0) =
          ∑ d ∈ smoothTen N, cArith d := by
        rw [tsum_eq_sum (s := smoothTen N) fun d hd => if_neg hd]
        exact Finset.sum_congr rfl fun d hd => if_pos hd
      rw [← hsum_fin, ← summable_cArith.tsum_sub hfin]
      congr 1; ext d; split_ifs <;> ring
    rw [hdiff]
    have hrem_abs : Summable (fun d : ℕ => |if d ∈ smoothTen N then (0 : ℝ) else cArith d|) := by
      refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun d => ?_) summable_abs_cArith
      split_ifs <;> simp
    calc |∑' d : ℕ, if d ∈ smoothTen N then 0 else cArith d|
        ≤ ∑' d : ℕ, |if d ∈ smoothTen N then (0 : ℝ) else cArith d| := abs_tsum_le hrem_abs
      _ ≤ ∑' d : ℕ, (|cArith d| * (d : ℝ) ^ ((1 : ℝ) / 4)) / (N : ℝ) ^ ((1 : ℝ) / 4) := by
          apply Summable.tsum_le_tsum _ hrem_abs (summable_abs_cArith_rpow.div_const _)
          intro d
          split_ifs with hd
          · simp; positivity
          · by_cases hc0 : cArith d = 0
            · simp [hc0]
            have hd1 : 1 ≤ d := by
              by_contra hd0; push Not at hd0
              have : d = 0 := by omega
              subst this; exact hc0 (by simp [cArith])
            have hgeN : N < d := by
              by_contra! hle
              have hex : ∃ p ∈ d.primeFactors, 10 ≤ d.factorization p := by
                by_contra! hall
                apply hd
                rw [mem_smoothTen_iff]
                refine ⟨hd1, fun p hp => ⟨?_, by have := hall p hp; omega⟩⟩
                exact (Nat.le_of_dvd hd1 (Nat.dvd_of_mem_primeFactors hp)).trans hle
              obtain ⟨p, hp, h10⟩ := hex
              apply hc0
              rw [cArith_eq_prod_primeFactors hd1]
              exact Finset.prod_eq_zero hp (cArith_prime_pow_eq_zero (Nat.prime_of_mem_primeFactors hp) h10)
            rw [le_div_iff₀ (Real.rpow_pos_of_pos hN_pos _)]
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow hN_pos.le (by exact_mod_cast hgeN.le) (by norm_num)) (abs_nonneg _)
      _ = (∑' d : ℕ, |cArith d| * (d : ℝ) ^ ((1 : ℝ) / 4)) / (N : ℝ) ^ ((1 : ℝ) / 4) :=
          tsum_div_const
  -- Pick N large enough that tail ≤ c59 / 2
  let W := ∑' d : ℕ, |cArith d| * (d : ℝ) ^ ((1 : ℝ) / 4)
  have hW_nn : 0 ≤ W := tsum_nonneg fun d => by positivity
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((2 * W / c59) ^ 4)
  let N := max 60 N0
  have hN60 : 60 ≤ N := le_max_left _ _
  have hN_gt : (2 * W / c59) ^ 4 < (N : ℝ) := hN0.trans_le (by exact_mod_cast le_max_right 60 N0)
  have htailN := htail N hN60
  have hlowN := hlower N hN60
  have htail_half : W / (N : ℝ) ^ ((1 : ℝ) / 4) ≤ c59 / 2 := by
    have hN_pos : (0 : ℝ) < N := by positivity
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hN_pos _)]
    have hr : 2 * W / c59 ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
      calc 2 * W / c59 = ((2 * W / c59) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) hN_gt.le (by norm_num)
    have hmul : (c59 / 2) * (2 * W / c59) = W := by field_simp [hc59_pos.ne']
    nlinarith
  have habs := (abs_le.mp htailN).1
  linarith

private lemma log_pow_le_const_rpow (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → (Real.log (d : ℝ)) ^ j ≤ C * (d : ℝ) ^ ((1 : ℝ) / 4) := by
  by_cases hj : j = 0
  · subst hj
    refine ⟨1, one_pos, fun d hd => ?_⟩
    simp only [pow_zero, one_mul]
    exact Real.one_le_rpow (by exact_mod_cast hd) (by norm_num)
  have hj_pos : (0 : ℝ) < j := by positivity
  refine ⟨(4 * (j : ℝ)) ^ j, by positivity, fun d hd => ?_⟩
  have hd_pos : (0 : ℝ) < d := by positivity
  have h1 : Real.log (d : ℝ) ≤ (4 * (j : ℝ)) * (d : ℝ) ^ ((1 : ℝ) / (4 * (j : ℝ))) := by
    have hu := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hd_pos (1 / (4 * (j : ℝ))))
    rw [Real.log_rpow hd_pos] at hu
    have hmul : Real.log (d : ℝ) = (4 * (j : ℝ)) * (1 / (4 * (j : ℝ)) * Real.log (d : ℝ)) := by
      field_simp [hj_pos.ne']
    nlinarith
  calc (Real.log (d : ℝ)) ^ j
      ≤ ((4 * (j : ℝ)) * (d : ℝ) ^ ((1 : ℝ) / (4 * (j : ℝ)))) ^ j :=
        pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast hd)) h1 j
    _ = (4 * (j : ℝ)) ^ j * ((d : ℝ) ^ ((1 : ℝ) / (4 * (j : ℝ)))) ^ j := mul_pow _ _ _
    _ = (4 * (j : ℝ)) ^ j * (d : ℝ) ^ ((1 : ℝ) / 4) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hd_pos.le]
        congr 1
        field_simp [hj_pos.ne']

private lemma Hsum_asymp :
    ∃ C_P : ℝ, 0 < C_P ∧ ∃ M0 : ℝ, 0 < M0 ∧ ∀ u : ℕ, 2 ≤ u →
      |Hsum u - C_P * (Real.log u) ^ 8| ≤ M0 * (Real.log u + 1) ^ 7 := by
  obtain ⟨K8, hK8_pos, hK8⟩ := sum_tau_div_id 8 (by norm_num)
  let CE := ∑' d : ℕ, cArith d
  have hCE_pos : 0 < CE := tsum_cArith_pos
  have hfac8_pos : (0 : ℝ) < ((Nat.factorial 8 : ℕ) : ℝ) := by positivity
  let CP := CE / ((Nat.factorial 8 : ℕ) : ℝ)
  have hCP_pos : 0 < CP := div_pos hCE_pos hfac8_pos
  obtain ⟨CL1, hCL1_pos, hCL1⟩ := log_pow_le_const_rpow 1
  obtain ⟨CL8, hCL8_pos, hCL8⟩ := log_pow_le_const_rpow 8
  let W := ∑' d : ℕ, |cArith d| * (d : ℝ) ^ ((1 : ℝ) / 4)
  have hW_nn : 0 ≤ W := tsum_nonneg fun d => by positivity
  have hW0_le : ∑' d : ℕ, |cArith d| ≤ W := by
    apply Summable.tsum_le_tsum _ summable_abs_cArith summable_abs_cArith_rpow
    intro d
    by_cases hd0 : d = 0
    · subst hd0; simp
    have h1 : (1 : ℝ) ≤ (d : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ d by omega)) (by norm_num)
    nlinarith [abs_nonneg (cArith d)]
  let M0 : ℝ := K8 * W + (8 * (CL1 + 1) * W + CL8 * W) / ((Nat.factorial 8 : ℕ) : ℝ) + 1
  refine ⟨CP, hCP_pos, M0, by positivity, fun u hu => ?_⟩
  have hu1 : 1 ≤ u := by omega
  have hlu_pos : 0 < Real.log u := Real.log_pos (by exact_mod_cast (show 1 < u by omega))
  -- Rewrite Hsum u via Dirichlet convolution aArith = cArith * bArith
  have hH_eq : Hsum u = ∑ d ∈ Finset.Icc 1 u, cArith d *
      (∑ q ∈ Finset.Icc 1 (u / d), (tau 8 q : ℝ) / (q : ℝ)) := by
    have h1 : Hsum u = ∑ n ∈ Finset.Icc 1 u, aArith n := by
      unfold Hsum sfLE
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      simp [aArith, hn1]
    rw [h1, ← cArith_mul_bArith]
    simp_rw [ArithmeticFunction.mul_apply, Finset.mul_sum]
    -- Swap sums via bijection (n, (d, q)) ↔ (d, q) with d * q ≤ u
    rw [Finset.sum_sigma', Finset.sum_sigma']
    symm
    apply Finset.sum_bij (fun dq _ => ⟨dq.1 * dq.2, (dq.1, dq.2)⟩)
    · intro dq hdq
      rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Icc] at hdq
      rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
      have hmul_le : dq.1 * dq.2 ≤ u := by
        rw [mul_comm]; exact (Nat.le_div_iff_mul_le hdq.1.1).mp hdq.2.2
      have hmul_pos : 0 < dq.1 * dq.2 := Nat.mul_pos hdq.1.1 hdq.2.1
      exact ⟨⟨hmul_pos, hmul_le⟩, rfl, hmul_pos.ne'⟩
    · intro a _ b _ heq
      have h2 : (a.1, a.2) = (b.1, b.2) := by
        have := Sigma.mk.inj_iff.mp heq
        exact eq_of_heq this.2
      cases a; cases b
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      rfl
    · intro x hx
      rw [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hx
      have hd_pos : 0 < x.2.1 := Nat.pos_of_mul_pos_right (hx.2.1.symm ▸ hx.1.1)
      have hq_pos : 0 < x.2.2 := Nat.pos_of_mul_pos_left (hx.2.1.symm ▸ hx.1.1)
      have hd_le : x.2.1 ≤ u := (Nat.le_mul_of_pos_right x.2.1 hq_pos).trans (hx.2.1 ▸ hx.1.2)
      have hq_le : x.2.2 ≤ u / x.2.1 :=
        (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm, hx.2.1]; exact hx.1.2)
      refine ⟨⟨x.2.1, x.2.2⟩, Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd_pos, hd_le⟩,
        Finset.mem_Icc.mpr ⟨hq_pos, hq_le⟩⟩, ?_⟩
      exact Sigma.ext hx.2.1 (by simp)
    · intro dq _
      simp [bArith]
  rw [hH_eq]
  -- Split into three errors:
  -- (E1) replacing ∑_{q=1}^{u/d} tau 8 q / q by (log (u/d))^8 / 8!
  -- (E2) replacing (log (u/d))^8 by (log u)^8
  -- (E3) extending ∑_{d=1}^u cArith d to ∑' d, cArith d
  have hE1 : |∑ d ∈ Finset.Icc 1 u, cArith d * (∑ q ∈ Finset.Icc 1 (u / d), (tau 8 q : ℝ) / (q : ℝ)) -
      ∑ d ∈ Finset.Icc 1 u, cArith d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ))| ≤
      K8 * W * (Real.log u + 1) ^ 7 := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ d ∈ Finset.Icc 1 u, (cArith d * (∑ q ∈ Finset.Icc 1 (u / d), (tau 8 q : ℝ) / (q : ℝ)) -
            cArith d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ)))|
        ≤ ∑ d ∈ Finset.Icc 1 u, |cArith d * (∑ q ∈ Finset.Icc 1 (u / d), (tau 8 q : ℝ) / (q : ℝ)) -
            cArith d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 u, |cArith d| * (K8 * (Real.log u + 1) ^ 7) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          rw [← mul_sub, abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have hud : 1 ≤ u / d := Nat.div_pos hd.2 hd.1
          have h1 := hK8 (u / d) hud
          have hlu_le : Real.log ((u / d : ℕ) : ℝ) ≤ Real.log u :=
            Real.log_le_log (by positivity) (by exact_mod_cast Nat.div_le_self u d)
          have hlu_nn : 0 ≤ Real.log ((u / d : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hud)
          exact h1.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith) (by linarith) 7) hK8_pos.le)
      _ = (∑ d ∈ Finset.Icc 1 u, |cArith d|) * (K8 * (Real.log u + 1) ^ 7) := (Finset.sum_mul _ _ _).symm
      _ ≤ W * (K8 * (Real.log u + 1) ^ 7) := by
          have hsum_le : ∑ d ∈ Finset.Icc 1 u, |cArith d| ≤ W :=
            (summable_abs_cArith.sum_le_tsum (Finset.Icc 1 u) fun _ _ => abs_nonneg _).trans hW0_le
          exact mul_le_mul_of_nonneg_right hsum_le (by positivity)
      _ = K8 * W * (Real.log u + 1) ^ 7 := by ring
  have hE2 : |∑ d ∈ Finset.Icc 1 u, cArith d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ)) -
      (∑ d ∈ Finset.Icc 1 u, cArith d) * ((Real.log u) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ))| ≤
      (8 * (CL1 + 1) * W / ((Nat.factorial 8 : ℕ) : ℝ)) * (Real.log u + 1) ^ 7 := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    calc |∑ d ∈ Finset.Icc 1 u, (cArith d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ)) -
            cArith d * ((Real.log u) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ)))|
        ≤ ∑ d ∈ Finset.Icc 1 u, |cArith d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ)) -
            cArith d * ((Real.log u) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 u, (|cArith d| * (d : ℝ) ^ ((1 : ℝ) / 4)) *
            (8 * (CL1 + 1) / ((Nat.factorial 8 : ℕ) : ℝ) * (Real.log u + 1) ^ 7) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          have hud : 1 ≤ u / d := Nat.div_pos hd.2 hd.1
          have hud_r : (0 : ℝ) < ((u / d : ℕ) : ℝ) := Nat.cast_pos.mpr hud
          have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd.1
          have hu_pos : (0 : ℝ) < u := Nat.cast_pos.mpr hu1
          have hlog_ud_nn : 0 ≤ Real.log ((u / d : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hud)
          have hlog_ud_le : Real.log ((u / d : ℕ) : ℝ) ≤ Real.log u :=
            Real.log_le_log hud_r (by exact_mod_cast Nat.div_le_self u d)
          have hgap : Real.log u - Real.log ((u / d : ℕ) : ℝ) ≤ Real.log d + Real.log 2 := by
            have h2 : (u : ℝ) ≤ 2 * ((u / d : ℕ) : ℝ) * (d : ℝ) := by
              have hnat : u < (u / d + 1) * d := by
                have := Nat.div_add_mod u d; have := Nat.mod_lt u hd.1; nlinarith
              have hnat2 : u / d + 1 ≤ 2 * (u / d) := by omega
              exact_mod_cast (show u ≤ 2 * (u / d) * d by nlinarith)
            have hlg := Real.log_le_log hu_pos h2
            rw [Real.log_mul (by positivity) hd_pos.ne', Real.log_mul (by norm_num) hud_r.ne'] at hlg
            linarith
          have hpow := (pow_sub_pow_bounds hlog_ud_nn hlog_ud_le 7).2
          have hdiff8 : |(Real.log ((u / d : ℕ) : ℝ)) ^ 8 - (Real.log u) ^ 8| ≤
              8 * (Real.log u + 1) ^ 7 * (Real.log d + Real.log 2) := by
            have hle : (Real.log ((u / d : ℕ) : ℝ)) ^ 8 ≤ (Real.log u) ^ 8 :=
              pow_le_pow_left₀ hlog_ud_nn hlog_ud_le 8
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
            have hlu7 : (Real.log u) ^ 7 ≤ (Real.log u + 1) ^ 7 :=
              pow_le_pow_left₀ hlu_pos.le (by linarith) 7
            have hgap_nn : 0 ≤ Real.log u - Real.log ((u / d : ℕ) : ℝ) := sub_nonneg.mpr hlog_ud_le
            calc (Real.log u) ^ 8 - (Real.log ((u / d : ℕ) : ℝ)) ^ 8
                ≤ ((7 + 1 : ℕ) : ℝ) * (Real.log u) ^ 7 * (Real.log u - Real.log ((u / d : ℕ) : ℝ)) := hpow
              _ ≤ 8 * (Real.log u + 1) ^ 7 * (Real.log d + Real.log 2) := by
                  norm_num
                  exact mul_le_mul (mul_le_mul_of_nonneg_left hlu7 (by norm_num)) hgap hgap_nn (by positivity)
          have hlog_d_bound : Real.log d + Real.log 2 ≤ (CL1 + 1) * (d : ℝ) ^ ((1 : ℝ) / 4) := by
            have h1 := hCL1 d hd.1
            have hlog2 : Real.log 2 ≤ 1 := by
              have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
              linarith
            have hdr : 1 ≤ (d : ℝ) ^ ((1 : ℝ) / 4) :=
              Real.one_le_rpow (by exact_mod_cast hd.1) (by norm_num)
            simp only [pow_one] at h1
            nlinarith
          rw [← mul_sub, ← sub_div, abs_mul, abs_div, abs_of_pos hfac8_pos]
          have h1 : |(Real.log ((u / d : ℕ) : ℝ)) ^ 8 - (Real.log u) ^ 8| ≤
              8 * (Real.log u + 1) ^ 7 * ((CL1 + 1) * (d : ℝ) ^ ((1 : ℝ) / 4)) :=
            hdiff8.trans (mul_le_mul_of_nonneg_left hlog_d_bound (by positivity))
          calc |cArith d| * (|(Real.log ((u / d : ℕ) : ℝ)) ^ 8 - (Real.log u) ^ 8| / ((Nat.factorial 8 : ℕ) : ℝ))
              ≤ |cArith d| * ((8 * (Real.log u + 1) ^ 7 * ((CL1 + 1) * (d : ℝ) ^ ((1 : ℝ) / 4))) /
                  ((Nat.factorial 8 : ℕ) : ℝ)) := by gcongr
            _ = (|cArith d| * (d : ℝ) ^ ((1 : ℝ) / 4)) *
                  (8 * (CL1 + 1) / ((Nat.factorial 8 : ℕ) : ℝ) * (Real.log u + 1) ^ 7) := by ring
      _ = (∑ d ∈ Finset.Icc 1 u, |cArith d| * (d : ℝ) ^ ((1 : ℝ) / 4)) *
            (8 * (CL1 + 1) / ((Nat.factorial 8 : ℕ) : ℝ) * (Real.log u + 1) ^ 7) := (Finset.sum_mul _ _ _).symm
      _ ≤ W * (8 * (CL1 + 1) / ((Nat.factorial 8 : ℕ) : ℝ) * (Real.log u + 1) ^ 7) := by
          have hsum_le : ∑ d ∈ Finset.Icc 1 u, |cArith d| * (d : ℝ) ^ ((1 : ℝ) / 4) ≤ W :=
            summable_abs_cArith_rpow.sum_le_tsum (Finset.Icc 1 u) fun _ _ => by positivity
          exact mul_le_mul_of_nonneg_right hsum_le (by positivity)
      _ = (8 * (CL1 + 1) * W / ((Nat.factorial 8 : ℕ) : ℝ)) * (Real.log u + 1) ^ 7 := by ring
  have hE3 : |(∑ d ∈ Finset.Icc 1 u, cArith d) * ((Real.log u) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ)) -
      CP * (Real.log u) ^ 8| ≤
      (CL8 * W / ((Nat.factorial 8 : ℕ) : ℝ)) * (Real.log u + 1) ^ 7 := by
    have hrew : (∑ d ∈ Finset.Icc 1 u, cArith d) * ((Real.log u) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ)) -
        CP * (Real.log u) ^ 8 =
        ((∑ d ∈ Finset.Icc 1 u, cArith d) - CE) * ((Real.log u) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ)) := by
      dsimp only [CP]; ring
    rw [hrew, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.log u) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ))]
    have hu_pos : (0 : ℝ) < u := by positivity
    have htail_u : |(∑ d ∈ Finset.Icc 1 u, cArith d) - CE| ≤ W / (u : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [abs_sub_comm]
      have hfin : Summable (fun d : ℕ => if d ∈ Finset.Icc 1 u then cArith d else 0) :=
        summable_of_ne_finset_zero (s := Finset.Icc 1 u) fun d hd => if_neg hd
      have hsum_fin : ∑' d : ℕ, (if d ∈ Finset.Icc 1 u then cArith d else 0) =
          ∑ d ∈ Finset.Icc 1 u, cArith d := by
        rw [tsum_eq_sum (s := Finset.Icc 1 u) fun d hd => if_neg hd]
        exact Finset.sum_congr rfl fun d hd => if_pos hd
      have hdiff : CE - ∑ d ∈ Finset.Icc 1 u, cArith d =
          ∑' d : ℕ, if d ∈ Finset.Icc 1 u then 0 else cArith d := by
        dsimp only [CE]
        rw [← hsum_fin, ← summable_cArith.tsum_sub hfin]
        congr 1; ext d; split_ifs <;> ring
      rw [hdiff]
      have hrem_abs : Summable (fun d : ℕ => |if d ∈ Finset.Icc 1 u then (0 : ℝ) else cArith d|) := by
        refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun d => ?_) summable_abs_cArith
        split_ifs <;> simp
      calc |∑' d : ℕ, if d ∈ Finset.Icc 1 u then 0 else cArith d|
          ≤ ∑' d : ℕ, |if d ∈ Finset.Icc 1 u then (0 : ℝ) else cArith d| := abs_tsum_le hrem_abs
        _ ≤ ∑' d : ℕ, (|cArith d| * (d : ℝ) ^ ((1 : ℝ) / 4)) / (u : ℝ) ^ ((1 : ℝ) / 4) := by
            apply Summable.tsum_le_tsum _ hrem_abs (summable_abs_cArith_rpow.div_const _)
            intro d
            split_ifs with hd
            · simp; positivity
            · by_cases hd0 : d = 0
              · subst hd0; simp [cArith]
              have hd_gt : u < d := by
                rw [Finset.mem_Icc] at hd; omega
              rw [le_div_iff₀ (Real.rpow_pos_of_pos hu_pos _)]
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow hu_pos.le (by exact_mod_cast hd_gt.le) (by norm_num)) (abs_nonneg _)
        _ = W / (u : ℝ) ^ ((1 : ℝ) / 4) := tsum_div_const
    have hlog8_u := hCL8 u hu1
    have hpow7_ge1 : (1 : ℝ) ≤ (Real.log u + 1) ^ 7 := one_le_pow₀ (by linarith)
    calc |(∑ d ∈ Finset.Icc 1 u, cArith d) - CE| * ((Real.log u) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ))
        ≤ (W / (u : ℝ) ^ ((1 : ℝ) / 4)) * (CL8 * (u : ℝ) ^ ((1 : ℝ) / 4) / ((Nat.factorial 8 : ℕ) : ℝ)) := by
          gcongr
      _ = CL8 * W / ((Nat.factorial 8 : ℕ) : ℝ) := by
          have hur : (u : ℝ) ^ ((1 : ℝ) / 4) ≠ 0 := (Real.rpow_pos_of_pos hu_pos _).ne'
          field_simp
      _ = (CL8 * W / ((Nat.factorial 8 : ℕ) : ℝ)) * 1 := (mul_one _).symm
      _ ≤ (CL8 * W / ((Nat.factorial 8 : ℕ) : ℝ)) * (Real.log u + 1) ^ 7 :=
          mul_le_mul_of_nonneg_left hpow7_ge1 (by positivity)
  have htri1 := abs_sub_le
    (∑ d ∈ Finset.Icc 1 u, cArith d * (∑ q ∈ Finset.Icc 1 (u / d), (tau 8 q : ℝ) / (q : ℝ)))
    (∑ d ∈ Finset.Icc 1 u, cArith d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ)))
    (CP * (Real.log u) ^ 8)
  have htri2 := abs_sub_le
    (∑ d ∈ Finset.Icc 1 u, cArith d * ((Real.log ((u / d : ℕ) : ℝ)) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ)))
    ((∑ d ∈ Finset.Icc 1 u, cArith d) * ((Real.log u) ^ 8 / ((Nat.factorial 8 : ℕ) : ℝ)))
    (CP * (Real.log u) ^ 8)
  have hM0_expand : M0 * (Real.log u + 1) ^ 7 =
      K8 * W * (Real.log u + 1) ^ 7 +
      (8 * (CL1 + 1) * W / ((Nat.factorial 8 : ℕ) : ℝ)) * (Real.log u + 1) ^ 7 +
      (CL8 * W / ((Nat.factorial 8 : ℕ) : ℝ)) * (Real.log u + 1) ^ 7 +
      (Real.log u + 1) ^ 7 := by dsimp only [M0]; ring
  have hnn7 : 0 ≤ (Real.log u + 1) ^ 7 := by positivity
  linarith

end

/- Section 5: 50-Bin Exact Integer Margin and Final Sieve Proof -/

private def Dscale : ℕ := 10000

private def stepInt (k : ℕ) : ℕ :=
  (Dscale / (2 * k) + 1) + (Dscale / (2 * k + 1) + 1)

private def logUbRec : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, b => stepInt (b + n) + logUbRec n b

private def logUbInt (a b : ℕ) : ℕ :=
  ∑ k ∈ Finset.Ico b a, stepInt k

private lemma logUbInt_eq_rec (a b : ℕ) : logUbInt a b = logUbRec (a - b) b := by
  unfold logUbInt
  rcases le_or_gt a b with hab | hab
  · have hsub : a - b = 0 := Nat.sub_eq_zero_of_le hab
    rw [hsub, Finset.Ico_eq_empty_of_le hab, Finset.sum_empty]; rfl
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hab.le
    clear hab
    rw [Nat.add_sub_cancel_left]
    induction n with
    | zero => simp [logUbRec]
    | succ n ih =>
      have hIco : Finset.Ico b (b + (n + 1)) = insert (b + n) (Finset.Ico b (b + n)) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hIco, Finset.sum_insert (by simp), ih]
      rfl

private def wInt (j : ℕ) : ℤ :=
  (j + 1 : ℤ) ^ 8 - (j : ℤ) ^ 8

private def I0LoRec : ℕ → ℤ
  | 0 => 0
  | n + 1 => (49 - (n : ℤ)) ^ 2 * wInt n + I0LoRec n

private def I0LoInt : ℤ :=
  ∑ j ∈ Finset.range 50, (49 - (j : ℤ)) ^ 2 * wInt j

private lemma I0LoInt_eq_rec : I0LoInt = I0LoRec 50 := by
  unfold I0LoInt
  suffices h : ∀ n : ℕ, ∑ j ∈ Finset.range n, (49 - (j : ℤ)) ^ 2 * wInt j = I0LoRec n from h 50
  intro n
  induction n with
  | zero => simp [I0LoRec]
  | succ n ih => rw [Finset.sum_range_succ, ih, I0LoRec]; ring

private def valRec (j : ℕ) : ℤ :=
  let s : ℤ := 50 - (j : ℤ)
  5400 * s ^ 2 * (Dscale : ℤ) - 40 * s ^ 3 * (Dscale : ℤ) +
    10800 * s ^ 2 * (logUbRec (50 - (50 - j)) (50 - j) : ℤ) - 120 * s ^ 2 * (50 - s) * (Dscale : ℤ)

private def valInt (j : ℕ) : ℤ :=
  let s : ℤ := 50 - (j : ℤ)
  5400 * s ^ 2 * (Dscale : ℤ) - 40 * s ^ 3 * (Dscale : ℤ) +
    10800 * s ^ 2 * (logUbInt 50 (50 - j) : ℤ) - 120 * s ^ 2 * (50 - s) * (Dscale : ℤ)

private lemma valInt_eq_rec (j : ℕ) : valInt j = valRec j := by
  unfold valInt valRec
  rw [logUbInt_eq_rec]

private def J2CoeffRec : ℤ :=
  196 * (Dscale : ℤ) - 72 * (logUbRec 4 5 : ℤ)

private def J2CoeffInt : ℤ :=
  196 * (Dscale : ℤ) - 72 * (logUbInt 9 5 : ℤ)

private lemma J2CoeffInt_eq_rec : J2CoeffInt = J2CoeffRec := by
  unfold J2CoeffInt J2CoeffRec
  rw [logUbInt_eq_rec]

private def Term1Int : ℤ :=
  150 * J2CoeffInt * I0LoInt

private def Term2Rec : ℕ → ℤ
  | 0 => 0
  | n + 1 => wInt n * valRec n + Term2Rec n

private def Term2Int : ℤ :=
  ∑ j ∈ Finset.range 50, wInt j * valInt j

private lemma Term2Int_eq_rec : Term2Int = Term2Rec 50 := by
  unfold Term2Int
  suffices h : ∀ n : ℕ, ∑ j ∈ Finset.range n, wInt j * valInt j = Term2Rec n from h 50
  intro n
  induction n with
  | zero => simp [Term2Rec]
  | succ n ih => rw [Finset.sum_range_succ, ih, valInt_eq_rec, Term2Rec]; ring

private def Term3Int : ℤ :=
  27 * 144 * 625 * (50 : ℤ) ^ 7 * (Dscale : ℤ)

private def TargetInt : ℤ :=
  27 * (50 : ℤ) ^ 10 * (Dscale : ℤ)

private lemma margin_rec_ge :
    TargetInt ≤ 150 * J2CoeffRec * I0LoRec 50 - Term2Rec 50 - Term3Int := by decide

private lemma margin_int_ge : TargetInt ≤ Term1Int - Term2Int - Term3Int := by
  unfold Term1Int
  rw [J2CoeffInt_eq_rec, I0LoInt_eq_rec, Term2Int_eq_rec]
  exact margin_rec_ge

private lemma J2CoeffInt_pos : 0 < J2CoeffInt := by
  rw [J2CoeffInt_eq_rec]; decide

private lemma I0LoInt_pos : 0 < I0LoInt := by
  rw [I0LoInt_eq_rec]; decide

private lemma valInt_nonneg : ∀ j : ℕ, j < 50 → (0 : ℤ) ≤ valInt j := by
  have h : ∀ i : Fin 50, (0 : ℤ) ≤ valRec i.val := by decide
  intro j hj
  rw [valInt_eq_rec]
  exact h ⟨j, hj⟩

noncomputable section

private lemma real_log_div_le_logUbInt {a b : ℕ} (hb : 1 ≤ b) (hba : b ≤ a) :
    Real.log ((a : ℝ) / (b : ℝ)) ≤ (logUbInt a b : ℝ) / (Dscale : ℝ) := by
  induction a with
  | zero => omega
  | succ a ih =>
    rcases eq_or_lt_of_le hba with rfl | hlt
    · simp [logUbInt]
    · have hba' : b ≤ a := Nat.lt_succ_iff.mp hlt
      have ha1 : 1 ≤ a := hb.trans hba'
      have ha_pos : (0 : ℝ) < a := by positivity
      have hb_pos : (0 : ℝ) < b := by positivity
      have hD_pos : (0 : ℝ) < Dscale := by norm_num [Dscale]
      have hIco : Finset.Ico b (a + 1) = insert a (Finset.Ico b a) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hlog_step : Real.log (((a + 1 : ℕ) : ℝ) / (a : ℝ)) ≤ (stepInt a : ℝ) / (Dscale : ℝ) := by
        have h2a_pos : (0 : ℝ) < (2 * a : ℕ) := by positivity
        have h2a1_pos : (0 : ℝ) < (2 * a + 1 : ℕ) := by positivity
        have h2a2_pos : (0 : ℝ) < (2 * a + 2 : ℕ) := by positivity
        have hprod : ((a + 1 : ℕ) : ℝ) / (a : ℝ) =
            (((2 * a + 1 : ℕ) : ℝ) / ((2 * a : ℕ) : ℝ)) *
            (((2 * a + 2 : ℕ) : ℝ) / ((2 * a + 1 : ℕ) : ℝ)) := by
          push_cast; field_simp
        rw [hprod, Real.log_mul (div_pos h2a1_pos h2a_pos).ne' (div_pos h2a2_pos h2a1_pos).ne']
        have h1 := Real.log_le_sub_one_of_pos (div_pos h2a1_pos h2a_pos)
        have h2 := Real.log_le_sub_one_of_pos (div_pos h2a2_pos h2a1_pos)
        have hs1 : ((2 * a + 1 : ℕ) : ℝ) / ((2 * a : ℕ) : ℝ) - 1 = 1 / ((2 * a : ℕ) : ℝ) := by
          push_cast; field_simp; ring
        have hs2 : ((2 * a + 2 : ℕ) : ℝ) / ((2 * a + 1 : ℕ) : ℝ) - 1 = 1 / ((2 * a + 1 : ℕ) : ℝ) := by
          push_cast; field_simp; ring
        have hnat_div : ∀ m : ℕ, 0 < m → (1 : ℝ) / (m : ℝ) ≤ ((Dscale / m + 1 : ℕ) : ℝ) / (Dscale : ℝ) := by
          intro m hm
          have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
          rw [div_le_div_iff₀ hm_pos hD_pos, one_mul]
          have hltm : Dscale < (Dscale / m + 1) * m := by
            have := Nat.div_add_mod Dscale m; have := Nat.mod_lt Dscale hm; nlinarith
          have hcast : (Dscale : ℝ) < ((Dscale / m + 1 : ℕ) : ℝ) * (m : ℝ) := by exact_mod_cast hltm
          linarith
        have hd1 := hnat_div (2 * a) (by omega)
        have hd2 := hnat_div (2 * a + 1) (by omega)
        have hrhs : (stepInt a : ℝ) / (Dscale : ℝ) =
            ((Dscale / (2 * a) + 1 : ℕ) : ℝ) / (Dscale : ℝ) +
            ((Dscale / (2 * a + 1) + 1 : ℕ) : ℝ) / (Dscale : ℝ) := by
          dsimp only [stepInt]; rw [Nat.cast_add, add_div]
        linarith
      have hsplit : Real.log (((a + 1 : ℕ) : ℝ) / (b : ℝ)) =
          Real.log ((a : ℝ) / (b : ℝ)) + Real.log (((a + 1 : ℕ) : ℝ) / (a : ℝ)) := by
        rw [← Real.log_mul (div_pos ha_pos hb_pos).ne' (div_pos (by positivity) ha_pos).ne']
        congr 1; field_simp
      have hrhs_add : (logUbInt (a + 1) b : ℝ) / (Dscale : ℝ) =
          (stepInt a : ℝ) / (Dscale : ℝ) + (logUbInt a b : ℝ) / (Dscale : ℝ) := by
        unfold logUbInt
        rw [hIco, Finset.sum_insert (by simp), Nat.cast_add, add_div]
      linarith [ih hba']

private def Score (B n : ℕ) : ℝ :=
  (36 : ℝ) - ((F n).primeFactors.card : ℝ) - 36 * (((F n).primeFactors.filter (· ≤ B)).card : ℝ)

private lemma score_le_36 (B n : ℕ) : Score B n ≤ 36 := by
  unfold Score
  have h1 : (0 : ℝ) ≤ ((F n).primeFactors.card : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (((F n).primeFactors.filter (· ≤ B)).card : ℝ) := Nat.cast_nonneg _
  linarith

private lemma mem_U_of_score_pos {B n : ℕ} (hB : 5040 ≤ B) (hpos : 0 < Score B n) :
    (∀ q ∈ P, ∀ p ∈ (q * n + 1).primeFactors, B < p) ∧
    (∑ q ∈ P, (q * n + 1).primeFactors.card) ≤ 35 := by
  unfold Score at hpos
  have hfilt0 : ((F n).primeFactors.filter (· ≤ B)).card = 0 := by
    by_contra hne
    have hge1 : 1 ≤ ((F n).primeFactors.filter (· ≤ B)).card := Nat.pos_of_ne_zero hne
    have hge1r : (1 : ℝ) ≤ (((F n).primeFactors.filter (· ≤ B)).card : ℝ) := by exact_mod_cast hge1
    have hnn : (0 : ℝ) ≤ ((F n).primeFactors.card : ℝ) := Nat.cast_nonneg _
    linarith
  have hrough : ∀ p ∈ (F n).primeFactors, B < p := by
    intro p hp
    by_contra! hle
    have hmem : p ∈ (F n).primeFactors.filter (· ≤ B) := Finset.mem_filter.mpr ⟨hp, hle⟩
    have := Finset.card_pos.mpr ⟨p, hmem⟩
    omega
  constructor
  · intro q hq p hp
    rw [Nat.mem_primeFactors] at hp
    exact hrough p (Nat.mem_primeFactors.mpr
      ⟨hp.1, (prime_dvd_F_iff hp.1).mpr ⟨q, hq, hp.2.1⟩, (F_pos n).ne'⟩)
  · rw [sum_primeFactors_card_eq_F hB hrough]
    rw [hfilt0, Nat.cast_zero, mul_zero, sub_zero] at hpos
    have hlt36 : ((F n).primeFactors.card : ℝ) < 36 := by linarith
    have hlt36n : (F n).primeFactors.card < 36 := by exact_mod_cast hlt36
    omega

private lemma score_ge_richert {B X y n : ℕ} (hy : 2 ≤ y) (hX : 1 ≤ X) (hn : n ≤ 2 * X) :
    36 - 8 * Real.log (119 * (X : ℝ)) / Real.log (y : ℝ) -
      ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F n), (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) -
      36 * ∑ _p ∈ (Nat.primesLE B).filter (fun p => p ∣ F n), (1 : ℝ) ≤ Score B n := by
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  -- Show (F n).primeFactors.filter (· ≤ B) = (Nat.primesLE B).filter (fun p => p ∣ F n)
  have hBset : (F n).primeFactors.filter (· ≤ B) = (Nat.primesLE B).filter (fun p => p ∣ F n) := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Nat.mem_primesLE, (F_pos n).ne',
      ne_eq, not_false_eq_true, and_true]
    tauto
  have hBcard : (((F n).primeFactors.filter (· ≤ B)).card : ℝ) =
      ∑ p ∈ (Nat.primesLE B).filter (fun p => p ∣ F n), (1 : ℝ) := by
    rw [hBset, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Show (F n).primeFactors.card ≤ log(F n)/log y + ∑_{p ≤ y, p ∣ F n} (1 - log p / log y)
  have hprod_dvd : (∏ p ∈ (F n).primeFactors, p) ∣ F n :=
    Nat.prod_primeFactors_dvd (F n)
  have hprod_le : (∏ p ∈ (F n).primeFactors, (p : ℝ)) ≤ (F n : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (F_pos n) hprod_dvd
  have hsum_log : ∑ p ∈ (F n).primeFactors, Real.log (p : ℝ) ≤ Real.log (F n : ℝ) := by
    rw [← Real.log_prod (fun p hp => (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos).ne')]
    exact Real.log_le_log
      (Finset.prod_pos fun _p hp => Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos) hprod_le
  have hlogF_le : Real.log (F n : ℝ) ≤ 8 * Real.log (119 * (X : ℝ)) := by
    have hFle : (F n : ℝ) ≤ (119 * (X : ℝ)) ^ 8 := by exact_mod_cast F_le_of_le hX hn
    have hlg := Real.log_le_log (Nat.cast_pos.mpr (F_pos n)) hFle
    rwa [Real.log_pow] at hlg
  have hcard_le : ((F n).primeFactors.card : ℝ) ≤
      8 * Real.log (119 * (X : ℝ)) / Real.log (y : ℝ) +
      ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F n), (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) := by
    have hsplit : ((F n).primeFactors.card : ℝ) =
        (∑ p ∈ (F n).primeFactors, Real.log (p : ℝ)) / Real.log (y : ℝ) +
        ∑ p ∈ (F n).primeFactors, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      simp [Finset.sum_const]
    rw [hsplit]
    have h1 : (∑ p ∈ (F n).primeFactors, Real.log (p : ℝ)) / Real.log (y : ℝ) ≤
        8 * Real.log (119 * (X : ℝ)) / Real.log (y : ℝ) :=
      div_le_div_of_nonneg_right (hsum_log.trans hlogF_le) hlogy.le
    have h2 : ∑ p ∈ (F n).primeFactors, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) ≤
        ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F n), (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) := by
      have hpf_y : (F n).primeFactors.filter (· ≤ y) = (Nat.primesLE y).filter (fun p => p ∣ F n) := by
        ext p
        simp only [Finset.mem_filter, Nat.mem_primeFactors, Nat.mem_primesLE, (F_pos n).ne',
          ne_eq, not_false_eq_true, and_true]
        tauto
      rw [← Finset.sum_filter_add_sum_filter_not (F n).primeFactors (· ≤ y), hpf_y]
      have hneg : ∑ p ∈ (F n).primeFactors.filter (fun p => ¬ p ≤ y),
          (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) ≤ 0 := by
        apply Finset.sum_nonpos
        intro p hp
        have hgt : y < p := by have := (Finset.mem_filter.mp hp).2; omega
        have hle : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast hgt.le)
        have : 1 ≤ Real.log (p : ℝ) / Real.log (y : ℝ) := (one_le_div hlogy).mpr hle
        linarith
      linarith
    linarith
  unfold Score
  rw [hBcard]
  linarith

private lemma selbergW_nonneg (R n : ℕ) : 0 ≤ selbergW R n :=
  sq_nonneg _

private lemma selbergW_expand (R n : ℕ) :
    selbergW R n = ∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R,
      if Nat.lcm d1 d2 ∣ F n then lam R d1 * lam R d2 else 0 := by
  unfold selbergW
  rw [sq, Finset.sum_mul]
  trans ∑ d1 ∈ (sfLE R).filter (fun d => d ∣ F n),
      ∑ d2 ∈ (sfLE R).filter (fun d => d ∣ F n), lam R d1 * lam R d2
  · refine Finset.sum_congr rfl fun d1 _ => Finset.mul_sum _ _ _
  · rw [Finset.sum_filter (s := sfLE R)]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    by_cases h1 : d1 ∣ F n
    · rw [if_pos h1, Finset.sum_filter (s := sfLE R)]
      refine Finset.sum_congr rfl fun d2 _ => ?_
      by_cases h2 : d2 ∣ F n
      · rw [if_pos h2, if_pos (Nat.lcm_dvd h1 h2)]
      · rw [if_neg h2, if_neg (fun h => h2 ((Nat.dvd_lcm_right d1 d2).trans h))]
    · rw [if_neg h1]
      symm
      refine Finset.sum_eq_zero fun d2 _ => ?_
      rw [if_neg (fun h => h1 ((Nat.dvd_lcm_left d1 d2).trans h))]

private lemma squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have h1 : p * p ∣ a * b := by
    have : Nat.lcm a b ∣ a * b := Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)
    exact hpp.trans this
  -- Actually check directly via p^2 ∣ lcm a b → p^2 ∣ a ∨ p^2 ∣ b!
  have hdvd_pow : p ^ 2 ∣ Nat.lcm a b := by simpa [sq] using hpp
  have hlcm_ne : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha.ne_zero hb.ne_zero
  have hfac : 2 ≤ (Nat.lcm a b).factorization p := (hp.pow_dvd_iff_le_factorization hlcm_ne).mp hdvd_pow
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero, Finsupp.sup_apply] at hfac
  rcases le_max_iff.mp hfac with hfa | hfb
  · have : p * p ∣ a := by
      simpa [sq] using (hp.pow_dvd_iff_le_factorization ha.ne_zero).mpr hfa
    exact hp.not_isUnit (ha p this)
  · have : p * p ∣ b := by
      simpa [sq] using (hp.pow_dvd_iff_le_factorization hb.ne_zero).mpr hfb
    exact hp.not_isUnit (hb p this)

private lemma sum_selbergW_approx {C_om : ℝ} (hCom_pos : 0 < C_om)
    (hCom : ∀ d : ℕ, Squarefree d → (omegaD d : ℝ) ≤ C_om * (d : ℝ) ^ ((1 : ℝ) / 100))
    {X R : ℕ} (hR : 2 ≤ R) :
    |∑ n ∈ Finset.Ioc X (2 * X), selbergW R n -
      (X : ℝ) * ∑ r ∈ sfLE R, (zW R r) ^ 2 / phiG r| ≤
      C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 := by
  have hswap : ∑ n ∈ Finset.Ioc X (2 * X), selbergW R n =
      ∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R, lam R d1 * lam R d2 *
        (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F n)).card : ℝ) := by
    simp_rw [selbergW_expand]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d2 _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hswap, ← selberg_diag_main R, Finset.mul_sum]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R,
          (lam R d1 * lam R d2 *
            (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F n)).card : ℝ) -
           (X : ℝ) * (lam R d1 * lam R d2 * gF (Nat.lcm d1 d2)))|
      ≤ ∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R,
          |lam R d1 * lam R d2 *
            (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F n)).card : ℝ) -
           (X : ℝ) * (lam R d1 * lam R d2 * gF (Nat.lcm d1 d2))| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _d1 ∈ sfLE R, ∑ _d2 ∈ sfLE R,
          C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 := by
        apply Finset.sum_le_sum; intro d1 hd1
        apply Finset.sum_le_sum; intro d2 hd2
        have hsf1 := (Finset.mem_filter.mp hd1).2
        have hsf2 := (Finset.mem_filter.mp hd2).2
        have hI1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hd1).1
        have hI2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hd2).1
        have hsf_lcm := squarefree_lcm hsf1 hsf2
        have hrew : lam R d1 * lam R d2 *
              (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F n)).card : ℝ) -
            (X : ℝ) * (lam R d1 * lam R d2 * gF (Nat.lcm d1 d2)) =
            lam R d1 * lam R d2 *
              ((((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F n)).card : ℝ) -
                (X : ℝ) * ((omegaD (Nat.lcm d1 d2) : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ))) := by
          unfold gF; ring
        rw [hrew, abs_mul, abs_mul]
        have hl1 := abs_lam_le_Hsum_sq (d := d1) hR
        have hl2 := abs_lam_le_Hsum_sq (d := d2) hR
        have hcnt := count_dvd_F_Ioc X (Nat.lcm d1 d2) hsf_lcm
        have hom := hCom (Nat.lcm d1 d2) hsf_lcm
        have hlcm_le : (Nat.lcm d1 d2 : ℝ) ≤ (R : ℝ) ^ 2 := by
          have hnat : Nat.lcm d1 d2 ≤ d1 * d2 := Nat.le_of_dvd (Nat.mul_pos hI1.1 hI2.1)
            (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
          have hnat2 : d1 * d2 ≤ R * R := Nat.mul_le_mul hI1.2 hI2.2
          have : (Nat.lcm d1 d2 : ℝ) ≤ (R : ℝ) * (R : ℝ) := by exact_mod_cast (hnat.trans hnat2)
          linarith [sq (R : ℝ)]
        have hrpow_le : ((Nat.lcm d1 d2 : ℕ) : ℝ) ^ ((1 : ℝ) / 100) ≤ ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hlcm_le (by norm_num)
        have hprod_lam : |lam R d1| * |lam R d2| ≤ (Hsum R) ^ 4 := by
          calc |lam R d1| * |lam R d2| ≤ (Hsum R) ^ 2 * (Hsum R) ^ 2 :=
                mul_le_mul hl1 hl2 (abs_nonneg _) (sq_nonneg _)
            _ = (Hsum R) ^ 4 := by ring
        have hcnt_le : |(((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F n)).card : ℝ) -
            (X : ℝ) * ((omegaD (Nat.lcm d1 d2) : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ))| ≤
            C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
          hcnt.trans (hom.trans (mul_le_mul_of_nonneg_left hrpow_le hCom_pos.le))
        calc |lam R d1| * |lam R d2| *
              |(((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm d1 d2 ∣ F n)).card : ℝ) -
                (X : ℝ) * ((omegaD (Nat.lcm d1 d2) : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ))|
            ≤ (Hsum R) ^ 4 * (C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100)) :=
              mul_le_mul hprod_lam hcnt_le (abs_nonneg _) (by positivity)
          _ = C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 := by ring
    _ ≤ C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 := by
        have hcard : ((sfLE R).card : ℝ) ≤ (R : ℝ) := by
          have hsub : sfLE R ⊆ Finset.Icc 1 R := Finset.filter_subset _ _
          have h1 : (sfLE R).card ≤ (Finset.Icc 1 R).card := Finset.card_le_card hsub
          rw [Nat.card_Icc] at h1
          exact_mod_cast (show (sfLE R).card ≤ R by omega)
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hnn : 0 ≤ C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 := by positivity
        have hsq : ((sfLE R).card : ℝ) * ((sfLE R).card : ℝ) ≤ (R : ℝ) ^ 2 := by
          rw [sq]; exact mul_le_mul hcard hcard (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        calc ((sfLE R).card : ℝ) * (((sfLE R).card : ℝ) * (C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4))
            = (((sfLE R).card : ℝ) * ((sfLE R).card : ℝ)) * (C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4) := by ring
          _ ≤ (R : ℝ) ^ 2 * (C_om * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4) :=
              mul_le_mul_of_nonneg_right hsq hnn
          _ = C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 := by ring

private lemma sum_selbergW_prime_approx {C_om : ℝ} (hCom_pos : 0 < C_om)
    (hCom : ∀ d : ℕ, Squarefree d → (omegaD d : ℝ) ≤ C_om * (d : ℝ) ^ ((1 : ℝ) / 100))
    {X R p : ℕ} (hR : 2 ≤ R) (hp : p.Prime) :
    |∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F n), selbergW R n -
      (X : ℝ) * gF p * ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r| ≤
      C_om * (R : ℝ) ^ 2 * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 := by
  have hswap : ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F n), selbergW R n =
      ∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R, lam R d1 * lam R d2 *
        (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm p (Nat.lcm d1 d2) ∣ F n)).card : ℝ) := by
    simp_rw [selbergW_expand]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d2 _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 3
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn, hpn⟩, hln⟩
      exact ⟨hn, Nat.lcm_dvd hpn hln⟩
    · rintro ⟨hn, hpln⟩
      exact ⟨⟨hn, (Nat.dvd_lcm_left _ _).trans hpln⟩, (Nat.dvd_lcm_right _ _).trans hpln⟩
  rw [hswap]
  have hdiag := selberg_diag_prime R p hp
  have hmain_eq : (X : ℝ) * gF p *
      ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r =
      (X : ℝ) * ∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R,
        lam R d1 * lam R d2 * gF (Nat.lcm p (Nat.lcm d1 d2)) := by
    rw [hdiag]; ring
  rw [hmain_eq, Finset.mul_sum]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R,
          (lam R d1 * lam R d2 *
            (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm p (Nat.lcm d1 d2) ∣ F n)).card : ℝ) -
           (X : ℝ) * (lam R d1 * lam R d2 * gF (Nat.lcm p (Nat.lcm d1 d2))))|
      ≤ ∑ d1 ∈ sfLE R, ∑ d2 ∈ sfLE R,
          |lam R d1 * lam R d2 *
            (((Finset.Ioc X (2 * X)).filter (fun n => Nat.lcm p (Nat.lcm d1 d2) ∣ F n)).card : ℝ) -
           (X : ℝ) * (lam R d1 * lam R d2 * gF (Nat.lcm p (Nat.lcm d1 d2)))| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _d1 ∈ sfLE R, ∑ _d2 ∈ sfLE R,
          C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 := by
        apply Finset.sum_le_sum; intro d1 hd1
        apply Finset.sum_le_sum; intro d2 hd2
        have hsf1 := (Finset.mem_filter.mp hd1).2
        have hsf2 := (Finset.mem_filter.mp hd2).2
        have hI1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hd1).1
        have hI2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hd2).1
        have hsf_lcm := squarefree_lcm hp.squarefree (squarefree_lcm hsf1 hsf2)
        let D := Nat.lcm p (Nat.lcm d1 d2)
        have hrew : lam R d1 * lam R d2 *
              (((Finset.Ioc X (2 * X)).filter (fun n => D ∣ F n)).card : ℝ) -
            (X : ℝ) * (lam R d1 * lam R d2 * gF D) =
            lam R d1 * lam R d2 *
              ((((Finset.Ioc X (2 * X)).filter (fun n => D ∣ F n)).card : ℝ) -
                (X : ℝ) * ((omegaD D : ℝ) / (D : ℝ))) := by
          unfold gF; ring
        rw [hrew, abs_mul, abs_mul]
        have hl1 := abs_lam_le_Hsum_sq (d := d1) hR
        have hl2 := abs_lam_le_Hsum_sq (d := d2) hR
        have hcnt := count_dvd_F_Ioc X D hsf_lcm
        have hom := hCom D hsf_lcm
        have hD_le : (D : ℝ) ≤ (p : ℝ) * (R : ℝ) ^ 2 := by
          have h1 : Nat.lcm d1 d2 ≤ d1 * d2 := Nat.le_of_dvd (Nat.mul_pos hI1.1 hI2.1)
            (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
          have h2 : D ≤ p * Nat.lcm d1 d2 := Nat.le_of_dvd
            (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hsf1.ne_zero hsf2.ne_zero)))
            (Nat.lcm_dvd (dvd_mul_right p _) (dvd_mul_left _ p))
          have h3 : d1 * d2 ≤ R * R := Nat.mul_le_mul hI1.2 hI2.2
          have hnat : D ≤ p * (R * R) := h2.trans (Nat.mul_le_mul_left p (h1.trans h3))
          have hcast : (D : ℝ) ≤ (p : ℝ) * ((R : ℝ) * (R : ℝ)) := by exact_mod_cast hnat
          linarith [sq (R : ℝ)]
        have hrpow_le : (D : ℝ) ^ ((1 : ℝ) / 100) ≤ ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hD_le (by norm_num)
        have hprod_lam : |lam R d1| * |lam R d2| ≤ (Hsum R) ^ 4 := by
          calc |lam R d1| * |lam R d2| ≤ (Hsum R) ^ 2 * (Hsum R) ^ 2 :=
                mul_le_mul hl1 hl2 (abs_nonneg _) (sq_nonneg _)
            _ = (Hsum R) ^ 4 := by ring
        have hcnt_le : |(((Finset.Ioc X (2 * X)).filter (fun n => D ∣ F n)).card : ℝ) -
            (X : ℝ) * ((omegaD D : ℝ) / (D : ℝ))| ≤
            C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
          hcnt.trans (hom.trans (mul_le_mul_of_nonneg_left hrpow_le hCom_pos.le))
        calc |lam R d1| * |lam R d2| *
              |(((Finset.Ioc X (2 * X)).filter (fun n => D ∣ F n)).card : ℝ) -
                (X : ℝ) * ((omegaD D : ℝ) / (D : ℝ))|
            ≤ (Hsum R) ^ 4 * (C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100)) :=
              mul_le_mul hprod_lam hcnt_le (abs_nonneg _) (by positivity)
          _ = C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 := by ring
    _ ≤ C_om * (R : ℝ) ^ 2 * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 := by
        have hcard : ((sfLE R).card : ℝ) ≤ (R : ℝ) := by
          have hsub : sfLE R ⊆ Finset.Icc 1 R := Finset.filter_subset _ _
          have h1 : (sfLE R).card ≤ (Finset.Icc 1 R).card := Finset.card_le_card hsub
          rw [Nat.card_Icc] at h1
          exact_mod_cast (show (sfLE R).card ≤ R by omega)
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hnn : 0 ≤ C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 := by positivity
        have hsq : ((sfLE R).card : ℝ) * ((sfLE R).card : ℝ) ≤ (R : ℝ) ^ 2 := by
          rw [sq]; exact mul_le_mul hcard hcard (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        calc ((sfLE R).card : ℝ) * (((sfLE R).card : ℝ) * (C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4))
            = (((sfLE R).card : ℝ) * ((sfLE R).card : ℝ)) * (C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4) := by ring
          _ ≤ (R : ℝ) ^ 2 * (C_om * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4) :=
              mul_le_mul_of_nonneg_right hsq hnn
          _ = C_om * (R : ℝ) ^ 2 * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 := by ring

private lemma selbergW_le_of_primeFactors_le_35 {R n : ℕ} (hR : 2 ≤ R)
    (hcard : (F n).primeFactors.card ≤ 35) :
    selbergW R n ≤ ((2 : ℝ) ^ 35 * (Hsum R) ^ 2) ^ 2 := by
  -- Every d ∈ (sfLE R).filter (· ∣ F n) is determined by d.primeFactors ⊆ (F n).primeFactors
  have hcnt : ((sfLE R).filter (fun d => d ∣ F n)).card ≤ 2 ^ 35 := by
    have hinj : Set.InjOn Nat.primeFactors ↑((sfLE R).filter (fun d => d ∣ F n)) := by
      intro d1 hd1 d2 hd2 heq
      have hsf1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hd1).1).2
      have hsf2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hd2).1).2
      rw [← Nat.prod_primeFactors_of_squarefree hsf1, ← Nat.prod_primeFactors_of_squarefree hsf2, heq]
    have himg : ((sfLE R).filter (fun d => d ∣ F n)).image Nat.primeFactors ⊆
        (F n).primeFactors.powerset := by
      intro s hs
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
      rw [Finset.mem_powerset]
      exact Nat.primeFactors_mono (Finset.mem_filter.mp hd).2 (F_pos n).ne'
    calc ((sfLE R).filter (fun d => d ∣ F n)).card
        = (((sfLE R).filter (fun d => d ∣ F n)).image Nat.primeFactors).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (F n).primeFactors.powerset.card := Finset.card_le_card himg
      _ = 2 ^ (F n).primeFactors.card := Finset.card_powerset _
      _ ≤ 2 ^ 35 := Nat.pow_le_pow_right (by norm_num) hcard
  have habs : |∑ d ∈ (sfLE R).filter (fun d => d ∣ F n), lam R d| ≤
      (2 : ℝ) ^ 35 * (Hsum R) ^ 2 := by
    calc |∑ d ∈ (sfLE R).filter (fun d => d ∣ F n), lam R d|
        ≤ ∑ d ∈ (sfLE R).filter (fun d => d ∣ F n), |lam R d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ (sfLE R).filter (fun d => d ∣ F n), (Hsum R) ^ 2 :=
          Finset.sum_le_sum fun d _ => abs_lam_le_Hsum_sq hR
      _ = (((sfLE R).filter (fun d => d ∣ F n)).card : ℝ) * (Hsum R) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ 35 * (Hsum R) ^ 2 := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcnt) (sq_nonneg _)
  unfold selbergW
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

private def sfBin (B j : ℕ) : Finset ℕ :=
  if j = 0 then sfLE (B ^ 2) else sfLE (B ^ (2 * (j + 1))) \ sfLE (B ^ (2 * j))

private lemma sum_sfLE_eq_sum_sfBin {B : ℕ} (hB : 2 ≤ B) (f : ℕ → ℝ) :
    ∑ r ∈ sfLE (B ^ 100), f r = ∑ j ∈ Finset.range 50, ∑ r ∈ sfBin B j, f r := by
  suffices h : ∀ m : ℕ, 1 ≤ m →
      ∑ r ∈ sfLE (B ^ (2 * m)), f r = ∑ j ∈ Finset.range m, ∑ r ∈ sfBin B j, f r by
    simpa using h 50 (by norm_num)
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases m with _ | m
    · simp [sfBin]
    · rw [Finset.sum_range_succ, ← ih (by omega)]
      have hsub : sfLE (B ^ (2 * (m + 1))) ⊆ sfLE (B ^ (2 * (m + 2))) := by
        intro r hr
        rw [sfLE, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
        exact ⟨⟨hr.1.1, hr.1.2.trans (Nat.pow_le_pow_right (by omega) (by omega))⟩, hr.2⟩
      simp only [sfBin, Nat.succ_ne_zero, ↓reduceIte]
      rw [Finset.sum_sdiff_eq_sub hsub]
      ring

private lemma Hsum_sfBin_bound {C_P M0 : ℝ} (_hCP : 0 < C_P) (hM0 : 0 < M0)
    (hH : ∀ u : ℕ, 2 ≤ u → |Hsum u - C_P * (Real.log u) ^ 8| ≤ M0 * (Real.log u + 1) ^ 7)
    {B j : ℕ} (hB : 2 ≤ B) (hj : j < 50) :
    |∑ r ∈ sfBin B j, (1 : ℝ) / phiG r -
      C_P * ((wInt j : ℝ) / (50 : ℝ) ^ 8) * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 8| ≤
      2 * M0 * (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 7 := by
  have hlogR : Real.log ((B ^ 100 : ℕ) : ℝ) = 100 * Real.log (B : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlog_pow : ∀ t : ℕ, Real.log ((B ^ (2 * t) : ℕ) : ℝ) =
      ((t : ℝ) / 50) * Real.log ((B ^ 100 : ℕ) : ℝ) := by
    intro t
    rw [Nat.cast_pow, Real.log_pow, hlogR]
    push_cast; ring
  have hw_cast : (wInt j : ℝ) = ((j + 1 : ℕ) : ℝ) ^ 8 - (j : ℝ) ^ 8 := by
    unfold wInt; push_cast; ring
  by_cases hj0 : j = 0
  · subst hj0
    simp only [sfBin, ↓reduceIte]
    have hsum_eq : ∑ r ∈ sfLE (B ^ 2), (1 : ℝ) / phiG r = Hsum (B ^ 2) := rfl
    rw [hsum_eq]
    have hB2 : 2 ≤ B ^ 2 := by nlinarith
    have hb := hH (B ^ 2) hB2
    have hlog2 : Real.log ((B ^ 2 : ℕ) : ℝ) = ((1 : ℝ) / 50) * Real.log ((B ^ 100 : ℕ) : ℝ) := by
      simpa using hlog_pow 1
    have hmain : C_P * (Real.log ((B ^ 2 : ℕ) : ℝ)) ^ 8 =
        C_P * ((wInt 0 : ℝ) / (50 : ℝ) ^ 8) * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 8 := by
      rw [hlog2, hw_cast]; simp; ring
    rw [← hmain]
    have hleR : Real.log ((B ^ 2 : ℕ) : ℝ) ≤ Real.log ((B ^ 100 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega))
    have hpow7 : (Real.log ((B ^ 2 : ℕ) : ℝ) + 1) ^ 7 ≤ (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 7 :=
      pow_le_pow_left₀ (by rw [hlog2]; positivity) (by linarith) 7
    have h1 := hb.trans (mul_le_mul_of_nonneg_left hpow7 hM0.le)
    have hnn : 0 ≤ M0 * (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 7 := by positivity
    linarith
  · simp only [sfBin, hj0, ↓reduceIte]
    have hsub : sfLE (B ^ (2 * j)) ⊆ sfLE (B ^ (2 * (j + 1))) := by
      intro r hr
      rw [sfLE, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
      exact ⟨⟨hr.1.1, hr.1.2.trans (Nat.pow_le_pow_right (by omega) (by omega))⟩, hr.2⟩
    have hsum_eq : ∑ r ∈ sfLE (B ^ (2 * (j + 1))) \ sfLE (B ^ (2 * j)), (1 : ℝ) / phiG r =
        Hsum (B ^ (2 * (j + 1))) - Hsum (B ^ (2 * j)) :=
      Finset.sum_sdiff_eq_sub hsub
    rw [hsum_eq]
    have hge2_a : 2 ≤ B ^ (2 * j) :=
      le_trans hB (Nat.le_self_pow (by omega) B)
    have hge2_b : 2 ≤ B ^ (2 * (j + 1)) :=
      le_trans hB (Nat.le_self_pow (by omega) B)
    have ha := hH (B ^ (2 * j)) hge2_a
    have hb := hH (B ^ (2 * (j + 1))) hge2_b
    have hmain : C_P * (Real.log ((B ^ (2 * (j + 1)) : ℕ) : ℝ)) ^ 8 -
        C_P * (Real.log ((B ^ (2 * j) : ℕ) : ℝ)) ^ 8 =
        C_P * ((wInt j : ℝ) / (50 : ℝ) ^ 8) * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 8 := by
      rw [hlog_pow (j + 1), hlog_pow j, hw_cast]
      ring
    rw [← hmain]
    have hrew : (Hsum (B ^ (2 * (j + 1))) - Hsum (B ^ (2 * j))) -
        (C_P * (Real.log ((B ^ (2 * (j + 1)) : ℕ) : ℝ)) ^ 8 -
          C_P * (Real.log ((B ^ (2 * j) : ℕ) : ℝ)) ^ 8) =
        (Hsum (B ^ (2 * (j + 1))) - C_P * (Real.log ((B ^ (2 * (j + 1)) : ℕ) : ℝ)) ^ 8) -
        (Hsum (B ^ (2 * j)) - C_P * (Real.log ((B ^ (2 * j) : ℕ) : ℝ)) ^ 8) := by ring
    rw [hrew]
    have htri := abs_sub
      (Hsum (B ^ (2 * (j + 1))) - C_P * (Real.log ((B ^ (2 * (j + 1)) : ℕ) : ℝ)) ^ 8)
      (Hsum (B ^ (2 * j)) - C_P * (Real.log ((B ^ (2 * j) : ℕ) : ℝ)) ^ 8)
    have hle_b : Real.log ((B ^ (2 * (j + 1)) : ℕ) : ℝ) ≤ Real.log ((B ^ 100 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega))
    have hle_a : Real.log ((B ^ (2 * j) : ℕ) : ℝ) ≤ Real.log ((B ^ 100 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega))
    have hpb7 : (Real.log ((B ^ (2 * (j + 1)) : ℕ) : ℝ) + 1) ^ 7 ≤
        (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 7 :=
      pow_le_pow_left₀ (by rw [hlog_pow]; positivity) (by linarith) 7
    have hpa7 : (Real.log ((B ^ (2 * j) : ℕ) : ℝ) + 1) ^ 7 ≤
        (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 7 :=
      pow_le_pow_left₀ (by rw [hlog_pow]; positivity) (by linarith) 7
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hpb7 hM0.le)
    have ha' := ha.trans (mul_le_mul_of_nonneg_left hpa7 hM0.le)
    linarith

private lemma sfBin_log_bounds {B j r : ℕ} (hB : 2 ≤ B) (hj : j < 50) (hr : r ∈ sfBin B j) :
    ((49 - (j : ℝ)) / 50) ≤ 1 - Real.log (r : ℝ) / Real.log ((B ^ 100 : ℕ) : ℝ) ∧
    1 - Real.log (r : ℝ) / Real.log ((B ^ 100 : ℕ) : ℝ) ≤ ((50 - (j : ℝ)) / 50) := by
  have hlogR : Real.log ((B ^ 100 : ℕ) : ℝ) = 100 * Real.log (B : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogR_pos : 0 < Real.log ((B ^ 100 : ℕ) : ℝ) := by rw [hlogR]; positivity
  by_cases hj0 : j = 0
  · subst hj0
    simp only [sfBin, ↓reduceIte, sfLE, Finset.mem_filter, Finset.mem_Icc] at hr
    have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr.1.1
    have hlo : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast hr.1.1)
    have hhi : Real.log (r : ℝ) ≤ 2 * Real.log (B : ℝ) := by
      have h := Real.log_le_log hr_pos (by exact_mod_cast hr.1.2 : (r : ℝ) ≤ ((B ^ 2 : ℕ) : ℝ))
      rwa [Nat.cast_pow, Real.log_pow] at h
    constructor
    · rw [hlogR]
      have : Real.log (r : ℝ) / (100 * Real.log (B : ℝ)) ≤ 1 / 50 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      push_cast; linarith
    · have : 0 ≤ Real.log (r : ℝ) / Real.log ((B ^ 100 : ℕ) : ℝ) := div_nonneg hlo hlogR_pos.le
      simp only [Nat.cast_zero, sub_zero]; linarith
  · simp only [sfBin, hj0, ↓reduceIte, Finset.mem_sdiff, sfLE, Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨⟨hr1, hr_hi⟩, hsf⟩, hnot⟩ := hr
    have hr_gt : B ^ (2 * j) < r := by
      by_contra! hle
      exact hnot ⟨⟨hr1, hle⟩, hsf⟩
    have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr1
    have hlo : ((2 * j : ℕ) : ℝ) * Real.log (B : ℝ) ≤ Real.log (r : ℝ) := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < ((B ^ (2 * j) : ℕ) : ℝ))
        (by exact_mod_cast hr_gt.le : ((B ^ (2 * j) : ℕ) : ℝ) ≤ (r : ℝ))
      rwa [Nat.cast_pow, Real.log_pow] at h
    have hhi : Real.log (r : ℝ) ≤ ((2 * (j + 1) : ℕ) : ℝ) * Real.log (B : ℝ) := by
      have h := Real.log_le_log hr_pos (by exact_mod_cast hr_hi : (r : ℝ) ≤ ((B ^ (2 * (j + 1)) : ℕ) : ℝ))
      rwa [Nat.cast_pow, Real.log_pow] at h
    constructor
    · rw [hlogR]
      have : Real.log (r : ℝ) / (100 * Real.log (B : ℝ)) ≤ ((j + 1 : ℕ) : ℝ) / 50 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        push_cast at hhi ⊢; linarith
      push_cast at this ⊢; linarith
    · rw [hlogR]
      have : (j : ℝ) / 50 ≤ Real.log (r : ℝ) / (100 * Real.log (B : ℝ)) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        push_cast at hlo ⊢; linarith
      linarith

private def I0LoR : ℝ := (I0LoInt : ℝ) / (50 : ℝ) ^ 10
private def J2UbR : ℝ := 8 * ((logUbInt 9 5 : ℝ) / (Dscale : ℝ) - 4 / 9)
private def numHiR : ℝ := (Term2Int : ℝ) / (27 * (50 : ℝ) ^ 11 * (Dscale : ℝ))
private def K59const : ℝ := ∑ p ∈ Nat.primesLE 59, (8 : ℝ) * (Real.log (p : ℝ)) ^ 3 / (p : ℝ)

private lemma K59const_nonneg : 0 ≤ K59const := by
  unfold K59const
  apply Finset.sum_nonneg; intro p hp
  have hpp := (Nat.mem_primesLE.mp hp).2
  have := Real.log_nonneg (by exact_mod_cast hpp.one_le : (1 : ℝ) ≤ (p : ℝ))
  positivity

private lemma margin_real_ge :
    (1 / 50 : ℝ) ≤ (36 - 160 / 9 - J2UbR) * I0LoR - numHiR - 144 / 10000 := by
  have hD_pos : (0 : ℝ) < (Dscale : ℝ) := by norm_num [Dscale]
  have hZ : (TargetInt : ℝ) ≤ (Term1Int : ℝ) - (Term2Int : ℝ) - (Term3Int : ℝ) := by
    exact_mod_cast margin_int_ge
  have hden_pos : (0 : ℝ) < 27 * (50 : ℝ) ^ 11 * (Dscale : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_right hZ hden_pos.le
  have h1 : (TargetInt : ℝ) / (27 * (50 : ℝ) ^ 11 * (Dscale : ℝ)) = 1 / 50 := by
    unfold TargetInt; push_cast; field_simp; ring
  have h2 : (Term1Int : ℝ) / (27 * (50 : ℝ) ^ 11 * (Dscale : ℝ)) =
      (36 - 160 / 9 - J2UbR) * I0LoR := by
    unfold Term1Int J2CoeffInt I0LoR J2UbR; push_cast; field_simp; ring
  have h3 : (Term3Int : ℝ) / (27 * (50 : ℝ) ^ 11 * (Dscale : ℝ)) = 144 / 10000 := by
    unfold Term3Int; push_cast; field_simp; ring
  rw [sub_div, sub_div, h1, h2, h3] at hdiv
  exact hdiv

private lemma J2coeff_pos : 0 < 36 - 160 / 9 - J2UbR := by
  have hD_pos : (0 : ℝ) < (Dscale : ℝ) := by norm_num [Dscale]
  have hZ : (0 : ℝ) < (J2CoeffInt : ℝ) := by exact_mod_cast J2CoeffInt_pos
  have heq : 36 - 160 / 9 - J2UbR = (J2CoeffInt : ℝ) / (9 * (Dscale : ℝ)) := by
    unfold J2CoeffInt J2UbR; push_cast; field_simp; ring
  rw [heq]; positivity

private lemma sfBin_subset_sfLE {B j : ℕ} (hB : 2 ≤ B) (hj : j < 50) :
    sfBin B j ⊆ sfLE (B ^ 100) := by
  intro r hr
  by_cases hj0 : j = 0
  · subst hj0
    simp only [sfBin, ↓reduceIte, sfLE, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
    exact ⟨⟨hr.1.1, hr.1.2.trans (Nat.pow_le_pow_right (by omega) (by norm_num))⟩, hr.2⟩
  · simp only [sfBin, hj0, ↓reduceIte, Finset.mem_sdiff, sfLE, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
    exact ⟨⟨hr.1.1.1, hr.1.1.2.trans (Nat.pow_le_pow_right (by omega) (by omega))⟩, hr.1.2⟩

private lemma Isf_lower_bound {C_P M0 : ℝ} (hCP : 0 < C_P) (hM0 : 0 < M0)
    (hH : ∀ u : ℕ, 2 ≤ u → |Hsum u - C_P * (Real.log u) ^ 8| ≤ M0 * (Real.log u + 1) ^ 7)
    {B : ℕ} (hB : 2 ≤ B) :
    C_P * I0LoR * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 8 -
      50 * (2 * M0) * (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 7 ≤
    ∑ r ∈ sfLE (B ^ 100), (zW (B ^ 100) r) ^ 2 / phiG r := by
  let R := B ^ 100
  let logR := Real.log (R : ℝ)
  rw [sum_sfLE_eq_sum_sfBin hB]
  have hbin_lo : ∀ j ∈ Finset.range 50,
      ((49 - (j : ℝ)) / 50) ^ 2 * (C_P * ((wInt j : ℝ) / (50 : ℝ) ^ 8) * logR ^ 8 -
        2 * M0 * (logR + 1) ^ 7) ≤
      ∑ r ∈ sfBin B j, (zW R r) ^ 2 / phiG r := by
    intro j hj
    have hj50 : j < 50 := Finset.mem_range.mp hj
    have hsum_ge : ((49 - (j : ℝ)) / 50) ^ 2 * ∑ r ∈ sfBin B j, (1 : ℝ) / phiG r ≤
        ∑ r ∈ sfBin B j, (zW R r) ^ 2 / phiG r := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro r hr
      rw [zW_sq_eq (sfBin_subset_sfLE hB hj50 hr)]
      have hb := (sfBin_log_bounds hB hj50 hr).1
      have hnn : 0 ≤ (49 - (j : ℝ)) / 50 := by
        have : (j : ℝ) ≤ 49 := by exact_mod_cast (show j ≤ 49 by omega)
        linarith
      have hsq := pow_le_pow_left₀ hnn hb 2
      calc ((49 - (j : ℝ)) / 50) ^ 2 * (1 / phiG r)
          = ((49 - (j : ℝ)) / 50) ^ 2 / phiG r := by ring
        _ ≤ (1 - Real.log (r : ℝ) / logR) ^ 2 / phiG r :=
            div_le_div_of_nonneg_right hsq (phiG_pos r).le
    have hHbin := (abs_le.mp (Hsum_sfBin_bound hCP hM0 hH hB hj50)).1
    exact (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)).trans hsum_ge
  have htot := Finset.sum_le_sum hbin_lo
  have hrew : ∑ j ∈ Finset.range 50,
      ((49 - (j : ℝ)) / 50) ^ 2 * (C_P * ((wInt j : ℝ) / (50 : ℝ) ^ 8) * logR ^ 8 -
        2 * M0 * (logR + 1) ^ 7) =
      C_P * I0LoR * logR ^ 8 -
      (∑ j ∈ Finset.range 50, ((49 - (j : ℝ)) / 50) ^ 2) * (2 * M0 * (logR + 1) ^ 7) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    congr 1
    unfold I0LoR I0LoInt; push_cast
    rw [Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hrew] at htot
  have hsq50 : ∑ j ∈ Finset.range 50, ((49 - (j : ℝ)) / 50) ^ 2 ≤ 50 := by
    calc ∑ j ∈ Finset.range 50, ((49 - (j : ℝ)) / 50) ^ 2
        ≤ ∑ _j ∈ Finset.range 50, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro j hj
          have hj49 : (j : ℝ) ≤ 49 := by exact_mod_cast (show j ≤ 49 by have := Finset.mem_range.mp hj; omega)
          have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          nlinarith
      _ = 50 := by simp
  have hlogR_nn : 0 ≤ logR := Real.log_nonneg (by exact_mod_cast (one_le_pow₀ (by omega : 1 ≤ B)))
  have hnn7 : 0 ≤ 2 * M0 * (logR + 1) ^ 7 := by positivity
  nlinarith only [htot, hsq50, hnn7]

private lemma small_primes_upper_bound {C_P M0 C2 : ℝ} (_hCP : 0 < C_P) (hM0 : 0 < M0) (hC2_pos : 0 < C2)
    (hH : ∀ u : ℕ, 2 ≤ u → |Hsum u - C_P * (Real.log u) ^ 8| ≤ M0 * (Real.log u + 1) ^ 7)
    (hC2 : ∀ n : ℕ, 2 ≤ n → ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 2 / (p : ℝ) ≤
      (1 / 2) * (Real.log n) ^ 2 + C2 * (Real.log n + 1))
    {B : ℕ} (hB : 6000 ≤ B)
    (hH_R_le : Hsum (B ^ 100) ≤ (C_P + 2 * M0) * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 8) :
    36 * ∑ p ∈ Nat.primesLE B, gF p *
      ∑ r ∈ (sfLE (B ^ 100)).filter (fun r => ¬ p ∣ r),
        (zW (B ^ 100) r + zW (B ^ 100) (p * r)) ^ 2 / phiG r ≤
    (144 / 10000) * C_P * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 8 +
    (36 * 8 * C2 * (C_P + 2 * M0) + 36 * 4 * (2 * M0)) * (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 7 := by
  let R := B ^ 100
  let logR := Real.log (R : ℝ)
  let logB := Real.log (B : ℝ)
  have hB2 : 2 ≤ B := by omega
  have hR2 : 2 ≤ R := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hlogB_pos : 0 < logB := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogR_eq : logR = 100 * logB := by dsimp only [logR, R, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogB_ge1 : 1 ≤ logB := by
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hB3 : (3 : ℝ) ≤ B := by exact_mod_cast (show 3 ≤ B by omega)
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hlogR_pos : 0 < logR := by rw [hlogR_eq]; positivity
  have hstep1 : ∑ p ∈ Nat.primesLE B, gF p *
      ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r ≤
      (8 / logR ^ 2 * ∑ p ∈ Nat.primesLE B, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) * Hsum R := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum; intro p hp
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hgp_le : gF p ≤ 8 / (p : ℝ) := by
      rw [gF_prime hprime]
      exact div_le_div_of_nonneg_right (by exact_mod_cast omegaP_le_eight hprime) (Nat.cast_nonneg p)
    have hinner_le : ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r),
        (zW R r + zW R (p * r)) ^ 2 / phiG r ≤ (Real.log (p : ℝ) / logR) ^ 2 * Hsum R := by
      unfold Hsum; rw [Finset.mul_sum]
      calc ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r
          ≤ ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (Real.log (p : ℝ) / logR) ^ 2 * (1 / phiG r) := by
            apply Finset.sum_le_sum; intro r hr
            have hr_mem := (Finset.mem_filter.mp hr).1
            have hr_nd := (Finset.mem_filter.mp hr).2
            rw [zW_add_sq_eq hR2 hprime hr_mem hr_nd]
            have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr_mem).1
            have hmin_nn : 0 ≤ min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR) := by
              have h1 : 0 ≤ Real.log (p : ℝ) / logR :=
                div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) hlogR_pos.le
              have h2 : Real.log (r : ℝ) / logR ≤ 1 := (div_le_one hlogR_pos).mpr
                (Real.log_le_log (by exact_mod_cast hr_Icc.1) (by exact_mod_cast hr_Icc.2))
              exact le_min h1 (by linarith)
            have hsq := pow_le_pow_left₀ hmin_nn (min_le_left _ _) 2
            calc (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2 / phiG r
                ≤ (Real.log (p : ℝ) / logR) ^ 2 / phiG r := div_le_div_of_nonneg_right hsq (phiG_pos r).le
              _ = (Real.log (p : ℝ) / logR) ^ 2 * (1 / phiG r) := by ring
        _ ≤ ∑ r ∈ sfLE R, (Real.log (p : ℝ) / logR) ^ 2 * (1 / phiG r) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun r _ _ => mul_nonneg (sq_nonneg _) (div_nonneg zero_le_one (phiG_pos r).le)
    calc gF p * ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r
        ≤ (8 / (p : ℝ)) * ((Real.log (p : ℝ) / logR) ^ 2 * Hsum R) :=
          mul_le_mul hgp_le hinner_le
            (Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (phiG_pos r).le) (by positivity)
      _ = 8 / logR ^ 2 * (Real.log (p : ℝ) ^ 2 / (p : ℝ)) * Hsum R := by ring
  have hsqB := hC2 B hB2
  have hH_R_ub : Hsum R ≤ C_P * logR ^ 8 + M0 * (logR + 1) ^ 7 := by
    have := (abs_le.mp (hH R hR2)).2; linarith
  have hsumB_le : 8 / logR ^ 2 * ∑ p ∈ Nat.primesLE B, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) ≤
      4 / 10000 + 8 * C2 / logR := by
    have h1 : 8 / logR ^ 2 * ((1 / 2) * logB ^ 2 + C2 * (logB + 1)) =
        4 / 10000 + 8 * C2 * (logB + 1) / logR ^ 2 := by
      rw [hlogR_eq]; field_simp [hlogB_pos.ne']; ring
    have h2 : logB + 1 ≤ logR := by linarith only [hlogR_eq, hlogB_ge1]
    have h3 : 8 * C2 * (logB + 1) / logR ^ 2 ≤ 8 * C2 / logR := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hlogR_pos) hlogR_pos]
      have h2' : (logB + 1) * logR ≤ logR ^ 2 := by nlinarith only [h2, hlogR_pos]
      nlinarith only [hC2_pos, h2']
    have h4 : 8 / logR ^ 2 * ∑ p ∈ Nat.primesLE B, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) ≤
        8 / logR ^ 2 * ((1 / 2) * logB ^ 2 + C2 * (logB + 1)) :=
      mul_le_mul_of_nonneg_left hsqB (by positivity)
    linarith only [h1, h3, h4]
  have hprod_le : (4 / 10000 + 8 * C2 / logR) * Hsum R ≤
      (4 / 10000) * C_P * logR ^ 8 + (8 * C2 * (C_P + 2 * M0) + 4 * (2 * M0)) * (logR + 1) ^ 7 := by
    have h1 : (4 / 10000) * Hsum R ≤ (4 / 10000) * C_P * logR ^ 8 +
        (4 / 10000) * M0 * (logR + 1) ^ 7 := by linarith only [hH_R_ub]
    have h2 : (8 * C2 / logR) * Hsum R ≤ 8 * C2 * (C_P + 2 * M0) * logR ^ 7 := by
      calc (8 * C2 / logR) * Hsum R ≤ (8 * C2 / logR) * ((C_P + 2 * M0) * logR ^ 8) :=
            mul_le_mul_of_nonneg_left hH_R_le (by positivity)
        _ = 8 * C2 * (C_P + 2 * M0) * logR ^ 7 := by field_simp [hlogR_pos.ne']
    have h7 : logR ^ 7 ≤ (logR + 1) ^ 7 := pow_le_pow_left₀ hlogR_pos.le (by linarith) 7
    have hCH_nn : 0 ≤ 8 * C2 * (C_P + 2 * M0) := by positivity
    have hnn7 : 0 ≤ (logR + 1) ^ 7 := by positivity
    nlinarith only [h1, h2, h7, hCH_nn, hnn7, hM0]
  have hcomb := hstep1.trans (mul_le_mul_of_nonneg_right hsumB_le (Hsum_nonneg R)) |>.trans hprod_le
  linarith only [hcomb]

private lemma upper_primes_upper_bound {C4 C5 : ℝ} (_hC4_pos : 0 < C4) (hC5_pos : 0 < C5)
    (hC4 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log b / Real.log a) + C4 / Real.log a)
    (hC5 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      Real.log b - Real.log a - C5 ≤
        ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ))
    {B : ℕ} (hB : 6000 ≤ B) :
    ∑ p ∈ Nat.primesLE (B ^ 180) \ Nat.primesLE (B ^ 100),
      (1 - Real.log (p : ℝ) / Real.log ((B ^ 180 : ℕ) : ℝ)) * (gF p *
        ∑ r ∈ (sfLE (B ^ 100)).filter (fun r => ¬ p ∣ r),
          (zW (B ^ 100) r + zW (B ^ 100) (p * r)) ^ 2 / phiG r) ≤
    (J2UbR + (8 * C4 + 8 * C5) / Real.log ((B ^ 100 : ℕ) : ℝ)) *
      (∑ r ∈ sfLE (B ^ 100), (zW (B ^ 100) r) ^ 2 / phiG r) := by
  let R := B ^ 100
  let y := B ^ 180
  let logR := Real.log (R : ℝ)
  let logy := Real.log (y : ℝ)
  let logB := Real.log (B : ℝ)
  let Isf := ∑ r ∈ sfLE R, (zW R r) ^ 2 / phiG r
  have hB2 : 2 ≤ B := by omega
  have hR2 : 2 ≤ R := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hRy : R ≤ y := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hlogB_pos : 0 < logB := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogR_eq : logR = 100 * logB := by dsimp only [logR, R, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogy_eq : logy = 180 * logB := by dsimp only [logy, y, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogR_pos : 0 < logR := by rw [hlogR_eq]; positivity
  have hlogy_pos : 0 < logy := by rw [hlogy_eq]; positivity
  have hIsf_nn : 0 ≤ Isf := Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (phiG_pos r).le
  have hstep1 : ∑ p ∈ Nat.primesLE y \ Nat.primesLE R,
      (1 - Real.log (p : ℝ) / logy) * (gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) ≤
      (∑ p ∈ Nat.primesLE y \ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * (8 / (p : ℝ))) * Isf := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum; intro p hp
    obtain ⟨hpy, hnotR⟩ := Finset.mem_sdiff.mp hp
    have hprime := (Nat.mem_primesLE.mp hpy).2
    have hp_le_y := (Nat.mem_primesLE.mp hpy).1
    have hp_gt_R : R < p := by by_contra! hle; exact hnotR (Nat.mem_primesLE.mpr ⟨hle, hprime⟩)
    have hp59 : 59 < p := by
      have hR59 : 59 < R := lt_of_lt_of_le (by omega : 59 < B) (Nat.le_self_pow (by norm_num) B)
      omega
    have hgp : gF p = 8 / (p : ℝ) := by rw [gF_prime hprime, omegaP_eq_eight hprime hp59]; norm_num
    have hwt_nn : 0 ≤ 1 - Real.log (p : ℝ) / logy := by
      have : Real.log (p : ℝ) / logy ≤ 1 := (div_le_one hlogy_pos).mpr
        (Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hp_le_y))
      linarith
    have hinner_le : ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r),
        (zW R r + zW R (p * r)) ^ 2 / phiG r ≤ Isf := by
      dsimp only [Isf]
      calc ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r
          = ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r) ^ 2 / phiG r := by
            refine Finset.sum_congr rfl fun r hr => ?_
            have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
            have hgt : ¬ p * r ≤ R := by nlinarith
            simp [zW, hgt]
        _ ≤ ∑ r ∈ sfLE R, (zW R r) ^ 2 / phiG r :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun r _ _ => div_nonneg (sq_nonneg _) (phiG_pos r).le
    rw [hgp, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner_le (by positivity)) hwt_nn
  have hsum_coeff : ∑ p ∈ Nat.primesLE y \ Nat.primesLE R,
      (1 - Real.log (p : ℝ) / logy) * (8 / (p : ℝ)) ≤ J2UbR + (8 * C4 + 8 * C5) / logR := by
    have hrew : ∑ p ∈ Nat.primesLE y \ Nat.primesLE R,
        (1 - Real.log (p : ℝ) / logy) * (8 / (p : ℝ)) =
        8 * (∑ p ∈ Nat.primesLE y \ Nat.primesLE R, (1 : ℝ) / (p : ℝ)) -
        (8 / logy) * (∑ p ∈ Nat.primesLE y \ Nat.primesLE R, Real.log (p : ℝ) / (p : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hrew]
    have hinv := hC4 R y hR2 hRy
    have hlogp := hC5 R y hR2 hRy
    have hrat : logy / logR = (9 : ℝ) / (5 : ℝ) := by
      rw [hlogy_eq, hlogR_eq]; field_simp [hlogB_pos.ne']; ring
    have hlog95 : Real.log (logy / logR) ≤ (logUbInt 9 5 : ℝ) / (Dscale : ℝ) := by
      rw [hrat]; exact real_log_div_le_logUbInt (by norm_num) (by norm_num)
    have hratio2 : (logy - logR) / logy = 4 / 9 := by
      rw [hlogy_eq, hlogR_eq]; field_simp [hlogB_pos.ne']; ring
    have hC5_le : 8 * C5 / logy ≤ 8 * C5 / logR :=
      div_le_div_of_nonneg_left (by positivity) hlogR_pos (by linarith only [hlogy_eq, hlogR_eq, hlogB_pos])
    have h2 : (8 / logy) * (logy - logR - C5) ≤
        (8 / logy) * ∑ p ∈ Nat.primesLE y \ Nat.primesLE R, Real.log (p : ℝ) / (p : ℝ) :=
      mul_le_mul_of_nonneg_left hlogp (by positivity)
    have h2rew : (8 / logy) * (logy - logR - C5) = 8 * (4 / 9) - 8 * C5 / logy := by
      calc (8 / logy) * (logy - logR - C5) = 8 * ((logy - logR) / logy) - 8 * C5 / logy := by ring
        _ = 8 * (4 / 9) - 8 * C5 / logy := by rw [hratio2]
    unfold J2UbR
    have hsplit_err : (8 * C4 + 8 * C5) / logR = 8 * (C4 / logR) + 8 * C5 / logR := by ring
    linarith only [hinv, hlog95, hC5_le, h2, h2rew, hsplit_err]
  exact hstep1.trans (mul_le_mul_of_nonneg_right hsum_coeff hIsf_nn)

private lemma lower_primes_bin_p_bound {C2 C3 C4 C5 : ℝ}
    (hC2_pos : 0 < C2) (hC3_pos : 0 < C3) (hC4_pos : 0 < C4) (hC5_pos : 0 < C5)
    (hC2 : ∀ n : ℕ, 2 ≤ n → ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 2 / (p : ℝ) ≤
      (1 / 2) * (Real.log n) ^ 2 + C2 * (Real.log n + 1))
    (hC3 : ∀ n : ℕ, 2 ≤ n → (1 / 3) * (Real.log n) ^ 3 - C3 * (Real.log n + 1) ^ 2 ≤
      ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 3 / (p : ℝ))
    (hC4 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log b / Real.log a) + C4 / Real.log a)
    (hC5 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      Real.log b - Real.log a - C5 ≤
        ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ))
    {B j : ℕ} (hB : 6000 ≤ B) (hj50 : j < 50) :
    let R := B ^ 100
    let y := B ^ 180
    let s : ℝ := (50 - (j : ℝ)) / 50
    ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * gF p *
      (min (Real.log (p : ℝ) / Real.log (R : ℝ)) s) ^ 2 ≤
    (valInt j : ℝ) / (27 * (50 : ℝ) ^ 3 * (Dscale : ℝ)) +
    (16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16) / Real.log (R : ℝ) := by
  dsimp only
  let R := B ^ 100
  let y := B ^ 180
  let logR := Real.log (R : ℝ)
  let logy := Real.log (y : ℝ)
  let logB := Real.log (B : ℝ)
  let s : ℝ := (50 - (j : ℝ)) / 50
  let Q := B ^ (100 - 2 * j)
  have hB2 : 2 ≤ B := by omega
  have hQ2 : 2 ≤ Q := le_trans hB2 (Nat.le_self_pow (by omega) B)
  have hQR : Q ≤ R := Nat.pow_le_pow_right (by omega) (by omega)
  have hD_pos : (0 : ℝ) < (Dscale : ℝ) := by norm_num [Dscale]
  have hlogB_pos : 0 < logB := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogB_ge1 : 1 ≤ logB := by
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hB3 : (3 : ℝ) ≤ B := by exact_mod_cast (show 3 ≤ B by omega)
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hlogR_eq : logR = 100 * logB := by dsimp only [logR, R, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogy_eq : logy = 180 * logB := by dsimp only [logy, y, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogR_ge1 : 1 ≤ logR := by linarith only [hlogR_eq, hlogB_ge1]
  have hlogR_pos : 0 < logR := by linarith only [hlogR_ge1]
  have hlogy_pos : 0 < logy := by rw [hlogy_eq]; positivity
  have hs_pos : 0 < s := by dsimp only [s]; have : (j : ℝ) < 50 := Nat.cast_lt.mpr hj50; linarith
  have hs_le1 : s ≤ 1 := by dsimp only [s]; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have hlogQ_eq : Real.log (Q : ℝ) = s * logR := by
    dsimp only [Q, s]; rw [Nat.cast_pow, Real.log_pow, hlogR_eq]
    rw [Nat.cast_sub (by omega : 2 * j ≤ 100)]; push_cast; ring
  have hsubQ : Nat.primesLE Q ⊆ Nat.primesLE R := fun p hp => by
    rw [Nat.mem_primesLE] at hp ⊢; exact ⟨hp.1.trans hQR, hp.2⟩
  rw [← Finset.sum_sdiff hsubQ]
  -- Part 1: p ≤ Q
  have hpart1 : ∑ p ∈ Nat.primesLE Q, (1 - Real.log (p : ℝ) / logy) * gF p *
      (min (Real.log (p : ℝ) / logR) s) ^ 2 ≤
      8 * (s ^ 2 / 2 - (5 / 9 : ℝ) * s ^ 3 / 3) +
      (16 * C2 + 32 * C3 + K59const + 16) / logR := by
    have h1 : ∑ p ∈ Nat.primesLE Q, (1 - Real.log (p : ℝ) / logy) * gF p *
        (min (Real.log (p : ℝ) / logR) s) ^ 2 ≤
        ∑ p ∈ Nat.primesLE Q, (1 - Real.log (p : ℝ) / logy) * gF p *
          (Real.log (p : ℝ) / logR) ^ 2 := by
      apply Finset.sum_le_sum; intro p hp
      have hprime := (Nat.mem_primesLE.mp hp).2
      have hple := (Nat.mem_primesLE.mp hp).1
      have hwt_nn : 0 ≤ 1 - Real.log (p : ℝ) / logy := by
        have : Real.log (p : ℝ) / logy ≤ 1 := (div_le_one hlogy_pos).mpr
          (Real.log_le_log (by exact_mod_cast hprime.pos)
            (by exact_mod_cast hple.trans (hQR.trans (Nat.pow_le_pow_right (by omega) (by norm_num)))))
        linarith
      have hmin_nn : 0 ≤ min (Real.log (p : ℝ) / logR) s :=
        le_min (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) hlogR_pos.le) hs_pos.le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmin_nn (min_le_left _ _) 2)
        (mul_nonneg hwt_nn (gF_pos hprime.pos).le)
    have h2 : ∑ p ∈ Nat.primesLE Q, (1 - Real.log (p : ℝ) / logy) * gF p *
        (Real.log (p : ℝ) / logR) ^ 2 ≤
        (8 / logR ^ 2) * (∑ p ∈ Nat.primesLE Q, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) -
        (8 / (logy * logR ^ 2)) * (∑ p ∈ Nat.primesLE Q, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) +
        K59const / logR := by
      have hrew : (8 / logR ^ 2) * (∑ p ∈ Nat.primesLE Q, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) -
          (8 / (logy * logR ^ 2)) * (∑ p ∈ Nat.primesLE Q, (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) =
          ∑ p ∈ Nat.primesLE Q, (1 - Real.log (p : ℝ) / logy) * (8 / (p : ℝ)) *
            (Real.log (p : ℝ) / logR) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun p _ => by ring
      rw [hrew]
      have hdiff : ∑ p ∈ Nat.primesLE Q,
          ((1 - Real.log (p : ℝ) / logy) * gF p * (Real.log (p : ℝ) / logR) ^ 2 -
           (1 - Real.log (p : ℝ) / logy) * (8 / (p : ℝ)) * (Real.log (p : ℝ) / logR) ^ 2) ≤
          K59const / logR := by
        calc ∑ p ∈ Nat.primesLE Q,
              ((1 - Real.log (p : ℝ) / logy) * gF p * (Real.log (p : ℝ) / logR) ^ 2 -
               (1 - Real.log (p : ℝ) / logy) * (8 / (p : ℝ)) * (Real.log (p : ℝ) / logR) ^ 2)
            ≤ ∑ p ∈ Nat.primesLE Q,
                if p ≤ 59 then (8 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) / logR else 0 := by
              apply Finset.sum_le_sum; intro p hp
              have hprime := (Nat.mem_primesLE.mp hp).2
              by_cases hp59 : p ≤ 59
              · rw [if_pos hp59]
                have hgp_nn : 0 ≤ gF p := (gF_pos hprime.pos).le
                have hgp_le : gF p ≤ 8 / (p : ℝ) := by
                  rw [gF_prime hprime]
                  exact div_le_div_of_nonneg_right (by exact_mod_cast omegaP_le_eight hprime) (Nat.cast_nonneg p)
                have h1_le : gF p * (Real.log (p : ℝ) / logR) ^ 2 ≤
                    (8 / (p : ℝ)) * (Real.log (p : ℝ) / logR) ^ 2 :=
                  mul_le_mul_of_nonneg_right hgp_le (sq_nonneg _)
                have hneg_le : (Real.log (p : ℝ) / logy) * (8 / (p : ℝ) - gF p) *
                    (Real.log (p : ℝ) / logR) ^ 2 ≤
                    (8 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) / logR := by
                  have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
                  have h1_ge : 1 ≤ logR ^ 2 := one_le_pow₀ hlogR_ge1
                  have hlogy_ge : logR ≤ logy := by linarith only [hlogy_eq, hlogR_eq, hlogB_pos]
                  have ha : Real.log (p : ℝ) / logy ≤ Real.log (p : ℝ) / logR :=
                    div_le_div_of_nonneg_left hlogp_nn hlogR_pos hlogy_ge
                  have hb : 8 / (p : ℝ) - gF p ≤ 8 / (p : ℝ) := by linarith only [hgp_nn]
                  have hc : (Real.log (p : ℝ) / logR) ^ 2 ≤ (Real.log (p : ℝ)) ^ 2 := by
                    rw [div_pow]; exact div_le_self (sq_nonneg _) h1_ge
                  have h3 := mul_le_mul (mul_le_mul ha hb (by linarith only [hgp_le]) (by positivity))
                    hc (sq_nonneg _) (by positivity)
                  have heq : (Real.log (p : ℝ) / logR) * (8 / (p : ℝ)) * (Real.log (p : ℝ)) ^ 2 =
                      (8 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) / logR := by ring
                  linarith only [h3, heq]
                have hrew2 : (1 - Real.log (p : ℝ) / logy) * gF p * (Real.log (p : ℝ) / logR) ^ 2 -
                    (1 - Real.log (p : ℝ) / logy) * (8 / (p : ℝ)) * (Real.log (p : ℝ) / logR) ^ 2 =
                    (gF p - 8 / (p : ℝ)) * (Real.log (p : ℝ) / logR) ^ 2 +
                    (Real.log (p : ℝ) / logy) * (8 / (p : ℝ) - gF p) * (Real.log (p : ℝ) / logR) ^ 2 := by ring
                linarith only [h1_le, hneg_le, hrew2]
              · rw [if_neg hp59]
                have hgp : gF p = 8 / (p : ℝ) := by
                  rw [gF_prime hprime, omegaP_eq_eight hprime (by omega)]; norm_num
                rw [hgp, sub_self]
          _ = (∑ p ∈ (Nat.primesLE Q).filter (· ≤ 59), (8 * (Real.log (p : ℝ)) ^ 3 / (p : ℝ))) / logR := by
              rw [← Finset.sum_filter, Finset.sum_div]
          _ ≤ K59const / logR := by
              apply div_le_div_of_nonneg_right _ hlogR_pos.le
              unfold K59const
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro p hp; rw [Finset.mem_filter, Nat.mem_primesLE] at hp
                exact Nat.mem_primesLE.mpr ⟨hp.2, hp.1.2⟩
              · intro p hp _
                have hpp := (Nat.mem_primesLE.mp hp).2
                have := Real.log_nonneg (by exact_mod_cast hpp.one_le : (1 : ℝ) ≤ (p : ℝ))
                positivity
      rw [Finset.sum_sub_distrib] at hdiff
      linarith only [hdiff]
    have hsqQ := hC2 Q hQ2
    have hcubQ := hC3 Q hQ2
    have hlogQ_le_R : Real.log (Q : ℝ) ≤ logR := by nlinarith only [hlogQ_eq, hs_le1, hlogR_pos]
    have hlogQ1 : Real.log (Q : ℝ) + 1 ≤ 2 * logR := by linarith only [hlogQ_le_R, hlogR_ge1]
    have hA : (8 / logR ^ 2) * ∑ p ∈ Nat.primesLE Q, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) ≤
        8 * (s ^ 2 / 2) + 16 * C2 / logR := by
      have hmul := mul_le_mul_of_nonneg_left hsqQ (by positivity : (0 : ℝ) ≤ 8 / logR ^ 2)
      have hrew : (8 / logR ^ 2) * ((1 / 2) * (Real.log (Q : ℝ)) ^ 2 + C2 * (Real.log (Q : ℝ) + 1)) =
          8 * (s ^ 2 / 2) + 8 * C2 * (Real.log (Q : ℝ) + 1) / logR ^ 2 := by
        rw [hlogQ_eq]; field_simp [hlogR_pos.ne']
      have herr : 8 * C2 * (Real.log (Q : ℝ) + 1) / logR ^ 2 ≤ 16 * C2 / logR := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hlogR_pos) hlogR_pos]
        have hq1' : (Real.log (Q : ℝ) + 1) * logR ≤ 2 * logR ^ 2 := by nlinarith only [hlogQ1, hlogR_pos]
        nlinarith only [hC2_pos, hq1']
      linarith only [hmul, hrew, herr]
    have hB_cub : 8 * ((5 / 9 : ℝ) * s ^ 3 / 3) - 32 * C3 / logR ≤
        (8 / (logy * logR ^ 2)) * ∑ p ∈ Nat.primesLE Q, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hcubQ (by positivity : (0 : ℝ) ≤ 8 / (logy * logR ^ 2))
      have hrew : (8 / (logy * logR ^ 2)) * ((1 / 3) * (Real.log (Q : ℝ)) ^ 3 - C3 * (Real.log (Q : ℝ) + 1) ^ 2) =
          8 * ((5 / 9 : ℝ) * s ^ 3 / 3) - 8 * C3 * (Real.log (Q : ℝ) + 1) ^ 2 / (logy * logR ^ 2) := by
        rw [hlogQ_eq, hlogy_eq, hlogR_eq]; field_simp [hlogB_pos.ne']; ring
      have herr : 8 * C3 * (Real.log (Q : ℝ) + 1) ^ 2 / (logy * logR ^ 2) ≤ 32 * C3 / logR := by
        have hlogQ_nn : 0 ≤ Real.log (Q : ℝ) := by rw [hlogQ_eq]; positivity
        have hsq2 : (Real.log (Q : ℝ) + 1) ^ 2 ≤ 4 * logR ^ 2 := by nlinarith only [hlogQ1, hlogQ_nn]
        have hlogy_ge : logR ≤ logy := by linarith only [hlogy_eq, hlogR_eq, hlogB_pos]
        calc 8 * C3 * (Real.log (Q : ℝ) + 1) ^ 2 / (logy * logR ^ 2)
            ≤ 8 * C3 * (4 * logR ^ 2) / (logR * logR ^ 2) := by
              apply div_le_div₀ (by positivity) (by nlinarith only [hC3_pos, hsq2]) (by positivity)
              exact mul_le_mul_of_nonneg_right hlogy_ge (sq_nonneg logR)
          _ = 32 * C3 / logR := by field_simp [hlogR_pos.ne']; ring
      linarith only [hmul, hrew, herr]
    have hcomb_err : 16 * C2 / logR + 32 * C3 / logR + K59const / logR ≤
        (16 * C2 + 32 * C3 + K59const + 16) / logR := by
      have h16 : 0 ≤ 16 / logR := by positivity
      have heq : (16 * C2 + 32 * C3 + K59const + 16) / logR =
          16 * C2 / logR + 32 * C3 / logR + K59const / logR + 16 / logR := by ring
      linarith only [h16, heq]
    linarith only [h1, h2, hA, hB_cub, hcomb_err]
  -- Part 2: Q < p ≤ R
  have hpart2 : ∑ p ∈ Nat.primesLE R \ Nat.primesLE Q,
      (1 - Real.log (p : ℝ) / logy) * gF p *
      (min (Real.log (p : ℝ) / logR) s) ^ 2 ≤
      8 * s ^ 2 * ((logUbInt 50 (50 - j) : ℝ) / (Dscale : ℝ) - (5 / 9 : ℝ) * (1 - s)) +
      (8 * C4 + 8 * C5) / logR := by
    have h1 : ∑ p ∈ Nat.primesLE R \ Nat.primesLE Q,
        (1 - Real.log (p : ℝ) / logy) * gF p *
        (min (Real.log (p : ℝ) / logR) s) ^ 2 ≤
        s ^ 2 * ∑ p ∈ Nat.primesLE R \ Nat.primesLE Q,
          (1 - Real.log (p : ℝ) / logy) * (8 / (p : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro p hp
      obtain ⟨hpR, hnotQ⟩ := Finset.mem_sdiff.mp hp
      have hprime := (Nat.mem_primesLE.mp hpR).2
      have hp_le_R := (Nat.mem_primesLE.mp hpR).1
      have hp_gt_Q : Q < p := by by_contra! hle; exact hnotQ (Nat.mem_primesLE.mpr ⟨hle, hprime⟩)
      have hp59 : 59 < p := by
        have hQ59 : 59 < Q := lt_of_lt_of_le (by omega : 59 < B) (Nat.le_self_pow (by omega) B)
        omega
      have hgp : gF p = 8 / (p : ℝ) := by rw [gF_prime hprime, omegaP_eq_eight hprime hp59]; norm_num
      have hwt_nn : 0 ≤ 1 - Real.log (p : ℝ) / logy := by
        have : Real.log (p : ℝ) / logy ≤ 1 := (div_le_one hlogy_pos).mpr
          (Real.log_le_log (by exact_mod_cast hprime.pos)
            (by exact_mod_cast hp_le_R.trans (Nat.pow_le_pow_right (by omega) (by norm_num))))
        linarith
      have hmin_nn : 0 ≤ min (Real.log (p : ℝ) / logR) s :=
        le_min (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) hlogR_pos.le) hs_pos.le
      have hsq := pow_le_pow_left₀ hmin_nn (min_le_right _ _) 2
      rw [hgp]
      calc (1 - Real.log (p : ℝ) / logy) * (8 / (p : ℝ)) * (min (Real.log (p : ℝ) / logR) s) ^ 2
          ≤ (1 - Real.log (p : ℝ) / logy) * (8 / (p : ℝ)) * s ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = s ^ 2 * ((1 - Real.log (p : ℝ) / logy) * (8 / (p : ℝ))) := by ring
    have hrew : ∑ p ∈ Nat.primesLE R \ Nat.primesLE Q,
        (1 - Real.log (p : ℝ) / logy) * (8 / (p : ℝ)) =
        8 * (∑ p ∈ Nat.primesLE R \ Nat.primesLE Q, (1 : ℝ) / (p : ℝ)) -
        (8 / logy) * (∑ p ∈ Nat.primesLE R \ Nat.primesLE Q, Real.log (p : ℝ) / (p : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    have hinv := hC4 Q R hQ2 hQR
    have hlogp := hC5 Q R hQ2 hQR
    have hrat : logR / Real.log (Q : ℝ) = ((50 : ℕ) : ℝ) / ((50 - j : ℕ) : ℝ) := by
      rw [hlogQ_eq]; dsimp only [s]; rw [Nat.cast_sub (by omega : j ≤ 50)]
      push_cast; field_simp [hlogR_pos.ne']
    have hlog_ub : Real.log (logR / Real.log (Q : ℝ)) ≤ (logUbInt 50 (50 - j) : ℝ) / (Dscale : ℝ) := by
      rw [hrat]; exact real_log_div_le_logUbInt (by omega) (by omega)
    have hsub_rat : (logR - Real.log (Q : ℝ)) / logy = (5 / 9 : ℝ) * (1 - s) := by
      rw [hlogQ_eq, hlogy_eq, hlogR_eq]; field_simp [hlogB_pos.ne']; ring
    have h2 : (8 / logy) * (logR - Real.log (Q : ℝ) - C5) ≤
        (8 / logy) * ∑ p ∈ Nat.primesLE R \ Nat.primesLE Q, Real.log (p : ℝ) / (p : ℝ) :=
      mul_le_mul_of_nonneg_left hlogp (by positivity)
    have h2rew : (8 / logy) * (logR - Real.log (Q : ℝ) - C5) =
        8 * ((5 / 9 : ℝ) * (1 - s)) - 8 * C5 / logy := by
      calc (8 / logy) * (logR - Real.log (Q : ℝ) - C5)
          = 8 * ((logR - Real.log (Q : ℝ)) / logy) - 8 * C5 / logy := by ring
        _ = 8 * ((5 / 9 : ℝ) * (1 - s)) - 8 * C5 / logy := by rw [hsub_rat]
    have hC4_s : s ^ 2 * (8 * (C4 / Real.log (Q : ℝ))) ≤ 8 * C4 / logR := by
      rw [hlogQ_eq]
      have heq : s ^ 2 * (8 * (C4 / (s * logR))) = s * (8 * C4 / logR) := by
        field_simp [hs_pos.ne', hlogR_pos.ne']
      rw [heq]; nlinarith only [hs_le1, show (0 : ℝ) ≤ 8 * C4 / logR by positivity]
    have hC5_s : s ^ 2 * (8 * C5 / logy) ≤ 8 * C5 / logR := by
      have hs2 : s ^ 2 ≤ 1 := by nlinarith only [hs_pos, hs_le1]
      have hlogy_ge : logR ≤ logy := by linarith only [hlogy_eq, hlogR_eq, hlogB_pos]
      have h1' : 8 * C5 / logy ≤ 8 * C5 / logR := div_le_div_of_nonneg_left (by positivity) hlogR_pos hlogy_ge
      nlinarith only [hs2, h1', show (0 : ℝ) ≤ 8 * C5 / logR by positivity, show (0 : ℝ) ≤ s ^ 2 by positivity]
    have hinner2 : ∑ p ∈ Nat.primesLE R \ Nat.primesLE Q,
        (1 - Real.log (p : ℝ) / logy) * (8 / (p : ℝ)) ≤
        8 * ((logUbInt 50 (50 - j) : ℝ) / (Dscale : ℝ) - (5 / 9 : ℝ) * (1 - s)) +
        8 * (C4 / Real.log (Q : ℝ)) + 8 * C5 / logy := by
      rw [hrew]; linarith only [hinv, hlog_ub, h2, h2rew]
    have hmul2 := mul_le_mul_of_nonneg_left hinner2 (sq_nonneg s)
    have hsplit8 : (8 * C4 + 8 * C5) / logR = 8 * C4 / logR + 8 * C5 / logR := by ring
    linarith only [h1, hmul2, hC4_s, hC5_s, hsplit8]
  have hval_eq : 8 * (s ^ 2 / 2 - (5 / 9 : ℝ) * s ^ 3 / 3) +
      8 * s ^ 2 * ((logUbInt 50 (50 - j) : ℝ) / (Dscale : ℝ) - (5 / 9 : ℝ) * (1 - s)) =
      (valInt j : ℝ) / (27 * (50 : ℝ) ^ 3 * (Dscale : ℝ)) := by
    unfold valInt; dsimp only [s]; push_cast; field_simp [hD_pos.ne']; ring
  have herr_split : (16 * C2 + 32 * C3 + K59const + 16) / logR + (8 * C4 + 8 * C5) / logR =
      (16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16) / logR := by ring
  linarith only [hpart1, hpart2, hval_eq, herr_split]

private lemma lower_primes_upper_bound {C_P M0 C2 C3 C4 C5 : ℝ}
    (hCP_pos : 0 < C_P) (hM0_pos : 0 < M0) (hC2_pos : 0 < C2) (hC3_pos : 0 < C3)
    (hC4_pos : 0 < C4) (hC5_pos : 0 < C5)
    (hH : ∀ u : ℕ, 2 ≤ u → |Hsum u - C_P * (Real.log u) ^ 8| ≤ M0 * (Real.log u + 1) ^ 7)
    (hC2 : ∀ n : ℕ, 2 ≤ n → ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 2 / (p : ℝ) ≤
      (1 / 2) * (Real.log n) ^ 2 + C2 * (Real.log n + 1))
    (hC3 : ∀ n : ℕ, 2 ≤ n → (1 / 3) * (Real.log n) ^ 3 - C3 * (Real.log n + 1) ^ 2 ≤
      ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 3 / (p : ℝ))
    (hC4 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log b / Real.log a) + C4 / Real.log a)
    (hC5 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      Real.log b - Real.log a - C5 ≤
        ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ))
    {B : ℕ} (hB : 6000 ≤ B)
    (hH_R_le : Hsum (B ^ 100) ≤ (C_P + 2 * M0) * (Real.log ((B ^ 100 : ℕ) : ℝ)) ^ 8) :
    let R := B ^ 100
    let y := B ^ 180
    let logR := Real.log (R : ℝ)
    ∑ p ∈ Nat.primesLE R,
      (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * (gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) ≤
    C_P * numHiR * logR ^ 8 +
    (50 * (2 * M0) * (8 * (1 + (logUbInt 50 1 : ℝ) / (Dscale : ℝ))) +
      50 * (C_P + 2 * M0) * (16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16)) * (logR + 1) ^ 7 := by
  dsimp only
  let R := B ^ 100
  let y := B ^ 180
  let logR := Real.log (R : ℝ)
  let logy := Real.log (y : ℝ)
  let C_Hsum := C_P + 2 * M0
  have hB2 : 2 ≤ B := by omega
  have hR2 : 2 ≤ R := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hD_pos : (0 : ℝ) < (Dscale : ℝ) := by norm_num [Dscale]
  have hlogR_pos : 0 < logR := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hlogy_pos : 0 < logy := Real.log_pos (by exact_mod_cast (show 1 < y by
    have := le_trans hB2 (Nat.le_self_pow (by norm_num) B : B ≤ y); omega))
  -- Swap p and r
  have hswap_pr : ∑ p ∈ Nat.primesLE R,
      (1 - Real.log (p : ℝ) / logy) * (gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) ≤
      ∑ r ∈ sfLE R, (1 / phiG r) *
        ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * gF p *
          (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2 := by
    have hlhs_eq : ∑ p ∈ Nat.primesLE R,
        (1 - Real.log (p : ℝ) / logy) * (gF p *
          ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) =
        ∑ p ∈ Nat.primesLE R, ∑ r ∈ sfLE R,
          if ¬ p ∣ r then (1 / phiG r) * ((1 - Real.log (p : ℝ) / logy) * gF p *
            (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2) else 0 := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hprime := (Nat.mem_primesLE.mp hp).2
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun r hr => ?_
      by_cases hnd : ¬ p ∣ r
      · rw [if_pos hnd, if_pos hnd, zW_add_sq_eq hR2 hprime hr hnd]; ring
      · simp [hnd]
    rw [hlhs_eq, Finset.sum_comm]
    apply Finset.sum_le_sum; intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro p hp
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hple := (Nat.mem_primesLE.mp hp).1
    have hwt_nn : 0 ≤ 1 - Real.log (p : ℝ) / logy := by
      have : Real.log (p : ℝ) / logy ≤ 1 := (div_le_one hlogy_pos).mpr
        (Real.log_le_log (by exact_mod_cast hprime.pos)
          (by exact_mod_cast hple.trans (Nat.pow_le_pow_right (by omega) (by norm_num))))
      linarith
    split_ifs
    · exact mul_nonneg (div_nonneg zero_le_one (phiG_pos r).le)
        (mul_nonneg (mul_nonneg hwt_nn (gF_pos hprime.pos).le) (sq_nonneg _))
    · exact le_rfl
  refine hswap_pr.trans ?_
  rw [sum_sfLE_eq_sum_sfBin hB2]
  have hterm_ub : ∀ j ∈ Finset.range 50,
      ∑ r ∈ sfBin B j, (1 / phiG r) *
        ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * gF p *
          (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2 ≤
      C_P * (((wInt j : ℝ) * (valInt j : ℝ)) / (27 * (50 : ℝ) ^ 11 * (Dscale : ℝ))) * logR ^ 8 +
      (2 * M0 * (8 * (1 + (logUbInt 50 1 : ℝ) / (Dscale : ℝ))) +
        C_Hsum * (16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16)) * (logR + 1) ^ 7 := by
    intro j hj
    have hj50 : j < 50 := Finset.mem_range.mp hj
    have hp_bound := lower_primes_bin_p_bound hC2_pos hC3_pos hC4_pos hC5_pos hC2 hC3 hC4 hC5 hB hj50
    have hbin1 : ∑ r ∈ sfBin B j, (1 / phiG r) *
        ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * gF p *
          (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2 ≤
        ((valInt j : ℝ) / (27 * (50 : ℝ) ^ 3 * (Dscale : ℝ)) +
          (16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16) / logR) *
        (∑ r ∈ sfBin B j, (1 : ℝ) / phiG r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro r hr
      have hsr := (sfBin_log_bounds hB2 hj50 hr).2
      have hr_sfLE := sfBin_subset_sfLE hB2 hj50 hr
      have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr_sfLE).1
      have hr_nn : 0 ≤ 1 - Real.log (r : ℝ) / logR := by
        have : Real.log (r : ℝ) / logR ≤ 1 := (div_le_one hlogR_pos).mpr
          (Real.log_le_log (by exact_mod_cast hr_Icc.1) (by exact_mod_cast hr_Icc.2))
        linarith
      have hr_sum_le : ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * gF p *
          (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2 ≤
          ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * gF p *
            (min (Real.log (p : ℝ) / logR) ((50 - (j : ℝ)) / 50)) ^ 2 := by
        apply Finset.sum_le_sum; intro p hp
        have hprime := (Nat.mem_primesLE.mp hp).2
        have hple := (Nat.mem_primesLE.mp hp).1
        have hwt_nn : 0 ≤ 1 - Real.log (p : ℝ) / logy := by
          have : Real.log (p : ℝ) / logy ≤ 1 := (div_le_one hlogy_pos).mpr
            (Real.log_le_log (by exact_mod_cast hprime.pos)
              (by exact_mod_cast hple.trans (Nat.pow_le_pow_right (by omega) (by norm_num))))
          linarith
        have hmin_nn : 0 ≤ min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR) :=
          le_min (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) hlogR_pos.le) hr_nn
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmin_nn (min_le_min_left _ hsr) 2)
          (mul_nonneg hwt_nn (gF_pos hprime.pos).le)
      calc (1 / phiG r) * ∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * gF p *
            (min (Real.log (p : ℝ) / logR) (1 - Real.log (r : ℝ) / logR)) ^ 2
          ≤ (1 / phiG r) * ((valInt j : ℝ) / (27 * (50 : ℝ) ^ 3 * (Dscale : ℝ)) +
            (16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16) / logR) :=
            mul_le_mul_of_nonneg_left (hr_sum_le.trans hp_bound) (div_nonneg zero_le_one (phiG_pos r).le)
        _ = _ := by ring
    refine hbin1.trans ?_
    have hHbin := (abs_le.mp (Hsum_sfBin_bound hCP_pos hM0_pos hH hB2 hj50)).2
    have hbin_le_H : ∑ r ∈ sfBin B j, (1 : ℝ) / phiG r ≤ C_Hsum * logR ^ 8 :=
      (Finset.sum_le_sum_of_subset_of_nonneg (sfBin_subset_sfLE hB2 hj50)
        fun r _ _ => div_nonneg zero_le_one (phiG_pos r).le).trans hH_R_le
    have hval_le : (valInt j : ℝ) / (27 * (50 : ℝ) ^ 3 * (Dscale : ℝ)) ≤
        8 * (1 + (logUbInt 50 1 : ℝ) / (Dscale : ℝ)) := by
      have hlog_mono : (logUbInt 50 (50 - j) : ℝ) ≤ (logUbInt 50 1 : ℝ) := by
        exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg
          (fun k hk => by rw [Finset.mem_Ico] at hk ⊢; omega) (fun _ _ _ => Nat.zero_le _)
      have hs_nn : (0 : ℝ) ≤ (50 - (j : ℝ)) / 50 := by
        have : (j : ℝ) ≤ 50 := Nat.cast_le.mpr hj50.le; linarith
      have hs_le1 : (50 - (j : ℝ)) / 50 ≤ 1 := by
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
      have heq : (valInt j : ℝ) / (27 * (50 : ℝ) ^ 3 * (Dscale : ℝ)) =
          8 * (((50 - (j : ℝ)) / 50) ^ 2 / 2 - (5 / 9 : ℝ) * ((50 - (j : ℝ)) / 50) ^ 3 / 3) +
          8 * ((50 - (j : ℝ)) / 50) ^ 2 *
            ((logUbInt 50 (50 - j) : ℝ) / (Dscale : ℝ) - (5 / 9 : ℝ) * (1 - (50 - (j : ℝ)) / 50)) := by
        unfold valInt; push_cast; field_simp [hD_pos.ne']; ring
      rw [heq]
      have hs2_le1 : ((50 - (j : ℝ)) / 50) ^ 2 ≤ 1 := by nlinarith only [hs_nn, hs_le1]
      have hs3_nn : 0 ≤ ((50 - (j : ℝ)) / 50) ^ 3 := pow_nonneg hs_nn 3
      have h1s_nn : 0 ≤ 1 - (50 - (j : ℝ)) / 50 := by linarith only [hs_le1]
      have hlog_div : (logUbInt 50 (50 - j) : ℝ) / (Dscale : ℝ) ≤ (logUbInt 50 1 : ℝ) / (Dscale : ℝ) :=
        div_le_div_of_nonneg_right hlog_mono hD_pos.le
      have hlog_nn : 0 ≤ (logUbInt 50 1 : ℝ) / (Dscale : ℝ) := by positivity
      have hs2_nn : 0 ≤ ((50 - (j : ℝ)) / 50) ^ 2 := sq_nonneg _
      nlinarith only [hs2_le1, hs2_nn, hs3_nn, h1s_nn, hlog_div, hlog_nn]
    have hval_nn : 0 ≤ (valInt j : ℝ) / (27 * (50 : ℝ) ^ 3 * (Dscale : ℝ)) :=
      div_nonneg (by exact_mod_cast valInt_nonneg j hj50) (by positivity)
    have h1 : (valInt j : ℝ) / (27 * (50 : ℝ) ^ 3 * (Dscale : ℝ)) *
        (∑ r ∈ sfBin B j, (1 : ℝ) / phiG r) ≤
        C_P * (((wInt j : ℝ) * (valInt j : ℝ)) / (27 * (50 : ℝ) ^ 11 * (Dscale : ℝ))) * logR ^ 8 +
        2 * M0 * (8 * (1 + (logUbInt 50 1 : ℝ) / (Dscale : ℝ))) * (logR + 1) ^ 7 := by
      have ha := mul_le_mul_of_nonneg_left
        (by linarith only [hHbin] : ∑ r ∈ sfBin B j, (1 : ℝ) / phiG r ≤
          C_P * ((wInt j : ℝ) / (50 : ℝ) ^ 8) * logR ^ 8 + 2 * M0 * (logR + 1) ^ 7) hval_nn
      have hnn : 0 ≤ 2 * M0 * (logR + 1) ^ 7 := by positivity
      have hb : (valInt j : ℝ) / (27 * (50 : ℝ) ^ 3 * (Dscale : ℝ)) * (2 * M0 * (logR + 1) ^ 7) ≤
          2 * M0 * (8 * (1 + (logUbInt 50 1 : ℝ) / (Dscale : ℝ))) * (logR + 1) ^ 7 := by
        nlinarith only [hval_le, hnn]
      have hrew : (valInt j : ℝ) / (27 * (50 : ℝ) ^ 3 * (Dscale : ℝ)) *
          (C_P * ((wInt j : ℝ) / (50 : ℝ) ^ 8) * logR ^ 8) =
          C_P * (((wInt j : ℝ) * (valInt j : ℝ)) / (27 * (50 : ℝ) ^ 11 * (Dscale : ℝ))) * logR ^ 8 := by ring
      linarith only [ha, hb, hrew]
    have h2 : ((16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16) / logR) *
        (∑ r ∈ sfBin B j, (1 : ℝ) / phiG r) ≤
        C_Hsum * (16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16) * (logR + 1) ^ 7 := by
      have hK_nn : 0 ≤ 16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16 := by
        linarith only [hC2_pos, hC3_pos, hC4_pos, hC5_pos, K59const_nonneg]
      have ha := mul_le_mul_of_nonneg_left hbin_le_H (div_nonneg hK_nn hlogR_pos.le)
      have heq : ((16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16) / logR) * (C_Hsum * logR ^ 8) =
          C_Hsum * (16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16) * logR ^ 7 := by
        field_simp [hlogR_pos.ne']
      have h7 : logR ^ 7 ≤ (logR + 1) ^ 7 := pow_le_pow_left₀ hlogR_pos.le (by linarith) 7
      have hCH_nn : 0 ≤ C_Hsum := by dsimp only [C_Hsum]; positivity
      have hCH_K : 0 ≤ C_Hsum * (16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16) := mul_nonneg hCH_nn hK_nn
      nlinarith only [ha, heq, h7, hCH_K]
    linarith only [h1, h2]
  have htot := Finset.sum_le_sum hterm_ub
  rw [Finset.sum_add_distrib] at htot
  have hmain_sum : ∑ j ∈ Finset.range 50,
      C_P * (((wInt j : ℝ) * (valInt j : ℝ)) / (27 * (50 : ℝ) ^ 11 * (Dscale : ℝ))) * logR ^ 8 =
      C_P * numHiR * logR ^ 8 := by
    unfold numHiR Term2Int; push_cast
    rw [Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
  rw [hmain_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at htot
  linarith only [htot]

private lemma spiro_rem_y_gen {C_om M : ℝ} (hCom_pos : 0 < C_om) (hM_nn : 0 ≤ M)
    (hCom : ∀ d : ℕ, Squarefree d → (omegaD d : ℝ) ≤ C_om * (d : ℝ) ^ ((1 : ℝ) / 100))
    {X R y : ℕ} (hR2 : 2 ≤ R) (hy2 : 2 ≤ y)
    (hrem_scale : C_om * (R : ℝ) ^ 2 * ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 ≤ M / (y : ℝ)) :
    ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) *
      (∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F n), selbergW R n) ≤
    (X : ℝ) * ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * (gF p *
      ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) + M := by
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (show 0 < y by omega)
  have hlogy_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hterm_y : ∀ p ∈ Nat.primesLE y,
      (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) *
        (∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F n), selbergW R n) ≤
      (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * ((X : ℝ) * gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) +
      M / (y : ℝ) := by
    intro p hp
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hple := (Nat.mem_primesLE.mp hp).1
    have hwt_nn : 0 ≤ 1 - Real.log (p : ℝ) / Real.log (y : ℝ) := by
      have : Real.log (p : ℝ) / Real.log (y : ℝ) ≤ 1 := (div_le_one hlogy_pos).mpr
        (Real.log_le_log (by exact_mod_cast hprime.pos) (Nat.cast_le.mpr hple))
      linarith
    have hwt_le1 : 1 - Real.log (p : ℝ) / Real.log (y : ℝ) ≤ 1 := by
      have : 0 ≤ Real.log (p : ℝ) / Real.log (y : ℝ) :=
        div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hprime.one_le)) hlogy_pos.le
      linarith
    have hp_app := (abs_le.mp (sum_selbergW_prime_approx hCom_pos hCom (X := X) hR2 hprime)).2
    have hpr_le : ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) ≤
        ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (by positivity)
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hple) (sq_nonneg _)) (by norm_num)
    have herr_p : C_om * (R : ℝ) ^ 2 * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 ≤
        M / (y : ℝ) :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpr_le (by positivity))
        (pow_nonneg (Hsum_nonneg R) 4)).trans hrem_scale
    have hnn_err : 0 ≤ M / (y : ℝ) := div_nonneg hM_nn hy_pos.le
    have h1 : ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F n), selbergW R n ≤
        (X : ℝ) * gF p * ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r),
          (zW R r + zW R (p * r)) ^ 2 / phiG r + M / (y : ℝ) := by linarith only [hp_app, herr_p]
    have h2 := mul_le_mul_of_nonneg_left h1 hwt_nn
    have h3 : (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * (M / (y : ℝ)) ≤ M / (y : ℝ) := by
      nlinarith only [hwt_le1, hnn_err]
    linarith only [h2, h3]
  have hsum_y := Finset.sum_le_sum hterm_y
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum_y
  have hcard_y : ((Nat.primesLE y).card : ℝ) ≤ (y : ℝ) := by
    have hsub : Nat.primesLE y ⊆ Finset.Icc 1 y := fun p hp => by
      rw [Nat.mem_primesLE] at hp; exact Finset.mem_Icc.mpr ⟨hp.2.one_le, hp.1⟩
    have h1 := Finset.card_le_card hsub; rw [Nat.card_Icc] at h1
    exact Nat.cast_le.mpr (by omega)
  have hmul_y : ((Nat.primesLE y).card : ℝ) * (M / (y : ℝ)) ≤ M := by
    calc ((Nat.primesLE y).card : ℝ) * (M / (y : ℝ))
        ≤ (y : ℝ) * (M / (y : ℝ)) := mul_le_mul_of_nonneg_right hcard_y (div_nonneg hM_nn hy_pos.le)
      _ = M := mul_div_cancel₀ M hy_pos.ne'
  have hfact_X : ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * ((X : ℝ) * gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) =
      (X : ℝ) * ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / Real.log (y : ℝ)) * (gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
  linarith only [hsum_y, hmul_y, hfact_X]

private lemma spiro_rem_B_gen {C_om M : ℝ} (hCom_pos : 0 < C_om) (hM_nn : 0 ≤ M)
    (hCom : ∀ d : ℕ, Squarefree d → (omegaD d : ℝ) ≤ C_om * (d : ℝ) ^ ((1 : ℝ) / 100))
    {B X R y : ℕ} (hR2 : 2 ≤ R) (hy2 : 2 ≤ y) (hBy : B ≤ y)
    (hrem_scale : C_om * (R : ℝ) ^ 2 * ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 ≤ M / (y : ℝ)) :
    36 * ∑ p ∈ Nat.primesLE B, (∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F n), selbergW R n) ≤
    (X : ℝ) * (36 * ∑ p ∈ Nat.primesLE B, gF p *
      ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) + 36 * M := by
  have hy_pos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (show 0 < y by omega)
  have hterm_B : ∀ p ∈ Nat.primesLE B,
      ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => p ∣ F n), selbergW R n ≤
      (X : ℝ) * gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r +
      M / (y : ℝ) := by
    intro p hp
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hple := (Nat.mem_primesLE.mp hp).1.trans hBy
    have hp_app := (abs_le.mp (sum_selbergW_prime_approx hCom_pos hCom (X := X) hR2 hprime)).2
    have hpr_le : ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) ≤
        ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (by positivity)
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hple) (sq_nonneg _)) (by norm_num)
    have herr_p : C_om * (R : ℝ) ^ 2 * ((p : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 ≤
        M / (y : ℝ) :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpr_le (by positivity))
        (pow_nonneg (Hsum_nonneg R) 4)).trans hrem_scale
    linarith only [hp_app, herr_p]
  have hsum_B := Finset.sum_le_sum hterm_B
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum_B
  have hcard_B : ((Nat.primesLE B).card : ℝ) ≤ (y : ℝ) := by
    have hsub : Nat.primesLE B ⊆ Finset.Icc 1 B := fun p hp => by
      rw [Nat.mem_primesLE] at hp; exact Finset.mem_Icc.mpr ⟨hp.2.one_le, hp.1⟩
    have h1 := Finset.card_le_card hsub; rw [Nat.card_Icc] at h1
    exact Nat.cast_le.mpr (by omega)
  have hmul_B : ((Nat.primesLE B).card : ℝ) * (M / (y : ℝ)) ≤ M := by
    calc ((Nat.primesLE B).card : ℝ) * (M / (y : ℝ))
        ≤ (y : ℝ) * (M / (y : ℝ)) := mul_le_mul_of_nonneg_right hcard_B (div_nonneg hM_nn hy_pos.le)
      _ = M := mul_div_cancel₀ M hy_pos.ne'
  have hfact_X : 36 * ∑ p ∈ Nat.primesLE B, (X : ℝ) * gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r =
      (X : ℝ) * (36 * ∑ p ∈ Nat.primesLE B, gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) := by
    rw [← mul_assoc, mul_comm (X : ℝ) 36, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => by ring
  linarith only [hsum_B, hmul_B, hfact_X]

private lemma spiro_rem_bounds {C_om C_P M0 : ℝ}
    (hCom_pos : 0 < C_om) (hCP_pos : 0 < C_P) (hM0_pos : 0 < M0)
    (hCom : ∀ d : ℕ, Squarefree d → (omegaD d : ℝ) ≤ C_om * (d : ℝ) ^ ((1 : ℝ) / 100))
    {B : ℕ} (hB : 6000 ≤ B)
    (hH_R_le_cap : Hsum (B ^ 100) ≤ (C_P + 2 * M0 + 1) * (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 8) :
    let X := B ^ 400
    let R := B ^ 100
    let y := B ^ 180
    let logR := Real.log (R : ℝ)
    let logy := Real.log (y : ℝ)
    let I := Finset.Ioc X (2 * X)
    let C_Hsum := C_P + 2 * M0
    (∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) *
        (∑ n ∈ I.filter (fun n => p ∣ F n), selbergW R n) ≤
      (X : ℝ) * ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) * (gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) +
      C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ)) ∧
    (36 * ∑ p ∈ Nat.primesLE B, (∑ n ∈ I.filter (fun n => p ∣ F n), selbergW R n) ≤
      (X : ℝ) * (36 * ∑ p ∈ Nat.primesLE B, gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) +
      36 * C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ)) ∧
    (C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 ≤
      C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ)) := by
  dsimp only
  let X := B ^ 400
  let R := B ^ 100
  let y := B ^ 180
  let logR := Real.log (R : ℝ)
  let C_Hsum := C_P + 2 * M0
  let M := C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ)
  have hB2 : 2 ≤ B := by omega
  have hR2 : 2 ≤ R := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hy2 : 2 ≤ y := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hBy : B ≤ y := Nat.le_self_pow (by norm_num) B
  have hlogR_pos : 0 < logR := Real.log_pos (Nat.one_lt_cast.mpr (by omega : 1 < R))
  have hM_nn : 0 ≤ M := by dsimp only [M, C_Hsum]; positivity
  have hrem_scale : C_om * (R : ℝ) ^ 2 * ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 ≤ M / (y : ℝ) := by
    dsimp only [M]
    have hy_pos : (0 : ℝ) < (y : ℝ) := Nat.cast_pos.mpr (by omega)
    have hB_pos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr (by omega)
    have hpow_le : ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) ≤ (B : ℝ) ^ 4 := by
      have h380 : (y : ℝ) * (R : ℝ) ^ 2 ≤ (B : ℝ) ^ 400 := by
        dsimp only [y, R]; rw [Nat.cast_pow, Nat.cast_pow]
        have h1 : (B : ℝ) ^ 380 ≤ (B : ℝ) ^ 400 :=
          pow_le_pow_right₀ (Nat.one_le_cast.mpr (by omega)) (by norm_num)
        have h2 : (B : ℝ) ^ 180 * ((B : ℝ) ^ 100) ^ 2 = (B : ℝ) ^ 380 := by rw [← pow_mul, ← pow_add]
        linarith only [h1, h2]
      calc ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100)
          ≤ ((B : ℝ) ^ (400 : ℕ)) ^ ((1 : ℝ) / 100) := Real.rpow_le_rpow (by positivity) h380 (by norm_num)
        _ = (B : ℝ) ^ (4 : ℕ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hB_pos.le]; norm_num
    have hH4 : (Hsum R) ^ 4 ≤ (C_Hsum + 1) ^ 4 * (logR + 1) ^ 32 := by
      calc (Hsum R) ^ 4 ≤ ((C_Hsum + 1) * (logR + 1) ^ 8) ^ 4 :=
            pow_le_pow_left₀ (Hsum_nonneg R) hH_R_le_cap 4
        _ = (C_Hsum + 1) ^ 4 * (logR + 1) ^ 32 := by rw [mul_pow, ← pow_mul]
    have hB_id : (y : ℝ) * (R : ℝ) ^ 2 * (B : ℝ) ^ 4 = (X : ℝ) / (B : ℝ) ^ 16 := by
      dsimp only [y, R, X]
      rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, eq_div_iff (pow_ne_zero 16 hB_pos.ne')]
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    rw [le_div_iff₀ hy_pos]
    calc C_om * (R : ℝ) ^ 2 * ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 * (y : ℝ)
        = C_om * ((y : ℝ) * (R : ℝ) ^ 2 * ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100)) * (Hsum R) ^ 4 := by ring
      _ ≤ C_om * ((y : ℝ) * (R : ℝ) ^ 2 * (B : ℝ) ^ 4) * ((C_Hsum + 1) ^ 4 * (logR + 1) ^ 32) := by gcongr
      _ = C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ) := by
          rw [hB_id]
          generalize (logR + 1) ^ 32 = L32
          generalize (C_Hsum + 1) ^ 4 = CH4
          generalize (B : ℝ) ^ 16 = B16
          ring
  have hrem_y := spiro_rem_y_gen hCom_pos hM_nn hCom (X := X) hR2 hy2 hrem_scale
  have hrem_B := spiro_rem_B_gen hCom_pos hM_nn hCom (X := X) hR2 hy2 hBy hrem_scale
  have hrem0_le : C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 ≤ M := by
    have h1 : ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) ≤ ((y : ℝ) * (R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow (by positivity)
        (le_mul_of_one_le_left (sq_nonneg _) (Nat.one_le_cast.mpr (by omega))) (by norm_num)
    have h2 := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity))
      (pow_nonneg (Hsum_nonneg R) 4)).trans hrem_scale
    exact h2.trans (div_le_self hM_nn (Nat.one_le_cast.mpr (by omega)))
  refine ⟨hrem_y, ?_, hrem0_le⟩
  have hassoc : 36 * M = 36 * C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ) := by
    dsimp only [M]; simp only [mul_assoc]
  rwa [hassoc] at hrem_B

set_option maxHeartbeats 800000 in
private lemma spiro_main_ineq {C_om C_P M0 C2 C3 C4 C5 : ℝ}
    (hCom_pos : 0 < C_om) (hCP_pos : 0 < C_P) (hM0_pos : 0 < M0)
    (hC2_pos : 0 < C2) (hC3_pos : 0 < C3) (hC4_pos : 0 < C4) (hC5_pos : 0 < C5)
    (hCom : ∀ d : ℕ, Squarefree d → (omegaD d : ℝ) ≤ C_om * (d : ℝ) ^ ((1 : ℝ) / 100))
    (hH : ∀ u : ℕ, 2 ≤ u → |Hsum u - C_P * (Real.log u) ^ 8| ≤ M0 * (Real.log u + 1) ^ 7)
    (hC2 : ∀ n : ℕ, 2 ≤ n → ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 2 / (p : ℝ) ≤
      (1 / 2) * (Real.log n) ^ 2 + C2 * (Real.log n + 1))
    (hC3 : ∀ n : ℕ, 2 ≤ n → (1 / 3) * (Real.log n) ^ 3 - C3 * (Real.log n + 1) ^ 2 ≤
      ∑ p ∈ Nat.primesLE n, (Real.log p) ^ 3 / (p : ℝ))
    (hC4 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, (1 : ℝ) / (p : ℝ) ≤
        Real.log (Real.log b / Real.log a) + C4 / Real.log a)
    (hC5 : ∀ a b : ℕ, 2 ≤ a → a ≤ b →
      Real.log b - Real.log a - C5 ≤
        ∑ p ∈ Nat.primesLE b \ Nat.primesLE a, Real.log p / (p : ℝ)) :
    ∃ E1 E2 : ℝ, 0 < E1 ∧ 0 < E2 ∧ ∀ B : ℕ, 6000 ≤ B →
      let X := B ^ 400
      let R := B ^ 100
      let logR := Real.log (R : ℝ)
      ((1 / 50 : ℝ) * C_P - E1 / logR - E2 * (logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ) * logR ^ 8 ≤
        ∑ n ∈ Finset.Ioc X (2 * X), selbergW R n * Score B n := by
  let C_Hsum : ℝ := C_P + 2 * M0
  let E_bin : ℝ := 50 * (2 * M0) * (36 - 160 / 9 - J2UbR) +
    50 * (2 * M0) * (8 * (1 + (logUbInt 50 1 : ℝ) / (Dscale : ℝ))) +
    50 * C_Hsum * (16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16) +
    C_Hsum * (8 * Real.log 119 + 8 * C4 + 8 * C5 + 1) +
    36 * 8 * C2 * C_Hsum + 36 * 4 * (2 * M0) + 100
  let E_rem : ℝ := 74 * C_om * (C_Hsum + 1) ^ 4 + 1
  have hEbin_pos : 0 < E_bin := by
    dsimp only [E_bin, C_Hsum]
    have h1 := J2coeff_pos
    have h2 := K59const_nonneg
    have h3 : 0 ≤ Real.log 119 := Real.log_nonneg (by norm_num)
    positivity
  refine ⟨E_bin * 2 ^ 7 + 1, E_rem + 1, by positivity, by positivity, fun B hB => ?_⟩
  dsimp only
  let X := B ^ 400
  let R := B ^ 100
  let y := B ^ 180
  let logR := Real.log (R : ℝ)
  let logy := Real.log (y : ℝ)
  let logB := Real.log (B : ℝ)
  let I := Finset.Ioc X (2 * X)
  let Isf := ∑ r ∈ sfLE R, (zW R r) ^ 2 / phiG r
  have hB2 : 2 ≤ B := by omega
  have hX1 : 1 ≤ X := one_le_pow₀ (by omega)
  have hR2 : 2 ≤ R := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hy2 : 2 ≤ y := le_trans hB2 (Nat.le_self_pow (by norm_num) B)
  have hlogB_pos : 0 < logB := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogB_ge1 : 1 ≤ logB := by
    have h3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hB3 : (3 : ℝ) ≤ B := by exact_mod_cast (show 3 ≤ B by omega)
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hlogR_eq : logR = 100 * logB := by dsimp only [logR, R, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogy_eq : logy = 180 * logB := by dsimp only [logy, y, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogR_ge64 : 64 ≤ logR := by linarith only [hlogR_eq, hlogB_ge1]
  have hlogR_ge1 : 1 ≤ logR := by linarith only [hlogR_ge64]
  have hlogR_pos : 0 < logR := by linarith only [hlogR_ge1]
  have hlogy_pos : 0 < logy := by rw [hlogy_eq]; positivity
  have hpow7_le : (logR + 1) ^ 7 ≤ 2 ^ 7 * logR ^ 7 := by
    calc (logR + 1) ^ 7 ≤ (2 * logR) ^ 7 := pow_le_pow_left₀ (by linarith) (by linarith) 7
      _ = 2 ^ 7 * logR ^ 7 := mul_pow _ _ _
  have hH_R_le : Hsum R ≤ C_Hsum * logR ^ 8 := by
    have hb := (abs_le.mp (hH R hR2)).2
    have h7 : (logR + 1) ^ 7 ≤ 2 * logR ^ 8 := by
      have : 2 ^ 7 * logR ^ 7 ≤ (2 * logR) * logR ^ 7 :=
        mul_le_mul_of_nonneg_right (by linarith only [hlogR_ge64]) (pow_nonneg hlogR_pos.le 7)
      have heq : (2 * logR) * logR ^ 7 = 2 * logR ^ 8 := by ring
      linarith only [hpow7_le, this, heq]
    dsimp only [C_Hsum]
    nlinarith only [hb, h7, hM0_pos]
  have hH_R_le_cap : Hsum R ≤ (C_Hsum + 1) * (logR + 1) ^ 8 := by
    have h1 : logR ^ 8 ≤ (logR + 1) ^ 8 := pow_le_pow_left₀ hlogR_pos.le (by linarith) 8
    have hCH_nn : 0 ≤ C_Hsum := by dsimp only [C_Hsum]; positivity
    nlinarith only [hH_R_le, h1, hCH_nn, pow_nonneg hlogR_pos.le 8]
  have hIsf_nn : 0 ≤ Isf := Finset.sum_nonneg fun r _ => div_nonneg (sq_nonneg _) (phiG_pos r).le
  have hIsf_le_H : Isf ≤ Hsum R := by
    apply Finset.sum_le_sum; intro r hr
    rw [zW_sq_eq hr]
    have hr_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
    have h1 : 0 ≤ Real.log (r : ℝ) / logR := div_nonneg (Real.log_nonneg (by exact_mod_cast hr_Icc.1)) hlogR_pos.le
    have h2 : Real.log (r : ℝ) / logR ≤ 1 := (div_le_one hlogR_pos).mpr
      (Real.log_le_log (by exact_mod_cast hr_Icc.1) (by exact_mod_cast hr_Icc.2))
    exact div_le_div_of_nonneg_right (by nlinarith only [h1, h2]) (phiG_pos r).le
  -- Invoke the 4 modular main-term lemmas
  have hIsf_lo := Isf_lower_bound hCP_pos hM0_pos hH hB2
  have hsmall_main := small_primes_upper_bound hCP_pos hM0_pos hC2_pos hH hC2 hB hH_R_le
  have hupper_main := upper_primes_upper_bound hC4_pos hC5_pos hC4 hC5 hB
  have hlower_main := lower_primes_upper_bound hCP_pos hM0_pos hC2_pos hC3_pos hC4_pos hC5_pos
    hH hC2 hC3 hC4 hC5 hB hH_R_le
  -- Pointwise Richert sum swap
  have hscore_sum :
      (36 - 8 * Real.log (119 * (X : ℝ)) / logy) * (∑ n ∈ I, selbergW R n) -
      ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) *
        (∑ n ∈ I.filter (fun n => p ∣ F n), selbergW R n) -
      36 * ∑ p ∈ Nat.primesLE B, (∑ n ∈ I.filter (fun n => p ∣ F n), selbergW R n) ≤
      ∑ n ∈ I, selbergW R n * Score B n := by
    have h1 : ∑ n ∈ I, selbergW R n *
        (36 - 8 * Real.log (119 * (X : ℝ)) / logy -
          ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F n), (1 - Real.log (p : ℝ) / logy) -
          36 * ∑ p ∈ (Nat.primesLE B).filter (fun p => p ∣ F n), (1 : ℝ)) ≤
        ∑ n ∈ I, selbergW R n * Score B n := by
      apply Finset.sum_le_sum; intro n hn
      exact mul_le_mul_of_nonneg_left
        (score_ge_richert hy2 hX1 (Finset.mem_Ioc.mp hn).2) (selbergW_nonneg R n)
    refine le_trans ?_ h1
    have hA : ∑ n ∈ I, selbergW R n * (36 - 8 * Real.log (119 * (X : ℝ)) / logy) =
        (36 - 8 * Real.log (119 * (X : ℝ)) / logy) * (∑ n ∈ I, selbergW R n) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => mul_comm _ _
    have hB_swap : ∑ n ∈ I, selbergW R n *
        ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F n), (1 - Real.log (p : ℝ) / logy) =
        ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) *
          ∑ n ∈ I.filter (fun n => p ∣ F n), selbergW R n := by
      trans ∑ n ∈ I, ∑ p ∈ Nat.primesLE y,
        if p ∣ F n then selbergW R n * (1 - Real.log (p : ℝ) / logy) else 0
      · refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum, Finset.sum_filter]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
    have hC_swap : ∑ n ∈ I, selbergW R n *
        (36 * ∑ p ∈ (Nat.primesLE B).filter (fun p => p ∣ F n), (1 : ℝ)) =
        36 * ∑ p ∈ Nat.primesLE B, ∑ n ∈ I.filter (fun n => p ∣ F n), selbergW R n := by
      trans 36 * ∑ n ∈ I, ∑ p ∈ Nat.primesLE B, if p ∣ F n then selbergW R n else 0
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => by split_ifs <;> ring
      · rw [Finset.sum_comm]; congr 1
        refine Finset.sum_congr rfl fun p _ => by rw [Finset.sum_filter]
    have hexp : ∑ n ∈ I, selbergW R n *
        (36 - 8 * Real.log (119 * (X : ℝ)) / logy -
          ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F n), (1 - Real.log (p : ℝ) / logy) -
          36 * ∑ p ∈ (Nat.primesLE B).filter (fun p => p ∣ F n), (1 : ℝ)) =
        (36 - 8 * Real.log (119 * (X : ℝ)) / logy) * (∑ n ∈ I, selbergW R n) -
        ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) *
          (∑ n ∈ I.filter (fun n => p ∣ F n), selbergW R n) -
        36 * ∑ p ∈ Nat.primesLE B, (∑ n ∈ I.filter (fun n => p ∣ F n), selbergW R n) := by
      calc _ = ∑ n ∈ I, (selbergW R n * (36 - 8 * Real.log (119 * (X : ℝ)) / logy) -
              selbergW R n * ∑ p ∈ (Nat.primesLE y).filter (fun p => p ∣ F n), (1 - Real.log (p : ℝ) / logy) -
              selbergW R n * (36 * ∑ p ∈ (Nat.primesLE B).filter (fun p => p ∣ F n), (1 : ℝ))) :=
            Finset.sum_congr rfl fun n _ => by ring
        _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hA, hB_swap, hC_swap]
    exact hexp.ge
  -- Sieve remainder bounds from helper lemma
  obtain ⟨hrem_y, hrem_B, hrem0_le⟩ := spiro_rem_bounds hCom_pos hCP_pos hM0_pos hCom hB hH_R_le_cap
  have h160_bound : 8 * Real.log (119 * (X : ℝ)) / logy ≤ 160 / 9 + 8 * Real.log 119 / logR := by
    have hlogX : Real.log (119 * (X : ℝ)) = Real.log 119 + 400 * logB := by
      rw [Real.log_mul (by norm_num) (by positivity)]
      dsimp only [X, logB]; rw [Nat.cast_pow, Real.log_pow]; norm_num
    rw [hlogX, hlogy_eq, hlogR_eq]
    have heq : 8 * (Real.log 119 + 400 * logB) / (180 * logB) =
        160 / 9 + 8 * Real.log 119 / (180 * logB) := by field_simp [hlogB_pos.ne']; ring
    rw [heq]
    have hnn : 0 ≤ 8 * Real.log 119 := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 119); positivity
    have hle : 8 * Real.log 119 / (180 * logB) ≤ 8 * Real.log 119 / (100 * logB) :=
      div_le_div_of_nonneg_left hnn (by positivity) (by linarith only [hlogB_pos])
    linarith only [hle]
  have hcoeff0_pos : 0 ≤ 36 - 8 * Real.log (119 * (X : ℝ)) / logy := by
    have hlog119 : Real.log 119 ≤ 7 := by
      have h1 : Real.log 119 ≤ Real.log (128 : ℝ) := Real.log_le_log (by norm_num) (by norm_num)
      have h2 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
        rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
      have h3 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      linarith only [h1, h2, h3]
    have : 8 * Real.log 119 / logR ≤ 1 := by rw [div_le_one hlogR_pos]; linarith only [hlog119, hlogR_ge64]
    linarith only [h160_bound, this]
  have hcoeff0_le36 : 36 - 8 * Real.log (119 * (X : ℝ)) / logy ≤ 36 := by
    have : 0 ≤ 8 * Real.log (119 * (X : ℝ)) / logy := by
      have : 0 ≤ Real.log (119 * (X : ℝ)) := Real.log_nonneg (by
        have hX1' : (1 : ℝ) ≤ X := Nat.one_le_cast.mpr hX1
        linarith)
      positivity
    linarith only [this]
  have hrem1 := (abs_le.mp (sum_selbergW_approx hCom_pos hCom (X := X) hR2)).1
  have hsubRY : Nat.primesLE R ⊆ Nat.primesLE y := fun p hp => by
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans (Nat.pow_le_pow_right (by omega) (by norm_num)), hp.2⟩
  have hy_split : ∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) * (gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) =
      (∑ p ∈ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * (gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r)) +
      (∑ p ∈ Nat.primesLE y \ Nat.primesLE R, (1 - Real.log (p : ℝ) / logy) * (gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r)) :=
    (Finset.sum_sdiff hsubRY).symm.trans (add_comm _ _)
  -- Combine the 4 main terms cleanly using `linarith only`
  have hmain_comb : ((1 / 50 : ℝ) * C_P - (E_bin * 2 ^ 7 + 1) / logR) * logR ^ 8 ≤
      (36 - 8 * Real.log (119 * (X : ℝ)) / logy) * Isf -
      (∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) * (gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r)) -
      36 * ∑ p ∈ Nat.primesLE B, gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r := by
    rw [hy_split]
    have hcoeff_main : (36 - 160 / 9 - J2UbR) * Isf -
        ((8 * Real.log 119 + 8 * C4 + 8 * C5) / logR) * Isf ≤
        (36 - 8 * Real.log (119 * (X : ℝ)) / logy) * Isf -
        (J2UbR + (8 * C4 + 8 * C5) / logR) * Isf := by
      have h1 : (36 - 160 / 9 - 8 * Real.log 119 / logR) * Isf ≤
          (36 - 8 * Real.log (119 * (X : ℝ)) / logy) * Isf :=
        mul_le_mul_of_nonneg_right (by linarith only [h160_bound]) hIsf_nn
      have h2 : (36 - 160 / 9 - J2UbR) * Isf - ((8 * Real.log 119 + 8 * C4 + 8 * C5) / logR) * Isf =
          (36 - 160 / 9 - 8 * Real.log 119 / logR) * Isf - (J2UbR + (8 * C4 + 8 * C5) / logR) * Isf := by ring
      linarith only [h1, h2]
    have hIsf_err : ((8 * Real.log 119 + 8 * C4 + 8 * C5) / logR) * Isf ≤
        C_Hsum * (8 * Real.log 119 + 8 * C4 + 8 * C5 + 1) * (logR + 1) ^ 7 := by
      have hlog119_nn : 0 ≤ Real.log 119 := Real.log_nonneg (by norm_num)
      have h1 : ((8 * Real.log 119 + 8 * C4 + 8 * C5) / logR) * Isf ≤
          ((8 * Real.log 119 + 8 * C4 + 8 * C5) / logR) * (C_Hsum * logR ^ 8) :=
        mul_le_mul_of_nonneg_left (hIsf_le_H.trans hH_R_le) (by positivity)
      have h2 : ((8 * Real.log 119 + 8 * C4 + 8 * C5) / logR) * (C_Hsum * logR ^ 8) =
          C_Hsum * (8 * Real.log 119 + 8 * C4 + 8 * C5) * logR ^ 7 := by
        field_simp [hlogR_pos.ne']
      have h7 : logR ^ 7 ≤ (logR + 1) ^ 7 := pow_le_pow_left₀ hlogR_pos.le (by linarith) 7
      have hCH_nn : 0 ≤ C_Hsum := by dsimp only [C_Hsum]; positivity
      have hK_nn : 0 ≤ C_Hsum * (8 * Real.log 119 + 8 * C4 + 8 * C5) :=
        mul_nonneg hCH_nn (by linarith only [hlog119_nn, hC4_pos, hC5_pos])
      have h3 : C_Hsum * (8 * Real.log 119 + 8 * C4 + 8 * C5) * logR ^ 7 ≤
          C_Hsum * (8 * Real.log 119 + 8 * C4 + 8 * C5) * (logR + 1) ^ 7 :=
        mul_le_mul_of_nonneg_left h7 hK_nn
      have h4 : 0 ≤ C_Hsum * (logR + 1) ^ 7 :=
        mul_nonneg hCH_nn (pow_nonneg (by linarith only [hlogR_pos]) 7)
      linarith only [h1, h2, h3, h4]
    have hpos_Isf := mul_le_mul_of_nonneg_left hIsf_lo J2coeff_pos.le
    have hlead : (1 / 50 : ℝ) * C_P * logR ^ 8 ≤
        ((36 - 160 / 9 - J2UbR) * I0LoR - numHiR - 144 / 10000) * C_P * logR ^ 8 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right margin_real_ge hCP_pos.le)
        (pow_nonneg hlogR_pos.le 8)
    have hEbin_bound : E_bin * (logR + 1) ^ 7 ≤ ((E_bin * 2 ^ 7 + 1) / logR) * logR ^ 8 := by
      have heq : ((E_bin * 2 ^ 7 + 1) / logR) * logR ^ 8 = (E_bin * 2 ^ 7 + 1) * logR ^ 7 := by
        field_simp [hlogR_pos.ne']
      rw [heq]
      nlinarith only [hEbin_pos, hpow7_le, pow_nonneg hlogR_pos.le 7]
    have hEbin_expand : E_bin * (logR + 1) ^ 7 =
        (50 * (2 * M0) * (36 - 160 / 9 - J2UbR)) * (logR + 1) ^ 7 +
        (50 * (2 * M0) * (8 * (1 + (logUbInt 50 1 : ℝ) / (Dscale : ℝ))) +
          50 * C_Hsum * (16 * C2 + 32 * C3 + 8 * C4 + 8 * C5 + K59const + 16)) * (logR + 1) ^ 7 +
        C_Hsum * (8 * Real.log 119 + 8 * C4 + 8 * C5 + 1) * (logR + 1) ^ 7 +
        (36 * 8 * C2 * C_Hsum + 36 * 4 * (2 * M0)) * (logR + 1) ^ 7 +
        100 * (logR + 1) ^ 7 := by generalize (logR + 1) ^ 7 = L7; dsimp only [E_bin]; ring
    have hnn7 : 0 ≤ (logR + 1) ^ 7 := by positivity
    have hlead_exp : ((36 - 160 / 9 - J2UbR) * I0LoR - numHiR - 144 / 10000) * C_P * logR ^ 8 =
        (36 - 160 / 9 - J2UbR) * (C_P * I0LoR * logR ^ 8) -
        C_P * numHiR * logR ^ 8 - (144 / 10000) * C_P * logR ^ 8 := by generalize logR ^ 8 = L8; ring
    have hpos_exp : (36 - 160 / 9 - J2UbR) * (C_P * I0LoR * logR ^ 8 - 50 * (2 * M0) * (logR + 1) ^ 7) =
        (36 - 160 / 9 - J2UbR) * (C_P * I0LoR * logR ^ 8) -
        50 * (2 * M0) * (36 - 160 / 9 - J2UbR) * (logR + 1) ^ 7 := by
      generalize (logR + 1) ^ 7 = L7; generalize logR ^ 8 = L8; ring
    have hlhs_exp : ((1 / 50 : ℝ) * C_P - (E_bin * 2 ^ 7 + 1) / logR) * logR ^ 8 =
        (1 / 50 : ℝ) * C_P * logR ^ 8 - ((E_bin * 2 ^ 7 + 1) / logR) * logR ^ 8 := by
      generalize logR ^ 8 = L8; ring
    linarith only [hupper_main, hlower_main, hsmall_main, hcoeff_main, hIsf_err,
      hpos_Isf, hlead, hEbin_bound, hEbin_expand, hnn7, hlead_exp, hpos_exp, hlhs_exp]
  -- Final assembly with sieve remainders
  have hX_nn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hmain_X := mul_le_mul_of_nonneg_left hmain_comb hX_nn
  have hrem_tot : (36 - 8 * Real.log (119 * (X : ℝ)) / logy) *
        (C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4) +
      C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ) +
      36 * C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ) ≤
      (E_rem + 1) * (logR + 1) ^ 32 / (B : ℝ) ^ 16 * (X : ℝ) * logR ^ 8 := by
    have h36 : (36 - 8 * Real.log (119 * (X : ℝ)) / logy) *
        (C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4) ≤
        36 * (C_om * (C_Hsum + 1) ^ 4 * ((logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ)) :=
      mul_le_mul hcoeff0_le36 hrem0_le (by positivity) (by norm_num)
    have hlog8_ge1 : (1 : ℝ) ≤ logR ^ 8 := one_le_pow₀ hlogR_ge1
    have h73 : 73 * C_om * (C_Hsum + 1) ^ 4 ≤ E_rem + 1 := by
      dsimp only [E_rem]
      have hCH4_nn : 0 ≤ C_om * (C_Hsum + 1) ^ 4 := by dsimp only [C_Hsum]; positivity
      linarith only [hCH4_nn]
    have hfrac_nn : 0 ≤ ((logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ) := by positivity
    calc _ ≤ (73 * C_om * (C_Hsum + 1) ^ 4) * (((logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ)) := by
            linarith only [h36]
      _ ≤ (E_rem + 1) * (((logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ)) :=
          mul_le_mul_of_nonneg_right h73 hfrac_nn
      _ ≤ (E_rem + 1) * (((logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ)) * logR ^ 8 :=
          le_mul_of_one_le_right (by dsimp only [E_rem, C_Hsum]; positivity) hlog8_ge1
      _ = (E_rem + 1) * (logR + 1) ^ 32 / (B : ℝ) ^ 16 * (X : ℝ) * logR ^ 8 := by
          generalize (logR + 1) ^ 32 = L32; generalize (B : ℝ) ^ 16 = B16; generalize logR ^ 8 = L8; ring
  have hstep0 : (36 - 8 * Real.log (119 * (X : ℝ)) / logy) * ((X : ℝ) * Isf) -
      (36 - 8 * Real.log (119 * (X : ℝ)) / logy) *
        (C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4) ≤
      (36 - 8 * Real.log (119 * (X : ℝ)) / logy) * (∑ n ∈ I, selbergW R n) := by
    have hmul := mul_le_mul_of_nonneg_left
      (by linarith only [hrem1] : (X : ℝ) * Isf -
        C_om * (R : ℝ) ^ 2 * ((R : ℝ) ^ 2) ^ ((1 : ℝ) / 100) * (Hsum R) ^ 4 ≤
        ∑ n ∈ I, selbergW R n) hcoeff0_pos
    linarith only [hmul]
  have hlhs_rew : ((1 / 50 : ℝ) * C_P - (E_bin * 2 ^ 7 + 1) / logR -
        (E_rem + 1) * (logR + 1) ^ 32 / (B : ℝ) ^ 16) * (X : ℝ) * logR ^ 8 =
      (X : ℝ) * (((1 / 50 : ℝ) * C_P - (E_bin * 2 ^ 7 + 1) / logR) * logR ^ 8) -
      (E_rem + 1) * (logR + 1) ^ 32 / (B : ℝ) ^ 16 * (X : ℝ) * logR ^ 8 := by
    generalize (logR + 1) ^ 32 = L32; generalize (B : ℝ) ^ 16 = B16; generalize logR ^ 8 = L8; ring
  have hX_dist : (X : ℝ) * ((36 - 8 * Real.log (119 * (X : ℝ)) / logy) * Isf -
        (∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) * (gF p *
          ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r)) -
        36 * ∑ p ∈ Nat.primesLE B, gF p *
          ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) =
      (36 - 8 * Real.log (119 * (X : ℝ)) / logy) * ((X : ℝ) * Isf) -
      (X : ℝ) * (∑ p ∈ Nat.primesLE y, (1 - Real.log (p : ℝ) / logy) * (gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r)) -
      (X : ℝ) * (36 * ∑ p ∈ Nat.primesLE B, gF p *
        ∑ r ∈ (sfLE R).filter (fun r => ¬ p ∣ r), (zW R r + zW R (p * r)) ^ 2 / phiG r) := by ring
  rw [hlhs_rew]
  linarith only [hscore_sum, hstep0, hrem_y, hrem_B, hrem_tot, hmain_X, hX_dist]

set_option maxHeartbeats 800000 in
private lemma spiro_H1_proof : OMA.R_Erdos946_erdos_946_variants_spiro_5040_R1.H1 := by
  refine ⟨400, by norm_num, ?_⟩
  obtain ⟨C_om, hCom_pos, hCom⟩ := omegaD_le_const_rpow
  obtain ⟨C_P, hCP_pos, M0, hM0_pos, hH⟩ := Hsum_asymp
  obtain ⟨C2, hC2_pos, hC2⟩ := sum_log_sq_div_p_le
  obtain ⟨C3, hC3_pos, hC3⟩ := sum_log_cube_div_p_ge
  obtain ⟨C4, hC4_pos, hC4⟩ := sum_inv_p_Ioc_le
  obtain ⟨C5, hC5_pos, hC5⟩ := sum_log_div_p_Ioc_ge
  obtain ⟨E1, E2, hE1_pos, hE2_pos, hmain⟩ :=
    spiro_main_ineq hCom_pos hCP_pos hM0_pos hC2_pos hC3_pos hC4_pos hC5_pos
      hCom hH hC2 hC3 hC4 hC5
  have hlog32 : ∃ C_L : ℝ, 0 < C_L ∧ ∀ B : ℕ, 2 ≤ B →
      (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 32 ≤ C_L * (B : ℝ) ^ ((1 : ℝ) / 2) := by
    refine ⟨(100 * 64 + 1) ^ 32, by positivity, fun B hB => ?_⟩
    have hB_pos : (0 : ℝ) < B := by positivity
    have hlogB : Real.log (B : ℝ) ≤ 64 * (B : ℝ) ^ ((1 : ℝ) / 64) := by
      have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hB_pos (1 / 64))
      rw [Real.log_rpow hB_pos] at h
      linarith
    have hB_rpow_ge1 : (1 : ℝ) ≤ (B : ℝ) ^ ((1 : ℝ) / 64) :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ B by omega)) (by norm_num)
    have hR : Real.log ((B ^ 100 : ℕ) : ℝ) + 1 ≤ (100 * 64 + 1) * (B : ℝ) ^ ((1 : ℝ) / 64) := by
      rw [Nat.cast_pow, Real.log_pow]; push_cast; nlinarith only [hlogB, hB_rpow_ge1]
    calc (Real.log ((B ^ 100 : ℕ) : ℝ) + 1) ^ 32
        ≤ ((100 * 64 + 1) * (B : ℝ) ^ ((1 : ℝ) / 64)) ^ 32 :=
          pow_le_pow_left₀ (by positivity) hR 32
      _ = (100 * 64 + 1) ^ 32 * ((B : ℝ) ^ ((1 : ℝ) / 64)) ^ 32 := mul_pow _ _ _
      _ = (100 * 64 + 1) ^ 32 * (B : ℝ) ^ ((1 : ℝ) / 2) := by
          congr 1; rw [← Real.rpow_natCast, ← Real.rpow_mul hB_pos.le]; norm_num
  obtain ⟨C_L, hCL_pos, hCL⟩ := hlog32
  let K_U : ℝ := 36 * ((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 * C_L
  obtain ⟨B1, hB1⟩ := exists_nat_gt (Real.exp (200 * E1 / C_P))
  obtain ⟨B2, hB2⟩ := exists_nat_gt (200 * E2 * C_L / C_P)
  obtain ⟨B3, hB3⟩ := exists_nat_gt ((2000 * K_U / ((1 / 100 : ℝ) * C_P)) ^ 2)
  let B0 := max (max 6000 B1) (max B2 B3)
  rw [Filter.eventually_atTop]
  refine ⟨B0, fun B hB => ?_⟩
  have hB6000 : 6000 ≤ B := (le_trans (le_max_left 6000 B1) (le_max_left _ _)).trans hB
  have hB_gt1 : Real.exp (200 * E1 / C_P) < (B : ℝ) :=
    hB1.trans_le (by exact_mod_cast (le_trans (le_max_right 6000 B1) (le_max_left _ _)).trans hB)
  have hB_gt2 : 200 * E2 * C_L / C_P < (B : ℝ) :=
    hB2.trans_le (by exact_mod_cast (le_trans (le_max_left B2 B3) (le_max_right _ _)).trans hB)
  have hB_gt3 : (2000 * K_U / ((1 / 100 : ℝ) * C_P)) ^ 2 < (B : ℝ) :=
    hB3.trans_le (by exact_mod_cast (le_trans (le_max_right B2 B3) (le_max_right _ _)).trans hB)
  let X := B ^ 400
  let R := B ^ 100
  let logR := Real.log (R : ℝ)
  have hB2_nat : 2 ≤ B := by omega
  have hR2 : 2 ≤ R := le_trans hB2_nat (Nat.le_self_pow (by norm_num) B)
  have hB_pos : (0 : ℝ) < B := by positivity
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogR_eq : logR = 100 * Real.log (B : ℝ) := by dsimp only [logR, R]; rw [Nat.cast_pow, Real.log_pow]; norm_num
  have hlogR_pos : 0 < logR := by rw [hlogR_eq]; positivity
  have hE1_small : E1 / logR ≤ (1 / 200 : ℝ) * C_P := by
    have hlg := Real.log_lt_log (Real.exp_pos _) hB_gt1
    rw [Real.log_exp] at hlg
    rw [div_le_iff₀ hlogR_pos]
    have h1 : 200 * E1 / C_P < logR := by linarith only [hlg, hlogR_eq, hlogB_pos]
    have hmul := (div_lt_iff₀ hCP_pos).mp h1
    linarith only [hmul]
  have hE2_small : E2 * (logR + 1) ^ 32 / (B : ℝ) ^ 16 ≤ (1 / 200 : ℝ) * C_P := by
    have h1 := hCL B hB2_nat
    have hB15 : (B : ℝ) ^ ((1 : ℝ) / 2) * (B : ℝ) ≤ (B : ℝ) ^ (16 : ℕ) := by
      have hB1' : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
      have hsq : (B : ℝ) ^ ((1 : ℝ) / 2) ≤ (B : ℝ) := by
        simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB1' (by norm_num : (1 : ℝ) / 2 ≤ 1)
      have h2 : (B : ℝ) * (B : ℝ) ≤ (B : ℝ) ^ (16 : ℕ) := by
        simpa [sq] using pow_le_pow_right₀ hB1' (show 2 ≤ 16 by norm_num)
      nlinarith only [hsq, h2, hB_pos]
    calc E2 * (logR + 1) ^ 32 / (B : ℝ) ^ 16
        ≤ E2 * (C_L * (B : ℝ) ^ ((1 : ℝ) / 2)) / ((B : ℝ) ^ ((1 : ℝ) / 2) * (B : ℝ)) := by
          apply div_le_div₀ (by positivity) (by gcongr) (by positivity) hB15
      _ = E2 * C_L / (B : ℝ) := by
          have hrp : (B : ℝ) ^ ((1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hB_pos _).ne'
          field_simp
      _ ≤ (1 / 200 : ℝ) * C_P := by
          rw [div_le_iff₀ hB_pos]
          have := (div_lt_iff₀ hCP_pos).mp hB_gt2
          linarith only [this]
  have hsum_pos : ((1 / 100 : ℝ) * C_P) * (X : ℝ) * logR ^ 8 ≤
      ∑ n ∈ Finset.Ioc X (2 * X), selbergW R n * Score B n := by
    have hm := hmain B hB6000
    have hcoeff : (1 / 100 : ℝ) * C_P ≤
        (1 / 50 : ℝ) * C_P - E1 / logR - E2 * (logR + 1) ^ 32 / (B : ℝ) ^ 16 := by
      linarith only [hE1_small, hE2_small]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg X))
      (pow_nonneg hlogR_pos.le 8)).trans hm
  let U := (Finset.Ioc X (2 * X)).filter (fun n => 0 < Score B n)
  refine ⟨U, ?_, ?_⟩
  · have hH_le : Hsum R ≤ (C_P + M0 + 1) * (logR + 1) ^ 8 := by
      have hb := (abs_le.mp (hH R hR2)).2
      have h8 : logR ^ 8 ≤ (logR + 1) ^ 8 := pow_le_pow_left₀ hlogR_pos.le (by linarith) 8
      have h7 : (logR + 1) ^ 7 ≤ (logR + 1) ^ 8 :=
        pow_le_pow_right₀ (by linarith only [hlogR_pos]) (by norm_num)
      nlinarith only [hb, h8, h7, hCP_pos, hM0_pos, pow_nonneg (by linarith only [hlogR_pos] : 0 ≤ logR + 1) 8]
    have hupper_U : ∑ n ∈ Finset.Ioc X (2 * X), selbergW R n * Score B n ≤
        (U.card : ℝ) * (36 * ((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 * (logR + 1) ^ 32) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc X (2 * X)) (fun n => 0 < Score B n)]
      have hneg : ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ¬ 0 < Score B n),
          selbergW R n * Score B n ≤ 0 := by
        apply Finset.sum_nonpos; intro n hn
        exact mul_nonpos_of_nonneg_of_nonpos (selbergW_nonneg R n) (not_lt.mp (Finset.mem_filter.mp hn).2)
      have hpos_U : ∑ n ∈ U, selbergW R n * Score B n ≤
          (U.card : ℝ) * (36 * ((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 * (logR + 1) ^ 32) := by
        calc ∑ n ∈ U, selbergW R n * Score B n
            ≤ ∑ _n ∈ U, (36 * ((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 * (logR + 1) ^ 32) := by
              apply Finset.sum_le_sum; intro n hn
              have hsc : 0 < Score B n := (Finset.mem_filter.mp hn).2
              have hmemU := mem_U_of_score_pos (by omega : 5040 ≤ B) hsc
              have hFcard : (F n).primeFactors.card ≤ 35 := by
                have hrough : ∀ p ∈ (F n).primeFactors, B < p := by
                  intro p hp
                  rw [Nat.mem_primeFactors] at hp
                  obtain ⟨q, hq, hqd⟩ := (prime_dvd_F_iff hp.1).mp hp.2.1
                  exact hmemU.1 q hq p (Nat.mem_primeFactors.mpr ⟨hp.1, hqd, Nat.succ_ne_zero _⟩)
                rw [← sum_primeFactors_card_eq_F (by omega : 5040 ≤ B) hrough]
                exact hmemU.2
              have hw := selbergW_le_of_primeFactors_le_35 hR2 hFcard
              have hw2 : ((2 : ℝ) ^ 35 * (Hsum R) ^ 2) ^ 2 ≤
                  ((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 * (logR + 1) ^ 32 := by
                have hH2 : (Hsum R) ^ 2 ≤ (C_P + M0 + 1) ^ 2 * (logR + 1) ^ 16 := by
                  calc (Hsum R) ^ 2 ≤ ((C_P + M0 + 1) * (logR + 1) ^ 8) ^ 2 :=
                        pow_le_pow_left₀ (Hsum_nonneg R) hH_le 2
                    _ = (C_P + M0 + 1) ^ 2 * (logR + 1) ^ 16 := by rw [mul_pow, ← pow_mul]
                calc ((2 : ℝ) ^ 35 * (Hsum R) ^ 2) ^ 2
                    ≤ ((2 : ℝ) ^ 35 * ((C_P + M0 + 1) ^ 2 * (logR + 1) ^ 16)) ^ 2 :=
                      pow_le_pow_left₀ (by positivity)
                        (mul_le_mul_of_nonneg_left hH2 (by positivity)) 2
                  _ = ((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 * (logR + 1) ^ 32 := by
                      rw [← mul_assoc, mul_pow, ← pow_mul]
              calc selbergW R n * Score B n ≤ selbergW R n * 36 :=
                    mul_le_mul_of_nonneg_left (score_le_36 B n) (selbergW_nonneg R n)
                _ ≤ (((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 * (logR + 1) ^ 32) * 36 :=
                    mul_le_mul_of_nonneg_right (hw.trans hw2) (by norm_num)
                _ = 36 * ((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 * (logR + 1) ^ 32 := by
                    generalize (logR + 1) ^ 32 = L32
                    generalize ((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 = M2; ring
          _ = (U.card : ℝ) * (36 * ((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 * (logR + 1) ^ 32) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      linarith only [hneg, hpos_U]
    have hlogR_ge1 : 1 ≤ logR := by
      have h3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      have hB3 : (3 : ℝ) ≤ B := by exact_mod_cast (show 3 ≤ B by omega)
      have h1 : 1 ≤ Real.log (B : ℝ) := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
      linarith only [h1, hlogR_eq]
    have hlog8_ge1 : (1 : ℝ) ≤ logR ^ 8 := one_le_pow₀ hlogR_ge1
    have hU_mul : ((1 / 100 : ℝ) * C_P) * (X : ℝ) ≤ (U.card : ℝ) * (K_U * (B : ℝ) ^ ((1 : ℝ) / 2)) := by
      have h1 : ((1 / 100 : ℝ) * C_P) * (X : ℝ) ≤ ((1 / 100 : ℝ) * C_P) * (X : ℝ) * logR ^ 8 :=
        le_mul_of_one_le_right (by positivity) hlog8_ge1
      have h2 := h1.trans (hsum_pos.trans hupper_U)
      have h3 := hCL B hB2_nat
      have h4 : 36 * ((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 * (logR + 1) ^ 32 ≤
          K_U * (B : ℝ) ^ ((1 : ℝ) / 2) := by
        dsimp only [K_U]
        calc 36 * ((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 * (logR + 1) ^ 32
            ≤ 36 * ((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 * (C_L * (B : ℝ) ^ ((1 : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = _ := by generalize ((2 : ℝ) ^ 35 * (C_P + M0 + 1) ^ 2) ^ 2 = M2; ring
      exact h2.trans (mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _))
    have hB_half : 2000 * K_U / ((1 / 100 : ℝ) * C_P) ≤ (B : ℝ) ^ ((1 : ℝ) / 2) := by
      have hKU_nn : 0 ≤ K_U := by dsimp only [K_U]; positivity
      calc 2000 * K_U / ((1 / 100 : ℝ) * C_P)
          = ((2000 * K_U / ((1 / 100 : ℝ) * C_P)) ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ (B : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) hB_gt3.le (by norm_num)
    have hB_half_mul : 2000 * (K_U * (B : ℝ) ^ ((1 : ℝ) / 2)) ≤ ((1 / 100 : ℝ) * C_P) * (B : ℝ) := by
      have h1 : 2000 * K_U ≤ ((1 / 100 : ℝ) * C_P) * (B : ℝ) ^ ((1 : ℝ) / 2) := by
        have h1' := (div_le_iff₀ (by positivity : (0 : ℝ) < (1 / 100 : ℝ) * C_P)).mp hB_half
        linarith only [h1']
      have hsq : (B : ℝ) ^ ((1 : ℝ) / 2) * (B : ℝ) ^ ((1 : ℝ) / 2) = (B : ℝ) := by
        rw [← Real.rpow_add hB_pos]; norm_num
      calc 2000 * (K_U * (B : ℝ) ^ ((1 : ℝ) / 2))
          = (2000 * K_U) * (B : ℝ) ^ ((1 : ℝ) / 2) := by ring
        _ ≤ (((1 / 100 : ℝ) * C_P) * (B : ℝ) ^ ((1 : ℝ) / 2)) * (B : ℝ) ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hB_pos.le _)
        _ = ((1 / 100 : ℝ) * C_P) * ((B : ℝ) ^ ((1 : ℝ) / 2) * (B : ℝ) ^ ((1 : ℝ) / 2)) := by ring
        _ = ((1 / 100 : ℝ) * C_P) * (B : ℝ) := by rw [hsq]
    have hU_real : (2000 * (B : ℝ) ^ 399) * (K_U * (B : ℝ) ^ ((1 : ℝ) / 2)) ≤
        (U.card : ℝ) * (K_U * (B : ℝ) ^ ((1 : ℝ) / 2)) := by
      calc (2000 * (B : ℝ) ^ 399) * (K_U * (B : ℝ) ^ ((1 : ℝ) / 2))
          = (B : ℝ) ^ 399 * (2000 * (K_U * (B : ℝ) ^ ((1 : ℝ) / 2))) := by
            generalize (B : ℝ) ^ 399 = B399; ring
        _ ≤ (B : ℝ) ^ 399 * (((1 / 100 : ℝ) * C_P) * (B : ℝ)) :=
            mul_le_mul_of_nonneg_left hB_half_mul (pow_nonneg hB_pos.le 399)
        _ = ((1 / 100 : ℝ) * C_P) * (X : ℝ) := by
            dsimp only [X]; rw [Nat.cast_pow, ← mul_assoc, mul_comm ((B : ℝ) ^ 399), mul_assoc, ← pow_succ]
        _ ≤ (U.card : ℝ) * (K_U * (B : ℝ) ^ ((1 : ℝ) / 2)) := hU_mul
    have hKU_pos : 0 < K_U * (B : ℝ) ^ ((1 : ℝ) / 2) := by dsimp only [K_U]; positivity
    have hU_ge : (2000 * (B : ℝ) ^ 399) ≤ (U.card : ℝ) := le_of_mul_le_mul_right hU_real hKU_pos
    have hU_cast : ((2000 * B ^ 399 : ℕ) : ℝ) ≤ (U.card : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      exact hU_ge
    exact Nat.cast_le.mp hU_cast
  · intro n hn
    obtain ⟨hnI, hsc⟩ := Finset.mem_filter.mp hn
    obtain ⟨hgt, hle⟩ := Finset.mem_Ioc.mp hnI
    obtain ⟨hrough, hsum35⟩ := mem_U_of_score_pos (by omega : 5040 ≤ B) hsc
    exact ⟨hgt, hle, hrough, hsum35⟩

end

end Erdos946Spiro

theorem OMA.solution : OMA.R_Erdos946_erdos_946_variants_spiro_5040_R1.H1 :=
  Erdos946Spiro.spiro_H1_proof
