import OMAReductions.R_Erdos912_erdos_912_R2
import Mathlib

/-!
# Erdős Problem 912 Hypothesis 1

This file proves `OMA.R_Erdos912_erdos_912_R2.H1` by Selberg upper-bound sieve on shifted
primes and Cauchy-Schwarz on the multiplicity of `n / p`.
-/

-- Step Erdos912.erdos_912.R2.H1: hypothesis H1 of reduction Erdos912.erdos_912.R2
-- Credit: @nnkostov
-- H1 := ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ...

namespace OMA.Erdos912R2H1

open Finset Filter Asymptotics
open scoped BigOperators Topology

private lemma sum_le_sum_of_injOn {α β : Type*} [DecidableEq β]
    {s : Finset α} {t : Finset β} (e : α → β) {f : α → ℝ} {g : β → ℝ}
    (hmaps : ∀ a ∈ s, e a ∈ t)
    (hinj : Set.InjOn e (s : Set α))
    (hle : ∀ a ∈ s, f a ≤ g (e a))
    (hnn : ∀ b ∈ t, 0 ≤ g b) :
    ∑ a ∈ s, f a ≤ ∑ b ∈ t, g b := by
  calc ∑ a ∈ s, f a ≤ ∑ a ∈ s, g (e a) := Finset.sum_le_sum hle
    _ = ∑ b ∈ s.image e, g b := (Finset.sum_image (fun a ha b hb h => hinj ha hb h)).symm
    _ ≤ ∑ b ∈ t, g b := Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
        (fun b hb _ => hnn b hb)

private lemma squarefree_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact squarefree_one
  | @insert p s hps ih =>
    rw [Finset.prod_insert hps]
    have hp := hS p (Finset.mem_insert_self p s)
    have ih' := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
    have hcop : p.Coprime (∏ q ∈ s, q) := Nat.Coprime.prod_right fun q hq =>
      hp.coprime_iff_not_dvd.mpr fun h =>
        hps (((hS q (Finset.mem_insert_of_mem hq)).eq_one_or_self_of_dvd p h).resolve_left
          hp.ne_one ▸ hq)
    rw [Nat.squarefree_mul hcop]
    exact ⟨hp.squarefree, ih'⟩

/- ### Section 1: Multiplicative Sieve Functions and Counting Mod q -/

private def omegaD (d p : ℕ) : ℕ := if p ∣ d then 1 else 2

private def gD (d q : ℕ) : ℕ := ∏ p ∈ q.primeFactors, omegaD d p

private noncomputable def rhoD (d q : ℕ) : ℝ := (gD d q : ℝ) / (q : ℝ)

private noncomputable def hD (d k : ℕ) : ℝ :=
  ∏ p ∈ k.primeFactors, (((p : ℝ) - (omegaD d p : ℝ)) / (omegaD d p : ℝ))

private noncomputable def weightW (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))

private lemma omegaD_pos (d p : ℕ) : 0 < omegaD d p := by
  unfold omegaD; split_ifs <;> norm_num

private lemma omegaD_le_two (d p : ℕ) : omegaD d p ≤ 2 := by
  unfold omegaD; split_ifs <;> norm_num

private lemma sqfree_prod_primeFactors {q : ℕ} (hq : Squarefree q) :
    ∏ p ∈ q.primeFactors, p = q := by
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hq.ne_zero]
  rw [Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.factorization_eq_one_of_squarefree hq
    (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp), pow_one]

private lemma squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  rw [Nat.squarefree_iff_factorization_le_one (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)]
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero, Finsupp.sup_apply]
  exact sup_le ((Nat.squarefree_iff_factorization_le_one ha.ne_zero).mp ha p)
    ((Nat.squarefree_iff_factorization_le_one hb.ne_zero).mp hb p)

private lemma coprime_squarefree_mul {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hab : a.Coprime b) : Squarefree (a * b) := by
  rw [Nat.squarefree_iff_factorization_le_one (mul_ne_zero ha.ne_zero hb.ne_zero)]
  intro p
  rw [Nat.factorization_mul ha.ne_zero hb.ne_zero, Finsupp.coe_add, Pi.add_apply]
  by_cases hp : p.Prime
  · by_cases hpa : p ∣ a
    · have hpb : ¬ p ∣ b := fun h => hp.not_dvd_one (hab.gcd_eq_one ▸ Nat.dvd_gcd hpa h)
      rw [Nat.factorization_eq_zero_of_not_dvd hpb, add_zero]
      exact (Nat.squarefree_iff_factorization_le_one ha.ne_zero).mp ha p
    · rw [Nat.factorization_eq_zero_of_not_dvd hpa, zero_add]
      exact (Nat.squarefree_iff_factorization_le_one hb.ne_zero).mp hb p
  · rw [Nat.factorization_eq_zero_of_not_prime a hp, Nat.factorization_eq_zero_of_not_prime b hp]
    norm_num

private lemma primeFactors_lcm_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_union, ne_eq, Nat.lcm_ne_zero ha hb, not_false_eq_true,
    and_true]
  refine ⟨fun ⟨hp, hpd⟩ => ?_, ?_⟩
  · have hmul : p ∣ a * b := hpd.trans (Nat.lcm_dvd_mul a b)
    rcases hp.dvd_mul.mp hmul with h | h
    · exact Or.inl ⟨hp, h, ha⟩
    · exact Or.inr ⟨hp, h, hb⟩
  · rintro (⟨hp, hpa, -⟩ | ⟨hp, hpb, -⟩)
    · exact ⟨hp, hpa.trans (Nat.dvd_lcm_left a b)⟩
    · exact ⟨hp, hpb.trans (Nat.dvd_lcm_right a b)⟩

private lemma primeFactors_gcd_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.gcd a b).primeFactors = a.primeFactors ∩ b.primeFactors := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_inter, ne_eq, Nat.gcd_ne_zero_left ha,
    not_false_eq_true, and_true, Nat.dvd_gcd_iff]
  tauto

private lemma gD_one (d : ℕ) : gD d 1 = 1 := by
  simp [gD]

private lemma gD_prime {d p : ℕ} (hp : p.Prime) : gD d p = omegaD d p := by
  simp [gD, hp.primeFactors]

private lemma gD_pos (d q : ℕ) : 0 < gD d q := by
  unfold gD
  exact Finset.prod_pos fun p _ => omegaD_pos d p

private lemma gD_mul_coprime {d a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    gD d (a * b) = gD d a * gD d b := by
  unfold gD
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hab.disjoint_primeFactors]

private lemma gD_lcm_mul_gcd {d a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    gD d (Nat.lcm a b) * gD d (Nat.gcd a b) = gD d a * gD d b := by
  unfold gD
  rw [primeFactors_lcm_eq ha hb, primeFactors_gcd_eq ha hb]
  exact Finset.prod_union_inter

private lemma gD_le_card_divisors {d q : ℕ} (hq : Squarefree q) :
    gD d q ≤ q.divisors.card := by
  have h1 : gD d q ≤ ∏ _p ∈ q.primeFactors, 2 :=
    Finset.prod_le_prod' fun p _ => omegaD_le_two d p
  rw [Finset.prod_const, ← Finset.card_powerset] at h1
  refine h1.trans ?_
  refine Finset.card_le_card_of_injOn (fun s => ∏ p ∈ s, p) ?_ ?_
  · intro s hs
    have hs' : s ⊆ q.primeFactors := Finset.mem_powerset.mp hs
    refine Nat.mem_divisors.mpr ⟨?_, hq.ne_zero⟩
    calc ∏ p ∈ s, p ∣ ∏ p ∈ q.primeFactors, p :=
          Finset.prod_dvd_prod_of_subset s q.primeFactors id hs'
      _ = q := sqfree_prod_primeFactors hq
  · intro s₁ hs₁ s₂ hs₂ heq
    have heq' : ∏ p ∈ s₁, p = ∏ p ∈ s₂, p := heq
    have h1s := Finset.mem_powerset.mp hs₁
    have h2s := Finset.mem_powerset.mp hs₂
    ext p
    constructor
    · intro hp
      have hp_prime := Nat.prime_of_mem_primeFactors (h1s hp)
      have hdvd : p ∣ ∏ x ∈ s₂, x := by
        rw [← heq']
        exact Finset.dvd_prod_of_mem id hp
      obtain ⟨x, hx, hpx⟩ := (hp_prime.prime.dvd_finsetProd_iff id).mp hdvd
      have hx_prime := Nat.prime_of_mem_primeFactors (h2s hx)
      rcases hx_prime.eq_one_or_self_of_dvd p hpx with h | h
      · exact absurd h hp_prime.ne_one
      · rwa [h]
    · intro hp
      have hp_prime := Nat.prime_of_mem_primeFactors (h2s hp)
      have hdvd : p ∣ ∏ x ∈ s₁, x := by
        rw [heq']
        exact Finset.dvd_prod_of_mem id hp
      obtain ⟨x, hx, hpx⟩ := (hp_prime.prime.dvd_finsetProd_iff id).mp hdvd
      have hx_prime := Nat.prime_of_mem_primeFactors (h1s hx)
      rcases hx_prime.eq_one_or_self_of_dvd p hpx with h | h
      · exact absurd h hp_prime.ne_one
      · rwa [h]

private lemma rhoD_pos {d q : ℕ} (hq : 0 < q) : 0 < rhoD d q := by
  unfold rhoD
  exact div_pos (by exact_mod_cast gD_pos d q) (by exact_mod_cast hq)

private lemma rhoD_one (d : ℕ) : rhoD d 1 = 1 := by
  simp [rhoD, gD_one]

private lemma rhoD_prime {d p : ℕ} (hp : p.Prime) :
    rhoD d p = (omegaD d p : ℝ) / (p : ℝ) := by
  simp [rhoD, gD_prime hp]

private lemma rhoD_lcm_eq {d a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    rhoD d (Nat.lcm a b) = rhoD d a * rhoD d b / rhoD d (Nat.gcd a b) := by
  unfold rhoD
  have hgcd_pos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hlcm_pos : 0 < Nat.lcm a b := Nat.lcm_pos ha hb
  have hgl : (Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ) = (a : ℝ) * (b : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  have hgd : (gD d (Nat.lcm a b) : ℝ) * (gD d (Nat.gcd a b) : ℝ) =
      (gD d a : ℝ) * (gD d b : ℝ) := by
    exact_mod_cast gD_lcm_mul_gcd ha.ne' hb.ne'
  have hg_ne : (gD d (Nat.gcd a b) : ℝ) ≠ 0 := by exact_mod_cast (gD_pos d _).ne'
  have ha_ne : (a : ℝ) ≠ 0 := by positivity
  have hb_ne : (b : ℝ) ≠ 0 := by positivity
  have hgcd_ne : (Nat.gcd a b : ℝ) ≠ 0 := by positivity
  have hlcm_ne : (Nat.lcm a b : ℝ) ≠ 0 := by positivity
  field_simp
  calc (gD d (Nat.lcm a b) : ℝ) * (a : ℝ) * (b : ℝ) * (gD d (Nat.gcd a b) : ℝ)
      = ((gD d (Nat.lcm a b) : ℝ) * (gD d (Nat.gcd a b) : ℝ)) * ((a : ℝ) * (b : ℝ)) := by ring
    _ = ((gD d a : ℝ) * (gD d b : ℝ)) * ((Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ)) := by
        rw [hgd, hgl]
    _ = (Nat.lcm a b : ℝ) * (gD d a : ℝ) * (gD d b : ℝ) * (Nat.gcd a b : ℝ) := by ring

private lemma hD_factor_pos {d p : ℕ} (hd : 2 ∣ d) (hp : p.Prime) :
    0 < (((p : ℝ) - (omegaD d p : ℝ)) / (omegaD d p : ℝ)) := by
  have hω_pos : (0 : ℝ) < omegaD d p := by exact_mod_cast omegaD_pos d p
  refine div_pos ?_ hω_pos
  rcases eq_or_ne p 2 with rfl | hp2
  · have h2 : omegaD d 2 = 1 := by simp [omegaD, hd]
    rw [h2]; norm_num
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hω2 : omegaD d p ≤ 2 := omegaD_le_two d p
    have : (omegaD d p : ℝ) ≤ 2 := by exact_mod_cast hω2
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    linarith

private lemma hD_pos {d k : ℕ} (hd : 2 ∣ d) : 0 < hD d k := by
  unfold hD
  exact Finset.prod_pos fun p hp => hD_factor_pos hd (Nat.prime_of_mem_primeFactors hp)

private lemma hD_one (d : ℕ) : hD d 1 = 1 := by
  simp [hD]

private lemma hD_prime {d p : ℕ} (hp : p.Prime) :
    hD d p = ((p : ℝ) - (omegaD d p : ℝ)) / (omegaD d p : ℝ) := by
  simp [hD, hp.primeFactors]

private lemma hD_mul_coprime {d a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    hD d (a * b) = hD d a * hD d b := by
  unfold hD
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hab.disjoint_primeFactors]

private lemma sum_hD_divisors {d q : ℕ} (_hd : 2 ∣ d) (hq : Squarefree q) :
    ∑ k ∈ q.divisors, hD d k = (rhoD d q)⁻¹ := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases eq_or_ne q 1 with rfl | hq1
    · simp [hD_one, rhoD_one]
    · have hpf : q.primeFactors.Nonempty := by
        rw [Nat.nonempty_primeFactors]
        have := hq.ne_zero
        omega
      obtain ⟨p, hp⟩ := hpf
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
      let q' := q / p
      have hqq' : q = p * q' := (Nat.mul_div_cancel' hp_dvd).symm
      have hq'_pos : 0 < q' := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq.ne_zero) hp_dvd)
        hp_prime.pos
      have hq'_lt : q' < q := Nat.div_lt_self (Nat.pos_of_ne_zero hq.ne_zero) hp_prime.one_lt
      have hq'_sq : Squarefree q' := hq.squarefree_of_dvd (by rw [hqq']; exact dvd_mul_left q' p)
      have hp_cop : p.Coprime q' := by
        refine hp_prime.coprime_iff_not_dvd.mpr fun h => ?_
        have hpp : p * p ∣ q := by
          rw [hqq']
          exact mul_dvd_mul_left p h
        exact (Nat.squarefree_iff_prime_squarefree.mp hq p hp_prime) hpp
      have hdiv_eq : q.divisors = q'.divisors ∪ q'.divisors.image (p * ·) := by
        ext x
        simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
        constructor
        · rintro ⟨hxq, hq0⟩
          by_cases hpx : p ∣ x
          · right
            refine ⟨x / p, ⟨?_, hq'_pos.ne'⟩, Nat.mul_div_cancel' hpx⟩
            rw [hqq'] at hxq
            have : p * (x / p) ∣ p * q' := by rwa [Nat.mul_div_cancel' hpx]
            exact (Nat.mul_dvd_mul_iff_left hp_prime.pos).mp this
          · left
            refine ⟨?_, hq'_pos.ne'⟩
            have hcop_x : x.Coprime p := (hp_prime.coprime_iff_not_dvd.mpr hpx).symm
            rw [hqq'] at hxq
            exact hcop_x.dvd_of_dvd_mul_left hxq
        · rintro (⟨hxq', _⟩ | ⟨v, ⟨hvq', _⟩, rfl⟩)
          · exact ⟨hxq'.trans (by rw [hqq']; exact dvd_mul_left q' p), hq.ne_zero⟩
          · exact ⟨by rw [hqq']; exact mul_dvd_mul_left p hvq', hq.ne_zero⟩
      have hdisj : Disjoint q'.divisors (q'.divisors.image (p * ·)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx2
        have hpx : p ∣ q' := (dvd_mul_right p v).trans (Nat.dvd_of_mem_divisors hx1)
        exact (hp_prime.coprime_iff_not_dvd.mp hp_cop) hpx
      have hsum_split : ∑ k ∈ q.divisors, hD d k =
          (1 + hD d p) * ∑ k ∈ q'.divisors, hD d k := by
        rw [hdiv_eq, Finset.sum_union hdisj, Finset.sum_image]
        · have hmul_k : ∀ k ∈ q'.divisors, hD d (p * k) = hD d p * hD d k := fun k hk =>
            hD_mul_coprime hp_prime.ne_zero (Nat.pos_of_mem_divisors hk).ne'
              (hp_cop.coprime_dvd_right (Nat.dvd_of_mem_divisors hk))
          rw [Finset.sum_congr rfl hmul_k, ← Finset.mul_sum]
          ring
        · intro x _ y _ hxy
          exact mul_left_cancel₀ hp_prime.ne_zero hxy
      have h1hp : 1 + hD d p = (rhoD d p)⁻¹ := by
        rw [hD_prime hp_prime, rhoD_prime hp_prime]
        have hω : (omegaD d p : ℝ) ≠ 0 := by exact_mod_cast (omegaD_pos d p).ne'
        have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast hp_prime.ne_zero
        rw [inv_div]
        field_simp
        ring
      have hrho_mul : rhoD d q = rhoD d p * rhoD d q' := by
        unfold rhoD
        rw [hqq', gD_mul_coprime hp_prime.ne_zero hq'_pos.ne' hp_cop]
        push_cast
        ring
      rw [hsum_split, ih q' hq'_lt hq'_sq, h1hp, hrho_mul, mul_inv]

private def solCard (d q : ℕ) : ℕ :=
  ((Finset.range q).filter (fun x => q ∣ x * (x + d))).card

private lemma solCard_prime {d p : ℕ} (hp : p.Prime) : solCard d p = omegaD d p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  unfold solCard omegaD
  have hbij :
      ((Finset.range p).filter (fun x => p ∣ x * (x + d))).card =
        ((Finset.univ : Finset (ZMod p)).filter (fun x : ZMod p => x * (x + (d : ZMod p)) = 0)).card := by
    refine Finset.card_bij (fun x _ => (x : ZMod p)) ?_ ?_ ?_
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← Nat.cast_add, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      exact hx'
    · intro x₁ hx₁ x₂ hx₂ heq
      have h1 : x₁ < p := Finset.mem_range.mp (Finset.mem_filter.mp hx₁).1
      have h2 : x₂ < p := Finset.mem_range.mp (Finset.mem_filter.mp hx₂).1
      have hv := congrArg ZMod.val heq
      rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hv
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩,
        ZMod.natCast_zmod_val x⟩
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val x]
      exact hx'
  have hset : (Finset.univ : Finset (ZMod p)).filter (fun x : ZMod p => x * (x + (d : ZMod p)) = 0) =
      {(0 : ZMod p), -(d : ZMod p)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, mul_eq_zero]
    rw [add_eq_zero_iff_eq_neg]
  rw [hbij, hset]
  by_cases hd : p ∣ d
  · have h0 : -(d : ZMod p) = 0 := by
      rw [neg_eq_zero, ZMod.natCast_eq_zero_iff]
      exact hd
    rw [if_pos hd, h0, Finset.pair_eq_singleton, Finset.card_singleton]
  · have hne : (0 : ZMod p) ≠ -(d : ZMod p) := by
      intro h
      rw [eq_comm, neg_eq_zero, ZMod.natCast_eq_zero_iff] at h
      exact hd h
    rw [if_neg hd, Finset.card_pair hne]

private lemma solCard_mul_coprime {d a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    solCard d (a * b) = solCard d a * solCard d b := by
  have : NeZero a := ⟨ha.ne'⟩
  have : NeZero b := ⟨hb.ne'⟩
  have : NeZero (a * b) := ⟨mul_ne_zero ha.ne' hb.ne'⟩
  have hbridge : ∀ q : ℕ, 0 < q → ∀ [NeZero q],
      solCard d q =
        ((Finset.univ : Finset (ZMod q)).filter (fun x : ZMod q => x * (x + (d : ZMod q)) = 0)).card := by
    intro q hq _
    unfold solCard
    refine Finset.card_bij (fun x _ => (x : ZMod q)) ?_ ?_ ?_
    · intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← Nat.cast_add, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      exact (Finset.mem_filter.mp hx).2
    · intro x₁ hx₁ x₂ hx₂ heq
      have h1 : x₁ < q := Finset.mem_range.mp (Finset.mem_filter.mp hx₁).1
      have h2 : x₂ < q := Finset.mem_range.mp (Finset.mem_filter.mp hx₂).1
      have hv := congrArg ZMod.val heq
      rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hv
    · intro x hx
      refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩,
        ZMod.natCast_zmod_val x⟩
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val x]
      exact (Finset.mem_filter.mp hx).2
  rw [hbridge (a * b) (Nat.mul_pos ha hb), hbridge a ha, hbridge b hb]
  let e := ZMod.chineseRemainder hab
  rw [← Finset.card_product]
  refine Finset.card_bij (fun x _ => ((e x).1, (e x).2)) ?_ ?_ ?_
  · intro x hx
    have hx' : x * (x + (d : ZMod (a * b))) = 0 := (Finset.mem_filter.mp hx).2
    have h1 := congr_arg (fun z => (e z).1) hx'
    have h2 := congr_arg (fun z => (e z).2) hx'
    simp only [map_mul, map_add, map_natCast, map_zero, Prod.fst_mul, Prod.fst_add,
      Prod.snd_mul, Prod.snd_add] at h1 h2
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩
  · intro x₁ _ x₂ _ h
    exact e.injective (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  · rintro ⟨u, v⟩ huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    have hu' : u * (u + (d : ZMod a)) = 0 := (Finset.mem_filter.mp hu).2
    have hv' : v * (v + (d : ZMod b)) = 0 := (Finset.mem_filter.mp hv).2
    refine ⟨e.symm (u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    apply e.injective
    simp only [e.apply_symm_apply, map_mul, map_add, map_natCast, map_zero]
    exact Prod.ext hu' hv'

private lemma solCard_eq_gD {d q : ℕ} (hq : Squarefree q) : solCard d q = gD d q := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases eq_or_ne q 1 with rfl | hq1
    · simp [solCard, gD_one]
    · have hpf : q.primeFactors.Nonempty := by
        rw [Nat.nonempty_primeFactors]
        have := hq.ne_zero
        omega
      obtain ⟨p, hp⟩ := hpf
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
      let q' := q / p
      have hqq' : q = p * q' := (Nat.mul_div_cancel' hp_dvd).symm
      have hq'_pos : 0 < q' := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq.ne_zero) hp_dvd)
        hp_prime.pos
      have hq'_lt : q' < q := Nat.div_lt_self (Nat.pos_of_ne_zero hq.ne_zero) hp_prime.one_lt
      have hq'_sq : Squarefree q' := hq.squarefree_of_dvd (by rw [hqq']; exact dvd_mul_left q' p)
      have hp_cop : p.Coprime q' := by
        refine hp_prime.coprime_iff_not_dvd.mpr fun h => ?_
        have hpp : p * p ∣ q := by
          rw [hqq']; exact mul_dvd_mul_left p h
        exact (Nat.squarefree_iff_prime_squarefree.mp hq p hp_prime) hpp
      rw [hqq', solCard_mul_coprime hp_prime.pos hq'_pos hp_cop, solCard_prime hp_prime,
        ih q' hq'_lt hq'_sq, gD_mul_coprime hp_prime.ne_zero hq'_pos.ne' hp_cop, gD_prime hp_prime]

private lemma card_mod_solutions {d q : ℕ} (hq : Squarefree q) :
    ((Finset.range q).filter (fun x => q ∣ x * (x + d))).card = gD d q := by
  change solCard d q = gD d q
  exact solCard_eq_gD hq

private lemma card_Icc_shift_eq_range {d q a : ℕ} (hq : 0 < q) :
    ((Finset.Icc (a * q + 1) (a * q + q)).filter (fun m => q ∣ m * (m + d))).card =
      ((Finset.range q).filter (fun x => q ∣ x * (x + d))).card := by
  refine Finset.card_bij (fun m _ => m % q) ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt m hq, ?_⟩
    have hcongr : m ≡ m % q [MOD q] := (Nat.mod_modEq m q).symm
    have hmul := hcongr.mul (hcongr.add_right d)
    exact Nat.modEq_zero_iff_dvd.mp (hmul.symm.trans (Nat.modEq_zero_iff_dvd.mpr hm.2))
  · intro m₁ hm₁ m₂ hm₂ hmod
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm₁ hm₂
    have hm1_mod : m₁ % q = (m₁ - a * q) % q := by
      have h1 : m₁ = (m₁ - a * q) + a * q := by omega
      conv_lhs => rw [h1, Nat.add_mul_mod_self_right]
    have hm2_mod : m₂ % q = (m₂ - a * q) % q := by
      have h2 : m₂ = (m₂ - a * q) + a * q := by omega
      conv_lhs => rw [h2, Nat.add_mul_mod_self_right]
    have hmod' : (m₁ - a * q) % q = (m₂ - a * q) % q := by rw [← hm1_mod, ← hm2_mod, hmod]
    have hsub_eq : m₁ - a * q = m₂ - a * q := by
      have h1_le : m₁ - a * q ≤ q := by omega
      have h2_le : m₂ - a * q ≤ q := by omega
      have h1_pos : 0 < m₁ - a * q := by omega
      have h2_pos : 0 < m₂ - a * q := by omega
      rcases h1_le.eq_or_lt with h1q | h1q <;> rcases h2_le.eq_or_lt with h2q | h2q
      · omega
      · rw [h1q, Nat.mod_self, Nat.mod_eq_of_lt h2q] at hmod'; omega
      · rw [h2q, Nat.mod_self, Nat.mod_eq_of_lt h1q] at hmod'; omega
      · rw [Nat.mod_eq_of_lt h1q, Nat.mod_eq_of_lt h2q] at hmod'; exact hmod'
    omega
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_range] at hy
    by_cases hy0 : y = 0
    · refine ⟨a * q + q, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩, ?_⟩
      · have h1 : q ∣ a * q + q := ⟨a + 1, by ring⟩
        exact dvd_mul_of_dvd_left h1 _
      · rw [hy0, show a * q + q = (a + 1) * q by ring, Nat.mul_mod_left]
    · refine ⟨a * q + y, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩, ?_⟩
      · have hcongr : a * q + y ≡ y [MOD q] := by
          rw [Nat.ModEq, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
        have hmul := hcongr.mul (hcongr.add_right d)
        exact Nat.modEq_zero_iff_dvd.mp (hmul.trans (Nat.modEq_zero_iff_dvd.mpr hy.2))
      · rw [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hy.1]

private lemma card_Icc_solutions_err {d q N : ℕ} (hq : Squarefree q) :
    |(((Finset.Icc 1 N).filter (fun m => q ∣ m * (m + d))).card : ℝ) - (N : ℝ) * rhoD d q| ≤
      (gD d q : ℝ) := by
  have hq_pos : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  set k := N / q
  set r := N % q
  have hN_eq : N = k * q + r := by rw [mul_comm]; exact (Nat.div_add_mod N q).symm
  have hr_lt : r < q := Nat.mod_lt N hq_pos
  have hpart : Finset.Icc 1 N =
      ((Finset.range k).biUnion (fun a => Finset.Icc (a * q + 1) (a * q + q))) ∪
        Finset.Icc (k * q + 1) (k * q + r) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨hm1, hmN⟩
      by_cases hmk : m ≤ k * q
      · left
        refine ⟨(m - 1) / q, ?_, ?_, ?_⟩
        · have hm1_lt : m - 1 < k * q := by omega
          exact (Nat.div_lt_iff_lt_mul hq_pos).mpr hm1_lt
        · have hdm := Nat.div_mul_le_self (m - 1) q
          have hdm' : (m - 1) / q * q ≤ m - 1 := hdm
          omega
        · have hdm := Nat.div_add_mod (m - 1) q
          have hmod_lt : (m - 1) % q < q := Nat.mod_lt (m - 1) hq_pos
          have hdm' : q * ((m - 1) / q) = (m - 1) / q * q := Nat.mul_comm _ _
          omega
      · right; omega
    · rintro (⟨a, hak, hm1, hm2⟩ | ⟨hm1, hm2⟩)
      · refine ⟨by omega, ?_⟩
        have h1 : a + 1 ≤ k := hak
        have h2 : (a + 1) * q ≤ k * q := Nat.mul_le_mul_right q h1
        have h3 : (a + 1) * q = a * q + q := by ring
        omega
      · omega
  have hdisj_rem : Disjoint ((Finset.range k).biUnion (fun a => Finset.Icc (a * q + 1) (a * q + q)))
      (Finset.Icc (k * q + 1) (k * q + r)) := by
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_Icc] at hm1 hm2
    rcases hm1 with ⟨a, hak, _, hma⟩
    have h1 : (a + 1) * q ≤ k * q := Nat.mul_le_mul_right q hak
    have h2 : (a + 1) * q = a * q + q := by ring
    omega
  have hdisj_blocks : Set.PairwiseDisjoint (Finset.range k : Set ℕ)
      (fun a => Finset.Icc (a * q + 1) (a * q + q)) := by
    intro a₁ _ a₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro m hm1 hm2
    simp only [Finset.mem_Icc] at hm1 hm2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : (a₁ + 1) * q ≤ a₂ * q := Nat.mul_le_mul_right q hlt
      have h2 : (a₁ + 1) * q = a₁ * q + q := by ring
      omega
    · have h1 : (a₂ + 1) * q ≤ a₁ * q := Nat.mul_le_mul_right q hlt
      have h2 : (a₂ + 1) * q = a₂ * q + q := by ring
      omega
  have hcount_split : ((Finset.Icc 1 N).filter (fun m => q ∣ m * (m + d))).card =
      k * gD d q + ((Finset.Icc (k * q + 1) (k * q + r)).filter (fun m => q ∣ m * (m + d))).card := by
    rw [hpart, Finset.filter_union, Finset.card_union_of_disjoint
      (disjoint_of_subset_left (Finset.filter_subset _ _)
        (disjoint_of_subset_right (Finset.filter_subset _ _) hdisj_rem))]
    congr 1
    rw [Finset.filter_biUnion, Finset.card_biUnion]
    · have hblock : ∀ a ∈ Finset.range k,
          ((Finset.Icc (a * q + 1) (a * q + q)).filter (fun m => q ∣ m * (m + d))).card =
            gD d q := fun a _ => by
        rw [card_Icc_shift_eq_range hq_pos, card_mod_solutions hq]
      rw [Finset.sum_congr rfl hblock, Finset.sum_const, Finset.card_range, smul_eq_mul]
    · intro a₁ ha₁ a₂ ha₂ hne
      exact disjoint_of_subset_left (Finset.filter_subset _ _)
        (disjoint_of_subset_right (Finset.filter_subset _ _) (hdisj_blocks ha₁ ha₂ hne))
  have hrem_le : ((Finset.Icc (k * q + 1) (k * q + r)).filter (fun m => q ∣ m * (m + d))).card ≤
      gD d q := by
    rw [← card_mod_solutions hq]
    refine Finset.card_le_card_of_injOn (fun m => m % q) ?_ ?_
    · intro m hm
      have hm' := Finset.mem_filter.mp (Finset.mem_coe.mp hm)
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt m hq_pos), ?_⟩)
      have hcongr : m ≡ m % q [MOD q] := (Nat.mod_modEq m q).symm
      have hmul := hcongr.mul (hcongr.add_right d)
      exact Nat.modEq_zero_iff_dvd.mp (hmul.symm.trans (Nat.modEq_zero_iff_dvd.mpr hm'.2))
    · intro m₁ hm₁ m₂ hm₂ hmod
      have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hm₁)).1
      have h2 := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hm₂)).1
      dsimp only at hmod
      have hm1_mod : m₁ % q = m₁ - k * q := by
        have h1' : m₁ = (m₁ - k * q) + k * q := by omega
        conv_lhs => rw [h1', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hm2_mod : m₂ % q = m₂ - k * q := by
        have h2' : m₂ = (m₂ - k * q) + k * q := by omega
        conv_lhs => rw [h2', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [hm1_mod, hm2_mod] at hmod
      omega
  have hN_rho : (N : ℝ) * rhoD d q = (k : ℝ) * gD d q + (r : ℝ) / q * gD d q := by
    unfold rhoD
    rw [hN_eq]
    push_cast
    have hq_ne : (q : ℝ) ≠ 0 := by positivity
    field_simp
  have hrem_nn : (0 : ℝ) ≤ (((Finset.Icc (k * q + 1) (k * q + r)).filter
      (fun m => q ∣ m * (m + d))).card : ℝ) := Nat.cast_nonneg _
  have hrem_ub : (((Finset.Icc (k * q + 1) (k * q + r)).filter (fun m => q ∣ m * (m + d))).card : ℝ) ≤
      (gD d q : ℝ) := by exact_mod_cast hrem_le
  have hr_frac_nn : 0 ≤ (r : ℝ) / q * gD d q := by positivity
  have hr_frac_ub : (r : ℝ) / q * gD d q ≤ gD d q := by
    have : (r : ℝ) / q ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hr_lt.le)
    calc (r : ℝ) / q * gD d q ≤ 1 * gD d q := mul_le_mul_of_nonneg_right this (by positivity)
      _ = gD d q := one_mul _
  rw [hcount_split]
  push_cast
  rw [hN_rho, abs_le]
  constructor <;> linarith

/- ### Section 2: Selberg Upper-Bound Sieve -/

private def sqfreeUpTo (R : ℕ) : Finset ℕ := (Finset.Icc 1 R).filter Squarefree

private noncomputable def selbergS (d R : ℕ) : ℝ := ∑ k ∈ sqfreeUpTo R, (hD d k)⁻¹

private noncomputable def selbergLambda (d R r : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selbergS d R * rhoD d r) *
    ∑ k ∈ (sqfreeUpTo R).filter (fun k => r ∣ k), (hD d k)⁻¹

private lemma one_mem_sqfreeUpTo {R : ℕ} (hR : 1 ≤ R) : 1 ∈ sqfreeUpTo R := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hR⟩, squarefree_one⟩

private lemma selbergS_pos {d R : ℕ} (hd : 2 ∣ d) (hR : 1 ≤ R) : 0 < selbergS d R := by
  unfold selbergS
  refine Finset.sum_pos' (fun k _ => inv_nonneg.mpr (hD_pos hd).le) ?_
  exact ⟨1, one_mem_sqfreeUpTo hR, inv_pos.mpr (hD_pos hd)⟩

private lemma selbergLambda_one {d R : ℕ} (hd : 2 ∣ d) (hR : 1 ≤ R) : selbergLambda d R 1 = 1 := by
  unfold selbergLambda
  rw [ArithmeticFunction.moebius_apply_one, Int.cast_one, rhoD_one, mul_one]
  have hf : (sqfreeUpTo R).filter (fun k => 1 ∣ k) = sqfreeUpTo R := by
    ext k; simp
  rw [hf]
  change 1 / selbergS d R * selbergS d R = 1
  exact div_mul_cancel₀ 1 (selbergS_pos hd hR).ne'

private lemma sqfree_coprime_div {m k : ℕ} (hm : Squarefree m) (hkm : k ∣ m) :
    k.Coprime (m / k) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h
  have hk0 : k ≠ 0 := fun hk => by subst hk; simp at hkm; exact hm.ne_zero hkm
  have hpos : 0 < Nat.gcd k (m / k) := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hk0)
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd k (m / k) ≠ 1)
  have hpk : p ∣ k := hp_dvd.trans (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ m / k := hp_dvd.trans (Nat.gcd_dvd_right _ _)
  have hpp : p * p ∣ m := by
    rw [← Nat.mul_div_cancel' hkm]
    exact mul_dvd_mul hpk hpq
  exact Nat.squarefree_iff_prime_squarefree.mp hm p hp_prime hpp

private lemma moebius_sum_divisors_filter {m k : ℕ} (hm : Squarefree m) (hkm : k ∣ m) :
    ∑ r ∈ m.divisors.filter (fun r => k ∣ r), ((ArithmeticFunction.moebius r : ℤ) : ℝ) =
      if m = k then ((ArithmeticFunction.moebius k : ℤ) : ℝ) else 0 := by
  have hk_pos : 0 < k := by
    rcases eq_or_ne k 0 with rfl | hk0
    · simp at hkm; exact absurd hkm hm.ne_zero
    · exact Nat.pos_of_ne_zero hk0
  have hcop := sqfree_coprime_div hm hkm
  have hsum_z : ∑ r ∈ m.divisors.filter (fun r => k ∣ r), (ArithmeticFunction.moebius r : ℤ) =
      (ArithmeticFunction.moebius k : ℤ) *
        ∑ u ∈ (m / k).divisors, (ArithmeticFunction.moebius u : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij' (fun r _ => r / k) (fun u _ => k * u) ?_ ?_ ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_filter, Nat.mem_divisors] at hr
      have hdiv_pos : 0 < m / k := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm.ne_zero) hkm) hk_pos
      have hdvd_k : r / k ∣ m / k := by
        have hmul_dvd : k * (r / k) ∣ k * (m / k) := by
          rw [Nat.mul_div_cancel' hr.2, Nat.mul_div_cancel' hkm]
          exact hr.1.1
        exact (Nat.mul_dvd_mul_iff_left hk_pos).mp hmul_dvd
      exact Nat.mem_divisors.mpr ⟨hdvd_k, hdiv_pos.ne'⟩
    · intro u hu
      simp only [Nat.mem_divisors] at hu
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hm.ne_zero⟩, dvd_mul_right k u⟩
      rw [← Nat.mul_div_cancel' hkm]
      exact mul_dvd_mul_left k hu.1
    · intro r hr
      have hkr := (Finset.mem_filter.mp hr).2
      exact Nat.mul_div_cancel' hkr
    · intro u _
      exact Nat.mul_div_cancel_left u hk_pos
    · intro r hr
      have hrm := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hr).1
      have hkr := (Finset.mem_filter.mp hr).2
      have hdvd_k : r / k ∣ m / k := by
        have hmul_dvd : k * (r / k) ∣ k * (m / k) := by
          rw [Nat.mul_div_cancel' hkr, Nat.mul_div_cancel' hkm]
          exact hrm
        exact (Nat.mul_dvd_mul_iff_left hk_pos).mp hmul_dvd
      have hcop_u : k.Coprime (r / k) := hcop.coprime_dvd_right hdvd_k
      have hmk' : r = k * (r / k) := (Nat.mul_div_cancel' hkr).symm
      conv_lhs => rw [hmk']
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_u]
  have hzeta : ∑ u ∈ (m / k).divisors, (ArithmeticFunction.moebius u : ℤ) = if m = k then 1 else 0 := by
    have hmul : (ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) (m / k) =
        ∑ u ∈ (m / k).divisors, (ArithmeticFunction.moebius u : ℤ) := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
    rw [← hmul, ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
    have heq_one : m / k = 1 ↔ m = k := by
      constructor
      · intro h
        rw [← Nat.mul_div_cancel' hkm, h, mul_one]
      · rintro rfl
        exact Nat.div_self hk_pos
    simp [heq_one]
  have hcast : (∑ r ∈ m.divisors.filter (fun r => k ∣ r), ((ArithmeticFunction.moebius r : ℤ) : ℝ)) =
      ((∑ r ∈ m.divisors.filter (fun r => k ∣ r), (ArithmeticFunction.moebius r : ℤ) : ℤ) : ℝ) := by
    push_cast; rfl
  rw [hcast, hsum_z, hzeta]
  split_ifs with h <;> simp

private lemma selberg_z_eval {d R k : ℕ} (hd : 2 ∣ d) (hR : 1 ≤ R) (hk : k ∈ sqfreeUpTo R) :
    ∑ r ∈ (sqfreeUpTo R).filter (fun r => k ∣ r), selbergLambda d R r * rhoD d r =
      ((ArithmeticFunction.moebius k : ℤ) : ℝ) / (selbergS d R * hD d k) := by
  have hterm : ∀ r ∈ (sqfreeUpTo R).filter (fun r => k ∣ r),
      selbergLambda d R r * rhoD d r =
        ∑ m ∈ (sqfreeUpTo R).filter (fun m => r ∣ m),
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selbergS d R * hD d m) := by
    intro r hr
    have hr_sq := (Finset.mem_filter.mp hr).1
    have hr_pos : 0 < r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr_sq).1).1
    have hrho_ne : rhoD d r ≠ 0 := (rhoD_pos hr_pos).ne'
    have hsimp : selbergLambda d R r * rhoD d r =
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) / selbergS d R *
          ∑ k ∈ (sqfreeUpTo R).filter (fun k => r ∣ k), (hD d k)⁻¹ := by
      unfold selbergLambda
      have hS_ne : selbergS d R ≠ 0 := (selbergS_pos hd hR).ne'
      field_simp
    rw [hsimp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [Finset.sum_congr rfl hterm]
  have hswap :
      ∑ r ∈ (sqfreeUpTo R).filter (fun r => k ∣ r),
        ∑ m ∈ (sqfreeUpTo R).filter (fun m => r ∣ m),
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selbergS d R * hD d m) =
      ∑ m ∈ (sqfreeUpTo R).filter (fun m => k ∣ m),
        ∑ r ∈ m.divisors.filter (fun r => k ∣ r),
          ((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selbergS d R * hD d m) := by
    have h1 :
        ∑ r ∈ (sqfreeUpTo R).filter (fun r => k ∣ r),
          ∑ m ∈ (sqfreeUpTo R).filter (fun m => r ∣ m),
            ((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selbergS d R * hD d m) =
        ∑ r ∈ sqfreeUpTo R, ∑ m ∈ sqfreeUpTo R,
          if k ∣ r then if r ∣ m then
            ((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selbergS d R * hD d m) else 0 else 0 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs with hkr
      · rw [Finset.sum_filter]
      · simp
    rw [h1, Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    have hm_sq := (Finset.mem_filter.mp hm).2
    by_cases hkm : k ∣ m
    · rw [if_pos hkm]
      have hset :
          ∑ r ∈ sqfreeUpTo R,
            (if k ∣ r then if r ∣ m then
              ((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selbergS d R * hD d m) else 0 else 0) =
          ∑ r ∈ m.divisors.filter (fun r => k ∣ r),
            ((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selbergS d R * hD d m) := by
        have hpt : ∀ r ∈ sqfreeUpTo R,
            (if k ∣ r then if r ∣ m then
              ((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selbergS d R * hD d m) else 0 else 0) =
            (if k ∣ r ∧ r ∣ m then
              ((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selbergS d R * hD d m) else 0) :=
          fun r _ => by split_ifs <;> tauto
        rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter]
        refine Finset.sum_bij (fun r _ => r) ?_ (fun _ _ _ _ h => h) ?_ (fun _ _ => rfl)
        · intro r hr
          obtain ⟨_, hkr, hrm⟩ := Finset.mem_filter.mp hr
          exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hrm, hm_sq.ne_zero⟩, hkr⟩
        · intro r hr
          obtain ⟨hr_div, hkr⟩ := Finset.mem_filter.mp hr
          have hrd : r ∣ m := Nat.dvd_of_mem_divisors hr_div
          have hr_pos : 0 < r := Nat.pos_of_mem_divisors hr_div
          have hr_le : r ≤ R := (Nat.le_of_dvd hm_icc.1 hrd).trans hm_icc.2
          exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hr_pos, hr_le⟩, hm_sq.squarefree_of_dvd hrd⟩, hkr, hrd⟩, rfl⟩
      exact hset
    · rw [if_neg hkm]
      refine Finset.sum_eq_zero fun r _ => ?_
      split_ifs with hkr hrm
      · exact absurd (hkr.trans hrm) hkm
      · rfl
      · rfl
  rw [hswap]
  have hinner : ∀ m ∈ (sqfreeUpTo R).filter (fun m => k ∣ m),
      ∑ r ∈ m.divisors.filter (fun r => k ∣ r),
        ((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selbergS d R * hD d m) =
      if m = k then ((ArithmeticFunction.moebius k : ℤ) : ℝ) / (selbergS d R * hD d k) else 0 := by
    intro m hm
    obtain ⟨hm_sqf, hkm⟩ := Finset.mem_filter.mp hm
    have hm_sq := (Finset.mem_filter.mp hm_sqf).2
    rw [← Finset.sum_div, moebius_sum_divisors_filter hm_sq hkm]
    split_ifs with hmk
    · rw [hmk]
    · simp
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_filter.mpr ⟨hk, dvd_refl k⟩)]

private lemma selberg_quad_eq {d R : ℕ} (hd : 2 ∣ d) (hR : 1 ≤ R) :
    ∑ r₁ ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R,
      selbergLambda d R r₁ * selbergLambda d R r₂ * rhoD d (Nat.lcm r₁ r₂) = (selbergS d R)⁻¹ := by
  have hstep1 :
      ∑ r₁ ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R,
        selbergLambda d R r₁ * selbergLambda d R r₂ * rhoD d (Nat.lcm r₁ r₂) =
      ∑ r₁ ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R, ∑ k ∈ sqfreeUpTo R,
        (if k ∣ r₁ ∧ k ∣ r₂ then
          hD d k * (selbergLambda d R r₁ * rhoD d r₁) * (selbergLambda d R r₂ * rhoD d r₂)
        else 0) := by
    refine Finset.sum_congr rfl fun r₁ hr₁ => Finset.sum_congr rfl fun r₂ hr₂ => ?_
    have hr1_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr₁).1
    have hr1_sq := (Finset.mem_filter.mp hr₁).2
    have hr2_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr₂).1
    have hg_sq : Squarefree (Nat.gcd r₁ r₂) := hr1_sq.squarefree_of_dvd (Nat.gcd_dvd_left r₁ r₂)
    have hdiv_sum :
        (rhoD d (Nat.gcd r₁ r₂))⁻¹ = ∑ k ∈ sqfreeUpTo R, if k ∣ r₁ ∧ k ∣ r₂ then hD d k else 0 := by
      rw [← sum_hD_divisors hd hg_sq, ← Finset.sum_filter]
      refine Finset.sum_bij (fun k _ => k) ?_ (fun _ _ _ _ h => h) ?_ (fun _ _ => rfl)
      · intro k hk
        have hkd := Nat.dvd_of_mem_divisors hk
        have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
        have hkg : k ≤ Nat.gcd r₁ r₂ := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left r₂ hr1_icc.1) hkd
        have hkR : k ≤ R := hkg.trans ((Nat.gcd_le_left r₂ hr1_icc.1).trans hr1_icc.2)
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hk_pos, hkR⟩, hg_sq.squarefree_of_dvd hkd⟩,
          Nat.dvd_gcd_iff.mp hkd⟩
      · intro k hk
        obtain ⟨_, hkr₁, hkr₂⟩ := Finset.mem_filter.mp hk
        exact ⟨k, Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hkr₁ hkr₂, hg_sq.ne_zero⟩, rfl⟩
    rw [rhoD_lcm_eq hr1_icc.1 hr2_icc.1, div_eq_mul_inv, hdiv_sum]
    have hmul1 : selbergLambda d R r₁ * selbergLambda d R r₂ *
        (rhoD d r₁ * rhoD d r₂ * ∑ k ∈ sqfreeUpTo R, if k ∣ r₁ ∧ k ∣ r₂ then hD d k else 0) =
        ((selbergLambda d R r₁ * rhoD d r₁) * (selbergLambda d R r₂ * rhoD d r₂)) *
          ∑ k ∈ sqfreeUpTo R, if k ∣ r₁ ∧ k ∣ r₂ then hD d k else 0 := by ring
    rw [hmul1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [hstep1]
  have hswap1 :
      ∑ r₁ ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R, ∑ k ∈ sqfreeUpTo R,
        (if k ∣ r₁ ∧ k ∣ r₂ then
          hD d k * (selbergLambda d R r₁ * rhoD d r₁) * (selbergLambda d R r₂ * rhoD d r₂)
        else 0) =
      ∑ k ∈ sqfreeUpTo R, hD d k *
        (∑ r₁ ∈ (sqfreeUpTo R).filter (fun r => k ∣ r), selbergLambda d R r₁ * rhoD d r₁) *
        (∑ r₂ ∈ (sqfreeUpTo R).filter (fun r => k ∣ r), selbergLambda d R r₂ * rhoD d r₂) := by
    calc _ = ∑ r₁ ∈ sqfreeUpTo R, ∑ k ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R,
          (if k ∣ r₁ ∧ k ∣ r₂ then
            hD d k * (selbergLambda d R r₁ * rhoD d r₁) * (selbergLambda d R r₂ * rhoD d r₂)
          else 0) := by
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k ∈ sqfreeUpTo R, ∑ r₁ ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R,
          (if k ∣ r₁ ∧ k ∣ r₂ then
            hD d k * (selbergLambda d R r₁ * rhoD d r₁) * (selbergLambda d R r₂ * rhoD d r₂)
          else 0) := Finset.sum_comm
      _ = ∑ k ∈ sqfreeUpTo R, hD d k *
            (∑ r₁ ∈ (sqfreeUpTo R).filter (fun r => k ∣ r), selbergLambda d R r₁ * rhoD d r₁) *
            (∑ r₂ ∈ (sqfreeUpTo R).filter (fun r => k ∣ r), selbergLambda d R r₂ * rhoD d r₂) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          symm
          rw [Finset.sum_filter]
          rw [show hD d k * (∑ a ∈ sqfreeUpTo R, if k ∣ a then selbergLambda d R a * rhoD d a else 0) =
              ∑ a ∈ sqfreeUpTo R, hD d k * (if k ∣ a then selbergLambda d R a * rhoD d a else 0) by
            rw [Finset.mul_sum]]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun r₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r₂ _ => ?_
          by_cases hk1 : k ∣ r₁ <;> by_cases hk2 : k ∣ r₂ <;> simp [hk1, hk2]
  rw [hswap1]
  have hterm_k : ∀ k ∈ sqfreeUpTo R,
      hD d k * (∑ r₁ ∈ (sqfreeUpTo R).filter (fun r => k ∣ r), selbergLambda d R r₁ * rhoD d r₁) *
        (∑ r₂ ∈ (sqfreeUpTo R).filter (fun r => k ∣ r), selbergLambda d R r₂ * rhoD d r₂) =
      (hD d k)⁻¹ / (selbergS d R) ^ 2 := by
    intro k hk
    rw [selberg_z_eval hd hR hk]
    have hk_sq := (Finset.mem_filter.mp hk).2
    have hμ2 : ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hk_sq
    have hS_ne : selbergS d R ≠ 0 := (selbergS_pos hd hR).ne'
    have hh_ne : hD d k ≠ 0 := (hD_pos hd).ne'
    calc hD d k * (((ArithmeticFunction.moebius k : ℤ) : ℝ) / (selbergS d R * hD d k)) *
          (((ArithmeticFunction.moebius k : ℤ) : ℝ) / (selbergS d R * hD d k))
        = ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 * hD d k /
            ((selbergS d R) ^ 2 * (hD d k) ^ 2) := by ring
      _ = 1 * hD d k / ((selbergS d R) ^ 2 * (hD d k) ^ 2) := by rw [hμ2]
      _ = (hD d k)⁻¹ / (selbergS d R) ^ 2 := by field_simp
  rw [Finset.sum_congr rfl hterm_k, ← Finset.sum_div]
  change selbergS d R / (selbergS d R) ^ 2 = (selbergS d R)⁻¹
  have hS_ne : selbergS d R ≠ 0 := (selbergS_pos hd hR).ne'
  field_simp

private lemma inv_rho_mul_hD_eq_sum_inv {d r : ℕ} (hd : 2 ∣ d) (hr : Squarefree r) :
    (rhoD d r * hD d r)⁻¹ = ∑ v ∈ r.divisors, (hD d v)⁻¹ := by
  rw [mul_inv, ← sum_hD_divisors hd hr, Finset.sum_mul]
  refine Finset.sum_bij (fun u _ => r / u) ?_ ?_ ?_ ?_
  · intro u hu
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hu), hr.ne_zero⟩
  · intro u₁ hu₁ u₂ hu₂ heq
    have h1 := Nat.dvd_of_mem_divisors hu₁
    have h2 := Nat.dvd_of_mem_divisors hu₂
    have h1_pos := Nat.pos_of_mem_divisors hu₁
    have h2_pos := Nat.pos_of_mem_divisors hu₂
    have hm1 := Nat.mul_div_cancel' h1
    have hm2 := Nat.mul_div_cancel' h2
    rw [heq] at hm1
    have hdiv_pos : 0 < r / u₂ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hr.ne_zero) h2) h2_pos
    exact Nat.mul_right_cancel hdiv_pos (hm1.trans hm2.symm)
  · intro v hv
    refine ⟨r / v, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hv), hr.ne_zero⟩,
      ?_⟩
    exact Nat.div_div_self (Nat.dvd_of_mem_divisors hv) hr.ne_zero
  · intro u hu
    have hud := Nat.dvd_of_mem_divisors hu
    have hu_pos := Nat.pos_of_mem_divisors hu
    have hv_pos := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hr.ne_zero) hud) hu_pos
    have hcop := sqfree_coprime_div hr hud
    have hmul : hD d r = hD d u * hD d (r / u) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hud]
      exact hD_mul_coprime hu_pos.ne' hv_pos.ne' hcop
    rw [hmul]
    have h1 : hD d u ≠ 0 := (hD_pos hd).ne'
    have h2 : hD d (r / u) ≠ 0 := (hD_pos hd).ne'
    field_simp

private lemma abs_selbergLambda_le_one {d R r : ℕ} (hd : 2 ∣ d) (hR : 1 ≤ R)
    (hr : r ∈ sqfreeUpTo R) : |selbergLambda d R r| ≤ 1 := by
  have hr_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1
  have hr_sq := (Finset.mem_filter.mp hr).2
  have hS_pos : 0 < selbergS d R := selbergS_pos hd hR
  have hrho_pos : 0 < rhoD d r := rhoD_pos hr_icc.1
  have hh_pos : 0 < hD d r := hD_pos hd
  let T := (sqfreeUpTo (R / r)).filter (fun t => r.Coprime t)
  have hsplit_sum :
      ∑ k ∈ (sqfreeUpTo R).filter (fun k => r ∣ k), (hD d k)⁻¹ =
        (hD d r)⁻¹ * ∑ t ∈ T, (hD d t)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun k _ => k / r) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨hk_sqf, hrk⟩ := Finset.mem_filter.mp hk
      have hk_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hk_sqf).1
      have hk_sq := (Finset.mem_filter.mp hk_sqf).2
      have hcop := sqfree_coprime_div hk_sq hrk
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩, hcop⟩
      · exact Nat.div_pos (Nat.le_of_dvd hk_icc.1 hrk) hr_icc.1
      · exact Nat.div_le_div_right hk_icc.2
      · exact hk_sq.squarefree_of_dvd (Nat.div_dvd_of_dvd hrk)
    · intro k₁ hk₁ k₂ hk₂ heq
      have h1 := (Finset.mem_filter.mp hk₁).2
      have h2 := (Finset.mem_filter.mp hk₂).2
      rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
    · intro t ht
      obtain ⟨ht_sqf, hcop⟩ := Finset.mem_filter.mp ht
      have ht_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp ht_sqf).1
      have ht_sq := (Finset.mem_filter.mp ht_sqf).2
      refine ⟨r * t, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩,
        dvd_mul_right r t⟩, Nat.mul_div_cancel_left t hr_icc.1⟩
      · exact Nat.mul_pos hr_icc.1 ht_icc.1
      · calc r * t ≤ r * (R / r) := Nat.mul_le_mul_left r ht_icc.2
          _ ≤ R := Nat.mul_div_le R r
      · exact coprime_squarefree_mul hr_sq ht_sq hcop
    · intro k hk
      obtain ⟨hk_sqf, hrk⟩ := Finset.mem_filter.mp hk
      have hk_sq := (Finset.mem_filter.mp hk_sqf).2
      have hcop := (sqfree_coprime_div hk_sq hrk).symm
      have hdiv_pos : 0 < k / r :=
        Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk_sq.ne_zero) hrk) hr_icc.1
      have hr_ne : r ≠ 0 := by omega
      have hmul : hD d k = hD d r * hD d (k / r) := by
        conv_lhs => rw [← Nat.mul_div_cancel' hrk]
        exact hD_mul_coprime hr_ne hdiv_pos.ne' hcop.symm
      rw [hmul, mul_inv]
  have hprod_le : (∑ v ∈ r.divisors, (hD d v)⁻¹) * ∑ t ∈ T, (hD d t)⁻¹ ≤ selbergS d R := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']
    unfold selbergS
    refine sum_le_sum_of_injOn (fun vt => vt.1 * vt.2) ?_ ?_ ?_ fun x _ =>
      inv_nonneg.mpr (hD_pos hd).le
    · rintro ⟨v, t⟩ hvt
      obtain ⟨hv, ht⟩ := Finset.mem_product.mp hvt
      obtain ⟨ht_sqf, hcop_rt⟩ := Finset.mem_filter.mp ht
      have ht_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp ht_sqf).1
      have ht_sq := (Finset.mem_filter.mp ht_sqf).2
      have hvr := Nat.dvd_of_mem_divisors hv
      have hv_pos := Nat.pos_of_mem_divisors hv
      have hv_sq := hr_sq.squarefree_of_dvd hvr
      have hcop_vt := hcop_rt.coprime_dvd_left hvr
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩)
      · exact Nat.mul_pos hv_pos ht_icc.1
      · calc v * t ≤ r * (R / r) := Nat.mul_le_mul (Nat.le_of_dvd hr_icc.1 hvr) ht_icc.2
          _ ≤ R := Nat.mul_div_le R r
      · exact coprime_squarefree_mul hv_sq ht_sq hcop_vt
    · rintro ⟨v₁, t₁⟩ hv1 ⟨v₂, t₂⟩ hv2 heq
      obtain ⟨hv1', ht1'⟩ := Finset.mem_product.mp hv1
      obtain ⟨hv2', ht2'⟩ := Finset.mem_product.mp hv2
      have hvr1 := Nat.dvd_of_mem_divisors hv1'
      have hvr2 := Nat.dvd_of_mem_divisors hv2'
      have hv1_pos := Nat.pos_of_mem_divisors hv1'
      have hcop1 := (Finset.mem_filter.mp ht1').2
      have hcop2 := (Finset.mem_filter.mp ht2').2
      have hgcd1 : Nat.gcd (v₁ * t₁) r = v₁ := by
        refine Nat.dvd_antisymm ?_ (Nat.dvd_gcd (dvd_mul_right v₁ t₁) hvr1)
        exact (hcop1.coprime_dvd_left (Nat.gcd_dvd_right (v₁ * t₁) r)).dvd_of_dvd_mul_right
          (Nat.gcd_dvd_left (v₁ * t₁) r)
      have hgcd2 : Nat.gcd (v₂ * t₂) r = v₂ := by
        refine Nat.dvd_antisymm ?_ (Nat.dvd_gcd (dvd_mul_right v₂ t₂) hvr2)
        exact (hcop2.coprime_dvd_left (Nat.gcd_dvd_right (v₂ * t₂) r)).dvd_of_dvd_mul_right
          (Nat.gcd_dvd_left (v₂ * t₂) r)
      have heq' : v₁ * t₁ = v₂ * t₂ := heq
      have hv_eq : v₁ = v₂ := by rw [← hgcd1, ← hgcd2, heq']
      have ht_eq : t₁ = t₂ := by
        rw [← hv_eq] at heq'
        exact Nat.mul_left_cancel hv1_pos heq'
      exact Prod.ext hv_eq ht_eq
    · rintro ⟨v, t⟩ hvt
      obtain ⟨hv, ht⟩ := Finset.mem_product.mp hvt
      have hv_pos := Nat.pos_of_mem_divisors hv
      have ht_pos : 0 < t := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1).1
      have hcop_vt := (Finset.mem_filter.mp ht).2.coprime_dvd_left (Nat.dvd_of_mem_divisors hv)
      rw [hD_mul_coprime hv_pos.ne' ht_pos.ne' hcop_vt, mul_inv]
  unfold selbergLambda
  rw [hsplit_sum, abs_mul]
  have hμ_le : |((ArithmeticFunction.moebius r : ℤ) : ℝ)| ≤ 1 := by
    have : |(ArithmeticFunction.moebius r : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
    exact_mod_cast this
  have hS_pos' : 0 ≤ (selbergS d R * rhoD d r)⁻¹ := by positivity
  have hsum_nn : 0 ≤ (hD d r)⁻¹ * ∑ t ∈ T, (hD d t)⁻¹ :=
    mul_nonneg (inv_nonneg.mpr hh_pos.le) (Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (hD_pos hd).le)
  calc |((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selbergS d R * rhoD d r)| *
        |(hD d r)⁻¹ * ∑ t ∈ T, (hD d t)⁻¹|
      = |((ArithmeticFunction.moebius r : ℤ) : ℝ)| / (selbergS d R * rhoD d r) *
          ((hD d r)⁻¹ * ∑ t ∈ T, (hD d t)⁻¹) := by
          rw [abs_div, abs_of_pos (mul_pos hS_pos hrho_pos), abs_of_nonneg hsum_nn]
    _ ≤ 1 / (selbergS d R * rhoD d r) * ((hD d r)⁻¹ * ∑ t ∈ T, (hD d t)⁻¹) := by
          gcongr
    _ = ((rhoD d r * hD d r)⁻¹ * ∑ t ∈ T, (hD d t)⁻¹) / selbergS d R := by ring
    _ = ((∑ v ∈ r.divisors, (hD d v)⁻¹) * ∑ t ∈ T, (hD d t)⁻¹) / selbergS d R := by
          rw [inv_rho_mul_hD_eq_sum_inv hd hr_sq]
    _ ≤ selbergS d R / selbergS d R := div_le_div_of_nonneg_right hprod_le hS_pos.le
    _ = 1 := div_self hS_pos.ne'

private lemma harmonic_le_log_add_one (R : ℕ) (hR : 1 ≤ R) :
    ∑ a ∈ Finset.Icc 1 R, (1 : ℝ) / (a : ℝ) ≤ Real.log R + 1 := by
  induction R with
  | zero => omega
  | succ k ih =>
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
      have hk_pos : (0 : ℝ) < k := by positivity
      have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      have hih := ih hk1
      have hlog : (1 : ℝ) / (k + 1 : ℝ) ≤ Real.log (k + 1 : ℝ) - Real.log k := by
        have h1 : Real.log ((k : ℝ) / (k + 1 : ℝ)) ≤ (k : ℝ) / (k + 1 : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have heq1 : Real.log ((k : ℝ) / (k + 1 : ℝ)) = Real.log k - Real.log (k + 1 : ℝ) :=
          Real.log_div hk_pos.ne' (by positivity)
        have heq2 : (k : ℝ) / (k + 1 : ℝ) - 1 = -((1 : ℝ) / (k + 1 : ℝ)) := by
          field_simp; ring
        linarith
      push_cast
      linarith

private lemma sum_divisors_card_le (R : ℕ) (hR : 1 ≤ R) :
    ∑ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ) ≤ (R : ℝ) * (Real.log R + 1) := by
  have hswap : ∑ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ) =
      ∑ a ∈ Finset.Icc 1 R, (((Finset.Icc 1 R).filter (fun r => a ∣ r)).card : ℝ) := by
    have h1 : ∀ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ) =
        ∑ a ∈ Finset.Icc 1 R, if a ∣ r then (1 : ℝ) else 0 := by
      intro r hr
      have hr_icc := Finset.mem_Icc.mp hr
      rw [← Finset.sum_filter]
      have hcard : r.divisors.card = ((Finset.Icc 1 R).filter (fun a => a ∣ r)).card := by
        refine congrArg Finset.card ?_
        ext a
        simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨har, hr0⟩
          have ha_pos : 0 < a := Nat.pos_of_ne_zero (fun h => by subst h; simp at har; omega)
          exact ⟨⟨ha_pos, (Nat.le_of_dvd hr_icc.1 har).trans hr_icc.2⟩, har⟩
        · rintro ⟨_, har⟩
          exact ⟨har, by omega⟩
      simp [hcard]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  rw [hswap]
  have hmult : ∀ a ∈ Finset.Icc 1 R,
      (((Finset.Icc 1 R).filter (fun r => a ∣ r)).card : ℝ) ≤ (R : ℝ) / (a : ℝ) := by
    intro a ha
    have ha_pos : 0 < a := (Finset.mem_Icc.mp ha).1
    have hle : ((Finset.Icc 1 R).filter (fun r => a ∣ r)).card ≤ (Finset.Icc 1 (R / a)).card := by
      refine Finset.card_le_card_of_injOn (fun r => r / a) ?_ ?_
      · intro r hr
        obtain ⟨hr_icc, har⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hr)
        have hr_icc' := Finset.mem_Icc.mp hr_icc
        exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr
          ⟨Nat.div_pos (Nat.le_of_dvd hr_icc'.1 har) ha_pos, Nat.div_le_div_right hr_icc'.2⟩)
      · intro r₁ hr₁ r₂ hr₂ heq
        have heq' : r₁ / a = r₂ / a := heq
        have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hr₁)).2
        have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hr₂)).2
        have h1_mul := Nat.mul_div_cancel' h1
        have h2_mul := Nat.mul_div_cancel' h2
        rw [← h1_mul, ← h2_mul, heq']
    have hcard : (Finset.Icc 1 (R / a)).card = R / a := by simp
    have hle' : ((Finset.Icc 1 R).filter (fun r => a ∣ r)).card ≤ R / a := hle.trans_eq hcard
    calc (((Finset.Icc 1 R).filter (fun r => a ∣ r)).card : ℝ) ≤ ((R / a : ℕ) : ℝ) := by
          exact_mod_cast hle'
      _ ≤ (R : ℝ) / (a : ℝ) := Nat.cast_div_le
  calc ∑ a ∈ Finset.Icc 1 R, (((Finset.Icc 1 R).filter (fun r => a ∣ r)).card : ℝ)
      ≤ ∑ a ∈ Finset.Icc 1 R, (R : ℝ) / (a : ℝ) := Finset.sum_le_sum hmult
    _ = (R : ℝ) * ∑ a ∈ Finset.Icc 1 R, (1 : ℝ) / (a : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => by ring
    _ ≤ (R : ℝ) * (Real.log R + 1) :=
        mul_le_mul_of_nonneg_left (harmonic_le_log_add_one R hR) (by positivity)

private lemma sieve_shifted_primes_bound {d N R : ℕ} (hd : 2 ∣ d) (hR : 1 ≤ R) :
    (((Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ) ≤
      (R : ℝ) + (N : ℝ) / selbergS d R + ((R : ℝ) * (Real.log R + 1)) ^ 2 := by
  let P := (Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)
  let P_sm := P.filter (fun p => p ≤ R)
  let P_lg := P.filter (fun p => R < p)
  have hP_split : P.card ≤ P_sm.card + P_lg.card := by
    have hsub : P ⊆ P_sm ∪ P_lg := fun p hp => by
      by_cases h : p ≤ R
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, by omega⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le P_sm P_lg)
  have hsm_le : P_sm.card ≤ R := by
    have hsub : P_sm ⊆ Finset.Icc 1 R := fun p hp => by
      have hp1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
      have hp2 := (Finset.mem_filter.mp hp).2
      exact Finset.mem_Icc.mpr ⟨hp1, hp2⟩
    calc P_sm.card ≤ (Finset.Icc 1 R).card := Finset.card_le_card hsub
      _ = R := by simp
  have hlg_one : ∀ m ∈ P_lg,
      ∑ r ∈ (sqfreeUpTo R).filter (fun r => r ∣ m * (m + d)), selbergLambda d R r = 1 := by
    intro m hm
    obtain ⟨hmP, hmR⟩ := Finset.mem_filter.mp hm
    obtain ⟨_, hm_p, hmd_p⟩ := Finset.mem_filter.mp hmP
    have hfilt : (sqfreeUpTo R).filter (fun r => r ∣ m * (m + d)) = {1} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hr_sqf, hrm⟩
        have hr_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr_sqf).1
        by_contra hr1
        have hr2 : 2 ≤ r := by omega
        obtain ⟨q, hq_prime, hqr⟩ := Nat.exists_prime_and_dvd hr1
        have hq_le : q ≤ R := (Nat.le_of_dvd hr_icc.1 hqr).trans hr_icc.2
        have hqm : q ∣ m * (m + d) := hqr.trans hrm
        rcases hq_prime.dvd_mul.mp hqm with hq1 | hq2
        · rcases hm_p.eq_one_or_self_of_dvd q hq1 with h | h
          · exact hq_prime.ne_one h
          · omega
        · rcases hmd_p.eq_one_or_self_of_dvd q hq2 with h | h
          · exact hq_prime.ne_one h
          · omega
      · rintro rfl
        exact ⟨one_mem_sqfreeUpTo hR, one_dvd _⟩
    rw [hfilt, Finset.sum_singleton, selbergLambda_one hd hR]
  have hlg_le_sum : (P_lg.card : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 N,
        (∑ r ∈ (sqfreeUpTo R).filter (fun r => r ∣ m * (m + d)), selbergLambda d R r) ^ 2 := by
    have h1 : (P_lg.card : ℝ) = ∑ m ∈ P_lg,
        (∑ r ∈ (sqfreeUpTo R).filter (fun r => r ∣ m * (m + d)), selbergLambda d R r) ^ 2 := by
      calc (P_lg.card : ℝ) = ∑ _m ∈ P_lg, (1 : ℝ) := by simp
        _ = ∑ m ∈ P_lg,
              (∑ r ∈ (sqfreeUpTo R).filter (fun r => r ∣ m * (m + d)), selbergLambda d R r) ^ 2 := by
            refine Finset.sum_congr rfl fun m hm => ?_
            rw [hlg_one m hm, one_pow]
    rw [h1]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun m hm =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1) (fun _ _ _ => sq_nonneg _)
  have hsq_expand :
      ∑ m ∈ Finset.Icc 1 N,
        (∑ r ∈ (sqfreeUpTo R).filter (fun r => r ∣ m * (m + d)), selbergLambda d R r) ^ 2 =
      ∑ r₁ ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R,
        selbergLambda d R r₁ * selbergLambda d R r₂ *
          (((Finset.Icc 1 N).filter (fun m => Nat.lcm r₁ r₂ ∣ m * (m + d))).card : ℝ) := by
    have hpt : ∀ m ∈ Finset.Icc 1 N,
        (∑ r ∈ (sqfreeUpTo R).filter (fun r => r ∣ m * (m + d)), selbergLambda d R r) ^ 2 =
        ∑ r₁ ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R,
          if Nat.lcm r₁ r₂ ∣ m * (m + d) then selbergLambda d R r₁ * selbergLambda d R r₂ else 0 := by
      intro m _
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun r₁ _ => ?_
      rw [Finset.sum_filter]
      by_cases h1 : r₁ ∣ m * (m + d)
      · rw [if_pos h1]
        refine Finset.sum_congr rfl fun r₂ _ => ?_
        by_cases h2 : r₂ ∣ m * (m + d)
        · rw [if_pos h2, if_pos (Nat.lcm_dvd h1 h2)]
        · rw [if_neg h2, if_neg (fun h => h2 ((Nat.dvd_lcm_right r₁ r₂).trans h))]
      · rw [if_neg h1]
        symm
        refine Finset.sum_eq_zero fun r₂ _ => ?_
        rw [if_neg (fun h => h1 ((Nat.dvd_lcm_left r₁ r₂).trans h))]
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r₂ _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hmain_err :
      ∑ r₁ ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R,
        selbergLambda d R r₁ * selbergLambda d R r₂ *
          (((Finset.Icc 1 N).filter (fun m => Nat.lcm r₁ r₂ ∣ m * (m + d))).card : ℝ) ≤
      (N : ℝ) / selbergS d R + ((R : ℝ) * (Real.log R + 1)) ^ 2 := by
    have hdecomp :
        ∑ r₁ ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R,
          selbergLambda d R r₁ * selbergLambda d R r₂ *
            (((Finset.Icc 1 N).filter (fun m => Nat.lcm r₁ r₂ ∣ m * (m + d))).card : ℝ) =
        (N : ℝ) * (∑ r₁ ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R,
            selbergLambda d R r₁ * selbergLambda d R r₂ * rhoD d (Nat.lcm r₁ r₂)) +
          ∑ r₁ ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R,
            selbergLambda d R r₁ * selbergLambda d R r₂ *
              ((((Finset.Icc 1 N).filter (fun m => Nat.lcm r₁ r₂ ∣ m * (m + d))).card : ℝ) -
                (N : ℝ) * rhoD d (Nat.lcm r₁ r₂)) := by
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r₁ _ => Finset.sum_congr rfl fun r₂ _ => ?_
      ring
    have herr_bound :
        ∑ r₁ ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R,
          selbergLambda d R r₁ * selbergLambda d R r₂ *
            ((((Finset.Icc 1 N).filter (fun m => Nat.lcm r₁ r₂ ∣ m * (m + d))).card : ℝ) -
              (N : ℝ) * rhoD d (Nat.lcm r₁ r₂)) ≤
          ((R : ℝ) * (Real.log R + 1)) ^ 2 := by
      calc _ ≤ ∑ r₁ ∈ sqfreeUpTo R, ∑ r₂ ∈ sqfreeUpTo R,
            (r₁.divisors.card : ℝ) * (r₂.divisors.card : ℝ) := by
              refine Finset.sum_le_sum fun r₁ hr₁ => Finset.sum_le_sum fun r₂ hr₂ => ?_
              have hr1_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr₁).1
              have hr2_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hr₂).1
              have hr1_sq := (Finset.mem_filter.mp hr₁).2
              have hr2_sq := (Finset.mem_filter.mp hr₂).2
              have hlcm_sq := squarefree_lcm hr1_sq hr2_sq
              have h1 := abs_selbergLambda_le_one hd hR hr₁
              have h2 := abs_selbergLambda_le_one hd hR hr₂
              have herr := card_Icc_solutions_err (d := d) (N := N) hlcm_sq
              have hg_le : (gD d (Nat.lcm r₁ r₂) : ℝ) ≤ (r₁.divisors.card : ℝ) * (r₂.divisors.card : ℝ) := by
                have hgl : gD d (Nat.lcm r₁ r₂) ≤ gD d r₁ * gD d r₂ := by
                  have hr1_ne : r₁ ≠ 0 := by omega
                  have hr2_ne : r₂ ≠ 0 := by omega
                  have hprod := gD_lcm_mul_gcd (d := d) hr1_ne hr2_ne
                  have hgcd_pos : 1 ≤ gD d (Nat.gcd r₁ r₂) := gD_pos d _
                  calc gD d (Nat.lcm r₁ r₂) = gD d (Nat.lcm r₁ r₂) * 1 := (mul_one _).symm
                    _ ≤ gD d (Nat.lcm r₁ r₂) * gD d (Nat.gcd r₁ r₂) :=
                        Nat.mul_le_mul_left _ hgcd_pos
                    _ = gD d r₁ * gD d r₂ := hprod
                have hd1 : gD d r₁ ≤ r₁.divisors.card := gD_le_card_divisors hr1_sq
                have hd2 : gD d r₂ ≤ r₂.divisors.card := gD_le_card_divisors hr2_sq
                exact_mod_cast hgl.trans (Nat.mul_le_mul hd1 hd2)
              calc selbergLambda d R r₁ * selbergLambda d R r₂ * _
                  ≤ |selbergLambda d R r₁ * selbergLambda d R r₂ * _| := le_abs_self _
                _ = |selbergLambda d R r₁| * |selbergLambda d R r₂| * |_| := by
                    rw [abs_mul, abs_mul]
                _ ≤ 1 * 1 * (gD d (Nat.lcm r₁ r₂) : ℝ) :=
                    mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one) herr (abs_nonneg _)
                      (by norm_num)
                _ ≤ (r₁.divisors.card : ℝ) * (r₂.divisors.card : ℝ) := by
                    rw [one_mul, one_mul]; exact hg_le
        _ = (∑ r ∈ sqfreeUpTo R, (r.divisors.card : ℝ)) ^ 2 := by
              rw [sq, Finset.sum_mul]
              refine Finset.sum_congr rfl fun r₁ _ => ?_
              rw [Finset.mul_sum]
        _ ≤ (∑ r ∈ Finset.Icc 1 R, (r.divisors.card : ℝ)) ^ 2 := by
              refine pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) ?_ 2
              exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun _ _ _ => Nat.cast_nonneg _)
        _ ≤ ((R : ℝ) * (Real.log R + 1)) ^ 2 := by
              refine pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
                (sum_divisors_card_le R hR) 2
    rw [hdecomp, selberg_quad_eq hd hR, ← div_eq_mul_inv]
    linarith
  have hP_real : (P.card : ℝ) ≤ (P_sm.card : ℝ) + (P_lg.card : ℝ) := by exact_mod_cast hP_split
  have hsm_real : (P_sm.card : ℝ) ≤ (R : ℝ) := by exact_mod_cast hsm_le
  linarith [hP_real, hsm_real, hlg_le_sum, hsq_expand, hmain_err]

/- ### Section 3: Lower Bound on selbergS and Mean-Value Bound on weightW ^ 2 -/

private lemma log_le_harmonic (M : ℕ) (hM : 1 ≤ M) :
    Real.log M ≤ ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) := by
  have hstrong : ∀ k : ℕ, Real.log (k + 1 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 k, (1 : ℝ) / (m : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk1 : (0 : ℝ) < k + 1 := by positivity
      have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      have hstep : Real.log ((k + 1 : ℝ) + 1) - Real.log (k + 1 : ℝ) ≤ (1 : ℝ) / (k + 1 : ℝ) := by
        have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < ((k + 1 : ℝ) + 1) / (k + 1 : ℝ))
        have heq1 : Real.log (((k + 1 : ℝ) + 1) / (k + 1 : ℝ)) =
            Real.log ((k + 1 : ℝ) + 1) - Real.log (k + 1 : ℝ) :=
          Real.log_div (by positivity) hk1.ne'
        have heq2 : ((k + 1 : ℝ) + 1) / (k + 1 : ℝ) - 1 = (1 : ℝ) / (k + 1 : ℝ) := by
          field_simp; ring
        linarith
      push_cast
      linarith
  have hm_pos : (0 : ℝ) < M := by positivity
  calc Real.log M ≤ Real.log ((M : ℝ) + 1) := Real.log_le_log hm_pos (by linarith)
    _ ≤ ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) := hstrong M

private lemma geom_sum_prime_le {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∑ e ∈ Finset.range K, (1 : ℝ) / (p : ℝ) ^ e ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h1p : (1 : ℝ) / (p : ℝ) ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq (by positivity)]
    linarith
  have hsum : ∑ e ∈ Finset.range K, ((1 : ℝ) / (p : ℝ)) ^ e =
      (((1 : ℝ) / (p : ℝ)) ^ K - 1) / ((1 : ℝ) / (p : ℝ) - 1) := geom_sum_eq h1p K
  have hcongr : ∑ e ∈ Finset.range K, (1 : ℝ) / (p : ℝ) ^ e =
      ∑ e ∈ Finset.range K, ((1 : ℝ) / (p : ℝ)) ^ e := by
    refine Finset.sum_congr rfl fun e _ => by rw [one_div, one_div, inv_pow]
  rw [hcongr, hsum]
  have hnum : ((1 : ℝ) / (p : ℝ)) ^ K - 1 ≤ 0 := by
    have : ((1 : ℝ) / (p : ℝ)) ^ K ≤ 1 := pow_le_one₀ (by positivity) (by
      rw [div_le_one (by positivity)]; linarith)
    linarith
  have hden : (1 : ℝ) / (p : ℝ) - 1 < 0 := by
    have : (1 : ℝ) / (p : ℝ) < 1 := (div_lt_one (by positivity)).mpr hp1
    linarith
  have hneg : (((1 : ℝ) / (p : ℝ)) ^ K - 1) / ((1 : ℝ) / (p : ℝ) - 1) =
      (1 - ((1 : ℝ) / (p : ℝ)) ^ K) / (1 - (1 : ℝ) / (p : ℝ)) := by
    rw [← neg_div_neg_eq]; congr 1 <;> ring
  rw [hneg]
  have hle : (1 - ((1 : ℝ) / (p : ℝ)) ^ K) / (1 - (1 : ℝ) / (p : ℝ)) ≤
      1 / (1 - (1 : ℝ) / (p : ℝ)) := by
    refine div_le_div_of_nonneg_right ?_ (by linarith)
    linarith [show 0 ≤ ((1 : ℝ) / (p : ℝ)) ^ K by positivity]
  have heq : 1 / (1 - (1 : ℝ) / (p : ℝ)) = (p : ℝ) / ((p : ℝ) - 1) := by
    have hp_ne : (p : ℝ) ≠ 0 := by positivity
    have hp1_ne : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  exact hle.trans_eq heq

private lemma exp_lt_of_prime_pow_le {p e M : ℕ} (hp : p.Prime) (hm : p ^ e ≤ M) :
    e < M + 1 := by
  have h2p : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp.two_le e
  have hlt : e < 2 ^ e := Nat.lt_two_pow_self
  omega

private lemma prod_prime_pow_factorization_eq {m : ℕ} (hm : 0 < m) (S : Finset ℕ)
    (hS : m.primeFactors ⊆ S) :
    ∏ p ∈ S, p ^ m.factorization p = m := by
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm.ne']
  rw [Finsupp.prod, Nat.support_factorization]
  refine (Finset.prod_subset hS fun p _ hp_not => ?_).symm
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, ne_eq, not_not] at hp_not
  rw [hp_not, pow_zero]

private lemma rad_fiber_sum_le {d M k : ℕ} (hd : 2 ∣ d) (_hk : Squarefree k) (hcop : k.Coprime d) :
    ∑ ab ∈ ((Finset.Icc 1 M).filter (fun a => a.Coprime d) ×ˢ
        (Finset.Icc 1 M).filter (fun b => b.Coprime d)).filter
          (fun ab => ∏ p ∈ (ab.1 * ab.2).primeFactors, p = k),
      (1 : ℝ) / ((ab.1 : ℝ) * (ab.2 : ℝ)) ≤ (hD d k)⁻¹ := by
  let E := (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).erase (0, 0)
  let F := (Fintype.piFinset (fun _ : k.primeFactors => E))
  have hprod_sum :
      ∑ f ∈ F, ∏ p : k.primeFactors,
        ((1 : ℝ) / ((p.1 : ℝ) ^ (f p).1) * ((1 : ℝ) / ((p.1 : ℝ) ^ (f p).2))) =
      ∏ p : k.primeFactors,
        ∑ xy ∈ E, ((1 : ℝ) / ((p.1 : ℝ) ^ xy.1) * ((1 : ℝ) / ((p.1 : ℝ) ^ xy.2))) := by
    exact Finset.sum_prod_piFinset E (fun (p : k.primeFactors) (xy : ℕ × ℕ) =>
      ((1 : ℝ) / ((p.1 : ℝ) ^ xy.1) * ((1 : ℝ) / ((p.1 : ℝ) ^ xy.2))))
  have hsum_le_F :
      ∑ ab ∈ ((Finset.Icc 1 M).filter (fun a => a.Coprime d) ×ˢ
          (Finset.Icc 1 M).filter (fun b => b.Coprime d)).filter
            (fun ab => ∏ p ∈ (ab.1 * ab.2).primeFactors, p = k),
        (1 : ℝ) / ((ab.1 : ℝ) * (ab.2 : ℝ)) ≤
      ∑ f ∈ F, ∏ p : k.primeFactors,
        ((1 : ℝ) / ((p.1 : ℝ) ^ (f p).1) * ((1 : ℝ) / ((p.1 : ℝ) ^ (f p).2))) := by
    refine sum_le_sum_of_injOn
      (fun ab (p : k.primeFactors) => (ab.1.factorization p.1, ab.2.factorization p.1))
      ?_ ?_ ?_ (fun _ _ => Finset.prod_nonneg fun _ _ => by positivity)
    · rintro ⟨a, b⟩ hab
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hab
      obtain ⟨⟨⟨⟨ha1, haM⟩, _⟩, ⟨⟨hb1, hbM⟩, _⟩⟩, hrad⟩ := hab
      have hpf : (a * b).primeFactors = k.primeFactors := by
        rw [← hrad]
        refine Finset.ext fun q => ?_
        constructor
        · intro hq
          have hqp := Nat.prime_of_mem_primeFactors hq
          exact Nat.mem_primeFactors.mpr ⟨hqp, Finset.dvd_prod_of_mem id hq,
            (Finset.prod_pos fun x hx => (Nat.prime_of_mem_primeFactors hx).pos).ne'⟩
        · intro hq
          have hqp := Nat.prime_of_mem_primeFactors hq
          have hdvd := Nat.dvd_of_mem_primeFactors hq
          obtain ⟨x, hx, hqx⟩ := (hqp.prime.dvd_finsetProd_iff id).mp hdvd
          have hxp := Nat.prime_of_mem_primeFactors hx
          rcases hxp.eq_one_or_self_of_dvd q hqx with h | h
          · exact absurd h hqp.ne_one
          · rwa [h]
      refine Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr fun p => Finset.mem_erase.mpr ⟨?_, ?_⟩)
      · intro h0
        have hp_pf : p.1 ∈ (a * b).primeFactors := hpf.symm ▸ p.2
        have ha_ne : a ≠ 0 := by omega
        have hb_ne : b ≠ 0 := by omega
        have hsum0 : (a * b).factorization p.1 = 0 := by
          rw [Nat.factorization_mul ha_ne hb_ne, Finsupp.coe_add, Pi.add_apply]
          have h1 : a.factorization p.1 = 0 := congrArg Prod.fst h0
          have h2 : b.factorization p.1 = 0 := congrArg Prod.snd h0
          omega
        exact (Finsupp.mem_support_iff.mp (Nat.support_factorization (a * b) ▸ hp_pf)) hsum0
      · have hp_prime := Nat.prime_of_mem_primeFactors p.2
        have hpa : p.1 ^ a.factorization p.1 ≤ M :=
          (Nat.le_of_dvd ha1 (Nat.ordProj_dvd a p.1)).trans haM
        have hpb : p.1 ^ b.factorization p.1 ≤ M :=
          (Nat.le_of_dvd hb1 (Nat.ordProj_dvd b p.1)).trans hbM
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (exp_lt_of_prime_pow_le hp_prime hpa),
          Finset.mem_range.mpr (exp_lt_of_prime_pow_le hp_prime hpb)⟩
    · rintro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h1 h2
      obtain ⟨⟨⟨⟨ha11, _⟩, _⟩, ⟨⟨hb11, _⟩, _⟩⟩, hrad1⟩ := h1
      obtain ⟨⟨⟨⟨ha21, _⟩, _⟩, ⟨⟨hb21, _⟩, _⟩⟩, hrad2⟩ := h2
      have ha1_ne : a₁ ≠ 0 := Nat.ne_of_gt ha11
      have hb1_ne : b₁ ≠ 0 := Nat.ne_of_gt hb11
      have ha2_ne : a₂ ≠ 0 := Nat.ne_of_gt ha21
      have hb2_ne : b₂ ≠ 0 := Nat.ne_of_gt hb21
      have hpf1 : (a₁ * b₁).primeFactors ⊆ k.primeFactors := by
        intro q hq
        rw [← hrad1]
        exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq, Finset.dvd_prod_of_mem id hq,
          (Finset.prod_pos fun x hx => (Nat.prime_of_mem_primeFactors hx).pos).ne'⟩
      have hpf2 : (a₂ * b₂).primeFactors ⊆ k.primeFactors := by
        intro q hq
        rw [← hrad2]
        exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq, Finset.dvd_prod_of_mem id hq,
          (Finset.prod_pos fun x hx => (Nat.prime_of_mem_primeFactors hx).pos).ne'⟩
      have ha1_sub : a₁.primeFactors ⊆ k.primeFactors :=
        (Nat.primeFactors_mul ha1_ne hb1_ne ▸ Finset.subset_union_left).trans hpf1
      have hb1_sub : b₁.primeFactors ⊆ k.primeFactors :=
        (Nat.primeFactors_mul ha1_ne hb1_ne ▸ Finset.subset_union_right).trans hpf1
      have ha2_sub : a₂.primeFactors ⊆ k.primeFactors :=
        (Nat.primeFactors_mul ha2_ne hb2_ne ▸ Finset.subset_union_left).trans hpf2
      have hb2_sub : b₂.primeFactors ⊆ k.primeFactors :=
        (Nat.primeFactors_mul ha2_ne hb2_ne ▸ Finset.subset_union_right).trans hpf2
      have ha_eq : a₁ = a₂ := by
        rw [← prod_prime_pow_factorization_eq ha11 k.primeFactors ha1_sub,
          ← prod_prime_pow_factorization_eq ha21 k.primeFactors ha2_sub]
        refine Finset.prod_congr rfl fun q hq => ?_
        have hfq := congrArg Prod.fst (congrFun heq ⟨q, hq⟩)
        dsimp only at hfq
        rw [hfq]
      have hb_eq : b₁ = b₂ := by
        rw [← prod_prime_pow_factorization_eq hb11 k.primeFactors hb1_sub,
          ← prod_prime_pow_factorization_eq hb21 k.primeFactors hb2_sub]
        refine Finset.prod_congr rfl fun q hq => ?_
        have hfq := congrArg Prod.snd (congrFun heq ⟨q, hq⟩)
        dsimp only at hfq
        rw [hfq]
      exact Prod.ext ha_eq hb_eq
    · rintro ⟨a, b⟩ hab
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hab
      obtain ⟨⟨⟨⟨ha1, _⟩, _⟩, ⟨⟨hb1, _⟩, _⟩⟩, hrad⟩ := hab
      have ha_ne : a ≠ 0 := Nat.ne_of_gt ha1
      have hb_ne : b ≠ 0 := Nat.ne_of_gt hb1
      have hpf : (a * b).primeFactors ⊆ k.primeFactors := by
        intro q hq
        rw [← hrad]
        exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq, Finset.dvd_prod_of_mem id hq,
          (Finset.prod_pos fun x hx => (Nat.prime_of_mem_primeFactors hx).pos).ne'⟩
      have ha_sub : a.primeFactors ⊆ k.primeFactors :=
        (Nat.primeFactors_mul ha_ne hb_ne ▸ Finset.subset_union_left).trans hpf
      have hb_sub : b.primeFactors ⊆ k.primeFactors :=
        (Nat.primeFactors_mul ha_ne hb_ne ▸ Finset.subset_union_right).trans hpf
      have ha_prod : (a : ℝ) = ∏ p : k.primeFactors, (p.1 : ℝ) ^ a.factorization p.1 := by
        have hnat := prod_prime_pow_factorization_eq ha1 k.primeFactors ha_sub
        conv_lhs => rw [← hnat]
        push_cast
        exact (Finset.prod_coe_sort k.primeFactors (fun p => (p : ℝ) ^ a.factorization p)).symm
      have hb_prod : (b : ℝ) = ∏ p : k.primeFactors, (p.1 : ℝ) ^ b.factorization p.1 := by
        have hnat := prod_prime_pow_factorization_eq hb1 k.primeFactors hb_sub
        conv_lhs => rw [← hnat]
        push_cast
        exact (Finset.prod_coe_sort k.primeFactors (fun p => (p : ℝ) ^ b.factorization p)).symm
      rw [ha_prod, hb_prod]
      have hpa : (∏ p : k.primeFactors, (p.1 : ℝ) ^ a.factorization p.1)⁻¹ =
          ∏ p : k.primeFactors, (1 : ℝ) / (p.1 : ℝ) ^ a.factorization p.1 := by
        rw [← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun p _ => (one_div _).symm
      have hpb : (∏ p : k.primeFactors, (p.1 : ℝ) ^ b.factorization p.1)⁻¹ =
          ∏ p : k.primeFactors, (1 : ℝ) / (p.1 : ℝ) ^ b.factorization p.1 := by
        rw [← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun p _ => (one_div _).symm
      rw [one_div, mul_inv, hpa, hpb, ← Finset.prod_mul_distrib]
  have hfactor_le : ∀ p : k.primeFactors,
      ∑ xy ∈ E, ((1 : ℝ) / ((p.1 : ℝ) ^ xy.1) * ((1 : ℝ) / ((p.1 : ℝ) ^ xy.2))) ≤
        (((p.1 : ℝ) - (omegaD d p.1 : ℝ)) / (omegaD d p.1 : ℝ))⁻¹ := by
    intro p
    have hp_prime := Nat.prime_of_mem_primeFactors p.2
    have hpdvd : p.1 ∣ k := Nat.dvd_of_mem_primeFactors p.2
    have hp_ndvd : ¬ p.1 ∣ d := fun h => hp_prime.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpdvd h)
    have hp2_ne : p.1 ≠ 2 := fun h => hp_ndvd (h ▸ hd)
    have hp3 : 3 ≤ p.1 := by have := hp_prime.two_le; omega
    have hω_eq : omegaD d p.1 = 2 := by simp [omegaD, hp_ndvd]
    have hE_sum :
        ∑ xy ∈ E, ((1 : ℝ) / ((p.1 : ℝ) ^ xy.1) * ((1 : ℝ) / ((p.1 : ℝ) ^ xy.2))) =
          (∑ e ∈ Finset.range (M + 1), (1 : ℝ) / (p.1 : ℝ) ^ e) ^ 2 - 1 := by
      have h00 : (0, 0) ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1) := by simp
      have hfull := Finset.sum_erase_add (Finset.range (M + 1) ×ˢ Finset.range (M + 1))
        (fun xy => (1 : ℝ) / ((p.1 : ℝ) ^ xy.1) * ((1 : ℝ) / ((p.1 : ℝ) ^ xy.2))) h00
      have he00 : ((1 : ℝ) / ((p.1 : ℝ) ^ 0) * ((1 : ℝ) / ((p.1 : ℝ) ^ 0))) = 1 := by norm_num
      have hprod_eq :
          ∑ xy ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
            ((1 : ℝ) / ((p.1 : ℝ) ^ xy.1) * ((1 : ℝ) / ((p.1 : ℝ) ^ xy.2))) =
          (∑ e ∈ Finset.range (M + 1), (1 : ℝ) / (p.1 : ℝ) ^ e) ^ 2 := by
        rw [Finset.sum_product, sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun e₁ _ => ?_
        rw [Finset.mul_sum]
      dsimp only [E]
      linarith
    have hgeom := geom_sum_prime_le hp_prime (M + 1)
    have hsq_le : (∑ e ∈ Finset.range (M + 1), (1 : ℝ) / (p.1 : ℝ) ^ e) ^ 2 - 1 ≤
        ((p.1 : ℝ) / ((p.1 : ℝ) - 1)) ^ 2 - 1 := by
      have hnn : 0 ≤ ∑ e ∈ Finset.range (M + 1), (1 : ℝ) / (p.1 : ℝ) ^ e :=
        Finset.sum_nonneg fun _ _ => by positivity
      linarith [pow_le_pow_left₀ hnn hgeom 2]
    have hp_real : (3 : ℝ) ≤ p.1 := by exact_mod_cast hp3
    have halg : ((p.1 : ℝ) / ((p.1 : ℝ) - 1)) ^ 2 - 1 ≤
        (((p.1 : ℝ) - (omegaD d p.1 : ℝ)) / (omegaD d p.1 : ℝ))⁻¹ := by
      rw [hω_eq]
      push_cast
      rw [inv_div]
      have hne1 : (p.1 : ℝ) - 1 ≠ 0 := by linarith
      have hpos2 : (0 : ℝ) < (p.1 : ℝ) - 2 := by linarith
      rw [div_pow, div_sub_one (pow_ne_zero 2 hne1), div_le_div_iff₀ (by positivity) hpos2]
      have hid : 2 * ((p.1 : ℝ) - 1) ^ 2 - ((p.1 : ℝ) ^ 2 - ((p.1 : ℝ) - 1) ^ 2) * ((p.1 : ℝ) - 2) =
          (p.1 : ℝ) := by ring
      linarith
    exact hE_sum.symm ▸ hsq_le.trans halg
  have hprod_le :
      ∏ p : k.primeFactors,
        ∑ xy ∈ E, ((1 : ℝ) / ((p.1 : ℝ) ^ xy.1) * ((1 : ℝ) / ((p.1 : ℝ) ^ xy.2))) ≤
      (hD d k)⁻¹ := by
    have hle := Finset.prod_le_prod (s := (Finset.univ : Finset k.primeFactors))
      (fun (p : k.primeFactors) _ => Finset.sum_nonneg fun _ _ => by positivity)
      (fun (p : k.primeFactors) _ => hfactor_le p)
    have hinv : ∏ p : k.primeFactors,
        (((p.1 : ℝ) - (omegaD d p.1 : ℝ)) / (omegaD d p.1 : ℝ))⁻¹ = (hD d k)⁻¹ := by
      rw [Finset.prod_inv_distrib, Finset.prod_coe_sort k.primeFactors
        (fun p => (((p : ℝ) - (omegaD d p : ℝ)) / (omegaD d p : ℝ)))]
      rfl
    exact hle.trans_eq hinv
  exact hsum_le_F.trans (hprod_sum ▸ hprod_le)

private lemma harmonic_coprime_lower {d M : ℕ} (hd : 0 < d) :
    ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) ≤
      weightW d * ∑ a ∈ (Finset.Icc 1 M).filter (fun a => a.Coprime d), (1 : ℝ) / (a : ℝ) := by
  let A := (Finset.Icc 1 M).filter (fun a => a.Coprime d)
  let G := Fintype.piFinset (fun _ : d.primeFactors => Finset.range (M + 1))
  have hG_sum :
      (∑ f ∈ G, ∏ p : d.primeFactors, (1 : ℝ) / (p.1 : ℝ) ^ (f p)) *
        (∑ a ∈ A, (1 : ℝ) / (a : ℝ)) =
      ∑ fa ∈ G ×ˢ A,
        (∏ p : d.primeFactors, (1 : ℝ) / (p.1 : ℝ) ^ (fa.1 p)) * ((1 : ℝ) / (fa.2 : ℝ)) := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    exact (Finset.sum_product' _ _ _).symm
  have hm_decomp : ∀ m ∈ Finset.Icc 1 M,
      let k_d := ∏ p : d.primeFactors, p.1 ^ m.factorization p.1
      k_d ∣ m ∧ (m / k_d) ∈ A ∧
        (∏ p : d.primeFactors, (1 : ℝ) / (p.1 : ℝ) ^ m.factorization p.1) *
          ((1 : ℝ) / ((m / k_d : ℕ) : ℝ)) = (1 : ℝ) / (m : ℝ) := by
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hmM := (Finset.mem_Icc.mp hm).2
    let k_d := ∏ p : d.primeFactors, p.1 ^ m.factorization p.1
    have hk_dvd : k_d ∣ m := by
      have hsub : Finset.filter (fun p => p ∈ d.primeFactors) m.primeFactors ⊆ m.primeFactors :=
        Finset.filter_subset _ _
      have h1 : k_d = ∏ p ∈ m.primeFactors.filter (fun p => p ∈ d.primeFactors), p ^ m.factorization p := by
        dsimp only [k_d]
        rw [Finset.prod_coe_sort d.primeFactors (fun p => p ^ m.factorization p)]
        refine (Finset.prod_subset_one_on_sdiff (fun p hp => (Finset.mem_filter.mp hp).2) ?_
          fun _ _ => rfl).symm
        intro p hp
        have hp_m : p ∉ m.primeFactors := fun h =>
          (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨h, (Finset.mem_sdiff.mp hp).1⟩)
        have hf0 : m.factorization p = 0 := by
          by_contra h
          exact hp_m (Nat.support_factorization m ▸ Finsupp.mem_support_iff.mpr h)
        rw [hf0, pow_zero]
      rw [h1]
      calc _ ∣ ∏ p ∈ m.primeFactors, p ^ m.factorization p :=
            Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
        _ = m := by
            have hm_ne : m ≠ 0 := by omega
            have hprod := Nat.prod_factorization_pow_eq_self hm_ne
            rwa [Finsupp.prod, Nat.support_factorization] at hprod
    have hk_pos : 0 < k_d := Finset.prod_pos fun p _ => pow_pos (Nat.prime_of_mem_primeFactors p.2).pos _
    have ha_pos : 0 < m / k_d := Nat.div_pos (Nat.le_of_dvd hm1 hk_dvd) hk_pos
    have ha_le : m / k_d ≤ M := (Nat.div_le_self m k_d).trans hmM
    have ha_cop : (m / k_d).Coprime d := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra h
      obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd (m / k_d) d ≠ 1)
      have hpa := hp_dvd.trans (Nat.gcd_dvd_left _ _)
      have hpd := hp_dvd.trans (Nat.gcd_dvd_right _ _)
      have hp_mem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hpd, hd.ne'⟩
      have hpe_dvd : p ^ m.factorization p ∣ k_d :=
        Finset.dvd_prod_of_mem (fun (x : d.primeFactors) => x.1 ^ m.factorization x.1)
          (Finset.mem_univ ⟨p, hp_mem⟩)
      have hpe1 : p ^ (m.factorization p + 1) ∣ m := by
        have hlhs : p ^ (m.factorization p + 1) = p ^ m.factorization p * p := pow_succ p _
        have hrhs : m = k_d * (m / k_d) := (Nat.mul_div_cancel' hk_dvd).symm
        conv_rhs => rw [hrhs]
        rw [hlhs]
        exact mul_dvd_mul hpe_dvd hpa
      have hm_ne : m ≠ 0 := by omega
      have hcontra := (Nat.Prime.pow_dvd_iff_le_factorization hp_prime hm_ne).mp hpe1
      omega
    refine ⟨hk_dvd, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha_pos, ha_le⟩, ha_cop⟩, ?_⟩
    have hm_eq : (m : ℝ) = (k_d : ℝ) * ((m / k_d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hk_dvd).symm
    rw [hm_eq]
    have hkd_real : (k_d : ℝ) = ∏ p : d.primeFactors, (p.1 : ℝ) ^ m.factorization p.1 := by
      dsimp only [k_d]; push_cast; rfl
    rw [hkd_real]
    simp_rw [one_div]
    rw [Finset.prod_inv_distrib, mul_inv]
  have hsum_le : ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) ≤
      ∑ fa ∈ G ×ˢ A,
        (∏ p : d.primeFactors, (1 : ℝ) / (p.1 : ℝ) ^ (fa.1 p)) * ((1 : ℝ) / (fa.2 : ℝ)) := by
    refine sum_le_sum_of_injOn
      (fun m => (fun p : d.primeFactors => m.factorization p.1,
        m / ∏ p : d.primeFactors, p.1 ^ m.factorization p.1))
      ?_ ?_ ?_ (fun _ _ => by positivity)
    · intro m hm
      obtain ⟨_, haA, _⟩ := hm_decomp m hm
      have hm1 := (Finset.mem_Icc.mp hm).1
      have hmM := (Finset.mem_Icc.mp hm).2
      refine Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun p => ?_, haA⟩)
      have hp_prime := Nat.prime_of_mem_primeFactors p.2
      have hpe : p.1 ^ m.factorization p.1 ≤ M :=
        (Nat.le_of_dvd hm1 (Nat.ordProj_dvd m p.1)).trans hmM
      exact Finset.mem_range.mpr (exp_lt_of_prime_pow_le hp_prime hpe)
    · intro m₁ hm1 m₂ hm2 heq
      obtain ⟨hd1, _, _⟩ := hm_decomp m₁ hm1
      obtain ⟨hd2, _, _⟩ := hm_decomp m₂ hm2
      have hf_eq := congrArg Prod.fst heq
      have ha_eq := congrArg Prod.snd heq
      dsimp only at hf_eq ha_eq
      have hk_eq : (∏ p : d.primeFactors, p.1 ^ m₁.factorization p.1) =
          ∏ p : d.primeFactors, p.1 ^ m₂.factorization p.1 := by
        refine Finset.prod_congr rfl fun p _ => ?_
        have hfq := congrFun hf_eq p
        rw [hfq]
      calc m₁ = (∏ p : d.primeFactors, p.1 ^ m₁.factorization p.1) *
            (m₁ / ∏ p : d.primeFactors, p.1 ^ m₁.factorization p.1) := (Nat.mul_div_cancel' hd1).symm
        _ = (∏ p : d.primeFactors, p.1 ^ m₂.factorization p.1) *
            (m₂ / ∏ p : d.primeFactors, p.1 ^ m₂.factorization p.1) := congrArg₂ (· * ·) hk_eq ha_eq
        _ = m₂ := Nat.mul_div_cancel' hd2
    · intro m hm
      obtain ⟨_, _, heq⟩ := hm_decomp m hm
      exact le_of_eq heq.symm
  have hG_le : ∑ f ∈ G, ∏ p : d.primeFactors, (1 : ℝ) / (p.1 : ℝ) ^ (f p) ≤ weightW d := by
    have hprod_sum : ∑ f ∈ G, ∏ p : d.primeFactors, (1 : ℝ) / (p.1 : ℝ) ^ (f p) =
        ∏ p : d.primeFactors, ∑ e ∈ Finset.range (M + 1), (1 : ℝ) / (p.1 : ℝ) ^ e :=
      Finset.sum_prod_piFinset (Finset.range (M + 1)) (fun (p : d.primeFactors) (e : ℕ) => (1 : ℝ) / (p.1 : ℝ) ^ e)
    rw [hprod_sum]
    have hle := Finset.prod_le_prod (s := (Finset.univ : Finset d.primeFactors))
      (fun (p : d.primeFactors) _ => Finset.sum_nonneg fun _ _ => by positivity)
      (fun (p : d.primeFactors) _ => geom_sum_prime_le (Nat.prime_of_mem_primeFactors p.2) (M + 1))
    unfold weightW
    rw [← Finset.prod_coe_sort d.primeFactors (fun p => (p : ℝ) / ((p : ℝ) - 1))]
    exact hle
  calc ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ)
      ≤ ∑ fa ∈ G ×ˢ A, _ := hsum_le
    _ = (∑ f ∈ G, ∏ p : d.primeFactors, (1 : ℝ) / (p.1 : ℝ) ^ (f p)) *
          (∑ a ∈ A, (1 : ℝ) / (a : ℝ)) := hG_sum.symm
    _ ≤ weightW d * ∑ a ∈ A, (1 : ℝ) / (a : ℝ) :=
        mul_le_mul_of_nonneg_right hG_le (Finset.sum_nonneg fun _ _ => by positivity)

private lemma selbergS_lower {d R : ℕ} (hd : 2 ∣ d) (hd_pos : 0 < d) (hR : 1 ≤ R) :
    (Real.log (Nat.sqrt R) / weightW d) ^ 2 ≤ selbergS d R := by
  let M := Nat.sqrt R
  have hM1 : 1 ≤ M := Nat.le_sqrt.mpr (by simpa using hR)
  have hMM_R : M * M ≤ R := Nat.sqrt_le R
  let A := (Finset.Icc 1 M).filter (fun a => a.Coprime d)
  have hw_pos : 0 < weightW d := by
    unfold weightW
    refine Finset.prod_pos fun p hp => ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact div_pos (by linarith) (by linarith)
  have hlog_le : Real.log M / weightW d ≤ ∑ a ∈ A, (1 : ℝ) / (a : ℝ) := by
    rw [div_le_iff₀ hw_pos, mul_comm]
    exact (log_le_harmonic M hM1).trans (harmonic_coprime_lower hd_pos)
  have hlog_nn : 0 ≤ Real.log M / weightW d := by
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hM1)) hw_pos.le
  have hsq_le : (Real.log M / weightW d) ^ 2 ≤
      ∑ ab ∈ A ×ˢ A, (1 : ℝ) / ((ab.1 : ℝ) * (ab.2 : ℝ)) := by
    calc (Real.log M / weightW d) ^ 2 ≤ (∑ a ∈ A, (1 : ℝ) / (a : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hlog_nn hlog_le 2
      _ = ∑ ab ∈ A ×ˢ A, (1 : ℝ) / ((ab.1 : ℝ) * (ab.2 : ℝ)) := by
          rw [sq, Finset.sum_mul]
          simp_rw [Finset.mul_sum]
          rw [← Finset.sum_product']
          refine Finset.sum_congr rfl fun ab _ => by ring
  let rad : ℕ × ℕ → ℕ := fun ab => ∏ p ∈ (ab.1 * ab.2).primeFactors, p
  let Kset := (sqfreeUpTo R).filter (fun k => k.Coprime d)
  have hmap : ∀ ab ∈ A ×ˢ A, rad ab ∈ Kset := by
    rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    have ha_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
    have hb_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
    have ha_cop := (Finset.mem_filter.mp ha).2
    have hb_cop := (Finset.mem_filter.mp hb).2
    have hprod_pos : 0 < a * b := Nat.mul_pos ha_icc.1 hb_icc.1
    have hrad_pos : 0 < rad (a, b) :=
      Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    have hrad_dvd : rad (a, b) ∣ a * b := Nat.prod_primeFactors_dvd (a * b)
    have hrad_le : rad (a, b) ≤ R := by
      calc rad (a, b) ≤ a * b := Nat.le_of_dvd hprod_pos hrad_dvd
        _ ≤ M * M := Nat.mul_le_mul ha_icc.2 hb_icc.2
        _ ≤ R := hMM_R
    have hrad_sq : Squarefree (rad (a, b)) :=
      squarefree_prod_primes fun p hp => Nat.prime_of_mem_primeFactors hp
    have hrad_cop : (rad (a, b)).Coprime d := (ha_cop.mul_left hb_cop).coprime_dvd_left hrad_dvd
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hrad_pos, hrad_le⟩,
      hrad_sq⟩, hrad_cop⟩
  have hfiber :
      ∑ ab ∈ A ×ˢ A, (1 : ℝ) / ((ab.1 : ℝ) * (ab.2 : ℝ)) =
        ∑ k ∈ Kset, ∑ ab ∈ (A ×ˢ A).filter (fun ab => rad ab = k),
          (1 : ℝ) / ((ab.1 : ℝ) * (ab.2 : ℝ)) := by
    exact (Finset.sum_fiberwise_of_maps_to hmap _).symm
  have hle_K : ∑ k ∈ Kset, ∑ ab ∈ (A ×ˢ A).filter (fun ab => rad ab = k),
      (1 : ℝ) / ((ab.1 : ℝ) * (ab.2 : ℝ)) ≤ ∑ k ∈ Kset, (hD d k)⁻¹ := by
    refine Finset.sum_le_sum fun k hk => ?_
    obtain ⟨hk_sqf, hk_cop⟩ := Finset.mem_filter.mp hk
    exact rad_fiber_sum_le hd (Finset.mem_filter.mp hk_sqf).2 hk_cop
  have hle_S : ∑ k ∈ Kset, (hD d k)⁻¹ ≤ selbergS d R :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun k _ _ => inv_nonneg.mpr (hD_pos hd).le)
  exact hsq_le.trans (hfiber ▸ hle_K.trans hle_S)

private lemma sum_weightW_sq_le (H : ℕ) :
    ∑ d ∈ Finset.Icc 1 H, (weightW d) ^ 2 ≤ Real.exp 4 * (H : ℝ) := by
  let f : ℕ → ℝ := fun p => (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2
  have hterm_expand : ∀ d ∈ Finset.Icc 1 H,
      (weightW d) ^ 2 = ∑ q ∈ sqfreeUpTo H, if q ∣ d then ∏ p ∈ q.primeFactors, f p else 0 := by
    intro d hd_icc
    have hd_icc' := Finset.mem_Icc.mp hd_icc
    unfold weightW
    rw [← Finset.prod_pow]
    have hfac : ∀ p ∈ d.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 = 1 + f p := by
      intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      have hne : (p : ℝ) - 1 ≠ 0 := by linarith
      dsimp only [f]
      field_simp
      ring
    rw [Finset.prod_congr rfl hfac, Finset.prod_one_add]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun S _ => ∏ p ∈ S, p) ?_ ?_ ?_ ?_
    · intro S hS
      have hS' := Finset.mem_powerset.mp hS
      have hprod_pos : 0 < ∏ p ∈ S, p :=
        Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (hS' hp)).pos
      have hprod_dvd : ∏ p ∈ S, p ∣ d := by
        calc ∏ p ∈ S, p ∣ ∏ p ∈ d.primeFactors, p :=
              Finset.prod_dvd_prod_of_subset S d.primeFactors id hS'
          _ ∣ d := Nat.prod_primeFactors_dvd d
      have hprod_sq : Squarefree (∏ p ∈ S, p) :=
        squarefree_prod_primes fun p hp => Nat.prime_of_mem_primeFactors (hS' hp)
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hprod_pos, (Nat.le_of_dvd hd_icc'.1 hprod_dvd).trans hd_icc'.2⟩, hprod_sq⟩, hprod_dvd⟩
    · intro S₁ hS1 S₂ hS2 heq
      have h1 := Finset.mem_powerset.mp hS1
      have h2 := Finset.mem_powerset.mp hS2
      ext p
      constructor
      · intro hp
        have hpp := Nat.prime_of_mem_primeFactors (h1 hp)
        obtain ⟨x, hx, hpx⟩ := (hpp.prime.dvd_finsetProd_iff id).mp (heq ▸ Finset.dvd_prod_of_mem id hp)
        rcases (Nat.prime_of_mem_primeFactors (h2 hx)).eq_one_or_self_of_dvd p hpx with h | h
        · exact absurd h hpp.ne_one
        · rwa [h]
      · intro hp
        have hpp := Nat.prime_of_mem_primeFactors (h2 hp)
        obtain ⟨x, hx, hpx⟩ := (hpp.prime.dvd_finsetProd_iff id).mp (heq.symm ▸ Finset.dvd_prod_of_mem id hp)
        rcases (Nat.prime_of_mem_primeFactors (h1 hx)).eq_one_or_self_of_dvd p hpx with h | h
        · exact absurd h hpp.ne_one
        · rwa [h]
    · intro q hq
      obtain ⟨hq_sqf, hqd⟩ := Finset.mem_filter.mp hq
      have hq_sq := (Finset.mem_filter.mp hq_sqf).2
      refine ⟨q.primeFactors, Finset.mem_powerset.mpr ?_, sqfree_prod_primeFactors hq_sq⟩
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hd_ne : d ≠ 0 := by omega
      exact Nat.mem_primeFactors.mpr ⟨hpp, (Nat.dvd_of_mem_primeFactors hp).trans hqd, hd_ne⟩
    · intro S hS
      have hS' := Finset.mem_powerset.mp hS
      have hpf : (∏ p ∈ S, p).primeFactors = S := by
        ext p
        simp only [Nat.mem_primeFactors, ne_eq, (Finset.prod_pos fun x hx =>
          (Nat.prime_of_mem_primeFactors (hS' hx)).pos).ne', not_false_eq_true, and_true]
        constructor
        · rintro ⟨hp, hpd⟩
          obtain ⟨x, hx, hpx⟩ := (hp.prime.dvd_finsetProd_iff id).mp hpd
          rcases (Nat.prime_of_mem_primeFactors (hS' hx)).eq_one_or_self_of_dvd p hpx with h | h
          · exact absurd h hp.ne_one
          · rwa [h]
        · intro hp
          exact ⟨Nat.prime_of_mem_primeFactors (hS' hp), Finset.dvd_prod_of_mem id hp⟩
      rw [hpf]
  have hswap : ∑ d ∈ Finset.Icc 1 H, (weightW d) ^ 2 ≤
      (H : ℝ) * ∑ q ∈ sqfreeUpTo H, ∏ p ∈ q.primeFactors, (f p / (p : ℝ)) := by
    rw [Finset.sum_congr rfl hterm_expand, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    have hq_sq := (Finset.mem_filter.mp hq).2
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard_le : (((Finset.Icc 1 H).filter (fun d => q ∣ d)).card : ℝ) ≤ (H : ℝ) / (q : ℝ) := by
      have h1 : ((Finset.Icc 1 H).filter (fun d => q ∣ d)).card ≤ (Finset.Icc 1 (H / q)).card := by
        refine Finset.card_le_card_of_injOn (fun d => d / q) ?_ ?_
        · intro d hd
          obtain ⟨hd_icc, hqd⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hd)
          have hd_icc' := Finset.mem_Icc.mp hd_icc
          exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr
            ⟨Nat.div_pos (Nat.le_of_dvd hd_icc'.1 hqd) hq_icc.1, Nat.div_le_div_right hd_icc'.2⟩)
        · intro d₁ hd₁ d₂ hd₂ heq
          have heq' : d₁ / q = d₂ / q := heq
          have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hd₁)).2
          have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hd₂)).2
          have hm1 := Nat.mul_div_cancel' h1
          have hm2 := Nat.mul_div_cancel' h2
          rw [← hm1, ← hm2, heq']
      have hcard : (Finset.Icc 1 (H / q)).card = H / q := by simp
      calc (((Finset.Icc 1 H).filter (fun d => q ∣ d)).card : ℝ) ≤ ((H / q : ℕ) : ℝ) := by
            exact_mod_cast (h1.trans_eq hcard)
        _ ≤ (H : ℝ) / (q : ℝ) := Nat.cast_div_le
    have hq_prod : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
      conv_lhs => rw [← sqfree_prod_primeFactors hq_sq]
      push_cast; rfl
    have hfp_nn : 0 ≤ ∏ p ∈ q.primeFactors, f p := by
      refine Finset.prod_nonneg fun p hp => ?_
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      dsimp only [f]
      exact div_nonneg (by linarith) (sq_nonneg _)
    calc (((Finset.Icc 1 H).filter (fun d => q ∣ d)).card : ℝ) * ∏ p ∈ q.primeFactors, f p
        ≤ ((H : ℝ) / (q : ℝ)) * ∏ p ∈ q.primeFactors, f p :=
          mul_le_mul_of_nonneg_right hcard_le hfp_nn
      _ = (H : ℝ) * ((∏ p ∈ q.primeFactors, f p) / (q : ℝ)) := by ring
      _ = (H : ℝ) * ∏ p ∈ q.primeFactors, (f p / (p : ℝ)) := by
          rw [hq_prod, ← Finset.prod_div_distrib]
  let Pset := (Finset.Icc 2 H).filter Nat.Prime
  have hsqf_le_pow : ∑ q ∈ sqfreeUpTo H, ∏ p ∈ q.primeFactors, (f p / (p : ℝ)) ≤
      ∏ p ∈ Pset, (1 + f p / (p : ℝ)) := by
    rw [Finset.prod_one_add]
    refine sum_le_sum_of_injOn (fun q => q.primeFactors) ?_ ?_ ?_ (fun S hS => ?_)
    · intro q hq
      have hq_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
      refine Finset.mem_coe.mpr (Finset.mem_powerset.mpr fun p hp => ?_)
      have hpp := Nat.prime_of_mem_primeFactors hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.two_le,
        (Nat.le_of_dvd hq_icc.1 (Nat.dvd_of_mem_primeFactors hp)).trans hq_icc.2⟩, hpp⟩
    · intro q₁ hq₁ q₂ hq₂ heq
      have heq' : q₁.primeFactors = q₂.primeFactors := heq
      have h1 := (Finset.mem_filter.mp hq₁).2
      have h2 := (Finset.mem_filter.mp hq₂).2
      rw [← sqfree_prod_primeFactors h1, ← sqfree_prod_primeFactors h2, heq']
    · intro q _
      exact le_rfl
    · refine Finset.prod_nonneg fun p hp => ?_
      have hp2 : (2 : ℝ) ≤ p := by
        exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_powerset.mp (Finset.mem_coe.mp hS) hp)).1).1
      dsimp only [f]
      exact div_nonneg (div_nonneg (by linarith) (sq_nonneg _)) (by linarith)
  have htel : ∀ M : ℕ, ∑ m ∈ Finset.Icc 2 M, ((1 : ℝ) / ((m : ℝ) - 1) - (1 : ℝ) / (m : ℝ)) ≤ 1 := by
    intro M
    have hval : ∀ k : ℕ,
        ∑ m ∈ Finset.Icc 2 k, ((1 : ℝ) / ((m : ℝ) - 1) - (1 : ℝ) / (m : ℝ)) =
          if k ≤ 1 then 0 else 1 - (1 : ℝ) / (k : ℝ) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        by_cases hk1 : k ≤ 1
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with rfl | rfl
          · simp
          · simp; norm_num
        · have hk2 : 2 ≤ k := by omega
          have hsplit : Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hsplit, Finset.sum_insert (by simp), ih, if_neg hk1, if_neg (by omega : ¬ k + 1 ≤ 1)]
          push_cast
          ring
    rw [hval M]
    split_ifs
    · norm_num
    · have hM_pos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
      linarith [div_pos one_pos hM_pos]
  have hP_le : ∏ p ∈ Pset, (1 + f p / (p : ℝ)) ≤ Real.exp 4 := by
    calc ∏ p ∈ Pset, (1 + f p / (p : ℝ))
        ≤ ∏ p ∈ Pset, Real.exp (f p / (p : ℝ)) := by
            refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
            · have hp2 : (2 : ℝ) ≤ p := by
                exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
              dsimp only [f]
              have hnn : 0 ≤ (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 / (p : ℝ) :=
                div_nonneg (div_nonneg (by linarith) (sq_nonneg _)) (by linarith)
              linarith
            · linarith [Real.add_one_le_exp (f p / (p : ℝ))]
      _ = Real.exp (∑ p ∈ Pset, f p / (p : ℝ)) := (Real.exp_sum Pset _).symm
      _ ≤ Real.exp 4 := by
          refine Real.exp_le_exp.mpr ?_
          have hsub : ∑ p ∈ Pset, f p / (p : ℝ) ≤ ∑ m ∈ Finset.Icc 2 H, f m / (m : ℝ) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun m hm _ => ?_
            have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
            dsimp only [f]
            exact div_nonneg (div_nonneg (by linarith) (sq_nonneg _)) (by linarith)
          have hterm : ∑ m ∈ Finset.Icc 2 H, f m / (m : ℝ) ≤
              4 * ∑ m ∈ Finset.Icc 2 H, ((1 : ℝ) / ((m : ℝ) - 1) - (1 : ℝ) / (m : ℝ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun m hm => ?_
            have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
            have hm1_ne : (m : ℝ) - 1 ≠ 0 := by linarith
            have hm_ne : (m : ℝ) ≠ 0 := by linarith
            dsimp only [f]
            have hrhs : 4 * ((1 : ℝ) / ((m : ℝ) - 1) - (1 : ℝ) / (m : ℝ)) =
                (4 * ((m : ℝ) - 1)) / (((m : ℝ) - 1) ^ 2 * (m : ℝ)) := by
              field_simp; ring
            rw [div_div, hrhs]
            exact div_le_div_of_nonneg_right (by linarith) (by positivity)
          exact hsub.trans (hterm.trans (by linarith [htel H]))
  calc ∑ d ∈ Finset.Icc 1 H, (weightW d) ^ 2
      ≤ (H : ℝ) * ∑ q ∈ sqfreeUpTo H, ∏ p ∈ q.primeFactors, (f p / (p : ℝ)) := hswap
    _ ≤ (H : ℝ) * ∏ p ∈ Pset, (1 + f p / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqf_le_pow (Nat.cast_nonneg _)
    _ ≤ (H : ℝ) * Real.exp 4 := mul_le_mul_of_nonneg_left hP_le (Nat.cast_nonneg _)
    _ = Real.exp 4 * (H : ℝ) := mul_comm _ _

/- ### Section 4: Close Prime Pairs Bound -/

private lemma odd_shifted_primes_le (d N : ℕ) (hd : ¬ 2 ∣ d) :
    ((Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro p₁ hp₁ p₂ hp₂
  have htwo : ∀ p ∈ (Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime), p = 2 := by
    intro p hp
    obtain ⟨_, hp_prime, hpd_prime⟩ := Finset.mem_filter.mp hp
    rcases hp_prime.eq_two_or_odd with rfl | hp_odd
    · rfl
    · exfalso
      have hd_mod : d % 2 = 1 := Nat.mod_two_ne_zero.mp fun h => hd (Nat.dvd_of_mod_eq_zero h)
      have hpd_even : 2 ∣ p + d := Nat.dvd_of_mod_eq_zero (by omega)
      have hpd_gt : 2 < p + d := by
        have hp2 : 2 ≤ p := hp_prime.two_le
        have hp3 : 3 ≤ p := by omega
        have hd1 : 1 ≤ d := by
          by_contra h0
          have : d = 0 := by omega
          subst this; simp at hd
        omega
      rcases hpd_prime.eq_two_or_odd with h2 | hodd
      · omega
      · have hmod := Nat.dvd_iff_mod_eq_zero.mp hpd_even
        omega
  rw [htwo p₁ hp₁, htwo p₂ hp₂]

private lemma close_prime_pairs_bound {X : ℝ} (hX : (2 : ℝ) ^ 96 ≤ X) (H : ℕ) :
    ((((Finset.Icc 1 ⌊X⌋₊ ×ˢ Finset.Icc 1 ⌊X⌋₊).filter
        (fun pq => pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ H))).card : ℝ) ≤
      (256 * Real.exp 4 + 1) * (H : ℝ) * X / (Real.log X) ^ 2 := by
  have hX_pos : 0 < X := lt_of_lt_of_le (by positivity) hX
  have hX_gt1 : 1 < X := (one_lt_pow₀ (by norm_num) (by norm_num) : (1 : ℝ) < (2 : ℝ) ^ 96).trans_le hX
  have hlogX_pos : 0 < Real.log X := Real.log_pos hX_gt1
  rcases eq_or_ne H 0 with rfl | hH_ne
  · have h_empty :
        ((Finset.Icc 1 ⌊X⌋₊ ×ˢ Finset.Icc 1 ⌊X⌋₊).filter
          (fun pq => pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ 0)) = ∅ := by
      ext ⟨p, q⟩
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _ _ _ hpq hsub
      omega
    rw [h_empty]
    simp
  let N := ⌊X⌋₊
  let pairs := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
    (fun pq => pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ H)
  have hmap_sub : pairs.card ≤
      ∑ d ∈ Finset.Icc 1 H, ((Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).card := by
    have hbi : pairs.card ≤
        ((Finset.Icc 1 H).biUnion (fun d =>
          ((Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).image
            (fun p => (p, p + d)))).card := by
      refine Finset.card_le_card ?_
      rintro ⟨p, q⟩ hpq
      simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
        Finset.mem_image, Finset.mem_Icc] at hpq ⊢
      refine ⟨q - p, ⟨by omega, hpq.2.2.2.2⟩, p, ⟨hpq.1.1, hpq.2.1, ?_⟩, ?_⟩
      · have heq : p + (q - p) = q := by omega
        rw [heq]; exact hpq.2.2.1
      · (ext <;> simp); all_goals omega
    calc pairs.card
        ≤ ((Finset.Icc 1 H).biUnion (fun d =>
            ((Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).image
              (fun p => (p, p + d)))).card := hbi
      _ ≤ ∑ d ∈ Finset.Icc 1 H,
            (((Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).image
              (fun p => (p, p + d))).card := Finset.card_biUnion_le
      _ ≤ ∑ d ∈ Finset.Icc 1 H,
            ((Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).card := by
          refine Finset.sum_le_sum fun d _ => Finset.card_image_le
  let R := ⌊X ^ (1 / 4 : ℝ)⌋₊
  have hX14_ge : (2 : ℝ) ^ 24 ≤ X ^ (1 / 4 : ℝ) := by
    have hpow : (2 : ℝ) ^ 24 = ((2 : ℝ) ^ 96) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast (2 : ℝ) 24, ← Real.rpow_natCast (2 : ℝ) 96,
        ← Real.rpow_mul (by positivity)]
      norm_num
    exact hpow.trans_le (Real.rpow_le_rpow (by positivity) hX (by norm_num))
  have hR_ge : 2 ^ 24 ≤ R :=
    Nat.le_floor (show ((2 ^ 24 : ℕ) : ℝ) ≤ X ^ (1 / 4 : ℝ) by
      simp only [Nat.cast_pow, Nat.cast_ofNat]; exact hX14_ge)
  have hR_pos : 1 ≤ R := le_trans (by norm_num) hR_ge
  have hR_real_pos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR_pos
  have hR_le_X14 : (R : ℝ) ≤ X ^ (1 / 4 : ℝ) := Nat.floor_le (by positivity)
  have hX_div_logsq_ge1 : 1 ≤ X / (Real.log X) ^ 2 := by
    rw [one_le_div (sq_pos_of_pos hlogX_pos)]
    have hls := OMA.R_Erdos912_erdos_912_R2.log_le_sqrt hX_pos
    calc (Real.log X) ^ 2 ≤ (√X) ^ 2 := pow_le_pow_left₀ hlogX_pos.le hls 2
      _ = X := Real.sq_sqrt hX_pos.le
  have hlog96 : 96 * Real.log 2 ≤ Real.log X := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ 96) hX
    rwa [Real.log_pow] at h
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM_log : (1 / 16 : ℝ) * Real.log X ≤ Real.log (Nat.sqrt R : ℝ) := by
    let M := Nat.sqrt R
    have hM1 : 1 ≤ M := Nat.le_sqrt.mpr (by simpa using hR_pos)
    have hlt1 : X ^ (1 / 4 : ℝ) < ((M : ℝ) + 1) ^ 2 := by
      have h1 : X ^ (1 / 4 : ℝ) < (R : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : R < (M + 1) * (M + 1) := Nat.lt_succ_sqrt R
      have h2r : (R : ℝ) + 1 ≤ ((M : ℝ) + 1) ^ 2 := by
        have hnat : R + 1 ≤ (M + 1) * (M + 1) := h2
        have hr : ((R + 1 : ℕ) : ℝ) ≤ (((M + 1) * (M + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
        push_cast at hr
        nlinarith
      exact h1.trans_le h2r
    have hX18_sq : (X ^ (1 / 8 : ℝ)) ^ 2 = X ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast (X ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul hX_pos.le]
      norm_num
    have hlt2 : X ^ (1 / 8 : ℝ) < (M : ℝ) + 1 := by
      by_contra h
      push Not at h
      have hsq : ((M : ℝ) + 1) ^ 2 ≤ (X ^ (1 / 8 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
      linarith [hX18_sq]
    have hM2 : (M : ℝ) + 1 ≤ 2 * (M : ℝ) := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
      linarith
    have hX18_half : X ^ (1 / 8 : ℝ) / 2 ≤ (M : ℝ) := by linarith
    have hlogM : Real.log (X ^ (1 / 8 : ℝ) / 2) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (by positivity) hX18_half
    have hlog_eq : Real.log (X ^ (1 / 8 : ℝ) / 2) = (1 / 8 : ℝ) * Real.log X - Real.log 2 := by
      rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hX_pos]
    have hlog2_le : Real.log 2 ≤ (1 / 16 : ℝ) * Real.log X := by linarith
    linarith
  have herr_le : (R : ℝ) + ((R : ℝ) * (Real.log R + 1)) ^ 2 ≤ X / (Real.log X) ^ 2 := by
    have hlogR_le : Real.log (R : ℝ) ≤ (1 / 4 : ℝ) * Real.log X := by
      have h1 : Real.log (R : ℝ) ≤ Real.log (X ^ (1 / 4 : ℝ)) :=
        Real.log_le_log hR_real_pos hR_le_X14
      rwa [Real.log_rpow hX_pos] at h1
    have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogX_gt48 : 48 < Real.log X := by linarith
    have hlogR1 : Real.log (R : ℝ) + 1 ≤ (1 / 2 : ℝ) * Real.log X := by linarith
    have hR14_pos : 0 ≤ (R : ℝ) * (Real.log (R : ℝ) + 1) := by
      have : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR_pos)
      positivity
    have hsq1 : ((R : ℝ) * (Real.log (R : ℝ) + 1)) ^ 2 ≤
        (1 / 4 : ℝ) * X ^ (1 / 2 : ℝ) * (Real.log X) ^ 2 := by
      have hprod : (R : ℝ) * (Real.log (R : ℝ) + 1) ≤ X ^ (1 / 4 : ℝ) * ((1 / 2 : ℝ) * Real.log X) :=
        mul_le_mul hR_le_X14 hlogR1 (by linarith [Real.log_nonneg (by exact_mod_cast hR_pos : (1 : ℝ) ≤ R)]) (by positivity)
      have hsq' := pow_le_pow_left₀ hR14_pos hprod 2
      have hX14_sq : (X ^ (1 / 4 : ℝ)) ^ 2 = X ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast (X ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hX_pos.le]
        norm_num
      calc ((R : ℝ) * (Real.log (R : ℝ) + 1)) ^ 2
          ≤ (X ^ (1 / 4 : ℝ) * ((1 / 2 : ℝ) * Real.log X)) ^ 2 := hsq'
        _ = (X ^ (1 / 4 : ℝ)) ^ 2 * ((1 / 4 : ℝ) * (Real.log X) ^ 2) := by ring
        _ = (1 / 4 : ℝ) * X ^ (1 / 2 : ℝ) * (Real.log X) ^ 2 := by rw [hX14_sq]; ring
    have hR_le_main : (R : ℝ) ≤ (1 / 4 : ℝ) * X ^ (1 / 2 : ℝ) * (Real.log X) ^ 2 := by
      have hX14_le_12 : X ^ (1 / 4 : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have h14log : 1 ≤ (1 / 4 : ℝ) * (Real.log X) ^ 2 := by nlinarith
      calc (R : ℝ) ≤ X ^ (1 / 4 : ℝ) := hR_le_X14
        _ ≤ X ^ (1 / 2 : ℝ) := hX14_le_12
        _ = X ^ (1 / 2 : ℝ) * 1 := (mul_one _).symm
        _ ≤ X ^ (1 / 2 : ℝ) * ((1 / 4 : ℝ) * (Real.log X) ^ 2) :=
            mul_le_mul_of_nonneg_left h14log (by positivity)
        _ = (1 / 4 : ℝ) * X ^ (1 / 2 : ℝ) * (Real.log X) ^ 2 := by ring
    have hlogX_16 : Real.log X ≤ 16 * X ^ (1 / 32 : ℝ) := by
      have hls := OMA.R_Erdos912_erdos_912_R2.log_le_sqrt (by positivity : 0 < X ^ (1 / 16 : ℝ))
      rw [Real.log_rpow hX_pos, Real.sqrt_eq_rpow, ← Real.rpow_mul hX_pos.le] at hls
      have hmul : (1 / 16 : ℝ) * (1 / 2 : ℝ) = 1 / 32 := by norm_num
      rw [hmul] at hls
      linarith
    have hlogX4 : (Real.log X) ^ 4 ≤ (2 : ℝ) ^ 16 * X ^ (1 / 8 : ℝ) := by
      have h4 := pow_le_pow_left₀ hlogX_pos.le hlogX_16 4
      have hr : (X ^ (1 / 32 : ℝ)) ^ 4 = X ^ (1 / 8 : ℝ) := by
        rw [← Real.rpow_natCast (X ^ (1 / 32 : ℝ)) 4, ← Real.rpow_mul hX_pos.le]
        norm_num
      have h216 : (16 : ℝ) ^ 4 = (2 : ℝ) ^ 16 := by norm_num
      calc (Real.log X) ^ 4 ≤ (16 * X ^ (1 / 32 : ℝ)) ^ 4 := h4
        _ = (16 : ℝ) ^ 4 * (X ^ (1 / 32 : ℝ)) ^ 4 := by ring
        _ = (2 : ℝ) ^ 16 * X ^ (1 / 8 : ℝ) := by rw [hr, h216]
    have hX38 : (2 : ℝ) ^ 36 ≤ X ^ (3 / 8 : ℝ) := by
      have hpow : (2 : ℝ) ^ 36 = ((2 : ℝ) ^ 96) ^ (3 / 8 : ℝ) := by
        rw [← Real.rpow_natCast (2 : ℝ) 36, ← Real.rpow_natCast (2 : ℝ) 96,
          ← Real.rpow_mul (by positivity)]
        norm_num
      exact hpow.trans_le (Real.rpow_le_rpow (by positivity) hX (by norm_num))
    have h216_36 : (2 : ℝ) ^ 16 ≤ (2 : ℝ) ^ 36 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have hlogX4_le : (Real.log X) ^ 4 ≤ X ^ (1 / 2 : ℝ) := by
      calc (Real.log X) ^ 4 ≤ (2 : ℝ) ^ 16 * X ^ (1 / 8 : ℝ) := hlogX4
        _ ≤ X ^ (3 / 8 : ℝ) * X ^ (1 / 8 : ℝ) :=
            mul_le_mul_of_nonneg_right (h216_36.trans hX38) (by positivity)
        _ = X ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_add hX_pos]
            norm_num
    have hX12_sq : X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) = X := by
      rw [← Real.rpow_add hX_pos]
      norm_num
    have hfinal_alg : (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) * (Real.log X) ^ 2 ≤ X / (Real.log X) ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hlogX_pos)]
      calc (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) * (Real.log X) ^ 2 * (Real.log X) ^ 2
          = (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) * (Real.log X) ^ 4 := by ring
        _ ≤ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hlogX4_le (by positivity)
        _ = (1 / 2 : ℝ) * X := by rw [mul_assoc, hX12_sq]
        _ ≤ X := by linarith
    linarith
  have hd_bound : ∀ d ∈ Finset.Icc 1 H,
      (((Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ) ≤
        (256 * (weightW d) ^ 2 + 1) * X / (Real.log X) ^ 2 := by
    intro d hd_icc
    have hd_pos : 0 < d := (Finset.mem_Icc.mp hd_icc).1
    by_cases hd2 : 2 ∣ d
    · have hsieve := sieve_shifted_primes_bound (d := d) (N := N) (R := R) hd2 hR_pos
      have hS_lb := selbergS_lower hd2 hd_pos hR_pos
      have hw_pos : 0 < weightW d := by
        unfold weightW
        refine Finset.prod_pos fun p hp => ?_
        have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
        exact div_pos (by linarith) (by linarith)
      have hS_pos : 0 < selbergS d R := selbergS_pos hd2 hR_pos
      have hS_lb2 : (Real.log X) ^ 2 / (256 * (weightW d) ^ 2) ≤ selbergS d R := by
        have h1 : ((1 / 16 : ℝ) * Real.log X / weightW d) ^ 2 ≤ (Real.log (Nat.sqrt R : ℝ) / weightW d) ^ 2 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          exact div_le_div_of_nonneg_right hM_log hw_pos.le
        have h2 : ((1 / 16 : ℝ) * Real.log X / weightW d) ^ 2 = (Real.log X) ^ 2 / (256 * (weightW d) ^ 2) := by
          ring
        linarith
      have hN_le : (N : ℝ) ≤ X := Nat.floor_le hX_pos.le
      have hN_S : (N : ℝ) / selbergS d R ≤ 256 * (weightW d) ^ 2 * X / (Real.log X) ^ 2 := by
        calc (N : ℝ) / selbergS d R
            ≤ X / selbergS d R := div_le_div_of_nonneg_right hN_le hS_pos.le
          _ ≤ X / ((Real.log X) ^ 2 / (256 * (weightW d) ^ 2)) :=
              div_le_div_of_nonneg_left hX_pos.le (by positivity) hS_lb2
          _ = 256 * (weightW d) ^ 2 * X / (Real.log X) ^ 2 := by
              rw [div_div_eq_mul_div]; ring
      calc (((Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)
          ≤ (R : ℝ) + (N : ℝ) / selbergS d R + ((R : ℝ) * (Real.log R + 1)) ^ 2 := hsieve
        _ ≤ 256 * (weightW d) ^ 2 * X / (Real.log X) ^ 2 + X / (Real.log X) ^ 2 := by linarith
        _ = (256 * (weightW d) ^ 2 + 1) * X / (Real.log X) ^ 2 := by ring
    · have hodd : (((Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ) ≤ 1 := by
        exact_mod_cast odd_shifted_primes_le d N hd2
      have hnonneg : 0 ≤ 256 * (weightW d) ^ 2 * X / (Real.log X) ^ 2 := by positivity
      have hsplit : (256 * (weightW d) ^ 2 + 1) * X / (Real.log X) ^ 2 =
          256 * (weightW d) ^ 2 * X / (Real.log X) ^ 2 + X / (Real.log X) ^ 2 := by ring
      calc (((Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)
          ≤ 1 := hodd
        _ ≤ X / (Real.log X) ^ 2 := hX_div_logsq_ge1
        _ ≤ (256 * (weightW d) ^ 2 + 1) * X / (Real.log X) ^ 2 := by linarith [hsplit]
  have hsum_d :
      (∑ d ∈ Finset.Icc 1 H,
        (((Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)) ≤
      (256 * Real.exp 4 + 1) * (H : ℝ) * X / (Real.log X) ^ 2 := by
    calc ∑ d ∈ Finset.Icc 1 H,
          (((Finset.Icc 1 N).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)
        ≤ ∑ d ∈ Finset.Icc 1 H, (256 * (weightW d) ^ 2 + 1) * X / (Real.log X) ^ 2 :=
            Finset.sum_le_sum hd_bound
      _ = (256 * (∑ d ∈ Finset.Icc 1 H, (weightW d) ^ 2) + (H : ℝ)) * X / (Real.log X) ^ 2 := by
            rw [← Finset.sum_div, ← Finset.sum_mul]
            congr 1
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc]
            simp [nsmul_eq_mul]
      _ ≤ (256 * (Real.exp 4 * (H : ℝ)) + (H : ℝ)) * X / (Real.log X) ^ 2 := by
            gcongr
            exact sum_weightW_sq_le H
      _ = (256 * Real.exp 4 + 1) * (H : ℝ) * X / (Real.log X) ^ 2 := by ring
  exact (by exact_mod_cast hmap_sub : (pairs.card : ℝ) ≤ _).trans hsum_d

/- ### Section 5: Energy Bound and Main Theorem -/

private lemma energy_le {Pset : Finset ℕ} {f : ℕ → ℕ} :
    (Pset.card : ℝ) ^ 2 ≤ ((Pset.image f).card : ℝ) *
      ((Pset.card : ℝ) +
        2 * (((Pset ×ˢ Pset).filter (fun pq => pq.1 < pq.2 ∧ f pq.1 = f pq.2)).card : ℝ)) := by
  let img := Pset.image f
  have hcard_sum : (Pset.card : ℝ) = ∑ k ∈ img, ((Pset.filter (fun p => f p = k)).card : ℝ) := by
    have heq_set : Pset = img.biUnion (fun k => Pset.filter (fun p => f p = k)) := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, img]
      constructor
      · intro hp; exact ⟨f p, ⟨p, hp, rfl⟩, hp, rfl⟩
      · rintro ⟨_, _, hp, _⟩; exact hp
    have hdisj : Set.PairwiseDisjoint (img : Set ℕ) (fun k => Pset.filter (fun p => f p = k)) := by
      intro k₁ _ k₂ _ hne
      refine Finset.disjoint_left.mpr fun p hp1 hp2 => ?_
      have h1 := (Finset.mem_filter.mp hp1).2
      have h2 := (Finset.mem_filter.mp hp2).2
      exact hne (h1.symm.trans h2)
    have hnat : Pset.card = ∑ k ∈ img, (Pset.filter (fun p => f p = k)).card :=
      (congrArg Finset.card heq_set).trans (Finset.card_biUnion hdisj)
    exact_mod_cast hnat
  have hcs : (Pset.card : ℝ) ^ 2 ≤ (img.card : ℝ) *
      ∑ k ∈ img, ((Pset.filter (fun p => f p = k)).card : ℝ) ^ 2 := by
    rw [hcard_sum]
    simpa [mul_comm] using
      (sq_sum_le_card_mul_sum_sq (s := img) (f := fun k => ((Pset.filter (fun p => f p = k)).card : ℝ)))
  have hfib_eq : ∑ k ∈ img, ((Pset.filter (fun p => f p = k)).card : ℝ) ^ 2 =
      (((Pset ×ˢ Pset).filter (fun pq => f pq.1 = f pq.2)).card : ℝ) := by
    have hnat : ∑ k ∈ img, (Pset.filter (fun p => f p = k)).card ^ 2 =
        ((Pset ×ˢ Pset).filter (fun pq => f pq.1 = f pq.2)).card := by
      have hsq : ∀ k ∈ img, (Pset.filter (fun p => f p = k)).card ^ 2 =
          ((Pset ×ˢ Pset).filter (fun pq => f pq.1 = k ∧ f pq.2 = k)).card := by
        intro k _
        rw [sq, ← Finset.card_product]
        refine congrArg Finset.card ?_
        ext ⟨p, q⟩
        simp only [Finset.mem_product, Finset.mem_filter]
        tauto
      have heq_set : (img.biUnion (fun k => (Pset ×ˢ Pset).filter (fun pq => f pq.1 = k ∧ f pq.2 = k))) =
          (Pset ×ˢ Pset).filter (fun pq => f pq.1 = f pq.2) := by
        ext ⟨p, q⟩
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_image, img]
        constructor
        · rintro ⟨k, _, ⟨hp, hq⟩, hfp, hfq⟩
          exact ⟨⟨hp, hq⟩, hfp.trans hfq.symm⟩
        · rintro ⟨⟨hp, hq⟩, heq⟩
          exact ⟨f p, ⟨p, hp, rfl⟩, ⟨hp, hq⟩, rfl, heq.symm⟩
      have hdisj : Set.PairwiseDisjoint (img : Set ℕ)
          (fun k => (Pset ×ˢ Pset).filter (fun pq => f pq.1 = k ∧ f pq.2 = k)) := by
        intro k₁ _ k₂ _ hne
        refine Finset.disjoint_left.mpr fun pq hp1 hp2 => ?_
        exact hne ((Finset.mem_filter.mp hp1).2.1.symm.trans (Finset.mem_filter.mp hp2).2.1)
      rw [Finset.sum_congr rfl hsq, ← Finset.card_biUnion hdisj, heq_set]
    exact_mod_cast hnat
  have hpart : ((Pset ×ˢ Pset).filter (fun pq => f pq.1 = f pq.2)).card ≤
      Pset.card + 2 * ((Pset ×ˢ Pset).filter (fun pq => pq.1 < pq.2 ∧ f pq.1 = f pq.2)).card := by
    let S_all := (Pset ×ˢ Pset).filter (fun pq => f pq.1 = f pq.2)
    let S_diag := Pset.image (fun p => (p, p))
    let S_lt := (Pset ×ˢ Pset).filter (fun pq => pq.1 < pq.2 ∧ f pq.1 = f pq.2)
    let S_gt := S_lt.image (fun pq => (pq.2, pq.1))
    have hsub : S_all ⊆ S_diag ∪ (S_lt ∪ S_gt) := by
      rintro ⟨p, q⟩ hpq
      obtain ⟨hpq_prod, hfpq⟩ := Finset.mem_filter.mp hpq
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq_prod
      rcases lt_trichotomy p q with hlt | rfl | hgt
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hlt, hfpq⟩))
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨(q, p), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hq, hp⟩, hgt, hfpq.symm⟩, rfl⟩))
    calc S_all.card ≤ (S_diag ∪ (S_lt ∪ S_gt)).card := Finset.card_le_card hsub
      _ ≤ S_diag.card + (S_lt.card + S_gt.card) :=
          (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)
      _ ≤ Pset.card + (S_lt.card + S_lt.card) :=
          Nat.add_le_add Finset.card_image_le (Nat.add_le_add_left Finset.card_image_le _)
      _ = Pset.card + 2 * S_lt.card := by ring
  have hreal : (((Pset ×ˢ Pset).filter (fun pq => f pq.1 = f pq.2)).card : ℝ) ≤
      (Pset.card : ℝ) +
        2 * (((Pset ×ˢ Pset).filter (fun pq => pq.1 < pq.2 ∧ f pq.1 = f pq.2)).card : ℝ) := by
    exact_mod_cast hpart
  calc (Pset.card : ℝ) ^ 2
      ≤ (img.card : ℝ) * ∑ k ∈ img, ((Pset.filter (fun p => f p = k)).card : ℝ) ^ 2 := hcs
    _ = (img.card : ℝ) * (((Pset ×ˢ Pset).filter (fun pq => f pq.1 = f pq.2)).card : ℝ) := by
        rw [hfib_eq]
    _ ≤ (img.card : ℝ) * ((Pset.card : ℝ) +
          2 * (((Pset ×ˢ Pset).filter (fun pq => pq.1 < pq.2 ∧ f pq.1 = f pq.2)).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hreal (Nat.cast_nonneg _)

private lemma sqrt_mul_div_eq_sqrt_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    √(a * b) / b = √(a / b) := by
  rw [Real.sqrt_mul ha.le, Real.sqrt_div ha.le]
  conv_lhs => arg 2; rw [← Real.mul_self_sqrt hb.le]
  exact mul_div_mul_right _ _ (Real.sqrt_pos.mpr hb).ne'

private lemma close_algebra_bound {cS H X L logX sqnL : ℝ}
    (hcS : 0 ≤ cS) (hX : 0 < X) (hL : 0 < L)
    (hH : H ≤ 2 * L) (hlogX : (1 / 2 : ℝ) * L ≤ logX) (hdiv : X / L = sqnL) :
    cS * H * X / logX ^ 2 ≤ 8 * cS * sqnL := by
  calc cS * H * X / logX ^ 2
      ≤ cS * (2 * L) * X / ((1 / 2 : ℝ) * L) ^ 2 := by
          refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH hcS) hX.le
          · exact pow_le_pow_left₀ (by positivity) hlogX 2
    _ = (8 * cS * X * L) / (L * L) := by ring
    _ = (8 * cS * X) / L := mul_div_mul_right _ _ hL.ne'
    _ = 8 * cS * sqnL := by rw [← hdiv]; ring

private lemma large_n_window_facts {n : ℕ} (hn_exp : Real.exp 6600 ≤ (n : ℝ)) :
    let X : ℝ := √((n : ℝ) * Real.log (n : ℝ))
    let Y : ℝ := √(n : ℝ)
    (6601 : ℝ) ≤ (n : ℝ) ∧
    (6600 : ℝ) ≤ Real.log (n : ℝ) ∧
    (1024 : ℝ) ≤ X ∧
    1 < Y ∧
    (2 : ℝ) ^ 96 ≤ X ∧
    Y ≤ X ∧
    X ≤ (n : ℝ) / 2 := by
  intro X Y
  have hn_ge_6601 : (6601 : ℝ) ≤ (n : ℝ) :=
    (by linarith [Real.add_one_le_exp (6600 : ℝ)] : (6601 : ℝ) ≤ Real.exp 6600).trans hn_exp
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn_ge : (6600 : ℝ) ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 6600) hn_exp
    rwa [Real.log_exp] at h
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hlogn_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by linarith
  have hX_pos : 0 < X := Real.sqrt_pos.mpr (mul_pos hn_pos hlogn_pos)
  have hY_pos : 0 < Y := Real.sqrt_pos.mpr hn_pos
  have hX_ge_1024 : (1024 : ℝ) ≤ X := by
    refine le_of_sq_le_sq ?_ hX_pos.le
    rw [Real.sq_sqrt (mul_nonneg hn_pos.le hlogn_pos.le)]
    nlinarith
  have hY_gt1 : 1 < Y := by
    refine lt_of_lt_of_le (by norm_num : (1 : ℝ) < 80) (le_of_sq_le_sq ?_ hY_pos.le)
    rw [Real.sq_sqrt hn_pos.le]
    linarith
  have hX_ge_96 : (2 : ℝ) ^ 96 ≤ X := by
    have hlog2_le1 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h2_96 : (2 : ℝ) ^ 96 ≤ Real.exp 96 := by
      have hlog_le : Real.log ((2 : ℝ) ^ 96) ≤ 96 := by
        rw [Real.log_pow]
        push_cast
        linarith
      calc (2 : ℝ) ^ 96 = Real.exp (Real.log ((2 : ℝ) ^ 96)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp 96 := Real.exp_le_exp.mpr hlog_le
    refine le_of_sq_le_sq ?_ hX_pos.le
    rw [Real.sq_sqrt (mul_nonneg hn_pos.le hlogn_pos.le)]
    calc ((2 : ℝ) ^ 96) ^ 2 ≤ (Real.exp 96) ^ 2 := pow_le_pow_left₀ (by positivity) h2_96 2
      _ = Real.exp (96 + 96) := by rw [sq, ← Real.exp_add]
      _ ≤ Real.exp 6600 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ (n : ℝ) := hn_exp
      _ ≤ (n : ℝ) * Real.log (n : ℝ) := le_mul_of_one_le_right hn_pos.le hlogn_ge1
  have hY_le_X : Y ≤ X :=
    Real.sqrt_le_sqrt (le_mul_of_one_le_right hn_pos.le hlogn_ge1)
  have hX_le_half_n : X ≤ (n : ℝ) / 2 := by
    have hn_sq : (n : ℝ) * Real.log (n : ℝ) ≤ ((n : ℝ) / 2) ^ 2 := by
      have hls : Real.log (n : ℝ) ≤ √(n : ℝ) := OMA.R_Erdos912_erdos_912_R2.log_le_sqrt hn_pos
      have hns : √(n : ℝ) ≤ (n : ℝ) / 4 := by
        refine le_of_sq_le_sq ?_ (by positivity)
        rw [Real.sq_sqrt hn_pos.le, div_pow]
        have h16n : 16 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        linarith
      nlinarith
    have h1 := Real.sqrt_le_sqrt hn_sq
    rwa [Real.sqrt_sq (by positivity)] at h1
  exact ⟨hn_ge_6601, hlogn_ge, hX_ge_1024, hY_gt1, hX_ge_96, hY_le_X, hX_le_half_n⟩

private lemma prime_window_card_bounds {n : ℕ} (hn_exp : Real.exp 6600 ≤ (n : ℝ)) :
    let X : ℝ := √((n : ℝ) * Real.log (n : ℝ))
    let Y : ℝ := √(n : ℝ)
    let Pset : Finset ℕ := (Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ Y < (p : ℝ))
    Pset ⊆ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ n < p * p) ∧
    ((1 / 4 : ℝ) * Real.log 2) * √((n : ℝ) / Real.log (n : ℝ)) ≤ (Pset.card : ℝ) ∧
    (Pset.card : ℝ) ≤ 10 * √((n : ℝ) / Real.log (n : ℝ)) := by
  intro X Y Pset
  obtain ⟨hn_ge_6601, hlogn_ge, hX_ge_1024, hY_gt1, _, hY_le_X, hX_le_half_n⟩ :=
    large_n_window_facts hn_exp
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hX_pos : 0 < X := by linarith
  have hX_gt1 : 1 < X := by linarith
  have hY_pos : 0 < Y := Real.sqrt_pos.mpr hn_pos
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_gt : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  let N : ℕ := ⌊X⌋₊
  let M : ℕ := ⌊Y⌋₊
  let cP : ℝ := (1 / 4 : ℝ) * Real.log 2
  have hcP_pos : 0 < cP := by dsimp [cP]; positivity
  have hMN : M ≤ N := Nat.floor_mono hY_le_X
  have hPset_sub_target : Pset ⊆ (Finset.range (n + 1)).filter (fun p => p.Prime ∧ n < p * p) := by
    intro p hp
    obtain ⟨hp_icc, hp_prime, hp_gtY⟩ := Finset.mem_filter.mp hp
    have hpN := (Finset.mem_Icc.mp hp_icc).2
    have hp_le_n : p ≤ n := by
      have hpr : (p : ℝ) ≤ X := (Nat.le_floor_iff hX_pos.le).mp hpN
      have hpn : (p : ℝ) ≤ (n : ℝ) := hpr.trans (by linarith)
      exact_mod_cast hpn
    have hn_lt_pp : n < p * p := by
      have hsq : Y ^ 2 < (p : ℝ) ^ 2 := pow_lt_pow_left₀ hp_gtY hY_pos.le (by norm_num)
      rw [Real.sq_sqrt hn_pos.le] at hsq
      exact_mod_cast (by nlinarith : (n : ℝ) < (p : ℝ) * (p : ℝ))
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp_prime, hn_lt_pp⟩
  have hPset_card_eq : Pset.card = Nat.primeCounting N - Nat.primeCounting M := by
    let SN := (Finset.range (N + 1)).filter Nat.Prime
    let SM := (Finset.range (M + 1)).filter Nat.Prime
    have hsub : SM ⊆ SN := by
      intro p hp
      obtain ⟨hpM, hpp⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hpM)
        (Nat.add_le_add_right hMN 1)), hpp⟩
    have heq : Pset = SN \ SM := by
      ext p
      simp only [Pset, SN, SM, Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_range,
        not_and]
      constructor
      · rintro ⟨⟨_, hpN⟩, hp_prime, hpY⟩
        have hp_gtM : M < p := (Nat.floor_lt hY_pos.le).mpr hpY
        exact ⟨⟨by omega, hp_prime⟩, fun h => absurd h (by omega)⟩
      · rintro ⟨⟨hpN, hp_prime⟩, hnot⟩
        have hMp : M < p := by
          by_contra h
          exact hnot (by omega) hp_prime
        have hpY : Y < (p : ℝ) := (Nat.floor_lt hY_pos.le).mp hMp
        exact ⟨⟨hp_prime.pos, by omega⟩, hp_prime, hpY⟩
    have hpiN : Nat.primeCounting N = SN.card := by
      rw [Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting', Nat.count_eq_card_filter_range]
    have hpiM : Nat.primeCounting M = SM.card := by
      rw [Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting', Nat.count_eq_card_filter_range]
    rw [heq, Finset.card_sdiff_of_subset hsub, hpiN, hpiM]
  have hlogX_pos : 0 < Real.log X := Real.log_pos hX_gt1
  have hlogX_ge : (1 / 2 : ℝ) * Real.log (n : ℝ) ≤ Real.log X := by
    have hY_le_X' : Real.log Y ≤ Real.log X := Real.log_le_log hY_pos hY_le_X
    have hlogY : Real.log Y = (1 / 2 : ℝ) * Real.log (n : ℝ) := by
      rw [show Y = (n : ℝ) ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow _, Real.log_rpow hn_pos]
    linarith
  have hlogX_le : Real.log X ≤ Real.log (n : ℝ) :=
    Real.log_le_log hX_pos (by linarith)
  have hX_div : X / Real.log (n : ℝ) = √((n : ℝ) / Real.log (n : ℝ)) :=
    sqrt_mul_div_eq_sqrt_div hn_pos hlogn_pos
  have hpiN_lb : ((1 / 2 : ℝ) * Real.log 2) * √((n : ℝ) / Real.log (n : ℝ)) ≤
      (Nat.primeCounting N : ℝ) := by
    have hcheb := Chebyshev.pi_ge' hX_gt1
    have hnum_lb : (1 / 2 : ℝ) * Real.log 2 * X ≤ (X - 1) * Real.log 2 - Real.log (X + 2) := by
      have hlog_X2 : Real.log (X + 2) ≤ (1 / 4 : ℝ) * Real.log 2 * X := by
        have hls := OMA.R_Erdos912_erdos_912_R2.log_le_sqrt (by positivity : 0 < X + 2)
        have hX2_le : X + 2 ≤ 2 * X := by linarith
        have hsq2X : √(2 * X) ≤ (1 / 4 : ℝ) * Real.log 2 * X := by
          have h4 : (2 : ℝ) ≤ ((1 / 4 : ℝ) * Real.log 2) ^ 2 * X := by
            have hlog_sq : (4 / 9 : ℝ) ≤ (Real.log 2) ^ 2 := by nlinarith
            nlinarith
          have hsq' : (√(2 * X)) ^ 2 ≤ ((1 / 4 : ℝ) * Real.log 2 * X) ^ 2 := by
            rw [Real.sq_sqrt (by positivity)]
            calc 2 * X ≤ (((1 / 4 : ℝ) * Real.log 2) ^ 2 * X) * X := mul_le_mul_of_nonneg_right h4 hX_pos.le
              _ = ((1 / 4 : ℝ) * Real.log 2 * X) ^ 2 := by ring
          exact le_of_sq_le_sq hsq' (by positivity)
        exact hls.trans ((Real.sqrt_le_sqrt hX2_le).trans hsq2X)
      have h1_le : 1 ≤ (1 / 4 : ℝ) * X := by linarith
      nlinarith
    calc ((1 / 2 : ℝ) * Real.log 2) * √((n : ℝ) / Real.log (n : ℝ))
        = ((1 / 2 : ℝ) * Real.log 2 * X) / Real.log (n : ℝ) := by rw [← hX_div]; ring
      _ ≤ ((1 / 2 : ℝ) * Real.log 2 * X) / Real.log X :=
          div_le_div_of_nonneg_left (by positivity) hlogX_pos hlogX_le
      _ ≤ ((X - 1) * Real.log 2 - Real.log (X + 2)) / Real.log X :=
          div_le_div_of_nonneg_right hnum_lb hlogX_pos.le
      _ ≤ (Nat.primeCounting N : ℝ) := hcheb
  have hpiM_ub : (Nat.primeCounting M : ℝ) ≤ cP * √((n : ℝ) / Real.log (n : ℝ)) := by
    have hup := OMA.R_Erdos912_erdos_912_R2.prime_count_upper hY_gt1
    have hlogY : Real.log Y = (1 / 2 : ℝ) * Real.log (n : ℝ) := by
      rw [show Y = (n : ℝ) ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow _, Real.log_rpow hn_pos]
    have h10 : 5 * Y / Real.log Y = 10 * Y / Real.log (n : ℝ) := by
      rw [hlogY]; ring
    have hcmp : 10 * Y / Real.log (n : ℝ) ≤ cP * √((n : ℝ) / Real.log (n : ℝ)) := by
      have hsqrt_div : √((n : ℝ) / Real.log (n : ℝ)) = Y / √(Real.log (n : ℝ)) :=
        Real.sqrt_div hn_pos.le (Real.log (n : ℝ))
      rw [hsqrt_div]
      have hmain_cmp : 10 ≤ cP * √(Real.log (n : ℝ)) := by
        have hsq : (10 : ℝ) ^ 2 ≤ (cP * √(Real.log (n : ℝ))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hlogn_pos.le]
          dsimp [cP]
          have hlog_sq : 1600 ≤ (Real.log 2) ^ 2 * Real.log (n : ℝ) := by
            have h1 : (4 / 9 : ℝ) ≤ (Real.log 2) ^ 2 := by nlinarith
            nlinarith
          nlinarith
        exact le_of_sq_le_sq hsq (by positivity)
      calc 10 * Y / Real.log (n : ℝ)
          = 10 * Y / (√(Real.log (n : ℝ)) * √(Real.log (n : ℝ))) := by
              rw [Real.mul_self_sqrt hlogn_pos.le]
        _ = (10 / √(Real.log (n : ℝ))) * (Y / √(Real.log (n : ℝ))) := by ring
        _ ≤ cP * (Y / √(Real.log (n : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rwa [div_le_iff₀ (Real.sqrt_pos.mpr hlogn_pos)]
    exact hup.trans (h10 ▸ hcmp)
  have hPset_lb : cP * √((n : ℝ) / Real.log (n : ℝ)) ≤ (Pset.card : ℝ) := by
    have hpiM_le_N : Nat.primeCounting M ≤ Nat.primeCounting N := Nat.monotone_primeCounting hMN
    rw [hPset_card_eq, Nat.cast_sub hpiM_le_N]
    dsimp [cP] at hpiM_ub ⊢
    linarith
  have hPset_ub : (Pset.card : ℝ) ≤ 10 * √((n : ℝ) / Real.log (n : ℝ)) := by
    have hsub : Pset.card ≤ Nat.primeCounting N := by
      rw [hPset_card_eq]; exact Nat.sub_le _ _
    have hup := OMA.R_Erdos912_erdos_912_R2.prime_count_upper hX_gt1
    have hle1 : (Pset.card : ℝ) ≤ (Nat.primeCounting N : ℝ) := by exact_mod_cast hsub
    calc (Pset.card : ℝ) ≤ 5 * X / Real.log X := hle1.trans hup
      _ ≤ 5 * X / ((1 / 2 : ℝ) * Real.log (n : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlogX_ge
      _ = 10 * (X / Real.log (n : ℝ)) := by ring
      _ = 10 * √((n : ℝ) / Real.log (n : ℝ)) := by rw [hX_div]
  exact ⟨hPset_sub_target, hPset_lb, hPset_ub⟩

private lemma close_div_pairs_bound {n : ℕ} (hn_exp : Real.exp 6600 ≤ (n : ℝ)) :
    let X : ℝ := √((n : ℝ) * Real.log (n : ℝ))
    let Y : ℝ := √(n : ℝ)
    let Pset : Finset ℕ := (Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ Y < (p : ℝ))
    (((Pset ×ˢ Pset).filter (fun pq => pq.1 < pq.2 ∧ n / pq.1 = n / pq.2)).card : ℝ) ≤
      8 * (256 * Real.exp 4 + 1) * √((n : ℝ) / Real.log (n : ℝ)) := by
  intro X Y Pset
  obtain ⟨hn_ge_6601, hlogn_ge, hX_ge_1024, hY_gt1, hX_ge_96, hY_le_X, hX_le_half_n⟩ :=
    large_n_window_facts hn_exp
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hX_pos : 0 < X := by linarith
  have hX_gt1 : 1 < X := by linarith
  have hY_pos : 0 < Y := Real.sqrt_pos.mpr hn_pos
  have hlogX_ge : (1 / 2 : ℝ) * Real.log (n : ℝ) ≤ Real.log X := by
    have hY_le_X' : Real.log Y ≤ Real.log X := Real.log_le_log hY_pos hY_le_X
    have hlogY : Real.log Y = (1 / 2 : ℝ) * Real.log (n : ℝ) := by
      rw [show Y = (n : ℝ) ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow _, Real.log_rpow hn_pos]
    linarith
  have hX_div : X / Real.log (n : ℝ) = √((n : ℝ) / Real.log (n : ℝ)) :=
    sqrt_mul_div_eq_sqrt_div hn_pos hlogn_pos
  let N : ℕ := ⌊X⌋₊
  let H : ℕ := ⌊2 * Real.log (n : ℝ)⌋₊
  let cS : ℝ := 256 * Real.exp 4 + 1
  have hcS_pos : 0 < cS := by dsimp [cS]; positivity
  have hclose_sub :
      (Pset ×ˢ Pset).filter (fun pq => pq.1 < pq.2 ∧ n / pq.1 = n / pq.2) ⊆
      (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
        (fun pq => pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ H) := by
    rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_product] at hpq ⊢
    obtain ⟨⟨hpP, hqP⟩, hpq_lt, hdiv_eq⟩ := hpq
    obtain ⟨hp_icc, hp_prime, _⟩ := Finset.mem_filter.mp hpP
    obtain ⟨hq_icc, hq_prime, _⟩ := Finset.mem_filter.mp hqP
    refine ⟨⟨hp_icc, hq_icc⟩, hp_prime, hq_prime, hpq_lt, ?_⟩
    let k := n / p
    have hpN := (Finset.mem_Icc.mp hp_icc).2
    have hpr : (p : ℝ) ≤ X := (Nat.le_floor_iff hX_pos.le).mp hpN
    have hp_le_half : p ≤ n / 2 := by
      have h2p_real : ((2 * p : ℕ) : ℝ) ≤ (n : ℝ) := by
        push_cast
        linarith
      have h2p : 2 * p ≤ n := by exact_mod_cast h2p_real
      omega
    have hk_ge2 : 2 ≤ k := by
      have hp_pos : 0 < p := hp_prime.pos
      exact Nat.le_div_iff_mul_le hp_pos |>.mpr (by omega)
    have hk_q_le : k * q ≤ n := by
      have : n / q = k := hdiv_eq.symm
      rw [← this]
      exact Nat.div_mul_le_self n q
    have hn_lt_kp : n < (k + 1) * p := by
      have hp_pos : 0 < p := hp_prime.pos
      have hdm : p * k + n % p = n := Nat.div_add_mod n p
      have hmod : n % p < p := Nat.mod_lt n hp_pos
      calc n = p * k + n % p := hdm.symm
        _ < p * k + p := by omega
        _ = (k + 1) * p := by ring
    have hk_sub_lt : k * (q - p) < p := by
      have hadd : k * (q - p) + k * p < p + k * p := by
        calc k * (q - p) + k * p = k * ((q - p) + p) := by ring
          _ = k * q := by rw [Nat.sub_add_cancel hpq_lt.le]
          _ ≤ n := hk_q_le
          _ < (k + 1) * p := hn_lt_kp
          _ = p + k * p := by ring
      exact Nat.lt_of_add_lt_add_right hadd
    have hk_real_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hk_lb : (1 / 2 : ℝ) * √((n : ℝ) / Real.log (n : ℝ)) ≤ (k : ℝ) := by
      have h1 : (n : ℝ) < ((k : ℝ) + 1) * (p : ℝ) := by exact_mod_cast hn_lt_kp
      have h2 : (n : ℝ) / (p : ℝ) < (k : ℝ) + 1 := (div_lt_iff₀ (by exact_mod_cast hp_prime.pos)).mpr h1
      have h3 : (n : ℝ) / X ≤ (n : ℝ) / (p : ℝ) :=
        div_le_div_of_nonneg_left hn_pos.le (by exact_mod_cast hp_prime.pos) hpr
      have h4 : √((n : ℝ) / Real.log (n : ℝ)) = (n : ℝ) / X := by
        rw [Real.sqrt_div hn_pos.le, show X = √((n : ℝ) * Real.log (n : ℝ)) from rfl,
          Real.sqrt_mul hn_pos.le]
        conv_rhs => arg 1; rw [← Real.mul_self_sqrt hn_pos.le]
        exact (mul_div_mul_left _ _ hY_pos.ne').symm
      have hk12 : ((k : ℝ) + 1) ≤ 2 * (k : ℝ) := by
        have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge2
        linarith
      linarith
    have hdiff_real : ((q - p : ℕ) : ℝ) < 2 * Real.log (n : ℝ) := by
      have h1nat : (q - p) * k < p := by rw [mul_comm]; exact hk_sub_lt
      have h1 : ((q - p : ℕ) : ℝ) * (k : ℝ) < (p : ℝ) := by exact_mod_cast h1nat
      have h2 : ((q - p : ℕ) : ℝ) < (p : ℝ) / (k : ℝ) := (lt_div_iff₀ hk_real_pos).mpr h1
      have h3 : (p : ℝ) / (k : ℝ) ≤ X / ((1 / 2 : ℝ) * √((n : ℝ) / Real.log (n : ℝ))) :=
        div_le_div₀ hX_pos.le hpr (by positivity) hk_lb
      have h4 : X / ((1 / 2 : ℝ) * √((n : ℝ) / Real.log (n : ℝ))) = 2 * Real.log (n : ℝ) := by
        rw [← hX_div]
        have hXne : X ≠ 0 := hX_pos.ne'
        have hLne : Real.log (n : ℝ) ≠ 0 := hlogn_pos.ne'
        field_simp
      linarith
    exact Nat.le_floor hdiff_real.le
  have hle1 : (((Pset ×ˢ Pset).filter (fun pq => pq.1 < pq.2 ∧ n / pq.1 = n / pq.2)).card : ℝ) ≤
      (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
        (fun pq => pq.1.Prime ∧ pq.2.Prime ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ H)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hclose_sub
  have hcp := close_prime_pairs_bound hX_ge_96 H
  have hH_le : (H : ℝ) ≤ 2 * Real.log (n : ℝ) := Nat.floor_le (by positivity)
  have halg := close_algebra_bound hcS_pos.le hX_pos hlogn_pos hH_le hlogX_ge hX_div
  exact hle1.trans (hcp.trans halg)

private lemma main_proof : OMA.R_Erdos912_erdos_912_R2.H1 := by
  let cP : ℝ := (1 / 4 : ℝ) * Real.log 2
  let cS : ℝ := 256 * Real.exp 4 + 1
  let c : ℝ := cP ^ 2 / (10 + 16 * cS)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcP_pos : 0 < cP := by dsimp [cP]; positivity
  have hcS_pos : 0 < cS := by dsimp [cS]; positivity
  have hc_pos : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc_pos, Filter.eventually_atTop.mpr ⟨⌈Real.exp 6600⌉₊, fun n hn => ?_⟩⟩
  have hn_exp : Real.exp 6600 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  obtain ⟨hn_ge_6601, hlogn_ge, _, _, _, _, _⟩ := large_n_window_facts hn_exp
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  let X : ℝ := √((n : ℝ) * Real.log (n : ℝ))
  let Y : ℝ := √(n : ℝ)
  let Pset : Finset ℕ := (Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ Y < (p : ℝ))
  obtain ⟨hPset_sub_target, hPset_lb, hPset_ub⟩ := prime_window_card_bounds hn_exp
  have hclose_ub := close_div_pairs_bound hn_exp
  have henergy := energy_le (Pset := Pset) (f := fun p => n / p)
  have hden_ub : (Pset.card : ℝ) +
      2 * (((Pset ×ˢ Pset).filter (fun pq => pq.1 < pq.2 ∧ n / pq.1 = n / pq.2)).card : ℝ) ≤
      (10 + 16 * cS) * √((n : ℝ) / Real.log (n : ℝ)) := by
    dsimp [cS] at hclose_ub ⊢
    linarith
  have hden_pos : 0 < (10 + 16 * cS) * √((n : ℝ) / Real.log (n : ℝ)) := by positivity
  have hsq_lb : cP ^ 2 * ((n : ℝ) / Real.log (n : ℝ)) ≤ (Pset.card : ℝ) ^ 2 := by
    have h1 := pow_le_pow_left₀ (by positivity) hPset_lb 2
    rw [mul_pow, Real.sq_sqrt (div_nonneg hn_pos.le hlogn_pos.le)] at h1
    exact h1
  have himg_lb : c * ((n : ℝ) / Real.log (n : ℝ)) ^ (1 / 2 : ℝ) ≤
      ((Pset.image (fun p => n / p)).card : ℝ) := by
    have hrpow : ((n : ℝ) / Real.log (n : ℝ)) ^ (1 / 2 : ℝ) = √((n : ℝ) / Real.log (n : ℝ)) :=
      (Real.sqrt_eq_rpow _).symm
    rw [hrpow]
    have h1 : cP ^ 2 * ((n : ℝ) / Real.log (n : ℝ)) ≤
        ((Pset.image (fun p => n / p)).card : ℝ) *
          ((10 + 16 * cS) * √((n : ℝ) / Real.log (n : ℝ))) := by
      calc cP ^ 2 * ((n : ℝ) / Real.log (n : ℝ)) ≤ (Pset.card : ℝ) ^ 2 := hsq_lb
        _ ≤ ((Pset.image (fun p => n / p)).card : ℝ) * _ := henergy
        _ ≤ ((Pset.image (fun p => n / p)).card : ℝ) *
              ((10 + 16 * cS) * √((n : ℝ) / Real.log (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hden_ub (Nat.cast_nonneg _)
    have h2 := (div_le_iff₀ hden_pos).mpr h1
    have h3 : cP ^ 2 * ((n : ℝ) / Real.log (n : ℝ)) /
        ((10 + 16 * cS) * √((n : ℝ) / Real.log (n : ℝ))) =
        c * √((n : ℝ) / Real.log (n : ℝ)) := by
      have hsq : √((n : ℝ) / Real.log (n : ℝ)) * √((n : ℝ) / Real.log (n : ℝ)) =
          (n : ℝ) / Real.log (n : ℝ) := Real.mul_self_sqrt (div_nonneg hn_pos.le hlogn_pos.le)
      have hsn : √((n : ℝ) / Real.log (n : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (div_pos hn_pos hlogn_pos)).ne'
      calc cP ^ 2 * ((n : ℝ) / Real.log (n : ℝ)) /
            ((10 + 16 * cS) * √((n : ℝ) / Real.log (n : ℝ)))
          = (cP ^ 2 / (10 + 16 * cS)) *
              ((√((n : ℝ) / Real.log (n : ℝ)) * √((n : ℝ) / Real.log (n : ℝ))) /
                √((n : ℝ) / Real.log (n : ℝ))) := by
              symm; rw [div_mul_div_comm, hsq]
        _ = c * √((n : ℝ) / Real.log (n : ℝ)) := by
              rw [mul_div_cancel_right₀ _ hsn]
    exact h3 ▸ h2
  have himg_sub : (Pset.image (fun p => n / p)).card ≤
      (((Finset.range (n + 1)).filter (fun p => p.Prime ∧ n < p * p)).image (fun p => n / p)).card :=
    Finset.card_le_card (Finset.image_subset_image hPset_sub_target)
  exact himg_lb.trans (by exact_mod_cast himg_sub)

end OMA.Erdos912R2H1

theorem OMA.solution : OMA.R_Erdos912_erdos_912_R2.H1 := OMA.Erdos912R2H1.main_proof
