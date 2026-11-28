import FormalConjectures.ErdosProblems.«940»
import Mathlib

-- Credit: @kumagi

/-!
Separate the cubic, quartic and higher-power ranges of the infinitude
variant of Erdős 940. The cubic conclusion follows from the positive
lower density of the complement of sums of three positive cube-full
numbers, as in Beyer de Ryke, Corollary 1.2.
https://arxiv.org/abs/2609.35772

The bridges below formalize the canonical prime-exponent decomposition
in Section 6, its cubic form in Lemma 2.1, the elementary counting bound
and the negligible contribution of at most two positive summands.
-/

namespace Erdos940FullDecomposition

open Nat

/-- The part remaining after the canonical rth power is removed. -/
private def IsKernel (r d : ℕ) : Prop :=
  0 < d ∧ ∀ p, d.factorization p = 0 ∨
    r < d.factorization p ∧ d.factorization p < 2 * r

private def kernelExponent (r e : ℕ) : ℕ :=
  if e % r = 0 then 0 else r + e % r

private def baseExponent (r e : ℕ) : ℕ :=
  e / r - if e % r = 0 then 0 else 1

private lemma kernelExponent_range {r e : ℕ} (hr : 0 < r) :
    kernelExponent r e = 0 ∨ r < kernelExponent r e ∧ kernelExponent r e < 2 * r := by
  unfold kernelExponent
  split
  · exact Or.inl rfl
  · have h := Nat.mod_lt e hr
    omega

private lemma exponent_split {r e : ℕ} (hr : 0 < r) (he : e = 0 ∨ r ≤ e) :
    r * baseExponent r e + kernelExponent r e = e := by
  have hDiv := Nat.div_add_mod e r
  by_cases h : e % r = 0
  · simpa [baseExponent, kernelExponent, h] using hDiv
  · have hrle : r ≤ e := by rcases he with rfl | he <;> simp_all
    have hc : 1 ≤ e / r := (Nat.le_div_iff_mul_le hr).mpr (by simpa using hrle)
    have hstep : r * (e / r - 1) + r = r * (e / r) := by
      calc
        r * (e / r - 1) + r = r * (e / r - 1) + r * 1 := by rw [Nat.mul_one]
        _ = r * ((e / r - 1) + 1) := (Nat.mul_add ..).symm
        _ = _ := by rw [Nat.sub_add_cancel hc]
    simp only [baseExponent, kernelExponent, h, if_false, ← Nat.add_assoc, hstep]
    exact hDiv

private lemma kernelExponent_of_valid {r e : ℕ} (_hr : 0 < r)
    (he : e = 0 ∨ r < e ∧ e < 2 * r) : kernelExponent r e = e := by
  rcases he with rfl | ⟨h₁, h₂⟩
  · simp [kernelExponent]
  have hx : 0 < e - r := by omega
  have hy : e - r < r := by omega
  have hm : e % r = e - r := by
    calc
      e % r = ((e - r) + r) % r := by congr 1; omega
      _ = (e - r) % r := Nat.add_mod_right _ _
      _ = _ := Nat.mod_eq_of_lt hy
  simp [kernelExponent, hm, hx.ne', Nat.add_sub_of_le h₁.le]

private lemma kernelExponent_mul_add {r a d : ℕ} (hr : 0 < r)
    (hd : d = 0 ∨ r < d ∧ d < 2 * r) : kernelExponent r (r * a + d) = d := by
  unfold kernelExponent
  have hm : (r * a + d) % r = d % r := by simp [Nat.add_mod]
  rw [hm]
  exact kernelExponent_of_valid hr hd

private lemma full_valuation {r n p : ℕ} (h : r.Full n) :
    n.factorization p = 0 ∨ r ≤ n.factorization p := by
  by_cases hp : p ∈ n.primeFactors
  · exact Or.inr ((Nat.Prime.pow_dvd_iff_le_factorization
      (Nat.prime_of_mem_primeFactors hp) ((Nat.mem_primeFactors.mp hp).2.2)).mp (h p hp))
  · exact Or.inl (Finsupp.notMem_support_iff.mp hp)

private lemma positive_product (f : ℕ →₀ ℕ) (hf : ∀ p ∈ f.support, p.Prime) :
    0 < f.prod (· ^ ·) := by
  apply Finset.prod_pos
  exact fun p hp => Nat.pow_pos (hf p hp).pos

/-- Canonical rth-power decomposition of every positive r-full integer.
The kernel contains each prime to an exponent in [r+1, 2r-1]. -/
theorem exists_unique_kernel {r n : ℕ} (hr : 0 < r) (hn : 0 < n) (hfull : r.Full n) :
    ∃! ad : ℕ × ℕ, 0 < ad.1 ∧ IsKernel r ad.2 ∧ n = ad.1 ^ r * ad.2 := by
  let f := n.factorization.mapRange (baseExponent r) (by simp [baseExponent])
  let g := n.factorization.mapRange (kernelExponent r) (by simp [kernelExponent])
  let a := f.prod (· ^ ·)
  let d := g.prod (· ^ ·)
  have hf : ∀ p ∈ f.support, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
  have hg : ∀ p ∈ g.support, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
  have hfa : a.factorization = f := Nat.prod_pow_factorization_eq_self hf
  have hgd : d.factorization = g := Nat.prod_pow_factorization_eq_self hg
  have ha : 0 < a := positive_product _ hf
  have hd : 0 < d := positive_product _ hg
  have hdk : IsKernel r d := by
    refine ⟨hd, fun p => ?_⟩
    rw [hgd]
    exact kernelExponent_range hr
  have he : n = a ^ r * d := by
    apply Nat.factorization_inj hn.ne' (Nat.mul_ne_zero (pow_ne_zero _ ha.ne') hd.ne')
    rw [Nat.factorization_mul (pow_ne_zero _ ha.ne') hd.ne', Nat.factorization_pow, hfa, hgd]
    ext p
    exact (exponent_split hr (full_valuation hfull)).symm
  refine ⟨(a, d), ⟨ha, hdk, he⟩, ?_⟩
  rintro ⟨a', d'⟩ ⟨ha', hd', he'⟩
  have hexp (p : ℕ) :
      r * a'.factorization p + d'.factorization p = r * a.factorization p + d.factorization p := by
    have hh := congrArg (fun n : ℕ => n.factorization p) (he'.symm.trans he)
    rw [Nat.factorization_mul (pow_ne_zero _ ha'.ne') hd'.1.ne',
      Nat.factorization_mul (pow_ne_zero _ ha.ne') hd.ne', Nat.factorization_pow,
      Nat.factorization_pow] at hh
    exact hh
  have hde : d' = d := by
    apply Nat.factorization_inj hd'.1.ne' hd.ne'
    ext p
    have hd₁ := kernelExponent_mul_add (a := a'.factorization p) hr (hd'.2 p)
    have hd₂ := kernelExponent_mul_add (a := a.factorization p) hr (hdk.2 p)
    rw [hexp] at hd₁
    exact hd₁.symm.trans hd₂
  refine Prod.ext ?_ hde
  apply Nat.factorization_inj ha'.ne' ha.ne'
  ext p
  have hp := hexp p
  rw [hde] at hp
  exact mul_left_cancel₀ hr.ne' (Nat.add_right_cancel hp)

/-- Conversely, a product of the indicated types is r-full. -/
theorem full_of_kernel {r a d : ℕ} (_hr : 0 < r) (ha : 0 < a) (hd : IsKernel r d) :
    r.Full (a ^ r * d) := by
  intro p hp
  let n := a ^ r * d
  have hn : n ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ ha.ne') hd.1.ne'
  apply (Nat.Prime.pow_dvd_iff_le_factorization (Nat.prime_of_mem_primeFactors hp) hn).2
  have hpos : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
  rw [show n = a ^ r * d from rfl, Nat.factorization_mul (pow_ne_zero _ ha.ne') hd.1.ne',
    Nat.factorization_pow] at hpos ⊢
  change 0 < r * a.factorization p + d.factorization p at hpos
  change r ≤ r * a.factorization p + d.factorization p
  rcases hd.2 p with hz | ⟨hp, _⟩
  · have ha' : 0 < a.factorization p := by
      by_contra! hh
      simp [Nat.eq_zero_of_le_zero hh, hz] at hpos
    simpa [hz] using Nat.le_mul_of_pos_right r ha'
  · omega


private theorem kernel_three_valuations {d : ℕ} (hd : IsKernel 3 d) (p : ℕ) :
    d.factorization p = 0 ∨ d.factorization p = 4 ∨ d.factorization p = 5 := by
  rcases hd.2 p with h | h <;> omega

private lemma split_cube_kernel {d : ℕ} (hd : IsKernel 3 d) :
    ∃ b c : ℕ, 0 < b ∧ 0 < c ∧ Squarefree (b * c) ∧ d = b ^ 4 * c ^ 5 := by
  let f := d.factorization.mapRange (fun e => if e = 4 then 1 else 0) (by decide)
  let g := d.factorization.mapRange (fun e => if e = 5 then 1 else 0) (by decide)
  let b := f.prod (· ^ ·)
  let c := g.prod (· ^ ·)
  have hf : ∀ p ∈ f.support, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
  have hg : ∀ p ∈ g.support, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
  have hbf : b.factorization = f := Nat.prod_pow_factorization_eq_self hf
  have hcg : c.factorization = g := Nat.prod_pow_factorization_eq_self hg
  have hb : 0 < b := positive_product _ hf
  have hc : 0 < c := positive_product _ hg
  have hp : b * c ≠ 0 := mul_ne_zero hb.ne' hc.ne'
  refine ⟨b, c, hb, hc, (Nat.squarefree_iff_factorization_le_one hp).mpr ?_, ?_⟩
  · intro p
    rw [Nat.factorization_mul hb.ne' hc.ne', Finsupp.add_apply, hbf, hcg]
    change (if d.factorization p = 4 then 1 else 0) +
      (if d.factorization p = 5 then 1 else 0) ≤ 1
    rcases kernel_three_valuations hd p with he | he | he <;> simp [he]
  · apply Nat.factorization_inj hd.1.ne' (mul_ne_zero (pow_ne_zero _ hb.ne') (pow_ne_zero _ hc.ne'))
    rw [Nat.factorization_mul (pow_ne_zero _ hb.ne') (pow_ne_zero _ hc.ne'),
      Nat.factorization_pow, Nat.factorization_pow, hbf, hcg]
    ext p
    change d.factorization p = 4 * (if d.factorization p = 4 then 1 else 0) +
      5 * (if d.factorization p = 5 then 1 else 0)
    rcases kernel_three_valuations hd p with he | he | he <;> simp [he]

private lemma cube_kernel_of_squarefree {b c : ℕ} (hb : 0 < b) (hc : 0 < c)
    (hs : Squarefree (b * c)) : IsKernel 3 (b ^ 4 * c ^ 5) := by
  refine ⟨by positivity, fun p => ?_⟩
  have h := (Nat.squarefree_iff_factorization_le_one (mul_ne_zero hb.ne' hc.ne')).mp hs p
  rw [Nat.factorization_mul hb.ne' hc.ne', Finsupp.add_apply] at h
  rw [Nat.factorization_mul (pow_ne_zero _ hb.ne') (pow_ne_zero _ hc.ne'),
    Nat.factorization_pow, Nat.factorization_pow]
  change 4 * b.factorization p + 5 * c.factorization p = 0 ∨
    3 < 4 * b.factorization p + 5 * c.factorization p ∧
      4 * b.factorization p + 5 * c.factorization p < 2 * 3
  by_cases hb0 : b.factorization p = 0 <;> by_cases hc0 : c.factorization p = 0 <;> omega

private lemma cube_kernel_factors_inj {b c b' c' : ℕ}
    (hb : 0 < b) (hc : 0 < c) (hb' : 0 < b') (hc' : 0 < c')
    (hs : Squarefree (b * c)) (hs' : Squarefree (b' * c'))
    (he : b ^ 4 * c ^ 5 = b' ^ 4 * c' ^ 5) : b = b' ∧ c = c' := by
  have h (p : ℕ) : b.factorization p = b'.factorization p ∧ c.factorization p = c'.factorization p := by
    have hsum := (Nat.squarefree_iff_factorization_le_one (mul_ne_zero hb.ne' hc.ne')).mp hs p
    have hsum' := (Nat.squarefree_iff_factorization_le_one (mul_ne_zero hb'.ne' hc'.ne')).mp hs' p
    rw [Nat.factorization_mul hb.ne' hc.ne', Finsupp.add_apply] at hsum
    rw [Nat.factorization_mul hb'.ne' hc'.ne', Finsupp.add_apply] at hsum'
    have hpow := congrArg (fun d => (Nat.factorization d) p) he
    rw [Nat.factorization_mul (pow_ne_zero _ hb.ne') (pow_ne_zero _ hc.ne'),
      Nat.factorization_mul (pow_ne_zero _ hb'.ne') (pow_ne_zero _ hc'.ne'),
      Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow] at hpow
    change 4 * b.factorization p + 5 * c.factorization p =
      4 * b'.factorization p + 5 * c'.factorization p at hpow
    omega
  exact ⟨Nat.factorization_inj hb.ne' hb'.ne' (Finsupp.ext fun p => (h p).1),
    Nat.factorization_inj hc.ne' hc'.ne' (Finsupp.ext fun p => (h p).2)⟩

/-- Lemma 2.1 of Basile Beyer de Ryke, A density deficit for sums of three cube-full numbers.
The factors b and c may share primes with the base x. -/
theorem cube_full_unique_factorization {n : ℕ} (hn : 0 < n) (hfull : (3 : ℕ).Full n) :
    ∃! t : ℕ × ℕ × ℕ, 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
      Squarefree (t.2.1 * t.2.2) ∧ n = t.1 ^ 3 * (t.2.1 ^ 4 * t.2.2 ^ 5) := by
  obtain ⟨⟨x, d⟩, ⟨hx, hd, hnxd⟩, huni⟩ := exists_unique_kernel (r := 3) (by decide) hn hfull
  obtain ⟨b, c, hb, hc, hs, he⟩ := split_cube_kernel hd
  refine ⟨⟨x, b, c⟩, ⟨hx, hb, hc, hs, hnxd.trans (congrArg (x ^ 3 * ·) he)⟩, ?_⟩
  rintro ⟨x', b', c'⟩ ⟨hx', hb', hc', hs', he'⟩
  have hpair := huni (x', b' ^ 4 * c' ^ 5) ⟨hx', cube_kernel_of_squarefree hb' hc' hs', he'⟩
  have hxEq : x' = x := congrArg Prod.fst hpair
  have hdEq : b' ^ 4 * c' ^ 5 = b ^ 4 * c ^ 5 := (congrArg Prod.snd hpair).trans he
  obtain ⟨hbe, hce⟩ := cube_kernel_factors_inj hb' hc' hb hc hs' hs hdEq
  exact Prod.ext hxEq (Prod.ext hbe hce)


open Finset

private noncomputable def weight4 (b : ℕ) : ℝ := (b : ℝ) ^ (-(4 / 3) : ℝ)
private noncomputable def weight5 (c : ℕ) : ℝ := (c : ℝ) ^ (-(5 / 3) : ℝ)

private noncomputable def cubeBound (X b c : ℕ) : ℝ :=
  (X : ℝ) ^ (1 / 3 : ℝ) * weight4 b * weight5 c

private lemma base_le_cubeBound {X x b c : ℕ} (hb : 0 < b) (hc : 0 < c)
    (h : x ^ 3 * (b ^ 4 * c ^ 5) ≤ X) : (x : ℝ) ≤ cubeBound X b c := by
  have hbr : 0 < (b : ℝ) := by exact_mod_cast hb
  have hcr : 0 < (c : ℝ) := by exact_mod_cast hc
  have hxR : 0 ≤ (x : ℝ) := by positivity
  have hR : (x : ℝ) ^ 3 * ((b : ℝ) ^ 4 * (c : ℝ) ^ 5) ≤ (X : ℝ) := by exact_mod_cast h
  have hpow := Real.rpow_le_rpow (by positivity) hR (by norm_num : 0 ≤ (1 / 3 : ℝ))
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast_mul hxR, ← Real.rpow_natCast_mul hbr.le, ← Real.rpow_natCast_mul hcr.le] at hpow
  norm_num at hpow
  unfold cubeBound weight4 weight5
  rw [Real.rpow_neg hbr.le, Real.rpow_neg hcr.le]
  let B := (b : ℝ) ^ (4 / 3 : ℝ)
  let C := (c : ℝ) ^ (5 / 3 : ℝ)
  have hB : 0 < B := Real.rpow_pos_of_pos hbr _
  have hC : 0 < C := Real.rpow_pos_of_pos hcr _
  have hR : (x : ℝ) * (B * C) ≤ (X : ℝ) ^ (1 / 3 : ℝ) := by
    simpa [B, C, div_eq_mul_inv] using hpow
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hR (inv_nonneg.mpr hB.le)) (inv_nonneg.mpr hC.le)
  have he : ((x : ℝ) * (B * C) * B⁻¹) * C⁻¹ = x := by
    calc
      _ = (x : ℝ) * (B * B⁻¹) * (C * C⁻¹) := by ring
      _ = _ := by simp [hB.ne', hC.ne']
  rw [he] at hm
  exact hm

/-- The number of positive cube-full integers through X is O(X^(1/3)). -/
theorem cube_full_count_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      ((Icc 1 X).filter ((3 : ℕ).Full) |>.card : ℝ) ≤ C * (X : ℝ) ^ (1 / 3 : ℝ) := by
  have h4 : Summable weight4 := Real.summable_nat_rpow.mpr (by norm_num)
  have h5 : Summable weight5 := Real.summable_nat_rpow.mpr (by norm_num)
  let S4 := ∑' b, weight4 b
  let S5 := ∑' c, weight5 c
  have hS4 : 0 ≤ S4 := tsum_nonneg (fun _ => by unfold weight4; positivity)
  have hS5 : 0 ≤ S5 := tsum_nonneg (fun _ => by unfold weight5; positivity)
  refine ⟨(S4 + 1) * (S5 + 1), by positivity, ?_⟩
  intro X
  let B := Icc 1 X
  let A (p : ℕ × ℕ) := Icc 1 ⌊cubeBound X p.1 p.2⌋₊
  let D := (B ×ˢ B).sigma A
  let value (d : Sigma fun _ : ℕ × ℕ => ℕ) :=
    d.2 ^ 3 * (d.1.1 ^ 4 * d.1.2 ^ 5)
  have hcover : (Icc 1 X).filter ((3 : ℕ).Full) ⊆ D.image value := by
    intro n hn
    obtain ⟨hnI, hnF⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnX⟩ := mem_Icc.mp hnI
    obtain ⟨⟨x, b, c⟩, ⟨hx, hb, hc, _, he⟩, _⟩ :=
      cube_full_unique_factorization (by omega : 0 < n) hnF
    have hN : x ^ 3 * (b ^ 4 * c ^ 5) ≤ X := he ▸ hnX
    have hbX : b ≤ X := by
      have hbPow : b ≤ b ^ 4 := Nat.le_self_pow (by decide) _
      exact hbPow.trans ((Nat.le_mul_of_pos_right _ (by positivity : 0 < c ^ 5)).trans
        ((Nat.le_mul_of_pos_left _ (by positivity : 0 < x ^ 3)).trans hN))
    have hcX : c ≤ X := by
      have hcPow : c ≤ c ^ 5 := Nat.le_self_pow (by decide) _
      exact hcPow.trans ((Nat.le_mul_of_pos_left _ (by positivity : 0 < b ^ 4)).trans
        ((Nat.le_mul_of_pos_left _ (by positivity : 0 < x ^ 3)).trans hN))
    refine mem_image.mpr ⟨⟨(b, c), x⟩, ?_, he.symm⟩
    apply mem_sigma.mpr
    refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hb, hbX⟩, mem_Icc.mpr ⟨hc, hcX⟩⟩, ?_⟩
    have hnonneg : 0 ≤ cubeBound X b c := by unfold cubeBound weight4 weight5; positivity
    exact mem_Icc.mpr ⟨hx, (Nat.le_floor_iff hnonneg).mpr (base_le_cubeBound hb hc hN)⟩
  have hcard : ((Icc 1 X).filter ((3 : ℕ).Full)).card ≤ D.card :=
    (card_le_card hcover).trans card_image_le
  have h4sum : ∑ b ∈ B, weight4 b ≤ S4 :=
    h4.sum_le_tsum _ (fun _ _ => by unfold weight4; positivity)
  have h5sum : ∑ c ∈ B, weight5 c ≤ S5 :=
    h5.sum_le_tsum _ (fun _ _ => by unfold weight5; positivity)
  calc
    _ ≤ (D.card : ℝ) := by exact_mod_cast hcard
    _ = ∑ p ∈ (B ×ˢ B), ((A p).card : ℝ) := by simp only [D, card_sigma, Nat.cast_sum]
    _ ≤ ∑ p ∈ (B ×ˢ B), cubeBound X p.1 p.2 := by
      apply sum_le_sum
      intro p _
      have hnonneg : 0 ≤ cubeBound X p.1 p.2 := by unfold cubeBound weight4 weight5; positivity
      simp only [A, Nat.card_Icc, Nat.add_sub_cancel]
      exact Nat.floor_le hnonneg
    _ = (X : ℝ) ^ (1 / 3 : ℝ) * (∑ b ∈ B, weight4 b) * (∑ c ∈ B, weight5 c) := by
      simp [cubeBound, sum_product, mul_sum, sum_mul, mul_assoc]
      rw [sum_comm]
    _ ≤ (S4 + 1) * (S5 + 1) * (X : ℝ) ^ (1 / 3 : ℝ) := by
      rw [mul_comm ((S4 + 1) * (S5 + 1))]
      simp only [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h4' : (∑ b ∈ B, weight4 b) ≤ S4 + 1 :=
        h4sum.trans (le_add_of_nonneg_right zero_le_one)
      have h5' : (∑ c ∈ B, weight5 c) ≤ S5 + 1 :=
        h5sum.trans (le_add_of_nonneg_right zero_le_one)
      apply mul_le_mul h4' h5' _ (by positivity)
      exact sum_nonneg fun _ _ => by unfold weight5; positivity

open Filter
open scoped Topology

/-- Sums of two cube-full numbers, allowing zero. -/
private def Two : Set ℕ := {n | ∃ a b : ℕ, (3 : ℕ).Full a ∧ (3 : ℕ).Full b ∧ n = a + b}

/-- Sums of exactly three positive cube-full numbers. -/
private def ThreePositive : Set ℕ := {n | ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
  (3 : ℕ).Full a ∧ (3 : ℕ).Full b ∧ (3 : ℕ).Full c ∧ n = a + b + c}

private lemma full_mem_box {a X : ℕ} (ha : (3 : ℕ).Full a) (hx : a ≤ X) :
    a ∈ insert 0 ((Icc 1 X).filter ((3 : ℕ).Full)) := by
  by_cases h : a = 0
  · simp [h]
  · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hx⟩, ha⟩)

private lemma two_count_atTop :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 0 < X →
      ((Two ∩ Set.Iio X).ncard : ℝ) ≤ C * (X : ℝ) ^ (2 / 3 : ℝ) := by
  obtain ⟨C, hC, hcount⟩ := cube_full_count_upper
  refine ⟨(C + 1) ^ 2, by positivity, ?_⟩
  intro X hX
  let B := insert 0 ((Icc 1 X).filter ((3 : ℕ).Full))
  let A := (B ×ˢ B).image (fun p : ℕ × ℕ => p.1 + p.2)
  have hs : Two ∩ Set.Iio X ⊆ (A : Set ℕ) := by
    intro n hn
    obtain ⟨⟨a, b, ha, hb, he⟩, hlt⟩ := hn
    have hnX : n < X := hlt
    refine mem_image.mpr ⟨(a, b), mem_product.mpr ⟨?_, ?_⟩, he.symm⟩
    · exact full_mem_box ha (by omega)
    · exact full_mem_box hb (by omega)
  have hb (h : (1 : ℝ) ≤ (X : ℝ)) : (B.card : ℝ) ≤ (C + 1) * (X : ℝ) ^ (1 / 3 : ℝ) := by
    have h1 : (1 : ℝ) ≤ (X : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow h (by norm_num)
    have hbCard : B.card ≤ ((Icc 1 X).filter ((3 : ℕ).Full)).card + 1 := card_insert_le _ _
    have hbR : (B.card : ℝ) ≤ (((Icc 1 X).filter ((3 : ℕ).Full)).card : ℝ) + 1 := by
      exact_mod_cast hbCard
    linarith [hcount X]
  have hbR := hb (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hX.ne')
  have hAc : A.card ≤ B.card ^ 2 := by
    simpa [A, pow_two] using (Finset.card_image_le (s := B ×ˢ B) (f := fun p : ℕ × ℕ => p.1 + p.2))
  have hTwo : (Two ∩ Set.Iio X).ncard ≤ A.card := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hs A.finite_toSet
  calc
    _ ≤ (B.card : ℝ) ^ 2 := by exact_mod_cast hTwo.trans hAc
    _ ≤ ((C + 1) * (X : ℝ) ^ (1 / 3 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hbR _
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
      norm_num

private lemma density_univ_nat (S : Set ℕ) (X : ℕ) :
    S.partialDensity Set.univ X = ((S ∩ Set.Iio X).ncard : ℝ) / (X : ℝ) := by
  simp [Set.partialDensity]

/-- The contribution of at most two cube-full summands has natural density zero. -/
theorem two_hasDensity_zero : Two.HasDensity 0 := by
  obtain ⟨C, hC, hcount⟩ := two_count_atTop
  have hLim : Tendsto (fun X : ℕ => C * (X : ℝ) ^ (-(1 / 3) : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop
    simpa only [mul_zero, Function.comp_apply] using h.const_mul C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLim
  · exact Eventually.of_forall fun X => by rw [density_univ_nat]; positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    rw [density_univ_nat]
    apply (div_le_iff₀ hXR).mpr
    have he := (Real.rpow_add hXR (-(1 / 3) : ℝ) 1).symm
    rw [Real.rpow_one, show -(1 / 3 : ℝ) + 1 = 2 / 3 by ring] at he
    rw [mul_assoc, he]
    exact hcount X hX

private lemma at_most_three_split {n : ℕ} (h :
    ∃ S : Multiset ℕ, S.card ≤ 3 ∧ (∀ x ∈ S, (3 : ℕ).Full x) ∧ n = S.sum) :
    n ∈ Two ∨ n ∈ ThreePositive := by
  obtain ⟨S, hS, hfull, hsum⟩ := h
  have hcs : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hcs with hc | hc | hc | hc
  · have h0 := Multiset.card_eq_zero.mp hc
    exact Or.inl ⟨0, 0, Nat.Full.zero_right _, Nat.Full.zero_right _, by simp [h0] at hsum; simp [hsum]⟩
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hc
    exact Or.inl ⟨a, 0, hfull _ (by simp), Nat.Full.zero_right _, by simpa using hsum⟩
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hc
    exact Or.inl ⟨a, b, hfull _ (by simp), hfull _ (by simp), by simpa using hsum⟩
  · obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp hc
    have ha := hfull a (by simp)
    have hb := hfull b (by simp)
    have hc := hfull c (by simp)
    have he : n = a + b + c := by simpa [add_assoc] using hsum
    by_cases ha0 : a = 0
    · exact Or.inl ⟨b, c, hb, hc, by simpa [ha0] using he⟩
    by_cases hb0 : b = 0
    · exact Or.inl ⟨a, c, ha, hc, by simpa [hb0] using he⟩
    by_cases hc0 : c = 0
    · exact Or.inl ⟨a, b, ha, hb, by simpa [hc0] using he⟩
    exact Or.inr ⟨a, b, c, Nat.pos_of_ne_zero ha0, Nat.pos_of_ne_zero hb0,
      Nat.pos_of_ne_zero hc0, ha, hb, hc, he⟩

/-- The positive lower density in Beyer de Ryke's Corollary 1.2 implies
the r = 3 case of the infinitude variant of Erdős 940. -/
theorem not_eventually_at_most_three_of_positive_lowerDensity
    (hdeficit : 0 < ThreePositiveᶜ.lowerDensity Set.univ) :
    ¬ ∀ᶠ n : ℕ in atTop, ∃ S : Multiset ℕ, S.card ≤ 3 ∧
      (∀ x ∈ S, (3 : ℕ).Full x) ∧ n = S.sum := by
  intro hev
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  have hsub (X : ℕ) :
      ThreePositiveᶜ ∩ Set.Iio X ⊆ (Two ∩ Set.Iio X) ∪ Set.Iio K := by
    intro n hn
    by_cases hnK : K ≤ n
    · rcases at_most_three_split (hK n hnK) with ha | hb
      · exact Or.inl ⟨ha, hn.2⟩
      · exact (hn.1 hb).elim
    · exact Or.inr (lt_of_not_ge hnK)
  have hb (X : ℕ) : ThreePositiveᶜ.partialDensity Set.univ X ≤
      Two.partialDensity Set.univ X + (K : ℝ) / X := by
    have hfin : ((Two ∩ Set.Iio X) ∪ Set.Iio K).Finite :=
      ((Set.finite_Iio X).inter_of_right _).union (Set.finite_Iio K)
    have hc := (Set.ncard_le_ncard (hsub X) hfin).trans (Set.ncard_union_le _ _)
    simp only [density_univ_nat, ← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (by simpa using hc)
  have ht : Tendsto (fun X : ℕ => Two.partialDensity Set.univ X + (K : ℝ) / X) atTop (𝓝 0) := by
    have h := two_hasDensity_zero.add (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))
    simpa only [zero_add] using h
  have hzero : ThreePositiveᶜ.HasDensity 0 :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun X => by rw [density_univ_nat]; positivity) hb
  have hEq : ThreePositiveᶜ.lowerDensity Set.univ = 0 := hzero.liminf_eq
  rw [hEq] at hdeficit
  exact (lt_irrefl 0) hdeficit

end Erdos940FullDecomposition


namespace OMA.R_Erdos940_erdos_940_variants_large_integers_R1

open Filter

/-- The positive lower density furnished by the cubic density deficit. -/
def H1 : Prop :=
  0 < {n : ℕ | ¬ ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    (3 : ℕ).Full a ∧ (3 : ℕ).Full b ∧ (3 : ℕ).Full c ∧ n = a + b + c}.lowerDensity Set.univ

/-- The quartic case of the infinitude assertion. -/
def H2 : Prop :=
  ¬ ∀ᶠ n : ℕ in atTop, ∃ S : Multiset ℕ, S.card ≤ 4 ∧
    (∀ x ∈ S, (4 : ℕ).Full x) ∧ n = S.sum

/-- The infinitude assertion for exponents starting at five. -/
def H3 : Prop :=
  ∀ r ≥ 5, ¬ ∀ᶠ n : ℕ in atTop, ∃ S : Multiset ℕ, S.card ≤ r ∧
    (∀ x ∈ S, r.Full x) ∧ n = S.sum

theorem main : H1 → H2 → H3 → type_of% @Erdos940.erdos_940.variants.large_integers := by
  intro hc hq hother r hr
  by_cases h : 5 ≤ r
  · exact hother r h
  · interval_cases r
    · exact Erdos940FullDecomposition.not_eventually_at_most_three_of_positive_lowerDensity hc
    · exact hq

end OMA.R_Erdos940_erdos_940_variants_large_integers_R1
