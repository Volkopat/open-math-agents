import FormalConjectures.Wikipedia.ArtinPrimitiveRootsConjecture
import Mathlib

-- Reduction ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.variants.part_ii_power_squarefreePart_modeq_one.R1
-- Credit: @pyaf

/-! # A finite sieve for the Artin density of an odd power, entangled case

A prime divisor of the index of a unit modulo p obstructs generation of the unit group.
The two remaining inputs are the finite Kummer-field density (Chebotarev, with the entanglement
`√b₀ ∈ ℚ(ζ_{b₀})` for `b₀ ≡ 1 mod 4`, which appears once the sieved primes contain those of `2 b₀`)
and Hooley's tail estimate. The passage to density and the Euler product correction are proved
below. The sieve lemmas are adapted from the merged reduction of the case `b₀ ≢ 1 mod 4`
(Steve Digital, #4044). See Hooley (1967), and Lenstra, Moree and Stevenhagen, arXiv:1112.4816,
Eq. (1.4). -/

namespace OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_variants_part_ii_power_squarefreePart_modeq_one_R1

open Finset Set Real Filter Topology ArtinPrimitiveRootsConjecture
open scoped Classical

-- For each finite set of index primes containing those of 2 b₀, the Kummer splitting conditions
-- have a finite density: the local factors times the entanglement correction.
def H1 : Prop := ∀ a m b : ℕ, a = b^m → (∀ u v, 1 < u → b ≠ v^u) →
    1 < m → Odd m → b.squarefreePart ≡ 1 [MOD 4] → ∀ P : Finset Nat.Primes,
    (∀ q : Nat.Primes, q.val ∣ 2 * b.squarefreePart → q ∈ P) →
    {p : ℕ | p.Prime ∧ (a:ZMod p) ≠ 0 ∧
      ∀ q ∈ P, q.val ∣ p-1 → (a:ZMod p)^((p-1)/q.val) ≠ 1}.HasDensity
      ((∏ q ∈ P, if q.val ∣ m then 1-1/(q.val-1:ℝ) else 1-1/((q.val:ℝ)*(q.val-1:ℝ))) *
        entanglementFactor b m)
      {p | p.Prime}

-- The analytic remainder counts primes whose index has a prime factor outside P.
def H2 : Prop := ∀ a m b : ℕ, a = b^m → (∀ u v, 1 < u → b ≠ v^u) →
    1 < m → Odd m → b.squarefreePart ≡ 1 [MOD 4] → HooleyHypothesis a →
    ∀ ε > (0:ℝ), ∀ᶠ P : Finset Nat.Primes in atTop, ∀ᶠ x : ℕ in atTop,
      {p : ℕ | p.Prime ∧ (a:ZMod p) ≠ 0 ∧ ∃ q : Nat.Primes, q ∉ P ∧ q.val ∣ p-1 ∧
        (a:ZMod p)^((p-1)/q.val) = 1}.partialDensity {p | p.Prime} x < ε

lemma artin_prod_limit :
    HasProd (fun q : Nat.Primes => 1 - 1/((q.val:ℝ)*(q.val-1:ℝ)))
      (∏' (q : Nat.Primes), (1 - 1/((q.val:ℝ)*(q.val-1:ℝ)))) := by
  let w (q : Nat.Primes) := 1/((q.val:ℝ)*(q.val-1:ℝ))
  have sq : Summable (fun q : Nat.Primes => ((q.val:ℝ)^2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).comp_injective Subtype.val_injective
  have sw : Summable w := by
    apply (sq.mul_left 2).of_norm_bounded
    intro q
    have two : (2:ℝ) ≤ q.val := by exact_mod_cast q.property.two_le
    have pos : 0 < (q.val:ℝ) := by linarith
    have sub : 0 < (q.val:ℝ)-1 := by linarith
    simp only [w,Real.norm_eq_abs,abs_of_nonneg (div_nonneg zero_le_one (mul_nonneg pos.le sub.le)),← div_eq_mul_inv]
    rw [div_le_div_iff₀ (mul_pos pos sub) (pow_pos pos 2)]
    nlinarith [mul_nonneg pos.le (sub_nonneg.mpr two)]
  have hs := Real.multipliable_one_add_of_summable sw.neg
  apply Multipliable.hasProd
  simpa only [w,sub_eq_add_neg,Pi.neg_apply] using hs

lemma corrected_prod (m : ℕ) (hm : m ≠ 0) (A : Finset Nat.Primes)
    (contains : ∀ p ∈ m.primeFactors, ∃ q ∈ A, q.val = p) :
    (∏ q ∈ A, if q.val ∣ m then 1-1/(q.val-1:ℝ) else 1-1/((q.val:ℝ)*(q.val-1:ℝ))) =
      (∏ q ∈ A, (1-1/((q.val:ℝ)*(q.val-1:ℝ)))) *
      (∏ p ∈ m.primeFactors, (p:ℝ)*(p-2)/(p^2-p-1)) := by
  classical
  let c (p : ℕ) := (p:ℝ)*(p-2)/(p^2-p-1)
  let B := A.filter (fun q : Nat.Primes => q.val ∣ m)
  have imageB : B.image Subtype.val = m.primeFactors := by
    ext p
    constructor
    · intro h
      obtain ⟨q,hq,rfl⟩ := mem_image.mp h
      exact Nat.mem_primeFactors.mpr ⟨q.property,(mem_filter.mp hq).2,hm⟩
    · intro h
      obtain ⟨q,hq,eq⟩ := contains p h
      exact mem_image.mpr ⟨q,mem_filter.mpr ⟨hq,eq ▸ (Nat.mem_primeFactors.mp h).2.1⟩,eq⟩
  have corr : (∏ q ∈ A, if q.val ∣ m then c q.val else 1) = ∏ p ∈ m.primeFactors,c p := by
    rw [← prod_filter,← imageB]
    exact (Finset.prod_image (f := c) (s := B) (g := fun q : Nat.Primes => q.val) (fun _ _ _ _ e => Subtype.ext e)).symm
  rw [← corr,← prod_mul_distrib]
  apply prod_congr rfl
  intro q _
  by_cases h : q.val ∣ m
  · simp only [if_pos h,c]
    have two : (2:ℝ) ≤ q.val := by exact_mod_cast q.property.two_le
    have qp : (q.val:ℝ) ≠ 0 := by linarith
    have m1 : (q.val:ℝ)-1 ≠ 0 := by linarith
    have denom : (q.val:ℝ)^2-q.val-1 ≠ 0 := by nlinarith [mul_nonneg (sub_nonneg.mpr two) (by linarith : (0:ℝ) ≤ q.val)]
    rw [← mul_div_assoc,eq_div_iff denom]
    field_simp [qp,m1]
    <;> ring
  · simp [h]

lemma pd_mono {A B R : Set ℕ} (h : A ⊆ B) (N : ℕ) :
    A.partialDensity R N ≤ B.partialDensity R N := by
  unfold Set.partialDensity
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_left _ (Set.inter_subset_inter_left R h))
    ((Set.finite_Iio N).subset Set.inter_subset_right)

lemma pd_union (A B R : Set ℕ) (N : ℕ) :
    (A ∪ B).partialDensity R N ≤ A.partialDensity R N + B.partialDensity R N := by
  unfold Set.partialDensity
  simp only [Set.union_inter_distrib_right,← add_div,← Nat.cast_add]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Set.ncard_union_le _ _) (Nat.cast_nonneg _)

lemma relative_sieve {ι : Type*} (R S : Set ℕ) (F T : ι → Set ℕ) (L : Filter ι) [L.NeBot]
    (d : ι → ℝ) (D : ℝ) (sub : ∀ i,S ⊆ F i) (miss : ∀ i, F i ⊆ S ∪ T i)
    (approx : ∀ᶠ i in L, (F i).HasDensity (d i) R) (lim : Tendsto d L (𝓝 D))
    (tail : ∀ ε > (0:ℝ), ∀ᶠ i in L, ∀ᶠ N : ℕ in atTop, (T i).partialDensity R N < ε) :
    S.HasDensity D R := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  have pos : 0<ε/3 := by positivity
  obtain ⟨i,hi,ht,ha⟩ := ((Metric.tendsto_nhds.mp lim _ pos).and ((tail _ pos).and approx)).exists
  have near := Metric.tendsto_nhds.mp ha _ pos
  filter_upwards [near,ht] with N hn htail
  have low := (pd_mono (R:=R) (miss i) N).trans (pd_union S (T i) R N)
  have high := pd_mono (R:=R) (sub i) N
  rw [Real.dist_eq,abs_lt] at hi hn ⊢
  change -(ε/3) < (F i).partialDensity R N-d i ∧ (F i).partialDensity R N-d i < ε/3 at hn
  change -ε < S.partialDensity R N-D ∧ S.partialDensity R N-D < ε
  constructor <;> linarith

lemma generator_iff (p a : ℕ) (hp : p.Prime) :
    orderOf (a:ZMod p)=p-1 ↔
      (a:ZMod p)≠0 ∧ ∀ q : Nat.Primes, q.val ∣ p-1 → (a:ZMod p)^((p-1)/q.val)≠1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have pp : 0 < p-1 := by have := hp.two_le; omega
  constructor
  · intro h
    have ha : (a:ZMod p)≠0 := by
      intro hz
      rw [hz,orderOf_zero] at h
      omega
    refine ⟨ha,?_⟩
    intro q hd hpow
    have divides := orderOf_dvd_of_pow_eq_one hpow
    rw [h] at divides
    exact (Nat.not_le_of_gt (Nat.div_lt_self pp q.property.one_lt))
      (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd pp hd) q.property.pos) divides)
  · rintro ⟨nz,good⟩
    exact orderOf_eq_of_pow_and_pow_div_prime pp (ZMod.pow_card_sub_one_eq_one nz)
      (fun q hq => good ⟨q,hq⟩)

lemma density_limit (m : ℕ) (hm : m ≠ 0) :
    Tendsto (fun P : Finset Nat.Primes => ∏ q ∈ P,
      if q.val ∣ m then 1-1/(q.val-1:ℝ) else 1-1/((q.val:ℝ)*(q.val-1:ℝ)))
      atTop (𝓝 (ArtinConstant * powCorrectionFactor m)) := by
  classical
  let E : Finset Nat.Primes := m.primeFactors.attach.image
    (fun p => ⟨p.val,(Nat.mem_primeFactors.mp p.property).1⟩)
  have containsE : ∀ p ∈ m.primeFactors, ∃ q ∈ E, q.val = p := by
    intro p hp
    exact ⟨⟨p,(Nat.mem_primeFactors.mp hp).1⟩,
      mem_image.mpr ⟨⟨p,hp⟩,mem_attach _ _,rfl⟩,rfl⟩
  have b : Tendsto (fun P : Finset Nat.Primes => ∏ q ∈ P, (1-1/((q.val:ℝ)*(q.val-1:ℝ))))
      atTop (𝓝 ArtinConstant) := artin_prod_limit
  apply (b.mul_const (powCorrectionFactor m)).congr'
  filter_upwards [eventually_ge_atTop E] with P hP
  apply Eq.symm
  apply corrected_prod m hm P
  intro p hp
  obtain ⟨q,hq,hv⟩ := containsE p hp
  exact ⟨q,hP hq,hv⟩

theorem main : H1 → H2 → type_of% @ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.variants.part_ii_power_squarefreePart_modeq_one := by
  intro finiteDensity tail a m b ha hb hm ho hs grh
  classical
  let F (P : Finset Nat.Primes) : Set ℕ := {p : ℕ | p.Prime ∧ (a:ZMod p) ≠ 0 ∧
    ∀ q ∈ P, q.val ∣ p-1 → (a:ZMod p)^((p-1)/q.val) ≠ 1}
  let T (P : Finset Nat.Primes) : Set ℕ := {p : ℕ | p.Prime ∧ (a:ZMod p) ≠ 0 ∧
    ∃ q : Nat.Primes, q ∉ P ∧ q.val ∣ p-1 ∧ (a:ZMod p)^((p-1)/q.val) = 1}
  let E : Finset Nat.Primes := (2 * b.squarefreePart).primeFactors.attach.image
    (fun p => ⟨p.val,(Nat.mem_primeFactors.mp p.property).1⟩)
  have approx : ∀ᶠ P : Finset Nat.Primes in atTop, F P |>.HasDensity
      ((∏ q ∈ P, if q.val ∣ m then 1-1/(q.val-1:ℝ) else 1-1/((q.val:ℝ)*(q.val-1:ℝ))) *
        entanglementFactor b m) {p | p.Prime} := by
    filter_upwards [eventually_ge_atTop E] with P hP
    refine finiteDensity a m b ha hb hm ho hs P fun q hq => hP ?_
    exact mem_image.mpr ⟨⟨q.val,Nat.mem_primeFactors.mpr ⟨q.property,hq,
      mul_ne_zero two_ne_zero (Nat.squarefreePart_ne_zero b)⟩⟩,mem_attach _ _,rfl⟩
  apply relative_sieve {p : ℕ | p.Prime} (S a) F T atTop _ _ _ _
    approx ((density_limit m (by omega)).mul_const (entanglementFactor b m))
    (tail a m b ha hb hm ho hs grh)
  · intro P p hp
    obtain ⟨hp,gen⟩ := hp
    have h : orderOf (a:ZMod p) = p-1 := by simpa using gen
    obtain ⟨nz,criterion⟩ := (generator_iff p a hp).mp h
    exact ⟨hp,nz,fun q _ => criterion q⟩
  · intro P p hp
    obtain ⟨hp,nz,small⟩ := hp
    by_cases h : ∀ q : Nat.Primes, q.val ∣ p-1 → (a:ZMod p)^((p-1)/q.val) ≠ 1
    · apply Or.inl
      exact ⟨hp,by simpa using (generator_iff p a hp).mpr ⟨nz,h⟩⟩
    · push_neg at h
      obtain ⟨q,hd,he⟩ := h
      exact Or.inr ⟨hp,nz,q,(fun mem => small q mem hd he),hd,he⟩

end OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_variants_part_ii_power_squarefreePart_modeq_one_R1
