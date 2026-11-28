import FormalConjectures.Wikipedia.ArtinPrimitiveRootsConjecture
import Mathlib

-- Reduction ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.parts.ii.R1
-- Credit: @pyaf

/-! # A finite sieve for Artin's constant

A prime divisor of the index of a unit modulo p obstructs generation of the unit group.
The two remaining inputs are the finite Kummer-field density (Chebotarev: for a non-power `a`
whose squarefree part is not `1 mod 4`, the fields `ℚ(ζ_d, a^{1/d})`, `d` squarefree, have
degree `d φ(d)`, so the sieve over finitely many index primes has the Euler factors of Artin's
constant) and Hooley's tail estimate. The passage to density is proved below. The sieve lemmas
are adapted from the merged reduction of the power case (Steve Digital, #4044). See Hooley (1967),
and Lenstra, Moree and Stevenhagen, arXiv:1112.4816. -/

namespace OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_ii_R1

open Finset Set Real Filter Topology ArtinPrimitiveRootsConjecture
open scoped Classical

-- For each finite set of index primes, the Kummer splitting conditions have the Euler factors
-- of Artin's constant as density.
def H1 : Prop := ∀ a a_0 b : ℤ, a = a_0 * b ^ 2 → (∀ n m, m ≠ 1 → a ≠ n ^ m) → Squarefree a_0 →
    ¬a_0 ≡ 1 [ZMOD 4] → ∀ P : Finset Nat.Primes,
    {p : ℕ | p.Prime ∧ (a:ZMod p) ≠ 0 ∧
      ∀ q ∈ P, q.val ∣ p-1 → (a:ZMod p)^((p-1)/q.val) ≠ 1}.HasDensity
      (∏ q ∈ P, (1-1/((q.val:ℝ)*(q.val-1:ℝ)))) {p | p.Prime}

-- The analytic remainder counts primes whose index has a prime factor outside P.
def H2 : Prop := ∀ a a_0 b : ℤ, a = a_0 * b ^ 2 → (∀ n m, m ≠ 1 → a ≠ n ^ m) → Squarefree a_0 →
    ¬a_0 ≡ 1 [ZMOD 4] → HooleyHypothesis a →
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
    (approx : ∀ i, (F i).HasDensity (d i) R) (lim : Tendsto d L (𝓝 D))
    (tail : ∀ ε > (0:ℝ), ∀ᶠ i in L, ∀ᶠ N : ℕ in atTop, (T i).partialDensity R N < ε) :
    S.HasDensity D R := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  have pos : 0<ε/3 := by positivity
  obtain ⟨i,hi,ht⟩ := ((Metric.tendsto_nhds.mp lim _ pos).and (tail _ pos)).exists
  have near := Metric.tendsto_nhds.mp (approx i) _ pos
  filter_upwards [near,ht] with N hn htail
  have low := (pd_mono (R:=R) (miss i) N).trans (pd_union S (T i) R N)
  have high := pd_mono (R:=R) (sub i) N
  rw [Real.dist_eq,abs_lt] at hi hn ⊢
  change -(ε/3) < (F i).partialDensity R N-d i ∧ (F i).partialDensity R N-d i < ε/3 at hn
  change -ε < S.partialDensity R N-D ∧ S.partialDensity R N-D < ε
  constructor <;> linarith

lemma generator_iff (p : ℕ) (a : ℤ) (hp : p.Prime) :
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

theorem main : H1 → H2 → type_of% @ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.parts.ii := by
  intro finiteDensity tail a a_0 b ha hp hs hm grh
  classical
  let F (P : Finset Nat.Primes) : Set ℕ := {p : ℕ | p.Prime ∧ (a:ZMod p) ≠ 0 ∧
    ∀ q ∈ P, q.val ∣ p-1 → (a:ZMod p)^((p-1)/q.val) ≠ 1}
  let T (P : Finset Nat.Primes) : Set ℕ := {p : ℕ | p.Prime ∧ (a:ZMod p) ≠ 0 ∧
    ∃ q : Nat.Primes, q ∉ P ∧ q.val ∣ p-1 ∧ (a:ZMod p)^((p-1)/q.val) = 1}
  apply relative_sieve {p : ℕ | p.Prime} (S a) F T atTop _ _ _ _
    (finiteDensity a a_0 b ha hp hs hm) artin_prod_limit
    (tail a a_0 b ha hp hs hm grh)
  · intro P p hp
    obtain ⟨hp,gen⟩ := hp
    obtain ⟨nz,criterion⟩ := (generator_iff p a hp).mp gen
    exact ⟨hp,nz,fun q _ => criterion q⟩
  · intro P p hp
    obtain ⟨hp,nz,small⟩ := hp
    by_cases h : ∀ q : Nat.Primes, q.val ∣ p-1 → (a:ZMod p)^((p-1)/q.val) ≠ 1
    · exact Or.inl ⟨hp,(generator_iff p a hp).mpr ⟨nz,h⟩⟩
    · push_neg at h
      obtain ⟨q,hd,he⟩ := h
      exact Or.inr ⟨hp,nz,q,(fun mem => small q mem hd he),hd,he⟩

end OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_ii_R1
