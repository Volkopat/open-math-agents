import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H2_R1
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! Signed squarefree prime-ideal expansion for the first step proposed in
PR 12960. The finite prime sieve also proves the normalization of the product. -/
noncomputable section
namespace OMA.SquarefreeStep
open Complex Filter Set NumberField Asymptotics
open scoped NumberField Topology NNReal ENNReal Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev ideals := Ideal (𝓞 K)
abbrev fiber (n : ℕ) := {I : ideals K // Ideal.absNorm I = n}
abbrev a (n : ℕ) := Nat.card (fiber K n)

-- The coefficient estimate is the one used in the earlier Mellin audit.
theorem coeff_mean :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (a K k : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum, a, fiber]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem series_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (a K n : ℂ)) s := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (a K n : ℝ))
    (r := 1) (isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using coeff_mean K))
    (fun n => Nat.cast_nonneg _) zero_le_one hs
  simpa only [ofReal_natCast] using h

def weight (s : ℂ) (I : ideals K) : ℂ := (Ideal.absNorm I : ℂ) ^ (-s)

theorem weight_mul (s : ℂ) (I J : ideals K) :
    weight K s (I * J) = weight K s I * weight K s J := by
  simp only [weight, map_mul, Nat.cast_mul, natCast_mul_natCast_cpow]

theorem term_eq {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    LSeries.term (fun k => (a K k : ℂ)) s n = (a K n : ℂ) * (n : ℂ) ^ (-s) := by
  rw [LSeries.term_of_ne_zero' hs, cpow_neg, div_eq_mul_inv]

private abbrev fiberFintype (n : ℕ) : Fintype (fiber K n) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).fintype

theorem fiber_sum {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    (∑' I : fiber K n, weight K s I.val) = LSeries.term (fun k => (a K k : ℂ)) s n := by
  let _ := fiberFintype K n
  rw [term_eq K hs, tsum_fintype]
  simp [weight, fun I : fiber K n => I.property, a, Nat.card_eq_fintype_card, nsmul_eq_mul]

theorem fiber_norm {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    (∑' I : fiber K n, ‖weight K s I.val‖) = ‖LSeries.term (fun k => (a K k : ℂ)) s n‖ := by
  let _ := fiberFintype K n
  rw [term_eq K hs, tsum_fintype, norm_mul]
  simp [weight, fun I : fiber K n => I.property, a, Nat.card_eq_fintype_card, nsmul_eq_mul]

theorem norm_summable {s : ℂ} (hs : 1 < s.re) : Summable fun I => ‖weight K s I‖ := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  let F (n : ℕ) : Set (ideals K) := {I | Ideal.absNorm I = n}
  apply (summable_partition (s := F) (fun I => norm_nonneg _) ?_).2
  · refine ⟨fun n => ?_, ?_⟩
    · let _ := fiberFintype K n
      change Summable fun I : fiber K n => ‖weight K s I.val‖
      exact Summable.of_finite
    · change Summable fun n => ∑' I : fiber K n, ‖weight K s I.val‖
      simp_rw [fiber_norm K hs0]
      exact (series_summable K hs).norm
  · exact fun I => ⟨Ideal.absNorm I, rfl, fun _ h => h.symm⟩

theorem sum_eq_zeta {s : ℂ} (hs : 1 < s.re) : (∑' I, weight K s I) = dedekindZeta K s := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h := ((norm_summable K hs).of_norm.hasSum.tsum_fiberwise (fun I : ideals K => Ideal.absNorm I)).tsum_eq
  exact h.symm.trans (tsum_congr fun n => fiber_sum K hs0 n)

abbrev primeIdeals := {P : ideals K // P.IsPrime ∧ P ≠ ⊥}

theorem primeElement (p : primeIdeals K) : Prime p.val := (Ideal.prime_iff_isPrime p.property.2).mpr p.property.1

def sift (s : ℂ) (S : Finset (primeIdeals K)) (I : ideals K) : ℂ := by
  classical
  exact if ∀ p ∈ S, ¬p.val ∣ I then weight K s I else 0

theorem norm_sift_le (s : ℂ) (S : Finset (primeIdeals K)) (I : ideals K) :
    ‖sift K s S I‖ ≤ ‖weight K s I‖ := by
  classical
  unfold sift
  split <;> simp

theorem sift_mul (s : ℂ) {S : Finset (primeIdeals K)} {p : primeIdeals K} (hp : p ∉ S)
    (I : ideals K) : sift K s S (p.val * I) = weight K s p.val * sift K s S I := by
  classical
  have he : (∀ q ∈ S, ¬q.val ∣ p.val * I) ↔ (∀ q ∈ S, ¬q.val ∣ I) := by
    constructor
    · intro h q hq hI
      exact h q hq (dvd_mul_of_dvd_right hI _)
    · intro h q hq hmul
      rcases (primeElement K q).dvd_or_dvd hmul with hqp | hqI
      · have heq : q = p := Subtype.ext (associated_iff_eq.mp ((primeElement K q).associated_of_dvd (primeElement K p) hqp))
        exact hp (heq ▸ hq)
      · exact h q hq hqI
  simp only [sift, he, weight_mul]
  split <;> simp

theorem sift_insert {s : ℂ} (hs : 1 < s.re) (S : Finset (primeIdeals K)) (p : primeIdeals K)
    (hp : p ∉ S) :
    (∑' I, sift K s (insert p S) I) = (1 - weight K s p.val) * (∑' I, sift K s S I) := by
  classical
  let omitted (I : ideals K) := if p.val ∣ I then sift K s S I else 0
  have hS := (norm_summable K hs).of_norm_bounded (norm_sift_le K s S)
  have hO : Summable omitted := (norm_summable K hs).of_norm_bounded fun I => by
    dsimp [omitted]; split
    · exact norm_sift_le K s S I
    · simp
  have hdiff (I : ideals K) : sift K s (insert p S) I = sift K s S I - omitted I := by
    by_cases h : p.val ∣ I <;> simp [sift, omitted, h]
  have hi : Function.Injective (fun I : ideals K => p.val * I) := mul_right_injective₀ (primeElement K p).ne_zero
  have hsupp : Function.support omitted ⊆ Set.range (fun I : ideals K => p.val * I) := by
    intro I hI
    by_contra h
    have hn : ¬p.val ∣ I := fun ⟨d, hd⟩ => h ⟨d, hd.symm⟩
    exact hI (if_neg hn)
  have hsum : (∑' I, omitted I) = weight K s p.val * (∑' I, sift K s S I) := by
    rw [← hi.tsum_eq hsupp, ← tsum_mul_left]
    apply tsum_congr
    intro I
    simpa [omitted] using sift_mul K s hp I
  simp_rw [hdiff]
  rw [hS.tsum_sub hO, hsum, sub_mul, one_mul]

theorem sift_limit {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun S : Finset (primeIdeals K) => ∑' I, sift K s S I) atTop (𝓝 1) := by
  classical
  let g (I : ideals K) : ℂ := if I = 1 then 1 else 0
  have hg : (∑' I, g I) = 1 := by simp [g]
  rw [← hg]
  apply tendsto_tsum_of_dominated_convergence (norm_summable K hs)
  · intro I
    refine (tendsto_congr' ?_).2 (tendsto_const_nhds (x := g I))
    by_cases h1 : I = 1
    · subst I
      exact Filter.Eventually.of_forall fun S => by
        have h : ∀ q ∈ S, ¬(q : primeIdeals K).val ∣ (1 : ideals K) := fun q _ => (primeElement K q).not_dvd_one
        change (if ∀ q ∈ S, ¬q.val ∣ (1 : ideals K) then weight K s 1 else 0) = g 1
        rw [if_pos h]
        simp [weight, g]
    · by_cases h0 : I = 0
      · subst I
        have hs' : -s ≠ 0 := neg_ne_zero.mpr (by rintro rfl; norm_num at hs)
        exact Filter.Eventually.of_forall fun S => by simp [sift, weight, g, zero_cpow hs']
      · have hu : ¬IsUnit I := fun h => h1 (by simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp h)
        obtain ⟨P, hirr, hd⟩ := WfDvdMonoid.exists_irreducible_factor hu h0
        have hP : P ≠ ⊥ := by simpa only [Ideal.zero_eq_bot] using hirr.prime.ne_zero
        let p : primeIdeals K := ⟨P,(Ideal.prime_iff_isPrime hP).mp hirr.prime,hP⟩
        filter_upwards [eventually_finset_mem_atTop p] with S hS
        have hbad : ¬∀ q ∈ S, ¬q.val ∣ I := fun h => (h p hS) hd
        change (if ∀ q ∈ S, ¬q.val ∣ I then weight K s I else 0) = if I = 1 then 1 else 0
        rw [if_neg hbad, if_neg h1]
  · exact Filter.Eventually.of_forall fun S I => norm_sift_le K s S I

/-- Dedekind zeta is nonzero in the half-plane of absolute convergence. -/

def prodIdeal (S : Finset (primeIdeals K)) : ideals K := ∏ p ∈ S, p.val
def normProduct (S : Finset (primeIdeals K)) : ℕ := ∏ p ∈ S, Ideal.absNorm p.val
def coeff (n : ℕ) : ℂ := ∑' S : normProduct K ⁻¹' {n}, (-1:ℂ)^S.val.card

theorem dvd_prod_iff (p : primeIdeals K) (S : Finset (primeIdeals K)) :
    p.val ∣ prodIdeal K S ↔ p ∈ S := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [prodIdeal,Finset.prod_empty,Finset.notMem_empty,iff_false]
    exact (primeElement K p).not_dvd_one
  | @insert q S hq ih =>
    rw [prodIdeal,Finset.prod_insert hq,(primeElement K p).dvd_mul,Finset.mem_insert]
    change (p.val ∣ q.val ∨ p.val ∣ prodIdeal K S) ↔ _
    rw [ih]
    have hpq : p.val ∣ q.val ↔ p=q := by
      constructor
      · intro h; exact Subtype.ext (associated_iff_eq.mp ((primeElement K p).associated_of_dvd (primeElement K q) h))
      · rintro rfl; exact dvd_refl _
    rw [hpq]

theorem prod_injective : Function.Injective (prodIdeal K) := by
  intro S T h
  ext p
  rw [← dvd_prod_iff K p S,h,dvd_prod_iff]

theorem prod_weight (s : ℂ) (S : Finset (primeIdeals K)) :
    weight K s (prodIdeal K S) = ∏ p ∈ S, weight K s p.val := by
  induction S using Finset.induction_on with
  | empty => simp [prodIdeal,weight]
  | @insert p S hp ih =>
    rw [prodIdeal,Finset.prod_insert hp,weight_mul,Finset.prod_insert hp,← ih]; rfl

theorem reciprocal_expansion (s : ℂ) (hs : 1 < s.re) :
    ∃ w : ℂ, HasSum (LSeries.term (coeff K) s) w ∧ dedekindZeta K s*w=1 := by
  classical
  let W (S : Finset (primeIdeals K)) := ∏ p ∈ S, -weight K s p.val
  have hw (S : Finset (primeIdeals K)) : W S=(-1:ℂ)^S.card*weight K s (prodIdeal K S) := by
    simp only [W,Finset.prod_neg,prod_weight]
  have hsum : Summable W := by
    apply Summable.of_norm
    apply ((norm_summable K hs).comp_injective (prod_injective K)).congr
    intro S
    simp only [hw,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,Function.comp_apply]
  refine ⟨∑' S,W S,?_,?_⟩
  · have hf (n : ℕ) : (∑' S : normProduct K ⁻¹' {n}, W S.val) = LSeries.term (coeff K) s n := by
      rw [LSeries.term_of_ne_zero' (ne_zero_of_re_pos (zero_lt_one.trans hs)),div_eq_mul_inv,← cpow_neg,coeff,← tsum_mul_right]
      apply tsum_congr
      intro S
      have hn : Ideal.absNorm (prodIdeal K S.val)=n := by
        simpa only [prodIdeal,map_prod,normProduct] using (show normProduct K S.val=n from S.property)
      rw [hw,weight,hn]
    have H := hsum.hasSum.tsum_fiberwise (normProduct K)
    simpa only [hf] using H
  · have hp := hasProd_one_add_of_hasSum_prod (f := fun p : primeIdeals K => -weight K s p.val) hsum.hasSum
    have he (S : Finset (primeIdeals K)) :
        dedekindZeta K s * (∏ p ∈ S, (1 + -weight K s p.val)) = ∑' I, sift K s S I := by
      induction S using Finset.induction_on with
      | empty => simpa [sift] using (sum_eq_zeta K hs).symm
      | @insert p S hP ih =>
        rw [Finset.prod_insert hP,sift_insert K hs S p hP,← ih,sub_eq_add_neg]; ring
    exact tendsto_nhds_unique_of_eventuallyEq (hp.const_mul (dedekindZeta K s)) (sift_limit K hs)
      (Eventually.of_forall he)

end OMA.SquarefreeStep

theorem OMA.solution : OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R1.H1 := by
  intro K _ _
  exact OMA.SquarefreeStep.reciprocal_expansion K
