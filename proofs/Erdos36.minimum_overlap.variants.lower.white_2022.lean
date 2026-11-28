import FormalConjectures.ErdosProblems.«36»
import Mathlib


-- ACCEPTED SOURCE: Erdos36.minimum_overlap.variants.lower.white_2022.R1

-- Reduction Erdos36.minimum_overlap.variants.lower.white_2022.R1 of Erdős Problem 36 — white 2022
-- Credit: @ivillar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
White (arXiv 2201.05704, Theorem 1) proves his bound for the function form of the minimum
overlap problem due to Moser, Murdeshwar and Swinnerton-Dyer: for measurable f from [-1,1] to
[0,1] with integral 1 and g = 1 - f on [-1,1], the overlap integral of f(t) g(x+t) over t is at
least 0.379005 for some x. This is `H1`. The statement about partitions of {1,...,2n} follows
from the elementary half of the Swinnerton-Dyer correspondence, split here into two steps.
`H3`: the step function of a partition (A,B) has overlap function at most 1/n times the
piecewise linear interpolation of the discrete overlap counts, written as a sum of tent
functions over A x B. `H2`: that interpolation never exceeds the maximum overlap.
-/

namespace OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1

open Filter MeasureTheory

/-- White's theorem for the function form of the minimum overlap problem. -/
def H1 : Prop := ∀ f : ℝ → ℝ, Measurable f → (∀ t, 0 ≤ f t ∧ f t ≤ 1) →
  (∫ t in (-1 : ℝ)..1, f t) = 1 →
  ∃ x : ℝ, (0.379005 : ℝ) ≤
    ∫ t in (-1 : ℝ)..1, f t * (Set.Icc (-1 : ℝ) 1).indicator (fun y => 1 - f y) (x + t)

/-- The tent interpolation of the overlap counts is at most the maximum overlap. -/
def H2 : Prop := ∀ (A B : Finset ℤ) (y : ℝ),
  ∑ p ∈ A ×ˢ B, max 0 (1 - |((p.2 - p.1 : ℤ) : ℝ) - y|) ≤ (Erdos36.MaxOverlap A B : ℝ)

/-- The step function of a partition has overlap function at most the tent interpolation
divided by n. -/
def H3 : Prop := ∀ (n : ℕ), 0 < n → ∀ A B : Finset ℤ, Disjoint A B →
  A ∪ B = Finset.Icc (1 : ℤ) (2 * n) → A.card = B.card →
  ∃ f : ℝ → ℝ, Measurable f ∧ (∀ t, 0 ≤ f t ∧ f t ≤ 1) ∧ (∫ t in (-1 : ℝ)..1, f t) = 1 ∧
    ∀ x : ℝ,
      (∫ t in (-1 : ℝ)..1, f t * (Set.Icc (-1 : ℝ) 1).indicator (fun y => 1 - f y) (x + t)) ≤
        (∑ p ∈ A ×ˢ B, max 0 (1 - |((p.2 - p.1 : ℤ) : ℝ) - n * x|)) / n

lemma overlap_le_card (A B : Finset ℤ) (k : ℤ) : Erdos36.Overlap A B k ≤ A.card := by
  unfold Erdos36.Overlap
  refine Finset.card_le_card_of_injOn Prod.fst (fun p hp => ?_) (fun p hp q hq h => ?_)
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · have hp2 := (Finset.mem_filter.mp hp).2
    have hq2 := (Finset.mem_filter.mp hq).2
    exact Prod.ext h (by omega)

lemma maxOverlap_le_card (A B : Finset ℤ) : Erdos36.MaxOverlap A B ≤ A.card :=
  ciSup_le fun k => overlap_le_card A B k

lemma card_left {n : ℕ} {A B : Finset ℤ} (hd : Disjoint A B)
    (hu : A ∪ B = Finset.Icc (1 : ℤ) (2 * n)) (hc : A.card = B.card) : A.card = n := by
  have h1 : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hd
  rw [hu, Int.card_Icc] at h1
  omega

lemma exists_min (n : ℕ) : ∃ A B : Finset ℤ, Disjoint A B ∧
    A ∪ B = Finset.Icc (1 : ℤ) (2 * n) ∧ A.card = B.card ∧
    Erdos36.MaxOverlap A B = Erdos36.M n := by
  have hne : {x : ℕ | ∃ (A : Finset ℤ) (B : Finset ℤ) (_ : Disjoint A B)
      (_ : A ∪ B = Finset.Icc (1 : ℤ) (2 * n)) (_ : A.card = B.card),
      Erdos36.MaxOverlap A B = x}.Nonempty := by
    refine ⟨_, Finset.Icc 1 n, Finset.Icc (n + 1) (2 * n), ?_, ?_, ?_, rfl⟩
    · rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_Icc] at ha hb
      omega
    · ext a
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    · rw [Int.card_Icc, Int.card_Icc]
      omega
  obtain ⟨A, B, hd, hu, hc, hm⟩ := Nat.sInf_mem hne
  exact ⟨A, B, hd, hu, hc, hm⟩

theorem main : H1 → H2 → H3 →
    type_of% @Erdos36.minimum_overlap.variants.lower.white_2022 := by
  intro h1 h2 h3
  have hle : ∀ n : ℕ, Erdos36.MinOverlapQuotient n ≤ 1 := by
    intro n
    obtain ⟨A, B, hd, hu, hc, hm⟩ := exists_min n
    have h4 : Erdos36.M n ≤ n := by
      rw [← hm, ← card_left hd hu hc]
      exact maxOverlap_le_card A B
    unfold Erdos36.MinOverlapQuotient
    have h5 : (Erdos36.M n : ℝ) ≤ n := by exact_mod_cast h4
    exact div_le_one_of_le₀ h5 (Nat.cast_nonneg n)
  have key : ∀ n : ℕ, 1 ≤ n → (0.379005 : ℝ) ≤ Erdos36.MinOverlapQuotient n := by
    intro n hn
    obtain ⟨A, B, hd, hu, hc, hm⟩ := exists_min n
    obtain ⟨f, hfm, hf01, hfint, hfx⟩ := h3 n hn A B hd hu hc
    obtain ⟨x, hx⟩ := h1 f hfm hf01 hfint
    have h6 := hfx x
    have h7 := h2 A B (n * x)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    unfold Erdos36.MinOverlapQuotient
    rw [← hm]
    calc (0.379005 : ℝ) ≤ _ := hx
      _ ≤ _ := h6
      _ ≤ (Erdos36.MaxOverlap A B : ℝ) / n := by gcongr
  exact Filter.le_liminf_of_le (Filter.isCoboundedUnder_ge_of_le _ hle)
    (Filter.eventually_atTop.mpr ⟨1, key⟩)

end OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1


-- ACCEPTED SOURCE: Erdos36.minimum_overlap.variants.lower.white_2022.R1.H1

/-!
# Proof of `Erdos36.minimum_overlap.variants.lower.white_2022.R1.H1`

White's (2022) lower bound `0.379005` for the continuous minimum overlap problem, proved via
an elementary `L^1` Fourier-duality method:
1. Exact Fubini identities express the moments and Fourier coefficients `A_m, B_m` of
   `M(x) = ∫_{-1}^1 f(t) g(x+t) dt` in terms of `h(t) = f(t) - 1/2`.
2. Symmetry `f(t) ↦ f(-t)` and `f(t) ↦ 1 - f(-t)` reduces to `E(M) ≥ 0` and `c₁ ≥ 0`,
   while Bessel's inequality gives `c₁² + d₁² ≤ 1/2`.
3. Moser's variance inequality handles `E(M) ≥ 0.42`.
4. Seven explicit `R = 6` trigonometric dual certificates (verified in pure integer arithmetic
   via a certified binary-tree trig table and second-order Taylor integral bounds) together with
   a 166-leaf dyadic integer octree cover the remaining region `0 ≤ E(M) ≤ 0.42`, `c₁ ≥ 0`,
   `c₁² + d₁² ≤ 1/2`.
-/

noncomputable section

open MeasureTheory Set Filter Real
open scoped BigOperators

namespace OMA.White2022H1

/-! ### Section 1: Overlap function, Fubini master identity, moments, Fourier coefficients, Bessel -/

private def gFun (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  (Icc (-1 : ℝ) 1).indicator (fun z => 1 - f z) y

private def MFun (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, f t * gFun f (x + t)

private def hFun (f : ℝ → ℝ) (t : ℝ) : ℝ := f t - 1 / 2

private lemma gFun_nonneg {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) (y : ℝ) :
    0 ≤ gFun f y := by
  unfold gFun
  by_cases hy : y ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hy]; linarith [(hf y).2]
  · rw [indicator_of_notMem hy]

private lemma gFun_le_one {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) (y : ℝ) :
    gFun f y ≤ 1 := by
  unfold gFun
  by_cases hy : y ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hy]; linarith [(hf y).1]
  · rw [indicator_of_notMem hy]; norm_num

private lemma MFun_nonneg {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) (x : ℝ) :
    0 ≤ MFun f x := by
  unfold MFun
  refine intervalIntegral.integral_nonneg (by norm_num) fun t _ => ?_
  exact mul_nonneg (hf t).1 (gFun_nonneg hf (x + t))

private lemma MFun_le_two {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) (x : ℝ) :
    MFun f x ≤ 2 := by
  unfold MFun
  have hint : IntervalIntegrable (fun t => f t * gFun f (x + t)) volume (-1) 1 := by
    refine IntervalIntegrable.mono_fun' (g := fun _ => (1 : ℝ)) intervalIntegrable_const ?_ ?_
    · exact (hfm.mul (((measurable_const.sub hfm).indicator measurableSet_Icc).comp
        (measurable_const.add measurable_id))).aestronglyMeasurable
    · filter_upwards with t
      rw [Real.norm_of_nonneg (mul_nonneg (hf t).1 (gFun_nonneg hf _))]
      exact mul_le_one₀ (hf t).2 (gFun_nonneg hf _) (gFun_le_one hf _)
  calc ∫ t in (-1 : ℝ)..1, f t * gFun f (x + t)
      ≤ ∫ _t in (-1 : ℝ)..1, (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const
          (fun t _ => mul_le_one₀ (hf t).2 (gFun_nonneg hf _) (gFun_le_one hf _))
    _ = 2 := by norm_num

private lemma MFun_measurable {f : ℝ → ℝ} (hfm : Measurable f) : Measurable (MFun f) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => f p.2 * gFun f (p.1 + p.2)) :=
    (hfm.comp measurable_snd).mul
      (((measurable_const.sub hfm).indicator measurableSet_Icc).comp
        (measurable_fst.add measurable_snd))
  have hEq : MFun f = fun x => ∫ t in Ioc (-1 : ℝ) 1, f t * gFun f (x + t) := by
    ext x; unfold MFun; exact intervalIntegral.integral_of_le (by norm_num)
  rw [hEq]
  exact hmeas.stronglyMeasurable.integral_prod_right'.measurable

private lemma MFun_mul_cont_intervalIntegrable {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) {φ : ℝ → ℝ} (hφ : Continuous φ) (a b : ℝ) :
    IntervalIntegrable (fun x => φ x * MFun f x) volume a b := by
  obtain ⟨C, hC⟩ := isCompact_uIcc (a := a) (b := b) |>.exists_bound_of_continuousOn hφ.continuousOn
  refine IntervalIntegrable.mono_fun' (g := fun _ => 2 * max C 0) intervalIntegrable_const
    (hφ.measurable.mul (MFun_measurable hfm)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  rw [norm_mul, Real.norm_of_nonneg (MFun_nonneg hf x)]
  have h1 : ‖φ x‖ ≤ max C 0 := (hC x (uIoc_subset_uIcc hx)).trans (le_max_left _ _)
  have h2 : MFun f x ≤ 2 := MFun_le_two hfm hf x
  nlinarith [norm_nonneg (φ x), MFun_nonneg hf x]

private lemma cont_mul_f_intervalIntegrable {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) {φ : ℝ → ℝ} (hφ : Continuous φ) (a b : ℝ) :
    IntervalIntegrable (fun t => φ t * f t) volume a b := by
  obtain ⟨C, hC⟩ := isCompact_uIcc (a := a) (b := b) |>.exists_bound_of_continuousOn hφ.continuousOn
  refine IntervalIntegrable.mono_fun' (g := fun _ => max C 0) intervalIntegrable_const
    (hφ.measurable.mul hfm).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [norm_mul, Real.norm_of_nonneg (hf t).1]
  exact (mul_le_of_le_one_right (norm_nonneg _) (hf t).2).trans
    ((hC t (uIoc_subset_uIcc ht)).trans (le_max_left _ _))

private lemma cont_mul_h_intervalIntegrable {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) {φ : ℝ → ℝ} (hφ : Continuous φ) (a b : ℝ) :
    IntervalIntegrable (fun t => φ t * hFun f t) volume a b := by
  have hEq : (fun t => φ t * hFun f t) = fun t => φ t * f t - (1 / 2 : ℝ) * φ t := by
    ext t; unfold hFun; ring
  rw [hEq]
  exact (cont_mul_f_intervalIntegrable hfm hf hφ a b).sub
    ((continuous_const.mul hφ).intervalIntegrable a b)

/-- Master Fubini identity: for any continuous `φ`,
`∫_{-2}^2 φ(x) M(x) dx = ∫_{-1}^1 ∫_{-1}^1 φ(y - t) f(t) (1 - f(y)) dy dt`. -/
private lemma integral_mul_M {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∫ x in (-2 : ℝ)..2, φ x * MFun f x =
      ∫ t in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, φ (y - t) * (f t * (1 - f y)) := by
  have hle2 : (-2 : ℝ) ≤ 2 := by norm_num
  have hle1 : (-1 : ℝ) ≤ 1 := by norm_num
  rw [intervalIntegral.integral_of_le hle2]
  simp_rw [MFun, intervalIntegral.integral_of_le hle1]
  have hpull : ∀ x : ℝ, φ x * ∫ t in Ioc (-1 : ℝ) 1, f t * gFun f (x + t) =
      ∫ t in Ioc (-1 : ℝ) 1, φ x * (f t * gFun f (x + t)) := fun x =>
    (integral_const_mul (φ x) _).symm
  simp_rw [hpull]
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hφ.continuousOn
  have hIntProd : Integrable (Function.uncurry fun x t : ℝ => φ x * (f t * gFun f (x + t)))
      ((volume.restrict (Ioc (-2 : ℝ) 2)).prod (volume.restrict (Ioc (-1 : ℝ) 1))) := by
    have hmeas : Measurable (Function.uncurry fun x t : ℝ => φ x * (f t * gFun f (x + t))) :=
      (hφ.measurable.comp measurable_fst).mul
        ((hfm.comp measurable_snd).mul
          (((measurable_const.sub hfm).indicator measurableSet_Icc).comp
            (measurable_fst.add measurable_snd)))
    refine Integrable.mono' (integrable_const (max C 0)) hmeas.aestronglyMeasurable ?_
    have hmem : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioc (-2 : ℝ) 2)).prod
        (volume.restrict (Ioc (-1 : ℝ) 1))), p.1 ∈ Ioc (-2 : ℝ) 2 :=
      Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst
        (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hmem] with ⟨x, t⟩ hx
    simp only [Function.uncurry, norm_mul]
    have hfg : ‖f t * gFun f (x + t)‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (mul_nonneg (hf t).1 (gFun_nonneg hf _))]
      exact mul_le_one₀ (hf t).2 (gFun_nonneg hf _) (gFun_le_one hf _)
    calc ‖φ x‖ * (‖f t‖ * ‖gFun f (x + t)‖)
        = ‖φ x‖ * ‖f t * gFun f (x + t)‖ := by rw [norm_mul]
      _ ≤ ‖φ x‖ * 1 := mul_le_mul_of_nonneg_left hfg (norm_nonneg _)
      _ = ‖φ x‖ := mul_one _
      _ ≤ C := hC x (Ioc_subset_Icc_self hx)
      _ ≤ max C 0 := le_max_left _ _
  rw [MeasureTheory.integral_integral_swap hIntProd]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [← intervalIntegral.integral_of_le hle2]
  have hcomp : ∫ x in (-2 : ℝ)..2, φ x * (f t * gFun f (x + t)) =
      ∫ y in (-2 + t)..(2 + t), φ (y - t) * (f t * gFun f y) := by
    have h1 := intervalIntegral.integral_comp_add_right
      (fun y => φ (y - t) * (f t * gFun f y)) t (a := (-2 : ℝ)) (b := 2)
    simpa [add_sub_cancel_right] using h1
  rw [hcomp]
  have ht1 : -2 + t ≤ -1 := by linarith [ht.2]
  have ht2 : (1 : ℝ) ≤ 2 + t := by linarith [ht.1]
  have hint_sub : ∀ a b : ℝ,
      IntervalIntegrable (fun y => φ (y - t) * (f t * gFun f y)) volume a b := by
    intro a b
    obtain ⟨K, hK⟩ := isCompact_uIcc (a := a) (b := b) |>.exists_bound_of_continuousOn
      (hφ.comp (continuous_id.sub continuous_const)).continuousOn
    refine IntervalIntegrable.mono_fun' (g := fun _ => max K 0) intervalIntegrable_const ?_ ?_
    · exact ((hφ.measurable.comp (measurable_id.sub measurable_const)).mul
        (measurable_const.mul ((measurable_const.sub hfm).indicator measurableSet_Icc))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
      rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (hf t).1 (gFun_nonneg hf y))]
      have hfg : f t * gFun f y ≤ 1 := mul_le_one₀ (hf t).2 (gFun_nonneg hf y) (gFun_le_one hf y)
      calc ‖φ (y - t)‖ * (f t * gFun f y)
          ≤ ‖φ (y - t)‖ * 1 := mul_le_mul_of_nonneg_left hfg (norm_nonneg _)
        _ = ‖φ (y - t)‖ := mul_one _
        _ ≤ K := hK y (uIoc_subset_uIcc hy)
        _ ≤ max K 0 := le_max_left _ _
  have hleft : ∫ y in (-2 + t)..(-1 : ℝ), φ (y - t) * (f t * gFun f y) = 0 := by
    rw [intervalIntegral.integral_of_le ht1, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have hnot : y ∉ Icc (-1 : ℝ) 1 := fun h => by linarith [hy.2, h.1]
    simp [gFun, indicator_of_notMem hnot]
  have hright : ∫ y in (1 : ℝ)..(2 + t), φ (y - t) * (f t * gFun f y) = 0 := by
    rw [intervalIntegral.integral_of_le ht2]
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have hnot : y ∉ Icc (-1 : ℝ) 1 := fun h => by linarith [hy.1, h.2]
    simp [gFun, indicator_of_notMem hnot]
  have hsplit : ∫ y in (-2 + t)..(2 + t), φ (y - t) * (f t * gFun f y) =
      ∫ y in (-1 : ℝ)..1, φ (y - t) * (f t * gFun f y) := by
    have h1 := (intervalIntegral.integral_add_adjacent_intervals
      (hint_sub (-2 + t) (-1)) (hint_sub (-1) (2 + t))).symm
    have h2 := (intervalIntegral.integral_add_adjacent_intervals
      (hint_sub (-1) 1) (hint_sub 1 (2 + t))).symm
    rw [h1, h2, hleft, hright, zero_add, add_zero]
  rw [hsplit, intervalIntegral.integral_of_le hle1]
  refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
  have hmem : y ∈ Icc (-1 : ℝ) 1 := Ioc_subset_Icc_self hy
  simp [gFun, indicator_of_mem hmem]

private lemma integral_h_eq_zero {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (hfint : (∫ t in (-1 : ℝ)..1, f t) = 1) :
    ∫ t in (-1 : ℝ)..1, hFun f t = 0 := by
  unfold hFun
  rw [intervalIntegral.integral_sub (by simpa using cont_mul_f_intervalIntegrable hfm hf (φ := fun _ => (1 : ℝ)) continuous_const (-1) 1)
    intervalIntegrable_const, hfint]
  norm_num

private lemma integral_one_sub_f {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (hfint : (∫ t in (-1 : ℝ)..1, f t) = 1) :
    ∫ y in (-1 : ℝ)..1, (1 - f y) = 1 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (by simpa using cont_mul_f_intervalIntegrable hfm hf (φ := fun _ => (1 : ℝ)) continuous_const (-1) 1), hfint]
  norm_num

private lemma integral_M_eq_one {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (hfint : (∫ t in (-1 : ℝ)..1, f t) = 1) :
    ∫ x in (-2 : ℝ)..2, MFun f x = 1 := by
  have h1 := integral_mul_M hfm hf (φ := fun _ => (1 : ℝ)) continuous_const
  simp only [one_mul] at h1
  rw [h1]
  have h2 : ∀ t : ℝ, ∫ y in (-1 : ℝ)..1, f t * (1 - f y) = f t := fun t => by
    rw [intervalIntegral.integral_const_mul, integral_one_sub_f hfm hf hfint, mul_one]
  simp_rw [h2, hfint]

private def EM (f : ℝ → ℝ) : ℝ := ∫ x in (-2 : ℝ)..2, x * MFun f x

private lemma EM_eq {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (hfint : (∫ t in (-1 : ℝ)..1, f t) = 1) :
    EM f = -2 * ∫ t in (-1 : ℝ)..1, t * hFun f t := by
  unfold EM
  rw [integral_mul_M hfm hf (φ := fun x => x) continuous_id]
  have hid : Continuous (fun y : ℝ => y) := continuous_id
  have hf0 : IntervalIntegrable f volume (-1) 1 := by
    simpa using cont_mul_f_intervalIntegrable hfm hf (φ := fun _ => (1 : ℝ)) continuous_const (-1) 1
  have hf1 : IntervalIntegrable (fun y : ℝ => y * f y) volume (-1) 1 :=
    cont_mul_f_intervalIntegrable hfm hf hid (-1) 1
  have h1 : ∀ t : ℝ, ∫ y in (-1 : ℝ)..1, (y - t) * (f t * (1 - f y)) =
      f t * (∫ y in (-1 : ℝ)..1, y * (1 - f y)) - t * f t := fun t => by
    have hEq : (fun y => (y - t) * (f t * (1 - f y))) =
        fun y => f t * (y * (1 - f y)) - (t * f t) * (1 - f y) := by ext y; ring
    have hi1 : IntervalIntegrable (fun y : ℝ => y * (1 - f y)) volume (-1) 1 := by
      have : (fun y : ℝ => y * (1 - f y)) = fun y => y - y * f y := by ext y; ring
      rw [this]
      exact (hid.intervalIntegrable (-1) 1).sub hf1
    rw [hEq, intervalIntegral.integral_sub (hi1.const_mul _) ((intervalIntegrable_const.sub hf0).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_one_sub_f hfm hf hfint, mul_one]
  simp_rw [h1]
  rw [intervalIntegral.integral_sub (hf0.mul_const _) hf1,
    intervalIntegral.integral_mul_const, hfint, one_mul]
  have hy0 : ∫ y in (-1 : ℝ)..1, y = 0 := by norm_num
  have hsub : ∫ y in (-1 : ℝ)..1, y * (1 - f y) = - ∫ y in (-1 : ℝ)..1, y * f y := by
    have hEq : (fun y : ℝ => y * (1 - f y)) = fun y => y - y * f y := by ext y; ring
    rw [hEq, intervalIntegral.integral_sub (hid.intervalIntegrable (-1) 1) hf1, hy0, zero_sub]
  rw [hsub]
  have hth : ∫ t in (-1 : ℝ)..1, t * hFun f t = ∫ t in (-1 : ℝ)..1, t * f t := by
    have hEq : (fun t : ℝ => t * hFun f t) = fun t => t * f t - (1 / 2 : ℝ) * t := by
      ext t; unfold hFun; ring
    rw [hEq, intervalIntegral.integral_sub hf1 ((hid.intervalIntegrable (-1) 1).const_mul (1 / 2)),
      intervalIntegral.integral_const_mul, hy0, mul_zero, sub_zero]
  rw [hth]; ring

private lemma second_moment_M {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (hfint : (∫ t in (-1 : ℝ)..1, f t) = 1) :
    ∫ x in (-2 : ℝ)..2, x ^ 2 * MFun f x = 2 / 3 + (EM f) ^ 2 / 2 := by
  rw [integral_mul_M hfm hf (continuous_pow 2)]
  set I1 := ∫ y in (-1 : ℝ)..1, y * f y
  set I2 := ∫ y in (-1 : ℝ)..1, y ^ 2 * f y
  have hid : Continuous (fun y : ℝ => y) := continuous_id
  have hf0 : IntervalIntegrable f volume (-1) 1 := by
    simpa using cont_mul_f_intervalIntegrable hfm hf (φ := fun _ => (1 : ℝ)) continuous_const (-1) 1
  have hf1 : IntervalIntegrable (fun t : ℝ => t * f t) volume (-1) 1 :=
    cont_mul_f_intervalIntegrable hfm hf hid (-1) 1
  have hf2 : IntervalIntegrable (fun t : ℝ => t ^ 2 * f t) volume (-1) 1 :=
    cont_mul_f_intervalIntegrable hfm hf (continuous_pow 2) (-1) 1
  have hy0 : ∫ y in (-1 : ℝ)..1, y = 0 := by norm_num
  have hy2 : ∫ y in (-1 : ℝ)..1, y ^ 2 = (2 / 3 : ℝ) := by norm_num
  have h1g : ∫ y in (-1 : ℝ)..1, y * (1 - f y) = -I1 := by
    have hEq : (fun y : ℝ => y * (1 - f y)) = fun y => y - y * f y := by ext y; ring
    rw [hEq, intervalIntegral.integral_sub (hid.intervalIntegrable (-1) 1) hf1, hy0, zero_sub]
  have h2g : ∫ y in (-1 : ℝ)..1, y ^ 2 * (1 - f y) = 2 / 3 - I2 := by
    have hEq : (fun y : ℝ => y ^ 2 * (1 - f y)) = fun y => y ^ 2 - y ^ 2 * f y := by ext y; ring
    rw [hEq, intervalIntegral.integral_sub ((continuous_pow 2).intervalIntegrable (-1) 1) hf2, hy2]
  have hinner : ∀ t : ℝ, ∫ y in (-1 : ℝ)..1, (y - t) ^ 2 * (f t * (1 - f y)) =
      f t * (2 / 3 - I2) + (2 * I1) * (t * f t) + t ^ 2 * f t := fun t => by
    have hEq : (fun y : ℝ => (y - t) ^ 2 * (f t * (1 - f y))) =
        fun y => (f t * (y ^ 2 * (1 - f y)) - (2 * t * f t) * (y * (1 - f y))) +
          (t ^ 2 * f t) * (1 - f y) := by ext y; ring
    have hi2 : IntervalIntegrable (fun y => y ^ 2 * (1 - f y)) volume (-1) 1 := by
      have : (fun y : ℝ => y ^ 2 * (1 - f y)) = fun y => y ^ 2 - y ^ 2 * f y := by ext y; ring
      rw [this]
      exact ((continuous_pow 2).intervalIntegrable (-1) 1).sub hf2
    have hi1 : IntervalIntegrable (fun y => y * (1 - f y)) volume (-1) 1 := by
      have : (fun y : ℝ => y * (1 - f y)) = fun y => y - y * f y := by ext y; ring
      rw [this]
      exact (hid.intervalIntegrable (-1) 1).sub hf1
    have hi0 : IntervalIntegrable (fun y => 1 - f y) volume (-1) 1 :=
      intervalIntegrable_const.sub hf0
    rw [hEq, intervalIntegral.integral_add ((hi2.const_mul _).sub (hi1.const_mul _)) (hi0.const_mul _),
      intervalIntegral.integral_sub (hi2.const_mul _) (hi1.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, h2g, h1g, integral_one_sub_f hfm hf hfint]
    ring
  simp_rw [hinner]
  rw [intervalIntegral.integral_add ((hf0.mul_const _).add (hf1.const_mul _)) hf2,
    intervalIntegral.integral_add (hf0.mul_const _) (hf1.const_mul _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, hfint]
  have hEM : EM f = -2 * I1 := by
    rw [EM_eq hfm hf hfint]
    have hEq : (fun t : ℝ => t * hFun f t) = fun t => t * f t - (1 / 2 : ℝ) * t := by
      ext t; unfold hFun; ring
    rw [hEq, intervalIntegral.integral_sub hf1 ((hid.intervalIntegrable (-1) 1).const_mul (1 / 2)),
      intervalIntegral.integral_const_mul, hy0, mul_zero, sub_zero]
  rw [hEM]; ring

private def sVal (m : ℕ) : ℝ := Real.sin (π * (m : ℝ) / 2) / (π * (m : ℝ))

private def alphaM (f : ℝ → ℝ) (m : ℕ) : ℝ :=
  (1 / 2) * ∫ t in (-1 : ℝ)..1, Real.cos (π * (m : ℝ) * t / 2) * hFun f t

private def betaM (f : ℝ → ℝ) (m : ℕ) : ℝ :=
  (1 / 2) * ∫ t in (-1 : ℝ)..1, Real.sin (π * (m : ℝ) * t / 2) * hFun f t

private lemma integral_cos_symm (ω : ℝ) (hω : ω ≠ 0) :
    ∫ t in (-1 : ℝ)..1, Real.cos (ω * t) = 2 * Real.sin ω / ω := by
  have hd : ∀ t ∈ uIcc (-1 : ℝ) 1,
      HasDerivAt (fun x => Real.sin (ω * x) / ω) (Real.cos (ω * t)) t := fun t _ => by
    have h1 := (Real.hasDerivAt_sin (ω * t)).comp t ((hasDerivAt_id t).const_mul ω)
    simpa [mul_comm, mul_div_cancel_left₀ _ hω] using h1.div_const ω
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable (-1) 1)]
  simp [Real.sin_neg]; ring

private lemma integral_sin_symm (ω : ℝ) :
    ∫ t in (-1 : ℝ)..1, Real.sin (ω * t) = 0 := by
  by_cases hω : ω = 0
  · simp [hω]
  · have hd : ∀ t ∈ uIcc (-1 : ℝ) 1,
        HasDerivAt (fun x => -Real.cos (ω * x) / ω) (Real.sin (ω * t)) t := fun t _ => by
      have h1 := ((Real.hasDerivAt_cos (ω * t)).comp t ((hasDerivAt_id t).const_mul ω)).neg
      simpa [mul_comm, mul_div_cancel_left₀ _ hω] using h1.div_const ω
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable (-1) 1)]
    simp [Real.cos_neg]

private lemma A_m_eq {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (m : ℕ) (hm : 1 ≤ m) :
    (1 / 2) * ∫ x in (-2 : ℝ)..2, Real.cos (π * (m : ℝ) * x / 2) * MFun f x =
      2 * (sVal m) ^ 2 - 2 * ((alphaM f m) ^ 2 + (betaM f m) ^ 2) := by
  set ω : ℝ := π * (m : ℝ) / 2
  have hω : ω ≠ 0 := by positivity
  have hcos_cont : Continuous (fun x : ℝ => Real.cos (ω * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsin_cont : Continuous (fun x : ℝ => Real.sin (ω * x)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hArg : ∀ x : ℝ, Real.cos (π * (m : ℝ) * x / 2) = Real.cos (ω * x) := fun x => by
    congr 1; simp [ω]; ring
  simp_rw [hArg]
  rw [integral_mul_M hfm hf hcos_cont]
  have hfg_eq : ∀ t y : ℝ, f t * (1 - f y) =
      1 / 4 + (hFun f t - hFun f y) / 2 - hFun f t * hFun f y := fun t y => by
    unfold hFun; ring
  have hIc : ∫ y in (-1 : ℝ)..1, Real.cos (ω * y) = 4 * sVal m := by
    rw [integral_cos_symm ω hω]; unfold sVal; simp only [ω]; field_simp; ring
  have hIs : ∫ y in (-1 : ℝ)..1, Real.sin (ω * y) = 0 := integral_sin_symm ω
  have hhc : ∫ y in (-1 : ℝ)..1, Real.cos (ω * y) * hFun f y = 2 * alphaM f m := by
    unfold alphaM
    have : (fun y => Real.cos (π * (m : ℝ) * y / 2) * hFun f y) =
        fun y => Real.cos (ω * y) * hFun f y := by ext y; congr 2; simp [ω]; ring
    rw [this]; ring
  have hhs : ∫ y in (-1 : ℝ)..1, Real.sin (ω * y) * hFun f y = 2 * betaM f m := by
    unfold betaM
    have : (fun y => Real.sin (π * (m : ℝ) * y / 2) * hFun f y) =
        fun y => Real.sin (ω * y) * hFun f y := by ext y; congr 2; simp [ω]; ring
    rw [this]; ring
  have hic := hcos_cont.intervalIntegrable (μ := volume) (-1) 1
  have his := hsin_cont.intervalIntegrable (μ := volume) (-1) 1
  have hihc := cont_mul_h_intervalIntegrable hfm hf hcos_cont (-1) 1
  have hihs := cont_mul_h_intervalIntegrable hfm hf hsin_cont (-1) 1
  have hinner : ∀ t : ℝ,
      ∫ y in (-1 : ℝ)..1, Real.cos (ω * (y - t)) * (f t * (1 - f y)) =
        ((1 / 4 + hFun f t / 2) * Real.cos (ω * t)) * (4 * sVal m) -
        ((1 / 2 + hFun f t) * Real.cos (ω * t)) * (2 * alphaM f m) -
        ((1 / 2 + hFun f t) * Real.sin (ω * t)) * (2 * betaM f m) := fun t => by
    have hEq : (fun y => Real.cos (ω * (y - t)) * (f t * (1 - f y))) = fun y =>
        (((1 / 4 + hFun f t / 2) * Real.cos (ω * t)) * Real.cos (ω * y) +
         ((1 / 4 + hFun f t / 2) * Real.sin (ω * t)) * Real.sin (ω * y)) -
        (((1 / 2 + hFun f t) * Real.cos (ω * t)) * (Real.cos (ω * y) * hFun f y) +
         ((1 / 2 + hFun f t) * Real.sin (ω * t)) * (Real.sin (ω * y) * hFun f y)) := by
      ext y
      rw [mul_sub, Real.cos_sub, hfg_eq]
      ring
    rw [hEq, intervalIntegral.integral_sub ((hic.const_mul _).add (his.const_mul _))
        ((hihc.const_mul _).add (hihs.const_mul _)),
      intervalIntegral.integral_add (hic.const_mul _) (his.const_mul _),
      intervalIntegral.integral_add (hihc.const_mul _) (hihs.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hIc, hIs, hhc, hhs]
    ring
  simp_rw [hinner]
  have hEq2 : (fun t => ((1 / 4 + hFun f t / 2) * Real.cos (ω * t)) * (4 * sVal m) -
      ((1 / 2 + hFun f t) * Real.cos (ω * t)) * (2 * alphaM f m) -
      ((1 / 2 + hFun f t) * Real.sin (ω * t)) * (2 * betaM f m)) = fun t =>
      ((sVal m - alphaM f m) * Real.cos (ω * t) - betaM f m * Real.sin (ω * t)) +
      ((2 * sVal m - 2 * alphaM f m) * (Real.cos (ω * t) * hFun f t) -
       (2 * betaM f m) * (Real.sin (ω * t) * hFun f t)) := by ext t; ring
  rw [hEq2, intervalIntegral.integral_add ((hic.const_mul _).sub (his.const_mul _))
      ((hihc.const_mul _).sub (hihs.const_mul _)),
    intervalIntegral.integral_sub (hic.const_mul _) (his.const_mul _),
    intervalIntegral.integral_sub (hihc.const_mul _) (hihs.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hIc, hIs, hhc, hhs]
  ring

private lemma B_m_eq {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (m : ℕ) (hm : 1 ≤ m) :
    (1 / 2) * ∫ x in (-2 : ℝ)..2, Real.sin (π * (m : ℝ) * x / 2) * MFun f x =
      -4 * sVal m * betaM f m := by
  set ω : ℝ := π * (m : ℝ) / 2
  have hω : ω ≠ 0 := by positivity
  have hcos_cont : Continuous (fun x : ℝ => Real.cos (ω * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsin_cont : Continuous (fun x : ℝ => Real.sin (ω * x)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hArg : ∀ x : ℝ, Real.sin (π * (m : ℝ) * x / 2) = Real.sin (ω * x) := fun x => by
    congr 1; simp [ω]; ring
  simp_rw [hArg]
  rw [integral_mul_M hfm hf hsin_cont]
  have hfg_eq : ∀ t y : ℝ, f t * (1 - f y) =
      1 / 4 + (hFun f t - hFun f y) / 2 - hFun f t * hFun f y := fun t y => by
    unfold hFun; ring
  have hIc : ∫ y in (-1 : ℝ)..1, Real.cos (ω * y) = 4 * sVal m := by
    rw [integral_cos_symm ω hω]; unfold sVal; simp only [ω]; field_simp; ring
  have hIs : ∫ y in (-1 : ℝ)..1, Real.sin (ω * y) = 0 := integral_sin_symm ω
  have hhc : ∫ y in (-1 : ℝ)..1, Real.cos (ω * y) * hFun f y = 2 * alphaM f m := by
    unfold alphaM
    have : (fun y => Real.cos (π * (m : ℝ) * y / 2) * hFun f y) =
        fun y => Real.cos (ω * y) * hFun f y := by ext y; congr 2; simp [ω]; ring
    rw [this]; ring
  have hhs : ∫ y in (-1 : ℝ)..1, Real.sin (ω * y) * hFun f y = 2 * betaM f m := by
    unfold betaM
    have : (fun y => Real.sin (π * (m : ℝ) * y / 2) * hFun f y) =
        fun y => Real.sin (ω * y) * hFun f y := by ext y; congr 2; simp [ω]; ring
    rw [this]; ring
  have hic := hcos_cont.intervalIntegrable (μ := volume) (-1) 1
  have his := hsin_cont.intervalIntegrable (μ := volume) (-1) 1
  have hihc := cont_mul_h_intervalIntegrable hfm hf hcos_cont (-1) 1
  have hihs := cont_mul_h_intervalIntegrable hfm hf hsin_cont (-1) 1
  have hinner : ∀ t : ℝ,
      ∫ y in (-1 : ℝ)..1, Real.sin (ω * (y - t)) * (f t * (1 - f y)) =
        (-(1 / 4 + hFun f t / 2) * Real.sin (ω * t)) * (4 * sVal m) -
        ((1 / 2 + hFun f t) * Real.cos (ω * t)) * (2 * betaM f m) +
        ((1 / 2 + hFun f t) * Real.sin (ω * t)) * (2 * alphaM f m) := fun t => by
    have hEq : (fun y => Real.sin (ω * (y - t)) * (f t * (1 - f y))) = fun y =>
        (((1 / 4 + hFun f t / 2) * Real.cos (ω * t)) * Real.sin (ω * y) -
         ((1 / 4 + hFun f t / 2) * Real.sin (ω * t)) * Real.cos (ω * y)) -
        (((1 / 2 + hFun f t) * Real.cos (ω * t)) * (Real.sin (ω * y) * hFun f y) -
         ((1 / 2 + hFun f t) * Real.sin (ω * t)) * (Real.cos (ω * y) * hFun f y)) := by
      ext y
      rw [mul_sub, Real.sin_sub, hfg_eq]
      ring
    rw [hEq, intervalIntegral.integral_sub ((his.const_mul _).sub (hic.const_mul _))
        ((hihs.const_mul _).sub (hihc.const_mul _)),
      intervalIntegral.integral_sub (his.const_mul _) (hic.const_mul _),
      intervalIntegral.integral_sub (hihs.const_mul _) (hihc.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hIc, hIs, hhc, hhs]
    ring
  simp_rw [hinner]
  have hEq2 : (fun t => (-(1 / 4 + hFun f t / 2) * Real.sin (ω * t)) * (4 * sVal m) -
      ((1 / 2 + hFun f t) * Real.cos (ω * t)) * (2 * betaM f m) +
      ((1 / 2 + hFun f t) * Real.sin (ω * t)) * (2 * alphaM f m)) = fun t =>
      ((-betaM f m) * Real.cos (ω * t) + (alphaM f m - sVal m) * Real.sin (ω * t)) +
      ((-2 * betaM f m) * (Real.cos (ω * t) * hFun f t) +
       (2 * alphaM f m - 2 * sVal m) * (Real.sin (ω * t) * hFun f t)) := by ext t; ring
  rw [hEq2, intervalIntegral.integral_add ((hic.const_mul _).add (his.const_mul _))
      ((hihc.const_mul _).add (hihs.const_mul _)),
    intervalIntegral.integral_add (hic.const_mul _) (his.const_mul _),
    intervalIntegral.integral_add (hihc.const_mul _) (hihs.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hIc, hIs, hhc, hhs]
  ring

private lemma sVal_two : sVal 2 = 0 := by
  unfold sVal; simp [show π * (2 : ℝ) / 2 = π by ring]

private def c1Val (f : ℝ → ℝ) : ℝ := 2 * alphaM f 2
private def d1Val (f : ℝ → ℝ) : ℝ := 2 * betaM f 2

private lemma bessel_c1_d1 {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) :
    (c1Val f) ^ 2 + (d1Val f) ^ 2 ≤ 1 / 2 := by
  set c := c1Val f
  set d := d1Val f
  have hc : ∫ t in (-1 : ℝ)..1, Real.cos (π * t) * hFun f t = c := by
    simp only [c, c1Val, alphaM]
    have : (fun t : ℝ => Real.cos (π * (2 : ℕ) * t / 2) * hFun f t) =
        fun t => Real.cos (π * t) * hFun f t := by ext t; congr 2; push_cast; ring
    rw [this]; ring
  have hd : ∫ t in (-1 : ℝ)..1, Real.sin (π * t) * hFun f t = d := by
    simp only [d, d1Val, betaM]
    have : (fun t : ℝ => Real.sin (π * (2 : ℕ) * t / 2) * hFun f t) =
        fun t => Real.sin (π * t) * hFun f t := by ext t; congr 2; push_cast; ring
    rw [this]; ring
  have hcos2 : ∫ t in (-1 : ℝ)..1, (Real.cos (π * t)) ^ 2 = 1 := by
    have hEq : (fun t : ℝ => (Real.cos (π * t)) ^ 2) = fun t => (1 + Real.cos ((2 * π) * t)) / 2 := by
      ext t; have := Real.cos_two_mul (π * t); rw [show 2 * (π * t) = (2 * π) * t by ring] at this; linarith
    have hc1 : Continuous (fun t : ℝ => Real.cos ((2 * π) * t)) :=
      Real.continuous_cos.comp (continuous_const.mul continuous_id)
    rw [hEq, intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const
      (hc1.intervalIntegrable (-1) 1),
      integral_cos_symm (2 * π) (by positivity)]
    simp [Real.sin_two_pi]
  have hsin2 : ∫ t in (-1 : ℝ)..1, (Real.sin (π * t)) ^ 2 = 1 := by
    have hEq : (fun t : ℝ => (Real.sin (π * t)) ^ 2) = fun t => 1 - (Real.cos (π * t)) ^ 2 := by
      ext t; linarith [Real.sin_sq_add_cos_sq (π * t)]
    have hc2 : Continuous (fun t : ℝ => (Real.cos (π * t)) ^ 2) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2
    rw [hEq, intervalIntegral.integral_sub intervalIntegrable_const
      (hc2.intervalIntegrable (-1) 1),
      hcos2]; norm_num
  have hcs : ∫ t in (-1 : ℝ)..1, Real.cos (π * t) * Real.sin (π * t) = 0 := by
    have hEq : (fun t : ℝ => Real.cos (π * t) * Real.sin (π * t)) =
        fun t => Real.sin ((2 * π) * t) / 2 := by
      ext t; have := Real.sin_two_mul (π * t); rw [show 2 * (π * t) = (2 * π) * t by ring] at this
      linarith
    rw [hEq, intervalIntegral.integral_div, integral_sin_symm (2 * π), zero_div]
  have hh2_int : IntervalIntegrable (fun t => (hFun f t) ^ 2) volume (-1) 1 := by
    refine IntervalIntegrable.mono_fun' (g := fun _ => (1 / 4 : ℝ)) intervalIntegrable_const
      ((hfm.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have ht := hf t; unfold hFun; nlinarith
  have hh2_le : ∫ t in (-1 : ℝ)..1, (hFun f t) ^ 2 ≤ 1 / 2 := by
    calc ∫ t in (-1 : ℝ)..1, (hFun f t) ^ 2
        ≤ ∫ _t in (-1 : ℝ)..1, (1 / 4 : ℝ) :=
          intervalIntegral.integral_mono_on (by norm_num) hh2_int intervalIntegrable_const fun t _ => by
            have ht := hf t; unfold hFun; nlinarith
      _ = 1 / 2 := by norm_num
  have h0 : 0 ≤ ∫ t in (-1 : ℝ)..1, (hFun f t - c * Real.cos (π * t) - d * Real.sin (π * t)) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  have hcos_c : Continuous (fun t : ℝ => Real.cos (π * t)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hsin_c : Continuous (fun t : ℝ => Real.sin (π * t)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hexp : ∫ t in (-1 : ℝ)..1, (hFun f t - c * Real.cos (π * t) - d * Real.sin (π * t)) ^ 2 =
      (∫ t in (-1 : ℝ)..1, (hFun f t) ^ 2) - c ^ 2 - d ^ 2 := by
    have hEq : (fun t : ℝ => (hFun f t - c * Real.cos (π * t) - d * Real.sin (π * t)) ^ 2) =
        fun t => ((hFun f t) ^ 2 - (2 * c) * (Real.cos (π * t) * hFun f t) -
          (2 * d) * (Real.sin (π * t) * hFun f t)) +
          (c ^ 2 * (Real.cos (π * t)) ^ 2 + d ^ 2 * (Real.sin (π * t)) ^ 2 +
          (2 * c * d) * (Real.cos (π * t) * Real.sin (π * t))) := by ext t; ring
    have ihc := cont_mul_h_intervalIntegrable hfm hf hcos_c (-1) 1
    have ihs := cont_mul_h_intervalIntegrable hfm hf hsin_c (-1) 1
    have ic2 : IntervalIntegrable (fun t : ℝ => (Real.cos (π * t)) ^ 2) volume (-1) 1 :=
      (hcos_c.pow 2).intervalIntegrable (-1) 1
    have is2 : IntervalIntegrable (fun t : ℝ => (Real.sin (π * t)) ^ 2) volume (-1) 1 :=
      (hsin_c.pow 2).intervalIntegrable (-1) 1
    have ics : IntervalIntegrable (fun t : ℝ => Real.cos (π * t) * Real.sin (π * t)) volume (-1) 1 :=
      (hcos_c.mul hsin_c).intervalIntegrable (-1) 1
    rw [hEq, intervalIntegral.integral_add ((hh2_int.sub (ihc.const_mul _)).sub (ihs.const_mul _))
        (((ic2.const_mul _).add (is2.const_mul _)).add (ics.const_mul _)),
      intervalIntegral.integral_sub (hh2_int.sub (ihc.const_mul _)) (ihs.const_mul _),
      intervalIntegral.integral_sub hh2_int (ihc.const_mul _),
      intervalIntegral.integral_add ((ic2.const_mul _).add (is2.const_mul _)) (ics.const_mul _),
      intervalIntegral.integral_add (ic2.const_mul _) (is2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hc, hd, hcos2, hsin2, hcs]
    ring
  linarith

/-! Symmetry reduction: WLOG `0 ≤ EM f` and `0 ≤ c1Val f`. -/

private lemma symm_neg {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (hfint : (∫ t in (-1 : ℝ)..1, f t) = 1) :
    let f' := fun t => f (-t)
    Measurable f' ∧ (∀ t, 0 ≤ f' t ∧ f' t ≤ 1) ∧ (∫ t in (-1 : ℝ)..1, f' t) = 1 ∧
      (∀ x, MFun f' x = MFun f (-x)) ∧ EM f' = -EM f := by
  intro f'
  refine ⟨hfm.comp measurable_neg, fun t => hf (-t), ?_, ?_, ?_⟩
  · have h := intervalIntegral.integral_comp_neg f (a := (-1 : ℝ)) (b := 1)
    simp only [neg_neg] at h
    simpa [f'] using h.trans hfint
  · intro x
    unfold MFun
    have h := intervalIntegral.integral_comp_neg (fun t => f t * gFun f (-x + t)) (a := (-1 : ℝ)) (b := 1)
    have hEq : (fun t => f (-t) * gFun f (-x + -t)) = fun t => f' t * gFun f' (x + t) := by
      ext t; simp only [f', gFun]
      have hmem : (-x + -t) ∈ Icc (-1 : ℝ) 1 ↔ (x + t) ∈ Icc (-1 : ℝ) 1 := by
        simp only [mem_Icc]; constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
      by_cases hx : (x + t) ∈ Icc (-1 : ℝ) 1
      · rw [indicator_of_mem (hmem.mpr hx), indicator_of_mem hx]; ring_nf
      · rw [indicator_of_notMem (mt hmem.mp hx), indicator_of_notMem hx]
    simpa [hEq] using h
  · unfold EM
    have hM : ∀ x, MFun f' x = MFun f (-x) := by
      intro x; unfold MFun
      have h := intervalIntegral.integral_comp_neg (fun t => f t * gFun f (-x + t)) (a := (-1 : ℝ)) (b := 1)
      have hEq : (fun t => f (-t) * gFun f (-x + -t)) = fun t => f' t * gFun f' (x + t) := by
        ext t; simp only [f', gFun]
        have hmem : (-x + -t) ∈ Icc (-1 : ℝ) 1 ↔ (x + t) ∈ Icc (-1 : ℝ) 1 := by
          simp only [mem_Icc]; constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
        by_cases hx : (x + t) ∈ Icc (-1 : ℝ) 1
        · rw [indicator_of_mem (hmem.mpr hx), indicator_of_mem hx]; ring_nf
        · rw [indicator_of_notMem (mt hmem.mp hx), indicator_of_notMem hx]
      simpa [hEq] using h
    simp_rw [hM]
    have h := intervalIntegral.integral_comp_neg (fun x => x * MFun f x) (a := (-2 : ℝ)) (b := 2)
    have hEq : (fun x => -x * MFun f (-x)) = fun x => -(x * MFun f (-x)) := by ext x; ring
    rw [show (∫ x in (-2 : ℝ)..2, x * MFun f (-x)) = - ∫ x in (-2 : ℝ)..2, -(x * MFun f (-x)) by
      rw [intervalIntegral.integral_neg, neg_neg], ← hEq]
    simpa using congrArg Neg.neg h

private lemma symm_comp_neg {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (hfint : (∫ t in (-1 : ℝ)..1, f t) = 1) :
    let f' := fun t => 1 - f (-t)
    Measurable f' ∧ (∀ t, 0 ≤ f' t ∧ f' t ≤ 1) ∧ (∫ t in (-1 : ℝ)..1, f' t) = 1 ∧
      (∀ x, MFun f' x = MFun f x) ∧ EM f' = EM f ∧ c1Val f' = -c1Val f := by
  intro f'
  have hfm' : Measurable f' := measurable_const.sub (hfm.comp measurable_neg)
  have hf' : ∀ t, 0 ≤ f' t ∧ f' t ≤ 1 := fun t => by
    have := hf (-t); simp only [f']; constructor <;> linarith
  have hfint' : (∫ t in (-1 : ℝ)..1, f' t) = 1 := by
    have h1 := (symm_neg hfm hf hfint).2.2.1
    have hfneg_int : IntervalIntegrable (fun t => f (-t)) volume (-1) 1 := by
      simpa using cont_mul_f_intervalIntegrable (hfm.comp measurable_neg) (fun t => hf (-t)) (φ := fun _ => (1 : ℝ)) continuous_const (-1) 1
    rw [show f' = fun t => 1 - f (-t) from rfl,
      intervalIntegral.integral_sub intervalIntegrable_const hfneg_int, h1]
    norm_num
  have hM : ∀ x, MFun f' x = MFun f x := fun x => by
    unfold MFun
    -- Change variable u = -(x + t) <=> t = -x - u
    have hEq1 : ∀ t ∈ Icc (-1 : ℝ) 1,
        f' t * gFun f' (x + t) =
          (Icc (-1 : ℝ) 1).indicator (fun u => f u * gFun f (x + u)) (-(x + t)) := by
      intro t ht
      simp only [f', gFun]
      have hmem : -(x + t) ∈ Icc (-1 : ℝ) 1 ↔ x + t ∈ Icc (-1 : ℝ) 1 := by
        simp only [mem_Icc]; constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
      by_cases hx : x + t ∈ Icc (-1 : ℝ) 1
      · rw [indicator_of_mem hx, indicator_of_mem (hmem.mpr hx)]
        have hmem2 : x + -(x + t) ∈ Icc (-1 : ℝ) 1 := by
          simp only [mem_Icc] at ht ⊢; constructor <;> linarith
        rw [indicator_of_mem hmem2]
        have : x + -(x + t) = -t := by ring
        rw [this]; ring_nf
      · rw [indicator_of_notMem hx, indicator_of_notMem (mt hmem.mp hx), mul_zero]
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    have hcongr : ∫ t in Ioc (-1 : ℝ) 1, f' t * gFun f' (x + t) =
        ∫ t in Ioc (-1 : ℝ) 1, (Icc (-1 : ℝ) 1).indicator (fun u => f u * gFun f (x + u)) (-(x + t)) :=
      setIntegral_congr_fun measurableSet_Ioc fun t ht => hEq1 t (Ioc_subset_Icc_self ht)
    rw [hcongr, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    have hcomp1 := intervalIntegral.integral_comp_sub_left
      (fun u => (Icc (-1 : ℝ) 1).indicator (fun v => f v * gFun f (x + v)) u) (-x) (a := (-1 : ℝ)) (b := 1)
    have hEq2 : (fun t => (Icc (-1 : ℝ) 1).indicator (fun v => f v * gFun f (x + v)) (-(x + t))) =
        fun t => (Icc (-1 : ℝ) 1).indicator (fun v => f v * gFun f (x + v)) (-x - t) := by
      ext t; congr 1; ring
    rw [hEq2, hcomp1]
    -- Now ∫ u in (-x - 1)..(-x + 1), (Icc (-1) 1).indicator (fun v => f v * gFun f (x + v)) u
    -- Notice: if v ∈ [-1, 1] and x + v ∈ [-1, 1], then v ∈ [-x - 1, -x + 1]!
    -- So the integrand vanishes outside [-x - 1, -x + 1] AND outside [-1, 1], i.e. supported on their intersection!
    have hsupp : ∀ u, (Icc (-1 : ℝ) 1).indicator (fun v => f v * gFun f (x + v)) u =
        (Icc (-x - 1) (-x + 1)).indicator (fun v => (Icc (-1 : ℝ) 1).indicator (fun w => f w * gFun f (x + w)) v) u := by
      intro u
      by_cases hu : u ∈ Icc (-x - 1) (-x + 1)
      · rw [indicator_of_mem hu]
      · rw [indicator_of_notMem hu]
        by_cases hu1 : u ∈ Icc (-1 : ℝ) 1
        · rw [indicator_of_mem hu1]
          have hnot : x + u ∉ Icc (-1 : ℝ) 1 := by
            intro h; apply hu; simp only [mem_Icc] at h ⊢; constructor <;> linarith
          simp [gFun, indicator_of_notMem hnot]
        · rw [indicator_of_notMem hu1]
    have hsupp2 : ∀ u, (Icc (-x - 1) (-x + 1)).indicator
        (fun v => (Icc (-1 : ℝ) 1).indicator (fun w => f w * gFun f (x + w)) v) u =
        (Icc (-1 : ℝ) 1).indicator
          (fun v => (Icc (-x - 1) (-x + 1)).indicator (fun w => f w * gFun f (x + w)) v) u := by
      intro u
      by_cases h1 : u ∈ Icc (-x - 1) (-x + 1) <;> by_cases h2 : u ∈ Icc (-1 : ℝ) 1 <;>
        simp [indicator_of_mem, indicator_of_notMem, h1, h2]
    have hle_x : -x - 1 ≤ -x + 1 := by linarith
    have hle_1 : (-1 : ℝ) ≤ 1 := by norm_num
    rw [sub_neg_eq_add, intervalIntegral.integral_of_le hle_x, intervalIntegral.integral_of_le hle_1,
      ← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
    -- Replace Ioc by Icc (measure-zero difference)
    have hae : ∀ (a b : ℝ) (F : ℝ → ℝ),
        (Ioc a b).indicator F =ᵐ[volume] (Icc a b).indicator F := fun a b F => by
      have hne : ∀ᵐ u ∂volume, u ≠ a := ae_iff.mpr (by
        rw [show {u : ℝ | ¬u ≠ a} = {a} by ext u; simp]
        exact measure_singleton a)
      filter_upwards [hne] with u hu
      by_cases h : u ∈ Ioc a b
      · rw [indicator_of_mem h, indicator_of_mem (Ioc_subset_Icc_self h)]
      · rw [indicator_of_notMem h, indicator_of_notMem]
        intro hcc; apply h
        exact ⟨lt_of_le_of_ne hcc.1 (Ne.symm hu), hcc.2⟩
    rw [integral_congr_ae (hae _ _ _), integral_congr_ae (hae _ _ _)]
    congr 1; ext u
    exact (hsupp u).symm
  refine ⟨hfm', hf', hfint', hM, by simp [EM, hM], ?_⟩
  simp only [c1Val, alphaM]
  have h1 : (fun t : ℝ => Real.cos (π * (2 : ℕ) * t / 2) * hFun f' t) =
      fun t => -(Real.cos (π * (2 : ℕ) * (-t) / 2) * hFun f (-t)) := by
    ext t; simp only [f', hFun]
    have : Real.cos (π * (2 : ℕ) * (-t) / 2) = Real.cos (π * (2 : ℕ) * t / 2) := by
      rw [show π * (2 : ℕ) * (-t) / 2 = -(π * (2 : ℕ) * t / 2) by ring, Real.cos_neg]
    rw [this]; ring
  rw [h1, intervalIntegral.integral_neg]
  have h2 := intervalIntegral.integral_comp_neg (fun t : ℝ => Real.cos (π * (2 : ℕ) * t / 2) * hFun f t) (a := (-1 : ℝ)) (b := 1)
  simp only [neg_neg] at h2
  rw [h2]; ring

/-! ### Section 2: Moser's variance bound for `E(M) ≥ 0.42` -/

private lemma moser_contradiction {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (hfint : (∫ t in (-1 : ℝ)..1, f t) = 1)
    (hM_le : ∀ x, MFun f x ≤ (379005 : ℝ) / 1000000)
    (hE : (42 : ℝ) / 100 ≤ EM f) : False := by
  set Ω : ℝ := (379005 : ℝ) / 1000000
  set E : ℝ := EM f
  set a : ℝ := 1 / (2 * Ω)
  have hΩ : 0 < Ω := by norm_num [Ω]
  have ha : 0 < a := by positivity
  -- Pointwise: ((x - E)^2 - a^2) * M(x) ≥ -Ω * max 0 (a^2 - (x - E)^2)
  have hpt : ∀ x : ℝ, -Ω * max 0 (a ^ 2 - (x - E) ^ 2) ≤ ((x - E) ^ 2 - a ^ 2) * MFun f x := by
    intro x
    by_cases h : (x - E) ^ 2 ≤ a ^ 2
    · rw [max_eq_right (by linarith)]
      have h1 : MFun f x ≤ Ω := hM_le x
      nlinarith
    · push Not at h
      rw [max_eq_left (by linarith), mul_zero]
      exact mul_nonneg (by linarith) (MFun_nonneg hf x)
  have hphi_cont : Continuous (fun x : ℝ => (x - E) ^ 2 - a ^ 2) :=
    ((continuous_id.sub continuous_const).pow 2).sub continuous_const
  have hmax_cont : Continuous (fun x : ℝ => -Ω * max 0 (a ^ 2 - (x - E) ^ 2)) :=
    continuous_const.mul (continuous_const.max (continuous_const.sub
      ((continuous_id.sub continuous_const).pow 2)))
  have hInt_le : ∫ x in (-2 : ℝ)..2, -Ω * max 0 (a ^ 2 - (x - E) ^ 2) ≤
      ∫ x in (-2 : ℝ)..2, ((x - E) ^ 2 - a ^ 2) * MFun f x :=
    intervalIntegral.integral_mono_on (by norm_num) (hmax_cont.intervalIntegrable (-2) 2)
      (MFun_mul_cont_intervalIntegrable hfm hf hphi_cont (-2) 2) (fun x _ => hpt x)
  -- Compute RHS = 2/3 - E^2/2 - a^2
  have hRHS : ∫ x in (-2 : ℝ)..2, ((x - E) ^ 2 - a ^ 2) * MFun f x = 2 / 3 - E ^ 2 / 2 - a ^ 2 := by
    have hEq : (fun x => ((x - E) ^ 2 - a ^ 2) * MFun f x) =
        fun x => x ^ 2 * MFun f x - (2 * E) * (x * MFun f x) + (E ^ 2 - a ^ 2) * MFun f x := by
      ext x; ring
    have i2 := MFun_mul_cont_intervalIntegrable hfm hf (continuous_pow 2) (-2) 2
    have i1 := MFun_mul_cont_intervalIntegrable hfm hf (φ := fun x => x) continuous_id (-2) 2
    have i0 := MFun_mul_cont_intervalIntegrable hfm hf (φ := fun _ => (1 : ℝ)) continuous_const (-2) 2
    simp only [one_mul] at i0
    rw [hEq, intervalIntegral.integral_add (i2.sub (i1.const_mul _)) (i0.const_mul _),
      intervalIntegral.integral_sub i2 (i1.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      second_moment_M hfm hf hfint, integral_M_eq_one hfm hf hfint]
    change 2 / 3 + E ^ 2 / 2 - 2 * E * E + (E ^ 2 - a ^ 2) * 1 = 2 / 3 - E ^ 2 / 2 - a ^ 2
    ring
  -- Bound ∫_{-2}^2 max 0 (a^2 - (x - E)^2) dx ≤ ∫_{E-a}^{E+a} (a^2 - (x - E)^2) dx = 4/3 * a^3
  have hmax_le : ∫ x in (-2 : ℝ)..2, max 0 (a ^ 2 - (x - E) ^ 2) ≤ (4 / 3 : ℝ) * a ^ 3 := by
    have hmc : Continuous (fun x : ℝ => max 0 (a ^ 2 - (x - E) ^ 2)) :=
      continuous_const.max (continuous_const.sub ((continuous_id.sub continuous_const).pow 2))
    set L := min (-2 : ℝ) (E - a)
    set R' := max (2 : ℝ) (E + a)
    have h1 : ∫ x in (-2 : ℝ)..2, max 0 (a ^ 2 - (x - E) ^ 2) ≤
        ∫ x in L..R', max 0 (a ^ 2 - (x - E) ^ 2) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2),
        intervalIntegral.integral_of_le (by linarith [min_le_left (-2 : ℝ) (E - a), le_max_left (2 : ℝ) (E + a)])]
      refine setIntegral_mono_set (hmc.integrableOn_Ioc)
        (ae_of_all _ fun x => le_max_left 0 _)
        (Eventually.of_forall fun x hx => ⟨lt_of_le_of_lt (min_le_left _ _) hx.1,
          le_trans hx.2 (le_max_left _ _)⟩)
    have h2 : ∫ x in L..R', max 0 (a ^ 2 - (x - E) ^ 2) =
        ∫ x in (E - a)..(E + a), (a ^ 2 - (x - E) ^ 2) := by
      have hL : L ≤ E - a := min_le_right _ _
      have hR : E + a ≤ R' := le_max_right _ _
      have hzeroL : ∫ x in L..(E - a), max 0 (a ^ 2 - (x - E) ^ 2) = 0 := by
        rw [intervalIntegral.integral_of_le hL]
        refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
        exact max_eq_left (by nlinarith [hx.2])
      have hzeroR : ∫ x in (E + a)..R', max 0 (a ^ 2 - (x - E) ^ 2) = 0 := by
        rw [intervalIntegral.integral_of_le hR]
        refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
        exact max_eq_left (by nlinarith [hx.1])
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hmc.intervalIntegrable L (E - a)) (hmc.intervalIntegrable (E - a) R'),
        ← intervalIntegral.integral_add_adjacent_intervals
        (hmc.intervalIntegrable (E - a) (E + a)) (hmc.intervalIntegrable (E + a) R'),
        hzeroL, hzeroR, zero_add, add_zero]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le (by linarith)] at hx
      exact max_eq_right (by nlinarith [hx.1, hx.2])
    have h3 : ∫ x in (E - a)..(E + a), (a ^ 2 - (x - E) ^ 2) = (4 / 3 : ℝ) * a ^ 3 := by
      have hc := intervalIntegral.integral_comp_sub_right (fun u : ℝ => a ^ 2 - u ^ 2) E
        (a := E - a) (b := E + a)
      rw [show E - a - E = -a by ring, show E + a - E = a by ring] at hc
      rw [hc]
      have hd : ∀ u ∈ uIcc (-a) a, HasDerivAt (fun x => a ^ 2 * x - x ^ 3 / 3) (a ^ 2 - u ^ 2) u :=
        fun u _ => by
          have h1 := ((hasDerivAt_id u).const_mul (a ^ 2)).sub ((hasDerivAt_pow 3 u).div_const 3)
          rw [show a ^ 2 - u ^ 2 = a ^ 2 * 1 - ((3 : ℕ) : ℝ) * u ^ (3 - 1) / 3 by norm_num]
          exact h1
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((continuous_const.sub (continuous_pow 2)).intervalIntegrable (-a) a)]
      ring
    exact h1.trans (h2.trans h3).le
  rw [intervalIntegral.integral_const_mul] at hInt_le
  have hmain : -Ω * ((4 / 3 : ℝ) * a ^ 3) ≤ 2 / 3 - E ^ 2 / 2 - a ^ 2 := by
    have hneg : -Ω * ((4 / 3 : ℝ) * a ^ 3) ≤ -Ω * ∫ x in (-2 : ℝ)..2, max 0 (a ^ 2 - (x - E) ^ 2) := by
      nlinarith [hmax_le, hΩ]
    exact hneg.trans (hInt_le.trans hRHS.le)
  have h12 : 1 / (12 * Ω ^ 2) ≤ 2 / 3 - E ^ 2 / 2 := by
    have : a ^ 2 - Ω * ((4 / 3 : ℝ) * a ^ 3) = 1 / (12 * Ω ^ 2) := by
      simp only [a]; field_simp; ring
    linarith
  have hnum : 2 / 3 - ((42 : ℝ) / 100) ^ 2 / 2 < 1 / (12 * Ω ^ 2) := by
    simp only [Ω]; norm_num
  nlinarith

/-! ### Section 3: Certified Binary-Tree Integer Trig Table (`θ₀ = π / 2048`, `SB = 10^10`) -/

private def SB : ℤ := 10000000000
private def C1 : ℤ := 9999988235
private def S1 : ℤ := 15339802
private def θ₀ : ℝ := π / 2048

private def trigNext (p : ℤ × ℤ) : ℤ × ℤ :=
  ((p.1 * C1 - p.2 * S1) / SB, (p.2 * C1 + p.1 * S1) / SB)

private def trigStep : ℕ → ℤ × ℤ
  | 0 => (SB, 0)
  | n + 1 => trigNext (trigStep n)

private inductive TrigTree : Type
  | leaf : ℤ × ℤ → TrigTree
  | node : TrigTree → TrigTree → TrigTree

private def buildTrigTree : ℕ → ℤ × ℤ → TrigTree × (ℤ × ℤ)
  | 0, p => (TrigTree.leaf p, trigNext p)
  | d + 1, p =>
      let (l, p1) := buildTrigTree d p
      let (r, p2) := buildTrigTree d p1
      (TrigTree.node l r, p2)

private def TrigTree.get : TrigTree → ℕ → ℕ → ℤ × ℤ
  | TrigTree.leaf p, _, _ => p
  | TrigTree.node l r, d + 1, k =>
      if k < 2 ^ d then l.get d k else r.get d (k - 2 ^ d)
  | TrigTree.node l _, 0, _ => l.get 0 0

private def trigTree10 : TrigTree := (buildTrigTree 10 (SB, 0)).1

private lemma buildTrigTree_spec (d : ℕ) (n : ℕ) :
    (buildTrigTree d (trigStep n)).2 = trigStep (n + 2 ^ d) ∧
    ∀ k < 2 ^ d, (buildTrigTree d (trigStep n)).1.get d k = trigStep (n + k) := by
  induction d generalizing n with
  | zero =>
      simp only [buildTrigTree, pow_zero, TrigTree.get]
      refine ⟨rfl, fun k hk => ?_⟩
      have hk0 : k = 0 := by omega
      subst hk0; simp
  | succ d ih =>
      simp only [buildTrigTree]
      have h1 := ih n
      have h2 := ih (n + 2 ^ d)
      rw [h1.1]
      refine ⟨?_, fun k hk => ?_⟩
      · rw [h2.1, pow_succ]; ring_nf
      · simp only [TrigTree.get]
        split_ifs with hlt
        · exact h1.2 k hlt
        · have hk' : k - 2 ^ d < 2 ^ d := by rw [pow_succ] at hk; omega
          rw [h2.2 (k - 2 ^ d) hk']
          congr 1; omega

private lemma trigTree10_get (k : ℕ) (hk : k < 1024) :
    trigTree10.get 10 k = trigStep k := by
  have h := (buildTrigTree_spec 10 0).2 k (by norm_num; exact hk)
  simpa [trigTree10, trigStep] using h

private def trigQuad (r : ℕ) : ℤ × ℤ :=
  if r < 1024 then trigTree10.get 10 r else (0, SB)

private def cosInt (k : ℤ) : ℤ :=
  let r := (k % 4096).toNat
  if r ≤ 1024 then (trigQuad r).1
  else if r ≤ 2048 then -(trigQuad (2048 - r)).1
  else if r ≤ 3072 then -(trigQuad (r - 2048)).1
  else (trigQuad (4096 - r)).1

private def sinInt (k : ℤ) : ℤ :=
  let r := (k % 4096).toNat
  if r ≤ 1024 then (trigQuad r).2
  else if r ≤ 2048 then (trigQuad (2048 - r)).2
  else if r ≤ 3072 then -(trigQuad (r - 2048)).2
  else -(trigQuad (4096 - r)).2

private lemma c1_s1_err :
    |Real.cos θ₀ - (C1 : ℝ) / (SB : ℝ)| ≤ 2 / (SB : ℝ) ∧
    |Real.sin θ₀ - (S1 : ℝ) / (SB : ℝ)| ≤ 6 / (SB : ℝ) := by
  have hpi1 : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
  have hpi2 : π < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hθ_lo : (153398078 : ℝ) / 10 ^ 11 < θ₀ := by unfold θ₀; linarith
  have hθ_hi : θ₀ < (153398079 : ℝ) / 10 ^ 11 := by unfold θ₀; linarith
  have hθ_pos : 0 < θ₀ := by linarith
  have hsin_hi : Real.sin θ₀ < θ₀ := Real.sin_lt hθ_pos
  have hsin_lo : θ₀ - θ₀ ^ 3 / 6 < Real.sin θ₀ := Real.sin_gt_sub_cube hθ_pos
  have hcube : θ₀ ^ 3 / 6 < (61 : ℝ) / 10 ^ 11 := by
    have : θ₀ < (1534 : ℝ) / 10 ^ 6 := by linarith
    nlinarith [sq_nonneg θ₀]
  have hs_lo : (153398017 : ℝ) / 10 ^ 11 < Real.sin θ₀ := by linarith
  have hs_hi : Real.sin θ₀ < (153398079 : ℝ) / 10 ^ 11 := by linarith
  have hs_err : |Real.sin θ₀ - (S1 : ℝ) / (SB : ℝ)| ≤ 6 / (SB : ℝ) := by
    rw [abs_le]; constructor <;> norm_num [S1, SB] <;> linarith
  have hcos_nonneg : 0 ≤ Real.cos θ₀ := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> unfold θ₀ <;> linarith
  have hsq : Real.cos θ₀ ^ 2 = 1 - Real.sin θ₀ ^ 2 := by linarith [Real.cos_sq_add_sin_sq θ₀]
  have hc_lo : (C1 : ℝ) / (SB : ℝ) - 2 / (SB : ℝ) ≤ Real.cos θ₀ := by
    have h1 : ((C1 : ℝ) / (SB : ℝ) - 2 / (SB : ℝ)) ^ 2 ≤ Real.cos θ₀ ^ 2 := by
      rw [hsq]; norm_num [C1, SB]; nlinarith [hs_lo, hs_hi]
    have h2 : (0 : ℝ) ≤ (C1 : ℝ) / (SB : ℝ) - 2 / (SB : ℝ) := by norm_num [C1, SB]
    nlinarith [hcos_nonneg, h1, h2]
  have hc_hi : Real.cos θ₀ ≤ (C1 : ℝ) / (SB : ℝ) + 2 / (SB : ℝ) := by
    have h1 : Real.cos θ₀ ^ 2 ≤ ((C1 : ℝ) / (SB : ℝ) + 2 / (SB : ℝ)) ^ 2 := by
      rw [hsq]; norm_num [C1, SB]; nlinarith [hs_lo, hs_hi]
    have h2 : (0 : ℝ) ≤ (C1 : ℝ) / (SB : ℝ) + 2 / (SB : ℝ) := by norm_num [C1, SB]
    nlinarith [hcos_nonneg, h1, h2]
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, hs_err⟩

private lemma ediv_real_err (a b : ℤ) (hb : 0 < b) :
    |((a / b : ℤ) : ℝ) - (a : ℝ) / (b : ℝ)| ≤ 1 := by
  have h1 : (a / b) * b ≤ a := Int.ediv_mul_le a (by omega)
  have h2 : a < (a / b + 1) * b := by
    have hrem := Int.emod_lt_of_pos a hb
    have hdiv := Int.mul_ediv_add_emod a b
    nlinarith
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h1R : ((a / b : ℤ) : ℝ) * (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast h1
  have h2R : (a : ℝ) < (((a / b : ℤ) : ℝ) + 1) * (b : ℝ) := by exact_mod_cast h2
  have h1' : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := (le_div_iff₀ hbR).mpr h1R
  have h2' : (a : ℝ) / (b : ℝ) < ((a / b : ℤ) : ℝ) + 1 := (div_lt_iff₀ hbR).mpr h2R
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma trigStep_norm_err (k : ℕ) (hk : k ≤ 1024) :
    Real.sqrt ((Real.cos ((k : ℝ) * θ₀) - ((trigStep k).1 : ℝ) / (SB : ℝ)) ^ 2 +
      (Real.sin ((k : ℝ) * θ₀) - ((trigStep k).2 : ℝ) / (SB : ℝ)) ^ 2) ≤
      10 * (k : ℝ) / (SB : ℝ) := by
  have hSB : (0 : ℝ) < (SB : ℝ) := by norm_num [SB]
  obtain ⟨hc1, hs1⟩ := c1_s1_err
  induction k with
  | zero =>
      simp [trigStep, SB]
  | succ k ih =>
      have hk' : k ≤ 1024 := by omega
      have ih' := ih hk'
      set ck : ℝ := ((trigStep k).1 : ℝ) / (SB : ℝ)
      set sk : ℝ := ((trigStep k).2 : ℝ) / (SB : ℝ)
      set Ck : ℝ := Real.cos ((k : ℝ) * θ₀)
      set Sk : ℝ := Real.sin ((k : ℝ) * θ₀)
      set c1r : ℝ := (C1 : ℝ) / (SB : ℝ)
      set s1r : ℝ := (S1 : ℝ) / (SB : ℝ)
      set C1r : ℝ := Real.cos θ₀
      set S1r : ℝ := Real.sin θ₀
      have hck_sk_norm : Real.sqrt (ck ^ 2 + sk ^ 2) ≤ 1 + 10 * (k : ℝ) / (SB : ℝ) := by
        have htri : Real.sqrt (ck ^ 2 + sk ^ 2) ≤
            Real.sqrt (Ck ^ 2 + Sk ^ 2) + Real.sqrt ((Ck - ck) ^ 2 + (Sk - sk) ^ 2) := by
          have h1 : (Ck - ck) ^ 2 + (Sk - sk) ^ 2 ≥ 0 := by positivity
          have h2 : Ck ^ 2 + Sk ^ 2 = 1 := Real.cos_sq_add_sin_sq _
          have hcs : -(Ck * (Ck - ck) + Sk * (Sk - sk)) ≤
              Real.sqrt (Ck ^ 2 + Sk ^ 2) * Real.sqrt ((Ck - ck) ^ 2 + (Sk - sk) ^ 2) := by
            rw [← Real.sqrt_mul (by positivity)]
            exact le_trans (le_abs_self _) (by
              rw [← Real.sqrt_sq_eq_abs]
              exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Ck * (Sk - sk) - Sk * (Ck - ck))]))
          have hsq : ck ^ 2 + sk ^ 2 ≤
              (Real.sqrt (Ck ^ 2 + Sk ^ 2) + Real.sqrt ((Ck - ck) ^ 2 + (Sk - sk) ^ 2)) ^ 2 := by
            rw [add_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt h1]
            nlinarith
          exact Real.sqrt_le_iff.mpr ⟨by positivity, hsq⟩
        have h1 : Real.sqrt (Ck ^ 2 + Sk ^ 2) = 1 := by rw [Real.cos_sq_add_sin_sq, Real.sqrt_one]
        linarith
      have hck_sk_le : Real.sqrt (ck ^ 2 + sk ^ 2) ≤ 1001 / 1000 := by
        have hkR : (k : ℝ) ≤ 1024 := by exact_mod_cast hk'
        have : 10 * (k : ℝ) / (SB : ℝ) ≤ 1 / 1000 := by norm_num [SB]; linarith
        linarith
      -- Decompose error at k+1:
      -- (C_{k+1} - ck1, S_{k+1} - sk1) = rot(θ₀)(Ck - ck, Sk - sk) + rot_diff(ck, sk) + round_err
      have hcos_succ : Real.cos (((k + 1 : ℕ) : ℝ) * θ₀) = Ck * C1r - Sk * S1r := by
        push_cast; rw [add_mul, one_mul, Real.cos_add]
      have hsin_succ : Real.sin (((k + 1 : ℕ) : ℝ) * θ₀) = Sk * C1r + Ck * S1r := by
        push_cast; rw [add_mul, one_mul, Real.sin_add]
      have hdiv1 : |(((trigStep (k + 1)).1 : ℝ) / (SB : ℝ)) - (ck * c1r - sk * s1r)| ≤ 1 / (SB : ℝ) := by
        simp only [trigStep, trigNext]
        have h := ediv_real_err ((trigStep k).1 * C1 - (trigStep k).2 * S1) SB (by norm_num [SB])
        have hEq : ((((trigStep k).1 * C1 - (trigStep k).2 * S1 : ℤ) : ℝ) / (SB : ℝ)) / (SB : ℝ) =
            ck * c1r - sk * s1r := by
          simp only [ck, sk, c1r, s1r]; push_cast; ring
        rw [← hEq, ← sub_div, abs_div, abs_of_pos hSB]
        exact div_le_div_of_nonneg_right h hSB.le
      have hdiv2 : |(((trigStep (k + 1)).2 : ℝ) / (SB : ℝ)) - (sk * c1r + ck * s1r)| ≤ 1 / (SB : ℝ) := by
        simp only [trigStep, trigNext]
        have h := ediv_real_err ((trigStep k).2 * C1 + (trigStep k).1 * S1) SB (by norm_num [SB])
        have hEq : ((((trigStep k).2 * C1 + (trigStep k).1 * S1 : ℤ) : ℝ) / (SB : ℝ)) / (SB : ℝ) =
            sk * c1r + ck * s1r := by
          simp only [ck, sk, c1r, s1r]; push_cast; ring
        rw [← hEq, ← sub_div, abs_div, abs_of_pos hSB]
        exact div_le_div_of_nonneg_right h hSB.le
      -- Use triangle inequality in R^2: ‖u + v + w‖ ≤ ‖u‖ + ‖v‖ + ‖w‖
      have tri2 : ∀ a1 b1 a2 b2 : ℝ,
          Real.sqrt ((a1 + a2) ^ 2 + (b1 + b2) ^ 2) ≤
            Real.sqrt (a1 ^ 2 + b1 ^ 2) + Real.sqrt (a2 ^ 2 + b2 ^ 2) := fun a1 b1 a2 b2 => by
        have hcs : a1 * a2 + b1 * b2 ≤
            Real.sqrt (a1 ^ 2 + b1 ^ 2) * Real.sqrt (a2 ^ 2 + b2 ^ 2) := by
          rw [← Real.sqrt_mul (by positivity)]
          exact le_trans (le_abs_self _) (by
            rw [← Real.sqrt_sq_eq_abs]
            exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a1 * b2 - b1 * a2)]))
        refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
        nlinarith [Real.sq_sqrt (show 0 ≤ a1 ^ 2 + b1 ^ 2 by positivity),
          Real.sq_sqrt (show 0 ≤ a2 ^ 2 + b2 ^ 2 by positivity), hcs]
      set u1 := (Ck - ck) * C1r - (Sk - sk) * S1r
      set u2 := (Sk - sk) * C1r + (Ck - ck) * S1r
      set v1 := ck * (C1r - c1r) - sk * (S1r - s1r)
      set v2 := sk * (C1r - c1r) + ck * (S1r - s1r)
      set w1 := (ck * c1r - sk * s1r) - ((trigStep (k + 1)).1 : ℝ) / (SB : ℝ)
      set w2 := (sk * c1r + ck * s1r) - ((trigStep (k + 1)).2 : ℝ) / (SB : ℝ)
      have hdecomp1 : Real.cos (((k + 1 : ℕ) : ℝ) * θ₀) - ((trigStep (k + 1)).1 : ℝ) / (SB : ℝ) =
          (u1 + v1) + w1 := by rw [hcos_succ]; simp only [u1, v1, w1]; ring
      have hdecomp2 : Real.sin (((k + 1 : ℕ) : ℝ) * θ₀) - ((trigStep (k + 1)).2 : ℝ) / (SB : ℝ) =
          (u2 + v2) + w2 := by rw [hsin_succ]; simp only [u2, v2, w2]; ring
      rw [hdecomp1, hdecomp2]
      have hu : Real.sqrt (u1 ^ 2 + u2 ^ 2) = Real.sqrt ((Ck - ck) ^ 2 + (Sk - sk) ^ 2) := by
        congr 1
        have hEq : u1 ^ 2 + u2 ^ 2 = ((Ck - ck) ^ 2 + (Sk - sk) ^ 2) * (C1r ^ 2 + S1r ^ 2) := by
          simp only [u1, u2]; ring
        rw [hEq, Real.cos_sq_add_sin_sq, mul_one]
      have hv : Real.sqrt (v1 ^ 2 + v2 ^ 2) ≤ (1001 / 1000) * (7 / (SB : ℝ)) := by
        have hv_eq : v1 ^ 2 + v2 ^ 2 = (ck ^ 2 + sk ^ 2) * ((C1r - c1r) ^ 2 + (S1r - s1r) ^ 2) := by
          simp only [v1, v2]; ring
        rw [hv_eq, Real.sqrt_mul (by positivity)]
        have hd : Real.sqrt ((C1r - c1r) ^ 2 + (S1r - s1r) ^ 2) ≤ 7 / (SB : ℝ) := by
          refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
          have hc1' : (C1r - c1r) ^ 2 ≤ (2 / (SB : ℝ)) ^ 2 := by
            rw [← sq_abs (C1r - c1r)]; exact sq_le_sq' (by linarith [abs_nonneg (C1r - c1r)]) hc1
          have hs1' : (S1r - s1r) ^ 2 ≤ (6 / (SB : ℝ)) ^ 2 := by
            rw [← sq_abs (S1r - s1r)]; exact sq_le_sq' (by linarith [abs_nonneg (S1r - s1r)]) hs1
          have hnum : (2 / (SB : ℝ)) ^ 2 + (6 / (SB : ℝ)) ^ 2 ≤ (7 / (SB : ℝ)) ^ 2 := by
            norm_num [SB]
          linarith
        exact mul_le_mul hck_sk_le hd (Real.sqrt_nonneg _) (by positivity)
      have hw : Real.sqrt (w1 ^ 2 + w2 ^ 2) ≤ 2 / (SB : ℝ) := by
        refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
        have hw1 : w1 ^ 2 ≤ (1 / (SB : ℝ)) ^ 2 := by
          rw [← sq_abs w1]
          have : |w1| ≤ 1 / (SB : ℝ) := by simpa [w1, abs_sub_comm] using hdiv1
          exact sq_le_sq' (by linarith [abs_nonneg w1]) this
        have hw2 : w2 ^ 2 ≤ (1 / (SB : ℝ)) ^ 2 := by
          rw [← sq_abs w2]
          have : |w2| ≤ 1 / (SB : ℝ) := by simpa [w2, abs_sub_comm] using hdiv2
          exact sq_le_sq' (by linarith [abs_nonneg w2]) this
        have hnum : (1 / (SB : ℝ)) ^ 2 + (1 / (SB : ℝ)) ^ 2 ≤ (2 / (SB : ℝ)) ^ 2 := by
          norm_num [SB]
        linarith
      calc Real.sqrt (((u1 + v1) + w1) ^ 2 + ((u2 + v2) + w2) ^ 2)
          ≤ Real.sqrt ((u1 + v1) ^ 2 + (u2 + v2) ^ 2) + Real.sqrt (w1 ^ 2 + w2 ^ 2) := tri2 _ _ _ _
        _ ≤ Real.sqrt (u1 ^ 2 + u2 ^ 2) + Real.sqrt (v1 ^ 2 + v2 ^ 2) + Real.sqrt (w1 ^ 2 + w2 ^ 2) := by
            linarith [tri2 u1 u2 v1 v2]
        _ ≤ 10 * (k : ℝ) / (SB : ℝ) + (1001 / 1000) * (7 / (SB : ℝ)) + 2 / (SB : ℝ) := by
            rw [hu]; linarith
        _ ≤ 10 * ((k + 1 : ℕ) : ℝ) / (SB : ℝ) := by
            push_cast; norm_num [SB]; linarith

private lemma trigQuad_err (r : ℕ) (hr : r ≤ 1024) :
    |Real.cos ((r : ℝ) * θ₀) - ((trigQuad r).1 : ℝ) / (SB : ℝ)| ≤ 10240 / (SB : ℝ) ∧
    |Real.sin ((r : ℝ) * θ₀) - ((trigQuad r).2 : ℝ) / (SB : ℝ)| ≤ 10240 / (SB : ℝ) := by
  by_cases hlt : r < 1024
  · simp only [trigQuad, if_pos hlt, trigTree10_get r hlt]
    have hn := trigStep_norm_err r hr
    have hrR : (r : ℝ) ≤ 1024 := by exact_mod_cast hr
    have hbd : 10 * (r : ℝ) / (SB : ℝ) ≤ 10240 / (SB : ℝ) := by norm_num [SB]; linarith
    have h1 : |Real.cos ((r : ℝ) * θ₀) - ((trigStep r).1 : ℝ) / (SB : ℝ)| ≤
        Real.sqrt ((Real.cos ((r : ℝ) * θ₀) - ((trigStep r).1 : ℝ) / (SB : ℝ)) ^ 2 +
          (Real.sin ((r : ℝ) * θ₀) - ((trigStep r).2 : ℝ) / (SB : ℝ)) ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
    have h2 : |Real.sin ((r : ℝ) * θ₀) - ((trigStep r).2 : ℝ) / (SB : ℝ)| ≤
        Real.sqrt ((Real.cos ((r : ℝ) * θ₀) - ((trigStep r).1 : ℝ) / (SB : ℝ)) ^ 2 +
          (Real.sin ((r : ℝ) * θ₀) - ((trigStep r).2 : ℝ) / (SB : ℝ)) ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
    exact ⟨h1.trans (hn.trans hbd), h2.trans (hn.trans hbd)⟩
  · have hr1024 : r = 1024 := by omega
    subst hr1024
    simp only [trigQuad, lt_irrefl, ite_false, Int.cast_zero, zero_div, sub_zero]
    have hEq : ((1024 : ℕ) : ℝ) * θ₀ = π / 2 := by unfold θ₀; push_cast; ring
    rw [hEq, Real.cos_pi_div_two, Real.sin_pi_div_two, div_self (by norm_num [SB] : (SB : ℝ) ≠ 0)]
    norm_num [SB]

private lemma cosInt_sinInt_err (k : ℤ) :
    |Real.cos ((k : ℝ) * θ₀) - (cosInt k : ℝ) / (SB : ℝ)| ≤ 10240 / (SB : ℝ) ∧
    |Real.sin ((k : ℝ) * θ₀) - (sinInt k : ℝ) / (SB : ℝ)| ≤ 10240 / (SB : ℝ) := by
  set r : ℕ := (k % 4096).toNat
  have hr_lt : r < 4096 := by
    have h1 := Int.emod_nonneg k (by norm_num : (4096 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 4096)
    omega
  have hk_eq : (k : ℝ) * θ₀ = (r : ℝ) * θ₀ + ((k / 4096 : ℤ) : ℝ) * (2 * π) := by
    have hdiv := Int.mul_ediv_add_emod k 4096
    have hr_cast : (r : ℤ) = k % 4096 := Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))
    have hR : (k : ℝ) = (r : ℝ) + 4096 * ((k / 4096 : ℤ) : ℝ) := by
      have : k = (r : ℤ) + 4096 * (k / 4096) := by omega
      exact_mod_cast this
    rw [hR]; unfold θ₀; ring
  have hcos_per : Real.cos ((k : ℝ) * θ₀) = Real.cos ((r : ℝ) * θ₀) := by
    rw [hk_eq]; exact Real.cos_add_int_mul_two_pi _ _
  have hsin_per : Real.sin ((k : ℝ) * θ₀) = Real.sin ((r : ℝ) * θ₀) := by
    rw [hk_eq]; exact Real.sin_add_int_mul_two_pi _ _
  rw [hcos_per, hsin_per]
  unfold cosInt sinInt
  dsimp only
  change |Real.cos ((r : ℝ) * θ₀) -
    ((if r ≤ 1024 then (trigQuad r).1
      else if r ≤ 2048 then -(trigQuad (2048 - r)).1
      else if r ≤ 3072 then -(trigQuad (r - 2048)).1
      else (trigQuad (4096 - r)).1 : ℤ) : ℝ) / (SB : ℝ)| ≤ 10240 / (SB : ℝ) ∧
    |Real.sin ((r : ℝ) * θ₀) -
    ((if r ≤ 1024 then (trigQuad r).2
      else if r ≤ 2048 then (trigQuad (2048 - r)).2
      else if r ≤ 3072 then -(trigQuad (r - 2048)).2
      else -(trigQuad (4096 - r)).2 : ℤ) : ℝ) / (SB : ℝ)| ≤ 10240 / (SB : ℝ)
  have hneg_abs : ∀ (a : ℝ) (b : ℤ),
      |a - ((-b : ℤ) : ℝ) / (SB : ℝ)| = |-a - (b : ℝ) / (SB : ℝ)| := fun a b => by
    push_cast
    rw [show a - -(b : ℝ) / (SB : ℝ) = -(-a - (b : ℝ) / (SB : ℝ)) by ring, abs_neg]
  split_ifs with h1 h2 h3
  · exact trigQuad_err r h1
  · have hq := trigQuad_err (2048 - r) (by omega)
    have hEq : ((2048 - r : ℕ) : ℝ) * θ₀ = π - (r : ℝ) * θ₀ := by
      rw [Nat.cast_sub h2]; unfold θ₀; push_cast; ring
    rw [hEq, Real.cos_pi_sub, Real.sin_pi_sub] at hq
    exact ⟨by rw [hneg_abs]; exact hq.1, hq.2⟩
  · have hq := trigQuad_err (r - 2048) (by omega)
    have hEq : ((r - 2048 : ℕ) : ℝ) * θ₀ = (r : ℝ) * θ₀ - π := by
      rw [Nat.cast_sub (by omega)]; unfold θ₀; push_cast; ring
    rw [hEq, Real.cos_sub_pi, Real.sin_sub_pi] at hq
    exact ⟨by rw [hneg_abs]; exact hq.1, by rw [hneg_abs]; exact hq.2⟩
  · have hq := trigQuad_err (4096 - r) (by omega)
    have hEq : ((4096 - r : ℕ) : ℝ) * θ₀ = 2 * π - (r : ℝ) * θ₀ := by
      rw [Nat.cast_sub (by omega)]; unfold θ₀; push_cast; ring
    rw [hEq, Real.cos_two_pi_sub, Real.sin_two_pi_sub] at hq
    exact ⟨hq.1, by rw [hneg_abs]; exact hq.2⟩

/-! ### Section 4: Second-Order Taylor Integral Bounds & Pure-Integer Dual Certificate Verifier -/

private def linMaxInt (a b h : ℝ) : ℝ :=
  if a ≤ -b * h then 0 else if b * h ≤ a then 2 * h * a else (a + b * h) ^ 2 / (2 * b)

private def linAbsInt (a b h : ℝ) : ℝ :=
  if b * h ≤ a then 2 * h * a else (a ^ 2 + (b * h) ^ 2) / b

private lemma integral_max_lin (a b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h) :
    ∫ u in (-h)..h, max 0 (a + b * u) = linMaxInt a b h := by
  unfold linMaxInt
  split_ifs with h1 h2
  · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro u hu; rw [uIcc_of_le (by linarith)] at hu
      exact max_eq_left (by nlinarith [hu.2])
  · rw [intervalIntegral.integral_congr (g := fun u => a + b * u)]
    · have hd : ∀ u ∈ uIcc (-h) h, HasDerivAt (fun x => a * x + b * x ^ 2 / 2) (a + b * u) u :=
        fun u _ => by
          have h1 := ((hasDerivAt_id u).const_mul a).add (((hasDerivAt_pow 2 u).const_mul b).div_const 2)
          rw [show a + b * u = a * 1 + b * (((2 : ℕ) : ℝ) * u ^ (2 - 1)) / 2 by norm_num; ring]
          exact h1
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable (-h) h)]
      ring
    · intro u hu; rw [uIcc_of_le (by linarith)] at hu
      exact max_eq_right (by nlinarith [hu.1])
  · push Not at h1 h2
    have hbpos : 0 < b := by nlinarith
    set r := -a / b
    have hr1 : -h < r := by rw [lt_div_iff₀ hbpos]; linarith
    have hr2 : r < h := by rw [div_lt_iff₀ hbpos]; linarith
    have hmc : Continuous (fun u : ℝ => max 0 (a + b * u)) :=
      continuous_const.max (continuous_const.add (continuous_const.mul continuous_id))
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hmc.intervalIntegrable (-h) r) (hmc.intervalIntegrable r h)]
    have hL : ∫ u in (-h)..r, max 0 (a + b * u) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro u hu; rw [uIcc_of_le hr1.le] at hu
        have : b * u ≤ b * r := mul_le_mul_of_nonneg_left hu.2 hb
        have hbr : b * r = -a := by simp only [r]; field_simp
        exact max_eq_left (by linarith)
    have hR : ∫ u in r..h, max 0 (a + b * u) = (a + b * h) ^ 2 / (2 * b) := by
      rw [intervalIntegral.integral_congr (g := fun u => a + b * u)]
      · have hd : ∀ u ∈ uIcc r h, HasDerivAt (fun x => a * x + b * x ^ 2 / 2) (a + b * u) u :=
          fun u _ => by
            have h1 := ((hasDerivAt_id u).const_mul a).add (((hasDerivAt_pow 2 u).const_mul b).div_const 2)
            rw [show a + b * u = a * 1 + b * (((2 : ℕ) : ℝ) * u ^ (2 - 1)) / 2 by norm_num; ring]
            exact h1
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
          ((continuous_const.add (continuous_const.mul continuous_id)).intervalIntegrable r h)]
        simp only [r]; field_simp; ring
      · intro u hu; rw [uIcc_of_le hr2.le] at hu
        have : b * r ≤ b * u := mul_le_mul_of_nonneg_left hu.1 hb
        have hbr : b * r = -a := by simp only [r]; field_simp
        exact max_eq_right (by linarith)
    rw [hL, hR, zero_add]

private lemma integral_max_lin_signed (a b h : ℝ) (hh : 0 ≤ h) :
    ∫ u in (-h)..h, max 0 (a + b * u) = linMaxInt a |b| h := by
  by_cases hb : 0 ≤ b
  · rw [abs_of_nonneg hb]; exact integral_max_lin a b h hb hh
  · push Not at hb
    rw [abs_of_neg hb]
    have hcomp := intervalIntegral.integral_comp_neg (fun u => max 0 (a + (-b) * u)) (a := -h) (b := h)
    have hEq : (fun u => max 0 (a + (-b) * (-u))) = fun u => max 0 (a + b * u) := by ext u; ring_nf
    rw [neg_neg, hEq] at hcomp
    rw [hcomp]; exact integral_max_lin a (-b) h (by linarith) hh

private lemma integral_abs_lin_signed (a b h : ℝ) (hh : 0 ≤ h) :
    ∫ u in (-h)..h, |a + b * u| = linAbsInt |a| |b| h := by
  have hEq : (fun u => |a + b * u|) = fun u => max 0 (a + b * u) + max 0 (-a + (-b) * u) := by
    ext u
    by_cases h0 : 0 ≤ a + b * u
    · rw [abs_of_nonneg h0, max_eq_right h0, max_eq_left (by linarith), add_zero]
    · push Not at h0
      rw [abs_of_neg h0, max_eq_left h0.le, max_eq_right (by linarith), zero_add]; ring
  have hc1 : Continuous (fun u : ℝ => max 0 (a + b * u)) :=
    continuous_const.max (continuous_const.add (continuous_const.mul continuous_id))
  have hc2 : Continuous (fun u : ℝ => max 0 (-a + (-b) * u)) :=
    continuous_const.max (continuous_const.add (continuous_const.mul continuous_id))
  rw [hEq, intervalIntegral.integral_add (hc1.intervalIntegrable (-h) h) (hc2.intervalIntegrable (-h) h),
    integral_max_lin_signed a b h hh, integral_max_lin_signed (-a) (-b) h hh, abs_neg]
  unfold linMaxInt linAbsInt
  have hbh : 0 ≤ |b| * h := mul_nonneg (abs_nonneg b) hh
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    by_cases hle : |b| * h ≤ a
    · by_cases h0 : a = 0
      · have hbh0 : |b| * h = 0 := by linarith
        simp [h0, hbh0]
      · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
        rw [if_pos hle, if_neg (by linarith : ¬a ≤ -|b| * h), if_pos hle, if_pos (by linarith : -a ≤ -|b| * h)]
        ring
    · push Not at hle
      have hbpos : 0 < |b| := by nlinarith
      rw [if_neg hle.not_ge, if_neg (by linarith : ¬a ≤ -|b| * h), if_neg hle.not_ge,
        if_neg (by linarith : ¬-a ≤ -|b| * h), if_neg (by linarith : ¬|b| * h ≤ -a)]
      field_simp; ring
  · push Not at ha
    rw [abs_of_neg ha]
    by_cases hle : |b| * h ≤ -a
    · rw [if_pos hle, if_pos (by linarith : a ≤ -|b| * h), if_neg (by linarith : ¬-a ≤ -|b| * h), if_pos hle]
      ring
    · push Not at hle
      have hbpos : 0 < |b| := by nlinarith
      rw [if_neg hle.not_ge, if_neg (by linarith : ¬a ≤ -|b| * h), if_neg (by linarith : ¬|b| * h ≤ a),
        if_neg (by linarith : ¬-a ≤ -|b| * h), if_neg hle.not_ge]
      field_simp; ring

/-- Second-order Taylor remainder via two applications of FTC. -/
private lemma taylor2_bound {F F' F'' : ℝ → ℝ} {m h L2 : ℝ} (hh : 0 ≤ h) (_hL2 : 0 ≤ L2)
    (hF : ∀ x ∈ Icc (m - h) (m + h), HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc (m - h) (m + h), HasDerivAt F' (F'' x) x)
    (hF''c : Continuous F'')
    (hF''b : ∀ x ∈ Icc (m - h) (m + h), |F'' x| ≤ L2)
    {x : ℝ} (hx : x ∈ Icc (m - h) (m + h)) :
    |F x - (F m + F' m * (x - m))| ≤ (1 / 2) * L2 * (x - m) ^ 2 := by
  have hF'c : ContinuousOn F' (Icc (m - h) (m + h)) := fun y hy => (hF' y hy).continuousAt.continuousWithinAt
  have h1 : ∀ t ∈ Icc (m - h) (m + h), |F' t - F' m| ≤ L2 * |t - m| := by
    intro t ht
    have hsub : uIcc m t ⊆ Icc (m - h) (m + h) := by
      intro z hz; rw [mem_uIcc] at hz
      rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith [ht.1, ht.2]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z hz => hF' z (hsub hz)) (hF''c.intervalIntegrable m t)
    rw [← hftc]
    have hnb := intervalIntegral.norm_integral_le_of_norm_le_const (a := m) (b := t)
      (f := F'') (C := L2) fun z hz => by
        rw [Real.norm_eq_abs]; exact hF''b z (hsub (uIoc_subset_uIcc hz))
    simpa [Real.norm_eq_abs, mul_comm] using hnb
  have hsubx : uIcc m x ⊆ Icc (m - h) (m + h) := by
    intro z hz; rw [mem_uIcc] at hz
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith [hx.1, hx.2]
  have hftc2 : ∫ t in m..x, (F' t - F' m) = F x - (F m + F' m * (x - m)) := by
    have hd : ∀ t ∈ uIcc m x, HasDerivAt (fun y => F y - F' m * y) (F' t - F' m) t := fun t ht =>
      (hF t (hsubx ht)).sub (by simpa using (hasDerivAt_id t).const_mul (F' m))
    have hi : IntervalIntegrable (fun t => F' t - F' m) volume m x :=
      ((hF'c.mono hsubx).intervalIntegrable).sub intervalIntegrable_const
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]; ring
  rw [← hftc2]
  by_cases hmx : m ≤ x
  · have hi1 : IntervalIntegrable (fun t => F' t - F' m) volume m x :=
      ((hF'c.mono hsubx).intervalIntegrable).sub intervalIntegrable_const
    have hi2 : IntervalIntegrable (fun t => L2 * (t - m)) volume m x :=
      (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable m x
    have hle : |∫ t in m..x, (F' t - F' m)| ≤ ∫ t in m..x, L2 * (t - m) := by
      have h1' : |∫ t in m..x, (F' t - F' m)| ≤ ∫ t in m..x, |F' t - F' m| := by
        simpa [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun t => F' t - F' m) hmx
      refine h1'.trans (intervalIntegral.integral_mono_on hmx hi1.abs hi2 fun t ht => ?_)
      rw [← abs_of_nonneg (by linarith [ht.1] : 0 ≤ t - m)]
      exact h1 t ⟨by linarith [ht.1], by linarith [ht.2, hx.2]⟩
    have heval : ∫ t in m..x, L2 * (t - m) = (1 / 2) * L2 * (x - m) ^ 2 := by
      have hd : ∀ t ∈ uIcc m x, HasDerivAt (fun y => (1 / 2) * L2 * (y - m) ^ 2) (L2 * (t - m)) t :=
        fun t _ => by
          have h1 := (((hasDerivAt_id t).sub_const m).pow 2).const_mul ((1 / 2) * L2)
          rw [show L2 * (t - m) = (1 / 2) * L2 * (((2 : ℕ) : ℝ) * (t - m) ^ (2 - 1) * 1) by norm_num; ring]
          exact h1
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi2]; ring
    linarith
  · push Not at hmx
    rw [intervalIntegral.integral_symm x m, abs_neg]
    have hsubx' : uIcc x m ⊆ Icc (m - h) (m + h) := by rw [uIcc_comm]; exact hsubx
    have hi1 : IntervalIntegrable (fun t => F' t - F' m) volume x m :=
      ((hF'c.mono hsubx').intervalIntegrable).sub intervalIntegrable_const
    have hi2 : IntervalIntegrable (fun t => L2 * (m - t)) volume x m :=
      (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable x m
    have hle : |∫ t in x..m, (F' t - F' m)| ≤ ∫ t in x..m, L2 * (m - t) := by
      have h1' : |∫ t in x..m, (F' t - F' m)| ≤ ∫ t in x..m, |F' t - F' m| := by
        simpa [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun t => F' t - F' m) hmx.le
      refine h1'.trans (intervalIntegral.integral_mono_on hmx.le hi1.abs hi2 fun t ht => ?_)
      have : |t - m| = m - t := by rw [abs_of_nonpos (by linarith [ht.2])]; ring
      rw [← this]
      exact h1 t ⟨by linarith [ht.1, hx.1], by linarith [ht.2]⟩
    have heval : ∫ t in x..m, L2 * (m - t) = (1 / 2) * L2 * (x - m) ^ 2 := by
      have hd : ∀ t ∈ uIcc x m, HasDerivAt (fun y => -(1 / 2) * L2 * (m - y) ^ 2) (L2 * (m - t)) t :=
        fun t _ => by
          have h1 := (((hasDerivAt_const t m).sub (hasDerivAt_id t)).pow 2).const_mul (-(1 / 2) * L2)
          rw [show L2 * (m - t) = -(1 / 2) * L2 * (((2 : ℕ) : ℝ) * (m - t) ^ (2 - 1) * (0 - 1)) by norm_num; ring]
          exact h1
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi2]; ring
    linarith

private lemma integral_sq_symm (h : ℝ) : ∫ u in (-h)..h, u ^ 2 = (2 / 3 : ℝ) * h ^ 3 := by
  have hd : ∀ u ∈ uIcc (-h) h, HasDerivAt (fun x => x ^ 3 / 3) (u ^ 2) u := fun u _ => by
    have h1 := (hasDerivAt_pow 3 u).div_const 3
    rw [show u ^ 2 = ((3 : ℕ) : ℝ) * u ^ (3 - 1) / 3 by norm_num]
    exact h1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((continuous_pow 2).intervalIntegrable (-h) h)]
  ring

private lemma integral_max_neg_le_taylor {F F' F'' : ℝ → ℝ} {m h a0 b0 e0 e1 L2 : ℝ}
    (hh : 0 ≤ h) (hL2 : 0 ≤ L2)
    (hFc : Continuous F) (hF''c : Continuous F'')
    (hF : ∀ x ∈ Icc (m - h) (m + h), HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc (m - h) (m + h), HasDerivAt F' (F'' x) x)
    (hF''b : ∀ x ∈ Icc (m - h) (m + h), |F'' x| ≤ L2)
    (ha : |F m - a0| ≤ e0) (hb : |F' m - b0| ≤ e1) :
    ∫ x in (m - h)..(m + h), max 0 (-F x) ≤
      linMaxInt (-a0) |b0| h + 2 * e0 * h + 2 * e1 * h ^ 2 + (1 / 3) * L2 * h ^ 3 := by
  have hcomp := intervalIntegral.integral_comp_add_right (fun x => max 0 (-F x)) m (a := -h) (b := h)
  have h1 : -h + m = m - h := by ring
  have h2 : h + m = m + h := by ring
  rw [h1, h2] at hcomp
  rw [← hcomp]
  have he0 : 0 ≤ e0 := le_trans (abs_nonneg _) ha
  have he1 : 0 ≤ e1 := le_trans (abs_nonneg _) hb
  have hpt : ∀ u ∈ Icc (-h) h,
      max 0 (-F (u + m)) ≤ max 0 ((-a0) + (-b0) * u) + e0 + e1 * h + (1 / 2) * L2 * u ^ 2 := by
    intro u hu
    have hmem : u + m ∈ Icc (m - h) (m + h) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have ht := taylor2_bound hh hL2 hF hF' hF''c hF''b hmem
    rw [show u + m - m = u by ring] at ht
    have h1' : -F m ≤ -a0 + e0 := by linarith [(abs_le.mp ha).1]
    have h2' : -(F' m - b0) * u ≤ e1 * h := by
      calc -(F' m - b0) * u ≤ |-(F' m - b0) * u| := le_abs_self _
        _ = |F' m - b0| * |u| := by rw [abs_mul, abs_neg]
        _ ≤ e1 * h := mul_le_mul hb (abs_le.mpr ⟨hu.1, hu.2⟩) (abs_nonneg _) he1
    have h3' := (abs_le.mp ht).1
    have hab : -F (u + m) ≤ (-a0) + (-b0) * u + e0 + e1 * h + (1 / 2) * L2 * u ^ 2 := by nlinarith
    have hq : 0 ≤ (1 / 2) * L2 * u ^ 2 := by positivity
    exact max_le (by linarith [le_max_left 0 ((-a0) + (-b0) * u), mul_nonneg he1 hh])
      (by linarith [le_max_right 0 ((-a0) + (-b0) * u)])
  have hcL : Continuous (fun u : ℝ => max 0 (-F (u + m))) :=
    continuous_const.max (hFc.comp (continuous_id.add continuous_const)).neg
  have hcR1 : Continuous (fun u : ℝ => max 0 ((-a0) + (-b0) * u)) :=
    continuous_const.max (continuous_const.add (continuous_const.mul continuous_id))
  have hcR2 : Continuous (fun u : ℝ => (e0 + e1 * h) + (1 / 2) * L2 * u ^ 2) :=
    continuous_const.add (continuous_const.mul (continuous_pow 2))
  calc ∫ u in (-h)..h, max 0 (-F (u + m))
      ≤ ∫ u in (-h)..h, (max 0 ((-a0) + (-b0) * u) + ((e0 + e1 * h) + (1 / 2) * L2 * u ^ 2)) :=
        intervalIntegral.integral_mono_on (by linarith) (hcL.intervalIntegrable (-h) h)
          ((hcR1.add hcR2).intervalIntegrable (-h) h) fun u hu => by linarith [hpt u hu]
    _ = (∫ u in (-h)..h, max 0 ((-a0) + (-b0) * u)) +
        (∫ _u in (-h)..h, (e0 + e1 * h)) + (1 / 2) * L2 * (∫ u in (-h)..h, u ^ 2) := by
        rw [intervalIntegral.integral_add (hcR1.intervalIntegrable (-h) h) (hcR2.intervalIntegrable (-h) h),
          intervalIntegral.integral_add intervalIntegrable_const
            (((continuous_pow 2).intervalIntegrable (-h) h).const_mul ((1 / 2) * L2)),
          intervalIntegral.integral_const_mul, add_assoc]
    _ = linMaxInt (-a0) |b0| h + 2 * e0 * h + 2 * e1 * h ^ 2 + (1 / 3) * L2 * h ^ 3 := by
        rw [integral_max_lin_signed (-a0) (-b0) h hh, abs_neg,
          intervalIntegral.integral_const, smul_eq_mul, integral_sq_symm h]
        ring

private lemma integral_abs_le_taylor {F F' F'' : ℝ → ℝ} {m h a0 b0 e0 e1 L2 : ℝ}
    (hh : 0 ≤ h) (hL2 : 0 ≤ L2)
    (hFc : Continuous F) (hF''c : Continuous F'')
    (hF : ∀ x ∈ Icc (m - h) (m + h), HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc (m - h) (m + h), HasDerivAt F' (F'' x) x)
    (hF''b : ∀ x ∈ Icc (m - h) (m + h), |F'' x| ≤ L2)
    (ha : |F m - a0| ≤ e0) (hb : |F' m - b0| ≤ e1) :
    ∫ x in (m - h)..(m + h), |F x| ≤
      linAbsInt |a0| |b0| h + 2 * e0 * h + 2 * e1 * h ^ 2 + (1 / 3) * L2 * h ^ 3 := by
  have hcomp := intervalIntegral.integral_comp_add_right (fun x => |F x|) m (a := -h) (b := h)
  have h1 : -h + m = m - h := by ring
  have h2 : h + m = m + h := by ring
  rw [h1, h2] at hcomp
  rw [← hcomp]
  have he0 : 0 ≤ e0 := le_trans (abs_nonneg _) ha
  have he1 : 0 ≤ e1 := le_trans (abs_nonneg _) hb
  have hpt : ∀ u ∈ Icc (-h) h,
      |F (u + m)| ≤ |a0 + b0 * u| + e0 + e1 * h + (1 / 2) * L2 * u ^ 2 := by
    intro u hu
    have hmem : u + m ∈ Icc (m - h) (m + h) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have ht := taylor2_bound hh hL2 hF hF' hF''c hF''b hmem
    rw [show u + m - m = u by ring] at ht
    have h2' : |(F' m - b0) * u| ≤ e1 * h := by
      rw [abs_mul]; exact mul_le_mul hb (abs_le.mpr ⟨hu.1, hu.2⟩) (abs_nonneg _) he1
    have hEq : F (u + m) = (a0 + b0 * u) + (F m - a0) + (F' m - b0) * u +
        (F (u + m) - (F m + F' m * u)) := by ring
    rw [hEq]
    calc |(a0 + b0 * u) + (F m - a0) + (F' m - b0) * u + (F (u + m) - (F m + F' m * u))|
        ≤ |(a0 + b0 * u) + (F m - a0) + (F' m - b0) * u| + |F (u + m) - (F m + F' m * u)| := abs_add_le _ _
      _ ≤ |(a0 + b0 * u) + (F m - a0)| + |(F' m - b0) * u| + |F (u + m) - (F m + F' m * u)| := by
          linarith [abs_add_le ((a0 + b0 * u) + (F m - a0)) ((F' m - b0) * u)]
      _ ≤ |a0 + b0 * u| + |F m - a0| + |(F' m - b0) * u| + |F (u + m) - (F m + F' m * u)| := by
          linarith [abs_add_le (a0 + b0 * u) (F m - a0)]
      _ ≤ |a0 + b0 * u| + e0 + e1 * h + (1 / 2) * L2 * u ^ 2 := by linarith
  have hcL : Continuous (fun u : ℝ => |F (u + m)|) :=
    continuous_abs.comp (hFc.comp (continuous_id.add continuous_const))
  have hcR1 : Continuous (fun u : ℝ => |a0 + b0 * u|) :=
    continuous_abs.comp (continuous_const.add (continuous_const.mul continuous_id))
  have hcR2 : Continuous (fun u : ℝ => (e0 + e1 * h) + (1 / 2) * L2 * u ^ 2) :=
    continuous_const.add (continuous_const.mul (continuous_pow 2))
  calc ∫ u in (-h)..h, |F (u + m)|
      ≤ ∫ u in (-h)..h, (|a0 + b0 * u| + ((e0 + e1 * h) + (1 / 2) * L2 * u ^ 2)) :=
        intervalIntegral.integral_mono_on (by linarith) (hcL.intervalIntegrable (-h) h)
          ((hcR1.add hcR2).intervalIntegrable (-h) h) fun u hu => by linarith [hpt u hu]
    _ = (∫ u in (-h)..h, |a0 + b0 * u|) +
        (∫ _u in (-h)..h, (e0 + e1 * h)) + (1 / 2) * L2 * (∫ u in (-h)..h, u ^ 2) := by
        rw [intervalIntegral.integral_add (hcR1.intervalIntegrable (-h) h) (hcR2.intervalIntegrable (-h) h),
          intervalIntegral.integral_add intervalIntegrable_const
            (((continuous_pow 2).intervalIntegrable (-h) h).const_mul ((1 / 2) * L2)),
          intervalIntegral.integral_const_mul, add_assoc]
    _ = linAbsInt |a0| |b0| h + 2 * e0 * h + 2 * e1 * h ^ 2 + (1 / 3) * L2 * h ^ 3 := by
        rw [integral_abs_lin_signed a0 b0 h hh,
          intervalIntegral.integral_const, smul_eq_mul, integral_sq_symm h]
        ring

private structure CertData where
  lam0 : ℤ
  lam1 : ℤ
  lam2 : ℤ
  u2 : ℤ
  eta : ℤ
  nu : ℤ
  mu : ℤ
  kappa : ℤ
  u : List ℤ
  w : List ℤ
  r : List ℤ
  q : List ℤ

private def getI (l : List ℤ) (i : Fin 12) : ℤ := l.getD i.1 0

private def cdiv (a b : ℤ) : ℤ := -((-a) / b)

private lemma le_cdiv_real (a b : ℤ) (hb : 0 < b) : (a : ℝ) / (b : ℝ) ≤ (cdiv a b : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)]
  have h : (-a) / b * b ≤ -a := Int.ediv_mul_le (-a) (by omega)
  have h' : a ≤ cdiv a b * b := by unfold cdiv; nlinarith
  exact_mod_cast h'

private def ZSC : ℤ := 10000
private def FSC : ℤ := 100000000
private def QSC : ℤ := 1000000
private def PILO : ℤ := 314159265
private def PIHI : ℤ := 314159266

private def uReal (c : CertData) (i : Fin 12) : ℝ := (getI c.u i : ℝ) / (ZSC : ℝ)
private def wReal (c : CertData) (i : Fin 12) : ℝ := (getI c.w i : ℝ) / (ZSC : ℝ)
private def rReal (c : CertData) (i : Fin 12) : ℝ := (getI c.r i : ℝ) / (ZSC : ℝ)
private def qReal (c : CertData) (i : Fin 12) : ℝ := (getI c.q i : ℝ) / (ZSC : ℝ)

private def acReal (c : CertData) (i : Fin 12) : ℝ :=
  if i.1 = 1 then -(c.nu : ℝ) / (ZSC : ℝ) else -rReal c i / 2

private def asReal (c : CertData) (i : Fin 12) : ℝ :=
  (if i.1 = 1 then -(c.mu : ℝ) / (ZSC : ℝ) else -qReal c i / 2) - 2 * wReal c i * sVal (i.1 + 1)

private def PCert (c : CertData) (x : ℝ) : ℝ :=
  (c.lam0 : ℝ) / (ZSC : ℝ) + ((c.lam1 : ℝ) / (ZSC : ℝ)) * x + ((c.lam2 : ℝ) / (ZSC : ℝ)) * x ^ 2 +
    (1 / 2) * ∑ i : Fin 12,
      (uReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) +
       wReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2))

private def PsiCert (c : CertData) (t : ℝ) : ℝ :=
  (-2 * ((c.lam1 - c.eta : ℤ) : ℝ) / (ZSC : ℝ)) * t - (c.kappa : ℝ) / (ZSC : ℝ) +
    ∑ i : Fin 12,
      (acReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) +
       asReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2))

private lemma PCert_continuous (c : CertData) : Continuous (PCert c) := by
  unfold PCert
  refine (((continuous_const.add (continuous_const.mul continuous_id)).add
    (continuous_const.mul (continuous_pow 2))).add (continuous_const.mul ?_))
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_const.mul (Real.continuous_cos.comp
    ((continuous_const.mul continuous_id).div_const 2))).add
    (continuous_const.mul (Real.continuous_sin.comp
      ((continuous_const.mul continuous_id).div_const 2)))

private lemma PsiCert_continuous (c : CertData) : Continuous (PsiCert c) := by
  unfold PsiCert
  refine (((continuous_const.mul continuous_id).sub continuous_const).add ?_)
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_const.mul (Real.continuous_cos.comp
    ((continuous_const.mul continuous_id).div_const 2))).add
    (continuous_const.mul (Real.continuous_sin.comp
      ((continuous_const.mul continuous_id).div_const 2)))

/-- Master `L^1` dual inequality for any certificate `c` with `u_i > 0` (`i ≠ 1`) and `u_1 = u2`. -/
private lemma dual_cert_ineq {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (hfint : (∫ t in (-1 : ℝ)..1, f t) = 1)
    (hM_le : ∀ x, MFun f x ≤ (379005 : ℝ) / 1000000)
    (c : CertData) (hu_pos : ∀ i : Fin 12, i.1 ≠ 1 → 0 < getI c.u i) (hu2 : getI c.u ⟨1, by omega⟩ = c.u2)
    {D_ub L1_ub C0_ub : ℝ}
    (hD : ∫ x in (-2 : ℝ)..2, max 0 (-PCert c x) ≤ D_ub)
    (hL1 : (1 / 2) * ∫ t in (-1 : ℝ)..1, |PsiCert c t| ≤ L1_ub)
    (hC0 : (c.lam0 : ℝ) / (ZSC : ℝ) + (2 / 3) * ((c.lam2 : ℝ) / (ZSC : ℝ)) +
      (∑ i : Fin 12, if i.1 = 1 then 0 else
        2 * uReal c i * (sVal (i.1 + 1)) ^ 2 +
        ((rReal c i) ^ 2 + (qReal c i) ^ 2) / (8 * uReal c i)) + L1_ub ≤ C0_ub) :
    -(C0_ub + ((379005 : ℝ) / 1000000) * D_ub)
      - ((c.lam2 : ℝ) / (2 * (ZSC : ℝ))) * (EM f) ^ 2
      - ((c.eta : ℝ) / (ZSC : ℝ)) * EM f
      + ((c.u2 : ℝ) / (2 * (ZSC : ℝ))) * ((c1Val f) ^ 2 + (d1Val f) ^ 2)
      - ((c.nu : ℝ) / (ZSC : ℝ)) * c1Val f
      - ((c.mu : ℝ) / (ZSC : ℝ)) * d1Val f ≤ 0 := by
  set Ω : ℝ := (379005 : ℝ) / 1000000
  have hΩ : 0 ≤ Ω := by norm_num [Ω]
  -- 1. Lower bound (bathtub): -Ω * D_ub ≤ ∫_{-2}^2 PCert c x * MFun f x dx
  have hlow : -Ω * D_ub ≤ ∫ x in (-2 : ℝ)..2, PCert c x * MFun f x := by
    have hpt : ∀ x : ℝ, -Ω * max 0 (-PCert c x) ≤ PCert c x * MFun f x := fun x => by
      by_cases hp : 0 ≤ PCert c x
      · rw [max_eq_left (by linarith), mul_zero]
        exact mul_nonneg hp (MFun_nonneg hf x)
      · push Not at hp
        rw [max_eq_right (by linarith)]
        nlinarith [hM_le x]
    have hmc : Continuous (fun x => -Ω * max 0 (-PCert c x)) :=
      continuous_const.mul (continuous_const.max (PCert_continuous c).neg)
    have h1 := intervalIntegral.integral_mono_on (by norm_num : (-2 : ℝ) ≤ 2)
      (hmc.intervalIntegrable (-2) 2)
      (MFun_mul_cont_intervalIntegrable hfm hf (PCert_continuous c) (-2) 2) (fun x _ => hpt x)
    rw [intervalIntegral.integral_const_mul] at h1
    nlinarith
  -- 2. Exact expansion of ∫_{-2}^2 PCert c x * MFun f x dx
  have hexp : ∫ x in (-2 : ℝ)..2, PCert c x * MFun f x =
      (c.lam0 : ℝ) / (ZSC : ℝ) + ((c.lam1 : ℝ) / (ZSC : ℝ)) * EM f +
      ((c.lam2 : ℝ) / (ZSC : ℝ)) * (2 / 3 + (EM f) ^ 2 / 2) +
      ∑ i : Fin 12,
        (uReal c i * (2 * (sVal (i.1 + 1)) ^ 2 - 2 * ((alphaM f (i.1 + 1)) ^ 2 + (betaM f (i.1 + 1)) ^ 2)) -
         4 * wReal c i * sVal (i.1 + 1) * betaM f (i.1 + 1)) := by
    have hEq : (fun x => PCert c x * MFun f x) = fun x =>
        ((c.lam0 : ℝ) / (ZSC : ℝ)) * MFun f x +
        ((c.lam1 : ℝ) / (ZSC : ℝ)) * (x * MFun f x) +
        ((c.lam2 : ℝ) / (ZSC : ℝ)) * (x ^ 2 * MFun f x) +
        ∑ i : Fin 12,
          (uReal c i * ((1 / 2) * (Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) * MFun f x)) +
           wReal c i * ((1 / 2) * (Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) * MFun f x))) := by
      ext x; unfold PCert; rw [Finset.mul_sum, add_mul, add_mul, add_mul, Finset.sum_mul]
      congr 1; ring
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hEq]
    have i0 := MFun_mul_cont_intervalIntegrable hfm hf (φ := fun _ => (1 : ℝ)) continuous_const (-2) 2
    simp only [one_mul] at i0
    have i1 := MFun_mul_cont_intervalIntegrable hfm hf (φ := fun x => x) continuous_id (-2) 2
    have i2 := MFun_mul_cont_intervalIntegrable hfm hf (continuous_pow 2) (-2) 2
    have itrig : ∀ i : Fin 12, IntervalIntegrable (fun x =>
        uReal c i * ((1 / 2) * (Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) * MFun f x)) +
        wReal c i * ((1 / 2) * (Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) * MFun f x))) volume (-2) 2 :=
      fun i =>
        (((MFun_mul_cont_intervalIntegrable hfm hf
          (Real.continuous_cos.comp ((continuous_const.mul continuous_id).div_const 2)) (-2) 2).const_mul _).const_mul _).add
        (((MFun_mul_cont_intervalIntegrable hfm hf
          (Real.continuous_sin.comp ((continuous_const.mul continuous_id).div_const 2)) (-2) 2).const_mul _).const_mul _)
    have hsum_int : IntervalIntegrable (fun x => ∑ i : Fin 12,
        (uReal c i * ((1 / 2) * (Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) * MFun f x)) +
         wReal c i * ((1 / 2) * (Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) * MFun f x)))) volume (-2) 2 := by
      have hs : ∀ s : Finset (Fin 12), IntervalIntegrable (fun x => ∑ i ∈ s,
          (uReal c i * ((1 / 2) * (Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) * MFun f x)) +
           wReal c i * ((1 / 2) * (Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) * MFun f x)))) volume (-2) 2 := fun s => by
        classical induction s using Finset.induction with
        | empty => simp
        | insert a s ha ih => simp only [Finset.sum_insert ha]; exact (itrig a).add ih
      exact hs Finset.univ
    rw [intervalIntegral.integral_add (((i0.const_mul _).add (i1.const_mul _)).add (i2.const_mul _)) hsum_int,
      intervalIntegral.integral_add ((i0.const_mul _).add (i1.const_mul _)) (i2.const_mul _),
      intervalIntegral.integral_add (i0.const_mul _) (i1.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_M_eq_one hfm hf hfint, second_moment_M hfm hf hfint,
      intervalIntegral.integral_finsetSum (fun i _ => itrig i)]
    change (c.lam0 : ℝ) / (ZSC : ℝ) * 1 + (c.lam1 : ℝ) / (ZSC : ℝ) * EM f +
      (c.lam2 : ℝ) / (ZSC : ℝ) * (2 / 3 + EM f ^ 2 / 2) + _ = _
    rw [mul_one]; congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have ic := MFun_mul_cont_intervalIntegrable hfm hf
      (φ := fun x => Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2))
      (Real.continuous_cos.comp ((continuous_const.mul continuous_id).div_const 2)) (-2) 2
    have is' := MFun_mul_cont_intervalIntegrable hfm hf
      (φ := fun x => Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2))
      (Real.continuous_sin.comp ((continuous_const.mul continuous_id).div_const 2)) (-2) 2
    rw [intervalIntegral.integral_add ((ic.const_mul _).const_mul _) ((is'.const_mul _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      A_m_eq hfm hf (i.1 + 1) (by omega), B_m_eq hfm hf (i.1 + 1) (by omega)]
    ring
  -- 3. Upper bound on ∫_{-1}^1 PsiCert c t * hFun f t dt ≤ L1_ub
  have hPsi_le : ∫ t in (-1 : ℝ)..1, PsiCert c t * hFun f t ≤ L1_ub := by
    have h1 : ∫ t in (-1 : ℝ)..1, PsiCert c t * hFun f t ≤
        ∫ t in (-1 : ℝ)..1, (1 / 2) * |PsiCert c t| := by
      refine intervalIntegral.integral_mono_on (by norm_num)
        (cont_mul_h_intervalIntegrable hfm hf (PsiCert_continuous c) (-1) 1)
        ((continuous_const.mul (continuous_abs.comp (PsiCert_continuous c))).intervalIntegrable (-1) 1)
        fun t _ => ?_
      have hh : |hFun f t| ≤ 1 / 2 := by
        unfold hFun; rw [abs_le]; constructor <;> linarith [(hf t).1, (hf t).2]
      calc PsiCert c t * hFun f t ≤ |PsiCert c t * hFun f t| := le_abs_self _
        _ = |PsiCert c t| * |hFun f t| := abs_mul _ _
        _ ≤ |PsiCert c t| * (1 / 2) := mul_le_mul_of_nonneg_left hh (abs_nonneg _)
        _ = (1 / 2) * |PsiCert c t| := mul_comm _ _
    rw [intervalIntegral.integral_const_mul] at h1
    exact h1.trans hL1
  -- 4. Expand ∫_{-1}^1 PsiCert c t * hFun f t dt
  have hPsi_eq : ∫ t in (-1 : ℝ)..1, PsiCert c t * hFun f t =
      ((c.lam1 - c.eta : ℤ) : ℝ) / (ZSC : ℝ) * EM f +
      ∑ i : Fin 12,
        (2 * acReal c i * alphaM f (i.1 + 1) + 2 * asReal c i * betaM f (i.1 + 1)) := by
    have hEq : (fun t => PsiCert c t * hFun f t) = fun t =>
        (-2 * ((c.lam1 - c.eta : ℤ) : ℝ) / (ZSC : ℝ)) * (t * hFun f t) -
        ((c.kappa : ℝ) / (ZSC : ℝ)) * hFun f t +
        ∑ i : Fin 12,
          (acReal c i * (Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) * hFun f t) +
           asReal c i * (Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) * hFun f t)) := by
      ext t; unfold PsiCert; rw [add_mul, sub_mul, Finset.sum_mul]
      congr 1; ring
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hEq]
    have it := cont_mul_h_intervalIntegrable hfm hf (φ := fun t => t) continuous_id (-1) 1
    have i0 : IntervalIntegrable (hFun f) volume (-1) 1 := by
      simpa using cont_mul_h_intervalIntegrable hfm hf (φ := fun _ => (1 : ℝ)) continuous_const (-1) 1
    have ih_trig : ∀ i : Fin 12, IntervalIntegrable (fun t =>
        acReal c i * (Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) * hFun f t) +
        asReal c i * (Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) * hFun f t)) volume (-1) 1 :=
      fun i =>
        ((cont_mul_h_intervalIntegrable hfm hf
          (Real.continuous_cos.comp ((continuous_const.mul continuous_id).div_const 2)) (-1) 1).const_mul _).add
        ((cont_mul_h_intervalIntegrable hfm hf
          (Real.continuous_sin.comp ((continuous_const.mul continuous_id).div_const 2)) (-1) 1).const_mul _)
    have hsum_int : IntervalIntegrable (fun t => ∑ i : Fin 12,
        (acReal c i * (Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) * hFun f t) +
         asReal c i * (Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) * hFun f t))) volume (-1) 1 := by
      have hs : ∀ s : Finset (Fin 12), IntervalIntegrable (fun t => ∑ i ∈ s,
          (acReal c i * (Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) * hFun f t) +
           asReal c i * (Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) * hFun f t))) volume (-1) 1 := fun s => by
        classical induction s using Finset.induction with
        | empty => simp
        | insert a s ha ih => simp only [Finset.sum_insert ha]; exact (ih_trig a).add ih
      exact hs Finset.univ
    rw [intervalIntegral.integral_add ((it.const_mul _).sub (i0.const_mul _)) hsum_int,
      intervalIntegral.integral_sub (it.const_mul _) (i0.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_h_eq_zero hfm hf hfint, mul_zero, sub_zero,
      intervalIntegral.integral_finsetSum (fun i _ => ih_trig i)]
    have hEM' : (-2 * ((c.lam1 - c.eta : ℤ) : ℝ) / (ZSC : ℝ)) * ∫ t in (-1 : ℝ)..1, t * hFun f t =
        ((c.lam1 - c.eta : ℤ) : ℝ) / (ZSC : ℝ) * EM f := by
      rw [EM_eq hfm hf hfint]; ring
    rw [hEM']; congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have ic := cont_mul_h_intervalIntegrable hfm hf
      (φ := fun t => Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2))
      (Real.continuous_cos.comp ((continuous_const.mul continuous_id).div_const 2)) (-1) 1
    have is' := cont_mul_h_intervalIntegrable hfm hf
      (φ := fun t => Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2))
      (Real.continuous_sin.comp ((continuous_const.mul continuous_id).div_const 2)) (-1) 1
    rw [intervalIntegral.integral_add (ic.const_mul _) (is'.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    unfold alphaM betaM; ring
  -- 5. Complete the square for each i ≠ 1, and handle i = 1 explicitly!
  have hsum_le :
      ∑ i : Fin 12,
        (uReal c i * (2 * (sVal (i.1 + 1)) ^ 2 - 2 * ((alphaM f (i.1 + 1)) ^ 2 + (betaM f (i.1 + 1)) ^ 2)) -
         4 * wReal c i * sVal (i.1 + 1) * betaM f (i.1 + 1)) ≤
      -(c.u2 : ℝ) / (2 * (ZSC : ℝ)) * ((c1Val f) ^ 2 + (d1Val f) ^ 2) +
      ((c.nu : ℝ) / (ZSC : ℝ)) * c1Val f + ((c.mu : ℝ) / (ZSC : ℝ)) * d1Val f +
      (∑ i : Fin 12, if i.1 = 1 then 0 else
        2 * uReal c i * (sVal (i.1 + 1)) ^ 2 +
        ((rReal c i) ^ 2 + (qReal c i) ^ 2) / (8 * uReal c i)) +
      ∑ i : Fin 12,
        (2 * acReal c i * alphaM f (i.1 + 1) + 2 * asReal c i * betaM f (i.1 + 1)) := by
    have hsplit : ∀ i : Fin 12,
        uReal c i * (2 * (sVal (i.1 + 1)) ^ 2 - 2 * ((alphaM f (i.1 + 1)) ^ 2 + (betaM f (i.1 + 1)) ^ 2)) -
          4 * wReal c i * sVal (i.1 + 1) * betaM f (i.1 + 1) ≤
        (if i.1 = 1 then
          -(c.u2 : ℝ) / (2 * (ZSC : ℝ)) * ((c1Val f) ^ 2 + (d1Val f) ^ 2) +
          ((c.nu : ℝ) / (ZSC : ℝ)) * c1Val f + ((c.mu : ℝ) / (ZSC : ℝ)) * d1Val f
        else
          2 * uReal c i * (sVal (i.1 + 1)) ^ 2 +
          ((rReal c i) ^ 2 + (qReal c i) ^ 2) / (8 * uReal c i)) +
        (2 * acReal c i * alphaM f (i.1 + 1) + 2 * asReal c i * betaM f (i.1 + 1)) := by
      intro i
      by_cases hi : i.1 = 1
      · rcases i with ⟨i, hi'⟩
        simp only at hi
        subst hi
        have hi1 : (⟨1, hi'⟩ : Fin 12) = ⟨1, by omega⟩ := rfl
        rw [hi1]
        simp only [ite_true, acReal, asReal, uReal, hu2, c1Val, d1Val]
        rw [show (1 + 1 : ℕ) = 2 from rfl, sVal_two]
        ring_nf; linarith
      · simp only [if_neg hi, acReal, asReal]
        have hu : 0 < uReal c i := by
          unfold uReal; exact div_pos (by exact_mod_cast hu_pos i hi) (by norm_num [ZSC])
        have hsq1 : -2 * uReal c i * (alphaM f (i.1 + 1)) ^ 2 ≤
            -rReal c i * alphaM f (i.1 + 1) + (rReal c i) ^ 2 / (8 * uReal c i) := by
          have h0 : 0 ≤ 2 * uReal c i * (alphaM f (i.1 + 1) - rReal c i / (4 * uReal c i)) ^ 2 := by positivity
          have : 2 * uReal c i * (alphaM f (i.1 + 1) - rReal c i / (4 * uReal c i)) ^ 2 =
              2 * uReal c i * (alphaM f (i.1 + 1)) ^ 2 - rReal c i * alphaM f (i.1 + 1) +
              (rReal c i) ^ 2 / (8 * uReal c i) := by field_simp; ring
          linarith
        have hsq2 : -2 * uReal c i * (betaM f (i.1 + 1)) ^ 2 ≤
            -qReal c i * betaM f (i.1 + 1) + (qReal c i) ^ 2 / (8 * uReal c i) := by
          have h0 : 0 ≤ 2 * uReal c i * (betaM f (i.1 + 1) - qReal c i / (4 * uReal c i)) ^ 2 := by positivity
          have : 2 * uReal c i * (betaM f (i.1 + 1) - qReal c i / (4 * uReal c i)) ^ 2 =
              2 * uReal c i * (betaM f (i.1 + 1)) ^ 2 - qReal c i * betaM f (i.1 + 1) +
              (qReal c i) ^ 2 / (8 * uReal c i) := by field_simp; ring
          linarith
        rw [add_div]
        linarith
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hsplit i
    rw [Finset.sum_add_distrib] at hsum
    have hite : (∑ i : Fin 12,
        if i.1 = 1 then
          -(c.u2 : ℝ) / (2 * (ZSC : ℝ)) * ((c1Val f) ^ 2 + (d1Val f) ^ 2) +
          ((c.nu : ℝ) / (ZSC : ℝ)) * c1Val f + ((c.mu : ℝ) / (ZSC : ℝ)) * d1Val f
        else
          2 * uReal c i * (sVal (i.1 + 1)) ^ 2 +
          ((rReal c i) ^ 2 + (qReal c i) ^ 2) / (8 * uReal c i)) =
        -(c.u2 : ℝ) / (2 * (ZSC : ℝ)) * ((c1Val f) ^ 2 + (d1Val f) ^ 2) +
        ((c.nu : ℝ) / (ZSC : ℝ)) * c1Val f + ((c.mu : ℝ) / (ZSC : ℝ)) * d1Val f +
        ∑ i : Fin 12, if i.1 = 1 then 0 else
          2 * uReal c i * (sVal (i.1 + 1)) ^ 2 +
          ((rReal c i) ^ 2 + (qReal c i) ^ 2) / (8 * uReal c i) := by
      conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨1, by omega⟩ : Fin 12))]
      conv_rhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨1, by omega⟩ : Fin 12))]
      simp only [ite_true, zero_add]
      congr 1
    linarith
  -- Combine everything!
  have hcast : ((c.lam1 - c.eta : ℤ) : ℝ) / (ZSC : ℝ) * EM f =
      (c.lam1 : ℝ) / (ZSC : ℝ) * EM f - (c.eta : ℝ) / (ZSC : ℝ) * EM f := by push_cast; ring
  rw [hcast] at hPsi_eq
  have hlam2_eq : ((c.lam2 : ℝ) / (ZSC : ℝ)) * (2 / 3 + (EM f) ^ 2 / 2) =
      (2 / 3) * ((c.lam2 : ℝ) / (ZSC : ℝ)) + ((c.lam2 : ℝ) / (2 * (ZSC : ℝ))) * (EM f) ^ 2 := by ring
  have hu2_eq : -(c.u2 : ℝ) / (2 * (ZSC : ℝ)) * ((c1Val f) ^ 2 + (d1Val f) ^ 2) =
      -(((c.u2 : ℝ) / (2 * (ZSC : ℝ))) * ((c1Val f) ^ 2 + (d1Val f) ^ 2)) := by ring
  have hΩD : -Ω * D_ub = -(Ω * D_ub) := by ring
  have hstep1 : -Ω * D_ub ≤
      (c.lam0 : ℝ) / (ZSC : ℝ) + ((c.lam1 : ℝ) / (ZSC : ℝ)) * EM f +
      ((2 / 3) * ((c.lam2 : ℝ) / (ZSC : ℝ)) + ((c.lam2 : ℝ) / (2 * (ZSC : ℝ))) * (EM f) ^ 2) +
      (-(((c.u2 : ℝ) / (2 * (ZSC : ℝ))) * ((c1Val f) ^ 2 + (d1Val f) ^ 2)) +
       ((c.nu : ℝ) / (ZSC : ℝ)) * c1Val f + ((c.mu : ℝ) / (ZSC : ℝ)) * d1Val f +
       (∑ i : Fin 12, if i.1 = 1 then 0 else
         2 * uReal c i * (sVal (i.1 + 1)) ^ 2 +
         ((rReal c i) ^ 2 + (qReal c i) ^ 2) / (8 * uReal c i)) +
       ∑ i : Fin 12,
         (2 * acReal c i * alphaM f (i.1 + 1) + 2 * asReal c i * betaM f (i.1 + 1))) := by
    rw [hexp, hlam2_eq] at hlow
    rw [hu2_eq] at hsum_le
    linarith
  have hstep2 : ((c.lam1 : ℝ) / (ZSC : ℝ)) * EM f +
      ∑ i : Fin 12, (2 * acReal c i * alphaM f (i.1 + 1) + 2 * asReal c i * betaM f (i.1 + 1)) ≤
      L1_ub + ((c.eta : ℝ) / (ZSC : ℝ)) * EM f := by
    rw [hPsi_eq] at hPsi_le
    linarith
  linarith [hstep1, hstep2, hC0, hΩD]

/-! Pure-integer verifier for `D_ub`, `L1_ub`, and `C0_ub` (at scale `QSC = 10^6`). -/

private def sumAbsUW (c : CertData) : ℤ :=
  (List.range 12).foldl (fun acc i => acc + |c.u.getD i 0| + |c.w.getD i 0|) 0

private def sumMAbsUW (c : CertData) : ℤ :=
  (List.range 12).foldl (fun acc i => acc + ((i + 1 : ℕ) : ℤ) * (|c.u.getD i 0| + |c.w.getD i 0|)) 0

private def sumM2AbsUW (c : CertData) : ℤ :=
  (List.range 12).foldl (fun acc i => acc + ((i + 1 : ℕ) : ℤ) ^ 2 * (|c.u.getD i 0| + |c.w.getD i 0|)) 0

private def errPInt (c : CertData) : ℤ := cdiv (sumAbsUW c * 10240) 2000000 + 4

private def errPpInt (c : CertData) : ℤ :=
  cdiv (sumMAbsUW c * (PIHI * 10240 + SB)) (4 * ZSC * SB) + 3

private def Lp2Int (c : CertData) : ℤ :=
  2 * |c.lam2| * 10000 + cdiv (sumM2AbsUW c * PIHI * PIHI) (8 * ZSC * 100000000)

private def stepDInt (c : CertData) (j : ℕ) : ℤ :=
  let numX : ℤ := 2 * (j : ℤ) - 1023
  let (trigP, trigPp) := (List.range 12).foldl (fun (acc : ℤ × ℤ) i =>
    let m : ℤ := (i + 1 : ℕ)
    let kx : ℤ := m * (2 * numX)
    let cv := cosInt kx
    let sv := sinInt kx
    let ui := c.u.getD i 0
    let wi := c.w.getD i 0
    (acc.1 + ui * cv + wi * sv, acc.2 + m * (-ui * sv + wi * cv))) (0, 0)
  let pInt := c.lam0 * 10000 + (c.lam1 * numX * 10000) / 512 +
    (c.lam2 * numX * numX * 10000) / (512 * 512) + trigP / 2000000
  let ppInt := c.lam1 * 10000 + (2 * c.lam2 * numX * 10000) / 512 +
    (PILO * trigPp) / 400000000000000
  let a512 := 512 * (-pInt)
  let b := |ppInt|
  if a512 ≤ -b then 0
  else if b ≤ a512 then 2 * a512
  else cdiv ((a512 + b) * (a512 + b)) (2 * b)

private def sumDIntLoop (c : CertData) : ℕ → ℤ → ℤ
  | 0, acc => acc
  | n + 1, acc => sumDIntLoop c n (acc + stepDInt c n)

private def DubQ (c : CertData) : ℤ :=
  let dSum := sumDIntLoop c 1024 0
  let dNum := 3 * dSum + 3 * 4 * 512 * 512 * errPInt c + 3 * 4 * 512 * errPpInt c + 2 * Lp2Int c
  cdiv (dNum * QSC) (3 * 512 * 512 * FSC)

private def acInt (c : CertData) (i : ℕ) : ℤ :=
  if i = 1 then -c.nu * 10000 else -(c.r.getD i 0) * 5000

private def asInt (c : CertData) (i : ℕ) : ℤ :=
  let base := if i = 1 then -c.mu * 10000 else -(c.q.getD i 0) * 5000
  let m := i + 1
  if m % 2 = 1 then
    let sgn : ℤ := if ((m - 1) / 2) % 2 = 0 then 1 else -1
    base + (-2 * c.w.getD i 0 * sgn * 1000000000000) / (PILO * (m : ℤ))
  else base

private def asErrInt (c : CertData) (i : ℕ) : ℤ :=
  let m := i + 1
  if m % 2 = 1 then
    cdiv (2 * |c.w.getD i 0| * 10000000000000000) (ZSC * (m : ℤ) * PILO * PILO) + 1
  else 0

private def errPsiInt (c : CertData) : ℤ :=
  let sumSErr := (List.range 12).foldl (fun acc i => acc + asErrInt c i) 0
  let sumAcAs := (List.range 12).foldl (fun acc i => acc + |acInt c i| + |asInt c i| + asErrInt c i) 0
  sumSErr + cdiv (sumAcAs * 10240) SB + 3

private def errPsipInt (c : CertData) : ℤ :=
  let sumMSErr := (List.range 12).foldl (fun acc i => acc + ((i + 1 : ℕ) : ℤ) * asErrInt c i) 0
  let sumMAcAs := (List.range 12).foldl (fun acc i =>
    acc + ((i + 1 : ℕ) : ℤ) * (|acInt c i| + |asInt c i| + asErrInt c i)) 0
  cdiv (PIHI * sumMSErr) 200000000 + cdiv (sumMAcAs * (PIHI * 10240 + SB)) (200000000 * SB) + 2

private def Lq2Int (c : CertData) : ℤ :=
  let sumM2AcAs := (List.range 12).foldl (fun acc i =>
    acc + ((i + 1 : ℕ) : ℤ) ^ 2 * (|acInt c i| + |asInt c i| + asErrInt c i)) 0
  cdiv (sumM2AcAs * PIHI * PIHI) 40000000000000000

private def stepL1Int (c : CertData) (acL asL : List ℤ) (j : ℕ) : ℤ :=
  let numT : ℤ := 2 * (j : ℤ) - 1023
  let ctInt : ℤ := -2 * (c.lam1 - c.eta) * 10000
  let (trigQ, trigQp) := (List.range 12).foldl (fun (acc : ℤ × ℤ) i =>
    let m : ℤ := (i + 1 : ℕ)
    let kt : ℤ := m * numT
    let cv := cosInt kt
    let sv := sinInt kt
    let aci := acL.getD i 0
    let asi := asL.getD i 0
    (acc.1 + aci * cv + asi * sv, acc.2 + m * (-aci * sv + asi * cv))) (0, 0)
  let qInt := (ctInt * numT) / 1024 - c.kappa * 10000 + trigQ / SB
  let qpInt := ctInt + (PILO * trigQp) / 2000000000000000000
  let qa1024 := 1024 * |qInt|
  let qb := |qpInt|
  if qb ≤ qa1024 then 2 * qa1024
  else cdiv (qa1024 * qa1024 + qb * qb) qb

private def sumL1IntLoop (c : CertData) (acL asL : List ℤ) : ℕ → ℤ → ℤ
  | 0, acc => acc
  | n + 1, acc => sumL1IntLoop c acL asL n (acc + stepL1Int c acL asL n)

private def L1ubQ (c : CertData) : ℤ :=
  let acL := (List.range 12).map (acInt c)
  let asL := (List.range 12).map (asInt c)
  let l1Sum := sumL1IntLoop c acL asL 1024 0
  let l1Num := 3 * l1Sum + 3 * 2 * 1024 * 1024 * errPsiInt c + 3 * 2 * 1024 * errPsipInt c + Lq2Int c
  cdiv (l1Num * QSC) (6 * 1024 * 1024 * FSC)

private def C0ubQ (c : CertData) : ℤ :=
  let base := c.lam0 * 100 + cdiv (2 * c.lam2 * 100) 3 + L1ubQ c
  (List.range 12).foldl (fun acc i =>
    if i = 1 then acc
    else
      let m : ℕ := i + 1
      let ui := c.u.getD i 0
      let ri := c.r.getD i 0
      let qi := c.q.getD i 0
      let sTerm := if m % 2 = 1 then
        cdiv (2 * ui * 10000000000000000 * QSC) (ZSC * (m : ℤ) * (m : ℤ) * PILO * PILO)
      else 0
      let qTerm := cdiv ((ri * ri + qi * qi) * QSC) (8 * ZSC * ui)
      acc + sTerm + qTerm) base

private def certC0Int (c : CertData) : ℤ :=
  -(C0ubQ c + cdiv (379005 * DubQ c) 1000000)

/-! Soundness of `DubQ`, `L1ubQ`, `C0ubQ` -/

private lemma foldl_range_12 (g : ℕ → ℤ) :
    (List.range 12).foldl (fun acc i => acc + g i) 0 = ∑ i : Fin 12, g i.1 := by
  simp [Fin.sum_univ_succ, List.range_succ]; ring

private lemma foldl_range_12_prod (g1 g2 : ℕ → ℤ) :
    (List.range 12).foldl (fun (acc : ℤ × ℤ) i => (acc.1 + g1 i, acc.2 + g2 i)) (0, 0) =
      (∑ i : Fin 12, g1 i.1, ∑ i : Fin 12, g2 i.1) := by
  ext <;> (simp [Fin.sum_univ_succ, List.range_succ]; ring)

private lemma sumDIntLoop_eq (c : CertData) (n : ℕ) (acc : ℤ) :
    sumDIntLoop c n acc = acc + ∑ j ∈ Finset.range n, stepDInt c j := by
  induction n generalizing acc with
  | zero => simp [sumDIntLoop]
  | succ n ih =>
      simp only [sumDIntLoop, ih, Finset.sum_range_succ]; ring

private lemma sumL1IntLoop_eq (c : CertData) (acL asL : List ℤ) (n : ℕ) (acc : ℤ) :
    sumL1IntLoop c acL asL n acc = acc + ∑ j ∈ Finset.range n, stepL1Int c acL asL j := by
  induction n generalizing acc with
  | zero => simp [sumL1IntLoop]
  | succ n ih =>
      simp only [sumL1IntLoop, ih, Finset.sum_range_succ]; ring

private lemma pi_bounds : (PILO : ℝ) / 100000000 < π ∧ π < (PIHI : ℝ) / 100000000 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  constructor <;> norm_num [PILO, PIHI] <;> linarith

private lemma DubQ_sound (c : CertData) :
    ∫ x in (-2 : ℝ)..2, max 0 (-PCert c x) ≤ (DubQ c : ℝ) / (QSC : ℝ) := by
  -- Derivatives of PCert c
  let P' : ℝ → ℝ := fun x =>
    (c.lam1 : ℝ) / (ZSC : ℝ) + 2 * ((c.lam2 : ℝ) / (ZSC : ℝ)) * x +
      (1 / 2) * ∑ i : Fin 12,
        ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
          (-uReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) +
            wReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2)))
  let P'' : ℝ → ℝ := fun x =>
    2 * ((c.lam2 : ℝ) / (ZSC : ℝ)) +
      (1 / 2) * ∑ i : Fin 12,
        ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 *
          (-uReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) -
            wReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2)))
  have hP_deriv : ∀ x : ℝ, HasDerivAt (PCert c) (P' x) x := fun x => by
    unfold PCert; simp only [P']
    have hpoly : HasDerivAt (fun y => (c.lam0 : ℝ) / (ZSC : ℝ) + ((c.lam1 : ℝ) / (ZSC : ℝ)) * y +
        ((c.lam2 : ℝ) / (ZSC : ℝ)) * y ^ 2)
        ((c.lam1 : ℝ) / (ZSC : ℝ) + 2 * ((c.lam2 : ℝ) / (ZSC : ℝ)) * x) x := by
      have h1 := ((hasDerivAt_const x ((c.lam0 : ℝ) / (ZSC : ℝ))).add
        ((hasDerivAt_id x).const_mul ((c.lam1 : ℝ) / (ZSC : ℝ)))).add
        ((hasDerivAt_pow 2 x).const_mul ((c.lam2 : ℝ) / (ZSC : ℝ)))
      rw [show (c.lam1 : ℝ) / (ZSC : ℝ) + 2 * ((c.lam2 : ℝ) / (ZSC : ℝ)) * x =
        0 + (c.lam1 : ℝ) / (ZSC : ℝ) * 1 + (c.lam2 : ℝ) / (ZSC : ℝ) * (((2 : ℕ) : ℝ) * x ^ (2 - 1)) by norm_num; ring]
      exact h1
    have htrig : HasDerivAt (fun y => (1 / 2) * ∑ i : Fin 12,
        (uReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * y / 2) +
         wReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * y / 2)))
        ((1 / 2) * ∑ i : Fin 12,
          ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
            (-uReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) +
              wReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2)))) x := by
      refine (HasDerivAt.fun_sum fun i _ => ?_).const_mul (1 / 2)
      have ha : HasDerivAt (fun y => π * ((i.1 + 1 : ℕ) : ℝ) * y / 2) (π * ((i.1 + 1 : ℕ) : ℝ) / 2) x := by
        have h1 := ((hasDerivAt_id x).const_mul (π * ((i.1 + 1 : ℕ) : ℝ))).div_const 2
        rw [show π * ((i.1 + 1 : ℕ) : ℝ) / 2 = π * ((i.1 + 1 : ℕ) : ℝ) * 1 / 2 by ring]
        exact h1
      have hc := ((Real.hasDerivAt_cos _).comp x ha).const_mul (uReal c i)
      have hs := ((Real.hasDerivAt_sin _).comp x ha).const_mul (wReal c i)
      rw [show (π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
        (-uReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) +
          wReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2)) =
        uReal c i * (-Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) * (π * ((i.1 + 1 : ℕ) : ℝ) / 2)) +
        wReal c i * (Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) * (π * ((i.1 + 1 : ℕ) : ℝ) / 2)) by ring]
      exact hc.add hs
    exact hpoly.add htrig
  have hP'_deriv : ∀ x : ℝ, HasDerivAt P' (P'' x) x := fun x => by
    simp only [P', P'']
    have hpoly : HasDerivAt (fun y => (c.lam1 : ℝ) / (ZSC : ℝ) + 2 * ((c.lam2 : ℝ) / (ZSC : ℝ)) * y)
        (2 * ((c.lam2 : ℝ) / (ZSC : ℝ))) x := by
      simpa only [mul_one] using
        ((hasDerivAt_id' x).const_mul (2 * ((c.lam2 : ℝ) / (ZSC : ℝ)))).const_add ((c.lam1 : ℝ) / (ZSC : ℝ))
    have htrig : HasDerivAt (fun y => (1 / 2) * ∑ i : Fin 12,
        ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
          (-uReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * y / 2) +
            wReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * y / 2))))
        ((1 / 2) * ∑ i : Fin 12,
          ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 *
            (-uReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) -
              wReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2)))) x := by
      refine (HasDerivAt.fun_sum fun i _ => ?_).const_mul (1 / 2)
      have ha : HasDerivAt (fun y => π * ((i.1 + 1 : ℕ) : ℝ) * y / 2) (π * ((i.1 + 1 : ℕ) : ℝ) / 2) x := by
        have h1 := ((hasDerivAt_id x).const_mul (π * ((i.1 + 1 : ℕ) : ℝ))).div_const 2
        rw [show π * ((i.1 + 1 : ℕ) : ℝ) / 2 = π * ((i.1 + 1 : ℕ) : ℝ) * 1 / 2 by ring]
        exact h1
      have hs := ((Real.hasDerivAt_sin _).comp x ha).const_mul (-uReal c i)
      have hc := ((Real.hasDerivAt_cos _).comp x ha).const_mul (wReal c i)
      rw [show (π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 *
        (-uReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) -
          wReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2)) =
        (π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
          (-uReal c i * (Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) * (π * ((i.1 + 1 : ℕ) : ℝ) / 2)) +
           wReal c i * (-Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) * (π * ((i.1 + 1 : ℕ) : ℝ) / 2))) by ring]
      exact (hs.add hc).const_mul (π * ((i.1 + 1 : ℕ) : ℝ) / 2)
    exact hpoly.add htrig
  have hP''c : Continuous P'' := by
    refine continuous_const.add (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_))
    exact continuous_const.mul
      ((continuous_const.mul (Real.continuous_cos.comp ((continuous_const.mul continuous_id).div_const 2))).sub
       (continuous_const.mul (Real.continuous_sin.comp ((continuous_const.mul continuous_id).div_const 2))))
  have hpi := pi_bounds
  have hpi_pos : 0 < π := Real.pi_pos
  -- Bound |P'' x| ≤ Lp2Int c / FSC
  have hP''b : ∀ x : ℝ, |P'' x| ≤ (Lp2Int c : ℝ) / (FSC : ℝ) := fun x => by
    simp only [P'']
    have h1 : |∑ i : Fin 12, (π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 *
        (-uReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) -
          wReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2))| ≤
        (π ^ 2 / (4 * (ZSC : ℝ))) * (sumM2AbsUW c : ℝ) := by
      have htri := Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin 12)))
        (f := fun i => (π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 *
          (-uReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) -
            wReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2)))
      have hterm : ∀ i : Fin 12,
          |(π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 *
            (-uReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) -
              wReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2))| ≤
          (π ^ 2 / (4 * (ZSC : ℝ))) * (((i.1 + 1 : ℕ) : ℝ) ^ 2 * (|(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)|)) := by
        intro i
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hcs : |-uReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2) -
            wReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2)| ≤
            (|(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)|) / (ZSC : ℝ) := by
          have hc1 : |Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2)| ≤ 1 := Real.abs_cos_le_one _
          have hs1 : |Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * x / 2)| ≤ 1 := Real.abs_sin_le_one _
          calc |-uReal c i * Real.cos _ - wReal c i * Real.sin _|
              ≤ |-uReal c i * Real.cos _| + |wReal c i * Real.sin _| := abs_sub _ _
            _ = |uReal c i| * |Real.cos _| + |wReal c i| * |Real.sin _| := by rw [abs_mul, abs_neg, abs_mul]
            _ ≤ |uReal c i| * 1 + |wReal c i| * 1 := by gcongr
            _ = (|(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)|) / (ZSC : ℝ) := by
                simp only [uReal, wReal, getI, abs_div, abs_of_pos (by norm_num [ZSC] : (0 : ℝ) < ZSC)]; ring
        calc (π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 * |-uReal c i * Real.cos _ - wReal c i * Real.sin _|
            ≤ (π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 * ((|(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)|) / (ZSC : ℝ)) := by gcongr
          _ = (π ^ 2 / (4 * (ZSC : ℝ))) * (((i.1 + 1 : ℕ) : ℝ) ^ 2 * (|(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)|)) := by ring
      have hsum := htri.trans (Finset.sum_le_sum fun i _ => hterm i)
      rw [← Finset.mul_sum] at hsum
      have heq : (sumM2AbsUW c : ℝ) = ∑ i : Fin 12,
          ((i.1 + 1 : ℕ) : ℝ) ^ 2 * (|(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)|) := by
        unfold sumM2AbsUW; rw [foldl_range_12]; push_cast; rfl
      rw [heq]; exact hsum
    have hsm_nn : (0 : ℝ) ≤ (sumM2AbsUW c : ℝ) := by
      unfold sumM2AbsUW; rw [foldl_range_12]; push_cast; positivity
    have hpi2 : π ^ 2 ≤ ((PIHI : ℝ) / 100000000) ^ 2 := by nlinarith [hpi.2, hpi_pos]
    have hcd := le_cdiv_real (sumM2AbsUW c * PIHI * PIHI) (8 * ZSC * 100000000) (by norm_num [ZSC])
    calc |2 * ((c.lam2 : ℝ) / (ZSC : ℝ)) + (1 / 2) * ∑ i : Fin 12, _|
        ≤ |2 * ((c.lam2 : ℝ) / (ZSC : ℝ))| + |(1 / 2) * ∑ i : Fin 12, _| := abs_add_le _ _
      _ = |2 * ((c.lam2 : ℝ) / (ZSC : ℝ))| + (1 / 2) * |∑ i : Fin 12, _| := by
          rw [abs_mul (1 / 2 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      _ ≤ 2 * (|(c.lam2 : ℝ)| / (ZSC : ℝ)) + (1 / 2) * ((π ^ 2 / (4 * (ZSC : ℝ))) * (sumM2AbsUW c : ℝ)) := by
          have : |2 * ((c.lam2 : ℝ) / (ZSC : ℝ))| = 2 * (|(c.lam2 : ℝ)| / (ZSC : ℝ)) := by
            rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
              abs_of_pos (by norm_num [ZSC] : (0 : ℝ) < ZSC)]
          linarith
      _ ≤ 2 * (|(c.lam2 : ℝ)| / (ZSC : ℝ)) +
          (((sumM2AbsUW c : ℝ) * (PIHI : ℝ) * (PIHI : ℝ)) / (8 * (ZSC : ℝ) * 100000000)) / (FSC : ℝ) := by
          have hZSC : (0 : ℝ) ≤ 4 * (ZSC : ℝ) := by norm_num [ZSC]
          have hle : (1 / 2) * ((π ^ 2 / (4 * (ZSC : ℝ))) * (sumM2AbsUW c : ℝ)) ≤
              (1 / 2) * ((((PIHI : ℝ) / 100000000) ^ 2 / (4 * (ZSC : ℝ))) * (sumM2AbsUW c : ℝ)) := by gcongr
          have heq : (1 / 2) * ((((PIHI : ℝ) / 100000000) ^ 2 / (4 * (ZSC : ℝ))) * (sumM2AbsUW c : ℝ)) =
              (((sumM2AbsUW c : ℝ) * (PIHI : ℝ) * (PIHI : ℝ)) / (8 * (ZSC : ℝ) * 100000000)) / (FSC : ℝ) := by
            unfold FSC ZSC; push_cast; ring
          linarith
      _ ≤ (Lp2Int c : ℝ) / (FSC : ℝ) := by
          unfold Lp2Int; push_cast
          have hcd' : ((sumM2AbsUW c : ℝ) * (PIHI : ℝ) * (PIHI : ℝ)) / (8 * (ZSC : ℝ) * 100000000) ≤
              (cdiv (sumM2AbsUW c * PIHI * PIHI) (8 * ZSC * 100000000) : ℝ) := by
            simpa [Int.cast_mul, Int.cast_ofNat] using hcd
          have hlam : 2 * (|(c.lam2 : ℝ)| / (ZSC : ℝ)) = (2 * |(c.lam2 : ℝ)| * 10000) / (FSC : ℝ) := by
            norm_num [ZSC, FSC]; ring
          rw [hlam, ← add_div]
          exact div_le_div_of_nonneg_right (by linarith) (by norm_num [FSC])
  have hLp2_nn : (0 : ℝ) ≤ (Lp2Int c : ℝ) / (FSC : ℝ) := le_trans (abs_nonneg (P'' 0)) (hP''b 0)
  -- Split [-2, 2] into 1024 intervals of width 2/512 = 1/256 (half-width hx = 1/512)
  have hsplit : ∫ x in (-2 : ℝ)..2, max 0 (-PCert c x) =
      ∑ j ∈ Finset.range 1024,
        ∫ x in ((-2 : ℝ) + 2 * (j : ℝ) / 512)..((-2 : ℝ) + 2 * ((j + 1 : ℕ) : ℝ) / 512),
          max 0 (-PCert c x) := by
    have hcont : Continuous (fun x => max 0 (-PCert c x)) :=
      continuous_const.max (PCert_continuous c).neg
    have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (n := 1024)
      (a := fun j : ℕ => (-2 : ℝ) + 2 * (j : ℝ) / 512)
      (f := fun x => max 0 (-PCert c x))
      (fun j _ => hcont.intervalIntegrable (μ := volume) _ _)
    rw [hsum]
    rw [show ((-2 : ℝ) + 2 * ((0 : ℕ) : ℝ) / 512) = -2 by norm_num,
        show ((-2 : ℝ) + 2 * ((1024 : ℕ) : ℝ) / 512) = 2 by norm_num]
  rw [hsplit]
  -- Bound each subinterval j
  have hterm_j : ∀ j ∈ Finset.range 1024,
      ∫ x in ((-2 : ℝ) + 2 * (j : ℝ) / 512)..((-2 : ℝ) + 2 * ((j + 1 : ℕ) : ℝ) / 512),
        max 0 (-PCert c x) ≤
      (stepDInt c j : ℝ) / (512 ^ 2 * (FSC : ℝ)) +
      2 * ((errPInt c : ℝ) / (FSC : ℝ)) * (1 / 512) +
      2 * ((errPpInt c : ℝ) / (FSC : ℝ)) * (1 / 512) ^ 2 +
      (1 / 3) * ((Lp2Int c : ℝ) / (FSC : ℝ)) * (1 / 512) ^ 3 := by
    intro j _
    set numX : ℤ := 2 * (j : ℤ) - 1023
    set mX : ℝ := (numX : ℝ) / 512
    have hlo : (-2 : ℝ) + 2 * (j : ℝ) / 512 = mX - 1 / 512 := by
      simp only [mX, numX]; push_cast; ring
    have hhi : (-2 : ℝ) + 2 * ((j + 1 : ℕ) : ℝ) / 512 = mX + 1 / 512 := by
      simp only [mX, numX]; push_cast; ring
    rw [hlo, hhi]
    set trigP : ℤ := ∑ i : Fin 12,
      (c.u.getD i.1 0 * cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) +
       c.w.getD i.1 0 * sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)))
    set trigPp : ℤ := ∑ i : Fin 12,
      (((i.1 + 1 : ℕ) : ℤ) * (-c.u.getD i.1 0 * sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) +
        c.w.getD i.1 0 * cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX))))
    set pInt : ℤ := c.lam0 * 10000 + (c.lam1 * numX * 10000) / 512 +
      (c.lam2 * numX * numX * 10000) / (512 * 512) + trigP / 2000000
    set ppInt : ℤ := c.lam1 * 10000 + (2 * c.lam2 * numX * 10000) / 512 +
      (PILO * trigPp) / 400000000000000
    have hang : ∀ i : Fin 12,
        π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2 = ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) : ℝ) * θ₀ := fun i => by
      simp only [mX, θ₀]; push_cast; ring
    -- Bound |PCert c mX - pInt / FSC| ≤ errPInt c / FSC
    have ha_err : |PCert c mX - (pInt : ℝ) / (FSC : ℝ)| ≤ (errPInt c : ℝ) / (FSC : ℝ) := by
      have hd1 := ediv_real_err (c.lam1 * numX * 10000) 512 (by norm_num)
      have hd2 := ediv_real_err (c.lam2 * numX * numX * 10000) (512 * 512) (by norm_num)
      have hd3 := ediv_real_err trigP 2000000 (by norm_num)
      have htrig_err : |(1 / 2) * ∑ i : Fin 12,
          (uReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2) +
           wReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2)) -
          (trigP : ℝ) / (2000000 * (FSC : ℝ))| ≤
          (sumAbsUW c : ℝ) * 10240 / (2 * (ZSC : ℝ) * (SB : ℝ)) := by
        have hEq : (1 / 2) * ∑ i : Fin 12,
            (uReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2) +
             wReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2)) -
            (trigP : ℝ) / (2000000 * (FSC : ℝ)) =
            (1 / (2 * (ZSC : ℝ))) * ∑ i : Fin 12,
              ((c.u.getD i.1 0 : ℝ) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                (cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)) +
               (c.w.getD i.1 0 : ℝ) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                (sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ))) := by
          simp only [trigP, uReal, wReal, getI, hang]; push_cast
          rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          norm_num [ZSC, FSC, SB]; ring
        rw [hEq, abs_mul, abs_of_pos (by norm_num [ZSC] : (0 : ℝ) < 1 / (2 * (ZSC : ℝ)))]
        have hsum_bd : |∑ i : Fin 12,
            ((c.u.getD i.1 0 : ℝ) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
              (cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)) +
             (c.w.getD i.1 0 : ℝ) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
              (sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)))| ≤
            (sumAbsUW c : ℝ) * (10240 / (SB : ℝ)) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          have hterm : ∀ i : Fin 12,
              |(c.u.getD i.1 0 : ℝ) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                (cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)) +
               (c.w.getD i.1 0 : ℝ) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                (sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ))| ≤
              (|(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)|) * (10240 / (SB : ℝ)) := fun i => by
            have he := cosInt_sinInt_err (((i.1 + 1 : ℕ) : ℤ) * (2 * numX))
            have h1 := abs_add_le
              ((c.u.getD i.1 0 : ℝ) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                (cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)))
              ((c.w.getD i.1 0 : ℝ) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                (sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)))
            rw [abs_mul, abs_mul] at h1
            have h2 := mul_le_mul_of_nonneg_left he.1 (abs_nonneg (c.u.getD i.1 0 : ℝ))
            have h3 := mul_le_mul_of_nonneg_left he.2 (abs_nonneg (c.w.getD i.1 0 : ℝ))
            linarith
          refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
          rw [← Finset.sum_mul]; congr 1
          unfold sumAbsUW; simp only [add_assoc]; rw [foldl_range_12]; push_cast; rfl
        calc (1 / (2 * (ZSC : ℝ))) * |∑ i : Fin 12,
              ((c.u.getD i.1 0 : ℝ) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                (cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)) +
               (c.w.getD i.1 0 : ℝ) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                (sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)))|
            ≤ (1 / (2 * (ZSC : ℝ))) * ((sumAbsUW c : ℝ) * (10240 / (SB : ℝ))) :=
              mul_le_mul_of_nonneg_left hsum_bd (by norm_num [ZSC])
          _ = (sumAbsUW c : ℝ) * 10240 / (2 * (ZSC : ℝ) * (SB : ℝ)) := by ring
      -- Combine trig error + 3 floor division errors
      have hdecomp : PCert c mX - (pInt : ℝ) / (FSC : ℝ) =
          (((c.lam1 : ℝ) * (numX : ℝ) * 10000 / 512 - (((c.lam1 * numX * 10000) / 512 : ℤ) : ℝ)) / (FSC : ℝ)) +
          (((c.lam2 : ℝ) * (numX : ℝ) * (numX : ℝ) * 10000 / (512 * 512) -
            (((c.lam2 * numX * numX * 10000) / (512 * 512) : ℤ) : ℝ)) / (FSC : ℝ)) +
          (((trigP : ℝ) / 2000000 - ((trigP / 2000000 : ℤ) : ℝ)) / (FSC : ℝ)) +
          ((1 / 2) * ∑ i : Fin 12,
            (uReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2) +
             wReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2)) -
            (trigP : ℝ) / (2000000 * (FSC : ℝ))) := by
        unfold PCert; simp only [pInt, mX]; push_cast; norm_num [ZSC, FSC]; ring
      rw [hdecomp]
      have h3 : |(((c.lam1 : ℝ) * (numX : ℝ) * 10000 / 512 - (((c.lam1 * numX * 10000) / 512 : ℤ) : ℝ)) / (FSC : ℝ))| ≤ 1 / (FSC : ℝ) := by
        rw [abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC), abs_sub_comm]
        exact div_le_div_of_nonneg_right (by simpa [Int.cast_mul, Int.cast_ofNat] using hd1) (by norm_num [FSC])
      have h4 : |(((c.lam2 : ℝ) * (numX : ℝ) * (numX : ℝ) * 10000 / (512 * 512) -
          (((c.lam2 * numX * numX * 10000) / (512 * 512) : ℤ) : ℝ)) / (FSC : ℝ))| ≤ 1 / (FSC : ℝ) := by
        rw [abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC), abs_sub_comm]
        have hd2' : |(((c.lam2 * numX * numX * 10000) / (512 * 512) : ℤ) : ℝ) -
            (c.lam2 : ℝ) * (numX : ℝ) * (numX : ℝ) * 10000 / (512 * 512)| ≤ 1 := by
          convert hd2 using 2; push_cast; norm_num
        exact div_le_div_of_nonneg_right hd2' (by norm_num [FSC])
      have h5 : |(((trigP : ℝ) / 2000000 - ((trigP / 2000000 : ℤ) : ℝ)) / (FSC : ℝ))| ≤ 1 / (FSC : ℝ) := by
        rw [abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC), abs_sub_comm]
        exact div_le_div_of_nonneg_right (by simpa [Int.cast_ofNat] using hd3) (by norm_num [FSC])
      have hcd := le_cdiv_real (sumAbsUW c * 10240) 2000000 (by norm_num)
      have hcomb : (sumAbsUW c : ℝ) * 10240 / (2 * (ZSC : ℝ) * (SB : ℝ)) + 3 / (FSC : ℝ) ≤
          (errPInt c : ℝ) / (FSC : ℝ) := by
        unfold errPInt; push_cast
        have hcd' : (sumAbsUW c : ℝ) * 10240 / 2000000 ≤ (cdiv (sumAbsUW c * 10240) 2000000 : ℝ) := by
          simpa [Int.cast_mul, Int.cast_ofNat] using hcd
        have heq : (sumAbsUW c : ℝ) * 10240 / (2 * (ZSC : ℝ) * (SB : ℝ)) =
            ((sumAbsUW c : ℝ) * 10240 / 2000000) / (FSC : ℝ) := by norm_num [ZSC, SB, FSC]; ring
        rw [heq, ← add_div]
        exact div_le_div_of_nonneg_right (by linarith) (by norm_num [FSC])
      have ha1 := abs_add_le
        ((((c.lam1 : ℝ) * (numX : ℝ) * 10000 / 512 - (((c.lam1 * numX * 10000) / 512 : ℤ) : ℝ)) / (FSC : ℝ)) +
         (((c.lam2 : ℝ) * (numX : ℝ) * (numX : ℝ) * 10000 / (512 * 512) -
           (((c.lam2 * numX * numX * 10000) / (512 * 512) : ℤ) : ℝ)) / (FSC : ℝ)) +
         (((trigP : ℝ) / 2000000 - ((trigP / 2000000 : ℤ) : ℝ)) / (FSC : ℝ)))
        ((1 / 2) * ∑ i : Fin 12,
          (uReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2) +
           wReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2)) -
          (trigP : ℝ) / (2000000 * (FSC : ℝ)))
      have ha2 := abs_add_le
        ((((c.lam1 : ℝ) * (numX : ℝ) * 10000 / 512 - (((c.lam1 * numX * 10000) / 512 : ℤ) : ℝ)) / (FSC : ℝ)) +
         (((c.lam2 : ℝ) * (numX : ℝ) * (numX : ℝ) * 10000 / (512 * 512) -
           (((c.lam2 * numX * numX * 10000) / (512 * 512) : ℤ) : ℝ)) / (FSC : ℝ)))
        (((trigP : ℝ) / 2000000 - ((trigP / 2000000 : ℤ) : ℝ)) / (FSC : ℝ))
      have ha3 := abs_add_le
        (((c.lam1 : ℝ) * (numX : ℝ) * 10000 / 512 - (((c.lam1 * numX * 10000) / 512 : ℤ) : ℝ)) / (FSC : ℝ))
        (((c.lam2 : ℝ) * (numX : ℝ) * (numX : ℝ) * 10000 / (512 * 512) -
          (((c.lam2 * numX * numX * 10000) / (512 * 512) : ℤ) : ℝ)) / (FSC : ℝ))
      have h3f : 1 / (FSC : ℝ) + 1 / (FSC : ℝ) + 1 / (FSC : ℝ) = 3 / (FSC : ℝ) := by ring
      linarith
    -- Bound |P' mX - ppInt / FSC| ≤ errPpInt c / FSC
    have hb_err : |P' mX - (ppInt : ℝ) / (FSC : ℝ)| ≤ (errPpInt c : ℝ) / (FSC : ℝ) := by
      have hd1 := ediv_real_err (2 * c.lam2 * numX * 10000) 512 (by norm_num)
      have hd2 := ediv_real_err (PILO * trigPp) 400000000000000 (by norm_num)
      have htrig_err : |(1 / 2) * ∑ i : Fin 12,
          ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
            (-uReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2) +
              wReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2))) -
          ((PILO : ℝ) * (trigPp : ℝ)) / (400000000000000 * (FSC : ℝ))| ≤
          (sumMAbsUW c : ℝ) * ((PIHI : ℝ) * 10240 + (SB : ℝ)) / (4 * (ZSC : ℝ) * (SB : ℝ) * (FSC : ℝ)) := by
        have hEq : (1 / 2) * ∑ i : Fin 12,
            ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
              (-uReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2) +
                wReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2))) -
            ((PILO : ℝ) * (trigPp : ℝ)) / (400000000000000 * (FSC : ℝ)) =
            (1 / (4 * (ZSC : ℝ))) * ∑ i : Fin 12,
              (((i.1 + 1 : ℕ) : ℝ) *
                (π * (-(c.u.getD i.1 0 : ℝ) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                    (sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)) +
                  (c.w.getD i.1 0 : ℝ) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                    (cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ))) +
                 (π - (PILO : ℝ) / 100000000) *
                  (-(c.u.getD i.1 0 : ℝ) * ((sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)) +
                   (c.w.getD i.1 0 : ℝ) * ((cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ))))) := by
          simp only [trigPp, uReal, wReal, getI, hang]; push_cast
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          norm_num [ZSC, FSC, SB]; ring
        rw [hEq, abs_mul, abs_of_pos (by norm_num [ZSC] : (0 : ℝ) < 1 / (4 * (ZSC : ℝ)))]
        have hpi_diff : |π - (PILO : ℝ) / 100000000| ≤ 1 / 100000000 := by
          rw [abs_le]; constructor <;> norm_num [PILO, PIHI] at hpi ⊢ <;> linarith
        have hcs_le : ∀ k : ℤ, |(cosInt k : ℝ) / (SB : ℝ)| ≤ 1 + 10240 / (SB : ℝ) ∧
            |(sinInt k : ℝ) / (SB : ℝ)| ≤ 1 + 10240 / (SB : ℝ) := fun k => by
          have he := cosInt_sinInt_err k
          constructor
          · have h1 := Real.abs_cos_le_one ((k : ℝ) * θ₀)
            have h2 := abs_sub_abs_le_abs_sub ((cosInt k : ℝ) / (SB : ℝ)) (Real.cos ((k : ℝ) * θ₀))
            rw [abs_sub_comm] at h2; linarith [he.1]
          · have h1 := Real.abs_sin_le_one ((k : ℝ) * θ₀)
            have h2 := abs_sub_abs_le_abs_sub ((sinInt k : ℝ) / (SB : ℝ)) (Real.sin ((k : ℝ) * θ₀))
            rw [abs_sub_comm] at h2; linarith [he.2]
        -- Even simpler: rewrite with (π - PILO/10^8) multiplying exact sin/cos (bounded by 1!),
        -- and PILO/10^8 multiplying trig error (bounded by 10240/SB)!
        -- Wait: our hEq has π multiplying trig error (bounded by PIHI/10^8 * 10240/SB) and (π - PILO/10^8) multiplying cosInt/SB (bounded by 1 + 10^-6).
        -- Since PIHI/10^8 * 10240/SB is slightly larger than π * 10240/SB (by > 10^-14), let's just split the OTHER way!
        have hEq2 : (1 / (4 * (ZSC : ℝ))) * |∑ i : Fin 12,
              (((i.1 + 1 : ℕ) : ℝ) *
                (π * (-(c.u.getD i.1 0 : ℝ) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                    (sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)) +
                  (c.w.getD i.1 0 : ℝ) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                    (cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ))) +
                 (π - (PILO : ℝ) / 100000000) *
                  (-(c.u.getD i.1 0 : ℝ) * ((sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)) +
                   (c.w.getD i.1 0 : ℝ) * ((cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)))))| =
            (1 / (4 * (ZSC : ℝ))) * |∑ i : Fin 12,
              (((i.1 + 1 : ℕ) : ℝ) *
                (((PILO : ℝ) / 100000000) *
                  (-(c.u.getD i.1 0 : ℝ) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                    (sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)) +
                   (c.w.getD i.1 0 : ℝ) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                    (cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ))) +
                 (π - (PILO : ℝ) / 100000000) *
                  (-(c.u.getD i.1 0 : ℝ) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) +
                   (c.w.getD i.1 0 : ℝ) * Real.cos ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀))))| := by
          congr 2; refine Finset.sum_congr rfl fun i _ => by ring
        rw [hEq2]
        have hsum_bd : |∑ i : Fin 12,
              (((i.1 + 1 : ℕ) : ℝ) *
                (((PILO : ℝ) / 100000000) *
                  (-(c.u.getD i.1 0 : ℝ) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                    (sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)) +
                   (c.w.getD i.1 0 : ℝ) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                    (cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ))) +
                 (π - (PILO : ℝ) / 100000000) *
                  (-(c.u.getD i.1 0 : ℝ) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) +
                   (c.w.getD i.1 0 : ℝ) * Real.cos ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀))))| ≤
            (sumMAbsUW c : ℝ) * (((PIHI : ℝ) * 10240 + (SB : ℝ)) / ((SB : ℝ) * (FSC : ℝ))) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          have hterm : ∀ i : Fin 12,
              |((i.1 + 1 : ℕ) : ℝ) *
                (((PILO : ℝ) / 100000000) *
                  (-(c.u.getD i.1 0 : ℝ) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                    (sinInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ)) +
                   (c.w.getD i.1 0 : ℝ) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) -
                    (cosInt (((i.1 + 1 : ℕ) : ℤ) * (2 * numX)) : ℝ) / (SB : ℝ))) +
                 (π - (PILO : ℝ) / 100000000) *
                  (-(c.u.getD i.1 0 : ℝ) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀) +
                   (c.w.getD i.1 0 : ℝ) * Real.cos ((((i.1 + 1 : ℕ) : ℤ) * (2 * numX) : ℤ) * θ₀)))| ≤
              (((i.1 + 1 : ℕ) : ℝ) * (|(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)|)) *
                (((PIHI : ℝ) * 10240 + (SB : ℝ)) / ((SB : ℝ) * (FSC : ℝ))) := fun i => by
            set kxi : ℤ := ((i.1 + 1 : ℕ) : ℤ) * (2 * numX)
            have he := cosInt_sinInt_err kxi
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            have ht1 : |((PILO : ℝ) / 100000000) *
                (-(c.u.getD i.1 0 : ℝ) * (Real.sin ((kxi : ℝ) * θ₀) - (sinInt kxi : ℝ) / (SB : ℝ)) +
                 (c.w.getD i.1 0 : ℝ) * (Real.cos ((kxi : ℝ) * θ₀) - (cosInt kxi : ℝ) / (SB : ℝ)))| ≤
                ((PIHI : ℝ) / 100000000) * ((|(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)|) * (10240 / (SB : ℝ))) := by
              rw [abs_mul, abs_of_pos (by norm_num [PILO])]
              have h1 : |-(c.u.getD i.1 0 : ℝ) * (Real.sin ((kxi : ℝ) * θ₀) - (sinInt kxi : ℝ) / (SB : ℝ)) +
                  (c.w.getD i.1 0 : ℝ) * (Real.cos ((kxi : ℝ) * θ₀) - (cosInt kxi : ℝ) / (SB : ℝ))| ≤
                  (|(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)|) * (10240 / (SB : ℝ)) := by
                have ha := abs_add_le
                  (-(c.u.getD i.1 0 : ℝ) * (Real.sin ((kxi : ℝ) * θ₀) - (sinInt kxi : ℝ) / (SB : ℝ)))
                  ((c.w.getD i.1 0 : ℝ) * (Real.cos ((kxi : ℝ) * θ₀) - (cosInt kxi : ℝ) / (SB : ℝ)))
                rw [abs_mul, abs_neg, abs_mul] at ha
                have hb := mul_le_mul_of_nonneg_left he.2 (abs_nonneg (c.u.getD i.1 0 : ℝ))
                have hc := mul_le_mul_of_nonneg_left he.1 (abs_nonneg (c.w.getD i.1 0 : ℝ))
                linarith
              have h2 : (PILO : ℝ) / 100000000 ≤ (PIHI : ℝ) / 100000000 := by norm_num [PILO, PIHI]
              exact mul_le_mul h2 h1 (abs_nonneg _) (by norm_num [PIHI])
            have ht2 : |(π - (PILO : ℝ) / 100000000) *
                (-(c.u.getD i.1 0 : ℝ) * Real.sin ((kxi : ℝ) * θ₀) + (c.w.getD i.1 0 : ℝ) * Real.cos ((kxi : ℝ) * θ₀))| ≤
                (1 / 100000000) * (|(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)|) := by
              rw [abs_mul]
              have h1 : |-(c.u.getD i.1 0 : ℝ) * Real.sin ((kxi : ℝ) * θ₀) + (c.w.getD i.1 0 : ℝ) * Real.cos ((kxi : ℝ) * θ₀)| ≤
                  |(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)| := by
                have ha := abs_add_le
                  (-(c.u.getD i.1 0 : ℝ) * Real.sin ((kxi : ℝ) * θ₀))
                  ((c.w.getD i.1 0 : ℝ) * Real.cos ((kxi : ℝ) * θ₀))
                rw [abs_mul, abs_neg, abs_mul] at ha
                have hb := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one ((kxi : ℝ) * θ₀)) (abs_nonneg (c.u.getD i.1 0 : ℝ))
                have hc := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one ((kxi : ℝ) * θ₀)) (abs_nonneg (c.w.getD i.1 0 : ℝ))
                linarith
              exact mul_le_mul hpi_diff h1 (abs_nonneg _) (by norm_num)
            have htot : |((PILO : ℝ) / 100000000) *
                  (-(c.u.getD i.1 0 : ℝ) * (Real.sin ((kxi : ℝ) * θ₀) - (sinInt kxi : ℝ) / (SB : ℝ)) +
                   (c.w.getD i.1 0 : ℝ) * (Real.cos ((kxi : ℝ) * θ₀) - (cosInt kxi : ℝ) / (SB : ℝ))) +
                 (π - (PILO : ℝ) / 100000000) *
                  (-(c.u.getD i.1 0 : ℝ) * Real.sin ((kxi : ℝ) * θ₀) +
                   (c.w.getD i.1 0 : ℝ) * Real.cos ((kxi : ℝ) * θ₀))| ≤
                (|(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)|) *
                (((PIHI : ℝ) * 10240 + (SB : ℝ)) / ((SB : ℝ) * (FSC : ℝ))) := by
              calc |_ + _| ≤ |_| + |_| := abs_add_le _ _
                _ ≤ _ := add_le_add ht1 ht2
                _ = _ := by norm_num [FSC, SB, PIHI]; ring
            calc ((i.1 + 1 : ℕ) : ℝ) * |_ + _|
                ≤ ((i.1 + 1 : ℕ) : ℝ) * ((|(c.u.getD i.1 0 : ℝ)| + |(c.w.getD i.1 0 : ℝ)|) *
                    (((PIHI : ℝ) * 10240 + (SB : ℝ)) / ((SB : ℝ) * (FSC : ℝ)))) :=
                  mul_le_mul_of_nonneg_left htot (Nat.cast_nonneg _)
              _ = _ := by ring
          refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
          rw [← Finset.sum_mul]; congr 1
          unfold sumMAbsUW; rw [foldl_range_12]; push_cast; rfl
        calc (1 / (4 * (ZSC : ℝ))) * |∑ i : Fin 12, _|
            ≤ (1 / (4 * (ZSC : ℝ))) * _ := mul_le_mul_of_nonneg_left hsum_bd (by norm_num [ZSC])
          _ = _ := by ring
      have hdecomp : P' mX - (ppInt : ℝ) / (FSC : ℝ) =
          (((2 * (c.lam2 : ℝ) * (numX : ℝ) * 10000 / 512) -
            (((2 * c.lam2 * numX * 10000) / 512 : ℤ) : ℝ)) / (FSC : ℝ)) +
          ((((PILO : ℝ) * (trigPp : ℝ) / 400000000000000) -
            (((PILO * trigPp) / 400000000000000 : ℤ) : ℝ)) / (FSC : ℝ)) +
          ((1 / 2) * ∑ i : Fin 12,
            ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
              (-uReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2) +
                wReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2))) -
            ((PILO : ℝ) * (trigPp : ℝ)) / (400000000000000 * (FSC : ℝ))) := by
        simp only [P', ppInt, mX]; push_cast; norm_num [ZSC, FSC]; ring
      rw [hdecomp]
      have h3 : |(((2 * (c.lam2 : ℝ) * (numX : ℝ) * 10000 / 512) -
          (((2 * c.lam2 * numX * 10000) / 512 : ℤ) : ℝ)) / (FSC : ℝ))| ≤ 1 / (FSC : ℝ) := by
        rw [abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC), abs_sub_comm]
        exact div_le_div_of_nonneg_right (by simpa [Int.cast_mul, Int.cast_ofNat] using hd1) (by norm_num [FSC])
      have h4 : |((((PILO : ℝ) * (trigPp : ℝ) / 400000000000000) -
          (((PILO * trigPp) / 400000000000000 : ℤ) : ℝ)) / (FSC : ℝ))| ≤ 1 / (FSC : ℝ) := by
        rw [abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC), abs_sub_comm]
        exact div_le_div_of_nonneg_right (by simpa [Int.cast_mul, Int.cast_ofNat] using hd2) (by norm_num [FSC])
      have hcd := le_cdiv_real (sumMAbsUW c * (PIHI * 10240 + SB)) (4 * ZSC * SB) (by norm_num [ZSC, SB])
      have hcomb : (sumMAbsUW c : ℝ) * ((PIHI : ℝ) * 10240 + (SB : ℝ)) / (4 * (ZSC : ℝ) * (SB : ℝ) * (FSC : ℝ)) +
          2 / (FSC : ℝ) ≤ (errPpInt c : ℝ) / (FSC : ℝ) := by
        unfold errPpInt; push_cast
        have hcd' : (sumMAbsUW c : ℝ) * ((PIHI : ℝ) * 10240 + (SB : ℝ)) / (4 * (ZSC : ℝ) * (SB : ℝ)) ≤
            (cdiv (sumMAbsUW c * (PIHI * 10240 + SB)) (4 * ZSC * SB) : ℝ) := by
          simpa [Int.cast_mul, Int.cast_add, Int.cast_ofNat] using hcd
        have heq : (sumMAbsUW c : ℝ) * ((PIHI : ℝ) * 10240 + (SB : ℝ)) / (4 * (ZSC : ℝ) * (SB : ℝ) * (FSC : ℝ)) =
            ((sumMAbsUW c : ℝ) * ((PIHI : ℝ) * 10240 + (SB : ℝ)) / (4 * (ZSC : ℝ) * (SB : ℝ))) / (FSC : ℝ) := by ring
        rw [heq, ← add_div]
        exact div_le_div_of_nonneg_right (by linarith) (by norm_num [FSC])
      have ha1 := abs_add_le
        ((((2 * (c.lam2 : ℝ) * (numX : ℝ) * 10000 / 512) -
          (((2 * c.lam2 * numX * 10000) / 512 : ℤ) : ℝ)) / (FSC : ℝ)) +
         ((((PILO : ℝ) * (trigPp : ℝ) / 400000000000000) -
          (((PILO * trigPp) / 400000000000000 : ℤ) : ℝ)) / (FSC : ℝ)))
        ((1 / 2) * ∑ i : Fin 12,
          ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
            (-uReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2) +
              wReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * mX / 2))) -
          ((PILO : ℝ) * (trigPp : ℝ)) / (400000000000000 * (FSC : ℝ)))
      have ha2 := abs_add_le
        (((2 * (c.lam2 : ℝ) * (numX : ℝ) * 10000 / 512) -
          (((2 * c.lam2 * numX * 10000) / 512 : ℤ) : ℝ)) / (FSC : ℝ))
        ((((PILO : ℝ) * (trigPp : ℝ) / 400000000000000) -
          (((PILO * trigPp) / 400000000000000 : ℤ) : ℝ)) / (FSC : ℝ))
      have h2f : 1 / (FSC : ℝ) + 1 / (FSC : ℝ) = 2 / (FSC : ℝ) := by ring
      linarith
    -- Apply Taylor bound!
    have htay := integral_max_neg_le_taylor (m := mX) (h := 1 / 512)
      (a0 := (pInt : ℝ) / (FSC : ℝ)) (b0 := (ppInt : ℝ) / (FSC : ℝ))
      (e0 := (errPInt c : ℝ) / (FSC : ℝ)) (e1 := (errPpInt c : ℝ) / (FSC : ℝ))
      (L2 := (Lp2Int c : ℝ) / (FSC : ℝ))
      (by norm_num) hLp2_nn (PCert_continuous c) hP''c
      (fun x _ => hP_deriv x) (fun x _ => hP'_deriv x) (fun x _ => hP''b x) ha_err hb_err
    -- Relate linMaxInt to stepDInt c j
    have hlin : linMaxInt (-(pInt : ℝ) / (FSC : ℝ)) |(ppInt : ℝ) / (FSC : ℝ)| (1 / 512) ≤
        (stepDInt c j : ℝ) / (512 ^ 2 * (FSC : ℝ)) := by
      have hfold : (List.range 12).foldl (fun (acc : ℤ × ℤ) i =>
          let m : ℤ := (i + 1 : ℕ)
          let kx : ℤ := m * (2 * numX)
          let cv := cosInt kx
          let sv := sinInt kx
          let ui := c.u.getD i 0
          let wi := c.w.getD i 0
          (acc.1 + ui * cv + wi * sv, acc.2 + m * (-ui * sv + wi * cv))) (0, 0) = (trigP, trigPp) := by
        simpa [trigP, trigPp, add_assoc] using foldl_range_12_prod
          (fun i => c.u.getD i 0 * cosInt (((i + 1 : ℕ) : ℤ) * (2 * numX)) +
            c.w.getD i 0 * sinInt (((i + 1 : ℕ) : ℤ) * (2 * numX)))
          (fun i => ((i + 1 : ℕ) : ℤ) * (-c.u.getD i 0 * sinInt (((i + 1 : ℕ) : ℤ) * (2 * numX)) +
            c.w.getD i 0 * cosInt (((i + 1 : ℕ) : ℤ) * (2 * numX))))
      have hstep : stepDInt c j =
          if 512 * (-pInt) ≤ -|ppInt| then 0
          else if |ppInt| ≤ 512 * (-pInt) then 2 * (512 * (-pInt))
          else cdiv ((512 * (-pInt) + |ppInt|) * (512 * (-pInt) + |ppInt|)) (2 * |ppInt|) := by
        unfold stepDInt; dsimp only; rw [hfold]
      rw [hstep]
      unfold linMaxInt
      rw [abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC)]
      have hFSC : (0 : ℝ) < (FSC : ℝ) := by norm_num [FSC]
      have hc1 : (-(pInt : ℝ) / (FSC : ℝ) ≤ -(|(ppInt : ℝ)| / (FSC : ℝ)) * (1 / 512)) ↔
          (512 * (-pInt) ≤ -|ppInt|) := by
        constructor <;> intro h
        · have : (512 * (-pInt) : ℝ) ≤ (-|ppInt| : ℝ) := by
            have h' := mul_le_mul_of_nonneg_right h (mul_nonneg (by norm_num : (0 : ℝ) ≤ 512) hFSC.le)
            field_simp at h'; push_cast; linarith
          exact_mod_cast this
        · have hR : (512 * (-pInt) : ℝ) ≤ (-|ppInt| : ℝ) := by exact_mod_cast h
          push_cast at hR
          rw [show -(|(ppInt : ℝ)| / (FSC : ℝ)) * (1 / 512) = (-|(ppInt : ℝ)| / 512) / (FSC : ℝ) by ring]
          exact div_le_div_of_nonneg_right (by linarith) hFSC.le
      have hc2 : (|(ppInt : ℝ)| / (FSC : ℝ) * (1 / 512) ≤ -(pInt : ℝ) / (FSC : ℝ)) ↔
          (|ppInt| ≤ 512 * (-pInt)) := by
        constructor <;> intro h
        · have : (|ppInt| : ℝ) ≤ (512 * (-pInt) : ℝ) := by
            have h' := mul_le_mul_of_nonneg_right h (mul_nonneg (by norm_num : (0 : ℝ) ≤ 512) hFSC.le)
            field_simp at h'; linarith
          exact_mod_cast this
        · have hR : (|ppInt| : ℝ) ≤ (512 * (-pInt) : ℝ) := by exact_mod_cast h
          rw [show |(ppInt : ℝ)| / (FSC : ℝ) * (1 / 512) = (|(ppInt : ℝ)| / 512) / (FSC : ℝ) by ring]
          exact div_le_div_of_nonneg_right (by linarith) hFSC.le
      by_cases h1 : 512 * (-pInt) ≤ -|ppInt|
      · rw [if_pos (hc1.mpr h1), if_pos h1]; simp
      · rw [if_neg (mt hc1.mp h1), if_neg h1]
        by_cases h2 : |ppInt| ≤ 512 * (-pInt)
        · rw [if_pos (hc2.mpr h2), if_pos h2]; push_cast; ring_nf; rfl
        · rw [if_neg (mt hc2.mp h2), if_neg h2]
          have hbpos : (0 : ℤ) < 2 * |ppInt| := by
            have : 0 ≤ |ppInt| := abs_nonneg ppInt
            omega
          have hcd := le_cdiv_real ((512 * (-pInt) + |ppInt|) * (512 * (-pInt) + |ppInt|)) (2 * |ppInt|) hbpos
          have hbR : (0 : ℝ) < |(ppInt : ℝ)| := by
            have : (0 : ℤ) < |ppInt| := by omega
            exact_mod_cast this
          have hEq : (-(pInt : ℝ) / (FSC : ℝ) + |(ppInt : ℝ)| / (FSC : ℝ) * (1 / 512)) ^ 2 /
              (2 * (|(ppInt : ℝ)| / (FSC : ℝ))) =
              (((512 * (-pInt) + |ppInt|) * (512 * (-pInt) + |ppInt|) : ℤ) : ℝ) /
              ((2 * |ppInt| : ℤ) : ℝ) / (512 ^ 2 * (FSC : ℝ)) := by
            push_cast; field_simp
          rw [hEq]
          exact div_le_div_of_nonneg_right hcd (mul_nonneg (by norm_num) (by norm_num [FSC]))
    rw [← neg_div] at htay
    linarith [htay, hlin]
  -- Sum over j ∈ range 1024 and compare with DubQ c / QSC
  have hsum := Finset.sum_le_sum hterm_j
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_ofNat, ← Finset.sum_div] at hsum
  have hcd := le_cdiv_real
    ((3 * sumDIntLoop c 1024 0 + 3 * 4 * 512 * 512 * errPInt c + 3 * 4 * 512 * errPpInt c +
      2 * Lp2Int c) * QSC) (3 * 512 * 512 * FSC) (by norm_num [FSC])
  refine hsum.trans ?_
  unfold DubQ; dsimp only
  have hloop : (sumDIntLoop c 1024 0 : ℝ) = ∑ j ∈ Finset.range 1024, (stepDInt c j : ℝ) := by
    rw [sumDIntLoop_eq, zero_add]; push_cast; rfl
  have hEq : (∑ j ∈ Finset.range 1024, (stepDInt c j : ℝ)) / (512 ^ 2 * (FSC : ℝ)) +
      1024 * (2 * ((errPInt c : ℝ) / (FSC : ℝ)) * (1 / 512)) +
      1024 * (2 * ((errPpInt c : ℝ) / (FSC : ℝ)) * (1 / 512) ^ 2) +
      1024 * ((1 / 3) * ((Lp2Int c : ℝ) / (FSC : ℝ)) * (1 / 512) ^ 3) =
      (((3 * sumDIntLoop c 1024 0 + 3 * 4 * 512 * 512 * errPInt c +
        3 * 4 * 512 * errPpInt c + 2 * Lp2Int c) * QSC : ℤ) : ℝ) /
      ((3 * 512 * 512 * FSC : ℤ) : ℝ) / (QSC : ℝ) := by
    push_cast; rw [hloop]; norm_num [QSC, FSC]; ring
  rw [hEq]
  exact div_le_div_of_nonneg_right hcd (by norm_num [QSC])

private lemma sVal_odd_eq (m : ℕ) (hm : m % 2 = 1) :
    sVal m = (if ((m - 1) / 2) % 2 = 0 then (1 : ℝ) else -1) / (π * (m : ℝ)) := by
  unfold sVal
  congr 1
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
  have h1 : (2 * k + 1 - 1) / 2 = k := by omega
  rw [h1]
  have h2 : π * ((2 * k + 1 : ℕ) : ℝ) / 2 = π / 2 + (k : ℝ) * π := by push_cast; ring
  rw [h2, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two]
  rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · have : (r + r) % 2 = 0 := by omega
    rw [if_pos this, ← two_mul, pow_mul]; norm_num
  · have : (2 * r + 1) % 2 ≠ 0 := by omega
    rw [if_neg this, pow_add, pow_mul]; norm_num

private lemma sVal_even_eq (m : ℕ) (hm : m % 2 = 0) : sVal m = 0 := by
  unfold sVal
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
  have : π * ((2 * k : ℕ) : ℝ) / 2 = (k : ℝ) * π := by push_cast; ring
  rw [this, Real.sin_nat_mul_pi, zero_div]

private lemma asReal_err (c : CertData) (i : Fin 12) :
    |asReal c i - (asInt c i : ℝ) / (FSC : ℝ)| ≤ (asErrInt c i : ℝ) / (FSC : ℝ) := by
  unfold asReal asInt asErrInt
  set m := i.1 + 1
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  by_cases hodd : m % 2 = 1
  · rw [if_pos hodd, if_pos hodd, sVal_odd_eq m hodd]
    set sgn : ℤ := if ((m - 1) / 2) % 2 = 0 then 1 else -1
    have hsgn_cast : (if ((m - 1) / 2) % 2 = 0 then (1 : ℝ) else -1) = (sgn : ℝ) := by
      simp only [sgn]; split_ifs <;> norm_num
    rw [hsgn_cast]
    have hbase : (if i.1 = 1 then -(c.mu : ℝ) / (ZSC : ℝ) else -qReal c i / 2) =
        ((if i.1 = 1 then -c.mu * 10000 else -(c.q.getD i.1 0) * 5000 : ℤ) : ℝ) / (FSC : ℝ) := by
      split_ifs <;> simp [qReal, getI, ZSC, FSC] <;> ring
    rw [hbase]
    have hpi := pi_bounds
    have hpi_diff : |1 / π - 100000000 / (PILO : ℝ)| ≤ 100000000 / ((PILO : ℝ) * (PILO : ℝ)) := by
      have h1 : 0 < π := Real.pi_pos
      have h2 : (0 : ℝ) < (PILO : ℝ) := by norm_num [PILO]
      have hEq : 1 / π - 100000000 / (PILO : ℝ) = ((PILO : ℝ) - 100000000 * π) / (π * (PILO : ℝ)) := by
        field_simp
      rw [hEq, abs_div, abs_of_pos (mul_pos h1 h2)]
      have hnum : |(PILO : ℝ) - 100000000 * π| ≤ 1 := by
        rw [abs_le]; constructor <;> norm_num [PILO, PIHI] at hpi ⊢ <;> linarith
      have hden : (PILO : ℝ) * (PILO : ℝ) / 100000000 ≤ π * (PILO : ℝ) := by
        have := hpi.1; nlinarith
      rw [div_le_div_iff₀ (mul_pos h1 h2) (mul_pos h2 h2)]
      nlinarith
    have hd := ediv_real_err (-2 * c.w.getD i.1 0 * sgn * 1000000000000) (PILO * (m : ℤ))
      (mul_pos (by norm_num [PILO]) (by omega))
    have hEq : ((if i.1 = 1 then -c.mu * 10000 else -(c.q.getD i.1 0) * 5000 : ℤ) : ℝ) / (FSC : ℝ) -
        2 * wReal c i * ((sgn : ℝ) / (π * (m : ℝ))) -
        (((if i.1 = 1 then -c.mu * 10000 else -(c.q.getD i.1 0) * 5000 : ℤ) +
          (-2 * c.w.getD i.1 0 * sgn * 1000000000000) / (PILO * (m : ℤ)) : ℤ) : ℝ) / (FSC : ℝ) =
        (-2 * (c.w.getD i.1 0 : ℝ) * (sgn : ℝ) / ((ZSC : ℝ) * (m : ℝ))) * (1 / π - 100000000 / (PILO : ℝ)) +
        (((-2 * (c.w.getD i.1 0 : ℝ) * (sgn : ℝ) * 1000000000000 / ((PILO : ℝ) * (m : ℝ))) -
          (((-2 * c.w.getD i.1 0 * sgn * 1000000000000) / (PILO * (m : ℤ)) : ℤ) : ℝ)) / (FSC : ℝ)) := by
      have hpi0 : π ≠ 0 := Real.pi_ne_zero
      split_ifs <;> (simp only [wReal, getI]; push_cast; norm_num [ZSC, FSC, PILO]; field_simp; ring)
    rw [hEq]
    have hsgn_abs : |(sgn : ℝ)| = 1 := by simp only [sgn]; split_ifs <;> norm_num
    have h1 : |(-2 * (c.w.getD i.1 0 : ℝ) * (sgn : ℝ) / ((ZSC : ℝ) * (m : ℝ))) *
        (1 / π - 100000000 / (PILO : ℝ))| ≤
        (2 * |(c.w.getD i.1 0 : ℝ)| * 10000000000000000 / ((ZSC : ℝ) * (m : ℝ) * (PILO : ℝ) * (PILO : ℝ))) / (FSC : ℝ) := by
      rw [abs_mul, abs_div, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        hsgn_abs, mul_one, abs_of_pos (mul_pos (by norm_num [ZSC]) hm_pos)]
      have hZSC : (0 : ℝ) < (ZSC : ℝ) := by norm_num [ZSC]
      calc 2 * |(c.w.getD i.1 0 : ℝ)| / ((ZSC : ℝ) * (m : ℝ)) * |1 / π - 100000000 / (PILO : ℝ)|
          ≤ 2 * |(c.w.getD i.1 0 : ℝ)| / ((ZSC : ℝ) * (m : ℝ)) * (100000000 / ((PILO : ℝ) * (PILO : ℝ))) := by gcongr
        _ = _ := by norm_num [FSC]; ring
    have h2 : |(((-2 * (c.w.getD i.1 0 : ℝ) * (sgn : ℝ) * 1000000000000 / ((PILO : ℝ) * (m : ℝ))) -
        (((-2 * c.w.getD i.1 0 * sgn * 1000000000000) / (PILO * (m : ℤ)) : ℤ) : ℝ)) / (FSC : ℝ))| ≤
        1 / (FSC : ℝ) := by
      rw [abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC), abs_sub_comm]
      exact div_le_div_of_nonneg_right (by simpa [Int.cast_mul, Int.cast_neg, Int.cast_ofNat] using hd) (by norm_num [FSC])
    have hcd := le_cdiv_real (2 * |c.w.getD i.1 0| * 10000000000000000) (ZSC * (m : ℤ) * PILO * PILO)
      (mul_pos (mul_pos (mul_pos (by norm_num [ZSC]) (by omega)) (by norm_num [PILO])) (by norm_num [PILO]))
    calc |_ + _| ≤ |_| + |_| := abs_add_le _ _
      _ ≤ _ := add_le_add h1 h2
      _ ≤ ((cdiv (2 * |c.w.getD i.1 0| * 10000000000000000) (ZSC * (m : ℤ) * PILO * PILO) + 1 : ℤ) : ℝ) / (FSC : ℝ) := by
          push_cast; rw [← add_div]
          exact div_le_div_of_nonneg_right (by
            have hcd' : 2 * |(c.w.getD i.1 0 : ℝ)| * 10000000000000000 / ((ZSC : ℝ) * (m : ℝ) * (PILO : ℝ) * (PILO : ℝ)) ≤
                (cdiv (2 * |c.w.getD i.1 0| * 10000000000000000) (ZSC * (m : ℤ) * PILO * PILO) : ℝ) := by
              simpa [Int.cast_mul, Int.cast_abs, Int.cast_ofNat] using hcd
            linarith) (by norm_num [FSC])
  · have heven : m % 2 = 0 := by omega
    rw [if_neg hodd, if_neg hodd, sVal_even_eq m heven, mul_zero, sub_zero]
    have hbase : (if i.1 = 1 then -(c.mu : ℝ) / (ZSC : ℝ) else -qReal c i / 2) =
        ((if i.1 = 1 then -c.mu * 10000 else -(c.q.getD i.1 0) * 5000 : ℤ) : ℝ) / (FSC : ℝ) := by
      split_ifs <;> simp [qReal, getI, ZSC, FSC] <;> ring
    rw [hbase, sub_self, abs_zero]; simp

private lemma acReal_eq (c : CertData) (i : Fin 12) :
    acReal c i = (acInt c i.1 : ℝ) / (FSC : ℝ) := by
  unfold acReal acInt; split_ifs <;> simp [rReal, getI, ZSC, FSC] <;> ring

private lemma L1ubQ_sound (c : CertData) :
    (1 / 2) * ∫ t in (-1 : ℝ)..1, |PsiCert c t| ≤ (L1ubQ c : ℝ) / (QSC : ℝ) := by
  let Psi' : ℝ → ℝ := fun t =>
    -2 * ((c.lam1 - c.eta : ℤ) : ℝ) / (ZSC : ℝ) +
      ∑ i : Fin 12,
        ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
          (-acReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) +
            asReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2)))
  let Psi'' : ℝ → ℝ := fun t =>
    ∑ i : Fin 12,
      ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 *
        (-acReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) -
          asReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2)))
  have hPsi_deriv : ∀ t : ℝ, HasDerivAt (PsiCert c) (Psi' t) t := fun t => by
    unfold PsiCert; simp only [Psi']
    have hlin : HasDerivAt (fun y => (-2 * ((c.lam1 - c.eta : ℤ) : ℝ) / (ZSC : ℝ)) * y - (c.kappa : ℝ) / (ZSC : ℝ))
        (-2 * ((c.lam1 - c.eta : ℤ) : ℝ) / (ZSC : ℝ)) t := by
      simpa only [mul_one] using ((hasDerivAt_id' t).const_mul (-2 * ((c.lam1 - c.eta : ℤ) : ℝ) / (ZSC : ℝ))).sub_const ((c.kappa : ℝ) / (ZSC : ℝ))
    have htrig : HasDerivAt (fun y => ∑ i : Fin 12,
        (acReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * y / 2) +
         asReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * y / 2)))
        (∑ i : Fin 12,
          ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
            (-acReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) +
              asReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2)))) t := by
      refine HasDerivAt.fun_sum fun i _ => ?_
      have ha : HasDerivAt (fun y => π * ((i.1 + 1 : ℕ) : ℝ) * y / 2) (π * ((i.1 + 1 : ℕ) : ℝ) / 2) t := by
        have h1 := ((hasDerivAt_id t).const_mul (π * ((i.1 + 1 : ℕ) : ℝ))).div_const 2
        rw [show π * ((i.1 + 1 : ℕ) : ℝ) / 2 = π * ((i.1 + 1 : ℕ) : ℝ) * 1 / 2 by ring]
        exact h1
      have hc := ((Real.hasDerivAt_cos _).comp t ha).const_mul (acReal c i)
      have hs := ((Real.hasDerivAt_sin _).comp t ha).const_mul (asReal c i)
      rw [show (π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
        (-acReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) +
          asReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2)) =
        acReal c i * (-Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) * (π * ((i.1 + 1 : ℕ) : ℝ) / 2)) +
        asReal c i * (Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) * (π * ((i.1 + 1 : ℕ) : ℝ) / 2)) by ring]
      exact hc.add hs
    exact hlin.add htrig
  have hPsi'_deriv : ∀ t : ℝ, HasDerivAt Psi' (Psi'' t) t := fun t => by
    simp only [Psi', Psi'']
    have htrig : HasDerivAt (fun y => ∑ i : Fin 12,
        ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
          (-acReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * y / 2) +
            asReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * y / 2))))
        (∑ i : Fin 12,
          ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 *
            (-acReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) -
              asReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2)))) t := by
      refine HasDerivAt.fun_sum fun i _ => ?_
      have ha : HasDerivAt (fun y => π * ((i.1 + 1 : ℕ) : ℝ) * y / 2) (π * ((i.1 + 1 : ℕ) : ℝ) / 2) t := by
        have h1 := ((hasDerivAt_id t).const_mul (π * ((i.1 + 1 : ℕ) : ℝ))).div_const 2
        rw [show π * ((i.1 + 1 : ℕ) : ℝ) / 2 = π * ((i.1 + 1 : ℕ) : ℝ) * 1 / 2 by ring]
        exact h1
      have hs := ((Real.hasDerivAt_sin _).comp t ha).const_mul (-acReal c i)
      have hc := ((Real.hasDerivAt_cos _).comp t ha).const_mul (asReal c i)
      rw [show (π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 *
        (-acReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) -
          asReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2)) =
        (π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
          (-acReal c i * (Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) * (π * ((i.1 + 1 : ℕ) : ℝ) / 2)) +
           asReal c i * (-Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) * (π * ((i.1 + 1 : ℕ) : ℝ) / 2))) by ring]
      exact (hs.add hc).const_mul (π * ((i.1 + 1 : ℕ) : ℝ) / 2)
    have h1 := (hasDerivAt_const t (-2 * ((c.lam1 - c.eta : ℤ) : ℝ) / (ZSC : ℝ))).add htrig
    rw [zero_add] at h1
    exact h1
  have hPsi''c : Continuous Psi'' := by
    refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    exact (continuous_const.mul (Real.continuous_cos.comp ((continuous_const.mul continuous_id).div_const 2))).sub
      (continuous_const.mul (Real.continuous_sin.comp ((continuous_const.mul continuous_id).div_const 2)))
  have hpi := pi_bounds
  have hpi_pos : 0 < π := Real.pi_pos
  have has_abs : ∀ i : Fin 12, |asReal c i| ≤ (|(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) / (FSC : ℝ) := fun i => by
    have he := asReal_err c i
    have h1 := abs_sub_abs_le_abs_sub (asReal c i) ((asInt c i.1 : ℝ) / (FSC : ℝ))
    rw [abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC)] at h1
    rw [add_div]; linarith
  have hac_abs : ∀ i : Fin 12, |acReal c i| = |(acInt c i.1 : ℝ)| / (FSC : ℝ) := fun i => by
    rw [acReal_eq, abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC)]
  -- Bound |Psi'' t| ≤ Lq2Int c / FSC
  have hPsi''b : ∀ t : ℝ, |Psi'' t| ≤ (Lq2Int c : ℝ) / (FSC : ℝ) := fun t => by
    simp only [Psi'']
    set S2 : ℤ := (List.range 12).foldl (fun acc i =>
      acc + ((i + 1 : ℕ) : ℤ) ^ 2 * (|acInt c i| + |asInt c i| + asErrInt c i)) 0
    have hS2_eq : (S2 : ℝ) = ∑ i : Fin 12,
        ((i.1 + 1 : ℕ) : ℝ) ^ 2 * (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) := by
      simp only [S2]; rw [foldl_range_12]; push_cast; rfl
    have hsum : |∑ i : Fin 12,
        (π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 *
          (-acReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) -
            asReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2))| ≤
        (π ^ 2 / (4 * (FSC : ℝ))) * (S2 : ℝ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ i : Fin 12,
          |(π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 *
            (-acReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) -
              asReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2))| ≤
          (π ^ 2 / (4 * (FSC : ℝ))) *
            (((i.1 + 1 : ℕ) : ℝ) ^ 2 * (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ))) := fun i => by
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hcs : |-acReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) -
            asReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2)| ≤
            (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) / (FSC : ℝ) := by
          calc |-acReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) -
                asReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2)|
              ≤ |-acReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2)| +
                |asReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2)| := abs_sub _ _
            _ = |acReal c i| * |Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2)| +
                |asReal c i| * |Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2)| := by rw [abs_mul, abs_neg, abs_mul]
            _ ≤ |acReal c i| * 1 + |asReal c i| * 1 := by
                gcongr; exact Real.abs_cos_le_one _; exact Real.abs_sin_le_one _
            _ ≤ (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) / (FSC : ℝ) := by
                rw [mul_one, mul_one, hac_abs]
                have hadd : (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) / (FSC : ℝ) =
                    |(acInt c i.1 : ℝ)| / (FSC : ℝ) + (|(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) / (FSC : ℝ) := by ring
                linarith [has_abs i]
        calc (π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 * |-acReal c i * Real.cos (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2) -
                asReal c i * Real.sin (π * ((i.1 + 1 : ℕ) : ℝ) * t / 2)|
            ≤ (π * ((i.1 + 1 : ℕ) : ℝ) / 2) ^ 2 *
                ((|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) / (FSC : ℝ)) :=
              mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
          _ = (π ^ 2 / (4 * (FSC : ℝ))) *
                (((i.1 + 1 : ℕ) : ℝ) ^ 2 * (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ))) := by ring
      refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, hS2_eq]
    have hS2_nn : (0 : ℝ) ≤ (S2 : ℝ) := by
      rw [hS2_eq]; refine Finset.sum_nonneg fun i _ => ?_
      have : (0 : ℝ) ≤ (asErrInt c i.1 : ℝ) := by
        unfold asErrInt; dsimp only; split_ifs
        · exact_mod_cast (by
            have : 0 ≤ cdiv (2 * |c.w.getD i.1 0| * 10000000000000000) (ZSC * ((i.1 + 1 : ℕ) : ℤ) * PILO * PILO) := by
              have hden : (0 : ℤ) < ZSC * ((i.1 + 1 : ℕ) : ℤ) * PILO * PILO :=
                mul_pos (mul_pos (mul_pos (by norm_num [ZSC]) (by omega)) (by norm_num [PILO])) (by norm_num [PILO])
              have h := le_cdiv_real (2 * |c.w.getD i.1 0| * 10000000000000000) (ZSC * ((i.1 + 1 : ℕ) : ℤ) * PILO * PILO) hden
              have h0 : (0 : ℝ) ≤ ((2 * |c.w.getD i.1 0| * 10000000000000000 : ℤ) : ℝ) / ((ZSC * ((i.1 + 1 : ℕ) : ℤ) * PILO * PILO : ℤ) : ℝ) :=
                div_nonneg (by positivity) (by exact_mod_cast hden.le)
              exact_mod_cast h0.trans h
            omega : (0 : ℤ) ≤ _)
        · norm_num
      positivity
    have hpi2 : π ^ 2 ≤ ((PIHI : ℝ) / 100000000) ^ 2 := by nlinarith [hpi.2, hpi_pos]
    have hcd := le_cdiv_real (S2 * PIHI * PIHI) 40000000000000000 (by norm_num)
    have hFSC4 : (0 : ℝ) ≤ 4 * (FSC : ℝ) := by norm_num [FSC]
    calc |∑ i : Fin 12, _| ≤ (π ^ 2 / (4 * (FSC : ℝ))) * (S2 : ℝ) := hsum
      _ ≤ (((PIHI : ℝ) / 100000000) ^ 2 / (4 * (FSC : ℝ))) * (S2 : ℝ) := by gcongr
      _ = ((S2 : ℝ) * (PIHI : ℝ) * (PIHI : ℝ) / 40000000000000000) / (FSC : ℝ) := by ring
      _ ≤ (Lq2Int c : ℝ) / (FSC : ℝ) := by
          unfold Lq2Int; dsimp only
          exact div_le_div_of_nonneg_right (by simpa [S2, Int.cast_mul, Int.cast_ofNat] using hcd) (by norm_num [FSC])
  have hLq2_nn : (0 : ℝ) ≤ (Lq2Int c : ℝ) / (FSC : ℝ) := le_trans (abs_nonneg (Psi'' 0)) (hPsi''b 0)
  -- Split [-1, 1] into 1024 intervals of width 2/1024 = 1/512 (half-width ht = 1/1024)
  have hsplit : ∫ t in (-1 : ℝ)..1, |PsiCert c t| =
      ∑ j ∈ Finset.range 1024,
        ∫ t in ((-1 : ℝ) + 2 * (j : ℝ) / 1024)..((-1 : ℝ) + 2 * ((j + 1 : ℕ) : ℝ) / 1024),
          |PsiCert c t| := by
    have hcont : Continuous (fun t => |PsiCert c t|) := continuous_abs.comp (PsiCert_continuous c)
    have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (n := 1024)
      (a := fun j : ℕ => (-1 : ℝ) + 2 * (j : ℝ) / 1024)
      (f := fun t => |PsiCert c t|) (fun j _ => hcont.intervalIntegrable (μ := volume) _ _)
    rw [hsum]
    rw [show ((-1 : ℝ) + 2 * ((0 : ℕ) : ℝ) / 1024) = -1 by norm_num,
        show ((-1 : ℝ) + 2 * ((1024 : ℕ) : ℝ) / 1024) = 1 by norm_num]
  rw [hsplit]
  set acL := (List.range 12).map (acInt c)
  set asL := (List.range 12).map (asInt c)
  have hacL : ∀ i : Fin 12, acL.getD i.1 0 = acInt c i.1 := fun i => by
    simp [acL, List.getD_eq_getElem?_getD, i.2]
  have hasL : ∀ i : Fin 12, asL.getD i.1 0 = asInt c i.1 := fun i => by
    simp [asL, List.getD_eq_getElem?_getD, i.2]
  have hterm_j : ∀ j ∈ Finset.range 1024,
      ∫ t in ((-1 : ℝ) + 2 * (j : ℝ) / 1024)..((-1 : ℝ) + 2 * ((j + 1 : ℕ) : ℝ) / 1024),
        |PsiCert c t| ≤
      (stepL1Int c acL asL j : ℝ) / (1024 ^ 2 * (FSC : ℝ)) +
      2 * ((errPsiInt c : ℝ) / (FSC : ℝ)) * (1 / 1024) +
      2 * ((errPsipInt c : ℝ) / (FSC : ℝ)) * (1 / 1024) ^ 2 +
      (1 / 3) * ((Lq2Int c : ℝ) / (FSC : ℝ)) * (1 / 1024) ^ 3 := by
    intro j _
    set numT : ℤ := 2 * (j : ℤ) - 1023
    set mT : ℝ := (numT : ℝ) / 1024
    have hlo : (-1 : ℝ) + 2 * (j : ℝ) / 1024 = mT - 1 / 1024 := by simp only [mT, numT]; push_cast; ring
    have hhi : (-1 : ℝ) + 2 * ((j + 1 : ℕ) : ℝ) / 1024 = mT + 1 / 1024 := by simp only [mT, numT]; push_cast; ring
    rw [hlo, hhi]
    set ctInt : ℤ := -2 * (c.lam1 - c.eta) * 10000
    set trigQ : ℤ := ∑ i : Fin 12,
      (acInt c i.1 * cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) +
       asInt c i.1 * sinInt (((i.1 + 1 : ℕ) : ℤ) * numT))
    set trigQp : ℤ := ∑ i : Fin 12,
      (((i.1 + 1 : ℕ) : ℤ) * (-acInt c i.1 * sinInt (((i.1 + 1 : ℕ) : ℤ) * numT) +
        asInt c i.1 * cosInt (((i.1 + 1 : ℕ) : ℤ) * numT)))
    set qInt : ℤ := (ctInt * numT) / 1024 - c.kappa * 10000 + trigQ / SB
    set qpInt : ℤ := ctInt + (PILO * trigQp) / 2000000000000000000
    have hang : ∀ i : Fin 12,
        π * ((i.1 + 1 : ℕ) : ℝ) * mT / 2 = ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) : ℝ) * θ₀ := fun i => by
      simp only [mT, θ₀]; push_cast; ring
    have ha_err : |PsiCert c mT - (qInt : ℝ) / (FSC : ℝ)| ≤ (errPsiInt c : ℝ) / (FSC : ℝ) := by
      have hd1 := ediv_real_err (ctInt * numT) 1024 (by norm_num)
      have hd2 := ediv_real_err trigQ SB (by norm_num [SB])
      have hdecomp : PsiCert c mT - (qInt : ℝ) / (FSC : ℝ) =
          (((ctInt : ℝ) * (numT : ℝ) / 1024 - (((ctInt * numT) / 1024 : ℤ) : ℝ)) / (FSC : ℝ)) +
          (((trigQ : ℝ) / (SB : ℝ) - ((trigQ / SB : ℤ) : ℝ)) / (FSC : ℝ)) +
          ∑ i : Fin 12,
            ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) +
             ((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
               (cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ)) +
             ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
               (sinInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ))) := by
        unfold PsiCert; simp only [qInt, ctInt, trigQ, mT, hang, acReal_eq]; push_cast
        have hsum_eq : ∑ i : Fin 12,
            ((acInt c i.1 : ℝ) / (FSC : ℝ) * Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) +
              asReal c i * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀)) -
            (∑ i : Fin 12,
              ((acInt c i.1 : ℝ) * (cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) +
               (asInt c i.1 : ℝ) * (sinInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ))) / (SB : ℝ) / (FSC : ℝ) =
            ∑ i : Fin 12,
              ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) +
               ((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
                 (cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ)) +
               ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
                 (sinInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ))) := by
          rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        push_cast at hsum_eq
        rw [← hsum_eq]; norm_num [ZSC, FSC, SB]; ring
      rw [hdecomp]
      have h3 : |(((ctInt : ℝ) * (numT : ℝ) / 1024 - (((ctInt * numT) / 1024 : ℤ) : ℝ)) / (FSC : ℝ))| ≤ 1 / (FSC : ℝ) := by
        rw [abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC), abs_sub_comm]
        exact div_le_div_of_nonneg_right (by simpa [Int.cast_mul, Int.cast_ofNat] using hd1) (by norm_num [FSC])
      have h4 : |(((trigQ : ℝ) / (SB : ℝ) - ((trigQ / SB : ℤ) : ℝ)) / (FSC : ℝ))| ≤ 1 / (FSC : ℝ) := by
        rw [abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC), abs_sub_comm]
        exact div_le_div_of_nonneg_right hd2 (by norm_num [FSC])
      set S_serr : ℤ := (List.range 12).foldl (fun acc i => acc + asErrInt c i) 0
      set S_acas : ℤ := (List.range 12).foldl (fun acc i => acc + |acInt c i| + |asInt c i| + asErrInt c i) 0
      have hsum_bd : |∑ i : Fin 12,
          ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) +
           ((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
             (cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ)) +
           ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
             (sinInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ)))| ≤
          ((S_serr : ℝ) + ((S_acas : ℝ) * 10240 / (SB : ℝ))) / (FSC : ℝ) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have hterm : ∀ i : Fin 12,
            |(asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) +
             ((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
               (cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ)) +
             ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
               (sinInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ))| ≤
            ((asErrInt c i.1 : ℝ) + (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) * (10240 / (SB : ℝ))) / (FSC : ℝ) := fun i => by
          have he := cosInt_sinInt_err (((i.1 + 1 : ℕ) : ℤ) * numT)
          have hse := asReal_err c i
          have hse_nn : (0 : ℝ) ≤ (asErrInt c i.1 : ℝ) := by
            have := le_trans (abs_nonneg _) hse
            exact (div_nonneg_iff.mp this).resolve_right (by norm_num [FSC]) |>.1
          have ha1 := abs_add_le
            ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) +
             ((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
               (cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ)))
            (((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
              (sinInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ)))
          have ha2 := abs_add_le
            ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀))
            (((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
              (cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ)))
          rw [abs_mul, abs_mul, abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC)] at ha2
          rw [abs_mul, abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC)] at ha1
          have ht1 : |asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)| * |Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀)| ≤
              (asErrInt c i.1 : ℝ) / (FSC : ℝ) := by
            have := mul_le_mul hse (Real.abs_sin_le_one ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀))
              (abs_nonneg (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀)))
              (div_nonneg hse_nn (by norm_num [FSC]))
            linarith
          have ht2 := mul_le_mul_of_nonneg_left he.1 (div_nonneg (abs_nonneg (acInt c i.1 : ℝ)) (by norm_num [FSC] : (0 : ℝ) ≤ FSC))
          have ht3 := mul_le_mul_of_nonneg_left he.2 (div_nonneg (abs_nonneg (asInt c i.1 : ℝ)) (by norm_num [FSC] : (0 : ℝ) ≤ FSC))
          have h0 : 0 ≤ (asErrInt c i.1 : ℝ) * (10240 / (SB : ℝ)) / (FSC : ℝ) :=
            div_nonneg (mul_nonneg hse_nn (by norm_num [SB])) (by norm_num [FSC])
          have hEq : (asErrInt c i.1 : ℝ) / (FSC : ℝ) +
              (|(acInt c i.1 : ℝ)| / (FSC : ℝ)) * (10240 / (SB : ℝ)) +
              (|(asInt c i.1 : ℝ)| / (FSC : ℝ)) * (10240 / (SB : ℝ)) +
              (asErrInt c i.1 : ℝ) * (10240 / (SB : ℝ)) / (FSC : ℝ) =
              ((asErrInt c i.1 : ℝ) + (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) * (10240 / (SB : ℝ))) / (FSC : ℝ) := by ring
          linarith
        refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul]
        have hS1 : (S_serr : ℝ) = ∑ i : Fin 12, (asErrInt c i.1 : ℝ) := by
          simp only [S_serr]; rw [foldl_range_12]; push_cast; rfl
        have hS2 : (S_acas : ℝ) = ∑ i : Fin 12, (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) := by
          simp only [S_acas]; simp only [add_assoc]; rw [foldl_range_12]; push_cast; rfl
        rw [hS1, hS2]; ring
      have hcd := le_cdiv_real (S_acas * 10240) SB (by norm_num [SB])
      have ha1 := abs_add_le
        ((((ctInt : ℝ) * (numT : ℝ) / 1024 - (((ctInt * numT) / 1024 : ℤ) : ℝ)) / (FSC : ℝ)) +
         (((trigQ : ℝ) / (SB : ℝ) - ((trigQ / SB : ℤ) : ℝ)) / (FSC : ℝ)))
        (∑ i : Fin 12,
          ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) +
           ((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
             (cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ)) +
           ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
             (sinInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ))))
      have ha2 := abs_add_le
        (((ctInt : ℝ) * (numT : ℝ) / 1024 - (((ctInt * numT) / 1024 : ℤ) : ℝ)) / (FSC : ℝ))
        (((trigQ : ℝ) / (SB : ℝ) - ((trigQ / SB : ℤ) : ℝ)) / (FSC : ℝ))
      have hfin : 1 / (FSC : ℝ) + 1 / (FSC : ℝ) + ((S_serr : ℝ) + (S_acas : ℝ) * 10240 / (SB : ℝ)) / (FSC : ℝ) ≤
          (errPsiInt c : ℝ) / (FSC : ℝ) := by
        change _ ≤ ((S_serr + cdiv (S_acas * 10240) SB + 3 : ℤ) : ℝ) / (FSC : ℝ)
        push_cast
        have hcd' : (S_acas : ℝ) * 10240 / (SB : ℝ) ≤ (cdiv (S_acas * 10240) SB : ℝ) := by
          simpa [Int.cast_mul, Int.cast_ofNat] using hcd
        rw [show 1 / (FSC : ℝ) + 1 / (FSC : ℝ) + ((S_serr : ℝ) + (S_acas : ℝ) * 10240 / (SB : ℝ)) / (FSC : ℝ) =
          ((S_serr : ℝ) + (S_acas : ℝ) * 10240 / (SB : ℝ) + 2) / (FSC : ℝ) by ring]
        exact div_le_div_of_nonneg_right (by linarith) (by norm_num [FSC])
      linarith
    have hb_err : |Psi' mT - (qpInt : ℝ) / (FSC : ℝ)| ≤ (errPsipInt c : ℝ) / (FSC : ℝ) := by
      have hd1 := ediv_real_err (PILO * trigQp) 2000000000000000000 (by norm_num)
      have hpi_diff : |π - (PILO : ℝ) / 100000000| ≤ 1 / 100000000 := by
        rw [abs_le]; constructor <;> norm_num [PILO, PIHI] at hpi ⊢ <;> linarith
      have hdecomp : Psi' mT - (qpInt : ℝ) / (FSC : ℝ) =
          ((((PILO : ℝ) * (trigQp : ℝ) / 2000000000000000000) -
            (((PILO * trigQp) / 2000000000000000000 : ℤ) : ℝ)) / (FSC : ℝ)) +
          (1 / 2) * ∑ i : Fin 12,
            (((i.1 + 1 : ℕ) : ℝ) *
              (π * ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀)) +
               ((PILO : ℝ) / 100000000) *
                 (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
                    (sinInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ)) +
                  ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
                    (cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ))) +
               (π - (PILO : ℝ) / 100000000) *
                 (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) +
                  ((asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀)))) := by
        simp only [Psi', qpInt, ctInt, trigQp, hang, acReal_eq]; push_cast
        have hsum_eq : ∑ i : Fin 12,
            ((π * ((i.1 + 1 : ℕ) : ℝ) / 2) *
              (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) +
                asReal c i * Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀))) -
            (PILO : ℝ) * (∑ i : Fin 12,
              (((i.1 + 1 : ℕ) : ℝ) *
                (-(acInt c i.1 : ℝ) * (sinInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) +
                 (asInt c i.1 : ℝ) * (cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ)))) / 2000000000000000000 / (FSC : ℝ) =
            (1 / 2) * ∑ i : Fin 12,
              (((i.1 + 1 : ℕ) : ℝ) *
                (π * ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀)) +
                 ((PILO : ℝ) / 100000000) *
                   (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
                      (sinInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ)) +
                    ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
                      (cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ))) +
                 (π - (PILO : ℝ) / 100000000) *
                   (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) +
                    ((asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀)))) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          norm_num [FSC, SB]; ring
        push_cast at hsum_eq
        rw [← hsum_eq]; norm_num [ZSC, FSC]; ring
      rw [hdecomp]
      have h3 : |((((PILO : ℝ) * (trigQp : ℝ) / 2000000000000000000) -
          (((PILO * trigQp) / 2000000000000000000 : ℤ) : ℝ)) / (FSC : ℝ))| ≤ 1 / (FSC : ℝ) := by
        rw [abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC), abs_sub_comm]
        exact div_le_div_of_nonneg_right (by simpa [Int.cast_mul, Int.cast_ofNat] using hd1) (by norm_num [FSC])
      set SM_serr : ℤ := (List.range 12).foldl (fun acc i => acc + ((i + 1 : ℕ) : ℤ) * asErrInt c i) 0
      set SM_acas : ℤ := (List.range 12).foldl (fun acc i =>
        acc + ((i + 1 : ℕ) : ℤ) * (|acInt c i| + |asInt c i| + asErrInt c i)) 0
      have hsum_bd : |(1 / 2) * ∑ i : Fin 12,
          (((i.1 + 1 : ℕ) : ℝ) *
            (π * ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀)) +
             ((PILO : ℝ) / 100000000) *
               (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
                  (sinInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ)) +
                ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
                  (cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ))) +
             (π - (PILO : ℝ) / 100000000) *
               (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) +
                ((asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀))))| ≤
          (((PIHI : ℝ) * (SM_serr : ℝ)) / 200000000 +
           ((SM_acas : ℝ) * ((PIHI : ℝ) * 10240 + (SB : ℝ))) / (200000000 * (SB : ℝ))) / (FSC : ℝ) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)).trans ?_
        have hterm : ∀ i : Fin 12,
            |((i.1 + 1 : ℕ) : ℝ) *
              (π * ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀)) +
               ((PILO : ℝ) / 100000000) *
                 (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
                    (sinInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ)) +
                  ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) -
                    (cosInt (((i.1 + 1 : ℕ) : ℤ) * numT) : ℝ) / (SB : ℝ))) +
               (π - (PILO : ℝ) / 100000000) *
                 (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀) +
                  ((asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((((i.1 + 1 : ℕ) : ℤ) * numT : ℤ) * θ₀)))| ≤
            (((i.1 + 1 : ℕ) : ℝ) * (asErrInt c i.1 : ℝ) * ((PIHI : ℝ) / 100000000) +
             ((i.1 + 1 : ℕ) : ℝ) * (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) *
               (((PIHI : ℝ) * 10240 + (SB : ℝ)) / (100000000 * (SB : ℝ)))) / (FSC : ℝ) := fun i => by
          set kti : ℤ := ((i.1 + 1 : ℕ) : ℤ) * numT
          have he := cosInt_sinInt_err kti
          have hse := asReal_err c i
          have hse_nn : (0 : ℝ) ≤ (asErrInt c i.1 : ℝ) := by
            have := le_trans (abs_nonneg _) hse
            exact (div_nonneg_iff.mp this).resolve_right (by norm_num [FSC]) |>.1
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          have ht1 : |π * ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((kti : ℝ) * θ₀))| ≤
              ((PIHI : ℝ) / 100000000) * ((asErrInt c i.1 : ℝ) / (FSC : ℝ)) := by
            rw [abs_mul, abs_of_pos hpi_pos, abs_mul]
            have h1 : |asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)| * |Real.cos ((kti : ℝ) * θ₀)| ≤ (asErrInt c i.1 : ℝ) / (FSC : ℝ) := by
              have := mul_le_mul hse (Real.abs_cos_le_one ((kti : ℝ) * θ₀))
                (abs_nonneg (Real.cos ((kti : ℝ) * θ₀)))
                (div_nonneg hse_nn (by norm_num [FSC]))
              linarith
            exact mul_le_mul hpi.2.le h1 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num [PIHI])
          have ht2 : |((PILO : ℝ) / 100000000) *
              (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((kti : ℝ) * θ₀) - (sinInt kti : ℝ) / (SB : ℝ)) +
               ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((kti : ℝ) * θ₀) - (cosInt kti : ℝ) / (SB : ℝ)))| ≤
              ((PIHI : ℝ) / 100000000) * ((|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)|) / (FSC : ℝ) * (10240 / (SB : ℝ))) := by
            rw [abs_mul, abs_of_pos (by norm_num [PILO])]
            have h1 : |-((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((kti : ℝ) * θ₀) - (sinInt kti : ℝ) / (SB : ℝ)) +
                ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((kti : ℝ) * θ₀) - (cosInt kti : ℝ) / (SB : ℝ))| ≤
                (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)|) / (FSC : ℝ) * (10240 / (SB : ℝ)) := by
              have ha := abs_add_le
                (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((kti : ℝ) * θ₀) - (sinInt kti : ℝ) / (SB : ℝ)))
                (((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((kti : ℝ) * θ₀) - (cosInt kti : ℝ) / (SB : ℝ)))
              rw [abs_mul, abs_neg, abs_mul, abs_div, abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC)] at ha
              have hb := mul_le_mul_of_nonneg_left he.2 (div_nonneg (abs_nonneg (acInt c i.1 : ℝ)) (by norm_num [FSC] : (0 : ℝ) ≤ FSC))
              have hc := mul_le_mul_of_nonneg_left he.1 (div_nonneg (abs_nonneg (asInt c i.1 : ℝ)) (by norm_num [FSC] : (0 : ℝ) ≤ FSC))
              have hEq : (|(acInt c i.1 : ℝ)| / (FSC : ℝ)) * (10240 / (SB : ℝ)) +
                  (|(asInt c i.1 : ℝ)| / (FSC : ℝ)) * (10240 / (SB : ℝ)) =
                  (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)|) / (FSC : ℝ) * (10240 / (SB : ℝ)) := by ring
              linarith
            exact mul_le_mul (by norm_num [PILO, PIHI]) h1 (abs_nonneg _) (by norm_num [PIHI])
          have ht3 : |(π - (PILO : ℝ) / 100000000) *
              (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((kti : ℝ) * θ₀) + ((asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((kti : ℝ) * θ₀))| ≤
              (1 / 100000000) * ((|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)|) / (FSC : ℝ)) := by
            rw [abs_mul]
            have h1 : |-((acInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((kti : ℝ) * θ₀) + ((asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((kti : ℝ) * θ₀)| ≤
                (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)|) / (FSC : ℝ) := by
              have ha := abs_add_le
                (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((kti : ℝ) * θ₀))
                (((asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((kti : ℝ) * θ₀))
              rw [abs_mul, abs_neg, abs_mul, abs_div, abs_div, abs_of_pos (by norm_num [FSC] : (0 : ℝ) < FSC)] at ha
              have hb := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one ((kti : ℝ) * θ₀)) (div_nonneg (abs_nonneg (acInt c i.1 : ℝ)) (by norm_num [FSC] : (0 : ℝ) ≤ FSC))
              have hc := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one ((kti : ℝ) * θ₀)) (div_nonneg (abs_nonneg (asInt c i.1 : ℝ)) (by norm_num [FSC] : (0 : ℝ) ≤ FSC))
              have hEq : |(acInt c i.1 : ℝ)| / (FSC : ℝ) + |(asInt c i.1 : ℝ)| / (FSC : ℝ) =
                  (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)|) / (FSC : ℝ) := by ring
              linarith
            exact mul_le_mul hpi_diff h1 (abs_nonneg _) (by norm_num)
          have htot : |π * ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((kti : ℝ) * θ₀)) +
               ((PILO : ℝ) / 100000000) *
                 (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((kti : ℝ) * θ₀) - (sinInt kti : ℝ) / (SB : ℝ)) +
                  ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((kti : ℝ) * θ₀) - (cosInt kti : ℝ) / (SB : ℝ))) +
               (π - (PILO : ℝ) / 100000000) *
                 (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((kti : ℝ) * θ₀) +
                  ((asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((kti : ℝ) * θ₀))| ≤
              ((asErrInt c i.1 : ℝ) * ((PIHI : ℝ) / 100000000) +
               (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) *
                 (((PIHI : ℝ) * 10240 + (SB : ℝ)) / (100000000 * (SB : ℝ)))) / (FSC : ℝ) := by
            have h0 : 0 ≤ (asErrInt c i.1 : ℝ) * (((PIHI : ℝ) * 10240 + (SB : ℝ)) / (100000000 * (SB : ℝ))) / (FSC : ℝ) :=
              div_nonneg (mul_nonneg hse_nn (by norm_num [PIHI, SB])) (by norm_num [FSC])
            have ha1 := abs_add_le
              (π * ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((kti : ℝ) * θ₀)) +
               ((PILO : ℝ) / 100000000) *
                 (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((kti : ℝ) * θ₀) - (sinInt kti : ℝ) / (SB : ℝ)) +
                  ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((kti : ℝ) * θ₀) - (cosInt kti : ℝ) / (SB : ℝ))))
              ((π - (PILO : ℝ) / 100000000) *
                 (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * Real.sin ((kti : ℝ) * θ₀) +
                  ((asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((kti : ℝ) * θ₀)))
            have ha2 := abs_add_le
              (π * ((asReal c i - (asInt c i.1 : ℝ) / (FSC : ℝ)) * Real.cos ((kti : ℝ) * θ₀)))
              (((PILO : ℝ) / 100000000) *
                 (-((acInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.sin ((kti : ℝ) * θ₀) - (sinInt kti : ℝ) / (SB : ℝ)) +
                  ((asInt c i.1 : ℝ) / (FSC : ℝ)) * (Real.cos ((kti : ℝ) * θ₀) - (cosInt kti : ℝ) / (SB : ℝ))))
            have hEq : ((PIHI : ℝ) / 100000000) * ((asErrInt c i.1 : ℝ) / (FSC : ℝ)) +
              ((PIHI : ℝ) / 100000000) * ((|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)|) / (FSC : ℝ) * (10240 / (SB : ℝ))) +
              (1 / 100000000) * ((|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)|) / (FSC : ℝ)) +
              (asErrInt c i.1 : ℝ) * (((PIHI : ℝ) * 10240 + (SB : ℝ)) / (100000000 * (SB : ℝ))) / (FSC : ℝ) =
              ((asErrInt c i.1 : ℝ) * ((PIHI : ℝ) / 100000000) +
               (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) *
                 (((PIHI : ℝ) * 10240 + (SB : ℝ)) / (100000000 * (SB : ℝ)))) / (FSC : ℝ) := by
              norm_num [FSC, SB, PIHI]; ring
            linarith
          calc ((i.1 + 1 : ℕ) : ℝ) * |_ + _ + _|
              ≤ ((i.1 + 1 : ℕ) : ℝ) * _ := mul_le_mul_of_nonneg_left htot (Nat.cast_nonneg _)
            _ = _ := by ring
        refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) (by norm_num)).trans (le_of_eq ?_)
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        have hSM1 : (SM_serr : ℝ) = ∑ i : Fin 12, ((i.1 + 1 : ℕ) : ℝ) * (asErrInt c i.1 : ℝ) := by
          simp only [SM_serr]; rw [foldl_range_12]; push_cast; rfl
        have hSM2 : (SM_acas : ℝ) = ∑ i : Fin 12,
            ((i.1 + 1 : ℕ) : ℝ) * (|(acInt c i.1 : ℝ)| + |(asInt c i.1 : ℝ)| + (asErrInt c i.1 : ℝ)) := by
          simp only [SM_acas]; rw [foldl_range_12]; push_cast; rfl
        rw [hSM1, hSM2]; ring
      have hcd1 := le_cdiv_real (PIHI * SM_serr) 200000000 (by norm_num)
      have hcd2 := le_cdiv_real (SM_acas * (PIHI * 10240 + SB)) (200000000 * SB) (by norm_num [SB])
      calc |_ + _| ≤ |_| + |_| := abs_add_le _ _
        _ ≤ 1 / (FSC : ℝ) + _ := add_le_add h3 hsum_bd
        _ ≤ (errPsipInt c : ℝ) / (FSC : ℝ) := by
            change _ ≤ ((cdiv (PIHI * SM_serr) 200000000 + cdiv (SM_acas * (PIHI * 10240 + SB)) (200000000 * SB) + 2 : ℤ) : ℝ) / (FSC : ℝ)
            push_cast
            have h1' : (PIHI : ℝ) * (SM_serr : ℝ) / 200000000 ≤ (cdiv (PIHI * SM_serr) 200000000 : ℝ) := by
              simpa [Int.cast_mul, Int.cast_ofNat] using hcd1
            have h2' : (SM_acas : ℝ) * ((PIHI : ℝ) * 10240 + (SB : ℝ)) / (200000000 * (SB : ℝ)) ≤
                (cdiv (SM_acas * (PIHI * 10240 + SB)) (200000000 * SB) : ℝ) := by
              simpa [Int.cast_mul, Int.cast_add, Int.cast_ofNat] using hcd2
            rw [← add_div]
            exact div_le_div_of_nonneg_right (by linarith) (by norm_num [FSC])
    have htay := integral_abs_le_taylor (m := mT) (h := 1 / 1024)
      (a0 := (qInt : ℝ) / (FSC : ℝ)) (b0 := (qpInt : ℝ) / (FSC : ℝ))
      (e0 := (errPsiInt c : ℝ) / (FSC : ℝ)) (e1 := (errPsipInt c : ℝ) / (FSC : ℝ))
      (L2 := (Lq2Int c : ℝ) / (FSC : ℝ))
      (by norm_num) hLq2_nn (PsiCert_continuous c) hPsi''c
      (fun t _ => hPsi_deriv t) (fun t _ => hPsi'_deriv t) (fun t _ => hPsi''b t) ha_err hb_err
    have hlin : linAbsInt |(qInt : ℝ) / (FSC : ℝ)| |(qpInt : ℝ) / (FSC : ℝ)| (1 / 1024) ≤
        (stepL1Int c acL asL j : ℝ) / (1024 ^ 2 * (FSC : ℝ)) := by
      have hfold : (List.range 12).foldl (fun (acc : ℤ × ℤ) i =>
          let m : ℤ := (i + 1 : ℕ)
          let kt : ℤ := m * numT
          let cv := cosInt kt
          let sv := sinInt kt
          let aci := acL.getD i 0
          let asi := asL.getD i 0
          (acc.1 + aci * cv + asi * sv, acc.2 + m * (-aci * sv + asi * cv))) (0, 0) = (trigQ, trigQp) := by
        have h1 := foldl_range_12_prod
          (fun i => acL.getD i 0 * cosInt (((i + 1 : ℕ) : ℤ) * numT) +
            asL.getD i 0 * sinInt (((i + 1 : ℕ) : ℤ) * numT))
          (fun i => ((i + 1 : ℕ) : ℤ) * (-acL.getD i 0 * sinInt (((i + 1 : ℕ) : ℤ) * numT) +
            asL.getD i 0 * cosInt (((i + 1 : ℕ) : ℤ) * numT)))
        simp only [add_assoc] at h1 ⊢
        rw [h1]
        apply Prod.ext <;> (dsimp only; refine Finset.sum_congr rfl fun i _ => by rw [hacL i, hasL i])
      have hstep : stepL1Int c acL asL j =
          if |qpInt| ≤ 1024 * |qInt| then 2 * (1024 * |qInt|)
          else cdiv ((1024 * |qInt|) * (1024 * |qInt|) + |qpInt| * |qpInt|) |qpInt| := by
        unfold stepL1Int; dsimp only; rw [hfold]
      rw [hstep]
      unfold linAbsInt
      have hFSC : (0 : ℝ) < (FSC : ℝ) := by norm_num [FSC]
      rw [abs_div, abs_div, abs_of_pos hFSC]
      have hc1 : (|(qpInt : ℝ)| / (FSC : ℝ) * (1 / 1024) ≤ |(qInt : ℝ)| / (FSC : ℝ)) ↔
          (|qpInt| ≤ 1024 * |qInt|) := by
        constructor <;> intro h
        · have : (|qpInt| : ℝ) ≤ (1024 * |qInt| : ℝ) := by
            have h' := mul_le_mul_of_nonneg_right h (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1024) hFSC.le)
            field_simp at h'; push_cast; linarith
          exact_mod_cast this
        · have hR : (|qpInt| : ℝ) ≤ (1024 * |qInt| : ℝ) := by exact_mod_cast h
          push_cast at hR
          rw [show |(qpInt : ℝ)| / (FSC : ℝ) * (1 / 1024) = (|(qpInt : ℝ)| / 1024) / (FSC : ℝ) by ring]
          exact div_le_div_of_nonneg_right (by linarith) hFSC.le
      by_cases h1 : |qpInt| ≤ 1024 * |qInt|
      · rw [if_pos (hc1.mpr h1), if_pos h1]; push_cast; ring_nf; rfl
      · rw [if_neg (mt hc1.mp h1), if_neg h1]
        have hbpos : (0 : ℤ) < |qpInt| := by
          have : 0 ≤ |qInt| := abs_nonneg qInt
          have : 0 ≤ |qpInt| := abs_nonneg qpInt
          omega
        have hcd := le_cdiv_real ((1024 * |qInt|) * (1024 * |qInt|) + |qpInt| * |qpInt|) |qpInt| hbpos
        have hbR : (0 : ℝ) < |(qpInt : ℝ)| := by exact_mod_cast hbpos
        have hEq : ((|(qInt : ℝ)| / (FSC : ℝ)) ^ 2 + (|(qpInt : ℝ)| / (FSC : ℝ) * (1 / 1024)) ^ 2) /
            (|(qpInt : ℝ)| / (FSC : ℝ)) =
            ((((1024 * |qInt|) * (1024 * |qInt|) + |qpInt| * |qpInt|) : ℤ) : ℝ) /
            ((|qpInt| : ℤ) : ℝ) / (1024 ^ 2 * (FSC : ℝ)) := by
          push_cast; field_simp
        rw [hEq]
        exact div_le_div_of_nonneg_right hcd (mul_nonneg (by norm_num) (by norm_num [FSC]))
    linarith [htay, hlin]
  have hsum := Finset.sum_le_sum hterm_j
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_ofNat, ← Finset.sum_div] at hsum
  have hcd := le_cdiv_real
    ((3 * sumL1IntLoop c acL asL 1024 0 + 3 * 2 * 1024 * 1024 * errPsiInt c +
      3 * 2 * 1024 * errPsipInt c + Lq2Int c) * QSC) (6 * 1024 * 1024 * FSC) (by norm_num [FSC])
  have hloop : (sumL1IntLoop c acL asL 1024 0 : ℝ) = ∑ j ∈ Finset.range 1024, (stepL1Int c acL asL j : ℝ) := by
    rw [sumL1IntLoop_eq, zero_add]; push_cast; rfl
  refine (mul_le_mul_of_nonneg_left hsum (by norm_num)).trans ?_
  unfold L1ubQ; dsimp only
  have hEq : (1 / 2) * ((∑ j ∈ Finset.range 1024, (stepL1Int c acL asL j : ℝ)) / (1024 ^ 2 * (FSC : ℝ)) +
      1024 * (2 * ((errPsiInt c : ℝ) / (FSC : ℝ)) * (1 / 1024)) +
      1024 * (2 * ((errPsipInt c : ℝ) / (FSC : ℝ)) * (1 / 1024) ^ 2) +
      1024 * ((1 / 3) * ((Lq2Int c : ℝ) / (FSC : ℝ)) * (1 / 1024) ^ 3)) =
      (((3 * sumL1IntLoop c acL asL 1024 0 + 3 * 2 * 1024 * 1024 * errPsiInt c +
        3 * 2 * 1024 * errPsipInt c + Lq2Int c) * QSC : ℤ) : ℝ) /
      ((6 * 1024 * 1024 * FSC : ℤ) : ℝ) / (QSC : ℝ) := by
    push_cast; rw [hloop]; norm_num [QSC, FSC]; ring
  rw [hEq]
  exact div_le_div_of_nonneg_right hcd (by norm_num [QSC])

private lemma C0ubQ_sound (c : CertData) (hu_pos : ∀ i : Fin 12, i.1 ≠ 1 → 0 < getI c.u i) :
    (c.lam0 : ℝ) / (ZSC : ℝ) + (2 / 3) * ((c.lam2 : ℝ) / (ZSC : ℝ)) +
      (∑ i : Fin 12, if i.1 = 1 then 0 else
        2 * uReal c i * (sVal (i.1 + 1)) ^ 2 +
        ((rReal c i) ^ 2 + (qReal c i) ^ 2) / (8 * uReal c i)) +
      (L1ubQ c : ℝ) / (QSC : ℝ) ≤ (C0ubQ c : ℝ) / (QSC : ℝ) := by
  unfold C0ubQ; dsimp only
  set g : ℕ → ℤ := fun i =>
    if i = 1 then 0
    else
      let m : ℕ := i + 1
      let ui := c.u.getD i 0
      let ri := c.r.getD i 0
      let qi := c.q.getD i 0
      let sTerm := if m % 2 = 1 then
        cdiv (2 * ui * 10000000000000000 * QSC) (ZSC * (m : ℤ) * (m : ℤ) * PILO * PILO)
      else 0
      let qTerm := cdiv ((ri * ri + qi * qi) * QSC) (8 * ZSC * ui)
      sTerm + qTerm
  have hfold : (List.range 12).foldl (fun acc i =>
      if i = 1 then acc
      else
        let m : ℕ := i + 1
        let ui := c.u.getD i 0
        let ri := c.r.getD i 0
        let qi := c.q.getD i 0
        let sTerm := if m % 2 = 1 then
          cdiv (2 * ui * 10000000000000000 * QSC) (ZSC * (m : ℤ) * (m : ℤ) * PILO * PILO)
        else 0
        let qTerm := cdiv ((ri * ri + qi * qi) * QSC) (8 * ZSC * ui)
        acc + sTerm + qTerm) (c.lam0 * 100 + cdiv (2 * c.lam2 * 100) 3 + L1ubQ c) =
      (c.lam0 * 100 + cdiv (2 * c.lam2 * 100) 3 + L1ubQ c) + ∑ i : Fin 12, g i.1 := by
    have hshift : ∀ (l : List ℕ) (a : ℤ), l.foldl (fun acc i => acc + g i) a = a + l.foldl (fun acc i => acc + g i) 0 := by
      intro l; induction l with
      | nil => intro a; simp
      | cons x xs ih => intro a; simp only [List.foldl_cons, zero_add]; rw [ih (a + g x), ih (g x)]; ring
    have h1 : ∀ (l : List ℕ) (a : ℤ),
        l.foldl (fun acc i =>
          if i = 1 then acc
          else
            let m : ℕ := i + 1
            let ui := c.u.getD i 0
            let ri := c.r.getD i 0
            let qi := c.q.getD i 0
            let sTerm := if m % 2 = 1 then
              cdiv (2 * ui * 10000000000000000 * QSC) (ZSC * (m : ℤ) * (m : ℤ) * PILO * PILO)
            else 0
            let qTerm := cdiv ((ri * ri + qi * qi) * QSC) (8 * ZSC * ui)
            acc + sTerm + qTerm) a = a + l.foldl (fun acc i => acc + g i) 0 := by
      intro l; induction l with
      | nil => intro a; simp
      | cons x xs ih =>
          intro a; simp only [List.foldl_cons]
          by_cases hx : x = 1
          · rw [if_pos hx, ih a, show g x = 0 by simp [g, hx], zero_add]
          · rw [if_neg hx, ih, zero_add, hshift xs (g x)]
            dsimp only [g]; rw [if_neg hx]; ring
    rw [h1, foldl_range_12]
  rw [hfold]; push_cast
  have hpi := pi_bounds
  have hlam2 : (2 / 3 : ℝ) * ((c.lam2 : ℝ) / (ZSC : ℝ)) ≤ (cdiv (2 * c.lam2 * 100) 3 : ℝ) / (QSC : ℝ) := by
    have hcd := le_cdiv_real (2 * c.lam2 * 100) 3 (by norm_num)
    have hEq : (2 / 3 : ℝ) * ((c.lam2 : ℝ) / (ZSC : ℝ)) =
        (((2 * c.lam2 * 100 : ℤ) : ℝ) / 3) / (QSC : ℝ) := by push_cast; norm_num [ZSC, QSC]; ring
    rw [hEq]; exact div_le_div_of_nonneg_right hcd (by norm_num [QSC])
  have hsum : ∑ i : Fin 12, (if i.1 = 1 then (0 : ℝ) else
      2 * uReal c i * (sVal (i.1 + 1)) ^ 2 +
      ((rReal c i) ^ 2 + (qReal c i) ^ 2) / (8 * uReal c i)) ≤
      (∑ i : Fin 12, (g i.1 : ℝ)) / (QSC : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : i.1 = 1
    · simp [g, hi]
    · simp only [if_neg hi, g]
      have hui : 0 < c.u.getD i.1 0 := hu_pos i hi
      have hs : 2 * uReal c i * (sVal (i.1 + 1)) ^ 2 ≤
          ((if (i.1 + 1) % 2 = 1 then
            cdiv (2 * c.u.getD i.1 0 * 10000000000000000 * QSC)
              (ZSC * ((i.1 + 1 : ℕ) : ℤ) * ((i.1 + 1 : ℕ) : ℤ) * PILO * PILO)
          else 0 : ℤ) : ℝ) / (QSC : ℝ) := by
        by_cases hodd : (i.1 + 1) % 2 = 1
        · rw [if_pos hodd, sVal_odd_eq (i.1 + 1) hodd]
          have hsgn2 : (if ((i.1 + 1 - 1) / 2) % 2 = 0 then (1 : ℝ) else -1) ^ 2 = 1 := by
            split_ifs <;> norm_num
          rw [div_pow, hsgn2]
          have hpi2 : ((PILO : ℝ) / 100000000) ^ 2 ≤ π ^ 2 := by
            have hpl : (0 : ℝ) < (PILO : ℝ) / 100000000 := by norm_num [PILO]
            nlinarith [hpi.1, Real.pi_pos, hpl]
          have hcd := le_cdiv_real (2 * c.u.getD i.1 0 * 10000000000000000 * QSC)
            (ZSC * ((i.1 + 1 : ℕ) : ℤ) * ((i.1 + 1 : ℕ) : ℤ) * PILO * PILO)
            (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num [ZSC]) (by omega)) (by omega)) (by norm_num [PILO])) (by norm_num [PILO]))
          have h1 : 2 * uReal c i * (1 / (π * ((i.1 + 1 : ℕ) : ℝ)) ^ 2) ≤
              2 * uReal c i * (1 / (((PILO : ℝ) / 100000000) * ((i.1 + 1 : ℕ) : ℝ)) ^ 2) := by
            have huR : 0 < uReal c i := by unfold uReal; exact div_pos (by exact_mod_cast hui) (by norm_num [ZSC])
            have hm_pos : (0 : ℝ) < ((i.1 + 1 : ℕ) : ℝ) := by positivity
            have hpl : (0 : ℝ) < (PILO : ℝ) / 100000000 := by norm_num [PILO]
            gcongr; exact hpi.1.le
          refine h1.trans ?_
          have hEq : 2 * uReal c i * (1 / (((PILO : ℝ) / 100000000) * ((i.1 + 1 : ℕ) : ℝ)) ^ 2) =
              (((2 * c.u.getD i.1 0 * 10000000000000000 * QSC : ℤ) : ℝ) /
               ((ZSC * ((i.1 + 1 : ℕ) : ℤ) * ((i.1 + 1 : ℕ) : ℤ) * PILO * PILO : ℤ) : ℝ)) / (QSC : ℝ) := by
            unfold uReal getI; push_cast; norm_num [ZSC, QSC, PILO]; field_simp; ring
          rw [hEq]; exact div_le_div_of_nonneg_right hcd (by norm_num [QSC])
        · rw [if_neg hodd, sVal_even_eq (i.1 + 1) (by omega)]; simp
      have hq : ((rReal c i) ^ 2 + (qReal c i) ^ 2) / (8 * uReal c i) ≤
          (cdiv ((c.r.getD i.1 0 * c.r.getD i.1 0 + c.q.getD i.1 0 * c.q.getD i.1 0) * QSC)
            (8 * ZSC * c.u.getD i.1 0) : ℝ) / (QSC : ℝ) := by
        have hcd := le_cdiv_real
          ((c.r.getD i.1 0 * c.r.getD i.1 0 + c.q.getD i.1 0 * c.q.getD i.1 0) * QSC)
          (8 * ZSC * c.u.getD i.1 0) (mul_pos (by norm_num [ZSC]) hui)
        have hEq : ((rReal c i) ^ 2 + (qReal c i) ^ 2) / (8 * uReal c i) =
            ((((c.r.getD i.1 0 * c.r.getD i.1 0 + c.q.getD i.1 0 * c.q.getD i.1 0) * QSC : ℤ) : ℝ) /
             ((8 * ZSC * c.u.getD i.1 0 : ℤ) : ℝ)) / (QSC : ℝ) := by
          unfold rReal qReal uReal getI; push_cast
          have huiR : (c.u.getD i.1 0 : ℝ) ≠ 0 := by exact_mod_cast hui.ne'
          norm_num [ZSC, QSC]; field_simp; ring
        rw [hEq]; exact div_le_div_of_nonneg_right hcd (by norm_num [QSC])
      rw [Int.cast_add]; conv_rhs => rw [add_div]
      linarith [hs, hq]
  have hlam0 : (c.lam0 : ℝ) / (ZSC : ℝ) = ((c.lam0 * 100 : ℤ) : ℝ) / (QSC : ℝ) := by
    push_cast; norm_num [ZSC, QSC]; ring
  rw [add_div, add_div, add_div]
  have hlam0' : (c.lam0 : ℝ) * 100 / (QSC : ℝ) = (c.lam0 : ℝ) / (ZSC : ℝ) := by
    norm_num [ZSC, QSC]; ring
  linarith

private structure Quad6 where
  c0 : ℤ
  ch2 : ℤ
  ch : ℤ
  cr2 : ℤ
  cp : ℤ
  cq : ℤ

private def evalQuad (Q : Quad6) (h p q : ℝ) : ℝ :=
  ((Q.c0 : ℝ) + (Q.ch2 : ℝ) * h ^ 2 + (Q.ch : ℝ) * h +
   (Q.cr2 : ℝ) * (p ^ 2 + q ^ 2) + (Q.cp : ℝ) * p + (Q.cq : ℝ) * q) / (QSC : ℝ)

private lemma certC0Int_sound {f : ℝ → ℝ} (hfm : Measurable f) (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1)
    (hfint : (∫ t in (-1 : ℝ)..1, f t) = 1)
    (hM_le : ∀ x, MFun f x ≤ (379005 : ℝ) / 1000000)
    (c : CertData) (hu_pos : ∀ i : Fin 12, i.1 ≠ 1 → 0 < getI c.u i)
    (hu2 : getI c.u ⟨1, by omega⟩ = c.u2)
    (c0_lb : ℤ) (hc0 : c0_lb ≤ certC0Int c) :
    evalQuad ⟨c0_lb, -50 * c.lam2, -100 * c.eta, 50 * c.u2, -100 * c.nu, -100 * c.mu⟩
      (EM f) (c1Val f) (d1Val f) ≤ 0 := by
  have hmain := dual_cert_ineq hfm hf hfint hM_le c hu_pos hu2
    (DubQ_sound c) (L1ubQ_sound c) (C0ubQ_sound c hu_pos)
  have hc0R : (c0_lb : ℝ) / (QSC : ℝ) ≤ -(C0ubQ c : ℝ) / (QSC : ℝ) -
      ((379005 : ℝ) / 1000000) * ((DubQ c : ℝ) / (QSC : ℝ)) := by
    have h1 : (c0_lb : ℝ) ≤ (certC0Int c : ℝ) := by exact_mod_cast hc0
    have hcd := le_cdiv_real (379005 * DubQ c) 1000000 (by norm_num)
    unfold certC0Int at h1; push_cast at h1
    have hcd' : (379005 : ℝ) * (DubQ c : ℝ) / 1000000 ≤ (cdiv (379005 * DubQ c) 1000000 : ℝ) := by
      simpa [Int.cast_mul, Int.cast_ofNat] using hcd
    have h2 : (c0_lb : ℝ) ≤ -(C0ubQ c : ℝ) - (379005 : ℝ) * (DubQ c : ℝ) / 1000000 := by linarith
    have h3 := div_le_div_of_nonneg_right h2 (by norm_num [QSC] : (0 : ℝ) ≤ QSC)
    have h4 : (-(C0ubQ c : ℝ) - (379005 : ℝ) * (DubQ c : ℝ) / 1000000) / (QSC : ℝ) =
        -(C0ubQ c : ℝ) / (QSC : ℝ) - ((379005 : ℝ) / 1000000) * ((DubQ c : ℝ) / (QSC : ℝ)) := by ring
    linarith
  unfold evalQuad; dsimp only
  have hEq : (((c0_lb : ℝ) + ((-50 * c.lam2 : ℤ) : ℝ) * (EM f) ^ 2 + ((-100 * c.eta : ℤ) : ℝ) * EM f +
      ((50 * c.u2 : ℤ) : ℝ) * ((c1Val f) ^ 2 + (d1Val f) ^ 2) +
      ((-100 * c.nu : ℤ) : ℝ) * c1Val f + ((-100 * c.mu : ℤ) : ℝ) * d1Val f) / (QSC : ℝ)) =
      (c0_lb : ℝ) / (QSC : ℝ)
        - ((c.lam2 : ℝ) / (2 * (ZSC : ℝ))) * (EM f) ^ 2
        - ((c.eta : ℝ) / (ZSC : ℝ)) * EM f
        + ((c.u2 : ℝ) / (2 * (ZSC : ℝ))) * ((c1Val f) ^ 2 + (d1Val f) ^ 2)
        - ((c.nu : ℝ) / (ZSC : ℝ)) * c1Val f
        - ((c.mu : ℝ) / (ZSC : ℝ)) * d1Val f := by
    push_cast; norm_num [ZSC, QSC]; ring
  rw [hEq]; rw [neg_div] at hc0R; linarith

/-! ### Section 5: The 7 Verified Certificates and 166-Leaf Dyadic Integer Octree -/

private def cert0 : CertData :=
  { lam0 := -50000, lam1 := -13, lam2 := 21281, u2 := -31873,
    eta := -35, nu := -8066, mu := -19, kappa := 2610,
    u := [1, -31873, 33520, 41238, 33409, 12401, 1038, 1, 2761, 4282, 2603, 1008],
    w := [-26, -99, -58, -39, -3, 1, 10, 12, 18, 16, 10, 5],
    r := [0, 0, 16226, -3370, -4604, 2784, 271, 0, -701, 106, 382, -187],
    q := [0, 0, 1, -2, -5, 4, 0, 0, -2, 0, 1, 0] }

private def cert1 : CertData :=
  { lam0 := -50000, lam1 := 5703, lam2 := 22500, u2 := -50000,
    eta := 23216, nu := 0, mu := 23205, kappa := 0,
    u := [1, -50000, 4905, 17396, 23912, 16448, 12105, 8821, 8813, 6172, 3675, 891],
    w := [10652, 50000, 50000, 50000, 31569, 13270, -1443, -6197, -4450, -446, 1017, 1084],
    r := [0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 1, -2],
    q := [0, 0, -2780, -5293, 890, -170, -2466, -607, 1675, 492, -611, 103] }

private def cert2 : CertData :=
  { lam0 := -50000, lam1 := -7442, lam2 := 22512, u2 := -50000,
    eta := -17706, nu := -1, mu := -16561, kappa := 0,
    u := [1, -50000, 1, 8507, 10923, 8472, 7163, 9317, 7869, 6336, 2813, 1232],
    w := [-3631, -50000, -46209, -50000, -28328, -13886, -2075, -2239, -3911, -4631, -2781, -826],
    r := [0, 0, 0, 4, 0, -11, 17, -11, 5, -6, 8, -5],
    q := [0, 0, 0, 1239, 722, 1195, 1254, 114, -725, 297, 197, -287] }

private def cert3 : CertData :=
  { lam0 := -50000, lam1 := -9231, lam2 := 21753, u2 := 14211,
    eta := -20423, nu := -14659, mu := -1708, kappa := 5000,
    u := [1, 14211, 49992, 36911, 159, 1, 1, 3090, 1, 1, 764, 89],
    w := [-22578, -48012, -4401, 12707, 3128, 2296, 1762, 10592, 1774, -700, -2854, -125],
    r := [0, 0, 28557, -9600, -80, 0, 0, 385, 0, 0, -87, -3],
    q := [0, 0, -9, 13, -6, 0, 0, -293, 0, 0, -172, -29] }

private def cert4 : CertData :=
  { lam0 := -50000, lam1 := -6682, lam2 := 17682, u2 := 18263,
    eta := -8615, nu := -4345, mu := 33044, kappa := 1424,
    u := [1, 18263, 50000, 11530, 1, 3666, 2843, 1, 3416, 5275, 2017, 375],
    w := [-50000, -50000, 31235, 41559, 29297, 8590, 7793, -6771, -7998, -7675, -1329, -2108],
    r := [0, 0, 8936, -3212, 0, -242, 506, 0, -224, -26, 141, -28],
    q := [0, 0, -17779, -1199, 0, -620, -433, 0, 1335, 622, -510, -45] }

private def cert5 : CertData :=
  { lam0 := -50000, lam1 := 2261, lam2 := 20054, u2 := -5379,
    eta := 14262, nu := -14458, mu := 22370, kappa := 4941,
    u := [1, -5379, 50000, 34293, 9899, 1, 3035, 6127, 2232, 497, 1, 770],
    w := [-5052, 20184, 36801, 35265, 10955, -8692, -8582, -3490, -1597, -6416, -5542, -3129],
    r := [0, 0, 26887, -5850, -3422, 0, 1262, 642, -689, -125, 0, 176],
    q := [0, 0, -4040, -1444, -368, 0, -526, -690, -117, -63, 0, -259] }

private def cert6 : CertData :=
  { lam0 := -50000, lam1 := -2148, lam2 := 20110, u2 := -5066,
    eta := -14120, nu := -14542, mu := -22513, kappa := 4987,
    u := [2, -5066, 50000, 34504, 9908, 7, 2940, 5921, 2050, 422, 2, 808],
    w := [5398, -19339, -36765, -35374, -11347, 8995, 8777, 3954, 1452, 6324, 5263, 3067],
    r := [1, 0, 26986, -5840, -3397, 1, 1251, 600, -637, -122, 0, 159],
    q := [0, 0, 4056, 1561, 427, 1, 540, 748, 117, 46, 1, 259] }

private def verifiedQuads : List Quad6 :=
  [
    { c0 := -63353, ch2 := -1064050, ch := 3500, cr2 := -1593650, cp := 806600, cq := 1900 },
    { c0 := 178046, ch2 := -1125000, ch := -2321600, cr2 := -2500000, cp := 0, cq := -2320500 },
    { c0 := 279589, ch2 := -1125600, ch := 1770600, cr2 := -2500000, cp := 100, cq := 1656100 },
    { c0 := -728707, ch2 := -1087650, ch := 2042300, cr2 := 710550, cp := 1465900, cq := 170800 },
    { c0 := -589500, ch2 := -884100, ch := 861500, cr2 := 913150, cp := 434500, cq := -3304400 },
    { c0 := -537894, ch2 := -1002700, ch := -1426200, cr2 := -268950, cp := 1445800, cq := -2237000 },
    { c0 := -544616, ch2 := -1005500, ch := 1412000, cr2 := -253300, cp := 1454200, cq := 2251300 }
  ]

private lemma cert0_ok : (-63353 : ℤ) ≤ certC0Int cert0 := by
  set_option maxRecDepth 200000 in decide +kernel
private lemma cert1_ok : (178046 : ℤ) ≤ certC0Int cert1 := by
  set_option maxRecDepth 200000 in decide +kernel
private lemma cert2_ok : (279589 : ℤ) ≤ certC0Int cert2 := by
  set_option maxRecDepth 200000 in decide +kernel
private lemma cert3_ok : (-728707 : ℤ) ≤ certC0Int cert3 := by
  set_option maxRecDepth 200000 in decide +kernel
private lemma cert4_ok : (-589500 : ℤ) ≤ certC0Int cert4 := by
  set_option maxRecDepth 200000 in decide +kernel
private lemma cert5_ok : (-537894 : ℤ) ≤ certC0Int cert5 := by
  set_option maxRecDepth 200000 in decide +kernel
private lemma cert6_ok : (-544616 : ℤ) ≤ certC0Int cert6 := by
  set_option maxRecDepth 200000 in decide +kernel

private def BSC : ℤ := 4096

private def minQInt (a b x1 x2 : ℤ) : ℤ :=
  if a ≤ 0 then min (a * x1 * x1 + b * BSC * x1) (a * x2 * x2 + b * BSC * x2)
  else
    let s := x1 + x2
    let d := x2 - x1
    (a * s * s + 2 * b * BSC * s - |2 * a * s + 2 * b * BSC| * d) / 4

private lemma minQInt_le (a b x1 x2 : ℤ) {x : ℝ}
    (hx1 : (x1 : ℝ) / (BSC : ℝ) ≤ x) (hx2 : x ≤ (x2 : ℝ) / (BSC : ℝ)) :
    (minQInt a b x1 x2 : ℝ) ≤ (a : ℝ) * ((BSC : ℝ) * x) ^ 2 + (b : ℝ) * (BSC : ℝ) * ((BSC : ℝ) * x) := by
  set y : ℝ := (BSC : ℝ) * x
  have hy1 : (x1 : ℝ) ≤ y := by
    have hB : (0 : ℝ) < (BSC : ℝ) := by norm_num [BSC]
    have := mul_le_mul_of_nonneg_left hx1 hB.le
    simpa [y, mul_div_cancel₀ _ hB.ne'] using this
  have hy2 : y ≤ (x2 : ℝ) := by
    have hB : (0 : ℝ) < (BSC : ℝ) := by norm_num [BSC]
    have := mul_le_mul_of_nonneg_left hx2 hB.le
    simpa [y, mul_div_cancel₀ _ hB.ne'] using this
  unfold minQInt
  split_ifs with ha
  · have haR : (a : ℝ) ≤ 0 := by exact_mod_cast ha
    -- Concave quadratic on [x1, x2] attains min at an endpoint:
    -- (y - x1) * (x2 - y) ≥ 0, a ≤ 0 => a * (y - x1) * (y - x2) ≥ 0
    have hconc : (a : ℝ) * y ^ 2 + (b : ℝ) * (BSC : ℝ) * y ≥
        min ((a : ℝ) * (x1 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x1 : ℝ))
            ((a : ℝ) * (x2 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x2 : ℝ)) := by
      by_cases h12 : (x1 : ℝ) = (x2 : ℝ)
      · have hyx : y = (x1 : ℝ) := by linarith
        rw [hyx, h12]; simp
      · have hpos : 0 < (x2 : ℝ) - (x1 : ℝ) := sub_pos.mpr (lt_of_le_of_ne (le_trans hy1 hy2) h12)
        have hlin : (a : ℝ) * y ^ 2 + (b : ℝ) * (BSC : ℝ) * y ≥
            (((x2 : ℝ) - y) * ((a : ℝ) * (x1 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x1 : ℝ)) +
             (y - (x1 : ℝ)) * ((a : ℝ) * (x2 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x2 : ℝ))) /
            ((x2 : ℝ) - (x1 : ℝ)) := by
          rw [ge_iff_le, div_le_iff₀ hpos]
          have hpos_rhs : 0 ≤ (-(a : ℝ)) * ((x2 : ℝ) - (x1 : ℝ)) * ((y - (x1 : ℝ)) * ((x2 : ℝ) - y)) := by
            have : 0 ≤ -(a : ℝ) := by linarith
            have : 0 ≤ (y - (x1 : ℝ)) * ((x2 : ℝ) - y) := mul_nonneg (by linarith) (by linarith)
            positivity
          have hEq : ((a : ℝ) * y ^ 2 + (b : ℝ) * (BSC : ℝ) * y) * ((x2 : ℝ) - (x1 : ℝ)) -
              (((x2 : ℝ) - y) * ((a : ℝ) * (x1 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x1 : ℝ)) +
               (y - (x1 : ℝ)) * ((a : ℝ) * (x2 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x2 : ℝ))) =
              (-(a : ℝ)) * ((x2 : ℝ) - (x1 : ℝ)) * ((y - (x1 : ℝ)) * ((x2 : ℝ) - y)) := by ring
          linarith
        have hmin : min ((a : ℝ) * (x1 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x1 : ℝ))
            ((a : ℝ) * (x2 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x2 : ℝ)) ≤
            (((x2 : ℝ) - y) * ((a : ℝ) * (x1 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x1 : ℝ)) +
             (y - (x1 : ℝ)) * ((a : ℝ) * (x2 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x2 : ℝ))) /
            ((x2 : ℝ) - (x1 : ℝ)) := by
          rw [le_div_iff₀ hpos]
          nlinarith [min_le_left ((a : ℝ) * (x1 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x1 : ℝ))
            ((a : ℝ) * (x2 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x2 : ℝ)),
            min_le_right ((a : ℝ) * (x1 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x1 : ℝ))
            ((a : ℝ) * (x2 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x2 : ℝ))]
        linarith
    have hcast : ((min (a * x1 * x1 + b * BSC * x1) (a * x2 * x2 + b * BSC * x2) : ℤ) : ℝ) =
        min ((a : ℝ) * (x1 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x1 : ℝ))
            ((a : ℝ) * (x2 : ℝ) ^ 2 + (b : ℝ) * (BSC : ℝ) * (x2 : ℝ)) := by
      push_cast; simp only [sq, mul_assoc]
    linarith
  · push Not at ha
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha
    set s : ℤ := x1 + x2
    set d : ℤ := x2 - x1
    have hdiv : (((a * s * s + 2 * b * BSC * s - |2 * a * s + 2 * b * BSC| * d) / 4 : ℤ) : ℝ) ≤
        ((a * s * s + 2 * b * BSC * s - |2 * a * s + 2 * b * BSC| * d : ℤ) : ℝ) / 4 := by
      have h := Int.ediv_mul_le (a * s * s + 2 * b * BSC * s - |2 * a * s + 2 * b * BSC| * d)
        (by norm_num : (4 : ℤ) ≠ 0)
      have hR : (((a * s * s + 2 * b * BSC * s - |2 * a * s + 2 * b * BSC| * d) / 4 : ℤ) : ℝ) * 4 ≤
          ((a * s * s + 2 * b * BSC * s - |2 * a * s + 2 * b * BSC| * d : ℤ) : ℝ) := by
        exact_mod_cast h
      linarith
    refine hdiv.trans ?_
    have hconv : ((a * s * s + 2 * b * BSC * s - |2 * a * s + 2 * b * BSC| * d : ℤ) : ℝ) ≤
        4 * ((a : ℝ) * y ^ 2 + (b : ℝ) * (BSC : ℝ) * y) := by
      push_cast
      have hmid : |2 * y - (s : ℝ)| ≤ (d : ℝ) := by
        simp only [s, d]; push_cast; rw [abs_le]; constructor <;> linarith
      have htan : -|(2 * (a : ℝ) * (s : ℝ) + 2 * (b : ℝ) * (BSC : ℝ))| * (d : ℝ) ≤
          (2 * (a : ℝ) * (s : ℝ) + 2 * (b : ℝ) * (BSC : ℝ)) * (2 * y - (s : ℝ)) := by
        have h1 : |((2 * (a : ℝ) * (s : ℝ) + 2 * (b : ℝ) * (BSC : ℝ)) * (2 * y - (s : ℝ)))| ≤
            |(2 * (a : ℝ) * (s : ℝ) + 2 * (b : ℝ) * (BSC : ℝ))| * (d : ℝ) := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hmid (abs_nonneg _)
        linarith [(abs_le.mp h1).1]
      have hsq : 0 ≤ (a : ℝ) * (2 * y - (s : ℝ)) ^ 2 := by positivity
      nlinarith
    linarith

private def checkBoxInt (quads : List Quad6) (h1 h2 p1 p2 q1 q2 : ℤ) : Bool :=
  let qmin : ℤ := if q1 ≤ 0 ∧ 0 ≤ q2 then 0 else min |q1| |q2|
  if 2 * (p1 * p1 + qmin * qmin) > BSC * BSC then true
  else if 100 * h1 ≥ 42 * BSC then true
  else quads.any fun Q =>
    0 < Q.c0 * BSC * BSC + minQInt Q.ch2 Q.ch h1 h2 + minQInt Q.cr2 Q.cp p1 p2 + minQInt Q.cr2 Q.cq q1 q2

private def verifyOctree (quads : List Quad6) : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → Bool
  | 0, h1, h2, p1, p2, q1, q2 => checkBoxInt quads h1 h2 p1 p2 q1 q2
  | fuel + 1, h1, h2, p1, p2, q1, q2 =>
      if checkBoxInt quads h1 h2 p1 p2 q1 q2 then true
      else
        let dh := h2 - h1
        let dp := p2 - p1
        let dq := q2 - q1
        if dh ≥ dp ∧ dh ≥ dq then
          let hm := (h1 + h2) / 2
          verifyOctree quads fuel h1 hm p1 p2 q1 q2 && verifyOctree quads fuel hm h2 p1 p2 q1 q2
        else if dp ≥ dq then
          let pm := (p1 + p2) / 2
          verifyOctree quads fuel h1 h2 p1 pm q1 q2 && verifyOctree quads fuel h1 h2 pm p2 q1 q2
        else
          let qm := (q1 + q2) / 2
          verifyOctree quads fuel h1 h2 p1 p2 q1 qm && verifyOctree quads fuel h1 h2 p1 p2 qm q2

private lemma checkBoxInt_sound {quads : List Quad6} {h1 h2 p1 p2 q1 q2 : ℤ}
    (hok : checkBoxInt quads h1 h2 p1 p2 q1 q2 = true)
    (hp1_nn : 0 ≤ p1)
    {h p q : ℝ}
    (hh : (h1 : ℝ) / (BSC : ℝ) ≤ h ∧ h ≤ (h2 : ℝ) / (BSC : ℝ))
    (hp : (p1 : ℝ) / (BSC : ℝ) ≤ p ∧ p ≤ (p2 : ℝ) / (BSC : ℝ))
    (hq : (q1 : ℝ) / (BSC : ℝ) ≤ q ∧ q ≤ (q2 : ℝ) / (BSC : ℝ))
    (hdisk : p ^ 2 + q ^ 2 ≤ 1 / 2)
    (hmoser : h < 42 / 100) :
    ∃ Q ∈ quads, 0 < evalQuad Q h p q := by
  unfold checkBoxInt at hok
  dsimp only at hok
  set qmin : ℤ := if q1 ≤ 0 ∧ 0 ≤ q2 then 0 else min |q1| |q2|
  have hqmin : (qmin : ℝ) / (BSC : ℝ) ≤ |q| := by
    simp only [qmin]
    split_ifs with h0
    · simp
    · have hB : (0 : ℝ) < (BSC : ℝ) := by norm_num [BSC]
      have hcase : q2 < 0 ∨ 0 < q1 := by omega
      rcases hcase with hneg | hpos
      · have hqneg : q ≤ 0 := le_trans hq.2 (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hneg.le) hB.le)
        rw [abs_of_nonpos hqneg]
        have h1' : ((min |q1| |q2| : ℤ) : ℝ) ≤ (|q2| : ℝ) := by exact_mod_cast min_le_right |q1| |q2|
        have h2' : (|q2| : ℝ) = -(q2 : ℝ) := by
          have : |q2| = -q2 := abs_of_neg hneg
          exact_mod_cast this
        have h3' : -(q2 : ℝ) / (BSC : ℝ) ≤ -q := by rw [neg_div]; linarith [hq.2]
        exact le_trans (div_le_div_of_nonneg_right (by linarith) hB.le) h3'
      · have hqpos : 0 ≤ q := le_trans (div_nonneg (by exact_mod_cast hpos.le) hB.le) hq.1
        rw [abs_of_nonneg hqpos]
        have h1' : ((min |q1| |q2| : ℤ) : ℝ) ≤ (|q1| : ℝ) := by exact_mod_cast min_le_left |q1| |q2|
        have h2' : (|q1| : ℝ) = (q1 : ℝ) := by
          have : |q1| = q1 := abs_of_pos hpos
          exact_mod_cast this
        exact le_trans (div_le_div_of_nonneg_right (by linarith) hB.le) hq.1
  by_cases hdisk_out : 2 * (p1 * p1 + qmin * qmin) > BSC * BSC
  · exfalso
    have hB : (0 : ℝ) < (BSC : ℝ) := by norm_num [BSC]
    have hp1R : (0 : ℝ) ≤ (p1 : ℝ) / (BSC : ℝ) := div_nonneg (by exact_mod_cast hp1_nn) hB.le
    have hqminR : (0 : ℝ) ≤ (qmin : ℝ) / (BSC : ℝ) := by
      simp only [qmin]; split_ifs <;> positivity
    have hsq1 : ((p1 : ℝ) / (BSC : ℝ)) ^ 2 ≤ p ^ 2 := by nlinarith [hp.1]
    have hsq2 : ((qmin : ℝ) / (BSC : ℝ)) ^ 2 ≤ q ^ 2 := by
      rw [← sq_abs q]; nlinarith [hqmin]
    have hgt : (1 / 2 : ℝ) < ((p1 : ℝ) / (BSC : ℝ)) ^ 2 + ((qmin : ℝ) / (BSC : ℝ)) ^ 2 := by
      have h1R : ((BSC * BSC : ℤ) : ℝ) < ((2 * (p1 * p1 + qmin * qmin) : ℤ) : ℝ) := by exact_mod_cast hdisk_out
      push_cast at h1R
      rw [div_pow, div_pow, ← add_div, lt_div_iff₀ (sq_pos_of_pos hB)]
      linarith
    linarith
  · rw [if_neg hdisk_out] at hok
    by_cases hmoser_out : 100 * h1 ≥ 42 * BSC
    · exfalso
      have h2R : (42 : ℝ) * (BSC : ℝ) ≤ 100 * (h1 : ℝ) := by exact_mod_cast hmoser_out
      have hB : (0 : ℝ) < (BSC : ℝ) := by norm_num [BSC]
      have : (42 : ℝ) / 100 ≤ (h1 : ℝ) / (BSC : ℝ) := by
        rw [div_le_div_iff₀ (by norm_num) hB]; linarith
      linarith [hh.1]
    · rw [if_neg hmoser_out] at hok
      rw [List.any_eq_true] at hok
      obtain ⟨Q, hQmem, hQpos⟩ := hok
      refine ⟨Q, hQmem, ?_⟩
      have hposI : (0 : ℤ) < Q.c0 * BSC * BSC + minQInt Q.ch2 Q.ch h1 h2 +
          minQInt Q.cr2 Q.cp p1 p2 + minQInt Q.cr2 Q.cq q1 q2 := of_decide_eq_true hQpos
      have hposR : (0 : ℝ) < (Q.c0 : ℝ) * (BSC : ℝ) ^ 2 +
          (minQInt Q.ch2 Q.ch h1 h2 : ℝ) +
          (minQInt Q.cr2 Q.cp p1 p2 : ℝ) +
          (minQInt Q.cr2 Q.cq q1 q2 : ℝ) := by
        have : (0 : ℝ) < ((Q.c0 * BSC * BSC + minQInt Q.ch2 Q.ch h1 h2 +
            minQInt Q.cr2 Q.cp p1 p2 + minQInt Q.cr2 Q.cq q1 q2 : ℤ) : ℝ) := by exact_mod_cast hposI
        push_cast at this; linarith
      have hm1 := minQInt_le Q.ch2 Q.ch h1 h2 hh.1 hh.2
      have hm2 := minQInt_le Q.cr2 Q.cp p1 p2 hp.1 hp.2
      have hm3 := minQInt_le Q.cr2 Q.cq q1 q2 hq.1 hq.2
      unfold evalQuad
      have hB2 : (0 : ℝ) < (BSC : ℝ) ^ 2 := by norm_num [BSC]
      have hQSC : (0 : ℝ) < (QSC : ℝ) := by norm_num [QSC]
      apply div_pos _ hQSC
      have hmul : 0 < (BSC : ℝ) ^ 2 * ((Q.c0 : ℝ) + (Q.ch2 : ℝ) * h ^ 2 + (Q.ch : ℝ) * h +
          (Q.cr2 : ℝ) * (p ^ 2 + q ^ 2) + (Q.cp : ℝ) * p + (Q.cq : ℝ) * q) := by linarith
      exact pos_of_mul_pos_right hmul hB2.le

private lemma verifyOctree_sound (quads : List Quad6) (fuel : ℕ) :
    ∀ (h1 h2 p1 p2 q1 q2 : ℤ),
      verifyOctree quads fuel h1 h2 p1 p2 q1 q2 = true →
      0 ≤ p1 →
      ∀ {h p q : ℝ},
        (h1 : ℝ) / (BSC : ℝ) ≤ h → h ≤ (h2 : ℝ) / (BSC : ℝ) →
        (p1 : ℝ) / (BSC : ℝ) ≤ p → p ≤ (p2 : ℝ) / (BSC : ℝ) →
        (q1 : ℝ) / (BSC : ℝ) ≤ q → q ≤ (q2 : ℝ) / (BSC : ℝ) →
        p ^ 2 + q ^ 2 ≤ 1 / 2 → h < 42 / 100 →
        ∃ Q ∈ quads, 0 < evalQuad Q h p q := by
  induction fuel with
  | zero =>
      intro h1 h2 p1 p2 q1 q2 hok hp1 h p q hh1 hh2 hp1' hp2' hq1 hq2 hdisk hmoser
      exact checkBoxInt_sound hok hp1 ⟨hh1, hh2⟩ ⟨hp1', hp2'⟩ ⟨hq1, hq2⟩ hdisk hmoser
  | succ fuel ih =>
      intro h1 h2 p1 p2 q1 q2 hok hp1 h p q hh1 hh2 hp1' hp2' hq1 hq2 hdisk hmoser
      unfold verifyOctree at hok
      dsimp only at hok
      split_ifs at hok with hbox hdh hdp
      · exact checkBoxInt_sound hbox hp1 ⟨hh1, hh2⟩ ⟨hp1', hp2'⟩ ⟨hq1, hq2⟩ hdisk hmoser
      · rw [Bool.and_eq_true] at hok
        set hm := (h1 + h2) / 2
        by_cases hle : h ≤ (hm : ℝ) / (BSC : ℝ)
        · exact ih h1 hm p1 p2 q1 q2 hok.1 hp1 hh1 hle hp1' hp2' hq1 hq2 hdisk hmoser
        · exact ih hm h2 p1 p2 q1 q2 hok.2 hp1 (le_of_not_ge hle) hh2 hp1' hp2' hq1 hq2 hdisk hmoser
      · rw [Bool.and_eq_true] at hok
        set pm := (p1 + p2) / 2
        by_cases hle : p ≤ (pm : ℝ) / (BSC : ℝ)
        · exact ih h1 h2 p1 pm q1 q2 hok.1 hp1 hh1 hh2 hp1' hle hq1 hq2 hdisk hmoser
        · have hpm_nn : 0 ≤ pm := by
            have hp12 : p1 ≤ p2 := by
              have hB : (0 : ℝ) < (BSC : ℝ) := by norm_num [BSC]
              have : (p1 : ℝ) / (BSC : ℝ) ≤ (p2 : ℝ) / (BSC : ℝ) := le_trans hp1' hp2'
              have : (p1 : ℝ) ≤ (p2 : ℝ) := (div_le_div_iff_of_pos_right hB).mp this
              exact_mod_cast this
            omega
          exact ih h1 h2 pm p2 q1 q2 hok.2 hpm_nn hh1 hh2 (le_of_not_ge hle) hp2' hq1 hq2 hdisk hmoser
      · rw [Bool.and_eq_true] at hok
        set qm := (q1 + q2) / 2
        by_cases hle : q ≤ (qm : ℝ) / (BSC : ℝ)
        · exact ih h1 h2 p1 p2 q1 qm hok.1 hp1 hh1 hh2 hp1' hp2' hq1 hle hdisk hmoser
        · exact ih h1 h2 p1 p2 qm q2 hok.2 hp1 hh1 hh2 hp1' hp2' (le_of_not_ge hle) hq2 hdisk hmoser

private lemma octree_ok :
    verifyOctree verifiedQuads 25 0 1792 0 3072 (-3072) 3072 = true := by
  set_option maxRecDepth 200000 in decide +kernel

end OMA.White2022H1

open OMA.White2022H1 in
theorem OMA.msl_closed_H1 : OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1.H1 := by
  intro f hfm hf hfint
  by_contra hlt
  push Not at hlt
  have hM_le : ∀ x : ℝ, MFun f x ≤ (379005 : ℝ) / 1000000 := fun x => by
    have := hlt x
    unfold MFun gFun
    norm_num at this ⊢
    exact this.le
  -- Step 1: Symmetry reduction to 0 ≤ EM f₁ and 0 ≤ c1Val f₂
  obtain ⟨f₁, hfm₁, hf₁, hfint₁, hM₁, hEM₁⟩ :
      ∃ f₁ : ℝ → ℝ, Measurable f₁ ∧ (∀ t, 0 ≤ f₁ t ∧ f₁ t ≤ 1) ∧
        (∫ t in (-1 : ℝ)..1, f₁ t) = 1 ∧ (∀ x, MFun f₁ x ≤ (379005 : ℝ) / 1000000) ∧
        0 ≤ EM f₁ := by
    by_cases h0 : 0 ≤ EM f
    · exact ⟨f, hfm, hf, hfint, hM_le, h0⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := symm_neg hfm hf hfint
      exact ⟨fun t => f (-t), h1, h2, h3, fun x => by rw [h4 x]; exact hM_le (-x), by linarith⟩
  obtain ⟨f₂, hfm₂, hf₂, hfint₂, hM₂, hEM₂, hc1₂⟩ :
      ∃ f₂ : ℝ → ℝ, Measurable f₂ ∧ (∀ t, 0 ≤ f₂ t ∧ f₂ t ≤ 1) ∧
        (∫ t in (-1 : ℝ)..1, f₂ t) = 1 ∧ (∀ x, MFun f₂ x ≤ (379005 : ℝ) / 1000000) ∧
        0 ≤ EM f₂ ∧ 0 ≤ c1Val f₂ := by
    by_cases h0 : 0 ≤ c1Val f₁
    · exact ⟨f₁, hfm₁, hf₁, hfint₁, hM₁, hEM₁, h0⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := symm_comp_neg hfm₁ hf₁ hfint₁
      exact ⟨fun t => 1 - f₁ (-t), h1, h2, h3, fun x => by rw [h4 x]; exact hM₁ x,
        by linarith, by linarith⟩
  -- Step 2: Moser handles EM f₂ ≥ 0.42
  by_cases hE42 : (42 : ℝ) / 100 ≤ EM f₂
  · exact moser_contradiction hfm₂ hf₂ hfint₂ hM₂ hE42
  push Not at hE42
  -- Step 3: Bessel gives c1^2 + d1^2 ≤ 1/2, hence c1 ≤ 3072/4096 and |d1| ≤ 3072/4096
  have hdisk : (c1Val f₂) ^ 2 + (d1Val f₂) ^ 2 ≤ 1 / 2 := bessel_c1_d1 hfm₂ hf₂
  have hc1_hi : c1Val f₂ ≤ (3072 : ℝ) / (BSC : ℝ) := by
    have : (c1Val f₂) ^ 2 ≤ ((3072 : ℝ) / (BSC : ℝ)) ^ 2 := by
      norm_num [BSC]; nlinarith [sq_nonneg (d1Val f₂)]
    norm_num [BSC] at this ⊢; nlinarith
  have hd1_lo : ((-3072 : ℤ) : ℝ) / (BSC : ℝ) ≤ d1Val f₂ := by
    have : (d1Val f₂) ^ 2 ≤ ((3072 : ℝ) / (BSC : ℝ)) ^ 2 := by
      norm_num [BSC]; nlinarith [sq_nonneg (c1Val f₂)]
    push_cast; norm_num [BSC] at this ⊢; nlinarith
  have hd1_hi : d1Val f₂ ≤ (3072 : ℝ) / (BSC : ℝ) := by
    have : (d1Val f₂) ^ 2 ≤ ((3072 : ℝ) / (BSC : ℝ)) ^ 2 := by
      norm_num [BSC]; nlinarith [sq_nonneg (c1Val f₂)]
    norm_num [BSC] at this ⊢; nlinarith
  -- Step 4: Octree gives one of the 7 verified quadratics > 0
  obtain ⟨Q, hQmem, hQpos⟩ := verifyOctree_sound verifiedQuads 25 0 1792 0 3072 (-3072) 3072
    octree_ok le_rfl
    (by simp [hEM₂]) (by norm_num [BSC]; linarith)
    (by simp [hc1₂]) hc1_hi hd1_lo hd1_hi hdisk hE42
  -- Step 5: Each of the 7 quadratics is ≤ 0 by certC0Int_sound!
  simp only [verifiedQuads, List.mem_cons, List.not_mem_nil, or_false] at hQmem
  rcases hQmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hq := certC0Int_sound hfm₂ hf₂ hfint₂ hM₂ cert0 (by decide) (by decide) (-63353) cert0_ok
    dsimp only [cert0] at hq; norm_num at hq; linarith
  · have hq := certC0Int_sound hfm₂ hf₂ hfint₂ hM₂ cert1 (by decide) (by decide) 178046 cert1_ok
    dsimp only [cert1] at hq; norm_num at hq; linarith
  · have hq := certC0Int_sound hfm₂ hf₂ hfint₂ hM₂ cert2 (by decide) (by decide) 279589 cert2_ok
    dsimp only [cert2] at hq; norm_num at hq; linarith
  · have hq := certC0Int_sound hfm₂ hf₂ hfint₂ hM₂ cert3 (by decide) (by decide) (-728707) cert3_ok
    dsimp only [cert3] at hq; norm_num at hq; linarith
  · have hq := certC0Int_sound hfm₂ hf₂ hfint₂ hM₂ cert4 (by decide) (by decide) (-589500) cert4_ok
    dsimp only [cert4] at hq; norm_num at hq; linarith
  · have hq := certC0Int_sound hfm₂ hf₂ hfint₂ hM₂ cert5 (by decide) (by decide) (-537894) cert5_ok
    dsimp only [cert5] at hq; norm_num at hq; linarith
  · have hq := certC0Int_sound hfm₂ hf₂ hfint₂ hM₂ cert6 (by decide) (by decide) (-544616) cert6_ok
    dsimp only [cert6] at hq; norm_num at hq; linarith


-- ACCEPTED SOURCE: Erdos36.minimum_overlap.variants.lower.white_2022.R1.H2

/-! Write y = k + t with k the floor of y. A pair with difference d contributes 1 - t when d = k,
t when d = k + 1, and 0 otherwise, so the sum is a convex combination of two overlap counts. -/

theorem OMA.msl_closed_H2 : OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1.H2 := by
  intro A B y
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ⌊y⌋ := ⟨_, rfl⟩
  have hky : (k : ℝ) ≤ y := hk ▸ Int.floor_le y
  have hyk : y < k + 1 := hk ▸ Int.lt_floor_add_one y
  have key : ∀ d : ℤ, max 0 (1 - |(d : ℝ) - y|) ≤
      (if d = k then 1 - (y - k) else 0) + (if d = k + 1 then y - k else 0) := by
    intro d
    rcases lt_trichotomy d k with h | h | h
    · have h1 : d ≠ k := by omega
      have h2 : d ≠ k + 1 := by omega
      have hd : (d : ℝ) ≤ k - 1 := by
        have : d ≤ k - 1 := by omega
        exact_mod_cast this
      rw [if_neg h1, if_neg h2, add_zero]
      refine max_le le_rfl ?_
      have : 1 ≤ |(d : ℝ) - y| := by
        rw [abs_sub_comm]; exact le_abs.mpr (Or.inl (by linarith))
      linarith
    · subst h
      have h2 : d ≠ d + 1 := by omega
      rw [if_pos rfl, if_neg h2, add_zero, abs_sub_comm, abs_of_nonneg (by linarith)]
      exact max_le (by linarith) le_rfl
    · rcases (show d = k + 1 ∨ k + 2 ≤ d by omega) with h2 | h2
      · subst h2
        have h1 : k + 1 ≠ k := by omega
        rw [if_neg h1, if_pos rfl, zero_add]
        push_cast
        rw [abs_of_nonneg (by linarith)]
        exact max_le (by linarith) (by linarith)
      · have h1 : d ≠ k := by omega
        have h3 : d ≠ k + 1 := by omega
        have hd : (k : ℝ) + 2 ≤ d := by exact_mod_cast h2
        rw [if_neg h1, if_neg h3, add_zero]
        refine max_le le_rfl ?_
        have : 1 ≤ |(d : ℝ) - y| := le_abs.mpr (Or.inl (by linarith))
        linarith
  have hbdd : BddAbove (Set.range (Erdos36.Overlap A B)) := by
    refine ⟨(A ×ˢ B).card, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact Finset.card_filter_le _ _
  have hO : ∀ j, (Erdos36.Overlap A B j : ℝ) ≤ (Erdos36.MaxOverlap A B : ℝ) := fun j => by
    exact_mod_cast le_ciSup hbdd j
  have hcard : ∀ j : ℤ, (((A ×ˢ B).filter (fun p : ℤ × ℤ => p.2 - p.1 = j)).card : ℝ)
      = (Erdos36.Overlap A B (-j) : ℝ) := by
    intro j
    congr 1
    unfold Erdos36.Overlap
    congr 1
    refine Finset.filter_congr ?_
    rintro ⟨a, b⟩ _
    simp only
    omega
  calc ∑ p ∈ A ×ˢ B, max 0 (1 - |((p.2 - p.1 : ℤ) : ℝ) - y|)
      ≤ ∑ p ∈ A ×ˢ B, ((if p.2 - p.1 = k then 1 - (y - k) else 0) +
          (if p.2 - p.1 = k + 1 then y - k else 0)) :=
        Finset.sum_le_sum fun p _ => key (p.2 - p.1)
    _ = (1 - (y - k)) * (((A ×ˢ B).filter (fun p : ℤ × ℤ => p.2 - p.1 = k)).card : ℝ) +
          (y - k) * (((A ×ˢ B).filter (fun p : ℤ × ℤ => p.2 - p.1 = k + 1)).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (1 - (y - k)) * (Erdos36.MaxOverlap A B : ℝ) + (y - k) * (Erdos36.MaxOverlap A B : ℝ) := by
        rw [hcard, hcard]
        have e1 : 0 ≤ 1 - (y - k) := by linarith
        have e2 : 0 ≤ y - k := by linarith
        exact add_le_add (mul_le_mul_of_nonneg_left (hO _) e1) (mul_le_mul_of_nonneg_left (hO _) e2)
    _ = (Erdos36.MaxOverlap A B : ℝ) := by ring


-- ACCEPTED SOURCE: Erdos36.minimum_overlap.variants.lower.white_2022.R1.H3

-- Step Erdos36.minimum_overlap.variants.lower.white_2022.R1.H3: hypothesis H3 of reduction Erdos36.minimum_overlap.variants.lower.white_2022.R1
-- Credit: @ivillar
-- The step function is 1 on the cells ((a-1)/n - 1, a/n - 1] with a in A. Its overlap integrand is bounded by the indicators of the pairwise cell intersections, whose lengths are the tent values divided by n.

namespace WhiteStep

open MeasureTheory

noncomputable def lo (n : ℕ) (a : ℤ) : ℝ := ((a : ℝ) - 1) / n - 1

noncomputable def hi (n : ℕ) (a : ℤ) : ℝ := (a : ℝ) / n - 1

lemma ceil_eq_iff_mem {n : ℕ} (hn : 0 < n) (a : ℤ) (t : ℝ) :
    ⌈(n : ℝ) * (t + 1)⌉ = a ↔ t ∈ Set.Ioc (lo n a) (hi n a) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Int.ceil_eq_iff, Set.mem_Ioc]
  unfold lo hi
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hN]
      nlinarith
    · rw [le_sub_iff_add_le, le_div_iff₀ hN]
      nlinarith
  · rintro ⟨h1, h2⟩
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hN] at h1
    rw [le_sub_iff_add_le, le_div_iff₀ hN] at h2
    constructor <;> nlinarith

lemma tent_eq {n : ℕ} (hn : 0 < n) (a b : ℤ) (x : ℝ) :
    max (min (hi n a) (hi n b - x) - max (lo n a) (lo n b - x)) 0 =
      max 0 (1 - |((b - a : ℤ) : ℝ) - n * x|) / n := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : hi n b - x = hi n a + (((b - a : ℤ) : ℝ) - n * x) / n := by
    unfold hi
    push_cast
    field_simp
    ring
  have e2 : lo n b - x = lo n a + (((b - a : ℤ) : ℝ) - n * x) / n := by
    unfold lo
    push_cast
    field_simp
    ring
  have e3 : hi n a - lo n a = 1 / n := by
    unfold hi lo
    field_simp
    ring
  rw [e1, e2]
  generalize (((b - a : ℤ) : ℝ) - n * x) = u
  have key : min (hi n a) (hi n a + u / n) - max (lo n a) (lo n a + u / n) = (1 - |u|) / n := by
    rcases le_total 0 u with h | h
    · have h' : 0 ≤ u / n := div_nonneg h hN.le
      rw [min_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg h, sub_div]
      linarith
    · have h' : u / n ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hN.le
      rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos h, sub_div, neg_div]
      linarith
  rw [key]
  rcases le_total 0 (1 - |u|) with h | h
  · rw [max_eq_left (div_nonneg h hN.le), max_eq_right h]
  · rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg h hN.le), max_eq_left h, zero_div]

end WhiteStep

open MeasureTheory WhiteStep OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1

theorem OMA.msl_closed_H3 : OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1.H3 := by
  intro n hn A B hd hu hc
  classical
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hAn : A.card = n := card_left hd hu hc
  have hmemA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ 2 * (n : ℤ) := by
    intro a ha
    have h1 : a ∈ Finset.Icc (1 : ℤ) (2 * n) := hu ▸ Finset.mem_union_left B ha
    exact Finset.mem_Icc.mp h1
  let f : ℝ → ℝ := fun t => if ⌈(n : ℝ) * (t + 1)⌉ ∈ A then 1 else 0
  have hf01 : ∀ t, 0 ≤ f t ∧ f t ≤ 1 := by
    intro t
    simp only [f]
    split_ifs <;> norm_num
  have hfm : Measurable f := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (Int.measurable_ceil.comp (measurable_const.mul (measurable_id.add_const 1)))
      (Finset.measurableSet A)
  have hfsum : ∀ t, f t = ∑ a ∈ A, (Set.Ioc (lo n a) (hi n a)).indicator (1 : ℝ → ℝ) t := by
    intro t
    have h1 : f t = ∑ a ∈ A, if ⌈(n : ℝ) * (t + 1)⌉ = a then (1 : ℝ) else 0 :=
      (Finset.sum_ite_eq A _ (fun _ => (1 : ℝ))).symm
    rw [h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : ⌈(n : ℝ) * (t + 1)⌉ = a
    · rw [if_pos h, Set.indicator_of_mem ((ceil_eq_iff_mem hn a t).mp h)]
      rfl
    · rw [if_neg h, Set.indicator_of_notMem (fun h' => h ((ceil_eq_iff_mem hn a t).mpr h'))]
  refine ⟨f, hfm, hf01, ?_, ?_⟩
  · rw [intervalIntegral.integral_of_le (by norm_num)]
    have hcell : ∀ a ∈ A, ∫ t in Set.Ioc (-1 : ℝ) 1,
        (Set.Ioc (lo n a) (hi n a)).indicator (1 : ℝ → ℝ) t = 1 / n := by
      intro a ha
      obtain ⟨h1, h2⟩ := hmemA a ha
      have h3 : (-1 : ℝ) ≤ lo n a := by
        unfold lo
        have h4 : (0 : ℝ) ≤ ((a : ℝ) - 1) / n :=
          div_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ a - 1)) hN.le
        linarith
      have h5 : hi n a ≤ 1 := by
        unfold hi
        have h6 : (a : ℝ) / n ≤ 2 := by
          rw [div_le_iff₀ hN]
          exact_mod_cast h2
        linarith
      rw [setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_right.mpr (Set.Ioc_subset_Ioc h3 h5)]
      simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]
      rw [Real.volume_real_Ioc_of_le (by unfold lo hi; rw [sub_le_sub_iff_right]; gcongr; linarith)]
      unfold hi lo
      field_simp
      ring
    have hint : ∀ a ∈ A, Integrable
        (fun t => (Set.Ioc (lo n a) (hi n a)).indicator (1 : ℝ → ℝ) t)
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
      fun a _ => (integrable_const (1 : ℝ)).indicator measurableSet_Ioc
    rw [show (fun t => f t) = fun t => ∑ a ∈ A,
        (Set.Ioc (lo n a) (hi n a)).indicator (1 : ℝ → ℝ) t from funext hfsum,
      integral_finsetSum _ hint, Finset.sum_congr rfl hcell, Finset.sum_const, hAn,
      nsmul_eq_mul]
    field_simp
  · intro x
    rw [intervalIntegral.integral_of_le (by norm_num)]
    let S : ℤ × ℤ → Set ℝ := fun p =>
      Set.Ioc (max (lo n p.1) (lo n p.2 - x)) (min (hi n p.1) (hi n p.2 - x))
    let F : ℝ → ℝ := fun t => (∑ p ∈ A ×ˢ B, (S p).indicator (1 : ℝ → ℝ) t) +
      ({-1 - x} : Set ℝ).indicator (1 : ℝ → ℝ) t
    have hF0 : ∀ t, 0 ≤ F t := by
      intro t
      refine add_nonneg (Finset.sum_nonneg fun p _ => ?_) ?_ <;>
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hSi : ∀ p : ℤ × ℤ, Integrable (fun t => (S p).indicator (1 : ℝ → ℝ) t) := fun p =>
      (integrableOn_const (by simp [S])).integrable_indicator measurableSet_Ioc
    have hPi : Integrable (fun t => ({-1 - x} : Set ℝ).indicator (1 : ℝ → ℝ) t) :=
      (integrableOn_const (by simp)).integrable_indicator (measurableSet_singleton _)
    have hFi : Integrable F := (integrable_finsetSum _ fun p _ => hSi p).add hPi
    have hpt : ∀ t, f t * (Set.Icc (-1 : ℝ) 1).indicator (fun y => 1 - f y) (x + t) ≤ F t := by
      intro t
      by_cases hft : ⌈(n : ℝ) * (t + 1)⌉ ∈ A
      · have hf1 : f t = 1 := if_pos hft
        rw [hf1, one_mul]
        by_cases hmem : x + t ∈ Set.Icc (-1 : ℝ) 1
        · rw [Set.indicator_of_mem hmem]
          by_cases hfx : ⌈(n : ℝ) * (x + t + 1)⌉ ∈ A
          · have : f (x + t) = 1 := if_pos hfx
            rw [this, sub_self]
            exact hF0 t
          · have : f (x + t) = 0 := if_neg hfx
            rw [this, sub_zero]
            by_cases hend : x + t = -1
            · have h1 : t ∈ ({-1 - x} : Set ℝ) := by
                rw [Set.mem_singleton_iff]
                linarith
              have h2 : (1 : ℝ) ≤ ({-1 - x} : Set ℝ).indicator (1 : ℝ → ℝ) t := by
                rw [Set.indicator_of_mem h1]
                rfl
              have h3 : 0 ≤ ∑ p ∈ A ×ˢ B, (S p).indicator (1 : ℝ → ℝ) t :=
                Finset.sum_nonneg fun p _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
              simp only [F]
              linarith
            · have hlt : -1 < x + t := lt_of_le_of_ne hmem.1 (Ne.symm hend)
              have hb1 : 1 ≤ ⌈(n : ℝ) * (x + t + 1)⌉ := by
                have : (0 : ℝ) < (n : ℝ) * (x + t + 1) := mul_pos hN (by linarith)
                exact Int.one_le_ceil_iff.mpr this
              have hb2 : ⌈(n : ℝ) * (x + t + 1)⌉ ≤ 2 * (n : ℤ) := by
                rw [Int.ceil_le]
                push_cast
                nlinarith [hmem.2]
              have hbB : ⌈(n : ℝ) * (x + t + 1)⌉ ∈ B := by
                have h1 : ⌈(n : ℝ) * (x + t + 1)⌉ ∈ A ∪ B := by
                  rw [hu]
                  exact Finset.mem_Icc.mpr ⟨hb1, hb2⟩
                rcases Finset.mem_union.mp h1 with h | h
                · exact absurd h hfx
                · exact h
              have hp : (⌈(n : ℝ) * (t + 1)⌉, ⌈(n : ℝ) * (x + t + 1)⌉) ∈ A ×ˢ B :=
                Finset.mem_product.mpr ⟨hft, hbB⟩
              have hta := (ceil_eq_iff_mem hn _ t).mp rfl
              have htb := (ceil_eq_iff_mem hn _ (x + t)).mp rfl
              have hmemS : t ∈ S (⌈(n : ℝ) * (t + 1)⌉, ⌈(n : ℝ) * (x + t + 1)⌉) := by
                simp only [S, Set.mem_Ioc, max_lt_iff, le_min_iff]
                refine ⟨⟨hta.1, ?_⟩, hta.2, ?_⟩
                · linarith [htb.1]
                · linarith [htb.2]
              have h2 : (1 : ℝ) ≤ ∑ p ∈ A ×ˢ B, (S p).indicator (1 : ℝ → ℝ) t := by
                have h3 := Finset.single_le_sum
                  (f := fun p => (S p).indicator (1 : ℝ → ℝ) t)
                  (fun p _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) hp
                rw [Set.indicator_of_mem hmemS] at h3
                exact h3
              have h4 : 0 ≤ ({-1 - x} : Set ℝ).indicator (1 : ℝ → ℝ) t :=
                Set.indicator_nonneg (fun _ _ => zero_le_one) _
              simp only [F]
              linarith
        · rw [Set.indicator_of_notMem hmem]
          exact hF0 t
      · have hf0 : f t = 0 := if_neg hft
        rw [hf0, zero_mul]
        exact hF0 t
    have hnn : ∀ t, 0 ≤ f t * (Set.Icc (-1 : ℝ) 1).indicator (fun y => 1 - f y) (x + t) := by
      intro t
      refine mul_nonneg (hf01 t).1 (Set.indicator_nonneg (fun y _ => ?_) _)
      linarith [(hf01 y).2]
    calc ∫ t in Set.Ioc (-1 : ℝ) 1,
          f t * (Set.Icc (-1 : ℝ) 1).indicator (fun y => 1 - f y) (x + t)
        ≤ ∫ t in Set.Ioc (-1 : ℝ) 1, F t :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hFi.integrableOn
            (Filter.Eventually.of_forall hpt)
      _ ≤ ∫ t, F t := setIntegral_le_integral hFi (Filter.Eventually.of_forall hF0)
      _ = ∑ p ∈ A ×ˢ B, volume.real (S p) + volume.real ({-1 - x} : Set ℝ) := by
          simp only [F]
          rw [integral_add (integrable_finsetSum _ fun p _ => hSi p) hPi,
            integral_finsetSum _ (fun p _ => hSi p),
            integral_indicator_one (measurableSet_singleton _)]
          congr 1
          exact Finset.sum_congr rfl fun p _ => integral_indicator_one measurableSet_Ioc
      _ = (∑ p ∈ A ×ˢ B, max 0 (1 - |((p.2 - p.1 : ℤ) : ℝ) - n * x|)) / n := by
          have hs0 : volume.real ({-1 - x} : Set ℝ) = 0 := by
            rw [measureReal_def, Real.volume_singleton, ENNReal.toReal_zero]
          rw [hs0, add_zero, Finset.sum_div]
          exact Finset.sum_congr rfl fun p _ =>
            Real.volume_real_Ioc.trans (tent_eq hn p.1 p.2 x)


theorem OMA.solution : type_of% @Erdos36.minimum_overlap.variants.lower.white_2022 := by
  exact OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1.main OMA.msl_closed_H1 OMA.msl_closed_H2 OMA.msl_closed_H3
