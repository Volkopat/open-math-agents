import FormalConjectures.ErdosProblems.«321»
import Mathlib

/-!
# The order of the largest reciprocal-dissociated subset of [1,N]

Every subset of an extremal family gives a different reciprocal sum, so
its cardinality times log 2 is at most log S(N). In the other direction,
the BGMS independent denominators are simultaneously admissible. Bounds
for these two counts give the same stopped iterated-logarithm product.

Credit: @yuka30240 for the reduction of the extremal cardinality to the
independent-denominator count and the total number of reciprocal subset sums,
and for integrating the following proofs in Lean 4.33.1. The problem 321 arguments and the
explicit answer are collected at the end of this file.

The mathematical bounds are due to Bettin, Grenié, Molteni and Sanna (lower
bound, arXiv:2509.10030), and Luo, Yang and Zhu (upper bound, Distinct Harmonic
Subset Sums). The analytic and combinatorial arguments for problem 320 are
adapted under Apache-2.0 from the project directed by Riley Sturgill, with
Jensen Kohlmeyer credited as project co-author. The project records its
AI-assisted implementation in ATTRIBUTION.md.
https://github.com/rsturg/erdos-320-lean/tree/8df8493d0b05c72cace943f44c4971bf70999b4a

The quantitative prime number theorem is taken from @sobrien032's 4.33.1
port in proofs/Erdos454.erdos_454.R1.H1.lean (PR #12333, commit 9ffb0a57d63c).
It adapts PrimeNumberTheoremAnd by Alex Kontorovich, Terence Tao and contributors,
commit 2c476fa6441c607096d93c8fc7ac0a227a655dae. The source of the port
also credits Rivka Lipkovitz's Erdős 878 formalization. Both are Apache-2.0.
Auxiliary.lean: Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


section PNT_Support

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function

end PNT_Support

section PNT_Basic

open Filter Real

theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end PNT_Basic

section PNT_Auxiliary

namespace Complex

lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt ofReal 1 x :=
  HasDerivAt.ofReal_comp <| hasDerivAt_id x

lemma differentiableAt_ofReal (x : ℝ) : DifferentiableAt ℝ ofReal x :=
  (hasDerivAt_ofReal x).differentiableAt

end Complex

lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

lemma deriv.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    deriv (fun x : ℝ ↦ e x) z = deriv e z :=
  hf.hasDerivAt.comp_ofReal.deriv

lemma DifferentiableAt.ofReal_comp {z : ℝ} {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z :=
  hf.hasDerivAt.ofReal_comp.differentiableAt

open Complex ContinuousLinearMap in
lemma HasDerivAt.of_hasDerivAt_ofReal_comp {z : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hf : HasDerivAt (fun y ↦ (f y : ℂ)) u z) :
    ∃ u' : ℝ, u = u' ∧ HasDerivAt f u' z := by
  lift u to ℝ
  · have H := (imCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt.deriv
    simp only [Function.comp_def, imCLM_apply, ofReal_im, deriv_const] at H
    rwa [eq_comm, comp_apply, imCLM_apply, toSpanSingleton_apply_one] at H
  refine ⟨u, rfl, ?_⟩
  convert! (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt
  rw [comp_apply, toSpanSingleton_apply_one, reCLM_apply, ofReal_re]

lemma DifferentiableAt.ofReal_comp_iff {z : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by
  refine ⟨fun H ↦ ?_, ofReal_comp⟩
  obtain ⟨u, _, hu₂⟩ := H.hasDerivAt.of_hasDerivAt_ofReal_comp
  exact HasDerivAt.differentiableAt hu₂

lemma Differentiable.ofReal_comp_iff {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.ofReal_comp_iff

lemma deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) ↦ (f y : ℂ)) z = deriv f z := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf' := mt DifferentiableAt.ofReal_comp_iff.mp hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]

end PNT_Auxiliary

section PNT_ZetaConj

open scoped Complex ComplexConjugate

theorem deriv_conj_conj' (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  trans deriv (conj ∘ f ∘ conj) (conj p)
  · rfl
  simp

theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  simp [← deriv_conj_conj']

theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_conj, ← RCLike.conj_smul,
    ← intervalIntegral.intervalIntegral_eq_integral_uIoc]

end PNT_ZetaConj

section PNT_EulerMaclaurin

open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  have := aestronglyMeasurable_B1
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring

end PNT_EulerMaclaurin

section PNT_Fourier

open Complex

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

end PNT_Fourier

section PNT_Rectangle

open Complex Set Topology

open scoped Interval

def RectangleBorder (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

theorem Set.left_not_mem_uIoo {a b : ℝ} : a ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (left_lt_sup.mp h2) (le_of_not_ge (inf_lt_left.mp h1))

theorem Set.right_not_mem_uIoo {a b : ℝ} : b ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (right_lt_sup.mp h2) (le_of_not_ge (inf_lt_right.mp h1))

theorem Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h ↦ Set.left_not_mem_uIoo (h ▸ hc)

theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h ↦ Set.right_not_mem_uIoo (h ▸ hc)

lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩

lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [RectangleBorder, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩,
    fun hc ↦ h.2.1 hc.1⟩

lemma rectangle_mem_nhds_iff {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]

lemma mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

lemma mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]

theorem not_mem_rectangleBorder_of_rectangle_mem_nhds {z w p : ℂ}
    (hp : Rectangle z w ∈ 𝓝 p) :
    p ∉ RectangleBorder z w := by
  refine Set.disjoint_right.mp (rectangleBorder_disjoint_singleton ?_) rfl
  have h1 := rectangle_mem_nhds_iff.mp hp
  exact ⟨Set.ne_left_of_mem_uIoo h1.1, Set.ne_right_of_mem_uIoo h1.1,
    Set.ne_left_of_mem_uIoo h1.2, Set.ne_right_of_mem_uIoo h1.2⟩

end PNT_Rectangle

section PNT_ResidueCalcOnRectangles

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)

noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w

noncomputable def VerticalIntegral (f : ℂ → E) (σ : ℝ) : E :=
    I • ∫ t : ℝ, f (σ + t * I)

noncomputable abbrev VerticalIntegral' (f : ℂ → E) (σ : ℝ) : E :=
    (1 / (2 * π * I)) • VerticalIntegral f σ

lemma verticalIntegral_split_three (a b : ℝ)
    (hf : Integrable (fun t : ℝ ↦ f (σ + t * I))) :
    VerticalIntegral f σ =
      I • (∫ t in Iic a, f (σ + t * I)) + VIntegral f σ a b +
      I • ∫ t in Ici b, f (σ + t * I) := by
  simp_rw [VerticalIntegral, VIntegral, ← smul_add]
  congr
  rw [← integral_Iic_sub_Iic hf.restrict hf.restrict, add_sub_cancel,
    integral_Iic_eq_integral_Iio, integral_Iio_add_Ici hf.restrict hf.restrict]

abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s

theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩

theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)

theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral VIntegral
  congrm ?_ - ?_ + I • ?_ - I • ?_ <;> refine integral_congr fun t ht ↦ h ?_
  exacts [mapsTo_rectangleBorder_left_im z w ht, mapsTo_rectangleBorder_right_im z w ht,
    mapsTo_rectangleBorder_right_re z w ht, mapsTo_rectangleBorder_left_re z w ht]

theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]

def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderIntegrable (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  ContinuousOn.rectangleBorder_integrable (hf.mono (rectangleBorder_subset_rectangle z w))

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderNoPIntegrable
    (hf : ContinuousOn f (Rectangle z w \ {p})) (pNotOnBorder : p ∉ RectangleBorder z w) :
    RectangleBorderIntegrable f z w := by
  refine ContinuousOn.rectangleBorder_integrable (hf.mono (Set.subset_sdiff.mpr ?_))
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

theorem HolomorphicOn.rectangleBorderIntegrable'
    (hf : HolomorphicOn f (Rectangle z w \ {p})) (hp : Rectangle z w ∈ nhds p) :
    RectangleBorderIntegrable f z w :=
  hf.continuousOn.rectangleBorderNoPIntegrable (not_mem_rectangleBorder_of_rectangle_mem_nhds hp)

theorem HolomorphicOn.rectangleBorderIntegrable (hf : HolomorphicOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := hf.continuousOn.rectangleBorderIntegrable

theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]

lemma Complex.inv_re_add_im : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring

lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]

lemma continuous_self_div_sq_add_sq (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)

lemma integral_self_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert! (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)

lemma integral_const_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring

lemma integral_const_div_self_add_im (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [inv_re_add_im]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]

lemma integral_const_div_re_add_self (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : x + y * I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : y + I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]

lemma ResidueTheoremAtOrigin' {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
  rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, arctan_neg, ofReal_neg,
    sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf

theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  simp only [rectangle_mem_nhds_iff, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm,
    mem_reProdIm, mem_Ioo] at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * I) * (2 * I * ↑π * c) = c := by
    field_simp
  rwa [ResidueTheoremAtOrigin']
  all_goals simp [*]

lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have hp := not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior
  have : Set.EqOn f (g + fun s ↦ A / (s - p)) (RectangleBorder z w) := fun s hs ↦ by
    rw [Pi.add_apply, ← principalPart ⟨rectangleBorder_subset_rectangle z w hs, by
      rintro rfl; exact hp hs⟩, Pi.sub_apply, sub_add_cancel]
  have t : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := fun s hs ↦
    ((differentiableAt_const A).div (differentiableAt_id.sub_const p)
      (sub_ne_zero.mpr hs.2)).differentiableWithinAt
  rw [RectangleIntegral'_congr this, RectangleIntegral', RectangleBorderIntegrable.add
    gHolo.rectangleBorderIntegrable (t.rectangleBorderIntegrable' pInRectInterior), smul_add,
    gHolo.vanishesOnRectangle subset_rfl, smul_zero, zero_add]
  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior

lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  obtain ⟨c, hc⟩ := f_near_p.bound
  obtain ⟨U, hU, hpU, h⟩ := mem_nhdsWithin.mp hc
  refine ⟨U, hU.mem_nhds hpU, c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  simpa using h hx

theorem BddAbove_on_rectangle_of_bdd_near {z w p : ℂ} {f : ℂ → ℂ}
    (f_cont : ContinuousOn f (Rectangle z w \ {p}))
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    BddAbove (norm ∘ f '' (Rectangle z w \ {p})) := by
  obtain ⟨V, hV, hb⟩ := IsBigO_to_BddAbove f_near_p
  obtain ⟨W, hWV, hW, hpW⟩ := mem_nhds_iff.mp hV
  have hK : IsCompact (Rectangle z w \ W) := (isCompact_uIcc.reProdIm isCompact_uIcc).diff hW
  refine ((hK.bddAbove_image (f_cont.norm.mono fun x hx ↦ ⟨hx.1, by rintro rfl; exact hx.2 hpW⟩)).union
    hb).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  by_cases h : x ∈ W
  exacts [Or.inr ⟨x, ⟨hWV h, hx.2⟩, rfl⟩, Or.inl ⟨x, ⟨hx.1, h⟩, rfl⟩]

theorem ResidueTheoremOnRectangleWithSimplePole' {f : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (fHolo : HolomorphicOn f (Rectangle z w \ {p}))
    (near_p : (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = A := by
  have gHolo : HolomorphicOn (f - fun s ↦ A / (s - p)) (Rectangle z w \ {p}) :=
    fHolo.sub fun s hs ↦ DifferentiableWithinAt.div (by fun_prop) (by fun_prop) (sub_ne_zero.mpr hs.2)
  obtain ⟨h, hHolo, hEq⟩ := existsDifferentiableOn_of_bddAbove pInRectInterior gHolo
    (BddAbove_on_rectangle_of_bdd_near gHolo.continuousOn near_p)
  exact ResidueTheoremOnRectangleWithSimplePole zRe_le_wRe zIm_le_wIm pInRectInterior hHolo hEq

end PNT_ResidueCalcOnRectangles
section PNT_ZetaBounds
open Complex Topology Filter Interval Set Asymptotics MeasureTheory
lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]
lemma one_div_cpow_eq_cpow_neg (x s : ℂ) : 1 / x ^ s = x ^ (-s) := by
  convert div_cpow_eq_cpow_neg 1 x s using 1; simp
lemma div_rpow_eq_rpow_neg (a x s : ℝ) (hx : 0 ≤ x) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, Real.rpow_neg hx]
lemma div_rpow_neg_eq_rpow_div {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (-s) / y ^ (-s) = (y / x) ^ s := by
  rw [div_eq_mul_inv, Real.rpow_neg hx, Real.rpow_neg hy, Real.div_rpow hy hx]; field_simp
lemma div_rpow_eq_rpow_div_neg {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ s / y ^ s = (y / x) ^ (-s) := by
  convert div_rpow_neg_eq_rpow_div (s := -s) hx hy using 1; simp only [neg_neg]
theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds s_ne_one] with z hz using differentiableAt_riemannZeta hz
theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ (deriv riemannZeta) s := by
  exact (analyticAt_riemannZeta s_ne_one).deriv.differentiableAt
theorem ResidueMult {f g : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (g_holc : HolomorphicOn g U) (U_in_nhds : U ∈ 𝓝 p) {A : ℂ}
    (f_near_p : (f - (fun s ↦ A * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    (f * g - (fun s ↦ A * g p * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have : (f * g - fun s ↦ A * g p * (s - p)⁻¹)
      = (f - A • fun s ↦ (s - p)⁻¹) * g + fun s ↦ (A * (g s - g p) / (s - p)) := by
    ext; simp; ring
  rw[this]
  have p_in_U : p ∈ U := mem_of_mem_nhds U_in_nhds
  refine Asymptotics.IsBigO.add ?_ ?_
  · rw[← mul_one (1 : ℂ → ℂ)]
    refine Asymptotics.IsBigO.mul f_near_p ?_
    have g_cont : ContinuousAt g p := by
      exact (g_holc.continuousOn.continuousWithinAt p_in_U).continuousAt U_in_nhds
    have := g_cont.norm.isBoundedUnder_le.isBigO_one ℂ
    exact IsBigO.mono this inf_le_left
  ·
    suffices (fun s ↦ A * ((s - p)⁻¹ * (g s - g p))) =O[𝓝[≠] p] 1 by
      convert! this using 2
      rw[div_eq_mul_inv]
      ring
    apply Asymptotics.IsBigO.const_mul_left
    have g_diff : HasDerivAt g (deriv g p) p :=
        (DifferentiableOn.differentiableAt g_holc U_in_nhds).hasDerivAt
    rw [hasDerivAt_iff_isLittleO] at g_diff
    apply Asymptotics.IsLittleO.isBigO at g_diff
    have : (fun x' ↦ deriv g p * (x' - p)) =O[𝓝 p] fun x' ↦ x' - p := by
      apply Asymptotics.IsBigO.const_mul_left
      exact Asymptotics.isBigO_refl (fun x ↦ x - p) (𝓝 p)
    have h1 := g_diff.add this
    have h2 : (fun x ↦ g x - g p) =O[𝓝 p] fun x' ↦ x' - p := by
      convert! h1 using 2
      simp
      ring
    refine (Asymptotics.isBigO_mul_iff_isBigO_div ?_).mpr ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_compl_iff, mem_singleton_iff] at hx
      exact inv_ne_zero (sub_ne_zero.mpr hx)
    · simp only [div_inv_eq_mul]
      refine Asymptotics.IsBigO.mono ?_ inf_le_left
      simpa
lemma zetaExt : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 1 = 1 ∧
    ∀ s, s ≠ 1 → riemannZeta s = g s / (s - 1) := by
  classical
  set g := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1
  have hd (w : ℂ) (hw : w ≠ 1) : DifferentiableAt ℂ g w :=
    ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hw)).congr_of_eventuallyEq
      (by filter_upwards [eventually_ne_nhds hw] with x hx; simp [g, hx])
  refine ⟨g, fun w ↦ ?_, by simp [g], fun s hs ↦ ?_⟩
  · rcases eq_or_ne w 1 with rfl | hw
    · exact (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        (eventually_nhdsWithin_of_forall hd) (continuousAt_update_same.mpr riemannZeta_residue_one)).differentiableAt
    · exact hd w hw
  · simp [g, hs, sub_ne_zero.mpr hs]
theorem riemannZetaLogDerivResidueBigO :
    (-deriv riemannZeta / riemannZeta - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨g, hg, g1, hζ⟩ := zetaExt
  have h0 : g 1 ≠ 0 := by simp [g1]
  refine (((((hg.analyticAt 1).deriv.continuousAt.div (hg 1).continuousAt h0).neg).norm.isBoundedUnder_le.isBigO_one ℂ).mono nhdsWithin_le_nhds).congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds ((hg 1).continuousAt.eventually_ne h0)] with z hz hgz
  have hz : z ≠ 1 := hz
  have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have e : riemannZeta =ᶠ[𝓝 z] g / fun w ↦ w - 1 := by
    filter_upwards [eventually_ne_nhds hz] with w hw using hζ w hw
  simp only [Pi.sub_apply, Pi.div_apply, Pi.neg_apply, e.deriv_eq, hζ z hz]
  rw [((hg z).hasDerivAt.div ((hasDerivAt_id' z).sub_const 1) hz').deriv]
  field_simp
  ring
noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)
lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : riemannZeta0 N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg]; ring
lemma Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])
lemma Complex.one_div_cpow_eq {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne, neg_add_cancel, cpow_zero]
lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  rw [uIcc_of_le a_lt_b.le] at φDiff
  convert sum_eq_integral_add_integral_deriv apos a_lt_b.le (fun t ht ↦ (φDiff t ht).differentiableAt) derivφCont using 1
  unfold B1
  push_cast
  suffices ∫ (x : ℝ) in a..b, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x = -∫ (t : ℝ) in a..b, deriv φ t * (↑t - ↑⌊t⌋₊ - 1 / 2) by
    rw [this]
    ring_nf!
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le a_lt_b.le, mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring
lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]
lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · refine intervalIntegral.integral_congr fun x hx ↦ one_div_cpow_eq ?_
    exact (xpos_of_uIcc ha hx).ne'
  · norm_cast; ring_nf
  · right; refine ⟨(by grind), ?_⟩
    exact fun hx ↦ (lt_self_iff_false 0).mp <| xpos_of_uIcc ha hx
lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  exact hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.differentiableAt_cpow_const_of_ne s xpos) (by simp [cpow_eq_zero_iff, xpos.ne'])
lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have r_add1_ne_zero : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr s_ne_zero, r] at hr
  have r_ne_neg1 : r ≠ -1 := fun hr ↦ (hr ▸ r_add1_ne_zero) <| by norm_num
  have hasDeriv := hasDerivAt_ofReal_cpow_const' xpos.ne' r_ne_neg1
  have := hasDeriv.deriv ▸ deriv_const_mul (-s) (hasDeriv).differentiableAt
  convert! this using 2
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div, sub_add_cancel, cpow_neg, neg_mul, r]
      field_simp
  · simp only [r]
    ring_nf
lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero <| xpos_of_uIcc ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| xpos_of_uIcc ha hx
lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc ha hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x :=
    fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := by
    exact fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_zero ha
  convert sum_eq_int_deriv (by linarith) (by exact_mod_cast ha.2) φDiff derivφCont using 1
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast, Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, ZetaSum_aux1₁ s_ne_one ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at φderiv
    intro x hx; simp_rw [φderiv x hx, φ']; ring_nf
lemma ZetaSum_aux1_1' {a b x : ℝ} (apos : 0 < a) (hx : x ∈ Icc a b) : 0 < x :=
  lt_of_lt_of_le apos hx.1
lemma ZetaSum_aux1_1 {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a, b]]) : 0 < x :=
  lt_of_lt_of_le apos (uIcc_of_le a_lt_b.le ▸ hx).1
lemma ZetaSum_aux1_2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c := by
  rw [(by ring : (a ^ (-c) - b ^ (-c)) / c = (b ^ (-c) - a ^ (-c)) / (-c))]
  have := integral_rpow (a := a) (b := b) (r := -c-1) (Or.inr ⟨by simp [h.1], h.2⟩)
  simp only [sub_add_cancel] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro x hx
  have : 0 ≤ x := (ZetaSum_aux1_1 apos a_lt_b hx).le
  simp [div_rpow_eq_rpow_neg _ _ _ this, sub_eq_add_neg, add_comm]
lemma ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩
lemma ZetaSum_aux1_4' (x : ℝ) (hx : 0 < x) (s : ℂ) :
      ‖(⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1)‖ =
      ‖⌊x⌋ + 1 / 2 - x‖ / x ^ ((s + 1).re) := by
  simp_rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← norm_real]
  simp
lemma ZetaSum_aux1_4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re := by
  apply intervalIntegral.integral_congr
  exact fun x hx ↦ ZetaSum_aux1_4' x (ZetaSum_aux1_1 apos a_lt_b hx) s
lemma ZetaSum_aux1_5a {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
  (h : x ∈ Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) := by
  apply div_le_div_of_nonneg_right _ _
  · exact le_trans (ZetaSum_aux1_3 x) (by norm_num)
  · apply Real.rpow_nonneg <| le_of_lt (ZetaSum_aux1_1' apos h)
lemma ZetaSum_aux1_5b {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ 1 / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  refine continuousOn_const.div ?_ ?_ |>.intervalIntegrable_of_Icc (le_of_lt a_lt_b)
  · exact continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt <| ZetaSum_aux1_1' apos hx)
  · exact fun x hx h ↦ by rw [Real.rpow_eq_zero] at h <;> linarith [ZetaSum_aux1_1' apos hx]
lemma measurable_floor_add_half_sub : Measurable fun (u : ℝ) ↦ ↑⌊u⌋ + 1 / 2 - u := by
  refine Measurable.add ?_ measurable_const |>.sub measurable_id
  exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor
lemma ZetaSum_aux1_5c {a b : ℝ} {s : ℂ} :
    let g : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1);
    AEStronglyMeasurable g
      (Measure.restrict volume (Ι a b)) := by
  intro
  refine (Measurable.div ?_ <| measurable_id.pow_const _).aestronglyMeasurable
  exact _root_.continuous_abs.measurable.comp measurable_floor_add_half_sub
lemma ZetaSum_aux1_5d {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  set g : ℝ → ℝ := (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1))
  apply ZetaSum_aux1_5b apos a_lt_b σpos |>.mono_fun ZetaSum_aux1_5c ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, one_div, norm_inv, abs_div, _root_.abs_abs]
  conv => rw [div_eq_mul_inv, ← one_div]; rhs; rw [← one_mul |x ^ (s.re + 1)|⁻¹]
  refine mul_le_mul ?_ (le_refl _) (by simp) <| by norm_num
  exact le_trans (ZetaSum_aux1_3 x) <| by norm_num
lemma ZetaSum_aux1_5 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤
    ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) := by
  apply intervalIntegral.integral_mono_on (le_of_lt a_lt_b) ?_ ?_
  · exact ZetaSum_aux1_5a apos
  · exact ZetaSum_aux1_5d apos a_lt_b σpos
  · exact ZetaSum_aux1_5b apos a_lt_b σpos
lemma ZetaBnd_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  calc
    _ = ∫ x in a..b, |(⌊x⌋ + 1 / 2 - x)| / x ^ (s+1).re := ZetaSum_aux1_4 apos a_lt_b
    _ ≤ ∫ x in a..b, 1 / x ^ (s.re + 1) := ZetaSum_aux1_5 apos a_lt_b σpos
    _ = (a ^ (-s.re) - b ^ (-s.re)) / s.re := ?_
  refine ZetaSum_aux1_2 (c := s.re) apos a_lt_b ⟨ne_of_gt σpos, ?_⟩
  exact fun h ↦ (lt_self_iff_false 0).mp <| ZetaSum_aux1_1 apos a_lt_b h
lemma Finset.Ioc_eq_Ico (M N : ℕ) : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega
lemma Finset.Icc_eq_Ico (M N : ℕ) : Finset.Icc N M = Finset.Ico N (M + 1) := by
  ext a; simp only [Finset.mem_Icc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega
lemma finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  have := Summable.hasSum_iff_tendsto_nat hf (m := ∑' (n : ℕ), f n) |>.mp hf.hasSum
  have const := tendsto_const_nhds (α := ℕ) (x := ∑ i ∈ Finset.range N, f i) (f := atTop)
  have := Filter.Tendsto.sub this const
  rw [← hf.sum_add_tsum_nat_add N, add_comm, add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N + 1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith
lemma Complex.cpow_tendsto {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  have one_sub_s_re_ne : (1 - s).re ≠ 0 := by simp only [sub_re, one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (one_sub_s_re_ne)]
  rw [(by simp only [sub_re, one_re, neg_sub] : (1 - s).re = - (s - 1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [s_re_gt]
lemma Complex.cpow_inv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv, Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  apply Filter.Tendsto.inv_tendsto_atTop
  exact (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
lemma ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3
lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  let f := fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s
  have hf := summable_one_div_nat_cpow.mpr s_re_gt
  simp_rw [Finset.Ioc_eq_Ico]
  convert finsetSum_tendsto_tsum (f := fun n ↦ f (n + 1)) (N := N) ?_ using 1
  · ext k
    rw [Finset.sum_Ico_add']
  · congr; ext n; simp only [one_div, Nat.cast_add, Nat.cast_one, f]
  · rwa [summable_nat_add_iff (k := 1)]
lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor
lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  have s_ne_zero : s ≠ 0 := fun hs ↦ by linarith [zero_re ▸ hs ▸ s_re_gt]
  have s_ne_one : s ≠ 1 := fun hs ↦ (lt_self_iff_false _).mp <| one_re ▸ hs ▸ s_re_gt
  apply tendsto_nhds_unique (X := ℂ) (Y := ℕ) (l := atTop)
    (f := fun k ↦ ((k : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) +
      1 / 2 * (1 / ↑k ^ s) - 1 / 2 * (1 / ↑N ^ s)
      + s * ∫ (x : ℝ) in (N : ℝ)..k, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
    (b := (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  · apply Filter.Tendsto.congr'
      (f₁ := fun (k : ℕ) ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) (l₁ := atTop)
    · apply Filter.eventually_atTop.mpr
      use N + 1
      intro k hk
      exact ZetaSum_aux1 (a := N) (b := k) s_ne_one s_ne_zero ⟨N_pos, hk⟩
    · exact ZetaSum_aux3 s_re_gt
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring : -↑N ^ (1 - s) / (1 - s) = (0 - ↑N ^ (1 - s)) / (1 - s) + 0)]
      apply cpow_tendsto s_re_gt |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div, one_mul, one_div, (by congr; ring : 𝓝 (0 : ℂ) = 𝓝 ((0 : ℂ) / 2))]
      apply Tendsto.div_const <| cpow_inv_tendsto (by positivity)
    · simp_rw [mul_comm_div, one_mul, one_div, cpow_neg]; exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := N)
        (b := (fun (n : ℕ) ↦ (n : ℝ)))
        (integrableOn_of_Zeta0_fun N_pos <| by positivity) tendsto_natCast_atTop_atTop
lemma ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by
  apply le_trans (by apply norm_integral_le_integral_norm)
  apply le_of_tendsto (x := atTop (α := ℝ)) (f := fun (t : ℝ) ↦ ∫ (x : ℝ) in N..t,
    ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) ?_ ?_
  · apply intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop) (b := id)
      (f := fun (x : ℝ) ↦ ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) N ?_ ?_ |>.congr' ?_
    · filter_upwards [Filter.mem_atTop ((N : ℝ))]
      intro u hu
      simp only [id_eq, intervalIntegral.integral_of_le hu, norm_div]
      apply setIntegral_congr_fun (by simp)
      intro x hx; beta_reduce
      iterate 2 (rw [norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])])
      simp
    · apply IntegrableOn.integrable ?_ |>.norm
      convert! integrableOn_of_Zeta0_fun (s := σ + t * I) Npos (by simp [σpos]) using 1
      simp_rw [div_eq_mul_inv, cpow_neg]
    · exact fun ⦃_⦄ a ↦ a
  · filter_upwards [mem_atTop (N + 1 : ℝ)] with t ht
    have : (N ^ (-σ) - t ^ (-σ)) / σ ≤ N ^ (-σ) / σ :=
      div_le_div_iff_of_pos_right σpos |>.mpr (by simp [Real.rpow_nonneg (by linarith)])
    apply le_trans ?_ this
    convert! ZetaBnd_aux1a (a := N) (b := t) (by positivity) (by linarith) ?_ <;> simp [σpos]
lemma ZetaBnd_aux1 (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (hσ : σ ∈ Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ 2 * |t| * N ^ (-σ) / σ := by
  rw [norm_mul, mul_div_assoc]
  rw [Set.mem_Ioc] at hσ
  apply mul_le_mul ?_ (ZetaBnd_aux1b N Npos hσ.1) (norm_nonneg _) (by positivity)
  refine le_trans (by apply norm_add_le) ?_
  simp only [Complex.norm_of_nonneg hσ.1.le, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_I,
    mul_one]
  linarith [hσ.2]
lemma isOpen_aux : IsOpen {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  refine IsOpen.inter isOpen_ne ?_
  exact isOpen_lt (g := fun (z : ℂ) ↦ z.re) (by continuity) (by continuity)
lemma integrable_log_over_pow {r : ℝ} (rneg : r < 0) {N : ℕ} (Npos : 0 < N) :
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  apply IntegrableOn.mono_set (hst := Set.Ioi_subset_Ici <| le_refl (N : ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun x ↦ x ^ (r / 2 - 1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx; left; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx; simp only [id_eq]; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
  · have := isLittleO_log_rpow_atTop (r := -r / 2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually, Filter.eventually_atTop] at this
    obtain ⟨C, hC⟩ := this
    have hh := hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    have := Filter.eventually_atTop.mp hh
    obtain ⟨x₀, hx₀ ⟩ := this
    filter_upwards [hh, Filter.mem_atTop x₀, Filter.mem_atTop 1]
    intro x hx x_gt x_pos
    use C
    intro y hy
    simp only [norm_mul, Real.norm_eq_abs, _root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos : 0 < y := by linarith
    have : y ^ (r / 2 - 1) = y ^ (r - 1) * y ^ (-r / 2) := by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this, abs_mul]
    have y_gt : y ≥ x₀ := by linarith
    have := hx₀ y y_gt
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc, mul_comm C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbc := this) (a := |y ^ (r - 1)|) (ha := by simp)
  · have := integrableOn_Ioi_rpow_iff (s := r / 2 - 1) (t := N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1
lemma integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  simp_rw [mul_assoc]
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply Integrable.bdd_mul (c := c) ?_ ?_ ?_
  · simp only [neg_add_rev, mul_neg, add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane]; linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx; simp only [id_eq]; linarith [mem_Ioi.mp hx]
    · simp only [norm_mul, norm_real]
      have := integrable_log_over_pow (r := -s.re) (by linarith) Npos
      apply IntegrableOn.congr_fun this ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff, norm_eq_zero, Real.log_eq_zero]
      left
      have xpos : 0 < x := by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos, Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor
  · apply MeasureTheory.ae_of_all
    convert hc with _ x; simp only [← Complex.norm_real]; simp
lemma hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [mem_ofPred_eq] at hs
  set f : ℝ → ℂ := fun x ↦ (⌊x⌋ : ℂ) + 1 / 2 - x
  set F : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * f x
  set F' : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * (- Real.log x) * f x
  set ε := s.re / 2
  have ε_pos : 0 < ε := by aesop
  set bound : ℝ → ℝ := fun x ↦ |x ^ (- s.re / 2 - 1)| * |Real.log x|
  let μ : Measure ℝ := volume.restrict (Ioi (N : ℝ))
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s := by
      rw [mem_nhds_iff]
      refine ⟨{z | 0 < z.re}, fun ⦃a⦄ a ↦ a, isOpen_lt continuous_const Complex.continuous_re, hs⟩
    filter_upwards [this] with z hz
    convert! integrableOn_of_Zeta0_fun Npos hz |>.aestronglyMeasurable using 1
    simp only [F, f]; ext x; ring_nf
  have hF_int : Integrable (F s) μ := by
    convert! integrableOn_of_Zeta0_fun Npos hs |>.integrable using 1
    simp only [F, f]; ext x; ring_nf
  have hF'_meas : AEStronglyMeasurable (F' s) μ := by
    convert! integrableOn_of_Zeta0_fun_log Npos hs |>.aestronglyMeasurable using 1
    simp only [F', f]; ext x; ring_nf
  have IoiSubIoi1 : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
      fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have measSetIoi1 : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have h_bound1 :
    ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x}, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    intro z hz
    simp only [F', f, bound]
    calc _ = ‖(x : ℂ) ^ (-z - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := by
            simp only [mul_neg, one_div, neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
              ← (by simp : (((⌊x⌋ + 2⁻¹ - x) : ℝ) : ℂ) = (⌊x⌋ : ℂ) + 2⁻¹ - ↑x),
              Complex.norm_real]
         _ = ‖x ^ (-z.re - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := ?_
         _ = |x ^ (-z.re - 1)| * |(Real.log x)| * |(⌊x⌋ + 1 / 2 - x)| := by simp
         _ ≤ _ := ?_
    · congr! 2
      simp only [Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith),
        sub_re, neg_re, one_re]
      apply abs_eq_self.mpr ?_ |>.symm
      positivity
    · rw [mul_comm, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
      simp only [Metric.mem_ball, ε, Complex.dist_eq] at hz
      apply le_trans (b := 1 * |x ^ (-z.re - 1)|)
      · apply mul_le_mul_of_nonneg_right (le_trans (ZetaSum_aux1_3 _) (by norm_num)) <| abs_nonneg _
      · simp_rw [one_mul, Real.abs_rpow_of_nonneg (by linarith : 0 ≤ x)]
        apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (by left; exact hx.le)
        have := abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
        simp only [sub_re, neg_le_sub_iff_le_add, tsub_le_iff_right] at this
        linarith [this.1]
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    exact h_bound1
  have bound_integrable : Integrable bound μ := by
    simp only [bound]
    convert! integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos using 0
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, HasDerivAt (fun w ↦ F w x) (F' z x) z := by
    simp only [F, F', f]
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [h_bound1, self_mem_ae_restrict measSetIoi1] with x _ one_lt_x
    intro z hz
    convert! HasDerivAt.mul_const (c := fun (w : ℂ) ↦ (x : ℂ) ^ (-w-1))
      (c' := (x : ℂ) ^ (-z-1) * -Real.log x) (d := (⌊x⌋ : ℝ) + 1 / 2 - x) ?_ using 1
    convert! HasDerivAt.comp (h := fun w ↦ -w-1) (h' := -1) (h₂ := fun w ↦ x ^ w)
      (h₂' := x ^ (-z-1) * Real.log x) (x := z) ?_ ?_ using 0
    · simp only [mul_neg, mul_one]; congr! 2
    · convert! HasDerivAt.const_cpow (c := (x : ℂ)) (f := fun w ↦ w) (f' := 1) (x := -z-1)
        (hasDerivAt_id _) ?_ using 1
      · simp only [mul_one, mul_eq_mul_left_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq]
        left
        rw [Complex.ofReal_log]
        linarith
      · right
        intro h
        simp only [Metric.mem_ball, ε, Complex.dist_eq,
          neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
        have := (abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
        simp only [sub_re, neg_re, one_re, neg_le_sub_iff_le_add, le_neg_add_iff_add_le] at this
        linarith
    · apply hasDerivAt_id _ |>.neg |>.sub_const
  convert! (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s ε) (bound := bound) (μ := μ) (Metric.ball_mem_nhds s ε_pos)
    hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2 using 3
  · ext a; simp only [one_div, F, f]; ring_nf
  · simp only [one_div, mul_neg, neg_mul, neg_inj, F', f]; ring_nf
noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))
lemma HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  convert! hasDerivAt_neg' s |>.const_cpow (c := N) (by aesop) |>.neg |>.div_const _ using 1
  simp [mul_comm]
lemma HasDerivAt_cpow_over_var (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹)
    (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log, neg_mul, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert! HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero
lemma HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (riemannZeta0 N) (ζ₀' N s) s := by
  unfold riemannZeta0 ζ₀'
  apply HasDerivAt.fun_sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert! hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop) using 1
    all_goals (ring_nf; simp [cpow_neg])
  · convert! HasDerivAt.comp (h₂ := fun z ↦ -(N : ℂ) ^ z / z) (h := fun z ↦ 1 - z) (h' := -1)
      (h₂' := ((N : ℂ) ^ (1 - s) / (1 - s) ^ 2 - Real.log (N : ℝ) * (N : ℂ) ^ (1 - s) / (1 - s)))
      (x := s) ?_ ?_ using 1
    · ring_nf
    · exact HasDerivAt_cpow_over_var N (by rw [sub_ne_zero]; exact s_ne_one.symm)
    · convert! hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1; simp
  · convert! HasDerivAt_neg_cpow_over2 Npos s using 1; simp only [natCast_log, neg_mul, neg_neg]
  · simp_rw [div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    convert! hasDerivAt_id s |>.mul <| hasDerivAt_Zeta0Integral Npos reS_pos using 1
lemma HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (riemannZeta0 N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (HasDerivAtZeta0 N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt
lemma HolomorphicOn_riemannZeta :
    HolomorphicOn riemannZeta {s : ℂ | s ≠ 1} := by
  intro z hz
  simp only [mem_ofPred_eq] at hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt
lemma Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    riemannZeta0 N s = riemannZeta s := by
  let f := riemannZeta
  let g := riemannZeta0 N
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have f_an : AnalyticOnNhd ℂ f U := by
    apply (HolomorphicOn_riemannZeta.analyticOnNhd isOpen_ne).mono
    simp only [ne_eq, ofPred_subset_ofPred, and_imp, U]
    exact fun a ha _ ↦ ha
  have g_an : AnalyticOnNhd ℂ g U := (HolomorphicOn_riemannZeta0 N_pos).analyticOnNhd isOpen_aux
  have preconU : IsPreconnected U := by
    have e : U = {z : ℂ | 1 < z.re} ∪ {z | 0 < z.re} ∩ {z | 0 < z.im} ∪ {z | 0 < z.re} ∩ {z | z.im < 0}
        ∪ {z | 0 < z.re} ∩ {z | z.re < 1} := by
      ext z
      simp only [U, mem_union, mem_inter_iff, mem_ofPred_eq, ne_eq, Complex.ext_iff, one_re, one_im]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_trichotomy z.re 1 with h | h | h
        · exact Or.inr ⟨h2, h⟩
        · rcases lt_trichotomy z.im 0 with h' | h' | h'
          · exact Or.inl (Or.inr ⟨h2, h'⟩)
          · exact absurd ⟨h, h'⟩ h1
          · exact Or.inl (Or.inl (Or.inr ⟨h2, h'⟩))
        · exact Or.inl (Or.inl (Or.inl h))
      · rintro (((h | h) | h) | h)
        · exact ⟨fun e ↦ by linarith [e.1], by linarith⟩
        · exact ⟨fun e ↦ by linarith [e.2, h.2], h.1⟩
        · exact ⟨fun e ↦ by linarith [e.2, h.2], h.1⟩
        · exact ⟨fun e ↦ by linarith [e.1, h.2], h.1⟩
    rw [e]
    exact (((convex_halfSpace_re_gt 1).isPreconnected.union (2 + I) (by norm_num) (by norm_num)
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected).union (2 - I)
      (by norm_num) (by norm_num) ((convex_halfSpace_re_gt 0).inter
      (convex_halfSpace_im_lt 0)).isPreconnected).union (1 / 2 + I) (by norm_num) (by norm_num)
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have s_mem : s ∈ U := by simp [U, reS_pos, s_ne_one]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an preconU h2 ?_ s_mem).symm
  have u_mem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
    apply mem_nhds_iff.mpr
    use {z : ℂ | 1 < z.re}
    simp only [ofPred_subset_ofPred, imp_self, forall_const, mem_ofPred_eq, re_ofNat,
      Nat.one_lt_ofNat, and_true, true_and]
    exact isOpen_lt (by continuity) (by continuity)
  filter_upwards [u_mem]
  intro z hz
  simp only [f,g, zeta_eq_tsum_one_div_nat_cpow hz, riemannZeta0_apply]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← ZetaSum_aux2 N_pos hz,
    ← (summable_one_div_nat_cpow.mpr hz).sum_add_tsum_nat_add (N + 1)]
  norm_cast
lemma DerivZeta0EqDerivZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re)
    (s_ne_one : s ≠ 1) :
    deriv (riemannZeta0 N) s = deriv riemannZeta s := by
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have {x : ℂ} (hx : x ∈ U) : riemannZeta0 N x = riemannZeta x := by
    simp only [mem_ofPred_eq, U] at hx; exact Zeta0EqZeta (N := N) N_pos hx.2 hx.1
  refine deriv_eqOn isOpen_aux ?_ (by simp [s_ne_one, reS_pos])
  intro x hx
  have hζ := HolomorphicOn_riemannZeta.mono (by aesop)|>.hasDerivAt (s := U) <|
    isOpen_aux.mem_nhds hx
  exact hζ.hasDerivWithinAt.congr (fun y hy ↦ this hy) (this hx)
lemma le_trans₄ {α : Type*} [Preorder α] {a b c d : α} : a ≤ b → b ≤ c → c ≤ d → a ≤ d :=
  fun hab hbc hcd ↦ le_trans (le_trans hab hbc) hcd
lemma lt_trans₄ {α : Type*} [Preorder α] {a b c d : α} : a < b → b < c → c < d → a < d :=
  fun hab hbc hcd ↦ lt_trans (lt_trans hab hbc) hcd
lemma norm_add₅_le {E : Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) (e : E) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  apply le_trans <| norm_add_le (a + b + c + d) e
  simp only [add_le_add_iff_right]; apply norm_add₄_le
lemma norm_add₆_le {E : Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) (e : E)
    (f : E) :
    ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  apply le_trans <| norm_add_le (a + b + c + d + e) f
  simp only [add_le_add_iff_right]; apply norm_add₅_le
lemma mul_le_mul₃ {α : Type*} {a b c d e f : α} [MulZeroClass α] [Preorder α] [PosMulMono α]
    [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (h₃ : e ≤ f) (c0 : 0 ≤ c) (b0 : 0 ≤ b)
    (e0 : 0 ≤ e) : a * c * e ≤ b * d * f := by
  apply mul_le_mul (mul_le_mul h₁ h₂ c0 b0) h₃ e0 <| mul_nonneg b0 <| le_trans c0 h₂
lemma ZetaBnd_aux2 {n : ℕ} {t A σ : ℝ} (Apos : 0 < A) (σpos : 0 < σ) (n_le_t : n ≤ |t|)
    (σ_ge : (1 : ℝ) - A / Real.log |t| ≤ σ) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * Real.exp A := by
  set s := σ + t * I
  by_cases n0 : n = 0
  · simp_rw [n0, CharP.cast_eq_zero, inv_zero, zero_mul]
    rw [Complex.zero_cpow ?_]
    · simp
    · exact fun h ↦ σpos.ne' <| zero_eq_neg.mp <| zero_re ▸ h ▸ (by simp [s])
  have n_gt_0 : 0 < n := Nat.pos_of_ne_zero n0
  have n_gt_0' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr n_gt_0
  have n_ge_1 : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr <| Nat.succ_le_of_lt n_gt_0
  calc
    _ = |((n : ℝ) ^ (-σ))| := ?_
    _ ≤ Real.exp (Real.log n * -σ) := Real.abs_rpow_le_exp_log_mul (n : ℝ) (-σ)
    _ ≤ Real.exp (Real.log n *  -(1 - A / Real.log t)) := ?_
    _ ≤ Real.exp (- Real.log n + A) := Real.exp_le_exp_of_le ?_
    _ ≤ _ := by rw [Real.exp_add, Real.exp_neg, Real.exp_log n_gt_0']
  · have : ‖(n : ℂ) ^ (-s)‖ = n ^ (-s.re) := norm_cpow_eq_rpow_re_of_pos n_gt_0' (-s)
    rw [this, abs_eq_self.mpr <| Real.rpow_nonneg n_gt_0'.le _]; simp [s]
  · apply Real.exp_le_exp_of_le <| mul_le_mul_of_nonneg_left _ <| Real.log_nonneg n_ge_1
    rw [neg_sub, neg_le_sub_iff_le_add, add_comm, ← Real.log_abs]; linarith
  · simp only [neg_sub, le_neg_add_iff_add_le]
    ring_nf
    conv => rw [mul_comm, ← mul_assoc, ← Real.log_abs]; rhs; rw [← one_mul A]
    gcongr
    by_cases ht1 : |t| = 1
    · simp [ht1]
    apply (inv_mul_le_iff₀ ?_).mpr
    · convert! Real.log_le_log n_gt_0' n_le_t using 1; rw [mul_one]
    · exact Real.log_pos <| lt_of_le_of_ne (le_trans n_ge_1 n_le_t) <| fun t ↦ ht1 (t.symm)
lemma logt_gt_one {t : ℝ} (t_ge : 3 ≤ t) : 1 < Real.log t :=
  (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
lemma UpperBnd_aux {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (σ_ge : 1 - A / Real.log |t| ≤ σ) :
    let N := ⌊|t|⌋₊;
    0 < N ∧ N ≤ |t| ∧ 1 < Real.log |t| ∧ 1 - A < σ ∧ 0 < σ ∧ σ + t * I ≠ 1 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  have logt_gt := logt_gt_one t_gt.le
  have σ_gt : 1 - A < σ := by
    apply lt_of_lt_of_le ((sub_lt_sub_iff_left (a := 1)).mpr ?_) σ_ge
    exact (div_lt_iff₀ (by linarith)).mpr <| lt_mul_right hA.1 logt_gt
  refine ⟨Npos, N_le_t, logt_gt, σ_gt, by linarith [hA.2], ?_⟩
  contrapose! t_gt
  simp only [Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, one_re, add_im, mul_im, zero_add, one_im] at t_gt
  norm_num [t_gt.2]
lemma UpperBnd_aux2 {A σ t : ℝ} (t_ge : 3 < |t|) (σ_ge : 1 - A / Real.log |t| ≤ σ) :
      |t| ^ (1 - σ) ≤ Real.exp A := by
  have : |t| ^ (1 - σ) ≤ |t| ^ (A / Real.log |t|) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  apply le_trans this ?_
  conv => lhs; lhs; rw [← Real.exp_log (by linarith : 0 < |t|)]
  rw [div_eq_mul_inv, Real.rpow_mul (by positivity), ← Real.exp_mul, ← Real.exp_mul, mul_comm,
    ← mul_assoc, inv_mul_cancel₀, one_mul]
  apply Real.log_ne_zero.mpr; split_ands <;> linarith
lemma riemannZeta0_zero_aux (N : ℕ) (Npos : 0 < N) :
    ∑ x ∈ Finset.Ico 0 N, ((x : ℝ))⁻¹ = ∑ x ∈ Finset.Ico 1 N, ((x : ℝ))⁻¹ := by
  have : Finset.Ico 1 N ⊆ Finset.Ico 0 N := by
    intro x hx
    simp only [Finset.mem_Ico, Nat.Ico_zero_eq_range, Finset.mem_range] at hx ⊢
    exact hx.2
  rw [← Finset.sum_sdiff (s₁ := Finset.Ico 1 N) (s₂ := Finset.Ico 0 N) this]
  have : Finset.Ico 0 N \ Finset.Ico 1 N = Finset.range 1 := by
    ext a
    simp only [Nat.Ico_zero_eq_range, Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico, not_and,
      not_lt, Finset.range_one, Finset.mem_singleton]
    exact ⟨fun _ ↦ by omega, fun ha ↦ ⟨by simp [ha, Npos], by omega⟩⟩
  rw [this]; simp
lemma UpperBnd_aux3 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), (n : ℂ) ^ (-(σ + t * I))‖ ≤
      Real.exp A * C * Real.log |t| := by
  intro N
  obtain ⟨Npos, N_le_t, _, _, σPos, _⟩ := UpperBnd_aux hA t_gt σ_ge
  have logt_gt := logt_gt_one t_gt.le
  have (n : ℕ) (hn : n ∈ Finset.range (N + 1)) := ZetaBnd_aux2 (n := n) hA.1 σPos ?_ σ_ge
  · replace := norm_sum_le_of_le (Finset.range (N + 1)) this
    rw [← Finset.sum_mul, mul_comm _ (Real.exp A)] at this
    rw [mul_assoc]
    apply le_trans this <| (mul_le_mul_iff_right₀ A.exp_pos).mpr ?_
    have : 1 + Real.log (N : ℝ) ≤ C * Real.log |t| := by
      by_cases hN : N = 1
      · simp only [hN, Nat.cast_one, Real.log_one, add_zero]
        have : 2 * 1 ≤ C * Real.log |t| := mul_le_mul hC logt_gt.le (by linarith) (by linarith)
        linarith
      · rw [(by ring : C * Real.log |t| = Real.log |t| + (C - 1) * Real.log |t|),
          ← one_mul <| Real.log (N: ℝ)]
        apply add_le_add logt_gt.le
        refine mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
        exact Real.log_le_log (by positivity) N_le_t
    refine le_trans ?_ this
    convert! harmonic_eq_sum_Icc ▸ harmonic_le_one_add_log N
    · simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.range_eq_Ico]
      rw [riemannZeta0_zero_aux (N + 1) (by linarith)]; congr! 1
  · simp only [Finset.mem_range] at hn
    linarith [(by exact_mod_cast (by omega : n ≤ N) : (n : ℝ) ≤ N)]
lemma Nat.self_div_floor_bound {t : ℝ} (t_ge : 1 ≤ |t|) : let N := ⌊|t|⌋₊;
    (|t| / N) ∈ Icc 1 2 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  constructor
  · apply le_div_iff₀ (by simp [Npos]) |>.mpr; simp [N_le_t]
  · apply div_le_iff₀ (by positivity) |>.mpr
    suffices |t| < N + 1 by linarith [(by exact_mod_cast (by omega) : 1 ≤ (N : ℝ))]
    apply Nat.lt_floor_add_one
lemma UpperBnd_aux5 {σ t : ℝ} (t_ge : 3 < |t|) (σ_le : σ ≤ 2) : (|t| / ⌊|t|⌋₊) ^ σ ≤ 4 := by
  obtain ⟨h₁, h₂⟩ := Nat.self_div_floor_bound (by linarith)
  calc _ ≤ ((|t| / ↑⌊|t|⌋₊) ^ (2 : ℝ)) := by gcongr
       _ ≤ (2 : ℝ) ^ (2 : ℝ) := by gcongr
       _ = 4 := by norm_num
lemma UpperBnd_aux6 {σ t : ℝ} (t_ge : 3 < |t|) (hσ : σ ∈ Ioc (1 / 2) 2)
    (neOne : σ + t * I ≠ 1) (Npos : 0 < ⌊|t|⌋₊) (N_le_t : ⌊|t|⌋₊ ≤ |t|) :
    ⌊|t|⌋₊ ^ (1 - σ) / ‖1 - (σ + t * I)‖ ≤ |t| ^ (1 - σ) * 2 ∧
    ⌊|t|⌋₊ ^ (-σ) / 2 ≤ |t| ^ (1 - σ) ∧ ⌊|t|⌋₊ ^ (-σ) / σ ≤ 8 * |t| ^ (-σ) := by
  have bnd := UpperBnd_aux5 t_ge hσ.2
  have bnd' : (|t| / ⌊|t|⌋₊) ^ σ ≤ 2 * |t| := by linarith
  split_ands
  · apply (div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm).mpr
    conv => rw [mul_assoc]; rhs; rw [mul_comm]
    apply (div_le_iff₀ <| Real.rpow_pos_of_pos (by linarith) _).mp
    rw [div_rpow_eq_rpow_div_neg (by positivity) (by positivity), neg_sub]
    refine le_trans₄ ?_ bnd' ?_
    · exact Real.rpow_le_rpow_of_exponent_le (one_le_div (by positivity) |>.mpr N_le_t) (by simp)
    · apply (mul_le_mul_iff_right₀ (by norm_num)).mpr; simpa using abs_im_le_norm (1 - (σ + t * I))
  · apply div_le_iff₀ (by norm_num) |>.mpr
    rw [Real.rpow_sub (by linarith), Real.rpow_one, div_mul_eq_mul_div, mul_comm]
    apply div_le_iff₀ (by positivity) |>.mp
    convert! bnd' using 1
    rw [← Real.rpow_neg (by linarith), div_rpow_neg_eq_rpow_div (by positivity) (by positivity)]
  · apply div_le_iff₀ (by linarith [hσ.1]) |>.mpr
    rw [mul_assoc, mul_comm, mul_assoc]
    apply div_le_iff₀' (by positivity) |>.mp
    apply le_trans ?_ (by linarith [hσ.1] : 4 ≤ σ * 8)
    convert! bnd using 1; exact div_rpow_neg_eq_rpow_div (by positivity) (by positivity)
lemma ZetaUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * (5 + 8 * 2);
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ + ‖(N : ℂ) ^ (1 - s) / (1 - s)‖
    + ‖(N : ℂ) ^ (-s) / 2‖
    + ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
    ≤ C * Real.log |t| := by
  intros C N s
  obtain ⟨Npos, N_le_t, logt_gt, σ_gt, σPos, neOne⟩ := UpperBnd_aux hA t_gt hσ.1
  replace σ_gt : 1 / 2 < σ := by linarith [hA.2]
  calc
    _ ≤ Real.exp A * 2 * Real.log |t| + ‖N ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖ +
      ‖s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + ‖N ^ (1 - s) / (1 - s)‖ + ‖(N : ℂ) ^ (-s) / 2‖ +
      2 * |t| * N ^ (-σ) / σ  := ?_
    _ = Real.exp A * 2 * Real.log |t| + N ^ (1 - σ) / ‖(1 - s)‖ + N ^ (-σ) / 2 +
      2 * |t| * N ^ (-σ) / σ  := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + |t| ^ (1 - σ) * 2 +
        |t| ^ (1 - σ) + 2 * |t| * (8 * |t| ^ (-σ)) := ?_
    _ = Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * |t| ^ (1 - σ) := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * Real.exp A * 1 := ?_
    _ ≤ Real.exp A * 2 * Real.log |t| + (3 + 8 * 2) * Real.exp A * Real.log |t| := ?_
    _ = _ := by ring
  · simp only [add_le_add_iff_right, one_div_cpow_eq_cpow_neg]
    convert UpperBnd_aux3 (C := 2) hA hσ.1 t_gt le_rfl using 1
  · simp only [add_le_add_iff_left]; exact ZetaBnd_aux1 N (by linarith) ⟨σPos, hσ.2⟩ (by linarith)
  · simp only [norm_div, RCLike.norm_ofNat, s]
    congr <;> (convert norm_natCast_cpow_of_pos Npos _; simp)
  · have ⟨h₁, h₂, h₃⟩ := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t
    gcongr
    rw [mul_div_assoc]
    gcongr
  · ring_nf; conv => lhs; rhs; lhs; rw [mul_comm |t|]
    rw [← Real.rpow_add_one (by positivity)]; ring_nf
  · simp only [Real.log_abs, add_le_add_iff_left, mul_one]
    exact mul_le_mul_iff_right₀ (by positivity) |>.mpr <| UpperBnd_aux2 t_gt hσ.1
  · simp only [add_le_add_iff_left]
    apply mul_le_mul_iff_right₀ (by norm_num [Real.exp_pos]) |>.mpr <| logt_gt.le
lemma ZetaUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2), ‖riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| := by
  let A := (1 / 2 : ℝ)
  let C := Real.exp A * (5 + 8 * 2)
  refine ⟨A, ⟨by norm_num, by norm_num⟩, C, (by positivity), ?_⟩
  intro σ t t_gt ⟨σ_ge, σ_le⟩
  obtain ⟨Npos, _, _, _, σPos, neOne⟩ := UpperBnd_aux ⟨by norm_num, by norm_num⟩ t_gt σ_ge
  rw [← Zeta0EqZeta Npos (by simp [σPos]) neOne]
  apply le_trans (by apply norm_add₄_le) ?_
  convert! ZetaUpperBnd' ⟨by norm_num, le_rfl⟩ t_gt ⟨σ_ge, σ_le⟩ using 1; simp
lemma norm_complex_log_ofNat (n : ℕ) : ‖(n : ℂ).log‖ = (n : ℝ).log := by
  have := Complex.ofReal_log (x := (n : ℝ)) (Nat.cast_nonneg n)
  rw [(by simp : ((n : ℝ) : ℂ) = (n : ℂ))] at this
  rw [← this, Complex.norm_of_nonneg]
  exact Real.log_natCast_nonneg n
lemma Finset.Icc0_eq (N : ℕ) : Finset.Icc 0 N = {0} ∪ Finset.Icc 1 N := by
  refine Finset.ext_iff.mpr ?_
  intro a
  cases a
  · simp only [Finset.mem_Icc, le_refl, zero_le, and_self, Finset.mem_union, Finset.mem_singleton,
    nonpos_iff_eq_zero, one_ne_zero, and_true, or_false]
  · simp only [Finset.mem_Icc, le_add_iff_nonneg_left, zero_le, true_and, Finset.mem_union,
    Finset.mem_singleton, add_eq_zero, one_ne_zero, and_false, false_or]
lemma harmonic_eq_sum_Icc0_aux (N : ℕ) :
    ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = ∑ i ∈ Finset.Icc 1 N, (i : ℝ)⁻¹ := by
  rw [Finset.Icc0_eq, Finset.sum_union]
  · simp only [Finset.sum_singleton, CharP.cast_eq_zero, inv_zero, zero_add]
  · simp only [Finset.disjoint_singleton_left, Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero,
    zero_le, and_true, not_false_eq_true]
lemma harmonic_eq_sum_Icc0 (N : ℕ) : ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc0_aux, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
lemma DerivUpperBnd_aux1 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖
      ≤ Real.exp A * C * (Real.log |t|) ^ 2 := by
  intro N
  obtain ⟨Npos, N_le_t, _, _, σPos, _⟩ := UpperBnd_aux hA t_gt σ_ge
  have logt_gt := logt_gt_one t_gt.le
  have logN_pos : 0 ≤ Real.log N := Real.log_nonneg (by norm_cast)
  have fact0 {n : ℕ} (hn : n ≤ N) : n ≤ |t| := by linarith [(by exact_mod_cast hn : (n : ℝ) ≤ N)]
  have fact1 {n : ℕ} (hn : n ≤ N) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * A.exp := ZetaBnd_aux2 hA.1 σPos (fact0 hn) σ_ge
  have fact2 {n : ℕ} (hn : n ≤ N) : Real.log n ≤ Real.log |t| := by
    cases n
    · simp only [CharP.cast_eq_zero, Real.log_zero]; linarith
    · exact Real.log_le_log (by exact_mod_cast Nat.add_one_pos _) (fact0 hn)
  have fact3 (n : ℕ) (hn : n ≤ N) :
    ‖-1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖ ≤ (n : ℝ)⁻¹ * Real.exp A * (Real.log |t|) := by
    convert! mul_le_mul (fact1 hn) (fact2 hn) (Real.log_natCast_nonneg n) (by positivity)
    simp only [norm_mul, norm_div, norm_neg, norm_one, one_div, natCast_log, ← norm_inv, cpow_neg]
    congr; exact norm_complex_log_ofNat n
  have := norm_sum_le_of_le (Finset.range (N + 1))
    (by simp only [Finset.mem_range, Nat.lt_succ_iff]; exact fact3)
  rw [← Finset.sum_mul, ← Finset.sum_mul, mul_comm _ A.exp, mul_assoc] at this
  rw [mul_assoc]
  apply le_trans this <| (mul_le_mul_iff_right₀ A.exp_pos).mpr ?_
  rw [pow_two, ← mul_assoc, Finset.range_eq_Ico, ← Finset.Icc_eq_Ico, harmonic_eq_sum_Icc0]
  apply le_trans (mul_le_mul (h₁ := harmonic_le_one_add_log (n := N)) (le_refl (Real.log |t|))
    (by linarith) (by linarith))
  apply (mul_le_mul_iff_left₀ (by linarith)).mpr
  rw [(by ring : C * Real.log |t| = Real.log |t| + (C - 1) * Real.log |t|),
      ← one_mul <| Real.log (N: ℝ)]
  refine add_le_add logt_gt.le <| mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
  exact Real.log_le_log (by positivity) N_le_t
lemma DerivUpperBnd_aux2 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 →
    1 / 2 < σ → ‖-↑N ^ (1 - s) / (1 - s) ^ 2‖ ≤ A.exp * 2 * (1 / 3) := by
  intro N s Npos N_le_t neOne σ_gt
  dsimp only [s]
  simp_rw [norm_div, norm_neg, norm_pow, norm_natCast_cpow_of_pos Npos _,
    sub_re, one_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero]
  have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.1
  rw [(by ring_nf : N ^ (1 - σ) / ‖1 - (↑σ + ↑t * I)‖ ^ 2 =
          N ^ (1 - σ) / ‖1 - (↑σ + ↑t * I)‖ * 1 / ‖1 - (↑σ + ↑t * I)‖)]
  apply mul_le_mul ?_ ?_ (inv_nonneg.mpr <| norm_nonneg _) ?_
  · rw [mul_one]; exact le_trans h (by gcongr; exact UpperBnd_aux2 t_gt hσ.1)
  · rw [inv_eq_one_div, div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm,
        mul_comm, ← mul_div_assoc, mul_one, le_div_iff₀ (by norm_num), one_mul]
    apply le_trans t_gt.le ?_
    rw [← abs_neg]; convert! abs_im_le_norm (1 - (σ + t * I)); simp
  · exact mul_nonneg (Real.exp_nonneg _) (by norm_num)
theorem DerivUpperBnd_aux3 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * ↑N ^ (1 - s) / (1 - s)‖ ≤ A.exp * 2 * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  rw [norm_div, norm_mul, mul_div_assoc, mul_comm]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.1
    convert le_trans h ?_ using 1
    · simp [s, norm_natCast_cpow_of_pos Npos _, N]
    · gcongr; exact UpperBnd_aux2 t_gt hσ.1
  · rw [natCast_log, norm_complex_log_ofNat]
    exact Real.log_le_log (by positivity) N_le_t
theorem DerivUpperBnd_aux4 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * (N : ℂ) ^ (-s) / 2‖ ≤ A.exp * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  rw [norm_div, norm_mul, mul_div_assoc, mul_comm, RCLike.norm_ofNat]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.2.1
    convert le_trans h (UpperBnd_aux2 t_gt hσ.1) using 1
    simp [s, norm_natCast_cpow_of_pos Npos _, N]
  · rw [natCast_log, norm_complex_log_ofNat]
    exact Real.log_le_log (by positivity) N_le_t
theorem DerivUpperBnd_aux5 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → 1 / 2 < σ →
    ‖1 * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1)‖ ≤
    1 / 3 * (2 * |t| * ↑N ^ (-σ) / σ) := by
  intro N s Npos σ_gt
  have neZero : s ≠ 0 := by
    contrapose! σ_gt
    simp only [Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, zero_re, add_im, mul_im, zero_add, zero_im, s] at σ_gt
    linarith
  have : 1 = 1 / s * s := by field_simp
  nth_rewrite 1 [this]
  rw [mul_assoc, norm_mul]
  apply mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · simp only [s, norm_div, norm_one]
    apply one_div_le_one_div (norm_pos_iff.mpr neZero) (by norm_num) |>.mpr
    apply le_trans t_gt.le ?_
    convert! abs_im_le_norm (σ + t * I); simp
  · have hσ : σ ∈ Ioc 0 2 := ⟨(by linarith), hσ.2⟩
    simp only [s]
    have := ZetaBnd_aux1 N (by omega) hσ (by linarith)
    simp only [div_cpow_eq_cpow_neg] at this
    convert! this using 1; congr; funext x; ring_nf
theorem DerivUpperBnd_aux6 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    0 < N → ↑N ≤ |t| → ↑σ + ↑t * I ≠ 1 → 1 / 2 < σ →
    2 * |t| * ↑N ^ (-σ) / σ ≤ 2 * (8 * A.exp) := by
  intro N Npos N_le_t neOne σ_gt
  rw [mul_div_assoc, mul_assoc]
  apply mul_le_mul_iff_right₀ (by norm_num) |>.mpr
  have h := UpperBnd_aux6 t_gt ⟨σ_gt, hσ.2⟩ neOne Npos N_le_t |>.2.2
  apply le_trans (mul_le_mul_iff_right₀ (a := |t|) (by positivity) |>.mpr h) ?_
  rw [← mul_assoc, mul_comm _ 8, mul_assoc]
  gcongr
  convert! UpperBnd_aux2 t_gt hσ.1 using 1
  rw [mul_comm, ← Real.rpow_add_one (by positivity)]; ring_nf
lemma DerivUpperBnd_aux7_1 {x σ t : ℝ} (hx : 1 ≤ x) :
    let s := ↑σ + ↑t * I;
    ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ = |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
  have xpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have : ‖(x.log : ℂ)‖ = x.log := Complex.norm_of_nonneg <| Real.log_nonneg hx
  simp [← norm_real, this, Complex.norm_cpow_eq_rpow_re_of_pos xpos, ← Real.norm_eq_abs, ← ofReal_ofNat,
    ← ofReal_inv, ← ofReal_add, ← ofReal_sub, ← ofReal_intCast, one_div]
lemma DerivUpperBnd_aux7_2 {x σ : ℝ} (hx : 1 ≤ x) :
    |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log ≤ x ^ (-σ - 1) * x.log := by
  rw [← one_mul (x ^ (-σ - 1) * Real.log x), mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (by bound)
  exact le_trans (ZetaSum_aux1_3 x) (by norm_num)
lemma DerivUpperBnd_aux7_3 {x σ : ℝ} (xpos : 0 < x) (σnz : σ ≠ 0) :
    HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  have h1 := Real.hasDerivAt_rpow_const (p := -σ) (Or.inl xpos.ne.symm)
  have h2 := h1.const_mul (1 / σ^2)
  have cancel : 1 / σ^2 * σ = 1 / σ := by field_simp
  rw [neg_mul, mul_neg, ← mul_assoc, cancel] at h2
  have h3 := Real.hasDerivAt_log xpos.ne.symm
  have h4 := HasDerivAt.mul (h1.const_mul (1 / σ)) h3
  have cancel := Real.rpow_add xpos (-σ) (-1)
  have : -σ + -1 = -σ - 1 := by rfl
  rw [← Real.rpow_neg_one x, mul_assoc (1 / σ) (x ^ (-σ)), ← cancel, this] at h4
  convert! h2.add h4 |>.neg using 1
  field_simp; ring
lemma DerivUpperBnd_aux7_3' {a σ : ℝ} (apos : 0 < a) (σnz : σ ≠ 0) :
    ∀ x ∈ Ici a, HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  intro x hx
  simp at hx
  exact DerivUpperBnd_aux7_3 (by linarith) σnz
lemma DerivUpperBnd_aux7_nonneg {a σ : ℝ} (ha : 1 ≤ a) :
    ∀ x ∈ Ioi a, 0 ≤ x ^ (-σ - 1) * Real.log x := by
  intro x hx
  simp at hx
  bound
lemma DerivUpperBnd_aux7_tendsto {σ : ℝ} (σpos : 0 < σ) :
    Tendsto (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t)) atTop (nhds 0) := by
  have h1 := tendsto_rpow_neg_atTop σpos
  have h2 := h1.const_mul (1 / σ^2)
  have h3 : Tendsto (fun t : ℝ ↦ t ^ (-σ) * Real.log t) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_pow_atTop σ 1 σpos
    simp only [Real.rpow_one] at this
    apply Tendsto.congr' _ this
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [mul_comm]
    apply div_rpow_eq_rpow_neg _ _ _ hx
  have h4 := h3.const_mul (1 / σ)
  have h5 := (h2.add h4).neg
  convert h5 using 1
  · ext; ring
  simp
lemma DerivUpperBnd_aux7_4 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ x ^ (-σ - 1) * Real.log x) (Ioi a) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg' (l := 0)
  · exact DerivUpperBnd_aux7_3' (by linarith) (by linarith)
  · exact DerivUpperBnd_aux7_nonneg ha
  · exact DerivUpperBnd_aux7_tendsto σpos
lemma DerivUpperBnd_aux7_5 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ |(↑⌊x⌋ + (1 : ℝ) / 2 - x)| * x ^ (-σ - 1) * Real.log x)
      (Ioi a) volume := by
  simp_rw [mul_assoc]
  apply Integrable.bdd_mul (c := 1 / 2) <| DerivUpperBnd_aux7_4 σpos ha
  · exact Measurable.aestronglyMeasurable <| Measurable.abs measurable_floor_add_half_sub
  apply ae_of_all
  intro x
  simp only [Real.norm_eq_abs, _root_.abs_abs]
  exact  ZetaSum_aux1_3 x
lemma DerivUpperBnd_aux7_integral_eq {a σ : ℝ} (ha : 1 ≤ a) (σpos : 0 < σ) :
    ∫ (x : ℝ) in Ioi a, x ^ (-σ - 1) * Real.log x =
      1 / σ^2 * a ^ (-σ) + 1 / σ * a ^ (-σ) * Real.log a := by
  convert integral_Ioi_of_hasDerivAt_of_nonneg'
    (DerivUpperBnd_aux7_3' (by linarith) (by linarith))
    (DerivUpperBnd_aux7_nonneg ha) (DerivUpperBnd_aux7_tendsto σpos) using 1
  ring
theorem DerivUpperBnd_aux7 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ ≤
      6 * |t| * ↑N ^ (-σ) / σ * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  have σpos : 0 < σ := lt_trans (by norm_num) σ_gt
  rw [norm_mul, (by ring : 6 * |t| * ↑N ^ (-σ) / σ * Real.log |t| = (2 * |t|) * (3 * ↑N ^ (-σ) / σ * Real.log |t|))]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply le_trans (by apply norm_add_le)
    simp [abs_of_pos σpos]
    linarith [hσ.2]
  apply le_trans (by apply norm_integral_le_integral_norm)
  calc ∫ (x : ℝ) in Ioi (N : ℝ), ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖
    _ = ∫ (x : ℝ) in Ioi (N : ℝ), |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
      apply setIntegral_congr_fun (by measurability)
      intro x hx
      simp only [mem_Ioi] at hx
      exact DerivUpperBnd_aux7_1 (lt_of_le_of_lt (mod_cast Npos) hx).le
    _ ≤ ∫ (x : ℝ) in Ioi (N : ℝ), x ^ (-σ - 1) * x.log := by
      apply setIntegral_mono_on _ _ (by measurability)
      · intro x hx
        exact DerivUpperBnd_aux7_2 (lt_of_le_of_lt (mod_cast Npos) hx).le
      · apply DerivUpperBnd_aux7_5 σpos (mod_cast Npos)
      apply DerivUpperBnd_aux7_4 σpos (mod_cast Npos)
    _ = 1 / σ^2 * N ^ (-σ) + 1 / σ * N ^ (-σ) * Real.log N :=
      DerivUpperBnd_aux7_integral_eq (mod_cast Npos) σpos
    _ ≤ 3 * ↑N ^ (-σ) / σ * |t|.log := by
      have h2 : 1 / σ * ↑N ^ (-σ) * Real.log ↑N ≤ ↑N ^ (-σ) / σ * Real.log |t| := calc
        _ = ↑N ^ (-σ) / σ * Real.log N := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.log_le_log (mod_cast Npos) N_le_t
      have : 2 ≤ 2 * Real.log |t| := by
        nth_rewrite 1  [← mul_one 2]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact logt_gt_one t_gt.le |>.le
      have h1 : 1 / σ^2 * ↑N ^ (-σ) ≤ 2 * ↑N ^ (-σ) / σ * Real.log |t| := calc
        1 / σ^2 * ↑N ^ (-σ) = (↑N ^ (-σ) / σ) * (1 / σ) := by ring
        _ ≤ ↑N ^ (-σ) / σ * (2 * Real.log |t|):= by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply le_trans _ this
          exact (one_div_le σpos (by norm_num)).mpr σ_gt.le
        _ = _ := by ring
      convert! add_le_add h1 h2 using 1
      ring
lemma ZetaDerivUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * 59;
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * (Real.log n)‖ +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖
        ≤ C * Real.log |t| ^ 2 := by
  dsimp only
  obtain ⟨Npos, N_le_t, logt_gt, σ_gt, _, neOne⟩ := UpperBnd_aux hA t_gt hσ.1
  replace σ_gt : 1 / 2 < σ := by linarith [hA.2]
  have h6 := DerivUpperBnd_aux6 t_gt hσ Npos N_le_t neOne σ_gt
  have e0 := Real.exp_pos A
  have := mul_le_mul_of_nonneg_right (by linarith [show 6 * |t| * ↑⌊|t|⌋₊ ^ (-σ) / σ =
    3 * (2 * |t| * ↑⌊|t|⌋₊ ^ (-σ) / σ) by ring] : 6 * |t| * ↑⌊|t|⌋₊ ^ (-σ) / σ ≤ 48 * Real.exp A)
    (by linarith : 0 ≤ Real.log |t|)
  have := mul_le_mul_of_nonneg_left (by nlinarith : Real.log |t| ≤ Real.log |t| ^ 2) e0.le
  have := mul_le_mul_of_nonneg_left (by nlinarith : 1 ≤ Real.log |t| ^ 2) e0.le
  linarith [DerivUpperBnd_aux1 hA hσ.1 t_gt le_rfl, DerivUpperBnd_aux2 t_gt hσ Npos N_le_t neOne σ_gt,
    DerivUpperBnd_aux3 t_gt hσ Npos N_le_t neOne σ_gt, DerivUpperBnd_aux4 t_gt hσ Npos N_le_t neOne σ_gt,
    DerivUpperBnd_aux5 t_gt hσ Npos σ_gt, DerivUpperBnd_aux7 t_gt hσ Npos N_le_t neOne σ_gt]
lemma ZetaDerivUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2),
    ‖deriv riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| ^ 2 := by
  obtain ⟨A, hA, _, _, _⟩ := ZetaUpperBnd
  let C := Real.exp A * 59
  refine ⟨A, hA, C, by positivity, ?_⟩
  intro σ t t_gt ⟨σ_ge, σ_le⟩
  obtain ⟨Npos, N_le_t, _, _, σPos, neOne⟩ := UpperBnd_aux hA t_gt σ_ge
  rw [← DerivZeta0EqDerivZeta Npos (by simp [σPos]) neOne]
  set N : ℕ := ⌊|t|⌋₊
  rw [(HasDerivAtZeta0 Npos (s := σ + t * I) (by simp [σPos]) neOne).deriv]
  dsimp only [ζ₀']
  rw [← add_assoc]
  set aa := ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)
  set bb := -(N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I)) ^ 2
  set cc := (Real.log N) * (N : ℂ) ^ (1 - (σ + t * I)) / (1 - (σ + t * I))
  set dd := (Real.log N) * (N : ℂ) ^ (-(σ + t * I)) / 2
  set ee := 1 * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1)
  set ff := (σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(σ + t * I) - 1) * -(Real.log x)
  rw [(by ring : aa + (bb + cc) + dd + ee + ff = aa + bb + cc + dd + ee + ff)]
  apply le_trans (by apply norm_add₆_le) ?_
  convert ZetaDerivUpperBnd' hA t_gt ⟨σ_ge, σ_le⟩
lemma ZetaNear1BndExact :
    ∃ (c : ℝ) (_ : 0 < c), ∀ (σ : ℝ) (_ : σ ∈ Ioc 1 2), ‖riemannZeta σ‖ ≤ c / (σ - 1) := by
  obtain ⟨g, hg, -, hζ⟩ := zetaExt
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
    (hg.continuous.comp continuous_ofReal).continuousOn
  refine ⟨max C 1, by positivity, fun σ hσ ↦ ?_⟩
  have h1 : (0:ℝ) < σ - 1 := by linarith [hσ.1]
  rw [hζ σ (by exact_mod_cast hσ.1.ne'), norm_div, ← ofReal_one, ← ofReal_sub, norm_real,
    Real.norm_of_nonneg h1.le]
  exact div_le_div_of_nonneg_right ((hC σ (Ioc_subset_Icc_self hσ)).trans (le_max_left _ _)) h1.le
lemma norm_zeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖riemannZeta (1 + x) ^ 3 * riemannZeta (1 + x + I * y) ^ 4 * riemannZeta (1 + x + 2 * I * y)‖ ≥ 1 := by
  have h₀ : 1 < ( 1 + x : ℂ).re := by simp[hx]
  have h₁ : 1 < (1 + x + I * y).re := by simp [hx]
  have h₂ : 1 < (1 + x + 2 * I * y).re := by simp [hx]
  simpa only [one_pow, norm_mul, norm_pow, DirichletCharacter.LSeries_modOne_eq,
    LSeries_one_eq_riemannZeta, h₀, h₁, h₂] using
    DirichletCharacter.norm_LSeries_product_ge_one (1 : DirichletCharacter ℂ 1) hx y
lemma ZetaInvBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / ‖riemannZeta (σ + t * I)‖ ≤ ‖riemannZeta σ‖ ^ ((3 : ℝ) / 4) * ‖riemannZeta (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
  apply (div_le_iff₀ ?_).mpr
  · apply (Real.rpow_le_rpow_iff (z := 4) (by norm_num) ?_ (by norm_num)).mp
    · simp only [Real.one_rpow]
      rw [Real.mul_rpow, Real.mul_rpow, ← Real.rpow_mul, ← Real.rpow_mul]
      · simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          IsUnit.div_mul_cancel, Real.rpow_one]
        conv => rw [mul_assoc]; rhs; rhs; rw [mul_comm]
        rw [← mul_assoc]
        have := norm_zeta_product_ge_one (x := σ - 1) (by linarith) t
        simp_rw [ge_iff_le, norm_mul, norm_pow, ofReal_sub, ofReal_one, add_sub_cancel, ← Real.rpow_natCast] at this
        convert this using 3 <;> ring_nf
      any_goals ring_nf
      any_goals apply norm_nonneg
      any_goals apply Real.rpow_nonneg <| norm_nonneg _
      apply mul_nonneg <;> apply Real.rpow_nonneg <| norm_nonneg _
    · refine mul_nonneg (mul_nonneg ?_ ?_) ?_ <;> simp [Real.rpow_nonneg]
  · have s_ne_one : σ + t * I ≠ 1 := by
      contrapose! σ_gt; apply le_of_eq; apply And.left; simpa [Complex.ext_iff] using σ_gt
    simpa using riemannZeta_ne_zero_of_one_le_re (by simp [σ_gt.le])
lemma ZetaInvBound2 :
    ∃ C > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    1 / ‖riemannZeta (σ + t * I)‖ ≤ C * (σ - 1) ^ (-(3 : ℝ) / 4) * (Real.log |t|) ^ ((1 : ℝ) / 4) := by
  obtain ⟨A, ha, C, hC, h⟩ := ZetaUpperBnd
  obtain ⟨c, hc, h_inv⟩ := ZetaNear1BndExact
  refine ⟨(2 * C) ^ ((1 : ℝ)/ 4) * c ^ ((3 : ℝ)/ 4), by positivity, fun {σ} hσ t ht ↦ ?_⟩
  have h1 : 0 < σ - 1 := by linarith [hσ.1]
  have hL := logt_gt_one ht.le
  have h2t : 3 < |2 * t| := by rw [abs_mul, abs_two]; linarith
  have h2 : Real.log |2 * t| ≤ 2 * Real.log |t| := by
    rw [abs_mul, abs_two, Real.log_mul two_ne_zero (by linarith : (0:ℝ) < |t|).ne']
    linarith [Real.log_two_lt_d9]
  have h0 : 0 ≤ A / Real.log |2 * t| := div_nonneg ha.1.le (Real.log_nonneg (by linarith))
  have h3 := h σ (2 * t) h2t ⟨by linarith [hσ.1], hσ.2⟩
  push_cast at h3
  calc _ ≤ _ := ZetaInvBound1 hσ.1
    _ ≤ (c / (σ - 1)) ^ ((3 : ℝ) / 4) * (2 * C * Real.log |t|) ^ ((1 : ℝ) / 4) :=
      mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) (h_inv σ hσ) (by norm_num))
        (Real.rpow_le_rpow (norm_nonneg _) (by linarith [mul_le_mul_of_nonneg_left h2 hC.le])
        (by norm_num)) (by positivity) (by positivity)
    _ = _ := by
      rw [Real.div_rpow hc.le h1.le, Real.mul_rpow (by positivity) (by linarith), neg_div,
        Real.rpow_neg h1.le]
      ring
lemma ZetaLowerBound3 :
    ∃ c > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    c * (σ - 1) ^ ((3 : ℝ) / 4) / (Real.log |t|) ^ ((1 : ℝ) / 4) ≤ ‖riemannZeta (σ + t * I)‖ := by
  obtain ⟨C, hC, h⟩ := ZetaInvBound2
  refine ⟨C⁻¹, inv_pos.mpr hC, fun {σ} hσ t ht ↦ ?_⟩
  have h1 : 0 < σ - 1 := by linarith [hσ.1]
  have ha := Real.rpow_pos_of_pos h1 ((3 : ℝ) / 4)
  have hL := Real.rpow_pos_of_pos (by linarith [logt_gt_one ht.le] : 0 < Real.log |t|) ((1 : ℝ) / 4)
  have := h hσ t ht
  rw [neg_div, Real.rpow_neg h1.le] at this
  calc _ = 1 / (C * ((σ - 1) ^ ((3 : ℝ) / 4))⁻¹ * Real.log |t| ^ ((1 : ℝ) / 4)) := by
        field_simp [ha.ne', hL.ne', hC.ne']
    _ ≤ _ := (one_div_le (norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ.1)))
      (mul_pos (mul_pos hC (inv_pos.mpr ha)) hL)).mp this
lemma deriv_fun_re {t : ℝ} {f : ℂ → ℂ} (diff : ∀ (σ : ℝ), DifferentiableAt ℂ f (↑σ + ↑t * I)) :
    (deriv fun {σ₂ : ℝ} ↦ f (σ₂ + t * I)) = fun (σ : ℝ) ↦ deriv f (σ + t * I) := by
  ext σ
  have := deriv_comp (h := fun (σ : ℝ) ↦ σ + t * I) (h₂ := f) σ (diff σ) ?_
  · simp only [deriv_add_const', _root_.deriv_ofReal, mul_one] at this
    exact this
  · apply DifferentiableAt.add_const _ <| differentiableAt_ofReal σ
lemma Zeta_eq_int_derivZeta {σ₁ σ₂ t : ℝ} (t_ne_zero : t ≠ 0) :
    (∫ σ in σ₁..σ₂, deriv riemannZeta (σ + t * I)) = riemannZeta (σ₂ + t * I) - riemannZeta (σ₁ + t * I) := by
  have diff : ∀ (σ : ℝ), DifferentiableAt ℂ riemannZeta (σ + t * I) := by
    intro σ
    refine differentiableAt_riemannZeta ?_
    contrapose! t_ne_zero; apply And.right; simpa [Complex.ext_iff] using t_ne_zero
  apply intervalIntegral.integral_deriv_eq_sub'
  · exact deriv_fun_re diff
  · intro s _
    apply DifferentiableAt.comp
    · exact (diff s).restrictScalars ℝ
    · exact DifferentiableAt.add_const (c := t * I) <| differentiableAt_ofReal _
  · apply ContinuousOn.comp (g := deriv riemannZeta) ?_ ?_ (mapsTo_image _ _)
    · apply HasDerivAt.continuousOn (f' := deriv <| deriv riemannZeta)
      intro x hx
      apply hasDerivAt_deriv_iff.mpr
      replace hx : x ≠ 1 := by
        contrapose! hx
        simp only [hx, mem_image, Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
          I_im, mul_one, sub_self, add_zero, one_re, add_im, mul_im, zero_add, one_im, not_exists,
          not_and]
        exact fun _ _ _ ↦ t_ne_zero
      exact differentiableAt_deriv_riemannZeta hx
    · exact continuous_ofReal.continuousOn.add continuousOn_const
lemma Zeta_diff_Bnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ₁ σ₂ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : 1 - A / Real.log |t| ≤ σ₁) (_ : σ₂ ≤ 2) (_ : σ₁ < σ₂),
    ‖riemannZeta (σ₂ + t * I) - riemannZeta (σ₁ + t * I)‖ ≤  C * Real.log |t| ^ 2 * (σ₂ - σ₁) := by
  obtain ⟨A, hA, C, Cpos, hC⟩ := ZetaDerivUpperBnd
  refine ⟨A, hA, C, Cpos, ?_⟩
  intro σ₁ σ₂ t t_gt σ₁_ge σ₂_le σ₁_lt_σ₂
  have t_ne_zero : t ≠ 0 := by contrapose! t_gt; simp only [t_gt, abs_zero, Nat.ofNat_nonneg]
  rw [← Zeta_eq_int_derivZeta t_ne_zero]
  convert intervalIntegral.norm_integral_le_of_norm_le_const ?_ using 1
  · congr; rw [_root_.abs_of_nonneg (by linarith)]
  · intro σ hσ; rw [uIoc_of_le σ₁_lt_σ₂.le, mem_Ioc] at hσ
    exact hC σ t t_gt ⟨le_trans σ₁_ge hσ.1.le, le_trans hσ.2 σ₂_le⟩
lemma ZetaInvBnd_aux' {t : ℝ} (logt_gt_one : 1 < Real.log |t|) : Real.log |t| < Real.log |t| ^ (9 : ℝ) := by
  nth_rewrite 1 [← Real.rpow_one <| Real.log |t|]
  exact mod_cast Real.rpow_lt_rpow_left_iff (y := 1) (z := 9) logt_gt_one |>.mpr (by norm_num)
lemma ZetaInvBnd_aux {t : ℝ} (logt_gt_one : 1 < Real.log |t|) : Real.log |t| ≤ Real.log |t| ^ (9 : ℝ) :=
    ZetaInvBnd_aux' logt_gt_one |>.le
lemma ZetaInvBnd_aux2 {A C₁ C₂ : ℝ} (Apos : 0 < A) (C₁pos : 0 < C₁) (C₂pos : 0 < C₂)
    (hA : A ≤ 1 / 2 * (C₁ / (C₂ * 2)) ^ (4 : ℝ)) :
    0 < (C₁ * A ^ (3 / 4 : ℝ) - C₂ * 2 * A)⁻¹ := by
  simp only [inv_pos, sub_pos]
  apply div_lt_iff₀ (by positivity) |>.mp
  rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity), mul_assoc]
  apply lt_div_iff₀' (by positivity) |>.mp
  nth_rewrite 1 [← Real.rpow_one A]
  rw [← Real.rpow_add (by positivity)]
  norm_num
  apply Real.rpow_lt_rpow_iff (z := 4) (by positivity) (by positivity) (by positivity) |>.mp
  rw [← Real.rpow_mul (by positivity)]
  norm_num
  apply lt_of_le_of_lt hA
  rw [div_mul_comm, mul_one, Real.rpow_ofNat]
  apply half_lt_self
  positivity
lemma ZetaLowerBndIco :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (c : ℝ) (_ : 0 < c), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ (9 : ℝ)) (1 + A / (Real.log |t|) ^ (9 : ℝ))),
    c / (Real.log |t|) ^ (7 : ℝ) ≤ ‖riemannZeta (σ + t * I)‖ := by
  obtain ⟨C', C'pos, hC₁⟩ := ZetaInvBound2
  obtain ⟨A', hA', C₂, C₂pos, hC₂⟩ := Zeta_diff_Bnd
  set C₁ := 1 / C'
  let A := min A' <| (1 / 2 : ℝ) * (C₁ / (C₂ * 2)) ^ (4 : ℝ)
  have Apos : 0 < A := by have := hA'.1; positivity
  have Ale : A ≤ 1 / 2 := by dsimp only [A]; apply min_le_iff.mpr; left; exact hA'.2
  set C := (C₁ * A ^ (3 / 4 : ℝ) - C₂ * 2 * A)⁻¹
  have Cpos : 0 < C := by
    refine ZetaInvBnd_aux2 (by positivity) (by positivity) (by positivity) ?_
    apply min_le_right
  refine ⟨A, ⟨Apos, by linarith [hA'.2]⟩ , C⁻¹, inv_pos.mpr Cpos, ?_⟩
  intro σ t t_gt hσ
  have logt_gt_one := logt_gt_one t_gt.le
  have σ_ge : 1 - A / Real.log |t| ≤ σ := by
    apply le_trans ?_ hσ.1
    suffices A / Real.log |t| ^ (9 : ℝ) ≤ A / Real.log |t| by linarith
    exact div_le_div₀ Apos.le (by rfl) (by positivity) <| ZetaInvBnd_aux logt_gt_one
  obtain ⟨_, _, neOne⟩ := UpperBnd_aux ⟨Apos, Ale⟩ t_gt σ_ge
  set σ' := 1 + A / Real.log |t| ^ (9 : ℝ)
  have σ'_gt : 1 < σ' := by simp only [σ', lt_add_iff_pos_right]; positivity
  have σ'_le : σ' ≤ 2 := by
    simp only [σ']
    suffices A / Real.log |t| ^ (9 : ℝ) < 1 by linarith
    apply div_lt_one (by positivity) |>.mpr
    exact lt_trans₄ (by linarith) logt_gt_one <| ZetaInvBnd_aux' logt_gt_one
  set s := σ + t * I
  set s' := σ' + t * I
  have e : C⁻¹ / Real.log |t| ^ (7 : ℝ) = 1 / (C * Real.log |t| ^ (7 : ℝ)) := by
    rw [div_mul_eq_div_div, one_div]
  rw [e]
  have pos_aux : 0 < (σ' - 1) := by linarith
  calc
    _ ≥ ‖riemannZeta s'‖ - ‖riemannZeta s - riemannZeta s'‖ := ?_
    _ ≥ C₁ * (σ' - 1) ^ ((3 : ℝ)/ 4) * Real.log |t|  ^ ((-1 : ℝ)/ 4) - C₂ * Real.log |t| ^ 2 * (σ' - σ) := ?_
    _ ≥ C₁ * (A / Real.log |t| ^ (9 : ℝ)) ^ ((3 : ℝ)/ 4) * Real.log |t| ^ ((-1 : ℝ)/ 4) - C₂ * Real.log |t| ^ (2 : ℝ) * 2 * A / Real.log |t| ^ (9 : ℝ) := ?_
    _ ≥ C₁ * A ^ ((3 : ℝ)/ 4) * Real.log |t| ^ (-7 : ℝ) - C₂ * 2 * A * Real.log |t| ^ (-7 : ℝ) := ?_
    _ = (C₁ * A ^ ((3 : ℝ)/ 4) - C₂ * 2 * A) * Real.log |t| ^ (-7 : ℝ) := by ring
    _ ≥ _ := ?_
  · apply ge_iff_le.mpr
    convert norm_sub_norm_le (a := riemannZeta s') (b := riemannZeta s' - riemannZeta s) using 1
    · rw [(by simp : riemannZeta s' - riemannZeta s = -(riemannZeta s - riemannZeta s'))]; simp only [norm_neg]
    · simp
  · apply sub_le_sub
    · have := one_div_le ?_ (by positivity) |>.mp <| hC₁ ⟨σ'_gt, σ'_le⟩ t t_gt
      · convert this using 1
        rw [one_div, mul_inv_rev, mul_comm, mul_inv_rev, mul_comm _ C'⁻¹]
        simp only [one_div C', C₁]
        congr <;> (rw [← Real.rpow_neg (by linarith), neg_div]); rw [neg_neg]
      · apply norm_pos_iff.mpr <| riemannZeta_ne_zero_of_one_lt_re (by simp [σ'_gt])
    · rw [(by simp : riemannZeta s - riemannZeta s' = -(riemannZeta s' - riemannZeta s)), norm_neg]
      refine hC₂ σ σ' t t_gt ?_ σ'_le <| by rw [Set.mem_Ico] at hσ; exact hσ.2
      apply le_trans ?_ hσ.1
      rw [tsub_le_iff_right, ← add_sub_right_comm, le_sub_iff_add_le, add_le_add_iff_left]
      exact div_le_div₀ hA'.1.le (by simp [A]) (by positivity) <| ZetaInvBnd_aux logt_gt_one
  · apply sub_le_sub (by simp only [add_sub_cancel_left, σ']; exact_mod_cast le_rfl) ?_
    rw [mul_div_assoc, mul_assoc _ 2 _]
    apply mul_le_mul (by exact_mod_cast le_rfl) ?_ (by linarith [hσ.2]) (by positivity)
    suffices h : σ' + (1 - A / Real.log |t| ^ (9 : ℝ)) ≤ (1 + A / Real.log |t| ^ (9 : ℝ)) + σ by
      simp only [tsub_le_iff_right]
      convert! le_sub_right_of_add_le h using 1; ring_nf
    exact add_le_add (by linarith) (by linarith [hσ.1])
  · simp_rw [tsub_le_iff_right, div_eq_mul_inv _ (Real.log |t| ^ (9 : ℝ))]
    rw [← Real.rpow_neg (by positivity), Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_mul (by positivity)]
    ring_nf
    conv => rhs; lhs; rw [mul_assoc, ← Real.rpow_add (by positivity)]
    rw [(by ring : C₂ * Real.log |t| ^ (2 : ℝ) * A * Real.log |t| ^ (-9 : ℝ) * 2 = C₂ * (Real.log |t| ^ (2 : ℝ) * Real.log |t| ^ (-9 : ℝ) ) * A * 2)]
    rw [← Real.rpow_add (by positivity)]; norm_num; group; exact le_rfl
  · apply div_le_iff₀ (by positivity) |>.mpr
    conv => rw [mul_assoc]; rhs; rhs; rw [mul_comm C, ← mul_assoc, ← Real.rpow_add (by positivity)]
    have := inv_inv C ▸ mul_inv_cancel₀ (a := C⁻¹) (by positivity) |>.symm.le
    simpa [C] using this
lemma ZetaInvBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ (9 : ℝ)) (1 + A / (Real.log |t|) ^ (9 : ℝ))),
    1 / ‖riemannZeta (σ + t * I)‖ ≤ C * (Real.log |t|) ^ (7 : ℝ) := by
  obtain ⟨A, hA, c, hc, h⟩ := ZetaLowerBndIco
  refine ⟨A, hA, c⁻¹, inv_pos.mpr hc, fun σ t ht hσ ↦ ?_⟩
  have hL := Real.rpow_pos_of_pos (one_pos.trans (logt_gt_one ht.le)) (7 : ℝ)
  have := h σ t ht hσ
  rw [one_div_le ((div_pos hc hL).trans_le this) (mul_pos (inv_pos.mpr hc) hL)]
  calc 1 / (c⁻¹ * Real.log |t| ^ (7 : ℝ)) = c / Real.log |t| ^ (7 : ℝ) := by
        rw [one_div, mul_inv, inv_inv, div_eq_mul_inv]
    _ ≤ _ := this
lemma ZetaLowerBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (c : ℝ) (_ : 0 < c),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ (9 : ℝ)) 1),
    c / (Real.log |t|) ^ (7 : ℝ) ≤ ‖riemannZeta (σ + t * I)‖ := by
  obtain ⟨A, hA, c, hc, h⟩ := ZetaLowerBndIco
  exact ⟨A, hA, c, hc, fun σ t ht hσ ↦ h σ t ht ⟨hσ.1, hσ.2.trans_le (le_add_of_nonneg_right
    (div_nonneg hA.1.le (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _)))⟩⟩
def ZetaZeroFreeGenProp (n : ℝ) : Prop := ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)),
    ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|) (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ n) 1),
    riemannZeta (σ + t * I) ≠ 0
lemma ZetaZeroFree9 : ZetaZeroFreeGenProp 9 := by
  obtain ⟨A, hA, c, hc, h_lower⟩ := ZetaLowerBnd
  refine ⟨A, hA, ?_⟩
  intro σ t ht hσ h_zero
  have := h_lower σ t ht hσ
  rw [h_zero, norm_zero] at this
  have pos_bound : 0 < c / (Real.log |t|) ^ (7 : ℝ) := by
    apply div_pos hc
    apply Real.rpow_pos_of_pos
    apply Real.log_pos
    linarith
  linarith
lemma LogDerivZetaBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / Real.log |t| ^ (9 : ℝ)) (1 + A / Real.log |t| ^ (9 : ℝ))),
      ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| ^ (9 : ℝ) := by
  obtain ⟨A, hA, C, hC, h⟩ := ZetaInvBnd
  obtain ⟨A', hA', C', hC', h'⟩ := ZetaDerivUpperBnd
  use min A A', ⟨lt_min hA.1 hA'.1, min_le_of_right_le hA'.2⟩, C * C', mul_pos hC hC'
  intro σ t t_gt ⟨σ_ge, σ_lt⟩
  have logt_gt : (1 : ℝ) < Real.log |t| := logt_gt_one t_gt.le
  have σ_ge' : 1 - A / Real.log |t| ^ (9 : ℝ) ≤ σ := by
    apply le_trans (tsub_le_tsub_left ?_ 1) σ_ge
    apply div_le_div_of_nonneg_right (min_le_left A A')
    apply Real.rpow_nonneg
    linarith
  have σ_ge'' : 1 - A' / Real.log |t| ≤ σ := by
    apply le_trans (tsub_le_tsub_left ?_ 1) σ_ge
    apply div_le_div₀ hA'.1.le (min_le_right A A') (lt_trans (by norm_num) logt_gt) ?_
    rw [← Real.rpow_one (Real.log |t|), ← Real.rpow_mul (by linarith), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le logt_gt.le Nat.one_le_ofNat
  replace h := h σ t t_gt ⟨σ_ge', by calc
    σ < 1 + min A A' / Real.log |t| ^ (9 : ℝ) := σ_lt
    _ ≤ 1 + A / Real.log |t| ^ (9 : ℝ) := by gcongr; simp⟩
  replace h' := h' σ t t_gt ⟨σ_ge'', by
   calc
    σ ≤ 1 + min A A' / Real.log |t| ^ (9 : ℝ) := by linarith [σ_lt]
    _ ≤ 1 + (1/2) / Real.log |t| ^ (9 : ℝ) := by gcongr; simp [Set.mem_Ioc] at hA' hA ⊢ ; simp [hA.2]
    _ ≤ 1 + (1/2) / 1 := by
          gcongr
          calc
            1 ≤ Real.log |t| := by linarith
            _ ≤ (Real.log |t|) ^ (9 : ℝ) := Real.self_le_rpow_of_one_le (by linarith) (by linarith)
    _ ≤ 2 := by linarith
    ⟩
  simp only [norm_div]
  convert! mul_le_mul h h' (by simp) ?_ using 1 <;> (norm_cast; ring_nf); positivity
lemma ZetaNoZerosInBox (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), riemannZeta (σ' + t * I) ≠ 0 := by
  obtain ⟨g, hg, g1, hζ⟩ := zetaExt
  have hK : (fun t : ℝ ↦ 1 + t * I) '' Icc (-T) T ⊆ g ⁻¹' {0}ᶜ := by
    rintro _ ⟨t, -, rfl⟩
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]
    rcases eq_or_ne t 0 with rfl | h0
    · simp [g1]
    · intro e
      exact riemannZeta_ne_zero_of_one_le_re (s := 1 + t * I) (by simp)
        (by rw [hζ _ (by simpa using h0), e, zero_div])
  obtain ⟨δ, δ0, hδ⟩ := (isCompact_Icc.image (by fun_prop)).exists_thickening_subset_open
    (isOpen_compl_singleton.preimage hg.continuous) hK
  refine ⟨1 - δ / 2, by linarith, fun t ht σ' hσ' ↦ ?_⟩
  rcases le_or_gt 1 σ' with h | h
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa using h)
  have hs : (σ' : ℂ) + t * I - 1 ≠ 0 := fun e ↦ h.ne (by simpa [sub_eq_zero] using congrArg re e)
  rw [hζ _ (sub_ne_zero.mp hs)]
  refine div_ne_zero (hδ (Metric.mem_thickening_iff.mpr ⟨1 + t * I, ⟨t, abs_le.mp ht, rfl⟩, ?_⟩)) hs
  rw [Complex.dist_eq, add_sub_add_right_eq_sub, ← ofReal_one, ← ofReal_sub, norm_real,
    Real.norm_eq_abs, abs_of_neg (by linarith)]
  linarith
lemma LogDerivZetaHoloOn {S : Set ℂ} (s_ne_one : 1 ∉ S)
    (nonzero : ∀ s ∈ S, riemannZeta s ≠ 0) :
    HolomorphicOn (fun s ↦ deriv riemannZeta s / riemannZeta s) S := by
  apply DifferentiableOn.div _ _ nonzero <;> intro s hs <;> apply DifferentiableAt.differentiableWithinAt
  · apply differentiableAt_deriv_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one
  · apply differentiableAt_riemannZeta
    exact ne_of_mem_of_not_mem hs s_ne_one
theorem LogDerivZetaHolcSmallT :
    ∃ (σ₂ : ℝ) (_ : σ₂ < 1), HolomorphicOn (fun (s : ℂ) ↦ deriv riemannZeta s / (riemannZeta s))
      (( [[ σ₂, 2 ]] ×ℂ [[ -3, 3 ]]) \ {1}) := by
  obtain ⟨σ₂, hσ₂_lt_one, hζ_ne_zero⟩ := ZetaNoZerosInBox 3
  refine ⟨σ₂, hσ₂_lt_one, ?_⟩
  let U := ([[σ₂, 2]] ×ℂ [[-3, 3]]) \ {1}
  have s_in_U_im_le3 : ∀ s ∈ U, |s.im| ≤ 3 := by
    intro s hs
    rw [Set.mem_sdiff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, him⟩
    simp only [Set.mem_preimage] at him
    obtain ⟨him_lower, him_upper⟩ := him
    apply abs_le.2
    simp only [neg_le_self_iff, Nat.ofNat_nonneg, inf_of_le_left] at him_lower
    simp only [neg_le_self_iff, Nat.ofNat_nonneg, sup_of_le_right] at him_upper
    exact ⟨him_lower, him_upper⟩
  have s_in_U_re_ges2 : ∀ s ∈ U, σ₂ ≤ s.re := by
    intro s hs
    rw [Set.mem_sdiff_singleton] at hs
    rcases hs with ⟨hbox, _hne⟩
    rcases hbox with ⟨hre, _him⟩
    simp only [Set.mem_preimage] at hre
    obtain ⟨hre_lower, hre_upper⟩ := hre
    have : min σ₂ 2 = σ₂ := by
      apply min_eq_left
      linarith [hσ₂_lt_one]
    rwa [← this]
  apply LogDerivZetaHoloOn
  · exact Set.notMem_sdiff_of_mem rfl
  · intro s hs
    rw[← re_add_im s]
    apply hζ_ne_zero
    · apply s_in_U_im_le3 _ hs
    · apply s_in_U_re_ges2 _ hs
lemma LogDerivZetaHolcSmallT' : ∃ (σ₂ : ℝ)
  (_ : σ₂ ∈ Ioo 0 1), HolomorphicOn (fun (s : ℂ) ↦ deriv riemannZeta s / (riemannZeta s))
    (( [[ σ₂, 2 ]] ×ℂ [[ -3, 3 ]]) \ {1}) := by
  obtain ⟨σ₂', σ₂'_lt_one, holo2'⟩ := LogDerivZetaHolcSmallT
  let σ₂ : ℝ := max σ₂' (1 / 2)
  have σ₂_pos : 0 < σ₂ := by bound
  have σ₂_lt_one : σ₂ < 1 := by bound
  refine ⟨σ₂, ⟨σ₂_pos, σ₂_lt_one⟩, holo2'.mono (fun s hs ↦ ?_)⟩
  simp only [neg_le_self_iff, Nat.ofNat_nonneg, uIcc_of_le, Set.mem_sdiff, mem_reProdIm, mem_Icc,
    mem_singleton_iff] at hs ⊢
  refine ⟨?_, hs.2⟩
  refine ⟨?_, hs.1.2⟩
  rcases hs.1.1 with ⟨left, right⟩
  constructor
  · apply le_trans _ left
    apply min_le_min_right
    apply le_max_left
  · rw [max_eq_right (by linarith)] at right ⊢
    exact right
def LogDerivZetaHolcLargeTGenProp (n : ℝ) : Prop := ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)),
    ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ deriv riemannZeta s / (riemannZeta s))
      (( (Icc ((1 : ℝ) - A / Real.log T ^ n) 2)  ×ℂ (Icc (-T) T) ) \ {1})
lemma LogDerivZetaHolcLargeTGen {n : ℝ} (ZetaZeroFree : ZetaZeroFreeGenProp n) (n_pos : 0 < n) :
  LogDerivZetaHolcLargeTGenProp n := by
  obtain ⟨A, A_inter, restOfZetaZeroFree⟩ := ZetaZeroFree
  obtain ⟨σ₁, σ₁_lt_one, noZerosInBox⟩ := ZetaNoZerosInBox 3
  let A₀ := min A ((1 - σ₁) * Real.log 3 ^ n)
  refine ⟨A₀, ?_, ?_⟩
  · constructor
    · apply lt_min A_inter.1
      bound
    · exact le_trans (min_le_left _ _) A_inter.2
  intro T hT
  apply LogDerivZetaHoloOn
  · exact Set.notMem_sdiff_of_mem rfl
  intro s hs
  rcases le_or_gt 1 s.re with one_le|lt_one
  · exact riemannZeta_ne_zero_of_one_le_re one_le
  rw [← re_add_im s]
  have := Complex.mem_reProdIm.mp hs.1
  rcases lt_or_ge 3 |s.im| with gt3|le3
  · apply restOfZetaZeroFree _ _ gt3
    refine ⟨?_, lt_one⟩
    calc
      _ ≤ 1 - A₀ / Real.log T ^ n := by
        gcongr
        · exact A_inter.1.le
        · bound
        · bound
        · bound
        · exact abs_le.mpr ⟨this.2.1, this.2.2⟩
      _ ≤ _:= by exact this.1.1
  · apply noZerosInBox _ le3
    calc
      _ ≥ 1 - A₀ / Real.log T ^ n := by exact this.1.1
      _ ≥ 1 - A₀ / Real.log 3 ^ n := by
        gcongr
        apply le_min A_inter.1.le
        bound
      _ ≥ 1 - (((1 - σ₁) * Real.log 3 ^ n)) / Real.log 3 ^ n := by
        gcongr
        apply min_le_right
      _ = _ := by field_simp; simp
theorem LogDerivZetaHolcLargeT9 : LogDerivZetaHolcLargeTGenProp 9 := by
  apply LogDerivZetaHolcLargeTGen ZetaZeroFree9 Nat.ofNat_pos'
theorem summable_complex_then_summable_real_part (f : ℕ → ℂ)
    (h : Summable f) : Summable (fun n ↦ (f n).re) := by
  rcases h with ⟨s, hs⟩
  exact ⟨s.re,  hasSum_re hs⟩
open ArithmeticFunction (vonMangoldt)
open scoped ComplexOrder in
theorem dlog_riemannZeta_bdd_on_vertical_lines_generalized
    (σ₀ σ₁ t : ℝ) (σ₀_gt_one : 1 < σ₀) (σ₀_lt_σ₁ : σ₀ ≤ σ₁) :
    ‖(- deriv riemannZeta (σ₁ + t * I) / riemannZeta (σ₁ + t * I))‖ ≤ ‖deriv riemannZeta σ₀ / riemannZeta σ₀‖ := by
  let s₁ := σ₁ + t * I
  have s₁_re_eq_sigma : s₁.re = σ₁ := by
    rw [add_re, ofReal_re, mul_I_re, ofReal_im]
    ring
  have s₀_re_eq_sigma : (↑σ₀ : ℂ).re = σ₀ := by
    rw [ofReal_re]
  let s₀ := σ₀
  have σ₁_gt_one : 1 < σ₁ := by exact lt_of_le_of_lt' σ₀_lt_σ₁ σ₀_gt_one
  have s₀_gt_one : 1 < (↑σ₀ : ℂ).re := by exact σ₀_gt_one
  have s₁_re_geq_one : 1 < s₁.re := by exact lt_of_lt_of_eq σ₁_gt_one (id (Eq.symm s₁_re_eq_sigma))
  rw [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₁_re_geq_one)]
  unfold LSeries
  have summable_von_mangoldt_at_σ₀ : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(vonMangoldt n)) σ₀ i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt σ₀_gt_one
  have summable_re_von_mangoldt_at_σ₀ :
      Summable (fun i ↦ (LSeries.term (fun n ↦ ↑(vonMangoldt n)) σ₀ i).re) := by
    exact summable_complex_then_summable_real_part (LSeries.term (fun n ↦ ↑(vonMangoldt n)) σ₀)
      summable_von_mangoldt_at_σ₀
  have summable_abs_value : Summable (fun i ↦ ‖LSeries.term (fun n ↦ ↑(vonMangoldt n)) s₁ i‖) := by
    rw [summable_norm_iff]
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt s₁_re_geq_one
  apply le_trans <| norm_tsum_le_tsum_norm summable_abs_value
  rw [← norm_neg, ← neg_div, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₀_gt_one]
  unfold LSeries
  rw [← re_eq_norm.mpr, re_tsum summable_von_mangoldt_at_σ₀]
  · apply Summable.tsum_mono summable_abs_value summable_re_von_mangoldt_at_σ₀
    intro n
    beta_reduce
    apply le_trans <| LSeries.norm_term_le_of_re_le_re (s := σ₀) _ _ _
    · rw [re_eq_norm.mpr]
      apply LSeries.term_nonneg
      exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
    · rwa [s₁_re_eq_sigma, s₀_re_eq_sigma]
  · apply tsum_nonneg
    intro n
    apply LSeries.term_nonneg
    exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
theorem triv_bound_zeta :  ∃C ≥ 0, ∀(σ₀ t : ℝ), 1 < σ₀ →
    ‖- deriv riemannZeta (σ₀ + t * I) / riemannZeta (σ₀ + t * I)‖ ≤ (σ₀ - 1)⁻¹ + C := by
  obtain ⟨c, hc⟩ := riemannZetaLogDerivResidueBigO.bound
  obtain ⟨ε, ε0, h⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hc)
  have key (σ : ℝ) (h1 : 1 < σ) (h2 : σ < 1 + ε) :
      ‖deriv riemannZeta σ / riemannZeta σ‖ ≤ (σ - 1)⁻¹ + c := by
    have e : ‖((σ : ℂ) - 1)⁻¹‖ = (σ - 1)⁻¹ := by
      rw [norm_inv, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_of_nonneg (by linarith)]
    have := @h σ (by rw [Complex.dist_eq, ← ofReal_one, ← ofReal_sub, norm_real,
      Real.norm_of_nonneg (by linarith)]; linarith) (by simpa using h1.ne')
    simp only [Pi.sub_apply, Pi.div_apply, Pi.neg_apply, Pi.one_apply, norm_one, mul_one] at this
    have h3 := norm_sub_norm_le (-deriv riemannZeta σ / riemannZeta σ) ((σ : ℂ) - 1)⁻¹
    rw [neg_div] at this h3
    rw [norm_neg, e] at h3
    linarith
  refine ⟨(ε / 2)⁻¹ + |c|, by positivity, fun σ₀ t hσ ↦ ?_⟩
  have := le_abs_self c
  rcases le_or_gt σ₀ (1 + ε / 2) with h' | h'
  · linarith [dlog_riemannZeta_bdd_on_vertical_lines_generalized σ₀ σ₀ t hσ le_rfl, key σ₀ hσ (by linarith),
      inv_nonneg.mpr (by linarith : 0 ≤ ε / 2)]
  · have := key (1 + ε / 2) (by linarith) (by linarith)
    rw [add_sub_cancel_left] at this
    linarith [dlog_riemannZeta_bdd_on_vertical_lines_generalized (1 + ε / 2) σ₀ t (by linarith) h'.le,
      inv_nonneg.mpr (by linarith : 0 ≤ σ₀ - 1)]
def LogDerivZetaBndUnifGenProp (n₁ n₂ : ℝ) : Prop := ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2))
  (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ n₁)), ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤
      C * Real.log |t| ^ n₂
lemma LogDerivZetaBndUnif99 : LogDerivZetaBndUnifGenProp 9 9 := by
  obtain ⟨A, hA, C, hC, h₁⟩ := LogDerivZetaBnd
  obtain ⟨D, hD, h₂⟩ := triv_bound_zeta
  refine ⟨A, hA, (1 + C + D) * A⁻¹, by have := hA.1; positivity, fun σ t ht hσ ↦ ?_⟩
  have hL : 0 < Real.log |t| ^ (9 : ℝ) :=
    one_pos.trans ((logt_gt_one ht.le).trans_le (ZetaInvBnd_aux (logt_gt_one ht.le)))
  have hA1 : 1 ≤ A⁻¹ := (one_le_inv₀ hA.1).mpr (by linarith [hA.2])
  have hAL : 1 ≤ A⁻¹ * Real.log |t| ^ (9 : ℝ) := by
    nlinarith [(logt_gt_one ht.le).trans_le (ZetaInvBnd_aux (logt_gt_one ht.le))]
  have h5 := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hL.le hA1) hC.le
  have h6 := le_mul_of_one_le_right hD hAL
  rcases lt_or_ge σ (1 + A / Real.log |t| ^ (9 : ℝ)) with h | h
  · linarith [h₁ σ t ht ⟨hσ, h⟩]
  have h3 := h₂ σ t (by linarith [div_pos hA.1 hL])
  rw [neg_div, norm_neg] at h3
  have h4 : (σ - 1)⁻¹ ≤ A⁻¹ * Real.log |t| ^ (9 : ℝ) := by
    rw [← div_eq_inv_mul, ← inv_div]; exact inv_anti₀ (div_pos hA.1 hL) (by linarith)
  linarith [mul_pos hC (one_pos.trans_le hAL)]
end PNT_ZetaBounds
section PNT_SmoothExistence

open MeasureTheory Set Real

open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]

lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

end PNT_SmoothExistence

section PNT_MellinCalculus

open scoped ContDiff

theorem MeasureTheory.setIntegral_integral_swap {α : Type*} {β : Type*} {E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : MeasureTheory.Measure α}
    {ν : MeasureTheory.Measure β} [NormedAddCommGroup E]
    [MeasureTheory.SigmaFinite ν] [NormedSpace ℝ E] [MeasureTheory.SigmaFinite μ]
    (f : α → β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn (f.uncurry) (s ×ˢ t) (μ.prod ν)) :
    (∫ (x : α) in s, ∫ (y : β) in t, f x y ∂ν ∂μ)
      = ∫ (y : β) in t, ∫ (x : α) in s, f x y ∂μ ∂ν := by
  apply integral_integral_swap
  convert hf.integrable
  exact Measure.prod_restrict s t

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

lemma MeasureTheory.integral_comp_mul_right_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (y * a) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  have := integral_comp_mul_right_Ioi (fun y ↦ f y / y) 0 ha
  simp only [RCLike.ofReal_mul, zero_mul, eq_inv_smul_iff₀ (ne_of_gt ha)] at this
  rw [← integral_smul] at this
  rw [← this, setIntegral_congr_fun (by simp)]
  intro _ _
  simp only [RCLike.real_smul_eq_coe_mul]
  rw [mul_comm (a : 𝕂), div_mul, mul_div_assoc, div_self ?_, mul_one]
  exact (RCLike.ofReal_ne_zero).mpr <| ne_of_gt ha

lemma MeasureTheory.integral_comp_mul_left_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a * y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  convert integral_comp_mul_right_I0i_haar f ha using 5; ring

lemma MeasureTheory.integral_comp_rpow_I0i_haar_real (f : ℝ → ℝ) {p : ℝ} (hp : p ≠ 0) :
    ∫ (y : ℝ) in Ioi 0, |p| * f (y ^ p) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  rw [← integral_comp_rpow_Ioi (fun y ↦ f y / y) hp, setIntegral_congr_fun (by simp)]
  intro y hy
  have ypos : 0 < y := mem_Ioi.mp hy
  simp only [rpow_sub_one ypos.ne', smul_eq_mul]
  field_simp

lemma MeasureTheory.integral_comp_inv_I0i_haar (f : ℝ → 𝕂) :
    ∫ (y : ℝ) in Ioi 0, f (1 / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  have := integral_comp_rpow_Ioi (fun y ↦ f y / y) (p := -1) (by simp)
  rw [← this, setIntegral_congr_fun (by simp)]
  intro y hy
  have : (y : 𝕂) ≠ 0 := (RCLike.ofReal_ne_zero).mpr <| LT.lt.ne' hy
  simp only [abs_neg, abs_one, rpow_neg_one, map_inv₀, div_inv_eq_mul,
    RCLike.real_smul_eq_coe_mul, RCLike.algebraMap_eq_ofReal]
  ring_nf
  simp [field]

lemma MeasureTheory.integral_comp_div_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  calc
    _ = ∫ (y : ℝ) in Ioi 0, f (a * y) / y := ?_
    _ = _ := integral_comp_mul_left_I0i_haar f ha
  convert (integral_comp_inv_I0i_haar fun y ↦ f (a * (1 / y))).symm using 4
  · rw [mul_one_div]
  · rw [one_div_one_div]

@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  simp only [support, ne_eq]; simp_rw [norm_ne_zero_iff]

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  apply Function.support_comp_eq (g := ofReal); simp

lemma Function.support_mul_subset_of_subset {s : Set ℝ} {f g : ℝ → 𝕂}
    (fSupp : f.support ⊆ s) : (f * g).support ⊆ s := by
  simp_rw [support_mul', inter_subset, subset_union_of_subset_right fSupp]

lemma Function.support_deriv_subset_Icc {a b : ℝ} {f : ℝ → 𝕂}
    (fSupp : f.support ⊆ Set.Icc a b) :
    (deriv f).support ⊆ Set.Icc a b := by
    have := support_deriv_subset (f := fun x ↦ f x)
    dsimp [tsupport] at this
    have := subset_trans this <| closure_mono fSupp
    rwa [closure_Icc] at this

lemma SetIntegral.integral_eq_integral_inter_of_support_subset {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set ℝ} {f : ℝ → E} (h : f.support ⊆ t) (ht : MeasurableSet t) :
    ∫ x in s, f x ∂μ = ∫ x in s ∩ t, f x ∂μ := by
  rw [← setIntegral_indicator ht, indicator_eq_self.2 h]

lemma SetIntegral.integral_eq_integral_inter_of_support_subset_Icc {a b} {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} {f : ℝ → E} (h : f.support ⊆ Icc a b) (hs : Icc a b ⊆ s) :
    ∫ x in s, f x ∂μ = ∫ x in Icc a b, f x ∂μ := by
  rw [SetIntegral.integral_eq_integral_inter_of_support_subset h measurableSet_Icc,
      inter_eq_self_of_subset_right hs]

lemma intervalIntegral.norm_integral_le_of_norm_le_const' {a b C : ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hab : a ≤ b) (h : ∀ x ∈ (Icc a b), ‖f x‖ ≤ C) :
    ‖∫ x in a..b, f x‖ ≤ C * |b - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  exact fun x hx ↦ h x <| mem_Icc_of_Ioc <| uIoc_of_le hab ▸ hx

lemma Filter.TendstoAtZero_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂) (ha : 0 < a)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f (𝓝[>]0) (𝓝 0) := by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioo_mem_nhdsGT ha] with c hc; replace hc := (mem_Ioo.mp hc).2
  have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
  convert mt (Function.support_subset_iff.mp fSupp c) h; simp

lemma Filter.TendstoAtTop_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f atTop (𝓝 0) := by
  apply Tendsto.comp (tendsto_nhds_of_eventually_eq ?_) tendsto_id
  filter_upwards [Ioi_mem_atTop b] with c hc; rw [mem_Ioi] at hc
  have h : c ∉ Icc a b := fun h ↦ by linarith [mem_Icc.mp h]
  convert mt (Function.support_subset_iff.mp fSupp c) h; simp

lemma Filter.BigO_zero_atZero_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂) (ha : 0 < a)
    (fSupp : f.support ⊆ Set.Icc a b) :
    f =O[𝓝[>] 0] fun _ ↦ (0 : ℝ) := by
  refine Eventually.isBigO ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < a)] with c hc
  refine norm_le_zero_iff.mpr <| Function.support_subset_iff'.mp fSupp c ?_
  exact fun h ↦ by linarith [mem_Icc.mp h, (mem_Ioo.mp hc).2]

lemma Filter.BigO_zero_atTop_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂)
    (fSupp : f.support ⊆ Set.Icc a b) :
    f =O[atTop] fun _ ↦ (0 : ℝ) := by
  refine Eventually.isBigO ?_
  filter_upwards [Ioi_mem_atTop b] with c hc; replace hc := mem_Ioi.mp hc
  refine norm_le_zero_iff.mpr <| Function.support_subset_iff'.mp fSupp c ?_
  exact fun h ↦ by linarith [mem_Icc.mp h]

lemma deriv.ofReal_comp' {f : ℝ → ℝ} :
    deriv (fun x : ℝ ↦ (f x : ℂ)) = (fun x ↦ ((deriv f) x : ℂ)) :=
  funext fun _ ↦ deriv.ofReal_comp

lemma PartialIntegration (f g : ℝ → ℂ)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fDerivgInt : IntegrableOn (f * deriv g) (Ioi 0))
    (gDerivfInt : IntegrableOn (deriv f * g) (Ioi 0))
    (lim_at_zero : Tendsto (f * g) (𝓝[>] 0) (𝓝 0))
    (lim_at_inf : Tendsto (f * g) atTop (𝓝 0)) :
    ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
  simpa using integral_Ioi_mul_deriv_eq_deriv_mul
    (fun x hx ↦ fDiff.hasDerivAt (Ioi_mem_nhds hx))
    (fun x hx ↦ gDiff.hasDerivAt (Ioi_mem_nhds hx))
    fDerivgInt gDerivfInt lim_at_zero lim_at_inf

lemma PartialIntegration_of_support_in_Icc {a b : ℝ} (f g : ℝ → ℂ) (ha : 0 < a)
    (h : a ≤ b)
    (fSupp : f.support ⊆ Set.Icc a b)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fderivCont : ContinuousOn (deriv f) (Ioi 0))
    (gderivCont : ContinuousOn (deriv g) (Ioi 0)) :
    ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
  have Icc_sub : Icc a b ⊆ Ioi 0 := (Icc_subset_Ioi_iff h).mpr ha
  have fderivSupp := Function.support_deriv_subset_Icc fSupp
  have fgSupp : (f * g).support ⊆ Icc a b := Function.support_mul_subset_of_subset fSupp
  have fDerivgInt : IntegrableOn (f * deriv g) (Ioi 0) := by
    apply (integrableOn_iff_integrable_of_support_subset <|
           Function.support_mul_subset_of_subset fSupp).mp
    exact fDiff.continuousOn.mono Icc_sub |>.mul (gderivCont.mono Icc_sub) |>.integrableOn_Icc
  have gDerivfInt : IntegrableOn (deriv f * g) (Ioi 0) := by
    apply (integrableOn_iff_integrable_of_support_subset <|
           Function.support_mul_subset_of_subset fderivSupp).mp
    exact fderivCont.mono Icc_sub |>.mul (gDiff.continuousOn.mono Icc_sub) |>.integrableOn_Icc
  have lim_at_zero : Tendsto (f * g) (𝓝[>]0) (𝓝 0) :=
    TendstoAtZero_of_support_in_Icc (f * g) ha fgSupp
  have lim_at_inf : Tendsto (f * g) atTop (𝓝 0) := TendstoAtTop_of_support_in_Icc (f * g) fgSupp
  apply PartialIntegration f g fDiff gDiff fDerivgInt gDerivfInt lim_at_zero lim_at_inf

noncomputable def MellinConvolution (f g : ℝ → 𝕂) (x : ℝ) : 𝕂 :=
  ∫ y in Ioi 0, f y * g (x / y) / y

lemma MellinConvolutionSymmetric (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
    MellinConvolution f g x = MellinConvolution g f x := by
  unfold MellinConvolution
  calc
    _ = ∫ y in Ioi 0, f (y * x) * g (1 / y) / y := ?_
    _ = _ := ?_
  · rw [← integral_comp_mul_right_I0i_haar (fun y ↦ f y * g (x / y)) xpos]
    simp [div_mul_cancel_right₀ <| ne_of_gt xpos]
  · convert (integral_comp_inv_I0i_haar fun y ↦ f (y * x) * g (1 / y)).symm using 3
    rw [one_div_one_div, mul_comm, mul_comm_div, one_mul]

lemma MellinConvolutionTransform (f g : ℝ → ℂ) (s : ℂ)
    (hf : IntegrableOn (fun x y ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)).uncurry
      (Ioi 0 ×ˢ Ioi 0)) :
    mellin (MellinConvolution f g) s = mellin f s * mellin g s := by
  dsimp [mellin, MellinConvolution]
  set f₁ : ℝ × ℝ → ℂ :=
    fun ⟨x, y⟩ ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)
  calc
    _ = ∫ (x : ℝ) in Ioi 0, ∫ (y : ℝ) in Ioi 0, f₁ (x, y) := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0, f₁ (x, y) :=
        setIntegral_integral_swap _ hf
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
        f y * g (x / y) / ↑y * ↑x ^ (s - 1) := rfl
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
        f y * g (x * y / y) / ↑y * ↑(x * y) ^ (s - 1) * y := ?_
    _ = ∫ (y : ℝ) in Ioi 0, ∫ (x : ℝ) in Ioi 0,
        f y * ↑y ^ (s - 1) * (g x * ↑x ^ (s - 1)) := ?_
    _ = ∫ (y : ℝ) in Ioi 0,
        f y * ↑y ^ (s - 1) * ∫ (x : ℝ) in Ioi 0, g x * ↑x ^ (s - 1) := ?_
    _ = _ := integral_mul_const _ _
  <;> try (rw [setIntegral_congr_fun (by simp)]; intro y hy; simp only [ofReal_mul])
  · simp only [integral_mul_const, f₁, mul_comm]
  · simp only [integral_mul_const]
    have := integral_comp_mul_right_Ioi
      (fun x ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)) 0 hy
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := slitPlane_ne_zero (Or.inl hy)
    field_simp at this ⊢
    simp only [ofReal_mul, one_div, mul_zero, real_smul, ofReal_inv, field] at this ⊢
    rw [← this]
    field_simp
    congr with x
    ring_nf
  · rw [setIntegral_congr_fun (by simp)]
    intro x hx
    have y_ne_zeroℝ : y ≠ 0 := ne_of_gt (mem_Ioi.mp hy)
    have y_ne_zeroℂ : (y : ℂ) ≠ 0 := by exact_mod_cast y_ne_zeroℝ
    field_simp
    rw [mul_cpow_ofReal_nonneg hy.le hx.le]
    ring
  · apply integral_const_mul
  · congr <;> ext <;> ring

lemma MellinOfPsi_aux {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    {s : ℂ} (hs : s ≠ 0) :
    ∫ (x : ℝ) in Ioi 0, (ν x) * (x : ℂ) ^ (s - 1) =
    - (1 / s) * ∫ (x : ℝ) in Ioi 0, (deriv ν x) * (x : ℂ) ^ s := by
  let g (s : ℂ) := fun (x : ℝ)  ↦ x ^ s / s
  have gderiv {s : ℂ} (hs : s ≠ 0) {x: ℝ} (hx : x ∈ Ioi 0) :
      deriv (g s) x = x ^ (s - 1) := by
    have := HasDerivAt.cpow_const (c := s) (hasDerivAt_id (x : ℂ)) (Or.inl hx)
    simp_rw [mul_one, id_eq] at this
    rw [deriv_div_const, deriv.comp_ofReal (e := fun x ↦ x ^ s)]
    · rw [this.deriv, mul_div_right_comm, div_self hs, one_mul]
    · apply hasDerivAt_deriv_iff.mp
      simp only [this.deriv, this]
  calc
    _ =  ∫ (x : ℝ) in Ioi 0, ↑(ν x) * deriv (@g s) x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv (fun x ↦ ↑(ν x)) x * @g s x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv ν x * @g s x := ?_
    _ = -∫ (x : ℝ) in Ioi 0, deriv ν x * x ^ s / s := by simp only [mul_div, g]
    _ = _ := ?_
  · rw [setIntegral_congr_fun (by simp)]
    intro _ hx
    simp only [gderiv hs hx]
  · apply PartialIntegration_of_support_in_Icc (ν ·) (g s)
      (a := 1 / 2) (b := 2) (by norm_num) (by norm_num)
    · simpa only [Function.support_subset_iff, ne_eq, ofReal_eq_zero]
    · exact (Differentiable.ofReal_comp_iff.mpr
        (diffν.differentiable (by norm_num))).differentiableOn
    · refine DifferentiableOn.div_const ?_ s
      intro a ha
      refine DifferentiableAt.comp_ofReal (e := fun x ↦ x ^ s) ?_ |>.differentiableWithinAt
      apply differentiableAt_fun_id.cpow (differentiableAt_const s) <| by exact Or.inl ha
    · simp only [deriv.ofReal_comp']
      exact continuous_ofReal.comp (diffν.continuous_deriv (by norm_num)) |>.continuousOn
    · apply ContinuousOn.congr (f := fun (x : ℝ) ↦ (x : ℂ) ^ (s - 1)) ?_
        fun x hx ↦ gderiv hs hx
      exact Continuous.continuousOn (by continuity) |>.cpow continuousOn_const (by simp)
  · congr; funext; congr
    apply (hasDerivAt_deriv_iff.mpr ?_).ofReal_comp.deriv
    exact diffν.contDiffAt.differentiableAt (by norm_num)
  · simp only [neg_mul, neg_inj]
    conv => lhs; rhs; intro; rw [← mul_one_div, mul_comm]
    rw [integral_const_mul]

lemma MellinOfPsi {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ C > 0, ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
    ‖mellin (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
  let f := fun (x : ℝ) ↦ ‖deriv ν x‖
  have cont : ContinuousOn f (Icc (1 / 2) 2) :=
    (Continuous.comp (by continuity) <| diffν.continuous_deriv (by norm_num)).continuousOn
  obtain ⟨a, _, max⟩ := isCompact_Icc.exists_isMaxOn (f := f) (by norm_num) cont
  let σ₂ : ℝ := 2
  let C : ℝ := f a * 2 ^ σ₂ * (3 / 2)
  have mainBnd : ∀ (σ₁ : ℝ), 0 < σ₁ → ∀ (s : ℂ), σ₁ ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
    intro σ₁ σ₁pos s hs₁ hs₂
    have s_ne_zero: s ≠ 0 := fun h ↦ by linarith [zero_re ▸ h ▸ hs₁]
    simp only [mellin, f, MellinOfPsi_aux diffν suppν s_ne_zero, norm_mul, smul_eq_mul, mul_comm]
    gcongr
    · simp
    calc
      _ ≤ ∫ (x : ℝ) in Ioi 0, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ = ∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖ := ?_
      _ ≤ ‖∫ (x : ℝ) in Icc (1 / 2) 2, ‖(deriv ν x * (x : ℂ) ^ s)‖‖ :=
          le_abs_self _
      _ ≤ _ := ?_
    · simp_rw [norm_integral_le_integral_norm]
    · apply SetIntegral.integral_eq_integral_inter_of_support_subset_Icc
      · simp only [Function.support_abs, Function.support_mul, Function.support_ofReal]
        apply subset_trans (by apply inter_subset_left) <| Function.support_deriv_subset_Icc suppν
      · exact (Icc_subset_Ioi_iff (by norm_num)).mpr (by norm_num)
    · have := intervalIntegral.norm_integral_le_of_norm_le_const' (C := f a * 2 ^ σ₂)
        (f := fun x ↦ f x * ‖(x : ℂ) ^ s‖) (a := (1 / 2 : ℝ)) ( b := 2) (by norm_num) ?_
      · simp only [Real.norm_eq_abs, norm_real, norm_mul] at this ⊢
        rwa [(by norm_num: |(2 : ℝ) - 1 / 2| = 3 / 2),
            intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at this
      · intro x hx;
        have f_bound := isMaxOn_iff.mp max x hx
        have pow_bound : ‖(x : ℂ) ^ s‖ ≤ 2 ^ σ₂ := by
          rw [norm_cpow_eq_rpow_re_of_pos (by linarith [mem_Icc.mp hx])]
          have xpos : 0 ≤ x := by linarith [(mem_Icc.mp hx).1]
          have h := rpow_le_rpow xpos (mem_Icc.mp hx).2 (by linarith : 0 ≤ s.re)
          exact le_trans h <| rpow_le_rpow_of_exponent_le (by norm_num) hs₂
        convert! mul_le_mul f_bound pow_bound (norm_nonneg _) ?_ using 1 <;> simp [f]
  have Cnonneg : 0 ≤ C := by
    have hh := mainBnd 1 (by norm_num) ((3 : ℂ) / 2) (by norm_num) (by norm_num)
    have hhh : 0 ≤ ‖mellin (fun x ↦ (ν x : ℂ)) ((3 : ℂ) / 2)‖ := by positivity
    have hhhh : 0 < ‖(3 : ℂ) / 2‖⁻¹ := by norm_num
    have := hhh.trans hh
    exact (mul_nonneg_iff_of_pos_right hhhh).mp this
  by_cases CeqZero : C = 0
  · refine ⟨1, by linarith, ?_⟩
    intro ε εpos s hs₁ hs₂
    have := mainBnd ε εpos s hs₁ hs₂
    rw [CeqZero, zero_mul] at this
    have : 0 ≤ 1 * ‖s‖⁻¹ := by positivity
    linarith
  · exact ⟨C, lt_of_le_of_ne Cnonneg fun a ↦ CeqZero (id (Eq.symm a)), mainBnd⟩

noncomputable def DeltaSpike (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ν (x ^ (1 / ε)) / ε

lemma DeltaSpikeMass {ν : ℝ → ℝ} (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ}
    (εpos : 0 < ε) : ∫ x in Ioi 0, ((DeltaSpike ν ε) x) / x = 1 :=
  calc
    _ = ∫ (x : ℝ) in Ioi 0, (|1/ε| * x ^ (1 / ε - 1)) •
      ((fun z ↦ (ν z) / z) (x ^ (1 / ε))) := by
      apply setIntegral_congr_ae measurableSet_Ioi
      filter_upwards with x hx
      simp only [smul_eq_mul, abs_of_pos (one_div_pos.mpr εpos)]
      symm; calc
        _ = (ν (x ^ (1 / ε)) / x ^ (1 / ε)) * x ^ (1 / ε - 1) * (1 / ε) := by ring
        _ = _ := by rw [rpow_sub hx, rpow_one]
        _ = (ν (x ^ (1 / ε)) / x ^ (1 / ε) * x ^ (1 / ε) / x) * (1/ ε) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ (ne_of_gt (rpow_pos_of_pos hx (1/ε)))]
        _ = (ν (x ^ (1 / ε)) / ε / x) := by ring
    _ = 1 := by
      rw [integral_comp_rpow_Ioi (fun z ↦ (ν z) / z), ← mass_one]
      simp only [ne_eq, div_eq_zero_iff, one_ne_zero, εpos.ne', or_self, not_false_eq_true]

lemma DeltaSpikeSupport_aux {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x).support ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
  unfold DeltaSpike
  simp only [one_div, Function.support_subset_iff, ne_eq, ite_eq_left_iff, not_lt, div_eq_zero_iff,
    not_forall, exists_prop, mem_Icc, and_imp]
  intro x hx h; push Not at h
  have := suppν <| Function.mem_support.mpr h.1
  simp only [one_div, mem_Icc] at this
  have hl := (le_rpow_inv_iff_of_pos (by norm_num) hx εpos).mp this.1
  rw [inv_rpow (by norm_num) ε, ← rpow_neg (by norm_num)] at hl
  refine ⟨hl, (rpow_inv_le_iff_of_pos ?_ (by norm_num) εpos).mp this.2⟩
  linarith [(by apply rpow_nonneg (by norm_num) : 0 ≤ (2 : ℝ) ^ (-ε))]

lemma DeltaSpikeSupport' {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    DeltaSpike ν ε x ≠ 0 → x ∈ Icc (2 ^ (-ε)) (2 ^ ε) := by
  intro h
  have : (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x) x = DeltaSpike ν ε x := by
    simp [xnonneg]
  rw [← this] at h
  exact (Function.support_subset_iff.mp <| DeltaSpikeSupport_aux εpos suppν) _ h

lemma DeltaSpikeSupport {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    x ∉ Icc (2 ^ (-ε)) (2 ^ ε) → DeltaSpike ν ε x = 0 := by
  contrapose!; exact DeltaSpikeSupport' εpos xnonneg suppν

lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  apply diffν.continuous.comp (g := ν) _ |>.div_const
  exact continuous_id.rpow_const fun _ ↦ Or.inr <| div_nonneg (by norm_num) εpos.le

lemma DeltaSpikeOfRealContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ (DeltaSpike ν ε x : ℂ)) :=
  continuous_ofReal.comp <| DeltaSpikeContinuous εpos diffν

theorem MellinOfDeltaSpike (ν : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) (s : ℂ) :
    mellin (fun x ↦ (DeltaSpike ν ε x : ℂ)) s = mellin (fun x ↦ (ν x : ℂ)) (ε * s) := by
  unfold DeltaSpike
  push_cast
  rw [mellin_div_const, mellin_comp_rpow (fun x ↦ (ν x : ℂ)), abs_of_nonneg (by positivity)]
  simp only [one_div, inv_inv, ofReal_inv, div_inv_eq_mul, real_smul]
  rw [mul_div_cancel_left₀ _ (ne_zero_of_re_pos εpos)]
  ring_nf

lemma MellinOfDeltaSpikeAt1_asymp {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) :
    (fun (ε : ℝ) ↦ (mellin (fun x ↦ (ν x : ℂ)) ε) - 1) =O[𝓝[>]0] id := by
  have diff : DifferentiableWithinAt ℝ
      (fun (ε : ℝ) ↦ mellin (fun x ↦ (ν x : ℂ)) ε - 1) (Ioi 0) 0 := by
    apply DifferentiableAt.differentiableWithinAt
    simp only [(differentiableAt_const _).fun_sub_iff_left]
    refine DifferentiableAt.comp_ofReal ?_
    refine mellin_differentiableAt_of_isBigO_rpow (a := 1) (b := -1) ?_ ?_ (by simp) ?_ (by simp)
    · apply (Continuous.continuousOn ?_).locallyIntegrableOn (by simp)
      have := diffν.continuous; continuity
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      apply BigO_zero_atTop_of_support_in_Icc (a := 1 / 2) (b := 2)
      rwa [ν.support_ofReal]
    · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
      apply BigO_zero_atZero_of_support_in_Icc (a := 1 / 2) (b := 2) (ha := (by norm_num))
      rwa [ν.support_ofReal]
  have := ofReal_zero ▸ diff.isBigO_sub
  simp only [sub_sub_sub_cancel_right, sub_zero] at this
  convert! this using 1
  simp only [mellin, zero_sub, cpow_neg_one, smul_eq_mul]
  funext ε
  congr 1
  symm
  calc (∫ (t : ℝ) in Ioi 0, (↑t)⁻¹ * ↑(ν t) : ℂ)
      = ∫ (t : ℝ) in Ioi 0, ((ν t / t : ℝ) : ℂ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => by push_cast; ring)
    _ = ((∫ t in Ioi 0, ν t / t : ℝ) : ℂ) := integral_ofReal
    _ = 1 := by rw [mass_one, ofReal_one]

lemma MellinOf1 (s : ℂ) (h : s.re > 0) :
    mellin ((fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0)) s = 1 / s := by
  convert (hasMellin_one_Ioc h).right
  congr
  simp [indicator]

noncomputable def Smooth1 (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) (DeltaSpike ν ε)

lemma Smooth1Properties_estimate {ε : ℝ} (εpos : 0 < ε) :
    (1 - 2 ^ (-ε)) / ε < Real.log 2 := by
  apply (div_lt_iff₀' εpos).mpr
  have : 1 - 1 / (2 : ℝ) ^ ε = ((2 : ℝ) ^ ε - 1) / (2 : ℝ) ^ ε := by
    rw [sub_div, div_self (by positivity)]
  rw [← Real.log_rpow (by norm_num), rpow_neg (by norm_num), inv_eq_one_div (2 ^ ε), this]
  set c := (2 : ℝ) ^ ε
  have hc : 1 < c := by
    rw [← rpow_zero (2 : ℝ)]
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num) εpos
  apply (div_lt_iff₀' (by positivity)).mpr <| lt_sub_iff_add_lt'.mp ?_
  let f := (fun x ↦ x * Real.log x - x)
  rw [(by simp [f] : -1 = f 1), (by simp [f] : c * Real.log c - c = f c)]
  have mono: StrictMonoOn f <| Ici 1 := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
    · apply continuousOn_id.mul (continuousOn_id.log ?_) |>.sub continuousOn_id
      intro x hx; simp only [mem_Ici] at hx; simp only [id_eq, ne_eq]; linarith
    · intro x hx; simp only [nonempty_Iio, interior_Ici', mem_Ioi] at hx
      dsimp only [f]
      rw [deriv_fun_sub, deriv_fun_mul, Real.deriv_log, deriv_id'', one_mul, mul_inv_cancel₀]
      · simp [log_pos hx]
      · linarith
      · simp only [differentiableAt_fun_id]
      · simp only [differentiableAt_log_iff, ne_eq]; linarith
      · exact differentiableAt_fun_id.mul <| differentiableAt_fun_id.log (by linarith)
      · simp only [differentiableAt_fun_id]
  exact mono (by rw [mem_Ici]) (mem_Ici.mpr <| le_of_lt hc) hc

lemma Smooth1Properties_below_aux {x ε : ℝ} (hx : x ≤ 1 - Real.log 2 * ε) (εpos : 0 < ε) :
    x < 2 ^ (-ε) := by
  calc
    x ≤ 1 - Real.log 2 * ε := hx
    _ < 2 ^ (-ε) := ?_
  rw [sub_lt_iff_lt_add, add_comm, ← sub_lt_iff_lt_add]
  exact (div_lt_iff₀ εpos).mp <| Smooth1Properties_estimate εpos

lemma Smooth1Properties_below {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ (c : ℝ), 0 < c ∧ c = Real.log 2 ∧
      ∀ (ε x) (_ : 0 < ε), 0 < x → x ≤ 1 - c * ε → Smooth1 ν ε x = 1 := by
  set c := Real.log 2; use c
  refine ⟨log_pos (by norm_num), rfl, ?_⟩
  intro ε x εpos xpos hx
  have hx2 := Smooth1Properties_below_aux hx εpos
  rewrite [← DeltaSpikeMass mass_one εpos]
  unfold Smooth1 MellinConvolution
  calc
    _ = ∫ (y : ℝ) in Ioi 0,
        indicator (Ioc 0 1) (fun y ↦ DeltaSpike ν ε (x / y) / ↑y) y := ?_
    _ = ∫ (y : ℝ) in Ioi 0, DeltaSpike ν ε (x / y) / y := ?_
    _ = _ := integral_comp_div_I0i_haar (fun y ↦ DeltaSpike ν ε y) xpos
  · rw [setIntegral_congr_fun (by simp)]
    intro y hy
    by_cases h : y ≤ 1 <;> simp [indicator, mem_Ioi.mp hy, h]
  · rw [setIntegral_congr_fun (by simp)]
    intro y hy
    have : y ≠ 0 := by
      rintro rfl
      simp at hy
    simp only [indicator_apply_eq_self, mem_Ioc, not_and, not_le, div_eq_zero_iff, this, or_false]
    intro hy2; replace hy2 := hy2 <| mem_Ioi.mp hy
    apply DeltaSpikeSupport εpos ?_ suppν
    · simp only [mem_Icc, not_and, not_le]; intro
      linarith [(by apply (div_lt_iff₀ (by linarith)).mpr; nlinarith : x / y < 2 ^ (-ε))]
    · rw [le_div_iff₀ (by linarith), zero_mul]; exact xpos.le

lemma Smooth1Properties_above_aux {x ε : ℝ} (hx : 1 + (2 * Real.log 2) * ε ≤ x)
    (hε : ε ∈ Ioo 0 1) :
    2 ^ ε < x := by
  calc
    x ≥ 1 + (2 * Real.log 2) * ε := hx
    _ > 2 ^ ε := ?_
  refine lt_add_of_sub_left_lt <| (div_lt_iff₀ hε.1).mp ?_
  calc
    2 * Real.log 2 > 2 * (1 - 2 ^ (-ε)) / ε := ?_
    _ > 2 ^ ε * (1 - 2 ^ (-ε)) / ε := ?_
    _ = (2 ^ ε - 1) / ε := ?_
  · field_simp
    exact Smooth1Properties_estimate hε.1
  · have : (2 : ℝ) ^ ε < 2 := by
      have h := rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) hε.2
      rwa [Real.rpow_one] at h
    have pos: 0 < (1 - 2 ^ (-ε)) / ε := by
      refine div_pos ?_ hε.1
      rw [sub_pos]
      have h := rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) (neg_lt_zero.mpr hε.1)
      rwa [Real.rpow_zero] at h
    have := (mul_lt_mul_iff_left₀ pos).mpr this
    ring_nf at this ⊢
    exact this
  · have : (2 : ℝ) ^ ε * (2 : ℝ) ^ (-ε) = (2 : ℝ) ^ (ε - ε) := by
      rw [← rpow_add (by norm_num), add_neg_cancel, sub_self]
    conv => lhs; lhs; ring_nf; rhs; simp [this]

lemma Smooth1Properties_above_aux2 {x y ε : ℝ} (hε : ε ∈ Ioo 0 1) (hy : y ∈ Ioc 0 1)
  (hx2 : 2 ^ ε < x) :
    2 < (x / y) ^ (1 / ε) := by
  obtain ⟨εpos, ε1⟩ := hε
  obtain ⟨ypos, y1⟩ := hy
  calc
    _ > (2 ^ ε / y) ^ (1 / ε) := ?_
    _ = 2 / y ^ (1 / ε) := ?_
    _ ≥ 2 / y := ?_
    _ ≥ 2 := ?_
  · rw [gt_iff_lt, div_rpow, div_rpow, lt_div_iff₀, mul_comm_div, div_self, mul_one]
    <;> try positivity
    · exact rpow_lt_rpow (by positivity) hx2 (by positivity)
    · exact LT.lt.le <| lt_trans (by positivity) hx2
  · rw [div_rpow, ← rpow_mul, mul_div_cancel₀ 1 <| ne_of_gt εpos, rpow_one] <;> positivity
  · have : y ^ (1 / ε) ≤ y := by
      nth_rewrite 2 [← rpow_one y]
      exact rpow_le_rpow_of_exponent_ge ypos y1 (by linarith [one_lt_one_div εpos ε1])
    have pos : 0 < y ^ (1 / ε) := rpow_pos_of_pos ypos _
    rw [ge_iff_le, div_le_iff₀, div_mul_eq_mul_div, le_div_iff₀', mul_comm] <;> try linarith
  · rw [ge_iff_le, le_div_iff₀ <| ypos]; exact (mul_le_iff_le_one_right zero_lt_two).mpr y1

lemma Smooth1Properties_above {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ (c : ℝ), 0 < c ∧ c = 2 * Real.log 2 ∧
      ∀ (ε x) (_ : ε ∈ Ioo 0 1), 1 + c * ε ≤ x → Smooth1 ν ε x = 0 := by
  set c := 2 * Real.log 2; use c
  constructor
  · simp only [c, zero_lt_two, mul_pos_iff_of_pos_left]; exact log_pos (by norm_num)
  constructor
  · rfl
  intro ε x hε hx
  have hx2 := Smooth1Properties_above_aux hx hε
  unfold Smooth1 MellinConvolution
  simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  have ypos := mem_Ioi.mp hy
  by_cases y1 : y ≤ 1
  swap
  · simp [ypos, y1]
  simp only [mem_Ioi.mp hy, y1, and_self, ↓reduceIte, div_eq_zero_iff]; left
  apply DeltaSpikeSupport hε.1 ?_ suppν
  on_goal 1 =>
    simp only [mem_Icc, not_and, not_le]
  on_goal 2 =>
    suffices h : 2 ^ ε < x / y by
      linarith [(by apply rpow_pos_of_pos (by norm_num) : 0 < (2 : ℝ) ^ ε)]
  all_goals
  try intro
  have : x / y = ((x / y) ^ (1 / ε)) ^ ε := by
    rw [← rpow_mul]
    simp only [one_div, inv_mul_cancel₀ (ne_of_gt hε.1), rpow_one]
    apply div_nonneg_iff.mpr; left;
    exact ⟨(le_trans (rpow_pos_of_pos (by norm_num) ε).le) hx2.le, ypos.le⟩
  rw [this]
  refine rpow_lt_rpow (by norm_num) ?_ hε.1
  exact Smooth1Properties_above_aux2 hε ⟨ypos, y1⟩ hx2

lemma DeltaSpikeNonNeg_of_NonNeg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
     {x ε : ℝ} (xpos : 0 < x) (εpos : 0 < ε) :
    0 ≤ DeltaSpike ν ε x := by
  dsimp [DeltaSpike]
  have : 0 < x ^ (1 / ε) := by positivity
  have : 0 ≤ ν (x ^ (1 / ε)) := νnonneg _ this
  positivity

lemma MellinConvNonNeg_of_NonNeg {f g : ℝ → ℝ} (f_nonneg : ∀ x > 0, 0 ≤ f x)
    (g_nonneg : ∀ x > 0, 0 ≤ g x) {x : ℝ} (xpos : 0 < x) :
    0 ≤ MellinConvolution f g x := by
  dsimp [MellinConvolution]
  apply MeasureTheory.setIntegral_nonneg
  · exact measurableSet_Ioi
  · intro y ypos; simp only [mem_Ioi] at ypos
    have : 0 ≤ f y := f_nonneg _ ypos
    have : 0 < x / y := by positivity
    have : 0 ≤ g (x / y) := g_nonneg _ this
    positivity

lemma Smooth1Nonneg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x) {ε x : ℝ}
    (xpos : 0 < x) (εpos : 0 < ε) : 0 ≤ Smooth1 ν ε x := by
  dsimp [Smooth1]
  apply MellinConvNonNeg_of_NonNeg ?_ ?_ xpos
  · intro y hy; by_cases h : y ≤ 1 <;> simp [h, hy]
  · intro y ypos; exact DeltaSpikeNonNeg_of_NonNeg νnonneg ypos εpos

lemma Smooth1LeOne_aux {x ε : ℝ} {ν : ℝ → ℝ} (xpos : 0 < x) (εpos : 0 < ε)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∫ (y : ℝ) in Ioi 0, ν ((x / y) ^ (1 / ε)) / ε / y = 1 := by
    calc
      _ = ∫ (y : ℝ) in Ioi 0, (ν (y ^ (1 / ε)) / ε) / y := ?_
      _ = ∫ (y : ℝ) in Ioi 0, ν y / y := ?_
      _ = 1 := mass_one
    · have := integral_comp_div_I0i_haar (fun y ↦ ν ((x / y) ^ (1 / ε)) / ε) xpos
      convert! this.symm using 1
      congr; funext y; congr; field_simp [mul_comm]
    · have := integral_comp_rpow_I0i_haar_real (fun y ↦ ν y) (one_div_ne_zero εpos.ne')
      rw [← this, abs_of_pos <| one_div_pos.mpr εpos]
      field_simp

lemma Smooth1LeOne {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) {x : ℝ} (xpos : 0 < x) :
    Smooth1 ν ε x ≤ 1 := by
  unfold Smooth1 MellinConvolution DeltaSpike
  have := Smooth1LeOne_aux xpos εpos mass_one
  calc
    _ = ∫ (y : ℝ) in Ioi 0,
        (fun y ↦ if y ∈ Ioc 0 1 then 1 else 0) y * (ν ((x / y) ^ (1 / ε)) / ε / y) := ?_
    _ ≤ ∫ (y : ℝ) in Ioi 0, (ν ((x / y) ^ (1 / ε)) / ε) / y := ?_
    _ = 1 := this
  · rw [setIntegral_congr_fun (by simp)]
    simp only [ite_mul, one_mul, zero_mul, RCLike.ofReal_real_eq_id, id_eq, mem_Ioc]
    intro y hy; aesop
  · refine setIntegral_mono_on ?_ (integrable_of_integral_eq_one this) (by simp) ?_
    · refine integrable_of_integral_eq_one this |>.bdd_mul ?_
        (ae_of_all _ <| by aesop)
      have : (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) =
          indicator (Ioc 0 1) (1 : ℝ → ℝ) := by
        aesop
      simp only [mem_Ioc, this, measurableSet_Ioc, aestronglyMeasurable_indicator_iff]
      exact aestronglyMeasurable_one
    · simp only [ite_mul, one_mul, zero_mul]
      intro y hy
      by_cases h : y ≤ 1
      · aesop
      field_simp
      simp only [mem_Ioc, h, and_false, ↓reduceIte, one_div, mul_zero]
      simp only [mem_Ioi] at hy
      apply div_nonneg
      · apply νnonneg; exact rpow_pos_of_pos (div_pos xpos <| mem_Ioi.mp hy) _
      · positivity

lemma MellinOfSmooth1a {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s =
      s⁻¹ * mellin (fun x ↦ (ν x : ℂ)) (ε * s) := by
  let f' : ℝ → ℂ := fun x ↦ DeltaSpike ν ε x
  let f : ℝ → ℂ := fun x ↦ DeltaSpike ν ε x / x
  let g : ℝ → ℂ := fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0
  let F : ℝ × ℝ → ℂ := Function.uncurry fun x y ↦ f y * g (x / y) * (x : ℂ) ^ (s - 1)
  let S := {⟨x, y⟩ : ℝ × ℝ | 0 < x  ∧ x ≤ y ∧ 2 ^ (-ε) ≤ y ∧ y ≤ 2 ^ ε}
  let F' : ℝ × ℝ → ℂ := piecewise S (fun ⟨x, y⟩ ↦ f y * (x : ℂ) ^ (s - 1))
     (fun _ ↦ 0)
  let Tx := Ioc 0 ((2 : ℝ) ^ ε)
  let Ty := Icc ((2 : ℝ) ^ (-ε)) ((2 : ℝ) ^ ε)

  have Seq : S = (Tx ×ˢ Ty) ∩ {(x, y) : ℝ × ℝ | x ≤ y} := by
    ext ⟨x, y⟩; constructor
    · exact fun h ↦ ⟨⟨⟨h.1, le_trans h.2.1 h.2.2.2⟩, ⟨h.2.2.1, h.2.2.2⟩⟩, h.2.1⟩
    · exact fun h ↦  ⟨h.1.1.1, ⟨h.2, h.1.2.1, h.1.2.2⟩⟩
  have SsubI : S ⊆ Ioi 0 ×ˢ Ioi 0 :=
    fun z hz ↦ ⟨hz.1, lt_of_lt_of_le (by apply rpow_pos_of_pos; norm_num) hz.2.2.1⟩
  have SsubT: S ⊆ Tx ×ˢ Ty := by simp_rw [Seq, inter_subset_left]
  have Smeas : MeasurableSet S := by
    rw [Seq]; apply MeasurableSet.inter ?_ <| measurableSet_le measurable_fst measurable_snd
    simp [measurableSet_prod, Tx, Ty]

  have int_F: IntegrableOn F (Ioi 0 ×ˢ Ioi 0) := by
    apply IntegrableOn.congr_fun (f := F') ?_ ?_ (by simp [measurableSet_prod]); swap
    · simp only [F, F', f, g, mul_ite, mul_one, mul_zero]
      intro ⟨x, y⟩ hz
      by_cases hS : ⟨x, y⟩ ∈ S <;> simp only [hS, piecewise]
      <;> simp only [mem_prod, mem_Ioi, mem_ofPred_eq, not_and, not_le, S] at hz hS
      · simp [div_pos hz.1 hz.2, (div_le_one hz.2).mpr hS.2.1]
      · by_cases hxy : x / y ≤ 1
        swap
        · simp [hxy]
        have hy : y ∉ Icc (2 ^ (-ε)) (2 ^ ε) := by
          simp only [mem_Icc, not_and, not_le]; exact hS hz.1 <| (div_le_one hz.2).mp hxy
        simp [DeltaSpikeSupport εpos hz.2.le suppν hy]
    · apply Integrable.piecewise Smeas ?_ integrableOn_zero
      simp only [IntegrableOn, Measure.restrict_restrict_of_subset SsubI]
      apply MeasureTheory.Integrable.mono_measure ?_
      · apply MeasureTheory.Measure.restrict_mono' SsubT.eventuallyLE le_rfl
      have : volume.restrict (Tx ×ˢ Ty) = (volume.restrict Tx).prod (volume.restrict Ty) := by
        rw [Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]
      erw [this]; conv => lhs; intro; rw [mul_comm]
      apply MeasureTheory.Integrable.mul_prod (f := fun x ↦ (x : ℂ) ^ (s - 1))
        (μ := Measure.restrict volume Tx)
      · simp only [Tx]
        rw [← IntegrableOn, integrableOn_Ioc_iff_integrableOn_Ioo,
          intervalIntegral.integrableOn_Ioo_cpow_iff]
        · simp [hs]
        · apply rpow_pos_of_pos (by norm_num)
      · apply (ContinuousOn.div ?_ ?_ ?_).integrableOn_compact isCompact_Icc
        · exact (DeltaSpikeOfRealContinuous εpos diffν).continuousOn
        · exact continuous_ofReal.continuousOn
        · intro x hx; simp only [mem_Icc] at hx; simp only [ofReal_ne_zero]
          linarith [(by apply rpow_pos_of_pos (by norm_num) : (0 : ℝ) < 2 ^ (-ε))]

  have : mellin (MellinConvolution g f') s = mellin g s * mellin f' s := by
    rw [mul_comm, ← MellinConvolutionTransform f' g s
      (by convert int_F using 1; simp only [f', F, f]; field_simp)]
    dsimp [mellin]; rw [setIntegral_congr_fun (by simp)]
    intro x hx; simp_rw [MellinConvolutionSymmetric _ _ <| mem_Ioi.mp hx]

  convert! this using 1
  · congr; funext x; convert! integral_ofReal.symm
    simp only [MellinConvolution, RCLike.ofReal_div, ite_mul, one_mul, zero_mul, @apply_ite ℝ ℂ,
      algebraMap.coe_zero, g]; rfl
  · rw [MellinOf1 s hs, MellinOfDeltaSpike ν εpos s]
    simp

lemma MellinOfSmooth1b {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (σ₁ : ℝ) (_ : 0 < σ₁)
    (s) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
    ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ := by
  obtain ⟨C, Cpos, hC⟩ := MellinOfPsi diffν suppν
  refine ⟨C, Cpos, ?_⟩
  intro σ₁ σ₁pos s hs1 hs2 ε εpos ε_lt_one
  rw [MellinOfSmooth1a diffν suppν εpos <| lt_of_le_of_lt' hs1 σ₁pos]
  have hh1 : ε * σ₁ ≤ (ε * s).re := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  have hh2 : (ε * s).re ≤ 2 := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  calc
    ‖s⁻¹ * mellin (fun x ↦ (ν x : ℂ)) (ε * s)‖ =
        ‖s⁻¹‖ * ‖mellin (fun x ↦ (ν x : ℂ)) (ε * s)‖ := by simp
    _                        ≤ ‖s⁻¹‖ * (C * (ε * ‖s‖)⁻¹) := by
      gcongr
      convert! hC (ε * σ₁) (by positivity) (ε * s) hh1 hh2
      simp [abs_eq_self.mpr εpos.le]
    _                        = C * (ε * ‖s‖ ^ 2)⁻¹ := by
      simp only [norm_inv, mul_inv_rev]
      ring

lemma MellinOfSmooth1c {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    (fun ε ↦ mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) =O[𝓝[>]0] id := by
  have h := MellinOfDeltaSpikeAt1_asymp diffν suppν mass_one
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  use c
  filter_upwards [hc, Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1)] with ε hε hε'
  rw [MellinOfSmooth1a diffν suppν hε'.1 (s := 1) (by norm_num)]
  simp only [inv_one, mul_one, one_mul, id_eq, Real.norm_eq_abs]
  exact hε

lemma Smooth1ContinuousAt {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : SmoothingF.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y) :
    ContinuousAt (fun x ↦ Smooth1 SmoothingF ε x) y := by
  apply ContinuousAt.congr
    (f := (fun x ↦ MellinConvolution (DeltaSpike SmoothingF ε)
      (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) x)) _
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply MellinConvolutionSymmetric _ _ hx
  apply continuousAt_of_dominated (bound := (fun x ↦ 2 ^ ε * DeltaSpike SmoothingF ε x))
  · filter_upwards [lt_mem_nhds ypos] with x hx
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · apply Measurable.mul
      · exact Continuous.measurable <| DeltaSpikeContinuous εpos diffSmoothingF
      · apply Measurable.ite _ (by fun_prop) (by fun_prop)
        apply MeasurableSet.congr (s := Ici x) (by measurability)
        ext a
        constructor
        · intro ha
          have apos : 0 < a := lt_of_lt_of_le hx ha
          constructor
          · exact div_pos hx apos
          · exact (div_le_one apos).mpr ha
        · intro ha
          have : 0 < a := (div_pos_iff_of_pos_left hx).mp ha.1
          exact (div_le_one this).mp ha.2
    · fun_prop
  · filter_upwards [lt_mem_nhds ypos] with x hx
    filter_upwards [ae_restrict_mem (by measurability)] with t ht
    simp only [mul_ite, mul_one, mul_zero, RCLike.ofReal_real_eq_id, id_eq, norm_div, norm_eq_abs]
    by_cases! h : DeltaSpike SmoothingF ε t = 0
    · simp [h]
    have := DeltaSpikeSupport' εpos ht.le suppSmoothingF h
    have dsnonneg : 0 ≤ DeltaSpike SmoothingF ε t := by
      apply DeltaSpikeNonNeg_of_NonNeg <;> assumption
    calc
      _ ≤ |DeltaSpike SmoothingF ε t| / |t| := by
        gcongr
        · split_ifs with h
          · apply le_refl
          · exact dsnonneg
      _ ≤ _ := by
        rw [_root_.abs_of_nonneg dsnonneg, mul_comm, div_eq_mul_one_div, _root_.abs_of_pos ht]
        gcongr
        apply (one_div_le ht (by bound)).mpr
        · convert this.1 using 1
          rw [div_eq_iff (by positivity), ← rpow_add (by norm_num), neg_add_cancel, rpow_zero]
  · apply Integrable.const_mul
    apply (integrable_indicator_iff (by measurability)).mp
    apply (integrableOn_iff_integrable_of_support_subset (s := Icc (2 ^ (-ε)) (2 ^ ε)) _).mp
    · apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply ContinuousOn.congr  (f := DeltaSpike SmoothingF ε)
      · apply Continuous.continuousOn
        apply DeltaSpikeContinuous<;> assumption
      · intro x hx
        have : x ∈ Ioi 0 := by
          apply mem_Ioi.mpr
          apply lt_of_lt_of_le (by bound) hx.1
        rw [indicator, if_pos this]
    · unfold indicator
      simp_rw [mem_Ioi]
      apply Function.support_subset_iff.mpr
      simp only [ne_eq, ite_eq_right_iff, Classical.not_imp, mem_Icc, and_imp]
      intro x hx
      apply DeltaSpikeSupport' εpos hx.le suppSmoothingF
  · have : ∀ᵐ (a : ℝ) ∂volume.restrict (Ioi 0), a ≠ y := by
      apply ae_iff.mpr
      simp
    filter_upwards [ae_restrict_mem (by measurability), this] with x hx hx2
    simp only [mem_Ioi] at hx
    apply ContinuousAt.div_const
    apply ContinuousAt.mul (by fun_prop)
    have : (fun x_1 ↦ if 0 < x_1 / x ∧ x_1 / x ≤ 1 then 1 else 0) =
        (Ioc 0 x).indicator (fun _ ↦ (1 : ℝ)) := by
      ext t
      unfold indicator
      simp [div_pos_iff_of_pos_right, div_le_one₀, hx]
    rw [this]
    apply ContinuousOn.continuousAt_indicator (by fun_prop)
    simp [frontier_Ioc hx, ypos.ne', hx2.symm]

lemma Smooth1MellinConvergent {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) : MellinConvergent (fun x ↦ (Smooth1 Ψ ε x : ℂ)) s := by
  apply mellinConvergent_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
  · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    apply continuousOn_of_forall_continuousAt
    exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
  · rw [Asymptotics.isBigO_iff]
    use 1
    obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
    filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
    rw [hc _ _ hε hx]
    simp only [ofReal_zero, norm_zero, neg_mul, one_mul, norm_eq_abs, abs_exp]
    bound
  · rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [norm_real, norm_eq_abs, neg_zero, rpow_zero, one_mem, CStarRing.norm_of_mem_unitary,
      mul_one]
    rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
    exact Smooth1LeOne Ψnonneg mass_one hε.1 hx

lemma Smooth1MellinDifferentiable {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (fun x ↦ (Smooth1 Ψ ε x : ℂ))) s := by
  apply mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one _ _ _ hs
  · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
    apply continuousOn_of_forall_continuousAt
    exact fun x hx ↦ Smooth1ContinuousAt diffΨ Ψnonneg suppΨ hε.1 hx |>.ofReal
  · rw [Asymptotics.isBigO_iff]
    use 1
    obtain ⟨c, cpos, ceq, hc⟩ := Smooth1Properties_above suppΨ
    filter_upwards [eventually_ge_atTop (1 + c * ε)] with x hx
    rw [hc _ _ hε hx]
    simp only [ofReal_zero, norm_zero, neg_mul, one_mul, norm_eq_abs, abs_exp]
    bound
  · rw [Asymptotics.isBigO_iff]
    use 1
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    simp only [norm_real, norm_eq_abs, neg_zero, rpow_zero, one_mem, CStarRing.norm_of_mem_unitary,
      mul_one]
    rw [_root_.abs_of_nonneg <| Smooth1Nonneg Ψnonneg hx hε.1]
    exact Smooth1LeOne Ψnonneg mass_one hε.1 hx

end PNT_MellinCalculus
section PNT_MediumPNT
open Set Function Filter Complex Real
open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev ArithmeticFunction.vonMangoldt
namespace Chebyshev
theorem psi_eq_sum_range (x : ℝ) :
    ψ x = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n := by
  rw [psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]
end Chebyshev
theorem LogDerivativeDirichlet (s : ℂ) (hs : 1 < s.re) :
    - deriv riemannZeta s / riemannZeta s = ∑' n, Λ n / (n : ℂ) ^ s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  dsimp [LSeries, LSeries.term]
  nth_rewrite 2 [Summable.tsum_eq_add_tsum_ite (b := 0) ?_]
  · simp
  · have := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    dsimp [LSeriesSummable] at this
    convert! this; rename ℕ => n
    by_cases h : n = 0 <;> simp [LSeries.term, h]
noncomputable abbrev SmoothedChebyshevIntegrand
    (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s
noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)
open ComplexConjugate
lemma smoothedChebyshevIntegrand_conj
    {SmoothingF : ℝ → ℝ} {ε X : ℝ} (Xpos : 0 < X) (s : ℂ) :
    SmoothedChebyshevIntegrand SmoothingF ε X (conj s) =
      conj (SmoothedChebyshevIntegrand SmoothingF ε X s) := by
  unfold SmoothedChebyshevIntegrand
  simp only [map_mul, map_div₀, map_neg]
  congr
  · exact deriv_riemannZeta_conj s
  · exact riemannZeta_conj s
  · unfold mellin
    rw[← integral_conj]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x xpos
    simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
    congr
    nth_rw 1 [← map_one conj]
    rw[← map_sub, Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg xpos.le]
    exact Real.pi_ne_zero.symm
  · rw[Complex.cpow_conj, Complex.conj_ofReal]
    rw[Complex.arg_ofReal_of_nonneg Xpos.le]
    exact Real.pi_ne_zero.symm
open MeasureTheory
lemma SmoothedChebyshevDirichlet_aux_integrable {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    MeasureTheory.Integrable
      (fun (y : ℝ) ↦ mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + y * I)) := by
  obtain ⟨c, cpos, hc⟩ := MellinOfSmooth1b diffSmoothingF suppSmoothingF
  apply Integrable.mono' (g := (fun t ↦ c / ε * 1 / (1 + t ^ 2)))
  · apply Integrable.const_mul integrable_inv_one_add_sq
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro x
    have := Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
      SmoothingFpos mass_one (s := σ + x * I) (by simp only [add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]; linarith) |>.continuousAt
    fun_prop
  · filter_upwards [] with t
    calc
      _≤ c / ε * 1 / (σ^2 + t^2) := by
        convert hc (σ / 2) (by linarith) (σ + t * I) (by simp only [add_re, ofReal_re, mul_re,
          I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, half_le_self_iff]; linarith)
          (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
            sub_self, add_zero]; linarith) ε εpos  ε_lt_one using 1
        simp only [mul_one, Complex.sq_norm, normSq_apply, add_re, ofReal_re, mul_re, I_re,
          mul_zero, ofReal_im, I_im, sub_self, add_zero, add_im, mul_im, zero_add, mul_inv_rev]
        ring_nf
      _ ≤ _ := by
        gcongr; nlinarith
lemma SmoothedChebyshevDirichlet_aux_tsum_integral {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) {X : ℝ}
    (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
    (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + t * I) *
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + ↑t * I) *
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by
  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + ↑a * I) := by
    rw [← continuousOn_univ]
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re })
    · refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
        SmoothingFpos mass_one hz).continuousAt
    · fun_prop
    · simp only [mapsTo_univ_iff, mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]; linarith
  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := i) (by linarith)]
    norm_cast
  rw [MeasureTheory.integral_tsum]
  · have x_neq_zero : X ≠ 0 := by linarith
    intro i
    by_cases i_eq_zero : i = 0
    · simpa [i_eq_zero] using aestronglyMeasurable_const
    · have hc (c : ℂ) (hc : c ≠ 0) : Continuous fun t : ℝ ↦ c ^ ((σ : ℂ) + t * I) :=
        .const_cpow (by fun_prop) (.inl hc)
      exact (((continuous_const.div₀ (hc _ (by simpa)) fun t ↦ by simp [i_eq_zero]).mul
        cont_mellin_smooth).mul (hc _ (by simpa))).aestronglyMeasurable
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [nnnorm_real, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply ENNReal.mul_lt_top ?_ ENNReal.coe_lt_top
    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]
    rw [ENNReal.tsum_mul_right]
    apply ENNReal.mul_lt_top
    · rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      convert (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
        (by simp only [ofReal_re]; linarith)).norm
      rw [LSeries.term_def]
      split_ifs with h <;> simp[h]
    · simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos suppSmoothingF
            mass_one εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral
theorem SmoothedChebyshevDirichlet {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    SmoothedChebyshev SmoothingF ε X =
      ∑' n, ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (n / X) := by
  dsimp [SmoothedChebyshev, SmoothedChebyshevIntegrand, VerticalIntegral', VerticalIntegral]
  set σ : ℝ := 1 + (Real.log X)⁻¹
  have log_gt : 1 < Real.log X := logt_gt_one X_gt.le
  have σ_gt : 1 < σ := by
    simp only [σ]
    have : 0 < (Real.log X)⁻¹ := by
      simp only [inv_pos]
      linarith
    linarith
  have σ_le : σ ≤ 2 := by
    simp only [σ]
    have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ log_gt
    linarith
  calc
    _ = 1 / (2 * π * I) * (I * ∫ (t : ℝ), ∑' n, Λ n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, ∫ (t : ℝ), Λ n / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, Λ n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, Λ n * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, Λ n * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) *
        ((n : ℂ) / X) ^ (-(σ + ↑t * I))) := ?_
    _ = _ := ?_
  · congr; ext t
    rw [LogDerivativeDirichlet]
    · rw [← tsum_mul_right, ← tsum_mul_right]
    · simp [σ_gt]
  · congr
    exact SmoothedChebyshevDirichlet_aux_tsum_integral diffSmoothingF SmoothingFpos
      suppSmoothingF mass_one (by linarith) εpos ε_lt_one σ_gt σ_le
  · field_simp; congr; ext n; rw [← MeasureTheory.integral_const_mul]; congr; ext t
    by_cases n_ne_zero : n = 0
    · simp [n_ne_zero]
    rw [mul_div_assoc, mul_assoc]
    congr
    rw [(div_eq_iff ?_).mpr]
    · have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + I * t) ?_ ?_
      · push_cast at this ⊢
        rw [← this, div_mul_cancel₀]
        · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
      · apply div_nonneg (by linarith : 0 ≤ X); simp
      · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, n_ne_zero, false_and,
        not_false_eq_true]
  · conv => rw [← mul_assoc, div_mul]; lhs; lhs; rhs; simp
  · simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
  · have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
    have hn (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
    have (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
      simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) (by linarith : 0 ≤ X)]
    have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
        ((n / X) ^ (-1 : ℂ)) ^ (σ + ↑t * I) := by
      rw [cpow_mul] <;> {rw [this n]; simp [Real.pi_pos, Real.pi_nonneg]}
    conv => rhs; lhs; intro n; rhs; rhs; rhs; intro t; rhs; rw [ht t, h n t]; lhs; rw [hn]
  · push_cast
    congr
    ext n
    by_cases n_zero : n = 0
    · simp [n_zero]
    have n_pos : 0 < n := by
      simpa only [n_zero, gt_iff_lt, false_or] using (Nat.eq_zero_or_pos n)
    congr
    have := mellinInv_mellin_eq σ (f := fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (x := n / X)
      ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [mellinInv, VerticalIntegral] at this
      convert! this using 4
      · norm_cast
      · rw [mul_comm]
        norm_cast
    · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
    · apply Smooth1MellinConvergent diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
        SmoothingFpos mass_one
      simp only [ofReal_re]
      linarith
    · dsimp [VerticalIntegrable]
      apply SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos
        suppSmoothingF mass_one εpos ε_lt_one σ_gt σ_le
    · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
      exact Smooth1ContinuousAt diffSmoothingF SmoothingFpos suppSmoothingF
        εpos (by positivity)
theorem SmoothedChebyshevClose_aux {Smooth1 : (ℝ → ℝ) → ℝ → ℝ → ℝ} (SmoothingF : ℝ → ℝ)
    (c₁ : ℝ) (c₁_pos : 0 < c₁) (c₁_lt : c₁ < 1)
    (c₂ : ℝ) (c₂_pos : 0 < c₂) (c₂_lt : c₂ < 2)
    (hc₂ : ∀ (ε x : ℝ), ε ∈ Ioo 0 1 → 1 + c₂ * ε ≤ x → Smooth1 SmoothingF ε x = 0)
    (C : ℝ) (C_eq : C = 6 * (3 * c₁ + c₂))
    (ε : ℝ) (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (X_pos : 0 < X) (X_gt_three : 3 < X)
    (X_bound_1 : 1 ≤ X * ε * c₁) (X_bound_2 : 1 ≤ X * ε * c₂)
    (smooth1BddAbove : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≤ 1)
    (smooth1BddBelow : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≥ 0)
    (smoothIs1 : ∀ (n : ℕ), 0 < n → ↑n ≤ X * (1 - c₁ * ε) →
      Smooth1 SmoothingF ε (↑n / X) = 1)
    (smoothIs0 : ∀ (n : ℕ), 1 + c₂ * ε ≤ ↑n / X → Smooth1 SmoothingF ε (↑n / X) = 0) :
  ‖(↑((∑' (n : ℕ), ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (↑n / X))) : ℂ) -
      ψ X‖ ≤
    C * ε * X * Real.log X := by
  norm_cast
  let F := Smooth1 SmoothingF ε
  let n₀ := ⌈X * (1 - c₁ * ε)⌉₊
  have n₀_pos : 0 < n₀ := by
    simp only [Nat.ceil_pos, n₀]
    subst C_eq
    simp_all only [mem_Ioo, and_imp, ge_iff_le, implies_true, mul_pos_iff_of_pos_left, sub_pos]
    exact (mul_le_of_le_one_right c₁_pos.le ε_lt_one.le).trans_lt c₁_lt
  have n₀_inside_le_X : X * (1 - c₁ * ε) ≤ X := by
    nth_rewrite 2 [← mul_one X]
    apply mul_le_mul_of_nonneg_left _ X_pos.le
    apply sub_le_self
    positivity
  have n₀_le : n₀ ≤ X * ((1 - c₁ * ε)) + 1 := by
    simp only [n₀]
    exact le_of_lt (Nat.ceil_lt_add_one (by bound))
  have n₀_gt : X * ((1 - c₁ * ε)) ≤ n₀ := by
    simp only [n₀]
    exact Nat.le_ceil (X * (1 - c₁ * ε))
  have sumΛ : Summable (fun (n : ℕ) ↦ Λ n * F (n / X)) := by
    exact (summable_of_ne_finset_zero fun a s=>mul_eq_zero_of_right _
    (hc₂ _ _ (⟨ε_pos, ε_lt_one⟩) ((le_div_iff₀ X_pos).2 (Nat.ceil_le.1 (not_lt.1
    (s ∘ Finset.mem_range.2))))))
  have sumΛn₀ (n₀ : ℕ) : Summable (fun n ↦ Λ (n + n₀) * F ((n + n₀) / X)) := by
    exact_mod_cast sumΛ.comp_injective fun Q => by omega
  rw[← Summable.sum_add_tsum_nat_add' (k := n₀) (mod_cast sumΛn₀ n₀)]
  let n₁ := ⌊X * (1 + c₂ * ε)⌋₊
  have n₁_pos : 0 < n₁ := by
    dsimp only [n₁]
    apply Nat.le_floor
    rw[Nat.succ_eq_add_one, zero_add]
    norm_cast
    apply one_le_mul_of_one_le_of_one_le (by linarith)
    apply le_add_of_nonneg_right
    positivity
  have n₁_ge : X * (1 + c₂ * ε) - 1 ≤ n₁ := by
    simp only [tsub_le_iff_right, n₁]
    exact le_of_lt (Nat.lt_floor_add_one (X * (1 + c₂ * ε)))
  have n₁_le : (n₁ : ℝ) ≤ X * (1 + c₂ * ε) := by
    simp only [n₁]
    exact Nat.floor_le (by bound)
  have n₁_ge_n₀ : n₀ ≤ n₁ := by
    exact_mod_cast le_imp_le_of_le_of_le n₀_le n₁_ge (by linarith)
  have n₁_sub_n₀ : (n₁ : ℝ) - n₀ ≤ X * ε * (c₂ + c₁) := by
    calc
      (n₁ : ℝ) - n₀ ≤ X * (1 + c₂ * ε) - n₀ := by
                        exact sub_le_sub_right n₁_le ↑n₀
       _            ≤ X * (1 + c₂ * ε) - (X * (1 - c₁ * ε)) := by
          exact tsub_le_tsub_left n₀_gt (X * (1 + c₂ * ε))
       _            = X * ε * (c₂ + c₁) := by ring
  rw[show (∑' (n : ℕ), Λ (n + n₀ : ) * F ((n + n₀ : ) / X)) =
      (∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((n + n₀) / X)) +
      (∑' (n : ℕ), Λ (n + n₁ : ) * F ((n + n₁ : ) / X)) by
    rw[← Summable.sum_add_tsum_nat_add' (k := n₁ - n₀)]
    · congr! 5
      · simp only [Nat.cast_add]
      · omega
      · congr! 1
        norm_cast
        omega
    · convert sumΛn₀ ((n₁ - n₀) + n₀) using 4
      · omega
      · congr! 1
        norm_cast
        omega]
  rw [show(∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X)) = Λ (n₁) * F (↑n₁ / X) by
    have : (∑' (n : ℕ), Λ (n + n₁) * F (↑(n + n₁) / X)) =
        Λ (n₁) * F (↑n₁ / X) + (∑' (n : ℕ), Λ (n + 1 + n₁) * F (↑(n + 1 + n₁) / X)) := by
      let fTemp := fun n ↦ Λ (n + n₁) * F ((↑n + ↑n₁) / X)
      have hTemp (n : ℕ): fTemp n = Λ (n + n₁) * F (↑(n + n₁) / X) := by rw[Nat.cast_add]
      rw[← tsum_congr hTemp, ← tsum_congr fun n ↦ (hTemp (n + 1))]
      have : Λ n₁ * F (↑n₁ / X) = fTemp 0 := by
        dsimp only [fTemp]
        rw[← Nat.cast_add, zero_add]
      rw[this]
      exact Summable.tsum_eq_zero_add (sumΛn₀ n₁)
    rw[this]
    apply add_eq_left.mpr
    convert tsum_zero with n
    convert mul_zero _
    apply smoothIs0
    rw[← mul_le_mul_iff_left₀ X_pos]
    rw [(by field_simp : ↑(n + 1 + n₁) / X * X = ↑(n + 1 + n₁)),
      (by ring : (1 + c₂ * ε) * X = 1 + (X * (1 + c₂ * ε) - 1)), Nat.cast_add, Nat.cast_add]
    bound]
  have X_le_floor_add_one : X ≤ ↑⌊X + 1⌋₊ := by
    rw[Nat.floor_add_one (by linarith), Nat.cast_add, Nat.cast_one]
    apply le_trans <| Nat.le_ceil X
    exact_mod_cast Nat.ceil_le_floor_add_one X
  have floor_X_add_one_le_self : ↑⌊X + 1⌋₊ ≤ X + 1 := Nat.floor_le (by positivity)
  rw [show ψ X =
      (∑ x ∈ Finset.range n₀, Λ x) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + ↑n₀) by
    field_simp
    simp only [add_comm _ n₀]
    rw [← Finset.sum_range_add, Nat.add_sub_of_le, Chebyshev.psi_eq_sum_range,
      Nat.floor_add_one X_pos.le]
    dsimp only [n₀]
    exact Nat.ceil_le.mpr (by linarith)]
  rw [show ∑ n ∈ Finset.range n₀, Λ n * F (↑n / X) =
      ∑ n ∈ Finset.range n₀, Λ n by
    apply Finset.sum_congr rfl
    intro n hn
    obtain rfl|n_zero := eq_or_ne n 0
    · simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_div, zero_mul]
    · convert mul_one _
      apply smoothIs1 n (Nat.zero_lt_of_ne_zero n_zero) ?_
      simp only [Finset.mem_range, n₀] at hn
      exact Nat.lt_ceil.mp hn |>.le]
  have vonBnd1 :
    ∀ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ ≤ Real.log (X * (1 + c₂ * ε)) := by
    intro n hn
    have n_add_n0_le_n1: (n : ℝ) + n₀ ≤ n₁ := by
      apply le_of_lt
      rw[Finset.mem_range] at hn
      rw[← add_lt_add_iff_right (-↑n₀), add_neg_cancel_right, add_comm, ← sub_eq_neg_add]
      exact_mod_cast hn
    have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
    have inter2: Real.log (↑n + ↑n₀) ≤ Real.log (↑n₁) := by
      exact_mod_cast Real.log_le_log (by positivity) n_add_n0_le_n1
    have inter3: Real.log (↑n₁) ≤ Real.log (X * (1 + c₂ * ε)) := by
      exact Real.log_le_log (by bound) (by linarith)
    exact le_imp_le_of_le_of_le inter1 inter3 inter2
  have bnd1 :
    ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖
    ≤ (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) := by
    have : (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) =
        (∑ n ∈ Finset.range (n₁ - n₀), Real.log (X * (1 + c₂ * ε))) := by
      rw[← Nat.cast_sub]
      · nth_rewrite 1 [← Finset.card_range (n₁ - n₀)]
        rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
        exact Eq.symm (Finset.sum_const (Real.log (X * (1 + c₂ * ε))))
      exact n₁_ge_n₀
    rw [this]
    apply Finset.sum_le_sum
    intro n hn
    rw [← mul_one (Real.log (X * (1 + c₂ * ε)))]
    apply mul_le_mul (vonBnd1 _ hn) _ (norm_nonneg _) (log_nonneg (by bound))
    rw[Real.norm_of_nonneg, ← Nat.cast_add]
    · dsimp only [F]
      apply smooth1BddAbove
      bound
    rw[← Nat.cast_add]
    dsimp only [F]
    apply smooth1BddBelow
    bound
  have bnd2 :
    ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ ≤ (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) := by
    have : (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) =
        (∑ n ∈ Finset.range (⌊X + 1⌋₊ - n₀), Real.log (X + 1)) := by
      rw[← Nat.cast_sub]
      · nth_rewrite 1 [← Finset.card_range (⌊X + 1⌋₊ - n₀)]
        rw[Finset.cast_card, Finset.sum_const, smul_one_mul]
        exact Eq.symm (Finset.sum_const (Real.log (X + 1)))
      simp only [Nat.ceil_le, n₀]
      exact Preorder.le_trans (X * (1 - c₁ * ε)) X (↑⌊X + 1⌋₊) n₀_inside_le_X
        X_le_floor_add_one
    rw[this]
    apply Finset.sum_le_sum
    intro n hn
    have n_add_n0_le_X_add_one: (n : ℝ) + n₀ ≤ X + 1 := by
      rw[Finset.mem_range] at hn
      rw [← add_le_add_iff_right (-↑n₀), add_assoc, ← sub_eq_add_neg, sub_self, add_zero,
        ← sub_eq_add_neg]
      have temp: (n : ℝ) < ⌊X + 1⌋₊ - n₀ := by
        rw [← Nat.cast_sub, Nat.cast_lt]
        · exact hn
        simp only [Nat.ceil_le, n₀]
        exact le_trans n₀_inside_le_X X_le_floor_add_one
      have : ↑⌊X + 1⌋₊ - ↑n₀ ≤ X + 1 - ↑n₀ := by
        apply sub_le_sub_right floor_X_add_one_le_self
      exact le_of_lt (lt_of_le_of_lt' this temp)
    have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
    apply le_trans inter1
    exact_mod_cast Real.log_le_log (by positivity) (n_add_n0_le_X_add_one)
  clear vonBnd1
  have inter1 : Real.log (X * (1 + c₂ * ε)) ≤ Real.log (3 * X) := by
    apply Real.log_le_log (by positivity)
    have const_le_2: 1 + c₂ * ε ≤ 3 := by
      have : (3 : ℝ) = 1 + 2 := by ring
      rw[this]
      apply add_le_add_right
      rw[← mul_one 2]
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    rw[mul_comm]
    exact mul_le_mul const_le_2 (by rfl) (by positivity) (by positivity)
  calc
    _ = ‖∑ n ∈ Finset.range (n₁ - n₀), Λ (n + n₀) * F ((↑n + ↑n₀) / X) -
          ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), Λ (x + n₀) + Λ n₁ * F (↑n₁ / X)‖ := by
      congr 1
      ring
    _ ≤ (∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖F ((↑n + ↑n₀) / X)‖) +
        ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
        ‖Λ n₁‖ * ‖F (↑n₁ / X)‖ := by
      apply norm_add_le_of_le
      · apply norm_sub_le_of_le
        · apply norm_sum_le_of_le
          intro b hb
          exact norm_mul_le_of_le (by rfl) (by rfl)
        apply norm_sum_le_of_le
        intro b hb
        rfl
      exact_mod_cast norm_mul_le_of_le (by rfl) (by rfl)
    _ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * Real.log X + Real.log (3 * X) := by
      apply add_le_add
      · apply le_trans <| add_le_add bnd1 bnd2
        rw [(by ring : 2 * (X * ε * (3 * c₁ + c₂)) = 2 * (X * ε * (c₁ + c₂)) + 4 * (X * ε * c₁)), add_mul]
        apply add_le_add
        · calc
            _ ≤ (X * ε * (c₂ + c₁)) * (Real.log (X) + Real.log (3)) := by
              apply mul_le_mul n₁_sub_n₀ _ (log_nonneg (by linarith)) (by positivity)
              rw[← Real.log_mul (by positivity) (by positivity)]
              nth_rewrite 3 [mul_comm]
              exact inter1
            _ ≤ 2 * ((X * ε * (c₂ + c₁)) * Real.log X) := by
              rw[two_mul, mul_add]
              bound
            _ = _ := by ring
        calc
          _ ≤ 2 * (X * ε * c₁) * (Real.log (X) + Real.log (3)) := by
            apply mul_le_mul _ _ (log_nonneg (by linarith)) (by positivity)
            · rw [(by ring : 2 * (X * ε * c₁) = (X * (1 + ε * c₁)) - (X * (1 - ε * c₁)))]
              apply sub_le_sub
              · apply le_trans floor_X_add_one_le_self
                ring_nf
                rw[add_comm, add_le_add_iff_left]
                exact X_bound_1
              nth_rewrite 2 [mul_comm]
              exact n₀_gt
            rw[← Real.log_mul (by positivity) (by norm_num), mul_comm]
            exact Real.log_le_log (by positivity) (by linarith)
          _ = 2 * (X * ε * c₁ * Real.log X) + 2 * (X * ε * c₁ * Real.log 3) := by ring
          _ ≤ 2 * (X * ε * c₁ * Real.log X) + 2 * (X * ε * c₁ * Real.log X) := by gcongr
          _ = _ := by ring
      · apply le_trans _ inter1
        rw[← mul_one (Real.log (X * (1 + c₂ * ε)))]
        apply mul_le_mul _ _ (norm_nonneg _) (log_nonneg (by bound))
        · rw[Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact le_trans ArithmeticFunction.vonMangoldt_le_log <|
            Real.log_le_log (mod_cast n₁_pos) n₁_le
        rw[Real.norm_of_nonneg <| smooth1BddBelow _ n₁_pos]
        apply smooth1BddAbove _ n₁_pos
    _ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * (Real.log X + (Real.log X + Real.log 3)) := by
      rw [← Real.log_mul (by positivity) (by positivity), mul_comm X 3]
      nth_rewrite 2 [mul_add]
      apply add_le_add_right
      nth_rewrite 1 [← one_mul (Real.log (3 * X))]
      apply mul_le_mul_of_nonneg_right _ (log_nonneg (by linarith))
      linarith
    _ = 4 * (X * ε * (3 * c₁ + c₂)) * Real.log X +
          2 * (X * ε * (3 * c₁ + c₂)) * Real.log 3 := by ring
    _ ≤ 4 * (X * ε * (3 * c₁ + c₂)) * Real.log X +
          2 * (X * ε * (3 * c₁ + c₂)) * Real.log X := by gcongr
    _ = _ := by
      rw [C_eq]
      ring
theorem SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ψ X‖ ≤ C * ε * X * Real.log X := by
  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ := Smooth1Properties_below suppSmoothingF mass_one
  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ := Smooth1Properties_above suppSmoothingF
  have c₁_lt : c₁ < 1 := by
    rw[c₁_eq]
    exact lt_trans (Real.log_two_lt_d9) (by norm_num)
  have c₂_lt : c₂ < 2 := by
    rw[c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    · rfl
    · exact lt_trans (Real.log_two_lt_d9) (by norm_num)
    · exact Real.log_nonneg (by norm_num)
    · positivity
  let C : ℝ := 6 * (3 * c₁ + c₂)
  have C_eq : C = 6 * (3 * c₁ + c₂) := rfl
  clear_value C
  have Cpos : 0 < C := by
    rw [C_eq]
    positivity
  refine ⟨C, Cpos, fun X X_ge_C ε εpos ε_lt_one ↦ ?_⟩
  have X_gt_zero : (0 : ℝ) < X := by linarith
  have n_on_X_pos {n : ℕ} (npos : 0 < n) :
      0 < n / X := by
    have : (0 : ℝ) < n := by exact_mod_cast npos
    positivity
  have smooth1BddAbove (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one εpos (n_on_X_pos npos)
  have smooth1BddBelow (n : ℕ) (npos : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≥ 0 :=
    Smooth1Nonneg SmoothingFnonneg (n_on_X_pos npos) εpos
  have smoothIs1 (n : ℕ) (npos : 0 < n) (n_le : n ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (↑n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) εpos (n_on_X_pos npos)
    exact (div_le_iff₀' X_gt_zero).mpr n_le
  have smoothIs0 (n : ℕ) (n_le : (1 + c₂ * ε) ≤ n / X) :=
    hc₂ (ε := ε) (n / X) ⟨εpos, ε_lt_one⟩ n_le
  have ε_pos: ε > 0 := by linarith
  have X_pos: X > 0 := by linarith
  have X_gt_three : 3 < X := by linarith
  intro X_bound
  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw[c₁_eq, ← div_le_iff₀]
    · have : 1 / Real.log 2 < 2 := by
        nth_rewrite 2 [← one_div_one_div 2]
        rw[one_div_lt_one_div]
        · exact lt_of_le_of_lt (by norm_num) (Real.log_two_gt_d9)
        · exact Real.log_pos (by norm_num)
        norm_num
      exact le_of_lt (gt_trans X_bound this)
    exact Real.log_pos (by norm_num)
  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw[c₂_eq, ← div_le_iff₀]
    · have : 1 / (2 * Real.log 2) < 2 := by
        nth_rewrite 3 [← one_div_one_div 2]
        · rw[one_div_lt_one_div, ← one_mul (1 / 2)]
          · apply mul_lt_mul
            · norm_num
            · apply le_of_lt
              exact lt_trans (by norm_num) (Real.log_two_gt_d9)
            repeat norm_num
          · norm_num
            exact Real.log_pos (by norm_num)
          · norm_num
      exact le_of_lt (gt_trans X_bound this)
    norm_num
    exact Real.log_pos (by norm_num)
  rw [SmoothedChebyshevDirichlet diffSmoothingF SmoothingFnonneg suppSmoothingF
    mass_one (by linarith) εpos ε_lt_one]
  convert SmoothedChebyshevClose_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C C_eq ε
    ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2 smooth1BddAbove smooth1BddBelow
    smoothIs1 smoothIs0
def LogDerivZetaHasBound (n₁ n₂ : ℝ) (A C : ℝ) : Prop := ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ n₁)), ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤
    C * Real.log |t| ^ n₂
noncomputable def I₁ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))
noncomputable def I₂ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)))
noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))
noncomputable def I₈ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + T * I)))
noncomputable def I₉ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))
noncomputable def I₃ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))
noncomputable def I₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))
noncomputable def I₄ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)))
noncomputable def I₆ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + 3 * I)))
noncomputable def I₅ (SmoothingF : ℝ → ℝ) (ε X σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) *
    (I * (∫ t in (-3)..3, SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)))
theorem realDiff_of_complexDiff {f : ℂ → ℂ} (s : ℂ) (hf : DifferentiableAt ℂ f s) :
    ContinuousAt (fun (x : ℝ) ↦ f (s.re + x * I)) s.im := by
  apply ContinuousAt.comp _ (by fun_prop)
  convert hf.continuousAt
  simp
def LogDerivZetaIsHoloSmall (σ₂ : ℝ) : Prop :=
    HolomorphicOn (fun (s : ℂ) ↦ deriv riemannZeta s / (riemannZeta s))
    (((uIcc σ₂ 2)  ×ℂ (uIcc (-3) 3)) \ {1})
theorem dlog_riemannZeta_bdd_on_vertical_lines_explicit {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
  ∀(t : ℝ), ‖(-deriv riemannZeta (σ₀ + t * I) / riemannZeta (σ₀ + t * I))‖ ≤ ‖(deriv riemannZeta σ₀ / riemannZeta σ₀)‖ :=
  fun _ ↦ dlog_riemannZeta_bdd_on_vertical_lines_generalized _ _ _ σ₀_gt <| le_refl _
theorem dlog_riemannZeta_bdd_on_vertical_lines {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) :
    ∃ c > 0, ∀(t : ℝ), ‖deriv riemannZeta (σ₀ + t * I) / riemannZeta (σ₀ + t * I)‖ ≤ c := by
  refine ⟨1 + ‖(deriv riemannZeta σ₀ / riemannZeta σ₀)‖, (by positivity), fun t ↦ ?_⟩
  have := dlog_riemannZeta_bdd_on_vertical_lines_explicit σ₀_gt t
  rw [neg_div, norm_neg] at this
  exact le_trans this (lt_one_add _).le
theorem SmoothedChebyshevPull1_aux_integrable {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    {X : ℝ} (X_gt : 3 < X)
    {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) (σ₀_le_2 : σ₀ ≤ 2)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    :
    Integrable (fun (t : ℝ) ↦
      SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + (t : ℂ) * I)) volume := by
  obtain ⟨C, C_pos, hC⟩ := dlog_riemannZeta_bdd_on_vertical_lines σ₀_gt
  let c : ℝ := C * X ^ σ₀
  have : ∀ t, ‖(fun (t : ℝ) ↦ (- deriv riemannZeta (σ₀ + (t : ℂ) * I)) /
    riemannZeta (σ₀ + (t : ℂ) * I) *
    (X : ℂ) ^ (σ₀ + (t : ℂ) * I)) t‖ ≤ c := by
    intro t
    simp only [Complex.norm_mul, c]
    gcongr
    · convert! hC t using 1
      simp
    · rw [Complex.norm_cpow_eq_rpow_re_of_nonneg]
      · simp
      · linarith
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          add_zero, ne_eq]
        linarith
  convert (SmoothedChebyshevDirichlet_aux_integrable ContDiffSmoothingF SmoothingFnonneg
    suppSmoothingF mass_one ε_pos ε_lt_one σ₀_gt σ₀_le_2).bdd_mul
      (c := c) ?_ (ae_of_all _ this) using 2
  · unfold SmoothedChebyshevIntegrand
    ring
  · apply Continuous.aestronglyMeasurable
    rw [← continuousOn_univ]
    intro t _
    let s := σ₀ + (t : ℂ) * I
    have s_ne_one : s ≠ 1 := by
      intro h
      have : σ₀ = 1 := by
        have := congr_arg Complex.re h
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, one_re, s] at this
        exact this
      linarith [σ₀_gt]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · have diffζ := differentiableAt_riemannZeta s_ne_one
      apply ContinuousAt.div
      · apply ContinuousAt.neg
        have : DifferentiableAt ℂ (fun s ↦ deriv riemannZeta s) s :=
          differentiableAt_deriv_riemannZeta s_ne_one
        convert realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) this <;> simp
      · convert realDiff_of_complexDiff (s := σ₀ + (t : ℂ) * I) diffζ <;> simp
      · apply riemannZeta_ne_zero_of_one_lt_re
        simp [σ₀_gt]
    · apply ContinuousAt.comp _ (by fun_prop)
      apply continuousAt_const_cpow
      norm_cast
      linarith
theorem SmoothedChebyshevPull1 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ}
    (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (holoOn : HolomorphicOn (deriv riemannZeta / riemannZeta) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I₁ SmoothingF ε X T -
      I₂ SmoothingF ε T X σ₁ +
      I₃₇ SmoothingF ε T X σ₁ +
      I₈ SmoothingF ε T X σ₁ +
      I₉ SmoothingF ε X T
      + mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X := by
  unfold SmoothedChebyshev
  unfold VerticalIntegral'
  have X_eq_gt_one : 1 < 1 + (Real.log X)⁻¹ := by
    nth_rewrite 1 [← add_zero 1]
    bound
  have X_eq_lt_two : (1 + (Real.log X)⁻¹) < 2 := by
    rw[← one_add_one_eq_two]
    gcongr
    exact inv_lt_one_of_one_lt₀ <| logt_gt_one X_gt.le
  have X_eq_le_two : 1 + (Real.log X)⁻¹ ≤ 2 := X_eq_lt_two.le
  rw [verticalIntegral_split_three (a := -T) (b := T)]
  swap
  · exact SmoothedChebyshevPull1_aux_integrable ε_pos ε_lt_one X_gt X_eq_gt_one
      X_eq_le_two suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF
  · have temp : ↑(1 + (Real.log X)⁻¹) = (1 : ℂ) + ↑(Real.log X)⁻¹ := by simp
    unfold I₁
    simp only [smul_eq_mul, mul_add, temp, sub_eq_add_neg, add_assoc, add_left_cancel_iff]
    unfold I₉
    nth_rewrite 6 [add_comm]
    simp only [← add_assoc]
    rw [add_right_cancel_iff,
        ← add_right_inj (1 / (2 * ↑π * I) *
          -VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) (1 + (Real.log X)⁻¹) (-T) T),
        ← mul_add, ← sub_eq_neg_add, sub_self, mul_zero]
    unfold VIntegral I₂ I₃₇ I₈
    simp only [smul_eq_mul, temp, ← add_assoc, ← mul_neg, ← mul_add]
    let fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦
      SmoothedChebyshevIntegrand SmoothingF ε X ((x : ℝ) + (y : ℝ) * I)
    let fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im
    have : ∫ (y : ℝ) in -T..T,
        SmoothedChebyshevIntegrand SmoothingF ε X (1 + ↑(Real.log X)⁻¹ + ↑y * I) =
        ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by
        unfold fTempRR
        simp only [temp]
    rw[this]
    have : ∫ (σ₀ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ - ↑T * I) =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by
        unfold fTempRR
        simp only [ofReal_neg, neg_mul, sub_eq_add_neg]
    rw[this]
    have : ∫ (t : ℝ) in -T..T,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₁ + ↑t * I) =
        ∫ (y : ℝ) in -T..T, fTempRR σ₁ y := rfl
    rw[this]
    have : ∫ (σ₀ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ + ↑T * I) =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := rfl
    rw[this]
    have : (((I * -∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y) +
        -∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T)) +
        I * ∫ (y : ℝ) in -T..T, fTempRR σ₁ y) +
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T =
        -(2 * ↑π * I) * RectangleIntegral' fTempC (σ₁ - T * I) (1 + ↑(Real.log X)⁻¹ + T * I) := by
        unfold RectangleIntegral' RectangleIntegral HIntegral VIntegral fTempC
        simp only [mul_neg, one_div, mul_inv_rev, inv_I, neg_mul, sub_im, ofReal_im, mul_im,
          ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_sub, ofReal_neg, add_re,
          neg_re, mul_re, sub_self, neg_zero, add_im, neg_im, zero_add, sub_re, sub_zero,
          ofReal_inv, one_re, inv_re, normSq_ofReal, div_self_mul_self', one_im, inv_im,
          zero_div, ofReal_add, ofReal_one, smul_eq_mul, neg_neg]
        ring_nf
        simp only [I_sq, neg_mul, one_mul, ne_eq, ofReal_eq_zero, pi_ne_zero, not_false_eq_true,
          mul_inv_cancel_right₀, sub_neg_eq_add, I_pow_three]
        ring_nf
    rw[this]
    field_simp
    rw[mul_comm, eq_comm, neg_add_eq_zero]
    have pInRectangleInterior :
        (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds 1) := by
      refine rectangle_mem_nhds_iff.mpr ?_
      refine mem_reProdIm.mpr ?_
      simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        sub_zero, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero,
        sub_im, mul_im, zero_sub, add_im, one_im, inv_im, neg_zero, zero_div, zero_add]
      constructor
      · unfold uIoo
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        exact mem_Ioo.mpr ⟨σ₁_lt_one, (by linarith)⟩
      · unfold uIoo
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        exact mem_Ioo.mpr ⟨(by linarith), (by linarith)⟩
    apply ResidueTheoremOnRectangleWithSimplePole'
    · simp; linarith
    · simp; linarith
    · simp only [one_div]
      exact pInRectangleInterior
    · apply DifferentiableOn.mul
      · apply DifferentiableOn.mul
        · simp only [re_add_im]
          have : (fun z ↦ -deriv riemannZeta z / riemannZeta z) = -(deriv riemannZeta / riemannZeta) := by ext; simp; ring
          rw [this]
          apply DifferentiableOn.neg
          apply holoOn.mono
          apply Set.sdiff_subset_sdiff_left
          apply reProdIm_subset_iff'.mpr
          left
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
            div_self_mul_self', add_zero, sub_im, mul_im, zero_sub, add_im, one_im, inv_im,
            neg_zero, zero_div, zero_add]
          constructor <;> apply uIcc_subset_Icc <;> constructor <;> linarith
        · intro s hs
          apply DifferentiableAt.differentiableWithinAt
          simp only [re_add_im]
          apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
            SmoothingFnonneg mass_one
          have := mem_reProdIm.mp hs.1 |>.1
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
            div_self_mul_self', add_zero] at this
          rw [uIcc_of_le (by linarith)] at this
          linarith [this.1]
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        simp only [re_add_im]
        apply DifferentiableAt.const_cpow (by fun_prop)
        left
        norm_cast
        linarith
    · let U : Set ℂ := Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I)
      let f : ℂ → ℂ := fun z ↦ -deriv riemannZeta z / riemannZeta z
      let g : ℂ → ℂ := fun z ↦ mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z
      unfold fTempC fTempRR SmoothedChebyshevIntegrand
      simp only [re_add_im]
      have g_holc : HolomorphicOn g U := by
        intro u uInU
        apply DifferentiableAt.differentiableWithinAt
        simp only [g]
        apply DifferentiableAt.mul
        · apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
            SmoothingFnonneg mass_one
          simp only [ofReal_inv, U] at uInU
          unfold Rectangle at uInU
          rw[Complex.mem_reProdIm] at uInU
          have := uInU.1
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero] at this
          rw [uIcc_of_le (by linarith)] at this
          linarith [this.1]
        · unfold HPow.hPow instHPow
          apply DifferentiableAt.const_cpow differentiableAt_fun_id
          left
          norm_cast
          linarith
      have f_near_p : (f - fun (z : ℂ) => 1 * (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
        simp only [one_mul, f]
        exact riemannZetaLogDerivResidueBigO
      convert ResidueMult g_holc pInRectangleInterior f_near_p using 1
      ext
      simp [f, g]
      ring
lemma interval_membership (r : ℝ) (a b : ℝ) (h1 : r ∈ Set.Icc (min a b) (max a b)) (h2 : a < b) :
    a ≤ r ∧ r ≤ b := by
  have min_eq : min a b = a := min_eq_left (le_of_lt h2)
  have max_eq : max a b = b := max_eq_right (le_of_lt h2)
  rw [min_eq, max_eq] at h1
  rw [← @mem_Icc]
  exact h1
lemma verticalIntegral_split_three_finite {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    VIntegral f σ s e =
    VIntegral f σ s a +
    VIntegral f σ a b +
    VIntegral f σ b e := by
  dsimp [VIntegral]
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at hf
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := a),
    ← intervalIntegral.integral_add_adjacent_intervals (a := a) (b := b)]
  · ring
  all_goals
    apply IntervalIntegrable.mono_set hf
    apply uIcc_subset_uIcc <;> apply mem_uIcc_of_le <;> linarith
lemma verticalIntegral_split_three_finite' {s a b e σ : ℝ} {f : ℂ → ℂ}
    (hf : IntegrableOn (fun t : ℝ ↦ f (σ + t * I)) (Icc s e))
    (hab: s < a ∧ a < b ∧ b < e):
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s e) =
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
    (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) := by
  have : (1 : ℂ) / (2 * π * I) * (VIntegral f σ s a) +
      (1 : ℂ) / (2 * π * I) * (VIntegral f σ a b) +
      (1 : ℂ) / (2 * π * I) * (VIntegral f σ b e) =
        (1 : ℂ) / (2 * π * I) * ((VIntegral f σ s a) +
    (VIntegral f σ a b) +
    (VIntegral f σ b e)) := by ring
  rw [this]
  clear this
  rw [← verticalIntegral_split_three_finite hf hab]
theorem SmoothedChebyshevPull2_aux1 {T σ₁ : ℝ} (σ₁lt : σ₁ < 1)
  (holoOn : HolomorphicOn (deriv riemannZeta / riemannZeta) (Icc σ₁ 2 ×ℂ Icc (-T) T \ {1})) :
  ContinuousOn (fun (t : ℝ) ↦ -deriv riemannZeta (σ₁ + t * I) / riemannZeta (σ₁ + t * I)) (Icc (-T) T) := by
  rw [show (fun (t : ℝ) ↦ -deriv riemannZeta (↑σ₁ + ↑t * I) / riemannZeta (↑σ₁ + ↑t * I)) =
      -(deriv riemannZeta / riemannZeta) ∘ (fun (t : ℝ) ↦ ↑σ₁ + ↑t * I) by ext; simp; ring_nf]
  apply ContinuousOn.neg
  apply holoOn.continuousOn.comp (by fun_prop)
  intro t ht
  simp only [Set.mem_sdiff, mem_singleton_iff]
  constructor
  · apply mem_reProdIm.mpr
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, left_mem_Icc, ht, and_true]
    linarith
  · intro h
    replace h := congr_arg re h
    simp at h
    linarith
theorem SmoothedChebyshevPull2 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (T_pos : 3 < T) {σ₁ σ₂ : ℝ}
    (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1)
    (σ₂_lt_σ₁ : σ₂ < σ₁)
    (holoOn : HolomorphicOn (deriv riemannZeta / riemannZeta) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
    (holoOn2 : HolomorphicOn (SmoothedChebyshevIntegrand SmoothingF ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (diff_SmoothingF : ContDiff ℝ 1 SmoothingF) :
    I₃₇ SmoothingF ε T X σ₁ =
      I₃ SmoothingF ε T X σ₁ -
      I₄ SmoothingF ε X σ₁ σ₂ +
      I₅ SmoothingF ε X σ₂ +
      I₆ SmoothingF ε X σ₁ σ₂ +
      I₇ SmoothingF ε T X σ₁ := by
  let z : ℂ := σ₂ - 3 * I
  let w : ℂ := σ₁ + 3 * I
  have σ₁_pos : 0 < σ₁ := by linarith
  have sub : z.Rectangle w ⊆ Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1} := by
    intro x hx
    obtain ⟨h1, h2⟩ := interval_membership x.re z.re w.re hx.1 (by simpa [z, w] using σ₂_lt_σ₁)
    obtain ⟨h3, h4⟩ := interval_membership x.im z.im w.im hx.2 (by norm_num [z, w])
    simp [z, w] at h1 h2 h3 h4
    exact ⟨⟨⟨h1, by linarith⟩, h3, h4⟩, fun h ↦ by rw [Set.mem_singleton_iff.1 h] at h2; simp at h2; linarith⟩
  have zero_over_box := HolomorphicOn.vanishesOnRectangle holoOn2 sub
  have splitting : I₃₇ SmoothingF ε T X σ₁ =
    I₃ SmoothingF ε T X σ₁ + I₅ SmoothingF ε X σ₁ + I₇ SmoothingF ε T X σ₁ := by
    unfold I₃₇ I₃ I₅ I₇
    apply verticalIntegral_split_three_finite'
    · apply ContinuousOn.integrableOn_Icc
      unfold SmoothedChebyshevIntegrand
      apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · apply SmoothedChebyshevPull2_aux1 σ₁_lt_one holoOn
        · apply continuousOn_of_forall_continuousAt
          intro t t_mem
          have := Smooth1MellinDifferentiable diff_SmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩
            SmoothingFnonneg mass_one (s := ↑σ₁ + ↑t * I) (by simpa)
          simpa using realDiff_of_complexDiff _ this
      · apply continuousOn_of_forall_continuousAt
        intro t t_mem
        apply ContinuousAt.comp
        · refine continuousAt_const_cpow' ?_
          intro h
          have : σ₁ = 0 := by
            have h_real : (↑σ₁ + ↑t * I).re = (0 : ℂ).re := by
              rw [h]
            simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero, zero_re] at h_real
            exact h_real
          linarith
        ·
          apply ContinuousAt.add
          · exact continuousAt_const
          · apply ContinuousAt.mul
            · apply continuous_ofReal.continuousAt
            · exact continuousAt_const
    · refine ⟨by linarith, by linarith, by linarith⟩
  calc I₃₇ SmoothingF ε T X σ₁ =
        I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) * (0 : ℂ) := by simp
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) *
        (RectangleIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z w) := by rw [← zero_over_box]
    _ = I₃₇ SmoothingF ε T X σ₁ - (1 / (2 * π * I)) *
        (HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
        - HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
        + VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
        - VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp [RectangleIntegral]
    _ = I₃₇ SmoothingF ε T X σ₁ -
        ((1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re z.im
        - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
        + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
        - (1 / (2 * π * I)) *
            VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by ring
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - (1 / (2 * π * I)) * HIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re w.re w.im
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, sub_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_sub, ofReal_neg,
        ofReal_ofNat, sub_re, ofReal_re, mul_re, sub_self, sub_zero, add_re, add_im, zero_add,
        sub_neg_eq_add, I₄, sub_right_inj, add_left_inj, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
        I_ne_zero, inv_eq_zero, ofReal_eq_zero, OfNat.ofNat_ne_zero, or_false, false_or, z, w]
      left
      rfl
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, add_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_add, ofReal_ofNat, sub_re,
        ofReal_re, mul_re, sub_self, sub_zero, add_re, sub_neg_eq_add, sub_im, zero_sub, I₆, w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - (1 / (2 * π * I)) * VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, add_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, add_zero, sub_im, ofReal_im,
        mul_im, zero_sub, add_im, zero_add, smul_eq_mul, sub_re, sub_zero, sub_neg_eq_add, I₅,
        w, z]
    _ = I₃₇ SmoothingF ε T X σ₁ - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      simp only [I₅, one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, sub_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, sub_zero, sub_im, ofReal_im,
        mul_im, add_zero, zero_sub, add_im, zero_add, smul_eq_mul, sub_neg_eq_add, z, w]
    _ = I₃ SmoothingF ε T X σ₁
    + I₅ SmoothingF ε X σ₁
    + I₇ SmoothingF ε T X σ₁
    - (I₄ SmoothingF ε X σ₁ σ₂
    - I₆ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₁
    - I₅ SmoothingF ε X σ₂) := by
      rw [splitting]
    _ = I₃ SmoothingF ε T X σ₁
    - I₄ SmoothingF ε X σ₁ σ₂
    + I₅ SmoothingF ε X σ₂
    + I₆ SmoothingF ε X σ₁ σ₂
    + I₇ SmoothingF ε T X σ₁ := by
      ring
theorem poisson_kernel_integrable (x : ℝ) (hx : x ≠ 0) :
  MeasureTheory.Integrable (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) := by
  have h1 : ∀ t : ℝ, ‖x + t * I‖^2 = x^2 + t^2 := by
    intro t
    rw [← normSq_eq_norm_sq, normSq_add_mul_I]
  simp_rw [h1]
  apply integrable_comp_mul_left_iff _ hx |>.mp
  have : (fun t ↦ (x ^ 2 + (x * t) ^ 2) ⁻¹) = (fun t ↦ (1 / x ^ 2) * (1 + t ^ 2) ⁻¹) := by
    ext
    field_simp
  rw [this]
  apply integrable_inv_one_add_sq.const_mul
theorem ae_volume_of_contains_compl_singleton_zero
  (s : Set ℝ)
  (h : (univ : Set ℝ) \ {0} ⊆ s) :
  s ∈ (MeasureTheory.ae volume) :=
  mem_ae_iff.2 (measure_mono_null (fun _ hx ↦ Classical.byContradiction fun h0 ↦ hx (h ⟨trivial, h0⟩))
    volume_singleton)
theorem integral_evaluation (x : ℝ) (T : ℝ) (T_large : 3 < T) :
    ∫ (t : ℝ) in Iic (-T), (‖x + t * I‖ ^ 2)⁻¹ ≤ T⁻¹ := by
  have h2 : ∫ t in Iic (-T), (t ^ 2)⁻¹ = T⁻¹ := by
    rw [← integral_comp_neg_Ioi]
    conv => lhs; arg 2; ext x; rw [show ((-x) ^ 2)⁻¹ = x ^ (-2 : ℝ) by simp [zpow_ofNat]]
    rw [integral_Ioi_rpow_of_lt (by norm_num) (by linarith)]
    ring_nf
    rw [rpow_neg_one]
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity)
    (Integrable.of_integral_ne_zero (by rw [h2]; positivity))
    (ae_restrict_of_forall_mem measurableSet_Iic fun t ht ↦ ?_)).trans h2.le
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  exact inv_anti₀ (by nlinarith [mem_Iic.1 ht]) (le_add_of_nonneg_left (sq_nonneg x))
lemma IBound_aux1 (X₀ : ℝ) (X₀pos : X₀ > 0) {k : ℝ} (k_pos : 0 < k) : ∃ C ≥ 1, ∀ X ≥ X₀, Real.log X ^ k ≤ C * X := by
  have ⟨M, hM⟩ := Filter.eventually_atTop.mp (isLittleO_log_rpow_rpow_atTop k zero_lt_one).eventuallyLE
  let f := fun X ↦ Real.log X ^ k / X
  set I := Icc X₀ M with defI
  have : 0 ∉ I := notMem_Icc_of_lt X₀pos
  have f_cont : ContinuousOn f (Icc X₀ M) := by
    unfold f
    refine ContinuousOn.div₀ (ContinuousOn.rpow (continuousOn_log.mono ?_) continuousOn_const (fun _ _ ↦ Or.inr k_pos)) (continuousOn_id' _) (fun x hx h ↦ ?_)
    · simp only [subset_compl_singleton_iff, ← defI, this, not_false_eq_true]
    · rw [← defI, h] at hx
      exact this hx
  have ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn f_cont
  use max C₁ 1, le_max_right C₁ 1
  intro X hX
  have Xpos : X > 0 := lt_of_lt_of_le X₀pos hX
  by_cases hXM : X ≤ M
  · rw[← div_le_iff₀ Xpos]
    calc
      f X ≤ ‖f X‖ := le_norm_self _
      _ ≤ C₁ := hC₁ X ⟨hX, hXM⟩
      _ ≤ max C₁ 1 := le_max_left C₁ 1
  · calc
      Real.log X ^ k ≤ ‖Real.log X ^ k‖ := le_norm_self _
      _ ≤ ‖X ^ 1‖ := by exact_mod_cast hM X (by linarith[hXM])
      _ = 1 * X := by
        rw[pow_one, one_mul]
        apply norm_of_nonneg
        exact Xpos.le
      _ ≤ max C₁ 1 * X := by
        rw[mul_le_mul_iff_left₀ Xpos]
        exact le_max_right C₁ 1
def I1BoundGenProp (SmoothingF : ℝ → ℝ) : Prop := ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T)
theorem I1Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    I1BoundGenProp SmoothingF := by
  obtain ⟨M, Mpos, hM⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  obtain ⟨K, K0, hK⟩ := triv_bound_zeta
  refine ⟨(K + 1) * M * rexp 1, by positivity, fun ε hε hε1 X hX T hT ↦ ?_⟩
  have hX0 : 0 < X := by linarith
  have hl : 1 < Real.log X := logt_gt_one hX.le
  have hl0 : 0 < Real.log X := by linarith
  set σ : ℝ := 1 + (Real.log X)⁻¹ with hσ
  have hσ1 : 1 < σ := by linarith [inv_pos.2 hl0]
  have hσ2 : σ ≤ 2 := by linarith [inv_lt_one_of_one_lt₀ hl]
  have hb : ∀ t : ℝ, ‖SmoothedChebyshevIntegrand SmoothingF ε X (σ + t * I)‖ ≤
      (K + 1) * M * rexp 1 * X * Real.log X / ε * (‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ := by
    intro t
    have hz := hK σ t hσ1
    rw [show (σ - 1)⁻¹ = Real.log X by simp [hσ]] at hz
    have hm := hM σ (by linarith) (σ + t * I) (by simp) (by simp; linarith) ε hε hε1
    have hx : ‖(X : ℂ) ^ ((σ : ℂ) + t * I)‖ = rexp 1 * X := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0, show ((σ : ℂ) + t * I).re = σ by simp, hσ,
        Real.rpow_one_add' hX0.le (by positivity), Real.rpow_inv_log hX0 (ne_of_gt (by linarith)), mul_comm]
    simp only [SmoothedChebyshevIntegrand, norm_mul, norm_div, norm_neg, hx] at hz ⊢
    calc _ ≤ ((K + 1) * Real.log X) * (M * (ε * ‖(σ : ℂ) + t * I‖ ^ 2)⁻¹) * (rexp 1 * X) := by
          gcongr
          nlinarith [mul_nonneg K0 (by linarith : (0:ℝ) ≤ Real.log X - 1)]
      _ = _ := by ring
  have hint := (SmoothedChebyshevPull1_aux_integrable hε hε1 hX hσ1 hσ2 suppSmoothingF
    SmoothingFnonneg mass_one ContDiffSmoothingF).restrict (s := Iic (-T))
  have hpk := ((poisson_kernel_integrable σ (by linarith : (0:ℝ) < σ).ne').const_mul
    ((K + 1) * M * rexp 1 * X * Real.log X / ε)).restrict (s := Iic (-T))
  have key : ‖∫ t in Iic (-T), SmoothedChebyshevIntegrand SmoothingF ε X (σ + t * I)‖ ≤
      (K + 1) * M * rexp 1 * X * Real.log X / ε * T⁻¹ :=
    (norm_integral_le_integral_norm _).trans <| (integral_mono hint.norm hpk hb).trans <| by
      rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (integral_evaluation σ T hT) (by positivity)
  unfold I₁
  rw [show (1 + ((Real.log X)⁻¹ : ℝ) : ℂ) = (σ : ℂ) by simp [hσ], norm_mul, norm_mul, norm_I, one_mul]
  calc _ ≤ 1 * ((K + 1) * M * rexp 1 * X * Real.log X / ε * T⁻¹) := by
        gcongr
        simp only [one_div, norm_inv, norm_mul, Complex.norm_ofNat, norm_real, norm_eq_abs,
          abs_of_pos pi_pos, norm_I, mul_one]
        exact inv_le_one_of_one_le₀ (by nlinarith [pi_gt_three])
    _ = _ := by ring
lemma I9I1 {SmoothingF : ℝ → ℝ} {ε X T : ℝ} (Xpos : 0 < X) :
    I₉ SmoothingF ε X T = conj (I₁ SmoothingF ε X T) := by
  unfold I₉ I₁
  simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
  rw [neg_mul, mul_neg, ← neg_mul]
  congr
  · ring
  · rw [← integral_conj, ← integral_comp_neg_Ioi, integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun <| measurableSet_Ioi
    intro t ht
    simp only
    rw[← smoothedChebyshevIntegrand_conj Xpos]
    simp
def I9BoundGenProp (SmoothingF : ℝ → ℝ) : Prop := ∃ C > 0, ∀{ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₉ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T)
theorem I9Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    I9BoundGenProp SmoothingF := by
  obtain ⟨C, Cpos, bound⟩ := I1Bound suppSmoothingF ContDiffSmoothingF SmoothingFnonneg mass_one
  refine ⟨C, Cpos, ?_⟩
  intro ε εpos ε_lt_one X X_gt T T_gt
  specialize bound ε εpos ε_lt_one X X_gt T_gt
  rwa [I9I1 (by linarith), norm_conj]
lemma one_add_inv_log {X : ℝ} (X_ge : 3 ≤ X) : (1 + (Real.log X)⁻¹) < 2 := by
  rw[← one_add_one_eq_two]
  refine (add_lt_add_iff_left 1).mpr ?_
  refine inv_lt_one_of_one_lt₀ (logt_gt_one X_ge)
def I2BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε)
    (_ : ε < 1) {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₂ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T)
lemma I2GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound n₁ n₂ A C₂) (C₂pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    I2BoundGenProp n₁ SmoothingF A := by
  obtain ⟨C₁, C₁pos, Mbd⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  obtain ⟨C₃, C₃_gt, hC₃⟩ := IBound_aux1 3 (by norm_num) n₂_pos
  refine ⟨C₁ * C₂ * C₃ * rexp 1, by positivity, fun X hX ε hε hε1 T hT ↦ ?_⟩
  dsimp only
  have hX0 : 0 < X := by linarith
  have hT0 : 0 < T := by linarith
  have hl : 1 < Real.log X := logt_gt_one hX.le
  have hL : 1 < Real.log T ^ n₁ := Real.one_lt_rpow (logt_gt_one hT.le) n₁_pos
  have ha : A / Real.log T ^ n₁ < 1 / 2 := (div_lt_iff₀ (by linarith)).2 (by nlinarith [A_in.2])
  have ha0 : 0 < A / Real.log T ^ n₁ := div_pos A_in.1 (by linarith)
  have hi : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hi0 : 0 < (Real.log X)⁻¹ := inv_pos.2 (by linarith)
  have hb : ∀ σ ∈ uIoc (1 - A / Real.log T ^ n₁) (1 + (Real.log X)⁻¹),
      ‖SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)‖ ≤
      C₁ * C₂ * C₃ * rexp 1 * X / (ε * T) := by
    intro σ hσ
    rw [uIoc_of_le (by linarith)] at hσ
    have hz := has_bound σ (-T) (by rw [abs_neg, abs_of_pos hT0]; exact hT)
      (by rw [mem_Ici, abs_neg, abs_of_pos hT0]; linarith [hσ.1])
    rw [abs_neg, abs_of_pos hT0, show (σ : ℂ) + ((-T : ℝ) : ℂ) * I = σ - T * I by push_cast; ring] at hz
    replace hz := hz.trans (mul_le_mul_of_nonneg_left (hC₃ T hT.le) C₂pos.le)
    have hm := Mbd (1 - A / Real.log T ^ n₁) (by linarith) (σ - T * I) (by simp; linarith [hσ.1])
      (by simp; linarith [hσ.2]) ε hε hε1
    have hs : T ^ 2 ≤ ‖(σ : ℂ) - T * I‖ ^ 2 := by
      rw [Complex.sq_norm, show (σ : ℂ) - T * I = σ + (-T : ℝ) * I by push_cast; ring,
        Complex.normSq_add_mul_I]; nlinarith
    have hx : ‖(X : ℂ) ^ ((σ : ℂ) - T * I)‖ ≤ rexp 1 * X := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      calc _ ≤ X ^ (1 + (Real.log X)⁻¹) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by simp; linarith [hσ.2])
        _ = _ := by rw [Real.rpow_one_add' hX0.le (by positivity),
            Real.rpow_inv_log hX0 (ne_of_gt (by linarith)), mul_comm]
    simp only [SmoothedChebyshevIntegrand, norm_mul, norm_div, norm_neg] at hz ⊢
    calc _ ≤ C₂ * (C₃ * T) * (C₁ * (ε * T ^ 2)⁻¹) * (rexp 1 * X) := by
          gcongr
          exact hm.trans (by gcongr)
      _ = _ := by field_simp
  have h6 : ‖1 / (2 * π * I)‖ * |1 + (Real.log X)⁻¹ - (1 - A / Real.log T ^ n₁)| ≤ 1 := by
    simp only [one_div, norm_inv, norm_mul, Complex.norm_ofNat, norm_real, norm_eq_abs,
      abs_of_pos pi_pos, norm_I, mul_one]
    rw [abs_of_pos (by linarith), inv_mul_le_iff₀ (by positivity)]
    linarith [pi_gt_three]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hb
  unfold I₂
  rw [norm_mul]
  calc _ ≤ ‖1 / (2 * π * I)‖ * (C₁ * C₂ * C₃ * rexp 1 * X / (ε * T) *
          |1 + (Real.log X)⁻¹ - (1 - A / Real.log T ^ n₁)|) := by gcongr
    _ = ‖1 / (2 * π * I)‖ * |1 + (Real.log X)⁻¹ - (1 - A / Real.log T ^ n₁)| *
          (C₁ * C₂ * C₃ * rexp 1 * X / (ε * T)) := by ring
    _ ≤ _ := mul_le_of_le_one_left (by positivity) h6
lemma I8I2 {SmoothingF : ℝ → ℝ}
    {X ε T σ₁ : ℝ} (T_gt : 3 < T) :
    I₈ SmoothingF ε X T σ₁ = -conj (I₂ SmoothingF ε X T σ₁) := by
  unfold I₂ I₈
  rw[map_mul, ← neg_mul]
  congr
  · simp[conj_ofNat]
  · rw[← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only []
    rw[← smoothedChebyshevIntegrand_conj]
    · simp only [map_sub, conj_ofReal, map_mul, conj_I, mul_neg, sub_neg_eq_add]
    · exact lt_trans (by norm_num) T_gt
def I8BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀(X : ℝ) (_ : 3 < X) {ε : ℝ} (_: 0 < ε)
    (_ : ε < 1)
    {T : ℝ} (_ : 3 < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₈ SmoothingF ε T X σ₁‖ ≤ C * X / (ε * T)
lemma I8GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A C₂ : ℝ} (has_bound : LogDerivZetaHasBound n₁ n₂ A C₂) (C₂_pos : 0 < C₂) (A_in : A ∈ Ioc 0 (1 / 2)) :
    I8BoundGenProp n₁ SmoothingF A := by
  obtain ⟨C, hC, i2Bound⟩ := I2GenBound suppSmoothingF ContDiffSmoothingF n₁_pos n₂_pos has_bound C₂_pos A_in
  use C, hC
  intro X hX ε hε0 hε1 T hT σ₁
  let i2Bound := i2Bound X hX hε0 hε1 hT
  rw[I8I2 hX, norm_neg, norm_conj]
  exact i2Bound
lemma Real.log_le_const_mul_rpow {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    Real.log x ≤ c * x ^ (1 / c) := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (1 / c)); rw [Real.log_rpow hx] at h
  have h' := mul_le_mul_of_nonneg_left h hc.le; field_simp at h'
  nlinarith [Real.rpow_pos_of_pos hx (1 / c)]
lemma log_pow_over_xsq_integral_bounded :
  ∀ n : ℝ, (n_pos : 0 < n) →
    ∃ C : ℝ, 0 < C ∧ ∀ T > 3, ∫ x in Ioo 3 T, (Real.log x) ^ n / x ^ 2 < C := by
  intro n n_pos
  set c : ℝ := 2 * n with cDef
  have cpos : 0 < c := by linarith
  set g : ℝ → ℝ := fun x => c ^ n * x ^ (-(3 / 2) : ℝ) with gDef
  have g_nonneg : ∀ x ∈ Ioi (3 : ℝ), 0 ≤ g x := by
    intro x hx; simp only [mem_Ioi] at hx
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  have gInt_nonneg : 0 ≤ ∫ x in Ioi (3 : ℝ), g x := setIntegral_nonneg measurableSet_Ioi g_nonneg
  have g_integrable : IntegrableOn g (Ioi 3) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)) _
  have g_mono : ∀ x ∈ Ioi (3 : ℝ), Real.log x ^ n / x ^ 2 ≤ g x := by
    intro x hx; simp only [mem_Ioi] at hx
    have xpos : 0 < x := by linarith
    have logxPos : 0 < Real.log x := by
      rw [Real.log_pos_iff xpos.le]
      linarith
    have logBnd := Real.rpow_le_rpow logxPos.le (Real.log_le_const_mul_rpow cpos xpos) n_pos.le
    rw [Real.mul_rpow cpos.le (Real.rpow_nonneg xpos.le _), ← Real.rpow_mul xpos.le, cDef] at logBnd
    field_simp at logBnd
    have : - ((3 : ℝ) / 2) = (1 / 2) - 2 := by norm_num
    simp only [cDef, gDef, this, Real.rpow_sub xpos, ← mul_div_assoc, rpow_ofNat]
    exact (div_le_div_iff_of_pos_right (sq_pos_iff.mpr (ne_of_gt xpos))).mpr logBnd
  refine ⟨1 + (∫ x in Ioi (3 : ℝ), g x), by linarith, fun T _ => ?_⟩
  calc
    _ ≤ ∫ (x : ℝ) in Ioo 3 T, g x := by
      refine setIntegral_mono_on (IntegrableOn.mono_set (ContinuousOn.integrableOn_Icc
        (ContinuousOn.div (ContinuousOn.rpow_const (ContinuousOn.log (continuousOn_id' _)
        (fun x hx ↦ ?_)) ?_) (ContinuousOn.fun_pow (continuousOn_id' _) _)
        (fun x hx ↦ pow_ne_zero _ ?_))) Ioo_subset_Icc_self)
        (IntegrableOn.mono_set g_integrable Ioo_subset_Ioi_self) measurableSet_Ioo
        (fun x hx ↦ g_mono x hx.1)
      · linarith [hx.1]
      · simp only [mem_Icc, ne_eq, log_eq_zero, not_or, n_pos.le, or_true, implies_true]
      · linarith [hx.1]
    _ ≤ ∫ (x : ℝ) in Ioi 3, g x := by
      refine setIntegral_mono_set g_integrable ?_ (LE.le.eventuallyLE Ioo_subset_Ioi_self)
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx ↦ g_nonneg x hx)
  linarith
def I3BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X)
      {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
      {T : ℝ} (_ : 3 < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
      ‖I₃ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε
theorem I3GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound n₁ n₂ A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    I3BoundGenProp n₁ SmoothingF A := by
  obtain ⟨CM, CMpos, CMhyp⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  obtain ⟨Cint, Cintpos, Cinthyp⟩ := log_pow_over_xsq_integral_bounded n₂ n₂_pos
  refine ⟨Cint * CM * Cζ, by positivity, fun X hX ε hε hε1 T hT ↦ ?_⟩
  dsimp only
  have hX0 : 0 < X := by linarith
  have hL : 1 < Real.log T ^ n₁ := Real.one_lt_rpow (logt_gt_one hT.le) n₁_pos
  have ha : A / Real.log T ^ n₁ < 1 / 2 := (div_lt_iff₀ (by linarith)).2 (by nlinarith [hA.2])
  have ha0 : 0 < A / Real.log T ^ n₁ := div_pos hA.1 (by linarith)
  have hne : ∀ x ∈ uIcc (-T) (-3), x ≠ 0 := fun x hx ↦ by
    rw [uIcc_of_le (by linarith)] at hx; exact (by linarith [hx.2] : x < 0).ne
  have cont : ContinuousOn (fun t : ℝ ↦ Real.log |t| ^ n₂ / t ^ 2) (uIcc (-T) (-3)) :=
    ((continuous_abs.continuousOn.log fun x hx ↦ abs_ne_zero.2 (hne x hx)).rpow_const
      fun _ _ ↦ Or.inr n₂_pos.le).div (continuousOn_pow 2) fun x hx ↦ pow_ne_zero 2 (hne x hx)
  have hint : ∫ t in (-T)..(-3), Real.log |t| ^ n₂ / t ^ 2 ≤ Cint := by
    rw [← intervalIntegral.integral_comp_neg]
    simp only [abs_neg, log_abs, even_two, Even.neg_pow]
    rw [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo]
    exact (Cinthyp T hT).le
  have hb : ∀ᵐ t, t ∈ Ioc (-T) (-3) → ‖SmoothedChebyshevIntegrand SmoothingF ε X
      ((1 - A / Real.log T ^ n₁ : ℝ) + t * I)‖ ≤
      Cζ * CM * X ^ (1 - A / Real.log T ^ n₁) / ε * (Real.log |t| ^ n₂ / t ^ 2) := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (-3 : ℝ))] with t h3 ht
    have ht0 : t < 0 := by linarith [ht.2]
    have h3t : 3 < |t| := by rw [abs_of_neg ht0]; linarith [lt_of_le_of_ne ht.2 h3]
    have hlt : 0 < Real.log |t| := by linarith [logt_gt_one h3t.le]
    have hz := hCζ (1 - A / Real.log T ^ n₁) t h3t (sub_le_sub_left (div_le_div_of_nonneg_left hA.1.le
      (Real.rpow_pos_of_pos hlt _) (Real.rpow_le_rpow hlt.le (Real.log_le_log (by linarith)
      (by rw [abs_of_neg ht0]; linarith [ht.1])) n₁_pos.le)) 1)
    have hm := CMhyp (1 - A / Real.log T ^ n₁) (by linarith) ((1 - A / Real.log T ^ n₁ : ℝ) + t * I)
      (by simp) (by simp; linarith) ε hε hε1
    have hs : t ^ 2 ≤ ‖((1 - A / Real.log T ^ n₁ : ℝ) : ℂ) + t * I‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]; nlinarith
    have hx : ‖(X : ℂ) ^ (((1 - A / Real.log T ^ n₁ : ℝ) : ℂ) + t * I)‖ =
        X ^ (1 - A / Real.log T ^ n₁) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0]; simp
    have ht2 : t ≠ 0 := ht0.ne
    simp only [SmoothedChebyshevIntegrand, norm_mul, norm_div, norm_neg, hx] at hz ⊢
    calc _ ≤ Cζ * Real.log |t| ^ n₂ * (CM * (ε * t ^ 2)⁻¹) * X ^ (1 - A / Real.log T ^ n₁) := by
          gcongr
          exact hm.trans (by gcongr)
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le (by linarith) hb
    (cont.intervalIntegrable.const_mul (Cζ * CM * X ^ (1 - A / Real.log T ^ n₁) / ε))
  rw [intervalIntegral.integral_const_mul] at hi
  unfold I₃
  rw [norm_mul, norm_mul, norm_I, one_mul]
  calc _ ≤ 1 * (Cζ * CM * X ^ (1 - A / Real.log T ^ n₁) / ε * Cint) := by
        gcongr
        · simp only [one_div, norm_inv, norm_mul, Complex.norm_ofNat, norm_real, norm_eq_abs,
            abs_of_pos pi_pos, norm_I, mul_one]
          exact inv_le_one_of_one_le₀ (by nlinarith [pi_gt_three])
        · exact hi.trans (mul_le_mul_of_nonneg_left hint (by positivity))
    _ = _ := by
        rw [show (1 : ℝ) - A / Real.log T ^ n₁ = 1 + -A / Real.log T ^ n₁ by ring, Real.rpow_add hX0,
          Real.rpow_one]
        ring
lemma I7I3 {SmoothingF : ℝ → ℝ} {ε X T σ₁ : ℝ} (Xpos : 0 < X) :
    I₇ SmoothingF ε T X σ₁ = conj (I₃ SmoothingF ε T X σ₁) := by
  unfold I₃ I₇
  simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
  rw [neg_mul, mul_neg, ← neg_mul]
  congr
  · ring
  · rw [← intervalIntegral_conj, ← intervalIntegral.integral_comp_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [← smoothedChebyshevIntegrand_conj Xpos]
    simp
def I7BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X)
      {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
      {T : ℝ} (_ : 3 < T),
      let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
      ‖I₇ SmoothingF ε T X σ₁‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε
theorem I7GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {n₁ n₂ : ℝ} (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) {A Cζ : ℝ} (hCζ : LogDerivZetaHasBound n₁ n₂ A Cζ) (Cζpos : 0 < Cζ) (hA : A ∈ Ioc 0 (1 / 2)) :
    I7BoundGenProp n₁ SmoothingF A := by
  obtain ⟨C, Cpos, bound⟩ := I3GenBound suppSmoothingF ContDiffSmoothingF n₁_pos n₂_pos hCζ Cζpos hA
  refine ⟨C, Cpos, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I7I3 (by linarith), norm_conj]
def I4BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A σ₂ : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε
lemma I4GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {n : ℝ} (n_pos : n > 0) {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) :
    I4BoundGenProp n SmoothingF A σ₂ := by
  obtain ⟨σ₂0, σ₂1⟩ := hσ₂
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc σ₂ 1)
    (f := fun σ : ℝ ↦ deriv riemannZeta (σ - 3 * I) / riemannZeta (σ - 3 * I)) <|
    h_logDeriv_holo.continuousOn.comp (by fun_prop) fun σ hσ ↦ ⟨⟨by
      simpa [uIcc_of_le (σ₂1.le.trans one_le_two)] using ⟨hσ.1, by linarith [hσ.2]⟩, by simp⟩,
      fun h ↦ by simpa using congr_arg im h⟩
  obtain ⟨D, Dpos, hD⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  refine ⟨|K| * D, by positivity, max 4 (rexp ((A / (1 - σ₂)) ^ n⁻¹)), by norm_num, ?_⟩
  intro X hX ε hε hε1 T hT
  dsimp only
  have hX0 : 0 < X := by linarith
  have hT0 : 0 < T := by linarith [(le_max_left _ _).trans_lt hT]
  have hL : 0 < Real.log T ^ n := Real.rpow_pos_of_pos (Real.log_pos (by linarith [(le_max_left _ _).trans_lt hT])) n
  have h0 : 0 ≤ A / (1 - σ₂) := div_nonneg hA.1.le (by linarith)
  have h1 : (A / (1 - σ₂)) ^ n⁻¹ < Real.log T :=
    (Real.lt_log_iff_exp_lt hT0).2 ((le_max_right _ _).trans_lt hT)
  have h2 := Real.rpow_lt_rpow (Real.rpow_nonneg h0 _) h1 n_pos
  rw [Real.rpow_inv_rpow h0 n_pos.ne', div_lt_iff₀ (by linarith)] at h2
  have ha0 : 0 < A / Real.log T ^ n := div_pos hA.1 hL
  have ha1 : A / Real.log T ^ n ≤ 1 - σ₂ := (div_le_iff₀ hL).2 (by linarith)
  rw [neg_div]
  generalize A / Real.log T ^ n = a at ha0 ha1 ⊢
  have hb : ∀ σ ∈ uIoc σ₂ (1 - a), ‖SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)‖ ≤
      |K| * D * X * X ^ (-a) / ε := by
    intro σ hσ
    rw [uIoc_of_le (by linarith)] at hσ
    have hs : 1 ≤ ‖(σ : ℂ) - 3 * I‖ ^ 2 := by
      have := Complex.abs_im_le_norm ((σ : ℂ) - 3 * I)
      simp only [sub_im, ofReal_im, mul_im, re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero,
        add_zero, zero_sub, abs_neg] at this
      nlinarith [abs_of_pos (by norm_num : (0:ℝ) < 3)]
    have hm := hD σ₂ σ₂0 (σ - 3 * I) (by simp; linarith [hσ.1]) (by simp; linarith [hσ.2]) ε hε hε1
    have hx : ‖(X : ℂ) ^ ((σ : ℂ) - 3 * I)‖ ≤ X * X ^ (-a) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0, ← Real.rpow_one_add' hX0.le (ne_of_gt (by linarith))]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by simp; linarith [hσ.2])
    have hk := (hK σ ⟨hσ.1.le, by linarith [hσ.2]⟩).trans (le_abs_self K)
    simp only [SmoothedChebyshevIntegrand, norm_mul, norm_div, norm_neg] at hk ⊢
    calc _ ≤ |K| * (D * (ε * 1)⁻¹) * (X * X ^ (-a)) := by
          gcongr
          exact hm.trans (by gcongr)
      _ = _ := by field_simp
  unfold I₄
  rw [norm_mul]
  calc _ ≤ 1 * (|K| * D * X * X ^ (-a) / ε * |1 - a - σ₂|) := by
        gcongr
        · simp only [one_div, norm_inv, norm_mul, Complex.norm_ofNat, norm_real, norm_eq_abs,
            abs_of_pos pi_pos, norm_I, mul_one]
          exact inv_le_one_of_one_le₀ (by nlinarith [pi_gt_three])
        · exact intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ ≤ _ := by
        rw [one_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - a - σ₂)]
        exact mul_le_of_le_one_right (by positivity) (by linarith)
lemma I6I4 {SmoothingF : ℝ → ℝ} {ε X σ₁ σ₂ : ℝ} (Xpos : 0 < X) :
    I₆ SmoothingF ε X σ₁ σ₂ = -conj (I₄ SmoothingF ε X σ₁ σ₂) := by
  unfold I₆ I₄
  simp only [map_mul, map_div₀, conj_ofReal, conj_I, map_one, conj_ofNat]
  rw [← neg_mul]
  congr
  · ring
  · rw [← intervalIntegral_conj]
    apply intervalIntegral.integral_congr
    intro σ hσ
    simp only
    rw[← smoothedChebyshevIntegrand_conj Xpos]
    simp [conj_ofNat]
def I6BoundGenProp (n : ℝ) (SmoothingF : ℝ → ℝ) (A σ₂ : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ n
    ‖I₆ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ n)) / ε
lemma I6GenBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {n : ℝ} (n_pos : 0 < n) {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) :
    I6BoundGenProp n SmoothingF A σ₂ := by
  obtain ⟨C, Cpos, Tlb, Tlb_gt, bound⟩ := I4GenBound suppSmoothingF ContDiffSmoothingF h_logDeriv_holo hσ₂ n_pos hA
  refine ⟨C, Cpos, Tlb, Tlb_gt, fun X X_gt ε εpos ε_lt_one T T_gt ↦ ?_⟩
  specialize bound X X_gt εpos ε_lt_one T_gt
  intro σ₁
  rwa [I6I4 (by linarith), norm_neg, norm_conj]
def I5BoundGenProp (SmoothingF : ℝ → ℝ) (σ₂ : ℝ) : Prop := ∃ (C : ℝ) (_ : 0 < C),
    ∀ (X : ℝ) (_ : 3 < X) {ε : ℝ} (_ : 0 < ε) (_ : ε < 1),
    ‖I₅ SmoothingF ε X σ₂‖ ≤ C * X ^ σ₂ / ε
lemma I5Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1) :
    I5BoundGenProp SmoothingF σ₂ := by
  obtain ⟨σ₂0, σ₂1⟩ := hσ₂
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-3 : ℝ) 3)
    (f := fun t : ℝ ↦ deriv riemannZeta (σ₂ + t * I) / riemannZeta (σ₂ + t * I)) <|
    h_logDeriv_holo.continuousOn.comp (by fun_prop) fun t ht ↦ ⟨⟨by simp, by
      rw [uIcc_of_le (by norm_num)]; simpa using ht⟩, fun h ↦ by simp [Complex.ext_iff] at h; linarith [h.1]⟩
  obtain ⟨D, Dpos, hD⟩ := MellinOfSmooth1b ContDiffSmoothingF suppSmoothingF
  refine ⟨(|K| + 1) * D / σ₂ ^ 2, by positivity, fun X hX ε hε hε1 ↦ ?_⟩
  have hX0 : 0 < X := by linarith
  have hb : ∀ t ∈ uIoc (-3 : ℝ) 3, ‖SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)‖ ≤
      (|K| + 1) * D / σ₂ ^ 2 * X ^ σ₂ / ε := by
    intro t ht
    rw [uIoc_of_le (by norm_num)] at ht
    have hs : σ₂ ^ 2 ≤ ‖(σ₂ : ℂ) + t * I‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]; nlinarith [sq_nonneg t]
    have hm := hD σ₂ σ₂0 (σ₂ + t * I) (by simp) (by simp; linarith) ε hε hε1
    have hx : ‖(X : ℂ) ^ ((σ₂ : ℂ) + t * I)‖ ≤ X ^ σ₂ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0]; simp
    have hk := (hK t ⟨ht.1.le, ht.2⟩).trans ((le_abs_self K).trans (le_add_of_nonneg_right zero_le_one))
    simp only [SmoothedChebyshevIntegrand, norm_mul, norm_div, norm_neg] at hk ⊢
    calc _ ≤ (|K| + 1) * (D * (ε * σ₂ ^ 2)⁻¹) * X ^ σ₂ := by
          gcongr
          exact hm.trans (by gcongr)
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [show |(3 : ℝ) - -3| = 6 by norm_num] at hi
  have h6 : ‖1 / (2 * π * I)‖ * 6 ≤ 1 := by
    simp only [one_div, norm_inv, norm_mul, Complex.norm_ofNat, norm_real, norm_eq_abs,
      abs_of_pos pi_pos, norm_I, mul_one]
    rw [inv_mul_le_iff₀ (by positivity)]; linarith [pi_gt_three]
  unfold I₅
  rw [norm_mul, norm_mul, norm_I, one_mul]
  calc _ ≤ ‖1 / (2 * π * I)‖ * ((|K| + 1) * D / σ₂ ^ 2 * X ^ σ₂ / ε * 6) := by gcongr
    _ = ‖1 / (2 * π * I)‖ * 6 * ((|K| + 1) * D / σ₂ ^ 2 * X ^ σ₂ / ε) := by ring
    _ ≤ _ := mul_le_of_le_one_left (by positivity) h6
def LogDerivZetaBoundedAndHoloGenProp (n₁ n₂ : ℝ) : Prop := ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound n₁ n₂ A C
    ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ deriv riemannZeta s / (riemannZeta s))
    (( (Icc ((1 : ℝ) - A / Real.log T ^ n₁) 2)  ×ℂ (Icc (-T) T) ) \ {1})
lemma LogDerivZetaBoundedAndHoloGen {n₁ n₂ : ℝ}
  (LogDerivZetaBndUnif : LogDerivZetaBndUnifGenProp n₁ n₂)
  (LogDerivZetaHolcLargeT : LogDerivZetaHolcLargeTGenProp n₁) :
  LogDerivZetaBoundedAndHoloGenProp n₁ n₂ := by
  obtain ⟨A₁, A₁_in, C, C_pos, zeta_bnd⟩ := LogDerivZetaBndUnif
  obtain ⟨A₂, A₂_in, holo⟩ := LogDerivZetaHolcLargeT
  refine ⟨min A₁ A₂, C, C_pos, ?_, ?_, ?_⟩
  · exact ⟨lt_min A₁_in.1 A₂_in.1, le_trans (min_le_left _ _) A₁_in.2⟩
  · intro σ T hT hσ
    apply zeta_bnd _ _ hT
    apply mem_Ici.mpr (le_trans _ hσ)
    gcongr
    · bound
    · apply min_le_left
  · intro T hT
    apply (holo _ hT).mono
    intro s hs
    simp only [Set.mem_sdiff, mem_singleton_iff, mem_reProdIm] at hs ⊢
    refine ⟨?_, hs.2⟩
    refine ⟨?_, hs.1.2⟩
    refine ⟨?_, hs.1.1.2⟩
    apply le_trans _ hs.1.1.1
    gcongr
    · bound
    · apply min_le_right
lemma LogDerivZetaBoundedAndHolo99 : LogDerivZetaBoundedAndHoloGenProp 9 9 := by
  exact LogDerivZetaBoundedAndHoloGen LogDerivZetaBndUnif99 LogDerivZetaHolcLargeT9
lemma MellinOfSmooth1cExplicit {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ ε₀ c : ℝ, 0 < ε₀ ∧ 0 < c ∧
    ∀ ε ∈ Ioo 0 ε₀, ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1‖ ≤ c * ε := by
  have := MellinOfSmooth1c diffν suppν mass_one
  rw [Asymptotics.isBigO_iff'] at this
  rcases this with ⟨c, cpos, hc⟩
  unfold Filter.Eventually at hc
  rw [mem_nhdsGT_iff_exists_Ioo_subset] at hc
  rcases hc with ⟨ε₀, ε₀pos, h⟩
  refine ⟨ε₀, c, ε₀pos, cpos, fun ε hε ↦ ?_⟩
  specialize h hε
  rw [mem_ofPred_eq, id_eq, norm_of_nonneg hε.1.le] at h
  exact h
open Filter Topology
lemma x_ε_to_inf (c : ℝ) {B : ℝ} (B_le : B < 1) : Tendsto
    (fun x ↦ x * Real.exp (-c * (Real.log x) ^ B)) atTop atTop := by
  have coeff_to_zero {B : ℝ} (B_le : B < 1) :
      Tendsto (fun x ↦ Real.log x ^ (B - 1)) atTop (𝓝 0) := by
    have B_minus_1_neg : B - 1 < 0 := by linarith
    rw [← Real.zero_rpow (ne_of_lt B_minus_1_neg),
      zero_rpow (ne_of_lt B_minus_1_neg)]
    have one_minus_B_pos : 0 < 1 - B := by linarith
    rw [show B - 1 = -(1 - B) by ring]
    have : ∀ᶠ (x : ℝ) in atTop, Real.log x ^ (-(1 - B)) = (Real.log x ^ ((1 - B)))⁻¹ := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      apply Real.rpow_neg
      exact Real.log_nonneg hx
    rw [tendsto_congr' this]
    apply tendsto_inv_atTop_zero.comp
    apply (tendsto_rpow_atTop one_minus_B_pos).comp
    exact tendsto_log_atTop
  have log_sub_log_pow_inf (c : ℝ) {B : ℝ} (B_le : B < 1) :
      Tendsto (fun (x : ℝ) ↦ Real.log x - c * Real.log x ^ B) atTop atTop := by
    have factor_form : ∀ x > 1, Real.log x - c * Real.log x ^ B =
        Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      intro x hx
      ring_nf
      congr! 1
      rw [mul_assoc, mul_comm (Real.log x), mul_assoc]
      congr! 1
      have log_pos : 0 < Real.log x := Real.log_pos hx
      rw [(by simp : Real.log x ^ (-1 + B) * Real.log x =
        Real.log x ^ (-1 + B) * (Real.log x) ^ (1 : ℝ))]
      rw [← Real.rpow_add log_pos]
      ring_nf
    have coeff_to_one : Tendsto (fun x ↦ 1 - c * Real.log x ^ (B - 1)) atTop (𝓝 1) := by
      specialize coeff_to_zero B_le
      apply Tendsto.const_mul c at coeff_to_zero
      convert (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ))).sub coeff_to_zero
      ring
    have eventually_factored : ∀ᶠ x in atTop, Real.log x - c * Real.log x ^ B =
    Real.log x * (1 - c * Real.log x ^ (B - 1)) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact factor_form x hx
    rw [tendsto_congr' eventually_factored]
    apply Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) tendsto_log_atTop  coeff_to_one
  have x_εx_eq (c B : ℝ) : ∀ᶠ (x : ℝ) in atTop, x * rexp (-c * Real.log x ^ B) =
        rexp (Real.log x - c * Real.log x ^ B) := by
    filter_upwards [eventually_gt_atTop 0] with x hx_pos
    conv =>
      enter [1, 1]
      rw [(Real.exp_log hx_pos).symm]
    rw [← Real.exp_add]
    ring_nf
  rw [tendsto_congr' (x_εx_eq c B)]
  exact tendsto_exp_atTop.comp (log_sub_log_pow_inf c B_le)
lemma GenStrengthPNT {n₁ n₂ : ℝ}
  (LogDerivZetaBoundedAndHolo : LogDerivZetaBoundedAndHoloGenProp n₁ n₂)
  (n₁_pos : 0 < n₁) (n₂_pos : 0 < n₂) : ∃ c > 0,
  (ψ - id) =O[atTop]
    fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / (1 + n₁))) := by
  have ⟨ν, ContDiffν, ν_nonneg', ν_supp, ν_massOne'⟩ := SmoothExistence
  have ContDiff1ν : ContDiff ℝ 1 ν := by exact ContDiffν.of_le (by simp)
  have ν_nonneg : ∀ x > 0, 0 ≤ ν x := fun x _ ↦ ν_nonneg' x
  have ν_massOne : ∫ x in Ioi 0, ν x / x = 1 := by rwa [← integral_Ici_eq_integral_Ioi]
  obtain ⟨A, C_bnd, C_bnd_pos, A_in_Ioc, zeta_bnd, holo1⟩ := LogDerivZetaBoundedAndHolo
  obtain ⟨σ₂, σ₂InIoo, holo2⟩ := LogDerivZetaHolcSmallT'
  obtain ⟨c_close, c_close_pos, h_close⟩ := SmoothedChebyshevClose ContDiff1ν ν_supp ν_nonneg ν_massOne
  obtain ⟨ε_main, C_main, ε_main_pos, C_main_pos, h_main⟩  := MellinOfSmooth1cExplicit ContDiff1ν ν_supp ν_massOne
  obtain ⟨c₁, c₁pos, hc₁⟩ := I1Bound ν_supp ContDiff1ν ν_nonneg ν_massOne
  obtain ⟨c₂, c₂pos, hc₂⟩ := I2GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₃, c₃pos, hc₃⟩ := I3GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₅, c₅pos, hc₅⟩ := I5Bound ν_supp ContDiff1ν holo2  σ₂InIoo
  obtain ⟨c₇, c₇pos, hc₇⟩ := I7GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₈, c₈pos, hc₈⟩ := I8GenBound ν_supp ContDiff1ν n₁_pos n₂_pos zeta_bnd C_bnd_pos A_in_Ioc
  obtain ⟨c₉, c₉pos, hc₉⟩ := I9Bound ν_supp ContDiff1ν ν_nonneg ν_massOne
  obtain ⟨c₄, c₄pos, Tlb₄, Tlb₄bnd, hc₄⟩ := I4GenBound ν_supp ContDiff1ν holo2 σ₂InIoo n₁_pos A_in_Ioc
  obtain ⟨c₆, c₆pos, Tlb₆, Tlb₆bnd, hc₆⟩ := I6GenBound ν_supp ContDiff1ν holo2 σ₂InIoo n₁_pos A_in_Ioc
  let C' := c_close + C_main
  let C'' := c₁ + c₂ + c₈ + c₉
  let C''' := c₃ + c₄ + c₆ + c₇
  have hA0 := A_in_Ioc.1
  let c : ℝ := A ^ ((1 : ℝ) / (1 + n₁)) / 4
  have cpos : 0 < c := by simp only [c]; positivity
  refine ⟨c, cpos, ?_⟩
  rw [Asymptotics.isBigO_iff]
  let C : ℝ := C' + C'' + C''' + c₅
  refine ⟨C, ?_⟩
  let c_εx : ℝ := A ^ ((1 : ℝ) / (1 + n₁)) / 2
  have c_εx_pos : 0 < c_εx := by simp only [c_εx]; positivity
  let c_Tx : ℝ := A ^ ((1 : ℝ) / (1 + n₁))
  have c_Tx_pos : 0 < c_Tx := by simp only [c_Tx]; positivity
  let εx := (fun x ↦ Real.exp (-c_εx * (Real.log x) ^ ((1 : ℝ) / (1 + n₁))))
  let Tx := (fun x ↦ Real.exp (c_Tx * (Real.log x) ^ ((1 : ℝ) / (1 + n₁))))
  have one_div_succ_n₁_pos : 0 < (1 : ℝ) / (1 + n₁) := by
    simp only [one_div, inv_pos]
    linarith
  have one_div_succ_n₁_lt_one : (1 : ℝ) / (1 + n₁) < 1 := by
    rw [one_div, inv_lt_one₀ (one_div_pos.mp one_div_succ_n₁_pos)]
    norm_num [n₁_pos]
  have Tx_to_inf : Tendsto Tx atTop atTop := by
    unfold Tx
    apply tendsto_exp_atTop.comp
    apply Tendsto.pos_mul_atTop c_Tx_pos tendsto_const_nhds
    exact (tendsto_rpow_atTop one_div_succ_n₁_pos).comp Real.tendsto_log_atTop
  have ex_to_zero : Tendsto εx atTop (𝓝 0) := by
    unfold εx
    apply Real.tendsto_exp_atBot.comp
    have this (x) : -c_εx * Real.log x ^ ((1 : ℝ) / (1 + n₁)) = -(c_εx * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
      ring
    simp_rw [this]
    rw [tendsto_neg_atBot_iff]
    apply Tendsto.const_mul_atTop c_εx_pos
    exact (tendsto_rpow_atTop one_div_succ_n₁_pos).comp tendsto_log_atTop
  have eventually_εx_lt_one : ∀ᶠ (x : ℝ) in atTop, εx x < 1 := by
    apply (tendsto_order.mp ex_to_zero).2
    norm_num
  have eventually_2_lt : ∀ᶠ (x : ℝ) in atTop, 2 < x * εx x := by
    have := x_ε_to_inf c_εx one_div_succ_n₁_lt_one
    exact this.eventually_gt_atTop 2
  have eventually_T_gt_3 : ∀ᶠ (x : ℝ) in atTop, 3 < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop 3
  have eventually_T_gt_Tlb₄ : ∀ᶠ (x : ℝ) in atTop, Tlb₄ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _
  have eventually_T_gt_Tlb₆ : ∀ᶠ (x : ℝ) in atTop, Tlb₆ < Tx x := by
    exact Tx_to_inf.eventually_gt_atTop _
  have eventually_σ₂_lt_σ₁ : ∀ᶠ (x : ℝ) in atTop, σ₂ < 1 - A / (Real.log (Tx x)) ^ n₁ := by
    apply (tendsto_order.mp ?_).1
    · exact σ₂InIoo.2
    have := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop n₁_pos).comp
      (tendsto_log_atTop.comp Tx_to_inf))
    have := Tendsto.const_mul (b := A) this
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub this using 2
    · simp only [comp_apply, div_eq_mul_inv]
    · simp
  have eventually_ε_lt_ε_main : ∀ᶠ (x : ℝ) in atTop, εx x < ε_main := by
    apply (tendsto_order.mp ex_to_zero).2
    assumption
  have event_logX_ge : ∀ᶠ (x : ℝ) in atTop, 1 ≤ Real.log x := by
    apply Real.tendsto_log_atTop.eventually_ge_atTop
  have event_1_aux_1 {const1 const2 : ℝ} (const1pos : 0 < const1) (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp 0 := by
      have := ((isLittleO_log_rpow_atTop const2pos).bound const1pos)
      have : ∀ᶠ (x : ℝ) in atTop, Real.log (Real.log x) ≤
          const1 * (Real.log x) ^ const2 := by
        have := tendsto_log_atTop.eventually this
        filter_upwards [this, eventually_gt_atTop 10] with x hx x_gt
        convert hx using 1
        · rw [Real.norm_of_nonneg]
          exact Real.log_nonneg (logt_gt_one (by linarith)).le
        · congr! 1
          rw [Real.norm_of_nonneg]
          apply Real.rpow_nonneg
          apply Real.log_nonneg
          linarith
      have loglogx :  ∀ᶠ (x : ℝ) in atTop,
          Real.log x = rexp (Real.log (Real.log x)) := by
        filter_upwards [eventually_gt_atTop 3] with x hx
        rw [Real.exp_log]
        apply Real.log_pos
        linarith
      filter_upwards [loglogx, this] with x loglogx hx
      conv =>
        enter [1, 2]
        rw [loglogx]
      rw [← Real.exp_add]
      apply Real.exp_monotone
      grw [hx]
      simp
  have event_1_aux {const1 const1' const2 : ℝ} (const1bnds : const1' < const1)
    (const2pos : 0 < const2) :
    ∀ᶠ (x : ℝ) in atTop,
    rexp (-const1 * Real.log x ^ const2) * Real.log x ≤
    rexp (-const1' * Real.log x ^ const2) := by
      have : 0 < const1 - const1' := by linarith
      filter_upwards [event_1_aux_1 this const2pos] with x hx
      have : rexp (-const1 * Real.log x ^ const2) * Real.log x
        = rexp (-(const1') * Real.log x ^ const2)
          * rexp (-(const1 - const1') * Real.log x ^ const2) * Real.log x := by
          congr! 1
          rw [← Real.exp_add]
          congr! 1
          ring
      rw [this,
        mul_assoc]
      grw [hx]
      simp
  have event_1 : ∀ᶠ (x : ℝ) in atTop, C' * (εx x) * x * Real.log x ≤
      C' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold c εx c_εx
    have const1bnd : (A ^ ((1 : ℝ) / (1 + n₁)) / 4) < (A ^ ((1 : ℝ) / (1 + n₁)) / 2) := by
        linarith
    have this (x) :
      C' * rexp (-(A ^ ((1 : ℝ) / (1 + n₁)) / 2) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) * x * Real.log x =
      C' * x * (rexp (-(A ^ ((1 : ℝ) / (1 + n₁)) / 2) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) * Real.log x) := by ring
    simp_rw [this]
    filter_upwards [event_1_aux const1bnd one_div_succ_n₁_pos, eventually_gt_atTop 3] with x x_bnd x_gt
    grw [x_bnd]
  have event_2 : ∀ᶠ (x : ℝ) in atTop, C'' * x * Real.log x / (εx x * Tx x) ≤
      C'' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold c εx c_εx Tx c_Tx
    set const2 : ℝ := 1 / (1 + n₁)
    have const2bnd : 0 < const2 := one_div_succ_n₁_pos
    set const1 := (A ^ const2 / 2)
    set const1' := (A ^ const2 / 4)
    have this (x) : -(-const1 * Real.log x ^ const2 + A ^ const2 * Real.log x ^ const2) =
      -(A ^ const2 - const1) * Real.log x ^ const2 := by ring
    simp_rw [← Real.exp_add, div_eq_mul_inv, ← Real.exp_neg, this]
    have const1bnd : const1' < (A ^ const2 - const1) := by
      unfold const1' const1
      linarith
    filter_upwards [event_1_aux const1bnd const2bnd, eventually_gt_atTop 3] with x x_bnd x_gt
    rw [mul_assoc]
    conv =>
      enter [1, 2]
      rw [mul_comm]
    grw [x_bnd]
  have event_3_aux {const1 const1' const2 : ℝ} (const2_eq : const2 = 1 / (1 + n₁))
    (const1_eq : const1 = (A ^ const2 / 2)) (const1'_eq : const1' = (A ^ const2 / 4)) :
    ∀ᶠ (x : ℝ) in atTop,
      x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (n₁ : ℝ)) *
      rexp (-(-const1 * Real.log x ^ const2)) ≤
      rexp (-const1' * Real.log x ^ const2) := by
    have : ∀ᶠ (x : ℝ) in atTop, x = rexp (Real.log x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.exp_log hx]
    filter_upwards [this, eventually_gt_atTop 3] with x hx x_gt_3
    have logxpos : 0 < Real.log x := by apply Real.log_pos; linarith
    conv =>
      enter [1, 1, 1]
      rw [hx]
    rw [← Real.exp_mul, Real.log_exp, Real.mul_rpow]
    · have {y : ℝ} (ypos : 0 < y) : y / (y ^ const2) ^ (n₁ : ℝ) = y ^ const2 := by
        rw [← Real.rpow_mul ypos.le,
          div_eq_mul_inv]
        rw [← Real.rpow_neg ypos.le]
        conv =>
          enter [1, 1]
          rw [← Real.rpow_one y]
        rw [← Real.rpow_add ypos, const2_eq]
        field_simp
        ring_nf
      rw [div_mul_eq_div_div, neg_div, this (A_in_Ioc.1), mul_div]
      conv =>
        enter [1, 1, 1, 1]
        rw [mul_comm]
      rw [← mul_div, this (y := Real.log x) logxpos, ← Real.exp_add]
      apply Real.exp_monotone
      have : -A ^ const2 * Real.log x ^ const2 + -(-const1 * Real.log x ^ const2)
       = (-(A ^ const2 - const1) * Real.log x ^ const2) := by ring
      rw [this]
      gcongr
      rw [const1'_eq, const1_eq]
      have : 0 ≤ A ^ const2 := by
        apply Real.rpow_nonneg A_in_Ioc.1.le
      linarith
    · rw [const2_eq]
      positivity
    · apply Real.rpow_nonneg
      apply Real.log_nonneg
      linarith
  have event_3 : ∀ᶠ (x : ℝ) in atTop, C''' * x * x ^ (-A / Real.log (Tx x) ^ n₁) / (εx x) ≤
      C''' * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold c Tx c_Tx εx c_εx
    set const2 : ℝ := 1 / (1 + n₁) with const2eq
    set const1 := (A ^ const2 / 2) with const1eq
    set const1' := (A ^ const2 / 4) with const1'eq
    conv =>
      enter [1, x, 1]
      rw [div_eq_mul_inv, ← Real.exp_neg]
    filter_upwards [event_3_aux const2eq const1eq const1'eq,
      eventually_gt_atTop 3] with x x_bnd x_gt
    have this (x) : C''' * x * x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ n₁)
        * rexp (-(-const1 * Real.log x ^ const2))
      = C''' * x * (x ^ (-A / Real.log (rexp (A ^ const2 * Real.log x ^ const2)) ^ (n₁ : ℝ))
        * rexp (-(-const1 * Real.log x ^ const2))) := by
      ring
    rw [this]
    grw [x_bnd]
  have event_4_aux4 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      Tendsto (fun x ↦ c' * Real.log x ^ pow2) atTop (𝓝 0) := by
    rw [← mul_zero c']
    apply Tendsto.const_mul
    have := tendsto_rpow_neg_atTop (y := -pow2) (by linarith)
    rw [neg_neg] at this
    apply this.comp
    exact Real.tendsto_log_atTop
  have event_4_aux3 {pow2 : ℝ} (pow2_neg : pow2 < 0) {c : ℝ} (cpos : 0 < c) (c' : ℝ) :
      ∀ᶠ (x : ℝ) in atTop, c' * (Real.log x) ^ pow2 < c := by
    apply (event_4_aux4 pow2_neg cpos c').eventually_lt_const
    exact cpos
  have event_4_aux2 {c1 : ℝ} (c1pos : 0 < c1) (c2 : ℝ) {pow1 : ℝ} (pow1_lt : pow1 < 1) :
      ∀ᶠ (x : ℝ) in atTop, 0 ≤ Real.log x * (c1 - c2 * (Real.log x) ^ (pow1 - 1)) := by
    filter_upwards [eventually_gt_atTop 3 , event_4_aux3 (by linarith : pow1 - 1 < 0)
      (by linarith : 0 < c1 / 2) c2] with x x_gt hx
    have : 0 ≤ Real.log x := by
      apply Real.log_nonneg
      linarith
    apply mul_nonneg this
    linarith
  have event_4_aux1 {const1 : ℝ} (const1_lt : const1 < 1) (const2 const3 : ℝ)
      {pow1 : ℝ} (pow1_lt : pow1 < 1) : ∀ᶠ (x : ℝ) in atTop,
      const1 * Real.log x + const2 * Real.log x ^ pow1
        ≤ Real.log x - const3 * Real.log x ^ pow1 := by
    filter_upwards [event_4_aux2 (by linarith : 0 < 1 - const1) (const2 + const3) pow1_lt,
      eventually_gt_atTop 3] with x hx x_gt
    have :
      Real.log x - const3 * Real.log x ^ pow1 - (const1 * Real.log x + const2 * Real.log x ^ pow1)
      = (1 - const1) * Real.log x - (const2 + const3) * Real.log x ^ pow1 := by ring
    rw [← sub_nonneg, this]
    convert hx using 1
    ring_nf
    congr! 1
    · have : Real.log x * const2 * Real.log x ^ (-1 + pow1)
          = const2 * Real.log x ^ pow1 := by
        rw [mul_assoc, mul_comm, mul_assoc]
        congr! 1
        conv =>
          enter [1, 2]
          rw [← Real.rpow_one (Real.log x)]
        rw [← Real.rpow_add (Real.log_pos (by linarith))]
        ring_nf
      rw [this]
    have : Real.log x * const3 * Real.log x ^ (-1 + pow1)
        = const3 * Real.log x ^ pow1 := by
      rw [mul_assoc, mul_comm, mul_assoc]
      congr! 1
      conv =>
        enter [1, 2]
        rw [← Real.rpow_one (Real.log x)]
      rw [← Real.rpow_add (Real.log_pos (by linarith))]
      ring_nf
    rw [this]
  have event_4_aux : ∀ᶠ (x : ℝ) in atTop,
      c₅ * rexp (σ₂ * Real.log x + (A ^ ((1 : ℝ) / (1 + n₁)) / 2) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) ≤
      c₅ * rexp (Real.log x - (A ^ ((1 : ℝ) / (1 + n₁)) / 4) * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    filter_upwards [eventually_gt_atTop 3, event_4_aux1 σ₂InIoo.2 (A ^ ((1 : ℝ) / (1 + n₁)) / 2)
      (A ^ ((1 : ℝ) / (1 + n₁)) / 4) one_div_succ_n₁_lt_one] with x x_gt hx
    rw [mul_le_mul_iff_right₀ c₅pos]
    apply Real.exp_monotone
    convert hx
  have event_4 : ∀ᶠ (x : ℝ) in atTop, c₅ * x ^ σ₂ / (εx x) ≤
      c₅ * x * rexp (-c * Real.log x ^ ((1 : ℝ) / (1 + n₁))) := by
    unfold εx c_εx c
    filter_upwards [event_4_aux, eventually_gt_atTop 0] with x hx xpos
    convert hx using 1
    · rw [← mul_div]
      congr! 1
      rw [div_eq_mul_inv, ← Real.exp_neg]
      conv =>
        enter [1, 1, 1]
        rw [← Real.exp_log xpos]
      rw [← exp_mul, ← Real.exp_add]
      ring_nf
    · rw [mul_assoc]
      congr! 1
      conv =>
        enter [1, 1]
        rw [← Real.exp_log xpos]
      rw [← Real.exp_add]
      ring_nf
  filter_upwards [eventually_gt_atTop 3, eventually_εx_lt_one, eventually_2_lt,
    eventually_T_gt_3, eventually_T_gt_Tlb₄, eventually_T_gt_Tlb₆,
      eventually_σ₂_lt_σ₁, eventually_ε_lt_ε_main, event_logX_ge, event_1, event_2,
      event_3, event_4] with X X_gt_3 ε_lt_one ε_X T_gt_3 T_gt_Tlb₄ T_gt_Tlb₆
      σ₂_lt_σ₁ ε_lt_ε_main logX_ge event_1 event_2 event_3 event_4
  clear eventually_εx_lt_one eventually_2_lt eventually_T_gt_3 eventually_T_gt_Tlb₄
    eventually_T_gt_Tlb₆ eventually_σ₂_lt_σ₁ eventually_ε_lt_ε_main event_logX_ge
  let ε : ℝ := εx X
  have ε_pos : 0 < ε := by positivity
  specialize h_close X X_gt_3 ε ε_pos ε_lt_one ε_X
  let ψ_ε_of_X := SmoothedChebyshev ν ε X
  let T : ℝ := Tx X
  specialize holo1 T T_gt_3.le
  let σ₁ : ℝ := 1 - A / (Real.log T) ^ n₁
  have σ₁pos : 0 < σ₁ := by calc
    1 - A / (Real.log T) ^ n₁ >= 1 - (1/2) / 1 ^ n₁ := by
      gcongr
      · exact A_in_Ioc.2
      · exact (logt_gt_one T_gt_3.le).le
    _ > 0 := by norm_num
  have σ₁_lt_one : σ₁ < 1 := by
    apply sub_lt_self
    apply div_pos A_in_Ioc.1
    bound
  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)] at holo2
  have holo2a : HolomorphicOn (SmoothedChebyshevIntegrand ν ε X)
      (Icc σ₂ 2 ×ℂ Icc (-3) 3 \ {1}) := by
    apply DifferentiableOn.mul
    · apply DifferentiableOn.mul
      · rw [(by ext; ring : (fun s ↦ -deriv riemannZeta s / riemannZeta s) = (fun s ↦ -(deriv riemannZeta s / riemannZeta s)))]
        apply DifferentiableOn.neg holo2
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        apply Smooth1MellinDifferentiable ContDiff1ν ν_supp ⟨ε_pos, ε_lt_one⟩ ν_nonneg ν_massOne
        linarith [mem_reProdIm.mp hs.1 |>.1.1, σ₂InIoo.1]
    · intro s hs
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.const_cpow (by fun_prop)
      left
      norm_cast
      linarith
  have ψ_ε_diff : ‖ψ_ε_of_X - mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ ≤ ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖
    + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖
    + ‖I₈ ν ε T X σ₁‖ + ‖I₉ ν ε X T‖ := by
    unfold ψ_ε_of_X
    rw [SmoothedChebyshevPull1 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₁pos σ₁_lt_one holo1 ν_supp ν_nonneg ν_massOne ContDiff1ν]
    rw [SmoothedChebyshevPull2 ε_pos ε_lt_one X X_gt_3 (T := T) (by linarith)
      σ₂InIoo.1 σ₁_lt_one σ₂_lt_σ₁ holo1 holo2a ν_supp ν_nonneg ν_massOne ContDiff1ν]
    ring_nf
    iterate 5
      apply le_trans (by apply norm_add_le)
      gcongr
    rw [(by ring : I₁ ν ε X T - I₂ ν ε T X σ₁ + I₃ ν ε T X σ₁ - I₄ ν ε X σ₁ σ₂ = (I₁ ν ε X T - I₂ ν ε T X σ₁) + (I₃ ν ε T X σ₁ - I₄ ν ε X σ₁ σ₂))]
    apply le_trans (by apply norm_add_le)
    rw [(by ring : ‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖ =
      (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖) + (‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖))]
    gcongr <;> apply le_trans (by apply norm_sub_le) <;> rfl
  specialize h_main ε ⟨ε_pos, ε_lt_ε_main⟩
  have main : ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ ≤ C_main * ε * X := by
    nth_rewrite 2 [← one_mul X]
    push_cast
    rw [← sub_mul, norm_mul]
    gcongr
    rw [norm_real, norm_of_nonneg (by linarith)]
  specialize hc₁ ε ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₂ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₃ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₅ X X_gt_3 ε_pos ε_lt_one
  specialize hc₇ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₈ X X_gt_3 ε_pos ε_lt_one T_gt_3
  specialize hc₉ ε_pos ε_lt_one X X_gt_3 T_gt_3
  specialize hc₄ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₄
  specialize hc₆ X X_gt_3 ε_pos ε_lt_one T_gt_Tlb₆
  clear ν_nonneg ν_massOne ContDiff1ν ν_supp holo2
  have C'bnd : c_close * ε * X * Real.log X + C_main * ε * X ≤ C' * ε * X * Real.log X := by
    have : C_main * ε * X * 1 ≤ C_main * ε * X * Real.log X := by
      gcongr
    linarith
  have C''bnd : c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T) + c₈ * X / (ε * T)
    + c₉ * X * Real.log X / (ε * T) ≤ C'' * X * Real.log X / (ε * T) := by
    unfold C''
    rw [(by ring : (c₁ + c₂ + c₈ + c₉) * X * Real.log X / (ε * T)
      = c₁ * X * Real.log X / (ε * T) + c₂ * X * Real.log X / (ε * T)
        + c₈ * X * Real.log X / (ε * T) + c₉ * X * Real.log X / (ε * T))]
    have : c₂ * X / (ε * T) * 1 ≤ c₂ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₂ * X / (ε * T) ≤ c₂ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]
    have : c₈ * X / (ε * T) * 1 ≤ c₈ * X / (ε * T) * Real.log X := by
      gcongr
    have : c₈ * X / (ε * T) ≤ c₈ * X * Real.log X / (ε * T) := by
      ring_nf at this ⊢
      linarith
    grw [this]
  have C'''bnd : c₃ * X * X ^ (-A / Real.log T ^ n₁) / ε
                    + c₄ * X * X ^ (-A / Real.log T ^ n₁) / ε
                    + c₆ * X * X ^ (-A / Real.log T ^ n₁) / ε
                    + c₇ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  ≤ C''' * X * X ^ (-A / Real.log T ^ n₁) / ε := by
    apply le_of_eq
    ring
  calc
    _         = ‖(ψ X - ψ_ε_of_X) + (ψ_ε_of_X - X)‖ := by ring_nf; norm_cast
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - X‖ := norm_add_le _ _
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖(ψ_ε_of_X - mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X)
                  + (mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X)‖ := by ring_nf
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖ψ_ε_of_X - mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖
                  + ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖ := by
                    rw [add_assoc]
                    gcongr
                    apply norm_add_le
    _         = ‖ψ X - ψ_ε_of_X‖ + ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + ‖ψ_ε_of_X - mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X‖ := by ring
    _         ≤ ‖ψ X - ψ_ε_of_X‖ + ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 * X - X‖
                  + (‖I₁ ν ε X T‖ + ‖I₂ ν ε T X σ₁‖ + ‖I₃ ν ε T X σ₁‖ + ‖I₄ ν ε X σ₁ σ₂‖
                  + ‖I₅ ν ε X σ₂‖ + ‖I₆ ν ε X σ₁ σ₂‖ + ‖I₇ ν ε T X σ₁‖ + ‖I₈ ν ε T X σ₁‖
                  + ‖I₉ ν ε X T‖) := by gcongr
    _         ≤ c_close * ε * X * Real.log X + C_main * ε * X
                  + (c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₃ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₄ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₅ * X ^ σ₂ / ε
                  + c₆ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₇ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T)) := by
      gcongr
      convert! h_close using 1
      rw [← norm_neg]
      congr
      ring
    _         =  (c_close * ε * X * Real.log X + C_main * ε * X)
                  + ((c₁ * X * Real.log X / (ε * T) + c₂ * X / (ε * T)
                  + c₈ * X / (ε * T)
                  + c₉ * X * Real.log X / (ε * T))
                  + (c₃ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₄ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₆ * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₇ * X * X ^ (-A / Real.log T ^ n₁) / ε)
                  + c₅ * X ^ σ₂ / ε
                  ) := by ring
    _         ≤ C' * ε * X * Real.log X
                  + (C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₅ * X ^ σ₂ / ε
                  ) := by
      gcongr
    _        = C' * ε * X * Real.log X
                  + C'' * X * Real.log X / (ε * T)
                  + C''' * X * X ^ (-A / Real.log T ^ n₁) / ε
                  + c₅ * X ^ σ₂ / ε
                    := by ring
    _        ≤ C' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                  + C'' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                  + C''' * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                  + c₅ * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                    := by
      gcongr
    _        = C * X * rexp (-c * Real.log X ^ ((1 : ℝ) / (1 + n₁)))
                    := by ring
    _        = _ := by
      rw [Real.norm_of_nonneg]
      · rw [← mul_assoc]
      · positivity
theorem MediumPNT : ∃ c > 0,
    (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
  have := GenStrengthPNT LogDerivZetaBoundedAndHolo99 (by linarith) (by linarith); ring_nf at this
  simpa only [gt_iff_lt, one_div, neg_mul] using this
theorem PNTPort.MediumPNT : ∃ c > 0, (ψ - id) =O[atTop] fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) := _root_.MediumPNT
end PNT_MediumPNT



-- Adapted from Erdos320.Core.
section
/- Exact rational subset sums, their cardinality and the iterated-logarithm scale. -/

namespace Erdos320

/-- Exact rational values of reciprocal subset sums on a denominator set. -/
def sumsOf (A : Finset ℕ) : Finset ℚ :=
  A.powerset.image (fun (B : Finset ℕ) => ∑ n ∈ B, (n : ℚ)⁻¹)

/-- All denominators are positive, and every subset, including empty, is used. -/
def sums (N : ℕ) : Finset ℚ := sumsOf (Finset.Icc 1 N)

/-- Erdős's counting function. -/
def S (N : ℕ) : ℕ := (sums N).card

noncomputable def logS (N : ℕ) : ℝ := Real.log (S N : ℝ)

/-- A finite-height product stopped before logarithmic factors are at most 3.
The final statement uses height `N`; sufficiency of this height must be proved.
-/
noncomputable def stoppedProduct : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, x =>
      if x ≤ Real.exp 3 then 1
      else Real.log x * stoppedProduct k (Real.log x)

/-- The full, growing-depth comparison scale. -/
noncomputable def scale (N : ℕ) : ℝ :=
  ((N : ℝ) / Real.log N) *
    stoppedProduct N (Real.log (Real.log N))

/-- The prime blocks in the accepted upper-bound argument. -/
noncomputable def largePrimes (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter
    (fun p => Nat.Prime p ∧ (N : ℝ) / Real.log N < (p : ℝ))

end Erdos320
end


-- Adapted from Erdos320.UpperAnalyticDecay.
section
/-
Original elementary decay estimates used to turn the quantitative prime number
theorem into a polynomial logarithmic endpoint error.
-/

namespace Erdos320

/-- A stretched exponential in `log x` beats every fixed power of `log x`. -/
theorem tendsto_log_pow_mul_exp_neg_rpow
    (k : ℕ) (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    Filter.Tendsto
      (fun x : ℝ => Real.log x ^ k * Real.exp (-c * Real.log x ^ r))
      Filter.atTop (nhds 0) := by
  have hinner : Filter.Tendsto (fun x : ℝ => Real.log x ^ r)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hr).comp Real.tendsto_log_atTop
  have houter :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℝ) / r) c hc
  refine (houter.comp hinner).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  have hl : 0 ≤ Real.log x := (Real.log_pos hx).le
  have hpow : (Real.log x ^ r) ^ ((k : ℝ) / r) = Real.log x ^ k := by
    rw [← Real.rpow_mul hl, mul_div_cancel₀ _ hr.ne', Real.rpow_natCast]
  simp only [Function.comp_apply, hpow]

theorem eventual_exp_neg_log_rpow_le_inv_log_pow
    (k : ℕ) (C c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    ∀ᶠ x : ℝ in Filter.atTop,
      C * Real.exp (-c * Real.log x ^ r) ≤ 1 / Real.log x ^ k := by
  have hlim : Filter.Tendsto
      (fun x : ℝ => C * (Real.log x ^ k * Real.exp (-c * Real.log x ^ r)))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_log_pow_mul_exp_neg_rpow k c r hc hr).const_mul C
  have hsmall : ∀ᶠ x : ℝ in Filter.atTop,
      C * (Real.log x ^ k * Real.exp (-c * Real.log x ^ r)) < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, Filter.eventually_gt_atTop (1 : ℝ)] with x hx hxl
  apply (le_div_iff₀ (pow_pos (Real.log_pos hxl) k)).mpr
  nlinarith only [hx.le]

end Erdos320
end


-- Adapted from Erdos320.LowerAnalytic.Losses.
section
/-
Summable depth losses for the independent lower renewal argument. These are
elementary uniform estimates, rather than fixed-depth asymptotics.
-/

namespace Erdos320.LowerAnalytic

noncomputable def epsilon (k : ℕ) : ℝ := (1 / 4 : ℝ) ^ (k + 3)

noncomputable def iterationLoss (k : ℕ) : ℝ := 2 * (k + 2 : ℕ) * epsilon k

noncomputable def coefficient (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, (1 - iterationLoss i)

theorem epsilon_pos (k : ℕ) : 0 < epsilon k := by
  unfold epsilon
  positivity

theorem epsilon_le (k : ℕ) : epsilon k ≤ 1 / 64 := by
  have hp : (1 / 4 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold epsilon
  rw [pow_add]
  norm_num
  nlinarith

theorem epsilon_succ (k : ℕ) : epsilon (k + 1) = epsilon k / 4 := by
  unfold epsilon
  rw [show k + 1 + 3 = (k + 3) + 1 by omega, pow_succ]
  ring

private theorem index_le_two_pow (k : ℕ) : (k + 2 : ℕ) ≤ (2 : ℝ) ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast at ih ⊢
      rw [pow_succ]
      nlinarith

theorem iterationLoss_nonneg (k : ℕ) : 0 ≤ iterationLoss k := by
  unfold iterationLoss
  exact mul_nonneg (by positivity) (epsilon_pos k).le

theorem iterationLoss_le_geometric (k : ℕ) :
    iterationLoss k ≤ (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ k := by
  have hindex := index_le_two_pow k
  have heq : 2 * (2 : ℝ) ^ (k + 1) * (1 / 4 : ℝ) ^ (k + 3) =
      (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ k := by
    calc
      2 * (2 : ℝ) ^ (k + 1) * (1 / 4 : ℝ) ^ (k + 3) =
          (1 / 16 : ℝ) * ((2 : ℝ) ^ k * (1 / 4 : ℝ) ^ k) := by
        rw [pow_succ, pow_add]
        norm_num
        ring
      _ = _ := by rw [← mul_pow]; norm_num
  unfold iterationLoss epsilon
  rw [← heq]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hindex (by norm_num))
    (by positivity)

theorem iterationLoss_le (k : ℕ) : iterationLoss k ≤ 1 / 16 := by
  have hp : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h := iterationLoss_le_geometric k
  nlinarith

theorem sum_iterationLoss_le (k : ℕ) :
    (∑ i ∈ Finset.range k, iterationLoss i) ≤ 1 / 8 := by
  calc
    (∑ i ∈ Finset.range k, iterationLoss i) ≤
        ∑ i ∈ Finset.range k, (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ i :=
      Finset.sum_le_sum (fun i _ => iterationLoss_le_geometric i)
    _ = (1 / 16 : ℝ) * ∑ i ∈ Finset.range k, (1 / 2 : ℝ) ^ i :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (1 / 16 : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le k) (by norm_num)
    _ = 1 / 8 := by norm_num

private theorem one_sub_sum_le_product (s : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hfi := hf i (by simp)
      have hfs : ∀ j ∈ s, 0 ≤ f j ∧ f j ≤ 1 := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : 0 ≤ ∑ j ∈ s, f j :=
        Finset.sum_nonneg (fun j hj => (hfs j hj).1)
      have hmul := mul_le_mul_of_nonneg_left (ih hfs) (show 0 ≤ 1 - f i by linarith)
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      nlinarith [mul_nonneg hfi.1 hsum]

theorem coefficient_lower (k : ℕ) : 7 / 8 ≤ coefficient k := by
  have h := one_sub_sum_le_product (Finset.range k) iterationLoss
    (fun i _ => ⟨iterationLoss_nonneg i, (iterationLoss_le i).trans (by norm_num)⟩)
  have hsum := sum_iterationLoss_le k
  unfold coefficient
  linarith

theorem coefficient_pos (k : ℕ) : 0 < coefficient k :=
  lt_of_lt_of_le (by norm_num) (coefficient_lower k)

theorem coefficient_le_one (k : ℕ) : coefficient k ≤ 1 := by
  unfold coefficient
  exact Finset.prod_le_one (fun i _ => by have := iterationLoss_le i; linarith)
    (fun i _ => by have := iterationLoss_nonneg i; linarith)

theorem coefficient_zero : coefficient 0 = 1 := by simp [coefficient]

theorem coefficient_succ (k : ℕ) :
    coefficient (k + 1) = coefficient k * (1 - iterationLoss k) := by
  simp [coefficient, Finset.prod_range_succ]

/-- All multiplicative losses of one analytic step have a summable deficit. -/
theorem analytic_step_factor_lower (k : ℕ) :
    1 - iterationLoss k ≤
      (1 - epsilon k) * (1 - 2 * epsilon k) * (1 - epsilon k) ^ k := by
  have he := epsilon_le k
  have he0 := (epsilon_pos k).le
  have hb : 0 ≤ 1 - 2 * epsilon k := by linarith
  have ha : 0 ≤ 1 - epsilon k := by linarith
  have hbern := one_add_mul_le_pow
    (show (-2 : ℝ) ≤ -2 * epsilon k by linarith) (k + 2)
  rw [show 1 + -2 * epsilon k = 1 - 2 * epsilon k by ring] at hbern
  have hfirst : 1 - iterationLoss k ≤ (1 - 2 * epsilon k) ^ (k + 2) := by
    dsimp [iterationLoss]
    push_cast at hbern ⊢
    nlinarith
  apply hfirst.trans
  calc
    (1 - 2 * epsilon k) ^ (k + 2) =
        (1 - 2 * epsilon k) ^ k * (1 - 2 * epsilon k) ^ 2 := by rw [pow_add]
    _ ≤ (1 - epsilon k) ^ k * ((1 - epsilon k) * (1 - 2 * epsilon k)) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ hb (by linarith) _
      · rw [pow_two]
        exact mul_le_mul_of_nonneg_right (by linarith) hb
      · positivity
      · positivity
    _ = _ := by ring

end Erdos320.LowerAnalytic
end


-- Adapted from Erdos320.UpperAnalytic.
section
/-
Original analytic scaffolding for Erdős Problem 320.

The theorems here prove an abstract recurrence implication. They do not assume
the desired asymptotic bound, and they do not assert that the prime-block
recurrence has yet been converted to their hypotheses.

The `-A` in the induction invariant is essential: it absorbs the additive
recurrence cost without introducing a fixed multiplicative loss at each
iteration. A product that dominates the exact recurrence coefficients then
controls all iteration depths with one constant.
-/

namespace Erdos320

/-- A nonnegative running maximum, including the value at zero. -/
noncomputable def runningMaximum (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => max 0 (f 0)
  | n + 1 => max (runningMaximum f n) (f (n + 1))

theorem runningMaximum_monotone (f : ℕ → ℝ) : Monotone (runningMaximum f) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

theorem runningMaximum_nonneg (f : ℕ → ℝ) (n : ℕ) : 0 ≤ runningMaximum f n := by
  have h₀ : 0 ≤ runningMaximum f 0 := le_max_left _ _
  exact h₀.trans (runningMaximum_monotone f (Nat.zero_le n))

theorem le_runningMaximum (f : ℕ → ℝ) (n : ℕ) : f n ≤ runningMaximum f n := by
  cases n with
  | zero => exact le_max_right _ _
  | succ n => exact le_max_right _ _

theorem le_runningMaximum_of_le (f : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    f m ≤ runningMaximum f n :=
  (le_runningMaximum f m).trans (runningMaximum_monotone f hmn)

theorem runningMaximum_le (f : ℕ → ℝ) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n ≤ N, f n ≤ C) : runningMaximum f N ≤ C := by
  induction N with
  | zero => exact max_le hC (hf 0 le_rfl)
  | succ N ih =>
      apply max_le
      · exact ih (fun n hn => hf n (hn.trans (Nat.le_succ N)))
      · exact hf (N + 1) le_rfl

/-- A finite family of real values admits a positive uniform upper bound. -/
theorem finite_initial_segment_upper_bound (f : ℕ → ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n < N, f n ≤ C := by
  let C : ℝ := 1 + ∑ i ∈ Finset.range N, |f i|
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, |f i| := by positivity
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro n hn
  have hs : |f n| ≤ ∑ i ∈ Finset.range N, |f i| :=
    Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_range.mpr hn)
  have hf : f n ≤ |f n| := le_abs_self (f n)
  dsimp [C]
  linarith

/-- Solve a recursive upper bound using a product supersolution. The number of
recursive steps is unrestricted. The conclusion is uniform over every input.

The lower bound `2 ≤ b n` supplies enough slack to absorb the fixed additive
cost. It is not a multiplicative approximation to the coefficient: `b n` is
the actual coefficient appearing in `hrec` and `hweight`.
-/
theorem upper_bound_of_contracting_recurrence
    (f weight b : ℕ → ℝ) (q : ℕ → ℕ) (A : ℝ) (N₀ : ℕ)
    (hA : 0 ≤ A) (hweight_one : ∀ n, 1 ≤ weight n)
    (hdecrease : ∀ n, N₀ ≤ n → q n < n)
    (hcoeff : ∀ n, N₀ ≤ n → 2 ≤ b n)
    (hweight : ∀ n, N₀ ≤ n → b n * weight (q n) ≤ weight n)
    (hrec : ∀ n, N₀ ≤ n → f n ≤ A + b n * f (q n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, f n ≤ C * weight n := by
  obtain ⟨C₀, hC₀, hbase⟩ := finite_initial_segment_upper_bound f N₀
  let C : ℝ := C₀ + A
  have hC : 0 < C := by dsimp [C]; linarith
  have hinvariant : ∀ n, f n ≤ C * weight n - A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < N₀
      · have hfn := hbase n hn
        have hwn := hweight_one n
        have hmul : C₀ + A ≤ (C₀ + A) * weight n := by
          nlinarith
        dsimp [C]
        linarith
      · have hn₀ : N₀ ≤ n := Nat.le_of_not_gt hn
        have hi := ih (q n) (hdecrease n hn₀)
        have hb := hcoeff n hn₀
        have hw := hweight n hn₀
        have hr := hrec n hn₀
        have hb₀ : 0 ≤ b n := by linarith
        have hmul := mul_le_mul_of_nonneg_left hi hb₀
        have hprod := mul_le_mul_of_nonneg_left hw (le_of_lt hC)
        have hcost : 2 * A ≤ b n * A := by nlinarith
        nlinarith
  refine ⟨C, hC, ?_⟩
  intro n
  have hi := hinvariant n
  linarith

/-- Eventual recurrence and product comparison hypotheses are sufficient: all
finitely many exceptional inputs are absorbed into the same positive constant.
-/
theorem upper_bound_of_eventual_contracting_recurrence
    (f weight b : ℕ → ℝ) (q : ℕ → ℕ) (A : ℝ)
    (hA : 0 ≤ A) (hweight_one : ∀ n, 1 ≤ weight n)
    (hdecrease : ∀ᶠ n in Filter.atTop, q n < n)
    (hcoeff : ∀ᶠ n in Filter.atTop, 2 ≤ b n)
    (hweight : ∀ᶠ n in Filter.atTop, b n * weight (q n) ≤ weight n)
    (hrec : ∀ᶠ n in Filter.atTop, f n ≤ A + b n * f (q n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, f n ≤ C * weight n := by
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.mp (hdecrease.and (hcoeff.and (hweight.and hrec)))
  exact upper_bound_of_contracting_recurrence f weight b q A N₀ hA hweight_one
    (fun n hn => (hN₀ n hn).1)
    (fun n hn => (hN₀ n hn).2.1)
    (fun n hn => (hN₀ n hn).2.2.1)
    (fun n hn => (hN₀ n hn).2.2.2)

/-- The same induction works directly with a running maximum of the recursive
values. Only the comparison weight needs to be monotone; no monotonicity of
the original normalized counting function is asserted or used. -/
theorem upper_bound_of_envelope_recurrence
    (f weight b : ℕ → ℝ) (q : ℕ → ℕ) (A : ℝ) (N₀ : ℕ)
    (hA : 0 ≤ A) (hweight_one : ∀ n, 1 ≤ weight n)
    (hweight_mono : Monotone weight)
    (hdecrease : ∀ n, N₀ ≤ n → q n < n)
    (hcoeff : ∀ n, N₀ ≤ n → 2 ≤ b n)
    (hweight : ∀ n, N₀ ≤ n → b n * weight (q n) ≤ weight n)
    (hrec : ∀ n, N₀ ≤ n → f n ≤ A + b n * runningMaximum f (q n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, f n ≤ C * weight n := by
  obtain ⟨C₀, hC₀, hbase⟩ := finite_initial_segment_upper_bound f N₀
  let C : ℝ := C₀ + A
  have hC : 0 < C := by dsimp [C]; linarith
  have hinvariant : ∀ n, f n ≤ C * weight n - A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < N₀
      · have hfn := hbase n hn
        have hwn := hweight_one n
        have hmul : C₀ + A ≤ (C₀ + A) * weight n := by nlinarith
        dsimp [C]
        linarith
      · have hn₀ : N₀ ≤ n := Nat.le_of_not_gt hn
        have hq := hdecrease n hn₀
        have hb := hcoeff n hn₀
        have hw := hweight n hn₀
        have hr := hrec n hn₀
        have hMw : 0 ≤ C * weight (q n) - A := by
          have hw₁ := hweight_one (q n)
          dsimp [C]
          nlinarith
        have hM : runningMaximum f (q n) ≤ C * weight (q n) - A := by
          apply runningMaximum_le f (q n) _ hMw
          intro m hm
          have hf := ih m (hm.trans_lt hq)
          have hw_m := hweight_mono hm
          have hcmp := mul_le_mul_of_nonneg_left hw_m hC.le
          linarith
        have hmul := mul_le_mul_of_nonneg_left hM (by linarith : 0 ≤ b n)
        have hprod := mul_le_mul_of_nonneg_left hw hC.le
        have hcost : 2 * A ≤ b n * A := by nlinarith
        nlinarith
  refine ⟨C, hC, ?_⟩
  intro n
  have hi := hinvariant n
  linarith

theorem upper_bound_of_eventual_envelope_recurrence
    (f weight b : ℕ → ℝ) (q : ℕ → ℕ) (A : ℝ)
    (hA : 0 ≤ A) (hweight_one : ∀ n, 1 ≤ weight n)
    (hweight_mono : Monotone weight)
    (hdecrease : ∀ᶠ n in Filter.atTop, q n < n)
    (hcoeff : ∀ᶠ n in Filter.atTop, 2 ≤ b n)
    (hweight : ∀ᶠ n in Filter.atTop, b n * weight (q n) ≤ weight n)
    (hrec : ∀ᶠ n in Filter.atTop, f n ≤ A + b n * runningMaximum f (q n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, f n ≤ C * weight n := by
  obtain ⟨N₀, hN₀⟩ :=
    Filter.eventually_atTop.mp (hdecrease.and (hcoeff.and (hweight.and hrec)))
  exact upper_bound_of_envelope_recurrence f weight b q A N₀ hA hweight_one hweight_mono
    (fun n hn => (hN₀ n hn).1)
    (fun n hn => (hN₀ n hn).2.1)
    (fun n hn => (hN₀ n hn).2.2.1)
    (fun n hn => (hN₀ n hn).2.2.2)

/-- Lift a pointwise recurrence to its running maximum. Small exceptional inputs
are absorbed additively, and the coefficient is retained exactly.

This isolates the monotonic-envelope step from the number-theoretic estimate.
In the intended application, `q n = ⌊log n⌋` and `b n = log₃ n` above a fixed
threshold. No assertion about either function is assumed outside that range.
-/
theorem runningMaximum_recurrence
    (f b : ℕ → ℝ) (q : ℕ → ℕ) (A : ℝ) (N₀ : ℕ)
    (hA : 0 ≤ A) (hq : Monotone q)
    (hb_nonneg : ∀ n, N₀ ≤ n → 0 ≤ b n)
    (hb_mono : ∀ m n, N₀ ≤ m → m ≤ n → b m ≤ b n)
    (hrec : ∀ n, N₀ ≤ n →
      f n ≤ A + b n * runningMaximum f (q n)) :
    ∃ B : ℝ, 0 < B ∧ ∀ n, N₀ ≤ n →
      runningMaximum f n ≤ B + b n * runningMaximum f (q n) := by
  obtain ⟨C₀, hC₀, hbase⟩ := finite_initial_segment_upper_bound f N₀
  refine ⟨A + C₀, by linarith, ?_⟩
  intro n hn
  have htail_nonneg : 0 ≤ b n * runningMaximum f (q n) :=
    mul_nonneg (hb_nonneg n hn) (runningMaximum_nonneg f (q n))
  apply runningMaximum_le f n (A + C₀ + b n * runningMaximum f (q n))
  · linarith
  intro m hmn
  by_cases hm : m < N₀
  · have hfm := hbase m hm
    linarith
  · have hm₀ : N₀ ≤ m := Nat.le_of_not_gt hm
    have hfm := hrec m hm₀
    have hM : runningMaximum f (q m) ≤ runningMaximum f (q n) :=
      runningMaximum_monotone f (hq hmn)
    have hmul : b m * runningMaximum f (q m) ≤
        b n * runningMaximum f (q n) :=
      mul_le_mul (hb_mono m n hm₀ hmn) hM
        (runningMaximum_nonneg f (q m)) (hb_nonneg n hn)
    linarith

end Erdos320
end


-- Adapted from Erdos320.UpperAnalyticKernel.
section
/-
Original estimates for the logarithmic renewal kernel in Erdős Problem 320.

The finite tail begins at four. Integration begins at three, leaving the
strictly positive reserve `log (log 3)`. This reserve absorbs a vanishing
prime-counting error while retaining coefficient one at every recursion depth.
-/

namespace Erdos320

noncomputable def logarithmicKernel (x : ℝ) : ℝ := 1 / (x * Real.log x)

theorem logarithmicKernel_antitone :
    AntitoneOn logarithmicKernel (Set.Ici (3 : ℝ)) := by
  intro a ha b hb hab
  have ha₀ : 0 < a := by linarith [show (3 : ℝ) ≤ a from ha]
  have hb₀ : 0 < b := ha₀.trans_le hab
  have ha₁ : 1 < a := by linarith [show (3 : ℝ) ≤ a from ha]
  have hla : 0 < Real.log a := Real.log_pos ha₁
  have hl : Real.log a ≤ Real.log b := Real.log_le_log ha₀ hab
  have hp : a * Real.log a ≤ b * Real.log b :=
    mul_le_mul hab hl hla.le hb₀.le
  exact one_div_le_one_div_of_le (mul_pos ha₀ hla) hp

theorem hasDerivAt_loglog {x : ℝ} (hx : 3 ≤ x) :
    HasDerivAt (fun t : ℝ => Real.log (Real.log t)) (logarithmicKernel x) x := by
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx₁
  simpa [logarithmicKernel, div_eq_mul_inv, mul_inv_rev, mul_comm] using
    (Real.hasDerivAt_log hx₀.ne').log hl.ne'

theorem integral_logarithmicKernel {M : ℝ} (hM : 3 ≤ M) :
    (∫ t in (3 : ℝ)..M, logarithmicKernel t) =
      Real.log (Real.log M) - Real.log (Real.log 3) := by
  have ha : AntitoneOn logarithmicKernel (Set.uIcc (3 : ℝ) M) := by
    rw [Set.uIcc_of_le hM]
    exact logarithmicKernel_antitone.mono (fun _ hx => hx.1)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hM] at hx
    exact hasDerivAt_loglog hx.1
  · exact ha.intervalIntegrable

theorem sum_logarithmicKernel_le_loglog_sub (M : ℕ) (hM : 3 ≤ M) :
    (∑ i ∈ Finset.Ico 3 M, logarithmicKernel (i + 1 : ℕ)) ≤
      Real.log (Real.log M) - Real.log (Real.log 3) := by
  have ha : AntitoneOn logarithmicKernel (Set.Icc (3 : ℝ) M) :=
    logarithmicKernel_antitone.mono (fun _ hx => hx.1)
  calc
    (∑ i ∈ Finset.Ico 3 M, logarithmicKernel (i + 1 : ℕ))
        ≤ ∫ t in (3 : ℝ)..(M : ℝ), logarithmicKernel t :=
      ha.sum_le_integral_Ico hM
    _ = Real.log (Real.log M) - Real.log (Real.log 3) :=
      integral_logarithmicKernel (by exact_mod_cast hM)

/-- The reciprocal-log tail in its shifted-index form. -/
theorem sum_renewalKernel_shifted_le (M : ℕ) (hM : 3 ≤ M) :
    (∑ i ∈ Finset.Ico 3 M,
      1 / (((i + 1 : ℕ) : ℝ) + 1) / Real.log (i + 1 : ℕ)) ≤
      Real.log (Real.log M) - Real.log (Real.log 3) := by
  calc
    _ ≤ ∑ i ∈ Finset.Ico 3 M, logarithmicKernel (i + 1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi₃ : 3 ≤ i := (Finset.mem_Ico.mp hi).1
      have hi₀ : (0 : ℝ) < (i + 1 : ℕ) := by positivity
      have hi₁ : (1 : ℝ) < (i + 1 : ℕ) := by exact_mod_cast (by omega : 1 < i + 1)
      have hl : 0 < Real.log (i + 1 : ℕ) := Real.log_pos hi₁
      have hden : ((i + 1 : ℕ) : ℝ) * Real.log (i + 1 : ℕ) ≤
          (((i + 1 : ℕ) : ℝ) + 1) * Real.log (i + 1 : ℕ) := by nlinarith
      simpa [logarithmicKernel, div_eq_mul_inv, mul_inv_rev, mul_comm] using
        one_div_le_one_div_of_le (mul_pos hi₀ hl) hden
    _ ≤ Real.log (Real.log M) - Real.log (Real.log 3) :=
      sum_logarithmicKernel_le_loglog_sub M hM

theorem sum_renewalKernel_le (M : ℕ) (hM : 3 ≤ M) :
    (∑ m ∈ Finset.Icc 4 M, 1 / ((m : ℝ) + 1) / Real.log (m : ℝ)) ≤
      Real.log (Real.log M) - Real.log (Real.log 3) := by
  let f : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) / Real.log (m : ℝ)
  have hshift : (∑ m ∈ Finset.Icc 4 M, f m) =
      ∑ i ∈ Finset.Ico 3 M, f (i + 1) := by
    simpa only [Finset.Ico_add_one_right_eq_Icc, Nat.reduceAdd, Nat.add_comm] using
      (Finset.sum_Ico_add f 3 M 1).symm
  change (∑ m ∈ Finset.Icc 4 M, f m) ≤ _
  rw [hshift]
  exact sum_renewalKernel_shifted_le M hM

theorem loglog_three_pos : 0 < Real.log (Real.log (3 : ℝ)) := by
  apply Real.log_pos
  have h := Real.log_lt_log (Real.exp_pos (1 : ℝ)) Real.exp_one_lt_three
  simpa only [Real.log_exp] using h

/-- A positive reserve in the kernel absorbs the error without a repeated
fixed loss in the recurrence coefficient. -/
theorem multiplicative_error_absorbed_by_margin {δ T d : ℝ}
    (hδ : 0 ≤ δ) (hd : 0 < d) (herror : δ * T ≤ d) :
    (1 + δ) * (T - d) ≤ T := by
  have hδd : 0 ≤ δ * d := mul_nonneg hδ hd.le
  nlinarith

theorem eventual_multiplicative_error_absorbed_by_margin
    (δ T : ℕ → ℝ) (d : ℝ) (hd : 0 < d)
    (hδ : ∀ᶠ n in Filter.atTop, 0 ≤ δ n)
    (herror : Filter.Tendsto (fun n => δ n * T n) Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop, (1 + δ n) * (T n - d) ≤ T n := by
  have hsmall : ∀ᶠ n in Filter.atTop, δ n * T n < d :=
    herror.eventually (gt_mem_nhds hd)
  filter_upwards [hδ, hsmall] with n hn hs
  exact multiplicative_error_absorbed_by_margin hn hd hs.le

/-- A denominator loss `1-z`, with `z ≤ 1/2`, and a relative numerator error
`e` can be bounded with a coefficient tending to one when `z,e → 0`.
This is the arithmetic normalization used for a quantitative prime interval.
-/
theorem denominator_loss_normalization {B H L z e : ℝ}
    (hH : 0 ≤ H) (hz : 0 ≤ z) (hz_half : z ≤ 1 / 2)
    (he : 0 ≤ e) (hbound : B * L * (1 - z) ≤ H * (1 + e)) :
    B * L ≤ H * (1 + 2 * z + 2 * e) := by
  have hz₁ : 0 < 1 - z := by linarith
  have hreserve : 0 ≤ (z + e) * (1 - 2 * z) :=
    mul_nonneg (add_nonneg hz he) (by linarith)
  have hfactor : 1 + e ≤ (1 + 2 * z + 2 * e) * (1 - z) := by
    nlinarith
  have hnormalized : (B * L) * (1 - z) ≤
      (H * (1 + 2 * z + 2 * e)) * (1 - z) := by
    calc
      _ ≤ H * (1 + e) := hbound
      _ ≤ H * ((1 + 2 * z + 2 * e) * (1 - z)) :=
        mul_le_mul_of_nonneg_left hfactor hH
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ hz₁).mp hnormalized

end Erdos320
end


-- Adapted from Erdos320.UpperAnalyticPrimeIntervals.
section
/-
Original bridge from a quantitative Chebyshev-psi estimate to upper bounds for
prime blocks. It uses nonnegativity of the von Mangoldt function and therefore
does not need a separate quantitative prime-counting / logarithmic-integral
theorem.
-/

namespace Erdos320

/-- Each prime in `(a,b]` supplies at least `log a` to the positive increment
of Chebyshev's psi function. -/
theorem prime_card_mul_log_le_psi_sub
    (P : Finset ℕ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b) :
    (P.card : ℝ) * Real.log a ≤ Chebyshev.psi b - Chebyshev.psi a := by
  classical
  let Q : Finset ℕ := Finset.Ioc 0 ⌊a⌋₊
  let R : Finset ℕ := Finset.Ioc 0 ⌊b⌋₊
  have hb : 0 ≤ b := ha.le.trans hab
  have hQR : Q ⊆ R := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨hn'.1, hn'.2.trans (Nat.floor_mono hab)⟩
  have hPR : P ⊆ R := by
    intro p hp
    have h := hP p hp
    apply Finset.mem_Ioc.mpr
    exact ⟨h.1.pos, (Nat.le_floor_iff hb).mpr h.2.2⟩
  have hdis : Disjoint Q P := by
    apply Finset.disjoint_left.mpr
    intro p hpQ hpP
    have hpa : (p : ℝ) ≤ a :=
      (Nat.le_floor_iff ha.le).mp (Finset.mem_Ioc.mp hpQ).2
    exact (not_lt_of_ge hpa) (hP p hpP).2.1
  have hsum :
      (∑ n ∈ Q, ArithmeticFunction.vonMangoldt n) +
          ∑ p ∈ P, ArithmeticFunction.vonMangoldt p ≤
        ∑ n ∈ R, ArithmeticFunction.vonMangoldt n := by
    rw [← Finset.sum_union hdis]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.union_subset hQR hPR
    · intro n _ _
      exact ArithmeticFunction.vonMangoldt_nonneg
  have hlog : (P.card : ℝ) * Real.log a ≤
      ∑ p ∈ P, ArithmeticFunction.vonMangoldt p := by
    calc
      (P.card : ℝ) * Real.log a = ∑ _p ∈ P, Real.log a := by simp
      _ ≤ ∑ p ∈ P, Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log ha (hP p hp).2.1.le
      _ = ∑ p ∈ P, ArithmeticFunction.vonMangoldt p := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (ArithmeticFunction.vonMangoldt_apply_prime (hP p hp).1).symm
  change Chebyshev.psi a +
      ∑ p ∈ P, ArithmeticFunction.vonMangoldt p ≤ Chebyshev.psi b at hsum
  linarith

/-- A generic endpoint-error version, directly usable with a quantitative PNT.
The errors at the two endpoints may be different. -/
theorem prime_card_le_of_psi_endpoint_errors
    (P : Finset ℕ) (a b eₐ e_b : ℝ) (ha : 1 < a) (hab : a ≤ b)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b)
    (hₐ : |Chebyshev.psi a - a| ≤ eₐ)
    (h_b : |Chebyshev.psi b - b| ≤ e_b) :
    (P.card : ℝ) ≤ (b - a + eₐ + e_b) / Real.log a := by
  have hlog : 0 < Real.log a := Real.log_pos ha
  have hcount := prime_card_mul_log_le_psi_sub P a b (by linarith) hab hP
  have hupper : Chebyshev.psi b - b ≤ e_b := (le_abs_self _).trans h_b
  have hlower : -(Chebyshev.psi a - a) ≤ eₐ := (neg_le_abs _).trans hₐ
  apply (le_div_iff₀ hlog).mpr
  linarith

end Erdos320
end


-- Adapted from Erdos320.LowerFinite.
section
/-
Original development of the finite lower-bound mechanism for Erdős Problem 320.
The mathematical exact-doubling idea is due to Bleicher--Erdős and is also used
by Bettin--Grenié--Molteni--Sanna. No asymptotic result is asserted in this file.
-/

namespace Erdos320

/-- The translated old support obtained by adjoining denominator `N+1`. -/
def addedLayer (N : ℕ) : Finset ℚ :=
  (sums N).image (fun q => q + ((N + 1 : ℕ) : ℚ)⁻¹)

/-- A positive denominator independent of all signed sums of earlier terms. -/
def IndependentDenominator (d : ℕ) : Prop :=
  0 < d ∧ ∀ a ∈ sums (d - 1), ∀ b ∈ sums (d - 1),
    a - b ≠ (d : ℚ)⁻¹

noncomputable instance (d : ℕ) : Decidable (IndependentDenominator d) :=
  Classical.propDecidable _

/-- Independent denominators among the first `N` positive integers. -/
noncomputable def independentDenominators (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter IndependentDenominator

theorem sumsOf_insert (A : Finset ℕ) {d : ℕ} (hd : d ∉ A) :
    sumsOf (insert d A) =
      sumsOf A ∪ (sumsOf A).image (fun q => q + (d : ℚ)⁻¹) := by
  classical
  unfold sumsOf
  rw [Finset.powerset_insert, Finset.image_union]
  congr 1
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro B hB
  have hdB : d ∉ B := by
    intro h
    exact hd ((Finset.mem_powerset.mp hB) h)
  simp [hdB, add_comm]

theorem sums_succ_decomposition (N : ℕ) :
    sums (N + 1) = sums N ∪ addedLayer N := by
  have hnew : N + 1 ∉ Finset.Icc 1 N := by simp
  unfold sums addedLayer
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ N + 1)]
  exact sumsOf_insert _ hnew

theorem addedLayer_card (N : ℕ) : (addedLayer N).card = S N := by
  rw [addedLayer, S]
  exact Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)

theorem S_mono_step (N : ℕ) : S N ≤ S (N + 1) := by
  unfold S
  rw [sums_succ_decomposition]
  exact Finset.card_le_card Finset.subset_union_left

theorem S_exact_doubling {d : ℕ} (hd : IndependentDenominator d) :
    S d = 2 * S (d - 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd.1)
  have hd' : ∀ a ∈ sums d, ∀ b ∈ sums d,
      a - b ≠ ((d + 1 : ℕ) : ℚ)⁻¹ := by
    simpa using hd.2
  have hdis : Disjoint (sums d) (addedLayer d) := by
    rw [Finset.disjoint_left]
    intro a ha htrans
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp htrans
    exact hd' _ ha _ hb (by ring)
  change (sums (d + 1)).card = 2 * (sums d).card
  rw [sums_succ_decomposition, Finset.card_union_of_disjoint hdis,
    addedLayer_card]
  simp only [S]
  omega

theorem independentDenominators_succ (N : ℕ) :
    independentDenominators (N + 1) =
      if IndependentDenominator (N + 1) then
        insert (N + 1) (independentDenominators N)
      else independentDenominators N := by
  classical
  unfold independentDenominators
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ N + 1),
    Finset.filter_insert]

theorem S_zero_eq_one : S 0 = 1 := by
  simp [S, sums, sumsOf]

theorem independent_power_le_S (N : ℕ) :
    2 ^ (independentDenominators N).card ≤ S N := by
  classical
  induction N with
  | zero => simp [independentDenominators, S_zero_eq_one]
  | succ N ih =>
      rw [independentDenominators_succ]
      split_ifs with h
      · have hnew : N + 1 ∉ independentDenominators N := by
          simp [independentDenominators]
        rw [Finset.card_insert_of_notMem hnew, pow_succ, S_exact_doubling h]
        simpa only [Nat.succ_sub_one, Nat.mul_comm] using
          Nat.mul_le_mul_right 2 ih
      · exact le_trans ih (S_mono_step N)

theorem independent_count_log_lower (N : ℕ) :
    ((independentDenominators N).card : ℝ) * Real.log 2 ≤ logS N := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (independentDenominators N).card := by positivity
  have hineq : (2 : ℝ) ^ (independentDenominators N).card ≤ (S N : ℝ) := by
    exact_mod_cast independent_power_le_S N
  have hlog := Real.log_le_log hpow hineq
  simpa [logS, Real.log_pow] using hlog

end Erdos320
end


-- Adapted from Erdos320.LogProduct.
section
/- Elementary stopped-logarithm lemmas, developed for this project. -/

namespace Erdos320

private theorem log_gt_three {x : ℝ} (hx : Real.exp 3 < x) :
    3 < Real.log x := by
  have := Real.log_lt_log (Real.exp_pos 3) hx
  simpa using this

theorem stoppedProduct_eq_one {x : ℝ} (hx : x ≤ Real.exp 3) (k : ℕ) :
    stoppedProduct k x = 1 := by
  cases k with
  | zero => rfl
  | succ k => simp [stoppedProduct, hx]

theorem one_le_stoppedProduct (k : ℕ) (x : ℝ) :
    1 ≤ stoppedProduct k x := by
  induction k generalizing x with
  | zero => simp [stoppedProduct]
  | succ k ih =>
      by_cases hx : x ≤ Real.exp 3
      · simp [stoppedProduct, hx]
      · have hlog : 1 ≤ Real.log x := le_of_lt (lt_trans (by norm_num) (log_gt_three (lt_of_not_ge hx)))
        simp only [stoppedProduct, if_neg hx]
        exact one_le_mul_of_one_le_of_one_le hlog (ih _)

theorem stoppedProduct_pos (k : ℕ) (x : ℝ) :
    0 < stoppedProduct k x := lt_of_lt_of_le zero_lt_one (one_le_stoppedProduct k x)

theorem stoppedProduct_mono_height {a b : ℕ} (hab : a ≤ b) (x : ℝ) :
    stoppedProduct a x ≤ stoppedProduct b x := by
  have hstep : ∀ k : ℕ, ∀ y : ℝ, stoppedProduct k y ≤ stoppedProduct (k + 1) y := by
    intro k
    induction k with
    | zero => intro y; simpa [stoppedProduct] using one_le_stoppedProduct 1 y
    | succ k ih =>
        intro y
        by_cases hy : y ≤ Real.exp 3
        · simp [stoppedProduct, hy]
        · simp only [stoppedProduct, if_neg hy]
          exact mul_le_mul_of_nonneg_left (ih _) (le_of_lt (lt_trans (by norm_num) (log_gt_three (lt_of_not_ge hy))))
  exact (monotone_nat_of_le_succ (fun k => hstep k x)) hab

theorem stoppedProduct_monotone (k : ℕ) : Monotone (stoppedProduct k) := by
  induction k with
  | zero => intro x y hxy; simp [stoppedProduct]
  | succ k ih =>
      intro x y hxy
      by_cases hx : x ≤ Real.exp 3
      · rw [stoppedProduct_eq_one hx]
        exact one_le_stoppedProduct _ _
      · have hx' : Real.exp 3 < x := lt_of_not_ge hx
        have hy : ¬y ≤ Real.exp 3 := not_le.mpr (lt_of_lt_of_le hx' hxy)
        have hx0 : 0 < x := lt_trans (Real.exp_pos 3) hx'
        have hlogs : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
        simp only [stoppedProduct, if_neg hx, if_neg hy]
        exact mul_le_mul hlogs (ih hlogs) (le_of_lt (stoppedProduct_pos _ _))
          (le_of_lt (lt_trans (by norm_num) (log_gt_three (lt_of_not_ge hy))))

/-- The stopped logarithmic map fixes every argument at or below the threshold. -/
noncomputable def logStep (x : ℝ) : ℝ :=
  if x ≤ Real.exp 3 then x else Real.log x

noncomputable def logOrbit : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => logOrbit k (logStep x)

theorem logOrbit_of_small {x : ℝ} (hx : x ≤ Real.exp 3) (k : ℕ) :
    logOrbit k x = x := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [logOrbit, logStep, hx] using ih

theorem active_orbit_requires_large_input (k : ℕ) (x : ℝ)
    (hactive : Real.exp 3 < logOrbit k x) :
    Real.exp 3 + (k : ℝ) < x := by
  induction k generalizing x with
  | zero => simpa [logOrbit] using hactive
  | succ k ih =>
      by_cases hx : x ≤ Real.exp 3
      · rw [logOrbit_of_small hx] at hactive
        exact (not_lt_of_ge hx hactive).elim
      · have hx' : Real.exp 3 < x := lt_of_not_ge hx
        have hnext : Real.exp 3 < logOrbit k (Real.log x) := by
          simpa [logOrbit, logStep, hx] using hactive
        have hlarge := ih _ hnext
        have hdrop := Real.log_le_sub_one_of_pos (lt_trans (Real.exp_pos 3) hx')
        push_cast
        linarith

theorem logOrbit_stops {k : ℕ} {x : ℝ}
    (hx : x ≤ Real.exp 3 + (k : ℝ)) :
    logOrbit k x ≤ Real.exp 3 := by
  by_contra hn
  exact (not_lt_of_ge hx) (active_orbit_requires_large_input k x (lt_of_not_ge hn))

theorem stoppedProduct_stable {k : ℕ} {x : ℝ}
    (hstop : logOrbit k x ≤ Real.exp 3) :
    ∀ l : ℕ, k ≤ l → stoppedProduct l x = stoppedProduct k x := by
  induction k generalizing x with
  | zero =>
      intro l hl
      have hx : x ≤ Real.exp 3 := hstop
      simp [stoppedProduct_eq_one hx]
  | succ k ih =>
      intro l hl
      by_cases hx : x ≤ Real.exp 3
      · simp [stoppedProduct_eq_one hx]
      · have hstop' : logOrbit k (Real.log x) ≤ Real.exp 3 := by
          simpa [logOrbit, logStep, hx] using hstop
        cases l with
        | zero => omega
        | succ l =>
            simp only [stoppedProduct, if_neg hx]
            rw [ih hstop' l (by omega)]

theorem stoppedProduct_stable_of_input_le {k : ℕ} {x : ℝ}
    (hx : x ≤ Real.exp 3 + (k : ℝ)) {l : ℕ} (hkl : k ≤ l) :
    stoppedProduct l x = stoppedProduct k x :=
  stoppedProduct_stable (logOrbit_stops hx) l hkl

theorem loglog_le_nat {N : ℕ} (hN : 2 ≤ N) :
    Real.log (Real.log (N : ℝ)) ≤ (N : ℝ) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hNR
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hfirst := Real.log_le_sub_one_of_pos hN0
  have hsecond := Real.log_le_sub_one_of_pos hlog
  linarith

theorem stoppedProduct_stable_at_nat {N k : ℕ} (hN : 2 ≤ N) (hNk : N ≤ k) :
    stoppedProduct k (Real.log (Real.log (N : ℝ))) =
      stoppedProduct N (Real.log (Real.log (N : ℝ))) := by
  apply stoppedProduct_stable_of_input_le _ hNk
  have := loglog_le_nat hN
  have := Real.exp_pos (3 : ℝ)
  linarith

/-- The one-step scale comparison at any smaller integer argument. -/
theorem log_factor_product_comparison {n q : ℕ} (hq : 2 ≤ q) (hqn : q < n)
    (harg : Real.log (Real.log (q : ℝ)) ≤
      Real.log (Real.log (Real.log (n : ℝ))))
    (hactive : Real.exp 3 < Real.log (Real.log (n : ℝ))) :
    Real.log (Real.log (Real.log (n : ℝ))) *
        stoppedProduct q (Real.log (Real.log (q : ℝ))) ≤
      stoppedProduct n (Real.log (Real.log (n : ℝ))) := by
  have hqheight : q ≤ n - 1 := by omega
  have hP := stoppedProduct_monotone q harg
  have hH := stoppedProduct_mono_height hqheight
    (Real.log (Real.log (Real.log (n : ℝ))))
  have hlog : 0 ≤ Real.log (Real.log (Real.log (n : ℝ))) :=
    le_of_lt (lt_trans (by norm_num) (log_gt_three hactive))
  have hn : n = (n - 1) + 1 := by omega
  have hrec : stoppedProduct n (Real.log (Real.log (n : ℝ))) =
      Real.log (Real.log (Real.log (n : ℝ))) *
        stoppedProduct (n - 1) (Real.log (Real.log (Real.log (n : ℝ)))) := by
    have hh := congrArg (fun j : ℕ =>
      stoppedProduct j (Real.log (Real.log (n : ℝ)))) hn
    rw [stoppedProduct, if_neg (not_le.mpr hactive)] at hh
    exact hh
  rw [hrec]
  exact mul_le_mul_of_nonneg_left (hP.trans hH) hlog

theorem log_factor_product_of_le_log {n q : ℕ} (hn : 2 ≤ n) (hq : 2 ≤ q)
    (hqn : (q : ℝ) ≤ Real.log (n : ℝ))
    (hactive : Real.exp 3 < Real.log (Real.log (n : ℝ))) :
    Real.log (Real.log (Real.log (n : ℝ))) *
        stoppedProduct q (Real.log (Real.log (q : ℝ))) ≤
      stoppedProduct n (Real.log (Real.log (n : ℝ))) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hn0 : (0 : ℝ) < n := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hsmall := Real.log_le_sub_one_of_pos hn0
  have hqnNat : q < n := by
    have : (q : ℝ) < n := by linarith
    exact_mod_cast this
  apply log_factor_product_comparison hq hqnNat _ hactive
  have hfirst := Real.log_le_log hq0 hqn
  exact Real.log_le_log (Real.log_pos (by linarith)) hfirst

end Erdos320
end


-- Adapted from Erdos320.LogIntegral.
section
/- Original elementary power-comparison tools for the lower renewal argument. -/

namespace Erdos320

noncomputable def iterLog : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => Real.log (iterLog k x)

noncomputable def logFactors (k : ℕ) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.range k, iterLog (j + 1) x

theorem log_lower_near_one {a : ℝ} (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1) :
    -2 * (1 - a) ≤ Real.log a := by
  have ha₀ : 0 < a := by linarith
  have h := Real.one_sub_inv_le_log_of_pos ha₀
  have hi : -2 * (1 - a) ≤ 1 - a⁻¹ := by
    apply (mul_le_mul_iff_of_pos_right ha₀).mp
    have hcancel : a⁻¹ * a = 1 := inv_mul_cancel₀ ha₀.ne'
    nlinarith [mul_nonneg (show 0 ≤ 1 - a by linarith)
      (show 0 ≤ 2 * a - 1 by linarith)]
  exact hi.trans h

theorem log_mul_lower_scaled {a u : ℝ}
    (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1)
    (hu : 0 < u) (hlu : 2 ≤ Real.log u) :
    a * Real.log u ≤ Real.log (a * u) := by
  have ha₀ : 0 < a := by linarith
  rw [Real.log_mul ha₀.ne' hu.ne']
  have haLog := log_lower_near_one ha ha₁
  nlinarith [mul_nonneg (show 0 ≤ 1 - a by linarith)
    (show 0 ≤ Real.log u - 2 by linarith)]

theorem iterLog_power_lower {k : ℕ} {x a : ℝ}
    (hx : 0 < x) (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1)
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j x) :
    ∀ j : ℕ, 1 ≤ j → j ≤ k →
      a * iterLog j x ≤ iterLog j (x ^ a) := by
  intro j hj hjk
  induction j with
  | zero => omega
  | succ j ih =>
      cases j with
      | zero =>
          simp only [iterLog]
          rw [Real.log_rpow hx]
      | succ j =>
          have hprev : a * iterLog (j + 1) x ≤ iterLog (j + 1) (x ^ a) :=
            ih (by omega) (by omega)
          have hu : 0 < iterLog (j + 1) x :=
            lt_of_lt_of_le (Real.exp_pos 2) (hlogs (j + 1) (by omega) (by omega))
          have ha₀ : 0 < a := by linarith
          have hprod : 0 < a * iterLog (j + 1) x := mul_pos ha₀ hu
          have hnext : 2 ≤ Real.log (iterLog (j + 1) x) := by
            have he : (2 : ℝ) ≤ Real.exp 2 := by
              have := Real.add_one_le_exp (2 : ℝ)
              linarith
            exact he.trans (hlogs (j + 2) (by omega) (by omega))
          calc
            a * iterLog (j + 2) x = a * Real.log (iterLog (j + 1) x) := rfl
            _ ≤ Real.log (a * iterLog (j + 1) x) :=
              log_mul_lower_scaled ha ha₁ hu hnext
            _ ≤ Real.log (iterLog (j + 1) (x ^ a)) := Real.log_le_log hprod hprev
            _ = iterLog (j + 2) (x ^ a) := rfl

theorem logFactors_power_lower {k : ℕ} {x a : ℝ}
    (hx : 0 < x) (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1)
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j x) :
    a ^ k * logFactors k x ≤ logFactors k (x ^ a) := by
  have ha₀ : 0 ≤ a := by linarith
  have hnonneg : ∀ j ∈ Finset.range k, 0 ≤ a * iterLog (j + 1) x := by
    intro j hj
    exact mul_nonneg ha₀ (le_trans (le_of_lt (Real.exp_pos 2))
      (hlogs (j + 1) (by omega) (by have := Finset.mem_range.mp hj; omega)))
  have hp := Finset.prod_le_prod hnonneg (fun j hj =>
    iterLog_power_lower hx ha ha₁ hlogs (j + 1) (by omega)
      (by have := Finset.mem_range.mp hj; omega))
  simpa [logFactors, Finset.prod_mul_distrib] using hp

theorem iterLog_mono_of_positive {k : ℕ} {x y : ℝ}
    (hxy : x ≤ y) (hx : ∀ j : ℕ, j < k → 0 < iterLog j x) :
    iterLog k x ≤ iterLog k y := by
  induction k with
  | zero => exact hxy
  | succ k ih =>
      exact Real.log_le_log (hx k (by omega))
        (ih (fun j hj => hx j (by omega)))

theorem iterLog_power_pos {k : ℕ} {x a : ℝ}
    (hx : 0 < x) (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1)
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j x) :
    ∀ j : ℕ, j ≤ k → 0 < iterLog j (x ^ a) := by
  intro j hj
  cases j with
  | zero => exact Real.rpow_pos_of_pos hx _
  | succ j =>
      have ha₀ : 0 < a := by linarith
      have hlarge : 0 < iterLog (j + 1) x :=
        lt_of_lt_of_le (Real.exp_pos 2) (hlogs (j + 1) (by omega) hj)
      exact lt_of_lt_of_le (mul_pos ha₀ hlarge)
        (iterLog_power_lower hx ha ha₁ hlogs (j + 1) (by omega) hj)

theorem logFactors_monotone_above_power {k : ℕ} {x a y : ℝ}
    (hx : 0 < x) (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1)
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j x)
    (hy : x ^ a ≤ y) :
    logFactors k (x ^ a) ≤ logFactors k y := by
  apply Finset.prod_le_prod
  · intro j hj
    exact (iterLog_power_pos hx ha ha₁ hlogs (j + 1)
      (by have := Finset.mem_range.mp hj; omega)).le
  · intro j hj
    apply iterLog_mono_of_positive hy
    intro i hi
    exact iterLog_power_pos hx ha ha₁ hlogs i
      (by have := Finset.mem_range.mp hj; omega)

theorem iterLog_continuousOn {k : ℕ} {x : ℝ}
    (hx : ∀ j : ℕ, j < k → 0 < iterLog j x) :
    ContinuousOn (iterLog k) (Set.Ici x) := by
  induction k with
  | zero =>
      change ContinuousOn id (Set.Ici x)
      exact continuousOn_id
  | succ k ih =>
      have hsub : ∀ j : ℕ, j < k → 0 < iterLog j x :=
        fun j hj => hx j (by omega)
      apply (ih hsub).log
      intro y hy
      exact ne_of_gt ((hx k (by omega)).trans_le (iterLog_mono_of_positive hy hsub))

theorem logFactors_continuousOn {k : ℕ} {x : ℝ}
    (hx : ∀ j : ℕ, j < k → 0 < iterLog j x) :
    ContinuousOn (logFactors k) (Set.Ici x) := by
  unfold logFactors
  apply continuousOn_finsetProd
  intro j hj
  apply iterLog_continuousOn
  intro i hi
  exact hx i (by have := Finset.mem_range.mp hj; omega)

theorem integral_logFactors_power_lower {k : ℕ} {x a : ℝ}
    (hx : 0 < x) (ha : (1 : ℝ) / 2 ≤ a) (ha₁ : a ≤ 1)
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j x)
    (horder : x ^ a ≤ x) :
    (x - x ^ a) * a ^ k * logFactors k x ≤
      ∫ w in x ^ a..x, logFactors k w := by
  have hc : ContinuousOn (logFactors k) (Set.Icc (x ^ a) x) :=
    (logFactors_continuousOn (fun j hj =>
      iterLog_power_pos hx ha ha₁ hlogs j (by omega))).mono
        (fun _ hy => hy.1)
  have hi : IntervalIntegrable (logFactors k) MeasureTheory.volume (x ^ a) x :=
    hc.intervalIntegrable_of_Icc horder
  have hpoint : ∀ w ∈ Set.Icc (x ^ a) x,
      a ^ k * logFactors k x ≤ logFactors k w := by
    intro w hw
    exact (logFactors_power_lower hx ha ha₁ hlogs).trans
      (logFactors_monotone_above_power hx ha ha₁ hlogs hw.1)
  have h := intervalIntegral.integral_mono_on horder
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => a ^ k * logFactors k x) MeasureTheory.volume (x ^ a) x)
    hi hpoint
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_assoc] using h

end Erdos320
end


-- Adapted from Erdos320.UpperFinite.Combinatorics.
section
/-
Finite covering bounds used in the prime-block argument of Luo, Yang, and Zhu,
building on Bleicher and Erdős. The Lean proofs in this file were developed
independently for the project commissioned by Riley Sturgill.
-/

namespace Erdos320

theorem zero_mem_sumsOf (A : Finset ℕ) : (0 : ℚ) ∈ sumsOf A := by
  exact Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (by simp), by simp⟩

theorem card_sumsOf_pos (A : Finset ℕ) : 0 < (sumsOf A).card :=
  Finset.card_pos.mpr ⟨0, zero_mem_sumsOf A⟩

theorem sumsOf_mono {A B : Finset ℕ} (h : A ⊆ B) : sumsOf A ⊆ sumsOf B := by
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨C, hC, rfl⟩
  exact Finset.mem_image.mpr ⟨C,
    Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hC).trans h), rfl⟩

/-- Overlapping sets are allowed: allocate an intersection to the first set. -/
theorem card_sumsOf_union_le (A B : Finset ℕ) :
    (sumsOf (A ∪ B)).card ≤ (sumsOf A).card * (sumsOf B).card := by
  apply le_trans (Finset.card_le_card ?_)
    (Finset.card_image₂_le (fun x y : ℚ => x + y) (sumsOf A) (sumsOf B))
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨C, hC, rfl⟩
  have hCA : C ∩ A ⊆ A := Finset.inter_subset_right
  have hCB : C \ A ⊆ B := by
    intro n hn
    rcases Finset.mem_sdiff.mp hn with ⟨hnC, hnA⟩
    exact (Finset.mem_union.mp ((Finset.mem_powerset.mp hC) hnC)).resolve_left hnA
  apply Finset.mem_image₂.mpr
  refine ⟨∑ n ∈ C ∩ A, (n : ℚ)⁻¹, ?_, ∑ n ∈ C \ A, (n : ℚ)⁻¹, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨C ∩ A, Finset.mem_powerset.mpr hCA, rfl⟩
  · exact Finset.mem_image.mpr ⟨C \ A, Finset.mem_powerset.mpr hCB, rfl⟩
  · exact Finset.sum_inter_add_sum_sdiff C A (fun n => (n : ℚ)⁻¹)

theorem card_sumsOf_biUnion_le {ι : Type*} (P : Finset ι) (B : ι → Finset ℕ) :
    (sumsOf (P.biUnion B)).card ≤ ∏ p ∈ P, (sumsOf (B p)).card := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [sumsOf]
  | @insert p P hp ih =>
      rw [Finset.biUnion_insert, Finset.prod_insert hp]
      exact (card_sumsOf_union_le _ _).trans (Nat.mul_le_mul_left _ ih)

theorem card_sumsOf_cover_le {ι : Type*} (P : Finset ι) (B : ι → Finset ℕ)
    (A Z : Finset ℕ) (hcover : A ⊆ Z ∪ P.biUnion B) :
    (sumsOf A).card ≤ (sumsOf Z).card * ∏ p ∈ P, (sumsOf (B p)).card := by
  exact (Finset.card_le_card (sumsOf_mono hcover)).trans
    ((card_sumsOf_union_le _ _).trans
      (Nat.mul_le_mul_left _ (card_sumsOf_biUnion_le P B)))

/-- The reciprocal values from a dilated denominator set are scaled by `1/p`. -/
theorem sumsOf_mul_image (A : Finset ℕ) {p : ℕ} (hp : p ≠ 0) :
    sumsOf (A.image (fun n => p * n)) =
      (sumsOf A).image (fun q => (p : ℚ)⁻¹ * q) := by
  simp only [sumsOf, Finset.powerset_image, Finset.image_image]
  apply Finset.image_congr
  intro B hB
  change (∑ n ∈ B.image (fun n => p * n), (n : ℚ)⁻¹) =
    (p : ℚ)⁻¹ * ∑ n ∈ B, (n : ℚ)⁻¹
  rw [Finset.sum_image]
  · simp only [Nat.cast_mul, mul_inv_rev, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    exact mul_comm _ _
  · intro a ha b hb hab
    exact mul_left_cancel₀ hp hab

theorem card_sumsOf_mul_image (A : Finset ℕ) {p : ℕ} (hp : p ≠ 0) :
    (sumsOf (A.image (fun n => p * n))).card = (sumsOf A).card := by
  rw [sumsOf_mul_image A hp]
  apply Finset.card_image_of_injective
  apply mul_right_injective₀
  exact inv_ne_zero (by exact_mod_cast hp)

/-- Denominators at most `N` divisible by `p`. -/
def primeBlock (N p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => p ∣ n)

theorem primeBlock_eq_image (N : ℕ) {p : ℕ} (hp : 0 < p) :
    primeBlock N p = (Finset.Icc 1 (N / p)).image (fun n => p * n) := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hnI, m, rfl⟩
    rcases Finset.mem_Icc.mp hnI with ⟨hlo, hhi⟩
    have hm : 1 ≤ m := by
      by_contra h
      have hm0 : m = 0 := by omega
      simp [hm0] at hlo
    exact Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr
      ⟨hm, (Nat.le_div_iff_mul_le hp).mpr (by simpa [Nat.mul_comm] using hhi)⟩, rfl⟩
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
    rcases Finset.mem_Icc.mp hm with ⟨hmlo, hmhi⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right p m⟩
    · exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne' (by omega))
    · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hmhi

theorem card_sumsOf_primeBlock (N : ℕ) {p : ℕ} (hp : 0 < p) :
    (sumsOf (primeBlock N p)).card = S (N / p) := by
  rw [primeBlock_eq_image N hp, card_sumsOf_mul_image _ hp.ne']
  rfl

/-- Residual set after any chosen positive divisor blocks have been removed. -/
def residualBlock (N : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 N) \ P.biUnion (primeBlock N)

theorem finite_block_product_bound (N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) :
    S N ≤ (sumsOf (residualBlock N P)).card * ∏ p ∈ P, S (N / p) := by
  have hcover : Finset.Icc 1 N ⊆
      residualBlock N P ∪ P.biUnion (primeBlock N) := by
    intro n hn
    by_cases hm : n ∈ P.biUnion (primeBlock N)
    · exact Finset.mem_union_right _ hm
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hn, hm⟩)
  have h := card_sumsOf_cover_le P (primeBlock N) (Finset.Icc 1 N)
    (residualBlock N P) hcover
  change S N ≤ _ at h
  have heq : (∏ p ∈ P, (sumsOf (primeBlock N p)).card) =
      ∏ p ∈ P, S (N / p) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact card_sumsOf_primeBlock N (hP p hp)
  rw [heq] at h
  exact h

theorem finite_block_log_bound (N : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) :
    logS N ≤ Real.log ((sumsOf (residualBlock N P)).card : ℝ) +
      ∑ p ∈ P, logS (N / p) := by
  have hcount := finite_block_product_bound N P hP
  have hSpos : (0 : ℝ) < S N := by
    exact_mod_cast card_sumsOf_pos (Finset.Icc 1 N)
  have hzpos : (0 : ℝ) < (sumsOf (residualBlock N P)).card := by
    exact_mod_cast card_sumsOf_pos (residualBlock N P)
  have hpPos : ∀ p ∈ P, (0 : ℝ) < S (N / p) := by
    intro p hp
    exact_mod_cast card_sumsOf_pos (Finset.Icc 1 (N / p))
  have hprodPos : 0 < ∏ p ∈ P, (S (N / p) : ℝ) := Finset.prod_pos hpPos
  have hreal : (S N : ℝ) ≤ (sumsOf (residualBlock N P)).card *
      ∏ p ∈ P, (S (N / p) : ℝ) := by exact_mod_cast hcount
  have hlog := Real.log_le_log hSpos hreal
  rw [Real.log_mul hzpos.ne' hprodPos.ne', Real.log_prod (fun p hp => (hpPos p hp).ne')] at hlog
  exact hlog

end Erdos320
end


-- Adapted from Erdos320.UpperAnalyticPNT.
section
/-
Original consequence of the Apache-licensed upstream quantitative prime number
theorem. The theorem imported here is `MediumPNT`; no analytic input is added as
an axiom or an unproved proposition.
-/

namespace Erdos320

/-- The upstream stretched-exponential PNT error is eventually bounded by any
prescribed inverse power of the logarithm, with coefficient one. -/
theorem eventual_psi_error_le_log_power (k : ℕ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      |Chebyshev.psi x - x| ≤ x / Real.log x ^ k := by
  obtain ⟨c, hc, hpnt⟩ := MediumPNT
  obtain ⟨C, _hC, hbound⟩ := hpnt.exists_pos
  have hsmall := eventual_exp_neg_log_rpow_le_inv_log_pow k C c ((1 : ℝ) / 10)
    hc (by norm_num)
  filter_upwards [hbound.bound, hsmall, Filter.eventually_gt_atTop (1 : ℝ)]
    with x hx hsmallx hx₁
  have hx₀ : 0 ≤ x := by linarith
  have he : 0 ≤ Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) := (Real.exp_pos _).le
  have hx' : |Chebyshev.psi x - x| ≤
      C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
    simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hx₀, abs_of_nonneg he] using hx
  calc
    |Chebyshev.psi x - x|
        ≤ C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := hx'
    _ = x * (C * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by ring
    _ ≤ x * (1 / Real.log x ^ k) := mul_le_mul_of_nonneg_left hsmallx hx₀
    _ = x / Real.log x ^ k := by ring

end Erdos320
end


-- Adapted from Erdos320.UpperAnalyticUniform.
section
/-
Original uniform prime-interval normalization. The endpoint hypotheses are the
concrete estimates supplied by the quantitative PNT, rather than a prime-counting
axiom. Their consequence has leading coefficient one plus a vanishing error.
-/

namespace Erdos320

theorem prime_interval_normalized_of_endpoint_errors
    (P : Finset ℕ) (X L m u : ℝ)
    (hX : 0 < X) (hL : 0 < L) (hm : 0 < m)
    (hu : 0 ≤ u) (hu_half : u ≤ L / 2)
    (hlogₐ : L - u ≤ Real.log (X / (m + 1)))
    (hlog_b : L / 2 ≤ Real.log (X / m))
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X / (m + 1) < (p : ℝ) ∧ (p : ℝ) ≤ X / m)
    (hₐ : |Chebyshev.psi (X / (m + 1)) - X / (m + 1)| ≤
      (X / (m + 1)) / Real.log (X / (m + 1)) ^ 4)
    (h_b : |Chebyshev.psi (X / m) - X / m| ≤
      (X / m) / Real.log (X / m) ^ 4) :
    (L / X) * (P.card : ℝ) ≤
      (1 + 2 * (u / L) + 64 * (m + 1) / L ^ 4) / (m * (m + 1)) := by
  have hm₁ : 0 < m + 1 := by linarith
  have ha₀ : 0 < X / (m + 1) := div_pos hX hm₁
  have hb₀ : 0 < X / m := div_pos hX hm
  have hab : X / (m + 1) ≤ X / m :=
    div_le_div_of_nonneg_left hX.le hm (by linarith)
  have hla : L / 2 ≤ Real.log (X / (m + 1)) := by linarith
  have hhalf : 0 < L / 2 := by positivity
  have hea : (X / (m + 1)) / Real.log (X / (m + 1)) ^ 4 ≤
      16 * (X / m) / L ^ 4 := by
    calc
      _ ≤ (X / m) / Real.log (X / (m + 1)) ^ 4 :=
        div_le_div_of_nonneg_right hab (pow_nonneg (by linarith) _)
      _ ≤ (X / m) / (L / 2) ^ 4 :=
        div_le_div_of_nonneg_left hb₀.le (pow_pos hhalf _)
          (pow_le_pow_left₀ hhalf.le hla 4)
      _ = 16 * (X / m) / L ^ 4 := by ring
  have heb : (X / m) / Real.log (X / m) ^ 4 ≤
      16 * (X / m) / L ^ 4 := by
    calc
      _ ≤ (X / m) / (L / 2) ^ 4 :=
        div_le_div_of_nonneg_left hb₀.le (pow_pos hhalf _)
          (pow_le_pow_left₀ hhalf.le hlog_b 4)
      _ = 16 * (X / m) / L ^ 4 := by ring
  have hmass := prime_card_mul_log_le_psi_sub P (X / (m + 1)) (X / m) ha₀ hab hP
  have hpa := (neg_le_abs (Chebyshev.psi (X / (m + 1)) - X / (m + 1))).trans hₐ
  have hpb := (le_abs_self (Chebyshev.psi (X / m) - X / m)).trans h_b
  have hcard₀ : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hmass' : (P.card : ℝ) * (L - u) ≤
      X / m - X / (m + 1) + 32 * (X / m) / L ^ 4 := by
    have hlogmul := mul_le_mul_of_nonneg_left hlogₐ hcard₀
    calc
      _ ≤ (P.card : ℝ) * Real.log (X / (m + 1)) := hlogmul
      _ ≤ Chebyshev.psi (X / m) - Chebyshev.psi (X / (m + 1)) := hmass
      _ ≤ X / m - X / (m + 1) +
          ((X / (m + 1)) / Real.log (X / (m + 1)) ^ 4 +
            (X / m) / Real.log (X / m) ^ 4) := by linarith only [hpa, hpb]
      _ ≤ X / m - X / (m + 1) +
          (16 * (X / m) / L ^ 4 + 16 * (X / m) / L ^ 4) :=
        add_le_add le_rfl (add_le_add hea heb)
      _ = _ := by ring
  let H : ℝ := X / (m * (m + 1))
  let z : ℝ := u / L
  let e : ℝ := 32 * (m + 1) / L ^ 4
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hz : 0 ≤ z := div_nonneg hu hL.le
  have hz_half : z ≤ 1 / 2 := by
    dsimp [z]
    apply (div_le_iff₀ hL).mpr
    linarith
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hleft : (P.card : ℝ) * L * (1 - z) = (P.card : ℝ) * (L - u) := by
    dsimp [z]
    field_simp
  have hright : H * (1 + e) =
      X / m - X / (m + 1) + 32 * (X / m) / L ^ 4 := by
    dsimp [H, e]
    field_simp
    ring
  have hnormalized : (P.card : ℝ) * L ≤ H * (1 + 2 * z + 2 * e) :=
    denominator_loss_normalization hH hz hz_half he (by rw [hleft, hright]; exact hmass')
  have hdiv : ((P.card : ℝ) * L) / X ≤
      (1 + 2 * z + 2 * e) / (m * (m + 1)) := by
    apply (div_le_iff₀ hX).mpr
    calc
      _ ≤ H * (1 + 2 * z + 2 * e) := hnormalized
      _ = _ := by dsimp [H]; ring
  calc
    (L / X) * (P.card : ℝ) = ((P.card : ℝ) * L) / X := by ring
    _ ≤ (1 + 2 * z + 2 * e) / (m * (m + 1)) := hdiv
    _ = _ := by dsimp [z, e]; ring

/-- The preceding estimate is uniform for `m ≤ L`, with an error depending only
on `L,u`. -/
theorem prime_interval_normalized_uniform
    (P : Finset ℕ) (X L m u : ℝ)
    (hX : 0 < X) (hL : 1 ≤ L) (hm : 0 < m) (hmL : m ≤ L)
    (hu : 0 ≤ u) (hu_half : u ≤ L / 2)
    (hlogₐ : L - u ≤ Real.log (X / (m + 1)))
    (hlog_b : L / 2 ≤ Real.log (X / m))
    (hP : ∀ p ∈ P, Nat.Prime p ∧ X / (m + 1) < (p : ℝ) ∧ (p : ℝ) ≤ X / m)
    (hₐ : |Chebyshev.psi (X / (m + 1)) - X / (m + 1)| ≤
      (X / (m + 1)) / Real.log (X / (m + 1)) ^ 4)
    (h_b : |Chebyshev.psi (X / m) - X / m| ≤
      (X / m) / Real.log (X / m) ^ 4) :
    (L / X) * (P.card : ℝ) ≤
      (1 + (2 * (u / L) + 128 / L ^ 3)) / (m * (m + 1)) := by
  have hL₀ : 0 < L := by linarith
  have hterm : 64 * (m + 1) / L ^ 4 ≤ 128 / L ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hL₀ 4) (pow_pos hL₀ 3)).mpr
    have hm₂ : m + 1 ≤ 2 * L := by linarith
    have hpow : 0 ≤ L ^ 3 := (pow_pos hL₀ 3).le
    nlinarith only [mul_le_mul_of_nonneg_right hm₂ hpow]
  have h := prime_interval_normalized_of_endpoint_errors P X L m u hX hL₀ hm hu hu_half
    hlogₐ hlog_b hP hₐ h_b
  refine h.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ m * (m + 1))
  linarith

end Erdos320
end


-- Adapted from Erdos320.LowerArithmetic.
section
/-
Common denominators for the independently developed lower-bound construction.
The elementary fact that every prime is an independent denominator is included
as a base case, not as a claim to establish the full asymptotic lower bound.
-/

namespace Erdos320

/-- If every denominator divides `D`, the reduced denominator of the sum does
as well. Working with reduced rational denominators avoids choosing a signed
integer numerator for each subset sum. -/
theorem reciprocal_sum_den_dvd (A : Finset ℕ) (D : ℕ)
    (hpos : ∀ n ∈ A, 0 < n) (hdiv : ∀ n ∈ A, n ∣ D) :
    (∑ n ∈ A, (n : ℚ)⁻¹).den ∣ D := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert n A hn ih =>
      have hnpos : 0 < n := hpos n (by simp)
      have hndiv : n ∣ D := hdiv n (by simp)
      have hApos : ∀ a ∈ A, 0 < a := by
        intro a ha
        exact hpos a (by simp [ha])
      have hAdiv : ∀ a ∈ A, a ∣ D := by
        intro a ha
        exact hdiv a (by simp [ha])
      rw [Finset.sum_insert hn]
      apply dvd_trans (Rat.add_den_dvd_lcm _ _)
      exact Nat.lcm_dvd
        (by simpa [Rat.inv_natCast_den_of_pos hnpos] using hndiv)
        (ih hApos hAdiv)

/-- Every reciprocal subset sum from the first `N` denominators has a
reduced denominator dividing `N!`. -/
theorem sums_den_dvd_factorial {N : ℕ} {q : ℚ} (hq : q ∈ sums N) :
    q.den ∣ N.factorial := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hq
  have hsub : A ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp hA
  apply reciprocal_sum_den_dvd
  · intro n hn
    exact (Finset.mem_Icc.mp (hsub hn)).1
  · intro n hn
    have h := Finset.mem_Icc.mp (hsub hn)
    exact Nat.dvd_factorial h.1 h.2

theorem prime_independent {p : ℕ} (hp : Nat.Prime p) :
    IndependentDenominator p := by
  refine ⟨hp.pos, ?_⟩
  intro a ha b hb heq
  have haD := sums_den_dvd_factorial ha
  have hbD := sums_den_dvd_factorial hb
  have hd : (a - b).den ∣ (p - 1).factorial :=
    dvd_trans (Rat.sub_den_dvd_lcm _ _) (Nat.lcm_dvd haD hbD)
  rw [heq, Rat.inv_natCast_den_of_pos hp.pos] at hd
  have hple : p ≤ p - 1 := hp.dvd_factorial.mp hd
  have hpPos := hp.pos
  omega

theorem primes_in_independentDenominators {p N : ℕ}
    (hp : Nat.Prime p) (hpN : p ≤ N) :
    p ∈ independentDenominators N := by
  simp only [independentDenominators, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hp.one_lt.le, hpN⟩, prime_independent hp⟩

end Erdos320
end


-- Adapted from Erdos320.LogScale.
section
namespace Erdos320

open Filter

noncomputable def logIndex (n : ℕ) : ℕ := Nat.floor (Real.log (n : ℝ))

theorem log_nat_tendsto : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem loglog_nat_tendsto :
    Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp log_nat_tendsto

theorem logloglog_nat_tendsto :
    Tendsto (fun n : ℕ => Real.log (Real.log (Real.log (n : ℝ)))) atTop atTop :=
  Real.tendsto_log_atTop.comp loglog_nat_tendsto

theorem eventually_log_scale_conditions :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 2 ≤ logIndex n ∧
      (logIndex n : ℝ) ≤ Real.log (n : ℝ) ∧ logIndex n < n ∧
      Real.exp 3 < Real.log (Real.log (n : ℝ)) ∧
      2 ≤ Real.log (Real.log (Real.log (n : ℝ))) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    log_nat_tendsto.eventually (eventually_ge_atTop (2 : ℝ)),
    loglog_nat_tendsto.eventually (eventually_gt_atTop (Real.exp 3)),
    logloglog_nat_tendsto.eventually (eventually_ge_atTop (2 : ℝ))]
    with n hn hl hl₂ hl₃
  have hindex : 2 ≤ logIndex n := Nat.le_floor hl
  have hcast : (logIndex n : ℝ) ≤ Real.log (n : ℝ) :=
    Nat.floor_le (by linarith)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n by linarith)
  have hltR : (logIndex n : ℝ) < n := by linarith
  have hlt : logIndex n < n := by exact_mod_cast hltR
  exact ⟨hn, hindex, hcast, hlt, hl₂, hl₃⟩

theorem eventually_full_product_step :
    ∀ᶠ n : ℕ in atTop,
      Real.log (Real.log (Real.log (n : ℝ))) *
          stoppedProduct (logIndex n) (Real.log (Real.log (logIndex n : ℝ))) ≤
        stoppedProduct n (Real.log (Real.log (n : ℝ))) := by
  filter_upwards [eventually_log_scale_conditions] with n hn
  exact log_factor_product_of_le_log hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.2.1

end Erdos320
end


-- Adapted from Erdos320.Statement.
section
/- The manuscript's exact stopping convention and its formal correspondence. -/

namespace Erdos320

/-- Successive logarithmic factors strictly above `t`, with a finite height. -/
noncomputable def stoppedProductAt (t : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, x =>
      if x ≤ Real.exp t then 1
      else Real.log x * stoppedProductAt t k (Real.log x)

theorem stoppedProductAt_small (t : ℝ) (k : ℕ) {x : ℝ} (hx : x ≤ Real.exp t) :
    stoppedProductAt t k x = 1 := by
  cases k <;> simp [stoppedProductAt, hx]

theorem stoppedProductAt_three (k : ℕ) (x : ℝ) :
    stoppedProductAt 3 k x = stoppedProduct k x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [stoppedProductAt, stoppedProduct, ih]

theorem stopping_threshold_two_three (k : ℕ) (x : ℝ) :
    stoppedProductAt 3 k x ≤ stoppedProductAt 2 k x ∧
      stoppedProductAt 2 k x ≤ 3 * stoppedProductAt 3 k x := by
  induction k generalizing x with
  | zero => norm_num [stoppedProductAt]
  | succ k ih =>
      have he : Real.exp (2 : ℝ) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by norm_num)
      by_cases hx₂ : x ≤ Real.exp 2
      · have hx₃ := hx₂.trans he
        norm_num [stoppedProductAt, hx₂, hx₃]
      · have hx₀ : 0 < x := lt_trans (Real.exp_pos 2) (lt_of_not_ge hx₂)
        have hl₂ : 2 < Real.log x := by
          have := Real.log_lt_log (Real.exp_pos 2) (lt_of_not_ge hx₂)
          simpa using this
        by_cases hx₃ : x ≤ Real.exp 3
        · have hl₃ : Real.log x ≤ 3 := by
            have := Real.log_le_log hx₀ hx₃
            simpa using this
          have hsmall : Real.log x ≤ Real.exp 2 :=
            hl₃.trans (by have := Real.add_one_le_exp (2 : ℝ); linarith)
          simp only [stoppedProductAt, if_neg hx₂, if_pos hx₃,
            stoppedProductAt_small 2 k hsmall, mul_one, mul_one]
          constructor <;> linarith
        · obtain ⟨hlo, hup⟩ := ih (Real.log x)
          have hl₀ : 0 ≤ Real.log x := by linarith
          simp only [stoppedProductAt, if_neg hx₂, if_neg hx₃]
          refine ⟨mul_le_mul_of_nonneg_left hlo hl₀, ?_⟩
          calc
            _ ≤ Real.log x * (3 * stoppedProductAt 3 k (Real.log x)) :=
              mul_le_mul_of_nonneg_left hup hl₀
            _ = 3 * (Real.log x * stoppedProductAt 3 k (Real.log x)) := by ring

noncomputable def stoppedArgumentAt (t : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x =>
      if x ≤ Real.exp t then x else stoppedArgumentAt t k (Real.log x)

theorem stoppedArgumentAt_small (t : ℝ) (k : ℕ) {x : ℝ} (hx : x ≤ Real.exp t) :
    stoppedArgumentAt t k x = x := by
  cases k <;> simp [stoppedArgumentAt, hx]

theorem stoppedArgumentAt_active (t : ℝ) (k : ℕ) (x : ℝ)
    (hx : Real.exp t < stoppedArgumentAt t k x) : Real.exp t + (k : ℝ) < x := by
  induction k generalizing x with
  | zero => simpa [stoppedArgumentAt] using hx
  | succ k ih =>
      by_cases hsmall : x ≤ Real.exp t
      · rw [stoppedArgumentAt_small t (k + 1) hsmall] at hx
        exact (not_lt_of_ge hsmall hx).elim
      · have hx₀ : 0 < x := lt_trans (Real.exp_pos t) (lt_of_not_ge hsmall)
        have hnext : Real.exp t < stoppedArgumentAt t k (Real.log x) := by
          simpa [stoppedArgumentAt, hsmall] using hx
        have hh := ih _ hnext
        have hdrop := Real.log_le_sub_one_of_pos hx₀
        push_cast
        linarith

theorem stoppedProductAt_stable {t : ℝ} {k : ℕ} {x : ℝ}
    (hx : stoppedArgumentAt t k x ≤ Real.exp t) :
    ∀ l : ℕ, k ≤ l → stoppedProductAt t l x = stoppedProductAt t k x := by
  induction k generalizing x with
  | zero =>
      intro l hl
      have hs : x ≤ Real.exp t := hx
      rw [stoppedProductAt_small t l hs, stoppedProductAt_small t 0 hs]
  | succ k ih =>
      intro l hl
      by_cases hs : x ≤ Real.exp t
      · rw [stoppedProductAt_small t l hs, stoppedProductAt_small t (k + 1) hs]
      · have hnext : stoppedArgumentAt t k (Real.log x) ≤ Real.exp t := by
          simpa [stoppedArgumentAt, hs] using hx
        cases l with
        | zero => omega
        | succ l =>
            simp only [stoppedProductAt, if_neg hs]
            rw [ih hnext l (by omega)]

/-- This is the manuscript's `L₂(N)`: factors `log₃N, log₄N, ...` strictly
above two. The next theorem formally establishes that height `N` is sufficient. -/
noncomputable def fullLogProduct (N : ℕ) : ℝ :=
  stoppedProductAt 2 N (Real.log (Real.log (N : ℝ)))

theorem fullLogProduct_stable {N k : ℕ} (hN : 2 ≤ N) (hNk : N ≤ k) :
    stoppedProductAt 2 k (Real.log (Real.log (N : ℝ))) = fullLogProduct N := by
  have hstop : stoppedArgumentAt 2 N (Real.log (Real.log (N : ℝ))) ≤ Real.exp 2 := by
    by_contra hn
    have hlarge := stoppedArgumentAt_active 2 N _ (lt_of_not_ge hn)
    have hbound := loglog_le_nat hN
    have := Real.exp_pos (2 : ℝ)
    linarith
  exact stoppedProductAt_stable hstop k hNk

noncomputable def problemScale (N : ℕ) : ℝ :=
  ((N : ℝ) / Real.log N) * fullLogProduct N

theorem problemScale_comparison {N : ℕ} (hN : 2 ≤ N) :
    scale N ≤ problemScale N ∧ problemScale N ≤ 3 * scale N := by
  obtain ⟨hlo, hup⟩ := stopping_threshold_two_three N (Real.log (Real.log (N : ℝ)))
  rw [stoppedProductAt_three] at hlo hup
  have hpre : 0 ≤ (N : ℝ) / Real.log N := by
    apply div_nonneg (by positivity)
    exact (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).le
  refine ⟨mul_le_mul_of_nonneg_left hlo hpre, ?_⟩
  calc
    problemScale N ≤ ((N : ℝ) / Real.log N) *
        (3 * stoppedProduct N (Real.log (Real.log (N : ℝ)))) :=
      mul_le_mul_of_nonneg_left hup hpre
    _ = 3 * scale N := by dsimp [scale]; ring

end Erdos320
end


-- Adapted from Erdos320.LowerAnalytic.Cutoffs.
section
namespace Erdos320.LowerAnalytic

/-- The depth grows with the input. Squaring reserves room for all losses. -/
noncomputable def cutoff (H : ℝ) : ℕ → ℝ
  | 0 => H
  | k + 1 => Real.exp ((cutoff H k) ^ 2)

theorem cutoff_ge_base {H : ℝ} (hH : 1 ≤ H) (k : ℕ) : H ≤ cutoff H k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have ha : 1 ≤ cutoff H k := hH.trans ih
      have hexp := Real.add_one_le_exp ((cutoff H k) ^ 2)
      change H ≤ Real.exp ((cutoff H k) ^ 2)
      nlinarith

theorem cutoff_pos {H : ℝ} (hH : 1 ≤ H) (k : ℕ) : 0 < cutoff H k :=
  lt_of_lt_of_le (by linarith) (cutoff_ge_base hH k)

theorem cutoff_add_index_le {H : ℝ} (hH : 1 ≤ H) (k : ℕ) :
    H + k ≤ cutoff H k := by
  induction k with
  | zero => simp [cutoff]
  | succ k ih =>
      have ha : 1 ≤ cutoff H k := hH.trans (cutoff_ge_base hH k)
      have hexp := Real.add_one_le_exp ((cutoff H k) ^ 2)
      change H + (k + 1 : ℕ) ≤ Real.exp ((cutoff H k) ^ 2)
      push_cast
      nlinarith

theorem cutoff_step_log_growth {H : ℝ} (hH : 16 ≤ H) (k : ℕ) :
    16 * Real.log (cutoff H k) ≤ Real.log (cutoff H (k + 1)) := by
  have hH1 : 1 ≤ H := by linarith
  have ha : 16 ≤ cutoff H k := hH.trans (cutoff_ge_base hH1 k)
  have hlog := Real.log_le_sub_one_of_pos (cutoff_pos hH1 k)
  simp only [cutoff, Real.log_exp]
  nlinarith

/-- The geometric epsilon is tiny, but the threshold grows faster. -/
theorem epsilon_sq_log_cutoff_ge_one {H : ℝ} (hH : 16 ≤ H)
    (hlogH : 4096 ≤ Real.log H) (k : ℕ) :
    1 ≤ epsilon k ^ 2 * Real.log (cutoff H k) := by
  induction k with
  | zero => norm_num [epsilon, cutoff]; nlinarith
  | succ k ih =>
      have hgrowth := cutoff_step_log_growth hH k
      have hmul := mul_le_mul_of_nonneg_left hgrowth (sq_nonneg (epsilon (k + 1)))
      calc
        1 ≤ epsilon k ^ 2 * Real.log (cutoff H k) := ih
        _ = epsilon (k + 1) ^ 2 * (16 * Real.log (cutoff H k)) := by
          rw [epsilon_succ]
          ring
        _ ≤ _ := hmul

theorem iterLog_shift (k : ℕ) (x : ℝ) :
    iterLog (k + 1) x = iterLog k (Real.log x) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [iterLog] using congrArg Real.log ih

/-- Every retained ordinary logarithm stays in a positive fixed range. -/
theorem iterLog_ge_base_of_cutoff {H : ℝ} (hH : 1 ≤ H) (k : ℕ) :
    ∀ x : ℝ, cutoff H k ≤ x → ∀ j : ℕ, j ≤ k → H ≤ iterLog j x := by
  induction k with
  | zero =>
      intro x hx j hj
      have hj0 : j = 0 := by omega
      simpa [hj0, iterLog, cutoff] using hx
  | succ k ih =>
      intro x hx j hj
      cases j with
      | zero =>
          exact (cutoff_ge_base hH (k + 1)).trans hx
      | succ j =>
          have hapos := cutoff_pos hH k
          have hlog : cutoff H k ≤ Real.log x := by
            have h := Real.log_le_log (Real.exp_pos ((cutoff H k) ^ 2)) hx
            have ha : 1 ≤ cutoff H k := hH.trans (cutoff_ge_base hH k)
            simp only [Real.log_exp] at h
            nlinarith
          rw [iterLog_shift]
          exact ih (Real.log x) hlog j (by omega)

theorem cutoff_le_power {H L : ℝ} (hH : 16 ≤ H) (k : ℕ)
    (hL : cutoff H k ^ 2 ≤ L) :
    cutoff H k ≤ L ^ (1 - epsilon k) := by
  have hH1 : 1 ≤ H := by linarith
  have ha : 16 ≤ cutoff H k := hH.trans (cutoff_ge_base hH1 k)
  have hL1 : 1 ≤ L := by nlinarith
  have hroot : cutoff H k ≤ Real.sqrt L :=
    (Real.le_sqrt (by linarith : 0 ≤ cutoff H k) (by linarith : 0 ≤ L)).mpr hL
  have he := epsilon_le k
  calc
    cutoff H k ≤ Real.sqrt L := hroot
    _ = L ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow L
    _ ≤ L ^ (1 - epsilon k) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)

theorem power_le_epsilon_mul {H L : ℝ} (hH : 16 ≤ H)
    (hlogH : 4096 ≤ Real.log H) (k : ℕ) (hL : cutoff H k ≤ L) :
    L ^ (1 - epsilon k) ≤ epsilon k * L := by
  have hH1 : 1 ≤ H := by linarith
  have ha : 16 ≤ cutoff H k := hH.trans (cutoff_ge_base hH1 k)
  have hLpos : 0 < L := lt_of_lt_of_le (cutoff_pos hH1 k) hL
  have he := epsilon_pos k
  have hsquare := epsilon_sq_log_cutoff_ge_one hH hlogH k
  have hlog : Real.log (cutoff H k) ≤ Real.log L :=
    Real.log_le_log (cutoff_pos hH1 k) hL
  have hsquareL : 1 ≤ epsilon k ^ 2 * Real.log L :=
    hsquare.trans (mul_le_mul_of_nonneg_left hlog (sq_nonneg _))
  have hinv : 1 / epsilon k ≤ epsilon k * Real.log L := by
    apply (div_le_iff₀ he).mpr
    nlinarith
  have hsmallLog := Real.one_sub_inv_le_log_of_pos he
  have hexponent : Real.log L * (1 - epsilon k) ≤
      Real.log (epsilon k) + Real.log L := by
    rw [inv_eq_one_div] at hsmallLog
    nlinarith
  rw [Real.rpow_def_of_pos hLpos]
  calc
    Real.exp (Real.log L * (1 - epsilon k)) ≤
        Real.exp (Real.log (epsilon k) + Real.log L) := Real.exp_le_exp.mpr hexponent
    _ = epsilon k * L := by rw [Real.exp_add, Real.exp_log he, Real.exp_log hLpos]

theorem two_le_epsilon_mul {H L : ℝ} (hH : 16 ≤ H)
    (hlogH : 4096 ≤ Real.log H) (k : ℕ) (hL : cutoff H k ≤ L) :
    2 ≤ epsilon k * L := by
  have hH1 : 1 ≤ H := by linarith
  have hapos := cutoff_pos hH1 k
  have hA := epsilon_sq_log_cutoff_ge_one hH hlogH k
  have hlog := Real.log_le_sub_one_of_pos hapos
  have hmul := mul_le_mul_of_nonneg_left hlog (sq_nonneg (epsilon k))
  have he := epsilon_le k
  have he0 := (epsilon_pos k).le
  have ha0 := hapos.le
  have hprod : 0 ≤ epsilon k * cutoff H k := mul_nonneg he0 ha0
  have hsmall := mul_nonneg (show 0 ≤ 1 / 2 - epsilon k by linarith) hprod
  have hbase : 2 ≤ epsilon k * cutoff H k := by nlinarith
  exact hbase.trans (mul_le_mul_of_nonneg_left hL he0)

end Erdos320.LowerAnalytic
end


-- Adapted from Erdos320.UpperFinite.Denominator.
section
/-
An elementary rational grid bound. The common denominator need not be a
least common multiple. The proofs are independent implementations for this
project of the classical denominator-counting argument.
-/

namespace Erdos320

theorem card_sumsOf_le_common_denominator (A : Finset ℕ) (b : ℕ) (hb : 0 < b)
    (hApos : ∀ n ∈ A, 0 < n) (hdiv : ∀ n ∈ A, n ∣ b) :
    (sumsOf A).card ≤ b * A.card + 1 := by
  let grid : Finset ℚ := (Finset.range (b * A.card + 1)).image
    (fun a : ℕ => (a : ℚ) / b)
  have hsub : sumsOf A ⊆ grid := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨B, hBA, rfl⟩
    have hBA' : B ⊆ A := Finset.mem_powerset.mp hBA
    let a : ℕ := ∑ n ∈ B, b / n
    have ha : a ≤ b * A.card := by
      calc
        a ≤ ∑ _n ∈ B, b := Finset.sum_le_sum (fun n _ => Nat.div_le_self b n)
        _ = B.card * b := by simp
        _ ≤ A.card * b := Nat.mul_le_mul_right b (Finset.card_le_card hBA')
        _ = b * A.card := Nat.mul_comm _ _
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_range.mpr (by omega), ?_⟩
    dsimp [a]
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Nat.cast_div_charZero (hdiv n (hBA' hn))]
    have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (hApos n (hBA' hn)).ne'
    field_simp [hbQ, hnQ]
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans_eq (Finset.card_range _))

theorem log_card_sumsOf_le_log_common_denominator (A : Finset ℕ) (b : ℕ)
    (hb : 0 < b) (hApos : ∀ n ∈ A, 0 < n) (hdiv : ∀ n ∈ A, n ∣ b) :
    Real.log ((sumsOf A).card : ℝ) ≤ Real.log (b : ℝ) + Real.log (A.card + 1 : ℕ) := by
  have hcount := card_sumsOf_le_common_denominator A b hb hApos hdiv
  have hsmall : (sumsOf A).card ≤ b * (A.card + 1) := by
    have hb1 : 1 ≤ b := hb
    nlinarith
  have hpos : (0 : ℝ) < (sumsOf A).card := by exact_mod_cast card_sumsOf_pos A
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hsuccR : ((A.card + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hlog := Real.log_le_log hpos (show ((sumsOf A).card : ℝ) ≤
      (b : ℝ) * (A.card + 1 : ℕ) by exact_mod_cast hsmall)
  rwa [Real.log_mul hbR hsuccR] at hlog

end Erdos320
end


-- Adapted from Erdos320.LowerCompatible.
section
/-
Original residue-divisibility implementation of the compatible-prime principle.
The mathematical principle follows Bettin--Grenié--Molteni--Sanna, Section 2.
The arithmetic here uses reduced rational denominators rather than a p-adic
valuation or any external computation.
-/

namespace Erdos320

/-- A rational has a denominator invertible modulo the given prime. -/
def PrimeRegular (p : ℕ) (q : ℚ) : Prop := ¬p ∣ q.den

theorem primeRegular_zero {p : ℕ} (hp : Nat.Prime p) : PrimeRegular p 0 := by
  simpa [PrimeRegular] using hp.not_dvd_one

theorem primeRegular_add {p : ℕ} (hp : Nat.Prime p) {q r : ℚ}
    (hq : PrimeRegular p q) (hr : PrimeRegular p r) :
    PrimeRegular p (q + r) := by
  intro h
  exact hp.not_dvd_lcm hq hr (dvd_trans h (Rat.add_den_dvd_lcm q r))

theorem primeRegular_sub {p : ℕ} (hp : Nat.Prime p) {q r : ℚ}
    (hq : PrimeRegular p q) (hr : PrimeRegular p r) :
    PrimeRegular p (q - r) := by
  intro h
  exact hp.not_dvd_lcm hq hr (dvd_trans h (Rat.sub_den_dvd_lcm q r))

theorem primeRegular_reciprocal_sum {p : ℕ} (hp : Nat.Prime p)
    (A : Finset ℕ) (hpos : ∀ n ∈ A, 0 < n)
    (hunit : ∀ n ∈ A, ¬p ∣ n) :
    PrimeRegular p (∑ n ∈ A, (n : ℚ)⁻¹) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using primeRegular_zero hp
  | @insert n A hn ih =>
      rw [Finset.sum_insert hn]
      apply primeRegular_add hp
      · simpa [PrimeRegular, Rat.inv_natCast_den_of_pos (hpos n (by simp))]
          using hunit n (by simp)
      · apply ih
        · intro a ha
          exact hpos a (by simp [ha])
        · intro a ha
          exact hunit a (by simp [ha])

/-- Multiplying a rational regular at p by p forces p into its numerator. -/
theorem prime_dvd_mul_num {p : ℕ} (hp : Nat.Prime p) {q : ℚ}
    (hq : PrimeRegular p q) : (p : ℤ) ∣ ((p : ℚ) * q).num := by
  have hmul := Rat.mul_num_den' (p : ℚ) q
  simp only [Rat.num_natCast, Rat.den_natCast, Nat.cast_one, mul_one] at hmul
  have hd : (p : ℤ) ∣ ((p : ℚ) * q).num * q.den := by
    rw [hmul]
    exact ⟨q.num * ((p : ℚ) * q).den, by ring⟩
  have hq' : ¬(p : ℤ) ∣ (q.den : ℤ) := by
    simpa only [PrimeRegular, Int.natCast_dvd_natCast] using hq
  exact ((Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hd).resolve_right hq'

/-- A prime is compatible with m if every nonzero signed remainder at m
has numerator nonzero modulo the prime. -/
def CompatiblePrime (p m : ℕ) : Prop :=
  0 < m ∧ ∀ a ∈ sums (m - 1), ∀ b ∈ sums (m - 1),
    ¬(p : ℤ) ∣ ((m : ℚ)⁻¹ - (a - b)).num

theorem compatible_independent {p m : ℕ} (h : CompatiblePrime p m) :
    IndependentDenominator m := by
  refine ⟨h.1, ?_⟩
  intro a ha b hb heq
  have hnot := h.2 a ha b hb
  apply hnot
  rw [heq, sub_self]
  simp

end Erdos320
end


-- Adapted from Erdos320.LowerCofactors.
section
/-
The cofactor range for the original lower construction is the square root of
`log N`. These elementary rounding estimates are independent of prime counting.
-/

namespace Erdos320

open Filter

noncomputable def lowerCofactorBound (N : ℕ) : ℕ :=
  ⌊Real.sqrt (Real.log (N : ℝ))⌋₊

theorem lowerCofactorBound_cast_le (N : ℕ) :
    (lowerCofactorBound N : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) :=
  Nat.floor_le (Real.sqrt_nonneg _)

theorem cofactor_sq_le_log {N m : ℕ} (hN : 1 ≤ N)
    (hm : m ≤ lowerCofactorBound N) : (m : ℝ) ^ 2 ≤ Real.log (N : ℝ) := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hmR : (m : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) :=
    le_trans (by exact_mod_cast hm) (lowerCofactorBound_cast_le N)
  have hs := Real.sq_sqrt hlog
  nlinarith [Real.sqrt_nonneg (Real.log (N : ℝ)), Nat.cast_nonneg (α := ℝ) m]

theorem lowerCofactorBound_lt {N : ℕ} (hN : 2 ≤ N) : lowerCofactorBound N < N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hloglt : Real.log (N : ℝ) < (N : ℝ) ^ 2 := by
    have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N)
    nlinarith
  have hsqrt : Real.sqrt (Real.log (N : ℝ)) < (N : ℝ) :=
    (Real.sqrt_lt hlog (by positivity)).mpr hloglt
  have hcast := lt_of_le_of_lt (lowerCofactorBound_cast_le N) hsqrt
  exact_mod_cast hcast

theorem lowerCofactorBound_ge_three {N : ℕ} (hlog : 9 ≤ Real.log (N : ℝ)) :
    3 ≤ lowerCofactorBound N := by
  apply Nat.le_floor
  apply Real.le_sqrt_of_sq_le
  norm_num
  exact hlog

theorem half_sqrt_le_lowerCofactorBound {N : ℕ}
    (hlog : 4 ≤ Real.log (N : ℝ)) :
    Real.sqrt (Real.log (N : ℝ)) / 2 ≤ (lowerCofactorBound N : ℝ) := by
  have hsqrt : (2 : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) :=
    Real.le_sqrt_of_sq_le (by norm_num; exact hlog)
  have hfloor := Nat.lt_floor_add_one (Real.sqrt (Real.log (N : ℝ)))
  change Real.sqrt (Real.log (N : ℝ)) < (lowerCofactorBound N : ℝ) + 1 at hfloor
  linarith

theorem lower_cofactor_log_endpoint {N : ℕ} (hN : 3 ≤ N)
    (hlog : 9 ≤ Real.log (N : ℝ))
    (hloglog : 10 ≤ Real.log (Real.log (N : ℝ))) :
    Real.log (Real.log (Real.log ((N + 1 : ℕ) : ℝ))) - 2 ≤
      Real.log (Real.log (lowerCofactorBound N : ℝ)) := by
  let z : ℝ := Real.log (Real.log (N : ℝ))
  let z' : ℝ := Real.log (Real.log ((N + 1 : ℕ) : ℝ))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hspos : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hLpos
  have hyhalf := half_sqrt_le_lowerCofactorBound (by linarith : 4 ≤ Real.log (N : ℝ))
  have hlogy : z / 2 - Real.log 2 ≤ Real.log (lowerCofactorBound N : ℝ) := by
    have h := Real.log_le_log (div_pos hspos (by norm_num)) hyhalf
    rw [Real.log_div hspos.ne' (by norm_num), Real.log_sqrt hLpos.le] at h
    exact h
  have hNnextsq : ((N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    have hNR : (3 : ℝ) ≤ N := by exact_mod_cast hN
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hLnext : Real.log ((N + 1 : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (N + 1 : ℕ)) hNnextsq
    simpa [Real.log_pow] using h
  have hLnextpos : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))
  have hzz : z' ≤ Real.log 2 + z := by
    have h := Real.log_le_log hLnextpos hLnext
    rwa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hLpos.ne'] at h
  have hmono : z ≤ z' := by
    apply Real.log_le_log hLpos
    apply Real.log_le_log hNpos
    exact_mod_cast (Nat.le_succ N)
  have hzpos : 0 < z' := by
    change 10 ≤ z at hloglog
    linarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hquarter : z' / 4 ≤ Real.log (lowerCofactorBound N : ℝ) := by
    change 10 ≤ z at hloglog
    linarith
  have houter := Real.log_le_log (div_pos hzpos (by norm_num)) hquarter
  rw [Real.log_div hzpos.ne' (by norm_num : (4 : ℝ) ≠ 0)] at houter
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  change Real.log z' - 2 ≤ _
  linarith

theorem eventually_lower_cofactor_conditions :
    ∀ᶠ N : ℕ in atTop,
      3 ≤ lowerCofactorBound N ∧ lowerCofactorBound N < N ∧
      Real.log (Real.log (Real.log ((N + 1 : ℕ) : ℝ))) - 2 ≤
        Real.log (Real.log (lowerCofactorBound N : ℝ)) := by
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    log_nat_tendsto.eventually (eventually_ge_atTop (9 : ℝ)),
    loglog_nat_tendsto.eventually (eventually_ge_atTop (10 : ℝ))]
      with N hN hL hz
  exact ⟨lowerCofactorBound_ge_three hL, lowerCofactorBound_lt (by omega),
    lower_cofactor_log_endpoint hN hL hz⟩

end Erdos320
end


-- Adapted from Erdos320.UpperAnalyticApplication.
section
/-
The exact normalized recurrence implies the full, growing-depth upper scale.
This file isolates that implication; it does not assert the number-theoretic
recurrence without a proof.
-/

namespace Erdos320

noncomputable def logarithmicWeight (n : ℕ) : ℝ :=
  stoppedProduct n (Real.log (Real.log (n : ℝ)))

noncomputable def normalizedEntropy (n : ℕ) : ℝ :=
  (Real.log (n : ℝ) / (n : ℝ)) * logS n

theorem logarithmicWeight_one_le (n : ℕ) : 1 ≤ logarithmicWeight n :=
  one_le_stoppedProduct n _

theorem logarithmicWeight_monotone : Monotone logarithmicWeight := by
  intro a b hab
  by_cases ha : 2 ≤ a
  · have ha₁ : (1 : ℝ) < a := by exact_mod_cast (by omega : 1 < a)
    have ha₀ : (0 : ℝ) < a := by linarith
    have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hlog : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
      Real.log_le_log ha₀ habR
    have hloglog : Real.log (Real.log (a : ℝ)) ≤
        Real.log (Real.log (b : ℝ)) :=
      Real.log_le_log (Real.log_pos ha₁) hlog
    exact (stoppedProduct_mono_height hab _).trans
      (stoppedProduct_monotone b hloglog)
  · have ha' : a = 0 ∨ a = 1 := by omega
    rcases ha' with rfl | rfl
    · exact logarithmicWeight_one_le b
    · have h₁ : logarithmicWeight 1 = 1 := by
        simp [logarithmicWeight, stoppedProduct, (Real.exp_pos (3 : ℝ)).le]
      rw [h₁]
      exact logarithmicWeight_one_le b

/-- The exact logarithmic renewal recurrence, once proved, controls the complete
terminal product with one positive constant. No fixed iteration depth is used.
-/
theorem eventual_upper_bound_of_normalized_recurrence
    (A : ℝ) (hA : 0 ≤ A)
    (hrec : ∀ᶠ n : ℕ in Filter.atTop,
      normalizedEntropy n ≤ A + Real.log (Real.log (Real.log (n : ℝ))) *
        runningMaximum normalizedEntropy (logIndex n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop, logS n ≤ C * scale n := by
  have hdecrease : ∀ᶠ n : ℕ in Filter.atTop, logIndex n < n :=
    eventually_log_scale_conditions.mono (fun _ hn => hn.2.2.2.1)
  have hcoeff : ∀ᶠ n : ℕ in Filter.atTop,
      2 ≤ Real.log (Real.log (Real.log (n : ℝ))) :=
    eventually_log_scale_conditions.mono (fun _ hn => hn.2.2.2.2.2)
  have hweight : ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (Real.log (Real.log (n : ℝ))) * logarithmicWeight (logIndex n) ≤
        logarithmicWeight n := by
    simpa only [logarithmicWeight] using eventually_full_product_step
  obtain ⟨C, hC, hbound⟩ := upper_bound_of_eventual_envelope_recurrence
    normalizedEntropy logarithmicWeight
    (fun n => Real.log (Real.log (Real.log (n : ℝ)))) logIndex A hA
    logarithmicWeight_one_le logarithmicWeight_monotone hdecrease hcoeff hweight hrec
  refine ⟨C, hC, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
  have hn₁ : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn₀ : (0 : ℝ) < n := by linarith
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos hn₁
  have hfactor : 0 ≤ (n : ℝ) / Real.log (n : ℝ) := div_nonneg hn₀.le hl.le
  have hcancel : ((n : ℝ) / Real.log (n : ℝ)) * normalizedEntropy n = logS n := by
    dsimp [normalizedEntropy]
    field_simp
  calc
    logS n = ((n : ℝ) / Real.log (n : ℝ)) * normalizedEntropy n := hcancel.symm
    _ ≤ ((n : ℝ) / Real.log (n : ℝ)) * (C * logarithmicWeight n) :=
      mul_le_mul_of_nonneg_left (hbound n) hfactor
    _ = C * scale n := by
      dsimp [scale, logarithmicWeight]
      ring

end Erdos320
end


-- Adapted from Erdos320.UpperAnalyticLimits.
section
/- Original limiting estimates for the uniform prime-block error. -/

namespace Erdos320

noncomputable def renewalLogError (L : ℝ) : ℝ :=
  2 * (Real.log (L + 1) / L) + 128 / L ^ 3

noncomputable def renewalError (N : ℕ) : ℝ := renewalLogError (Real.log (N : ℝ))

theorem tendsto_log_add_one_pow_div (k : ℕ) :
    Filter.Tendsto (fun L : ℝ => Real.log (L + 1) ^ k / L)
      Filter.atTop (nhds 0) := by
  have hadd : Filter.Tendsto (fun L : ℝ => L + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
  simpa only [Function.comp_def, one_mul, add_neg_cancel_right] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) k one_ne_zero).comp hadd

theorem renewalLogError_mul_loglog_bound {L : ℝ} (hL : 3 ≤ L) :
    0 ≤ renewalLogError L * Real.log (Real.log L) ∧
      renewalLogError L * Real.log (Real.log L) ≤
        130 * (Real.log (L + 1) ^ 2 / L) := by
  have hL₀ : 0 < L := by linarith
  have hL₁ : 1 ≤ L := by linarith
  have hlog₁ : 1 < Real.log L := by
    have h := Real.log_lt_log (Real.exp_pos (1 : ℝ))
      (Real.exp_one_lt_three.trans_le hL)
    simpa only [Real.log_exp] using h
  have hlog₀ : 0 ≤ Real.log L := by linarith
  have hlogplus : Real.log L ≤ Real.log (L + 1) :=
    Real.log_le_log hL₀ (by linarith)
  have hu₁ : 1 ≤ Real.log (L + 1) := by linarith
  have hu₀ : 0 ≤ Real.log (L + 1) := by linarith
  have hT₀ : 0 ≤ Real.log (Real.log L) := Real.log_nonneg hlog₁.le
  have hTu : Real.log (Real.log L) ≤ Real.log (L + 1) :=
    (Real.log_le_self hlog₀).trans hlogplus
  have hLcube : L ≤ L ^ 3 := by
    calc
      L = L * 1 := by ring
      _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hL₁) hL₀.le
      _ = L ^ 3 := by ring
  have hLu : L ≤ Real.log (L + 1) * L ^ 3 :=
    hLcube.trans (by nlinarith only [mul_le_mul_of_nonneg_right hu₁ (pow_pos hL₀ 3).le])
  have hinv : 1 / L ^ 3 ≤ Real.log (L + 1) / L := by
    apply (div_le_div_iff₀ (pow_pos hL₀ 3) hL₀).mpr
    simpa using hLu
  have herror₀ : 0 ≤ renewalLogError L := by
    dsimp [renewalLogError]
    positivity
  have herror : renewalLogError L ≤ 130 * Real.log (L + 1) / L := by
    have h := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 128)
    calc
      renewalLogError L = 2 * (Real.log (L + 1) / L) + 128 * (1 / L ^ 3) := by
        dsimp [renewalLogError]
        ring
      _ ≤ 2 * (Real.log (L + 1) / L) + 128 * (Real.log (L + 1) / L) :=
        add_le_add le_rfl h
      _ = _ := by ring
  refine ⟨mul_nonneg herror₀ hT₀, ?_⟩
  calc
    renewalLogError L * Real.log (Real.log L)
        ≤ renewalLogError L * Real.log (L + 1) :=
      mul_le_mul_of_nonneg_left hTu herror₀
    _ ≤ (130 * Real.log (L + 1) / L) * Real.log (L + 1) :=
      mul_le_mul_of_nonneg_right herror hu₀
    _ = 130 * (Real.log (L + 1) ^ 2 / L) := by ring

theorem tendsto_renewalLogError_mul_loglog :
    Filter.Tendsto (fun L : ℝ => renewalLogError L * Real.log (Real.log L))
      Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto
      (fun L : ℝ => 130 * (Real.log (L + 1) ^ 2 / L))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_log_add_one_pow_div 2).const_mul (130 : ℝ)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with L hL
    exact (renewalLogError_mul_loglog_bound hL).1
  · filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with L hL
    exact (renewalLogError_mul_loglog_bound hL).2

theorem renewalError_mul_logloglog_tendsto :
    Filter.Tendsto
      (fun N : ℕ => renewalError N * Real.log (Real.log (Real.log (N : ℝ))))
      Filter.atTop (nhds 0) := by
  simpa only [renewalError, Function.comp_def] using
    tendsto_renewalLogError_mul_loglog.comp log_nat_tendsto

theorem eventually_renewalError_nonneg :
    ∀ᶠ N : ℕ in Filter.atTop, 0 ≤ renewalError N := by
  filter_upwards [log_nat_tendsto.eventually (Filter.eventually_ge_atTop (3 : ℝ))]
    with N hN
  have hL₀ : 0 < Real.log (N : ℝ) := by linarith
  have hu : 0 ≤ Real.log (Real.log (N : ℝ) + 1) := Real.log_nonneg (by linarith)
  dsimp [renewalError, renewalLogError]
  positivity

theorem eventually_renewalError_kernel_absorbed :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 + renewalError N) *
          (Real.log (Real.log (Real.log (N : ℝ))) - Real.log (Real.log 3)) ≤
        Real.log (Real.log (Real.log (N : ℝ))) :=
  eventual_multiplicative_error_absorbed_by_margin renewalError
    (fun N => Real.log (Real.log (Real.log (N : ℝ))))
    (Real.log (Real.log 3)) loglog_three_pos
    eventually_renewalError_nonneg renewalError_mul_logloglog_tendsto

theorem eventually_renewalError_le_one :
    ∀ᶠ N : ℕ in Filter.atTop, renewalError N ≤ 1 := by
  have hsmall : ∀ᶠ N : ℕ in Filter.atTop,
      renewalError N * Real.log (Real.log (Real.log (N : ℝ))) < 1 :=
    renewalError_mul_logloglog_tendsto.eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_renewalError_nonneg,
    eventually_log_scale_conditions] with N hs hδ hN
  nlinarith [hN.2.2.2.2.2]

theorem eventually_logIndex_three :
    ∀ᶠ N : ℕ in Filter.atTop, 3 ≤ logIndex N := by
  filter_upwards [log_nat_tendsto.eventually (Filter.eventually_ge_atTop (3 : ℝ))]
    with N hN
  exact Nat.le_floor hN

theorem eventually_log_add_one_le_half :
    ∀ᶠ L : ℝ in Filter.atTop, 1 ≤ L ∧ 0 ≤ Real.log (L + 1) ∧
      Real.log (L + 1) ≤ L / 2 := by
  have hsmall : ∀ᶠ L : ℝ in Filter.atTop, Real.log (L + 1) / L < 1 / 2 := by
    have h := (tendsto_log_add_one_pow_div 1).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    simpa only [pow_one] using h
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), hsmall] with L hL hs
  have hL₀ : 0 < L := by linarith
  refine ⟨hL, Real.log_nonneg (by linarith), ?_⟩
  have h := (div_lt_iff₀ hL₀).mp hs
  linarith

theorem tendsto_div_log_add_one_atTop :
    Filter.Tendsto (fun X : ℝ => X / (Real.log X + 1))
      Filter.atTop Filter.atTop := by
  have hlog : Filter.Tendsto (fun X : ℝ => Real.log X / X)
      Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Filter.Tendsto (fun X : ℝ => (1 : ℝ) / X)
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop Filter.tendsto_id 1
  have hratio : Filter.Tendsto (fun X : ℝ => (Real.log X + 1) / X)
      Filter.atTop (nhds 0) := by
    simpa only [add_div, add_zero] using hlog.add hinv
  have hpos : ∀ᶠ X : ℝ in Filter.atTop, 0 < (Real.log X + 1) / X := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with X hX
    exact div_pos (by linarith [Real.log_pos hX]) (by linarith)
  have hwithin : Filter.Tendsto (fun X : ℝ => (Real.log X + 1) / X)
      Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hratio, hpos⟩
  simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp hwithin

end Erdos320
end


-- Adapted from Erdos320.LowerAnalytic.Mesh.
section
namespace Erdos320.LowerAnalytic

noncomputable def meshCoordinate (m : ℕ) : ℝ := Real.log (Real.log (m : ℝ))

noncomputable def argument (m : ℕ) : ℝ := meshCoordinate (m + 1)

noncomputable def prefactor (m : ℕ) : ℝ := ((m + 1 : ℕ) : ℝ) / Real.log m

/-- A floor gives an upper bound at the left endpoint and a lower bound at
the right endpoint, exactly matching the discrete mesh. -/
noncomputable def startingPoint (x : ℝ) : ℕ := ⌊Real.exp (Real.exp x)⌋₊

theorem startingPoint_ge_three {x : ℝ} (hx : 16 ≤ x) : 3 ≤ startingPoint x := by
  have h₁ := Real.add_one_le_exp x
  have h₂ := Real.add_one_le_exp (Real.exp x)
  apply Nat.le_floor
  norm_num only [Nat.cast_ofNat]
  nlinarith

theorem mesh_startingPoint_le {x : ℝ} (hx : 16 ≤ x) :
    meshCoordinate (startingPoint x) ≤ x := by
  have hM : 3 ≤ startingPoint x := startingPoint_ge_three hx
  have hM0 : (0 : ℝ) < startingPoint x := by exact_mod_cast (show 0 < startingPoint x by omega)
  have hlogM : 0 < Real.log (startingPoint x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < startingPoint x by omega))
  have hfloor : (startingPoint x : ℝ) ≤ Real.exp (Real.exp x) :=
    Nat.floor_le (Real.exp_pos _).le
  have hfirst := Real.log_le_log hM0 hfloor
  rw [Real.log_exp] at hfirst
  have hsecond := Real.log_le_log hlogM hfirst
  simpa [meshCoordinate] using hsecond

theorem argument_ge_of_startingPoint {x : ℝ} {m : ℕ}
    (hm : startingPoint x ≤ m) : x ≤ argument m := by
  have hstart : Real.exp (Real.exp x) ≤ ((m + 1 : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (Real.exp (Real.exp x))
    have hcast : (startingPoint x : ℝ) ≤ m := by exact_mod_cast hm
    push_cast
    change Real.exp (Real.exp x) < (startingPoint x : ℝ) + 1 at h
    linarith
  have hfirst := Real.log_le_log (Real.exp_pos (Real.exp x)) hstart
  rw [Real.log_exp] at hfirst
  have hsecond := Real.log_le_log (Real.exp_pos x) hfirst
  simpa [argument, meshCoordinate] using hsecond

theorem startingPoint_le_of_endpoint {x : ℝ} {y : ℕ} (hy : 3 ≤ y)
    (hx : x ≤ meshCoordinate y) : startingPoint x ≤ y := by
  have hyR : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hyR
  have hfirst := Real.exp_le_exp.mpr hx
  rw [meshCoordinate, Real.exp_log hlogy] at hfirst
  have hsecond := Real.exp_le_exp.mpr hfirst
  rw [Real.exp_log (lt_trans zero_lt_one hyR)] at hsecond
  exact Nat.floor_le_of_le hsecond

theorem mesh_increment_le (m : ℕ) (hm : 2 ≤ m) :
    meshCoordinate (m + 1) - meshCoordinate m ≤
      1 / ((m : ℝ) * Real.log m) := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hm0 : (0 : ℝ) < m := lt_trans zero_lt_one hmR
  have hs0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hl0 : 0 < Real.log (m : ℝ) := Real.log_pos hmR
  have hls0 : 0 < Real.log ((m : ℝ) + 1) := Real.log_pos (by linarith)
  have hfirst := Real.log_le_sub_one_of_pos (div_pos hs0 hm0)
  rw [Real.log_div hs0.ne' hm0.ne'] at hfirst
  have hident : ((m : ℝ) + 1) / m - 1 = 1 / (m : ℝ) := by
    field_simp
    ring
  rw [hident] at hfirst
  have hsecond := Real.log_le_sub_one_of_pos (div_pos hls0 hl0)
  rw [Real.log_div hls0.ne' hl0.ne'] at hsecond
  have hident₂ : Real.log ((m : ℝ) + 1) / Real.log m - 1 =
      (Real.log ((m : ℝ) + 1) - Real.log m) / Real.log m := by
    field_simp
  rw [hident₂] at hsecond
  calc
    meshCoordinate (m + 1) - meshCoordinate m =
        Real.log (Real.log ((m : ℝ) + 1)) - Real.log (Real.log m) := by
      simp [meshCoordinate]
    _ ≤ (Real.log ((m : ℝ) + 1) - Real.log m) / Real.log m := hsecond
    _ ≤ (1 / (m : ℝ)) / Real.log m := div_le_div_of_nonneg_right hfirst hl0.le
    _ = _ := by ring

theorem reciprocal_log_sum_lower (M y : ℕ) (hM : 2 ≤ M) (hMy : M ≤ y) :
    meshCoordinate y - meshCoordinate M ≤
      ∑ m ∈ Finset.Ico M y, 1 / ((m : ℝ) * Real.log m) := by
  have h := Finset.sum_le_sum (s := Finset.Ico M y) (fun m hm =>
    mesh_increment_le m (hM.trans (Finset.mem_Ico.mp hm).1))
  rwa [Finset.sum_Ico_sub meshCoordinate hMy] at h

theorem logFactors_nonneg_of_logs {k : ℕ} {L : ℝ}
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j L) :
    0 ≤ logFactors k L := by
  unfold logFactors
  apply Finset.prod_nonneg
  intro j hj
  exact (Real.exp_pos 2).le.trans (hlogs (j + 1) (by omega)
    (by have := Finset.mem_range.mp hj; omega))

/-- A lower benchmark on a variable interval gives a constant multiple of
the elementary reciprocal-logarithm mesh. -/
theorem weighted_mesh_lower (A : ℕ → ℝ) (M y k : ℕ) (c L a : ℝ)
    (hM : 3 ≤ M) (hMy : M ≤ y) (hc : 0 ≤ c) (hL : 0 < L)
    (ha : 1 / 2 ≤ a) (ha₁ : a ≤ 1)
    (hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j L)
    (hleft : ∀ m ∈ Finset.Ico M y, L ^ a ≤ argument m)
    (hA : ∀ m ∈ Finset.Ico M y,
      c * prefactor m * logFactors k (argument m) ≤ A m) :
    c * a ^ k * logFactors k L * (meshCoordinate y - meshCoordinate M) ≤
      ∑ m ∈ Finset.Ico M y, A m / ((m : ℝ) * (m + 1)) := by
  have ha0 : 0 ≤ a := by linarith
  have hQ0 := logFactors_nonneg_of_logs hlogs
  have hC0 : 0 ≤ c * a ^ k * logFactors k L := by positivity
  have hsum := mul_le_mul_of_nonneg_left
    (reciprocal_log_sum_lower M y (by omega) hMy) hC0
  apply hsum.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hm3 : 3 ≤ m := hM.trans (Finset.mem_Ico.mp hm).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmLog : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hpref0 : 0 ≤ c * prefactor m := by
    unfold prefactor
    positivity
  have hQ := (logFactors_power_lower hL ha ha₁ hlogs).trans
    (logFactors_monotone_above_power hL ha ha₁ hlogs (hleft m hm))
  have hAm : c * prefactor m * (a ^ k * logFactors k L) ≤ A m :=
    (mul_le_mul_of_nonneg_left hQ hpref0).trans (hA m hm)
  have hdiv := div_le_div_of_nonneg_right hAm
    (show 0 ≤ (m : ℝ) * (m + 1) by positivity)
  convert hdiv using 1
  unfold prefactor
  push_cast
  field_simp

end Erdos320.LowerAnalytic
end


-- Adapted from Erdos320.UpperFinite.SmoothDenominator.
section
/-
A coarse common denominator for the residual prime block. A prime larger
than `sqrt N` can occur only once in a denominator at most `N`. All smaller
prime powers are absorbed by a power of `(sqrt N)!`. This intentionally
coarse construction suffices for a constant-factor upper recursion.
-/

namespace Erdos320

def smoothDenominator (N q : ℕ) : ℕ :=
  primorial q * (Nat.sqrt N).factorial ^ (Nat.log 2 N)

theorem smoothDenominator_pos (N q : ℕ) : 0 < smoothDenominator N q := by
  exact Nat.mul_pos (primorial_pos q) (pow_pos (Nat.factorial_pos _) _)

theorem dvd_smoothDenominator {N q n : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ q) :
    n ∣ smoothDenominator N q := by
  apply (Nat.factorization_prime_le_iff_dvd hn.ne' (smoothDenominator_pos N q).ne').mp
  intro p hp
  by_cases hpsmall : p ≤ Nat.sqrt N
  · have hpfact : p ∣ (Nat.sqrt N).factorial := Nat.dvd_factorial hp.pos hpsmall
    have hpfactExp : 1 ≤ ((Nat.sqrt N).factorial).factorization p :=
      hp.dvd_iff_one_le_factorization (Nat.factorial_ne_zero _ ) |>.mp hpfact
    have hexp : n.factorization p ≤ Nat.log 2 N := by
      apply Nat.le_log_of_pow_le (by norm_num)
      calc
        2 ^ n.factorization p ≤ p ^ n.factorization p := by gcongr; exact hp.two_le
        _ ≤ n := Nat.le_of_dvd hn (Nat.ordProj_dvd n p)
        _ ≤ N := hnN
    have hpow : n.factorization p ≤
        ((Nat.sqrt N).factorial ^ (Nat.log 2 N)).factorization p := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      nlinarith
    exact hpow.trans ((Nat.factorization_le_factorization_mul_right
      (primorial_pos q).ne') p)
  · have hexp : n.factorization p ≤ 1 := by
      by_contra h
      have htwo : 2 ≤ n.factorization p := by omega
      have hdvd : p ^ 2 ∣ n := (hp.pow_dvd_iff_le_factorization hn.ne').mpr htwo
      exact hpsmall (Nat.le_sqrt'.mpr ((Nat.le_of_dvd hn hdvd).trans hnN))
    by_cases hpn : p ∣ n
    · have hpprim : p ∣ primorial q := hp.dvd_primorial_iff.mpr (hsmooth p hp hpn)
      have hprimExp : 1 ≤ (primorial q).factorization p :=
        (hp.dvd_iff_one_le_factorization (primorial_pos q).ne').mp hpprim
      exact (hexp.trans hprimExp).trans
        ((Nat.factorization_le_factorization_mul_left
          (pow_ne_zero _ (Nat.factorial_ne_zero _))) p)
    · rw [Nat.factorization_eq_zero_of_not_dvd hpn]
      exact Nat.zero_le _

theorem residualBlock_prime_le (N : ℕ) {n : ℕ}
    (hn : n ∈ residualBlock N (largePrimes N)) {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    (p : ℝ) ≤ (N : ℝ) / Real.log N := by
  have hnI : n ∈ Finset.Icc 1 N := (Finset.mem_sdiff.mp hn).1
  have hnN := Finset.mem_Icc.mp hnI
  by_contra h
  have hpP : p ∈ largePrimes N := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hp.one_lt.le,
      (Nat.le_of_dvd (by omega) hpn).trans hnN.2⟩, hp, lt_of_not_ge h⟩
  apply (Finset.mem_sdiff.mp hn).2
  exact Finset.mem_biUnion.mpr ⟨p, hpP, Finset.mem_filter.mpr ⟨hnI, hpn⟩⟩

theorem residualBlock_dvd_smoothDenominator (N : ℕ) {n : ℕ}
    (hn : n ∈ residualBlock N (largePrimes N)) :
    n ∣ smoothDenominator N ⌊(N : ℝ) / Real.log N⌋₊ := by
  have hnI := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1
  apply dvd_smoothDenominator (by omega) hnI.2
  intro p hp hpn
  exact Nat.le_floor (residualBlock_prime_le N hn hp hpn)

end Erdos320
end


-- Adapted from Erdos320.LowerMultiplication.
section
/-
An original proof of the compatible-prime multiplication step. A subset of
denominators is partitioned according to divisibility by p. The divisible part
scales to earlier denominators at m, and the remaining part is regular modulo p.
-/

namespace Erdos320

def divisibleQuotients (p : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (A.filter (fun n => p ∣ n)).image (fun n => n / p)

def primeFreePart (p : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter (fun n => ¬p ∣ n)

theorem quotient_injective_on_divisible (p : ℕ) (A : Finset ℕ) :
    Set.InjOn (fun n => n / p) ↑(A.filter (fun n => p ∣ n)) := by
  intro a ha b hb hab
  have haD : p ∣ a := (Finset.mem_filter.mp ha).2
  have hbD : p ∣ b := (Finset.mem_filter.mp hb).2
  change a / p = b / p at hab
  calc
    a = a / p * p := (Nat.div_mul_cancel haD).symm
    _ = b / p * p := by rw [hab]
    _ = b := Nat.div_mul_cancel hbD

theorem reciprocal_divisible_split (p : ℕ) (A : Finset ℕ) :
    (∑ n ∈ A, (n : ℚ)⁻¹) =
      (p : ℚ)⁻¹ * (∑ n ∈ divisibleQuotients p A, (n : ℚ)⁻¹) +
        ∑ n ∈ primeFreePart p A, (n : ℚ)⁻¹ := by
  classical
  have himage : (∑ n ∈ divisibleQuotients p A, (n : ℚ)⁻¹) =
      ∑ n ∈ A.filter (fun n => p ∣ n), ((n / p : ℕ) : ℚ)⁻¹ := by
    unfold divisibleQuotients
    exact Finset.sum_image (quotient_injective_on_divisible p A)
  have hscaled : (∑ n ∈ A.filter (fun n => p ∣ n), (n : ℚ)⁻¹) =
      (p : ℚ)⁻¹ * (∑ n ∈ divisibleQuotients p A, (n : ℚ)⁻¹) := by
    rw [himage, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hdiv : p ∣ n := (Finset.mem_filter.mp hn).2
    have hfactor : (n : ℚ) = (p : ℚ) * ((n / p : ℕ) : ℚ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
    rw [hfactor, mul_inv_rev]
    ring
  calc
    (∑ n ∈ A, (n : ℚ)⁻¹) =
        (∑ n ∈ A.filter (fun n => p ∣ n), (n : ℚ)⁻¹) +
          ∑ n ∈ primeFreePart p A, (n : ℚ)⁻¹ := by
      exact (Finset.sum_filter_add_sum_filter_not A
        (fun n => p ∣ n) (fun n => (n : ℚ)⁻¹)).symm
    _ = _ := by rw [hscaled]

theorem divisibleQuotients_subset {p m : ℕ} (hp : 0 < p)
    {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 (m * p - 1)) :
    divisibleQuotients p A ⊆ Finset.Icc 1 (m - 1) := by
  intro q hq
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hnA, hpn⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn1, hnmax⟩ := Finset.mem_Icc.mp (hA hnA)
  have hpnle : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have hq1 : 1 ≤ n / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa)
  have hmp : 0 < m * p := by omega
  have hqM : n / p < m := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    omega
  exact Finset.mem_Icc.mpr ⟨hq1, by omega⟩

theorem divisibleQuotients_sum_mem {p m : ℕ} (hp : 0 < p)
    {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 (m * p - 1)) :
    (∑ n ∈ divisibleQuotients p A, (n : ℚ)⁻¹) ∈ sums (m - 1) := by
  apply Finset.mem_image.mpr
  refine ⟨divisibleQuotients p A, ?_, rfl⟩
  exact Finset.mem_powerset.mpr (divisibleQuotients_subset hp hA)

theorem primeFreePart_regular {p : ℕ} (hp : Nat.Prime p)
    (A : Finset ℕ) (hA : ∀ n ∈ A, 0 < n) :
    PrimeRegular p (∑ n ∈ primeFreePart p A, (n : ℚ)⁻¹) := by
  apply primeRegular_reciprocal_sum hp
  · intro n hn
    exact hA n (Finset.mem_filter.mp hn).1
  · intro n hn
    exact (Finset.mem_filter.mp hn).2

/-- The compatible-prime construction produces a new independent denominator.
This is the multiplicative mechanism needed for a growing-depth lower bound. -/
theorem compatible_prime_mul_independent {p m : ℕ} (hp : Nat.Prime p)
    (hcompatible : CompatiblePrime p m) : IndependentDenominator (m * p) := by
  refine ⟨Nat.mul_pos hcompatible.1 hp.pos, ?_⟩
  intro a ha b hb heq
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hb
  have hAsub : A ⊆ Finset.Icc 1 (m * p - 1) := Finset.mem_powerset.mp hA
  have hBsub : B ⊆ Finset.Icc 1 (m * p - 1) := Finset.mem_powerset.mp hB
  let a' : ℚ := ∑ n ∈ divisibleQuotients p A, (n : ℚ)⁻¹
  let b' : ℚ := ∑ n ∈ divisibleQuotients p B, (n : ℚ)⁻¹
  let u : ℚ := ∑ n ∈ primeFreePart p A, (n : ℚ)⁻¹
  let v : ℚ := ∑ n ∈ primeFreePart p B, (n : ℚ)⁻¹
  have ha' : a' ∈ sums (m - 1) := divisibleQuotients_sum_mem hp.pos hAsub
  have hb' : b' ∈ sums (m - 1) := divisibleQuotients_sum_mem hp.pos hBsub
  have hu : PrimeRegular p u := by
    apply primeFreePart_regular hp A
    intro n hn
    exact (Finset.mem_Icc.mp (hAsub hn)).1
  have hv : PrimeRegular p v := by
    apply primeFreePart_regular hp B
    intro n hn
    exact (Finset.mem_Icc.mp (hBsub hn)).1
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcompatible.1)
  have hAeq : (p : ℚ) * (∑ n ∈ A, (n : ℚ)⁻¹) = a' + p * u := by
    rw [reciprocal_divisible_split p A]
    change (p : ℚ) * ((p : ℚ)⁻¹ * a' + u) = a' + p * u
    calc
      _ = ((p : ℚ) * (p : ℚ)⁻¹) * a' + p * u := by ring
      _ = _ := by rw [mul_inv_cancel₀ hp0, one_mul]
  have hBeq : (p : ℚ) * (∑ n ∈ B, (n : ℚ)⁻¹) = b' + p * v := by
    rw [reciprocal_divisible_split p B]
    change (p : ℚ) * ((p : ℚ)⁻¹ * b' + v) = b' + p * v
    calc
      _ = ((p : ℚ) * (p : ℚ)⁻¹) * b' + p * v := by ring
      _ = _ := by rw [mul_inv_cancel₀ hp0, one_mul]
  have hscaled : (p : ℚ) *
      ((∑ n ∈ A, (n : ℚ)⁻¹) - ∑ n ∈ B, (n : ℚ)⁻¹) = (m : ℚ)⁻¹ := by
    rw [heq, Nat.cast_mul]
    field_simp [hp0, hm0]
  have hresidual : (m : ℚ)⁻¹ - (a' - b') = (p : ℚ) * (u - v) := by
    rw [← hscaled, mul_sub, hAeq, hBeq]
    ring
  apply hcompatible.2 a' ha' b' hb'
  rw [hresidual]
  exact prime_dvd_mul_num hp (primeRegular_sub hp hu hv)

end Erdos320
end


-- Adapted from Erdos320.LowerAnalytic.Iteration.
section
namespace Erdos320.LowerAnalytic

theorem argument_le_succ (N : ℕ) : argument N ≤ (N + 1 : ℕ) := by
  cases N with
  | zero => norm_num [argument, meshCoordinate]
  | succ N =>
      exact loglog_le_nat (show 2 ≤ N + 1 + 1 by omega)

theorem two_le_of_argument {H : ℝ} (hH : 16 ≤ H) {N : ℕ}
    (hN : H ≤ argument N) : 2 ≤ N := by
  have h := hN.trans (argument_le_succ N)
  by_contra hn
  have hnR : (N : ℝ) ≤ 1 := by exact_mod_cast (show N ≤ 1 by omega)
  push_cast at h
  linarith

theorem logFactors_succ_shift (k : ℕ) (x : ℝ) :
    logFactors (k + 1) x = Real.log x * logFactors k (Real.log x) := by
  unfold logFactors
  rw [Finset.prod_range_succ']
  have hprod : (∏ j ∈ Finset.range k, iterLog (j + 1 + 1) x) =
      ∏ j ∈ Finset.range k, iterLog (j + 1) (Real.log x) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact iterLog_shift (j + 1) x
  rw [hprod]
  change _ * Real.log x = Real.log x * _
  exact mul_comm _ _

/-- An unconditional-in-depth consequence of an explicitly stated renewal
inequality, a prime baseline, and a cofactor endpoint estimate. The actual
counting function must supply those hypotheses separately. -/
theorem depth_lower_bound
    (A : ℕ → ℝ) (y : ℕ → ℕ) (H c₀ : ℝ)
    (hH : 16 ≤ H) (hlogH : 4096 ≤ Real.log H) (hc₀ : 0 < c₀)
    (hbase : ∀ N : ℕ, H ≤ argument N → c₀ * prefactor N ≤ A N)
    (hrec : ∀ N : ℕ, H ≤ argument N → ∀ M : ℕ, 3 ≤ M → M ≤ y N →
      (1 - 1 / argument N ^ 2) * prefactor N *
        (∑ m ∈ Finset.Ico M (y N), A m / ((m : ℝ) * (m + 1))) ≤ A N)
    (hy : ∀ N : ℕ, H ≤ argument N →
      3 ≤ y N ∧ Real.log (argument N) - 2 ≤ meshCoordinate (y N)) :
    ∀ k N : ℕ, cutoff H k ≤ argument N →
      c₀ * coefficient k * prefactor N * logFactors k (argument N) ≤ A N := by
  have hH1 : 1 ≤ H := by linarith
  have hHexp : Real.exp 2 ≤ H := by
    have h := Real.exp_le_exp.mpr (show (2 : ℝ) ≤ Real.log H by linarith)
    simpa [Real.exp_log (show 0 < H by linarith)] using h
  intro k
  induction k with
  | zero =>
      intro N hN
      simpa [coefficient_zero, logFactors, cutoff] using hbase N hN
  | succ k ih =>
      intro N hN
      let z : ℝ := argument N
      let L : ℝ := Real.log z
      let a : ℝ := 1 - epsilon k
      let t : ℝ := L ^ a
      let M : ℕ := startingPoint t
      let T : ℝ := ∑ m ∈ Finset.Ico M (y N), A m / ((m : ℝ) * (m + 1))
      have hbaseN : H ≤ argument N := (cutoff_ge_base hH1 (k + 1)).trans hN
      have hN2 : 2 ≤ N := two_le_of_argument hH hbaseN
      have hpref : 0 < prefactor N := by
        unfold prefactor
        exact div_pos (by positivity) (Real.log_pos (by
          exact_mod_cast (show 1 < N by omega)))
      have hzpos : 0 < z := lt_of_lt_of_le (cutoff_pos hH1 (k + 1)) hN
      have hlogz : cutoff H k ^ 2 ≤ L := by
        have h := Real.log_le_log (Real.exp_pos (cutoff H k ^ 2)) hN
        simpa only [cutoff, Real.log_exp] using h
      have hAk : 16 ≤ cutoff H k := hH.trans (cutoff_ge_base hH1 k)
      have hAL : cutoff H k ≤ L := by nlinarith
      have hL : 0 < L := lt_of_lt_of_le (cutoff_pos hH1 k) hAL
      have he := epsilon_le k
      have he0 := (epsilon_pos k).le
      have ha : 1 / 2 ≤ a := by dsimp [a]; linarith
      have ha₁ : a ≤ 1 := by dsimp [a]; linarith
      have ha0 : 0 ≤ a := by linarith
      have hAt : cutoff H k ≤ t := cutoff_le_power hH k hlogz
      have ht16 : 16 ≤ t := hAk.trans hAt
      have htSmall : t ≤ epsilon k * L := power_le_epsilon_mul hH hlogH k hAL
      have htpos : 0 < t := Real.rpow_pos_of_pos hL _
      have hE := two_le_epsilon_mul hH hlogH k hAL
      have hyN := hy N hbaseN
      have hend : (1 - epsilon k) * L ≤ meshCoordinate (y N) := by
        dsimp [L, z] at *
        nlinarith [hyN.2]
      have htEnd : t ≤ meshCoordinate (y N) := by nlinarith
      have hM : 3 ≤ M := startingPoint_ge_three ht16
      have hMy : M ≤ y N := startingPoint_le_of_endpoint hyN.1 htEnd
      have hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j L := by
        intro j hj hjk
        exact hHexp.trans (iterLog_ge_base_of_cutoff hH1 k L hAL j hjk)
      have hQ0 := logFactors_nonneg_of_logs hlogs
      have hleft : ∀ m ∈ Finset.Ico M (y N), t ≤ argument m := by
        intro m hm
        exact argument_ge_of_startingPoint (Finset.mem_Ico.mp hm).1
      have hAm : ∀ m ∈ Finset.Ico M (y N),
          (c₀ * coefficient k) * prefactor m * logFactors k (argument m) ≤ A m := by
        intro m hm
        exact ih m (hAt.trans (hleft m hm))
      have hc : 0 ≤ c₀ * coefficient k := mul_nonneg hc₀.le (coefficient_pos k).le
      have hmesh := weighted_mesh_lower A M (y N) k (c₀ * coefficient k) L a
        hM hMy hc hL ha ha₁ hlogs hleft hAm
      have hwidth : (1 - 2 * epsilon k) * L ≤
          meshCoordinate (y N) - meshCoordinate M := by
        have hstart := mesh_startingPoint_le ht16
        change meshCoordinate M ≤ t at hstart
        nlinarith
      have hconst0 : 0 ≤ (c₀ * coefficient k) * a ^ k * logFactors k L := by positivity
      have hsum : c₀ * coefficient k * (1 - 2 * epsilon k) * a ^ k * L *
          logFactors k L ≤ T := by
        calc
          _ = ((c₀ * coefficient k) * a ^ k * logFactors k L) *
              ((1 - 2 * epsilon k) * L) := by ring
          _ ≤ ((c₀ * coefficient k) * a ^ k * logFactors k L) *
              (meshCoordinate (y N) - meshCoordinate M) :=
            mul_le_mul_of_nonneg_left hwidth hconst0
          _ ≤ T := hmesh
      have hsumBase0 : 0 ≤ c₀ * coefficient k * (1 - 2 * epsilon k) * a ^ k * L *
          logFactors k L := by
        have he2 : 0 ≤ 1 - 2 * epsilon k := by linarith
        positivity
      have hT0 : 0 ≤ T := hsumBase0.trans hsum
      have hz1 : 1 ≤ z := le_trans (by norm_num) (hH.trans hbaseN)
      have hlogle := Real.log_le_sub_one_of_pos hzpos
      have hez : 2 ≤ epsilon k * z := by
        dsimp [L] at hE
        nlinarith [mul_le_mul_of_nonneg_left hlogle he0]
      have hezsq : 1 ≤ epsilon k * z ^ 2 := by
        nlinarith [mul_nonneg (show 0 ≤ z - 1 by linarith)
          (show 0 ≤ epsilon k * z by positivity)]
      have hrecFactor : 1 - epsilon k ≤ 1 - 1 / z ^ 2 := by
        have hdiv : 1 / z ^ 2 ≤ epsilon k := (div_le_iff₀ (sq_pos_of_pos hzpos)).mpr hezsq
        linarith
      have hrecur := hrec N hbaseN M hM hMy
      have hmain : (1 - epsilon k) * prefactor N *
          (c₀ * coefficient k * (1 - 2 * epsilon k) * a ^ k * L * logFactors k L) ≤ A N := by
        calc
          _ ≤ (1 - epsilon k) * prefactor N * T :=
            mul_le_mul_of_nonneg_left hsum (by have := hpref.le; nlinarith)
          _ ≤ (1 - 1 / z ^ 2) * prefactor N * T := by
            have h := mul_le_mul_of_nonneg_right hrecFactor (mul_nonneg hpref.le hT0)
            simpa [mul_assoc] using h
          _ ≤ A N := hrecur
      have hcommon0 : 0 ≤ c₀ * coefficient k * prefactor N * L * logFactors k L := by positivity
      calc
        c₀ * coefficient (k + 1) * prefactor N * logFactors (k + 1) (argument N) =
            (c₀ * coefficient k * prefactor N * L * logFactors k L) *
              (1 - iterationLoss k) := by
          rw [coefficient_succ, logFactors_succ_shift]
          dsimp [L, z]
          ring
        _ ≤ (c₀ * coefficient k * prefactor N * L * logFactors k L) *
            ((1 - epsilon k) * (1 - 2 * epsilon k) * (1 - epsilon k) ^ k) :=
          mul_le_mul_of_nonneg_left (analytic_step_factor_lower k) hcommon0
        _ = (1 - epsilon k) * prefactor N *
            (c₀ * coefficient k * (1 - 2 * epsilon k) * a ^ k * L * logFactors k L) := by
          dsimp [a]
          ring
        _ ≤ A N := hmain

end Erdos320.LowerAnalytic
end


-- Adapted from Erdos320.UpperFinite.ResidualEstimate.
section
namespace Erdos320

private theorem log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x) ^ 2 ≤ 4 * x := by
  have hx0 : 0 ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 2)
  have hbound : Real.log x ≤ 2 * Real.sqrt x := by
    simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm] using hlog
  have hsquare := pow_le_pow_left₀ hlog0 hbound 2
  nlinarith [Real.sq_sqrt hx0]

private theorem sqrt_mul_log_sq_le {x : ℝ} (hx : 1 < x) :
    Real.sqrt x * (Real.log x) ^ 2 ≤ 216 * x / Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have hlog := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 6)
  have hcubed := pow_le_pow_left₀ hl.le hlog 3
  have hcubeeq : (x ^ (1 / 6 : ℝ) / (1 / 6 : ℝ)) ^ 3 =
      216 * Real.sqrt x := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num [Real.sqrt_eq_rpow, div_eq_mul_inv]
    ring
  rw [hcubeeq] at hcubed
  apply (le_div_iff₀ hl).mpr
  calc
    (Real.sqrt x * Real.log x ^ 2) * Real.log x =
        Real.sqrt x * Real.log x ^ 3 := by ring
    _ ≤ Real.sqrt x * (216 * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left hcubed (Real.sqrt_nonneg x)
    _ = 216 * x := by nlinarith [Real.sq_sqrt hx0]

private theorem log_succ_le_eight_quotient (N : ℕ) (hN : 2 ≤ N) :
    Real.log (N + 1 : ℕ) ≤ 8 * ((N : ℝ) / Real.log N) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hNN : ((N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    push_cast
    nlinarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (N + 1 : ℕ)) hNN
  rw [Real.log_pow] at hlog
  have htwo : 2 * Real.log (N : ℝ) ≤ 8 * ((N : ℝ) / Real.log N) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hl).mpr
    have hsq := log_sq_le_four_mul (show (1 : ℝ) ≤ N by linarith)
    nlinarith
  exact hlog.trans htwo

theorem log_smoothDenominator_bound (N : ℕ) (hN : 2 ≤ N) :
    Real.log (smoothDenominator N ⌊(N : ℝ) / Real.log N⌋₊ : ℝ) ≤
      (Real.log 4 + 216 / Real.log 2) * ((N : ℝ) / Real.log N) := by
  let q : ℕ := ⌊(N : ℝ) / Real.log N⌋₊
  let r : ℕ := Nat.sqrt N
  let k : ℕ := Nat.log 2 N
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hl4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hq : (q : ℝ) ≤ (N : ℝ) / Real.log N :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg N) hl.le)
  have hprimlog : Real.log (primorial q : ℝ) ≤
      Real.log 4 * ((N : ℝ) / Real.log N) := by
    have hpow : (primorial q : ℝ) ≤ (4 : ℝ) ^ q := by
      exact_mod_cast primorial_le_four_pow q
    have hp := Real.log_le_log (show (0 : ℝ) < primorial q by
      exact_mod_cast primorial_pos q) hpow
    rw [Real.log_pow] at hp
    exact hp.trans (by nlinarith)
  have hk : (k : ℝ) ≤ Real.log N / Real.log 2 := by
    simpa [k, Real.logb] using Real.natLog_le_logb N 2
  have hfact : Real.log (r.factorial : ℝ) ≤ (r : ℝ) * Real.log N := by
    have hf : r.factorial ≤ N ^ r :=
      (Nat.factorial_le_pow r).trans (by
        apply Nat.pow_le_pow_left
        exact Nat.sqrt_le_self N)
    have hfR : (r.factorial : ℝ) ≤ (N : ℝ) ^ r := by exact_mod_cast hf
    have hfLog := Real.log_le_log (show (0 : ℝ) < r.factorial by
      exact_mod_cast Nat.factorial_pos r) hfR
    simpa only [Real.log_pow] using hfLog
  have hsmall : (k : ℝ) * Real.log (r.factorial : ℝ) ≤
      (216 / Real.log 2) * ((N : ℝ) / Real.log N) := by
    calc
      (k : ℝ) * Real.log (r.factorial : ℝ) ≤
          (Real.log N / Real.log 2) * ((r : ℝ) * Real.log N) :=
        mul_le_mul hk hfact (Real.log_natCast_nonneg _) (div_nonneg hl.le hl2.le)
      _ ≤ (Real.log N / Real.log 2) * (Real.sqrt N * Real.log N) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hl.le hl2.le)
        exact mul_le_mul_of_nonneg_right Real.nat_sqrt_le_real_sqrt hl.le
      _ = (Real.sqrt N * Real.log N ^ 2) / Real.log 2 := by ring
      _ ≤ (216 * (N : ℝ) / Real.log N) / Real.log 2 :=
        div_le_div_of_nonneg_right (sqrt_mul_log_sq_le (show (1 : ℝ) < N by linarith)) hl2.le
      _ = (216 / Real.log 2) * ((N : ℝ) / Real.log N) := by ring
  have hprim0 : (primorial q : ℝ) ≠ 0 := by exact_mod_cast (primorial_pos q).ne'
  have hfact0 : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  change Real.log ((primorial q * r.factorial ^ k : ℕ) : ℝ) ≤ _
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hprim0 (pow_ne_zero _ hfact0), Real.log_pow]
  nlinarith

theorem residual_log_bound (N : ℕ) (hN : 2 ≤ N) :
    Real.log ((sumsOf (residualBlock N (largePrimes N))).card : ℝ) ≤
      (Real.log 4 + 216 / Real.log 2 + 8) * ((N : ℝ) / Real.log N) := by
  let Z := residualBlock N (largePrimes N)
  have hZpos : ∀ n ∈ Z, 0 < n := by
    intro n hn
    exact lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1).1
  have hdiv : ∀ n ∈ Z, n ∣ smoothDenominator N ⌊(N : ℝ) / Real.log N⌋₊ := by
    intro n hn
    exact residualBlock_dvd_smoothDenominator N hn
  have hgrid := log_card_sumsOf_le_log_common_denominator Z _
    (smoothDenominator_pos _ _) hZpos hdiv
  have hZcard : Z.card ≤ N := by
    have h := Finset.card_le_card (Finset.sdiff_subset : Z ⊆ Finset.Icc 1 N)
    simpa [Z, residualBlock] using h
  have hZlog : Real.log (Z.card + 1 : ℕ) ≤ 8 * ((N : ℝ) / Real.log N) := by
    have hcast : ((Z.card + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hZcard 1
    exact (Real.log_le_log (by positivity) hcast).trans (log_succ_le_eight_quotient N hN)
  have hdenom := log_smoothDenominator_bound N hN
  dsimp [Z] at hgrid hZlog
  nlinarith

end Erdos320
end


-- Adapted from Erdos320.LowerCutoff.
section
/-
A deliberately coarse, explicit compatibility cutoff. Factorial common
denominators suffice for an independent construction; no published numerical
table or external certificate enters these lemmas.
-/

namespace Erdos320

def compatibilityCutoff (m : ℕ) : ℕ := 2 * m * m.factorial

/-- A coarse exponential bound convenient when the cofactor is at most the
square root of `log N`. -/
theorem compatibilityCutoff_le_two_pow_square (m : ℕ) :
    compatibilityCutoff m ≤ 2 * m * 2 ^ (m * m) := by
  have hm : m ≤ 2 ^ m := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    compatibilityCutoff m = 2 * m * m.factorial := rfl
    _ ≤ 2 * m * m ^ m := Nat.mul_le_mul_left _ (Nat.factorial_le_pow m)
    _ ≤ 2 * m * (2 ^ m) ^ m :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm m)
    _ = 2 * m * 2 ^ (m * m) := by rw [pow_mul]

theorem sums_value_bounds {N : ℕ} {q : ℚ} (hq : q ∈ sums N) :
    0 ≤ q ∧ q ≤ (N : ℚ) := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hq
  have hsub : A ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp hA
  have hcard : A.card ≤ N := by
    have h := Finset.card_le_card hsub
    simpa using h
  constructor
  · apply Finset.sum_nonneg
    intro n hn
    positivity
  · calc
      (∑ n ∈ A, (n : ℚ)⁻¹) ≤ ∑ _n ∈ A, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (hsub hn)).1
        exact (inv_le_one₀ (by exact_mod_cast (show 0 < n by omega))).mpr
          (by exact_mod_cast hn1)
      _ = (A.card : ℚ) := by simp
      _ ≤ (N : ℚ) := by exact_mod_cast hcard

theorem remainder_den_dvd_factorial {m : ℕ} (hm : 0 < m)
    {a b : ℚ} (ha : a ∈ sums (m - 1)) (hb : b ∈ sums (m - 1)) :
    ((m : ℚ)⁻¹ - (a - b)).den ∣ m.factorial := by
  have haD : a.den ∣ m.factorial :=
    dvd_trans (sums_den_dvd_factorial ha)
      (Nat.factorial_dvd_factorial (Nat.sub_le m 1))
  have hbD : b.den ∣ m.factorial :=
    dvd_trans (sums_den_dvd_factorial hb)
      (Nat.factorial_dvd_factorial (Nat.sub_le m 1))
  apply dvd_trans (Rat.sub_den_dvd_lcm _ _)
  apply Nat.lcm_dvd
  · rw [Rat.inv_natCast_den_of_pos hm]
    exact Nat.dvd_factorial hm le_rfl
  · exact dvd_trans (Rat.sub_den_dvd_lcm a b) (Nat.lcm_dvd haD hbD)

theorem remainder_abs_le {m : ℕ} (hm : 0 < m)
    {a b : ℚ} (ha : a ∈ sums (m - 1)) (hb : b ∈ sums (m - 1)) :
    |(m : ℚ)⁻¹ - (a - b)| ≤ 2 * (m : ℚ) := by
  obtain ⟨ha0, haM⟩ := sums_value_bounds ha
  obtain ⟨hb0, hbM⟩ := sums_value_bounds hb
  have hm1 : 1 ≤ m := hm
  have hmcast : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by
    rw [Nat.cast_sub hm1]
    norm_num
  rw [hmcast] at haM hbM
  have hmi0 : 0 ≤ (m : ℚ)⁻¹ := by positivity
  have hmi1 : (m : ℚ)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by exact_mod_cast hm)).mpr (by exact_mod_cast hm1)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem remainder_numerator_bound {m : ℕ} (hm : 0 < m)
    {a b : ℚ} (ha : a ∈ sums (m - 1)) (hb : b ∈ sums (m - 1)) :
    ((m : ℚ)⁻¹ - (a - b)).num.natAbs ≤ compatibilityCutoff m := by
  let q : ℚ := (m : ℚ)⁻¹ - (a - b)
  have hqD : q.den ∣ m.factorial := remainder_den_dvd_factorial hm ha hb
  have hqLe : q.den ≤ m.factorial := Nat.le_of_dvd (Nat.factorial_pos m) hqD
  have habs : |q| ≤ 2 * (m : ℚ) := remainder_abs_le hm ha hb
  have hd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hrepr : (q.num : ℚ) = q * q.den := (div_eq_iff hd0).mp q.num_div_den
  have hnumQ : (q.num.natAbs : ℚ) ≤ (compatibilityCutoff m : ℚ) := by
    calc
      (q.num.natAbs : ℚ) = |(q.num : ℚ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      _ = |q| * (q.den : ℚ) := by
        rw [hrepr, abs_mul]
        exact congrArg (fun t : ℚ => |q| * t)
          (abs_of_nonneg (show (0 : ℚ) ≤ q.den by positivity))
      _ ≤ (2 * (m : ℚ)) * (m.factorial : ℚ) := by
        exact mul_le_mul habs (by exact_mod_cast hqLe) (by positivity) (by positivity)
      _ = (compatibilityCutoff m : ℚ) := by
        simp [compatibilityCutoff, Nat.cast_mul]
  exact_mod_cast hnumQ

theorem compatible_of_gt_cutoff {p m : ℕ} (hm : IndependentDenominator m)
    (hlarge : compatibilityCutoff m < p) : CompatiblePrime p m := by
  refine ⟨hm.1, ?_⟩
  intro a ha b hb hdiv
  let q : ℚ := (m : ℚ)⁻¹ - (a - b)
  have hq0 : q ≠ 0 := by
    intro hz
    exact hm.2 a ha b hb (sub_eq_zero.mp hz).symm
  have hnum0 : q.num ≠ 0 := Rat.num_ne_zero.mpr hq0
  have hnumPos : 0 < q.num.natAbs := Int.natAbs_pos.mpr hnum0
  have hnatDiv : p ∣ q.num.natAbs := by
    exact_mod_cast (Int.dvd_natAbs.mpr hdiv)
  have hpLe : p ≤ q.num.natAbs := Nat.le_of_dvd hnumPos hnatDiv
  have hbound := remainder_numerator_bound hm.1 ha hb
  change q.num.natAbs ≤ compatibilityCutoff m at hbound
  omega

theorem independent_mul_large_prime {p m : ℕ} (hp : Nat.Prime p)
    (hm : IndependentDenominator m) (hlarge : compatibilityCutoff m < p) :
    IndependentDenominator (m * p) :=
  compatible_prime_mul_independent hp (compatible_of_gt_cutoff hm hlarge)

end Erdos320
end


-- Adapted from Erdos320.LowerAnalytic.Comparison.
section
namespace Erdos320.LowerAnalytic

noncomputable def tower (B : ℝ) : ℕ → ℝ
  | 0 => B
  | k + 1 => Real.exp (tower B k)

theorem tower_shift (B : ℝ) (k : ℕ) : tower B (k + 1) = tower (Real.exp B) k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [tower] using congrArg Real.exp ih

theorem iterLog_tower (B : ℝ) (k : ℕ) : iterLog k (tower B k) = B := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iterLog_shift, tower, Real.log_exp]
      exact ih

/-- Adaptive thresholds stay below one ordinary exponential tower with a
larger fixed bottom. Hence the omitted terminal factors stay bounded. -/
theorem cutoff_sq_le_tower {H : ℝ} (hH : 16 ≤ H) (k : ℕ) :
    3 * cutoff H k ^ 2 ≤ tower (3 * H ^ 2) k := by
  have hH1 : 1 ≤ H := by linarith
  induction k with
  | zero => simp [cutoff, tower]
  | succ k ih =>
      have hAk : 16 ≤ cutoff H k := hH.trans (cutoff_ge_base hH1 k)
      have he := Real.add_one_le_exp (cutoff H k ^ 2)
      have hthree : 3 ≤ Real.exp (cutoff H k ^ 2) := by nlinarith
      change 3 * Real.exp (cutoff H k ^ 2) ^ 2 ≤ Real.exp (tower (3 * H ^ 2) k)
      calc
        3 * Real.exp (cutoff H k ^ 2) ^ 2 ≤ Real.exp (3 * cutoff H k ^ 2) := by
          rw [show (3 : ℝ) * cutoff H k ^ 2 = (3 : ℕ) * cutoff H k ^ 2 by norm_num,
            Real.exp_nat_mul]
          nlinarith [mul_nonneg (sq_nonneg (Real.exp (cutoff H k ^ 2)))
            (show 0 ≤ Real.exp (cutoff H k ^ 2) - 3 by linarith)]
        _ ≤ _ := Real.exp_le_exp.mpr ih

theorem cutoff_le_tower {H : ℝ} (hH : 16 ≤ H) (k : ℕ) :
    cutoff H k ≤ tower (3 * H ^ 2) k := by
  have ha : 16 ≤ cutoff H k := hH.trans (cutoff_ge_base (by linarith) k)
  have h := cutoff_sq_le_tower hH k
  nlinarith

theorem exists_adaptive_depth {H x : ℝ} (hH : 1 ≤ H) (hx : H ≤ x) :
    ∃ k : ℕ, cutoff H k ≤ x ∧ x < cutoff H (k + 1) := by
  classical
  let R : ℕ := ⌊x⌋₊
  let k : ℕ := Nat.findGreatest (fun i => cutoff H i ≤ x) R
  have hk : cutoff H k ≤ x := by
    dsimp [k]
    exact Nat.findGreatest_spec (P := fun i => cutoff H i ≤ x) (Nat.zero_le R)
      (show cutoff H 0 ≤ x from hx)
  have hkR : k ≤ R := Nat.findGreatest_le R
  refine ⟨k, hk, ?_⟩
  by_contra hnext
  have hnext' : cutoff H (k + 1) ≤ x := le_of_not_gt hnext
  have hbound : k + 1 ≤ R := by
    by_contra hbound
    have hkEq : k = R := by omega
    have hlarge := cutoff_add_index_le hH (R + 1)
    have hfloor : x < (R : ℝ) + 1 := Nat.lt_floor_add_one x
    rw [hkEq] at hnext'
    push_cast at hlarge
    nlinarith
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self k) hbound hnext'

theorem tail_argument_bounded {H x : ℝ} (hH : 16 ≤ H) {k : ℕ}
    (hlo : cutoff H k ≤ x) (hhi : x ≤ cutoff H (k + 1)) :
    iterLog k x ≤ Real.exp (3 * H ^ 2) := by
  have hH1 : 1 ≤ H := by linarith
  have hpos : ∀ j : ℕ, j < k → 0 < iterLog j x := by
    intro j hj
    exact lt_of_lt_of_le (by linarith : 0 < H)
      (iterLog_ge_base_of_cutoff hH1 k x hlo j (by omega))
  have h := iterLog_mono_of_positive (hhi.trans (cutoff_le_tower hH (k + 1))) hpos
  rw [tower_shift, iterLog_tower] at h
  exact h

theorem stoppedProduct_split (k h : ℕ) (x : ℝ)
    (hactive : ∀ j : ℕ, j < k → Real.exp 3 < iterLog j x) :
    stoppedProduct (k + h) x = logFactors k x * stoppedProduct h (iterLog k x) := by
  induction k generalizing x with
  | zero => simp [logFactors, iterLog]
  | succ k ih =>
      have hx : ¬x ≤ Real.exp 3 := not_le.mpr (hactive 0 (by omega))
      have hnext : ∀ j : ℕ, j < k → Real.exp 3 < iterLog j (Real.log x) := by
        intro j hj
        rw [← iterLog_shift]
        exact hactive (j + 1) (by omega)
      rw [show (k + 1) + h = (k + h) + 1 by omega, stoppedProduct, if_neg hx,
        ih (Real.log x) hnext, logFactors_succ_shift, iterLog_shift]
      ring

theorem stoppedProduct_uniform_bound (B : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ h : ℕ, ∀ x : ℝ, x ≤ B → stoppedProduct h x ≤ C := by
  let K : ℕ := ⌈B⌉₊
  refine ⟨stoppedProduct K B, one_le_stoppedProduct K B, ?_⟩
  intro h x hx
  have hBK : B ≤ Real.exp 3 + K := by
    have hceil : B ≤ (K : ℝ) := Nat.le_ceil B
    have he := Real.exp_pos (3 : ℝ)
    linarith
  apply (stoppedProduct_monotone h hx).trans
  by_cases hh : h ≤ K
  · exact stoppedProduct_mono_height hh B
  · exact (stoppedProduct_stable_of_input_le hBK (le_of_not_ge hh)).le

theorem full_product_le_partial {H x : ℝ} (hH : 16 ≤ H)
    (hlogH : 4096 ≤ Real.log H) (C : ℝ) (hC : 1 ≤ C)
    (hbound : ∀ h : ℕ, ∀ u : ℝ, u ≤ Real.exp (3 * H ^ 2) → stoppedProduct h u ≤ C)
    {k : ℕ} (hlo : cutoff H k ≤ x) (hhi : x ≤ cutoff H (k + 1)) (h : ℕ) :
    stoppedProduct h x ≤ C * logFactors k x := by
  have hH1 : 1 ≤ H := by linarith
  have hHexp : Real.exp 3 < H := by
    have h := Real.exp_lt_exp.mpr (show (3 : ℝ) < Real.log H by linarith)
    simpa [Real.exp_log (show 0 < H by linarith)] using h
  have hactive : ∀ j : ℕ, j < k → Real.exp 3 < iterLog j x := by
    intro j hj
    exact hHexp.trans_le (iterLog_ge_base_of_cutoff hH1 k x hlo j (by omega))
  have hQ0 : 0 ≤ logFactors k x := by
    unfold logFactors
    apply Finset.prod_nonneg
    intro j hj
    have h := iterLog_ge_base_of_cutoff hH1 k x hlo (j + 1)
      (by have := Finset.mem_range.mp hj; omega)
    linarith
  have htail := tail_argument_bounded hH hlo hhi
  by_cases hkh : k ≤ h
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkh
    rw [stoppedProduct_split k r x hactive]
    have h := mul_le_mul_of_nonneg_left (hbound r (iterLog k x) htail) hQ0
    simpa [mul_comm] using h
  · have hhk : h ≤ k := le_of_lt (lt_of_not_ge hkh)
    have hsplit := stoppedProduct_split k 0 x hactive
    simp only [Nat.add_zero, stoppedProduct, mul_one] at hsplit
    calc
      stoppedProduct h x ≤ stoppedProduct k x := stoppedProduct_mono_height hhk x
      _ = logFactors k x := hsplit
      _ ≤ C * logFactors k x := by nlinarith

theorem exists_full_product_comparison {H : ℝ} (hH : 16 ≤ H)
    (hlogH : 4096 ≤ Real.log H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, H ≤ x →
      ∃ k : ℕ, cutoff H k ≤ x ∧ ∀ h : ℕ, stoppedProduct h x ≤ C * logFactors k x := by
  obtain ⟨C, hC, hbound⟩ := stoppedProduct_uniform_bound (Real.exp (3 * H ^ 2))
  refine ⟨C, hC, ?_⟩
  intro x hx
  obtain ⟨k, hlo, hhi⟩ := exists_adaptive_depth (show 1 ≤ H by linarith) hx
  exact ⟨k, hlo, fun h => full_product_le_partial hH hlogH C hC hbound hlo hhi.le h⟩

end Erdos320.LowerAnalytic
end


-- Adapted from Erdos320.UpperRecurrence.
section
/-
The upper recursion from the classical prime-block decomposition, in the
form used by Luo, Yang, and Zhu. This is a finite combinatorial/elementary
analytic ingredient; the growing-depth asymptotic still requires proof.
-/

namespace Erdos320

theorem eventual_upper_recurrence :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in Filter.atTop,
      logS N ≤ A * ((N : ℝ) / Real.log N) +
        ∑ p ∈ largePrimes N, logS (N / p) := by
  refine ⟨Real.log 4 + 216 / Real.log 2 + 8, ?_, ?_⟩
  · have h4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    have hP : ∀ p ∈ largePrimes N, 0 < p := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2.1.pos
    exact (finite_block_log_bound N (largePrimes N) hP).trans
      (add_le_add (residual_log_bound N hN) le_rfl)

end Erdos320
end


-- Adapted from Erdos320.LowerCounting.
section
/-
Exact finite counting of the independently constructed compatible-prime
products. Each denominator is counted at most once, because its prime factor
strictly exceeds the cofactor. All prime-counting estimates are separate.
-/

namespace Erdos320

def admissiblePrimes (m N : ℕ) : Finset ℕ :=
  (Finset.Ioc (compatibilityCutoff m) (N / m)).filter Nat.Prime

def primeProducts (m N : ℕ) : Finset ℕ :=
  (admissiblePrimes m N).image (fun p => m * p)

theorem primeCounting_le_independent_card (N : ℕ) :
    Nat.primeCounting N ≤ (independentDenominators N).card := by
  have hsub : Nat.primesLE N ⊆ independentDenominators N := by
    intro p hp
    obtain ⟨hpN, hpPrime⟩ := Nat.mem_primesLE.mp hp
    exact primes_in_independentDenominators hpPrime hpN
  simpa using Finset.card_le_card hsub

theorem self_le_compatibilityCutoff (m : ℕ) : m ≤ compatibilityCutoff m := by
  have hf : 1 ≤ m.factorial := Nat.factorial_pos m
  have hmul := Nat.mul_le_mul_left (2 * m) hf
  dsimp [compatibilityCutoff]
  simp only [mul_one] at hmul
  omega

theorem prime_product_unique {m n p q : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hmp : m < p) (hnq : n < q) (heq : m * p = n * q) :
    m = n ∧ p = q := by
  by_cases hpq : p = q
  · subst q
    have hmn : m = n := Nat.eq_of_mul_eq_mul_right hp.pos heq
    exact ⟨hmn, rfl⟩
  · have hnpq : ¬p ∣ q := by
      intro h
      exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
    have hnqp : ¬q ∣ p := by
      intro h
      exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
    have hpn : p ∣ n := by
      apply (hp.dvd_mul.mp ?_).resolve_right hnpq
      rw [← heq]
      exact ⟨m, by ring⟩
    have hqm : q ∣ m := by
      apply (hq.dvd_mul.mp ?_).resolve_right hnqp
      rw [heq]
      exact ⟨n, by ring⟩
    have hpnLe : p ≤ n := Nat.le_of_dvd hn hpn
    have hqmLe : q ≤ m := Nat.le_of_dvd hm hqm
    omega

theorem primeProducts_card {m : ℕ} (hm : 0 < m) (N : ℕ) :
    (primeProducts m N).card = (admissiblePrimes m N).card := by
  unfold primeProducts
  apply Finset.card_image_of_injective
  intro p q heq
  exact Nat.eq_of_mul_eq_mul_left hm heq

theorem primeProducts_subset {m N : ℕ} (hm : IndependentDenominator m) :
    primeProducts m N ⊆ independentDenominators N := by
  intro d hd
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hinterval, hpPrime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hlarge, hpN⟩ := Finset.mem_Ioc.mp hinterval
  have hprod : m * p ≤ N := by
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm.1).mp hpN
  rw [independentDenominators, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨Nat.mul_pos hm.1 hpPrime.pos, hprod⟩,
    independent_mul_large_prime hpPrime hm hlarge⟩

theorem primeProducts_disjoint {m n N : ℕ}
    (hm : IndependentDenominator m) (hn : IndependentDenominator n)
    (hmn : m ≠ n) : Disjoint (primeProducts m N) (primeProducts n N) := by
  rw [Finset.disjoint_left]
  intro d hdm hdn
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hdm
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hdn
  obtain ⟨hpI, hpPrime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqI, hqPrime⟩ := Finset.mem_filter.mp hq
  have hmp : m < p := lt_of_le_of_lt (self_le_compatibilityCutoff m)
    (Finset.mem_Ioc.mp hpI).1
  have hnq : n < q := lt_of_le_of_lt (self_le_compatibilityCutoff n)
    (Finset.mem_Ioc.mp hqI).1
  exact hmn (prime_product_unique hm.1 hn.1 hpPrime hqPrime hmp hnq heq.symm).1

theorem sum_admissiblePrimes_card_le (B : Finset ℕ) (N : ℕ)
    (hB : ∀ m ∈ B, IndependentDenominator m) :
    ∑ m ∈ B, (admissiblePrimes m N).card ≤
      (independentDenominators N).card := by
  classical
  have hpair : (B : Set ℕ).PairwiseDisjoint (fun m => primeProducts m N) := by
    intro m hm n hn hmn
    exact primeProducts_disjoint (hB m hm) (hB n hn) hmn
  have hsub : B.biUnion (fun m => primeProducts m N) ⊆ independentDenominators N := by
    intro d hd
    obtain ⟨m, hm, hdm⟩ := Finset.mem_biUnion.mp hd
    exact primeProducts_subset (hB m hm) hdm
  calc
    ∑ m ∈ B, (admissiblePrimes m N).card = ∑ m ∈ B, (primeProducts m N).card := by
      apply Finset.sum_congr rfl
      intro m hm
      exact (primeProducts_card (hB m hm).1 N).symm
    _ = (B.biUnion (fun m => primeProducts m N)).card := (Finset.card_biUnion hpair).symm
    _ ≤ (independentDenominators N).card := Finset.card_le_card hsub

/-- Removing all small primes loses at most their prime count; no ordering
assumption between the two endpoints is required. -/
theorem primeCounting_le_small_add_admissible (m N : ℕ) :
    Nat.primeCounting (N / m) ≤ Nat.primeCounting (compatibilityCutoff m) +
      (admissiblePrimes m N).card := by
  have hsub : Nat.primesLE (N / m) ⊆
      Nat.primesLE (compatibilityCutoff m) ∪ admissiblePrimes m N := by
    intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    by_cases hsmall : p ≤ compatibilityCutoff m
    · exact Finset.mem_union_left _ (Nat.mem_primesLE.mpr ⟨hsmall, hp'.2⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hp'.1⟩, hp'.2⟩
  have hcard := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  simpa using hcard

theorem primeCounting_difference_le_admissible (m N : ℕ) :
    (Nat.primeCounting (N / m) : ℝ) - Nat.primeCounting (compatibilityCutoff m) ≤
      (admissiblePrimes m N).card := by
  have h : (Nat.primeCounting (N / m) : ℝ) ≤
      (Nat.primeCounting (compatibilityCutoff m) : ℝ) +
        (admissiblePrimes m N).card := by
    exact_mod_cast primeCounting_le_small_add_admissible m N
  linarith

theorem finite_compatible_prime_recurrence (B : Finset ℕ) (N : ℕ)
    (hB : ∀ m ∈ B, IndependentDenominator m) :
    ∑ m ∈ B, ((Nat.primeCounting (N / m) : ℝ) -
      Nat.primeCounting (compatibilityCutoff m)) ≤
        ((independentDenominators N).card : ℝ) := by
  calc
    _ ≤ ∑ m ∈ B, ((admissiblePrimes m N).card : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      exact primeCounting_difference_le_admissible m N
    _ ≤ ((independentDenominators N).card : ℝ) := by
      exact_mod_cast sum_admissiblePrimes_card_le B N hB

end Erdos320
end


-- Adapted from Erdos320.PrimeCounting.
section
/- Original uniform prime estimates for the compatible-prime lower construction. -/

namespace Erdos320

open Filter

theorem primeCounting_le_argument (n : ℕ) : Nat.primeCounting n ≤ n := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have hs : Nat.primesLE n ⊆ Finset.Icc 1 n := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).one_le,
      Nat.le_of_mem_primesLE hp⟩
  simpa using Finset.card_le_card hs

theorem prime_count_common_log_lower {n N : ℕ} {e : ℝ}
    (hn : 2 ≤ n) (hnN : n ≤ N) (hpsi : (n : ℝ) - e ≤ Chebyshev.psi n) :
    ((n : ℝ) - e) / Real.log N ≤ (Nat.primeCounting n : ℝ) := by
  have hN : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN
  apply (div_le_iff₀ hlog).mpr
  calc
    (n : ℝ) - e ≤ Chebyshev.psi n := hpsi
    _ ≤ (Nat.primeCounting n : ℝ) * Real.log n :=
      Chebyshev.psi_le_primeCounting_mul_log n
    _ ≤ (Nat.primeCounting n : ℝ) * Real.log N :=
      mul_le_mul_of_nonneg_left
        (Real.log_le_log hn0 (by exact_mod_cast hnN)) (by positivity)

theorem cofactor_quotient_ge_sqrt {N m : ℕ}
    (hN : (4 : ℝ) ≤ N) (hm : 1 ≤ m)
    (hmL : (m : ℝ) ≤ Real.sqrt (Real.log N))
    (hL : Real.log (N : ℝ) ≤ (N : ℝ) / 4) :
    Real.sqrt (N : ℝ) ≤ ((N / m : ℕ) : ℝ) := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := (Real.log_pos (by linarith)).le
  have hsL := Real.sq_sqrt hlog
  have hsN := Real.sq_sqrt hN0
  have hsL0 := Real.sqrt_nonneg (Real.log (N : ℝ))
  have hsN0 := Real.sqrt_nonneg (N : ℝ)
  have hm2 : (m : ℝ) ^ 2 ≤ Real.log N := by nlinarith
  have hmul : 2 * Real.sqrt (N : ℝ) * m ≤ N := by
    have htwom : 2 * (m : ℝ) ≤ Real.sqrt (N : ℝ) := by nlinarith
    nlinarith [mul_nonneg hsN0 (sub_nonneg.mpr htwom)]
  have hdivNat : N < (N / m + 1) * m := by
    simpa [Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < m by omega)
  have hdivR : (N : ℝ) < (((N / m : ℕ) : ℝ) + 1) * m := by exact_mod_cast hdivNat
  have hsN1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by nlinarith
  nlinarith

theorem prime_count_difference_lower {n N b : ℕ} {X e ε : ℝ}
    (hn : 2 ≤ n) (hnN : n ≤ N)
    (hpsi : (n : ℝ) - e ≤ Chebyshev.psi n)
    (hround : X - 1 ≤ (n : ℝ))
    (herror : 1 + e + (b : ℝ) * Real.log N ≤ ε * X) :
    (1 - ε) * X / Real.log N ≤
      (Nat.primeCounting n : ℝ) - Nat.primeCounting b := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp := (div_le_iff₀ hlog).mp (prime_count_common_log_lower hn hnN hpsi)
  have hb : (Nat.primeCounting b : ℝ) ≤ b := by exact_mod_cast primeCounting_le_argument b
  apply (div_le_iff₀ hlog).mpr
  nlinarith [mul_le_mul_of_nonneg_right hb hlog.le]

/-- A fully explicit sufficient set of uniform error conditions. The eventual
version below will discharge these from the quantitative PNT and elementary
growth estimates. -/
theorem uniform_prime_difference_of_bounds {N : ℕ} {z : ℝ}
    (hN : (4 : ℝ) ≤ N) (hL : 8 ≤ Real.log (N : ℝ))
    (hLsmall : Real.log (N : ℝ) ≤ (N : ℝ) / 4)
    (hpower : Real.log (N : ℝ) ^ 5 ≤ N)
    (hz : 1 ≤ z) (hzL : z ≤ Real.log (N : ℝ))
    (hcut : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ Real.sqrt (Real.log N) →
      (compatibilityCutoff m : ℝ) * m * Real.log N ^ 5 ≤ N)
    (hpnt : ∀ x : ℝ, Real.sqrt (N : ℝ) ≤ x →
      |Chebyshev.psi x - x| ≤ x / Real.log x ^ 6) :
    ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ Real.sqrt (Real.log N) →
      ((1 - 1 / z ^ 2) * ((N : ℝ) + 1) / Real.log N) / m ≤
        (Nat.primeCounting (N / m) : ℝ) - Nat.primeCounting (compatibilityCutoff m) := by
  intro m hm hmL
  let L : ℝ := Real.log N
  let n : ℕ := N / m
  let X : ℝ := (N : ℝ) / m
  let e : ℝ := (n : ℝ) / Real.log (n : ℝ) ^ 6
  have hL' : 8 ≤ L := hL
  have hL₀ : 0 < L := by linarith
  have hN₀ : (0 : ℝ) < N := by linarith
  have hm₀ : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsN := Real.sq_sqrt hN₀.le
  have hsN₀ := Real.sqrt_nonneg (N : ℝ)
  have hnsqrt : Real.sqrt (N : ℝ) ≤ (n : ℝ) :=
    cofactor_quotient_ge_sqrt hN hm hmL hLsmall
  have hnsqrt₂ : (2 : ℝ) ≤ Real.sqrt (N : ℝ) := by nlinarith
  have hn : 2 ≤ n := by exact_mod_cast hnsqrt₂.trans hnsqrt
  have hnN : n ≤ N := Nat.div_le_self N m
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn₀ : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogn : L / 2 ≤ Real.log (n : ℝ) := by
    have hh := Real.log_le_log (Real.sqrt_pos.mpr hN₀) hnsqrt
    simpa only [Real.log_sqrt hN₀.le] using hh
  have hL4 : 0 < L ^ 4 := pow_pos hL₀ _
  have hden : L ^ 4 ≤ Real.log (n : ℝ) ^ 6 := by
    have hpre : L ^ 4 ≤ (L / 2) ^ 6 := by
      nlinarith [mul_nonneg (pow_nonneg hL₀.le 4)
        (show 0 ≤ L ^ 2 - 64 by nlinarith)]
    exact hpre.trans (pow_le_pow_left₀ (by linarith) hlogn 6)
  have hnX : (n : ℝ) ≤ X := Nat.cast_div_le
  have he : e ≤ X / L ^ 4 := by
    exact (div_le_div_of_nonneg_left hn₀.le hL4 hden).trans
      (div_le_div_of_nonneg_right hnX hL4.le)
  have hmleL : (m : ℝ) ≤ L := by
    have hsL := Real.sq_sqrt hL₀.le
    have hsL₀ := Real.sqrt_nonneg L
    have : Real.sqrt L ≤ L := by nlinarith
    exact hmL.trans this
  have hfloor : 1 ≤ X / L ^ 4 := by
    apply (le_div_iff₀ hL4).mpr
    apply (le_div_iff₀ hm₀).mpr
    have hh := mul_le_mul_of_nonneg_right hmleL hL4.le
    have hp : L ^ 5 ≤ (N : ℝ) := hpower
    nlinarith only [hh, hp]
  have hcut' : (compatibilityCutoff m : ℝ) * L ≤ X / L ^ 4 := by
    apply (le_div_iff₀ hL4).mpr
    apply (le_div_iff₀ hm₀).mpr
    have hfactor : ((compatibilityCutoff m : ℝ) * L * L ^ 4) * m =
        (compatibilityCutoff m : ℝ) * m * Real.log N ^ 5 := by dsimp [L]; ring
    rw [hfactor]
    exact hcut m hm hmL
  have hpsi : (n : ℝ) - e ≤ Chebyshev.psi n := by
    have hh := (abs_le.mp (hpnt n hnsqrt)).1
    dsimp [e]
    linarith
  have hround : X - 1 ≤ (n : ℝ) := by
    have hh : N < (N / m + 1) * m := by
      simpa [Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < m by omega)
    have hhR : (N : ℝ) < ((n : ℝ) + 1) * m := by exact_mod_cast hh
    have : X < (n : ℝ) + 1 := (div_lt_iff₀ hm₀).mpr hhR
    linarith
  have herror : 1 + e + (compatibilityCutoff m : ℝ) * L ≤ (3 / L ^ 4) * X := by
    calc
      _ ≤ X / L ^ 4 + X / L ^ 4 + X / L ^ 4 := add_le_add (add_le_add hfloor he) hcut'
      _ = (3 / L ^ 4) * X := by ring
  have hprime := prime_count_difference_lower hn hnN hpsi hround herror
  have hz₀ : 0 < z := by linarith
  have hreserve : 4 * (1 / L ^ 4) ≤ 1 / z ^ 2 := by
    have hh : 4 / L ^ 4 ≤ 1 / z ^ 2 := by
      apply (div_le_div_iff₀ hL4 (sq_pos_of_pos hz₀)).mpr
      nlinarith [mul_nonneg (sq_nonneg L) (show 0 ≤ L ^ 2 - 4 by nlinarith)]
    simpa only [div_eq_mul_inv, one_mul] using hh
  have hL45 : L ^ 4 ≤ L ^ 5 := by
    exact pow_le_pow_right₀ (show 1 ≤ L by linarith) (by norm_num)
  have hunit : 1 ≤ (N : ℝ) * (1 / L ^ 4) := by
    have hh : L ^ 4 ≤ (N : ℝ) := hL45.trans hpower
    have hr : (1 : ℝ) ≤ (N : ℝ) / L ^ 4 :=
      (le_div_iff₀ hL4).mpr (by simpa only [one_mul] using hh)
    simpa only [div_eq_mul_inv, one_mul] using hr
  have hcompare : (1 - 1 / z ^ 2) * ((N : ℝ) + 1) ≤
      (1 - 3 / L ^ 4) * N := by
    have hh := mul_le_mul_of_nonneg_right hreserve hN₀.le
    have hd : 0 ≤ 1 / z ^ 2 := by positivity
    rw [show 3 / L ^ 4 = 3 * (1 / L ^ 4) by ring]
    nlinarith only [hh, hunit, hd]
  calc
    _ ≤ ((1 - 3 / L ^ 4) * (N : ℝ) / L) / m :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hcompare hL₀.le) hm₀.le
    _ = (1 - 3 / L ^ 4) * X / L := by dsimp [X]; ring
    _ ≤ (Nat.primeCounting (N / m) : ℝ) - Nat.primeCounting (compatibilityCutoff m) := hprime

end Erdos320
end


-- Adapted from Erdos320.LowerCutoffGrowth.
section
/-
Original uniform growth estimates for the factorial compatibility cutoff.
The inequality m! ≤ m^m ≤ 2^(m²) is sufficient in the square-root logarithmic
cofactor range; no precise factorial asymptotic is needed.
-/

namespace Erdos320

open Filter

theorem log_two_lt_one : Real.log (2 : ℝ) < 1 := by
  have h := Real.log_lt_sub_one_of_pos
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  norm_num at h
  exact h

theorem two_pow_square_le_rpow {N m : ℕ} (hN : 2 ≤ N)
    (hm : (m : ℝ) ≤ Real.sqrt (Real.log (N : ℝ))) :
    (2 : ℝ) ^ (m * m) ≤ (N : ℝ) ^ Real.log (2 : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hsq : (m : ℝ) ^ 2 ≤ Real.log (N : ℝ) :=
    (Real.le_sqrt (by positivity) hL).mp hm
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have hexp : Real.exp (Real.log (2 : ℝ)) = 2 := Real.exp_log (by norm_num)
  calc
    (2 : ℝ) ^ (m * m) =
        Real.exp ((m : ℝ) ^ 2 * Real.log (2 : ℝ)) := by
      rw [← hexp, ← Real.exp_nat_mul]
      congr 1
      norm_num only [Nat.cast_mul, pow_two, Real.log_exp]
    _ ≤ Real.exp (Real.log (N : ℝ) * Real.log (2 : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsq hlog2)
    _ = (N : ℝ) ^ Real.log (2 : ℝ) :=
      (Real.rpow_def_of_pos hNR _).symm

theorem cutoff_cast_le_rpow {N m : ℕ} (hN : 2 ≤ N)
    (hm : (m : ℝ) ≤ Real.sqrt (Real.log (N : ℝ))) :
    (compatibilityCutoff m : ℝ) ≤
      2 * (m : ℝ) * (N : ℝ) ^ Real.log (2 : ℝ) := by
  have hnat : (compatibilityCutoff m : ℝ) ≤ 2 * (m : ℝ) * (2 : ℝ) ^ (m * m) := by
    exact_mod_cast compatibilityCutoff_le_two_pow_square m
  exact hnat.trans (mul_le_mul_of_nonneg_left (two_pow_square_le_rpow hN hm) (by positivity))

/-- The discarded small-prime count is uniformly negligible throughout the
square-root logarithmic cofactor range. -/
theorem eventually_uniform_cutoff_error :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 1 ≤ m →
      (m : ℝ) ≤ Real.sqrt (Real.log (N : ℝ)) →
      (compatibilityCutoff m : ℝ) * m * Real.log (N : ℝ) ^ 5 ≤ (N : ℝ) := by
  have hs : 0 < 1 - Real.log (2 : ℝ) := sub_pos.mpr log_two_lt_one
  have hsmall := (isLittleO_log_rpow_rpow_atTop (6 : ℝ) hs).def
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hnat := tendsto_natCast_atTop_atTop.eventually hsmall
  filter_upwards [hnat, eventually_ge_atTop (2 : ℕ)] with N hsmallN hN
  intro m hm1 hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hsq : (m : ℝ) ^ 2 ≤ Real.log (N : ℝ) :=
    (Real.le_sqrt (by positivity) hL).mp hm
  have hcut := cutoff_cast_le_rpow hN hm
  have hsmall' : Real.log (N : ℝ) ^ 6 ≤
      (1 / 2 : ℝ) * (N : ℝ) ^ (1 - Real.log (2 : ℝ)) := by
    simpa only [Real.norm_eq_abs, Real.rpow_natCast, Real.rpow_ofNat,
      abs_of_nonneg (pow_nonneg hL 6),
      abs_of_nonneg (Real.rpow_nonneg hNpos.le _)] using hsmallN
  have hsmall2 : 2 * Real.log (N : ℝ) ^ 6 ≤
      (N : ℝ) ^ (1 - Real.log (2 : ℝ)) := by linarith
  have hR : 0 ≤ (N : ℝ) ^ Real.log (2 : ℝ) := Real.rpow_nonneg hNpos.le _
  have hL5 : 0 ≤ Real.log (N : ℝ) ^ 5 := pow_nonneg hL 5
  calc
    (compatibilityCutoff m : ℝ) * m * Real.log (N : ℝ) ^ 5 ≤
        (2 * (m : ℝ) * (N : ℝ) ^ Real.log (2 : ℝ)) * m *
          Real.log (N : ℝ) ^ 5 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcut (by positivity)) hL5
    _ = (2 * (m : ℝ) ^ 2 * Real.log (N : ℝ) ^ 5) *
        (N : ℝ) ^ Real.log (2 : ℝ) := by ring
    _ ≤ (2 * Real.log (N : ℝ) ^ 6) * (N : ℝ) ^ Real.log (2 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hR
      nlinarith [mul_le_mul_of_nonneg_right hsq hL5]
    _ ≤ (N : ℝ) ^ (1 - Real.log (2 : ℝ)) *
        (N : ℝ) ^ Real.log (2 : ℝ) := mul_le_mul_of_nonneg_right hsmall2 hR
    _ = (N : ℝ) := by
      rw [← Real.rpow_add hNpos]
      simp

end Erdos320
end


-- Adapted from Erdos320.LowerAnalytic.Renewal.
section
namespace Erdos320.LowerAnalytic

/-- A uniform lower renewal and a prime baseline imply the complete growing-
depth stopped-product lower bound. Every analytic hypothesis is explicit. -/
theorem eventual_lower_from_renewal
    (A : ℕ → ℝ) (y : ℕ → ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hbase : ∀ᶠ N : ℕ in Filter.atTop, c₀ * prefactor N ≤ A N)
    (hrec : ∀ᶠ N : ℕ in Filter.atTop, ∀ M : ℕ, 3 ≤ M → M ≤ y N →
      (1 - 1 / argument N ^ 2) * prefactor N *
        (∑ m ∈ Finset.Ico M (y N), A m / ((m : ℝ) * (m + 1))) ≤ A N)
    (hy : ∀ᶠ N : ℕ in Filter.atTop,
      3 ≤ y N ∧ Real.log (argument N) - 2 ≤ meshCoordinate (y N)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop, c * scale N ≤ A N := by
  have hdata : ∀ᶠ N : ℕ in Filter.atTop,
      c₀ * prefactor N ≤ A N ∧
      (∀ M : ℕ, 3 ≤ M → M ≤ y N →
        (1 - 1 / argument N ^ 2) * prefactor N *
          (∑ m ∈ Finset.Ico M (y N), A m / ((m : ℝ) * (m + 1))) ≤ A N) ∧
      3 ≤ y N ∧ Real.log (argument N) - 2 ≤ meshCoordinate (y N) := by
    filter_upwards [hbase, hrec, hy] with N hb hr hyN
    exact ⟨hb, hr, hyN⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hdata
  let H : ℝ := max (Real.exp 4096) ((N₀ : ℝ) + 16)
  have hH16 : 16 ≤ H := by
    have hmax : (N₀ : ℝ) + 16 ≤ H := le_max_right _ _
    have hN0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
    linarith
  have hlogH : 4096 ≤ Real.log H := by
    have h := Real.log_le_log (Real.exp_pos 4096) (le_max_left (Real.exp 4096) ((N₀ : ℝ) + 16))
    simpa [H] using h
  have hlarge : ∀ N : ℕ, H ≤ argument N → N₀ ≤ N := by
    intro N hN
    have hmax : (N₀ : ℝ) + 16 ≤ H := le_max_right _ _
    have harg := argument_le_succ N
    have hreal : (N₀ : ℝ) ≤ N := by
      push_cast at harg
      linarith
    exact_mod_cast hreal
  have hbaseAll : ∀ N : ℕ, H ≤ argument N → c₀ * prefactor N ≤ A N :=
    fun N hN => (hN₀ N (hlarge N hN)).1
  have hrecAll : ∀ N : ℕ, H ≤ argument N → ∀ M : ℕ, 3 ≤ M → M ≤ y N →
      (1 - 1 / argument N ^ 2) * prefactor N *
        (∑ m ∈ Finset.Ico M (y N), A m / ((m : ℝ) * (m + 1))) ≤ A N :=
    fun N hN => (hN₀ N (hlarge N hN)).2.1
  have hyAll : ∀ N : ℕ, H ≤ argument N →
      3 ≤ y N ∧ Real.log (argument N) - 2 ≤ meshCoordinate (y N) :=
    fun N hN => (hN₀ N (hlarge N hN)).2.2
  have hdepth := depth_lower_bound A y H c₀ hH16 hlogH hc₀ hbaseAll hrecAll hyAll
  obtain ⟨C, hC, hcompare⟩ := exists_full_product_comparison hH16 hlogH
  let c : ℝ := (7 * c₀) / (8 * C)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  have hxevent : ∀ᶠ N : ℕ in Filter.atTop, H ≤ meshCoordinate N := by
    simpa [meshCoordinate] using loglog_nat_tendsto.eventually (Filter.eventually_ge_atTop H)
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ), hxevent] with N hN hxH
  let x : ℝ := meshCoordinate N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hbasic0 : 0 ≤ (N : ℝ) / Real.log N := div_nonneg hNpos.le hlogN.le
  have hx0 : 0 < x := lt_of_lt_of_le (show 0 < H by linarith) hxH
  have hxz : x ≤ argument N := by
    apply Real.log_le_log hlogN
    exact Real.log_le_log hNpos (by exact_mod_cast Nat.le_succ N)
  obtain ⟨k, hk, hfull⟩ := hcompare x hxH
  have hH1 : 1 ≤ H := by linarith
  have hHexp : Real.exp 2 ≤ H := by
    have h := Real.exp_le_exp.mpr (show (2 : ℝ) ≤ Real.log H by linarith)
    simpa [Real.exp_log (show 0 < H by linarith)] using h
  have hlogs : ∀ j : ℕ, 1 ≤ j → j ≤ k → Real.exp 2 ≤ iterLog j x := by
    intro j hj hjk
    exact hHexp.trans (iterLog_ge_base_of_cutoff hH1 k x hk j hjk)
  have hQ0 := logFactors_nonneg_of_logs hlogs
  have hQ : logFactors k x ≤ logFactors k (argument N) := by
    have h := logFactors_monotone_above_power hx0 (by norm_num : (1 : ℝ) / 2 ≤ 1)
      (le_refl (1 : ℝ)) hlogs (show x ^ (1 : ℝ) ≤ argument N by simpa using hxz)
    simpa using h
  have hA := hdepth k N (hk.trans hxz)
  have hcoeff0 : 0 ≤ c₀ * coefficient k := mul_nonneg hc₀.le (coefficient_pos k).le
  have hpref0 : 0 ≤ prefactor N := by unfold prefactor; positivity
  have hcoeff : (7 / 8 : ℝ) * c₀ ≤ c₀ * coefficient k := by
    have h := mul_le_mul_of_nonneg_left (coefficient_lower k) hc₀.le
    nlinarith
  have hpref : (N : ℝ) / Real.log N ≤ prefactor N := by
    unfold prefactor
    apply div_le_div_of_nonneg_right _ hlogN.le
    push_cast
    linarith
  have hraw : (7 / 8 : ℝ) * c₀ * ((N : ℝ) / Real.log N) * logFactors k x ≤ A N := by
    calc
      _ ≤ (c₀ * coefficient k) * prefactor N * logFactors k x :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcoeff hpref hbasic0 hcoeff0) hQ0
      _ ≤ (c₀ * coefficient k) * prefactor N * logFactors k (argument N) :=
        mul_le_mul_of_nonneg_left hQ (mul_nonneg hcoeff0 hpref0)
      _ ≤ A N := hA
  calc
    c * scale N = c * (((N : ℝ) / Real.log N) * stoppedProduct N x) := rfl
    _ ≤ c * (((N : ℝ) / Real.log N) * (C * logFactors k x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hfull N) hbasic0) hc.le
    _ = (7 / 8 : ℝ) * c₀ * ((N : ℝ) / Real.log N) * logFactors k x := by
      dsimp [c]
      field_simp
    _ ≤ A N := hraw

end Erdos320.LowerAnalytic
end


-- Adapted from Erdos320.UpperFinite.Grouping.
section
namespace Erdos320

/-- The prime divisors contributing to the quotient `m`. -/
noncomputable def quotientPrimeFiber (N m : ℕ) : Finset ℕ := by
  classical
  exact (largePrimes N).filter (fun p => N / p = m)

theorem largePrime_quotient_lt_log {N p : ℕ} (hN : 2 ≤ N)
    (hp : p ∈ largePrimes N) : ((N / p : ℕ) : ℝ) < Real.log (N : ℝ) := by
  have hpdata := (Finset.mem_filter.mp hp).2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpdata.1.pos
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmul := (div_lt_iff₀ hlog).mp hpdata.2
  have hdiv : (N : ℝ) / p < Real.log N := by
    apply (div_lt_iff₀ hpR).mpr
    nlinarith
  exact lt_of_le_of_lt Nat.cast_div_le hdiv

theorem largePrime_quotient_mem_logIndex {N p : ℕ} (hN : 2 ≤ N)
    (hp : p ∈ largePrimes N) : N / p ∈ Finset.Icc 1 (logIndex N) := by
  have hppos := (Finset.mem_filter.mp hp).2.1.pos
  have hpN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  apply Finset.mem_Icc.mpr
  exact ⟨(Nat.le_div_iff_mul_le hppos).mpr (by simpa),
    Nat.le_floor (largePrime_quotient_lt_log hN hp).le⟩

/-- Exact grouping, before any analytic estimate or positivity assumption. -/
theorem prime_sum_grouped (N : ℕ) (hN : 2 ≤ N) (f : ℕ → ℝ) :
    (∑ p ∈ largePrimes N, f (N / p)) =
      ∑ m ∈ Finset.Icc 1 (logIndex N), (quotientPrimeFiber N m).card * f m := by
  classical
  have hmap : ∀ p ∈ largePrimes N, N / p ∈ Finset.Icc 1 (logIndex N) :=
    fun _ hp => largePrime_quotient_mem_logIndex hN hp
  have h := Finset.sum_fiberwise_of_maps_to' hmap f
  simpa only [Finset.sum_const, nsmul_eq_mul, quotientPrimeFiber] using h.symm

theorem quotientPrimeFiber_interval {N m : ℕ} (hm : 0 < m) :
    ∀ p ∈ quotientPrimeFiber N m,
      Nat.Prime p ∧ (N : ℝ) / (m + 1) < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ) / m := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpP, hquot⟩
  have hprime := (Finset.mem_filter.mp hpP).2.1
  have hlowNat : N < p * (m + 1) := by
    simpa [hquot] using Nat.lt_mul_div_succ N hprime.pos
  have hhighNat : m * p ≤ N := by
    simpa [hquot] using Nat.div_mul_le_self N p
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨hprime, (div_lt_iff₀ (show (0 : ℝ) < m + 1 by positivity)).mpr ?_,
    (le_div_iff₀ hmR).mpr ?_⟩
  · exact_mod_cast hlowNat
  · exact_mod_cast (show p * m ≤ N by simpa [Nat.mul_comm] using hhighNat)

end Erdos320
end


-- Adapted from Erdos320.LowerAbel.
section
/-
An exact discrete partial-summation identity for the independent-denominator
count, followed by the finite renewal inequality. Analytic estimates for the
prime counts enter through one explicit, separately proved hypothesis.
-/

namespace Erdos320

noncomputable def independentCount (N : ℕ) : ℝ :=
  (independentDenominators N).card

noncomputable def independentWeight (N : ℕ) : ℝ :=
  ∑ d ∈ independentDenominators N, 1 / (d : ℝ)

theorem independentCount_nonneg (N : ℕ) : 0 ≤ independentCount N := by
  unfold independentCount
  positivity

theorem primeCounting_le_independentCount (N : ℕ) :
    (Nat.primeCounting N : ℝ) ≤ independentCount N := by
  unfold independentCount
  exact_mod_cast primeCounting_le_independent_card N

theorem independentCount_log_lower (N : ℕ) :
    independentCount N * Real.log 2 ≤ logS N :=
  independent_count_log_lower N

theorem independentCount_succ (N : ℕ) :
    independentCount (N + 1) = independentCount N +
      if IndependentDenominator (N + 1) then 1 else 0 := by
  have hnew : N + 1 ∉ independentDenominators N := by
    simp [independentDenominators]
  unfold independentCount
  rw [independentDenominators_succ]
  split_ifs <;> simp [hnew]

theorem independentWeight_succ (N : ℕ) :
    independentWeight (N + 1) = independentWeight N +
      if IndependentDenominator (N + 1) then 1 / ((N + 1 : ℕ) : ℝ) else 0 := by
  classical
  have hnew : N + 1 ∉ independentDenominators N := by
    simp [independentDenominators]
  unfold independentWeight
  rw [independentDenominators_succ]
  split_ifs <;> simp [hnew, add_comm]

/-- Finite Abel summation, with no discarded endpoints or analytic limits. -/
theorem independent_weight_abel (N : ℕ) :
    independentWeight N = independentCount N / (N + 1) +
      ∑ m ∈ Finset.Icc 1 N,
        independentCount m / ((m : ℝ) * (m + 1)) := by
  induction N with
  | zero => simp [independentWeight, independentCount, independentDenominators]
  | succ N ih =>
      have hnew : N + 1 ∉ Finset.Icc 1 N := by simp
      have hsum : (∑ m ∈ Finset.Icc 1 (N + 1),
          independentCount m / ((m : ℝ) * (m + 1))) =
          (∑ m ∈ Finset.Icc 1 N,
            independentCount m / ((m : ℝ) * (m + 1))) +
            independentCount (N + 1) /
              (((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) + 1)) := by
        rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ N + 1),
          Finset.sum_insert hnew]
        ring
      rw [independentWeight_succ, ih, hsum]
      simp only [independentCount_succ]
      split_ifs
      all_goals
        norm_num only [Nat.cast_add, Nat.cast_one]
        have h₁ : (N : ℝ) + 1 ≠ 0 := by positivity
        have h₂ : (N : ℝ) + 1 + 1 ≠ 0 := by positivity
        field_simp [h₁, h₂]
        ring

theorem lower_mesh_le_weight (M y : ℕ) (hM : 1 ≤ M) :
    (∑ m ∈ Finset.Ico M y,
      independentCount m / ((m : ℝ) * (m + 1))) ≤ independentWeight y := by
  have hsub : Finset.Ico M y ⊆ Finset.Icc 1 y := by
    intro m hm
    obtain ⟨hMm, hmy⟩ := Finset.mem_Ico.mp hm
    exact Finset.mem_Icc.mpr ⟨le_trans hM hMm, hmy.le⟩
  have hnonneg : ∀ m : ℕ,
      0 ≤ independentCount m / ((m : ℝ) * (m + 1)) := by
    intro m
    exact div_nonneg (independentCount_nonneg m) (by positivity)
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 y,
        independentCount m / ((m : ℝ) * (m + 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro m hm hnot
      exact hnonneg m
    _ ≤ independentWeight y := by
      rw [independent_weight_abel]
      exact le_add_of_nonneg_left
        (div_nonneg (independentCount_nonneg y) (by positivity))

theorem finite_weight_lower (N y : ℕ) (a : ℝ)
    (hprime : ∀ m ∈ independentDenominators y,
      a / (m : ℝ) ≤ (Nat.primeCounting (N / m) : ℝ) -
        Nat.primeCounting (compatibilityCutoff m)) :
    a * independentWeight y ≤ independentCount N := by
  have hB : ∀ m ∈ independentDenominators y, IndependentDenominator m := by
    intro m hm
    exact (Finset.mem_filter.mp hm).2
  calc
    a * independentWeight y = ∑ m ∈ independentDenominators y, a / (m : ℝ) := by
      rw [independentWeight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ ∑ m ∈ independentDenominators y,
        ((Nat.primeCounting (N / m) : ℝ) -
          Nat.primeCounting (compatibilityCutoff m)) := Finset.sum_le_sum hprime
    _ ≤ independentCount N := finite_compatible_prime_recurrence _ N hB

/-- The exact renewal sum to which a uniform prime estimate is applied. -/
theorem finite_lower_mesh (N y M : ℕ) (a : ℝ) (ha : 0 ≤ a) (hM : 1 ≤ M)
    (hprime : ∀ m : ℕ, 1 ≤ m → m ≤ y →
      a / (m : ℝ) ≤ (Nat.primeCounting (N / m) : ℝ) -
        Nat.primeCounting (compatibilityCutoff m)) :
    a * (∑ m ∈ Finset.Ico M y,
      independentCount m / ((m : ℝ) * (m + 1))) ≤ independentCount N := by
  calc
    _ ≤ a * independentWeight y :=
      mul_le_mul_of_nonneg_left (lower_mesh_le_weight M y hM) ha
    _ ≤ independentCount N := by
      apply finite_weight_lower
      intro m hm
      obtain ⟨hmI, hgood⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm1, hmy⟩ := Finset.mem_Icc.mp hmI
      exact hprime m hm1 hmy

end Erdos320
end


-- Adapted from Erdos320.PrimeCountingEventual.
section
namespace Erdos320

open Filter

theorem eventually_basic_prime_conditions :
    ∀ᶠ N : ℕ in atTop,
      (4 : ℝ) ≤ N ∧ 8 ≤ Real.log (N : ℝ) ∧
      Real.log (N : ℝ) ≤ (N : ℝ) / 4 ∧ Real.log (N : ℝ) ^ 5 ≤ N ∧
      1 ≤ Real.log (Real.log ((N + 1 : ℕ) : ℝ)) ∧
      Real.log (Real.log ((N + 1 : ℕ) : ℝ)) ≤ Real.log (N : ℝ) := by
  have hsmall := Real.isLittleO_log_id_atTop.def (by norm_num : (0 : ℝ) < 1 / 4)
  have hpower := (isLittleO_log_rpow_rpow_atTop (5 : ℝ) (s := 1)
    (by norm_num)).def (by norm_num : (0 : ℝ) < 1)
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (4 : ℕ),
    log_nat_tendsto.eventually (eventually_ge_atTop (8 : ℝ)),
    loglog_nat_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),
    hcast.eventually hsmall, hcast.eventually hpower]
    with N hN hlog hloglog hs hp
  have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0 : ℝ) < N := by linarith
  have hl₀ : 0 < Real.log (N : ℝ) := by linarith
  have hs' : Real.log (N : ℝ) ≤ (1 / 4 : ℝ) * N := by
    simpa only [Real.norm_eq_abs, id_eq, abs_of_pos hN₀, abs_of_pos hl₀] using hs
  have hp' : Real.log (N : ℝ) ^ 5 ≤ N := by
    calc
      Real.log (N : ℝ) ^ 5 ≤ |Real.log (N : ℝ) ^ 5| := le_abs_self _
      _ ≤ N := by
        simpa only [Real.rpow_natCast, Real.rpow_ofNat, Real.rpow_one, Real.norm_eq_abs,
          abs_of_pos hN₀, one_mul] using hp
  have harg : Real.log (N : ℝ) ≤ Real.log (((N + 1 : ℕ) : ℝ)) :=
    Real.log_le_log hN₀ (by push_cast; linarith)
  have hz₁ : 1 ≤ Real.log (Real.log (((N + 1 : ℕ) : ℝ))) :=
    hloglog.trans (Real.log_le_log hl₀ harg)
  have hN1₀ : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hlN1₀ : 0 < Real.log (((N + 1 : ℕ) : ℝ)) :=
    Real.log_pos (by push_cast; linarith)
  have harg₂ : (((N + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by push_cast; linarith
  have hh := Real.log_le_log hN1₀ harg₂
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN₀.ne'] at hh
  have hz := Real.log_le_sub_one_of_pos hlN1₀
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  refine ⟨hNR, hlog, ?_, hp', hz₁, ?_⟩ <;> linarith

theorem eventual_prime_difference_of_cutoff_error
    (hcut : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ,
      1 ≤ m → (m : ℝ) ≤ Real.sqrt (Real.log N) →
      (compatibilityCutoff m : ℝ) * m * Real.log N ^ 5 ≤ N) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ,
      1 ≤ m → m ≤ lowerCofactorBound N →
      ((1 - 1 / Real.log (Real.log (((N + 1 : ℕ) : ℝ))) ^ 2) *
          ((N : ℝ) + 1) / Real.log N) / m ≤
        (Nat.primeCounting (N / m) : ℝ) - Nat.primeCounting (compatibilityCutoff m) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventual_psi_error_le_log_power 6)
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_basic_prime_conditions, hcut,
    hsqrt.eventually (eventually_ge_atTop B)] with N hN hcutN hBN
  intro m hm hmy
  have hmR : (m : ℝ) ≤ Real.sqrt (Real.log N) :=
    (by exact_mod_cast hmy : (m : ℝ) ≤ lowerCofactorBound N).trans
      (lowerCofactorBound_cast_le N)
  exact uniform_prime_difference_of_bounds hN.1 hN.2.1 hN.2.2.1
    hN.2.2.2.1 hN.2.2.2.2.1 hN.2.2.2.2.2 hcutN
      (fun x hx => hB x (hBN.trans hx)) m hm hmR

theorem eventual_uniform_prime_difference :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ,
      1 ≤ m → m ≤ lowerCofactorBound N →
      ((1 - 1 / Real.log (Real.log (((N + 1 : ℕ) : ℝ))) ^ 2) *
          ((N : ℝ) + 1) / Real.log N) / m ≤
        (Nat.primeCounting (N / m) : ℝ) - Nat.primeCounting (compatibilityCutoff m) :=
  eventual_prime_difference_of_cutoff_error eventually_uniform_cutoff_error

end Erdos320
end


-- Adapted from Erdos320.UpperAnalyticPrimeBlocks.
section
/- Original uniform quantitative bound for the exact quotient-prime fibers. -/

namespace Erdos320

theorem eventual_quotientPrimeFiber_bound :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ m ∈ Finset.Icc 1 (logIndex N),
      (Real.log (N : ℝ) / (N : ℝ)) * (quotientPrimeFiber N m).card ≤
        (1 + renewalError N) / ((m : ℝ) * (m + 1)) := by
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp (eventual_psi_error_le_log_power 4)
  have hcut : Filter.Tendsto
      (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ) + 1))
      Filter.atTop Filter.atTop :=
    tendsto_div_log_add_one_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_log_scale_conditions,
    log_nat_tendsto.eventually eventually_log_add_one_le_half,
    hcut.eventually (Filter.eventually_ge_atTop X₀)] with N hN hL hcutN
  intro m hm
  have hm₁ : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hm₁R : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hmL : (m : ℝ) ≤ Real.log (N : ℝ) :=
    (show (m : ℝ) ≤ logIndex N by exact_mod_cast (Finset.mem_Icc.mp hm).2).trans hN.2.2.1
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hLr : 0 < Real.log (N : ℝ) := by linarith [hL.1]
  have hden : (m : ℝ) + 1 ≤ Real.log (N : ℝ) + 1 := by linarith
  have hcut_le_a : (N : ℝ) / (Real.log (N : ℝ) + 1) ≤ (N : ℝ) / ((m : ℝ) + 1) :=
    div_le_div_of_nonneg_left hNr.le hm₁R hden
  have ha₀ : 0 < (N : ℝ) / ((m : ℝ) + 1) := div_pos hNr hm₁R
  have hab : (N : ℝ) / ((m : ℝ) + 1) ≤ (N : ℝ) / m :=
    div_le_div_of_nonneg_left hNr.le hmR (by linarith)
  have hlogₐ : Real.log (N : ℝ) - Real.log (Real.log (N : ℝ) + 1) ≤
      Real.log ((N : ℝ) / ((m : ℝ) + 1)) := by
    rw [Real.log_div hNr.ne' hm₁R.ne']
    have hlogden : Real.log ((m : ℝ) + 1) ≤ Real.log (Real.log (N : ℝ) + 1) :=
      Real.log_le_log hm₁R hden
    linarith
  have hlog_b : Real.log (N : ℝ) / 2 ≤ Real.log ((N : ℝ) / m) := by
    have hlogab := Real.log_le_log ha₀ hab
    linarith [hL.2.2]
  have hₐ := hX₀ ((N : ℝ) / ((m : ℝ) + 1)) (hcutN.trans hcut_le_a)
  have h_b := hX₀ ((N : ℝ) / m) (hcutN.trans (hcut_le_a.trans hab))
  have hbound := prime_interval_normalized_uniform (quotientPrimeFiber N m)
    (N : ℝ) (Real.log (N : ℝ)) (m : ℝ) (Real.log (Real.log (N : ℝ) + 1))
    hNr hL.1 hmR hmL hL.2.1 hL.2.2 hlogₐ hlog_b
    (quotientPrimeFiber_interval hmpos) hₐ h_b
  simpa only [renewalError, renewalLogError] using hbound

end Erdos320
end


-- Adapted from Erdos320.LowerRenewal.
section
/-
The actual independent-denominator count satisfies every input to the generic
uniform lower-renewal argument. The prime estimate used here is proved from the
audited quantitative PNT, and the finite counting/Abel steps are exact.
-/

namespace Erdos320

open Filter LowerAnalytic

theorem eventual_independent_prime_baseline :
    ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) * prefactor N ≤ independentCount N := by
  filter_upwards [eventual_uniform_prime_difference,
    eventually_lower_cofactor_conditions, eventually_ge_atTop (2 : ℕ),
    loglog_nat_tendsto.eventually (eventually_ge_atTop (2 : ℝ))]
      with N hprime hy hN hz
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have harg : 2 ≤ argument N := by
    apply le_trans hz
    apply Real.log_le_log hlogPos
    exact Real.log_le_log hNpos (by exact_mod_cast (Nat.le_succ N))
  have hargPos : 0 < argument N := by linarith
  have hfrac : 1 / argument N ^ 2 ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hargPos)).mpr
    nlinarith
  have hpref : 0 ≤ prefactor N := by
    unfold prefactor
    exact div_nonneg (by positivity) hlogPos.le
  have hp := hprime 1 (by norm_num) (by omega)
  have hprime' : (1 - 1 / argument N ^ 2) * prefactor N ≤
      (Nat.primeCounting N : ℝ) - Nat.primeCounting (compatibilityCutoff 1) := by
    simpa only [argument, meshCoordinate, prefactor, Nat.cast_add, Nat.cast_one,
      Nat.div_one, div_one, mul_div_assoc] using hp
  calc
    (1 / 2 : ℝ) * prefactor N ≤
        (1 - 1 / argument N ^ 2) * prefactor N := by
      exact mul_le_mul_of_nonneg_right (by linarith) hpref
    _ ≤ (Nat.primeCounting N : ℝ) :=
      hprime'.trans (sub_le_self _ (by positivity))
    _ ≤ independentCount N := primeCounting_le_independentCount N

theorem eventual_independent_lower_recurrence :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, 3 ≤ M → M ≤ lowerCofactorBound N →
      (1 - 1 / argument N ^ 2) * prefactor N *
        (∑ m ∈ Finset.Ico M (lowerCofactorBound N),
          independentCount m / ((m : ℝ) * (m + 1))) ≤ independentCount N := by
  filter_upwards [eventual_uniform_prime_difference,
    eventually_basic_prime_conditions] with N hprime hsize
  intro M hM hMy
  have hz : 1 ≤ argument N := hsize.2.2.2.2.1
  have hzPos : 0 < argument N := by linarith
  have hfrac : 1 / argument N ^ 2 ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hzPos)).mpr
    nlinarith
  have hlog : 0 ≤ Real.log (N : ℝ) := by linarith [hsize.2.1]
  let a : ℝ := (1 - 1 / argument N ^ 2) * prefactor N
  have ha : 0 ≤ a := by
    dsimp [a, prefactor]
    exact mul_nonneg (by linarith) (div_nonneg (by positivity) hlog)
  have hprime' : ∀ m : ℕ, 1 ≤ m → m ≤ lowerCofactorBound N →
      a / (m : ℝ) ≤ (Nat.primeCounting (N / m) : ℝ) -
        Nat.primeCounting (compatibilityCutoff m) := by
    intro m hm hmy
    simpa only [a, argument, meshCoordinate, prefactor, Nat.cast_add, Nat.cast_one,
      mul_div_assoc] using hprime m hm hmy
  exact finite_lower_mesh N (lowerCofactorBound N) M a ha (by omega) hprime'

theorem eventual_independent_lower_endpoint :
    ∀ᶠ N : ℕ in atTop,
      3 ≤ lowerCofactorBound N ∧
        Real.log (argument N) - 2 ≤ meshCoordinate (lowerCofactorBound N) := by
  filter_upwards [eventually_lower_cofactor_conditions] with N hN
  exact ⟨hN.1, hN.2.2⟩

end Erdos320
end


-- Adapted from Erdos320.UpperAnalyticFinal.
section
/-
Original closure of the upper bound. All prime-number-theorem inputs are proved
through the pinned upstream `MediumPNT`, and the exact finite decomposition is
proved in this project. The tail starts at four, preserving a positive kernel
reserve and hence coefficient one through the complete logarithmic iteration.
-/

namespace Erdos320

theorem logS_nonneg (N : ℕ) : 0 ≤ logS N := by
  have hS : 0 < S N := card_sumsOf_pos (Finset.Icc 1 N)
  have hS₁ : 1 ≤ S N := by omega
  exact Real.log_nonneg (by exact_mod_cast hS₁)

noncomputable def initialEntropyKernelMass : ℝ :=
  ∑ m ∈ Finset.Icc 1 3, logS m / ((m : ℝ) * (m + 1))

theorem initialEntropyKernelMass_nonneg : 0 ≤ initialEntropyKernelMass := by
  apply Finset.sum_nonneg
  intro m hm
  exact div_nonneg (logS_nonneg m) (by positivity)

theorem entropy_kernel_sum_split (q : ℕ) (hq : 3 ≤ q) :
    (∑ m ∈ Finset.Icc 1 q, logS m / ((m : ℝ) * (m + 1))) =
      initialEntropyKernelMass +
        ∑ m ∈ Finset.Icc 4 q, logS m / ((m : ℝ) * (m + 1)) := by
  have hunion : Finset.Icc 1 q = Finset.Icc 1 3 ∪ Finset.Icc 4 q := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdis : Disjoint (Finset.Icc 1 3) (Finset.Icc 4 q) := by
    apply Finset.disjoint_left.mpr
    intro m hm₁ hm₂
    simp only [Finset.mem_Icc] at hm₁ hm₂
    omega
  rw [hunion, Finset.sum_union hdis]
  rfl

theorem tail_entropy_kernel_bound (q : ℕ) (hq : 3 ≤ q) :
    (∑ m ∈ Finset.Icc 4 q, logS m / ((m : ℝ) * (m + 1))) ≤
      runningMaximum normalizedEntropy q *
        (Real.log (Real.log q) - Real.log (Real.log 3)) := by
  have hterm : ∀ m ∈ Finset.Icc 4 q,
      logS m / ((m : ℝ) * (m + 1)) ≤
        (1 / ((m : ℝ) + 1) / Real.log (m : ℝ)) *
          runningMaximum normalizedEntropy q := by
    intro m hm
    have hm₄ := (Finset.mem_Icc.mp hm).1
    have hm₁ : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
    have hm₀ : (0 : ℝ) < m := by linarith
    have hl : 0 < Real.log (m : ℝ) := Real.log_pos hm₁
    have hkernel : 0 ≤ 1 / ((m : ℝ) + 1) / Real.log (m : ℝ) := by positivity
    have hnorm : normalizedEntropy m ≤ runningMaximum normalizedEntropy q :=
      le_runningMaximum_of_le normalizedEntropy (Finset.mem_Icc.mp hm).2
    calc
      logS m / ((m : ℝ) * (m + 1)) =
          (1 / ((m : ℝ) + 1) / Real.log (m : ℝ)) * normalizedEntropy m := by
        dsimp [normalizedEntropy]
        field_simp [hm₀.ne', hl.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm hkernel
  calc
    _ ≤ ∑ m ∈ Finset.Icc 4 q,
        (1 / ((m : ℝ) + 1) / Real.log (m : ℝ)) *
          runningMaximum normalizedEntropy q := Finset.sum_le_sum hterm
    _ = (∑ m ∈ Finset.Icc 4 q, 1 / ((m : ℝ) + 1) / Real.log (m : ℝ)) *
        runningMaximum normalizedEntropy q := (Finset.sum_mul ..).symm
    _ ≤ (Real.log (Real.log q) - Real.log (Real.log 3)) *
        runningMaximum normalizedEntropy q :=
      mul_le_mul_of_nonneg_right (sum_renewalKernel_le q hq)
        (runningMaximum_nonneg normalizedEntropy q)
    _ = _ := by ring

theorem eventual_normalized_upper_recurrence :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in Filter.atTop,
      normalizedEntropy N ≤ A + Real.log (Real.log (Real.log (N : ℝ))) *
        runningMaximum normalizedEntropy (logIndex N) := by
  obtain ⟨A, hA, hrec⟩ := eventual_upper_recurrence
  refine ⟨A + 2 * initialEntropyKernelMass, by nlinarith [initialEntropyKernelMass_nonneg], ?_⟩
  filter_upwards [hrec, eventual_quotientPrimeFiber_bound, eventually_log_scale_conditions,
    eventually_logIndex_three, eventually_renewalError_nonneg, eventually_renewalError_le_one,
    eventually_renewalError_kernel_absorbed] with N hrecN hfiber hN hq₃ hδ₀ hδ₁ habsorb
  have hN₁ : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hN₀ : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN₁
  have hnormalizer : 0 ≤ Real.log (N : ℝ) / (N : ℝ) := div_nonneg hlog.le hN₀.le
  have hδ : 0 ≤ 1 + renewalError N := by linarith
  have hAidentity : (Real.log (N : ℝ) / (N : ℝ)) *
      (A * ((N : ℝ) / Real.log N)) = A := by
    field_simp
  have hnormalized : normalizedEntropy N ≤ A +
      ∑ m ∈ Finset.Icc 1 (logIndex N),
        ((Real.log (N : ℝ) / (N : ℝ)) * (quotientPrimeFiber N m).card) * logS m := by
    calc
      normalizedEntropy N ≤ (Real.log (N : ℝ) / (N : ℝ)) *
          (A * ((N : ℝ) / Real.log N) + ∑ p ∈ largePrimes N, logS (N / p)) :=
        mul_le_mul_of_nonneg_left hrecN hnormalizer
      _ = _ := by
        rw [prime_sum_grouped N hN.1 logS, mul_add, Finset.mul_sum, hAidentity]
        simp only [mul_assoc]
  have hcount : normalizedEntropy N ≤ A + (1 + renewalError N) *
      ∑ m ∈ Finset.Icc 1 (logIndex N), logS m / ((m : ℝ) * (m + 1)) := by
    calc
      _ ≤ A + ∑ m ∈ Finset.Icc 1 (logIndex N),
          ((Real.log (N : ℝ) / (N : ℝ)) * (quotientPrimeFiber N m).card) * logS m :=
        hnormalized
      _ ≤ A + ∑ m ∈ Finset.Icc 1 (logIndex N),
          ((1 + renewalError N) / ((m : ℝ) * (m + 1))) * logS m := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_right (hfiber m hm) (logS_nonneg m)
      _ = _ := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _hm
        ring
  rw [entropy_kernel_sum_split (logIndex N) hq₃] at hcount
  have hq₁ : (1 : ℝ) < logIndex N := by exact_mod_cast (by omega : 1 < logIndex N)
  have hq₀ : (0 : ℝ) < logIndex N := by linarith
  have hlogq : Real.log (logIndex N : ℝ) ≤ Real.log (Real.log (N : ℝ)) :=
    Real.log_le_log hq₀ hN.2.2.1
  have hloglogq : Real.log (Real.log (logIndex N : ℝ)) ≤
      Real.log (Real.log (Real.log (N : ℝ))) :=
    Real.log_le_log (Real.log_pos hq₁) hlogq
  have hfactor : (1 + renewalError N) *
      (Real.log (Real.log (logIndex N : ℝ)) - Real.log (Real.log 3)) ≤
        Real.log (Real.log (Real.log (N : ℝ))) :=
    (mul_le_mul_of_nonneg_left
      (sub_le_sub_right hloglogq (Real.log (Real.log 3))) hδ).trans habsorb
  have htail : (1 + renewalError N) *
      (∑ m ∈ Finset.Icc 4 (logIndex N), logS m / ((m : ℝ) * (m + 1))) ≤
        runningMaximum normalizedEntropy (logIndex N) *
          Real.log (Real.log (Real.log (N : ℝ))) := by
    calc
      _ ≤ (1 + renewalError N) *
          (runningMaximum normalizedEntropy (logIndex N) *
            (Real.log (Real.log (logIndex N : ℝ)) - Real.log (Real.log 3))) :=
        mul_le_mul_of_nonneg_left (tail_entropy_kernel_bound (logIndex N) hq₃) hδ
      _ = runningMaximum normalizedEntropy (logIndex N) *
          ((1 + renewalError N) *
            (Real.log (Real.log (logIndex N : ℝ)) - Real.log (Real.log 3))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfactor
        (runningMaximum_nonneg normalizedEntropy (logIndex N))
  have hbase : (1 + renewalError N) * initialEntropyKernelMass ≤
      2 * initialEntropyKernelMass :=
    mul_le_mul_of_nonneg_right (by linarith) initialEntropyKernelMass_nonneg
  nlinarith only [hcount, htail, hbase]

/-- The full, unbounded-depth upper estimate for Erdős Problem 320. -/
theorem eventual_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop, logS N ≤ C * scale N := by
  obtain ⟨A, hA, hrec⟩ := eventual_normalized_upper_recurrence
  exact eventual_upper_bound_of_normalized_recurrence A hA.le hrec

end Erdos320
end


-- Adapted from Erdos320.Lower.
section
namespace Erdos320

open Filter

theorem eventual_independent_full_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * scale N ≤ independentCount N :=
  LowerAnalytic.eventual_lower_from_renewal independentCount lowerCofactorBound
    (1 / 2) (by norm_num) eventual_independent_prime_baseline
    eventual_independent_lower_recurrence eventual_independent_lower_endpoint

end Erdos320
end


namespace OMA.ReciprocalSums

open Erdos320 Finset

/-- The independent denominators form a single dissociated set. Upon inserting
a new denominator, its translates of the old subset sums are disjoint from the
old subset sums, by the signed-sum condition defining independence. -/
theorem independent_injective (N : ℕ) :
    Set.InjOn (fun T : Finset ℕ => ∑ n ∈ T, (n : ℚ)⁻¹)
      (independentDenominators N).powerset := by
  induction N with
  | zero => simp [independentDenominators, Set.InjOn]
  | succ N ih =>
    rw [independentDenominators_succ]
    split_ifs with h
    · let I := independentDenominators N
      let f := fun T : Finset ℕ => ∑ n ∈ T, (n : ℚ)⁻¹
      have hsub : I ⊆ Icc 1 N := filter_subset _ _
      have old {T : Finset ℕ} (hT : T ∈ I.powerset) : f T ∈ sums N :=
        mem_image.mpr ⟨T, mem_powerset.mpr ((mem_powerset.mp hT).trans hsub), rfl⟩
      have shift {T : Finset ℕ} (hT : T ∈ I.powerset) :
          f (insert (N+1) T) = ((N+1 : ℕ) : ℚ)⁻¹ + f T := by
        apply sum_insert
        exact fun hm => (by simpa using hsub (mem_powerset.mp hT hm) : False)
      have separate {T U : Finset ℕ} (hT : T ∈ I.powerset) (hU : U ∈ I.powerset) :
          f T ≠ f (insert (N+1) U) := by
        intro heq
        have neq := h.2 (f T) (by simpa using old hT) (f U) (by simpa using old hU)
        apply neq
        rw [shift hU] at heq
        linarith
      intro T hT U hU heq
      change T ∈ (insert (N+1) I).powerset at hT
      change U ∈ (insert (N+1) I).powerset at hU
      change f T = f U at heq
      rw [powerset_insert, mem_union] at hT hU
      rcases hT with hT | hT <;> rcases hU with hU | hU
      · exact ih hT hU heq
      · obtain ⟨U, hUold, rfl⟩ := mem_image.mp hU
        exact (separate hT hUold heq).elim
      · obtain ⟨T, hTold, rfl⟩ := mem_image.mp hT
        exact (separate hU hTold heq.symm).elim
      · obtain ⟨T, hTold, rfl⟩ := mem_image.mp hT
        obtain ⟨U, hUold, rfl⟩ := mem_image.mp hU
        rw [shift hTold, shift hUold] at heq
        exact congrArg (insert (N+1)) (ih hTold hUold (add_left_cancel heq))
    · exact ih

/-- A single independent family supplies a lower bound for the optimum. -/
theorem independent_le_optimum (N : ℕ) : independentCount N ≤ Erdos321.R N := by
  change ((independentDenominators N).card : ℝ) ≤ (Erdos321.R N : ℝ)
  apply Nat.cast_le.mpr
  unfold Erdos321.R
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro _ ⟨A, hA, _, rfl⟩
    simpa using card_le_card hA
  · refine ⟨independentDenominators N, filter_subset _ _, ?_, rfl⟩
    simpa only [one_div] using independent_injective N

/-- Even an extremal family's distinct subset sums occur among the full
interval's subset sums. Taking logarithms gives the entropy upper bound. -/
theorem optimum_mul_log_two_le (N : ℕ) : (Erdos321.R N : ℝ) * Real.log 2 ≤ logS N := by
  let sizes := {k : ℕ | ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧
    Set.InjOn (fun T : Finset ℕ => ∑ n ∈ T, (1 : ℚ) / n) A.powerset ∧ A.card = k}
  have hb : BddAbove sizes := by
    refine ⟨N, ?_⟩
    rintro _ ⟨A, hA, _, rfl⟩
    simpa using card_le_card hA
  have hn : sizes.Nonempty := ⟨0, ∅, by simp, by simp [Set.InjOn], rfl⟩
  have hr : Erdos321.R N = sSup sizes := by
    unfold Erdos321.R
    congr 1
    ext k
    constructor
    · rintro ⟨A, ha, hi, rfl⟩
      exact ⟨A, ha, hi, rfl⟩
    · rintro ⟨A, ha, hi, rfl⟩
      exact ⟨A, ha, hi, rfl⟩
  obtain ⟨A, hA, inj, hcard⟩ := Nat.sSup_mem hn hb
  have heq : A.card = Erdos321.R N := hcard.trans hr.symm
  have him : (sumsOf A).card = 2 ^ A.card := by
    rw [sumsOf, card_image_of_injOn, card_powerset]
    simpa only [one_div] using inj
  have hs : sumsOf A ⊆ sums N :=
    image_subset_image (powerset_mono.mpr hA)
  have hnat : 2 ^ Erdos321.R N ≤ S N := by
    rw [← heq, ← him]
    exact card_le_card hs
  have hreal : (2 : ℝ) ^ Erdos321.R N ≤ (S N : ℝ) := by exact_mod_cast hnat
  have hlog := Real.log_le_log (by positivity) hreal
  simpa only [Real.log_pow, logS] using hlog

end OMA.ReciprocalSums

/-- N / log N times log₃ N · log₄ N · …, stopping before the first factor
at most two. The product is one if there are no such factors. -/
noncomputable def OMA.answer (N : ℕ) : ℝ :=
  ((N : ℝ) / Real.log N) * Erdos320.fullLogProduct N

open Filter Erdos320 OMA.ReciprocalSums in
theorem OMA.solution : Erdos321.erdos_321.variants.isTheta.answer = OMA.answer → type_of% @Erdos321.erdos_321.variants.isTheta := by
  intro h
  rw [h]
  obtain ⟨c, hc, hlower⟩ := eventual_independent_full_lower
  obtain ⟨C, hC, hupper⟩ := eventual_upper_bound
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hscale (N : ℕ) (hN : 2 ≤ N) : 0 ≤ scale N := by
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))))
      (stoppedProduct_pos _ _).le
  constructor
  · apply Asymptotics.IsBigO.of_bound (C / Real.log 2)
    filter_upwards [hupper, eventually_ge_atTop (2 : ℕ)] with N hu hN
    obtain ⟨hle, _⟩ := problemScale_comparison hN
    change ‖(Erdos321.R N : ℝ)‖ ≤ (C / Real.log 2) * ‖problemScale N‖
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg ((hscale N hN).trans hle)]
    have hb := (optimum_mul_log_two_le N).trans (hu.trans (mul_le_mul_of_nonneg_left hle hC.le))
    calc
      _ ≤ (C * problemScale N) / Real.log 2 := (le_div_iff₀ htwo).mpr hb
      _ = _ := by ring
  · apply Asymptotics.IsBigO.of_bound (3 / c)
    filter_upwards [hlower, eventually_ge_atTop (2 : ℕ)] with N hl hN
    obtain ⟨hle, hthree⟩ := problemScale_comparison hN
    change ‖problemScale N‖ ≤ (3 / c) * ‖(Erdos321.R N : ℝ)‖
    rw [Real.norm_of_nonneg ((hscale N hN).trans hle), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hb := hl.trans (independent_le_optimum N)
    calc
      _ ≤ 3 * scale N := hthree
      _ = (3 / c) * (c * scale N) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)


/-
License for the adapted proof sources

Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
