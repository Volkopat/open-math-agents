import FormalConjectures.ErdosProblems.«402»
import Mathlib

/-!
# The eventual strong form of Graham's gcd conjecture

The directed quotient of (a,b) is a/gcd(a,b). Normalize a finite positive
family by its gcd. For sufficiently large cardinality n, a first-moment
count using the prime number theorem shows that a primitive family whose
quotients are all at most n contains a multiple of some prime q > n/2.
Boyle's divisibility argument then forces 1 or the lcm into the family.
Normalization and the two extremal model scores give both directions of the
equality characterization.

The analytic input is the existing MediumPNT port from Erdős 454.
The original number-theoretic argument is due to Balasubramanian and
Soundararajan, Acta Arith. 75 (1996), 1–38. The counting development
adapts plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e
to include the non-strict quotient boundary. The normalization and large
prime classification reuse JaviSoto's Erdős 402 reductions at
da942fcbcd485eb0c2abd945b618003f9eee41bb in open-math-agents.
-/

/-!
# A quantitative prime number theorem for Erdős 402

This file extracts the proof of MediumPNT from the Erdős 454 long-chord step
in open-math-agents, contributed by sobrien032:
https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/da942fcbcd485eb0c2abd945b618003f9eee41bb/proofs/Erdos454.erdos_454.R1.H1.lean.
The later prime-counting consequences and the long-chord argument are omitted.
The source file's attribution and modifications notice follow.

This block adapts the following works, each licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).

1. PrimeNumberTheoremAnd, by Alex Kontorovich, Terence Tao and contributors, at commit
   2c476fa6441c607096d93c8fc7ac0a227a655dae: parts of Mathlib/Algebra/Notation/Support.lean,
   Mathlib/Analysis/SpecialFunctions/Log/Basic.lean, Auxiliary.lean, ZetaConj.lean,
   EulerMaclaurin.lean, Fourier.lean, Rectangle.lean, ResidueCalcOnRectangles.lean,
   ZetaBounds.lean, SmoothExistence.lean, MellinCalculus.lean, MediumPNT.lean and
   Consequences.lean. Auxiliary.lean carries this notice:

   Copyright (c) 2024 Michael Stoll. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Michael Stoll

2. The quantitative prime-counting bridge in Erdos878Proofs/QuantitativePNT.lean, from the proof
   of Erdős Problem 878(iv) by Rivka Lipkovitz, developed with OpenAI Codex: the repository
   erdos-878-cofactor-asymptotic at commit 38d5164065e85d6ef02d1c39253389da1ca64fff.

Modified: ported to Lean 4.33.1 and the board's checker rules, trimmed to the declarations
needed for the error term, merged into one file, and the bridge moved into the namespace
PNTBridge with a final restatement, PNTBridge.piLi_bound.
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

/-! Estimate conversion adapted from the Erdős 402 development in plby/lean-proofs. -/
namespace Erdos402Error
open Filter Asymptotics

private theorem exists_mediumPsi_error
    (pnt : ∃ c : ℝ, 0 < c ∧ (Chebyshev.psi - id) =O[atTop]
      fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤
        C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by
  obtain ⟨c, hc, hO⟩ := pnt
  obtain ⟨C, hC⟩ := hO.bound
  refine ⟨c, |C|, hc, abs_nonneg C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 0] with x hxO hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg] at hxO
  · exact hxO.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  · positivity

/-- Every fixed power of `log x` is dominated by the exponential decay in
`MediumPNT`.  The proof substitutes `t = (log x)^(1/10)` into the standard
polynomial-times-exponential limit. -/
private lemma tendsto_log_pow_mul_mediumDecay (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Tendsto (fun x : ℝ ↦ Real.log x ^ k *
      Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) atTop (nhds 0) := by
  have ht : Tendsto (fun x : ℝ ↦ Real.log x ^ ((1 : ℝ) / 10))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 10)).comp
      Real.tendsto_log_atTop
  have hdecay :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((10 * k : ℕ) : ℝ) c hc).comp ht
  apply hdecay.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  change (Real.log x ^ ((1 : ℝ) / 10)) ^ ((10 * k : ℕ) : ℝ) *
      Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) =
    Real.log x ^ k * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))
  congr 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hlog]
  congr 1
  push_cast
  ring

/-- The medium PNT error is eventually smaller than `δ x / log(x)^k`, for
an arbitrary fixed logarithmic power and arbitrary positive `δ`. -/
theorem logarithmic_error
    (pnt : ∃ c : ℝ, 0 < c ∧ (Chebyshev.psi - id) =O[atTop]
      fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) : ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤ δ * x / Real.log x ^ k := by
  obtain ⟨c, C, hc, hC, hpsi⟩ := exists_mediumPsi_error pnt
  have hlim := (tendsto_log_pow_mul_mediumDecay c hc k).const_mul C
  have hlim' : Tendsto (fun x : ℝ ↦ C * (Real.log x ^ k *
      Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))) atTop (nhds 0) := by
    simpa using hlim
  have hsmall : ∀ᶠ x : ℝ in atTop,
      C * (Real.log x ^ k *
        Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) < δ :=
    (Filter.Eventually.and
      (NormedAddGroup.tendsto_nhds_zero.mp hlim' δ hδ)
      (eventually_ge_atTop 1)).mono fun x hx ↦ by
      rw [Real.norm_of_nonneg] at hx
      · exact hx.1
      · exact mul_nonneg hC (mul_nonneg (pow_nonneg (Real.log_nonneg hx.2) k)
          (Real.exp_pos _).le)
  filter_upwards [hpsi, hsmall, eventually_gt_atTop 1] with x hxpsi hxsmall hx
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx.le
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogpow : 0 < Real.log x ^ k := pow_pos hlog k
  apply hxpsi.trans
  apply (le_div_iff₀ hlogpow).2
  calc
    C * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) *
        Real.log x ^ k =
        x * (C * (Real.log x ^ k *
          Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))) := by ring
    _ ≤ x * δ := mul_le_mul_of_nonneg_left hxsmall.le hx0
    _ = δ * x := by ring

end Erdos402Error

/-! Adapted from Boris Alexeev’s Lean development, formalized by Codex and GPT-5.6 Sol.
Source: https://github.com/plby/lean-proofs/blob/main/src/latest/ErdosProblems/Erdos402.lean
The counting argument follows R. Balasubramanian and K. Soundararajan,
On a conjecture of R. L. Graham, Acta Arithmetica 75 (1996), 1–38.
The theorem below allows equality in every directed quotient bound and concludes that a prime
larger than half the cardinality divides a member. -/
namespace Erdos402Log
open scoped Pointwise
open Filter Asymptotics

private theorem logPowRatio (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.log x ^ b / x ^ a) atTop (nhds 0) := by
  apply (Asymptotics.isLittleO_iff_tendsto' _).mp (isLittleO_log_rpow_rpow_atTop _ ha)
  filter_upwards [eventually_gt_atTop 0] with x hx
  exact (Real.rpow_pos_of_pos hx a).ne' |> fun hn h => False.elim (hn h)

def GrahamBound (A : Finset ℕ) : Prop :=
  (∃ a ∈ A, ∃ b ∈ A, A.card < a / a.gcd b) ∨
  (∃ p : ℕ, p.Prime ∧ A.card < 2*p ∧ ∃ a ∈ A, p ∣ a)

private lemma residue_inj_of_div_gcd_lt {p a b : ℕ} (hp : p.Prime)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hpa : ¬p ∣ a)
    (ha : a / a.gcd b < p) (hb : b / a.gcd b < p)
    (hc : (a : ZMod p) = (b : ZMod p)) : a = b := by
  letI : Fact p.Prime := ⟨hp⟩
  let g := a.gcd b
  let x := a / g
  let y := b / g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
  have hxlt : x < p := ha
  have hylt : y < p := hb
  have hga : g * x = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g * y = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hpg : ¬p ∣ g := fun h ↦ hpa (h.trans (Nat.gcd_dvd_left a b))
  have hcg0 : (g : ZMod p) ≠ 0 := by
    intro hz
    exact hpg ((ZMod.natCast_eq_zero_iff g p).mp hz)
  have hc' : (g : ZMod p) * x = (g : ZMod p) * y := by
    calc
      (g : ZMod p) * x = ((g * x : ℕ) : ZMod p) := (Nat.cast_mul g x).symm
      _ = (a : ZMod p) := congrArg (fun n : ℕ ↦ (n : ZMod p)) hga
      _ = (b : ZMod p) := hc
      _ = ((g * y : ℕ) : ZMod p) := congrArg (fun n : ℕ ↦ (n : ZMod p)) hgb.symm
      _ = (g : ZMod p) * y := Nat.cast_mul g y
  have hxyZ : (x : ZMod p) = y := mul_left_cancel₀ hcg0 hc'
  have hxy : x = y := by
    have hv := congrArg ZMod.val hxyZ
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] using hv
  rw [← hga, ← hgb, hxy]

private def foldedResidue (p a : ℕ) : ℕ :=
  min (a % p) (p - a % p)

private lemma foldedResidue_pos {p a : ℕ} (hp : 0 < p) (hpa : ¬p ∣ a) :
    0 < foldedResidue p a := by
  have hrlt : a % p < p := Nat.mod_lt a hp
  have hr0 : a % p ≠ 0 := by
    intro h
    exact hpa (Nat.dvd_of_mod_eq_zero h)
  unfold foldedResidue
  omega

private lemma foldedResidue_le_div_two {p a : ℕ} (hp : 0 < p) :
    foldedResidue p a ≤ p / 2 := by
  have hrlt : a % p < p := Nat.mod_lt a hp
  unfold foldedResidue
  omega

private lemma foldedResidue_eq_iff {p a b : ℕ} (hp : 0 < p)
    (hpa : ¬p ∣ a) (hpb : ¬p ∣ b)
    (h : foldedResidue p a = foldedResidue p b) :
    a % p = b % p ∨ a % p + b % p = p := by
  have halt : a % p < p := Nat.mod_lt a hp
  have hblt : b % p < p := Nat.mod_lt b hp
  have ha0 : a % p ≠ 0 := fun hz ↦ hpa (Nat.dvd_of_mod_eq_zero hz)
  have hb0 : b % p ≠ 0 := fun hz ↦ hpb (Nat.dvd_of_mod_eq_zero hz)
  unfold foldedResidue at h
  simp only [min_def] at h
  split at h <;> split at h <;> omega

private noncomputable def foldedMin (A : Finset ℕ) (p a : ℕ) : ℕ := by
  classical
  exact if ha : a ∈ A then
    (A.filter fun b ↦ foldedResidue p b = foldedResidue p a).min'
      ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  else 0

private lemma foldedMin_mem {A : Finset ℕ} {p a : ℕ} (ha : a ∈ A) :
    foldedMin A p a ∈ A := by
  classical
  unfold foldedMin
  rw [dif_pos ha]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1

private lemma foldedMin_color {A : Finset ℕ} {p a : ℕ} (ha : a ∈ A) :
    foldedResidue p (foldedMin A p a) = foldedResidue p a := by
  classical
  unfold foldedMin
  rw [dif_pos ha]
  let S := A.filter fun b ↦ foldedResidue p b = foldedResidue p a
  have hS : S.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  exact (Finset.mem_filter.mp (S.min'_mem hS)).2

private lemma foldedMin_le {A : Finset ℕ} {p a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hcolor : foldedResidue p b = foldedResidue p a) : foldedMin A p a ≤ b := by
  classical
  unfold foldedMin
  rw [dif_pos ha]
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨hb, hcolor⟩

private lemma foldedMin_eq_of_color {A : Finset ℕ} {p a b : ℕ}
    (ha : a ∈ A) (hb : b ∈ A)
    (hcolor : foldedResidue p a = foldedResidue p b) :
    foldedMin A p a = foldedMin A p b := by
  apply Nat.le_antisymm
  · apply foldedMin_le ha (foldedMin_mem hb)
    exact (foldedMin_color hb).trans hcolor.symm
  · apply foldedMin_le hb (foldedMin_mem ha)
    exact (foldedMin_color ha).trans hcolor

private def representedMultipliers (A : Finset ℕ) (α β : ℕ) : Finset ℕ :=
  (A.image fun a ↦ a / α).filter fun d ↦ 0 < d ∧ α * d ∈ A ∧ β * d ∈ A

private lemma mem_representedMultipliers {A : Finset ℕ} {α β d : ℕ} (hα : 0 < α) :
    d ∈ representedMultipliers A α β ↔ 0 < d ∧ α * d ∈ A ∧ β * d ∈ A := by
  classical
  constructor
  · exact fun h ↦ (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨α * d, h.2.1, ?_⟩, h⟩
    exact Nat.mul_div_cancel_left d hα

private lemma representedMultipliers_nonzero {A : Finset ℕ} {α β : ℕ} (hα : 0 < α) :
    0 ∉ representedMultipliers A α β := by
  rw [mem_representedMultipliers hα]
  simp

private def representationCount (A : Finset ℕ) (p α : ℕ) : ℕ :=
  (representedMultipliers A α (p - α)).card

private def representationPairs (A : Finset ℕ) (p : ℕ) :
    Finset ((α : ℕ) × ℕ) :=
  (Finset.Icc ((p + 1) / 2) A.card).sigma fun α ↦
    representedMultipliers A α (p - α)

private lemma zero_card_le_excess {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℕ) (h : S.card ≤ S.sum f) :
    (S.filter fun x ↦ f x = 0).card ≤
      (S.filter fun x ↦ 2 ≤ f x).sum fun x ↦ f x - 1 := by
  let Z := S.filter fun x ↦ f x = 0
  let M := S.filter fun x ↦ 2 ≤ f x
  have hZ : Z.card = ∑ x ∈ S, if f x = 0 then 1 else 0 := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_filter (fun x ↦ f x = 0) (fun _ ↦ 1)
  have hM : M.sum (fun x ↦ f x - 1) =
      ∑ x ∈ S, if 2 ≤ f x then f x - 1 else 0 := by
    exact Finset.sum_filter (fun x ↦ 2 ≤ f x) (fun x ↦ f x - 1)
  have hid : S.sum f + Z.card = S.card + M.sum (fun x ↦ f x - 1) := by
    rw [hZ, hM, Finset.card_eq_sum_ones]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> omega
  change Z.card ≤ M.sum fun x ↦ f x - 1
  omega

private def normalize (A : Finset ℕ) : Finset ℕ :=
  A.image fun a ↦ a / A.gcd id

private lemma gcd_pos (A : Finset ℕ) (h₀ : 0 ∉ A) (hA : A.Nonempty) :
    0 < A.gcd id := by
  apply Nat.pos_of_ne_zero
  intro hg
  obtain ⟨a, ha⟩ := hA
  have := Finset.gcd_eq_zero_iff.mp hg a ha
  exact h₀ (this ▸ ha)

private lemma normalize_card (A : Finset ℕ) : (normalize A).card = A.card := by
  classical
  rw [normalize, Finset.card_image_of_injOn]
  intro a ha b hb hab
  have hda : A.gcd id ∣ a := by
    obtain ⟨c, hc⟩ := Finset.gcd_dvd (f := id) ha
    exact ⟨c, hc⟩
  have hdb : A.gcd id ∣ b := by
    obtain ⟨c, hc⟩ := Finset.gcd_dvd (f := id) hb
    exact ⟨c, hc⟩
  exact (Nat.div_left_inj hda hdb).mp hab

private lemma normalize_nonzero (A : Finset ℕ) (h₀ : 0 ∉ A) : 0 ∉ normalize A := by
  classical
  intro h
  obtain ⟨a, ha, hadiv⟩ := Finset.mem_image.mp h
  have hgda : A.gcd id ∣ a := Finset.gcd_dvd ha
  have ha0 : a ≠ 0 := fun hzero ↦ h₀ (hzero ▸ ha)
  have hdiv0 : a / A.gcd id ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hgda)
      (gcd_pos A h₀ ⟨a, ha⟩)
  exact hdiv0 hadiv

private lemma normalize_gcd (A : Finset ℕ) (h₀ : 0 ∉ A) (hA : A.Nonempty) :
    (normalize A).gcd id = 1 := by
  classical
  unfold normalize
  rw [← Finset.gcd_eq_gcd_image]
  obtain ⟨a, ha⟩ := hA
  exact Finset.gcd_div_id_eq_one ha (fun h ↦ h₀ (h ▸ ha))

private lemma div_gcd_le_card (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (_ha0 : a ≠ 0) : a / a.gcd b ≤ A.card := by
  exact Nat.le_of_not_gt fun e => hbad (Or.inl ⟨a, ha, b, hb, e⟩)

private lemma prime_not_dvd_of_card_le (A : Finset ℕ) (_h₀ : 0 ∉ A)
    (_hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {q : ℕ} (hq : q.Prime)
    (hlarge : A.card ≤ q) {a : ℕ} (ha : a ∈ A) : ¬q ∣ a := by
  have hqpos := hq.pos
  exact fun dv => hbad (Or.inr ⟨q, hq, by omega, a, ha, dv⟩)

private lemma prime_not_dvd_of_card_le_two_mul (A : Finset ℕ) (_h₀ : 0 ∉ A)
    (_hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {q : ℕ} (hq : q.Prime)
    (hlarge : A.card < 2*q) {a : ℕ} (ha : a ∈ A) : ¬q ∣ a := by
  exact fun dv => hbad (Or.inr ⟨q, hq, hlarge, a, ha, dv⟩)

private lemma gcd_mul_cross_of_coprime {a b c d : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (hab : a.Coprime b) (hcd : c.Coprime d) :
    (a * c).gcd (b * d) = a.gcd d * b.gcd c := by
  apply Nat.eq_of_factorization_eq
    (Nat.gcd_pos_of_pos_left _
      (Nat.mul_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hc))).ne'
    (Nat.mul_ne_zero (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left hb))
  intro q
  have habf : min (a.factorization q) (b.factorization q) = 0 := by
    have h := congrArg (fun f ↦ f q) (Nat.factorization_gcd ha hb)
    rw [hab.gcd_eq_one, Nat.factorization_one] at h
    change 0 = min (a.factorization q) (b.factorization q) at h
    exact h.symm
  have hcdf : min (c.factorization q) (d.factorization q) = 0 := by
    have h := congrArg (fun f ↦ f q) (Nat.factorization_gcd hc hd)
    rw [hcd.gcd_eq_one, Nat.factorization_one] at h
    change 0 = min (c.factorization q) (d.factorization q) at h
    exact h.symm
  rw [Nat.factorization_gcd (Nat.mul_ne_zero ha hc) (Nat.mul_ne_zero hb hd),
    Nat.factorization_mul ha hc, Nat.factorization_mul hb hd,
    Nat.factorization_mul (Nat.gcd_ne_zero_left ha) (Nat.gcd_ne_zero_left hb),
    Nat.factorization_gcd ha hd, Nat.factorization_gcd hb hc]
  change min (a.factorization q + c.factorization q)
      (b.factorization q + d.factorization q) =
    min (a.factorization q) (d.factorization q) +
      min (b.factorization q) (c.factorization q)
  omega

private lemma div_gcd_mul_right (x y c : ℕ) (hc : 0 < c) :
    (x * c) / (x * c).gcd (y * c) = x / x.gcd y := by
  rw [Nat.gcd_mul_right, Nat.mul_div_mul_right _ _ hc]

private lemma coprime_prime_sub {p α : ℕ} (hp : p.Prime) (hα : 0 < α)
    (hαp : α < p) : α.Coprime (p - α) := by
  rw [Nat.coprime_sub_self_right hαp.le]
  exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hα hαp)).symm

private lemma factor_closeness {N α β d₁ d₂ : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hαβ : α.Coprime β) (hd : d₁.Coprime d₂)
    (hsq : N * N < 2 * (α * α))
    (hα₁₂ : (α * d₁) / (α * d₁).gcd (β * d₂) ≤ N)
    (hα₂₁ : (α * d₂) / (α * d₂).gcd (β * d₁) ≤ N)
    (hβ₁₂ : (β * d₁) / (β * d₁).gcd (α * d₂) ≤ N)
    (hβ₂₁ : (β * d₂) / (β * d₂).gcd (α * d₁) ≤ N) :
    d₁ = d₁.gcd α * d₁.gcd β ∧
    d₂ = d₂.gcd α * d₂.gcd β ∧
    α * d₁.gcd α ≤ N * d₂.gcd α ∧
    α * d₂.gcd α ≤ N * d₁.gcd α ∧
    β * d₁.gcd β ≤ N * d₂.gcd β ∧
    β * d₂.gcd β ≤ N * d₁.gcd β := by
  have cross {a b : ℕ} (h : a / a.gcd b ≤ N) : a ≤ N * a.gcd b := by
    simpa only [Nat.div_mul_cancel (Nat.gcd_dvd_left a b)] using Nat.mul_le_mul_right (a.gcd b) h
  let X₁ := d₁.gcd α
  let Y₁ := d₁.gcd β
  let X₂ := d₂.gcd α
  let Y₂ := d₂.gcd β
  have hX₁ : 0 < X₁ := Nat.gcd_pos_of_pos_left α hd₁
  have hY₁ : 0 < Y₁ := Nat.gcd_pos_of_pos_left β hd₁
  have hX₂ : 0 < X₂ := Nat.gcd_pos_of_pos_left α hd₂
  have hY₂ : 0 < Y₂ := Nat.gcd_pos_of_pos_left β hd₂
  have hXY₁ : X₁ * Y₁ ∣ d₁ := by
    apply (hαβ.gcd_both d₁ d₁).mul_dvd_of_dvd_of_dvd
    · exact Nat.gcd_dvd_left d₁ α
    · exact Nat.gcd_dvd_left d₁ β
  have hXY₂ : X₂ * Y₂ ∣ d₂ := by
    apply (hαβ.gcd_both d₂ d₂).mul_dvd_of_dvd_of_dvd
    · exact Nat.gcd_dvd_left d₂ α
    · exact Nat.gcd_dvd_left d₂ β
  let Z₁ := d₁ / (X₁ * Y₁)
  let Z₂ := d₂ / (X₂ * Y₂)
  have hZ₁ : 0 < Z₁ := Nat.div_pos (Nat.le_of_dvd hd₁ hXY₁)
    (Nat.mul_pos hX₁ hY₁)
  have hZ₂ : 0 < Z₂ := Nat.div_pos (Nat.le_of_dvd hd₂ hXY₂)
    (Nat.mul_pos hX₂ hY₂)
  have hd₁eq : d₁ = X₁ * Y₁ * Z₁ := by
    simpa [Z₁, mul_comm] using (Nat.div_mul_cancel hXY₁).symm
  have hd₂eq : d₂ = X₂ * Y₂ * Z₂ := by
    simpa [Z₂, mul_comm] using (Nat.div_mul_cancel hXY₂).symm
  have hgα₁₂ : (α * d₁).gcd (β * d₂) = X₂ * Y₁ := by
    rw [gcd_mul_cross_of_coprime hα.ne' hβ.ne' hd₁.ne' hd₂.ne' hαβ hd]
    simp only [X₂, Y₁, Nat.gcd_comm]
  have hgα₂₁ : (α * d₂).gcd (β * d₁) = X₁ * Y₂ := by
    rw [gcd_mul_cross_of_coprime hα.ne' hβ.ne' hd₂.ne' hd₁.ne' hαβ hd.symm]
    simp only [X₁, Y₂, Nat.gcd_comm]
  have hgβ₁₂ : (β * d₁).gcd (α * d₂) = Y₂ * X₁ := by
    rw [gcd_mul_cross_of_coprime hβ.ne' hα.ne' hd₁.ne' hd₂.ne' hαβ.symm hd]
    simp only [Y₂, X₁, Nat.gcd_comm]
  have hgβ₂₁ : (β * d₂).gcd (α * d₁) = Y₁ * X₂ := by
    rw [gcd_mul_cross_of_coprime hβ.ne' hα.ne' hd₂.ne' hd₁.ne' hαβ.symm hd.symm]
    simp only [Y₁, X₂, Nat.gcd_comm]
  have hiα₁₂ : α * X₁ * Z₁ ≤ N * X₂ := by
    have bound := cross hα₁₂
    rw [hgα₁₂] at bound
    rw [hd₁eq] at bound
    apply Nat.le_of_mul_le_mul_right _ hY₁
    simpa only [mul_assoc, mul_comm, mul_left_comm] using bound
  have hiα₂₁ : α * X₂ * Z₂ ≤ N * X₁ := by
    have bound := cross hα₂₁
    rw [hgα₂₁] at bound
    rw [hd₂eq] at bound
    apply Nat.le_of_mul_le_mul_right _ hY₂
    simpa only [mul_assoc, mul_comm, mul_left_comm] using bound
  have hprod : α * α * (Z₁ * Z₂) ≤ N * N := by
    have hm := Nat.mul_le_mul hiα₁₂ hiα₂₁
    have hm' : (α * α * (Z₁ * Z₂)) * (X₁ * X₂) ≤
        (N * N) * (X₁ * X₂) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hm
    exact Nat.le_of_mul_le_mul_right hm' (Nat.mul_pos hX₁ hX₂)
  have hZone : Z₁ * Z₂ = 1 := by
    have hlt : α * α * (Z₁ * Z₂) < α * α * 2 := by
      exact hprod.trans_lt (by simpa only [mul_comm] using hsq)
    have hlt' : Z₁ * Z₂ < 2 :=
      (Nat.mul_lt_mul_left (Nat.mul_pos hα hα)).mp hlt
    have hpos : 0 < Z₁ * Z₂ := Nat.mul_pos hZ₁ hZ₂
    omega
  have hz₁one : Z₁ = 1 := Nat.dvd_one.mp ⟨Z₂, hZone.symm⟩
  have hz₂one : Z₂ = 1 :=
    Nat.dvd_one.mp ⟨Z₁, by simpa [mul_comm] using hZone.symm⟩
  have hd₁fac : d₁ = X₁ * Y₁ := by simpa [hz₁one] using hd₁eq
  have hd₂fac : d₂ = X₂ * Y₂ := by simpa [hz₂one] using hd₂eq
  have hiβ₁₂ : β * Y₁ ≤ N * Y₂ := by
    have bound := cross hβ₁₂
    rw [hgβ₁₂] at bound
    rw [hd₁fac] at bound
    apply Nat.le_of_mul_le_mul_right _ hX₁
    simpa only [mul_assoc, mul_comm, mul_left_comm] using bound
  have hiβ₂₁ : β * Y₂ ≤ N * Y₁ := by
    have bound := cross hβ₂₁
    rw [hgβ₂₁] at bound
    rw [hd₂fac] at bound
    apply Nat.le_of_mul_le_mul_right _ hX₂
    simpa only [mul_assoc, mul_comm, mul_left_comm] using bound
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [X₁, Y₁] using hd₁fac
  · simpa only [X₂, Y₂] using hd₂fac
  · simpa only [X₁, X₂] using (by simpa [hz₁one] using hiα₁₂)
  · simpa only [X₁, X₂] using (by simpa [hz₂one] using hiα₂₁)
  · simpa only [Y₁, Y₂] using hiβ₁₂
  · simpa only [Y₁, Y₂] using hiβ₂₁

private lemma factor_closeness_of_counterexample (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {α β d₁ d₂ c : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hc : 0 < c)
    (hαβ : α.Coprime β) (hd : d₁.Coprime d₂)
    (hsq : A.card * A.card < 2 * (α * α))
    (hαd₁ : α * d₁ * c ∈ A) (hβd₁ : β * d₁ * c ∈ A)
    (hαd₂ : α * d₂ * c ∈ A) (hβd₂ : β * d₂ * c ∈ A) :
    d₁ = d₁.gcd α * d₁.gcd β ∧
    d₂ = d₂.gcd α * d₂.gcd β ∧
    α * d₁.gcd α ≤ A.card * d₂.gcd α ∧
    α * d₂.gcd α ≤ A.card * d₁.gcd α ∧
    β * d₁.gcd β ≤ A.card * d₂.gcd β ∧
    β * d₂.gcd β ≤ A.card * d₁.gcd β := by
  apply factor_closeness hα hβ hd₁ hd₂ hαβ hd hsq
  · have h := div_gcd_le_card A hbad hαd₁ hβd₂
      (Nat.mul_ne_zero (Nat.mul_ne_zero hα.ne' hd₁.ne') hc.ne')
    simpa only [div_gcd_mul_right (α * d₁) (β * d₂) c hc] using h
  · have h := div_gcd_le_card A hbad hαd₂ hβd₁
      (Nat.mul_ne_zero (Nat.mul_ne_zero hα.ne' hd₂.ne') hc.ne')
    simpa only [div_gcd_mul_right (α * d₂) (β * d₁) c hc] using h
  · have h := div_gcd_le_card A hbad hβd₁ hαd₂
      (Nat.mul_ne_zero (Nat.mul_ne_zero hβ.ne' hd₁.ne') hc.ne')
    simpa only [div_gcd_mul_right (β * d₁) (α * d₂) c hc] using h
  · have h := div_gcd_le_card A hbad hβd₂ hαd₁
      (Nat.mul_ne_zero (Nat.mul_ne_zero hβ.ne' hd₂.ne') hc.ne')
    simpa only [div_gcd_mul_right (β * d₂) (α * d₁) c hc] using h

private lemma gcd_quotients_sum_prime_of_folded_eq (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    {p a b : ℕ} (hp : p.Prime) (hlower : A.card < p)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hfold : foldedResidue p a = foldedResidue p b) :
    a / a.gcd b + b / a.gcd b = p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpfree {x : ℕ} (hx : x ∈ A) : ¬p ∣ x :=
    prime_not_dvd_of_card_le A h₀ hgcd hbad hp (Nat.le_of_lt hlower) hx
  have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ ha)
  have hb0 : b ≠ 0 := fun hz ↦ h₀ (hz ▸ hb)
  have hqa : a / a.gcd b < p :=
    (div_gcd_le_card A hbad ha hb ha0).trans_lt hlower
  have hqbRaw : b / b.gcd a < p :=
    (div_gcd_le_card A hbad hb ha hb0).trans_lt hlower
  have hqb : b / a.gcd b < p := by simpa [Nat.gcd_comm] using hqbRaw
  rcases foldedResidue_eq_iff hp.pos (hpfree ha) (hpfree hb) hfold with hsame | hsum
  · have hcast : (a : ZMod p) = (b : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff' a b p).mpr hsame
    exact (hab (residue_inj_of_div_gcd_lt hp ha0 hb0 (hpfree ha)
      hqa hqb hcast)).elim
  · let g := a.gcd b
    let x := a / g
    let y := b / g
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
    have hga : g * x = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
    have hgb : g * y = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
    have hpg : ¬p ∣ g := fun h ↦ (hpfree ha) (h.trans (Nat.gcd_dvd_left a b))
    have hcg0 : (g : ZMod p) ≠ 0 := by
      intro hz
      exact hpg ((ZMod.natCast_eq_zero_iff g p).mp hz)
    have hpab : p ∣ a + b := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod, hsum, Nat.mod_self]
    have hcastsum : (a : ZMod p) + (b : ZMod p) = 0 := by
      rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
      exact hpab
    have hfactor : (g : ZMod p) * ((x : ZMod p) + (y : ZMod p)) = 0 := by
      rw [mul_add]
      calc
        (g : ZMod p) * x + (g : ZMod p) * y =
            ((g * x : ℕ) : ZMod p) + ((g * y : ℕ) : ZMod p) := by
              rw [Nat.cast_mul, Nat.cast_mul]
        _ = (a : ZMod p) + (b : ZMod p) := by rw [hga, hgb]
        _ = 0 := hcastsum
    have hxycast : (x : ZMod p) + (y : ZMod p) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hcg0
    have hpxy : p ∣ x + y := by
      apply (ZMod.natCast_eq_zero_iff (x + y) p).mp
      simpa only [Nat.cast_add] using hxycast
    have hxpos : 0 < x :=
      Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha0)) hgpos
    have hypos : 0 < y :=
      Nat.div_pos (Nat.gcd_le_right a (Nat.pos_of_ne_zero hb0)) hgpos
    have hxlt : x < p := by simpa only [x, g] using hqa
    have hylt : y < p := by simpa only [y, g] using hqb
    have hxy : x + y = p :=
      Nat.eq_of_dvd_of_lt_two_mul (by omega) hpxy (by omega)
    simpa only [g, x, y] using hxy

private lemma card_J_le_representationPairs (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {p : ℕ} (hp : p.Prime)
    (hlower : A.card < p) (hupper : p < 2 * A.card) :
    (Finset.Icc ((p + 1) / 2) A.card).card ≤ (representationPairs A p).card := by
  classical
  have hpfree {a : ℕ} (ha : a ∈ A) : ¬p ∣ a :=
    prime_not_dvd_of_card_le A h₀ hgcd hbad hp (Nat.le_of_lt hlower) ha
  let R := A.filter fun a ↦ foldedMin A p a = a
  let E := A.filter fun a ↦ foldedMin A p a ≠ a
  have hpartition : R.card + E.card = A.card := by
    simpa only [R, E] using
      (Finset.card_filter_add_card_filter_not
        (s := A) (p := fun a ↦ foldedMin A p a = a))
  let color : {a // a ∈ R} → Fin (p / 2) := fun a ↦
    ⟨foldedResidue p a.1 - 1, by
      have haA : a.1 ∈ A := (Finset.mem_filter.mp a.2).1
      have hpos := foldedResidue_pos hp.pos (hpfree haA)
      have hle := foldedResidue_le_div_two (a := a.1) hp.pos
      omega⟩
  have hcolor : Function.Injective color := by
    intro a b hab
    apply Subtype.ext
    have haA : a.1 ∈ A := (Finset.mem_filter.mp a.2).1
    have hbA : b.1 ∈ A := (Finset.mem_filter.mp b.2).1
    have hapos := foldedResidue_pos hp.pos (hpfree haA)
    have hbpos := foldedResidue_pos hp.pos (hpfree hbA)
    have hval := congrArg Fin.val hab
    have hfold : foldedResidue p a.1 = foldedResidue p b.1 := by
      dsimp only [color] at hval
      omega
    have hmins := foldedMin_eq_of_color haA hbA hfold
    have harep : foldedMin A p a.1 = a.1 := (Finset.mem_filter.mp a.2).2
    have hbrep : foldedMin A p b.1 = b.1 := (Finset.mem_filter.mp b.2).2
    exact harep.symm.trans (hmins.trans hbrep)
  have hRcard : R.card ≤ p / 2 := by
    have hle := Fintype.card_le_of_injective color hcolor
    simpa using hle
  have hpne : p ≠ 2 := by
    intro hp2
    rw [hp2] at hlower hupper
    omega
  have hpmod : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hpne)
  have hJcard : (Finset.Icc ((p + 1) / 2) A.card).card = A.card - p / 2 := by
    rw [Nat.card_Icc]
    omega
  have hJleE : (Finset.Icc ((p + 1) / 2) A.card).card ≤ E.card := by
    rw [hJcard]
    omega
  let collisionMap : ℕ → ((α : ℕ) × ℕ) := fun a ↦
    ⟨a / (foldedMin A p a).gcd a, (foldedMin A p a).gcd a⟩
  have hmaps : Set.MapsTo collisionMap (↑E : Set ℕ) (↑(representationPairs A p)) := by
    intro a haE
    have haE' : a ∈ E := haE
    have haA : a ∈ A := (Finset.mem_filter.mp haE').1
    have hne : foldedMin A p a ≠ a := (Finset.mem_filter.mp haE').2
    let b := foldedMin A p a
    let g := b.gcd a
    have hbA : b ∈ A := foldedMin_mem haA
    have hfold : foldedResidue p b = foldedResidue p a := foldedMin_color haA
    have hble : b ≤ a := foldedMin_le haA haA rfl
    have hblt : b < a := hble.lt_of_ne hne
    have hb0 : b ≠ 0 := fun hz ↦ h₀ (hz ▸ hbA)
    have ha0 : a ≠ 0 := fun hz ↦ h₀ (hz ▸ haA)
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left a (Nat.pos_of_ne_zero hb0)
    have hgb : (b / g) * g = b := by
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left b a)
    have hga : (a / g) * g = a := by
      exact Nat.div_mul_cancel (Nat.gcd_dvd_right b a)
    have hsum : b / g + a / g = p := by
      simpa only [b, g] using gcd_quotients_sum_prime_of_folded_eq A h₀ hgcd hbad hp
        hlower hbA haA hne hfold
    have hquotorder : b / g < a / g := by
      apply (Nat.mul_lt_mul_right hgpos).mp
      simpa only [hgb, hga] using hblt
    have hαpos : 0 < a / g := by omega
    have hαlower : (p + 1) / 2 ≤ a / g := by omega
    have hαlt : a / g ≤ A.card := by
      have h := div_gcd_le_card A hbad haA hbA ha0
      simpa only [g, Nat.gcd_comm] using h
    have hβ : p - a / g = b / g := by omega
    change (⟨a / g, g⟩ : (α : ℕ) × ℕ) ∈ representationPairs A p
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hαlower, hαlt⟩, ?_⟩
    rw [mem_representedMultipliers hαpos]
    refine ⟨hgpos, ?_, ?_⟩
    · rw [hga]
      exact haA
    rw [hβ]
    rw [hgb]
    exact hbA
  have hinj : Set.InjOn collisionMap (↑E : Set ℕ) := by
    intro a ha b hb hab
    have hprod := congrArg (fun z : (α : ℕ) × ℕ ↦ z.1 * z.2) hab
    dsimp only [collisionMap] at hprod
    calc
      a = (a / (foldedMin A p a).gcd a) * (foldedMin A p a).gcd a :=
        (Nat.div_mul_cancel (Nat.gcd_dvd_right (foldedMin A p a) a)).symm
      _ = (b / (foldedMin A p b).gcd b) * (foldedMin A p b).gcd b := hprod
      _ = b := Nat.div_mul_cancel (Nat.gcd_dvd_right (foldedMin A p b) b)
  exact hJleE.trans (Finset.card_le_card_of_injOn collisionMap hmaps hinj)

private lemma zero_card_le_representation_excess (A : Finset ℕ) (h₀ : 0 ∉ A)
    (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A) {p : ℕ} (hp : p.Prime)
    (hlower : A.card < p) (hupper : p < 2 * A.card) :
    ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        representationCount A p α = 0).card ≤
      ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        2 ≤ representationCount A p α).sum fun α ↦ representationCount A p α - 1 := by
  apply zero_card_le_excess
  calc
    (Finset.Icc ((p + 1) / 2) A.card).card ≤
        (representationPairs A p).card :=
      card_J_le_representationPairs A h₀ hgcd hbad hp hlower hupper
    _ = (Finset.Icc ((p + 1) / 2) A.card).sum
        (representationCount A p) := by
      rw [representationPairs, Finset.card_sigma]
      rfl

private lemma lcm_div_gcd_eq (a : ℕ) (ha : a ≠ 0) (S : Finset ℕ) :
    S.lcm (fun b ↦ a / a.gcd b) = a / a.gcd (S.gcd id) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Nat.div_self (Nat.pos_of_ne_zero ha)]
  | @insert b S hb ih =>
      rw [Finset.lcm_insert, Finset.gcd_insert, ih]
      change Nat.lcm (a / a.gcd b) (a / a.gcd (S.gcd id)) =
        a / a.gcd (b.gcd (S.gcd id))
      rw [Nat.div_lcm_eq_div_gcd (Nat.gcd_dvd_left a b)
        (Nat.gcd_dvd_left a (S.gcd id))]
      have hden : (a.gcd b).gcd (a.gcd (S.gcd id)) =
          a.gcd (b.gcd (S.gcd id)) := by
        rw [Nat.gcd_assoc, Nat.gcd_left_comm b a (S.gcd id), ← Nat.gcd_assoc,
          Nat.gcd_self]
      rw [hden]

private lemma normalize_represented_dvd_product (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {α β : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α.Coprime β)
    (hsq : A.card * A.card < 2 * (α * α))
    (hD : (representedMultipliers A α β).Nonempty) :
    ∀ d ∈ normalize (representedMultipliers A α β), d ∣ α * β := by
  classical
  let D := representedMultipliers A α β
  let B := normalize D
  let c := D.gcd id
  have hD₀ : 0 ∉ D := representedMultipliers_nonzero hα
  have hc : 0 < c := gcd_pos D hD₀ hD
  have hBgcd : B.gcd id = 1 := normalize_gcd D hD₀ hD
  have hrepresented : ∀ {d}, d ∈ B →
      0 < d ∧ α * d * c ∈ A ∧ β * d * c ∈ A := by
    intro d hd
    change d ∈ D.image (fun e ↦ e / D.gcd id) at hd
    obtain ⟨e, heD, rfl⟩ := Finset.mem_image.mp hd
    have he := (mem_representedMultipliers hα).mp heD
    have hce : D.gcd id ∣ e := Finset.gcd_dvd heD
    have heq : e / D.gcd id * D.gcd id = e := Nat.div_mul_cancel hce
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd he.1 hce) hc
    · change α * (e / D.gcd id) * D.gcd id ∈ A
      rw [mul_assoc, heq]
      exact he.2.1
    · change β * (e / D.gcd id) * D.gcd id ∈ A
      rw [mul_assoc, heq]
      exact he.2.2
  intro d hdB
  have hdpos := (hrepresented hdB).1
  have hlocal : ∀ e ∈ B, d / d.gcd e ∣ α * β := by
    intro e heB
    have hepos := (hrepresented heB).1
    let g := d.gcd e
    let d' := d / g
    let e' := e / g
    have hg : 0 < g := Nat.gcd_pos_of_pos_left e hdpos
    have hd' : 0 < d' := Nat.div_pos (Nat.gcd_le_left e hdpos) hg
    have he' : 0 < e' := Nat.div_pos (Nat.gcd_le_right d hepos) hg
    have hcop : d'.Coprime e' := Nat.coprime_div_gcd_div_gcd hg
    have hdexpand : d' * (g * c) = d * c := by
      calc
        d' * (g * c) = (d' * g) * c := by simp only [mul_assoc]
        _ = d * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left d e)]
    have heexpand : e' * (g * c) = e * c := by
      calc
        e' * (g * c) = (e' * g) * c := by simp only [mul_assoc]
        _ = e * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right d e)]
    have hfac := factor_closeness_of_counterexample A hbad hα hβ hd' he'
      (Nat.mul_pos hg hc) hαβ hcop hsq
      (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact (hrepresented hdB).2.1)
      (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact (hrepresented hdB).2.2)
      (by rw [mul_assoc, heexpand, ← mul_assoc]; exact (hrepresented heB).2.1)
      (by rw [mul_assoc, heexpand, ← mul_assoc]; exact (hrepresented heB).2.2)
    change d' ∣ α * β
    rw [hfac.1]
    exact Nat.mul_dvd_mul (Nat.gcd_dvd_right d' α) (Nat.gcd_dvd_right d' β)
  have hlcm : B.lcm (fun e ↦ d / d.gcd e) ∣ α * β := Finset.lcm_dvd hlocal
  rw [lcm_div_gcd_eq d hdpos.ne' B, hBgcd, Nat.gcd_one_right, Nat.div_one] at hlcm
  exact hlcm

private lemma gcd_div_gcd_eq_component {α β d e : ℕ}
    (hαβ : α.Coprime β) (hd : 0 < d) (he : 0 < e)
    (hdfac : d = d.gcd α * d.gcd β)
    (hefac : e = e.gcd α * e.gcd β) :
    (d / d.gcd e).gcd α = d.gcd α / (d.gcd α).gcd (e.gcd α) := by
  let u := d.gcd α
  let v := d.gcd β
  let x := e.gcd α
  let y := e.gcd β
  have hu : 0 < u := Nat.gcd_pos_of_pos_left α hd
  have hv : 0 < v := Nat.gcd_pos_of_pos_left β hd
  have hx : 0 < x := Nat.gcd_pos_of_pos_left α he
  have hy : 0 < y := Nat.gcd_pos_of_pos_left β he
  have huα : u ∣ α := Nat.gcd_dvd_right d α
  have hvβ : v ∣ β := Nat.gcd_dvd_right d β
  have hxα : x ∣ α := Nat.gcd_dvd_right e α
  have hyβ : y ∣ β := Nat.gcd_dvd_right e β
  have huy : u.Coprime y := Nat.Coprime.of_dvd huα hyβ hαβ
  have hvx : v.Coprime x := Nat.Coprime.of_dvd hvβ hxα hαβ.symm
  have hgde : d.gcd e = u.gcd x * v.gcd y := by
    rw [hdfac, hefac]
    change (u * v).gcd (x * y) = u.gcd x * v.gcd y
    rw [mul_comm x y,
      gcd_mul_cross_of_coprime hu.ne' hy.ne' hv.ne' hx.ne' huy hvx]
    simp only [Nat.gcd_comm y v]
  have hdiv : d / d.gcd e =
      (u / u.gcd x) * (v / v.gcd y) := by
    rw [hgde, hdfac]
    exact (Nat.div_mul_div_comm (Nat.gcd_dvd_left u x)
      (Nat.gcd_dvd_left v y)).symm
  have huv : u / u.gcd x ∣ α :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left u x)).trans huα
  have hvv : v / v.gcd y ∣ β :=
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left v y)).trans hvβ
  have hcop : (v / v.gcd y).Coprime α :=
    Nat.Coprime.of_dvd hvv dvd_rfl hαβ.symm
  rw [hdiv, mul_comm]
  exact Nat.gcd_mul_of_coprime_of_dvd hcop huv

private def factorTriples (N D n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.Icc 1 n ×ˢ (Finset.Icc 1 D ×ˢ Finset.Icc 1 D)).filter fun t ↦
    n = t.1 * t.2.1 * t.2.2 ∧ t.2.1 < t.2.2 ∧
      n * t.2.2 ≤ N * t.2.1

private def kCount (N D n : ℕ) : ℕ := (factorTriples N D n).card

private lemma mem_factorTriples {N D n l X₁ X₂ : ℕ} :
    (l, (X₁, X₂)) ∈ factorTriples N D n ↔
      1 ≤ l ∧ l ≤ n ∧ 1 ≤ X₁ ∧ X₁ ≤ D ∧ 1 ≤ X₂ ∧ X₂ ≤ D ∧
        n = l * X₁ * X₂ ∧ X₁ < X₂ ∧ n * X₂ ≤ N * X₁ := by
  simp only [factorTriples, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc]
  tauto

private lemma factorTriple_multiplier_mul_le_gap_sq
    {N D n l X₁ X₂ : ℕ} (ht : (l, (X₁, X₂)) ∈ factorTriples N D n) :
    l * N ≤ (N - n) ^ 2 := by
  have h := mem_factorTriples.mp ht
  have hl : 0 < l := by omega
  have hX₁ : 0 < X₁ := by omega
  have hX₂ : 0 < X₂ := by omega
  have hn : 0 < n := by rw [h.2.2.2.2.2.2.1]; positivity
  have hnN : n ≤ N := by
    have hposX₂ : 0 < n * X₂ := Nat.mul_pos hn hX₂
    have hNX₁pos : 0 < N * X₁ := hposX₂.trans_le h.2.2.2.2.2.2.2.2
    by_contra hnot
    have hNn : N < n := Nat.lt_of_not_ge hnot
    have hstrict : N * X₁ < n * X₂ := by
      calc
        N * X₁ < n * X₁ := (Nat.mul_lt_mul_right hX₁).mpr hNn
        _ ≤ n * X₂ := Nat.mul_le_mul_left n (by omega)
    omega
  let δ := N - n
  have hδadd : δ + n = N := Nat.sub_add_cancel hnN
  have hsucc : X₁ + 1 ≤ X₂ := by omega
  have hnδX₁ : n ≤ δ * X₁ := by
    have haux : n * (X₁ + 1) ≤ N * X₁ :=
      (Nat.mul_le_mul_left n hsucc).trans h.2.2.2.2.2.2.2.2
    rw [← hδadd] at haux
    simp only [mul_add, mul_one, add_mul] at haux
    omega
  have hNδX₂ : N ≤ δ * X₂ := by
    rw [← hδadd]
    have hδmono : δ * X₁ + δ ≤ δ * X₂ := by
      calc
        δ * X₁ + δ = δ * (X₁ + 1) := by ring
        _ ≤ δ * X₂ := Nat.mul_le_mul_left δ hsucc
    omega
  have hmul : n * N ≤ (δ * X₁) * (δ * X₂) :=
    Nat.mul_le_mul hnδX₁ hNδX₂
  have hcancel : l * N * (X₁ * X₂) ≤ δ ^ 2 * (X₁ * X₂) := by
    calc
      l * N * (X₁ * X₂) = n * N := by
        rw [h.2.2.2.2.2.2.1]
        ring
      _ ≤ (δ * X₁) * (δ * X₂) := hmul
      _ = δ ^ 2 * (X₁ * X₂) := by ring
  exact Nat.le_of_mul_le_mul_right
    (by simpa only [mul_assoc] using hcancel) (Nat.mul_pos hX₁ hX₂)

private lemma factorTriple_multiplier_le_gap_sq_div
    {N D n l X₁ X₂ : ℕ} (hN : 0 < N)
    (ht : (l, (X₁, X₂)) ∈ factorTriples N D n) :
    l ≤ (N - n) ^ 2 / N := by
  apply (Nat.le_div_iff_mul_le hN).mpr
  simpa only [mul_comm] using factorTriple_multiplier_mul_le_gap_sq ht

private def firstMomentTriples (N D x : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.Icc 1 ((N - x) ^ 2 / N) ×ˢ
      (Finset.Icc 1 D ×ˢ Finset.Icc 1 D)).filter fun t ↦
    t.2.1 < t.2.2 ∧ x ≤ t.1 * t.2.1 * t.2.2 ∧
      t.1 * t.2.1 * t.2.2 ≤ N ∧
      (t.1 * t.2.1 * t.2.2) * t.2.2 ≤ N * t.2.1

private lemma mem_firstMomentTriples {N D x l X₁ X₂ : ℕ} :
    (l, (X₁, X₂)) ∈ firstMomentTriples N D x ↔
      1 ≤ l ∧ l ≤ (N - x) ^ 2 / N ∧
      1 ≤ X₁ ∧ X₁ ≤ D ∧ 1 ≤ X₂ ∧ X₂ ≤ D ∧
      X₁ < X₂ ∧ x ≤ l * X₁ * X₂ ∧ l * X₁ * X₂ ≤ N ∧
      (l * X₁ * X₂) * X₂ ≤ N * X₁ := by
  simp only [firstMomentTriples, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc]
  tauto

private lemma firstMomentTriples_mono_lower
    {N D x₁ x₂ : ℕ} (hxx : x₁ ≤ x₂) :
    firstMomentTriples N D x₂ ⊆ firstMomentTriples N D x₁ := by
  rintro ⟨l, X₁, X₂⟩ ht
  have h := mem_firstMomentTriples.mp ht
  have hgap : N - x₂ ≤ N - x₁ := Nat.sub_le_sub_left hxx N
  have hgapSq : (N - x₂) ^ 2 ≤ (N - x₁) ^ 2 :=
    pow_le_pow_left' hgap 2
  apply mem_firstMomentTriples.mpr
  exact ⟨h.1, h.2.1.trans (Nat.div_le_div_right hgapSq),
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, hxx.trans h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

private lemma firstMomentTriples_mono_cap
    {N D₁ D₂ x : ℕ} (hDD : D₁ ≤ D₂) :
    firstMomentTriples N D₁ x ⊆ firstMomentTriples N D₂ x := by
  rintro ⟨l, X₁, X₂⟩ ht
  have h := mem_firstMomentTriples.mp ht
  apply mem_firstMomentTriples.mpr
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.trans hDD,
    h.2.2.2.2.1, h.2.2.2.2.2.1.trans hDD,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

private lemma sum_kCount_Icc_le_firstMomentTriples_card
    {N D x : ℕ} (hN : 0 < N) :
    (Finset.Icc x N).sum (kCount N D) ≤
      (firstMomentTriples N D x).card := by
  let S := (Finset.Icc x N).sigma fun n ↦ factorTriples N D n
  let forgetN : ((n : ℕ) × (ℕ × (ℕ × ℕ))) → (ℕ × (ℕ × ℕ)) :=
    fun z ↦ z.2
  have hmaps : Set.MapsTo forgetN (↑S : Set ((n : ℕ) × (ℕ × (ℕ × ℕ))))
      (↑(firstMomentTriples N D x) : Set (ℕ × (ℕ × ℕ))) := by
    rintro ⟨n, ⟨l, X₁, X₂⟩⟩ hz
    have hz' := Finset.mem_sigma.mp hz
    have hnI : n ∈ Finset.Icc x N := by simpa using hz'.1
    have htmem : (l, (X₁, X₂)) ∈ factorTriples N D n := by
      simpa using hz'.2
    have ht := mem_factorTriples.mp htmem
    have hgap : N - n ≤ N - x := by
      have hxn := (Finset.mem_Icc.mp hnI).1
      omega
    have hgapSq : (N - n) ^ 2 ≤ (N - x) ^ 2 :=
      pow_le_pow_left' hgap 2
    have hlcut : l ≤ (N - x) ^ 2 / N :=
      (factorTriple_multiplier_le_gap_sq_div hN htmem).trans
        (Nat.div_le_div_right hgapSq)
    apply mem_firstMomentTriples.mpr
    refine ⟨ht.1, hlcut, ht.2.2.1, ht.2.2.2.1,
      ht.2.2.2.2.1, ht.2.2.2.2.2.1,
      ht.2.2.2.2.2.2.2.1, ?_, ?_, ?_⟩
    · simpa only [← ht.2.2.2.2.2.2.1] using (Finset.mem_Icc.mp hnI).1
    · simpa only [← ht.2.2.2.2.2.2.1] using (Finset.mem_Icc.mp hnI).2
    · simpa only [← ht.2.2.2.2.2.2.1] using ht.2.2.2.2.2.2.2.2
  have hinj : Set.InjOn forgetN
      (↑S : Set ((n : ℕ) × (ℕ × (ℕ × ℕ)))) := by
    rintro ⟨n, ⟨l, X₁, X₂⟩⟩ hn
      ⟨m, ⟨k, Y₁, Y₂⟩⟩ hm heq
    have hnmem : (l, (X₁, X₂)) ∈ factorTriples N D n := by
      simpa using (Finset.mem_sigma.mp hn).2
    have hmmem : (k, (Y₁, Y₂)) ∈ factorTriples N D m := by
      simpa using (Finset.mem_sigma.mp hm).2
    have hn' := mem_factorTriples.mp hnmem
    have hm' := mem_factorTriples.mp hmmem
    change (l, (X₁, X₂)) = (k, (Y₁, Y₂)) at heq
    injection heq with hlk hXY
    injection hXY with hX₁ hX₂
    subst k
    subst Y₁
    subst Y₂
    have hnm : n = m :=
      hn'.2.2.2.2.2.2.1.trans hm'.2.2.2.2.2.2.1.symm
    subst m
    rfl
  calc
    (Finset.Icc x N).sum (kCount N D) = S.card := by
      simp only [S, Finset.card_sigma, kCount]
      rfl
    _ ≤ (firstMomentTriples N D x).card :=
      Finset.card_le_card_of_injOn forgetN hmaps hinj

private def squareMomentSide (N H l : ℕ) : ℕ :=
  Nat.sqrt (N / l) + 1 -
    ((N - H) ⌈/⌉ (l * Nat.sqrt (N / l)))

private def squareMomentEnvelope (N H : ℕ) :
    Finset ((l : ℕ) × (ℕ × ℕ)) :=
  (Finset.Icc 1 (H ^ 2 / N)).sigma fun l ↦
    let s := Nat.sqrt (N / l)
    let lo := (N - H) ⌈/⌉ (l * s)
    Finset.Icc lo s ×ˢ Finset.Icc lo s

private lemma firstMomentTriples_card_le_squareMomentEnvelope
    {N H : ℕ} (hN : 0 < N) (hHN : H ≤ N) :
    (firstMomentTriples N N (N - H)).card ≤
      (squareMomentEnvelope N H).card := by
  let toEnvelope : (ℕ × (ℕ × ℕ)) → ((l : ℕ) × (ℕ × ℕ)) :=
    fun t ↦ ⟨t.1, t.2⟩
  apply Finset.card_le_card_of_injOn
    (s := firstMomentTriples N N (N - H))
    (t := squareMomentEnvelope N H) toEnvelope
  · rintro ⟨l, X₁, X₂⟩ ht
    dsimp only [toEnvelope]
    have h := mem_firstMomentTriples.mp ht
    have hlpos : 0 < l := by omega
    have hX₁pos : 0 < X₁ := by omega
    have hX₂pos : 0 < X₂ := by omega
    have hlcut : l ≤ H ^ 2 / N := by
      simpa only [Nat.sub_sub_self hHN] using h.2.1
    have hX₂sq : l * X₂ ^ 2 ≤ N := by
      apply Nat.le_of_mul_le_mul_right (c := X₁) ?_ hX₁pos
      calc
        (l * X₂ ^ 2) * X₁ = (l * X₁ * X₂) * X₂ := by ring
        _ ≤ N * X₁ := h.2.2.2.2.2.2.2.2.2
    have hX₂sqDiv : X₂ ^ 2 ≤ N / l :=
      (Nat.le_div_iff_mul_le hlpos).2 (by simpa only [mul_comm] using hX₂sq)
    have hX₂sqrt : X₂ ≤ Nat.sqrt (N / l) := by
      exact (Nat.le_sqrt).2 (by simpa only [pow_two] using hX₂sqDiv)
    have hspos : 0 < Nat.sqrt (N / l) := hX₂pos.trans_le hX₂sqrt
    have hlowerMul : N - H ≤
        (l * Nat.sqrt (N / l)) * X₁ := by
      calc
        N - H ≤ l * X₁ * X₂ := h.2.2.2.2.2.2.2.1
        _ ≤ l * X₁ * Nat.sqrt (N / l) :=
          Nat.mul_le_mul_left (l * X₁) hX₂sqrt
        _ = (l * Nat.sqrt (N / l)) * X₁ := by ring
    have hloX₁ : (N - H) ⌈/⌉ (l * Nat.sqrt (N / l)) ≤ X₁ :=
      (ceilDiv_le_iff_le_mul (Nat.mul_pos hlpos hspos)).2 hlowerMul
    have hloX₂ : (N - H) ⌈/⌉ (l * Nat.sqrt (N / l)) ≤ X₂ :=
      hloX₁.trans (Nat.le_of_lt h.2.2.2.2.2.2.1)
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨h.1, hlcut⟩, ?_⟩
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hloX₁,
        (Nat.le_of_lt h.2.2.2.2.2.2.1).trans hX₂sqrt⟩,
      Finset.mem_Icc.mpr ⟨hloX₂, hX₂sqrt⟩⟩
  · rintro ⟨l, X₁, X₂⟩ _ ⟨k, Y₁, Y₂⟩ _ heq
    dsimp only [toEnvelope] at heq
    cases heq
    rfl

private lemma squareMomentEnvelope_card (N H : ℕ) :
    (squareMomentEnvelope N H).card =
      ∑ l ∈ Finset.Icc 1 (H ^ 2 / N), (squareMomentSide N H l) ^ 2 := by
  simp only [squareMomentEnvelope, squareMomentSide, Finset.card_sigma,
    Finset.card_product, Nat.card_Icc, pow_two]

private lemma firstMomentTriples_card_le_squareMoment_sum
    {N H : ℕ} (hN : 0 < N) (hHN : H ≤ N) :
    (firstMomentTriples N N (N - H)).card ≤
      ∑ l ∈ Finset.Icc 1 (H ^ 2 / N), (squareMomentSide N H l) ^ 2 := by
  calc
    (firstMomentTriples N N (N - H)).card ≤
        (squareMomentEnvelope N H).card :=
      firstMomentTriples_card_le_squareMomentEnvelope hN hHN
    _ = _ := squareMomentEnvelope_card N H

private lemma squareMomentSide_le_div_add_one
    {N H l : ℕ} (hHN : H ≤ N) (hl : 0 < l) :
    squareMomentSide N H l ≤
      H / (l * Nat.sqrt (N / l)) + 1 := by
  let s := Nat.sqrt (N / l)
  let m := l * s
  let lo := (N - H) ⌈/⌉ m
  by_cases hs : s = 0
  · simp [squareMomentSide, s, m, hs]
  have hspos : 0 < s := Nat.pos_of_ne_zero hs
  have hmpos : 0 < m := Nat.mul_pos hl hspos
  have hms : m * s ≤ N := by
    have hsquare : s * s ≤ N / l := by
      simpa only [s] using Nat.sqrt_le (N / l)
    have := (Nat.le_div_iff_mul_le hl).1 hsquare
    simpa only [m, mul_assoc, mul_comm, mul_left_comm] using this
  by_cases hlo : lo ≤ s + 1
  · have hlower : N - H ≤ m * lo := by
      exact (ceilDiv_le_iff_le_mul hmpos).1 le_rfl
    have hsideLo : squareMomentSide N H l + lo = s + 1 := by
      simpa only [squareMomentSide, s, m, lo] using Nat.sub_add_cancel hlo
    have hsum :
        m * squareMomentSide N H l + m * lo = m * (s + 1) := by
      rw [← Nat.mul_add, hsideLo]
    have hsideMul : m * squareMomentSide N H l ≤ H + m := by
      have hNH : N - H + H = N := Nat.sub_add_cancel hHN
      have hmss : m * (s + 1) = m * s + m := by ring
      omega
    have hdiv : squareMomentSide N H l ≤ (H + m) / m :=
      (Nat.le_div_iff_mul_le hmpos).2 (by
        simpa only [mul_comm] using hsideMul)
    simpa only [m, Nat.add_div_right _ hmpos] using hdiv
  · have hslo : s + 1 ≤ lo := by omega
    simp only [squareMomentSide, s, m, lo]
    rw [Nat.sub_eq_zero_of_le hslo]
    exact Nat.zero_le _

private lemma squareMoment_denominator_sq_lower
    {N H l : ℕ} (hN : 0 < N) (hHN : H ≤ N) (hl : 1 ≤ l)
    (hlcut : l ≤ H ^ 2 / N) :
    N * l ≤ 4 * (l * Nat.sqrt (N / l)) ^ 2 := by
  have hHsq : H ^ 2 ≤ N * H := by
    have := Nat.mul_le_mul_left H hHN
    nlinarith
  have hLleH : H ^ 2 / N ≤ H := Nat.div_le_of_le_mul hHsq
  have hlN : l ≤ N := hlcut.trans (hLleH.trans hHN)
  have hlpos : 0 < l := by omega
  have hqpos : 0 < N / l := Nat.div_pos hlN hlpos
  let s := Nat.sqrt (N / l)
  have hspos : 0 < s := by
    exact Nat.sqrt_pos.mpr hqpos
  have hroot : N / l < (s + 1) * (s + 1) := by
    simpa only [s] using Nat.lt_succ_sqrt (N / l)
  have hqfour : N / l < 4 * s ^ 2 := by
    nlinarith
  have hNfour : N < (4 * s ^ 2) * l :=
    (Nat.div_lt_iff_lt_mul hlpos).1 hqfour
  have hmul := (Nat.mul_lt_mul_right hlpos).2 hNfour
  have hmul' : N * l < 4 * (l * s) ^ 2 := by
    calc
      N * l < (4 * s ^ 2) * l * l := hmul
      _ = 4 * (l * s) ^ 2 := by ring
  simpa only [s] using hmul'.le

private lemma squareMomentSide_sq_real_le
    {N H l : ℕ} (hN : 0 < N) (hHN : H ≤ N) (hl : 1 ≤ l)
    (hlcut : l ≤ H ^ 2 / N) :
    ((squareMomentSide N H l : ℕ) : ℝ) ^ 2 ≤
      8 * (H : ℝ) ^ 2 / ((N : ℝ) * (l : ℝ)) + 2 := by
  let s := Nat.sqrt (N / l)
  let m := l * s
  have hlpos : 0 < l := by omega
  have hdenNat := squareMoment_denominator_sq_lower hN hHN hl hlcut
  have hLleH : H ^ 2 / N ≤ H := by
    apply Nat.div_le_of_le_mul
    have := Nat.mul_le_mul_left H hHN
    nlinarith
  have hlN : l ≤ N := hlcut.trans (hLleH.trans hHN)
  have hqpos : 0 < N / l := Nat.div_pos hlN hlpos
  have hspos : 0 < s := by exact Nat.sqrt_pos.mpr hqpos
  have hmpos : 0 < m := Nat.mul_pos hlpos hspos
  have hsideNat := squareMomentSide_le_div_add_one hHN hlpos
  have hside : ((squareMomentSide N H l : ℕ) : ℝ) ≤
      (H : ℝ) / (m : ℝ) + 1 := by
    calc
      ((squareMomentSide N H l : ℕ) : ℝ) ≤
          ((H / m : ℕ) : ℝ) + 1 := by exact_mod_cast hsideNat
      _ ≤ (H : ℝ) / (m : ℝ) + 1 := by
        gcongr
        exact Nat.cast_div_le
  have hNmpos : 0 < (N : ℝ) * (l : ℝ) := by positivity
  have hmrealpos : 0 < (m : ℝ) ^ 2 := by positivity
  have hinv : (1 : ℝ) / (m : ℝ) ^ 2 ≤
      4 / ((N : ℝ) * (l : ℝ)) := by
    rw [div_le_div_iff₀ hmrealpos hNmpos]
    norm_num
    exact_mod_cast hdenNat
  have hfrac : (H : ℝ) ^ 2 / (m : ℝ) ^ 2 ≤
      4 * (H : ℝ) ^ 2 / ((N : ℝ) * (l : ℝ)) := by
    calc
      (H : ℝ) ^ 2 / (m : ℝ) ^ 2 =
          (H : ℝ) ^ 2 * (1 / (m : ℝ) ^ 2) := by ring
      _ ≤ (H : ℝ) ^ 2 *
          (4 / ((N : ℝ) * (l : ℝ))) := by gcongr
      _ = 4 * (H : ℝ) ^ 2 / ((N : ℝ) * (l : ℝ)) := by ring
  have hnonneg : 0 ≤ ((squareMomentSide N H l : ℕ) : ℝ) := by positivity
  have hrhsnonneg : 0 ≤ (H : ℝ) / (m : ℝ) + 1 := by positivity
  calc
    ((squareMomentSide N H l : ℕ) : ℝ) ^ 2 ≤
        ((H : ℝ) / (m : ℝ) + 1) ^ 2 :=
      (sq_le_sq₀ hnonneg hrhsnonneg).2 hside
    _ ≤ 2 * ((H : ℝ) ^ 2 / (m : ℝ) ^ 2) + 2 := by
      have hsquare : 0 ≤ ((H : ℝ) - (m : ℝ)) ^ 2 := sq_nonneg _
      field_simp
      nlinarith
    _ ≤ 8 * (H : ℝ) ^ 2 / ((N : ℝ) * (l : ℝ)) + 2 := by
      calc
        2 * ((H : ℝ) ^ 2 / (m : ℝ) ^ 2) + 2 ≤
            2 * (4 * (H : ℝ) ^ 2 /
              ((N : ℝ) * (l : ℝ))) + 2 := by gcongr
        _ = 8 * (H : ℝ) ^ 2 / ((N : ℝ) * (l : ℝ)) + 2 := by ring

private lemma squareMoment_sum_real_le
    {N H : ℕ} (hN : 0 < N) (hHN : H ≤ N) :
    ((∑ l ∈ Finset.Icc 1 (H ^ 2 / N),
        (squareMomentSide N H l) ^ 2 : ℕ) : ℝ) ≤
      (8 * (H : ℝ) ^ 2 / (N : ℝ)) *
          (1 + Real.log (H ^ 2 / N : ℕ)) +
        2 * (H ^ 2 / N : ℕ) := by
  let L := H ^ 2 / N
  have hharm :
      (∑ l ∈ Finset.Icc 1 L, ((l : ℝ) : ℝ)⁻¹) ≤
        1 + Real.log (L : ℝ) := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast] using harmonic_le_one_add_log L
  rw [Nat.cast_sum]
  calc
    ∑ l ∈ Finset.Icc 1 (H ^ 2 / N),
        (((squareMomentSide N H l) ^ 2 : ℕ) : ℝ) ≤
        ∑ l ∈ Finset.Icc 1 (H ^ 2 / N),
          (8 * (H : ℝ) ^ 2 / ((N : ℝ) * (l : ℝ)) + 2) := by
      apply Finset.sum_le_sum
      intro l hl
      have hlI := Finset.mem_Icc.mp hl
      simpa only [Nat.cast_pow] using
        squareMomentSide_sq_real_le hN hHN hlI.1 hlI.2
    _ = (8 * (H : ℝ) ^ 2 / (N : ℝ)) *
          (∑ l ∈ Finset.Icc 1 L, ((l : ℝ) : ℝ)⁻¹) + 2 * L := by
      dsimp only [L]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        have hlpos : (0 : ℝ) < l := by
          exact_mod_cast (Finset.mem_Icc.mp hl).1
        field_simp
      · simp [Nat.card_Icc, mul_comm]
    _ ≤ (8 * (H : ℝ) ^ 2 / (N : ℝ)) *
          (1 + Real.log (L : ℝ)) + 2 * L := by
      gcongr
    _ = (8 * (H : ℝ) ^ 2 / (N : ℝ)) *
          (1 + Real.log (H ^ 2 / N : ℕ)) +
        2 * (H ^ 2 / N : ℕ) := by rfl

private lemma firstMomentTriples_card_real_le
    {N H : ℕ} (hN : 0 < N) (hHN : H ≤ N) :
    ((firstMomentTriples N N (N - H)).card : ℝ) ≤
      (8 * (H : ℝ) ^ 2 / (N : ℝ)) *
          (1 + Real.log (H ^ 2 / N : ℕ)) +
        2 * (H ^ 2 / N : ℕ) := by
  have hnat := firstMomentTriples_card_le_squareMoment_sum hN hHN
  have hcast : ((firstMomentTriples N N (N - H)).card : ℝ) ≤
      ((∑ l ∈ Finset.Icc 1 (H ^ 2 / N),
        (squareMomentSide N H l) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans (squareMoment_sum_real_le hN hHN)

private noncomputable def firstMomentRealBound (N H : ℕ) : ℝ :=
  (8 * (H : ℝ) ^ 2 / (N : ℝ)) *
      (1 + Real.log (H ^ 2 / N : ℕ)) +
    2 * (H ^ 2 / N : ℕ)

private lemma firstMomentRealBound_nonneg (N H : ℕ) :
    0 ≤ firstMomentRealBound N H := by
  unfold firstMomentRealBound
  positivity [Real.log_natCast_nonneg]

private lemma firstMomentTriples_card_real_le_bound
    {N H : ℕ} (hN : 0 < N) (hHN : H ≤ N) :
    ((firstMomentTriples N N (N - H)).card : ℝ) ≤
      firstMomentRealBound N H := by
  simpa only [firstMomentRealBound] using
    firstMomentTriples_card_real_le hN hHN

private lemma firstMomentRealBound_le {N H : ℕ}
    (hN : 0 < N) (hH : H ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) :
    firstMomentRealBound N H ≤
      18 * (H : ℝ) ^ 2 * Real.log N / N := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  let q := H ^ 2 / N
  have hqN : q ≤ N := by
    dsimp only [q]
    apply Nat.div_le_of_le_mul
    simpa only [pow_two] using Nat.mul_self_le_mul_self hH
  have hqcast : (q : ℝ) ≤ (H : ℝ) ^ 2 / (N : ℝ) := by
    dsimp only [q]
    have hc := (Nat.cast_div_le :
      ((H ^ 2 / N : ℕ) : ℝ) ≤ ((H ^ 2 : ℕ) : ℝ) / (N : ℝ))
    simpa only [Nat.cast_pow] using hc
  have hlogq : Real.log (q : ℝ) ≤ Real.log (N : ℝ) := by
    by_cases hq : q = 0
    · simp only [hq, Nat.cast_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hq))
        (by exact_mod_cast hqN)
  have hxnonneg : 0 ≤ (H : ℝ) ^ 2 / (N : ℝ) := by positivity
  have hfactor : 1 + Real.log (q : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    linarith
  unfold firstMomentRealBound
  change (8 * (H : ℝ) ^ 2 / (N : ℝ)) * (1 + Real.log (q : ℝ)) +
      2 * (q : ℝ) ≤ _
  have hfirst :
      (8 * (H : ℝ) ^ 2 / (N : ℝ)) * (1 + Real.log (q : ℝ)) ≤
        (8 * (H : ℝ) ^ 2 / (N : ℝ)) * (2 * Real.log N) :=
    mul_le_mul_of_nonneg_left hfactor (by positivity)
  have hsecond : 2 * (q : ℝ) ≤
      2 * ((H : ℝ) ^ 2 / N) :=
    mul_le_mul_of_nonneg_left hqcast (by norm_num)
  have hthird : 2 * ((H : ℝ) ^ 2 / N) ≤
      2 * ((H : ℝ) ^ 2 / N) * Real.log N := by
    calc
      2 * ((H : ℝ) ^ 2 / N) =
          2 * ((H : ℝ) ^ 2 / N) * 1 := by ring
      _ ≤ 2 * ((H : ℝ) ^ 2 / N) * Real.log N :=
        mul_le_mul_of_nonneg_left hlog
          (mul_nonneg (by norm_num) hxnonneg)
  calc
    (8 * (H : ℝ) ^ 2 / (N : ℝ)) * (1 + Real.log (q : ℝ)) +
        2 * (q : ℝ) ≤
        (8 * (H : ℝ) ^ 2 / (N : ℝ)) * (2 * Real.log N) +
          2 * ((H : ℝ) ^ 2 / N) := add_le_add hfirst hsecond
    _ ≤ (8 * (H : ℝ) ^ 2 / (N : ℝ)) * (2 * Real.log N) +
          2 * ((H : ℝ) ^ 2 / N) * Real.log N := by
      exact add_le_add (le_refl _) hthird
    _ = 18 * (H : ℝ) ^ 2 * Real.log N / N := by ring

private lemma primeInterval_card_eq {u v : ℕ} (huv : u ≤ v) :
    ((Finset.Icc u v).filter Nat.Prime).card =
      Nat.primeCounting v - Nat.primeCounting (u - 1) := by
  have heq : (Finset.Icc u v).filter Nat.Prime =
      Nat.primesLE v \ Nat.primesLE (u - 1) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff,
      Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpu, hpv⟩, hp⟩
      exact ⟨⟨hpv, hp⟩, fun h ↦ by
        have hp2 := hp.two_le
        omega⟩
    · rintro ⟨⟨hpv, hp⟩, hnot⟩
      refine ⟨⟨?_, hpv⟩, hp⟩
      by_contra h
      apply hnot
      have hp2 := hp.two_le
      exact ⟨by omega, hp⟩
  rw [heq, Finset.card_sdiff_of_subset
    (Nat.primesLE_mono ((Nat.sub_le u 1).trans huv))]
  simp only [Nat.primesLE_card_eq_primeCounting]

private lemma theta_sub_le_primeInterval_card_mul_log {u v : ℕ}
    (huv : u ≤ v) :
    Chebyshev.theta v - Chebyshev.theta ((u - 1 : ℕ) : ℝ) ≤
      (((Finset.Icc u v).filter Nat.Prime).card : ℝ) * Real.log v := by
  have hsub : Nat.primesLE (u - 1) ⊆ Nat.primesLE v :=
    Nat.primesLE_mono ((Nat.sub_le u 1).trans huv)
  have hsum :
      ∑ p ∈ Nat.primesLE v \ Nat.primesLE (u - 1), Real.log p =
        Chebyshev.theta v - Chebyshev.theta ((u - 1 : ℕ) : ℝ) := by
    have hadd := Finset.sum_sdiff (f := fun p : ℕ ↦ Real.log p) hsub
    rw [← Chebyshev.theta_eq_sum_primesLE_log,
      ← Chebyshev.theta_eq_sum_primesLE_log] at hadd
    linarith
  rw [← hsum]
  calc
    ∑ p ∈ Nat.primesLE v \ Nat.primesLE (u - 1), Real.log p ≤
        ∑ _p ∈ Nat.primesLE v \ Nat.primesLE (u - 1), Real.log v := by
      apply Finset.sum_le_sum
      intro p hp
      apply Real.log_le_log
      · exact_mod_cast (Nat.Prime.pos (Nat.prime_of_mem_primesLE
          (Finset.mem_sdiff.mp hp).1))
      · exact_mod_cast Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
    _ = ((Nat.primesLE v \ Nat.primesLE (u - 1)).card : ℝ) * Real.log v := by
      simp
    _ = (((Finset.Icc u v).filter Nat.Prime).card : ℝ) * Real.log v := by
      congr 2
      exact_mod_cast (by
        rw [Finset.card_sdiff_of_subset hsub,
          Nat.primesLE_card_eq_primeCounting,
          Nat.primesLE_card_eq_primeCounting]
        exact (primeInterval_card_eq huv).symm)

private lemma theta_interval_lower_of_psi_bounds {u v : ℕ} {Eu Ev S : ℝ}
    (hEu : |Chebyshev.psi ((u - 1 : ℕ) : ℝ) - ((u - 1 : ℕ) : ℝ)| ≤ Eu)
    (hEv : |Chebyshev.psi v - (v : ℝ)| ≤ Ev)
    (hS : Chebyshev.psi v - Chebyshev.theta v ≤ S) :
    (v : ℝ) - ((u - 1 : ℕ) : ℝ) - Ev - Eu - S ≤
      Chebyshev.theta v - Chebyshev.theta ((u - 1 : ℕ) : ℝ) := by
  have hEu' := (abs_le.mp hEu).2
  have hEv' := (abs_le.mp hEv).1
  have htu := Chebyshev.theta_le_psi ((u - 1 : ℕ) : ℝ)
  linarith

private lemma tendsto_log_pow_div_sqrt (k : ℕ) :
    Tendsto (fun x : ℝ ↦ Real.log x ^ k / Real.sqrt x) atTop (nhds 0) := by
  have h := logPowRatio
    ((1 : ℝ) / 2) (k : ℝ) (by norm_num)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.rpow_natCast]
  rw [← Real.sqrt_eq_rpow]

private theorem eventually_psi_sub_theta_div_log_pow (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) : ∀ᶠ x : ℝ in atTop,
      Chebyshev.psi x - Chebyshev.theta x ≤
        δ * x / Real.log x ^ k := by
  have hlim := (tendsto_log_pow_div_sqrt (k + 1)).const_mul 2
  have hlim' : Tendsto (fun x : ℝ ↦
      2 * (Real.log x ^ (k + 1) / Real.sqrt x)) atTop (nhds 0) := by
    simpa using hlim
  have hsmall : ∀ᶠ x : ℝ in atTop,
      2 * (Real.log x ^ (k + 1) / Real.sqrt x) < δ := by
    have hnorm := NormedAddGroup.tendsto_nhds_zero.mp hlim' δ hδ
    filter_upwards [hnorm, eventually_gt_atTop 1] with x hxnorm hx
    rw [Real.norm_of_nonneg] at hxnorm
    · exact hxnorm
    · exact mul_nonneg (by norm_num) (div_nonneg
        (pow_nonneg (Real.log_nonneg hx.le) (k + 1)) (Real.sqrt_nonneg x))
  filter_upwards [hsmall, eventually_gt_atTop 1] with x hxsmall hx
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx.le
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogpow : 0 < Real.log x ^ k := pow_pos hlog k
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 (by positivity)
  apply (Chebyshev.psi_sub_theta_le hx.le).trans
  apply (le_div_iff₀ hlogpow).2
  have hsmall' : 2 * Real.log x ^ (k + 1) < δ * Real.sqrt x := by
    rw [← mul_div_assoc] at hxsmall
    exact (div_lt_iff₀ hsqrt).mp hxsmall
  have hmul := mul_le_mul_of_nonneg_left hsmall'.le (Real.sqrt_nonneg x)
  calc
    2 * Real.sqrt x * Real.log x * Real.log x ^ k =
        Real.sqrt x * (2 * Real.log x ^ (k + 1)) := by
      rw [pow_succ]
      ring
    _ ≤ Real.sqrt x * (δ * Real.sqrt x) := hmul
    _ = δ * Real.sqrt x ^ 2 := by ring
    _ = δ * x := by rw [Real.sq_sqrt hx0]

private lemma div_log_pow_le_two_pow_mul {x y : ℝ} (k : ℕ)
    (hy : 4 ≤ y) (hxy : x ≤ y) (hhalf : y ≤ 2 * x) :
    x / Real.log x ^ k ≤ (2 : ℝ) ^ k * y / Real.log y ^ k := by
  have hypos : 0 < y := by linarith
  have hxpos : 0 < x := by linarith
  have hyhalf : 2 ≤ y / 2 := by linarith
  have hhalfpos : 0 < y / 2 := by linarith
  have hloghalf_le : Real.log (y / 2) ≤ Real.log x := by
    apply Real.log_le_log hhalfpos
    linarith
  have hlog2_le : Real.log 2 ≤ Real.log (y / 2) := by
    apply Real.log_le_log (by norm_num)
    exact hyhalf
  have hlogsplit : Real.log y = Real.log 2 + Real.log (y / 2) := by
    calc
      Real.log y = Real.log (2 * (y / 2)) := by congr 1; field_simp
      _ = Real.log 2 + Real.log (y / 2) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hhalfpos.ne']
  have hlogcomp : Real.log y ≤ 2 * Real.log x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hpows : Real.log y ^ k ≤ (2 * Real.log x) ^ k :=
    pow_le_pow_left₀ hlogy.le hlogcomp k
  have hcross : x * Real.log y ^ k ≤
      ((2 : ℝ) ^ k * y) * Real.log x ^ k := by
    calc
      x * Real.log y ^ k ≤ y * Real.log y ^ k :=
        mul_le_mul_of_nonneg_right hxy (pow_nonneg hlogy.le k)
      _ ≤ y * (2 * Real.log x) ^ k :=
        mul_le_mul_of_nonneg_left hpows hypos.le
      _ = ((2 : ℝ) ^ k * y) * Real.log x ^ k := by rw [mul_pow]; ring
  exact (div_le_div_iff₀ (pow_pos hlogx k) (pow_pos hlogy k)).2 hcross

private theorem eventually_primeInterval_card_real_lower (k : ℕ)
    (estimate : ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤ δ * x / Real.log x ^ k) :
    ∀ᶠ v : ℕ in atTop, ∀ u : ℕ, u ≤ v → v ≤ 2 * (u - 1) →
      (v : ℝ) / Real.log v ^ k ≤
        (v : ℝ) - ((u - 1 : ℕ) : ℝ) →
      ((v : ℝ) - ((u - 1 : ℕ) : ℝ)) / (2 * Real.log v) ≤
        (((Finset.Icc u v).filter Nat.Prime).card : ℝ) := by
  let ε : ℝ := 1 / (4 * (2 + (2 : ℝ) ^ k))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hpsi := estimate ε hε
  have hcorr := eventually_psi_sub_theta_div_log_pow k hε
  rw [eventually_atTop] at hpsi hcorr
  obtain ⟨Xp, hXp⟩ := hpsi
  obtain ⟨Xc, hXc⟩ := hcorr
  let R := max 4 (max Xp Xc)
  obtain ⟨V, hV⟩ := exists_nat_ge (2 * R)
  rw [eventually_atTop]
  refine ⟨V, ?_⟩
  intro v hv u huv hhalf hwidth
  have hR4 : 4 ≤ R := le_max_left _ _
  have hRXp : Xp ≤ R := (le_max_left Xp Xc).trans (le_max_right 4 _)
  have hRXc : Xc ≤ R := (le_max_right Xp Xc).trans (le_max_right 4 _)
  have hvR : 2 * R ≤ (v : ℝ) := hV.trans (by exact_mod_cast hv)
  have hv4 : (4 : ℝ) ≤ v := hR4.trans (by linarith)
  have hu0v : ((u - 1 : ℕ) : ℝ) ≤ v := by
    exact_mod_cast (Nat.sub_le u 1).trans huv
  have hvu0 : (v : ℝ) ≤ 2 * ((u - 1 : ℕ) : ℝ) := by
    exact_mod_cast hhalf
  have hu0R : R ≤ ((u - 1 : ℕ) : ℝ) := by linarith
  have hEu0 := hXp ((u - 1 : ℕ) : ℝ) (hRXp.trans hu0R)
  have hEv := hXp (v : ℝ) (hRXp.trans (by linarith))
  have hS := hXc (v : ℝ) (hRXc.trans (by linarith))
  have htransfer := div_log_pow_le_two_pow_mul k hv4 hu0v hvu0
  have hEu : |Chebyshev.psi ((u - 1 : ℕ) : ℝ) - ((u - 1 : ℕ) : ℝ)| ≤
      ε * ((2 : ℝ) ^ k * (v : ℝ) / Real.log v ^ k) :=
    hEu0.trans (by
      simpa only [mul_div_assoc] using
        (mul_le_mul_of_nonneg_left htransfer hε.le))
  have htheta := theta_interval_lower_of_psi_bounds hEu hEv hS
  have hlogv : 0 < Real.log (v : ℝ) := Real.log_pos (by linarith)
  let B : ℝ := (v : ℝ) / Real.log v ^ k
  let W : ℝ := (v : ℝ) - ((u - 1 : ℕ) : ℝ)
  have herrors :
      ε * B + ε * B + ε * ((2 : ℝ) ^ k * B) ≤ W / 4 := by
    have heq : ε * B + ε * B + ε * ((2 : ℝ) ^ k * B) = B / 4 := by
      dsimp only [ε]
      field_simp
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hwidth (by norm_num)
  have htheta' : W / 2 ≤
      Chebyshev.theta v - Chebyshev.theta ((u - 1 : ℕ) : ℝ) := by
    have hEuRewrite :
        ε * ((2 : ℝ) ^ k * (v : ℝ) / Real.log v ^ k) =
          ε * ((2 : ℝ) ^ k * ((v : ℝ) / Real.log v ^ k)) := by ring
    rw [hEuRewrite] at hEu
    have hthetaNorm : W - ε * B - ε * ((2 : ℝ) ^ k * B) - ε * B ≤
        Chebyshev.theta v - Chebyshev.theta ((u - 1 : ℕ) : ℝ) := by
      calc
        W - ε * B - ε * ((2 : ℝ) ^ k * B) - ε * B =
            (v : ℝ) - ((u - 1 : ℕ) : ℝ) -
              ε * (v : ℝ) / Real.log v ^ k -
              ε * ((2 : ℝ) ^ k * (v : ℝ) / Real.log v ^ k) -
              ε * (v : ℝ) / Real.log v ^ k := by
                dsimp only [B, W]
                ring
        _ ≤ _ := htheta
    have hW0 : 0 ≤ W := by dsimp only [W]; exact sub_nonneg.mpr hu0v
    linarith
  have hcount := theta_sub_le_primeInterval_card_mul_log huv
  have hhalfcount : W / 2 ≤
      (((Finset.Icc u v).filter Nat.Prime).card : ℝ) * Real.log v :=
    htheta'.trans hcount
  apply (div_le_iff₀ (mul_pos (by norm_num) hlogv)).2
  nlinarith

private noncomputable def analyticG (N : ℕ) : ℕ :=
  ⌊(N : ℝ) / Real.log N ^ 4⌋₊

private lemma eventually_analyticG_bounds :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (2 * Real.log N ^ 4) ≤ (analyticG N : ℝ) ∧
      (analyticG N : ℝ) ≤ (N : ℝ) / Real.log N ^ 4 ∧
      0 < analyticG N := by
  have hratioReal := logPowRatio 1 4 (by norm_num)
  have hratio := hratioReal.comp tendsto_natCast_atTop_atTop
  simp only [Real.rpow_natCast, Real.rpow_one] at hratio
  have hsmall : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ 4 / (N : ℝ) < 1 / 2 := by
    have hnorm := NormedAddGroup.tendsto_nhds_zero.mp hratio
      (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hnorm, eventually_ge_atTop 3] with N hnorm hN
    have hpow : Real.log (N : ℝ) ^ (4 : ℝ) =
        Real.log (N : ℝ) ^ (4 : ℕ) := by
      simpa using Real.rpow_natCast (Real.log (N : ℝ)) 4
    have hnorm' : |Real.log (N : ℝ) ^ 4 / (N : ℝ)| < 1 / 2 := by
      simpa only [Function.comp_apply, Real.norm_eq_abs, hpow] using hnorm
    rw [abs_of_nonneg] at hnorm'
    · exact hnorm'
    · positivity
  filter_upwards [hsmall, eventually_ge_atTop 3] with N hsmall hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (by omega : 1 < N))
  have hlogpow : 0 < Real.log (N : ℝ) ^ 4 := pow_pos hlog 4
  have hx : 2 < (N : ℝ) / Real.log N ^ 4 := by
    rw [div_lt_iff₀ hNreal] at hsmall
    apply (lt_div_iff₀ hlogpow).2
    nlinarith
  have hfloorUpper : (analyticG N : ℝ) ≤
      (N : ℝ) / Real.log N ^ 4 := by
    exact Nat.floor_le (div_nonneg hNreal.le hlogpow.le)
  have hfloorLower : (N : ℝ) / Real.log N ^ 4 - 1 <
      (analyticG N : ℝ) := by
    exact Nat.sub_one_lt_floor _
  refine ⟨?_, hfloorUpper, ?_⟩
  · calc
      (N : ℝ) / (2 * Real.log N ^ 4) =
          ((N : ℝ) / Real.log N ^ 4) / 2 := by ring
      _ ≤ (N : ℝ) / Real.log N ^ 4 - 1 := by linarith
      _ ≤ (analyticG N : ℝ) := hfloorLower.le
  · exact_mod_cast (show (0 : ℝ) < (analyticG N : ℝ) by
      linarith [hfloorLower])

private lemma analytic_numeric_separation {N G : ℕ}
    (hN : 0 < N) (hG2 : 2 * G ≤ N)
    (hlog : 20000 ≤ Real.log (N : ℝ))
    (hGlower : (N : ℝ) / (2 * Real.log N ^ 4) ≤ (G : ℝ))
    (hGupper : (G : ℝ) ≤ (N : ℝ) / Real.log N ^ 4)
    (hGpos : 0 < G) :
    ((G + 1 : ℕ) : ℝ) * firstMomentRealBound N (2 * G) +
        firstMomentRealBound N G * firstMomentRealBound N (2 * G) <
      ((G : ℝ) / (4 * Real.log N)) * ((G : ℝ) / (2 * Real.log N)) := by
  let L := Real.log (N : ℝ)
  change 20000 ≤ L at hlog
  change (N : ℝ) / (2 * L ^ 4) ≤ (G : ℝ) at hGlower
  change (G : ℝ) ≤ (N : ℝ) / L ^ 4 at hGupper
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < L := by dsimp only [L]; linarith
  have hlogone : 1 ≤ Real.log (N : ℝ) := by linarith
  have hB1 := firstMomentRealBound_le hN (by omega : G ≤ N) hlogone
  have hB2 := firstMomentRealBound_le hN hG2 hlogone
  have hGsq : (G : ℝ) ^ 2 ≤ ((N : ℝ) / L ^ 4) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg G) hGupper 2
  have hB1' : firstMomentRealBound N G ≤ 72 * (N : ℝ) / L ^ 7 := by
    calc
      firstMomentRealBound N G ≤ 18 * (G : ℝ) ^ 2 * L / N := hB1
      _ ≤ 18 * ((N : ℝ) / L ^ 4) ^ 2 * L / N := by gcongr
      _ ≤ 72 * (N : ℝ) / L ^ 7 := by
        field_simp
        nlinarith [sq_nonneg L]
  have hB2' : firstMomentRealBound N (2 * G) ≤ 72 * (N : ℝ) / L ^ 7 := by
    calc
      firstMomentRealBound N (2 * G) ≤
          18 * ((2 * G : ℕ) : ℝ) ^ 2 * L / N := hB2
      _ = 72 * (G : ℝ) ^ 2 * L / N := by push_cast; ring
      _ ≤ 72 * ((N : ℝ) / L ^ 4) ^ 2 * L / N := by gcongr
      _ = 72 * (N : ℝ) / L ^ 7 := by field_simp
  have hxone : 1 ≤ (N : ℝ) / L ^ 4 :=
    hGupper.trans' (by exact_mod_cast hGpos)
  have hGadd : ((G + 1 : ℕ) : ℝ) ≤ 2 * ((N : ℝ) / L ^ 4) := by
    rw [Nat.cast_add, Nat.cast_one]
    calc
      (G : ℝ) + 1 ≤ (N : ℝ) / L ^ 4 + 1 :=
        add_le_add hGupper (le_refl 1)
      _ ≤ 2 * ((N : ℝ) / L ^ 4) := by linarith
  have hB1nonneg : 0 ≤ firstMomentRealBound N G :=
    firstMomentRealBound_nonneg N G
  have hB2nonneg : 0 ≤ firstMomentRealBound N (2 * G) :=
    firstMomentRealBound_nonneg N (2 * G)
  have hupper :
      ((G + 1 : ℕ) : ℝ) * firstMomentRealBound N (2 * G) +
          firstMomentRealBound N G * firstMomentRealBound N (2 * G) ≤
        144 * (N : ℝ) ^ 2 / L ^ 11 +
          5184 * (N : ℝ) ^ 2 / L ^ 14 := by
    calc
      _ ≤ (2 * ((N : ℝ) / L ^ 4)) * (72 * (N : ℝ) / L ^ 7) +
          (72 * (N : ℝ) / L ^ 7) * (72 * (N : ℝ) / L ^ 7) := by
            gcongr
      _ = _ := by field_simp; ring
  have hcoeff :
      144 * (N : ℝ) ^ 2 / L ^ 11 +
          5184 * (N : ℝ) ^ 2 / L ^ 14 <
        (N : ℝ) ^ 2 / (32 * L ^ 10) := by
    have hL1 : 1 < L := by linarith
    have h144 : (144 : ℝ) / L < 1 / 64 := by
      apply (div_lt_iff₀ hL).2
      nlinarith
    have h5184 : (5184 : ℝ) / L ^ 4 < 1 / 64 := by
      apply (div_lt_iff₀ (pow_pos hL 4)).2
      have hp : (12800 : ℝ) < L ^ 2 := by nlinarith
      nlinarith [sq_nonneg (L ^ 2 - 12800)]
    have hsum : (144 : ℝ) / L + 5184 / L ^ 4 < 1 / 32 := by linarith
    have hscale : 0 < (N : ℝ) ^ 2 / L ^ 10 := by positivity
    calc
      144 * (N : ℝ) ^ 2 / L ^ 11 + 5184 * (N : ℝ) ^ 2 / L ^ 14 =
          ((N : ℝ) ^ 2 / L ^ 10) * (144 / L + 5184 / L ^ 4) := by
            field_simp
      _ < ((N : ℝ) ^ 2 / L ^ 10) * (1 / 32) :=
        mul_lt_mul_of_pos_left hsum hscale
      _ = (N : ℝ) ^ 2 / (32 * L ^ 10) := by ring
  have hlower : (N : ℝ) ^ 2 / (32 * L ^ 10) ≤
      ((G : ℝ) / (4 * L)) * ((G : ℝ) / (2 * L)) := by
    have hsq := pow_le_pow_left₀
      (by positivity : (0 : ℝ) ≤ (N : ℝ) / (2 * L ^ 4)) hGlower 2
    calc
      (N : ℝ) ^ 2 / (32 * L ^ 10) =
          ((N : ℝ) / (2 * L ^ 4)) ^ 2 / (8 * L ^ 2) := by
            field_simp
            ring
      _ ≤ (G : ℝ) ^ 2 / (8 * L ^ 2) := by gcongr
      _ = ((G : ℝ) / (4 * L)) * ((G : ℝ) / (2 * L)) := by ring
  exact hupper.trans_lt (hcoeff.trans_le hlower)

private def pairTriple (n x y : ℕ) : ℕ × (ℕ × ℕ) :=
  let g := x.gcd y
  let X₁ := x / g
  let X₂ := y / g
  (n / (X₁ * X₂), (X₁, X₂))

private lemma pairTriple_mem {N D n x y : ℕ} (hn : 0 < n)
    (hx : 0 < x) (hy : 0 < y) (hxy : x < y)
    (hxn : x ∣ n) (hyn : y ∣ n)
    (hD : y / x.gcd y ≤ D)
    (hclose : n * (y / x.gcd y) ≤ N * (x / x.gcd y)) :
    pairTriple n x y ∈ factorTriples N D n := by
  let g := x.gcd y
  let X₁ := x / g
  let X₂ := y / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left y hx
  have hX₁ : 0 < X₁ := Nat.div_pos (Nat.gcd_le_left y hx) hg
  have hX₂ : 0 < X₂ := Nat.div_pos (Nat.gcd_le_right x hy) hg
  have hcop : X₁.Coprime X₂ := Nat.coprime_div_gcd_div_gcd hg
  have hX₁n : X₁ ∣ n := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left x y)).trans hxn
  have hX₂n : X₂ ∣ n := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right x y)).trans hyn
  have hprod : X₁ * X₂ ∣ n := hcop.mul_dvd_of_dvd_of_dvd hX₁n hX₂n
  have hprodpos : 0 < X₁ * X₂ := Nat.mul_pos hX₁ hX₂
  have hlpos : 0 < n / (X₁ * X₂) :=
    Nat.div_pos (Nat.le_of_dvd hn hprod) hprodpos
  have hXX : X₁ < X₂ :=
    (Nat.div_lt_div_right hg.ne' (Nat.gcd_dvd_left x y)
      (Nat.gcd_dvd_right x y)).mpr hxy
  rw [mem_factorTriples]
  refine ⟨hlpos, Nat.div_le_self n _, hX₁, ?_, hX₂, ?_, ?_, hXX, ?_⟩
  · exact hXX.le.trans hD
  · exact hD
  · simpa only [pairTriple, g, X₁, X₂, mul_assoc] using
      (Nat.div_mul_cancel hprod).symm
  · change n * (y / x.gcd y) ≤ N * (x / x.gcd y)
    exact hclose

private lemma pairTriple_injective_right {n x : ℕ} (hx : 0 < x) :
    Set.InjOn (pairTriple n x) (Set.Ioi 0) := by
  intro y hy z hz heq
  have hypos : 0 < y := hy
  have hzpos : 0 < z := hz
  let gy := x.gcd y
  let gz := x.gcd z
  let Xy₁ := x / gy
  let Xz₁ := x / gz
  let Xy₂ := y / gy
  let Xz₂ := z / gz
  have h₁ : Xy₁ = Xz₁ := congrArg (fun t ↦ t.2.1) heq
  have h₂ : Xy₂ = Xz₂ := congrArg (fun t ↦ t.2.2) heq
  have hgy : 0 < gy := Nat.gcd_pos_of_pos_left y hx
  have hgz : 0 < gz := Nat.gcd_pos_of_pos_left z hx
  have hX₁ : 0 < Xy₁ := Nat.div_pos (Nat.gcd_le_left y hx) hgy
  have hgeq : gy = gz := by
    apply Nat.mul_left_cancel hX₁
    calc
      Xy₁ * gy = x := Nat.div_mul_cancel (Nat.gcd_dvd_left x y)
      _ = Xz₁ * gz := (Nat.div_mul_cancel (Nat.gcd_dvd_left x z)).symm
      _ = Xy₁ * gz := by rw [h₁]
  calc
    y = Xy₂ * gy := (Nat.div_mul_cancel (Nat.gcd_dvd_right x y)).symm
    _ = Xz₂ * gz := by rw [h₂, hgeq]
    _ = z := Nat.div_mul_cancel (Nat.gcd_dvd_right x z)

private lemma card_le_kCount_add_one {N D n : ℕ} (S : Finset ℕ)
    (hpos : ∀ x ∈ S, 0 < x)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, x < y →
      pairTriple n x y ∈ factorTriples N D n) :
    S.card ≤ kCount N D n + 1 := by
  classical
  by_cases hS : S.Nonempty
  · let x := S.min' hS
    have hxS : x ∈ S := S.min'_mem hS
    have hx : 0 < x := hpos x hxS
    have hmap : ∀ y ∈ S.erase x,
        pairTriple n x y ∈ factorTriples N D n := by
      intro y hy
      have hyS := Finset.mem_of_mem_erase hy
      have hyne := (Finset.mem_erase.mp hy).1
      apply hpair x hxS y hyS
      exact (S.min'_le y hyS).lt_of_ne (Ne.symm hyne)
    have hinj : Set.InjOn (pairTriple n x) (↑(S.erase x) : Set ℕ) := by
      apply (pairTriple_injective_right hx).mono
      intro y hy
      exact hpos y (Finset.mem_of_mem_erase hy)
    have hcard : (S.erase x).card ≤ (factorTriples N D n).card :=
      Finset.card_le_card_of_injOn (pairTriple n x) hmap hinj
    rw [Finset.card_erase_of_mem hxS] at hcard
    rw [kCount]
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty] at hS
    simp [hS, kCount]

private lemma component_pairTriple_mem (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {α β d e c D : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α.Coprime β)
    (hsq : A.card * A.card < 2 * (α * α))
    (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hdfac : d = d.gcd α * d.gcd β)
    (hefac : e = e.gcd α * e.gcd β)
    (hαd : α * d * c ∈ A) (hβd : β * d * c ∈ A)
    (hαe : α * e * c ∈ A) (hβe : β * e * c ∈ A)
    (hlt : d.gcd α < e.gcd α)
    (hD : e.gcd α / (d.gcd α).gcd (e.gcd α) ≤ D) :
    pairTriple α (d.gcd α) (e.gcd α) ∈
      factorTriples A.card D α := by
  let g := d.gcd e
  let d' := d / g
  let e' := e / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left e hd
  have hd' : 0 < d' := Nat.div_pos (Nat.gcd_le_left e hd) hg
  have he' : 0 < e' := Nat.div_pos (Nat.gcd_le_right d he) hg
  have hcop : d'.Coprime e' := Nat.coprime_div_gcd_div_gcd hg
  have hdexpand : d' * (g * c) = d * c := by
    calc
      d' * (g * c) = (d' * g) * c := by simp only [mul_assoc]
      _ = d * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left d e)]
  have heexpand : e' * (g * c) = e * c := by
    calc
      e' * (g * c) = (e' * g) * c := by simp only [mul_assoc]
      _ = e * c := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right d e)]
  have hfac := factor_closeness_of_counterexample A hbad hα hβ hd' he'
    (Nat.mul_pos hg hc) hαβ hcop hsq
    (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact hαd)
    (by rw [mul_assoc, hdexpand, ← mul_assoc]; exact hβd)
    (by rw [mul_assoc, heexpand, ← mul_assoc]; exact hαe)
    (by rw [mul_assoc, heexpand, ← mul_assoc]; exact hβe)
  have hdcomp : d'.gcd α = d.gcd α / (d.gcd α).gcd (e.gcd α) := by
    exact gcd_div_gcd_eq_component hαβ hd he hdfac hefac
  have hecomp : e'.gcd α = e.gcd α / (d.gcd α).gcd (e.gcd α) := by
    simpa only [e', g, Nat.gcd_comm e d,
      Nat.gcd_comm (e.gcd α) (d.gcd α)] using
      (gcd_div_gcd_eq_component hαβ he hd hefac hdfac)
  apply pairTriple_mem hα (Nat.gcd_pos_of_pos_left α hd)
    (Nat.gcd_pos_of_pos_left α he) hlt
    (Nat.gcd_dvd_right d α) (Nat.gcd_dvd_right e α) hD
  rw [← hdcomp, ← hecomp]
  exact hfac.2.2.2.1

private lemma representationCount_le_kCount (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α D : ℕ} (hp : p.Prime)
    (hα : 0 < α) (hαp : α < p)
    (hsqα : A.card * A.card < 2 * (α * α))
    (hsqβ : A.card * A.card < 2 * ((p - α) * (p - α)))
    (hDα : ∀ d ∈ normalize (representedMultipliers A α (p - α)),
      ∀ e ∈ normalize (representedMultipliers A α (p - α)),
        e.gcd α / (d.gcd α).gcd (e.gcd α) ≤ D)
    (hDβ : ∀ d ∈ normalize (representedMultipliers A α (p - α)),
      ∀ e ∈ normalize (representedMultipliers A α (p - α)),
        e.gcd (p - α) / (d.gcd (p - α)).gcd (e.gcd (p - α)) ≤ D) :
    representationCount A p α ≤
      (kCount A.card D α + 1) * (kCount A.card D (p - α) + 1) := by
  classical
  let β := p - α
  let R := representedMultipliers A α β
  let B := normalize R
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hα hαp
  by_cases hR : R.Nonempty
  · have hR₀ : 0 ∉ R := representedMultipliers_nonzero hα
    let c := R.gcd id
    have hc : 0 < c := gcd_pos R hR₀ hR
    have hrepresented : ∀ {d}, d ∈ B →
        0 < d ∧ α * d * c ∈ A ∧ β * d * c ∈ A := by
      intro d hd
      change d ∈ R.image (fun e ↦ e / R.gcd id) at hd
      obtain ⟨e, heR, rfl⟩ := Finset.mem_image.mp hd
      have he := (mem_representedMultipliers hα).mp heR
      have hce : R.gcd id ∣ e := Finset.gcd_dvd heR
      have heq : e / R.gcd id * R.gcd id = e := Nat.div_mul_cancel hce
      refine ⟨Nat.div_pos (Nat.le_of_dvd he.1 hce) hc, ?_, ?_⟩
      · change α * (e / R.gcd id) * R.gcd id ∈ A
        rw [mul_assoc, heq]
        exact he.2.1
      · change β * (e / R.gcd id) * R.gcd id ∈ A
        rw [mul_assoc, heq]
        exact he.2.2
    have hdvd : ∀ d ∈ B, d ∣ α * β := by
      exact normalize_represented_dvd_product A hbad hα hβ hαβ hsqα hR
    have hfac : ∀ d ∈ B, d = d.gcd α * d.gcd β := by
      intro d hd
      exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hαβ).mpr
        (hdvd d hd)).symm
    let U := B.image fun d ↦ d.gcd α
    have hU : U.card ≤ kCount A.card D α + 1 := by
      apply card_le_kCount_add_one U
      · intro u hu
        obtain ⟨d, hdB, rfl⟩ := Finset.mem_image.mp hu
        exact Nat.gcd_pos_of_pos_left α (hrepresented hdB).1
      · intro u hu v hv huv
        obtain ⟨d, hdB, hdu⟩ := Finset.mem_image.mp hu
        obtain ⟨e, heB, hev⟩ := Finset.mem_image.mp hv
        subst u
        subst v
        apply component_pairTriple_mem A hbad hα hβ hαβ hsqα
          (hrepresented hdB).1 (hrepresented heB).1 hc
          (hfac d hdB) (hfac e heB)
          (hrepresented hdB).2.1 (hrepresented hdB).2.2
          (hrepresented heB).2.1 (hrepresented heB).2.2 huv
        simpa only [β] using hDα d hdB e heB
    have hfiber : ∀ u ∈ U,
        (B.filter fun d ↦ d.gcd α = u).card ≤
          kCount A.card D β + 1 := by
      intro u hu
      let T := B.filter fun d ↦ d.gcd α = u
      let V := T.image fun d ↦ d.gcd β
      have hTV : T.card = V.card := by
        change T.card = (T.image fun d ↦ d.gcd β).card
        rw [Finset.card_image_of_injOn]
        intro d hdT e heT hde
        have hdcomp := (Finset.mem_filter.mp hdT).2
        have hecomp := (Finset.mem_filter.mp heT).2
        change d.gcd β = e.gcd β at hde
        calc
          d = d.gcd α * d.gcd β := hfac d (Finset.mem_filter.mp hdT).1
          _ = e.gcd α * e.gcd β := by rw [hdcomp, hecomp, hde]
          _ = e := (hfac e (Finset.mem_filter.mp heT).1).symm
      rw [hTV]
      apply card_le_kCount_add_one V
      · intro v hv
        obtain ⟨d, hdT, rfl⟩ := Finset.mem_image.mp hv
        exact Nat.gcd_pos_of_pos_left β
          (hrepresented (Finset.mem_filter.mp hdT).1).1
      · intro v hv w hw hvw
        obtain ⟨d, hdT, hdv⟩ := Finset.mem_image.mp hv
        obtain ⟨e, heT, hew⟩ := Finset.mem_image.mp hw
        have hdB := (Finset.mem_filter.mp hdT).1
        have heB := (Finset.mem_filter.mp heT).1
        subst v
        subst w
        apply component_pairTriple_mem A hbad hβ hα hαβ.symm hsqβ
          (hrepresented hdB).1 (hrepresented heB).1 hc
          (by simpa only [mul_comm] using hfac d hdB)
          (by simpa only [mul_comm] using hfac e heB)
          (hrepresented hdB).2.2 (hrepresented hdB).2.1
          (hrepresented heB).2.2 (hrepresented heB).2.1 hvw
        simpa only [β] using hDβ d hdB e heB
    have hcardB : B.card ≤
        (kCount A.card D α + 1) * (kCount A.card D β + 1) := by
      calc
        B.card = ∑ u ∈ U, (B.filter fun d ↦ d.gcd α = u).card :=
          Finset.card_eq_sum_card_image (fun d ↦ d.gcd α) B
        _ ≤ ∑ _u ∈ U, (kCount A.card D β + 1) :=
          Finset.sum_le_sum hfiber
        _ = U.card * (kCount A.card D β + 1) := by
          exact Finset.sum_const_nat fun _ _ ↦ rfl
        _ ≤ (kCount A.card D α + 1) *
            (kCount A.card D β + 1) :=
          Nat.mul_le_mul_right _ hU
    change R.card ≤ _
    rw [← normalize_card R]
    simpa only [B, β] using hcardB
  · simp only [Finset.not_nonempty_iff_eq_empty] at hR
    simp [representationCount, R, β, hR]

private def reducedPairs (A : Finset ℕ) (p α : ℕ) : Finset (ℕ × ℕ) :=
  let B := normalize (representedMultipliers A α (p - α))
  (B ×ˢ B).image fun de ↦
    (de.1 / de.1.gcd de.2, de.2 / de.1.gcd de.2)

private def globalReducedPairs (A : Finset ℕ) (G : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G)).filter Nat.Prime).biUnion
    fun p ↦ (Finset.Icc ((p + 1) / 2) A.card).biUnion fun α ↦
      reducedPairs A p α

private def globalD (A : Finset ℕ) (G : ℕ) : ℕ :=
  (globalReducedPairs A G).sup fun de ↦ max de.1 de.2

private lemma reducedPair_mem_global {A : Finset ℕ} {G p α d e : ℕ}
    (hpwin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G))
    (hp : p.Prime) (hα : α ∈ Finset.Icc ((p + 1) / 2) A.card)
    (hd : d ∈ normalize (representedMultipliers A α (p - α)))
    (he : e ∈ normalize (representedMultipliers A α (p - α))) :
    (d / d.gcd e, e / d.gcd e) ∈ globalReducedPairs A G := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨p, Finset.mem_filter.mpr ⟨hpwin, hp⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨α, hα, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨(d, e), Finset.mem_product.mpr ⟨hd, he⟩, rfl⟩

private lemma pair_right_le_globalD {A : Finset ℕ} {G : ℕ} {de : ℕ × ℕ}
    (hde : de ∈ globalReducedPairs A G) : de.2 ≤ globalD A G := by
  exact le_max_right de.1 de.2 |>.trans
    (Finset.le_sup (f := fun de : ℕ × ℕ ↦ max de.1 de.2) hde)

private lemma component_div_le_div_gcd {α β d e : ℕ}
    (hαβ : α.Coprime β) (hd : 0 < d) (he : 0 < e)
    (hdfac : d = d.gcd α * d.gcd β)
    (hefac : e = e.gcd α * e.gcd β) :
    e.gcd α / (d.gcd α).gcd (e.gcd α) ≤ e / d.gcd e := by
  have hcomp : (e / d.gcd e).gcd α =
      e.gcd α / (d.gcd α).gcd (e.gcd α) := by
    simpa only [Nat.gcd_comm e d, Nat.gcd_comm (e.gcd α) (d.gcd α)] using
      (gcd_div_gcd_eq_component hαβ he hd hefac hdfac)
  rw [← hcomp]
  exact Nat.gcd_le_left α (Nat.div_pos
    (Nat.gcd_le_right d he) (Nat.gcd_pos_of_pos_left e hd))

private lemma component_le_globalD (A : Finset ℕ) (G : ℕ)
    (hbad : ¬ GrahamBound A) {p α d e : ℕ}
    (hpwin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G))
    (hp : p.Prime) (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card)
    (hαpos : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hd : d ∈ normalize (representedMultipliers A α (p - α)))
    (he : e ∈ normalize (representedMultipliers A α (p - α))) :
    e.gcd α / (d.gcd α).gcd (e.gcd α) ≤ globalD A G := by
  let R := representedMultipliers A α (p - α)
  let B := normalize R
  have hβ : 0 < p - α := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime (p - α) := coprime_prime_sub hp hαpos hαp
  have hR : R.Nonempty := by
    change d ∈ R.image (fun x ↦ x / R.gcd id) at hd
    obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hd
    exact ⟨x, hx⟩
  have hdvd : ∀ x ∈ B, x ∣ α * (p - α) :=
    normalize_represented_dvd_product A hbad hαpos hβ hαβ hsq hR
  have hfac : ∀ x ∈ B, x = x.gcd α * x.gcd (p - α) := by
    intro x hx
    exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hαβ).mpr
      (hdvd x hx)).symm
  have hfull : e / d.gcd e ≤ globalD A G :=
    pair_right_le_globalD (reducedPair_mem_global hpwin hp hαJ hd he)
  exact (component_div_le_div_gcd hαβ
    (Nat.pos_of_ne_zero fun hz ↦
      normalize_nonzero R (representedMultipliers_nonzero hαpos) (hz ▸ hd))
    (Nat.pos_of_ne_zero fun hz ↦
      normalize_nonzero R (representedMultipliers_nonzero hαpos) (hz ▸ he))
    (hfac d hd) (hfac e he)).trans hfull

private lemma complementary_component_le_globalD (A : Finset ℕ) (G : ℕ)
    (hbad : ¬ GrahamBound A) {p α d e : ℕ}
    (hpwin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G))
    (hp : p.Prime) (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card)
    (hαpos : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hd : d ∈ normalize (representedMultipliers A α (p - α)))
    (he : e ∈ normalize (representedMultipliers A α (p - α))) :
    e.gcd (p - α) / (d.gcd (p - α)).gcd (e.gcd (p - α)) ≤ globalD A G := by
  let R := representedMultipliers A α (p - α)
  let B := normalize R
  have hβ : 0 < p - α := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime (p - α) := coprime_prime_sub hp hαpos hαp
  have hR : R.Nonempty := by
    change d ∈ R.image (fun x ↦ x / R.gcd id) at hd
    obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hd
    exact ⟨x, hx⟩
  have hdvd : ∀ x ∈ B, x ∣ α * (p - α) :=
    normalize_represented_dvd_product A hbad hαpos hβ hαβ hsq hR
  have hfac : ∀ x ∈ B, x = x.gcd α * x.gcd (p - α) := by
    intro x hx
    exact ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hαβ).mpr
      (hdvd x hx)).symm
  have hfull : e / d.gcd e ≤ globalD A G :=
    pair_right_le_globalD (reducedPair_mem_global hpwin hp hαJ hd he)
  exact (component_div_le_div_gcd hαβ.symm
    (Nat.pos_of_ne_zero fun hz ↦
      normalize_nonzero R (representedMultipliers_nonzero hαpos) (hz ▸ hd))
    (Nat.pos_of_ne_zero fun hz ↦
      normalize_nonzero R (representedMultipliers_nonzero hαpos) (hz ▸ he))
    (by simpa only [mul_comm] using hfac d hd)
    (by simpa only [mul_comm] using hfac e he)).trans hfull

private lemma representationCount_le_globalD (A : Finset ℕ) (G : ℕ)
    (hbad : ¬ GrahamBound A) {p α : ℕ}
    (hpwin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G))
    (hp : p.Prime) (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card)
    (hαpos : 0 < α) (hαp : α < p)
    (hsqα : A.card * A.card < 2 * (α * α))
    (hsqβ : A.card * A.card < 2 * ((p - α) * (p - α))) :
    representationCount A p α ≤
      (kCount A.card (globalD A G) α + 1) *
        (kCount A.card (globalD A G) (p - α) + 1) := by
  apply representationCount_le_kCount A hbad hp hαpos hαp hsqα hsqβ
  · intro d hd e he
    exact component_le_globalD A G hbad hpwin hp hαJ hαpos hαp hsqα hd he
  · intro d hd e he
    exact complementary_component_le_globalD A G hbad hpwin hp hαJ
      hαpos hαp hsqα hd he

private lemma representationCount_sub_one_le_kCounts (A : Finset ℕ) (G : ℕ)
    (hbad : ¬GrahamBound A) {p α : ℕ}
    (hpwin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G))
    (hp : p.Prime) (hαJ : α ∈ Finset.Icc ((p + 1) / 2) A.card)
    (hαpos : 0 < α) (hαp : α < p)
    (hsqα : A.card * A.card < 2 * (α * α))
    (hsqβ : A.card * A.card < 2 * ((p - α) * (p - α))) :
    representationCount A p α - 1 ≤
      kCount A.card (globalD A G) α +
        kCount A.card (globalD A G) (p - α) +
          kCount A.card (globalD A G) α *
            kCount A.card (globalD A G) (p - α) := by
  let x := kCount A.card (globalD A G) α
  let y := kCount A.card (globalD A G) (p - α)
  have h : representationCount A p α ≤ (x + 1) * (y + 1) :=
    representationCount_le_globalD A G hbad hpwin hp hαJ
    hαpos hαp hsqα hsqβ
  have hexpand : (x + 1) * (y + 1) = x * y + x + y + 1 := by ring
  calc
    representationCount A p α - 1 ≤ (x + 1) * (y + 1) - 1 :=
      Nat.sub_le_sub_right h 1
    _ = x * y + x + y := by rw [hexpand]; omega
    _ = x + y + x * y := by ac_rfl

private lemma complement_square_lt_of_analytic_window {N G p α : ℕ}
    (hG : 0 < G) (hGN : 10 * G ≤ N)
    (hpwin : p ∈ Finset.Icc (2 * N - 2 * G) (2 * N - G))
    (hαJ : α ∈ Finset.Icc ((p + 1) / 2) N) :
    N * N < 2 * ((p - α) * (p - α)) := by
  have h2G : 2 * G ≤ N := by omega
  have hsplit : N - 2 * G + 2 * G = N := Nat.sub_add_cancel h2G
  have hβlower : N - 2 * G ≤ p - α := by
    have hp := (Finset.mem_Icc.mp hpwin).1
    have hα := (Finset.mem_Icc.mp hαJ).2
    omega
  have hbase : N * N < 2 * ((N - 2 * G) * (N - 2 * G)) := by
    nlinarith [sq_nonneg ((N : ℤ) - 4 * G)]
  exact hbase.trans_le (Nat.mul_le_mul_left 2 (Nat.mul_self_le_mul_self hβlower))

private def kUpperAt (N D p α : ℕ) : ℕ :=
  kCount N D α + kCount N D (p - α) +
    kCount N D α * kCount N D (p - α)

private def collisionExcess (A : Finset ℕ) (p : ℕ) : ℕ :=
  ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
    2 ≤ representationCount A p α).sum fun α ↦
      representationCount A p α - 1

private lemma sum_Icc_eq_sum_J_add_reflection {M : Type*}
    [AddCommMonoid M] {N p : ℕ} (hp : p.Prime) (hpN : N < p)
    (hp2 : 2 < p)
    (f : ℕ → M) :
    (Finset.Icc ((p + 1) / 2) N).sum (fun α ↦ f α + f (p - α)) =
      (Finset.Icc (p - N) N).sum f := by
  classical
  let J := Finset.Icc ((p + 1) / 2) N
  let H := Finset.Icc (p - N) (p - ((p + 1) / 2))
  let I := Finset.Icc (p - N) N
  have hpne : p ≠ 2 := by omega
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hpne
  have hinj : Set.InjOn (fun α : ℕ ↦ p - α) (↑J : Set ℕ) := by
    intro α hα β hβ hab
    change p - α = p - β at hab
    have hαp : α ≤ p := (Finset.mem_Icc.mp hα).2.trans hpN.le
    have hβp : β ≤ p := (Finset.mem_Icc.mp hβ).2.trans hpN.le
    have hsum : p - α + α = p - α + β := by
      calc
        p - α + α = p := Nat.sub_add_cancel hαp
        _ = p - β + β := (Nat.sub_add_cancel hβp).symm
        _ = p - α + β := by rw [hab]
    exact Nat.add_left_cancel hsum
  have himage : J.image (fun α : ℕ ↦ p - α) = H := by
    ext β
    constructor
    · intro hβ
      obtain ⟨α, hαJ, rfl⟩ := Finset.mem_image.mp hβ
      have hα := Finset.mem_Icc.mp hαJ
      exact Finset.mem_Icc.mpr ⟨by omega, Nat.sub_le_sub_left hα.1 p⟩
    · intro hβ
      have hβI := Finset.mem_Icc.mp hβ
      have hβp : β ≤ p := hβI.2.trans (Nat.sub_le p _)
      apply Finset.mem_image.mpr
      refine ⟨p - β, Finset.mem_Icc.mpr ⟨?_, ?_⟩, Nat.sub_sub_self hβp⟩
      · omega
      · omega
  have hreflect : J.sum (fun α ↦ f (p - α)) = H.sum f := by
    rw [← himage]
    exact (Finset.sum_image hinj).symm
  have hdisj : Disjoint H J := by
    rw [Finset.disjoint_left]
    intro n hnH hnJ
    have hh := Finset.mem_Icc.mp hnH
    have hj := Finset.mem_Icc.mp hnJ
    omega
  have hunion : H ∪ J = I := by
    ext n
    simp only [H, J, I, Finset.mem_union, Finset.mem_Icc]
    omega
  calc
    J.sum (fun α ↦ f α + f (p - α)) =
        J.sum f + J.sum (fun α ↦ f (p - α)) := Finset.sum_add_distrib
    _ = H.sum f + J.sum f := by rw [hreflect, add_comm]
    _ = (H ∪ J).sum f := (Finset.sum_union hdisj).symm
    _ = I.sum f := by rw [hunion]

private lemma collisionExcess_le_sum_kUpper (A : Finset ℕ) (G : ℕ)
    (hbad : ¬GrahamBound A) (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    {p : ℕ} (hpwin : p ∈ Finset.Icc
      (2 * A.card - 2 * G) (2 * A.card - G)) (hp : p.Prime) :
    collisionExcess A p ≤
      (Finset.Icc ((p + 1) / 2) A.card).sum fun α ↦
        kUpperAt A.card (globalD A G) p α := by
  let J := Finset.Icc ((p + 1) / 2) A.card
  let M := J.filter fun α ↦ 2 ≤ representationCount A p α
  have hsmall : 4 * G ≤ A.card := by omega
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hpoint : ∀ α ∈ M, representationCount A p α - 1 ≤
      kUpperAt A.card (globalD A G) p α := by
    intro α hαM
    have hαJ := (Finset.mem_filter.mp hαM).1
    have hαN := (Finset.mem_Icc.mp hαJ).2
    have hα : 0 < α := by
      have hlo := (Finset.mem_Icc.mp hαJ).1
      have hp2 := hp.two_le
      have hhalf : 0 < (p + 1) / 2 := Nat.div_pos (by omega) (by norm_num)
      omega
    have hαp : α < p := hαN.trans_lt hpN
    have hsqα : A.card * A.card < 2 * (α * α) := by
      have hGN' : G ≤ A.card := by omega
      have hsub : A.card - G + G = A.card := Nat.sub_add_cancel hGN'
      have halower : A.card - G ≤ α := by
        have hplower := (Finset.mem_Icc.mp hpwin).1
        have hαlower := (Finset.mem_Icc.mp hαJ).1
        omega
      have hthree : 3 * G ≤ A.card - G := by omega
      nlinarith [sq_nonneg (((A.card - G : ℕ) : ℤ) - 3 * G),
        sq_nonneg ((α : ℤ) - (A.card - G))]
    have hsqβ := complement_square_lt_of_analytic_window hG hGN hpwin hαJ
    exact representationCount_sub_one_le_kCounts A G hbad hpwin hp hαJ
      hα hαp hsqα hsqβ
  change M.sum (fun α ↦ representationCount A p α - 1) ≤ _
  calc
    M.sum (fun α ↦ representationCount A p α - 1) ≤
        M.sum (fun α ↦ kUpperAt A.card (globalD A G) p α) := by
      exact Finset.sum_le_sum hpoint
    _ ≤ J.sum (fun α ↦ kUpperAt A.card (globalD A G) p α) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ Nat.zero_le _)

private lemma collisionExcess_le_upper_split (A : Finset ℕ) (G : ℕ)
    (hbad : ¬GrahamBound A) (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    {p : ℕ} (hpwin : p ∈ Finset.Icc
      (2 * A.card - 2 * G) (2 * A.card - G)) (hp : p.Prime) :
    collisionExcess A p ≤
      (Finset.Icc (p - A.card) A.card).sum
          (kCount A.card (globalD A G)) +
        (Finset.Icc ((p + 1) / 2) A.card).sum (fun α ↦
          kCount A.card (globalD A G) α *
            kCount A.card (globalD A G) (p - α)) := by
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hp2 : 2 < p := by
    have hN : 10 ≤ A.card := by nlinarith
    omega
  refine (collisionExcess_le_sum_kUpper A G hbad hG hGN hpwin hp).trans_eq ?_
  rw [← sum_Icc_eq_sum_J_add_reflection hp hpN hp2
    (kCount A.card (globalD A G))]
  simp only [kUpperAt, Finset.sum_add_distrib]

private def primeWindow (N G : ℕ) : Finset ℕ :=
  (Finset.Icc (2 * N - 2 * G) (2 * N - G)).filter Nat.Prime

private def totalCollisionExcess (A : Finset ℕ) (G : ℕ) : ℕ :=
  (primeWindow A.card G).sum (collisionExcess A)

private def basicPrimeCollisionLower (N G : ℕ) : ℕ :=
  (primeWindow N G).sum fun p ↦
    ((Finset.Icc (p - N) N).filter Nat.Prime).card

private lemma real_mul_le_basicPrimeCollisionLower
    {N G : ℕ} {RP RQ : ℝ} (hRQ : 0 ≤ RQ)
    (hP : RP ≤ ((primeWindow N G).card : ℝ))
    (hQ : ∀ p ∈ primeWindow N G,
      RQ ≤ (((Finset.Icc (p - N) N).filter Nat.Prime).card : ℝ)) :
    RP * RQ ≤ (basicPrimeCollisionLower N G : ℝ) := by
  unfold basicPrimeCollisionLower
  calc
    RP * RQ ≤ ((primeWindow N G).card : ℝ) * RQ :=
      mul_le_mul_of_nonneg_right hP hRQ
    _ = ∑ _p ∈ primeWindow N G, RQ := by simp
    _ ≤ ∑ p ∈ primeWindow N G,
        (((Finset.Icc (p - N) N).filter Nat.Prime).card : ℝ) := by
      exact Finset.sum_le_sum hQ
    _ = ((∑ p ∈ primeWindow N G,
        ((Finset.Icc (p - N) N).filter Nat.Prime).card : ℕ) : ℝ) := by
      simp

private def totalLinearUpper (N G D : ℕ) : ℕ :=
  (primeWindow N G).sum fun p ↦
    (Finset.Icc (p - N) N).sum (kCount N D)

private def totalBilinearUpper (N G D : ℕ) : ℕ :=
  (primeWindow N G).sum fun p ↦
    (Finset.Icc ((p + 1) / 2) N).sum fun α ↦
      kCount N D α * kCount N D (p - α)

private def bilinearTuples (N G D : ℕ) :
    Finset ((p : ℕ) × ((α : ℕ) ×
      ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))))) :=
  (primeWindow N G).sigma fun p ↦
    (Finset.Icc ((p + 1) / 2) N).sigma fun α ↦
      factorTriples N D α ×ˢ factorTriples N D (p - α)

private lemma totalBilinearUpper_eq_card_bilinearTuples
    (N G D : ℕ) :
    totalBilinearUpper N G D = (bilinearTuples N G D).card := by
  simp only [totalBilinearUpper, bilinearTuples, Finset.card_sigma,
    Finset.card_product, kCount]

private def factorValue (t : ℕ × (ℕ × ℕ)) : ℕ :=
  t.1 * t.2.1 * t.2.2

private def factorParameters (N D : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.Icc 1 N ×ˢ (Finset.Icc 1 D ×ˢ Finset.Icc 1 D)).filter fun t ↦
    t.2.1 < t.2.2 ∧ factorValue t ≤ N ∧
      factorValue t * t.2.2 ≤ N * t.2.1

private lemma mem_factorParameters {N D l X₁ X₂ : ℕ} :
    (l, (X₁, X₂)) ∈ factorParameters N D ↔
      1 ≤ l ∧ l ≤ N ∧ 1 ≤ X₁ ∧ X₁ ≤ D ∧
        1 ≤ X₂ ∧ X₂ ≤ D ∧ X₁ < X₂ ∧
        l * X₁ * X₂ ≤ N ∧
        (l * X₁ * X₂) * X₂ ≤ N * X₁ := by
  rw [factorParameters, Finset.mem_filter, Finset.mem_product,
    Finset.mem_product]
  simp only [Finset.mem_Icc, factorValue]
  tauto

private lemma factorTriple_mem_factorParameters
    {N D n : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ factorTriples N D n) :
    t ∈ factorParameters N D ∧ factorValue t = n := by
  rcases t with ⟨l, X₁, X₂⟩
  have h := mem_factorTriples.mp ht
  have hX₂pos : 0 < X₂ := by omega
  have hvalueLe : l * X₁ * X₂ ≤ N := by
    apply Nat.le_of_mul_le_mul_right (c := X₂) ?_ hX₂pos
    calc
      (l * X₁ * X₂) * X₂ = n * X₂ := by rw [h.2.2.2.2.2.2.1]
      _ ≤ N * X₁ := h.2.2.2.2.2.2.2.2
      _ ≤ N * X₂ := Nat.mul_le_mul_left N (Nat.le_of_lt h.2.2.2.2.2.2.2.1)
  constructor
  · apply mem_factorParameters.mpr
    exact ⟨h.1, h.2.1.trans (h.2.2.2.2.2.2.1.symm ▸ hvalueLe),
      h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.1, hvalueLe, by
        simpa only [h.2.2.2.2.2.2.1] using h.2.2.2.2.2.2.2.2⟩
  · exact h.2.2.2.2.2.2.1.symm

private lemma factorValue_le_of_mem_factorParameters
    {N D : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ factorParameters N D) : factorValue t ≤ N := by
  exact (Finset.mem_filter.mp ht).2.2.1

private lemma factorParameter_mem_factorTriple
    {N D : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ factorParameters N D) :
    t ∈ factorTriples N D (factorValue t) := by
  rcases t with ⟨l, X₁, X₂⟩
  have h := mem_factorParameters.mp ht
  have hX₁pos : 0 < X₁ := by omega
  have hX₂pos : 0 < X₂ := by omega
  have hlvalue : l ≤ l * X₁ * X₂ := by
    calc
      l ≤ l * (X₁ * X₂) :=
        Nat.le_mul_of_pos_right l (Nat.mul_pos hX₁pos hX₂pos)
      _ = l * X₁ * X₂ := by ring
  apply mem_factorTriples.mpr
  simp only [factorValue]
  exact ⟨h.1,
    hlvalue,
    h.2.2.1,
    h.2.2.2.1,
    h.2.2.2.2.1,
    h.2.2.2.2.2.1,
    trivial, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

private lemma factorValue_pos_of_mem_factorTriples
    {N D n : ℕ} {t : ℕ × (ℕ × ℕ)}
    (ht : t ∈ factorTriples N D n) : 0 < factorValue t := by
  rcases t with ⟨l, X₁, X₂⟩
  have h := mem_factorTriples.mp ht
  simp only [factorValue]
  exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)

private def bilinearParameterPairs (N G D : ℕ) :
    Finset ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) :=
  (factorParameters N D ×ˢ factorParameters N D).filter fun ts ↦
    let α := factorValue ts.1
    let β := factorValue ts.2
    let p := α + β
    p ∈ primeWindow N G ∧ (p + 1) / 2 ≤ α

private def highFactorParameters (N G D : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (factorParameters N D).filter fun t ↦ N - G ≤ factorValue t

private lemma highFactorParameters_card_le_firstMomentTriples
    {N G D : ℕ} (hN : 0 < N) :
    (highFactorParameters N G D).card ≤
      (firstMomentTriples N D (N - G)).card := by
  apply Finset.card_le_card
  intro t ht
  rcases t with ⟨l, X₁, X₂⟩
  have hhigh := Finset.mem_filter.mp ht
  have htriple := factorParameter_mem_factorTriple hhigh.1
  have h := mem_factorTriples.mp htriple
  have hgap : N - factorValue (l, (X₁, X₂)) ≤ N - (N - G) := by
    have hnN := factorValue_le_of_mem_factorParameters hhigh.1
    omega
  have hgapSq : (N - factorValue (l, (X₁, X₂))) ^ 2 ≤
      (N - (N - G)) ^ 2 := pow_le_pow_left' hgap 2
  have hlcut : l ≤ (N - (N - G)) ^ 2 / N :=
    (factorTriple_multiplier_le_gap_sq_div hN htriple).trans
      (Nat.div_le_div_right hgapSq)
  apply mem_firstMomentTriples.mpr
  refine ⟨h.1, hlcut, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, ?_, ?_, ?_⟩
  · simpa only [factorValue] using hhigh.2
  · simpa only [factorValue] using
      (factorValue_le_of_mem_factorParameters hhigh.1)
  · simpa only [factorValue] using h.2.2.2.2.2.2.2.2

private lemma bilinearParameterPairs_subset_high_product
    {N G D : ℕ} (hGN : 2 * G ≤ N) :
    bilinearParameterPairs N G D ⊆
      highFactorParameters N G D ×ˢ highFactorParameters N (2 * G) D := by
  rintro ⟨t₁, t₂⟩ hpair
  simp only [bilinearParameterPairs, Finset.mem_filter, Finset.mem_product] at hpair
  have hpwindow := (Finset.mem_filter.mp hpair.2.1).1
  have hplower := (Finset.mem_Icc.mp hpwindow).1
  have ht₁le := factorValue_le_of_mem_factorParameters hpair.1.1
  have ht₂le := factorValue_le_of_mem_factorParameters hpair.1.2
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨hpair.1.1, ?_⟩
    change N - G ≤ factorValue t₁
    omega
  · apply Finset.mem_filter.mpr
    refine ⟨hpair.1.2, ?_⟩
    change N - 2 * G ≤ factorValue t₂
    omega

private lemma totalBilinearUpper_le_parameterPairs (N G D : ℕ) :
    totalBilinearUpper N G D ≤
      (bilinearParameterPairs N G D).card := by
  rw [totalBilinearUpper_eq_card_bilinearTuples]
  let forgetValues :
      ((p : ℕ) × ((α : ℕ) ×
        ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))))) →
        ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) :=
    fun z ↦ z.2.2
  apply Finset.card_le_card_of_injOn
    (s := bilinearTuples N G D) (t := bilinearParameterPairs N G D)
    forgetValues
  · rintro ⟨p, α, t₁, t₂⟩ hz
    dsimp only [forgetValues]
    have hzmem : p ∈ primeWindow N G ∧
        α ∈ Finset.Icc ((p + 1) / 2) N ∧
        t₁ ∈ factorTriples N D α ∧ t₂ ∈ factorTriples N D (p - α) := by
      simpa only [Finset.mem_coe, bilinearTuples, Finset.mem_sigma,
        Finset.mem_product]
        using hz
    have ht₁ := factorTriple_mem_factorParameters hzmem.2.2.1
    have ht₂ := factorTriple_mem_factorParameters hzmem.2.2.2
    have hβpos : 0 < p - α := by
      rw [← ht₂.2]
      exact factorValue_pos_of_mem_factorTriples hzmem.2.2.2
    have hαp : α ≤ p := by omega
    have hpvalue : factorValue t₁ + factorValue t₂ = p := by
      rw [ht₁.2, ht₂.2]
      omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨ht₁.1, ht₂.1⟩, ?_⟩
    dsimp only
    constructor
    · simpa only [hpvalue] using hzmem.1
    · have hpsum : factorValue t₁ + factorValue t₂ = p := hpvalue
      have hαvalue : factorValue t₁ = α := ht₁.2
      have hsum : α + factorValue t₂ = p := by omega
      rw [hαvalue, hsum]
      exact (Finset.mem_Icc.mp hzmem.2.1).1
  · rintro ⟨p, α, t₁, t₂⟩ hz ⟨q, β, u₁, u₂⟩ hw heq
    dsimp only [forgetValues] at heq
    have hzmem : p ∈ primeWindow N G ∧
        α ∈ Finset.Icc ((p + 1) / 2) N ∧
        t₁ ∈ factorTriples N D α ∧ t₂ ∈ factorTriples N D (p - α) := by
      simpa only [Finset.mem_coe, bilinearTuples, Finset.mem_sigma,
        Finset.mem_product]
        using hz
    have hwmem : q ∈ primeWindow N G ∧
        β ∈ Finset.Icc ((q + 1) / 2) N ∧
        u₁ ∈ factorTriples N D β ∧ u₂ ∈ factorTriples N D (q - β) := by
      simpa only [Finset.mem_coe, bilinearTuples, Finset.mem_sigma,
        Finset.mem_product]
        using hw
    injection heq with ht₁u₁ ht₂u₂
    subst u₁
    subst u₂
    have hαeq : α = β := by
      have h₁ := (factorTriple_mem_factorParameters hzmem.2.2.1).2
      have h₂ := (factorTriple_mem_factorParameters hwmem.2.2.1).2
      omega
    subst β
    have hpq : p = q := by
      have h₁ := (factorTriple_mem_factorParameters hzmem.2.2.2).2
      have h₂ := (factorTriple_mem_factorParameters hwmem.2.2.2).2
      have hvpos : 0 < factorValue t₂ :=
        factorValue_pos_of_mem_factorTriples hzmem.2.2.2
      have hpα : α ≤ p := by omega
      have hqα : α ≤ q := by omega
      omega
    subst q
    rfl

private lemma totalBilinearUpper_le_firstMoment_product
    {N G D : ℕ} (hN : 0 < N) (hGN : 2 * G ≤ N) :
    totalBilinearUpper N G D ≤
      (firstMomentTriples N D (N - G)).card *
        (firstMomentTriples N D (N - 2 * G)).card := by
  calc
    totalBilinearUpper N G D ≤
        (bilinearParameterPairs N G D).card :=
      totalBilinearUpper_le_parameterPairs N G D
    _ ≤ (highFactorParameters N G D ×ˢ
          highFactorParameters N (2 * G) D).card :=
      Finset.card_le_card (bilinearParameterPairs_subset_high_product hGN)
    _ = (highFactorParameters N G D).card *
          (highFactorParameters N (2 * G) D).card := Finset.card_product _ _
    _ ≤ (firstMomentTriples N D (N - G)).card *
          (firstMomentTriples N D (N - 2 * G)).card := by
      exact Nat.mul_le_mul
        (highFactorParameters_card_le_firstMomentTriples
          (N := N) (G := G) (D := D) hN)
        (highFactorParameters_card_le_firstMomentTriples
          (N := N) (G := 2 * G) (D := D) hN)

private lemma totalLinearUpper_le_sum_firstMomentTriples
    {N G D : ℕ} (hN : 0 < N) :
    totalLinearUpper N G D ≤
      (primeWindow N G).sum fun p ↦
        (firstMomentTriples N D (p - N)).card := by
  unfold totalLinearUpper
  apply Finset.sum_le_sum
  intro p _hp
  exact sum_kCount_Icc_le_firstMomentTriples_card hN

private lemma totalLinearUpper_le_primeWindow_mul_firstMoment
    {N G D : ℕ} (hN : 0 < N) (hGN : 2 * G ≤ N) :
    totalLinearUpper N G D ≤
      (primeWindow N G).card *
        (firstMomentTriples N D (N - 2 * G)).card := by
  calc
    totalLinearUpper N G D ≤
        (primeWindow N G).sum fun p ↦
          (firstMomentTriples N D (p - N)).card :=
      totalLinearUpper_le_sum_firstMomentTriples hN
    _ ≤ (primeWindow N G).sum fun _p ↦
          (firstMomentTriples N D (N - 2 * G)).card := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.card_le_card
      apply firstMomentTriples_mono_lower
      have hpwindow := (Finset.mem_filter.mp hp).1
      have hplower := (Finset.mem_Icc.mp hpwindow).1
      omega
    _ = (primeWindow N G).card *
          (firstMomentTriples N D (N - 2 * G)).card := by
      simp

private lemma totalCollisionExcess_le_upper (A : Finset ℕ) (G : ℕ)
    (hbad : ¬GrahamBound A) (hG : 0 < G) (hGN : 10 * G ≤ A.card) :
    totalCollisionExcess A G ≤
      totalLinearUpper A.card G (globalD A G) +
        totalBilinearUpper A.card G (globalD A G) := by
  unfold totalCollisionExcess totalLinearUpper totalBilinearUpper
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  exact collisionExcess_le_upper_split A G hbad hG hGN
    (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2

private lemma reducedPair_coordinates_lt_card (A : Finset ℕ)
    (hbad : ¬ GrahamBound A) {p α d e : ℕ}
    (hp : p.Prime) (hαpos : 0 < α) (hαp : α < p)
    (hsq : A.card * A.card < 2 * (α * α))
    (hd : d ∈ normalize (representedMultipliers A α (p - α)))
    (he : e ∈ normalize (representedMultipliers A α (p - α))) :
    d / d.gcd e ≤ A.card ∧ e / d.gcd e ≤ A.card := by
  let β := p - α
  let R := representedMultipliers A α β
  let B := normalize R
  have hβ : 0 < β := Nat.sub_pos_of_lt hαp
  have hαβ : α.Coprime β := coprime_prime_sub hp hαpos hαp
  have hR : R.Nonempty := by
    change d ∈ R.image (fun x ↦ x / R.gcd id) at hd
    obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hd
    exact ⟨x, hx⟩
  have hR₀ : 0 ∉ R := representedMultipliers_nonzero hαpos
  let c := R.gcd id
  have hc : 0 < c := gcd_pos R hR₀ hR
  have hrepresented : ∀ {x}, x ∈ B →
      0 < x ∧ α * x * c ∈ A ∧ β * x * c ∈ A := by
    intro x hx
    change x ∈ R.image (fun z ↦ z / R.gcd id) at hx
    obtain ⟨z, hzR, rfl⟩ := Finset.mem_image.mp hx
    have hz := (mem_representedMultipliers hαpos).mp hzR
    have hcz : R.gcd id ∣ z := Finset.gcd_dvd hzR
    have hzeq : z / R.gcd id * R.gcd id = z := Nat.div_mul_cancel hcz
    refine ⟨Nat.div_pos (Nat.le_of_dvd hz.1 hcz) hc, ?_, ?_⟩
    · change α * (z / R.gcd id) * R.gcd id ∈ A
      rw [mul_assoc, hzeq]
      exact hz.2.1
    · change β * (z / R.gcd id) * R.gcd id ∈ A
      rw [mul_assoc, hzeq]
      exact hz.2.2
  have bound {u v : ℕ} (hu : u ∈ B) (hv : v ∈ B) : u / u.gcd v ≤ A.card := by
    have hu' : u * (α*c) ∈ A := by
      simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (hrepresented hu).2.1
    have hv' : v * (α*c) ∈ A := by
      simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (hrepresented hv).2.1
    have h := div_gcd_le_card A hbad hu' hv'
      (Nat.mul_pos (hrepresented hu).1 (Nat.mul_pos hαpos hc)).ne'
    rwa [div_gcd_mul_right u v (α*c) (Nat.mul_pos hαpos hc)] at h
  exact ⟨bound hd he, by simpa only [Nat.gcd_comm] using bound he hd⟩

private lemma square_lt_of_window {N G p α : ℕ} (hG : 0 < G)
    (hsmall : 4 * G ≤ N)
    (hp : p ∈ Finset.Icc (2 * N - 2 * G) (2 * N - G))
    (hα : α ∈ Finset.Icc ((p + 1) / 2) N) :
    N * N < 2 * (α * α) := by
  obtain ⟨hplower, _hpupper⟩ := Finset.mem_Icc.mp hp
  obtain ⟨hαlower, _hαupper⟩ := Finset.mem_Icc.mp hα
  have hGN : G ≤ N := by omega
  have hsub : N - G + G = N := Nat.sub_add_cancel hGN
  have halower : N - G ≤ α := by omega
  have hthree : 3 * G ≤ N - G := by omega
  nlinarith [sq_nonneg ((N - G : ℤ) - 3 * G),
    sq_nonneg ((α : ℤ) - (N - G))]

private def primeFold (p q : ℕ) : ℕ := max q (p - q)

private lemma primeFold_injective_on_odd_primes {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp2 : 2 < p) (hq2 : 2 < q) (hr2 : 2 < r)
    (hqp : q ≤ p) (hrp : r ≤ p)
    (hfold : primeFold p q = primeFold p r) : q = r := by
  have hor : q = r ∨ q + r = p := by
    dsimp only [primeFold] at hfold
    by_cases hqside : q ≤ p - q
    · rw [max_eq_right hqside] at hfold
      by_cases hrside : r ≤ p - r
      · rw [max_eq_right hrside] at hfold
        left
        omega
      · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hrside))] at hfold
        right
        omega
    · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hqside))] at hfold
      by_cases hrside : r ≤ p - r
      · rw [max_eq_right hrside] at hfold
        right
        omega
      · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hrside))] at hfold
        left
        exact hfold
  rcases hor with h | hsum
  · exact h
  · obtain ⟨kp, hkp⟩ := hp.odd_of_ne_two (by omega)
    obtain ⟨kq, hkq⟩ := hq.odd_of_ne_two (by omega)
    obtain ⟨kr, hkr⟩ := hr.odd_of_ne_two (by omega)
    omega

private lemma primeFold_mem_J {N p q : ℕ} (hpN : N < p) (hpupper : p ≤ 2 * N)
    (hq : q ∈ Finset.Icc (p - N) N) :
    primeFold p q ∈ Finset.Icc ((p + 1) / 2) N := by
  obtain ⟨hqlower, hqupper⟩ := Finset.mem_Icc.mp hq
  have hqp : q ≤ p := hqupper.trans hpN.le
  have hsubupper : p - q ≤ N := by omega
  apply Finset.mem_Icc.mpr
  constructor
  · dsimp only [primeFold]
    omega
  · exact max_le hqupper hsubupper

private lemma representationCount_primeFold_eq_zero (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    {p q : ℕ} (hq : q.Prime) (hqp : q ≤ p)
    (hlarge : A.card < 2 * q) :
    representationCount A p (primeFold p q) = 0 := by
  rw [representationCount, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨d, hd⟩
  have hαpos : 0 < primeFold p q :=
    lt_max_of_lt_left hq.pos
  have hdata := (mem_representedMultipliers hαpos).mp hd
  by_cases hside : q ≤ p - q
  · have hfold : primeFold p q = p - q := max_eq_right hside
    have hcomp : p - primeFold p q = q := by rw [hfold]; omega
    have hmem : q * d ∈ A := by simpa only [hcomp] using hdata.2.2
    exact (prime_not_dvd_of_card_le_two_mul A h₀ hgcd hbad hq hlarge hmem)
      (dvd_mul_right q d)
  · have hfold : primeFold p q = q :=
      max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hside))
    have hmem : q * d ∈ A := by simpa only [hfold] using hdata.2.1
    exact (prime_not_dvd_of_card_le_two_mul A h₀ hgcd hbad hq hlarge hmem)
      (dvd_mul_right q d)

private lemma primeInterval_card_le_zeroFibers (A : Finset ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬ GrahamBound A)
    {p : ℕ} (hp : p.Prime) (hpN : A.card < p) (hpupper : p < 2 * A.card)
    (hlower : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      A.card < 2 * q)
    (hq2 : ∀ q ∈ (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      2 < q) :
    ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card ≤
      ((Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
        representationCount A p α = 0).card := by
  classical
  let Q := (Finset.Icc (p - A.card) A.card).filter Nat.Prime
  let Z := (Finset.Icc ((p + 1) / 2) A.card).filter fun α ↦
    representationCount A p α = 0
  apply Finset.card_le_card_of_injOn (primeFold p)
  · intro q hqQ
    have hqI := (Finset.mem_filter.mp hqQ).1
    have hqprime := (Finset.mem_filter.mp hqQ).2
    apply Finset.mem_filter.mpr
    refine ⟨primeFold_mem_J hpN hpupper.le hqI, ?_⟩
    exact representationCount_primeFold_eq_zero A h₀ hgcd hbad hqprime
      ((Finset.mem_Icc.mp hqI).2.trans hpN.le) (hlower q hqQ)
  · intro q hqQ r hrQ hfold
    have hqI := (Finset.mem_filter.mp hqQ).1
    have hrI := (Finset.mem_filter.mp hrQ).1
    exact primeFold_injective_on_odd_primes hp
      (Finset.mem_filter.mp hqQ).2 (Finset.mem_filter.mp hrQ).2
      (by omega) (hq2 q hqQ) (hq2 r hrQ)
      ((Finset.mem_Icc.mp hqI).2.trans hpN.le)
      ((Finset.mem_Icc.mp hrI).2.trans hpN.le) hfold

private lemma primeInterval_card_le_collisionExcess_of_window
    (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬GrahamBound A)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    {p : ℕ}
    (hpwin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G))
    (hp : p.Prime) :
    ((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card ≤
      collisionExcess A p := by
  have hpN : A.card < p := by
    have hlo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hpupper : p < 2 * A.card := by
    have hi := (Finset.mem_Icc.mp hpwin).2
    omega
  have hlower : ∀ q ∈
      (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      A.card < 2 * q := by
    intro q hq
    have hqI := (Finset.mem_filter.mp hq).1
    have hqlo := (Finset.mem_Icc.mp hqI).1
    have hpLo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hq2 : ∀ q ∈
      (Finset.Icc (p - A.card) A.card).filter Nat.Prime,
      2 < q := by
    intro q hq
    have hqI := (Finset.mem_filter.mp hq).1
    have hqlo := (Finset.mem_Icc.mp hqI).1
    have hpLo := (Finset.mem_Icc.mp hpwin).1
    omega
  have hzero := primeInterval_card_le_zeroFibers
    A h₀ hgcd hbad hp hpN hpupper hlower hq2
  have hexcess := zero_card_le_representation_excess
    A h₀ hgcd hbad hp hpN hpupper
  exact hzero.trans (by simpa only [collisionExcess] using hexcess)

private lemma basicPrimeCollisionLower_le_totalCollisionExcess
    (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1) (hbad : ¬GrahamBound A)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card) :
    basicPrimeCollisionLower A.card G ≤ totalCollisionExcess A G := by
  unfold basicPrimeCollisionLower totalCollisionExcess
  apply Finset.sum_le_sum
  intro p hp
  exact primeInterval_card_le_collisionExcess_of_window
    A G h₀ hgcd hbad hG hGN
      (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2

private lemma globalD_le_card (A : Finset ℕ) (G : ℕ)
    (hbad : ¬ GrahamBound A) (hG : 0 < G) (hsmall : 4 * G ≤ A.card) :
    globalD A G ≤ A.card := by
  classical
  rw [globalD, Finset.sup_le_iff]
  intro de hde
  rw [globalReducedPairs] at hde
  obtain ⟨p, hpF, hde⟩ := Finset.mem_biUnion.mp hde
  obtain ⟨hpwin, hp⟩ := Finset.mem_filter.mp hpF
  obtain ⟨α, hαJ, hde⟩ := Finset.mem_biUnion.mp hde
  have hpwinFin : p ∈ Finset.Icc (2 * A.card - 2 * G) (2 * A.card - G) := hpwin
  have hαJFin : α ∈ Finset.Icc ((p + 1) / 2) A.card := hαJ
  obtain ⟨hplower, _hpupper⟩ := Finset.mem_Icc.mp hpwinFin
  obtain ⟨hαlower, hαupper⟩ := Finset.mem_Icc.mp hαJFin
  simp only [reducedPairs] at hde
  obtain ⟨⟨d, e⟩, hdeB, rfl⟩ := Finset.mem_image.mp hde
  obtain ⟨hd, he⟩ := Finset.mem_product.mp hdeB
  have hpN : A.card < p := by omega
  have hαpos : 0 < α := by omega
  have hαp : α < p := hαupper.trans_lt hpN
  have hsq := square_lt_of_window hG hsmall hpwinFin hαJFin
  obtain ⟨hdlt, helt⟩ :=
    reducedPair_coordinates_lt_card A hbad hp hαpos hαp hsq hd he
  exact max_le hdlt helt

private lemma primeWindow_card_le_add_one {N G : ℕ} (hGN : G ≤ N) :
    (primeWindow N G).card ≤ G + 1 := by
  calc
    (primeWindow N G).card ≤
        (Finset.Icc (2 * N - 2 * G) (2 * N - G)).card := by
      exact Finset.card_filter_le _ _
    _ = G + 1 := by
      rw [Nat.card_Icc]
      omega

private lemma grahamBound_of_basic_analytic_separation
    (A : Finset ℕ) (G : ℕ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    (hseparate :
      (primeWindow A.card G).card *
          (firstMomentTriples A.card A.card (A.card - 2 * G)).card +
        (firstMomentTriples A.card A.card (A.card - G)).card *
          (firstMomentTriples A.card A.card (A.card - 2 * G)).card <
        basicPrimeCollisionLower A.card G) :
    GrahamBound A := by
  by_contra hbad
  have hN : 0 < A.card := by omega
  have htwoG : 2 * G ≤ A.card := by omega
  have hD : globalD A G ≤ A.card :=
    globalD_le_card A G hbad hG (by omega)
  have hF₁ :
      (firstMomentTriples A.card (globalD A G) (A.card - G)).card ≤
        (firstMomentTriples A.card A.card (A.card - G)).card :=
    Finset.card_le_card (firstMomentTriples_mono_cap hD)
  have hF₂ :
      (firstMomentTriples A.card (globalD A G) (A.card - 2 * G)).card ≤
        (firstMomentTriples A.card A.card (A.card - 2 * G)).card :=
    Finset.card_le_card (firstMomentTriples_mono_cap hD)
  have hlower := basicPrimeCollisionLower_le_totalCollisionExcess
    A G h₀ hgcd hbad hG hGN
  have hcollision := totalCollisionExcess_le_upper A G hbad hG hGN
  have hlinear := totalLinearUpper_le_primeWindow_mul_firstMoment
    (N := A.card) (G := G) (D := globalD A G) hN htwoG
  have hbilinear := totalBilinearUpper_le_firstMoment_product
    (N := A.card) (G := G) (D := globalD A G) hN htwoG
  have hlinear' :
      totalLinearUpper A.card G (globalD A G) ≤
        (primeWindow A.card G).card *
          (firstMomentTriples A.card A.card (A.card - 2 * G)).card :=
    hlinear.trans (Nat.mul_le_mul_left _ hF₂)
  have hbilinear' :
      totalBilinearUpper A.card G (globalD A G) ≤
        (firstMomentTriples A.card A.card (A.card - G)).card *
          (firstMomentTriples A.card A.card (A.card - 2 * G)).card :=
    hbilinear.trans (Nat.mul_le_mul hF₁ hF₂)
  omega

private lemma analytic_prime_bounds {N G V : ℕ}
    (hN : 0 < N) (hG : 0 < G) (h10 : 10 * G ≤ N)
    (hlog : 20000 ≤ Real.log (N : ℝ))
    (hGlower : (N : ℝ) / (2 * Real.log N ^ 4) ≤ (G : ℝ))
    (hshort : ∀ v : ℕ, V ≤ v → ∀ u : ℕ, u ≤ v → v ≤ 2 * (u - 1) →
      (v : ℝ) / Real.log v ^ 5 ≤ (v : ℝ) - ((u - 1 : ℕ) : ℝ) →
      ((v : ℝ) - ((u - 1 : ℕ) : ℝ)) / (2 * Real.log v) ≤
        (((Finset.Icc u v).filter Nat.Prime).card : ℝ))
    (hVN : V ≤ N) :
    (G : ℝ) / (4 * Real.log N) ≤ ((primeWindow N G).card : ℝ) ∧
      ∀ p ∈ primeWindow N G,
        (G : ℝ) / (2 * Real.log N) ≤
          (((Finset.Icc (p - N) N).filter Nat.Prime).card : ℝ) := by
  have hN2 : 2 ≤ N := by
    have hLpos : 0 < Real.log (N : ℝ) := by linarith
    have : (1 : ℝ) < N := (Real.log_pos_iff (by positivity)).mp hLpos
    have hNat : 1 < N := by exact_mod_cast this
    omega
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hlog4 : (4 : ℝ) ≤ Real.log (N : ℝ) := by linarith
  have hGle : G ≤ N := by omega
  have h2Gle : 2 * G ≤ N := by omega
  let u := 2 * N - 2 * G
  let v := 2 * N - G
  have huv : u ≤ v := by dsimp only [u, v]; omega
  have hNv : N ≤ v := by dsimp only [v]; omega
  have hv2N : v ≤ 2 * N := by dsimp only [v]; omega
  have hvhalf : v ≤ 2 * (u - 1) := by dsimp only [u, v]; omega
  have hlogNv : Real.log (N : ℝ) ≤ Real.log (v : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hN)
    exact_mod_cast hNv
  have hlogvpos : 0 < Real.log (v : ℝ) := hlogpos.trans_le hlogNv
  have hlogv2 : Real.log (v : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have hvpos : (0 : ℝ) < v := by exact_mod_cast hN.trans_le hNv
    have hlogvle : Real.log (v : ℝ) ≤ Real.log (2 * (N : ℝ)) := by
      apply Real.log_le_log hvpos
      exact_mod_cast hv2N
    have hlog2le : Real.log 2 ≤ Real.log (N : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hN2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by exact_mod_cast hN.ne')] at hlogvle
    linarith
  have hwidthNat : G ≤ v - (u - 1) := by dsimp only [u, v]; omega
  have hwidth : (v : ℝ) / Real.log v ^ 5 ≤
      (v : ℝ) - ((u - 1 : ℕ) : ℝ) := by
    have hlogNpow : 0 < Real.log (N : ℝ) ^ 5 := pow_pos hlogpos 5
    have hlogvpow : 0 < Real.log (v : ℝ) ^ 5 := pow_pos hlogvpos 5
    have hscale : 2 * (N : ℝ) / Real.log N ^ 5 ≤
        (N : ℝ) / (2 * Real.log N ^ 4) := by
      apply (div_le_div_iff₀ hlogNpow
        (mul_pos (by norm_num) (pow_pos hlogpos 4))).2
      calc
        2 * (N : ℝ) * (2 * Real.log N ^ 4) =
            4 * ((N : ℝ) * Real.log N ^ 4) := by ring
        _ ≤ Real.log N * ((N : ℝ) * Real.log N ^ 4) :=
          mul_le_mul_of_nonneg_right hlog4 (by positivity)
        _ = (N : ℝ) * Real.log N ^ 5 := by rw [pow_succ]; ring
    calc
      (v : ℝ) / Real.log v ^ 5 ≤
          (2 * (N : ℝ)) / Real.log v ^ 5 :=
        div_le_div_of_nonneg_right (by exact_mod_cast hv2N) hlogvpow.le
      _ ≤ (2 * (N : ℝ)) / Real.log N ^ 5 := by
        apply div_le_div_of_nonneg_left (by positivity) hlogNpow
        exact pow_le_pow_left₀ hlogpos.le hlogNv 5
      _ ≤ (N : ℝ) / (2 * Real.log N ^ 4) := hscale
      _ ≤ (G : ℝ) := hGlower
      _ ≤ (v : ℝ) - ((u - 1 : ℕ) : ℝ) := by
        rw [← Nat.cast_sub ((Nat.sub_le u 1).trans huv)]
        exact_mod_cast hwidthNat
  have houter := hshort v (hVN.trans hNv) u huv hvhalf hwidth
  have houterLower : (G : ℝ) / (4 * Real.log N) ≤
      ((v : ℝ) - ((u - 1 : ℕ) : ℝ)) / (2 * Real.log v) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hlogpos)
      (mul_pos (by norm_num) hlogvpos)).2
    have hWnonneg : (0 : ℝ) ≤ (v : ℝ) - ((u - 1 : ℕ) : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast (Nat.sub_le u 1).trans huv)
    have hGwidth : (G : ℝ) ≤ (v : ℝ) - ((u - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_sub ((Nat.sub_le u 1).trans huv)]
      exact_mod_cast hwidthNat
    calc
      (G : ℝ) * (2 * Real.log v) ≤
          ((v : ℝ) - ((u - 1 : ℕ) : ℝ)) * (2 * Real.log v) :=
        mul_le_mul_of_nonneg_right hGwidth (by positivity)
      _ ≤ ((v : ℝ) - ((u - 1 : ℕ) : ℝ)) *
          (4 * Real.log N) := by
        apply mul_le_mul_of_nonneg_left _ hWnonneg
        linarith
  refine ⟨houterLower.trans ?_, ?_⟩
  · simpa only [primeWindow, u, v] using houter
  · intro p hp
    have hpI := (Finset.mem_filter.mp hp).1
    have hpBounds := Finset.mem_Icc.mp hpI
    let ui := p - N
    have hui : ui ≤ N := by dsimp only [ui]; omega
    have hhalf : N ≤ 2 * (ui - 1) := by dsimp only [ui]; omega
    have hwidthNatI : G ≤ N - (ui - 1) := by dsimp only [ui]; omega
    have hwidthI : (N : ℝ) / Real.log N ^ 5 ≤
        (N : ℝ) - ((ui - 1 : ℕ) : ℝ) := by
      have hscale : (N : ℝ) / Real.log N ^ 5 ≤
          (N : ℝ) / (2 * Real.log N ^ 4) := by
        apply (div_le_div_iff₀ (pow_pos hlogpos 5)
          (mul_pos (by norm_num) (pow_pos hlogpos 4))).2
        calc
          (N : ℝ) * (2 * Real.log N ^ 4) =
              2 * ((N : ℝ) * Real.log N ^ 4) := by ring
          _ ≤ Real.log N * ((N : ℝ) * Real.log N ^ 4) :=
            mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ Real.log N)
              (by positivity)
          _ = (N : ℝ) * Real.log N ^ 5 := by rw [pow_succ]; ring
      exact hscale.trans (hGlower.trans (by
        rw [← Nat.cast_sub ((Nat.sub_le ui 1).trans hui)]
        exact_mod_cast hwidthNatI))
    have hi := hshort N hVN ui hui hhalf hwidthI
    have hGwidth : (G : ℝ) ≤ (N : ℝ) - ((ui - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_sub ((Nat.sub_le ui 1).trans hui)]
      exact_mod_cast hwidthNatI
    calc
      (G : ℝ) / (2 * Real.log N) ≤
          ((N : ℝ) - ((ui - 1 : ℕ) : ℝ)) / (2 * Real.log N) := by gcongr
      _ ≤ (((Finset.Icc ui N).filter Nat.Prime).card : ℝ) := hi
      _ = (((Finset.Icc (p - N) N).filter Nat.Prime).card : ℝ) := by rfl

private lemma grahamBound_of_basic_real_card_separation
    (A : Finset ℕ) (G : ℕ) (RP RQ : ℝ)
    (h₀ : 0 ∉ A) (hgcd : A.gcd id = 1)
    (hG : 0 < G) (hGN : 10 * G ≤ A.card)
    (hRQ : 0 ≤ RQ)
    (hP : RP ≤ ((primeWindow A.card G).card : ℝ))
    (hQ : ∀ p ∈ primeWindow A.card G,
      RQ ≤ (((Finset.Icc (p - A.card) A.card).filter Nat.Prime).card : ℝ))
    (hseparate :
      ((G + 1 : ℕ) : ℝ) * firstMomentRealBound A.card (2 * G) +
          firstMomentRealBound A.card G *
            firstMomentRealBound A.card (2 * G) < RP * RQ) :
    GrahamBound A := by
  have hN : 0 < A.card := by omega
  have hGle : G ≤ A.card := by omega
  have htwoG : 2 * G ≤ A.card := by omega
  let F₁ := (firstMomentTriples A.card A.card (A.card - G)).card
  let F₂ := (firstMomentTriples A.card A.card (A.card - 2 * G)).card
  have hF₁ : (F₁ : ℝ) ≤ firstMomentRealBound A.card G := by
    dsimp only [F₁]
    exact firstMomentTriples_card_real_le_bound hN hGle
  have hF₂ : (F₂ : ℝ) ≤ firstMomentRealBound A.card (2 * G) := by
    dsimp only [F₂]
    exact firstMomentTriples_card_real_le_bound hN htwoG
  have hwindow : (primeWindow A.card G).card ≤ G + 1 :=
    primeWindow_card_le_add_one hGle
  have hwindowReal : ((primeWindow A.card G).card : ℝ) ≤
      ((G + 1 : ℕ) : ℝ) := by
    exact_mod_cast hwindow
  have hB₁nonneg : 0 ≤ firstMomentRealBound A.card G :=
    (Nat.cast_nonneg F₁).trans hF₁
  have hupperReal :
      (((primeWindow A.card G).card * F₂ + F₁ * F₂ : ℕ) : ℝ) ≤
        ((G + 1 : ℕ) : ℝ) * firstMomentRealBound A.card (2 * G) +
          firstMomentRealBound A.card G *
            firstMomentRealBound A.card (2 * G) := by
    simp only [Nat.cast_add, Nat.cast_mul]
    apply add_le_add
    · have hmul :
          ((primeWindow A.card G).card : ℝ) * (F₂ : ℝ) ≤
            ((G + 1 : ℕ) : ℝ) * firstMomentRealBound A.card (2 * G) :=
        mul_le_mul hwindowReal hF₂ (Nat.cast_nonneg F₂) (by positivity)
      simpa only [Nat.cast_add] using hmul
    · exact mul_le_mul hF₁ hF₂ (Nat.cast_nonneg F₂) hB₁nonneg
  have hlowerReal : RP * RQ ≤
      (basicPrimeCollisionLower A.card G : ℝ) :=
    real_mul_le_basicPrimeCollisionLower hRQ hP hQ
  have hstrictReal :
      (((primeWindow A.card G).card * F₂ + F₁ * F₂ : ℕ) : ℝ) <
        (basicPrimeCollisionLower A.card G : ℝ) :=
    hupperReal.trans_lt (hseparate.trans_le hlowerReal)
  have hstrictNat :
      (primeWindow A.card G).card * F₂ + F₁ * F₂ <
        basicPrimeCollisionLower A.card G := by
    exact_mod_cast hstrictReal
  apply grahamBound_of_basic_analytic_separation A G h₀ hgcd hG hGN
  simpa only [F₁, F₂] using hstrictNat

theorem eventual_large_ratio_or_large_prime
    (estimate : ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - x| ≤ δ * x / Real.log x ^ 5) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A.card = N →
      0 ∉ A → A.gcd id = 1 → GrahamBound A := by
  have hshortEv := eventually_primeInterval_card_real_lower 5 estimate
  rw [eventually_atTop] at hshortEv
  obtain ⟨V, hshort⟩ := hshortEv
  have hlogEv : ∀ᶠ N : ℕ in atTop, 20000 ≤ Real.log (N : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 20000)
  filter_upwards [eventually_analyticG_bounds, hlogEv,
    eventually_ge_atTop V] with N hGb hlog hVN
  intro A hcard h₀ hgcd
  let G := analyticG N
  have hGlower : (N : ℝ) / (2 * Real.log N ^ 4) ≤ (G : ℝ) := hGb.1
  have hGupper : (G : ℝ) ≤ (N : ℝ) / Real.log N ^ 4 := hGb.2.1
  have hG : 0 < G := by exact_mod_cast hGb.2.2
  have hN : 0 < N := by
    by_contra hn
    have hNzero : N = 0 := Nat.eq_zero_of_not_pos hn
    norm_num [hNzero] at hlog
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hL4 : (10 : ℝ) ≤ Real.log (N : ℝ) ^ 4 := by
    have : (10 : ℝ) ≤ Real.log (N : ℝ) := by linarith
    nlinarith [sq_nonneg (Real.log (N : ℝ)),
      sq_nonneg (Real.log (N : ℝ) ^ 2 - 10)]
  have h10real : (10 : ℝ) * (G : ℝ) ≤ N := by
    calc
      (10 : ℝ) * (G : ℝ) ≤ 10 * ((N : ℝ) / Real.log N ^ 4) :=
        mul_le_mul_of_nonneg_left hGupper (by norm_num)
      _ ≤ (N : ℝ) := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (pow_pos hlogpos 4)).2
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_right hL4 (Nat.cast_nonneg N)
  have h10 : 10 * G ≤ N := by exact_mod_cast h10real
  have h2 : 2 * G ≤ N := by omega
  have hpcounts := analytic_prime_bounds hN hG h10 hlog hGlower
    hshort hVN
  have hsep := analytic_numeric_separation hN h2 hlog hGlower hGupper hG
  subst N
  apply grahamBound_of_basic_real_card_separation A G
      ((G : ℝ) / (4 * Real.log A.card))
      ((G : ℝ) / (2 * Real.log A.card)) h₀ hgcd hG h10
  · positivity
  · simpa only using hpcounts.1
  · intro p hp
    exact hpcounts.2 p hp
  · simpa only using hsep

end Erdos402Log

namespace Erdos402PrimeCardinality
open Finset

private lemma ratio_scale (k a b : ℕ) (hk : 0<k) :
    (k*a)/((k*a).gcd (k*b)) = a/a.gcd b := by
  rw [Nat.gcd_mul_left,Nat.mul_div_mul_left _ _ hk]

private lemma score_scale (A : Finset ℕ) (k : ℕ) (hk : 0<k) :
    ((A.image (k*·)) ×ˢ (A.image (k*·))).sup (fun p => p.1 / p.1.gcd p.2) = (A ×ˢ A).sup (fun p => p.1 / p.1.gcd p.2) := by
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨a,b⟩ hab
    obtain ⟨⟨i,hi,rfl⟩,⟨j,hj,rfl⟩⟩ := (mem_product.mp hab).imp mem_image.mp mem_image.mp
    change (k*i)/((k*i).gcd (k*j)) ≤ (A ×ˢ A).sup (fun p => p.1 / p.1.gcd p.2)
    rw [ratio_scale k i j hk]
    exact Finset.le_sup (f:=fun p : ℕ×ℕ => p.1 / p.1.gcd p.2) (b:=(i,j)) (mem_product.mpr ⟨hi,hj⟩)
  · apply Finset.sup_le
    rintro ⟨a,b⟩ hab
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    change a/a.gcd b ≤ _
    rw [←ratio_scale k a b hk]
    exact Finset.le_sup (f:=fun p : ℕ×ℕ => p.1 / p.1.gcd p.2) (b:=(k*a,k*b))
        (mem_product.mpr ⟨mem_image_of_mem (k*·) ha,mem_image_of_mem (k*·) hb⟩)

/-- Complementing divisors of a common multiple reverses each directed gcd quotient. -/
private lemma reciprocal_ratio {i j T : ℕ} (hi : 0 < i) (hj : 0 < j) (hT : 0 < T)
    (di : i∣T) (dj : j∣T) :
    (T/i)/((T/i).gcd (T/j)) = j/(j.gcd i) := by
  have left : (i*j)*(T/i)=T*j := by
    calc _ = (T/i*i)*j := by ring
         _ = _ := by rw [Nat.div_mul_cancel di]
  have right : (i*j)*(T/j)=T*i := by
    calc _ = (T/j*j)*i := by ring
         _ = _ := by rw [Nat.div_mul_cancel dj]
  rw [← ratio_scale (i*j) (T/i) (T/j) (Nat.mul_pos hi hj),left,right,ratio_scale T j i hT]

private lemma model_bound {n T : ℕ} (hT : 0<T) (dvd : ∀ i∈Icc 1 n,i∣T) :
    (((Icc 1 n).image (T/·)) ×ˢ ((Icc 1 n).image (T/·))).sup (fun p => p.1 / p.1.gcd p.2) ≤ n := by
  apply Finset.sup_le
  rintro ⟨a,b⟩ hab
  obtain ⟨⟨i,hi,rfl⟩,⟨j,hj,rfl⟩⟩ := (mem_product.mp hab).imp mem_image.mp mem_image.mp
  change (T/i)/((T/i).gcd (T/j)) ≤ n
  rw [reciprocal_ratio (mem_Icc.mp hi).1 (mem_Icc.mp hj).1 hT (dvd i hi) (dvd j hj)]
  exact (Nat.div_le_self ..).trans (mem_Icc.mp hj).2

private lemma ordinary_score {n : ℕ} (hn : 0<n) : ((Icc 1 n) ×ˢ (Icc 1 n)).sup (fun p => p.1 / p.1.gcd p.2) = n := by
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨a,b⟩ p
    exact (Nat.div_le_self ..).trans (mem_Icc.mp (mem_product.mp p).1).2
  · have pair : (n,1) ∈ Icc 1 n ×ˢ Icc 1 n := mem_product.mpr
      ⟨mem_Icc.mpr ⟨hn,le_rfl⟩,mem_Icc.mpr ⟨le_rfl,hn⟩⟩
    simpa using Finset.le_sup (f:=fun p : ℕ×ℕ => p.1 / p.1.gcd p.2) pair

private lemma reciprocal_score {n T : ℕ} (hn : 0<n) (hT : 0<T)
    (dvd : ∀ i∈Icc 1 n,i∣T) : (((Icc 1 n).image (T/·)) ×ˢ ((Icc 1 n).image (T/·))).sup (fun p => p.1 / p.1.gcd p.2) = n := by
  apply (model_bound hT dvd).antisymm
  have h1 : 1 ∈ Icc 1 n := mem_Icc.mpr ⟨le_rfl,hn⟩
  have hn' : n ∈ Icc 1 n := mem_Icc.mpr ⟨hn,le_rfl⟩
  have P : (T/1,T/n) ∈ (Icc 1 n).image (T/·) ×ˢ (Icc 1 n).image (T/·) := Finset.mem_product.mpr
    ⟨mem_image_of_mem (T/·) h1,mem_image_of_mem (T/·) hn'⟩
  have bound := Finset.le_sup (f:=fun p : ℕ×ℕ => p.1 / p.1.gcd p.2) (b:=(T/1,T/n)) P
  change (T/1)/((T/1).gcd (T/n)) ≤ _ at bound
  rw [reciprocal_ratio (by decide : 0<1) hn hT (dvd 1 h1) (dvd n hn')] at bound
  simpa only [Nat.gcd_one_right,Nat.div_one] using bound

private lemma primitive {A : Finset ℕ} (ha : A.Nonempty) (hz : 0∉A) :
    ∃ B : Finset ℕ, ∃ k>0, A=B.image (k*·) ∧ B.card=A.card ∧ 0∉B ∧ B.gcd id=1 := by
  obtain ⟨u,hu⟩ := ha
  have u0 : u≠0 := fun e => hz (e ▸ hu)
  let k := A.gcd id
  let B := A.image (·/k)
  have hk : 0<k := by
    apply Nat.pos_of_ne_zero
    intro e
    exact u0 ((A.gcd_eq_zero_iff.mp e) u hu)
  have recover (i) (hi:i∈A) : k*(i/k)=i := Nat.mul_div_cancel' (Finset.gcd_dvd (f:=id) hi)
  have hA : A = B.image (k*·) := by
    ext i
    constructor
    · intro hi
      exact mem_image.mpr ⟨i/k,mem_image_of_mem _ hi,recover _ hi⟩
    · intro hi
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hi
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hu
      rwa [recover _ hj]
  refine ⟨B,k,hk,hA,card_image_of_injOn (fun i hi j hj h => ?_),?_,?_⟩
  · change i/k=j/k at h
    rw [←recover i hi,←recover j hj,h]
  · intro h
    obtain ⟨i,hi,eq⟩ := mem_image.mp h
    have iz : i=0 := by calc
      i = k*(i/k) := (recover i hi).symm
      _ = 0 := by rw [eq,mul_zero]
    exact hz (iz ▸ hi)
  · dsimp [B]
    rw [Finset.gcd_image]
    exact gcd_div_id_eq_one hu u0

private lemma classify {B : Finset ℕ} {n : ℕ} (card : B.card=n) (hz : 0∉B)
    (ub : ∀ a∈B, ∀ b∈B, a/a.gcd b≤n) (extreme : 1∈B ∨ B.lcm id∈B) :
    B=Icc 1 n ∨ ∃ t>0, B=(Icc 1 n).image (t*(Icc 1 n).lcm id / ·) := by
  have positive (a) (ha : a∈B) : 0<a := Nat.pos_of_ne_zero (fun e => hz (e ▸ ha))
  have fill (F : Finset ℕ) (hc : F.card=n) (sub : F⊆Icc 1 n) : F=Icc 1 n :=
    eq_of_subset_of_card_le sub (by simp [hc])
  rcases extreme with unit|top
  · left
    apply fill _ card
    intro a ha
    exact mem_Icc.mpr ⟨positive a ha,by simpa using ub a ha 1 unit⟩
  · right
    let T := B.lcm id
    have tpos : 0<T := positive _ top
    have dvd (b) (hb : b∈B) : b∣T := Finset.dvd_lcm (f:=id) hb
    have inv (b) (hb:b∈B) : T/(T/b)=b := Nat.div_div_self (dvd b hb) tpos.ne'
    let I := B.image (T/·)
    have inj : Set.InjOn (T/·) (B:Set ℕ) := by
      intro a ha b hb e
      change T/a=T/b at e
      rw [←inv a ha,←inv b hb,e]
    have ir : I = Icc 1 n := by
      apply fill _ ((card_image_of_injOn inj).trans card)
      intro i hi
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hi
      apply mem_Icc.mpr
      refine ⟨Nat.div_pos (Nat.le_of_dvd tpos (dvd b hb)) (positive b hb),?_⟩
      simpa only [Nat.gcd_eq_right (dvd b hb)] using ub T top b hb
    have im : I.image (T/·)=B := by
      ext b
      constructor
      · intro hb
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hb
        obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
        rwa [inv j hj]
      · intro hb
        exact mem_image.mpr ⟨T/b,mem_image_of_mem _ hb,inv b hb⟩
    have dt : (Icc 1 n).lcm id ∣ T := by
      apply Finset.lcm_dvd
      intro i hi
      rw [←ir] at hi
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hi
      exact Nat.div_dvd_of_dvd (dvd b hb)
    obtain ⟨t,ht⟩ := dt
    have good : 0<t := by
      by_contra! z
      have tz : t=0 := by omega
      rw [tz,mul_zero] at ht
      omega
    refine ⟨t,good,?_⟩
    rw [←im,ir,ht,Nat.mul_comm t _]

private theorem recover_card {A : Finset ℕ} {f : ℕ → ℕ} (hf : Set.InjOn f A)
    {b : ℕ} (bounds : ∀ x ∈ A, f x ∈ Icc 1 b) : A.card ≤ b := by
  calc
    A.card = (A.image f).card := (card_image_of_injOn hf).symm
    _ ≤ (Icc 1 b).card := card_le_card (image_subset_iff.mpr bounds)
    _ = b := by simp

private theorem partition_product {U V : Finset ℕ} {n : ℕ} (hU : U.Nonempty)
    (hV : V.Nonempty) (up : ∀ u ∈ U, 0 < u) (vp : ∀ v ∈ V, 0 < v)
    (cross : ∀ u ∈ U, ∀ v ∈ V, u ∣ v ∧ v / u ≤ n) : U.card * V.card ≤ n := by
  let d := U.lcm id
  have ud (u) (hu : u ∈ U) : u ∣ d := dvd_lcm (f := id) hu
  have dv (v) (hv : v ∈ V) : d ∣ v := lcm_dvd fun u hu => (cross u hu v hv).1
  have dp : 0 < d := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr fun u hu => (up u hu).ne')
  let l := U.min' hU
  let h := V.max' hV
  have hl : l ∈ U := min'_mem _ _
  have hh : h ∈ V := max'_mem _ _
  have Ubound : U.card ≤ d / l := by
    apply recover_card (f := (d / ·))
    · intro u hu v hv e
      change d / u = d / v at e
      rw [← Nat.div_div_self (ud u hu) dp.ne', e, Nat.div_div_self (ud v hv) dp.ne']
    · intro u hu
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd dp (ud _ hu)) (up _ hu),
        Nat.div_le_div_left (min'_le U u hu) (up _ hl)⟩
  have Vbound : V.card ≤ h / d := by
    apply recover_card (f := (· / d))
    · intro u hu v hv e
      change u / d = v / d at e
      rw [← Nat.div_mul_cancel (dv u hu), e, Nat.div_mul_cancel (dv v hv)]
    · intro v hv
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (vp _ hv) (dv _ hv)) dp,
        Nat.div_le_div_right (le_max' V v hv)⟩
  calc
    U.card * V.card ≤ (d / l) * (h / d) := Nat.mul_le_mul Ubound Vbound
    _ = h / l := by
      apply Nat.eq_of_mul_eq_mul_right (up _ hl)
      calc
        d / l * (h / d) * l = h / d * (d / l * l) := by ring
        _ = h := by rw [Nat.div_mul_cancel (ud _ hl), Nat.div_mul_cancel (dv _ hh)]
        _ = h / l * l := (Nat.div_mul_cancel (cross _ hl _ hh).1).symm
    _ ≤ n := (cross _ hl _ hh).2

private theorem cross_quotient {a b q n : ℕ} (ha : 0 < a) (hq : q.Prime)
    (hn : n < 2*q) (qa : q ∣ a) (qb : ¬ q ∣ b)
    (ab : a / a.gcd b ≤ n) (ba : b / b.gcd a ≤ n) :
    q ≤ n ∧ a / q ∣ b ∧ b / (a / q) ≤ n := by
  let g := a.gcd b
  have ag : a/g*g=a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
  have qg : ¬ q ∣ g := fun t => qb (t.trans (Nat.gcd_dvd_right a b))
  have qt : q ∣ a/g := (hq.dvd_mul.mp (show q ∣ a/g*g by rw [ag]; exact qa)).resolve_right qg
  obtain ⟨k,hk⟩ := qt
  have pos : 0 < a/g := Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b))
    (Nat.gcd_pos_of_pos_left _ ha)
  have ub : a/g ≤ n := ab
  have ko : k=1 := by
    by_contra! h
    have kp : 0 < k := by
      apply Nat.pos_of_ne_zero
      rintro rfl
      simp only [Nat.mul_zero] at hk
      omega
    have := Nat.mul_le_mul_left q (show 2 ≤ k by omega)
    omega
  have aq : a/q = g := by
    have e : a=q*g := by simpa [hk,ko] using ag.symm
    rw [e,Nat.mul_div_cancel_left _ hq.pos]
  rw [aq]
  exact ⟨by simpa [hk, ko] using ub,Nat.gcd_dvd_right a b,
    by simpa [g,Nat.gcd_comm a b] using ba⟩

private theorem one_in_image {A : Finset ℕ} {n : ℕ} (card : A.card=n) (hn : 0<n)
    (f : ℕ → ℕ) (hf : Set.InjOn f A) (bounds : ∀ x ∈ A, f x ∈ Icc 1 n) :
    ∃ x ∈ A, f x = 1 := by
  have eq : A.image f = Icc 1 n := eq_of_subset_of_card_le (image_subset_iff.mpr bounds)
    (by simp [card_image_of_injOn hf,card])
  exact mem_image.mp (eq ▸ (mem_Icc.mpr ⟨by decide,hn⟩ : 1 ∈ Icc 1 n))

/-- A prime exceeding half the family size forces one of the two extremal elements. -/
theorem rigidity {A : Finset ℕ} {n q : ℕ} (card : A.card=n) (hn : 5≤n)
    (pos : ∀ a ∈ A, 0 < a) (primitive : A.gcd id=1)
    (bound : ∀ a∈A, ∀ b∈A, a/a.gcd b≤n)
    (hq : q.Prime) (large : n < 2*q) (occurs : ∃ a∈A, q∣a) :
    1∈A ∨ A.lcm id∈A := by
  classical
  let P := A.filter (q ∣ ·)
  let V := A.filter (fun b => ¬ q ∣ b)
  let U := P.image (·/q)
  obtain ⟨a,ha,hqa⟩ := occurs
  have haP : a∈P := mem_filter.mpr ⟨ha,hqa⟩
  have uNe : U.Nonempty := ⟨a/q,mem_image_of_mem _ haP⟩
  have vNe : V.Nonempty := by
    by_contra! h
    have qg : q ∣ A.gcd id := dvd_gcd fun b hb => by
      by_contra hq'
      have hin : b ∈ V := mem_filter.mpr ⟨hb,hq'⟩
      rw [h] at hin
      exact notMem_empty b hin
    exact hq.not_dvd_one (primitive ▸ qg)
  have un (u) (hu:u∈U) : ∃ x∈P, x/q=u := mem_image.mp hu
  have up (u) (hu:u∈U) : 0<u := by
    obtain ⟨x,hx,rfl⟩ := un u hu
    obtain ⟨inA,div⟩ := mem_filter.mp hx
    exact Nat.div_pos (Nat.le_of_dvd (pos _ inA) div) hq.pos
  have vp (v) (hv:v∈V) : 0<v := pos v (mem_filter.mp hv).1
  have cross (x) (hx:x∈P) (v) (hv:v∈V) :
      q ≤ n ∧ x/q ∣ v ∧ v/(x/q) ≤ n := by
    obtain ⟨xa,dx⟩ := mem_filter.mp hx
    obtain ⟨va,ndv⟩ := mem_filter.mp hv
    exact cross_quotient (pos _ xa) hq large dx ndv (bound _ xa _ va) (bound _ va _ xa)
  have uv : U.card*V.card≤n := partition_product uNe vNe up vp (by
    intro u hu v hv
    obtain ⟨x,hx,rfl⟩ := un u hu
    exact (cross _ hx _ hv).2)
  have inj : Set.InjOn (·/q) P := by
    intro x hx y hy e
    change x/q=y/q at e
    rw [← Nat.div_mul_cancel (mem_filter.mp hx).2,e,Nat.div_mul_cancel (mem_filter.mp hy).2]
  have sum : U.card+V.card=n := by
    change (P.image (·/q)).card + V.card=n
    rw [card_image_of_injOn inj, ←card]
    exact card_filter_add_card_filter_not ..
  have singleton : U.card=1 ∨ V.card=1 := by
    have := card_pos.mpr uNe
    have := card_pos.mpr vNe
    by_contra! neither
    have uu : 2≤U.card := by omega
    have vv : 2≤V.card := by omega
    have cu := Nat.sub_add_cancel uu
    have cv := Nat.sub_add_cancel vv
    nlinarith [Nat.zero_le ((U.card-2)*(V.card-2))]
  obtain ⟨v,hv⟩ := vNe
  have qle := (cross _ haP _ hv).1
  rcases singleton with sing|sing
  · left
    obtain ⟨u,su⟩ := card_eq_one.mp sing
    have only (x) (hx:x∈P) : x/q=u := mem_singleton.mp (su ▸ (mem_image_of_mem (·/q) hx : x/q∈U))
    have ug : u∣A.gcd id := dvd_gcd fun x hx => by
      by_cases dx : q∣x
      · rw [←only _ (mem_filter.mpr ⟨hx,dx⟩)]
        exact Nat.div_dvd_of_dvd dx
      · rw [←only _ haP]
        exact (cross _ haP _ (mem_filter.mpr ⟨hx,dx⟩)).2.1
    have uone : u=1 := Nat.dvd_one.mp (primitive ▸ ug)
    obtain ⟨z,hz,ez⟩ := one_in_image card (by omega) id Function.injective_id.injOn (by
      intro x hx
      refine mem_Icc.mpr ⟨pos _ hx,?_⟩
      by_cases dx : q∣x
      · have t := only _ (mem_filter.mpr ⟨hx,dx⟩)
        have e : x=q := by simpa [t,uone] using (Nat.div_mul_cancel dx).symm
        simpa [e] using qle
      · simpa [only _ haP,uone] using (cross _ haP _ (mem_filter.mpr ⟨hx,dx⟩)).2.2)
    exact ez ▸ hz
  · right
    have only (x) (hx:x∈V) : x=v := by
      obtain ⟨w,sw⟩ := card_eq_one.mp sing
      exact (mem_singleton.mp (sw ▸ hx)).trans (mem_singleton.mp (sw ▸ hv)).symm
    let T := q*v
    have tp : 0<T := Nat.mul_pos hq.pos (vp _ hv)
    have dxT (x) (hx:x∈A) : x∣T := by
      by_cases dx : q∣x
      · have udiv := (cross _ (mem_filter.mpr ⟨hx,dx⟩) _ hv).2.1
        have e := Nat.mul_dvd_mul_left q udiv
        rwa [Nat.mul_div_cancel' dx] at e
      · rw [only _ (mem_filter.mpr ⟨hx,dx⟩)]
        exact dvd_mul_left _ _
    have tinj : Set.InjOn (T/·) A := by
      intro x hx y hy e
      change T/x=T/y at e
      rw [←Nat.div_div_self (dxT _ hx) tp.ne',e,Nat.div_div_self (dxT _ hy) tp.ne']
    obtain ⟨z,hz,ez⟩ := one_in_image card (by omega) (T/·) tinj (by
      intro x hx
      refine mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd tp (dxT _ hx)) (pos _ hx),?_⟩
      by_cases dx : q∣x
      · have h := (cross _ (mem_filter.mpr ⟨hx,dx⟩) _ hv).2.2
        change q*v/x≤n
        conv_lhs => arg 2; rw [←Nat.mul_div_cancel' dx]
        simpa [Nat.mul_div_mul_left _ _ hq.pos] using h
      · change q*v/x≤n
        rw [only _ (mem_filter.mpr ⟨hx,dx⟩),Nat.mul_div_cancel _ (vp _ hv)]
        exact qle)
    have tz : T=z := by simpa [ez] using (Nat.div_mul_cancel (dxT _ hz)).symm
    have tm : T∈A := tz ▸ hz
    have e : A.lcm id=T := Nat.dvd_antisymm (lcm_dvd dxT) (dvd_lcm (f:=id) tm)
    exact e ▸ tm

/-- Graham’s full bound and equality classification follow from the single
rigidity assertion for primitive families with score at most their cardinality. -/
theorem solution_at_of_rigidity {n : ℕ} (hn : 5 ≤ n)
    (rigid : ∀ B : Finset ℕ, B.card = n → 0 ∉ B → B.gcd id = 1 →
      (∀ a ∈ B, ∀ b ∈ B, a / a.gcd b ≤ n) → 1 ∈ B ∨ B.lcm id ∈ B)
    (A : Finset ℕ) (hA : A.card = n) (hz : 0 ∉ A) :
    (n ≤ (A ×ˢ A).sup (fun p => p.1 / p.1.gcd p.2)) ∧
    (n = (A ×ˢ A).sup (fun p => p.1 / p.1.gcd p.2) ↔
      ∃ k > 0, A = (Icc 1 n).image (k * ·) ∨
        A = (Icc 1 n).image (k * (Icc 1 n).lcm id / ·)) := by
  classical
  have hnpos : 0 < n := by omega
  let score (F : Finset ℕ) := (F ×ˢ F).sup (fun p => p.1 / p.1.gcd p.2)
  let model := ∃ k > 0, A = (Icc 1 n).image (k * ·) ∨
    A = (Icc 1 n).image (k * (Icc 1 n).lcm id / ·)
  change n ≤ score A ∧ (n = score A ↔ model)
  have eq_of_model : model → n = score A := by
    rintro ⟨k, hk, hm | hm⟩
    · change n = (A ×ˢ A).sup _
      rw [hm, score_scale _ _ hk]
      exact (ordinary_score hnpos).symm
    · change n = (A ×ˢ A).sup _
      rw [hm]
      have nonzero : (Icc 1 n).lcm id ≠ 0 :=
        lcm_ne_zero_iff.mpr fun i hi => Nat.ne_of_gt (mem_Icc.mp hi).1
      exact (reciprocal_score hnpos (Nat.mul_pos hk (Nat.pos_of_ne_zero nonzero))
        (fun i hi => (Finset.dvd_lcm (f := id) hi).trans (dvd_mul_left _ _))).symm
  have model_of_le (h : score A ≤ n) : model := by
    obtain ⟨B, k, hk, ae, hB, bz, bg⟩ :=
      primitive (A := A) (card_pos.mp (by omega)) hz
    have card := hB.trans hA
    have scaled : score A = score B := ae ▸ score_scale B k hk
    have bound (a) (ha : a ∈ B) (b) (hb : b ∈ B) : a / a.gcd b ≤ n :=
      (Finset.le_sup (f := fun p : ℕ × ℕ => p.1 / p.1.gcd p.2)
        (b := (a,b)) (mem_product.mpr ⟨ha,hb⟩)).trans (scaled.symm.trans_le h)
    have ends := rigid B card bz bg bound
    rcases classify card bz bound ends with bm | ⟨t, ht, bm⟩
    · exact ⟨k, hk, Or.inl (by rw [ae, bm])⟩
    · refine ⟨k*t, Nat.mul_pos hk ht, Or.inr ?_⟩
      rw [ae, bm, image_image]
      apply image_congr
      intro i hi
      change k * (t*(Icc 1 n).lcm id / i) = k*t*(Icc 1 n).lcm id / i
      have dvd : i ∣ t*(Icc 1 n).lcm id :=
        (Finset.dvd_lcm (f := id) hi).trans (dvd_mul_left _ _)
      rw [Nat.mul_assoc, Nat.mul_div_assoc k dvd]
  refine ⟨?_, fun e => model_of_le e.ge, eq_of_model⟩
  by_contra! h
  exact h.ne (eq_of_model (model_of_le h.le)).symm

end Erdos402PrimeCardinality

open Filter in
theorem OMA.solution : type_of% @Erdos402.erdos_402.variants.szegedy_zaharescu_weak := by
  have estimates := Erdos402Log.eventual_large_ratio_or_large_prime
    (fun δ hδ => Erdos402Error.logarithmic_error PNTPort.MediumPNT 5 hδ)
  filter_upwards [estimates, eventually_ge_atTop 5] with n estimate hn
  intro A card positive
  apply Erdos402PrimeCardinality.solution_at_of_rigidity hn _ A card positive
  intro B hcard hz hgcd bound
  rcases estimate B hcard hz hgcd with ⟨a, ha, b, hb, h⟩ | ⟨q, hq, large, occurs⟩
  · exact False.elim ((not_lt_of_ge (bound a ha b hb)) (hcard ▸ h))
  · exact Erdos402PrimeCardinality.rigidity hcard hn
      (fun b hb => Nat.pos_of_ne_zero fun e => hz (e ▸ hb))
      hgcd bound hq (hcard ▸ large) occurs
