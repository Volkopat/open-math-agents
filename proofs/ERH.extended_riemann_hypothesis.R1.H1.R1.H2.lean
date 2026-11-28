import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H1_R1
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Hecke expansion and Poisson summation in arbitrary signature. Summing the reciprocal ideal-class averages identifies the normalized Mellin kernel at reciprocal scales. -/

namespace OMA.ThetaAux

open Complex Filter Set Asymptotics NumberField NumberField.Units NumberField.InfinitePlace
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone MeasureTheory HurwitzZeta Module Submodule
open scoped NumberField nonZeroDivisors Topology Classical

theorem norm_Gamma_le_real {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le, norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem gamma_shift_bound {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    |s.im| ^ n * ‖Gamma s‖ ≤ Real.Gamma (s.re + n) := by
  induction n generalizing s with
  | zero => simpa using norm_Gamma_le_real hs
  | succ n ih =>
    have hpos : 0 < (s + 1).re := by rw [add_re, one_re]; linarith
    have hstep : |s.im| * ‖Gamma s‖ ≤ ‖Gamma (s + 1)‖ := by
      rw [Gamma_add_one s (ne_zero_of_re_pos hs), norm_mul]
      exact mul_le_mul_of_nonneg_right (abs_im_le_norm s) (norm_nonneg _)
    calc |s.im| ^ (n + 1) * ‖Gamma s‖ = |s.im| ^ n * (|s.im| * ‖Gamma s‖) := by ring
         _ ≤ |s.im| ^ n * ‖Gamma (s + 1)‖ := by gcongr
         _ ≤ Real.Gamma ((s + 1).re + n) := by simpa using ih (s := s + 1) hpos
         _ = Real.Gamma (s.re + (n + 1 : ℕ)) := by push_cast; congr 1; simp; ring

theorem inverse_scaled (F : ℂ → ℂ) (σ : ℝ) {q x : ℝ} (hq : 0 < q) (hx : 0 < x) (c : ℂ) :
    mellinInv σ (fun s => c * ((q : ℂ) ^ (-s) * F s)) x = c * mellinInv σ F (q * x) := by
  let z (y : ℝ) : ℂ := σ + y * I
  have h (y : ℝ) : (x : ℂ) ^ (-z y) • (c * ((q : ℂ) ^ (-z y) * F (z y))) =
      c * ((↑(q * x) : ℂ) ^ (-z y) • F (z y)) := by
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hq.le hx.le]; simp only [smul_eq_mul]; ring
  unfold mellinInv
  change (1 / (2 * Real.pi) : ℝ) • (∫ y : ℝ, (x : ℂ) ^ (-z y) • (c * ((q : ℂ) ^ (-z y) * F (z y)))) = _
  simp_rw [h, integral_const_mul]
  simp [Algebra.smul_def, mul_left_comm, z]

variable (K : Type*) [Field K] [NumberField K]

theorem exists_grade (J : (Ideal (𝓞 K))⁰) (x : (idealLattice K (FractionalIdeal.mk0 K J))) :
    ∃ n : ℕ, mixedEmbedding.norm (x : mixedSpace K) = (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ) := by
  obtain ⟨y, hy, hyx⟩ := (mem_idealLattice K _).mp x.2
  change y ∈ ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) at hy
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hy
  obtain ⟨a, ha, rfl⟩ := hy
  obtain ⟨n, hn⟩ := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr ha)
  refine ⟨n, ?_⟩
  rw [← hyx, mixedEmbedding.norm_eq_norm, ← hn, Ideal.absNorm_span_singleton]
  change ((|Algebra.norm ℚ (a : K)| : ℚ) : ℝ) = _
  simp [← Algebra.coe_norm_int, Nat.cast_natAbs, Int.cast_abs]

end OMA.ThetaAux

namespace OMA.HeckeExpansion

namespace DedekindMellin

open Complex Filter Set NumberField NumberField.InfinitePlace MeasureTheory Asymptotics
open scoped NumberField Topology

noncomputable abbrev coeff (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

theorem coeff_mean (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (coeff K k : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum, coeff]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem summable (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coeff K n : ℂ)) s := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (coeff K n : ℝ))
    (r := 1) (isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using coeff_mean K))
    (fun n => Nat.cast_nonneg _) zero_le_one hs
  simpa only [ofReal_natCast] using h

def StripBound (a b : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc a b → ‖F s‖ ≤ C

def StripDecay (a b : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc a b → (1 + s.im ^ 2) * ‖F s‖ ≤ C

theorem StripDecay.bound {a b : ℝ} {F : ℂ → ℂ} (h : StripDecay a b F) : StripBound a b F := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun s hs => le_trans ?_ (h s hs)⟩
  nlinarith [mul_nonneg (sq_nonneg s.im) (norm_nonneg (F s))]

theorem StripBound.pow {a b : ℝ} {F : ℂ → ℂ} (h : StripBound a b F) (n : ℕ) :
    StripBound a b (fun s => F s ^ n) := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C ^ n, pow_nonneg hC _, fun s hs => (norm_pow _ _).le.trans (pow_le_pow_left₀ (norm_nonneg _) (h s hs) n)⟩

theorem StripDecay.mul_bound {a b : ℝ} {F G : ℂ → ℂ} (hF : StripDecay a b F) (hG : StripBound a b G) :
    StripDecay a b (fun s => F s * G s) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨C * D, mul_nonneg hC hD, fun s hs => ?_⟩
  dsimp only
  rw [norm_mul, ← mul_assoc]
  exact mul_le_mul (hF s hs) (hG s hs) (norm_nonneg _) hC

theorem StripDecay.pow_succ {a b : ℝ} {F : ℂ → ℂ} (hF : StripDecay a b F) (n : ℕ) :
    StripDecay a b (fun s => F s ^ (n + 1)) := by
  simpa only [pow_succ'] using hF.mul_bound (hF.bound.pow n)

theorem gamma_strip {a b : ℝ} (ha : 0 < a) : StripDecay a b Gamma := by
  let g (x : ℝ) := Real.Gamma x + Real.Gamma (x + 2)
  have hcont {x : ℝ} (hx : 0 < x) : ContinuousAt Real.Gamma x :=
    (Real.differentiableAt_Gamma (fun n => ne_of_gt (by have := Nat.cast_nonneg (α := ℝ) n; linarith : -(n : ℝ) < x))).continuousAt
  have hg : ContinuousOn g (Icc a b) := by
    intro x hx
    have hadd : ContinuousAt (fun y : ℝ => y + 2) x := by fun_prop
    have hshift : ContinuousAt (fun y : ℝ => Real.Gamma (y + 2)) x :=
      (hcont (x := x + 2) (by linarith [hx.1])).comp (f := fun y : ℝ => y + 2) hadd
    exact ((hcont (ha.trans_le hx.1)).fun_add hshift).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hg
  refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
  have h0 : 0 < s.re := ha.trans_le hs.1
  have h2 := OMA.ThetaAux.gamma_shift_bound h0 2
  simp only [Nat.cast_ofNat, sq_abs] at h2
  calc (1 + s.im ^ 2) * ‖Gamma s‖ ≤ g s.re := by dsimp [g]; linarith [OMA.ThetaAux.norm_Gamma_le_real h0]
       _ ≤ C := hC (mem_image_of_mem _ hs)
       _ ≤ _ := le_max_left _ _

theorem gammaR_strip {a b : ℝ} (ha : 0 < a) : StripDecay a b Gammaℝ := by
  obtain ⟨C, hC, h⟩ := gamma_strip (b := b / 2) (half_pos ha)
  refine ⟨4 * C, by positivity, fun s hs => ?_⟩
  have hhalf : (s / 2).re ∈ Icc (a / 2) (b / 2) := by
    simp only [Set.mem_Icc, div_ofNat_re]; constructor <;> linarith [hs.1, hs.2]
  have hx := h (s / 2) hhalf
  have hπ : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp; linarith [hs.1]
  have hG : ‖Gammaℝ s‖ ≤ ‖Gamma (s / 2)‖ := by
    rw [Gammaℝ_def, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hπ
  refine (mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ 1 + s.im ^ 2)).trans ?_
  simp only [div_ofNat_im] at hx
  nlinarith [norm_nonneg (Gamma (s / 2))]

theorem gammaC_strip {a b : ℝ} (ha : 0 < a) : StripDecay a b Gammaℂ := by
  have hR := gammaR_strip (b := b) ha
  obtain ⟨C, hC, h⟩ := (gammaR_strip (b := b + 1) (a := a + 1) (by linarith)).bound
  have hp : StripBound a b (fun s => Gammaℝ (s + 1)) :=
    ⟨C, hC, fun s hs => h (s + 1) (by simpa [Set.mem_Icc] using hs)⟩
  simpa only [Gammaℝ_mul_Gammaℝ_add_one] using hR.mul_bound hp

theorem StripDecay.vertical {F : ℂ → ℂ} {a b σ : ℝ} (h : StripDecay a b F) (hσ : σ ∈ Icc a b)
    (hcont : Continuous (fun y : ℝ => F (σ + y * I))) : VerticalIntegrable F σ := by
  obtain ⟨C, hC, h⟩ := h
  apply (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
  filter_upwards with y
  change ‖F (σ + y * I)‖ ≤ C * (1 + y ^ 2)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa [mul_comm] using h ((σ : ℂ) + y * I) (by simpa using hσ)

noncomputable def completion (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) * Gammaℝ s ^ nrRealPlaces K *
    Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s

noncomputable abbrev kernel (K : Type*) [Field K] [NumberField K] := mellinInv 2 (completion K)

end DedekindMellin

namespace DedekindIdealClasses

open Submodule Set NumberField NumberField.InfinitePlace NumberField.Units NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open scoped NumberField nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

abbrev ClassFiber (C : ClassGroup (𝓞 K)) (n : ℕ) :=
  {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧ ClassGroup.mk0 I = C}

theorem class_norm_to_principal {C : ClassGroup (𝓞 K)} (J : (Ideal (𝓞 K))⁰)
    (hJ : ClassGroup.mk0 J = C⁻¹) (n : ℕ) :
    Nat.card (ClassFiber K C n) = Nat.card {I : (Ideal (𝓞 K))⁰ //
      (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
      Ideal.absNorm (I : Ideal (𝓞 K)) = Ideal.absNorm (J : Ideal (𝓞 K)) * n} := by
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  apply Nat.card_congr
  refine ((Equiv.dvd J).subtypeEquiv (p := fun I : (Ideal (𝓞 K))⁰ => Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧ ClassGroup.mk0 I = C) ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ => J ∣ I) _)
  intro I
  rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
  simp only [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ, inv_mul_eq_one,
    Nat.mul_right_inj (Ideal.absNorm_pos_of_nonZeroDivisors J).ne']
  tauto

theorem class_count (C : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰) (hJ : ClassGroup.mk0 J = C⁻¹) (n : ℕ) :
    Nat.card (ClassFiber K C n) * torsionOrder K =
      Nat.card {x : idealSet K J // mixedEmbedding.norm (x : mixedSpace K) =
        (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ)} := by
  rw [class_norm_to_principal K J hJ n, torsionOrder, ← Nat.card_prod]
  exact Nat.card_congr (idealSetEquivNorm (K := K) (J := J) _).symm

theorem coeff_eq_sum_classes {n : ℕ} (hn : n ≠ 0) :
    DedekindMellin.coeff K n = ∑ C : ClassGroup (𝓞 K), Nat.card (ClassFiber K C n) := by
  classical
  let A := {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  let asNonzero (x : A) : (Ideal (𝓞 K))⁰ := ⟨x.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
    intro h; apply hn; rw [← x.2, h]; exact map_zero _)⟩
  let fieldClass (x : A) := ClassGroup.mk0 (asNonzero x)
  let e (C : ClassGroup (𝓞 K)) : {x : A // fieldClass x = C} ≃ ClassFiber K C n := {
    toFun := fun x => ⟨asNonzero x.1, x.1.2, x.2⟩
    invFun := fun I => ⟨⟨I.1.1, I.2.1⟩, I.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let : Finite A := (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  let (C : ClassGroup (𝓞 K)) : Finite (ClassFiber K C n) := Finite.of_equiv _ (e C)
  rw [← Nat.card_sigma]
  exact Nat.card_congr ((Equiv.sigmaFiberEquiv fieldClass).symm.trans (Equiv.sigmaCongrRight e))

end DedekindIdealClasses

namespace DedekindIdealPlane

open NumberField NumberField.mixedEmbedding
open scoped NumberField nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

noncomputable abbrev Lattice (J : (Ideal (𝓞 K))⁰) := idealLattice K (FractionalIdeal.mk0 K J)

end DedekindIdealPlane

namespace DedekindIdealSeries

open NumberField NumberField.mixedEmbedding DedekindIdealPlane
open scoped NumberField nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

noncomputable def grade (J : (Ideal (𝓞 K))⁰) (x : Lattice K J) : ℕ := (OMA.ThetaAux.exists_grade K J x).choose

theorem grade_eq_iff (J : (Ideal (𝓞 K))⁰) (x : Lattice K J) (n : ℕ) :
    grade K J x = n ↔ mixedEmbedding.norm (x : mixedSpace K) = (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ) := by
  rw [(OMA.ThetaAux.exists_grade K J x).choose_spec, Nat.cast_inj, Nat.mul_right_inj (Ideal.absNorm_pos_of_nonZeroDivisors J).ne']
  rfl

end DedekindIdealSeries

namespace DedekindRealMellin

open Complex Set MeasureTheory
open scoped Convolution

theorem hasMellin_log_iff (f : ℝ → ℂ) (s a : ℂ) : HasMellin f s a ↔
    Integrable (fun u : ℝ => exp (s * u) * f (Real.exp u)) ∧
      (∫ u : ℝ, exp (s * u) * f (Real.exp u)) = a := by
  have hr : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  have h (u : ℝ) : |Real.exp u| • (((Real.exp u : ℂ) ^ (s - 1)) • f (Real.exp u)) = exp (s * u) * f (Real.exp u) := by
    rw [abs_of_pos (Real.exp_pos _), Complex.real_smul, smul_eq_mul, ← mul_assoc,
      cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ← ofReal_log (Real.exp_pos _).le,
      Real.log_exp, ofReal_exp, ← Complex.exp_add]
    congr 2; ring
  unfold HasMellin MellinConvergent mellin
  rw [← hr, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn, integrableOn_univ, setIntegral_univ]
  simp only [h]

noncomputable def gauss (x : ℝ) : ℂ := Real.exp (-Real.pi * x ^ 2)

theorem gauss_mellin {s : ℂ} (hs : 0 < s.re) : HasMellin gauss s (Gammaℝ s / 2) := by
  have hcont : Continuous gauss := by unfold gauss; fun_prop
  constructor
  · unfold MellinConvergent
    rw [mellin_convergent_iff_norm (s := s) (Subset.rfl) measurableSet_Ioi hcont.aestronglyMeasurable]
    simp only [gauss, Complex.norm_of_nonneg (Real.exp_pos _).le]
    exact integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos (by linarith)
  · let g (t : ℝ) : ℂ := Real.exp (-t)
    have hsq : gauss = fun x : ℝ => g (Real.pi * x ^ (2 : ℝ)) := by
      funext x; simp [gauss, g]
    have hg := mellin_comp_rpow (fun t => g (Real.pi * t)) s 2
    rw [hsq, hg, mellin_comp_mul_left g _ Real.pi_pos]
    have hgamma : mellin g (s / 2) = Gamma (s / 2) := by
      rw [Gamma_eq_integral (by simpa using half_pos hs : 0 < (s / 2).re), GammaIntegral_eq_mellin]
    simp only [ofReal_ofNat, hgamma, Gammaℝ_def, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      Complex.real_smul, smul_eq_mul, ofReal_inv, neg_div]
    ring

end DedekindRealMellin

namespace DedekindArchimedeanProduct

open Complex Set MeasureTheory DedekindRealMellin
open scoped Convolution

noncomputable def convolution (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ v : ℝ, f (Real.exp v) * g (x / Real.exp v)

noncomputable def weight (s : ℂ) (f : ℝ → ℂ) (u : ℝ) := exp (s * u) * f (Real.exp u)

theorem weight_convolution (s : ℂ) (f g : ℝ → ℂ) (w : ℝ) :
    weight s (convolution f g) w = (weight s f ⋆[ContinuousLinearMap.mul ℝ ℂ] weight s g) w := by
  simp only [weight, convolution, ← integral_const_mul]
  change _ = ∫ v : ℝ, weight s f v * weight s g (w-v)
  apply integral_congr_ae
  filter_upwards with v
  simp only [weight, Real.exp_sub, ofReal_sub]
  rw [mul_mul_mul_comm, ← Complex.exp_add, show s * (v : ℂ) + s * ((w : ℂ) - v) = s * w by ring]

theorem hasMellin_convolution {f g : ℝ → ℂ} {s a b : ℂ} (hf : HasMellin f s a) (hg : HasMellin g s b) :
    HasMellin (convolution f g) s (a * b) := by
  let F (u : ℝ) := exp (s * u) * f (Real.exp u)
  let G (u : ℝ) := exp (s * u) * g (Real.exp u)
  obtain ⟨hiF, hF⟩ := (hasMellin_log_iff f s a).mp hf
  obtain ⟨hiG, hG⟩ := (hasMellin_log_iff g s b).mp hg
  have he (w : ℝ) : exp (s * w) * convolution f g (Real.exp w) = (F ⋆[ContinuousLinearMap.mul ℝ ℂ] G) w :=
    weight_convolution s f g w
  rw [hasMellin_log_iff]
  simp_rw [he]
  refine ⟨hiF.integrable_convolution (ContinuousLinearMap.mul ℝ ℂ) hiG, ?_⟩
  rw [integral_convolution _ hiF hiG]
  change (∫ u : ℝ, F u) * (∫ u : ℝ, G u) = a * b
  exact congrArg₂ (· * ·) hF hG

noncomputable def complexPlace (x : ℝ) : ℂ := Real.exp (-(2 * Real.pi * x))

theorem complexPlace_mellin {s : ℂ} (hs : 0 < s.re) : HasMellin complexPlace s (Gammaℂ s / 2) := by
  let g (x : ℝ) : ℂ := Real.exp (-x)
  have hI : MellinConvergent g s := by
    simpa only [MellinConvergent, g, smul_eq_mul, mul_comm] using (Complex.GammaIntegral_convergent hs)
  have hm : mellin g s = Gamma s := by rw [Gamma_eq_integral hs, GammaIntegral_eq_mellin]
  have hπ : 0 < 2 * Real.pi := by positivity
  change HasMellin (fun t => g ((2 * Real.pi) * t)) s _
  refine ⟨(MellinConvergent.comp_mul_left hπ).mpr hI, ?_⟩
  rw [mellin_comp_mul_left g s hπ, hm, Gammaℂ_def, smul_eq_mul, ofReal_mul, ofReal_ofNat]
  ring

inductive PlaceKind | real | complex

noncomputable def localGaussian : PlaceKind → ℝ → ℂ
  | .real => gauss
  | .complex => complexPlace

noncomputable def localGamma : PlaceKind → ℂ → ℂ
  | .real => Gammaℝ
  | .complex => Gammaℂ

noncomputable def product (first : PlaceKind) : List PlaceKind → ℝ → ℂ
  | [] => localGaussian first
  | k :: ks => convolution (localGaussian k) (product first ks)

theorem local_mellin (k : PlaceKind) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (localGaussian k) s (localGamma k s / 2) := by
  cases k with
  | real => exact gauss_mellin hs
  | complex => exact complexPlace_mellin hs

theorem product_mellin (first : PlaceKind) (ks : List PlaceKind) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (product first ks) s (((ks.map (fun k => localGamma k s / 2)).prod) * (localGamma first s / 2)) := by
  induction ks with
  | nil => simpa only [product, List.map_nil, List.prod_nil, one_mul] using local_mellin first hs
  | cons k ks ih => simpa only [product, List.map_cons, List.prod_cons, mul_assoc] using
      hasMellin_convolution (local_mellin k hs) ih

theorem local_weight_continuous (k : PlaceKind) : Continuous (weight 2 (localGaussian k)) := by
  cases k <;> unfold weight <;> simp only [localGaussian, gauss, complexPlace] <;> fun_prop

theorem local_weight_bounded (k : PlaceKind) : BddAbove (range fun u => ‖weight 2 (localGaussian k) u‖) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨u, rfl⟩
  have hπ : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  have he (x : ℝ) : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  cases k with
  | real =>
    simp only [weight, localGaussian, gauss, norm_mul, norm_exp, Complex.norm_of_nonneg (Real.exp_pos _).le,
      mul_re, re_ofNat, im_ofNat, ofReal_re, ofReal_im, zero_mul, sub_zero, ← Real.exp_add, Real.exp_le_one_iff]
    have hs : Real.exp u ^ 2 = Real.exp (2*u) := by rw [pow_two, ← Real.exp_add, two_mul]
    rw [hs]; nlinarith [he (2*u), mul_le_mul_of_nonneg_right hπ (Real.exp_pos (2*u)).le]
  | complex =>
    simp only [weight, localGaussian, complexPlace, norm_mul, norm_exp, Complex.norm_of_nonneg (Real.exp_pos _).le,
      mul_re, re_ofNat, im_ofNat, ofReal_re, ofReal_im, zero_mul, sub_zero, ← Real.exp_add, Real.exp_le_one_iff]
    nlinarith [he u, mul_le_mul_of_nonneg_right hπ (Real.exp_pos u).le]

theorem product_weight_continuous (first : PlaceKind) (ks : List PlaceKind) : Continuous (weight 2 (product first ks)) := by
  cases ks with
  | nil => exact local_weight_continuous first
  | cons k ks =>
    have hi := ((hasMellin_log_iff _ _ _).mp (product_mellin first ks (s := 2) (by norm_num))).1
    change Continuous (weight 2 (convolution (localGaussian k) (product first ks)))
    rw [funext (weight_convolution 2 _ _)]
    exact (local_weight_bounded k).continuous_convolution_left_of_integrable _ (local_weight_continuous k) hi

theorem product_continuousAt (first : PlaceKind) (ks : List PlaceKind) {x : ℝ} (hx : 0 < x) : ContinuousAt (product first ks) x := by
  let F := product first ks
  have he : F =ᶠ[nhds x] (fun t : ℝ => exp (-(2 * (Real.log t : ℂ))) * weight 2 F (Real.log t)) := by
    filter_upwards [lt_mem_nhds hx] with t ht
    simp only [weight, Real.exp_log ht, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  apply ContinuousAt.congr_of_eventuallyEq _ he
  have hc := Real.continuousAt_log hx.ne'
  exact (by fun_prop : ContinuousAt (fun t : ℝ => exp (-(2 * (Real.log t : ℂ)))) x).mul ((product_weight_continuous first ks).continuousAt.comp hc)

end DedekindArchimedeanProduct

namespace DedekindGeneralExpansion

open Complex Filter Set MeasureTheory NumberField NumberField.InfinitePlace DedekindMellin
open scoped NumberField Topology

noncomputable def arch (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K

theorem arch_continuous (K : Type*) [Field K] [NumberField K] : Continuous (fun y : ℝ => arch K ((2 : ℂ) + y * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  let z := (2 : ℂ) + y * I
  have hz : 0 < z.re := by simp [z]
  have hR {w : ℂ} (hw : 0 < w.re) : ContinuousAt Gammaℝ w := by
    simpa only [Pi.inv_def, inv_inv] using (differentiable_Gammaℝ_inv w).continuousAt.inv₀ (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hw))
  have hC : ContinuousAt Gammaℂ z := by
    have hshift : 0 < (z + 1).re := by norm_num [z]
    rw [show Gammaℂ = fun w => Gammaℝ w * Gammaℝ (w + 1) from funext fun w => (Gammaℝ_mul_Gammaℝ_add_one w).symm]
    exact (hR hz).mul ((hR hshift).comp (f := fun w : ℂ => w + 1) (by fun_prop))
  exact (((hR hz).pow _).mul (hC.pow _)).comp (f := fun y : ℝ => (2 : ℂ) + y * I) (by fun_prop)

theorem arch_vertical (K : Type*) [Field K] [NumberField K] : VerticalIntegrable (arch K) 2 := by
  have hR := gammaR_strip (a := 2) (b := 2) (by norm_num)
  have hG := gammaC_strip (a := 2) (b := 2) (by norm_num)
  have hplaces : 0 < nrRealPlaces K + nrComplexPlaces K := by
    rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]; exact Fintype.card_pos
  have harch : StripDecay 2 2 (arch K) := by
    unfold arch
    cases hr : nrRealPlaces K with
    | succ n => exact (hR.pow_succ n).mul_bound (hG.bound.pow _)
    | zero =>
      cases hc : nrComplexPlaces K with
      | zero => simp [hr, hc] at hplaces
      | succ n => simpa using hG.pow_succ n
  exact harch.vertical ⟨le_rfl, le_rfl⟩ (arch_continuous K)

theorem inverse_dirichlet (K : Type*) [Field K] [NumberField K] (A : ℂ → ℂ)
    (hA : VerticalIntegrable A 2) (hcont : Continuous (fun y : ℝ => A ((2 : ℂ) + y * I)))
    {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s => A s * dedekindZeta K s) x =
      ∑' n : ℕ, if n = 0 then 0 else (coeff K n : ℂ) * mellinInv 2 A (x * n) := by
  let z (y : ℝ) : ℂ := 2 + y * I
  let a (n : ℕ) : ℂ := coeff K n
  let G (n : ℕ) (y : ℝ) := (x : ℂ) ^ (-(z y)) * A (z y) * LSeries.term a (z y) n
  let w (n : ℕ) := ‖LSeries.term a 2 n‖
  have hw (n : ℕ) (y : ℝ) : ‖G n y‖ = (x ^ (-(2 : ℝ)) * w n) * ‖A (z y)‖ := by
    simp only [G, w, norm_mul, LSeries.norm_term_eq, norm_cpow_eq_rpow_re_of_pos hx, neg_re]
    simp [z, mul_right_comm]
  have hG (n : ℕ) : Integrable (G n) := by
    apply (hA.norm.const_mul (x ^ (-(2 : ℝ)) * w n)).mono'
    · by_cases hn : n = 0
      · subst n; simpa [G, LSeries.term] using (aestronglyMeasurable_const (b := (0 : ℂ)) (μ := (volume : Measure ℝ)))
      · have hz : Continuous z := by dsimp [z]; fun_prop
        have hp : Continuous (fun y : ℝ => (x : ℂ) ^ (-z y)) := hz.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
        have hg : Continuous (fun y : ℝ => A (z y)) := hcont
        have ht : Continuous (fun y => LSeries.term a (z y) n) := by
          simp only [LSeries.term_of_ne_zero hn]
          have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
          exact continuous_const.div₀ (hz.const_cpow (Or.inl hn')) (fun y => cpow_ne_zero_iff.mpr (Or.inl hn'))
        exact ((hp.fun_mul hg).fun_mul ht).aestronglyMeasurable
    · exact Eventually.of_forall fun y => (hw n y).le
  have hsum : Summable fun n => ∫ y : ℝ, ‖G n y‖ := by
    simp_rw [hw, integral_const_mul, mul_assoc]
    exact (((DedekindMellin.summable K (s := 2) (by norm_num)).norm.mul_right _).mul_left _)
  have hex (y : ℝ) : (x : ℂ) ^ (-z y) • (A (z y) * dedekindZeta K (z y)) = ∑' n, G n y := by
    simp only [G, dedekindZeta, LSeries, ← tsum_mul_left, smul_eq_mul, mul_assoc, a, coeff]
  unfold mellinInv
  change (1 / (2 * Real.pi) : ℝ) • (∫ y : ℝ, (x : ℂ) ^ (-z y) • (A (z y) * dedekindZeta K (z y))) = _
  simp_rw [hex]
  rw [← integral_tsum_of_summable_integral_norm hG hsum, ← tsum_const_smul'']
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n; simp [G, LSeries.term]
  · rw [if_neg hn]
    have hterm (y : ℝ) : G n y = a n * ((↑(x * n) : ℂ) ^ (-z y) • A (z y)) := by
      dsimp only [G]
      rw [LSeries.term_of_ne_zero hn, ofReal_mul, mul_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg _), ofReal_natCast]
      simp only [cpow_neg, smul_eq_mul, div_eq_mul_inv]
      ring
    simp_rw [hterm, integral_const_mul]
    simp [z, a, Algebra.smul_def, mul_left_comm, mul_assoc]

theorem kernel_series (K : Type*) [Field K] [NumberField K] {x : ℝ} (hx : 0 < x) :
    let q := (Real.sqrt ((discr K).natAbs : ℝ))⁻¹
    kernel K x = ∑' n : ℕ, if n = 0 then 0 else (coeff K n : ℂ) * mellinInv 2 (arch K) (q * x * n) := by
  let d := Real.sqrt ((discr K).natAbs : ℝ)
  let q := d⁻¹
  have hd₀ : 0 < ((discr K).natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)
  have hd : 0 < d := Real.sqrt_pos.mpr hd₀
  have hq : 0 < q := inv_pos.mpr hd
  have hc (s : ℂ) : exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) = (q : ℂ) ^ (-s) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hq.ne'), ← ofReal_log hq.le]
    dsimp only [q, d]
    rw [Real.log_inv, Real.log_sqrt hd₀.le, ofReal_neg]; congr 1; ring
  have hcomp : completion K = fun s => 1 * ((q : ℂ) ^ (-s) * (arch K s * dedekindZeta K s)) := by
    funext s; simp only [completion, hc, arch, one_mul, mul_assoc]
  dsimp only
  rw [kernel, hcomp, OMA.ThetaAux.inverse_scaled _ _ hq hx _, one_mul,
    inverse_dirichlet K (arch K) (arch_vertical K) (arch_continuous K) (mul_pos hq hx)]

end DedekindGeneralExpansion

namespace DedekindSignatureKernel

open Complex NumberField NumberField.InfinitePlace DedekindArchimedeanProduct DedekindGeneralExpansion DedekindMellin
open scoped NumberField

noncomputable def profile : ℕ → ℕ → ℝ → ℂ
  | r+1, c => product .real (List.replicate r .real ++ List.replicate c .complex)
  | 0, c+1 => product .complex (List.replicate c .complex)
  | 0, 0 => 0

theorem profile_mellin (r c : ℕ) (h : 0 < r + c) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (profile r c) s ((Gammaℝ s / 2) ^ r * (Gammaℂ s / 2) ^ c) := by
  cases r with
  | succ r =>
    have hm := product_mellin .real (List.replicate r .real ++ List.replicate c .complex) hs
    simpa only [profile, List.map_append, List.map_replicate, List.prod_append, List.prod_replicate, localGamma,
      pow_succ, mul_right_comm] using hm
  | zero =>
    cases c with
    | zero => omega
    | succ c => simpa only [profile, List.map_replicate, List.prod_replicate, localGamma, pow_zero, one_mul, pow_succ] using
        product_mellin .complex (List.replicate c .complex) hs

theorem profile_continuousAt (r c : ℕ) {x : ℝ} (hx : 0 < x) : ContinuousAt (profile r c) x := by
  cases r with
  | succ r => exact product_continuousAt _ _ hx
  | zero => cases c with
    | zero => exact continuousAt_const
    | succ c => exact product_continuousAt _ _ hx

variable (K : Type*) [Field K] [NumberField K]

theorem inverse_arch {x : ℝ} (hx : 0 < x) : mellinInv 2 (arch K) x =
    (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K) * profile (nrRealPlaces K) (nrComplexPlaces K) x := by
  let r := nrRealPlaces K
  let c := nrComplexPlaces K
  let F (x : ℝ) := (2 : ℂ) ^ (r + c) * profile r c x
  have hp : 0 < r + c := by dsimp only [r, c]; rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]; exact Fintype.card_pos
  have hm {s : ℂ} (hs : 0 < s.re) : HasMellin F s (arch K s) := by
    have h := profile_mellin r c hp hs
    have he := hasMellin_const_smul h.1 ((2 : ℂ) ^ (r+c))
    have hg : (2 : ℂ) ^ (r+c) * ((Gammaℝ s / 2) ^ r * (Gammaℂ s / 2) ^ c) = arch K s := by
      change _ = Gammaℝ s ^ r * Gammaℂ s ^ c
      rw [pow_add, div_pow, div_pow]; field_simp
    rw [h.2, smul_eq_mul, hg] at he
    exact he
  have heq (y : ℝ) : mellin F ((2 : ℂ) + y * I) = arch K (2 + y * I) := (hm (by simp)).2
  have hV : VerticalIntegrable (mellin F) 2 := by
    change MeasureTheory.Integrable (fun y : ℝ => mellin F ((2 : ℂ) + y * I))
    simpa only [VerticalIntegrable, ofReal_ofNat, heq] using arch_vertical K
  have hfc : ContinuousAt F x := continuousAt_const.mul (profile_continuousAt r c hx)
  change mellinInv 2 (arch K) x = F x
  rw [← mellinInv_mellin_eq 2 F hx (hm (s := 2) (by norm_num)).1 hV hfc]
  unfold mellinInv
  simp only [ofReal_ofNat, heq]

theorem explicit_kernel {x : ℝ} (hx : 0 < x) :
    let q := (Real.sqrt ((discr K).natAbs : ℝ))⁻¹
    let r := nrRealPlaces K
    let c := nrComplexPlaces K
    kernel K x = (2 : ℂ) ^ (r+c) * ∑' n : ℕ, if n = 0 then 0 else
      (coeff K n : ℂ) * profile r c (q * x * n) := by
  dsimp only
  rw [kernel_series K hx, ← tsum_mul_left]
  apply tsum_congr
  intro n
  split_ifs with hn
  · simp
  · have hd : 0 < Real.sqrt ((discr K).natAbs : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K))
    rw [inverse_arch K (mul_pos (mul_pos (inv_pos.mpr hd) hx) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))]
    ring

end DedekindSignatureKernel

namespace DedekindRealUnits

open NumberField NumberField.Units NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone DedekindIdealPlane
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

theorem unit_lattice {J : (Ideal (𝓞 K))⁰} (u : (𝓞 K)ˣ) {x : mixedSpace K} (hx : x ∈ Lattice K J) :
    u • x ∈ Lattice K J := by
  obtain ⟨y, hy, rfl⟩ := (mem_idealLattice K _).mp hx
  apply (mem_idealLattice K _).mpr
  let I := ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
  refine ⟨(u : 𝓞 K) • y, (I : Submodule (𝓞 K) K).smul_mem (u : 𝓞 K) hy, ?_⟩
  change mixedEmbedding K ((u : K) * y) = _
  rw [unitSMul_smul, map_mul]

end DedekindRealUnits

namespace DedekindUnitVectors

open NumberField NumberField.Units NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone DedekindIdealPlane
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev Exponents := Fin (rank K) → ℤ

noncomputable def unit (k : Exponents K) : (𝓞 K)ˣ := ∏ i, fundSystem K i ^ k i

theorem unit_zero : unit K 0 = 1 := by simp [unit]

theorem unit_neg (k : Exponents K) : unit K (-k) = (unit K k)⁻¹ := by
  simp [unit, Pi.neg_apply, zpow_neg]

theorem unit_sub (k l : Exponents K) : unit K (k-l) = unit K k * (unit K l)⁻¹ := by
  simp only [unit, Pi.sub_apply, zpow_sub, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

theorem unit_mem_torsion {k : Exponents K} (hk : unit K k ∈ torsion K) : k = 0 := by
  have h := fun_eq_repr (K := K) (x := unit K k) (ζ := 1) (f := k) (one_mem _) (by rw [one_mul]; rfl)
  have h0 := fun_eq_repr (K := K) (x := unit K k) (f := 0) hk (by simp)
  exact h.trans h0.symm

noncomputable def orbitEquiv (J : (Ideal (𝓞 K))⁰) :
    Exponents K × idealSet K J ≃ {x : Lattice K J // x ≠ 0} := by
  let F (p : Exponents K × idealSet K J) : {x : Lattice K J // x ≠ 0} :=
    ⟨⟨unit K p.1 • p.2.val, DedekindRealUnits.unit_lattice K _ p.2.prop.2⟩, by
      intro h
      have hh := congrArg (fun z : Lattice K J => (z : mixedSpace K)) h
      have hz := (unit_smul_eq_zero (unit K p.1) p.2.val).mp hh
      exact (norm_pos_of_mem p.2.prop.1).ne' (hz ▸ map_zero _)⟩
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · rintro ⟨k, a⟩ ⟨l, b⟩ h
    have he : unit K k • a.val = unit K l • b.val := congrArg (fun z : {x : Lattice K J // x ≠ 0} => z.1.val) h
    have hd : unit K (k-l) • a.val = b.val := by rw [unit_sub, mul_comm, mul_smul, he, inv_smul_smul]
    have ht := (unit_smul_mem_iff_mem_torsion a.prop.1 _).mp (hd ▸ b.prop.1)
    have hkl : k = l := sub_eq_zero.mp (unit_mem_torsion K ht)
    subst l
    exact Prod.ext rfl (Subtype.ext (by simpa [unit_zero] using hd))
  · intro x
    obtain ⟨y, _, hy⟩ := (mem_idealLattice K _).mp x.1.prop
    have hn : mixedEmbedding.norm x.1.val ≠ 0 := (mixedEmbedding.norm_eq_zero_iff' ⟨y, hy⟩).not.mpr
      (fun h => x.prop (Subtype.ext h))
    obtain ⟨v, hv⟩ := exists_unit_smul_mem hn
    obtain ⟨⟨ζ, k⟩, hk, _⟩ := exist_unique_eq_mul_prod K v
    change v = (ζ : (𝓞 K)ˣ) * unit K k at hk
    let b := unit K k • x.1.val
    have hb : b ∈ fundamentalCone K := by
      have h := torsion_smul_mem_of_mem hv ((torsion K).inv_mem ζ.prop)
      simpa only [hk, mul_smul, inv_smul_smul, b] using h
    refine ⟨⟨-k, ⟨b, hb, DedekindRealUnits.unit_lattice K _ x.1.prop⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change unit K (-k) • (unit K k • x.1.val) = x.1.val
    rw [unit_neg, inv_smul_smul]

theorem orbitEquiv_apply (J : (Ideal (𝓞 K))⁰) (p : Exponents K × idealSet K J) :
    ((orbitEquiv K J p).val : mixedSpace K) = unit K p.1 • p.2.val := rfl

end DedekindUnitVectors

namespace DedekindUnitDomain

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
open MeasureTheory Module DedekindUnitVectors Additive
open scoped NumberField Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable def domain : Set (logSpace K) := ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ _)

theorem fundamental : IsAddFundamentalDomain (unitLattice K) (domain K) volume :=
  ZLattice.isAddFundamentalDomain (basisUnitLattice K) volume

theorem volume_domain : volume.real (domain K) = regulator K :=
  (ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamental K)).symm

noncomputable def latticeEquiv : Exponents K ≃ unitLattice K := (basisUnitLattice K).equivFun.toEquiv.symm

theorem log_unit (k : Exponents K) : logEmbedding K (ofMul (unit K k)) = (latticeEquiv K k : logSpace K) := by
  change logEmbedding K (ofMul (∏ i, fundSystem K i ^ k i)) = ↑((basisUnitLattice K).equivFun.symm k)
  simp only [ofMul_prod, ofMul_zpow, map_sum, map_zsmul, logEmbedding_fundSystem,
    Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower]

theorem unfold_units (f : logSpace K → ℂ) (hf : Integrable f) :
    (∫ y : logSpace K, f y) = ∑' k : Exponents K, ∫ y in domain K, f (y + logEmbedding K (ofMul (unit K k))) := by
  let : MeasurableVAdd (unitLattice K) (logSpace K) := (inferInstance : MeasurableVAdd (unitLattice K).toAddSubgroup (logSpace K))
  let : VAddInvariantMeasure (unitLattice K) (logSpace K) volume := (inferInstance : VAddInvariantMeasure (unitLattice K).toAddSubgroup (logSpace K) volume)
  rw [(fundamental K).integral_eq_tsum'' f hf, ← (latticeEquiv K).tsum_eq]
  apply tsum_congr
  intro k
  rw [log_unit]
  apply setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _)
  intro y _
  exact congrArg f (add_comm _ _)

noncomputable def fullCoordinate (y : logSpace K) (w : InfinitePlace K) : ℝ :=
  if h : w = w₀ then -∑ v, y v else y ⟨w, h⟩

theorem full_sum (y : logSpace K) : ∑ w, fullCoordinate K y w = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
  have he (w : {w : InfinitePlace K // w ≠ w₀}) : fullCoordinate K y w.val = y w := by simp only [fullCoordinate, dif_neg w.prop]
  have hb : fullCoordinate K y w₀ = -∑ v, y v := dif_pos rfl
  rw [hb, Finset.sum_congr rfl (fun i _ => he i), neg_add_cancel]

theorem full_log_unit (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    fullCoordinate K (logEmbedding K (ofMul u)) w = (mult w : ℝ) * Real.log (w (u : K)) := by
  by_cases hw : w = w₀
  · subst w
    rw [fullCoordinate, dif_pos rfl, sum_logEmbedding_component, neg_mul, neg_neg]
  · simp [fullCoordinate, hw, logEmbedding_component]

end DedekindUnitDomain

namespace DedekindUnitGaussian

open NumberField NumberField.Units NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding DedekindUnitDomain DedekindUnitVectors MeasureTheory Additive
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable def dilation (y : logSpace K) (w : InfinitePlace K) : ℝ := Real.exp (fullCoordinate K y w / mult w)

theorem add_coord (y z : logSpace K) (w : InfinitePlace K) : fullCoordinate K (y+z) w = fullCoordinate K y w + fullCoordinate K z w := by
  by_cases h : w = w₀ <;> simp [fullCoordinate, h, Finset.sum_add_distrib, add_comm]

theorem determinant (y : logSpace K) : ∏ w, (dilation K y w) ^ mult w = 1 := by
  have he (w : InfinitePlace K) : (dilation K y w) ^ mult w = Real.exp (fullCoordinate K y w) := by
    rw [dilation, ← Real.exp_nat_mul]; congr 1; field_simp [mult_coe_ne_zero]
  simp_rw [he, ← Real.exp_sum, full_sum, Real.exp_zero]

theorem dilation_unit (u : (𝓞 K)ˣ) (y : logSpace K) (w : InfinitePlace K) :
    dilation K (y + logEmbedding K (ofMul u)) w = dilation K y w * w (u : K) := by
  rw [dilation, add_coord, add_div, Real.exp_add, full_log_unit,
    mul_div_cancel_left₀ _ mult_coe_ne_zero, Real.exp_log (pos_at_place u w)]
  rfl

noncomputable def gaussian (t : ℝ) (a : mixedSpace K) (y : logSpace K) : ℂ :=
  Real.exp (-(Real.pi * t) * ∑ w : InfinitePlace K, (mult w : ℝ) * (dilation K y w * normAtPlace w a) ^ 2)

theorem gaussian_unit (u : (𝓞 K)ˣ) (a : mixedSpace K) (t : ℝ) (y : logSpace K) :
    gaussian K t (u • a) y = gaussian K t a (y + logEmbedding K (ofMul u)) := by
  simp only [gaussian, dilation_unit, unitSMul_smul, map_mul, normAtPlace_apply, mul_assoc]

theorem unfold_gaussian (a : mixedSpace K) (t : ℝ) (hI : Integrable (gaussian K t a)) :
    (∑' k : Exponents K, ∫ y in domain K, gaussian K t (unit K k • a) y) = ∫ y, gaussian K t a y := by
  rw [unfold_units K _ hI]; simp_rw [gaussian_unit]

end DedekindUnitGaussian

namespace DedekindRadialOrbit

open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding
open DedekindUnitDomain DedekindUnitGaussian MeasureTheory
open scoped NumberField Classical

variable (K : Type*) [Field K] [NumberField K]

theorem complete_zero_sum (b : InfinitePlace K → ℝ) (hb : ∑ w, b w = 0) (w : InfinitePlace K) :
    fullCoordinate K (fun v => b v.val) w = b w := by
  by_cases hw : w = w₀
  · subst w
    rw [fullCoordinate, dif_pos rfl]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hb
    linarith
  · simp only [fullCoordinate, dif_neg hw]

noncomputable def radius (a : mixedSpace K) : ℝ := Real.exp (Real.log (mixedEmbedding.norm a) / Module.finrank ℚ K)

theorem abs_decompose (a : mixedSpace K) (ha : mixedEmbedding.norm a ≠ 0) (w : InfinitePlace K) :
    normAtPlace w a = radius K a * dilation K (logMap a) w := by
  let n : ℝ := Module.finrank ℚ K
  let L := Real.log (mixedEmbedding.norm a)
  let b (v : InfinitePlace K) := (mult v : ℝ) * (Real.log (normAtPlace v a) - L / n)
  have hn : n ≠ 0 := by dsimp only [n]; exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hmul : ∑ v : InfinitePlace K, (mult v : ℝ) = n := by dsimp only [n]; exact_mod_cast (sum_mult_eq (K := K))
  have hlog : ∑ v : InfinitePlace K, (mult v : ℝ) * Real.log (normAtPlace v a) = L := by
    simp only [L, mixedEmbedding.norm_apply, Real.log_prod (fun i _ => pow_ne_zero _ (mixedEmbedding.norm_ne_zero_iff.mp ha i)), Real.log_pow]
  have hb : ∑ v, b v = 0 := by
    simp only [b, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hlog, hmul]
    field_simp; ring
  have he : logMap a = fun v => b v.val := by ext v; simp only [logMap_apply, b, L, n, div_eq_mul_inv]
  rw [radius, dilation, he, complete_zero_sum K b hb, ← Real.exp_add]
  change normAtPlace w a = Real.exp (L/n + ((mult w : ℝ) * (Real.log (normAtPlace w a) - L/n)) / mult w)
  rw [mul_div_cancel_left₀ _ mult_coe_ne_zero, add_sub_cancel, Real.exp_log]
  exact lt_of_le_of_ne (normAtPlace_nonneg w a) (mixedEmbedding.norm_ne_zero_iff.mp ha w).symm

theorem radial_gaussian (a : mixedSpace K) (ha : mixedEmbedding.norm a ≠ 0) (t : ℝ) (y : logSpace K) :
    gaussian K t a y = gaussian K (t * radius K a ^ 2) 1 (y + logMap a) := by
  have hd (w : InfinitePlace K) : dilation K (y + logMap a) w = dilation K y w * dilation K (logMap a) w := by
    rw [dilation, add_coord, add_div, Real.exp_add]; rfl
  have he (w : InfinitePlace K) : (mult w : ℝ) * (dilation K y w * normAtPlace w a) ^ 2 =
      (radius K a)^2 * ((mult w : ℝ) * (dilation K (y+logMap a) w)^2) := by
    rw [abs_decompose K a ha w, hd]; ring
  simp only [gaussian, he, ← Finset.mul_sum, map_one, mul_one]
  congr 2; ring

theorem orbit_integral (a : mixedSpace K) (ha : mixedEmbedding.norm a ≠ 0) (t : ℝ) :
    (∫ y, gaussian K t a y) = ∫ y, gaussian K (t * radius K a ^ 2) 1 y := by
  simp_rw [radial_gaussian K a ha t]
  exact integral_add_right_eq_self _ _

end DedekindRadialOrbit

namespace DedekindOrbitIntegrable

open Set NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding
open DedekindUnitDomain DedekindUnitGaussian DedekindRadialOrbit DedekindUnitVectors MeasureTheory
open scoped NumberField Classical

theorem integrable_abs_exp {b : ℝ} (hb : 0 < b) : Integrable (fun x : ℝ => Real.exp (-b * |x|)) := by
  rw [← integrableOn_univ, ← (Iic_union_Ioi (a := (0 : ℝ))), integrableOn_union]
  constructor
  · apply (integrableOn_exp_mul_Iic hb 0).congr_fun _ measurableSet_Iic
    intro x hx; simp [abs_of_nonpos (mem_Iic.mp hx)]
  · apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 0).congr_fun _ measurableSet_Ioi
    intro x hx; simp [abs_of_pos (mem_Ioi.mp hx)]

variable (K : Type*) [Field K] [NumberField K]

theorem coordinate_bound (y : logSpace K) :
    ∑ v, |y v| ≤ ∑ w : InfinitePlace K, (mult w : ℝ) * (dilation K y w) ^ 2 := by
  let z := fullCoordinate K y
  have hc (w : InfinitePlace K) : |z w| + z w ≤ (mult w : ℝ) * (dilation K y w) ^ 2 := by
    rcases le_total 0 (z w) with hp | hn
    · rw [abs_of_nonneg hp]
      let m : ℝ := mult w
      have hm : m ≠ 0 := mult_coe_ne_zero
      have he : 2 * (z w / m) ≤ Real.exp (2 * (z w / m)) := by linarith [Real.add_one_le_exp (2 * (z w / m))]
      have hp' := mul_le_mul_of_nonneg_left he (show 0 ≤ m from Nat.cast_nonneg _)
      change z w + z w ≤ m * (Real.exp (z w / m)) ^ 2
      rw [pow_two, ← Real.exp_add, show z w / m + z w / m = 2 * (z w / m) by ring]
      exact (show z w + z w = m * (2 * (z w / m)) by field_simp; ring).le.trans hp'
    · rw [abs_of_nonpos hn, neg_add_cancel]; positivity
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hc w)
  rw [Finset.sum_add_distrib, show ∑ w, z w = 0 from full_sum K y, add_zero] at hs
  apply le_trans _ hs
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun w => |z w|) w₀]
  have he (v : {w : InfinitePlace K // w ≠ w₀}) : |z v.val| = |y v| := by simp only [z, fullCoordinate, dif_neg v.prop]
  rw [Finset.sum_congr rfl (fun v _ => he v)]
  exact le_add_of_nonneg_left (abs_nonneg _)

theorem continuous_coordinate (w : InfinitePlace K) : Continuous (fun y : logSpace K => fullCoordinate K y w) := by
  by_cases h : w = w₀
  · simp only [fullCoordinate, dif_pos h]
    exact (continuous_finsetSum _ (fun i _ => continuous_apply i)).neg
  · simp only [fullCoordinate, dif_neg h]
    exact continuous_apply _

theorem continuous_gaussian (t : ℝ) (a : mixedSpace K) : Continuous (gaussian K t a) := by
  have hd (w : InfinitePlace K) : Continuous (fun y : logSpace K => dilation K y w) :=
    ((continuous_coordinate K w).div_const _).rexp
  apply Complex.continuous_ofReal.comp
  apply Real.continuous_exp.comp
  apply continuous_const.mul
  exact continuous_finsetSum _ (fun w _ => continuous_const.mul (((hd w).mul continuous_const).pow 2))

theorem integrable_one {t : ℝ} (ht : 0 < t) : Integrable (gaussian K t 1) := by
  let b := Real.pi * t
  have hb : 0 < b := mul_pos Real.pi_pos ht
  have hdom : Integrable (fun y : logSpace K => ∏ v, Real.exp (-b * |y v|)) :=
    Integrable.fintype_prod (μ := fun _ : {w : InfinitePlace K // w ≠ w₀} => (volume : Measure ℝ))
      (f := fun _ v => Real.exp (-b * |v|)) (fun _ => integrable_abs_exp hb)
  apply hdom.mono' (continuous_gaussian K t 1).aestronglyMeasurable
  filter_upwards with y
  simp only [gaussian, map_one, mul_one, Complex.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_sum, ← Finset.mul_sum, Real.exp_le_exp]
  exact mul_le_mul_of_nonpos_left (coordinate_bound K y) (neg_nonpos.mpr hb.le)

theorem integrable_orbit {a : mixedSpace K} (ha : mixedEmbedding.norm a ≠ 0) {t : ℝ} (ht : 0 < t) :
    Integrable (gaussian K t a) := by
  have hr : 0 < radius K a := Real.exp_pos _
  have h := (integrable_one K (mul_pos ht (sq_pos_of_pos hr))).comp_add_right (logMap a)
  exact h.congr (.of_forall (fun y => (radial_gaussian K a ha t y).symm))

theorem complete_orbit {a : mixedSpace K} (ha : mixedEmbedding.norm a ≠ 0) {t : ℝ} (ht : 0 < t) :
    (∑' k : Exponents K, ∫ y in domain K, gaussian K t (unit K k • a) y) =
      ∫ y, gaussian K (t * radius K a ^ 2) 1 y :=
  (unfold_gaussian K a t (integrable_orbit K ha ht)).trans (orbit_integral K a ha t)

end DedekindOrbitIntegrable

namespace DedekindHyperplaneMellin

open Complex Set MeasureTheory DedekindRealMellin DedekindArchimedeanProduct
open scoped Classical Topology

variable {ι : Type*} [Fintype ι]

noncomputable def slice (k₀ : PlaceKind) (k : ι → PlaceKind) (x : ℝ) : ℂ :=
  ∫ y : ι → ℝ, localGaussian k₀ (Real.exp (Real.log x - ∑ i, y i)) *
    ∏ i, localGaussian (k i) (Real.exp (y i))

private theorem contWeight (s : ℂ) (k : PlaceKind) : Continuous (weight s (localGaussian k)) := by
  cases k <;> unfold weight <;> simp only [localGaussian, gauss, complexPlace] <;> fun_prop

private theorem wt_slice (k₀ : PlaceKind) (k : ι → PlaceKind) (s : ℂ) (v : ℝ) :
    weight s (slice k₀ k) v = ∫ y : ι → ℝ, weight s (localGaussian k₀) (v - ∑ i, y i) *
      ∏ i, weight s (localGaussian (k i)) (y i) := by
  simp only [weight, slice, Real.log_exp, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, mul_mul_mul_comm, ← Complex.exp_add]
  simp only [← Finset.mul_sum, ofReal_sub, ofReal_sum]
  rw [← mul_add, sub_add_cancel]

theorem slice_mellin (k₀ : PlaceKind) (k : ι → PlaceKind) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (slice k₀ k) s ((localGamma k₀ s / 2) * ∏ i, (localGamma (k i) s / 2)) := by
  let F := weight s (localGaussian k₀)
  let G (y : ι → ℝ) := ∏ i, weight s (localGaussian (k i)) (y i)
  let H (v : ℝ) (y : ι → ℝ) := F (v - ∑ i, y i) * G y
  have hF := (hasMellin_log_iff _ _ _).mp (local_mellin k₀ hs)
  have hG (i : ι) := (hasMellin_log_iff _ _ _).mp (local_mellin (k i) hs)
  have hiF : Integrable F := hF.1
  have hiG : Integrable G := Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℝ))
    (f := fun i => weight s (localGaussian (k i))) (fun i => (hG i).1)
  have hcG : Continuous G := continuous_finsetProd _ (fun i _ => (contWeight s (k i)).comp (continuous_apply i))
  have hcont : Continuous (Function.uncurry H) :=
    ((contWeight s k₀).comp (continuous_fst.sub (continuous_finsetSum _ (fun i _ => (continuous_apply i).comp continuous_snd)))).mul (hcG.comp continuous_snd)
  have hi : Integrable (Function.uncurry H) (volume.prod volume) := by
    apply (integrable_prod_iff' hcont.aestronglyMeasurable).mpr
    constructor
    · exact .of_forall fun y => by simpa only [H, Function.uncurry_apply_pair, sub_eq_add_neg] using
        (hiF.comp_add_right (-∑ i, y i)).mul_const (G y)
    · change Integrable (fun y => ∫ v : ℝ, ‖F (v - ∑ i, y i) * G y‖)
      have ht (y : ι → ℝ) : (∫ v : ℝ, ‖F (v - ∑ i, y i)‖) = ∫ v, ‖F v‖ :=
        integral_add_right_eq_self (fun v => ‖F v‖) (-∑ i, y i)
      simp only [norm_mul, integral_mul_const, ht]
      exact hiG.norm.const_mul _
  rw [hasMellin_log_iff]
  change Integrable (weight s (slice k₀ k)) ∧ (∫ v, weight s (slice k₀ k) v) = _
  simp_rw [funext (wt_slice k₀ k s)]
  refine ⟨hi.integral_prod_left, ?_⟩
  change (∫ v, ∫ y, H v y) = _
  rw [integral_integral_swap hi]
  simp only [H, integral_mul_const, sub_eq_add_neg, integral_add_right_eq_self, integral_const_mul]
  change (∫ v, F v) * (∫ y : ι → ℝ, ∏ i, weight s (localGaussian (k i)) (y i)) = _
  rw [show (∫ v, F v) = localGamma k₀ s / 2 from hF.2, integral_fintype_prod_volume_eq_prod]
  exact congrArg (_ * ·) (Finset.prod_congr rfl (fun i _ => (hG i).2))

theorem slice_weight_continuous (k₀ : PlaceKind) (k : ι → PlaceKind) : Continuous (weight 2 (slice k₀ k)) := by
  let F := weight 2 (localGaussian k₀)
  let G (y : ι → ℝ) := ∏ i, weight 2 (localGaussian (k i)) (y i)
  have hcG : Continuous G := continuous_finsetProd _ (fun i _ => (contWeight 2 (k i)).comp (continuous_apply i))
  have hiG : Integrable G := Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℝ))
    (f := fun i => weight 2 (localGaussian (k i))) (fun i => ((hasMellin_log_iff _ _ _).mp (local_mellin (k i) (s := 2) (by norm_num))).1)
  obtain ⟨B, hB⟩ := local_weight_bounded k₀
  rw [funext (wt_slice k₀ k 2)]
  apply continuous_of_dominated (bound := fun y => B * ‖G y‖)
  · intro v
    exact (((contWeight 2 k₀).comp (continuous_const.sub (continuous_finsetSum _ (fun i _ => continuous_apply i)))).mul hcG).aestronglyMeasurable
  · intro v; exact .of_forall fun y => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB (mem_range_self _)) (norm_nonneg _)
  · exact hiG.norm.const_mul B
  · exact .of_forall fun y => ((contWeight 2 k₀).comp (continuous_id.sub continuous_const)).mul continuous_const

theorem slice_continuousAt (k₀ : PlaceKind) (k : ι → PlaceKind) {x : ℝ} (hx : 0 < x) : ContinuousAt (slice k₀ k) x := by
  let F := slice k₀ k
  have he : F =ᶠ[nhds x] (fun t : ℝ => exp (-(2 * (Real.log t : ℂ))) * weight 2 F (Real.log t)) := by
    filter_upwards [lt_mem_nhds hx] with t ht
    simp only [weight, Real.exp_log ht, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  apply ContinuousAt.congr_of_eventuallyEq _ he
  exact (by fun_prop : ContinuousAt (fun t : ℝ => exp (-(2 * (Real.log t : ℂ)))) x).mul
    ((slice_weight_continuous k₀ k).continuousAt.comp (Real.continuousAt_log hx.ne'))

end DedekindHyperplaneMellin

namespace DedekindOrbitProfile

open Complex NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone MeasureTheory
open DedekindArchimedeanProduct DedekindHyperplaneMellin DedekindSignatureKernel
open DedekindUnitDomain DedekindUnitGaussian DedekindRadialOrbit DedekindOrbitIntegrable
open scoped Classical NumberField nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

noncomputable def kind (w : InfinitePlace K) : PlaceKind := if IsReal w then .real else .complex

omit [NumberField K] in
private theorem local_eq (w : InfinitePlace K) (v : ℝ) : localGaussian (kind w) (Real.exp v) =
    (Real.exp (-(Real.pi * mult w) * Real.exp (v / mult w) ^ 2) : ℂ) := by
  by_cases h : IsReal w
  · simp [kind, h, mult, localGaussian, DedekindRealMellin.gauss]
  · simp only [kind, if_neg h, mult, localGaussian, complexPlace, Nat.cast_ofNat,
      pow_two, ← Real.exp_add, add_halves, mul_comm Real.pi (2 : ℝ), neg_mul]

variable (K)

noncomputable abbrev S := slice (kind (w₀ : InfinitePlace K)) (fun v : {w : InfinitePlace K // w ≠ w₀} => kind v.val)

theorem signature_slice {x : ℝ} (hx : 0 < x) : S K x = profile (nrRealPlaces K) (nrComplexPlaces K) x := by
  let M : ℂ := 2 ^ (nrRealPlaces K + nrComplexPlaces K)
  let F (x : ℝ) := M * S K x
  have hm {s : ℂ} (hs : 0 < s.re) : HasMellin F s (DedekindGeneralExpansion.arch K s) := by
    let g (w : InfinitePlace K) := localGamma (kind w) s / 2
    have hg : ∏ w, g w = (Gammaℝ s / 2) ^ nrRealPlaces K * (Gammaℂ s / 2) ^ nrComplexPlaces K := by
      rw [prod_eq_prod_mul_prod]
      have hr (w : {w : InfinitePlace K // IsReal w}) : g w.val = Gammaℝ s / 2 := by simp [g, kind, w.prop, localGamma]
      have hc (w : {w : InfinitePlace K // IsComplex w}) : g w.val = Gammaℂ s / 2 := by simp [g, kind, not_isReal_iff_isComplex.mpr w.prop, localGamma]
      simp only [hr, hc, Finset.prod_const, Finset.card_univ, nrRealPlaces, nrComplexPlaces]
    have hs₀ := slice_mellin (kind (w₀ : InfinitePlace K)) (fun v : {w : InfinitePlace K // w ≠ w₀} => kind v.val) hs
    change HasMellin (S K) s (g w₀ * ∏ v : {w : InfinitePlace K // w ≠ w₀}, g v.val) at hs₀
    rw [← Fintype.prod_eq_mul_prod_subtype_ne g w₀, hg] at hs₀
    have he := hasMellin_const_smul hs₀.1 M
    rw [hs₀.2, smul_eq_mul] at he
    have hval : M * ((Gammaℝ s / 2) ^ nrRealPlaces K * (Gammaℂ s / 2) ^ nrComplexPlaces K) = DedekindGeneralExpansion.arch K s := by
      dsimp only [M, DedekindGeneralExpansion.arch]; rw [pow_add, div_pow, div_pow]; field_simp
    simpa only [F, smul_eq_mul, hval] using he
  have heq (y : ℝ) : mellin F ((2 : ℂ) + y * I) = DedekindGeneralExpansion.arch K (2 + y * I) := (hm (by simp)).2
  have hV : VerticalIntegrable (mellin F) 2 := by
    change Integrable (fun y : ℝ => mellin F ((2 : ℂ) + y * I))
    simpa only [VerticalIntegrable, ofReal_ofNat, heq] using DedekindGeneralExpansion.arch_vertical K
  have hinv : mellinInv 2 (DedekindGeneralExpansion.arch K) x = F x := by
    rw [← mellinInv_mellin_eq 2 F hx (hm (s := 2) (by norm_num)).1 hV
      (continuousAt_const.mul (slice_continuousAt _ _ hx))]
    unfold mellinInv; simp only [ofReal_ofNat, heq]
  rw [inverse_arch K hx] at hinv
  exact (mul_left_cancel₀ (show M ≠ 0 from pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)) hinv).symm

theorem radial_profile {z : ℝ} (hz : 0 < z) :
    (∫ y, gaussian K (z ^ ((2 : ℝ) / Module.finrank ℚ K)) 1 y) = profile (nrRealPlaces K) (nrComplexPlaces K) z := by
  let d : ℝ := Module.finrank ℚ K
  let L := Real.log z / d
  let b (w : InfinitePlace K) := (mult w : ℝ) * L
  let shift : logSpace K := fun v => b v.val
  have hd : d ≠ 0 := by dsimp [d]; exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hb : ∑ w, b w = Real.log z := by
    dsimp only [b, L]; rw [← Finset.sum_mul, show ∑ w : InfinitePlace K, (mult w : ℝ) = d by dsimp only [d]; exact_mod_cast (sum_mult_eq (K := K))]
    field_simp
  have hsq : Real.exp L ^ 2 = z ^ ((2 : ℝ) / d) := by
    rw [Real.rpow_def_of_pos hz, pow_two, ← Real.exp_add]; congr 1; dsimp only [L]; ring
  let U (y : logSpace K) (w : InfinitePlace K) := fullCoordinate K y w + b w
  have hU (y : logSpace K) (v : {w : InfinitePlace K // w ≠ w₀}) : U y v.val = (y + shift) v := by
    simp only [U, fullCoordinate, dif_neg v.prop, Pi.add_apply, shift]
  have h₀ (y : logSpace K) : U y w₀ = Real.log z - ∑ v, (y + shift) v := by
    have hsum : ∑ w, U y w = Real.log z := by simp only [U, Finset.sum_add_distrib, full_sum, zero_add, hb]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hsum
    simp only [hU] at hsum; linarith
  let A (y : logSpace K) := localGaussian (kind (w₀ : InfinitePlace K)) (Real.exp (Real.log z - ∑ v, y v)) *
    ∏ v, localGaussian (kind v.val) (Real.exp (y v))
  have hprod (y : logSpace K) : ∏ w, localGaussian (kind w) (Real.exp (U y w)) = A (y + shift) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ w₀]; simp only [A, h₀, hU]
  have hv (y : logSpace K) (w : InfinitePlace K) : Real.exp (U y w / mult w) = dilation K y w * Real.exp L := by
    simp only [U, b, add_div, mul_div_cancel_left₀ _ mult_coe_ne_zero, Real.exp_add, dilation]
  have he (y : logSpace K) : gaussian K (z ^ ((2 : ℝ) / d)) 1 y = A (y + shift) := by
    rw [← hprod]
    simp only [gaussian, map_one, mul_one, local_eq, hv, mul_pow, ← Complex.ofReal_prod, ← Real.exp_sum]
    congr 2
    simp_rw [show ∀ w : InfinitePlace K, -(Real.pi * mult w) * (dilation K y w ^ 2 * Real.exp L ^ 2) =
      -(Real.pi * (z ^ ((2 : ℝ) / d))) * (mult w * dilation K y w ^ 2) by intro w; rw [hsq]; ring]
    rw [Finset.mul_sum]
  rw [← signature_slice K hz]
  change (∫ y, gaussian K (z ^ ((2 : ℝ) / d)) 1 y) = ∫ y, A y
  simp_rw [he]; exact integral_add_right_eq_self A shift

theorem orbit_profile {T : ℝ} (hT : 0 < T) (a : mixedSpace K) (ha : 0 < mixedEmbedding.norm a) :
    (∑' k : DedekindUnitVectors.Exponents K, ∫ y in domain K,
      gaussian K (T ^ ((2 : ℝ) / Module.finrank ℚ K)) (DedekindUnitVectors.unit K k • a) y) =
    profile (nrRealPlaces K) (nrComplexPlaces K) (T * mixedEmbedding.norm a) := by
  have hrad : radius K a ^ 2 = mixedEmbedding.norm a ^ ((2 : ℝ) / Module.finrank ℚ K) := by
    rw [radius, pow_two, ← Real.exp_add, Real.rpow_def_of_pos ha]; congr 1; ring
  rw [complete_orbit K ha.ne' (Real.rpow_pos_of_pos hT _), hrad, ← Real.mul_rpow hT.le ha.le]
  exact radial_profile K (mul_pos hT ha)

end DedekindOrbitProfile

namespace DedekindGeneralTheta

open NumberField NumberField.Units NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory
open DedekindIdealPlane DedekindIdealClasses DedekindSignatureKernel DedekindMellin
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable def rep (C : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ := (ClassGroup.mk0_surjective C⁻¹).choose

theorem rep_class (C : ClassGroup (𝓞 K)) : ClassGroup.mk0 (rep K C) = C⁻¹ := (ClassGroup.mk0_surjective C⁻¹).choose_spec

noncomputable def q := (Real.sqrt ((discr K).natAbs : ℝ))⁻¹

noncomputable def avg (C : ClassGroup (𝓞 K)) (t : ℝ) : ℂ :=
  let J := rep K C
  let s := (q K * t / Ideal.absNorm (J : Ideal (𝓞 K))) ^ ((2 : ℝ) / Module.finrank ℚ K)
  ∫ y in DedekindUnitDomain.domain K, ∑' a : Lattice K J, DedekindUnitGaussian.gaussian K s a.val y

def Unfolds : Prop := ∀ C : ClassGroup (𝓞 K), ∀ t : ℝ, 0 < t →
  HasSum (fun n : ℕ => (Nat.card (ClassFiber K C n) * torsionOrder K : ℕ) *
    profile (nrRealPlaces K) (nrComplexPlaces K) (q K * t * n)) (avg K C t - (regulator K : ℂ))

theorem kernel_plus_constant (hu : Unfolds K) {t : ℝ} (ht : 0 < t) :
    let M := (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K)
    let c : ℂ := ((2 : ℝ) ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K / torsionOrder K : ℝ)
    kernel K t + c = M / (torsionOrder K : ℂ) * ∑ C, avg K C t := by
  let M := (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K)
  let W : ℂ := torsionOrder K
  let R : ℂ := regulator K
  let b (n : ℕ) : ℂ := if n = 0 then 0 else (coeff K n : ℂ) * profile (nrRealPlaces K) (nrComplexPlaces K) (q K * t * n)
  have hs : HasSum (fun n => W * b n) (∑ C, (avg K C t - R)) := by
    apply (hasSum_sum fun C _ => hu C t ht).congr_fun
    intro n
    simp only [b, ← Finset.sum_mul, ← Nat.cast_sum, ← Finset.sum_mul]
    by_cases hn : n = 0
    · subst n
      have h0 (C : ClassGroup (𝓞 K)) : Nat.card (ClassFiber K C 0) = 0 := by
        let : IsEmpty (ClassFiber K C 0) := ⟨fun I => (Ideal.absNorm_pos_of_nonZeroDivisors I.val).ne' I.prop.1⟩
        simp
      simp [h0]
    · rw [if_neg hn, ← coeff_eq_sum_classes K hn, Nat.cast_mul]; dsimp only [W]; ring
  have htot := hs.tsum_eq
  rw [tsum_mul_left, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htot
  have hA : ∑ C, avg K C t = W * (∑' n, b n) + (classNumber K : ℂ) * R := (eq_sub_iff_add_eq.mp htot).symm
  have hw : W ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  have hk : kernel K t = M * ∑' n, b n := explicit_kernel K ht
  dsimp only
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  rw [hk, hA]
  change M * _ + M * R * (classNumber K : ℂ) / W = M / W * _
  field_simp

end DedekindGeneralTheta

namespace DedekindLatticeGaussian

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding DedekindUnitDomain DedekindUnitGaussian DedekindIdealPlane
open scoped NumberField nonZeroDivisors Classical

theorem summable_gaussian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {b : ℝ} (hb : 0 < b) : Summable (fun x : L => Real.exp (-b * ‖x‖ ^ 2)) := by
  let m := Module.finrank ℤ L + 1
  let r : ℝ := -((2 * m : ℕ) : ℝ)
  have hr : r < -(Module.finrank ℤ L : ℝ) := by dsimp [r, m]; push_cast; linarith
  apply Summable.of_norm_bounded_eventually ((ZLattice.summable_norm_rpow L r hr).mul_left ((m.factorial : ℝ) / b ^ m))
  filter_upwards [Filter.eventually_cofinite_ne (0 : L)] with x hx
  have hX : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hF : 0 < (m.factorial : ℝ) := by positivity
  have h := Real.pow_div_factorial_le_exp (b * ‖x‖ ^ 2) (mul_nonneg hb.le (sq_nonneg ‖x‖)) m
  have hrx : ‖x‖ ^ r = (‖x‖ ^ (2 * m))⁻¹ := by dsimp only [r]; rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, hrx, neg_mul, Real.exp_neg]
  rw [mul_pow, ← pow_mul] at h
  calc (Real.exp (b * ‖x‖ ^ 2))⁻¹ ≤ (b ^ m * ‖x‖ ^ (2 * m) / (m.factorial : ℝ))⁻¹ := by
         simpa only [one_div] using one_div_le_one_div_of_le (div_pos (mul_pos (pow_pos hb _) (pow_pos hX _)) hF) h
       _ = (m.factorial : ℝ) / b ^ m * (‖x‖ ^ (2 * m))⁻¹ := by rw [inv_div, ← div_eq_mul_inv, div_div]

variable (K : Type*) [Field K] [NumberField K]

theorem domain_bounded : Bornology.IsBounded (domain K) := ZSpan.fundamentalDomain_isBounded _

theorem dilation_lower : ∃ c : ℝ, 0 < c ∧ ∀ y ∈ domain K, ∀ w, c ≤ dilation K y w := by
  have h0 : (0 : logSpace K) ∈ domain K := by simp [domain, ZSpan.fundamentalDomain]
  have hC := (domain_bounded K).isCompact_closure
  have hw (w : InfinitePlace K) : ∃ c : ℝ, 0 < c ∧ ∀ y ∈ domain K, c ≤ dilation K y w := by
    have hd : Continuous (fun y : logSpace K => dilation K y w) :=
      ((DedekindOrbitIntegrable.continuous_coordinate K w).div_const _).rexp
    obtain ⟨a, _, ha⟩ := hC.exists_isMinOn ⟨_, subset_closure h0⟩ hd.continuousOn
    exact ⟨_, Real.exp_pos _, fun y hy => isMinOn_iff.mp ha y (subset_closure hy)⟩
  choose c hc hle using hw
  obtain ⟨v, _, hv⟩ := Finset.univ.exists_min_image c Finset.univ_nonempty
  exact ⟨c v, hc v, fun y hy w => (hv w (Finset.mem_univ _)).trans (hle w y hy)⟩

theorem quadratic_lower {c : ℝ} (hc : 0 < c) (y : logSpace K) (hy : ∀ w, c ≤ dilation K y w)
    (a : mixedSpace K) : c ^ 2 * ‖a‖ ^ 2 ≤
      ∑ w : InfinitePlace K, (mult w : ℝ) * (dilation K y w * normAtPlace w a) ^ 2 := by
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun w : InfinitePlace K => normAtPlace w a)
  rw [norm_eq_sup'_normAtPlace, hw, ← mul_pow]
  have h := mul_le_mul_of_nonneg_right (hy w) (normAtPlace_nonneg w a)
  calc _ ≤ (dilation K y w * normAtPlace w a) ^ 2 := pow_le_pow_left₀ (mul_nonneg hc.le (normAtPlace_nonneg w a)) h 2
       _ ≤ (mult w : ℝ) * _ := le_mul_of_one_le_left (sq_nonneg _) one_le_mult
       _ ≤ _ := Finset.single_le_sum (fun v _ => mul_nonneg (Nat.cast_nonneg (mult v)) (sq_nonneg (dilation K y v * normAtPlace v a))) (Finset.mem_univ w)

theorem uniform_majorant (J : (Ideal (𝓞 K))⁰) {s : ℝ} (hs : 0 < s) :
    ∃ B : Lattice K J → ℝ, Summable B ∧ ∀ x : Lattice K J, ∀ y ∈ domain K, ‖gaussian K s x.val y‖ ≤ B x := by
  obtain ⟨c, hc, hle⟩ := dilation_lower K
  let b := Real.pi * s * c ^ 2
  refine ⟨fun x => Real.exp (-b * ‖x‖ ^ 2), summable_gaussian _ (mul_pos (mul_pos Real.pi_pos hs) (sq_pos_of_pos hc)), ?_⟩
  intro x y hy
  simp only [gaussian, Complex.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
  calc _ ≤ -(Real.pi * s) * (c ^ 2 * ‖x.val‖ ^ 2) := mul_le_mul_of_nonpos_left (quadratic_lower K hc y (hle y hy) _) (neg_nonpos.mpr (mul_pos Real.pi_pos hs).le)
       _ = _ := by change _ = -((Real.pi * s) * c ^ 2) * ‖x.val‖ ^ 2; ring

end DedekindLatticeGaussian

namespace DedekindClassUnfold

open MeasureTheory NumberField NumberField.Units NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding.fundamentalCone
open DedekindUnitDomain DedekindUnitGaussian DedekindIdealPlane DedekindUnitVectors
open DedekindGeneralTheta DedekindIdealClasses DedekindSignatureKernel
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

theorem lattice_sum (J : (Ideal (𝓞 K))⁰) {s : ℝ} (hs : 0 < s) :
    HasSum (fun x : Lattice K J => ∫ y in domain K, gaussian K s x.val y)
      (∫ y in domain K, ∑' x : Lattice K J, gaussian K s x.val y) := by
  obtain ⟨B, hB, hb⟩ := DedekindLatticeGaussian.uniform_majorant K J hs
  have hD : MeasurableSet (domain K) := ZSpan.fundamentalDomain_measurableSet _
  have hV : volume (domain K) ≠ ⊤ := ((DedekindLatticeGaussian.domain_bounded K).measure_lt_top).ne
  apply hasSum_integral_of_dominated_convergence (fun x _ => B x)
  · intro x; exact (DedekindOrbitIntegrable.continuous_gaussian K s _).aestronglyMeasurable
  · intro x; filter_upwards [ae_restrict_mem hD] with y hy using hb x y hy
  · exact .of_forall fun _ => hB
  · exact integrableOn_const hV
  · filter_upwards [ae_restrict_mem hD] with y hy
    exact (hB.of_norm_bounded fun x => hb x y hy).hasSum

theorem orbit_sum (J : (Ideal (𝓞 K))⁰) {s : ℝ} (hs : 0 < s) :
    HasSum (fun a : idealSet K J => ∑' k : Exponents K, ∫ y in domain K, gaussian K s (unit K k • a.val) y)
      ((∫ y in domain K, ∑' x : Lattice K J, gaussian K s x.val y) - (regulator K : ℂ)) := by
  classical
  have h := (({0} : Finset (Lattice K J)).hasSum_iff_compl).mp (lattice_sum K J hs)
  have hz (y : logSpace K) : gaussian K s 0 y = 1 := by simp [gaussian]
  have hI : (∫ y in domain K, gaussian K s (0 : Lattice K J).val y) = (regulator K : ℂ) := by
    simp only [Submodule.coe_zero, hz, setIntegral_const, volume_domain, Complex.real_smul, mul_one]
  rw [Finset.sum_singleton, hI] at h
  let e : {x : Lattice K J // x ≠ 0} ≃ {x : Lattice K J // x ∉ ({0} : Finset (Lattice K J))} :=
    Equiv.subtypeEquivRight (fun x => by simp)
  let E := (Equiv.prodComm (idealSet K J) (Exponents K)).trans ((orbitEquiv K J).trans e)
  have hp := E.hasSum_iff.mpr h
  rw [← hp.tsum_eq, hp.summable.tsum_prod]
  exact hp.summable.prod.hasSum

theorem unfolds : Unfolds K := by
  intro C t ht
  let J := rep K C
  let N : ℝ := Ideal.absNorm (J : Ideal (𝓞 K))
  let T := q K * t / N
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors J
  have hq : 0 < q K := inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)))
  have hT : 0 < T := div_pos (mul_pos hq ht) hN
  have h : HasSum (fun a : idealSet K J => profile (nrRealPlaces K) (nrComplexPlaces K) (T * mixedEmbedding.norm a.val))
      (avg K C t - (regulator K : ℂ)) := by
    apply (orbit_sum K J (Real.rpow_pos_of_pos hT ((2 : ℝ) / Module.finrank ℚ K))).congr_fun
    intro a; exact (DedekindOrbitProfile.orbit_profile K hT a.val (norm_pos_of_mem a.prop.1)).symm
  let g (a : idealSet K J) := DedekindIdealSeries.grade K J ⟨a.val, a.prop.2⟩
  have hg (a : idealSet K J) (n : ℕ) : g a = n ↔ mixedEmbedding.norm a.val = (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ) :=
    DedekindIdealSeries.grade_eq_iff K J _ n
  have hv (n : ℕ) (a : g ⁻¹' {n}) : T * mixedEmbedding.norm a.val.val = q K * t * n := by
    rw [(hg a.val n).mp a.prop, Nat.cast_mul]
    change (q K * t / N) * (N * n) = _
    field_simp
  apply (h.tsum_fiberwise g).congr_fun
  intro n
  simp_rw [hv n]
  rw [tsum_const, nsmul_eq_mul, class_count K C J (rep_class K C) n]
  congr 2
  exact Nat.card_congr (Equiv.subtypeEquivRight fun a => (hg a n).symm)

end DedekindClassUnfold

end OMA.HeckeExpansion

namespace OMA.IdealThetaReciprocity

namespace DedekindDualIdeals

open NumberField
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev Frac := FractionalIdeal (𝓞 K)⁰ K

noncomputable def dual (J : (Frac K)ˣ) : (Frac K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (J : Frac K)) (FractionalIdeal.dual_ne_zero ℤ ℚ J.ne_zero)

theorem dual_apply (J : (Frac K)ˣ) : dual K J = dual K 1 * J⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, dual, Units.val_mk0, Units.val_one]
  exact FractionalIdeal.dual_eq_mul_inv ℤ ℚ (J : Frac K)

noncomputable def classPerm : Equiv.Perm (ClassGroup (𝓞 K)) where
  toFun C := ClassGroup.mk K (dual K 1) * C⁻¹
  invFun C := ClassGroup.mk K (dual K 1) * C⁻¹
  left_inv C := by simp [mul_left_comm, mul_comm, mul_assoc]
  right_inv C := by simp [mul_left_comm, mul_comm, mul_assoc]

theorem class_dual (J : (Frac K)ˣ) : ClassGroup.mk K (dual K J) = classPerm K (ClassGroup.mk K J) := by
  rw [dual_apply, map_mul, map_inv]; rfl

theorem absNorm_dual (J : (Frac K)ˣ) :
    FractionalIdeal.absNorm (dual K J : Frac K) = (((discr K).natAbs : ℚ) * FractionalIdeal.absNorm (J : Frac K))⁻¹ := by
  have hD : FractionalIdeal.dual ℤ ℚ (1 : Frac K) = ((differentIdeal ℤ (𝓞 K) : Frac K))⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]
  change FractionalIdeal.absNorm (FractionalIdeal.dual ℤ ℚ (J : Frac K)) = _
  rw [FractionalIdeal.dual_eq_mul_inv, hD, map_mul, map_inv₀, map_inv₀, FractionalIdeal.coeIdeal_absNorm,
    absNorm_differentIdeal K (𝓞 K), mul_inv]

end DedekindDualIdeals

namespace DedekindIdealPlane
open NumberField NumberField.mixedEmbedding
open scoped NumberField nonZeroDivisors
variable (K : Type*) [Field K] [NumberField K]

noncomputable abbrev Lattice (J : (Ideal (𝓞 K))⁰) := idealLattice K (FractionalIdeal.mk0 K J)

end DedekindIdealPlane

namespace DedekindRealUnits

open NumberField NumberField.Units NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone DedekindIdealPlane
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

theorem unit_lattice {J : (Ideal (𝓞 K))⁰} (u : (𝓞 K)ˣ) {x : mixedSpace K} (hx : x ∈ Lattice K J) :
    u • x ∈ Lattice K J := by
  obtain ⟨y, hy, rfl⟩ := (mem_idealLattice K _).mp hx
  apply (mem_idealLattice K _).mpr
  let I := ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
  refine ⟨(u : 𝓞 K) • y, (I : Submodule (𝓞 K) K).smul_mem (u : 𝓞 K) hy, ?_⟩
  change mixedEmbedding K ((u : K) * y) = _
  rw [unitSMul_smul, map_mul]

end DedekindRealUnits

namespace DedekindUnitVectors

open NumberField NumberField.Units NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone DedekindIdealPlane
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev Exponents := Fin (rank K) → ℤ

noncomputable def unit (k : Exponents K) : (𝓞 K)ˣ := ∏ i, fundSystem K i ^ k i

end DedekindUnitVectors

namespace DedekindUnitDomain

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
open MeasureTheory Module DedekindUnitVectors Additive
open scoped NumberField Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable def domain : Set (logSpace K) := ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ _)

theorem fundamental : IsAddFundamentalDomain (unitLattice K) (domain K) volume :=
  ZLattice.isAddFundamentalDomain (basisUnitLattice K) volume



noncomputable def latticeEquiv : Exponents K ≃ unitLattice K := (basisUnitLattice K).equivFun.toEquiv.symm

theorem log_unit (k : Exponents K) : logEmbedding K (ofMul (unit K k)) = (latticeEquiv K k : logSpace K) := by
  change logEmbedding K (ofMul (∏ i, fundSystem K i ^ k i)) = ↑((basisUnitLattice K).equivFun.symm k)
  simp only [ofMul_prod, ofMul_zpow, map_sum, map_zsmul, logEmbedding_fundSystem,
    Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower]



noncomputable def fullCoordinate (y : logSpace K) (w : InfinitePlace K) : ℝ :=
  if h : w = w₀ then -∑ v, y v else y ⟨w, h⟩

theorem full_sum (y : logSpace K) : ∑ w, fullCoordinate K y w = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
  have he (w : {w : InfinitePlace K // w ≠ w₀}) : fullCoordinate K y w.val = y w := by simp only [fullCoordinate, dif_neg w.prop]
  have hb : fullCoordinate K y w₀ = -∑ v, y v := dif_pos rfl
  rw [hb, Finset.sum_congr rfl (fun i _ => he i), neg_add_cancel]

theorem full_log_unit (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    fullCoordinate K (logEmbedding K (ofMul u)) w = (mult w : ℝ) * Real.log (w (u : K)) := by
  by_cases hw : w = w₀
  · subst w
    rw [fullCoordinate, dif_pos rfl, sum_logEmbedding_component, neg_mul, neg_neg]
  · simp [fullCoordinate, hw, logEmbedding_component]

end DedekindUnitDomain

namespace DedekindUnitGaussian

open NumberField NumberField.Units NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding DedekindUnitDomain DedekindUnitVectors MeasureTheory Additive
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable def dilation (y : logSpace K) (w : InfinitePlace K) : ℝ := Real.exp (fullCoordinate K y w / mult w)

theorem add_coord (y z : logSpace K) (w : InfinitePlace K) : fullCoordinate K (y+z) w = fullCoordinate K y w + fullCoordinate K z w := by
  by_cases h : w = w₀ <;> simp [fullCoordinate, h, Finset.sum_add_distrib, add_comm]

theorem determinant (y : logSpace K) : ∏ w, (dilation K y w) ^ mult w = 1 := by
  have he (w : InfinitePlace K) : (dilation K y w) ^ mult w = Real.exp (fullCoordinate K y w) := by
    rw [dilation, ← Real.exp_nat_mul]; congr 1; field_simp [mult_coe_ne_zero]
  simp_rw [he, ← Real.exp_sum, full_sum, Real.exp_zero]

theorem dilation_unit (u : (𝓞 K)ˣ) (y : logSpace K) (w : InfinitePlace K) :
    dilation K (y + logEmbedding K (ofMul u)) w = dilation K y w * w (u : K) := by
  rw [dilation, add_coord, add_div, Real.exp_add, full_log_unit,
    mul_div_cancel_left₀ _ mult_coe_ne_zero, Real.exp_log (pos_at_place u w)]
  rfl

noncomputable def gaussian (t : ℝ) (a : mixedSpace K) (y : logSpace K) : ℂ :=
  Real.exp (-(Real.pi * t) * ∑ w : InfinitePlace K, (mult w : ℝ) * (dilation K y w * normAtPlace w a) ^ 2)

theorem gaussian_unit (u : (𝓞 K)ˣ) (a : mixedSpace K) (t : ℝ) (y : logSpace K) :
    gaussian K t (u • a) y = gaussian K t a (y + logEmbedding K (ofMul u)) := by
  simp only [gaussian, dilation_unit, unitSMul_smul, map_mul, normAtPlace_apply, mul_assoc]

end DedekindUnitGaussian

namespace DedekindRadialOrbit

open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding
open DedekindUnitDomain DedekindUnitGaussian MeasureTheory
open scoped NumberField Classical

variable (K : Type*) [Field K] [NumberField K]

theorem complete_zero_sum (b : InfinitePlace K → ℝ) (hb : ∑ w, b w = 0) (w : InfinitePlace K) :
    fullCoordinate K (fun v => b v.val) w = b w := by
  by_cases hw : w = w₀
  · subst w
    rw [fullCoordinate, dif_pos rfl]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hb
    linarith
  · simp only [fullCoordinate, dif_neg hw]

noncomputable def radius (a : mixedSpace K) : ℝ := Real.exp (Real.log (mixedEmbedding.norm a) / Module.finrank ℚ K)

theorem abs_decompose (a : mixedSpace K) (ha : mixedEmbedding.norm a ≠ 0) (w : InfinitePlace K) :
    normAtPlace w a = radius K a * dilation K (logMap a) w := by
  let n : ℝ := Module.finrank ℚ K
  let L := Real.log (mixedEmbedding.norm a)
  let b (v : InfinitePlace K) := (mult v : ℝ) * (Real.log (normAtPlace v a) - L / n)
  have hn : n ≠ 0 := by dsimp only [n]; exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hmul : ∑ v : InfinitePlace K, (mult v : ℝ) = n := by dsimp only [n]; exact_mod_cast (sum_mult_eq (K := K))
  have hlog : ∑ v : InfinitePlace K, (mult v : ℝ) * Real.log (normAtPlace v a) = L := by
    simp only [L, mixedEmbedding.norm_apply, Real.log_prod (fun i _ => pow_ne_zero _ (mixedEmbedding.norm_ne_zero_iff.mp ha i)), Real.log_pow]
  have hb : ∑ v, b v = 0 := by
    simp only [b, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hlog, hmul]
    field_simp; ring
  have he : logMap a = fun v => b v.val := by ext v; simp only [logMap_apply, b, L, n, div_eq_mul_inv]
  rw [radius, dilation, he, complete_zero_sum K b hb, ← Real.exp_add]
  change normAtPlace w a = Real.exp (L/n + ((mult w : ℝ) * (Real.log (normAtPlace w a) - L/n)) / mult w)
  rw [mul_div_cancel_left₀ _ mult_coe_ne_zero, add_sub_cancel, Real.exp_log]
  exact lt_of_le_of_ne (normAtPlace_nonneg w a) (mixedEmbedding.norm_ne_zero_iff.mp ha w).symm

end DedekindRadialOrbit

namespace DedekindGeneralTheta

open NumberField NumberField.Units NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory
open DedekindIdealPlane
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable def rep (C : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ := (ClassGroup.mk0_surjective C⁻¹).choose

theorem rep_class (C : ClassGroup (𝓞 K)) : ClassGroup.mk0 (rep K C) = C⁻¹ := (ClassGroup.mk0_surjective C⁻¹).choose_spec

noncomputable def dualLabel : Equiv.Perm (ClassGroup (𝓞 K)) :=
  ((Equiv.inv _).trans (DedekindDualIdeals.classPerm K)).trans (Equiv.inv _)

noncomputable def q := (Real.sqrt ((discr K).natAbs : ℝ))⁻¹

noncomputable def avg (C : ClassGroup (𝓞 K)) (t : ℝ) : ℂ :=
  let J := rep K C
  let s := (q K * t / Ideal.absNorm (J : Ideal (𝓞 K))) ^ ((2 : ℝ) / Module.finrank ℚ K)
  ∫ y in DedekindUnitDomain.domain K, ∑' a : Lattice K J, DedekindUnitGaussian.gaussian K s a.val y



def Reciprocal : Prop := ∀ (C : ClassGroup (𝓞 K)) (t : ℝ), 0 < t →
  avg K C (1/t) = (t : ℂ) * avg K (dualLabel K C) t

end DedekindGeneralTheta

namespace DedekindClassPeriods

open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
open NumberField.InfinitePlace NumberField.mixedEmbedding DedekindUnitDomain DedekindUnitGaussian
open DedekindUnitVectors DedekindRadialOrbit DedekindIdealPlane
open scoped NumberField nonZeroDivisors Classical Pointwise

variable (K : Type*) [Field K] [NumberField K]

theorem affine_average (f : logSpace K → ℂ) (hf : ∀ (v : unitLattice K) y, f (v.val + y) = f y)
    (b : logSpace K) : (∫ y in domain K, f (b - y)) = ∫ y in domain K, f y := by
  let : MeasurableVAdd (unitLattice K) (logSpace K) := (inferInstance : MeasurableVAdd (unitLattice K).toAddSubgroup (logSpace K))
  let : VAddInvariantMeasure (unitLattice K) (logSpace K) volume := (inferInstance : VAddInvariantMeasure (unitLattice K).toAddSubgroup (logSpace K) volume)
  let e : logSpace K ≃ logSpace K := { toFun := fun y => b-y, invFun := fun y => b-y,
                                        left_inv := sub_sub_cancel b, right_inv := sub_sub_cancel b }
  have hm := Measure.measurePreserving_sub_left (volume : Measure (logSpace K)) b
  have he : MeasurableEmbedding (fun y : logSpace K => b - y) :=
    (Homeomorph.subLeft b).measurableEmbedding
  have hD : IsAddFundamentalDomain (unitLattice K) (e '' domain K) volume :=
    (fundamental K).image_of_equiv e hm.quasiMeasurePreserving (Equiv.neg _) (by
      intro v y; change b - (-v.val + y) = v.val + (b-y); abel)
  exact (hm.setIntegral_image_emb he f (domain K)).symm.trans (hD.setIntegral_eq (fundamental K) hf)



theorem gaussian_mul (a b : mixedSpace K) (ha : mixedEmbedding.norm a ≠ 0) (s : ℝ) (y : logSpace K) :
    gaussian K s (a*b) y = gaussian K (s * radius K a ^ 2) b (y + logMap a) := by
  have hd (w : InfinitePlace K) : dilation K (y + logMap a) w = dilation K y w * dilation K (logMap a) w := by
    rw [dilation, add_coord, add_div, Real.exp_add]; rfl
  have hw (w : InfinitePlace K) : (mult w : ℝ) * (dilation K y w * normAtPlace w (a*b)) ^ 2 =
      radius K a ^ 2 * ((mult w : ℝ) * (dilation K (y+logMap a) w * normAtPlace w b) ^ 2) := by
    rw [map_mul, abs_decompose K a ha w, hd]; ring
  simp only [gaussian, hw, ← Finset.mul_sum]; congr 2; ring

theorem integral_unit_periodic (J : (Ideal (𝓞 K))⁰) (s : ℝ) (v : unitLattice K) (y : logSpace K) :
    (∑' a : Lattice K J, gaussian K s a.val (v.val + y)) = ∑' a : Lattice K J, gaussian K s a.val y := by
  let k := (latticeEquiv K).symm v
  let u := unit K k
  have hv : v.val = logEmbedding K (Additive.ofMul u) := by rw [log_unit]; exact congrArg Subtype.val ((latticeEquiv K).apply_symm_apply v).symm
  let e : Lattice K J ≃ Lattice K J := {
    toFun := fun a => ⟨u • a.val, DedekindRealUnits.unit_lattice K u a.prop⟩
    invFun := fun a => ⟨u⁻¹ • a.val, DedekindRealUnits.unit_lattice K u⁻¹ a.prop⟩
    left_inv := fun a => Subtype.ext (inv_smul_smul u a.val)
    right_inv := fun a => Subtype.ext (smul_inv_smul u a.val) }
  rw [hv, add_comm]
  simp_rw [← gaussian_unit]
  exact e.tsum_eq (fun a => gaussian K s a.val y)

end DedekindClassPeriods

namespace DedekindFractionalTheta

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding DedekindGeneralTheta DedekindDualIdeals DedekindClassPeriods
open DedekindUnitDomain DedekindUnitGaussian DedekindRadialOrbit
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev FIdeal := (Frac K)ˣ
abbrev Carrier (J : FIdeal K) := ↥((J.val : Frac K) : Submodule (𝓞 K) K)

noncomputable def embed (J : FIdeal K) : Carrier K J ≃ idealLattice K J :=
  Equiv.ofBijective (fun a => ⟨mixedEmbedding K a.val, (mem_idealLattice K J).mpr ⟨a.val,a.prop,rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (mixedEmbedding_injective (K := K) (congrArg Subtype.val h)), by
      intro x; obtain ⟨y, hy, he⟩ := (mem_idealLattice K J).mp x.prop; exact ⟨⟨y,hy⟩,Subtype.ext he⟩⟩

noncomputable def normF (J : FIdeal K) : ℝ := FractionalIdeal.absNorm J.val

theorem normF_pos (J : FIdeal K) : 0 < normF K J := by
  dsimp only [normF]; exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J.val) (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.mpr J.ne_zero))

noncomputable def scale (J : FIdeal K) (t : ℝ) := (q K * t / normF K J) ^ ((2 : ℝ) / Module.finrank ℚ K)

noncomputable def theta (J : FIdeal K) (t : ℝ) (y : logSpace K) : ℂ :=
  ∑' a : Carrier K J, gaussian K (scale K J t) (mixedEmbedding K a.val) y

theorem theta_lattice (J : FIdeal K) (t : ℝ) (y : logSpace K) : theta K J t y =
    ∑' a : idealLattice K J, gaussian K (scale K J t) a.val y :=
  (embed K J).tsum_eq (fun a => gaussian K (scale K J t) a.val y)

theorem avg_eq (C : ClassGroup (𝓞 K)) (t : ℝ) : avg K C t =
    ∫ y in domain K, theta K (FractionalIdeal.mk0 K (rep K C)) t y := by
  simp only [avg, theta_lattice, scale, normF, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]

theorem same_class {I J : FIdeal K} (h : ClassGroup.mk K I = ClassGroup.mk K J) :
    ∃ u : Kˣ, J = toPrincipalIdeal (𝓞 K) K u * I := by
  have h₁ : ClassGroup.mk K (J / I) = 1 := by simp only [map_div, ← h, div_self']
  have hp := ClassGroup.mk_eq_one_iff.mp h₁
  obtain ⟨a,ha⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hp
  have he : ((J / I : FIdeal K) : Frac K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
    apply Subtype.coe_injective; simp only [FractionalIdeal.val_eq_coe, ha, FractionalIdeal.coe_spanSingleton]
  have hn : a ≠ 0 := by intro hz; apply (J / I).ne_zero; simpa [hz] using he
  let u := Units.mk0 a hn
  have hI : toPrincipalIdeal (𝓞 K) K u = J / I := (toPrincipalIdeal_eq_iff).mpr he.symm
  exact ⟨u, by rw [hI, div_mul_cancel]⟩

variable (I : FIdeal K) (u : Kˣ)

theorem mem_principal_mul (z : K) :
    z ∈ (↑(toPrincipalIdeal (𝓞 K) K u * I) : Frac K) ↔ ∃ a ∈ I.val, z = (u : K) * a := by
  rw [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.mem_singleton_mul]

noncomputable def principalEquiv : Carrier K I ≃ Carrier K (toPrincipalIdeal (𝓞 K) K u * I) :=
  Equiv.ofBijective (fun a => ⟨(u : K) * a.val,(mem_principal_mul K I u _).mpr ⟨a.val,a.prop,rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (mul_left_cancel₀ u.ne_zero (congrArg Subtype.val h)), by
      intro z; obtain ⟨a,ha,hz⟩ := (mem_principal_mul K I u _).mp z.prop; exact ⟨⟨a,ha⟩,Subtype.ext hz.symm⟩⟩

theorem normF_principal : normF K (toPrincipalIdeal (𝓞 K) K u * I) =
    mixedEmbedding.norm (mixedEmbedding K u.val) * normF K I := by
  simp only [normF, Units.val_mul, map_mul, coe_toPrincipalIdeal, FractionalIdeal.absNorm_span_singleton,
    norm_eq_norm, Rat.cast_mul, Rat.cast_abs]

theorem principal_theta (t : ℝ) (ht : 0 < t) (y : logSpace K) :
    theta K (toPrincipalIdeal (𝓞 K) K u * I) t y = theta K I t (y + logMap (mixedEmbedding K u.val)) := by
  let a := mixedEmbedding K u.val
  have hA : 0 < mixedEmbedding.norm a := lt_of_le_of_ne (mixedEmbedding.norm_nonneg a)
    (Ne.symm ((mixedEmbedding.norm_eq_zero_iff' ⟨u.val,rfl⟩).not.mpr (fun hz => u.ne_zero ((mixedEmbedding_injective (K := K)) (hz.trans (map_zero (mixedEmbedding K)).symm)))))
  have hq : 0 < q K := inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)))
  have ha : radius K a ^ 2 = mixedEmbedding.norm a ^ ((2 : ℝ) / Module.finrank ℚ K) := by
    rw [radius, pow_two, ← Real.exp_add, Real.rpow_def_of_pos hA]; congr 1; ring
  have hscale : scale K (toPrincipalIdeal (𝓞 K) K u * I) t * radius K a ^ 2 = scale K I t := by
    rw [scale, scale, normF_principal, ha, ← Real.mul_rpow (div_pos (mul_pos hq ht) (mul_pos hA (normF_pos K I))).le hA.le]
    congr 1; change q K * t / (mixedEmbedding.norm a * normF K I) * mixedEmbedding.norm a = q K * t / normF K I
    field_simp [hA.ne']
  unfold theta; rw [← (principalEquiv K I u).tsum_eq]; apply tsum_congr
  intro z
  change gaussian K _ (mixedEmbedding K ((u : K) * z.val)) y = _
  rw [map_mul, gaussian_mul K a _ hA.ne', hscale]

theorem theta_periodic_rep (C : ClassGroup (𝓞 K)) (t : ℝ) (v : unitLattice K) (y : logSpace K) :
    theta K (FractionalIdeal.mk0 K (rep K C)) t (v.val + y) = theta K (FractionalIdeal.mk0 K (rep K C)) t y := by
  simp only [theta_lattice]; exact integral_unit_periodic K (rep K C) _ v y

theorem label_class (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (dual K (FractionalIdeal.mk0 K (rep K C))) =
      ClassGroup.mk K (FractionalIdeal.mk0 K (rep K (dualLabel K C))) := by
  rw [class_dual, ClassGroup.mk_mk0, ClassGroup.mk_mk0, rep_class, rep_class]
  simp [dualLabel]

theorem reciprocal_of_pointwise
    (hP : ∀ (C : ClassGroup (𝓞 K)) (t : ℝ), 0 < t → ∀ y : logSpace K,
      let I := FractionalIdeal.mk0 K (rep K C)
      theta K I (1/t) y = (t : ℂ) * theta K (dual K I) t (-y)) : Reciprocal K := by
  intro C t ht
  let I := FractionalIdeal.mk0 K (rep K C)
  let J := FractionalIdeal.mk0 K (rep K (dualLabel K C))
  obtain ⟨u,hu⟩ := same_class K (label_class K C).symm
  have he (y : logSpace K) : theta K (dual K I) t (-y) = theta K J t (logMap (mixedEmbedding K u.val) - y) := by
    rw [show dual K I = toPrincipalIdeal (𝓞 K) K u * J from hu, principal_theta K J u t ht, sub_eq_add_neg, add_comm]
  rw [avg_eq, avg_eq]; change (∫ y in domain K, theta K I (1/t) y) = (t : ℂ) * ∫ y in domain K, theta K J t y
  simp_rw [show ∀ y, theta K I (1/t) y = (t : ℂ) * theta K (dual K I) t (-y) from hP C t ht, he, integral_const_mul]
  exact congrArg ((t : ℂ) * ·) (affine_average K (theta K J t) (theta_periodic_rep K (dualLabel K C) t) _)

end DedekindFractionalTheta

namespace DedekindThetaScales

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding DedekindDualIdeals DedekindFractionalTheta DedekindGeneralTheta
open DedekindUnitGaussian
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

theorem q_pos : 0 < q K := inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)))

theorem q_sq : q K ^ 2 = ((discr K).natAbs : ℝ)⁻¹ := by
  dsimp [q]; rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem normF_dual (I : FIdeal K) : normF K (dual K I) = q K ^ 2 / normF K I := by
  rw [q_sq]; simp only [normF, absNorm_dual, Rat.cast_inv, Rat.cast_mul, Rat.cast_natCast, mul_inv, div_eq_mul_inv]

theorem scale_dual (I : FIdeal K) {t : ℝ} (ht : 0 < t) : scale K (dual K I) t = (scale K I (1/t))⁻¹ := by
  have hq := q_pos K; have hN := normF_pos K I
  rw [scale, scale, normF_dual, ← Real.inv_rpow (div_nonneg (mul_nonneg hq.le (one_div_pos.mpr ht).le) hN.le)]
  congr 1; field_simp

theorem scale_weight (I : FIdeal K) {t : ℝ} (ht : 0 < t) :
    (q K / normF K I) * (scale K I (1/t)) ^ (-(Module.finrank ℚ K : ℝ) / 2) = t := by
  have hq := q_pos K; have hN := normF_pos K I
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  rw [scale, ← Real.rpow_mul (div_nonneg (mul_nonneg hq.le (one_div_pos.mpr ht).le) hN.le),
    show ((2 : ℝ) / Module.finrank ℚ K) * (-(Module.finrank ℚ K : ℝ)/2) = -1 by field_simp,
    Real.rpow_neg_one]; field_simp

theorem covolume_weight (I : FIdeal K) :
    (2 : ℝ) ^ nrComplexPlaces K * ZLattice.covolume (idealLattice K I) = normF K I / q K := by
  rw [mixedEmbedding.covolume_idealLattice]
  simp only [normF, q, div_inv_eq_mul, Nat.cast_natAbs, Int.cast_abs]
  rw [show (2 : ℝ)⁻¹ ^ nrComplexPlaces K = ((2 : ℝ) ^ nrComplexPlaces K)⁻¹ by rw [inv_pow]]
  field_simp

noncomputable def raw (I : FIdeal K) (s : ℝ) (y : logSpace K) : ℂ :=
  ∑' a : Carrier K I, gaussian K s (mixedEmbedding K a.val) y

def LatticePoisson : Prop := ∀ (I : FIdeal K) (s : ℝ), 0 < s → ∀ y : logSpace K,
    raw K I s y = (((q K / normF K I) * s ^ (-(Module.finrank ℚ K : ℝ) / 2) : ℝ) : ℂ) * raw K (dual K I) s⁻¹ (-y)

theorem reciprocal (h : LatticePoisson K) : Reciprocal K := by
  apply reciprocal_of_pointwise K; intro C t ht y
  let I := FractionalIdeal.mk0 K (rep K C)
  have hs : 0 < scale K I (1/t) := Real.rpow_pos_of_pos (div_pos (mul_pos (q_pos K) (one_div_pos.mpr ht)) (normF_pos K I)) _
  have he := h I _ hs y
  rw [scale_weight K I ht, ← scale_dual K I ht] at he
  exact he

end DedekindThetaScales

namespace DedekindTorusPoisson

open MeasureTheory Set UnitAddTorus Filter Topology
open scoped Classical

variable {d : Type*} [Fintype d]

noncomputable def grid (k : d → ℤ) : d → ℝ := fun i => k i

noncomputable def proj (x : d → ℝ) : UnitAddTorus d := fun i => x i

theorem proj_open : IsOpenQuotientMap (proj (d := d)) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

theorem proj_grid (k : d → ℤ) : proj (grid k) = 0 := by
  funext i; change ((k i : ℝ) : UnitAddCircle) = 0
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k i, by simp⟩

theorem proj_add (x y : d → ℝ) : proj (x+y) = proj x + proj y := rfl

theorem same_proj {x y : d → ℝ} (h : proj x = proj y) : ∃ k : d → ℤ, x = y + grid k := by
  have he (i : d) : ∃ n : ℤ, (n : ℝ) = x i - y i := by
    have hh : (((x i - y i : ℝ)) : UnitAddCircle) = 0 := by
      change ((x i : UnitAddCircle) - (y i : UnitAddCircle)) = 0; exact sub_eq_zero.mpr (congrFun h i)
    simpa using ((AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hh)
  choose k hk using he
  exact ⟨k, funext fun i => by change x i = y i + (k i : ℝ); rw [hk]; ring⟩

noncomputable def period (f : (d → ℝ) → ℂ) (x : d → ℝ) := ∑' k : d → ℤ, f (x + grid k)

theorem period_add (f : (d → ℝ) → ℂ) (x : d → ℝ) (k : d → ℤ) : period f (x + grid k) = period f x := by
  have he (n : d → ℤ) : x + grid k + grid n = x + grid (k+n) := by ext i; simp [grid,add_assoc]
  simp only [period, he]; exact (Equiv.addLeft k).tsum_eq (fun n => f (x + grid n))

def UniformBound (f : (d → ℝ) → ℂ) : Prop := ∀ S : Set (d → ℝ), IsCompact S →
    ∃ B : (d → ℤ) → ℝ, Summable B ∧ ∀ k, ∀ x ∈ S, ‖f (x + grid k)‖ ≤ B k

theorem continuous_period {f : (d → ℝ) → ℂ} (hf : Continuous f) (hB : UniformBound f) : Continuous (period f) := by
  apply continuous_iff_continuousAt.mpr; intro x
  obtain ⟨B,hS,h⟩ := hB _ (isCompact_closedBall x 1)
  have hc : ContinuousOn (period f) (Metric.closedBall x 1) :=
    continuousOn_tsum (fun k => (hf.comp (continuous_id.add continuous_const)).continuousOn) hS h
  exact (hc x (Metric.mem_closedBall_self zero_le_one)).continuousAt (Metric.closedBall_mem_nhds _ zero_lt_one)

theorem lift_period {f : (d → ℝ) → ℂ} (hf : Continuous f) (hB : UniformBound f) :
    ∃ F : C(UnitAddTorus d, ℂ), ∀ x, F (proj x) = period f x := by
  let p := proj (d := d)
  let g (z : UnitAddTorus d) := (proj_open.surjective z).choose
  let F (z : UnitAddTorus d) := period f (g z)
  have he (x : d → ℝ) : F (p x) = period f x := by
    obtain ⟨k,hk⟩ := same_proj ((proj_open.surjective (p x)).choose_spec)
    change period f (g (p x)) = _; rw [show g (p x) = x + grid k from hk, period_add]
  refine ⟨⟨F, proj_open.isQuotientMap.continuous_iff.mpr ?_⟩,he⟩
  change Continuous (F ∘ p); rw [show F ∘ p = period f from funext he]; exact continuous_period hf hB

noncomputable def cube (d : Type*) := {x : d → ℝ | ∀ i, x i ∈ Ioc 0 1}

theorem cube_measurable : MeasurableSet (cube d) := MeasurableSet.univ_pi' fun _ => measurableSet_Ioc

theorem cube_subset : cube d ⊆ Icc (0 : d → ℝ) 1 := fun _ hx => ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩

theorem grid_integral (G : (d → ℝ) → ℂ) (hG : Integrable G) :
    (∫ x, G x) = ∑' k : d → ℤ, ∫ x in cube d, G (x + grid k) := by
  letI : AddAction (d → ℤ) (d → ℝ) := {
    vadd := fun k x => grid k + x
    zero_vadd := fun x => by funext i; change ((0 : ℤ) : ℝ) + x i = x i; simp
    add_vadd := fun k l x => by funext i; change ((k i + l i : ℤ) : ℝ) + x i = (k i : ℝ) + ((l i : ℝ) + x i); simp [add_assoc] }
  letI : MeasurableConstVAdd (d → ℤ) (d → ℝ) := ⟨fun k => measurable_const_add _⟩
  letI : VAddInvariantMeasure (d → ℤ) (d → ℝ) volume :=
    ⟨fun k _ h => (measurePreserving_add_left volume (grid k)).measure_preimage h.nullMeasurableSet⟩
  have hD : IsAddFundamentalDomain (d → ℤ) (cube d) volume := by
    apply IsAddFundamentalDomain.mk' cube_measurable.nullMeasurableSet
    intro x
    have hi (i : d) : ∃! n : ℤ, (n : ℝ) + x i ∈ Ioc 0 1 := by
      simpa only [zero_add, zsmul_eq_mul, mul_one, add_comm (x i)] using existsUnique_add_zsmul_mem_Ioc (zero_lt_one : 0 < (1 : ℝ)) (x i) 0
    choose n hn hu using hi
    exact ⟨n,hn,fun k hk => funext fun i => hu i (k i) (hk i)⟩
  rw [hD.integral_eq_tsum'' G hG]; apply tsum_congr; intro k
  change (∫ x in cube d, G (grid k + x)) = _
  simp_rw [add_comm (grid k)]

noncomputable def character (n : d → ℤ) (x : d → ℝ) : ℂ := mFourier (-n) (proj x)

theorem char_norm (n : d → ℤ) (x : d → ℝ) : ‖character n x‖ = 1 := by
  simp [character,mFourier,fourier_apply,norm_prod,Circle.norm_coe]

theorem coefficient {f : (d → ℝ) → ℂ} (hf : Continuous f) (hi : Integrable f) (hb : UniformBound f)
    (F : C(UnitAddTorus d, ℂ)) (hF : ∀ x, F (proj x) = period f x) (n : d → ℤ) :
    mFourierCoeff F n = ∫ x, character n x * f x := by
  let e := character n
  let G (x : d → ℝ) := e x * f x
  have he : Continuous e := (mFourier (-n)).continuous.comp proj_open.continuous
  have hG : Integrable G := hi.norm.mono' (he.mul hf).aestronglyMeasurable (.of_forall fun x => by
    simp only [G,e,norm_mul,char_norm,one_mul,le_rfl])
  have hper (x : d → ℝ) (k : d → ℤ) : e (x+grid k) = e x := by simp [e,character,proj_add,proj_grid]
  obtain ⟨B,hB,h⟩ := hb _ (isCompact_Icc (a := (0 : d → ℝ)) (b := 1))
  have hbound (k : d → ℤ) (x : d → ℝ) (hx : x ∈ cube d) : ‖G (x + grid k)‖ ≤ B k := by
    simp only [G,e,norm_mul,char_norm,one_mul]; exact h k x (cube_subset hx)
  have hs : HasSum (fun k : d → ℤ => ∫ x in cube d, G (x+grid k)) (∫ x in cube d, ∑' k, G (x+grid k)) := by
    apply hasSum_integral_of_dominated_convergence (fun k _ => B k)
    · intro k; exact ((he.mul hf).comp (continuous_id.add continuous_const)).aestronglyMeasurable
    · intro k; filter_upwards [ae_restrict_mem cube_measurable] with x hx using hbound k x hx
    · exact .of_forall fun _ => hB
    · exact integrableOn_const ((measure_mono cube_subset).trans_lt isCompact_Icc.measure_lt_top).ne
    · filter_upwards [ae_restrict_mem cube_measurable] with x hx
      exact (hB.of_norm_bounded (fun k => hbound k x hx)).hasSum
  rw [mFourierCoeff_eq_integral F n 0, grid_integral G hG, hs.tsum_eq]
  simp only [Pi.zero_apply, zero_add, smul_eq_mul]
  change (∫ x in cube d, e x * F (proj x)) = _
  simp only [G,hper,← tsum_mul_left,hF,period]

theorem poisson {f : (d → ℝ) → ℂ} (hf : Continuous f) (hi : Integrable f) (hb : UniformBound f)
    (hD : Summable fun n : d → ℤ => ∫ x, character n x * f x) :
    (∑' k : d → ℤ, f (grid k)) = ∑' n : d → ℤ, ∫ x, character n x * f x := by
  obtain ⟨F,hF⟩ := lift_period hf hb
  have hcoeff := coefficient hf hi hb F hF
  have hS : Summable (mFourierCoeff F) := hD.congr fun n => (hcoeff n).symm
  have h0 (n : d → ℤ) : mFourier n (proj (0 : d → ℝ)) = 1 := by simp [mFourier,proj]
  have hsum := (hasSum_mFourier_series_apply_of_summable hS (proj 0)).tsum_eq.symm
  simpa only [h0,smul_eq_mul,mul_one,hF,period,zero_add,hcoeff] using hsum

end DedekindTorusPoisson

namespace DedekindTraceCoordinates

open Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open DedekindDualIdeals DedekindFractionalTheta
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable def archTrace (z : mixedSpace K) : ℝ := (∑ w, z.1 w) + ∑ w, 2 * (z.2 w).re

theorem archTrace_embedding (a : K) : archTrace K (mixedEmbedding K a) = (Algebra.trace ℚ K a : ℝ) := by
  let e := (indexEquiv K).trans (RingHom.equivRatAlgHom K ℂ)
  have hh := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := a)
  rw [← e.sum_comp (fun σ : K →ₐ[ℚ] ℂ => σ a)] at hh
  have h := congrArg Complex.re hh
  simp only [eq_ratCast, Complex.ratCast_re, Complex.re_sum, Fintype.sum_sum_type,
    Finset.univ_product_univ.symm, Finset.sum_product, Fin.sum_univ_two, e, Equiv.trans_apply,
    RingHom.equivRatAlgHom_apply, RingHom.toRatAlgHom_apply, indexEquiv_apply_isReal,
    indexEquiv_apply_isComplex_fst, indexEquiv_apply_isComplex_snd, ComplexEmbedding.conjugate_coe_eq,
    Complex.conj_re, ← two_mul, Complex.add_re] at h
  have hr (w : {w : InfinitePlace K // IsReal w}) : (w.val.embedding a).re = embedding_of_isReal w.prop a := by
    rw [← embedding_of_isReal_apply w.prop a, Complex.ofReal_re]
  simpa only [archTrace,mixedEmbedding_apply_isReal,mixedEmbedding_apply_isComplex,
    hr] using h.symm

noncomputable def tracePair (x z : mixedSpace K) : ℝ := archTrace K (x * z)

theorem tracePair_embed (x z : K) : tracePair K (mixedEmbedding K x) (mixedEmbedding K z) =
    (Algebra.trace ℚ K (x*z) : ℝ) := by rw [tracePair, ← map_mul, archTrace_embedding]

theorem tracePair_sum {ι : Type*} [Fintype ι] (b : ι → mixedSpace K) (x : ι → ℝ) (z : mixedSpace K) :
    tracePair K (∑ i, x i • b i) z = ∑ i, x i * tracePair K (b i) z := by
  let A : mixedSpace K →ₗ[ℝ] ℝ := {
    toFun := archTrace K
    map_add' := fun u v => by simp only [archTrace,Prod.fst_add,Prod.snd_add,Pi.add_apply,Complex.add_re,mul_add,Finset.sum_add_distrib]; ring
    map_smul' := fun c u => by simp only [archTrace,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,Complex.smul_re, RingHom.id_apply, mul_add,Finset.mul_sum]; ring_nf }
  change A ((∑ i, x i • b i) * z) = ∑ i, x i * A (b i * z)
  simp only [Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,smul_eq_mul]

variable (I : FIdeal K)

abbrev Idx := Free.ChooseBasisIndex ℤ I

theorem dual_span : Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I).traceDual) =
    (((dual K I).val : Submodule (𝓞 K) K).restrictScalars ℤ) := by
  have h : (I.val : Submodule (𝓞 K) K).restrictScalars ℤ = Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) := by
    ext x; exact (mem_span_basisOfFractionalIdeal K).symm
  change _ = ((FractionalIdeal.dual ℤ ℚ I.val : Submodule (𝓞 K) K).restrictScalars ℤ)
  rw [FractionalIdeal.coe_dual ℤ ℚ I.ne_zero]
  exact (Submodule.traceDual_span_of_basis ℤ (I.val : Submodule (𝓞 K) K) (basisOfFractionalIdeal K I) h).symm

noncomputable def frequency : (Idx K I → ℤ) ≃ Carrier K (dual K I) :=
  (((basisOfFractionalIdeal K I).traceDual.restrictScalars ℤ).equivFun.toEquiv.symm).trans
    (Equiv.subtypeEquivRight fun x => SetLike.ext_iff.mp (dual_span K I) x)

theorem frequency_coord (n : Idx K I → ℤ) (i : Idx K I) :
    Algebra.trace ℚ K ((frequency K I n).val * basisOfFractionalIdeal K I i) = (n i : ℚ) := by
  let b := (basisOfFractionalIdeal K I).traceDual
  let z := (b.restrictScalars ℤ).equivFun.symm n
  have h := b.restrictScalars_repr_apply ℤ z i
  have hz : (b.restrictScalars ℤ).repr z i = n i := congrFun ((b.restrictScalars ℤ).equivFun.apply_symm_apply n) i
  rw [hz] at h
  change Algebra.trace ℚ K (z.val * basisOfFractionalIdeal K I i) = _
  simpa [b,Basis.traceDual_repr_apply,Algebra.traceForm_apply] using h.symm

theorem frequency_pair (n : Idx K I → ℤ) (x : Idx K I → ℝ) :
    tracePair K ((fractionalIdealLatticeBasis K I).equivFun.symm x) (mixedEmbedding K (frequency K I n).val) =
      ∑ i, x i * (n i : ℝ) := by
  rw [Basis.equivFun_symm_apply,tracePair_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [fractionalIdealLatticeBasis_apply, tracePair_embed, mul_comm (basisOfFractionalIdeal K I i), frequency_coord, Rat.cast_intCast]

end DedekindTraceCoordinates

namespace DedekindDiagonalTransform

open MeasureTheory Complex
open scoped Classical

variable {d : Type*} [Fintype d]

noncomputable def phase (t : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * I) * t)

theorem character_eq (n : d → ℤ) (x : d → ℝ) : DedekindTorusPoisson.character n x =
    phase (∑ i, x i * (n i : ℝ)) := by
  simp only [DedekindTorusPoisson.character,UnitAddTorus.mFourier,ContinuousMap.coe_mk,
    DedekindTorusPoisson.proj,Pi.neg_apply,fourier_coe_apply,Int.cast_neg,ofReal_one,div_one,
    phase,ofReal_sum,Finset.mul_sum,ofReal_mul,ofReal_intCast,Complex.exp_sum]
  apply Finset.prod_congr rfl; intro i _; congr 1; ring

noncomputable def wave (a f x : d → ℝ) : ℂ :=
  phase (∑ i, x i * f i) * (Real.exp (-Real.pi * ∑ i, a i * (x i)^2) : ℂ)

theorem wave_eq (a f x : d → ℝ) : wave a f x = Complex.exp
    (-(∑ i, (Real.pi * a i : ℝ) * (x i : ℂ)^2) + ∑ i, (-(2 * Real.pi * I) * f i) * x i) := by
  simp only [wave,phase,Complex.ofReal_exp,← Complex.exp_add,ofReal_neg,ofReal_sum,ofReal_mul,ofReal_pow,
    Finset.mul_sum,neg_mul,Finset.sum_neg_distrib]
  congr 1
  rw [add_comm]; congr 1 <;> try apply congrArg Neg.neg <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem integrable_wave (a f : d → ℝ) (ha : ∀ i, 0 < a i) : Integrable (wave a f) := by
  simp_rw [funext (wave_eq a f)]
  exact GaussianFourier.integrable_cexp_neg_sum_mul_add (fun i => (show 0 < (↑(Real.pi * a i) : ℂ).re from mul_pos Real.pi_pos (ha i))) _

theorem integral_wave (a f : d → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ x, wave a f x) = ((∏ i, (a i) ^ (-(1/2) : ℝ)) : ℝ) *
      (Real.exp (-Real.pi * ∑ i, (f i)^2 / a i) : ℂ) := by
  simp_rw [wave_eq]
  rw [GaussianFourier.integral_cexp_neg_sum_mul_add (fun i => (show 0 < (↑(Real.pi * a i) : ℂ).re from mul_pos Real.pi_pos (ha i))), Finset.prod_mul_distrib]
  congr 1
  · rw [ofReal_prod]; apply Finset.prod_congr rfl; intro i _
    rw [show ((Real.pi : ℂ) / ↑(Real.pi * a i)) = ((a i)⁻¹ : ℝ) by push_cast; field_simp [Real.pi_ne_zero],
      show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num,
      ← ofReal_cpow (inv_nonneg.mpr (ha i).le), Real.inv_rpow (ha i).le, Real.rpow_neg (ha i).le]
  · rw [← Complex.exp_sum, ofReal_exp]; congr 1
    simp only [ofReal_mul,ofReal_neg,ofReal_sum,ofReal_div,ofReal_pow,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hai : (a i : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ha i).ne'
    field_simp; ring_nf; simp [I_sq]

end DedekindDiagonalTransform

namespace DedekindBasisMeasure

open MeasureTheory MeasureTheory.Measure Module ZSpan
open NumberField NumberField.mixedEmbedding DedekindFractionalTheta
open scoped Classical NumberField nonZeroDivisors

variable {d E : Type*} [Fintype d] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

theorem coords_map (b : Basis d ℝ E) (μ : Measure E) [IsAddHaarMeasure μ] :
    μ.map b.equivFunL = μ (fundamentalDomain b) • (volume : Measure (d → ℝ)) := by
  have he : b.map b.equivFunL.toLinearEquiv = Pi.basisFun ℝ d := by
    ext i : 1; funext j
    simp [Pi.basisFun_apply,Basis.repr_self,Pi.single_apply,Finsupp.single_apply,eq_comm]
  have hm := addHaarMeasure_unique μ b.parallelepiped
  have hb : μ = μ (fundamentalDomain b) • b.addHaar := by
    rw [measure_congr (fundamentalDomain_ae_parallelepiped b μ)]
    simpa only [Basis.coe_parallelepiped,Basis.addHaar_def] using hm
  conv_lhs => rw [hb,Measure.map_smul,b.map_addHaar,he,Basis.addHaar_def,Basis.parallelepiped_basisFun,addHaarMeasure_eq_volume_pi]

theorem integrate (b : Basis d ℝ E) (μ : Measure E) [IsAddHaarMeasure μ] (f : E → ℂ) :
    (∫ x, f x ∂μ) = μ.real (fundamentalDomain b) • ∫ u, f (b.equivFun.symm u) := by
  let e := b.equivFunL.toHomeomorph.toMeasurableEquiv
  have h := e.measurableEmbedding.integral_map (μ := μ) (fun u => f (b.equivFun.symm u))
  change (∫ u, f (b.equivFun.symm u) ∂μ.map b.equivFunL) = ∫ x, f (b.equivFun.symm (b.equivFun x)) ∂μ at h
  simpa only [LinearEquiv.symm_apply_apply,coords_map,integral_smul_measure,measureReal_def] using h.symm

theorem integrable_iff (b : Basis d ℝ E) (μ : Measure E) [IsAddHaarMeasure μ] (f : E → ℂ) :
    Integrable f μ ↔ Integrable (fun u => f (b.equivFun.symm u)) := by
  let e := b.equivFunL.toHomeomorph.toMeasurableEquiv
  have h := e.measurableEmbedding.integrable_map_iff (μ := μ) (g := fun u => f (b.equivFun.symm u))
  change Integrable _ (μ.map b.equivFunL) ↔ Integrable (fun x => f (b.equivFun.symm (b.equivFun x))) μ at h
  rw [coords_map,integrable_smul_measure (measure_fundamentalDomain_ne_zero (μ := μ) b) (fundamentalDomain_isBounded b).measure_lt_top.ne] at h
  simpa using h.symm

end DedekindBasisMeasure

namespace DedekindLatticeGaussian

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding DedekindUnitDomain DedekindUnitGaussian DedekindIdealPlane
open scoped NumberField nonZeroDivisors Classical

theorem summable_gaussian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {b : ℝ} (hb : 0 < b) : Summable (fun x : L => Real.exp (-b * ‖x‖ ^ 2)) := by
  let m := Module.finrank ℤ L + 1
  let r : ℝ := -((2 * m : ℕ) : ℝ)
  have hr : r < -(Module.finrank ℤ L : ℝ) := by dsimp [r, m]; push_cast; linarith
  apply Summable.of_norm_bounded_eventually ((ZLattice.summable_norm_rpow L r hr).mul_left ((m.factorial : ℝ) / b ^ m))
  filter_upwards [Filter.eventually_cofinite_ne (0 : L)] with x hx
  have hX : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hF : 0 < (m.factorial : ℝ) := by positivity
  have h := Real.pow_div_factorial_le_exp (b * ‖x‖ ^ 2) (mul_nonneg hb.le (sq_nonneg ‖x‖)) m
  have hrx : ‖x‖ ^ r = (‖x‖ ^ (2 * m))⁻¹ := by dsimp only [r]; rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, hrx, neg_mul, Real.exp_neg]
  rw [mul_pow, ← pow_mul] at h
  calc (Real.exp (b * ‖x‖ ^ 2))⁻¹ ≤ (b ^ m * ‖x‖ ^ (2 * m) / (m.factorial : ℝ))⁻¹ := by
         simpa only [one_div] using one_div_le_one_div_of_le (div_pos (mul_pos (pow_pos hb _) (pow_pos hX _)) hF) h
       _ = (m.factorial : ℝ) / b ^ m * (‖x‖ ^ (2 * m))⁻¹ := by rw [inv_div, ← div_eq_mul_inv, div_div]

variable (K : Type*) [Field K] [NumberField K]



theorem quadratic_lower {c : ℝ} (hc : 0 < c) (y : logSpace K) (hy : ∀ w, c ≤ dilation K y w)
    (a : mixedSpace K) : c ^ 2 * ‖a‖ ^ 2 ≤
      ∑ w : InfinitePlace K, (mult w : ℝ) * (dilation K y w * normAtPlace w a) ^ 2 := by
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun w : InfinitePlace K => normAtPlace w a)
  rw [norm_eq_sup'_normAtPlace, hw, ← mul_pow]
  have h := mul_le_mul_of_nonneg_right (hy w) (normAtPlace_nonneg w a)
  calc _ ≤ (dilation K y w * normAtPlace w a) ^ 2 := pow_le_pow_left₀ (mul_nonneg hc.le (normAtPlace_nonneg w a)) h 2
       _ ≤ (mult w : ℝ) * _ := le_mul_of_one_le_left (sq_nonneg _) one_le_mult
       _ ≤ _ := Finset.single_le_sum (fun v _ => mul_nonneg (Nat.cast_nonneg (mult v)) (sq_nonneg (dilation K y v * normAtPlace v a))) (Finset.mem_univ w)

end DedekindLatticeGaussian

namespace DedekindGaussianConvergence

open MeasureTheory Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem DedekindFractionalTheta DedekindTraceCoordinates
open DedekindLatticeGaussian DedekindUnitGaussian DedekindTorusPoisson
open scoped Classical NumberField nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

noncomputable def point (I : FIdeal K) : (Idx K I → ℤ) ≃ idealLattice K I :=
  (((fractionalIdealLatticeBasis K I).restrictScalars ℤ).equivFun.toEquiv.symm).trans
    (Equiv.subtypeEquivRight fun x => SetLike.ext_iff.mp (span_idealLatticeBasis K I) x)

theorem point_eq (I : FIdeal K) (k : Idx K I → ℤ) : (point K I k).val =
    (fractionalIdealLatticeBasis K I).equivFun.symm (grid k) := by
  let b := fractionalIdealLatticeBasis K I
  let v := (b.restrictScalars ℤ).equivFun.symm k
  apply b.equivFun.injective; rw [LinearEquiv.apply_symm_apply]; funext i
  have h := b.restrictScalars_repr_apply ℤ v i
  have hv : (b.restrictScalars ℤ).repr v i = k i := congrFun ((b.restrictScalars ℤ).equivFun.apply_symm_apply k) i
  rw [hv] at h
  change b.repr v.val i = (k i : ℝ)
  simpa using h.symm

theorem bound {s : ℝ} (hs : 0 < s) (y : logSpace K) : ∃ b : ℝ, 0 < b ∧ ∀ z : mixedSpace K,
    ‖gaussian K s z y‖ ≤ Real.exp (-b * ‖z‖^2) := by
  obtain ⟨w,_,hw⟩ := Finset.univ.exists_min_image (dilation K y) Finset.univ_nonempty
  let c := dilation K y w
  have hc : 0 < c := Real.exp_pos _
  refine ⟨Real.pi * s * c^2,mul_pos (mul_pos Real.pi_pos hs) (sq_pos_of_pos hc),fun z => ?_⟩
  simp only [gaussian,Complex.norm_of_nonneg (Real.exp_pos _).le,Real.exp_le_exp]
  have h := mul_le_mul_of_nonpos_left (quadratic_lower K hc y (fun v => hw v (Finset.mem_univ _)) z) (neg_nonpos.mpr (mul_pos Real.pi_pos hs).le)
  linarith only [h]

theorem abs_sum (I : FIdeal K) {s : ℝ} (hs : 0 < s) (y : logSpace K) :
    Summable fun z : Carrier K I => gaussian K s (mixedEmbedding K z.val) y := by
  obtain ⟨b,hb,h⟩ := bound K hs y
  exact (embed K I).summable_iff.mpr ((summable_gaussian (idealLattice K I) hb).of_norm_bounded (fun z => h z.val))

noncomputable def sample (I : FIdeal K) (s : ℝ) (y : logSpace K) (x : Idx K I → ℝ) :=
  gaussian K s ((fractionalIdealLatticeBasis K I).equivFun.symm x) y

theorem continuous_sample (I : FIdeal K) (s : ℝ) (y : logSpace K) : Continuous (sample K I s y) := by
  have h (w : InfinitePlace K) := (continuous_normAtPlace w).comp (fractionalIdealLatticeBasis K I).equivFunL.symm.continuous
  unfold sample gaussian
  exact Complex.continuous_ofReal.comp (Continuous.rexp (continuous_const.mul (continuous_finsetSum _ (fun w _ => continuous_const.mul ((continuous_const.mul (h w)).pow 2)))))

theorem uniform (I : FIdeal K) {s : ℝ} (hs : 0 < s) (y : logSpace K) : UniformBound (sample K I s y) := by
  intro S hS
  let e := (fractionalIdealLatticeBasis K I).equivFunL.symm
  obtain ⟨R,hR,hSR⟩ := (hS.image e.continuous).isBounded.exists_pos_norm_le
  obtain ⟨b,hb,h⟩ := bound K hs y
  let B (z : idealLattice K I) := Real.exp (b * R^2) * Real.exp (-(b/2) * ‖z‖^2)
  refine ⟨fun k => B (point K I k),(point K I).summable_iff.mpr ((summable_gaussian _ (half_pos hb)).mul_left _),?_⟩
  intro k x hx
  let z := (point K I k).val
  have hz : e (grid k) = z := (point_eq K I k).symm
  have hR' : ‖e x‖ ≤ R := hSR _ ⟨_,hx,rfl⟩
  have ht : ‖z‖ ≤ R + ‖e x + z‖ := by
    have := norm_sub_le (e x + z) (e x)
    rw [add_sub_cancel_left] at this; linarith
  have hsq := pow_le_pow_left₀ (norm_nonneg z) ht 2
  have hh : ‖z‖^2 / 2 - R^2 ≤ ‖e x + z‖^2 := by nlinarith [sq_nonneg (R-‖e x+z‖)]
  change ‖gaussian K s (e (x+grid k)) y‖ ≤ Real.exp (b*R^2) * Real.exp (-(b/2)*‖z‖^2)
  rw [map_add,hz,← Real.exp_add]; apply (h _).trans; apply Real.exp_le_exp.mpr
  linarith only [mul_le_mul_of_nonneg_left hh hb.le]

end DedekindGaussianConvergence

namespace DedekindMixedAxes

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open DedekindTraceCoordinates DedekindUnitGaussian DedekindUnitDomain
open scoped Classical NumberField

variable (K : Type*) [Field K] [NumberField K]

def place : index K → InfinitePlace K := Sum.elim Subtype.val (fun p => p.1.val)

def sign : index K → ℝ := Sum.elim (fun _ => 1) (fun p => if p.2 = 0 then 1 else -1)

noncomputable def coord (z : mixedSpace K) := (stdBasis K).equivFun z

noncomputable def a (s : ℝ) (y : logSpace K) (i : index K) : ℝ :=
  s * (mult (place K i) : ℝ) * dilation K y (place K i) ^ 2

noncomputable def f (z : mixedSpace K) (i : index K) : ℝ :=
  mult (place K i) * sign K i * coord K z i

theorem a_pos {s : ℝ} (hs : 0 < s) (y : logSpace K) (i : index K) : 0 < a K s y i :=
  mul_pos (mul_pos hs (Nat.cast_pos.mpr mult_pos)) (sq_pos_of_pos (Real.exp_pos _))

theorem neg_dilation (y : logSpace K) (w : InfinitePlace K) : dilation K (-y) w = (dilation K y w)⁻¹ := by
  have h : fullCoordinate K (-y) w = -fullCoordinate K y w := by
    by_cases hw : w = w₀ <;> simp [fullCoordinate,hw,Finset.sum_neg_distrib]
  rw [dilation,dilation,h,neg_div,Real.exp_neg]

theorem quadratic (s : ℝ) (y : logSpace K) (z : mixedSpace K) :
    ∑ i, a K s y i * (coord K z i)^2 = s * ∑ w : InfinitePlace K, (mult w : ℝ) * (dilation K y w * normAtPlace w z)^2 := by
  rw [sum_eq_sum_add_sum (fun w : InfinitePlace K => (mult w : ℝ) * _),mul_add]
  simp only [Fintype.sum_sum_type,← Finset.univ_product_univ,Finset.sum_product,Fin.sum_univ_two,
    a,place,Sum.elim_inl,Sum.elim_inr,coord,Module.Basis.equivFun_apply,stdBasis_apply_isReal,
    stdBasis_apply_isComplex_fst,stdBasis_apply_isComplex_snd,mult_isReal,mult_isComplex,
    Finset.mul_sum,Nat.cast_one,Nat.cast_ofNat]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro w _
  · rw [normAtPlace_apply_of_isReal w.prop]; simp [Real.norm_eq_abs,mul_pow,sq_abs,mul_assoc]
  · rw [normAtPlace_apply_of_isComplex w.prop]; simp [mul_pow,Complex.sq_norm,Complex.normSq_apply]; ring

theorem pairing (u z : mixedSpace K) : ∑ i, coord K u i * f K z i = tracePair K u z := by
  simp only [f,sign,place,coord,Module.Basis.equivFun_apply,Fintype.sum_sum_type,← Finset.univ_product_univ,
    Finset.sum_product,Fin.sum_univ_two,Sum.elim_inl,Sum.elim_inr,stdBasis_apply_isReal,
    stdBasis_apply_isComplex_fst,stdBasis_apply_isComplex_snd,mult_isReal,mult_isComplex,
    tracePair,archTrace,Prod.fst_mul,Prod.snd_mul,Pi.mul_apply,Complex.mul_re]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro w _ <;> norm_num <;> ring

theorem sign_sq (i : index K) : sign K i ^ 2 = 1 := by
  rcases i with w | ⟨w,j⟩ <;> simp [sign]

theorem inverse_quad {s : ℝ} (hs : 0 < s) (y : logSpace K) (z : mixedSpace K) :
    ∑ i, (f K z i)^2 / a K s y i = s⁻¹ * ∑ w : InfinitePlace K, (mult w : ℝ) * (dilation K (-y) w * normAtPlace w z)^2 := by
  rw [← quadratic]; apply Finset.sum_congr rfl; intro i _
  simp only [a,f,neg_dilation,mul_pow,sign_sq,mul_one,inv_pow]
  have hd : dilation K y (place K i) ≠ 0 := (Real.exp_pos _).ne'
  field_simp [hs.ne',mult_coe_ne_zero,hd]

theorem index_prod (g : InfinitePlace K → ℝ) : (∏ i : index K, g (place K i)) = ∏ w, (g w) ^ mult w := by
  rw [prod_eq_prod_mul_prod (fun w : InfinitePlace K => (g w)^mult w)]
  simp [Fintype.prod_sum_type,← Finset.univ_product_univ,Finset.prod_product,Fin.prod_univ_two,place,mult_isReal,mult_isComplex,pow_two]

theorem amplitude {s : ℝ} (hs : 0 < s) (y : logSpace K) :
    (∏ i, (a K s y i)^(-(1/2):ℝ)) = ((2:ℝ)^nrComplexPlaces K)⁻¹ * s^(-(Module.finrank ℚ K : ℝ)/2) := by
  let p : ℝ := -(1/2)
  have hD (w : InfinitePlace K) : (dilation K y w ^ 2) ^ p = (dilation K y w)⁻¹ := by
    have hd : 0 ≤ dilation K y w := (Real.exp_pos _).le
    rw [← Real.rpow_natCast_mul hd]; norm_num [p,Real.rpow_neg_one]
  have hM : (∏ i : index K, (mult (place K i) : ℝ)^p) = ((2:ℝ)^nrComplexPlaces K)⁻¹ := by
    rw [index_prod K (fun w => (mult w : ℝ)^p),prod_eq_prod_mul_prod]
    simp only [mult_isReal,mult_isComplex,Nat.cast_one,Real.one_rpow,one_pow,Finset.prod_const_one,one_mul,
      Nat.cast_ofNat,← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
    norm_num [p, nrComplexPlaces, inv_pow]
  have hV : (∏ i : index K, (dilation K y (place K i))⁻¹) = 1 := by
    rw [Finset.prod_inv_distrib,index_prod,determinant,inv_one]
  simp only [a,Real.mul_rpow (mul_nonneg hs.le (Nat.cast_nonneg _)) (sq_nonneg _),Real.mul_rpow hs.le (Nat.cast_nonneg _),Finset.prod_mul_distrib]
  change _ * (∏ i, (mult (place K i) : ℝ)^p) * (∏ i, (dilation K y (place K i)^2)^p) = _
  simp only [hD,hV,hM,mul_one,Finset.prod_const,Finset.card_univ,← Real.rpow_mul_natCast hs.le]
  rw [← Module.finrank_eq_card_basis (stdBasis K),mixedEmbedding.finrank]
  ring_nf

end DedekindMixedAxes

namespace DedekindIdealPoisson

open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open DedekindFractionalTheta DedekindDualIdeals DedekindTraceCoordinates DedekindUnitGaussian
open DedekindThetaScales DedekindGaussianConvergence DedekindMixedAxes DedekindDiagonalTransform DedekindGeneralTheta
open scoped Classical NumberField nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

noncomputable def G (s : ℝ) (y : logSpace K) (z w : mixedSpace K) : ℂ :=
  phase (tracePair K w z) * gaussian K s w y

theorem G_coord (s : ℝ) (y : logSpace K) (z w : mixedSpace K) :
    G K s y z w = wave (a K s y) (f K z) (coord K w) := by
  simp only [G,wave,pairing,gaussian,quadratic,neg_mul,mul_assoc]

theorem G_standard (s : ℝ) (y : logSpace K) (z : mixedSpace K) (u : index K → ℝ) :
    G K s y z ((stdBasis K).equivFun.symm u) = wave (a K s y) (f K z) u := by
  rw [G_coord,coord,LinearEquiv.apply_symm_apply]

theorem integral_G {s : ℝ} (hs : 0 < s) (y : logSpace K) (z : mixedSpace K) :
    (∫ w, G K s y z w) = ((((2:ℝ)^nrComplexPlaces K)⁻¹ * s^(-(Module.finrank ℚ K : ℝ)/2) : ℝ) : ℂ) * gaussian K s⁻¹ z (-y) := by
  rw [DedekindBasisMeasure.integrate (stdBasis K) volume]
  simp only [measureReal_def,volume_fundamentalDomain_stdBasis,ENNReal.toReal_one,one_smul,G_standard,
    integral_wave _ _ (a_pos K hs y),amplitude K hs,inverse_quad K hs]
  simp only [gaussian,← mul_assoc,neg_mul]

theorem G_integer (I : FIdeal K) (s : ℝ) (y : logSpace K) (n : Idx K I → ℤ) (x : Idx K I → ℝ) :
    G K s y (mixedEmbedding K (frequency K I n).val) ((fractionalIdealLatticeBasis K I).equivFun.symm x) =
      DedekindTorusPoisson.character n x * sample K I s y x := by
  rw [G,frequency_pair,character_eq]; rfl

theorem int_sample (I : FIdeal K) {s : ℝ} (hs : 0 < s) (y : logSpace K) : Integrable (sample K I s y) := by
  have hi : Integrable (G K s y 0) := (DedekindBasisMeasure.integrable_iff (stdBasis K) volume _).mpr (by
    simp only [G_standard]; exact integrable_wave _ _ (a_pos K hs y))
  have h := (DedekindBasisMeasure.integrable_iff (fractionalIdealLatticeBasis K I) volume _).mp hi
  change Integrable (fun u : Idx K I → ℝ => gaussian K s ((fractionalIdealLatticeBasis K I).equivFun.symm u) y)
  simpa only [G,tracePair,mul_zero,archTrace,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,Complex.zero_re,
    Finset.sum_const_zero,zero_add,phase,Complex.ofReal_zero,Complex.exp_zero,one_mul] using h

noncomputable def factor (I : FIdeal K) (s : ℝ) : ℂ := ((q K / normF K I) * s^(-(Module.finrank ℚ K : ℝ)/2) : ℝ)

theorem coefficient (I : FIdeal K) {s : ℝ} (hs : 0 < s) (y : logSpace K) (n : Idx K I → ℤ) :
    (∫ x, DedekindTorusPoisson.character n x * sample K I s y x) =
      factor K I s * gaussian K s⁻¹ (mixedEmbedding K (frequency K I n).val) (-y) := by
  let z := mixedEmbedding K (frequency K I n).val
  let V := ZLattice.covolume (idealLattice K I)
  let m := s^(-(Module.finrank ℚ K : ℝ)/2)
  have hV : V ≠ 0 := ZLattice.covolume_ne_zero (idealLattice K I) volume
  have hA : (2:ℝ)^nrComplexPlaces K * V = normF K I / q K := covolume_weight K I
  have hfactor : V * (q K / normF K I * m) = ((2:ℝ)^nrComplexPlaces K)⁻¹ * m := by
    field_simp [(normF_pos K I).ne',(q_pos K).ne'] at hA ⊢; linear_combination m*hA
  have h := DedekindBasisMeasure.integrate (fractionalIdealLatticeBasis K I) volume (G K s y z)
  rw [← ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice K I),Complex.real_smul,
    integral_G K hs] at h
  simp only [z,G_integer] at h
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hV)
  rw [← h,← mul_assoc]
  change _ = ((V : ℂ) * ((q K / normF K I * m : ℝ) : ℂ)) * _
  rw [← Complex.ofReal_mul,hfactor]

theorem latticePoisson : LatticePoisson K := by
  intro I s hs y
  let b := fractionalIdealLatticeBasis K I
  let g (z : Carrier K (dual K I)) := gaussian K s⁻¹ (mixedEmbedding K z.val) (-y)
  have hD : Summable fun n : Idx K I → ℤ => ∫ x, DedekindTorusPoisson.character n x * sample K I s y x := by
    simp only [coefficient K I hs y]
    exact ((frequency K I).summable_iff.mpr (abs_sum K (dual K I) (inv_pos.mpr hs) (-y))).mul_left _
  have hP := DedekindTorusPoisson.poisson (continuous_sample K I s y) (int_sample K I hs y) (uniform K I hs y) hD
  have he : raw K I s y = ∑' k : Idx K I → ℤ, sample K I s y (DedekindTorusPoisson.grid k) := by
    calc raw K I s y = ∑' z : idealLattice K I, gaussian K s z.val y :=
           (embed K I).tsum_eq (fun z => gaussian K s z.val y)
         _ = _ := by rw [← (point K I).tsum_eq]; simp only [point_eq,sample]
  rw [he,hP]; simp only [coefficient K I hs y,tsum_mul_left]
  exact congrArg (factor K I s * ·) ((frequency K I).tsum_eq g)

theorem reciprocity : Reciprocal K := reciprocal K (latticePoisson K)

end DedekindIdealPoisson

end OMA.IdealThetaReciprocity

namespace OMA.ThetaInversion

open NumberField NumberField.Units NumberField.InfinitePlace

open scoped NumberField

theorem sum_reciprocal {ι : Type*} [Fintype ι] {f g : ι → ℂ} (p : Equiv.Perm ι) (x m : ℂ)
    (hp : ∀ C, f C = x * g (p C)) : m * (∑ C, f C) = x * (m * ∑ C, g C) := by
  simp_rw [hp]; rw [← Finset.mul_sum, Equiv.sum_comp p g, mul_left_comm]

theorem theta {K : Type*} [Field K] [NumberField K] {x : ℝ} (hx : 0 < x) :
    let c : ℂ := ((2 : ℝ) ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K / torsionOrder K : ℝ)
    HeckeExpansion.DedekindMellin.kernel K (1/x) + c = (x : ℂ) * (HeckeExpansion.DedekindMellin.kernel K x + c) := by
  dsimp only
  have hrec (C : ClassGroup (𝓞 K)) : HeckeExpansion.DedekindGeneralTheta.avg K C (1/x) =
      (x : ℂ) * HeckeExpansion.DedekindGeneralTheta.avg K (IdealThetaReciprocity.DedekindGeneralTheta.dualLabel K C) x :=
    IdealThetaReciprocity.DedekindIdealPoisson.reciprocity K C x hx
  rw [HeckeExpansion.DedekindGeneralTheta.kernel_plus_constant K (HeckeExpansion.DedekindClassUnfold.unfolds K) (one_div_pos.mpr hx),
    HeckeExpansion.DedekindGeneralTheta.kernel_plus_constant K (HeckeExpansion.DedekindClassUnfold.unfolds K) hx]
  exact sum_reciprocal (IdealThetaReciprocity.DedekindGeneralTheta.dualLabel K) (x : ℂ) _ hrec

end OMA.ThetaInversion

open NumberField NumberField.Units NumberField.InfinitePlace

theorem OMA.solution : OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1.H2 := by
  intro K _ _ _ A f
  exact ⟨((2 : ℝ) ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K / torsionOrder K : ℝ),
    fun _ hx => OMA.ThetaInversion.theta (K := K) hx⟩
