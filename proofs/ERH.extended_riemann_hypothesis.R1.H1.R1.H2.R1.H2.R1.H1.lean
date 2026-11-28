import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1_H2_R1
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Module.ZLattice.Summable

/-! Hecke's expansion in arbitrary signature. We first identify the archimedean inverse
Mellin transform with the logarithmic-hyperplane integral. The unit action unfolds each
nonzero orbit; a uniform Gaussian bound justifies termwise integration on the unit domain.
Grouping the resulting terms by integral ideal norm gives the theta expansion, with one
regulator for the origin of each ideal lattice. -/

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
  have h2 := OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.gamma_shift_bound h0 2
  simp only [Nat.cast_ofNat, sq_abs] at h2
  calc (1 + s.im ^ 2) * ‖Gamma s‖ ≤ g s.re := by dsimp [g]; linarith [OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.norm_Gamma_le_real h0]
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

noncomputable def grade (J : (Ideal (𝓞 K))⁰) (x : Lattice K J) : ℕ := (OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.exists_grade K J x).choose

theorem grade_eq_iff (J : (Ideal (𝓞 K))⁰) (x : Lattice K J) (n : ℕ) :
    grade K J x = n ↔ mixedEmbedding.norm (x : mixedSpace K) = (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ) := by
  rw [(OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.exists_grade K J x).choose_spec, Nat.cast_inj, Nat.mul_right_inj (Ideal.absNorm_pos_of_nonZeroDivisors J).ne']
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
  rw [kernel, hcomp, OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.inverse_scaled _ _ hq hx _, one_mul,
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

theorem OMA.solution : OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1_H2_R1.H1 := by
  intro K _ _ _
  dsimp only
  intro t ht
  exact OMA.HeckeExpansion.DedekindGeneralTheta.kernel_plus_constant K (OMA.HeckeExpansion.DedekindClassUnfold.unfolds K) ht
