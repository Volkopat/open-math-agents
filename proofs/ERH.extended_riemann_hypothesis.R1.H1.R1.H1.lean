import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H1_R1
import Mathlib.Analysis.MellinInversion

/-! Mellin inversion in the absolute convergence half-plane for the completed Dedekind zeta series.
The coefficient mean follows the ideal-counting argument in Mathlib's Dedekind zeta residue formula.
Gamma recurrence gives an integrable bound on closed vertical strips. Cauchy integration then moves
the inverse Mellin contour, and Fourier inversion in logarithmic coordinates recovers the series.
-/

namespace DedekindMellin

open Complex Filter Set NumberField NumberField.InfinitePlace MeasureTheory Asymptotics
open scoped NumberField Topology FourierTransform

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

theorem analytic (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (dedekindZeta K) s := by
  have habs : LSeries.abscissaOfAbsConv (fun n => (coeff K n : ℂ)) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun x hx => summable K (s := x) hx)
  exact LSeries_analyticOnNhd _ s (habs.trans_lt (EReal.coe_lt_coe_iff.mpr hs))

theorem bounded (K : Type*) [Field K] [NumberField K] {a : ℝ} (ha : 1 < a) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → ‖dedekindZeta K s‖ ≤ C := by
  let u : ℕ → ℂ := fun n => coeff K n
  have haS := (summable K (s := a) ha).norm
  refine ⟨∑' n, ‖LSeries.term u a n‖, fun s hs => ?_⟩
  exact (norm_tsum_le_tsum_norm (summable K (ha.trans_le hs)).norm).trans
    (((summable K (ha.trans_le hs)).norm).tsum_le_tsum
      (fun n => LSeries.norm_term_le_of_re_le_re u (s := a) hs n) haS)

theorem norm_Gamma_le_real {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le, norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- Shifting the gamma argument gains a power of the vertical coordinate at each step. -/
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
  have h2 := gamma_shift_bound h0 2
  simp only [Nat.cast_ofNat, sq_abs] at h2
  calc (1 + s.im ^ 2) * ‖Gamma s‖ ≤ g s.re := by dsimp [g]; linarith [norm_Gamma_le_real h0]
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

noncomputable def completion (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) * Gammaℝ s ^ nrRealPlaces K *
    Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s

theorem completion_decay (K : Type*) [Field K] [NumberField K] {a b : ℝ} (ha : 1 < a) :
    StripDecay a b (completion K) := by
  let l := Real.log (discr K).natAbs / 2
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (f := fun x : ℝ => Real.exp (x * l))
    (K := Icc a b) (by fun_prop)
  have hE : StripBound a b (fun s => exp (s * l)) := by
    refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
    simpa only [norm_exp, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero] using
      (hC (mem_image_of_mem (fun x : ℝ => Real.exp (x * l)) hs)).trans (le_max_left C 0)
  obtain ⟨D, hD⟩ := bounded K ha
  have hZ : StripBound a b (dedekindZeta K) :=
    ⟨max D 0, le_max_right _ _, fun s hs => (hD s hs.1).trans (le_max_left D 0)⟩
  have hR := gammaR_strip (b := b) (zero_lt_one.trans ha)
  have hG := gammaC_strip (b := b) (zero_lt_one.trans ha)
  have hplaces : 0 < nrRealPlaces K + nrComplexPlaces K := by
    rw [← card_eq_nrRealPlaces_add_nrComplexPlaces]; exact Fintype.card_pos
  have harch : StripDecay a b (fun s => Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K) := by
    cases hr : nrRealPlaces K with
    | succ n => exact (hR.pow_succ n).mul_bound (hG.bound.pow _)
    | zero =>
      cases hc : nrComplexPlaces K with
      | zero => simp [hr, hc] at hplaces
      | succ n => simpa using hG.pow_succ n
  convert ((harch.mul_bound hE).mul_bound hZ) using 2 with s
  dsimp [completion, l]; ring

theorem completion_differentiableAt (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (completion K) s := by
  have hR {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ Gammaℝ w := by
    have hn (n : ℕ) : w / 2 ≠ -(n : ℂ) := by
      intro he
      have hr := congrArg re he
      simp only [div_ofNat_re, neg_re, natCast_re] at hr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    unfold Gammaℝ
    apply DifferentiableAt.mul
    · apply DifferentiableAt.const_cpow _ (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
      fun_prop
    · exact (differentiableAt_Gamma _ hn).comp w (f := fun z : ℂ => z / 2) (by fun_prop)
  have hC : DifferentiableAt ℂ Gammaℂ s := by
    have hshift : 0 < (s + 1).re := by simp; linarith
    have h := (hR (zero_lt_one.trans hs)).mul ((hR hshift).comp s (f := fun z : ℂ => z + 1) (by fun_prop))
    rw [show Gammaℂ = fun w => Gammaℝ w * Gammaℝ (w + 1) from funext fun w => (Gammaℝ_mul_Gammaℝ_add_one w).symm]
    exact h
  unfold completion
  exact (((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => exp (z * (Real.log (discr K).natAbs / 2 : ℝ))) s).mul
    ((hR (zero_lt_one.trans hs)).pow _)).mul (hC.pow _)).mul (analytic K hs).differentiableAt

theorem StripDecay.vertical {F : ℂ → ℂ} {a b σ : ℝ} (h : StripDecay a b F) (hσ : σ ∈ Icc a b)
    (hcont : Continuous (fun y : ℝ => F (σ + y * I))) : VerticalIntegrable F σ := by
  obtain ⟨C, hC, h⟩ := h
  apply (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
  filter_upwards with y
  change ‖F (σ + y * I)‖ ≤ C * (1 + y ^ 2)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa [mul_comm] using h ((σ : ℂ) + y * I) (by simpa using hσ)

theorem completion_vertical (K : Type*) [Field K] [NumberField K] {σ : ℝ} (hσ : 1 < σ) :
    VerticalIntegrable (completion K) σ := by
  apply (completion_decay K hσ (b := σ)).vertical ⟨le_rfl, le_rfl⟩
  apply continuous_iff_continuousAt.mpr
  intro y
  apply (completion_differentiableAt K (s := σ + y * I) (by simpa using hσ)).continuousAt.comp
    (f := fun t : ℝ => (σ : ℂ) + t * I)
  fun_prop

theorem vertical_integral_shift {F : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ s : ℂ, s.re ∈ Icc a b → DifferentiableAt ℂ F s) (hD : StripDecay a b F) :
    (∫ t : ℝ, F (a + t * I)) = ∫ t : ℝ, F (b + t * I) := by
  let H (t : ℝ) := ∫ u : ℝ in a..b, F (u + t * I)
  let V (c t : ℝ) := ∫ u : ℝ in -t..t, F (c + u * I)
  have hv (c : ℝ) (hc : c ∈ Icc a b) : Tendsto (V c) atTop (𝓝 (∫ t : ℝ, F (c + t * I))) := by
    apply intervalIntegral_tendsto_integral _ tendsto_neg_atTop_atBot tendsto_id
    apply hD.vertical hc
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hd _ (by simpa using hc)).continuousAt.comp (f := fun y : ℝ => (c : ℂ) + y * I) (by fun_prop)
  obtain ⟨C, _, hC⟩ := hD
  have hbound (t : ℝ) : ‖H t‖ ≤ C / (1 + t ^ 2) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    have hu' : u ∈ Icc a b := Ioc_subset_Icc_self ((uIoc_of_le hab) ▸ hu)
    apply (le_div_iff₀ (by positivity)).2
    simpa [mul_comm] using hC ((u : ℂ) + t * I) (by simpa using hu')
  have hlim : Tendsto (fun t : ℝ => C / (1 + t ^ 2) * |b - a|) atTop (𝓝 0) := by
    have hpow : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by decide))
    simpa using (tendsto_const_nhds (x := C) |>.div_atTop hpow).mul_const |b - a|
  have htop : Tendsto H atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound hlim)
  have hbot : Tendsto (fun t => H (-t)) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) (fun t => by simpa using hbound (-t)) hlim)
  have hrect (t : ℝ) : H (-t) - H t + I * V b t - I * V a t = 0 := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn F (⟨a, -t⟩ : ℂ) (⟨b, t⟩ : ℂ)
      (fun s hs => (hd s (by simpa [uIcc_of_le hab] using hs.1)).differentiableWithinAt)
    simpa only [H, V, smul_eq_mul] using h
  have hLimit := (((hbot.sub htop).add (tendsto_const_nhds (x := I) |>.mul (hv b ⟨hab, le_rfl⟩))).sub
    (tendsto_const_nhds (x := I) |>.mul (hv a ⟨le_rfl, hab⟩)))
  have hEq := tendsto_nhds_unique (hLimit.congr hrect) (tendsto_const_nhds (x := (0 : ℂ)))
  have hmul : I * (∫ t : ℝ, F (b + t * I)) = I * (∫ t : ℝ, F (a + t * I)) :=
    sub_eq_zero.mp (by simpa only [sub_zero, zero_add] using hEq)
  exact (mul_left_cancel₀ I_ne_zero hmul).symm

theorem inv_shift (K : Type*) [Field K] [NumberField K] {a b x : ℝ}
    (ha : 1 < a) (hb : 1 < b) (hx : 0 < x) :
    mellinInv a (completion K) x = mellinInv b (completion K) x := by
  suffices ordered : ∀ {u v : ℝ}, 1 < u → u ≤ v → mellinInv u (completion K) x = mellinInv v (completion K) x by
    rcases le_total a b with h | h
    · exact ordered ha h
    · exact (ordered hb h).symm
  intro u v hu huv
  let W (s : ℂ) := (x : ℂ) ^ (-s)
  have hdW : Differentiable ℂ W := differentiable_neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  have hW : StripBound u v W := by
    obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (K := Icc u v) (f := fun r : ℝ => x ^ (-r))
      (by fun_prop (disch := positivity))
    refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
    dsimp only [W]
    rw [norm_cpow_eq_rpow_re_of_pos hx, neg_re]
    exact (hC (mem_image_of_mem (fun r : ℝ => x ^ (-r)) hs)).trans (le_max_left _ _)
  have hD := (completion_decay K hu (b := v)).mul_bound hW
  have hs := vertical_integral_shift (F := fun s => completion K s * W s) huv
    (fun s hs => (completion_differentiableAt K (hu.trans_le hs.1)).mul (hdW s)) hD
  unfold mellinInv
  congr 1
  simpa only [smul_eq_mul, mul_comm (W _) _, W] using hs

noncomputable abbrev kernel (K : Type*) [Field K] [NumberField K] := mellinInv 2 (completion K)

noncomputable abbrev line (K : Type*) [Field K] [NumberField K] (σ y : ℝ) :=
  completion K ((σ : ℂ) + (2 : ℂ) * (Real.pi : ℂ) * (y : ℂ) * I)

theorem line_integrable (K : Type*) [Field K] [NumberField K] {σ : ℝ} (hσ : 1 < σ) :
    Integrable (line K σ) := by
  have hc : 2 * Real.pi ≠ 0 := by positivity
  have h := (completion_vertical K hσ).comp_mul_right' hc
  change Integrable (fun y : ℝ => completion K ((σ : ℂ) + (2 : ℂ) * Real.pi * y * I))
  convert h using 1
  ext1 y
  congr 1
  push_cast
  ring

theorem line_continuous (K : Type*) [Field K] [NumberField K] {σ : ℝ} (hσ : 1 < σ) :
    Continuous (line K σ) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  apply (completion_differentiableAt K (s := σ + 2 * Real.pi * y * I) (by simpa using hσ)).continuousAt.comp
    (f := fun t : ℝ => (σ : ℂ) + 2 * Real.pi * t * I)
  fun_prop

theorem kernel_local (K : Type*) [Field K] [NumberField K] :
    LocallyIntegrableOn (kernel K) (Ioi 0) := by
  have hF : Continuous (𝓕 (line K 2)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ (line_integrable K (by norm_num))
  have hFi : Continuous (𝓕⁻ (line K 2)) := by
    simpa only [← Real.fourierInv_eq_fourier_neg, Function.comp_def] using hF.comp continuous_neg
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  apply ContinuousOn.congr (f := fun x : ℝ => (x : ℂ) ^ (-(2 : ℂ)) • 𝓕⁻ (line K 2) (-Real.log x))
  · apply continuousOn_of_forall_continuousAt
    intro x hx
    apply ContinuousAt.fun_smul
    · exact (continuousAt_cpow_const (ofReal_mem_slitPlane.2 hx)).comp (f := fun t : ℝ => (t : ℂ)) continuous_ofReal.continuousAt
    · exact hFi.continuousAt.comp (f := fun t : ℝ => -Real.log t) (Real.continuousAt_log hx.ne').neg
  · intro x hx
    unfold kernel line
    simpa only [ofReal_ofNat, ofReal_neg] using mellinInv_eq_fourierInv 2 (completion K) hx

theorem kernel_bound (K : Type*) [Field K] [NumberField K] {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖kernel K x‖ ≤ C * x ^ (-σ) := by
  let l (y : ℝ) := completion K (σ + y * I)
  let c := ‖(1 / (2 * Real.pi) : ℝ)‖
  refine ⟨c * ∫ y, ‖l y‖, mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _), fun x hx => ?_⟩
  rw [kernel, inv_shift K (by norm_num) hσ hx, mellinInv, norm_smul]
  have h := norm_integral_le_integral_norm (μ := volume) (fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I)) • l y)
  have hn (y : ℝ) : ‖(x : ℂ) ^ (-((σ : ℂ) + y * I)) • l y‖ = x ^ (-σ) * ‖l y‖ := by
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hx]; simp
  simp_rw [hn, integral_const_mul] at h
  calc _ ≤ c * (x ^ (-σ) * ∫ y, ‖l y‖) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
       _ = _ := by ring

theorem kernel_decay (K : Type*) [Field K] [NumberField K] (r : ℝ) :
    kernel K =O[atTop] (fun x : ℝ => x ^ r) := by
  let σ := max (2 : ℝ) (-r)
  obtain ⟨C, hC, hb⟩ := kernel_bound K (σ := σ) (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _))
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)]
  apply (hb x (zero_lt_one.trans_le hx)).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.rpow_le_rpow_of_exponent_le hx (by dsimp [σ]; linarith [le_max_right (2 : ℝ) (-r)])

theorem kernel_convergent (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (kernel K) s := by
  let b := (s.re + 1) / 2
  have hb : 1 < b := by dsimp [b]; linarith
  obtain ⟨C, _, h⟩ := kernel_bound K hb
  refine mellinConvergent_of_isBigO_rpow (kernel_local K) (kernel_decay K (-(s.re + 1))) (by linarith) ?_ (b := b) (by dsimp [b]; linarith)
  refine IsBigO.of_bound C ?_
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with x hx
  simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hx) _)] using h x hx

theorem log_integrable {f : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f σ) :
    Integrable (fun u : ℝ => Real.exp (-σ * u) • f (Real.exp (-u))) := by
  have hr : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  rw [MellinConvergent, ← hr, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn, integrableOn_univ] at hf
  have hpos : Integrable (fun u : ℝ => Real.exp (u * σ) • f (Real.exp u)) := by
    apply hf.congr
    filter_upwards with u
    rw [abs_of_pos (Real.exp_pos _)]
    have heq : ((Real.exp u : ℂ) ^ ((σ : ℂ) - 1)) = (Real.exp (u * (σ - 1)) : ℝ) := by
      rw [← ofReal_one, ← ofReal_sub, ← ofReal_cpow (Real.exp_pos u).le, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [heq, Complex.coe_smul, smul_smul, ← Real.exp_add]
    congr 2; ring
  simpa [mul_comm σ, neg_mul] using hpos.comp_mul_right' (R := -1) (by norm_num)

theorem kernel_hasMellin (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    HasMellin (kernel K) s (completion K s) := by
  refine ⟨kernel_convergent K hs, ?_⟩
  let σ := s.re
  let g (u : ℝ) := Real.exp (-σ * u) • kernel K (Real.exp (-u))
  have hg : Integrable g := log_integrable (kernel_convergent K (s := σ) hs)
  have hform : g = 𝓕⁻ (line K σ) := by
    funext u
    dsimp only [g, kernel]
    rw [inv_shift K (by norm_num) hs (Real.exp_pos _), mellinInv_eq_fourierInv _ _ (Real.exp_pos _), Real.log_exp, neg_neg]
    change Real.exp (-σ * u) • ((↑(Real.exp (-u)) : ℂ) ^ (-(σ : ℂ)) • 𝓕⁻ (line K σ) u) = _
    have heq : ((Real.exp (-u) : ℂ) ^ (-(σ : ℂ))) = (Real.exp (σ * u) : ℝ) := by
      rw [← ofReal_neg, ← ofReal_cpow (Real.exp_pos _).le, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 2; ring
    rw [heq, Complex.coe_smul, smul_smul, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, one_smul]
  have hfg : Integrable (𝓕 (line K σ)) := by
    have hneg := hg.comp_mul_right' (R := -1) (by norm_num)
    simpa [hform, Real.fourierInv_eq_fourier_neg] using hneg
  have hinv := (line_continuous K hs).fourier_fourierInv_eq (line_integrable K hs) hfg
  rw [mellin_eq_fourier]
  change 𝓕 g (s.im / (2 * Real.pi)) = _
  rw [hform, hinv]
  unfold line
  congr 1
  have ht : (2 : ℝ) * Real.pi * (s.im / (2 * Real.pi)) = s.im := by field_simp
  have htC : (2 : ℂ) * Real.pi * ((s.im / (2 * Real.pi) : ℝ) : ℂ) = (s.im : ℂ) := by exact_mod_cast ht
  rw [htC, Complex.re_add_im]

end DedekindMellin

theorem OMA.solution : OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1.H1 := by
  intro K _ _ _
  exact ⟨DedekindMellin.kernel_local K, DedekindMellin.kernel_decay K,
    fun s hs => DedekindMellin.kernel_hasMellin K hs⟩

