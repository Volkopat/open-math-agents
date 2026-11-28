import OMAReductions.R_Erdos967_erdos_967_variants_tauberian_R1
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion

/-! Wiener Tauberian theorem for the discrete Erdős–Ingham measure. -/

namespace OMA_Erdos967_H1

open Filter Set Real MeasureTheory Complex Erdos967
open scoped Topology FourierTransform Convolution

/- Section 1: Elementary tsum, Fourier, and convolution helpers -/

private lemma fourier_eq_mul (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ x : ℝ, (Real.fourierChar (-(x * ξ)) : ℂ) * f x := by
  rw [Real.fourier_eq]
  congr 1 with x
  simp [Circle.smul_def, mul_comm]

private lemma fourierInv_eq_mul (f : ℝ → ℂ) (x : ℝ) :
    𝓕⁻ f x = ∫ ξ : ℝ, (Real.fourierChar (x * ξ) : ℂ) * f ξ := by
  rw [Real.fourierInv_eq]
  congr 1 with ξ

private lemma fourier_char_mul (a b : ℝ) :
    (Real.fourierChar a : ℂ) * (Real.fourierChar b : ℂ) = (Real.fourierChar (a + b) : ℂ) := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]

private lemma norm_fourierChar_coe (t : ℝ) : ‖(Real.fourierChar t : ℂ)‖ = 1 :=
  Circle.norm_coe (Real.fourierChar t)

private lemma continuous_fourierChar_coe : Continuous (fun t : ℝ => (Real.fourierChar t : ℂ)) :=
  continuous_subtype_val.comp Real.continuous_fourierChar

private lemma integrable_fourier_mul {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun x : ℝ => (Real.fourierChar (-(x * ξ)) : ℂ) * f x) := by
  have h := (Real.fourierIntegral_convergent_iff ξ).2 hf
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [Circle.smul_def, mul_comm]

private lemma integral_complex_ofReal' (f : ℝ → ℝ) :
    (∫ x : ℝ, (f x : ℂ)) = ((∫ x : ℝ, f x : ℝ) : ℂ) := by
  simpa using (integral_ofReal (𝕜 := ℂ) (f := f) (μ := volume))

private lemma continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

private lemma integrable_tsum_of_summable_norm
    {F : ℕ → ℝ → ℂ} (hF : ∀ n, Integrable (F n))
    (hpt : ∀ x, Summable (fun n => ‖F n x‖))
    (hsum : Summable (fun n => ∫ x, ‖F n x‖)) :
    Integrable (fun x => ∑' n, F n x) := by
  refine ⟨?_, ?_⟩
  · have hmeas : ∀ N : ℕ, AEStronglyMeasurable (fun x => ∑ n ∈ Finset.range N, F n x) volume :=
      fun N => Finset.aestronglyMeasurable_fun_sum _ (fun n _ => (hF n).1)
    refine aestronglyMeasurable_of_tendsto_ae atTop hmeas ?_
    filter_upwards with x
    exact ((hpt x).of_norm).hasSum.tendsto_sum_nat
  · rw [hasFiniteIntegral_iff_enorm]
    have hle : ∫⁻ x, ‖∑' n, F n x‖ₑ ≤ ∫⁻ x, ∑' n, ‖F n x‖ₑ := by
      refine lintegral_mono fun x => ?_
      have h1 : ‖∑' n, F n x‖ ≤ ∑' n, ‖F n x‖ := norm_tsum_le_tsum_norm (hpt x)
      calc ‖∑' n, F n x‖ₑ
          = ENNReal.ofReal ‖∑' n, F n x‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (∑' n, ‖F n x‖) := ENNReal.ofReal_le_ofReal h1
        _ = ∑' n, ENNReal.ofReal ‖F n x‖ :=
            ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) (hpt x)
        _ = ∑' n, ‖F n x‖ₑ := by simp_rw [ofReal_norm]
    refine hle.trans_lt ?_
    rw [lintegral_tsum (fun n => (hF n).1.enorm)]
    have hterm : ∀ n, ∫⁻ x, ‖F n x‖ₑ = ENNReal.ofReal (∫ x, ‖F n x‖) := fun n =>
      (ofReal_integral_norm_eq_lintegral_enorm (hF n)).symm
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun x => norm_nonneg _) hsum]
    exact ENNReal.ofReal_lt_top

private lemma integral_norm_tsum_le
    {F : ℕ → ℝ → ℂ} (hF : ∀ n, Integrable (F n))
    (hpt : ∀ x, Summable (fun n => ‖F n x‖))
    (hsum : Summable (fun n => ∫ x, ‖F n x‖)) :
    ∫ x, ‖∑' n, F n x‖ ≤ ∑' n, ∫ x, ‖F n x‖ := by
  have hint_sum : Integrable (fun x => ∑' n, ‖F n x‖) := by
    have h1 := integrable_tsum_of_summable_norm
      (F := fun n x => (‖F n x‖ : ℂ))
      (fun n => (hF n).norm.ofReal)
      (fun x => by simpa using hpt x)
      (by simpa using hsum)
    have h2 : (fun x => ‖∑' n, (‖F n x‖ : ℂ)‖) = fun x => ∑' n, ‖F n x‖ := by
      ext x
      rw [← Complex.ofReal_tsum, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun n => norm_nonneg _)]
    simpa [h2] using h1.norm
  calc ∫ x, ‖∑' n, F n x‖
      ≤ ∫ x, ∑' n, ‖F n x‖ :=
        integral_mono (integrable_tsum_of_summable_norm hF hpt hsum).norm hint_sum
          (fun x => norm_tsum_le_tsum_norm (hpt x))
    _ = ∑' n, ∫ x, ‖F n x‖ :=
        (integral_tsum_of_summable_integral_norm (fun n => (hF n).norm)
          (by simpa using hsum)).symm

private noncomputable def conv (f g : ℝ → ℂ) : ℝ → ℂ :=
  f ⋆[ContinuousLinearMap.mul ℂ ℂ] g

private lemma conv_eq (f g : ℝ → ℂ) (x : ℝ) :
    conv f g x = ∫ t, f t * g (x - t) := rfl

private lemma conv_eq_swap (f g : ℝ → ℂ) (x : ℝ) :
    conv f g x = ∫ t, f (x - t) * g t :=
  convolution_mul_swap (f := f) (g := g) (μ := volume)

private lemma conv_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (conv f g) :=
  hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg

private lemma conv_continuous_left {f g : ℝ → ℂ} {C : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ C) (hf : Continuous f) (hg : Integrable g) :
    Continuous (conv f g) :=
  BddAbove.continuous_convolution_left_of_integrable (ContinuousLinearMap.mul ℂ ℂ)
    ⟨C, by rintro _ ⟨x, rfl⟩; exact hb x⟩ hf hg

private lemma conv_norm_le_left' {f g : ℝ → ℂ} {C : ℝ}
    (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ C) (hg : Integrable g) (x : ℝ) :
    ‖conv f g x‖ ≤ C * ∫ t, ‖g t‖ := by
  rw [conv_eq_swap]
  have hint : Integrable (fun t => f (x - t) * g t) := by
    refine (hg.norm.const_mul (max C 0)).mono' ?_ ?_
    · exact (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hg.aestronglyMeasurable
    · filter_upwards with t
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((hb (x - t)).trans (le_max_left _ _)) (norm_nonneg _)
  calc ‖∫ t, f (x - t) * g t‖
      ≤ ∫ t, ‖f (x - t) * g t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, C * ‖g t‖ := integral_mono hint.norm (hg.norm.const_mul C) fun t => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hb (x - t)) (norm_nonneg _)
    _ = C * ∫ t, ‖g t‖ := integral_const_mul _ _

private lemma conv_integral_norm_le {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ x, ‖conv f g x‖ ≤ (∫ x, ‖f x‖) * (∫ x, ‖g x‖) := by
  have hprod : Integrable (fun p : ℝ × ℝ => ‖f (p.1 - p.2)‖ * ‖g p.2‖) (volume.prod volume) := by
    simpa [mul_comm] using hg.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hf.norm
  have hint_inner : Integrable (fun x => ∫ y, ‖f (x - y)‖ * ‖g y‖) := hprod.integral_prod_left
  calc ∫ x, ‖conv f g x‖
      ≤ ∫ x, ∫ y, ‖f (x - y)‖ * ‖g y‖ := by
        refine integral_mono (conv_integrable hf hg).norm hint_inner fun x => ?_
        rw [conv_eq_swap]
        calc ‖∫ y, f (x - y) * g y‖
            ≤ ∫ y, ‖f (x - y) * g y‖ := norm_integral_le_integral_norm _
          _ = ∫ y, ‖f (x - y)‖ * ‖g y‖ := by simp_rw [norm_mul]
    _ = ∫ y, ∫ x, ‖f (x - y)‖ * ‖g y‖ := integral_integral_swap hprod
    _ = ∫ y, (∫ x, ‖f x‖) * ‖g y‖ := by
        congr 1 with y
        rw [integral_mul_const, integral_sub_right_eq_self (fun x => ‖f x‖) y]
    _ = (∫ x, ‖f x‖) * (∫ y, ‖g y‖) := integral_const_mul _ _

private lemma fourier_conv {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (conv f g) ξ = 𝓕 f ξ * 𝓕 g ξ :=
  Real.fourier_mul_convolution_eq hf hg ξ

/- Section 2: Tent function and Fejer kernel -/

private def tent (ξ : ℝ) : ℝ := max 0 (1 - |ξ|)

private lemma tent_continuous : Continuous tent :=
  continuous_const.max (continuous_const.sub continuous_abs)

private lemma tent_eq_zero_of_one_le {ξ : ℝ} (h : 1 ≤ |ξ|) : tent ξ = 0 := by
  simp only [tent, max_eq_left_iff]
  linarith

private lemma tent_nonneg (ξ : ℝ) : 0 ≤ tent ξ := le_max_left _ _

private lemma tent_neg (ξ : ℝ) : tent (-ξ) = tent ξ := by simp [tent]

private lemma tent_integrable : Integrable (fun ξ : ℝ => (tent ξ : ℂ)) := by
  have hcs : HasCompactSupport (fun ξ : ℝ => (tent ξ : ℂ)) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) ?_
    intro ξ hξ
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] at hξ
    by_contra hmem
    rw [mem_Icc, not_and_or] at hmem
    have habs : 1 ≤ |ξ| := by
      rcases hmem with h1 | h2
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact hξ (tent_eq_zero_of_one_le habs)
  exact (Complex.continuous_ofReal.comp tent_continuous).integrable_of_hasCompactSupport hcs

private noncomputable def fejer (x : ℝ) : ℝ :=
  if x = 0 then 1 else (Real.sin (π * x) / (π * x)) ^ 2

private lemma fejer_nonneg (x : ℝ) : 0 ≤ fejer x := by
  unfold fejer
  split_ifs
  · exact zero_le_one
  · exact sq_nonneg _

private lemma fejer_le_one (x : ℝ) : fejer x ≤ 1 := by
  unfold fejer
  split_ifs with h
  · exact le_rfl
  · have hpi : π * x ≠ 0 := mul_ne_zero pi_ne_zero h
    have habs : |Real.sin (π * x) / (π * x)| ≤ 1 := by
      rw [abs_div, div_le_one (abs_pos.mpr hpi)]
      exact Real.abs_sin_le_abs
    nlinarith [sq_abs (Real.sin (π * x) / (π * x)), abs_nonneg (Real.sin (π * x) / (π * x))]

private lemma fejer_le_two_div_one_add_sq (x : ℝ) : fejer x ≤ 2 / (1 + x ^ 2) := by
  by_cases hx : |x| ≤ 1
  · have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
    calc fejer x ≤ 1 := fejer_le_one x
      _ ≤ 2 / (1 + x ^ 2) := by rw [le_div_iff₀ (by positivity)]; linarith
  · push Not at hx
    have hx0 : x ≠ 0 := fun h => by rw [h, abs_zero] at hx; linarith
    have h1 : 1 < x ^ 2 := by nlinarith [sq_abs x]
    have hpi : 2 < π := by linarith [Real.pi_gt_three]
    have hpi2 : 4 < π ^ 2 := by nlinarith
    have hsin : (Real.sin (π * x)) ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (π * x), sq_nonneg (Real.cos (π * x))]
    rw [fejer, if_neg hx0, div_pow]
    calc (Real.sin (π * x)) ^ 2 / (π * x) ^ 2
        ≤ 1 / (π * x) ^ 2 := div_le_div_of_nonneg_right hsin (sq_nonneg _)
      _ ≤ 2 / (1 + x ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hsq : (π * x) ^ 2 = π ^ 2 * x ^ 2 := by ring
          nlinarith [sq_nonneg x]

private lemma fejer_continuous : Continuous fejer := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [ContinuousAt, fejer, if_pos rfl]
    have hderiv : HasDerivAt Real.sin (Real.cos 0) 0 := Real.hasDerivAt_sin 0
    rw [Real.cos_zero, hasDerivAt_iff_tendsto_slope_zero] at hderiv
    have hslope : Tendsto (fun t : ℝ => Real.sin t / t) (𝓝[≠] 0) (𝓝 1) := by
      simpa [div_eq_inv_mul, Real.sin_zero] using hderiv
    have hmul : Tendsto (fun t : ℝ => π * t) (𝓝[≠] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have hc : Continuous (fun t : ℝ => π * t) := continuous_const.mul continuous_id
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_ne_zero pi_ne_zero ht
    have hsq : Tendsto (fun t : ℝ => (Real.sin (π * t) / (π * t)) ^ 2) (𝓝[≠] 0) (𝓝 1) := by
      simpa using (hslope.comp hmul).pow 2
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.tendsto_nhdsWithin_nhds.mp hsq ε hε
    refine Filter.eventually_iff.mpr (Metric.mem_nhds_iff.mpr ⟨δ, hδ, fun y hy => ?_⟩)
    by_cases hy0 : y = 0
    · subst hy0; simp [fejer, hε]
    · simpa [fejer, hy0] using hball hy0 hy
  · have hcont : ContinuousAt (fun t : ℝ => (Real.sin (π * t) / (π * t)) ^ 2) x := by
      have hne : π * x ≠ 0 := mul_ne_zero pi_ne_zero hx
      fun_prop (disch := assumption)
    refine hcont.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    simp [fejer, hy]

private lemma fejer_integrable : Integrable fejer := by
  refine (integrable_inv_one_add_sq.const_mul 2).mono' fejer_continuous.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (fejer_nonneg x)]
  simpa [div_eq_mul_inv] using fejer_le_two_div_one_add_sq x

private lemma fourierInv_tent (x : ℝ) :
    𝓕⁻ (fun ξ : ℝ => (tent ξ : ℂ)) x = (fejer x : ℂ) := by
  rw [fourierInv_eq_mul]
  have hzero : ∀ ξ, ξ ∉ Ioc (-1 : ℝ) 1 → (Real.fourierChar (x * ξ) : ℂ) * (tent ξ : ℂ) = 0 := by
    intro ξ hξ
    rw [mem_Ioc, not_and_or] at hξ
    have habs : 1 ≤ |ξ| := by
      rcases hξ with h1 | h2
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    simp [tent_eq_zero_of_one_le habs]
  have h1 : (∫ ξ : ℝ, (Real.fourierChar (x * ξ) : ℂ) * (tent ξ : ℂ)) =
      ∫ ξ in (-1 : ℝ)..1, (Real.fourierChar (x * ξ) : ℂ) * (tent ξ : ℂ) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [← integral_indicator measurableSet_Ioc]
    congr 1 with ξ
    by_cases hξ : ξ ∈ Ioc (-1 : ℝ) 1
    · simp [hξ]
    · simp [hξ, hzero ξ hξ]
  rw [h1]
  have hcont : Continuous (fun ξ : ℝ => (Real.fourierChar (x * ξ) : ℂ) * (tent ξ : ℂ)) :=
    (continuous_fourierChar_coe.comp (continuous_const.mul continuous_id)).mul
      (Complex.continuous_ofReal.comp tent_continuous)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-1) 0) (hcont.intervalIntegrable 0 1)]
  have hleft : (∫ ξ in (-1 : ℝ)..0, (Real.fourierChar (x * ξ) : ℂ) * (tent ξ : ℂ)) =
      ∫ ξ in (0 : ℝ)..1, (Real.fourierChar (-(x * ξ)) : ℂ) * (tent ξ : ℂ) := by
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fun ξ : ℝ => (Real.fourierChar (x * ξ) : ℂ) * (tent ξ : ℂ)) (a := (0 : ℝ)) (b := 1)
    simp only [neg_zero] at hcomp
    rw [← hcomp]
    congr 1 with ξ
    rw [mul_neg, tent_neg]
  have hcont_neg : Continuous (fun ξ : ℝ => (Real.fourierChar (-(x * ξ)) : ℂ) * (tent ξ : ℂ)) :=
    (continuous_fourierChar_coe.comp (continuous_const.mul continuous_id).neg).mul
      (Complex.continuous_ofReal.comp tent_continuous)
  rw [hleft, ← intervalIntegral.integral_add (hcont_neg.intervalIntegrable 0 1)
    (hcont.intervalIntegrable 0 1)]
  have hintegrand : ∀ ξ ∈ Icc (0 : ℝ) 1,
      (Real.fourierChar (-(x * ξ)) : ℂ) * (tent ξ : ℂ) +
      (Real.fourierChar (x * ξ) : ℂ) * (tent ξ : ℂ) =
      ((2 * (1 - ξ) * Real.cos (2 * π * x * ξ) : ℝ) : ℂ) := by
    intro ξ hξ
    have htent : tent ξ = 1 - ξ := by
      rw [tent, abs_of_nonneg hξ.1, max_eq_right (by linarith [hξ.2])]
    rw [htent, ← add_mul]
    simp only [Real.fourierChar_apply]
    have hcos : Complex.exp (2 * π * I * (-(x * ξ) : ℝ)) + Complex.exp (2 * π * I * (x * ξ : ℝ)) =
        ((2 * Real.cos (2 * π * x * ξ) : ℝ) : ℂ) := by
      push_cast
      rw [Complex.cos]
      have harg1 : 2 * ↑π * I * -(↑x * ↑ξ) = -(2 * ↑π * ↑x * ↑ξ * I) := by ring
      have harg2 : 2 * ↑π * I * (↑x * ↑ξ) = 2 * ↑π * ↑x * ↑ξ * I := by ring
      rw [harg1, harg2]
      ring
    have hcoe1 : (Complex.exp (↑(2 * π * -(x * ξ)) * I)) = Complex.exp (2 * π * I * (-(x * ξ) : ℝ)) := by
      congr 1; push_cast; ring
    have hcoe2 : (Complex.exp (↑(2 * π * (x * ξ)) * I)) = Complex.exp (2 * π * I * (x * ξ : ℝ)) := by
      congr 1; push_cast; ring
    rw [hcoe1, hcoe2, hcos]
    push_cast
    ring
  have hreal : (∫ ξ in (0 : ℝ)..1,
      ((Real.fourierChar (-(x * ξ)) : ℂ) * (tent ξ : ℂ) +
        (Real.fourierChar (x * ξ) : ℂ) * (tent ξ : ℂ))) =
      ((∫ ξ in (0 : ℝ)..1, 2 * (1 - ξ) * Real.cos (2 * π * x * ξ) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun ξ hξ => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hξ
    exact hintegrand ξ hξ
  rw [hreal]
  congr 1
  by_cases hx : x = 0
  · subst hx
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one, fejer]
    have hprim : ∀ ξ ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => 2 * t - t ^ 2) (2 * (1 - ξ)) ξ := fun ξ _ => by
      have hd : HasDerivAt (fun t : ℝ => 2 * t - t ^ 2) (2 * 1 - ↑(2 : ℕ) * ξ ^ (2 - 1)) ξ :=
        ((hasDerivAt_id ξ).const_mul (2 : ℝ)).fun_sub (hasDerivAt_pow 2 ξ)
      rw [show (2 : ℝ) * (1 - ξ) = 2 * 1 - ↑(2 : ℕ) * ξ ^ (2 - 1) by norm_num; ring]
      exact hd
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprim
      ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable 0 1)]
    norm_num
  · rw [fejer, if_neg hx]
    let c : ℝ := π * x
    have hc : c ≠ 0 := mul_ne_zero pi_ne_zero hx
    let P : ℝ → ℝ := fun ξ =>
      (1 - ξ) * Real.sin (2 * c * ξ) / c - Real.cos (2 * c * ξ) / (2 * c ^ 2)
    have hP : ∀ ξ ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt P (2 * (1 - ξ) * Real.cos (2 * π * x * ξ)) ξ := fun ξ _ => by
      have hlin : HasDerivAt (fun t : ℝ => 2 * c * t) (2 * c) ξ := by
        simpa using (hasDerivAt_id ξ).const_mul (2 * c)
      have hsub1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) ξ := by
        have h := (hasDerivAt_const ξ (1 : ℝ)).fun_sub (hasDerivAt_id ξ)
        rw [show (-1 : ℝ) = 0 - 1 by norm_num]
        exact h
      have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * c * t)) (Real.cos (2 * c * ξ) * (2 * c)) ξ :=
        (Real.hasDerivAt_sin (2 * c * ξ)).comp ξ hlin
      have hcos' : HasDerivAt (fun t : ℝ => Real.cos (2 * c * t)) (-Real.sin (2 * c * ξ) * (2 * c)) ξ :=
        (Real.hasDerivAt_cos (2 * c * ξ)).comp ξ hlin
      have hd1 : HasDerivAt (fun t : ℝ => (1 - t) * Real.sin (2 * c * t))
          ((-1) * Real.sin (2 * c * ξ) + (1 - ξ) * (Real.cos (2 * c * ξ) * (2 * c))) ξ :=
        hsub1.fun_mul hsin
      have hd := (hd1.div_const c).fun_sub (hcos'.div_const (2 * c ^ 2))
      have heq_deriv : 2 * (1 - ξ) * Real.cos (2 * π * x * ξ) =
          ((-1) * Real.sin (2 * c * ξ) + (1 - ξ) * (Real.cos (2 * c * ξ) * (2 * c))) / c -
          (-Real.sin (2 * c * ξ) * (2 * c)) / (2 * c ^ 2) := by
        have hc2 : 2 * π * x * ξ = 2 * c * ξ := by dsimp [c]; ring
        rw [hc2]
        field_simp [hc]
        ring
      rw [heq_deriv]
      exact hd
    have hcont_int : Continuous (fun ξ : ℝ => 2 * (1 - ξ) * Real.cos (2 * π * x * ξ)) := by
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hP (hcont_int.intervalIntegrable 0 1)]
    dsimp [P, c]
    simp only [sub_self, zero_mul, zero_div, mul_zero, Real.sin_zero, Real.cos_zero, sub_zero, zero_sub]
    have hcos2 : Real.cos (2 * (π * x) * 1) = 1 - 2 * Real.sin (π * x) ^ 2 := by
      rw [mul_one, Real.cos_two_mul']
      nlinarith [Real.sin_sq_add_cos_sq (π * x)]
    rw [hcos2]
    field_simp [hc]
    ring

private lemma fourier_tent (x : ℝ) :
    𝓕 (fun ξ : ℝ => (tent ξ : ℂ)) x = (fejer x : ℂ) := by
  have h : 𝓕 (fun ξ : ℝ => (tent ξ : ℂ)) x = 𝓕⁻ (fun ξ : ℝ => (tent ξ : ℂ)) (-x) := by
    rw [fourier_eq_mul, fourierInv_eq_mul]
    congr 1 with ξ
    ring_nf
  rw [h, fourierInv_tent]
  congr 1
  unfold fejer
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx, neg_ne_zero.mpr hx, mul_neg, Real.sin_neg]

private lemma fourier_fejer (ξ : ℝ) :
    𝓕 (fun x : ℝ => (fejer x : ℂ)) ξ = (tent ξ : ℂ) := by
  have hinv := Continuous.fourier_fourierInv_eq
    (f := fun t : ℝ => (tent t : ℂ))
    (Complex.continuous_ofReal.comp tent_continuous)
    tent_integrable
    (by
      have heq : 𝓕 (fun t : ℝ => (tent t : ℂ)) = fun t : ℝ => (fejer t : ℂ) := funext fourier_tent
      rw [heq]
      exact fejer_integrable.ofReal)
  have heq : 𝓕⁻ (fun t : ℝ => (tent t : ℂ)) = fun t : ℝ => (fejer t : ℂ) := funext fourierInv_tent
  rw [heq] at hinv
  exact congrFun hinv ξ

private lemma integral_fejer : ∫ x : ℝ, fejer x = 1 := by
  have h := fourier_fejer 0
  rw [fourier_eq_mul] at h
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul, tent, abs_zero, sub_zero,
    max_eq_right (zero_le_one : (0 : ℝ) ≤ 1), Complex.ofReal_one] at h
  rw [integral_complex_ofReal'] at h
  exact Complex.ofReal_injective h

private lemma tendsto_fejer_translate :
    Tendsto (fun h : ℝ => ∫ x : ℝ, |fejer (x - h) - fejer x|) (𝓝 0) (𝓝 0) := by
  have h0 : (0 : ℝ) = ∫ x : ℝ, (0 : ℝ) := by simp
  nth_rewrite 2 [h0]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => 10 / (1 + x ^ 2)) ?_ ?_ ?_ ?_
  · filter_upwards with h
    exact (fejer_continuous.comp (continuous_id.sub continuous_const) |>.sub fejer_continuous).abs.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with h hh
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_abs]
    have hsq : 1 + x ^ 2 ≤ 4 * (1 + (x - h) ^ 2) := by
      have hh2 : h ^ 2 ≤ 1 := by nlinarith [sq_abs h, abs_nonneg h]
      nlinarith [sq_nonneg (3 * x - 4 * h)]
    have h1 : fejer (x - h) ≤ 8 / (1 + x ^ 2) := by
      calc fejer (x - h) ≤ 2 / (1 + (x - h) ^ 2) := fejer_le_two_div_one_add_sq (x - h)
        _ ≤ 8 / (1 + x ^ 2) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            linarith
    have h2 : fejer x ≤ 2 / (1 + x ^ 2) := fejer_le_two_div_one_add_sq x
    have htri : |fejer (x - h) - fejer x| ≤ fejer (x - h) + fejer x := by
      have := abs_sub (fejer (x - h)) (fejer x)
      rw [abs_of_nonneg (fejer_nonneg _), abs_of_nonneg (fejer_nonneg _)] at this
      exact this
    have hsum10 : 8 / (1 + x ^ 2) + 2 / (1 + x ^ 2) = 10 / (1 + x ^ 2) := by ring
    linarith
  · simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul (10 : ℝ)
  · filter_upwards with x
    have hlim : Tendsto (fun h : ℝ => |fejer (x - h) - fejer x|) (𝓝 0) (𝓝 |fejer (x - 0) - fejer x|) :=
      ((fejer_continuous.comp (continuous_const.sub continuous_id)).sub continuous_const).abs.continuousAt.tendsto
    simpa using hlim

private noncomputable def K (lam : ℝ) (x : ℝ) : ℝ := lam * fejer (lam * x)

private lemma K_nonneg {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : 0 ≤ K lam x :=
  mul_nonneg hlam.le (fejer_nonneg _)

private lemma K_le {lam : ℝ} (hlam : 0 < lam) (x : ℝ) : K lam x ≤ lam := by
  simpa [K] using mul_le_mul_of_nonneg_left (fejer_le_one (lam * x)) hlam.le

private lemma K_continuous (lam : ℝ) : Continuous (K lam) :=
  continuous_const.mul (fejer_continuous.comp (continuous_const.mul continuous_id))

private lemma K_integrable {lam : ℝ} (hlam : 0 < lam) : Integrable (K lam) :=
  (fejer_integrable.comp_mul_left' hlam.ne').const_mul lam

private lemma integral_K {lam : ℝ} (hlam : 0 < lam) : ∫ x : ℝ, K lam x = 1 := by
  unfold K
  rw [integral_const_mul, Measure.integral_comp_mul_left _ lam, abs_inv, abs_of_pos hlam,
    integral_fejer, smul_eq_mul]
  field_simp [hlam.ne']

private lemma fourier_K {lam : ℝ} (hlam : 0 < lam) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (K lam x : ℂ)) ξ = (tent (ξ / lam) : ℂ) := by
  rw [fourier_eq_mul]
  have h1 : (∫ x : ℝ, (Real.fourierChar (-(x * ξ)) : ℂ) * (K lam x : ℂ)) =
      (lam : ℂ) * ∫ x : ℝ, (Real.fourierChar (-(lam * x * (ξ / lam))) : ℂ) * (fejer (lam * x) : ℂ) := by
    rw [← integral_const_mul]
    congr 1 with x
    simp only [K, Complex.ofReal_mul]
    have harg : lam * x * (ξ / lam) = x * ξ := by field_simp [hlam.ne']
    rw [harg]
    ring
  rw [h1, Measure.integral_comp_mul_left
    (g := fun y : ℝ => (Real.fourierChar (-(y * (ξ / lam))) : ℂ) * (fejer y : ℂ)) lam]
  rw [abs_inv, abs_of_pos hlam]
  have h2 : (lam : ℂ) * ((lam⁻¹ : ℝ) • ∫ y : ℝ, (Real.fourierChar (-(y * (ξ / lam))) : ℂ) * (fejer y : ℂ)) =
      ∫ y : ℝ, (Real.fourierChar (-(y * (ξ / lam))) : ℂ) * (fejer y : ℂ) := by
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam.ne', Complex.ofReal_one, one_mul]
  rw [h2, ← fourier_eq_mul]
  exact fourier_fejer (ξ / lam)

private lemma fourier_mod {f : ℝ → ℂ} (ξ₀ ξ : ℝ) :
    𝓕 (fun x : ℝ => (Real.fourierChar (ξ₀ * x) : ℂ) * f x) ξ = 𝓕 f (ξ - ξ₀) := by
  rw [fourier_eq_mul, fourier_eq_mul]
  congr 1 with x
  rw [← mul_assoc, fourier_char_mul]
  have harg : -(x * ξ) + ξ₀ * x = -(x * (ξ - ξ₀)) := by ring
  rw [harg]

private lemma integral_K_sub_translate {lam : ℝ} (hlam : 0 < lam) (c : ℝ) :
    ∫ x : ℝ, |K lam (x - c) - K lam x| = ∫ y : ℝ, |fejer (y - lam * c) - fejer y| := by
  have h1 : (fun x : ℝ => |K lam (x - c) - K lam x|) =
      fun x => lam * |fejer (lam * x - lam * c) - fejer (lam * x)| := by
    ext x
    have harg : lam * (x - c) = lam * x - lam * c := by ring
    rw [K, K, ← mul_sub, abs_mul, abs_of_pos hlam, harg]
  rw [h1, integral_const_mul, Measure.integral_comp_mul_left
    (g := fun y : ℝ => |fejer (y - lam * c) - fejer y|) lam, abs_inv, abs_of_pos hlam]
  rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]

/- Section 3: Discrete convolution operator M and its symbol Φ -/

private noncomputable def M (a : ℕ → ℕ) (q : ℝ → ℂ) (x : ℝ) : ℂ :=
  q x + ∑' k, ((1 / (a k : ℝ) : ℝ) : ℂ) * q (x - Real.log (a k))

private noncomputable def Φ (a : ℕ → ℕ) (ξ : ℝ) : ℂ :=
  1 + ∑' k, Erdos967.summand (2 * π * ξ) (a k)

private lemma a_gt_one {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0) (k : ℕ) : 1 < a k :=
  lt_of_lt_of_le ha₀ (ha.monotone (Nat.zero_le k))

private lemma summand_eq_fourierChar {n : ℕ} (hn : 1 < n) (ξ : ℝ) :
    Erdos967.summand (2 * π * ξ) n =
      ((1 / (n : ℝ) : ℝ) : ℂ) * (Real.fourierChar (-(Real.log (n : ℝ) * ξ)) : ℂ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hn)
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  rw [Erdos967.summand, Complex.cpow_def_of_ne_zero hnc]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le]
  rw [Real.fourierChar_apply, one_div, ← Complex.exp_neg]
  rw [Complex.ofReal_div, Complex.ofReal_one, one_div]
  have h1 : -(Complex.ofReal (Real.log (n : ℝ)) * (1 + ↑(2 * π * ξ) * I)) =
      -(Complex.ofReal (Real.log (n : ℝ))) + ↑(2 * π * -(Real.log (n : ℝ) * ξ)) * I := by
    push_cast
    ring
  rw [h1, Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hn0]

private lemma M_properties {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k => 1 / (a k : ℝ)))
    {q : ℝ → ℂ} {B : ℝ} (_hB : 0 ≤ B)
    (hq_cont : Continuous q) (hq_bdd : ∀ x, ‖q x‖ ≤ B) (hq_int : Integrable q) :
    Continuous (M a q) ∧
    (∀ x, ‖M a q x‖ ≤ B * (1 + ∑' k, 1 / (a k : ℝ))) ∧
    Integrable (M a q) ∧
    (∀ ξ, 𝓕 (M a q) ξ = Φ a ξ * 𝓕 q ξ) := by
  let term : ℕ → ℝ → ℂ := fun k x => ((1 / (a k : ℝ) : ℝ) : ℂ) * q (x - Real.log (a k))
  have hterm_cont : ∀ k, Continuous (term k) := fun k =>
    continuous_const.mul (hq_cont.comp (continuous_id.sub continuous_const))
  have hterm_norm : ∀ k x, ‖term k x‖ ≤ (1 / (a k : ℝ)) * B := fun k x => by
    dsimp [term]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hq_bdd _) (by positivity)
  have hterm_int : ∀ k, Integrable (term k) := fun k =>
    (hq_int.comp_sub_right (Real.log (a k))).const_mul _
  have hterm_int_norm : ∀ k, ∫ x, ‖term k x‖ = (1 / (a k : ℝ)) * ∫ x, ‖q x‖ := fun k => by
    dsimp [term]
    simp_rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (a k : ℝ))]
    rw [integral_const_mul, integral_sub_right_eq_self (fun x => ‖q x‖) (Real.log (a k))]
  have hpt : ∀ x, Summable (fun k => ‖term k x‖) := fun x =>
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hterm_norm k x) (hsum.mul_right B)
  have hsum_int : Summable (fun k => ∫ x, ‖term k x‖) := by
    simp_rw [hterm_int_norm]
    exact hsum.mul_right _
  have htsum_cont : Continuous (fun x => ∑' k, term k x) :=
    continuous_tsum hterm_cont (hsum.mul_right B) hterm_norm
  have htsum_int : Integrable (fun x => ∑' k, term k x) :=
    integrable_tsum_of_summable_norm hterm_int hpt hsum_int
  refine ⟨hq_cont.add htsum_cont, ?_, hq_int.add htsum_int, ?_⟩
  · intro x
    calc ‖M a q x‖
        ≤ ‖q x‖ + ‖∑' k, term k x‖ := norm_add_le _ _
      _ ≤ B + ∑' k, ‖term k x‖ := add_le_add (hq_bdd x) (norm_tsum_le_tsum_norm (hpt x))
      _ ≤ B + ∑' k, (1 / (a k : ℝ)) * B :=
          add_le_add le_rfl (Summable.tsum_le_tsum (fun k => hterm_norm k x) (hpt x) (hsum.mul_right B))
      _ = B * (1 + ∑' k, 1 / (a k : ℝ)) := by rw [tsum_mul_right]; ring
  · intro ξ
    rw [fourier_eq_mul]
    have hsplit : (∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * M a q x) =
        (∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * q x) +
        (∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * (∑' k, term k x)) := by
      simp_rw [M, mul_add]
      exact integral_add (integrable_fourier_mul hq_int ξ) (integrable_fourier_mul htsum_int ξ)
    rw [hsplit]
    have hterm_f_int : ∀ k, Integrable (fun x => (Real.fourierChar (-(x * ξ)) : ℂ) * term k x) := fun k =>
      integrable_fourier_mul (hterm_int k) ξ
    have hterm_f_sum : Summable (fun k => ∫ x, ‖(Real.fourierChar (-(x * ξ)) : ℂ) * term k x‖) := by
      simpa [norm_mul, norm_fourierChar_coe] using hsum_int
    have hswap : (∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * (∑' k, term k x)) =
        ∑' k, ∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * term k x := by
      have hpoint : (fun x => (Real.fourierChar (-(x * ξ)) : ℂ) * (∑' k, term k x)) =
          fun x => ∑' k, (Real.fourierChar (-(x * ξ)) : ℂ) * term k x := by
        ext x
        rw [tsum_mul_left]
      rw [hpoint]
      exact (integral_tsum_of_summable_integral_norm hterm_f_int hterm_f_sum).symm
    rw [hswap]
    have hterm_eval : ∀ k, (∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * term k x) =
        Erdos967.summand (2 * π * ξ) (a k) * 𝓕 q ξ := fun k => by
      rw [summand_eq_fourierChar (a_gt_one ha ha₀ k) ξ, fourier_eq_mul]
      dsimp [term]
      have hsub := integral_sub_right_eq_self (μ := volume)
        (fun x : ℝ => (Real.fourierChar (-(x * ξ)) : ℂ) * (((1 / (a k : ℝ) : ℝ) : ℂ) * q (x - Real.log (a k))))
        (-Real.log (a k))
      rw [← hsub, ← integral_const_mul]
      congr 1 with x
      have hx_eq : x - -Real.log (a k) - Real.log (a k) = x := by ring
      rw [hx_eq]
      have hexp : (Real.fourierChar (-((x - -Real.log (a k)) * ξ)) : ℂ) =
          (Real.fourierChar (-(Real.log (a k) * ξ)) : ℂ) * (Real.fourierChar (-(x * ξ)) : ℂ) := by
        rw [fourier_char_mul]
        have harg : -((x - -Real.log (a k)) * ξ) = -(Real.log (a k) * ξ) + -(x * ξ) := by ring
        rw [harg]
      rw [hexp]
      ring
    simp_rw [hterm_eval]
    rw [tsum_mul_right, ← fourier_eq_mul, Φ]
    ring

/- Section 4: Local and Global Wiener Division -/

private lemma local_wiener_division
    {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k => 1 / (a k : ℝ)))
    (hz : ∀ t : ℝ, 1 + (∑' k, Erdos967.summand t (a k)) ≠ 0)
    (ξ₀ : ℝ) :
    ∃ δ > 0, ∀ (h : ℝ → ℂ), Continuous h → (∃ B, ∀ x, ‖h x‖ ≤ B) → Integrable h →
      (∀ ξ, δ < |ξ - ξ₀| → 𝓕 h ξ = 0) →
      ∃ (q : ℝ → ℂ), Continuous q ∧ (∃ Bq, ∀ x, ‖q x‖ ≤ Bq) ∧ Integrable q ∧
        ∀ x, M a q x = h x := by
  let c : ℂ := Φ a ξ₀
  have hc0 : c ≠ 0 := hz (2 * π * ξ₀)
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hS_nonneg : 0 ≤ ∑' k, 1 / (a k : ℝ) := tsum_nonneg fun k => by positivity
  -- Choose tail cutoff N so 6 * ∑_{k ≥ N} 1/a_k < ‖c‖ / 4
  have htail_lim : Tendsto (fun N : ℕ => ∑' k, (if N ≤ k then 1 / (a k : ℝ) else 0)) atTop (𝓝 0) := by
    have hts := hsum.hasSum.tendsto_sum_nat
    have hsub : Tendsto (fun N : ℕ => (∑' k, 1 / (a k : ℝ)) - ∑ k ∈ Finset.range N, 1 / (a k : ℝ))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := ∑' k, 1 / (a k : ℝ))).sub hts
    refine hsub.congr fun N => ?_
    have h1 := hsum.sum_add_tsum_nat_add N
    have h2 : (∑' k, if N ≤ k then 1 / (a k : ℝ) else 0) = ∑' k, 1 / (a (k + N) : ℝ) := by
      have hif_sum : Summable (fun k => if N ≤ k then 1 / (a k : ℝ) else 0) :=
        hsum.of_nonneg_of_le (fun k => by split_ifs <;> positivity)
          (fun k => by split_ifs; exact le_rfl; positivity)
      rw [← hif_sum.sum_add_tsum_nat_add N]
      have hfin : (∑ i ∈ Finset.range N, if N ≤ i then 1 / (a i : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun i hi => if_neg (not_le.mpr (Finset.mem_range.mp hi))
      rw [hfin, zero_add]
      congr 1 with k
      exact if_pos (Nat.le_add_left N k)
    linarith
  obtain ⟨N, hN⟩ := (htail_lim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ‖c‖ / 24))).exists
  -- Choose δ > 0 so for all k < N, the Fejer translation error is tiny
  let eps : ℝ := ‖c‖ / (12 * (1 + ∑' k, 1 / (a k : ℝ)))
  have heps : 0 < eps := by positivity
  obtain ⟨η, hη_pos, hη⟩ := Metric.tendsto_nhds_nhds.mp tendsto_fejer_translate eps heps
  let L : ℝ := 1 + ∑ k ∈ Finset.range N, Real.log (a k)
  have hL_pos : 0 < L := by
    have : 0 ≤ ∑ k ∈ Finset.range N, Real.log (a k) :=
      Finset.sum_nonneg fun k _ => Real.log_nonneg (by exact_mod_cast (a_gt_one ha ha₀ k).le)
    linarith
  let δ : ℝ := η / (2 * L)
  have hδ_pos : 0 < δ := by positivity
  refine ⟨δ, hδ_pos, ?_⟩
  -- Build the trapezoid function w and perturbation r
  let ψ : ℝ → ℝ := fun x => 2 * K (2 * δ) x - K δ x
  let w : ℝ → ℂ := fun x => (Real.fourierChar (ξ₀ * x) : ℂ) * (ψ x : ℂ)
  have hψ_cont : Continuous ψ :=
    (continuous_const.mul (K_continuous (2 * δ))).sub (K_continuous δ)
  have hψ_int : Integrable ψ :=
    ((K_integrable (by positivity)).const_mul 2).sub (K_integrable hδ_pos)
  have hψ_bdd : ∀ x, |ψ x| ≤ 5 * δ := fun x => by
    have h1 : 0 ≤ K (2 * δ) x := K_nonneg (by positivity) x
    have h2 : K (2 * δ) x ≤ 2 * δ := K_le (by positivity) x
    have h3 : 0 ≤ K δ x := K_nonneg hδ_pos x
    have h4 : K δ x ≤ δ := K_le hδ_pos x
    rw [abs_le]
    constructor <;> dsimp [ψ] <;> linarith
  have hw_cont : Continuous w :=
    (continuous_fourierChar_coe.comp (continuous_const.mul continuous_id)).mul
      (Complex.continuous_ofReal.comp hψ_cont)
  have hw_bdd : ∀ x, ‖w x‖ ≤ 5 * δ := fun x => by
    dsimp [w]
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact hψ_bdd x
  have hw_int : Integrable w := by
    refine hψ_int.norm.mono' hw_cont.aestronglyMeasurable ?_
    filter_upwards with x
    simp [w, norm_fourierChar_coe]
  have hMw := M_properties ha ha₀ hsum (by positivity : 0 ≤ 5 * δ) hw_cont hw_bdd hw_int
  have hfourier_w : ∀ ξ, 𝓕 w ξ = ((2 * tent ((ξ - ξ₀) / (2 * δ)) - tent ((ξ - ξ₀) / δ) : ℝ) : ℂ) := by
    intro ξ
    dsimp [w]
    rw [fourier_mod ξ₀ ξ]
    have hsub : (fun x : ℝ => (ψ x : ℂ)) =
        fun x : ℝ => (2 : ℂ) * (K (2 * δ) x : ℂ) - (K δ x : ℂ) := by
      ext x; simp [ψ]
    rw [hsub]
    have hsub_int1 : Integrable (fun x : ℝ => (2 : ℂ) * (K (2 * δ) x : ℂ)) :=
      (K_integrable (by positivity)).ofReal.const_mul 2
    have hsub_int2 : Integrable (fun x : ℝ => (K δ x : ℂ)) := (K_integrable hδ_pos).ofReal
    rw [fourier_eq_mul]
    have hlin : (∫ x, (Real.fourierChar (-(x * (ξ - ξ₀))) : ℂ) * ((2 : ℂ) * (K (2 * δ) x : ℂ) - (K δ x : ℂ))) =
        (2 : ℂ) * 𝓕 (fun x => (K (2 * δ) x : ℂ)) (ξ - ξ₀) - 𝓕 (fun x => (K δ x : ℂ)) (ξ - ξ₀) := by
      have hms : ∀ x : ℝ, (Real.fourierChar (-(x * (ξ - ξ₀))) : ℂ) * ((2 : ℂ) * (K (2 * δ) x : ℂ) - (K δ x : ℂ)) =
          (Real.fourierChar (-(x * (ξ - ξ₀))) : ℂ) * ((2 : ℂ) * (K (2 * δ) x : ℂ)) -
          (Real.fourierChar (-(x * (ξ - ξ₀))) : ℂ) * (K δ x : ℂ) := fun x => mul_sub _ _ _
      simp_rw [hms]
      rw [integral_sub (integrable_fourier_mul hsub_int1 _) (integrable_fourier_mul hsub_int2 _)]
      congr 1
      · rw [fourier_eq_mul, ← integral_const_mul]
        congr 1 with x
        ring
      · rw [fourier_eq_mul]
    rw [hlin, fourier_K (by positivity), fourier_K hδ_pos]
    push_cast
    ring
  -- Define r(x) = -c⁻¹ * (M a w x - c * w x)
  let r : ℝ → ℂ := fun x => -c⁻¹ * (M a w x - c * w x)
  have hr_cont : Continuous r :=
    continuous_const.mul (hMw.1.sub (continuous_const.mul hw_cont))
  have hr_int : Integrable r :=
    (hMw.2.2.1.sub (hw_int.const_mul c)).const_mul (-c⁻¹)
  have hr_fourier : ∀ ξ, 𝓕 r ξ = (1 - c⁻¹ * Φ a ξ) * 𝓕 w ξ := by
    intro ξ
    rw [fourier_eq_mul]
    have h1 : (∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * r x) =
        (-c⁻¹) * (𝓕 (M a w) ξ - c * 𝓕 w ξ) := by
      dsimp [r]
      have hconv1 := integrable_fourier_mul hMw.2.2.1 ξ
      have hconv2 := integrable_fourier_mul (hw_int.const_mul c) ξ
      calc (∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * ((-c⁻¹) * (M a w x - c * w x)))
          = (-c⁻¹) * ∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * (M a w x - c * w x) := by
              rw [← integral_const_mul]
              congr 1 with x
              ring
        _ = (-c⁻¹) * ((∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * M a w x) -
              (∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * (c * w x))) := by
              congr 1
              simp_rw [mul_sub]
              rw [integral_sub hconv1 hconv2]
        _ = (-c⁻¹) * (𝓕 (M a w) ξ - c * 𝓕 w ξ) := by
              congr 1
              rw [fourier_eq_mul, fourier_eq_mul, ← integral_const_mul]
              congr 2
              ext x
              ring
    rw [h1, hMw.2.2.2 ξ]
    field_simp [hc0]
    ring
  -- Bound ‖r‖_{L^1} ≤ 1/2
  have hr_L1 : ∫ x, ‖r x‖ ≤ 1 / 2 := by
    let diff : ℕ → ℝ → ℂ := fun k x =>
      ((1 / (a k : ℝ) : ℝ) : ℂ) * (Real.fourierChar (ξ₀ * (x - Real.log (a k))) : ℂ) *
        ((ψ (x - Real.log (a k)) - ψ x : ℝ) : ℂ)
    have hdiff_eq : ∀ x, M a w x - c * w x = ∑' k, diff k x := fun x => by
      have hsum1 : Summable (fun k => ((1 / (a k : ℝ) : ℝ) : ℂ) * w (x - Real.log (a k))) := by
        refine Summable.of_norm_bounded (g := fun k => (1 / (a k : ℝ)) * (5 * δ)) (hsum.mul_right _) fun k => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hw_bdd _) (by positivity)
      have hsum2 : Summable (fun k => Erdos967.summand (2 * π * ξ₀) (a k) * w x) := by
        refine Summable.of_norm_bounded (g := fun k => (1 / (a k : ℝ)) * (5 * δ)) (hsum.mul_right _) fun k => ?_
        rw [summand_eq_fourierChar (a_gt_one ha ha₀ k) ξ₀, norm_mul, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg (by positivity), Circle.norm_coe, mul_one]
        exact mul_le_mul_of_nonneg_left (hw_bdd _) (by positivity)
      dsimp [M, c, Φ]
      rw [add_mul, one_mul, ← tsum_mul_right]
      have : w x + (∑' k, ((1 / (a k : ℝ) : ℝ) : ℂ) * w (x - Real.log (a k))) -
          (w x + ∑' k, Erdos967.summand (2 * π * ξ₀) (a k) * w x) =
          (∑' k, ((1 / (a k : ℝ) : ℝ) : ℂ) * w (x - Real.log (a k))) -
          (∑' k, Erdos967.summand (2 * π * ξ₀) (a k) * w x) := by ring
      rw [this, ← hsum1.tsum_sub hsum2]
      congr 1 with k
      rw [summand_eq_fourierChar (a_gt_one ha ha₀ k) ξ₀]
      dsimp [diff, w]
      have hphase : (Real.fourierChar (-(Real.log (a k) * ξ₀)) : ℂ) * (Real.fourierChar (ξ₀ * x) : ℂ) =
          (Real.fourierChar (ξ₀ * (x - Real.log (a k))) : ℂ) := by
        rw [fourier_char_mul]
        congr 2
        ring
      calc ((1 / (a k : ℝ) : ℝ) : ℂ) * ((Real.fourierChar (ξ₀ * (x - Real.log (a k))) : ℂ) * (ψ (x - Real.log (a k)) : ℂ)) -
            ((1 / (a k : ℝ) : ℝ) : ℂ) * (Real.fourierChar (-(Real.log (a k) * ξ₀)) : ℂ) *
              ((Real.fourierChar (ξ₀ * x) : ℂ) * (ψ x : ℂ))
          = ((1 / (a k : ℝ) : ℝ) : ℂ) * (Real.fourierChar (ξ₀ * (x - Real.log (a k))) : ℂ) * (ψ (x - Real.log (a k)) : ℂ) -
            ((1 / (a k : ℝ) : ℝ) : ℂ) * ((Real.fourierChar (-(Real.log (a k) * ξ₀)) : ℂ) *
              (Real.fourierChar (ξ₀ * x) : ℂ)) * (ψ x : ℂ) := by ring
        _ = ((1 / (a k : ℝ) : ℝ) : ℂ) * (Real.fourierChar (ξ₀ * (x - Real.log (a k))) : ℂ) *
              ((ψ (x - Real.log (a k)) - ψ x : ℝ) : ℂ) := by rw [hphase]; push_cast; ring
    have hdiff_int : ∀ k, Integrable (diff k) := fun k => by
      refine (((hψ_int.comp_sub_right (Real.log (a k))).sub hψ_int).norm.const_mul (1 / (a k : ℝ))).mono' ?_ ?_
      · refine Continuous.aestronglyMeasurable ?_
        dsimp [diff]
        exact (continuous_const.mul (continuous_fourierChar_coe.comp
          (continuous_const.mul (continuous_id.sub continuous_const)))).mul
          (Complex.continuous_ofReal.comp ((hψ_cont.comp (continuous_id.sub continuous_const)).sub hψ_cont))
      · filter_upwards with x
        dsimp [diff]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
          norm_fourierChar_coe, mul_one, Complex.norm_real]
        exact le_rfl
    have hdiff_norm_int : ∀ k, ∫ x, ‖diff k x‖ ≤
        (1 / (a k : ℝ)) * (2 * (∫ y, |fejer (y - 2 * δ * Real.log (a k)) - fejer y|) +
          (∫ y, |fejer (y - δ * Real.log (a k)) - fejer y|)) := fun k => by
      have hpoint : ∀ x, ‖diff k x‖ ≤ (1 / (a k : ℝ)) *
          (2 * |K (2 * δ) (x - Real.log (a k)) - K (2 * δ) x| +
            |K δ (x - Real.log (a k)) - K δ x|) := fun x => by
        dsimp [diff, ψ]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
          Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have htri : |2 * K (2 * δ) (x - Real.log (a k)) - K δ (x - Real.log (a k)) -
            (2 * K (2 * δ) x - K δ x)| ≤
            |2 * (K (2 * δ) (x - Real.log (a k)) - K (2 * δ) x)| +
            |K δ (x - Real.log (a k)) - K δ x| := by
          have : 2 * K (2 * δ) (x - Real.log (a k)) - K δ (x - Real.log (a k)) -
              (2 * K (2 * δ) x - K δ x) =
              2 * (K (2 * δ) (x - Real.log (a k)) - K (2 * δ) x) -
              (K δ (x - Real.log (a k)) - K δ x) := by ring
          rw [this]
          exact abs_sub _ _
        rwa [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri
      have hi1 : Integrable (fun x => |K (2 * δ) (x - Real.log (a k)) - K (2 * δ) x|) :=
        ((K_integrable (by positivity)).comp_sub_right _ |>.sub (K_integrable (by positivity))).abs
      have hi2 : Integrable (fun x => |K δ (x - Real.log (a k)) - K δ x|) :=
        ((K_integrable hδ_pos).comp_sub_right _ |>.sub (K_integrable hδ_pos)).abs
      calc ∫ x, ‖diff k x‖
          ≤ ∫ x, (1 / (a k : ℝ)) *
              (2 * |K (2 * δ) (x - Real.log (a k)) - K (2 * δ) x| +
                |K δ (x - Real.log (a k)) - K δ x|) :=
            integral_mono (hdiff_int k).norm ((hi1.const_mul 2 |>.add hi2).const_mul _) hpoint
        _ = (1 / (a k : ℝ)) * (2 * (∫ x, |K (2 * δ) (x - Real.log (a k)) - K (2 * δ) x|) +
              (∫ x, |K δ (x - Real.log (a k)) - K δ x|)) := by
            rw [integral_const_mul, integral_add (hi1.const_mul 2) hi2, integral_const_mul]
        _ = (1 / (a k : ℝ)) * (2 * (∫ y, |fejer (y - 2 * δ * Real.log (a k)) - fejer y|) +
              (∫ y, |fejer (y - δ * Real.log (a k)) - fejer y|)) := by
            rw [integral_K_sub_translate (by positivity), integral_K_sub_translate hδ_pos]
    have hfejer_tr_le_two : ∀ s : ℝ, ∫ y, |fejer (y - s) - fejer y| ≤ 2 := fun s => by
      calc ∫ y, |fejer (y - s) - fejer y|
          ≤ ∫ y, (fejer (y - s) + fejer y) :=
            integral_mono ((fejer_integrable.comp_sub_right s).sub fejer_integrable).abs
              ((fejer_integrable.comp_sub_right s).add fejer_integrable) fun y => by
                have := abs_sub (fejer (y - s)) (fejer y)
                rwa [abs_of_nonneg (fejer_nonneg _), abs_of_nonneg (fejer_nonneg _)] at this
        _ = (∫ y, fejer (y - s)) + (∫ y, fejer y) :=
            integral_add (fejer_integrable.comp_sub_right s) fejer_integrable
        _ = 2 := by rw [integral_sub_right_eq_self fejer s, integral_fejer]; norm_num
    have hdiff_coarse : ∀ k, ∫ x, ‖diff k x‖ ≤ (1 / (a k : ℝ)) * 6 := fun k => by
      have h1 := hfejer_tr_le_two (2 * δ * Real.log (a k))
      have h2 := hfejer_tr_le_two (δ * Real.log (a k))
      have h3 : 2 * (∫ y, |fejer (y - 2 * δ * Real.log (a k)) - fejer y|) +
          (∫ y, |fejer (y - δ * Real.log (a k)) - fejer y|) ≤ 6 := by linarith
      exact (hdiff_norm_int k).trans (mul_le_mul_of_nonneg_left h3 (by positivity))
    have hdiff_pt : ∀ x, Summable (fun k => ‖diff k x‖) := fun x =>
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => by
        dsimp [diff]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
          Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith [hψ_bdd (x - Real.log (a k)), hψ_bdd x]))
          (by positivity)) (hsum.mul_right (10 * δ))
    have hdiff_sum : Summable (fun k => ∫ x, ‖diff k x‖) :=
      Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _) hdiff_coarse (hsum.mul_right 6)
    have hM_int : ∫ x, ‖M a w x - c * w x‖ ≤ ‖c‖ / 2 := by
      have hstep1 : ∫ x, ‖M a w x - c * w x‖ ≤ ∑' k, ∫ x, ‖diff k x‖ := by
        simp_rw [hdiff_eq]
        exact integral_norm_tsum_le hdiff_int hdiff_pt hdiff_sum
      refine hstep1.trans ?_
      rw [← hdiff_sum.sum_add_tsum_nat_add N]
      have hhead : ∑ k ∈ Finset.range N, ∫ x, ‖diff k x‖ ≤ ‖c‖ / 4 := by
        have hsmall : ∀ k ∈ Finset.range N, ∫ x, ‖diff k x‖ ≤ (1 / (a k : ℝ)) * (3 * eps) := by
          intro k hk
          have hlog_nonneg : 0 ≤ Real.log (a k) :=
            Real.log_nonneg (by exact_mod_cast (a_gt_one ha ha₀ k).le)
          have hlog_lt : Real.log (a k) < L := by
            have hle : Real.log (a k) ≤ ∑ j ∈ Finset.range N, Real.log (a j) :=
              Finset.single_le_sum (f := fun j => Real.log (a j))
                (fun j _ => Real.log_nonneg (by exact_mod_cast (a_gt_one ha ha₀ j).le)) hk
            linarith
          have harg1 : dist (2 * δ * Real.log (a k)) 0 < η := by
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
            have : 2 * δ * Real.log (a k) < 2 * δ * L := mul_lt_mul_of_pos_left hlog_lt (by positivity)
            have h2L : 2 * δ * L = η := by dsimp [δ]; field_simp [hL_pos.ne']
            linarith
          have harg2 : dist (δ * Real.log (a k)) 0 < η := by
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
            have : δ * Real.log (a k) ≤ 2 * δ * Real.log (a k) := by nlinarith
            have : 2 * δ * Real.log (a k) < 2 * δ * L := mul_lt_mul_of_pos_left hlog_lt (by positivity)
            have h2L : 2 * δ * L = η := by dsimp [δ]; field_simp [hL_pos.ne']
            linarith
          have he1 : ∫ y, |fejer (y - 2 * δ * Real.log (a k)) - fejer y| < eps := by
            have := hη harg1
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at this
            exact this
          have he2 : ∫ y, |fejer (y - δ * Real.log (a k)) - fejer y| < eps := by
            have := hη harg2
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at this
            exact this
          exact (hdiff_norm_int k).trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
        calc ∑ k ∈ Finset.range N, ∫ x, ‖diff k x‖
            ≤ ∑ k ∈ Finset.range N, (1 / (a k : ℝ)) * (3 * eps) := Finset.sum_le_sum hsmall
          _ = (∑ k ∈ Finset.range N, 1 / (a k : ℝ)) * (3 * eps) := (Finset.sum_mul _ _ _).symm
          _ ≤ (1 + ∑' k, 1 / (a k : ℝ)) * (3 * eps) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              have := hsum.sum_le_tsum (Finset.range N) (fun k _ => by positivity)
              linarith
          _ = ‖c‖ / 4 := by dsimp [eps]; field_simp [show (1 + ∑' k, 1 / (a k : ℝ)) ≠ 0 by linarith]; ring
      have htail : ∑' k, ∫ x, ‖diff (k + N) x‖ ≤ ‖c‖ / 4 := by
        have hif_sum : Summable (fun k => if N ≤ k then 1 / (a k : ℝ) else 0) :=
          hsum.of_nonneg_of_le (fun k => by split_ifs <;> positivity)
            (fun k => by split_ifs; exact le_rfl; positivity)
        have htail_eq : (∑' k, 1 / (a (k + N) : ℝ)) = ∑' k, if N ≤ k then 1 / (a k : ℝ) else 0 := by
          rw [← hif_sum.sum_add_tsum_nat_add N]
          have hfin : (∑ i ∈ Finset.range N, if N ≤ i then 1 / (a i : ℝ) else 0) = 0 :=
            Finset.sum_eq_zero fun i hi => if_neg (not_le.mpr (Finset.mem_range.mp hi))
          rw [hfin, zero_add]
          congr 1 with k
          exact (if_pos (Nat.le_add_left N k)).symm
        have hsum_shift : Summable (fun k => (1 / (a (k + N) : ℝ)) * 6) :=
          (hsum.comp_injective (add_left_injective N)).mul_right 6
        calc ∑' k, ∫ x, ‖diff (k + N) x‖
            ≤ ∑' k, (1 / (a (k + N) : ℝ)) * 6 :=
              Summable.tsum_le_tsum (fun k => hdiff_coarse (k + N))
                (hdiff_sum.comp_injective (add_left_injective N)) hsum_shift
          _ = (∑' k, 1 / (a (k + N) : ℝ)) * 6 := tsum_mul_right
          _ ≤ ‖c‖ / 4 := by rw [htail_eq]; linarith
      linarith
    have hr_norm_eq : (fun x => ‖r x‖) = fun x => ‖c‖⁻¹ * ‖M a w x - c * w x‖ := by
      ext x
      simp [r]
    rw [hr_norm_eq, integral_const_mul]
    calc ‖c‖⁻¹ * ∫ x, ‖M a w x - c * w x‖
        ≤ ‖c‖⁻¹ * (‖c‖ / 2) := mul_le_mul_of_nonneg_left hM_int (by positivity)
      _ = 1 / 2 := by field_simp [hcpos.ne']
  -- Now solve M a q = h for any h with supp(𝓕 h) ⊆ [ξ₀ - δ, ξ₀ + δ]
  intro h hh_cont ⟨Bh, hh_bdd⟩ hh_int hh_supp
  let B₀ : ℝ := max Bh 0
  have hB₀ : 0 ≤ B₀ := le_max_right _ _
  have hh_bdd' : ∀ x, ‖h x‖ ≤ B₀ := fun x => (hh_bdd x).trans (le_max_left _ _)
  let iter : ℕ → (ℝ → ℂ) := fun n => Nat.rec h (fun _ acc => conv acc r) n
  have hiter_props : ∀ n,
      Continuous (iter n) ∧
      (∀ x, ‖iter n x‖ ≤ B₀ * (1 / 2 : ℝ) ^ n) ∧
      Integrable (iter n) ∧
      (∫ x, ‖iter n x‖ ≤ (∫ x, ‖h x‖) * (1 / 2 : ℝ) ^ n) ∧
      (∀ ξ, 𝓕 (iter n) ξ = 𝓕 h ξ * (𝓕 r ξ) ^ n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨hh_cont, by simpa [iter] using hh_bdd', hh_int, by simp [iter], by simp [iter]⟩
    | succ n ih =>
      obtain ⟨hcont, hbdd, hint, hL1, hfour⟩ := ih
      have hcont' : Continuous (iter (n + 1)) := conv_continuous_left hbdd hcont hr_int
      have hbdd' : ∀ x, ‖iter (n + 1) x‖ ≤ B₀ * (1 / 2 : ℝ) ^ (n + 1) := fun x => by
        calc ‖conv (iter n) r x‖
            ≤ (B₀ * (1 / 2 : ℝ) ^ n) * ∫ t, ‖r t‖ := conv_norm_le_left' hcont hbdd hr_int x
          _ ≤ (B₀ * (1 / 2 : ℝ) ^ n) * (1 / 2) :=
              mul_le_mul_of_nonneg_left hr_L1 (by positivity)
          _ = B₀ * (1 / 2 : ℝ) ^ (n + 1) := by ring
      have hint' : Integrable (iter (n + 1)) := conv_integrable hint hr_int
      have hL1' : ∫ x, ‖iter (n + 1) x‖ ≤ (∫ x, ‖h x‖) * (1 / 2 : ℝ) ^ (n + 1) := by
        calc ∫ x, ‖conv (iter n) r x‖
            ≤ (∫ x, ‖iter n x‖) * (∫ x, ‖r x‖) := conv_integral_norm_le hint hr_int
          _ ≤ ((∫ x, ‖h x‖) * (1 / 2 : ℝ) ^ n) * (1 / 2) :=
              mul_le_mul hL1 hr_L1 (integral_nonneg fun _ => norm_nonneg _) (by positivity)
          _ = (∫ x, ‖h x‖) * (1 / 2 : ℝ) ^ (n + 1) := by ring
      have hfour' : ∀ ξ, 𝓕 (iter (n + 1)) ξ = 𝓕 h ξ * (𝓕 r ξ) ^ (n + 1) := fun ξ => by
        change 𝓕 (conv (iter n) r) ξ = _
        rw [fourier_conv hint hr_int ξ, hfour ξ]
        ring
      exact ⟨hcont', hbdd', hint', hL1', hfour'⟩
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  let q : ℝ → ℂ := fun x => c⁻¹ * ∑' n, iter n x
  have hq_cont : Continuous q :=
    continuous_const.mul (continuous_tsum (fun n => (hiter_props n).1)
      (hgeom.mul_left B₀) (fun n x => (hiter_props n).2.1 x))
  have hq_pt : ∀ x, Summable (fun n => ‖iter n x‖) := fun x =>
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => (hiter_props n).2.1 x) (hgeom.mul_left B₀)
  have hq_L1_sum : Summable (fun n => ∫ x, ‖iter n x‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => (hiter_props n).2.2.2.1) (hgeom.mul_left _)
  have hq_bdd : ∀ x, ‖q x‖ ≤ ‖c‖⁻¹ * (B₀ * 2) := fun x => by
    dsimp [q]
    rw [norm_mul, norm_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖∑' n, iter n x‖
        ≤ ∑' n, ‖iter n x‖ := norm_tsum_le_tsum_norm (hq_pt x)
      _ ≤ ∑' n, B₀ * (1 / 2 : ℝ) ^ n :=
          Summable.tsum_le_tsum (fun n => (hiter_props n).2.1 x) (hq_pt x) (hgeom.mul_left B₀)
      _ = B₀ * 2 := by rw [tsum_mul_left, tsum_geometric_two]
  have hq_int : Integrable q :=
    (integrable_tsum_of_summable_norm (fun n => (hiter_props n).2.2.1) hq_pt hq_L1_sum).const_mul c⁻¹
  have hMq := M_properties ha ha₀ hsum (by positivity : 0 ≤ ‖c‖⁻¹ * (B₀ * 2)) hq_cont hq_bdd hq_int
  -- Compute 𝓕 (M a q) ξ = 𝓕 h ξ for all ξ
  have hfourier_eq : ∀ ξ, 𝓕 (M a q) ξ = 𝓕 h ξ := by
    intro ξ
    rw [hMq.2.2.2 ξ]
    have hfq : 𝓕 q ξ = c⁻¹ * ∑' n, 𝓕 h ξ * (𝓕 r ξ) ^ n := by
      rw [fourier_eq_mul]
      have hterm_int : ∀ n, Integrable (fun x => (Real.fourierChar (-(x * ξ)) : ℂ) * iter n x) := fun n =>
        integrable_fourier_mul (hiter_props n).2.2.1 ξ
      have hterm_sum : Summable (fun n => ∫ x, ‖(Real.fourierChar (-(x * ξ)) : ℂ) * iter n x‖) := by
        simpa [norm_mul, norm_fourierChar_coe] using hq_L1_sum
      calc (∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * (c⁻¹ * ∑' n, iter n x))
          = c⁻¹ * ∫ x, ∑' n, (Real.fourierChar (-(x * ξ)) : ℂ) * iter n x := by
              rw [← integral_const_mul]
              congr 1 with x
              rw [tsum_mul_left]
              ring
        _ = c⁻¹ * ∑' n, ∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * iter n x := by
              rw [← integral_tsum_of_summable_integral_norm hterm_int hterm_sum]
        _ = c⁻¹ * ∑' n, 𝓕 h ξ * (𝓕 r ξ) ^ n := by
              congr 1
              refine tsum_congr fun n => ?_
              rw [← fourier_eq_mul, (hiter_props n).2.2.2.2 ξ]
    rw [hfq]
    by_cases hξ : δ < |ξ - ξ₀|
    · simp [hh_supp ξ hξ]
    · push Not at hξ
      have hW1 : 𝓕 w ξ = 1 := by
        rw [hfourier_w ξ]
        have h1 : |(ξ - ξ₀) / (2 * δ)| ≤ 1 / 2 := by
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * δ)]
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        have h2 : |(ξ - ξ₀) / δ| ≤ 1 := by
          rw [abs_div, abs_of_pos hδ_pos, div_le_one hδ_pos]
          exact hξ
        have ht1 : tent ((ξ - ξ₀) / (2 * δ)) = 1 - |(ξ - ξ₀) / (2 * δ)| :=
          max_eq_right (by linarith)
        have ht2 : tent ((ξ - ξ₀) / δ) = 1 - |(ξ - ξ₀) / δ| :=
          max_eq_right (by linarith)
        rw [ht1, ht2, abs_div, abs_div, abs_of_pos (by positivity : 0 < 2 * δ), abs_of_pos hδ_pos]
        have hval : 2 * (1 - |ξ - ξ₀| / (2 * δ)) - (1 - |ξ - ξ₀| / δ) = 1 := by
          field_simp [hδ_pos.ne']
          ring
        rw [hval, Complex.ofReal_one]
      have hFr_norm : ‖𝓕 r ξ‖ < 1 := by
        calc ‖𝓕 r ξ‖ ≤ ∫ x, ‖r x‖ := VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
          _ ≤ 1 / 2 := hr_L1
          _ < 1 := by norm_num
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hFr_norm, hr_fourier ξ, hW1, mul_one]
      have hsub : 1 - (1 - c⁻¹ * Φ a ξ) = c⁻¹ * Φ a ξ := by ring
      rw [hsub]
      have hΦ0 : Φ a ξ ≠ 0 := hz (2 * π * ξ)
      field_simp [hc0, hΦ0]
  -- Conclude M a q = h everywhere by Fourier inversion
  have hfh_int : Integrable (𝓕 h) := by
    have hfh_cont : Continuous (𝓕 h) := continuous_fourier_of_integrable hh_int
    have hcs : HasCompactSupport (𝓕 h) := by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := ξ₀ - δ) (b := ξ₀ + δ)) ?_
      intro ξ hξ
      simp only [Function.mem_support, ne_eq] at hξ
      by_contra hmem
      rw [mem_Icc, not_and_or] at hmem
      have : δ < |ξ - ξ₀| := by
        rcases hmem with h1 | h2
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      exact hξ (hh_supp ξ this)
    exact hfh_cont.integrable_of_hasCompactSupport hcs
  have hfun : 𝓕 (M a q) = 𝓕 h := funext hfourier_eq
  refine ⟨q, hq_cont, ⟨‖c‖⁻¹ * (B₀ * 2), hq_bdd⟩, hq_int, fun x => ?_⟩
  have h1 := hMq.1.fourierInv_fourier_eq hMq.2.2.1 (hfun ▸ hfh_int)
  have h2 := hh_cont.fourierInv_fourier_eq hh_int hfh_int
  rw [← congrFun h1 x, hfun, congrFun h2 x]

private lemma tent_partition_of_unity {lam : ℝ} (hlam : 0 < lam) {N : ℕ} (hN : 0 < N)
    {ξ : ℝ} (hξ : ξ ∈ Icc (-lam) lam) :
    let step : ℝ := lam / N
    ∑ j ∈ Finset.range (2 * N + 1), tent ((ξ - (-lam + j * step)) / step) = 1 := by
  intro step
  have hstep : 0 < step := by positivity
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  let u : ℝ := (ξ + lam) / step
  have hu0 : 0 ≤ u := div_nonneg (by linarith [hξ.1]) hstep.le
  have hu2N : u ≤ (2 * N : ℕ) := by
    dsimp [u, step]
    rw [div_le_iff₀ (by positivity)]
    push_cast
    have : (2 : ℝ) * N * (lam / N) = 2 * lam := by field_simp [hN_pos.ne']
    linarith [hξ.2]
  have harg : ∀ j : ℕ, (ξ - (-lam + j * step)) / step = u - j := fun j => by
    dsimp [u]
    field_simp [hstep.ne']
    ring
  simp_rw [harg]
  by_cases htop : u = (2 * N : ℕ)
  · rw [htop]
    rw [Finset.sum_eq_single (2 * N)]
    · simp [tent]
    · intro j hj hne
      rw [Finset.mem_range] at hj
      have hjlt : j < 2 * N := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hj) hne
      have hge : 1 ≤ |((2 * N : ℕ) : ℝ) - (j : ℝ)| := by
        have h1 : (j : ℝ) + 1 ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast hjlt
        rw [abs_of_nonneg (by linarith)]
        linarith
      exact tent_eq_zero_of_one_le hge
    · intro hmem; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) hmem
  · have hult : u < (2 * N : ℕ) := lt_of_le_of_ne hu2N htop
    let k : ℕ := ⌊u⌋₊
    have hk_le : (k : ℝ) ≤ u := Nat.floor_le hu0
    have hu_lt : u < (k : ℝ) + 1 := Nat.lt_floor_add_one u
    have hk_lt : k < 2 * N := (Nat.floor_lt hu0).mpr hult
    have hk_mem : k ∈ Finset.range (2 * N + 1) := Finset.mem_range.mpr (by omega)
    have hk1_mem : k + 1 ∈ Finset.range (2 * N + 1) := Finset.mem_range.mpr (by omega)
    have hother : ∀ j ∈ Finset.range (2 * N + 1), j ≠ k → j ≠ k + 1 → tent (u - j) = 0 := by
      intro j _ hjk hjk1
      apply tent_eq_zero_of_one_le
      by_cases hlt : j < k
      · have : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hlt
        rw [abs_of_nonneg (by linarith)]; linarith
      · have hgt : k + 2 ≤ j := by omega
        have : (k : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hgt
        rw [abs_of_neg (by linarith)]; linarith
    rw [Finset.sum_eq_add k (k + 1) (by omega) (fun j hj hne => hother j hj hne.1 hne.2)
      (fun h => absurd hk_mem h) (fun h => absurd hk1_mem h)]
    have htk : tent (u - k) = 1 - (u - k) := by
      rw [tent, abs_of_nonneg (by linarith), max_eq_right (by linarith)]
    have htk1 : tent (u - (k + 1 : ℕ)) = u - k := by
      rw [Nat.cast_add, Nat.cast_one, tent, abs_of_neg (by linarith)]
      rw [max_eq_right (by linarith)]
      ring
    rw [htk, htk1]
    ring

private lemma global_wiener_division
    {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k => 1 / (a k : ℝ)))
    (hz : ∀ t : ℝ, 1 + (∑' k, Erdos967.summand t (a k)) ≠ 0)
    {lam : ℝ} (hlam : 0 < lam)
    {G : ℝ → ℂ} (hG_cont : Continuous G) (hG_bdd : ∃ BG, ∀ x, ‖G x‖ ≤ BG)
    (hG_int : Integrable G) (hG_supp : ∀ ξ, lam < |ξ| → 𝓕 G ξ = 0) :
    ∃ (Q : ℝ → ℂ), Continuous Q ∧ (∃ BQ, ∀ x, ‖Q x‖ ≤ BQ) ∧ Integrable Q ∧
      ∀ x, M a Q x = G x := by
  have hloc := fun ξ₀ => local_wiener_division ha ha₀ hsum hz ξ₀
  choose δ hδ_pos hδ_solve using hloc
  -- Cover [-lam, lam] by open balls ball ξ₀ (δ ξ₀)
  obtain ⟨r, hr_pos, hr_cov⟩ := lebesgue_number_lemma_of_metric
    (isCompact_Icc (a := -lam) (b := lam))
    (c := fun ξ₀ : ℝ => Metric.ball ξ₀ (δ ξ₀))
    (fun _ => Metric.isOpen_ball)
    (fun ξ _ => mem_iUnion.mpr ⟨ξ, Metric.mem_ball_self (hδ_pos ξ)⟩)
  obtain ⟨N, hN_gt⟩ := exists_nat_gt (lam / (r / 2))
  have hN_pos : 0 < N := by
    by_contra h0
    have hN0 : N = 0 := by omega
    subst hN0
    simp only [Nat.cast_zero] at hN_gt
    have : 0 < lam / (r / 2) := by positivity
    linarith
  let step : ℝ := lam / N
  have hstep_pos : 0 < step := by positivity
  have hstep_lt : step < r / 2 := by
    dsimp [step]
    rw [div_lt_iff₀ (by exact_mod_cast hN_pos)]
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < r / 2)).mp hN_gt
    linarith
  let t : ℕ → ℝ := fun j => -lam + j * step
  let modK : ℕ → ℝ → ℂ := fun j x => (Real.fourierChar (t j * x) : ℂ) * (K step x : ℂ)
  have hmodK_int : ∀ j, Integrable (modK j) := fun j => by
    refine (K_integrable hstep_pos).norm.mono' ?_ ?_
    · exact ((continuous_fourierChar_coe.comp (continuous_const.mul continuous_id)).mul
        (Complex.continuous_ofReal.comp (K_continuous step))).aestronglyMeasurable
    · filter_upwards with x
      simp [modK, norm_fourierChar_coe]
  have hmodK_four : ∀ j ξ, 𝓕 (modK j) ξ = (tent ((ξ - t j) / step) : ℂ) := fun j ξ => by
    dsimp [modK]
    rw [fourier_mod, fourier_K hstep_pos]
  let piece : ℕ → ℝ → ℂ := fun j => conv G (modK j)
  obtain ⟨BG, hBG⟩ := hG_bdd
  have hpiece_props : ∀ j ∈ Finset.range (2 * N + 1),
      ∃ q : ℝ → ℂ, Continuous q ∧ (∃ Bq, ∀ x, ‖q x‖ ≤ Bq) ∧ Integrable q ∧
        ∀ x, M a q x = piece j x := by
    intro j hj
    rw [Finset.mem_range] at hj
    have ht_mem : t j ∈ Icc (-lam) lam := by
      dsimp [t, step]
      have hj_le : (j : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hj
      have hN_pos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
      constructor
      · have : 0 ≤ (j : ℝ) * (lam / N) := by positivity
        linarith
      · have : (j : ℝ) * (lam / N) ≤ 2 * N * (lam / N) :=
          mul_le_mul_of_nonneg_right hj_le (by positivity)
        have h2 : 2 * (N : ℝ) * (lam / N) = 2 * lam := by field_simp [hN_pos'.ne']
        linarith
    obtain ⟨ξ₀, hball⟩ := hr_cov (t j) ht_mem
    refine hδ_solve ξ₀ (piece j)
      (conv_continuous_left hBG hG_cont (hmodK_int j))
      ⟨BG * ∫ x, ‖modK j x‖, conv_norm_le_left' hG_cont hBG (hmodK_int j)⟩
      (conv_integrable hG_int (hmodK_int j)) ?_
    intro ξ hξ
    rw [fourier_conv hG_int (hmodK_int j) ξ, hmodK_four j ξ]
    have hgt : step < |ξ - t j| := by
      by_contra hle
      push Not at hle
      have hmem : ξ ∈ Metric.ball (t j) r := by
        rw [Metric.mem_ball, Real.dist_eq]
        linarith
      have hmem2 := hball hmem
      rw [Metric.mem_ball, Real.dist_eq] at hmem2
      linarith
    have h1 : 1 ≤ |(ξ - t j) / step| := by
      rw [abs_div, abs_of_pos hstep_pos, one_le_div hstep_pos]
      exact hgt.le
    rw [tent_eq_zero_of_one_le h1, Complex.ofReal_zero, mul_zero]
  choose q hq_cont hq_bdd hq_int hq_eq using hpiece_props
  let Q : ℝ → ℂ := fun x => ∑ j ∈ Finset.range (2 * N + 1), if hj : j ∈ Finset.range (2 * N + 1) then q j hj x else 0
  have hQ_eq : ∀ x, Q x = ∑ j ∈ (Finset.range (2 * N + 1)).attach, q j.1 j.2 x := fun x => by
    dsimp [Q]
    rw [← Finset.sum_attach (Finset.range (2 * N + 1))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [j.2]
  have hQ_cont : Continuous Q := by
    have : Q = fun x => ∑ j ∈ (Finset.range (2 * N + 1)).attach, q j.1 j.2 x := funext hQ_eq
    rw [this]
    exact continuous_finsetSum _ fun j _ => hq_cont j.1 j.2
  have hQ_int : Integrable Q := by
    have : Q = fun x => ∑ j ∈ (Finset.range (2 * N + 1)).attach, q j.1 j.2 x := funext hQ_eq
    rw [this]
    exact integrable_finsetSum _ fun j _ => hq_int j.1 j.2
  have hQ_bdd : ∃ BQ, ∀ x, ‖Q x‖ ≤ BQ := by
    choose Bq hBq using hq_bdd
    refine ⟨∑ j ∈ (Finset.range (2 * N + 1)).attach, max (Bq j.1 j.2) 0, fun x => ?_⟩
    rw [hQ_eq x]
    calc ‖∑ j ∈ (Finset.range (2 * N + 1)).attach, q j.1 j.2 x‖
        ≤ ∑ j ∈ (Finset.range (2 * N + 1)).attach, ‖q j.1 j.2 x‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ (Finset.range (2 * N + 1)).attach, max (Bq j.1 j.2) 0 :=
          Finset.sum_le_sum fun j _ => (hBq j.1 j.2 x).trans (le_max_left _ _)
  obtain ⟨BQ, hBQ⟩ := hQ_bdd
  have hQ_M : ∀ x, M a Q x = ∑ j ∈ Finset.range (2 * N + 1), piece j x := by
    intro x
    have hMQ : M a Q x = ∑ j ∈ (Finset.range (2 * N + 1)).attach, M a (q j.1 j.2) x := by
      dsimp [M]
      rw [hQ_eq x]
      simp_rw [hQ_eq, Finset.mul_sum]
      have hsumm : ∀ j ∈ (Finset.range (2 * N + 1)).attach,
          Summable (fun k => ((1 / (a k : ℝ) : ℝ) : ℂ) * q j.1 j.2 (x - Real.log (a k))) := by
        intro j _
        obtain ⟨B, hB⟩ := hq_bdd j.1 j.2
        refine Summable.of_norm_bounded (g := fun k => (1 / (a k : ℝ)) * max B 0)
          (hsum.mul_right _) fun k => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left ((hB _).trans (le_max_left _ _)) (by positivity)
      rw [Summable.tsum_finsetSum hsumm, Finset.sum_add_distrib]
    rw [hMQ]
    have h1 : ∑ j ∈ (Finset.range (2 * N + 1)).attach, M a (q j.1 j.2) x =
        ∑ j ∈ (Finset.range (2 * N + 1)).attach, piece j.1 x :=
      Finset.sum_congr rfl fun j _ => hq_eq j.1 j.2 x
    rw [h1, Finset.sum_attach (Finset.range (2 * N + 1)) (fun j => piece j x)]
  -- Show ∑ piece j = G everywhere by Fourier inversion
  let S : ℝ → ℂ := fun x => ∑ j ∈ Finset.range (2 * N + 1), piece j x
  have hS_cont : Continuous S :=
    continuous_finsetSum _ fun j _ => conv_continuous_left hBG hG_cont (hmodK_int j)
  have hS_int : Integrable S :=
    integrable_finsetSum _ fun j _ => conv_integrable hG_int (hmodK_int j)
  have hS_four : 𝓕 S = 𝓕 G := by
    ext ξ
    rw [fourier_eq_mul]
    have hsum_int : (∫ x, (Real.fourierChar (-(x * ξ)) : ℂ) * S x) =
        ∑ j ∈ Finset.range (2 * N + 1), 𝓕 (piece j) ξ := by
      dsimp [S]
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum _ fun j _ =>
        integrable_fourier_mul (conv_integrable hG_int (hmodK_int j)) ξ]
      refine Finset.sum_congr rfl fun j _ => (fourier_eq_mul (piece j) ξ).symm
    rw [hsum_int]
    have hterm : ∀ j, 𝓕 (piece j) ξ = 𝓕 G ξ * (tent ((ξ - t j) / step) : ℂ) := fun j => by
      dsimp [piece]
      rw [fourier_conv hG_int (hmodK_int j) ξ, hmodK_four j ξ]
    simp_rw [hterm, ← Finset.mul_sum]
    by_cases hξ : lam < |ξ|
    · rw [hG_supp ξ hξ, zero_mul]
    · push Not at hξ
      have hmem : ξ ∈ Icc (-lam) lam := abs_le.mp hξ
      have hpart := tent_partition_of_unity hlam hN_pos hmem
      have hpartC : (∑ j ∈ Finset.range (2 * N + 1), (tent ((ξ - t j) / step) : ℂ)) = 1 := by
        rw [← Complex.ofReal_sum]
        simpa [t, step] using congrArg Complex.ofReal hpart
      rw [hpartC, mul_one]
  have hfG_int : Integrable (𝓕 G) := by
    have hcs : HasCompactSupport (𝓕 G) := by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -lam) (b := lam)) ?_
      intro ξ hξ
      simp only [Function.mem_support, ne_eq] at hξ
      by_contra hmem
      exact hξ (hG_supp ξ (lt_of_not_ge fun hle => hmem (abs_le.mp hle)))
    exact (continuous_fourier_of_integrable hG_int).integrable_of_hasCompactSupport hcs
  have hSG : S = G := by
    have h1 := hS_cont.fourierInv_fourier_eq hS_int (hS_four ▸ hfG_int)
    have h2 := hG_cont.fourierInv_fourier_eq hG_int hfG_int
    rw [← h1, hS_four, h2]
  exact ⟨Q, hQ_cont, ⟨BQ, hBQ⟩, hQ_int, fun x => (hQ_M x).trans (congrFun hSG x)⟩

/- Section 5: Main Tauberian implication -/

private lemma convolution_M_tendsto_zero
    {a : ℕ → ℕ} (ha : StrictMono a) (ha₀ : 1 < a 0)
    (hsum : Summable (fun k => 1 / (a k : ℝ)))
    {F : ℝ → ℝ} {B : ℝ} (_hB : 0 ≤ B)
    (hF_meas : Measurable F) (hF_bdd : ∀ s, |F s| ≤ B)
    (hH_lim : Tendsto (fun t : ℝ => F t + ∑' k, (1 / (a k : ℝ)) * F (t - Real.log (a k))) atTop (𝓝 0))
    {Q : ℝ → ℂ} {BQ : ℝ} (hBQ : 0 ≤ BQ)
    (hQ_cont : Continuous Q) (hQ_bdd : ∀ x, ‖Q x‖ ≤ BQ) (hQ_int : Integrable Q) :
    Tendsto (fun t : ℝ => ∫ s : ℝ, M a Q s * (F (t - s) : ℂ)) atTop (𝓝 0) := by
  let H : ℝ → ℝ := fun t => F t + ∑' k, (1 / (a k : ℝ)) * F (t - Real.log (a k))
  have hH_meas : Measurable H := by
    refine hF_meas.add ?_
    exact Measurable.tsum fun k => measurable_const.mul (hF_meas.comp (measurable_id.sub measurable_const))
  have hH_bdd : ∀ t, |H t| ≤ B * (1 + ∑' k, 1 / (a k : ℝ)) := fun t => by
    have hsumm : Summable (fun k => ‖(1 / (a k : ℝ)) * F (t - Real.log (a k))‖) :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (hF_bdd _) (by positivity)) (hsum.mul_right B)
    calc |H t| ≤ |F t| + |∑' k, (1 / (a k : ℝ)) * F (t - Real.log (a k))| := abs_add_le _ _
      _ ≤ B + ∑' k, |(1 / (a k : ℝ)) * F (t - Real.log (a k))| :=
          add_le_add (hF_bdd t) (by simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsumm)
      _ ≤ B + ∑' k, (1 / (a k : ℝ)) * B :=
          add_le_add le_rfl (Summable.tsum_le_tsum (fun k => by
            rw [abs_mul, abs_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left (hF_bdd _) (by positivity))
            (by simpa [Real.norm_eq_abs] using hsumm) (hsum.mul_right B))
      _ = B * (1 + ∑' k, 1 / (a k : ℝ)) := by rw [tsum_mul_right]; ring
  have hswap_eq : ∀ t : ℝ, (∫ s : ℝ, M a Q s * (F (t - s) : ℂ)) = ∫ s : ℝ, Q s * (H (t - s) : ℂ) := by
    intro t
    have hMQ := M_properties ha ha₀ hsum hBQ hQ_cont hQ_bdd hQ_int
    have hF_shift_meas : Measurable (fun s : ℝ => (F (t - s) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hF_meas.comp (measurable_const.sub measurable_id))
    have hterm1 : Integrable (fun s => Q s * (F (t - s) : ℂ)) :=
      (hQ_int.norm.const_mul B).mono' (hQ_cont.aestronglyMeasurable.mul hF_shift_meas.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun s => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
          exact mul_le_mul_of_nonneg_right (hF_bdd _) (norm_nonneg _))
    have hterm_k : ∀ k, Integrable (fun s => ((1 / (a k : ℝ) : ℝ) : ℂ) * Q (s - Real.log (a k)) * (F (t - s) : ℂ)) :=
      fun k => by
        have hQk : Integrable (fun s => Q (s - Real.log (a k))) := hQ_int.comp_sub_right _
        refine (hQk.norm.const_mul ((1 / (a k : ℝ)) * B)).mono' ?_ ?_
        · exact ((continuous_const.mul (hQ_cont.comp (continuous_id.sub continuous_const))).aestronglyMeasurable.mul
            hF_shift_meas.aestronglyMeasurable)
        · filter_upwards with s
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
            Complex.norm_real, Real.norm_eq_abs]
          have := mul_le_mul_of_nonneg_left (hF_bdd (t - s)) (mul_nonneg (by positivity : 0 ≤ 1 / (a k : ℝ)) (norm_nonneg (Q (s - Real.log (a k)))))
          linarith
    have hterm_k_norm : ∀ k, ∫ s, ‖((1 / (a k : ℝ) : ℝ) : ℂ) * Q (s - Real.log (a k)) * (F (t - s) : ℂ)‖ ≤
        (1 / (a k : ℝ)) * (B * ∫ s, ‖Q s‖) := fun k => by
      have hQk : Integrable (fun s => Q (s - Real.log (a k))) := hQ_int.comp_sub_right _
      calc ∫ s, ‖((1 / (a k : ℝ) : ℝ) : ℂ) * Q (s - Real.log (a k)) * (F (t - s) : ℂ)‖
          ≤ ∫ s, (1 / (a k : ℝ)) * B * ‖Q (s - Real.log (a k))‖ :=
            integral_mono (hterm_k k).norm (hQk.norm.const_mul _) fun s => by
              rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
                Complex.norm_real, Real.norm_eq_abs]
              have := mul_le_mul_of_nonneg_left (hF_bdd (t - s))
                (mul_nonneg (by positivity : 0 ≤ 1 / (a k : ℝ)) (norm_nonneg (Q (s - Real.log (a k)))))
              linarith
        _ = (1 / (a k : ℝ)) * B * ∫ s, ‖Q (s - Real.log (a k))‖ := integral_const_mul _ _
        _ = (1 / (a k : ℝ)) * (B * ∫ s, ‖Q s‖) := by
            rw [integral_sub_right_eq_self (fun s => ‖Q s‖) (Real.log (a k))]; ring
    have hsum_k : Summable (fun k => ∫ s, ‖((1 / (a k : ℝ) : ℝ) : ℂ) * Q (s - Real.log (a k)) * (F (t - s) : ℂ)‖) :=
      Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) hterm_k_norm (hsum.mul_right _)
    have hterm_k2 : ∀ k, Integrable (fun s => Q s * (((1 / (a k : ℝ) : ℝ) : ℂ) * (F (t - s - Real.log (a k)) : ℂ))) :=
      fun k => by
        refine (hQ_int.norm.const_mul ((1 / (a k : ℝ)) * B)).mono' ?_ ?_
        · exact hQ_cont.aestronglyMeasurable.mul (measurable_const.mul
            (Complex.continuous_ofReal.measurable.comp
              (hF_meas.comp ((measurable_const.sub measurable_id).sub measurable_const)))).aestronglyMeasurable
        · filter_upwards with s
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
            Complex.norm_real, Real.norm_eq_abs]
          have := mul_le_mul_of_nonneg_left (hF_bdd (t - s - Real.log (a k)))
            (mul_nonneg (norm_nonneg (Q s)) (by positivity : 0 ≤ 1 / (a k : ℝ)))
          linarith
    have hterm_k2_eq : ∀ k,
        (∫ s, ((1 / (a k : ℝ) : ℝ) : ℂ) * Q (s - Real.log (a k)) * (F (t - s) : ℂ)) =
        ∫ s, Q s * (((1 / (a k : ℝ) : ℝ) : ℂ) * (F (t - s - Real.log (a k)) : ℂ)) := fun k => by
      have hsub := integral_sub_right_eq_self (μ := volume)
        (fun s : ℝ => ((1 / (a k : ℝ) : ℝ) : ℂ) * Q (s - Real.log (a k)) * (F (t - s) : ℂ))
        (-Real.log (a k))
      rw [← hsub]
      congr 1 with s
      have hs1 : s - -Real.log (a k) - Real.log (a k) = s := by ring
      have hs2 : t - (s - -Real.log (a k)) = t - s - Real.log (a k) := by ring
      rw [hs1, hs2]
      ring
    have hsum_k2 : Summable (fun k => ∫ s, ‖Q s * (((1 / (a k : ℝ) : ℝ) : ℂ) * (F (t - s - Real.log (a k)) : ℂ))‖) := by
      refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_) (hsum.mul_right (B * ∫ s, ‖Q s‖))
      calc ∫ s, ‖Q s * (((1 / (a k : ℝ) : ℝ) : ℂ) * (F (t - s - Real.log (a k)) : ℂ))‖
          ≤ ∫ s, (1 / (a k : ℝ)) * B * ‖Q s‖ :=
            integral_mono (hterm_k2 k).norm (hQ_int.norm.const_mul _) fun s => by
              rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
                Complex.norm_real, Real.norm_eq_abs]
              have := mul_le_mul_of_nonneg_left (hF_bdd (t - s - Real.log (a k)))
                (mul_nonneg (norm_nonneg (Q s)) (by positivity : 0 ≤ 1 / (a k : ℝ)))
              linarith
        _ = (1 / (a k : ℝ)) * (B * ∫ s, ‖Q s‖) := by rw [integral_const_mul]; ring
    have htsum_int1 : Integrable (fun s => ∑' k, ((1 / (a k : ℝ) : ℝ) : ℂ) * Q (s - Real.log (a k)) * (F (t - s) : ℂ)) :=
      integrable_tsum_of_summable_norm hterm_k (fun s =>
        Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
            Complex.norm_real, Real.norm_eq_abs]
          have h1 := mul_le_mul (hQ_bdd (s - Real.log (a k))) (hF_bdd (t - s)) (abs_nonneg _) hBQ
          have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 1 / (a k : ℝ))
          linarith) (hsum.mul_right (BQ * B))) hsum_k
    have htsum_int2 : Integrable (fun s => ∑' k, Q s * (((1 / (a k : ℝ) : ℝ) : ℂ) * (F (t - s - Real.log (a k)) : ℂ))) :=
      integrable_tsum_of_summable_norm hterm_k2 (fun s =>
        Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
            Complex.norm_real, Real.norm_eq_abs]
          have h1 := mul_le_mul (hQ_bdd s) (hF_bdd (t - s - Real.log (a k))) (abs_nonneg _) hBQ
          have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 1 / (a k : ℝ))
          linarith) (hsum.mul_right (BQ * B))) hsum_k2
    have hLHS : (fun s => M a Q s * (F (t - s) : ℂ)) =
        fun s => Q s * (F (t - s) : ℂ) +
          ∑' k, ((1 / (a k : ℝ) : ℝ) : ℂ) * Q (s - Real.log (a k)) * (F (t - s) : ℂ) := by
      ext s
      dsimp [M]
      rw [add_mul, tsum_mul_right]
    have hRHS : (fun s => Q s * (H (t - s) : ℂ)) =
        fun s => Q s * (F (t - s) : ℂ) +
          ∑' k, Q s * (((1 / (a k : ℝ) : ℝ) : ℂ) * (F (t - s - Real.log (a k)) : ℂ)) := by
      ext s
      dsimp [H]
      rw [Complex.ofReal_add, mul_add, Complex.ofReal_tsum, tsum_mul_left]
      simp_rw [Complex.ofReal_mul]
    rw [hLHS, integral_add hterm1 htsum_int1, hRHS, integral_add hterm1 htsum_int2]
    congr 1
    rw [← integral_tsum_of_summable_integral_norm hterm_k hsum_k,
      ← integral_tsum_of_summable_integral_norm hterm_k2 hsum_k2]
    exact tsum_congr fun k => hterm_k2_eq k
  simp_rw [hswap_eq]
  have hzero : (0 : ℂ) = ∫ s : ℝ, (0 : ℂ) := by simp
  rw [hzero]
  let C_H : ℝ := B * (1 + ∑' k, 1 / (a k : ℝ))
  refine tendsto_integral_filter_of_dominated_convergence (fun s => ‖Q s‖ * C_H) ?_ ?_ ?_ ?_
  · filter_upwards with t
    exact hQ_cont.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.measurable.comp (hH_meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · filter_upwards with t
    filter_upwards with s
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hH_bdd (t - s)) (norm_nonneg _)
  · exact hQ_int.norm.mul_const C_H
  · filter_upwards with s
    have hts : Tendsto (fun t : ℝ => t - s) atTop atTop := tendsto_id.atTop_add tendsto_const_nhds
    have hHs : Tendsto (fun t : ℝ => (H (t - s) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
      simpa [H, Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp (hH_lim.comp hts)
    simpa using tendsto_const_nhds.mul hHs

private lemma fejer_approx_indicator_exp {A B : ℝ} (_hAB : A < B) :
    let g : ℝ → ℂ := (Ioc A B).indicator (fun s => (Real.exp (-2 * s) : ℂ))
    Tendsto (fun lam : ℝ => ∫ x : ℝ, ‖conv (fun s => (K lam s : ℂ)) g x - g x‖) atTop (𝓝 0) := by
  intro g
  have hg_meas : Measurable g :=
    (Complex.continuous_ofReal.measurable.comp
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))).indicator measurableSet_Ioc
  have hg_int : Integrable g := by
    have hcont : Continuous (fun s : ℝ => (Real.exp (-2 * s) : ℂ)) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    exact (hcont.integrableOn_Ioc).integrable_indicator measurableSet_Ioc
  have hg_L1_tr : Tendsto (fun h : ℝ => ∫ x : ℝ, ‖g (x - h) - g x‖) (𝓝 0) (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ x : ℝ, (0 : ℝ) := by simp
    nth_rewrite 2 [h0]
    let M0 : ℝ := 2 * Real.exp (-2 * (A - 1))
    refine tendsto_integral_filter_of_dominated_convergence
      ((Icc (A - 1) (B + 1)).indicator (fun _ => M0)) ?_ ?_ ?_ ?_
    · filter_upwards with h
      exact ((hg_int.comp_sub_right h).sub hg_int).norm.aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with h hh
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_norm]
      by_cases hx : x ∈ Icc (A - 1) (B + 1)
      · rw [Set.indicator_of_mem hx]
        have hbnd : ∀ s : ℝ, ‖g s‖ ≤ Real.exp (-2 * (A - 1)) := fun s => by
          dsimp [g]
          by_cases hs : s ∈ Ioc A B
          · rw [Set.indicator_of_mem hs, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
            exact Real.exp_le_exp.mpr (by linarith [hs.1])
          · rw [Set.indicator_of_notMem hs, norm_zero]
            exact (Real.exp_pos _).le
        calc ‖g (x - h) - g x‖ ≤ ‖g (x - h)‖ + ‖g x‖ := norm_sub_le _ _
          _ ≤ Real.exp (-2 * (A - 1)) + Real.exp (-2 * (A - 1)) := add_le_add (hbnd _) (hbnd _)
          _ = M0 := by ring
      · rw [Set.indicator_of_notMem hx]
        have hx1 : x ∉ Ioc A B := fun hmem => hx ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
        have hx2 : x - h ∉ Ioc A B := fun hmem => by
          have habs := abs_lt.mp hh
          exact hx ⟨by linarith [hmem.1, habs.1, habs.2], by linarith [hmem.2, habs.1, habs.2]⟩
        simp [g, hx1, hx2]
    · exact (integrableOn_const (hs := measure_Icc_lt_top.ne)).integrable_indicator measurableSet_Icc
    · have hae : ∀ᵐ x : ℝ ∂volume, x ≠ A ∧ x ≠ B := by
        have hA : ({A} : Set ℝ)ᶜ ∈ ae volume := mem_ae_iff.mpr (by simp)
        have hB : ({B} : Set ℝ)ᶜ ∈ ae volume := mem_ae_iff.mpr (by simp)
        filter_upwards [hA, hB] with x hxA hxB
        exact ⟨hxA, hxB⟩
      filter_upwards [hae] with x ⟨hxA, hxB⟩
      have hcont_at : ContinuousAt g x := by
        by_cases hx : x ∈ Ioo A B
        · have hev : g =ᶠ[𝓝 x] (fun s => (Real.exp (-2 * s) : ℂ)) := by
            filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
            exact Set.indicator_of_mem (show s ∈ Ioc A B from ⟨hs.1, hs.2.le⟩) _
          exact ((Complex.continuous_ofReal.comp
            (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousAt).congr hev.symm
        · have hnot : x ∉ Icc A B := fun hmem => hx ⟨lt_of_le_of_ne hmem.1 hxA.symm, lt_of_le_of_ne hmem.2 hxB⟩
          have hev : g =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
            filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hnot] with s hs
            exact Set.indicator_of_notMem (fun hmem => hs ⟨hmem.1.le, hmem.2⟩) _
          exact continuousAt_const.congr hev.symm
      have hsub_t : Tendsto (fun h : ℝ => x - h) (𝓝 0) (𝓝 x) := by
        have hc : Continuous (fun h : ℝ => x - h) := continuous_const.sub continuous_id
        simpa using hc.continuousAt (x := (0 : ℝ)).tendsto
      have hlim : Tendsto (fun h : ℝ => ‖g (x - h) - g x‖) (𝓝 0) (𝓝 ‖g x - g x‖) :=
        ((hcont_at.tendsto.comp hsub_t).sub tendsto_const_nhds).norm
      simpa using hlim
  -- Bound the L1 error by ∫ z, fejer z * ∫ x, ‖g (x - z / lam) - g x‖
  have hbound : ∀ lam : ℝ, 0 < lam →
      ∫ x : ℝ, ‖conv (fun s => (K lam s : ℂ)) g x - g x‖ ≤
      ∫ z : ℝ, fejer z * (∫ x : ℝ, ‖g (x - z / lam) - g x‖) := by
    intro lam hlam
    have hK_int : Integrable (fun s => (K lam s : ℂ)) := (K_integrable hlam).ofReal
    have hdiff_eq : ∀ x, conv (fun s => (K lam s : ℂ)) g x - g x =
        ∫ z : ℝ, (fejer z : ℂ) * (g (x - z / lam) - g x) := fun x => by
      rw [conv_eq]
      have h1 : g x = ∫ y : ℝ, (K lam y : ℂ) * g x := by
        rw [integral_mul_const, integral_complex_ofReal', integral_K hlam, Complex.ofReal_one, one_mul]
      nth_rewrite 1 [h1]
      have hint1 : Integrable (fun y : ℝ => (K lam y : ℂ) * g (x - y)) := by
        have hcont : Continuous (fun y : ℝ => (K lam y : ℂ)) :=
          Complex.continuous_ofReal.comp (K_continuous lam)
        refine ((hg_int.comp_sub_left x).norm.const_mul lam).mono'
          (hcont.aestronglyMeasurable.mul (hg_int.comp_sub_left x).aestronglyMeasurable) ?_
        filter_upwards with y
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (K_nonneg hlam y)]
        exact mul_le_mul_of_nonneg_right (K_le hlam y) (norm_nonneg _)
      have hint2 : Integrable (fun y : ℝ => (K lam y : ℂ) * g x) := hK_int.mul_const _
      rw [← integral_sub hint1 hint2]
      have h2 : (∫ y : ℝ, ((K lam y : ℂ) * g (x - y) - (K lam y : ℂ) * g x)) =
          (lam : ℂ) * ∫ y : ℝ, (fejer (lam * y) : ℂ) * (g (x - (lam * y) / lam) - g x) := by
        rw [← integral_const_mul]
        congr 1 with y
        rw [mul_div_cancel_left₀ _ hlam.ne']
        simp only [K, Complex.ofReal_mul]
        ring
      rw [h2, Measure.integral_comp_mul_left
        (g := fun z : ℝ => (fejer z : ℂ) * (g (x - z / lam) - g x)) lam, abs_inv, abs_of_pos hlam]
      rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam.ne',
        Complex.ofReal_one, one_mul]
    have hprod_int : Integrable (fun p : ℝ × ℝ => fejer p.2 * ‖g (p.1 - p.2 / lam) - g p.1‖) (volume.prod volume) := by
      have h1 : Integrable (fun p : ℝ × ℝ => fejer p.2 * ‖g (p.1 - p.2 / lam)‖) (volume.prod volume) := by
        have hcomp := (K_integrable hlam).convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hg_int.norm
        have hchg : Integrable (fun p : ℝ × ℝ => (K lam p.2) * ‖g (p.1 - p.2)‖) (volume.prod volume) := by
          simpa using hcomp
        have heq : (fun p : ℝ × ℝ => fejer p.2 * ‖g (p.1 - p.2 / lam)‖) =
            fun p : ℝ × ℝ => lam⁻¹ * (K lam (lam⁻¹ * p.2) * ‖g (p.1 - lam⁻¹ * p.2)‖) := by
          ext ⟨x, z⟩
          dsimp [K]
          rw [mul_inv_cancel_left₀ hlam.ne', div_eq_inv_mul]
          field_simp [hlam.ne']
        rw [heq]
        have hmap : Measure.map (fun p : ℝ × ℝ => (p.1, lam⁻¹ * p.2)) (volume.prod volume) =
            ENNReal.ofReal lam • (volume.prod volume) := by
          have h1d : Measure.map (fun z : ℝ => lam⁻¹ * z) volume = ENNReal.ofReal lam • volume := by
            have hval : |lam⁻¹⁻¹| = lam := by rw [inv_inv, abs_of_pos hlam]
            rw [Real.map_volume_mul_left (inv_ne_zero hlam.ne'), hval]
          have hprod_map := Measure.map_prod_map (μa := (volume : Measure ℝ)) (μc := (volume : Measure ℝ))
            (f := id) (g := fun z : ℝ => lam⁻¹ * z) measurable_id (measurable_const.mul measurable_id)
          rw [Measure.map_id, h1d, Measure.prod_smul_right] at hprod_map
          exact hprod_map.symm
        have hint_smul : Integrable (fun p : ℝ × ℝ => K lam p.2 * ‖g (p.1 - p.2)‖)
            (Measure.map (fun p : ℝ × ℝ => (p.1, lam⁻¹ * p.2)) (volume.prod volume)) := by
          rw [hmap]
          exact hchg.smul_measure ENNReal.ofReal_ne_top
        exact (integrable_map_measure hint_smul.aestronglyMeasurable
          (measurable_fst.prodMk (measurable_const.mul measurable_snd)).aemeasurable |>.mp hint_smul).const_mul lam⁻¹
      have h2 : Integrable (fun p : ℝ × ℝ => fejer p.2 * ‖g p.1‖) (volume.prod volume) := by
        simpa [mul_comm] using hg_int.norm.mul_prod fejer_integrable
      refine (h1.add h2).mono' ?_ ?_
      · exact ((fejer_continuous.measurable.comp measurable_snd).mul
          ((hg_meas.comp (measurable_fst.sub (measurable_snd.div_const lam))).sub
            (hg_meas.comp measurable_fst)).norm).aestronglyMeasurable
      · filter_upwards with ⟨x, z⟩
        rw [Real.norm_of_nonneg (mul_nonneg (fejer_nonneg z) (norm_nonneg _))]
        exact (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (fejer_nonneg z)).trans_eq (mul_add _ _ _)
    calc ∫ x : ℝ, ‖conv (fun s => (K lam s : ℂ)) g x - g x‖
        ≤ ∫ x : ℝ, ∫ z : ℝ, fejer z * ‖g (x - z / lam) - g x‖ := by
          refine integral_mono ((conv_integrable hK_int hg_int).sub hg_int).norm
            hprod_int.integral_prod_left fun x => ?_
          rw [hdiff_eq x]
          calc ‖∫ z : ℝ, (fejer z : ℂ) * (g (x - z / lam) - g x)‖
              ≤ ∫ z : ℝ, ‖(fejer z : ℂ) * (g (x - z / lam) - g x)‖ := norm_integral_le_integral_norm _
            _ = ∫ z : ℝ, fejer z * ‖g (x - z / lam) - g x‖ := by
                congr 1 with z
                rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fejer_nonneg z)]
      _ = ∫ z : ℝ, ∫ x : ℝ, fejer z * ‖g (x - z / lam) - g x‖ := integral_integral_swap hprod_int
      _ = ∫ z : ℝ, fejer z * (∫ x : ℝ, ‖g (x - z / lam) - g x‖) := by
          congr 1 with z
          rw [integral_const_mul]
  -- Dominated convergence as lam → ∞ on the outer integral
  have hrhs_lim : Tendsto (fun lam : ℝ => ∫ z : ℝ, fejer z * (∫ x : ℝ, ‖g (x - z / lam) - g x‖)) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ z : ℝ, (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z : ℝ => fejer z * (2 * ∫ x, ‖g x‖)) ?_ ?_ ?_ ?_
    · filter_upwards with lam
      have hcont_tr : Continuous (fun h : ℝ => ∫ x : ℝ, ‖g (x - h) - g x‖) := by
        rw [Metric.continuous_iff]
        intro h₀ ε hε
        obtain ⟨δ, hδ, hball⟩ := Metric.tendsto_nhds_nhds.mp hg_L1_tr ε hε
        refine ⟨δ, hδ, fun h hh => ?_⟩
        rw [Real.dist_eq] at hh ⊢
        have hdiff : |(∫ x : ℝ, ‖g (x - h) - g x‖) - (∫ x : ℝ, ‖g (x - h₀) - g x‖)| ≤
            ∫ x : ℝ, ‖g (x - (h - h₀)) - g x‖ := by
          have hi1 : Integrable (fun x : ℝ => ‖g (x - h) - g x‖) :=
            ((hg_int.comp_sub_right h).sub hg_int).norm
          have hi2 : Integrable (fun x : ℝ => ‖g (x - h₀) - g x‖) :=
            ((hg_int.comp_sub_right h₀).sub hg_int).norm
          have hi3 : Integrable (fun x : ℝ => ‖g (x - h) - g (x - h₀)‖) :=
            ((hg_int.comp_sub_right h).sub (hg_int.comp_sub_right h₀)).norm
          calc |(∫ x : ℝ, ‖g (x - h) - g x‖) - (∫ x : ℝ, ‖g (x - h₀) - g x‖)|
              = |∫ x : ℝ, (‖g (x - h) - g x‖ - ‖g (x - h₀) - g x‖)| := by rw [integral_sub hi1 hi2]
            _ ≤ ∫ x : ℝ, |‖g (x - h) - g x‖ - ‖g (x - h₀) - g x‖| := by
                simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => ‖g (x - h) - g x‖ - ‖g (x - h₀) - g x‖)
            _ ≤ ∫ x : ℝ, ‖g (x - h) - g (x - h₀)‖ :=
                integral_mono (hi1.sub hi2).abs hi3 fun x => by
                  simpa [sub_sub_sub_cancel_right] using abs_norm_sub_norm_le (g (x - h) - g x) (g (x - h₀) - g x)
            _ = ∫ y : ℝ, ‖g (y - (h - h₀)) - g y‖ := by
                have hsh := integral_sub_right_eq_self (μ := volume)
                  (fun y : ℝ => ‖g (y - (h - h₀)) - g y‖) h₀
                rw [← hsh]
                congr 1 with x
                have hx_eq : x - h₀ - (h - h₀) = x - h := by ring
                rw [hx_eq]
        have hlt := hball (by simpa [Real.dist_eq] using hh)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at hlt
        exact hdiff.trans_lt hlt
      exact fejer_continuous.aestronglyMeasurable.mul
        (hcont_tr.comp (continuous_id.div_const lam)).aestronglyMeasurable
    · filter_upwards with lam
      filter_upwards with z
      rw [Real.norm_of_nonneg (mul_nonneg (fejer_nonneg z) (integral_nonneg fun _ => norm_nonneg _))]
      refine mul_le_mul_of_nonneg_left ?_ (fejer_nonneg z)
      calc ∫ x, ‖g (x - z / lam) - g x‖
          ≤ ∫ x, (‖g (x - z / lam)‖ + ‖g x‖) :=
            integral_mono ((hg_int.comp_sub_right _).sub hg_int).norm
              ((hg_int.comp_sub_right _).norm.add hg_int.norm) fun x => norm_sub_le _ _
        _ = (∫ x, ‖g (x - z / lam)‖) + (∫ x, ‖g x‖) :=
            integral_add (hg_int.comp_sub_right _).norm hg_int.norm
        _ = 2 * ∫ x, ‖g x‖ := by rw [integral_sub_right_eq_self (fun x => ‖g x‖) (z / lam)]; ring
    · exact fejer_integrable.mul_const _
    · filter_upwards with z
      have hzlim : Tendsto (fun lam : ℝ => z / lam) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa using tendsto_const_nhds.mul (hg_L1_tr.comp hzlim)
  refine squeeze_zero' (Filter.Eventually.of_forall fun lam => integral_nonneg fun _ => norm_nonneg _)
    (Filter.Eventually.mono (Ioi_mem_atTop 0) hbound) hrhs_lim

private lemma solution_aux : OMA.R_Erdos967_erdos_967_variants_tauberian_R1.H1 := by
  intro a ha ha₀ hsum hz f hm hn hf₀ hbdd hlim u v hu huv
  -- Helper: for every x, k ↦ f (x / a k) has finite support hence is summable
  have hf_fin_supp : ∀ x : ℝ, ∀ᶠ k : ℕ in atTop, f (x / (a k : ℝ)) = 0 := by
    intro x
    obtain ⟨K, hK⟩ := exists_nat_gt x
    filter_upwards [Filter.eventually_ge_atTop (max K 1)] with k hk
    have hk_le : k ≤ a k := ha.id_le k
    have hK_le : (K : ℝ) ≤ (a k : ℝ) := by exact_mod_cast (le_trans (le_max_left K 1) hk).trans hk_le
    have ha_pos : (0 : ℝ) < (a k : ℝ) := by exact_mod_cast (lt_trans zero_lt_one (a_gt_one ha ha₀ k))
    apply hf₀
    rw [div_lt_one ha_pos]
    linarith
  have hf_summable : ∀ x : ℝ, Summable (fun k : ℕ => f (x / (a k : ℝ))) := fun x =>
    summable_of_ne_finset_zero (s := Finset.range (Nat.ceil (max x 0) + 1)) fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      have hk_le : k ≤ a k := ha.id_le k
      have ha_pos : (0 : ℝ) < (a k : ℝ) := by exact_mod_cast (lt_trans zero_lt_one (a_gt_one ha ha₀ k))
      apply hf₀
      rw [div_lt_one ha_pos]
      have hceil : max x 0 ≤ (Nat.ceil (max x 0) : ℝ) := Nat.le_ceil _
      have hk_real : (Nat.ceil (max x 0) : ℝ) + 1 ≤ (a k : ℝ) := by exact_mod_cast hk.trans hk_le
      linarith [le_max_left x 0]
  -- Define F(s) = f(exp s) * exp(-s) - 1
  let F : ℝ → ℝ := fun s => f (Real.exp s) * Real.exp (-s) - 1
  have hF_meas : Measurable F :=
    ((hm.measurable.comp Real.continuous_exp.measurable).mul
      (Real.continuous_exp.comp continuous_neg).measurable).sub measurable_const
  -- Boundedness of F
  have hF_bdd_ex : ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, |F s| ≤ B := by
    have hev := hlim.eventually (gt_mem_nhds (lt_add_one (1 + ∑' k, 1 / (a k : ℝ))))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨X₀, hX₀⟩ := hev
    let X : ℝ := max X₀ 1
    have hX1 : 1 ≤ X := le_max_right _ _
    let B₀ : ℝ := max ((1 + ∑' k, 1 / (a k : ℝ)) + 1) (f X)
    have hB₀ : 0 ≤ B₀ := (hn X).trans (le_max_right _ _)
    refine ⟨B₀ + 1, by linarith, fun s => ?_⟩
    have hexp_pos : 0 < Real.exp s := Real.exp_pos s
    have hlow : 0 ≤ f (Real.exp s) * Real.exp (-s) := mul_nonneg (hn _) (Real.exp_pos _).le
    have hhigh : f (Real.exp s) * Real.exp (-s) ≤ B₀ := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      by_cases hx : X ≤ Real.exp s
      · have hle := hX₀ (Real.exp s) ((le_max_left X₀ 1).trans hx)
        have htsum_nonneg : 0 ≤ ∑' k, f (Real.exp s / (a k : ℝ)) :=
          tsum_nonneg fun k => hn _
        have hdiv : f (Real.exp s) / Real.exp s ≤
            (f (Real.exp s) + ∑' k, f (Real.exp s / (a k : ℝ))) / Real.exp s :=
          div_le_div_of_nonneg_right (by linarith) hexp_pos.le
        exact (hdiv.trans hle.le).trans (le_max_left _ _)
      · push Not at hx
        by_cases hx1 : 1 ≤ Real.exp s
        · calc f (Real.exp s) / Real.exp s
              ≤ f X / 1 := div_le_div₀ (hn X) (hm hx.le) zero_lt_one hx1
            _ = f X := div_one _
            _ ≤ B₀ := le_max_right _ _
        · push Not at hx1
          rw [hf₀ _ hx1, zero_div]
          exact hB₀
    dsimp [F]
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨B, hB, hF_bdd⟩ := hF_bdd_ex
  -- Log-scale limit H(t) → 0
  have hH_lim : Tendsto (fun t : ℝ => F t + ∑' k, (1 / (a k : ℝ)) * F (t - Real.log (a k))) atTop (𝓝 0) := by
    have hsub : Tendsto (fun t : ℝ =>
        (f (Real.exp t) + ∑' k, f (Real.exp t / (a k : ℝ))) / Real.exp t -
        (1 + ∑' k, 1 / (a k : ℝ))) atTop (𝓝 0) := by
      simpa using (hlim.comp Real.tendsto_exp_atTop).sub
        (tendsto_const_nhds (x := 1 + ∑' k, 1 / (a k : ℝ)))
    refine hsub.congr fun t => ?_
    have hexp_pos : 0 < Real.exp t := Real.exp_pos t
    have hterm_eq : ∀ k : ℕ, (1 / (a k : ℝ)) * F (t - Real.log (a k)) =
        f (Real.exp t / (a k : ℝ)) / Real.exp t - 1 / (a k : ℝ) := fun k => by
      have ha_pos : (0 : ℝ) < (a k : ℝ) := by exact_mod_cast (lt_trans zero_lt_one (a_gt_one ha ha₀ k))
      dsimp [F]
      rw [Real.exp_sub, Real.exp_log ha_pos]
      have hneg : Real.exp (-(t - Real.log (a k))) = (a k : ℝ) / Real.exp t := by
        rw [neg_sub, Real.exp_sub, Real.exp_log ha_pos]
      rw [hneg]
      field_simp [ha_pos.ne', hexp_pos.ne']
    have h1 : (∑' k, (1 / (a k : ℝ)) * F (t - Real.log (a k))) =
        (∑' k, f (Real.exp t / (a k : ℝ)) / Real.exp t) - ∑' k, 1 / (a k : ℝ) := by
      simp_rw [hterm_eq]
      exact ((hf_summable (Real.exp t)).div_const (Real.exp t)).tsum_sub hsum
    rw [h1, tsum_div_const]
    dsimp [F]
    rw [Real.exp_neg, ← div_eq_mul_inv]
    ring
  -- Define target test function g on log scale
  let A : ℝ := -Real.log v
  let B_int : ℝ := -Real.log u
  have hAB : A < B_int := by
    dsimp [A, B_int]
    linarith [Real.log_lt_log hu huv]
  let g : ℝ → ℂ := (Ioc A B_int).indicator (fun s => (Real.exp (-2 * s) : ℂ))
  have hg_int : Integrable g := by
    have hcont : Continuous (fun s : ℝ => (Real.exp (-2 * s) : ℂ)) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    exact (hcont.integrableOn_Ioc).integrable_indicator measurableSet_Ioc
  -- Show ∫ s, g s * (F (t - s) : ℂ) → 0 as t → ∞
  have hgF_lim : Tendsto (fun t : ℝ => ∫ s : ℝ, g s * (F (t - s) : ℂ)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have happrox := fejer_approx_indicator_exp hAB
    have heps1 : 0 < ε / (2 * (B + 1)) := by positivity
    obtain ⟨lam₀, hlam₀⟩ := (Metric.tendsto_atTop.mp happrox (ε / (2 * (B + 1))) heps1)
    let lam : ℝ := max lam₀ 1
    have hlam_pos : 0 < lam := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hL1_small : ∫ s : ℝ, ‖conv (fun r => (K lam r : ℂ)) g s - g s‖ < ε / (2 * (B + 1)) := by
      have h := hlam₀ lam (le_max_left _ _)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at h
      exact h
    let G : ℝ → ℂ := conv (fun r => (K lam r : ℂ)) g
    have hK_cont : Continuous (fun r => (K lam r : ℂ)) := Complex.continuous_ofReal.comp (K_continuous lam)
    have hK_bdd : ∀ r, ‖(K lam r : ℂ)‖ ≤ lam := fun r => by
      rw [Complex.norm_real, Real.norm_of_nonneg (K_nonneg hlam_pos r)]
      exact K_le hlam_pos r
    have hK_int : Integrable (fun r => (K lam r : ℂ)) := (K_integrable hlam_pos).ofReal
    have hG_cont : Continuous G := conv_continuous_left hK_bdd hK_cont hg_int
    have hG_bdd : ∃ BG, ∀ s, ‖G s‖ ≤ BG := ⟨lam * ∫ r, ‖g r‖, conv_norm_le_left' hK_cont hK_bdd hg_int⟩
    have hG_int : Integrable G := conv_integrable hK_int hg_int
    have hG_supp : ∀ ξ, lam < |ξ| → 𝓕 G ξ = 0 := by
      intro ξ hξ
      dsimp [G]
      rw [fourier_conv hK_int hg_int ξ, fourier_K hlam_pos ξ]
      have h1 : 1 ≤ |ξ / lam| := by
        rw [abs_div, abs_of_pos hlam_pos, one_le_div hlam_pos]
        exact hξ.le
      rw [tent_eq_zero_of_one_le h1, Complex.ofReal_zero, zero_mul]
    obtain ⟨Q, hQ_cont, ⟨BQ, hBQ⟩, hQ_int, hMQ⟩ :=
      global_wiener_division ha ha₀ hsum hz hlam_pos hG_cont hG_bdd hG_int hG_supp
    have hBQ' : ∀ x, ‖Q x‖ ≤ max BQ 0 := fun x => (hBQ x).trans (le_max_left _ _)
    have hGF_lim : Tendsto (fun t : ℝ => ∫ s : ℝ, G s * (F (t - s) : ℂ)) atTop (𝓝 0) := by
      simpa [hMQ] using convolution_M_tendsto_zero ha ha₀ hsum hB hF_meas hF_bdd hH_lim
        (le_max_right BQ 0) hQ_cont hBQ' hQ_int
    obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp hGF_lim (ε / 2) (by positivity)
    refine ⟨T, fun t ht => ?_⟩
    rw [dist_zero_right]
    have hF_shift_meas : Measurable (fun s : ℝ => (F (t - s) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hF_meas.comp (measurable_const.sub measurable_id))
    have hi_g : Integrable (fun s => g s * (F (t - s) : ℂ)) :=
      (hg_int.norm.const_mul B).mono' (hg_int.aestronglyMeasurable.mul hF_shift_meas.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun s => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
          exact mul_le_mul_of_nonneg_right (hF_bdd _) (norm_nonneg _))
    have hi_G : Integrable (fun s => G s * (F (t - s) : ℂ)) :=
      (hG_int.norm.const_mul B).mono' (hG_int.aestronglyMeasurable.mul hF_shift_meas.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun s => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
          exact mul_le_mul_of_nonneg_right (hF_bdd _) (norm_nonneg _))
    have hdiff_bound : ‖(∫ s : ℝ, g s * (F (t - s) : ℂ)) - (∫ s : ℝ, G s * (F (t - s) : ℂ))‖ < ε / 2 := by
      rw [← integral_sub hi_g hi_G]
      have hle : ‖∫ s : ℝ, (g s * (F (t - s) : ℂ) - G s * (F (t - s) : ℂ))‖ ≤
          B * ∫ s : ℝ, ‖G s - g s‖ := by
        calc ‖∫ s : ℝ, (g s * (F (t - s) : ℂ) - G s * (F (t - s) : ℂ))‖
            ≤ ∫ s : ℝ, ‖g s * (F (t - s) : ℂ) - G s * (F (t - s) : ℂ)‖ := norm_integral_le_integral_norm _
          _ ≤ ∫ s : ℝ, B * ‖G s - g s‖ := by
              refine integral_mono (hi_g.sub hi_G).norm ((hG_int.sub hg_int).norm.const_mul B) fun s => ?_
              rw [← sub_mul, norm_mul, norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, mul_comm]
              exact mul_le_mul_of_nonneg_right (hF_bdd _) (norm_nonneg _)
          _ = B * ∫ s : ℝ, ‖G s - g s‖ := integral_const_mul _ _
      have hmul : B * ∫ s : ℝ, ‖G s - g s‖ ≤ (B + 1) * ∫ s : ℝ, ‖G s - g s‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (integral_nonneg fun _ => norm_nonneg _)
      have hlt : (B + 1) * ∫ s : ℝ, ‖G s - g s‖ < ε / 2 := by
        have := mul_lt_mul_of_pos_left hL1_small (by positivity : 0 < B + 1)
        have hsimp : (B + 1) * (ε / (2 * (B + 1))) = ε / 2 := by field_simp [show (B + 1 : ℝ) ≠ 0 by linarith]
        linarith
      exact (hle.trans hmul).trans_lt hlt
    have hG_small : ‖∫ s : ℝ, G s * (F (t - s) : ℂ)‖ < ε / 2 := by
      simpa [dist_zero_right] using hT t ht
    calc ‖∫ s : ℝ, g s * (F (t - s) : ℂ)‖
        = ‖((∫ s : ℝ, g s * (F (t - s) : ℂ)) - (∫ s : ℝ, G s * (F (t - s) : ℂ))) +
            (∫ s : ℝ, G s * (F (t - s) : ℂ))‖ := by ring_nf
      _ ≤ ‖(∫ s : ℝ, g s * (F (t - s) : ℂ)) - (∫ s : ℝ, G s * (F (t - s) : ℂ))‖ +
            ‖∫ s : ℝ, G s * (F (t - s) : ℂ)‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hdiff_bound hG_small
      _ = ε := add_halves ε
  -- Relate the real target integral to ∫ s, g s * (F (log x - s) : ℂ)
  have hreal_lim : Tendsto (fun x : ℝ => (∫ y in u..v, f (x * y) / x) - (v ^ 2 - u ^ 2) / 2) atTop (𝓝 0) := by
    have hC_lim : Tendsto (fun x : ℝ => ∫ s : ℝ, g s * (F (Real.log x - s) : ℂ)) atTop (𝓝 (0 : ℂ)) :=
      hgF_lim.comp Real.tendsto_log_atTop
    have hre_lim : Tendsto (fun x : ℝ => (∫ s : ℝ, g s * (F (Real.log x - s) : ℂ)).re) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Complex.continuous_re.tendsto (0 : ℂ)).comp hC_lim
    refine hre_lim.congr' ?_
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with x hx
    have hmon : Monotone (fun y : ℝ => f (x * y) / x) := fun y₁ y₂ hy =>
      div_le_div_of_nonneg_right (hm (mul_le_mul_of_nonneg_left hy hx.le)) hx.le
    have hy_int : (∫ y in u..v, y) = (v ^ 2 - u ^ 2) / 2 := by
      have hderiv : ∀ y ∈ Set.uIcc u v, HasDerivAt (fun t : ℝ => t ^ 2 / 2) y y := fun y _ => by
        have hd : HasDerivAt (fun t : ℝ => t ^ 2 / 2) ((2 : ℝ) * y ^ 1 / 2) y := by
          simpa using (hasDerivAt_pow 2 y).div_const (2 : ℝ)
        convert hd using 1
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (continuous_id.intervalIntegrable u v)]
      ring
    have hsub_int : (∫ y in u..v, f (x * y) / x) - (v ^ 2 - u ^ 2) / 2 =
        ∫ y in u..v, (f (x * y) / x - y) := by
      rw [← hy_int]
      exact (intervalIntegral.integral_sub (hmon.intervalIntegrable (μ := volume))
        (continuous_id.intervalIntegrable u v)).symm
    have himg : (fun r : ℝ => Real.exp (-r)) '' Ioc A B_int = Ico u v := by
      ext y
      constructor
      · rintro ⟨r, ⟨hr1, hr2⟩, rfl⟩
        dsimp [A, B_int] at hr1 hr2
        refine ⟨?_, ?_⟩
        · rw [← Real.exp_log hu]
          exact Real.exp_le_exp.mpr (by linarith)
        · rw [← Real.exp_log (hu.trans huv)]
          exact Real.exp_lt_exp.mpr (by linarith)
      · rintro ⟨hy1, hy2⟩
        have hy_pos : 0 < y := lt_of_lt_of_le hu hy1
        refine ⟨-Real.log y, ⟨?_, ?_⟩, ?_⟩
        · dsimp [A]
          linarith [Real.log_lt_log hy_pos hy2]
        · dsimp [B_int]
          linarith [Real.log_le_log hu hy1]
        · dsimp only
          rw [neg_neg, Real.exp_log hy_pos]
    have hchg : (∫ y in u..v, (f (x * y) / x - y)) =
        ∫ r in Ioc A B_int, Real.exp (-2 * r) * F (Real.log x - r) := by
      rw [intervalIntegral.integral_of_le huv.le, ← integral_Ico_eq_integral_Ioc, ← himg]
      have hjac := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioc (a := A) (b := B_int))
        (f := fun r : ℝ => Real.exp (-r)) (f' := fun r : ℝ => -Real.exp (-r))
        (fun r _ => by
          have hd : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-r)) r := by
            simpa [Function.comp_def] using (Real.hasDerivAt_exp (-r)).comp r (hasDerivAt_neg r)
          exact hd.hasDerivWithinAt)
        (fun r₁ _ r₂ _ h => neg_injective (Real.exp_injective h))
        (fun y : ℝ => f (x * y) / x - y)
      rw [hjac]
      refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
      rw [smul_eq_mul, abs_neg, abs_of_pos (Real.exp_pos (-r))]
      dsimp [F]
      have harg1 : Real.exp (Real.log x - r) = x * Real.exp (-r) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hx]
      have harg2 : Real.exp (-(Real.log x - r)) = x⁻¹ * Real.exp r := by
        rw [neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log hx, mul_comm]
      rw [harg1, harg2]
      have h2r : Real.exp (-2 * r) = Real.exp (-r) * Real.exp (-r) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hcancel : Real.exp (-r) * Real.exp r = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      rw [h2r, div_eq_mul_inv]
      have hmul_eq : Real.exp (-r) * Real.exp (-r) * (f (x * Real.exp (-r)) * (x⁻¹ * Real.exp r)) =
          Real.exp (-r) * (f (x * Real.exp (-r)) * x⁻¹) * (Real.exp (-r) * Real.exp r) := by ring
      rw [mul_sub, mul_sub, mul_one, hmul_eq, hcancel, mul_one]
    have hre_eq : (∫ s : ℝ, g s * (F (Real.log x - s) : ℂ)).re =
        ∫ r in Ioc A B_int, Real.exp (-2 * r) * F (Real.log x - r) := by
      have hofReal : (fun s : ℝ => g s * (F (Real.log x - s) : ℂ)) =
          fun s : ℝ => (((Ioc A B_int).indicator (fun r => Real.exp (-2 * r) * F (Real.log x - r)) s : ℝ) : ℂ) := by
        ext s
        dsimp [g]
        by_cases hs : s ∈ Ioc A B_int
        · simp [hs]
        · simp [hs]
      rw [hofReal, integral_complex_ofReal', Complex.ofReal_re, integral_indicator measurableSet_Ioc]
    rw [hre_eq, ← hchg, ← hsub_int]
  have hadd := hreal_lim.add (tendsto_const_nhds (x := (v ^ 2 - u ^ 2) / 2))
  simp only [zero_add] at hadd
  exact hadd.congr fun x => sub_add_cancel _ _

end OMA_Erdos967_H1

theorem OMA.solution : OMA.R_Erdos967_erdos_967_variants_tauberian_R1.H1 :=
  OMA_Erdos967_H1.solution_aux
