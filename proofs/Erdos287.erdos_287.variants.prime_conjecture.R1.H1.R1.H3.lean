import OMAReductions.R_Erdos287_erdos_287_variants_prime_conjecture_R1_H1_R1
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The normalized major-arc singular integral converges to one half. -/

open Filter MeasureTheory Set
open scoped FourierTransform Convolution Topology

noncomputable section

private def phase (x : ℝ) : ℂ :=
  Complex.exp (↑(2 * Real.pi * x) * Complex.I)

private lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private def intervalIndicator (a b : ℝ) : ℝ → ℂ :=
  (Icc a b).indicator (fun _ => 1)

private lemma intervalIndicator_integrable (a b : ℝ) :
    Integrable (intervalIndicator a b) := by
  rw [intervalIndicator, integrable_indicator_iff measurableSet_Icc]
  exact continuous_const.integrableOn_Icc

private lemma fourier_interval (a b t : ℝ) :
    𝓕 (intervalIndicator a b) t = ∫ x in Icc a b, phase (-(x * t)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Icc a b
  · simp only [intervalIndicator, indicator_of_mem hx, smul_eq_mul, mul_one, phase]
    congr 1
    push_cast
    ring
  · simp [intervalIndicator, indicator_of_notMem hx]

private lemma as_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Icc a b, f x) = ∫ x in a..b, f x := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

private lemma norm_fourier_interval_le {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    ‖𝓕 (intervalIndicator a b) t‖ ≤ b - a := by
  rw [fourier_interval, as_intervalIntegral _ hab]
  simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun x => phase (-(x * t))) (C := 1)
      (fun x _ => (norm_phase _).le))

private lemma norm_fourier_interval_decay {a b t : ℝ} (hab : a ≤ b) (ht : t ≠ 0) :
    ‖𝓕 (intervalIndicator a b) t‖ ≤ |t|⁻¹ := by
  let c : ℂ := ↑(-(2 * Real.pi * t)) * Complex.I
  have hcoef (x : ℝ) : phase (-(x * t)) = Complex.exp (c * ↑x) := by
    unfold phase c
    push_cast
    congr 1
    ring
  have hc : c ≠ 0 := by
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) ht))) Complex.I_ne_zero
  have hcn : ‖c‖ = (2 * Real.pi) * |t| := by
    simp [c, abs_of_nonneg Real.pi_pos.le]
  rw [fourier_interval, as_intervalIntegral _ hab]
  simp_rw [hcoef]
  rw [integral_exp_mul_complex hc, norm_div, hcn]
  have hnum : ‖Complex.exp (c * ↑b) - Complex.exp (c * ↑a)‖ ≤ 2 := by
    rw [← hcoef, ← hcoef]
    simpa only [norm_phase, one_add_one_eq_two] using norm_sub_le (phase (-(b * t))) (phase (-(a * t)))
  have ht' := abs_pos.mpr ht
  refine (div_le_div_of_nonneg_right hnum (by positivity)).trans ?_
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi * |t|)).2
  have hpi : (2 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc
    (2 : ℝ) ≤ 2 * Real.pi := hpi
    _ = |t|⁻¹ * (2 * Real.pi * |t|) := by field_simp <;> ring

private def kernel (t : ℝ) : ℂ :=
  𝓕 (intervalIndicator 1 2) t * 𝓕 (intervalIndicator (-2) 0) t

private lemma continuous_kernel : Continuous kernel := by
  have h (a b : ℝ) : Continuous (𝓕 (intervalIndicator a b)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (ContinuousLinearMap.continuous₂ (innerSL ℝ)) (intervalIndicator_integrable a b)
  exact (h 1 2).mul (h (-2) 0)

private lemma norm_kernel (t : ℝ) : ‖kernel t‖ ≤ 4 * (1 + t ^ 2)⁻¹ := by
  have hden : 0 < 1 + t ^ 2 := by positivity
  by_cases ht : t ^ 2 ≤ 1
  · have h₁ : ‖𝓕 (intervalIndicator 1 2) t‖ ≤ 1 := by
      convert norm_fourier_interval_le (a := 1) (b := 2) (by norm_num) t using 1 <;> norm_num
    have h₂ : ‖𝓕 (intervalIndicator (-2) 0) t‖ ≤ 2 := by
      simpa using norm_fourier_interval_le (a := -2) (b := 0) (by norm_num) t
    rw [kernel, norm_mul, ← div_eq_mul_inv]
    refine (mul_le_mul h₁ h₂ (norm_nonneg _) (by norm_num)).trans ?_
    apply (le_div_iff₀ hden).2
    linarith
  · have ht' : t ≠ 0 := by intro h; simp [h] at ht
    have hsq : 0 < t ^ 2 := sq_pos_of_ne_zero ht'
    rw [kernel, norm_mul, ← div_eq_mul_inv]
    refine (mul_le_mul (norm_fourier_interval_decay (by norm_num) ht')
      (norm_fourier_interval_decay (by norm_num) ht') (norm_nonneg _) (by positivity)).trans ?_
    rw [← pow_two, inv_pow, sq_abs, ← one_div]
    apply (div_le_div_iff₀ hsq hden).2
    linarith

private lemma integrable_majorant :
    Integrable (fun t : ℝ => 4 * (1 + t ^ 2)⁻¹) :=
  integrable_inv_one_add_sq.const_mul _

private lemma integrable_kernel : Integrable kernel :=
  integrable_majorant.mono' continuous_kernel.aestronglyMeasurable (ae_of_all _ norm_kernel)

private lemma integral_kernel : ∫ t, kernel t = 1 := by
  let L := ContinuousLinearMap.mul ℂ ℂ
  let f := intervalIndicator 1 2
  let g := intervalIndicator (-2) 0
  have hf : Integrable f := intervalIndicator_integrable _ _
  have hg : Integrable g := intervalIndicator_integrable _ _
  have hfg : 𝓕 (f ⋆[L] g) = kernel := funext (Real.fourier_mul_convolution_eq hf hg)
  have hconv (s : ℝ) :
      (f ⋆[L] g) s = ↑(max (min 2 (s + 2) - max 1 s) 0) := by
    rw [MeasureTheory.convolution_def]
    have hi (x : ℝ) :
        L (f x) (g (s - x)) =
          (Icc (max 1 s) (min 2 (s + 2))).indicator (fun _ : ℝ => (1 : ℂ)) x := by
      by_cases h₁ : x ∈ Icc (1 : ℝ) 2 <;> by_cases h₂ : s - x ∈ Icc (-2 : ℝ) 0
      · have hx : x ∈ Icc (max 1 s) (min 2 (s + 2)) :=
          ⟨max_le h₁.1 (by linarith [h₂.2]), le_min h₁.2 (by linarith [h₂.1])⟩
        simp [L, f, g, intervalIndicator, h₁, h₂, hx]
      · have hx : x ∉ Icc (max 1 s) (min 2 (s + 2)) := fun h =>
          h₂ ⟨by linarith [le_min_iff.mp h.2 |>.2], by linarith [max_le_iff.mp h.1 |>.2]⟩
        simp [L, f, g, intervalIndicator, h₁, h₂, hx]
      · have hx : x ∉ Icc (max 1 s) (min 2 (s + 2)) := fun h =>
          h₁ ⟨(max_le_iff.mp h.1).1, (le_min_iff.mp h.2).1⟩
        simp [L, f, g, intervalIndicator, h₁, h₂, hx]
      · have hx : x ∉ Icc (max 1 s) (min 2 (s + 2)) := fun h =>
          h₁ ⟨(max_le_iff.mp h.1).1, (le_min_iff.mp h.2).1⟩
        simp [L, f, g, intervalIndicator, h₁, h₂, hx]
    simp_rw [hi]
    rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc]
    simp [Complex.real_smul]
  have hc : Continuous (f ⋆[L] g) := by
    have heq : (f ⋆[L] g) = fun s : ℝ => ↑(max (min 2 (s + 2) - max 1 s) 0) :=
      funext hconv
    rw [heq]
    fun_prop
  have hi := (hf.integrable_convolution L hg).fourierInv_fourier_eq
    (hfg.symm ▸ integrable_kernel) (v := 0) hc.continuousAt
  rw [hfg, Real.fourierInv_eq] at hi
  simpa [hconv, show (2 : ℝ) - 1 = 1 by norm_num] using hi

private lemma integral_complex_re {μ : Measure ℝ} {f : ℝ → ℂ} (hf : Integrable f μ) :
    (∫ x, (f x).re ∂μ) = (∫ x, f x ∂μ).re :=
  integral_re (𝕜 := ℂ) hf

private def model (a t : ℝ) : ℝ :=
  ∫ u in Icc (1 : ℝ) 2, ∫ v in Icc (0 : ℝ) 1,
    Real.cos (2 * Real.pi * ((u + a - 2 * v) * t))

private lemma model_eq (a t : ℝ) : model a t = (phase (-(a * t)) * kernel t).re / 2 := by
  let f := fun u : ℝ => phase (-(u * t))
  let g := fun z : ℝ => phase (-(z * t))
  have hsub : (∫ v in Icc (0 : ℝ) 1, g (-2 * v)) = (2 : ℂ)⁻¹ *
      ∫ z in Icc (-2 : ℝ) 0, g z := by
    rw [as_intervalIntegral _ (by norm_num : (0 : ℝ) ≤ 1),
      as_intervalIntegral _ (by norm_num : (-2 : ℝ) ≤ 0)]
    have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1) g
      (c := -2) (by norm_num)
    rw [show (-2 : ℝ) * 0 = 0 by ring, show (-2 : ℝ) * 1 = -2 by ring,
      intervalIntegral.integral_symm (-2) 0, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_neg, Complex.ofReal_ofNat, inv_neg, neg_mul, mul_neg, neg_neg] at h
    exact h
  have hfg : Continuous f := by unfold f phase; fun_prop
  have hgg : Continuous g := by unfold g phase; fun_prop
  have hre (w : ℝ) : (phase (-w)).re = Real.cos (2 * Real.pi * w) := by
    rw [phase, Complex.exp_ofReal_mul_I_re, mul_neg, Real.cos_neg]
  have hsplit (u v : ℝ) : phase (-((u + a - 2 * v) * t)) =
      phase (-(a * t)) * f u * g (-2 * v) := by
    rw [← phase_add, ← phase_add]
    congr 1
    ring
  have hinner (u : ℝ) :
      (∫ v in Icc (0 : ℝ) 1, Real.cos (2 * Real.pi * ((u + a - 2 * v) * t))) =
        (phase (-(a * t)) * f u * ((2 : ℂ)⁻¹ * ∫ z in Icc (-2 : ℝ) 0, g z)).re := by
    simp_rw [← hre, hsplit]
    rw [integral_complex_re, integral_const_mul, hsub]
    exact (continuous_const.mul (hgg.comp (by fun_prop))).continuousOn.integrableOn_Icc
  unfold model
  simp_rw [hinner]
  rw [integral_complex_re, integral_mul_const, integral_const_mul, kernel, fourier_interval, fourier_interval]
  · change (_ * (∫ u in Icc (1 : ℝ) 2, f u) *
        ((2 : ℂ)⁻¹ * ∫ z in Icc (-2 : ℝ) 0, g z)).re =
        (_ * ((∫ u in Icc (1 : ℝ) 2, f u) * ∫ z in Icc (-2 : ℝ) 0, g z)).re / 2
    rw [show ∀ w A B : ℂ, w * A * (2⁻¹ * B) = (2 : ℂ)⁻¹ * (w * (A * B)) by
      intros; ring]
    rw [show (2 : ℂ)⁻¹ = (((1 / 2 : ℝ)) : ℂ) by norm_num]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  · exact ((continuous_const.mul hfg).mul continuous_const).continuousOn.integrableOn_Icc

private lemma scale_setIntegral (f : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Icc (c * a) (c * b), f x) = c * ∫ x in Icc a b, f (c * x) := by
  rw [as_intervalIntegral _ (mul_le_mul_of_nonneg_left hab hc.le), as_intervalIntegral _ hab]
  exact (intervalIntegral.mul_integral_comp_mul_left c).symm

private def cutoff (N : ℕ) : ℝ :=
  Real.log (N : ℝ) ^ 2

private def singularIntegral (N : ℕ) : ℝ :=
  let δ := cutoff N / (N : ℝ)
  ∫ β in Icc (-δ) δ,
    ∫ x in Icc (N : ℝ) (2 * (N : ℝ)),
      ∫ y in Icc (0 : ℝ) (N : ℝ), Real.cos (2 * Real.pi * ((x + 1 - 2 * y) * β))

private lemma scale_singularIntegral (N : ℕ) (hN : 0 < N) :
    singularIntegral N = (N : ℝ) * ∫ t in Icc (-cutoff N) (cutoff N), model (N : ℝ)⁻¹ t := by
  let r : ℝ := N
  have hr : 0 < r := by
    change 0 < (N : ℝ)
    exact_mod_cast hN
  let F := fun x y β : ℝ => Real.cos (2 * Real.pi * ((x + 1 - 2 * y) * β))
  have hy (x β : ℝ) :
      (∫ y in Icc (0 : ℝ) r, F x y β) = r * ∫ v in Icc (0 : ℝ) 1, F x (r * v) β := by
    simpa only [mul_zero, mul_one] using
      (scale_setIntegral (fun y => F x y β) hr (a := 0) (b := 1) (by norm_num))
  have hx (t : ℝ) :
      (∫ x in Icc r (2 * r), ∫ y in Icc (0 : ℝ) r, F x y (r⁻¹ * t)) =
        r ^ 2 * model r⁻¹ t := by
    have h := scale_setIntegral (fun x => ∫ y in Icc (0 : ℝ) r, F x y (r⁻¹ * t))
      hr (a := 1) (b := 2) (by norm_num)
    rw [mul_one, mul_comm r 2] at h
    have harg (u v : ℝ) :
        F (r * u) (r * v) (r⁻¹ * t) = Real.cos (2 * Real.pi * ((u + r⁻¹ - 2 * v) * t)) := by
      unfold F
      congr 1
      field_simp [hr.ne']
    rw [h]
    simp_rw [hy, harg, integral_const_mul]
    rw [model]
    ring
  have hcut : 0 ≤ cutoff N := sq_nonneg _
  have houter := scale_setIntegral (fun β =>
    ∫ x in Icc r (2 * r), ∫ y in Icc (0 : ℝ) r, F x y β)
    (inv_pos.mpr hr) (a := -cutoff N) (b := cutoff N) (by linarith)
  rw [mul_neg, ← div_eq_inv_mul] at houter
  change (∫ β in Icc (-(cutoff N / r)) (cutoff N / r),
    ∫ x in Icc r (2 * r), ∫ y in Icc (0 : ℝ) r, F x y β) =
      r * ∫ t in Icc (-cutoff N) (cutoff N), model r⁻¹ t
  rw [houter]
  simp_rw [hx, integral_const_mul]
  field_simp [hr.ne']

private lemma tendsto_normalized :
    Tendsto (fun N : ℕ => ∫ t in Icc (-cutoff N) (cutoff N),
      model (N : ℝ)⁻¹ t) atTop (𝓝 (1 / 2 : ℝ)) := by
  let w := fun N : ℕ => Icc (-cutoff N) (cutoff N)
  let Φ := fun a t : ℝ => (phase (-(a * t)) * kernel t).re / 2
  have hmass : ∫ t, (kernel t).re / 2 = (1 / 2 : ℝ) := by
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const, integral_complex_re integrable_kernel, integral_kernel]
    simp
  have hΦ : ∀ a : ℝ, Continuous (Φ a) := by
    intro a
    have hp : Continuous (fun t : ℝ => phase (-(a * t))) := by unfold phase; fun_prop
    exact (Complex.continuous_re.comp (hp.mul continuous_kernel)).div_const 2
  have hcut : Tendsto cutoff atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simp_rw [model_eq, ← integral_indicator measurableSet_Icc]
  rw [← hmass]
  apply tendsto_integral_filter_of_dominated_convergence (F := fun N : ℕ =>
    (w N).indicator (Φ (N : ℝ)⁻¹)) (fun t : ℝ => 4 * (1 + t ^ 2)⁻¹)
  · exact Eventually.of_forall fun N => ((hΦ _).aestronglyMeasurable.indicator measurableSet_Icc)
  · exact Eventually.of_forall fun N => ae_of_all _ fun t => by
      by_cases ht : t ∈ w N
      · rw [indicator_of_mem ht]
        have hb : ‖(phase (-((N : ℝ)⁻¹ * t)) * kernel t).re‖ ≤ ‖kernel t‖ := by
          simpa [Real.norm_eq_abs, norm_mul, norm_phase] using
            Complex.abs_re_le_norm (phase (-((N : ℝ)⁻¹ * t)) * kernel t)
        change ‖(phase (-((N : ℝ)⁻¹ * t)) * kernel t).re / 2‖ ≤ _
        rw [norm_div, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact ((div_le_self (norm_nonneg _) (by norm_num)).trans hb).trans (norm_kernel t)
      · rw [indicator_of_notMem ht, norm_zero]
        positivity
  · exact integrable_majorant
  · exact ae_of_all _ fun t => by
      have hc : Continuous (fun a : ℝ => Φ a t) := by unfold Φ phase; fun_prop
      have hl : Tendsto (fun N : ℕ => Φ (N : ℝ)⁻¹ t) atTop (𝓝 ((kernel t).re / 2)) := by
        simpa [Φ, phase, Function.comp_def] using (hc.continuousAt (x := 0)).tendsto.comp hinv
      apply hl.congr'
      filter_upwards [hcut.eventually_ge_atTop |t|] with N hN
      have ht : t ∈ w N := ⟨by linarith [(neg_le_abs t).trans hN], (le_abs_self t).trans hN⟩
      rw [indicator_of_mem ht]

theorem OMA.solution : OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R1_H1_R1.H3 := by
  change ∀ᶠ N : ℕ in atTop, 31 * (N : ℝ) / 64 ≤ singularIntegral N
  have h := tendsto_normalized.eventually (eventually_gt_nhds
    (show (31 / 64 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with N hN hpos
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hpos
  rw [scale_singularIntegral N hpos]
  have hh := mul_le_mul_of_nonneg_left hN.le hN'.le
  linarith
