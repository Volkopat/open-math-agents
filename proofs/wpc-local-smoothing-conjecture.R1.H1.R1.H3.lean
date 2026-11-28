import OMAReductions.R_wpc_local_smoothing_conjecture_R1_H1_R1

/-!
# Dyadic cutoff estimate for the half-wave integral

The finite sums of the low-frequency multiplier and dyadic differences give
expanding cutoffs. Dominated convergence and the lower semicontinuity of the
extended-valued Lp norm give the claimed bound.
-/

open MeasureTheory Filter Finset OMA.S_wpc_local_smoothing_conjecture
open scoped ENNReal FourierTransform RealInnerProductSpace Topology

noncomputable section

namespace OMA.LocalSmoothingDyadic

private theorem angularFourier_regular {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    Continuous (angularFourier f) ∧ Integrable (angularFourier f) := by
  let q : ℝ := (2 * Real.pi)⁻¹
  let G : SchwartzMap (Space n) ℂ := 𝓕 f
  have hq : 2 * Real.pi ≠ 0 := by positivity
  have hG : (G : Space n → ℂ) = 𝓕 (f : Space n → ℂ) := SchwartzMap.fourier_coe f
  have h : angularFourier f = fun ξ => G (q • ξ) := by
    funext ξ
    rw [hG, Real.fourier_eq']
    unfold angularFourier
    congr 1
    funext x
    rw [smul_eq_mul, real_inner_smul_right]
    have harg : -2 * Real.pi * (q * inner ℝ x ξ) = -inner ℝ x ξ := by
      calc
        _ = (-(2 * Real.pi) * q) * inner ℝ x ξ := by ring
        _ = _ := by
          change (-(2 * Real.pi) * (2 * Real.pi)⁻¹) * inner ℝ x ξ = _
          rw [neg_mul, mul_inv_cancel₀ hq, neg_one_mul]
    rw [harg, Complex.ofReal_neg]
    rw [show -Complex.I * (↑(inner ℝ x ξ)) = -(↑(inner ℝ x ξ)) * Complex.I by ring]
  rw [h]
  have hsmul : Continuous (fun ξ : Space n => q • ξ) := continuous_id.const_smul q
  exact ⟨G.continuous.comp hsmul, G.integrable.comp_smul (inv_ne_zero hq)⟩

private def kernel {n : ℕ} (f : SchwartzMap (Space n) ℂ) (φ : Space n → ℂ)
    (z : Space n × ℝ) (ξ : Space n) : ℂ :=
  Complex.exp (Complex.I * ((inner ℝ z.1 ξ : ℝ) : ℂ)) *
    (Complex.exp (-Complex.I * (-z.2 * ‖ξ‖ : ℝ)) * φ ξ * angularFourier f ξ)

private def wave {n : ℕ} (f : SchwartzMap (Space n) ℂ) (φ : Space n → ℂ)
    (z : Space n × ℝ) : ℂ :=
  (((2 * Real.pi) ^ n)⁻¹ : ℝ) • ∫ ξ, kernel f φ z ξ

private theorem continuous_kernel {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    {φ : Space n → ℂ} (hφ : Continuous φ) :
    Continuous (fun p : (Space n × ℝ) × Space n => kernel f φ p.1 p.2) := by
  have hF := (angularFourier_regular f).1
  unfold kernel
  fun_prop

private theorem wave_measurable {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    {φ : Space n → ℂ} (hφ : Continuous φ) : StronglyMeasurable (wave f φ) := by
  unfold wave
  exact ((continuous_kernel f hφ).stronglyMeasurable.integral_prod_right'
    (ν := volume)).const_smul (((2 * Real.pi) ^ n)⁻¹ : ℝ)

private theorem norm_kernel {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    (φ : Space n → ℂ) (z : Space n × ℝ) (ξ : Space n) :
    ‖kernel f φ z ξ‖ = ‖φ ξ‖ * ‖angularFourier f ξ‖ := by
  unfold kernel
  rw [show -Complex.I * ((-z.2 * ‖ξ‖ : ℝ) : ℂ) =
      Complex.I * ((-(-z.2 * ‖ξ‖) : ℝ) : ℂ) by simp only [Complex.ofReal_neg, mul_neg, neg_mul]]
  simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

private theorem integrable_kernel {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    {φ : Space n → ℂ} (hφ : Continuous φ) (hb : ∀ ξ, ‖φ ξ‖ ≤ 1)
    (z : Space n × ℝ) : Integrable (kernel f φ z) := by
  have hc : Continuous (kernel f φ z) := by
    have hF := (angularFourier_regular f).1
    unfold kernel
    fun_prop
  refine (angularFourier_regular f).2.mono hc.aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
  rw [norm_kernel]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb ξ)

private theorem wave_sub {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    {φ ψ : Space n → ℂ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφ₁ : ∀ ξ, ‖φ ξ‖ ≤ 1) (hψ₁ : ∀ ξ, ‖ψ ξ‖ ≤ 1) :
    wave f (fun ξ => φ ξ - ψ ξ) = wave f φ - wave f ψ := by
  funext z
  have h : kernel f (fun ξ => φ ξ - ψ ξ) z =
      fun ξ => kernel f φ z ξ - kernel f ψ z ξ := by
    funext ξ
    simp only [kernel, mul_sub, sub_mul]
  simp only [Pi.sub_apply, wave, h,
    integral_sub (integrable_kernel f hφ hφ₁ z) (integrable_kernel f hψ hψ₁ z),
    smul_sub]

private theorem wave_tendsto {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    (cutoff : ℕ → Space n → ℂ) (hc : ∀ m, Continuous (cutoff m))
    (hb : ∀ m ξ, ‖cutoff m ξ‖ ≤ 1)
    (hg : ∀ ξ, Tendsto (fun m => cutoff m ξ) atTop (𝓝 1))
    (z : Space n × ℝ) :
    Tendsto (fun m => wave f (cutoff m) z) atTop (𝓝 (wave f (fun _ => 1) z)) := by
  have hi (m : ℕ) : AEStronglyMeasurable (kernel f (cutoff m) z) volume :=
    (integrable_kernel f (hc m) (hb m) z).aestronglyMeasurable
  have hnormF := (angularFourier_regular f).2.norm
  have hdom (m : ℕ) : ∀ᵐ ξ ∂(volume : Measure (Space n)),
      ‖kernel f (cutoff m) z ξ‖ ≤ ‖angularFourier f ξ‖ := by
    filter_upwards [] with ξ
    rw [norm_kernel]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb m ξ)
  have hpoint : ∀ᵐ ξ ∂(volume : Measure (Space n)),
      Tendsto (fun m => kernel f (cutoff m) z ξ) atTop (𝓝 (kernel f (fun _ => 1) z ξ)) := by
    refine ae_of_all _ fun ξ => ?_
    unfold kernel
    exact (((hg ξ).const_mul _).mul_const _).const_mul _
  have hi' := tendsto_integral_of_dominated_convergence _ hi hnormF hdom hpoint
  exact hi'.const_smul (((2 * Real.pi) ^ n)⁻¹ : ℝ)

private theorem eLpNorm_le_of_telescoping {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P : ℝ≥0∞) (hP : 1 ≤ P)
    (F A : ℕ → Ω → ℂ) (g : Ω → ℂ)
    (hF : ∀ m, AEStronglyMeasurable (F m) μ)
    (hA : ∀ m, AEStronglyMeasurable (A m) μ)
    (htel : ∀ m, F m = F 0 + ∑ j ∈ range m, A j)
    (hlim : ∀ z, Tendsto (fun m => F m z) atTop (𝓝 (g z))) :
    eLpNorm g P μ ≤ eLpNorm (F 0) P μ + ∑' j, eLpNorm (A j) P μ := by
  have hbound (m : ℕ) :
      eLpNorm (F m) P μ ≤ eLpNorm (F 0) P μ + ∑' j, eLpNorm (A j) P μ := by
    rw [htel m]
    have hm := Finset.aestronglyMeasurable_sum (range m) (fun j _ => hA j)
    have hsum : eLpNorm (∑ j ∈ range m, A j) P μ ≤ ∑' j, eLpNorm (A j) P μ :=
      (eLpNorm_sum_le (fun j _ => hA j) hP).trans (ENNReal.sum_le_tsum _)
    exact (eLpNorm_add_le (hF 0) hm hP).trans (add_le_add le_rfl hsum)
  exact Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbound) hF (ae_of_all μ hlim)

private theorem dyadic {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    (b : ContDiffBump (0 : Space n)) (P : ℝ≥0∞) (hP : 1 ≤ P) :
    let l : Space n → ℂ := fun ξ => (b ξ : ℝ)
    let a : Space n → ℂ := fun ξ => l ((1 / 2 : ℝ) • ξ) - l ξ
    eLpNorm (fun z : Space n × ℝ => halfWaveIntegral (-z.2) f z.1) P
        (observationMeasure n) ≤
      eLpNorm (wave f (fun ξ => l ((1 : ℝ) • ξ))) P (observationMeasure n) +
        ∑' j : ℕ, eLpNorm (wave f (fun ξ => a (((2 : ℝ)⁻¹ ^ j) • ξ))) P
          (observationMeasure n) := by
  let μ := observationMeasure n
  let l : Space n → ℂ := fun ξ => (b ξ : ℝ)
  let a : Space n → ℂ := fun ξ => l ((1 / 2 : ℝ) • ξ) - l ξ
  let scale (m : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ m
  let cutoff (m : ℕ) (ξ : Space n) : ℂ := l (scale m • ξ)
  let shell (m : ℕ) (ξ : Space n) : ℂ := a (scale m • ξ)
  let F (m : ℕ) := wave f (cutoff m)
  let A (m : ℕ) := wave f (shell m)
  change eLpNorm (fun z : Space n × ℝ => halfWaveIntegral (-z.2) f z.1) P μ ≤
    eLpNorm (wave f (fun ξ => l ((1 : ℝ) • ξ))) P μ +
      ∑' j : ℕ, eLpNorm (A j) P μ
  have hfull : (fun z : Space n × ℝ => halfWaveIntegral (-z.2) f z.1) =
      wave f (fun _ => 1) := by
    funext z
    simp only [halfWaveIntegral, angularInverse, wave, kernel, mul_one]
  rw [hfull]
  have hscale : Tendsto scale atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hl : Continuous l := Complex.continuous_ofReal.comp b.continuous
  have hcut (m : ℕ) : Continuous (cutoff m) := by
    have hsmul : Continuous (fun ξ : Space n => scale m • ξ) := continuous_id.const_smul (scale m)
    exact hl.comp hsmul
  have hnorm (m : ℕ) (ξ : Space n) : ‖cutoff m ξ‖ ≤ 1 := by
    change ‖(b (scale m • ξ) : ℂ)‖ ≤ 1
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg] using
      (b.le_one (x := scale m • ξ))
  have hs (m : ℕ) : shell m = fun ξ => cutoff (m + 1) ξ - cutoff m ξ := by
    funext ξ
    simp only [shell, a, cutoff, scale, pow_succ', smul_smul, one_div]
  have hF (m : ℕ) : AEStronglyMeasurable (F m) μ :=
    (wave_measurable f (hcut m)).aestronglyMeasurable
  have hA (m : ℕ) : AEStronglyMeasurable (A m) μ := by
    change AEStronglyMeasurable (wave f (shell m)) μ
    rw [hs]
    exact (wave_measurable f ((hcut (m + 1)).sub (hcut m))).aestronglyMeasurable
  have hstep (m : ℕ) : F (m + 1) = F m + A m := by
    have h := wave_sub f (hcut (m + 1)) (hcut m) (hnorm (m + 1)) (hnorm m)
    change wave f (cutoff (m + 1)) =
      wave f (cutoff m) + wave f (shell m)
    rw [hs, h]
    abel
  have htel (m : ℕ) : F m = F 0 + ∑ j ∈ range m, A j := by
    induction m with
    | zero => simp
    | succ m ih => rw [hstep, ih, sum_range_succ, add_assoc]
  have hzero : F 0 = wave f (fun ξ => l ((1 : ℝ) • ξ)) := by
    simp only [F, cutoff, scale, pow_zero]
  rw [← hzero]
  have hg (ξ : Space n) : Tendsto (fun m => cutoff m ξ) atTop (𝓝 1) := by
    have hsmul : Tendsto (fun m => scale m • ξ) atTop (𝓝 (0 : Space n)) := by
      simpa only [zero_smul] using hscale.smul_const ξ
    have hcenter : l 0 = 1 := by
      change (b 0 : ℂ) = 1
      rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
      norm_num
    simpa only [cutoff, hcenter, Function.comp_def] using (hl.continuousAt.tendsto.comp hsmul)
  exact eLpNorm_le_of_telescoping μ P hP F A (wave f fun _ => 1) hF hA htel
    (wave_tendsto f cutoff hcut hnorm hg)

end OMA.LocalSmoothingDyadic

theorem OMA.solution : OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1.H3 := by
  intro n P hP
  dsimp only
  intro f
  exact OMA.LocalSmoothingDyadic.dyadic f ⟨8, 16, by norm_num, by norm_num⟩ P hP
