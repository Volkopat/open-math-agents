import OMAReductions.R_wpc_local_smoothing_conjecture_R1_H1_R1
/- Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). -/
open MeasureTheory OMA.S_wpc_local_smoothing_conjecture
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace LSLeaf
open FourierTransform Filter OMA.S_wpc_local_smoothing_conjecture
open scoped Topology ContDiff ENNReal
theorem angularFourier_scaled {n : ℕ} (f : Space n → ℂ) (ξ : Space n) :
    angularFourier f ((2 * Real.pi) • ξ) = 𝓕 f ξ := by
  rw [angularFourier, Real.fourier_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    simp only [inner_smul_right, Complex.ofReal_mul, Complex.ofReal_neg, smul_eq_mul]
    congr 2
    push_cast
    ring

/-- Exact Jacobian cancellation in the angular-frequency inverse transform. -/
theorem angularInverse_eq_fourierInv_scaled {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    angularInverse g x = 𝓕⁻ (fun ξ ↦ g ((2 * Real.pi) • ξ)) x := by
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hchange := Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n))
    (fun ξ ↦ Complex.exp (Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * g ξ)
    (2 * Real.pi) (hR := hπ)
  calc
    angularInverse g x =
      ∫ ξ, Complex.exp (Complex.I * ((inner ℝ x ((2 * Real.pi) • ξ) : ℝ) : ℂ)) *
        g ((2 * Real.pi) • ξ) := by
      simpa [angularInverse, Space] using hchange.symm
    _ = 𝓕⁻ (fun ξ ↦ g ((2 * Real.pi) • ξ)) x := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ ↦ by
        simp only [inner_smul_right, real_inner_comm x ξ, Complex.ofReal_mul, smul_eq_mul]
        congr 2
        push_cast
        ring

def angularSchwartzMultiplier {n : ℕ} (m : Space n → ℝ)
    (f : SchwartzMap (Space n) ℂ) : SchwartzMap (Space n) ℂ :=
  SchwartzMap.fourierMultiplierCLM ℂ (fun ξ => m ((2*Real.pi) • ξ)) f

theorem angularSchwartzMultiplier_temperate {n : ℕ} {m : Space n → ℝ}
    (hm : m.HasTemperateGrowth) :
    (fun ξ => m ((2*Real.pi) • ξ)).HasTemperateGrowth :=
  hm.comp (by fun_prop)

theorem angularSchwartzMultiplier_eq_integral {n : ℕ} {m : Space n → ℝ}
    (hm : m.HasTemperateGrowth) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    angularSchwartzMultiplier m f x =
      angularInverse (fun ξ => m ξ • angularFourier f ξ) x := by
  rw [angularSchwartzMultiplier,SchwartzMap.fourierMultiplierCLM_apply,
    SchwartzMap.fourierInv_coe,angularInverse_eq_fourierInv_scaled]
  apply Real.fourierInv_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    rw [SchwartzMap.smulLeftCLM_apply_apply (angularSchwartzMultiplier_temperate hm)]
    dsimp only
    rw [angularFourier_scaled,SchwartzMap.fourier_coe]

def besselPotentialSchwartz {n : ℕ} (s : ℝ) (f : SchwartzMap (Space n) ℂ) :
    SchwartzMap (Space n) ℂ :=
  angularSchwartzMultiplier (fun ξ => (1+‖ξ‖^2)^(s/2)) f

theorem besselPotentialSchwartz_eq {n : ℕ} (s : ℝ)
    (f : SchwartzMap (Space n) ℂ) :
    (besselPotentialSchwartz s f : Space n → ℂ) = besselPotential s f := by
  funext x
  exact angularSchwartzMultiplier_eq_integral
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow (Space n) (s/2)) f x

theorem memLp_besselPotential {n : ℕ} (s : ℝ)
    (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    MemLp (besselPotential s f) p volume := by
  rw [← besselPotentialSchwartz_eq]
  exact (besselPotentialSchwartz s f).memLp p

open Set Metric
def smoothingLowBump (n : ℕ) : ContDiffBump (0 : Space n) where
  rIn := 8
  rOut := 16
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def smoothingLowCutoff {n : ℕ} (ξ : Space n) : ℂ := smoothingLowBump n ξ

/-- Its dilated differences give the annular pieces, at scales `2⁻ʲ`. -/
def smoothingAnnularCutoff {n : ℕ} (ξ : Space n) : ℂ :=
  smoothingLowCutoff ((1 / 2 : ℝ) • ξ) - smoothingLowCutoff ξ

def smoothingDyadicScale (j : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ j

theorem smoothingDyadicScale_pos (j : ℕ) : 0 < smoothingDyadicScale j := by
  unfold smoothingDyadicScale
  positivity

theorem smoothingDyadicScale_le_one (j : ℕ) : smoothingDyadicScale j ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem smoothingDyadicScale_succ (j : ℕ) :
    smoothingDyadicScale (j + 1) = (1 / 2 : ℝ) * smoothingDyadicScale j := by
  simp only [smoothingDyadicScale, pow_succ]
  ring

theorem contDiff_smoothingLowCutoff (n : ℕ) :
    ContDiff ℝ ∞ (@smoothingLowCutoff n) :=
  Complex.ofRealCLM.contDiff.comp (smoothingLowBump n).contDiff

theorem hasCompactSupport_smoothingLowCutoff (n : ℕ) :
    HasCompactSupport (@smoothingLowCutoff n) := by
  exact (smoothingLowBump n).hasCompactSupport.comp_left rfl

theorem smoothingLowCutoff_eq_one {n : ℕ} {ξ : Space n} (hξ : ‖ξ‖ ≤ 1) :
    smoothingLowCutoff ξ = 1 := by
  have hξ' : ‖ξ‖ ≤ 8 := hξ.trans (by norm_num)
  have h := (smoothingLowBump n).one_of_mem_closedBall (by
    simpa only [mem_closedBall, dist_zero_right, smoothingLowBump] using hξ')
  simp only [smoothingLowCutoff, h, Complex.ofReal_one]

theorem norm_smoothingLowCutoff_le_one {n : ℕ} (ξ : Space n) :
    ‖smoothingLowCutoff ξ‖ ≤ 1 := by
  simpa only [smoothingLowCutoff, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (smoothingLowBump n).nonneg] using
    (smoothingLowBump n).le_one (x := ξ)

theorem contDiff_smoothingAnnularCutoff (n : ℕ) :
    ContDiff ℝ ∞ (@smoothingAnnularCutoff n) := by
  have hd : ContDiff ℝ ∞ (fun ξ : Space n ↦ (1 / 2 : ℝ) • ξ) :=
    contDiff_id.const_smul _
  exact ((contDiff_smoothingLowCutoff n).comp hd).sub (contDiff_smoothingLowCutoff n)

theorem hasCompactSupport_smoothingAnnularCutoff (n : ℕ) :
    HasCompactSupport (@smoothingAnnularCutoff n) :=
  ((hasCompactSupport_smoothingLowCutoff n).comp_smul (by norm_num : (1 / 2 : ℝ) ≠ 0)).sub
    (hasCompactSupport_smoothingLowCutoff n)

theorem smoothingAnnularCutoff_eq_zero {n : ℕ} {ξ : Space n} (hξ : ‖ξ‖ ≤ 1) :
    smoothingAnnularCutoff ξ = 0 := by
  have hh : ‖(1 / 2 : ℝ) • ξ‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [norm_nonneg ξ]
  simp only [smoothingAnnularCutoff, smoothingLowCutoff_eq_one hh,
    smoothingLowCutoff_eq_one hξ, sub_self]

theorem zero_notMem_tsupport_smoothingAnnularCutoff (n : ℕ) :
    (0 : Space n) ∉ tsupport smoothingAnnularCutoff := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [Metric.ball_mem_nhds (0 : Space n) (by norm_num : (0 : ℝ) < 1)] with ξ hξ
  exact smoothingAnnularCutoff_eq_zero (le_of_lt (by
    simpa only [mem_ball, dist_zero_right] using hξ))

/-- The finite partition is an exact telescoping identity, before taking limits. -/
theorem smoothing_dyadic_partition {n : ℕ} (N : ℕ) (ξ : Space n) :
    smoothingLowCutoff ξ +
      ∑ j ∈ Finset.range N, smoothingAnnularCutoff (smoothingDyadicScale j • ξ) =
        smoothingLowCutoff (smoothingDyadicScale N • ξ) := by
  induction N with
  | zero => simp [smoothingDyadicScale]
  | succ N hN =>
    rw [Finset.sum_range_succ, ← add_assoc, hN]
    simp only [smoothingAnnularCutoff, smul_smul, smoothingDyadicScale_succ]
    ring

theorem eventually_smoothingLowCutoff_dyadic_eq_one {n : ℕ} (ξ : Space n) :
    ∀ᶠ N : ℕ in atTop, smoothingLowCutoff (smoothingDyadicScale N • ξ) = 1 := by
  have hscale : Tendsto smoothingDyadicScale atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hz : Tendsto (fun N ↦ smoothingDyadicScale N • ξ) atTop (𝓝 (0 : Space n)) := by
    simpa only [zero_smul] using hscale.smul_const ξ
  filter_upwards [hz.eventually (Metric.ball_mem_nhds (0 : Space n)
    (by norm_num : (0 : ℝ) < 1))] with N hN
  exact smoothingLowCutoff_eq_one (le_of_lt (by
    simpa only [mem_ball, dist_zero_right] using hN))

theorem tendsto_smoothing_dyadic_partition {n : ℕ} (ξ : Space n) :
    Tendsto (fun N : ℕ ↦ smoothingLowCutoff ξ +
      ∑ j ∈ Finset.range N, smoothingAnnularCutoff (smoothingDyadicScale j • ξ))
      atTop (𝓝 1) := by
  simp only [smoothing_dyadic_partition]
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_smoothingLowCutoff_dyadic_eq_one ξ] with N hN
  exact hN.symm

def smoothingDyadicLog (j : ℕ) : ℝ := 1 + Real.log (1 / smoothingDyadicScale j)

theorem smoothingDyadicLog_eq (j : ℕ) :
    smoothingDyadicLog j = 1 + (j : ℝ) * Real.log 2 := by
  simp [smoothingDyadicLog, smoothingDyadicScale, Real.log_pow]

theorem smoothingDyadicLog_pos (j : ℕ) : 0 < smoothingDyadicLog j := by
  rw [smoothingDyadicLog_eq]
  positivity

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  exact h

theorem smoothingDyadicLog_le (j : ℕ) : smoothingDyadicLog j ≤ (j : ℝ) + 1 := by
  rw [smoothingDyadicLog_eq]
  nlinarith [log_two_le_one, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

theorem smoothingDyadicLog_ge (j : ℕ) :
    Real.log 2 * ((j : ℝ) + 1) ≤ smoothingDyadicLog j := by
  rw [smoothingDyadicLog_eq]
  nlinarith [log_two_le_one]

theorem smoothingDyadicScale_rpow (j : ℕ) (ε : ℝ) :
    smoothingDyadicScale j ^ ε = ((2 : ℝ)⁻¹ ^ ε) ^ j := by
  rw [smoothingDyadicScale, ← Real.rpow_natCast_mul (by norm_num)]
  rw [mul_comm (j : ℝ) ε, Real.rpow_mul_natCast (by norm_num)]

theorem summable_smoothing_log_rpow {q : ℝ} (hq : q < -1) :
    Summable (fun j : ℕ ↦ smoothingDyadicLog j ^ q) := by
  have hs : Summable (fun j : ℕ ↦ ((j : ℝ) + 1) ^ q) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hq)
  have hc := hs.mul_left (Real.log 2 ^ q)
  apply Summable.of_nonneg_of_le
    (fun j ↦ Real.rpow_nonneg (smoothingDyadicLog_pos j).le q) (fun j ↦ ?_) hc
  calc
    smoothingDyadicLog j ^ q ≤ (Real.log 2 * ((j : ℝ) + 1)) ^ q :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (smoothingDyadicLog_ge j) (by linarith)
    _ = Real.log 2 ^ q * ((j : ℝ) + 1) ^ q :=
      Real.mul_rpow (Real.log_pos (by norm_num)).le (by positivity)

theorem summable_smoothing_log_weights (A : ℕ) {B : ℝ} (hB : (A : ℝ) + 1 < B) :
    Summable (fun j : ℕ ↦ smoothingDyadicLog j ^ A * smoothingDyadicLog j ^ (-B)) := by
  have he (j : ℕ) : smoothingDyadicLog j ^ A * smoothingDyadicLog j ^ (-B) =
      smoothingDyadicLog j ^ ((A : ℝ) - B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (smoothingDyadicLog_pos j)]
    congr 1
  simp_rw [he]
  exact summable_smoothing_log_rpow (by linarith)

theorem summable_shifted_pow_mul_geometric (A : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun j : ℕ ↦ ((j : ℝ) + 1) ^ A * r ^ j) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one A
    (show ‖r‖ < 1 by rwa [Real.norm_eq_abs, abs_of_pos hr])
  have ht := ((summable_nat_add_iff 1).mpr hs).mul_left r⁻¹
  apply ht.congr
  intro j
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

theorem summable_smoothing_sobolev_weights (A : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun j : ℕ ↦ smoothingDyadicScale j ^ ε * smoothingDyadicLog j ^ A) := by
  let r : ℝ := (2 : ℝ)⁻¹ ^ ε
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hε
  have hs := summable_shifted_pow_mul_geometric A hr hr1
  apply Summable.of_nonneg_of_le
    (fun j ↦ mul_nonneg (Real.rpow_nonneg (smoothingDyadicScale_pos j).le ε)
      (pow_nonneg (smoothingDyadicLog_pos j).le A)) (fun j ↦ ?_) hs
  rw [smoothingDyadicScale_rpow]
  change r ^ j * smoothingDyadicLog j ^ A ≤ ((j : ℝ) + 1) ^ A * r ^ j
  rw [mul_comm (r ^ j)]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (smoothingDyadicLog_pos j).le (smoothingDyadicLog_le j) A)
    (pow_nonneg hr.le j)

def frequencyHalfWave {n : ℕ} (φ : Space n → ℂ) (h t : ℝ)
    (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦ Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
    φ (h • ξ) * angularFourier f ξ)

theorem integrable_angularFourier_schwartz {n : ℕ} (u : SchwartzMap (Space n) ℂ) :
    Integrable (angularFourier u) := by
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hFu : Integrable (⇑(𝓕 u : SchwartzMap (Space n) ℂ)) volume := (𝓕 u).integrable
  have H := hFu.comp_smul (inv_ne_zero hπ)
  have he : angularFourier u = fun ξ ↦ (𝓕 u : SchwartzMap (Space n) ℂ) ((2 * Real.pi)⁻¹ • ξ) := by
    funext ξ
    rw [SchwartzMap.fourier_coe, ← angularFourier_scaled, smul_smul, mul_inv_cancel₀ hπ, one_smul]
  rwa [he]

theorem integrable_angularKernel_mul {n : ℕ} {g : Space n → ℂ}
    (hg : Integrable g) (x : Space n) :
    Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g ξ) := by
  apply hg.norm.mono'
  · exact (by fun_prop : Continuous (fun ξ : Space n ↦
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)))).aestronglyMeasurable.mul
      hg.aestronglyMeasurable
  · filter_upwards [] with ξ
    simp [Complex.norm_exp]

theorem angularInverse_sub_of_integrable {n : ℕ} {g k : Space n → ℂ}
    (hg : Integrable g) (hk : Integrable k) (x : Space n) :
    angularInverse (fun ξ ↦ g ξ - k ξ) x = angularInverse g x - angularInverse k x := by
  simp only [angularInverse, mul_sub,
    integral_sub (integrable_angularKernel_mul hg x) (integrable_angularKernel_mul hk x), smul_sub]

theorem integrable_wave_cutoff_symbol {n : ℕ} {χ : Space n → ℂ}
    (hχ : Continuous χ) {C : ℝ} (hC : ∀ ξ, ‖χ ξ‖ ≤ C)
    (h t : ℝ) (f : SchwartzMap (Space n) ℂ) :
    Integrable (fun ξ ↦ Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
      χ (h • ξ) * angularFourier f ξ) := by
  have hF := integrable_angularFourier_schwartz f
  apply (hF.norm.const_mul C).mono'
  · exact (by fun_prop : Continuous (fun ξ : Space n ↦
      Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) * χ (h • ξ))).aestronglyMeasurable.mul
      hF.aestronglyMeasurable
  · filter_upwards [] with ξ
    simpa only [norm_mul, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_mul, sub_zero, neg_zero, Real.exp_zero, one_mul] using
      mul_le_mul_of_nonneg_right (hC (h • ξ)) (norm_nonneg (angularFourier f ξ))

theorem smoothing_annular_wave_eq_sub {n : ℕ} (j : ℕ) (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) t f x =
      frequencyHalfWave smoothingLowCutoff (smoothingDyadicScale (j + 1)) t f x -
      frequencyHalfWave smoothingLowCutoff (smoothingDyadicScale j) t f x := by
  have hI (h : ℝ) := integrable_wave_cutoff_symbol (contDiff_smoothingLowCutoff n).continuous
    norm_smoothingLowCutoff_le_one h t f
  unfold frequencyHalfWave
  rw [← angularInverse_sub_of_integrable (hI _) (hI _) x]
  congr 1
  funext ξ
  simp only [smoothingAnnularCutoff, smoothingDyadicScale_succ, smul_smul]
  ring

/-- The actual half-wave integrals obey the finite telescoping decomposition. -/
theorem smoothing_wave_dyadic_partition {n : ℕ} (N : ℕ) (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    frequencyHalfWave smoothingLowCutoff 1 t f x +
      ∑ j ∈ Finset.range N,
        frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) t f x =
      frequencyHalfWave smoothingLowCutoff (smoothingDyadicScale N) t f x := by
  induction N with
  | zero => simp [smoothingDyadicScale]
  | succ N hN =>
    rw [Finset.sum_range_succ, ← add_assoc, hN, smoothing_annular_wave_eq_sub]
    ring

/-- Dominated convergence removes the low-pass truncation for the literal
Fourier-integral propagator, pointwise in both space and time. -/
theorem tendsto_smoothing_low_wave {n : ℕ} (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Tendsto (fun N : ℕ ↦
      frequencyHalfWave smoothingLowCutoff (smoothingDyadicScale N) t f x)
      atTop (𝓝 (halfWaveIntegral t f x)) := by
  unfold frequencyHalfWave halfWaveIntegral angularInverse
  apply Tendsto.const_smul
  apply tendsto_integral_of_dominated_convergence (fun ξ ↦ ‖angularFourier f ξ‖)
  · intro N
    exact (integrable_angularKernel_mul
      (integrable_wave_cutoff_symbol (contDiff_smoothingLowCutoff n).continuous
        norm_smoothingLowCutoff_le_one _ t f) x).aestronglyMeasurable
  · exact (integrable_angularFourier_schwartz f).norm
  · intro N
    filter_upwards [] with ξ
    have H := mul_le_mul_of_nonneg_right
      (norm_smoothingLowCutoff_le_one (smoothingDyadicScale N • ξ))
      (norm_nonneg (angularFourier f ξ))
    simpa [norm_mul, Complex.norm_exp] using H
  · filter_upwards [] with ξ
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_smoothingLowCutoff_dyadic_eq_one ξ] with N hN
    simp only [hN, mul_one]

theorem tendsto_smoothing_wave_dyadic_partition {n : ℕ} (t : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    Tendsto (fun N : ℕ ↦ frequencyHalfWave smoothingLowCutoff 1 t f x +
      ∑ j ∈ Finset.range N,
        frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) t f x)
      atTop (𝓝 (halfWaveIntegral t f x)) := by
  simpa only [smoothing_wave_dyadic_partition] using tendsto_smoothing_low_wave t f x

theorem eLpNorm_le_base_add_tsum_of_tendsto {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {u₀ v : X → E} {u : ℕ → X → E}
    (h₀ : AEStronglyMeasurable u₀ μ) (hu : ∀ j, AEStronglyMeasurable (u j) μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hlim : ∀ x, Tendsto (fun N ↦ u₀ x + ∑ j ∈ Finset.range N, u j x)
      atTop (𝓝 (v x))) :
    eLpNorm v p μ ≤ eLpNorm u₀ p μ + ∑' j, eLpNorm (u j) p μ := by
  apply Lp.eLpNorm_le_of_ae_tendsto
    (f := fun N x ↦ u₀ x + ∑ j ∈ Finset.range N, u j x)
    (Eventually.of_forall fun N ↦ ?_)
    (fun N ↦ h₀.add (Finset.aestronglyMeasurable_fun_sum _ (fun j _ ↦ hu j)))
    (Eventually.of_forall hlim)
  have he : (fun x ↦ u₀ x + ∑ j ∈ Finset.range N, u j x) =
      u₀ + ∑ j ∈ Finset.range N, u j := by
    funext x
    simp only [Pi.add_apply, Finset.sum_apply]
  rw [he]
  calc
    eLpNorm (u₀ + ∑ j ∈ Finset.range N, u j) p μ ≤
        eLpNorm u₀ p μ + eLpNorm (∑ j ∈ Finset.range N, u j) p μ :=
      eLpNorm_add_le (μ := μ) (p := p) (f := u₀)
        (g := ∑ j ∈ Finset.range N, u j) h₀ (Finset.aestronglyMeasurable_sum _ (fun j _ => hu j)) hp
    _ ≤ eLpNorm u₀ p μ + ∑ j ∈ Finset.range N, eLpNorm (u j) p μ :=
      add_le_add le_rfl (eLpNorm_sum_le (μ := μ) (p := p) (f := u)
        (s := Finset.range N) (fun j _ => hu j) hp)
    _ ≤ eLpNorm u₀ p μ + ∑' j, eLpNorm (u j) p μ :=
      add_le_add le_rfl (ENNReal.sum_le_tsum (s := Finset.range N)
        (f := fun j ↦ eLpNorm (u j) p μ))

private lemma measurable_scale {X : Type*} [MeasurableSpace X] (c : ℝ)
    {g : X → ℂ} (hg : Measurable g) : Measurable (fun x => c • g x) := hg.const_smul c

theorem measurable_piece {n : ℕ} (χ : Space n → ℂ) (hc : Continuous χ) (h : ℝ) (f : SchwartzMap (Space n) ℂ) :
    Measurable (fun z : Space n × ℝ => frequencyHalfWave χ h (-z.2) f z.1) := by
  have hm : Measurable (angularFourier f) := by
    unfold angularFourier
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right
    apply Continuous.stronglyMeasurable
    unfold Function.uncurry
    fun_prop
  unfold frequencyHalfWave angularInverse
  apply measurable_scale
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  unfold Function.uncurry
  fun_prop
theorem eLpNorm_halfWave_le_dyadic {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral (-z.2) f z.1) p (observationMeasure n) ≤
      eLpNorm (fun z : Space n × ℝ ↦ frequencyHalfWave smoothingLowCutoff 1 (-z.2) f z.1)
        p (observationMeasure n) +
      ∑' j, eLpNorm (fun z : Space n × ℝ ↦
        frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) (-z.2) f z.1)
        p (observationMeasure n) := by
  exact eLpNorm_le_base_add_tsum_of_tendsto (measurable_piece _ (contDiff_smoothingLowCutoff n).continuous 1 f).aestronglyMeasurable (fun j => (measurable_piece _ (contDiff_smoothingAnnularCutoff n).continuous _ f).aestronglyMeasurable) hp (fun z => tendsto_smoothing_wave_dyadic_partition (-z.2) f z.1)
theorem smoothing_bound_of_dyadic_bounds {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {g : Space n → ℂ} (hg : MemLp g p volume)
    {w : ℕ → ℝ} (hw₀ : ∀ j, 0 ≤ w j) (hw : Summable w)
    {C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hlow : eLpNorm (fun z : Space n × ℝ ↦
        frequencyHalfWave smoothingLowCutoff 1 (-z.2) f z.1) p (observationMeasure n) ≤
      ENNReal.ofReal C₀ * eLpNorm g p volume)
    (hann : ∀ j, eLpNorm (fun z : Space n × ℝ ↦
        frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) (-z.2) f z.1)
        p (observationMeasure n) ≤
      ENNReal.ofReal (C₁ * w j) * eLpNorm g p volume) :
    eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral (-z.2) f z.1) p (observationMeasure n) ≤
      ENNReal.ofReal (C₀ + C₁ * ∑' j, w j) * eLpNorm g p volume := by
  have hsum : (∑' j, ENNReal.ofReal (C₁ * w j) * eLpNorm g p volume) =
      ENNReal.ofReal (C₁ * ∑' j, w j) * eLpNorm g p volume := by
    simp_rw [ENNReal.ofReal_mul hC₁]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left,
      ← ENNReal.ofReal_tsum_of_nonneg hw₀ hw, ← ENNReal.ofReal_mul hC₁]
  have hb : eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral (-z.2) f z.1)
      p (observationMeasure n) ≤
      ENNReal.ofReal (C₀ + C₁ * ∑' j, w j) * eLpNorm g p volume := by
    calc
      _ ≤ eLpNorm (fun z : Space n × ℝ ↦
          frequencyHalfWave smoothingLowCutoff 1 (-z.2) f z.1) p (observationMeasure n) +
          ∑' j, eLpNorm (fun z : Space n × ℝ ↦
            frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) (-z.2) f z.1)
            p (observationMeasure n) := eLpNorm_halfWave_le_dyadic f hp
      _ ≤ ENNReal.ofReal C₀ * eLpNorm g p volume +
          ∑' j, ENNReal.ofReal (C₁ * w j) * eLpNorm g p volume :=
        add_le_add hlow (ENNReal.tsum_le_tsum hann)
      _ = _ := by
        rw [hsum, ← add_mul, ← ENNReal.ofReal_add hC₀ (mul_nonneg hC₁ (tsum_nonneg hw₀))]
  exact hb
def order (n : ℕ) (p : ℝ) := ((n:ℝ)-1)*(1/2-1/p)-1/p
def Low : Prop := ∀ (n : ℕ), 2 ≤ n → ∀ (p α : ℝ), 2*(n:ℝ)/(n-1) ≤ p → order n p < α →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap (Space n) ℂ,
    eLpNorm (fun z : Space n × ℝ => frequencyHalfWave smoothingLowCutoff 1 (-z.2) f z.1) (.ofReal p) (observationMeasure n) ≤ .ofReal C * eLpNorm (besselPotential α f) (.ofReal p) volume

def Annular : Prop := ∀ (n : ℕ), 2 ≤ n → ∀ (p α : ℝ), 2*(n:ℝ)/(n-1) ≤ p → order n p < α →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (f : SchwartzMap (Space n) ℂ),
    eLpNorm (fun z : Space n × ℝ => frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) (-z.2) f z.1) (.ofReal p) (observationMeasure n) ≤ .ofReal (C * (smoothingDyadicScale j ^ (α-order n p) * smoothingDyadicLog j ^ (2*n+5))) * eLpNorm (besselPotential α f) (.ofReal p) volume

theorem assemble : Low → Annular → OMA.R_wpc_local_smoothing_conjecture_R1.H1 := by
  intro hlo han n hn p α hp hα
  obtain ⟨L,hL,hl⟩ := hlo n hn p α hp hα
  obtain ⟨C,hC,hc⟩ := han n hn p α hp hα
  let w := fun j => smoothingDyadicScale j ^ (α-order n p) * smoothingDyadicLog j ^ (2*n+5)
  have hw₀ (j : ℕ) : 0 ≤ w j := mul_nonneg (Real.rpow_nonneg (smoothingDyadicScale_pos j).le _) (pow_nonneg (smoothingDyadicLog_pos j).le _)
  have hw : Summable w := summable_smoothing_sobolev_weights _ (sub_pos.mpr hα)
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n:ℝ)-1 := by linarith
  have hc' := (div_le_iff₀ hd).mp hp
  have hp2 : 1 ≤ p := by by_contra! h; nlinarith [mul_lt_mul_of_pos_right h hd]
  have hp' : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp2
  let D := L + C * ∑' j, w j
  have hD : 0 ≤ D := add_nonneg hL (mul_nonneg hC (tsum_nonneg hw₀))
  refine ⟨D+1, by linarith, fun f => ?_⟩
  have hm := memLp_besselPotential α f (.ofReal p)
  refine ⟨hm.eLpNorm_lt_top, (smoothing_bound_of_dyadic_bounds f hp' hm hw₀ hw hL hC (hl f) (fun j => hc j f)).trans ?_⟩
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (show D ≤ D+1 by linarith)) le_rfl
end LSLeaf
open MeasureTheory
open scoped RealInnerProductSpace ENNReal
/- Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). -/
noncomputable section
namespace LSLeaf.LowPart
open OMA.S_wpc_local_smoothing_conjecture MeasureTheory Set Metric Filter FourierTransform
open scoped ENNReal NNReal ContDiff Topology RealInnerProductSpace ComplexConjugate
section
-- OAI.Analysis.Fourier.SquareFunction.ConvolutionRegularity
open scoped ENNReal Convolution
noncomputable def convolveKernel {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (K : Space n → H) (f : Space n → ℂ) (x : Space n) : H :=
  ∫ y, f y • K (x - y)
end
section
-- OAI.Analysis.Fourier.WavePackets.Oscillatory
open scoped RealInnerProductSpace ContDiff
/-- The phase in the semiclassically rescaled Euclidean half-wave kernel. -/
noncomputable def euclideanWavePhase {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : E) (T : ℝ) (ξ : E) : ℝ :=
  ⟪X, ξ⟫ - T * ‖ξ‖
noncomputable def oscillation {E : Type*} (φ : E → ℝ) (h : ℝ) (x : E) : ℂ :=
  Complex.exp (((φ x / h : ℝ) : ℂ) * Complex.I)
theorem continuous_oscillation {E : Type*} [TopologicalSpace E]
    {φ : E → ℝ} (hφ : Continuous φ) (h : ℝ) : Continuous (oscillation φ h) := by
  unfold oscillation
  fun_prop
theorem norm_oscillation {E : Type*} (φ : E → ℝ) (h : ℝ) (x : E) :
    ‖oscillation φ h x‖ = 1 := by
  simp [oscillation, Complex.norm_exp]
theorem hasLineDerivAt_oscillation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {φ : E → ℝ} {d h : ℝ} {x v : E}
    (hφ : HasLineDerivAt ℝ φ d x v) :
    HasLineDerivAt ℝ (oscillation φ h)
      ((Complex.I / (h : ℂ)) * (d : ℂ) * oscillation φ h x) x v := by
  change HasDerivAt (fun t : ℝ => oscillation φ h (x + t • v)) _ 0
  change HasDerivAt (fun t : ℝ => φ (x + t • v)) d 0 at hφ
  convert ((hφ.div_const h).ofReal_comp.mul_const Complex.I).cexp using 1
  · ext t
    rfl
  · simp [oscillation, Complex.ofReal_div]
    ring
/-- One integration by parts in a fixed direction, with the amplitude written
as the directional phase derivative times `b`. This is the division by the
nonstationary phase gradient used in the off-cone argument. -/
theorem oscillatory_integration_by_parts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {φ d : E → ℝ} {b b' : E → ℂ} {h : ℝ} (hh : h ≠ 0) (v : E)
    (hφ : ∀ x ∈ tsupport b, HasLineDerivAt ℝ φ (d x) x v)
    (hb : ∀ x, HasLineDerivAt ℝ b (b' x) x v)
    (hint : Integrable (fun x => oscillation φ h x * ((d x : ℂ) * b x)) μ)
    (hint' : Integrable (fun x => oscillation φ h x * b' x) μ)
    (hintb : Integrable (fun x => oscillation φ h x * b x) μ) :
    (∫ x, oscillation φ h x * ((d x : ℂ) * b x) ∂μ) =
      Complex.I * (h : ℂ) * ∫ x, oscillation φ h x * b' x ∂μ := by
  have hleft : Integrable
      (fun x => ((Complex.I / (h : ℂ)) * (d x : ℂ) * oscillation φ h x) * b x) μ := by
    convert hint.const_mul (Complex.I / (h : ℂ)) using 1
    ext x
    ring
  have hi := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℂ) hleft hint' hintb
    (fun x hx => hasLineDerivAt_oscillation (hφ x hx)) (fun x _ => hb x)
  change (∫ x, oscillation φ h x * b' x ∂μ) =
    -(∫ x, ((Complex.I / (h : ℂ)) * (d x : ℂ) * oscillation φ h x) * b x ∂μ) at hi
  have hi' : (∫ x, oscillation φ h x * b' x ∂μ) =
      -(Complex.I / (h : ℂ) * ∫ x, oscillation φ h x * ((d x : ℂ) * b x) ∂μ) := by
    rw [← integral_const_mul]
    convert hi using 2
    congr 1
    ext x
    ring
  rw [hi']
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  field_simp
  simp [Complex.I_sq]
/-- Repeated integration by parts with explicit amplitude recursion. At each
stage `a k = d * b k` and `a (k+1)` is the derivative of `b k`. -/
theorem iterated_oscillatory_integration_by_parts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {φ d : E → ℝ} {a b : ℕ → E → ℂ} {h : ℝ} (hh : h ≠ 0) (v : E) (N : ℕ)
    (hφ : ∀ k < N, ∀ x ∈ tsupport (b k), HasLineDerivAt ℝ φ (d x) x v)
    (hb : ∀ k < N, ∀ x, HasLineDerivAt ℝ (b k) (a (k + 1) x) x v)
    (ha : ∀ k < N, ∀ x, a k x = (d x : ℂ) * b k x)
    (hinta : ∀ k ≤ N, Integrable (fun x => oscillation φ h x * a k x) μ)
    (hintb : ∀ k < N, Integrable (fun x => oscillation φ h x * b k x) μ) :
    (∫ x, oscillation φ h x * a 0 x ∂μ) =
      (Complex.I * (h : ℂ)) ^ N * ∫ x, oscillation φ h x * a N x ∂μ := by
  have step (k : ℕ) (hk : k < N) :
      (∫ x, oscillation φ h x * a k x ∂μ) =
        Complex.I * (h : ℂ) * ∫ x, oscillation φ h x * a (k + 1) x ∂μ := by
    have hi := oscillatory_integration_by_parts hh v (hφ k hk) (hb k hk)
      (by simpa only [← ha k hk] using hinta k hk.le)
      (hinta (k + 1) hk) (hintb k hk)
    simpa only [← ha k hk] using hi
  have induction_step : ∀ k, k ≤ N →
      (∫ x, oscillation φ h x * a 0 x ∂μ) =
        (Complex.I * (h : ℂ)) ^ k * ∫ x, oscillation φ h x * a k x ∂μ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      rw [ih (Nat.le_of_succ_le hk), step k hk, pow_succ]
      ring
  exact induction_step N le_rfl
/-- The explicit decay bound obtained after `N` integrations by parts. -/
theorem norm_integral_oscillation_mul_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {φ d : E → ℝ} {a b : ℕ → E → ℂ} {h : ℝ} (hh : 0 < h) (v : E) (N : ℕ)
    (hφ : ∀ k < N, ∀ x ∈ tsupport (b k), HasLineDerivAt ℝ φ (d x) x v)
    (hb : ∀ k < N, ∀ x, HasLineDerivAt ℝ (b k) (a (k + 1) x) x v)
    (ha : ∀ k < N, ∀ x, a k x = (d x : ℂ) * b k x)
    (hinta : ∀ k ≤ N, Integrable (fun x => oscillation φ h x * a k x) μ)
    (hintb : ∀ k < N, Integrable (fun x => oscillation φ h x * b k x) μ) :
    ‖∫ x, oscillation φ h x * a 0 x ∂μ‖ ≤ h ^ N * ∫ x, ‖a N x‖ ∂μ := by
  rw [iterated_oscillatory_integration_by_parts hh.ne' v N hφ hb ha hinta hintb]
  simp only [norm_mul, norm_pow, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hh]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hh.le _)
  simpa only [norm_mul, norm_oscillation, one_mul] using
    norm_integral_le_integral_norm (fun x => oscillation φ h x * a N x)
noncomputable def quotientAmplitude {E : Type*} (d : E → ℂ) (a : E → ℂ) : E → ℂ :=
  fun ξ => a ξ / d ξ
theorem tsupport_quotientAmplitude_subset {E : Type*} [TopologicalSpace E]
    (d a : E → ℂ) : tsupport (quotientAmplitude d a) ⊆ tsupport a := by
  unfold quotientAmplitude
  simp_rw [div_eq_mul_inv]
  exact tsupport_mul_subset_left
end
section
-- OAI.Analysis.Fourier.WavePackets.Uniform
open scoped RealInnerProductSpace ContDiff
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
noncomputable def jointAmplitudeStep (d : P × E → ℂ) (v : P → E)
    (a : P × E → ℂ) (q : P × E) : ℂ :=
  fderiv ℝ (quotientAmplitude d a) q (0, v q.1)
theorem tsupport_jointAmplitudeStep_subset (d : P × E → ℂ) (v : P → E)
    (a : P × E → ℂ) : tsupport (jointAmplitudeStep d v a) ⊆ tsupport a := by
  apply (show tsupport (jointAmplitudeStep d v a) ⊆ tsupport (quotientAmplitude d a) from ?_).trans
    (tsupport_quotientAmplitude_subset d a)
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro q hq
  by_contra h
  have hz := fderiv_of_notMem_tsupport ℝ h
  exact hq (by simp [jointAmplitudeStep, hz])
theorem joint_quotient_contDiffOn {U : Set P} (hU : IsOpen U)
    {S : Set E} {a d : P × E → ℂ}
    (ha : ContDiffOn ℝ ∞ a (U ×ˢ Set.univ))
    (hs : tsupport a ⊆ Set.univ ×ˢ S)
    (hd : ∀ q ∈ U ×ˢ S, ContDiffAt ℝ ∞ d q)
    (hd₀ : ∀ q ∈ U ×ˢ S, d q ≠ 0) :
    ContDiffOn ℝ ∞ (quotientAmplitude d a) (U ×ˢ Set.univ) := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  by_cases hqs : q.2 ∈ S
  · have haq : ContDiffAt ℝ ∞ a q := ha.contDiffAt ((hU.prod isOpen_univ).mem_nhds hq)
    unfold quotientAmplitude
    simp_rw [div_eq_mul_inv]
    exact haq.mul ((hd q ⟨hq.1, hqs⟩).inv (hd₀ q ⟨hq.1, hqs⟩))
  · have hqz : q ∉ tsupport (quotientAmplitude d a) := by
      intro h
      exact hqs (hs (tsupport_quotientAmplitude_subset d a h)).2
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hqz)
theorem jointAmplitudeStep_contDiffOn {U : Set P} (hU : IsOpen U)
    {S : Set E} {a d : P × E → ℂ} {v : P → E}
    (ha : ContDiffOn ℝ ∞ a (U ×ˢ Set.univ)) (hv : ContDiff ℝ ∞ v)
    (hs : tsupport a ⊆ Set.univ ×ˢ S)
    (hd : ∀ q ∈ U ×ˢ S, ContDiffAt ℝ ∞ d q)
    (hd₀ : ∀ q ∈ U ×ˢ S, d q ≠ 0) :
    ContDiffOn ℝ ∞ (jointAmplitudeStep d v a) (U ×ˢ Set.univ) := by
  have hq := joint_quotient_contDiffOn hU ha hs hd hd₀
  apply (hq.fderiv_of_isOpen (hU.prod isOpen_univ) (by simp)).clm_apply
  exact (contDiff_const.prodMk (hv.comp contDiff_fst)).contDiffOn
noncomputable def jointAmplitude (d : P × E → ℂ) (v : P → E)
    (a : P × E → ℂ) : ℕ → P × E → ℂ
  | 0 => a
  | k + 1 => jointAmplitudeStep d v (jointAmplitude d v a k)
theorem jointAmplitude_regular {U : Set P} (hU : IsOpen U)
    {S : Set E} {a d : P × E → ℂ} {v : P → E}
    (ha : ContDiffOn ℝ ∞ a (U ×ˢ Set.univ)) (hv : ContDiff ℝ ∞ v)
    (hs : tsupport a ⊆ Set.univ ×ˢ S)
    (hd : ∀ q ∈ U ×ˢ S, ContDiffAt ℝ ∞ d q)
    (hd₀ : ∀ q ∈ U ×ˢ S, d q ≠ 0) (k : ℕ) :
    ContDiffOn ℝ ∞ (jointAmplitude d v a k) (U ×ˢ Set.univ) ∧
      tsupport (jointAmplitude d v a k) ⊆ Set.univ ×ˢ S := by
  induction k with
  | zero => exact ⟨ha, hs⟩
  | succ k ih =>
    exact ⟨jointAmplitudeStep_contDiffOn hU ih.1 hv ih.2 hd hd₀,
      (tsupport_jointAmplitudeStep_subset d v _).trans ih.2⟩
theorem contDiff_slice {U : Set P} (hU : IsOpen U) {a : P × E → ℂ}
    (ha : ContDiffOn ℝ ∞ a (U ×ˢ Set.univ)) {p : P} (hp : p ∈ U) :
    ContDiff ℝ ∞ (fun ξ => a (p, ξ)) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  exact (ha.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hp, trivial⟩)).comp ξ
    (contDiffAt_const.prodMk contDiffAt_id)
omit [NormedSpace ℝ P] [NormedSpace ℝ E] in
theorem tsupport_slice_subset {S : Set E} (hS : IsClosed S) {a : P × E → ℂ}
    (ha : tsupport a ⊆ Set.univ ×ˢ S) (p : P) :
    tsupport (fun ξ => a (p, ξ)) ⊆ S := by
  apply closure_minimal ?_ hS
  intro ξ hξ
  exact (ha (subset_tsupport _ hξ)).2
theorem integral_norm_le_of_compact_support_bound
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [T2Space E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {S : Set E} (hS : IsCompact S)
    {f : E → ℂ} (hf : Function.support f ⊆ S) {C : ℝ}
    (hC : ∀ ξ ∈ S, ‖f ξ‖ ≤ C) : (∫ ξ, ‖f ξ‖ ∂μ) ≤ C * μ.real S := by
  have heq : (∫ ξ, ‖f ξ‖ ∂μ) = ∫ ξ in S, ‖f ξ‖ ∂μ := by
    rw [← integral_indicator hS.measurableSet]
    congr 1
    ext ξ
    by_cases hξ : ξ ∈ S
    · simp [hξ]
    · have hz : f ξ = 0 := by
        by_contra hn
        exact hξ (hf hn)
      simp [hξ, hz]
  rw [heq]
  have hb := norm_setIntegral_le_of_norm_le_const_ae' (μ := μ) (s := S) (f := fun ξ => ‖f ξ‖)
    hS.measure_lt_top (Filter.Eventually.of_forall fun ξ hξ => by simpa using hC ξ hξ)
  have hn : 0 ≤ ∫ ξ in S, ‖f ξ‖ ∂μ := integral_nonneg (fun ξ => norm_nonneg (f ξ))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The rescaled Euclidean kernel, with the Fourier normalization absorbed
into the amplitude. -/
noncomputable def semiclassicalWaveKernel [MeasurableSpace E]
    (μ : Measure E) (a : E → ℂ) (h T : ℝ) (X : E) : ℂ :=
  ((h : ℂ) ^ Module.finrank ℝ E)⁻¹ *
    ∫ ξ, oscillation (euclideanWavePhase X T) h ξ * a ξ ∂μ
end
section
-- OAI.Analysis.Fourier.WavePackets.Young
open scoped ENNReal NNReal
/-- Hölder's inequality against the constant function, with no finiteness
assumption on the measure or integral. -/
theorem lintegral_rpow_le_mass_mul {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, f x ∂ν) ^ p ≤ ν Set.univ ^ (p - 1) * ∫⁻ x, f x ^ p ∂ν := by
  have hp₀ : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hi : 0 ≤ 1 / p := by positivity
  have hi₁ : 0 ≤ 1 - 1 / p := by
    have : 1 / p ≤ 1 := (div_le_one hp₀).mpr hp
    linarith
  have hhold := ENNReal.lintegral_mul_norm_pow_le
    (μ := ν) (f := fun x => f x ^ p) (g := fun _ => 1)
    (hf.pow_const p).aemeasurable measurable_const.aemeasurable
    hi hi₁ (by ring)
  simp only [← ENNReal.rpow_mul, mul_one_div_cancel hp₀.ne', ENNReal.rpow_one,
    ENNReal.one_rpow, mul_one, lintegral_const] at hhold
  have hpow := ENNReal.rpow_le_rpow hhold hp₀.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp₀.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hpow
  have hi_id : 1 / p * p = 1 := by field_simp
  have hi_id' : (1 - 1 / p) * p = p - 1 := by field_simp
  simpa only [hi_id, hi_id', ENNReal.rpow_one, one_mul, mul_comm] using hpow
/-- Weighted Hölder in a form suited to convolution. -/
theorem lintegral_weighted_rpow_le {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {k f : α → ℝ≥0∞} (hk : Measurable k) (hf : Measurable f)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, k x * f x ∂ν) ^ p ≤
      (∫⁻ x, k x ∂ν) ^ (p - 1) * ∫⁻ x, k x * f x ^ p ∂ν := by
  have hb := lintegral_rpow_le_mass_mul (ν := ν.withDensity k) hf hp
  simpa only [lintegral_withDensity_eq_lintegral_mul _ hk hf,
    lintegral_withDensity_eq_lintegral_mul _ hk (hf.pow_const p),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, Pi.mul_apply] using hb
variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
  [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
/-- Young's inequality for the nonnegative convolution, before taking the
`p`-th root. It allows infinite integrals. -/
theorem lintegral_convolution_rpow_le {k f : G → ℝ≥0∞}
    (hk : Measurable k) (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, (∫⁻ y, k y * f (x - y) ∂μ) ^ p ∂μ) ≤
      (∫⁻ y, k y ∂μ) ^ p * ∫⁻ x, f x ^ p ∂μ := by
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, k y ∂μ) ^ (p - 1) *
        (∫⁻ y, k y * f (x - y) ^ p ∂μ) ∂μ := by
      apply lintegral_mono
      intro x
      exact lintegral_weighted_rpow_le hk (hf.comp (measurable_const.sub measurable_id)) hp
    _ = (∫⁻ y, k y ∂μ) ^ (p - 1) *
        (∫⁻ x, ∫⁻ y, k y * f (x - y) ^ p ∂μ ∂μ) := by
      apply lintegral_const_mul''
      fun_prop
    _ = (∫⁻ y, k y ∂μ) ^ (p - 1) *
        (∫⁻ y, ∫⁻ x, k y * f (x - y) ^ p ∂μ ∂μ) := by
      rw [lintegral_lintegral_swap (by fun_prop)]
    _ = (∫⁻ y, k y ∂μ) ^ (p - 1) *
        ((∫⁻ y, k y ∂μ) * ∫⁻ x, f x ^ p ∂μ) := by
      congr 1
      have hid (y : G) : (∫⁻ x, k y * f (x - y) ^ p ∂μ) =
          k y * ∫⁻ x, f x ^ p ∂μ := by
        have hm : AEMeasurable (fun x : G => f (x - y) ^ p) μ := by fun_prop
        rw [lintegral_const_mul'' (k y) hm,
          lintegral_sub_right_eq_self (fun x => f x ^ p) y]
      simp_rw [hid]
      exact lintegral_mul_const'' _ hk.aemeasurable
    _ = _ := by
      rw [← mul_assoc]
      congr 1
      calc
        _ = (∫⁻ y, k y ∂μ) ^ (p - 1) * (∫⁻ y, k y ∂μ) ^ (1 : ℝ) := by
          rw [ENNReal.rpow_one]
        _ = (∫⁻ y, k y ∂μ) ^ (p - 1 + 1) :=
          (ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr hp) zero_le_one).symm
        _ = _ := by congr 1; ring
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]
end
section
-- OAI.Analysis.Fourier.SquareFunction.VectorYoung
open scoped ENNReal
theorem convolveKernel_commuted {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (K : Space n → H) (f : Space n → ℂ) (x : Space n) :
    convolveKernel K f x = ∫ y, f (x - y) • K y := by
  unfold convolveKernel
  simpa only [sub_sub_cancel] using
    (integral_sub_left_eq_self (fun y => f y • K (x - y)) volume x).symm
theorem eLpNorm_convolveKernel_le {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {K : Space n → H} {f : Space n → ℂ} (hK : Continuous K)
    (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (convolveKernel K f) p volume ≤
      eLpNorm K 1 volume * eLpNorm f p volume := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_le_toReal ENNReal.one_ne_top hpt).mpr hp
  have hpr0 : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hpr
  have he : (∫⁻ x, ‖convolveKernel K f x‖ₑ ^ p.toReal) ≤
      (∫⁻ y, ‖K y‖ₑ) ^ p.toReal * ∫⁻ x, ‖f x‖ₑ ^ p.toReal := by
    apply le_trans ?_ (lintegral_convolution_rpow_le
      hK.enorm.measurable hf.enorm hpr)
    apply lintegral_mono
    intro x
    apply ENNReal.rpow_le_rpow ?_ hpr0.le
    rw [convolveKernel_commuted]
    simpa only [enorm_smul, mul_comm] using
      enorm_integral_le_lintegral_enorm (fun y => f (x - y) • K y)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
    eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hb := ENNReal.rpow_le_rpow he (show 0 ≤ 1 / p.toReal by positivity)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ 1 / p.toReal by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hpr0.ne', ENNReal.rpow_one] using hb
end
section
-- OAI.Analysis.Fourier.WavePackets.Spacetime
open scoped ENNReal
open scoped ContDiff RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]
omit [FiniteDimensional ℝ E] in
theorem continuous_semiclassicalWaveKernel_spacetime {a : E → ℂ}
    (ha : Continuous a) (hs : HasCompactSupport a) (h : ℝ) :
    Continuous (fun q : ℝ × E => semiclassicalWaveKernel μ a h q.1 q.2) := by
  apply continuous_const.mul
  apply continuous_of_dominated (bound := fun ξ => ‖a ξ‖)
  · intro q
    apply Continuous.aestronglyMeasurable
    exact (continuous_oscillation (by unfold euclideanWavePhase; fun_prop) h).mul ha
  · intro q
    exact Filter.Eventually.of_forall fun ξ => by simp [norm_oscillation]
  · exact (ha.integrable_of_hasCompactSupport hs).norm
  · apply Filter.Eventually.of_forall
    intro ξ
    unfold oscillation euclideanWavePhase
    fun_prop
end
section
-- OAI.Analysis.Fourier.WavePackets.KernelIdentity
open scoped ContDiff RealInnerProductSpace FourierTransform
noncomputable def waveAmplitude {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (h T : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  Complex.exp (-Complex.I * (((T / h) * ‖ξ‖ : ℝ) : ℂ)) * φ ξ
end
section
-- OAI.Analysis.Fourier.BochnerRiesz.Dilation
open scoped RealInnerProductSpace ENNReal
theorem angularInverse_dilate {n : ℕ} (g : Space n → ℂ) {r : ℝ} (hr : 0 < r)
    (x : Space n) :
    angularInverse (fun ξ ↦ g (r • ξ)) x = (r ^ n)⁻¹ • angularInverse g (r⁻¹ • x) := by
  have hchange := Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n))
    (fun ξ ↦ Complex.exp (Complex.I * ((inner ℝ (r⁻¹ • x) ξ : ℝ) : ℂ)) * g ξ)
    r (hR := hr.le)
  have hid (ξ : Space n) : inner ℝ (r⁻¹ • x) (r • ξ) = inner ℝ x ξ := by
    rw [real_inner_smul_left, inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  simp only [hid, Space, finrank_euclideanSpace_fin] at hchange
  simp only [angularInverse]
  rw [hchange]
  exact smul_comm _ _ _
theorem angularInverse_smul_real {n : ℕ} (c : ℝ) (g : Space n → ℂ) (x : Space n) :
    angularInverse (fun ξ ↦ c • g ξ) x = c • angularInverse g x := by
  simp only [angularInverse, mul_smul_comm, integral_smul]
  exact smul_comm _ _ _
/-- Real scalar dilation as a continuous linear equivalence. -/
def realDilationEquiv (n : ℕ) (r : ℝ) (hr : r ≠ 0) : Space n ≃L[ℝ] Space n where
  toFun x := r • x
  invFun x := r⁻¹ • x
  left_inv x := by simp [smul_smul, hr]
  right_inv x := by simp [smul_smul, hr]
  map_add' x y := smul_add _ _ _
  map_smul' c x := smul_comm _ _ _
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop
def schwartzDilate {n : ℕ} (r : ℝ) (hr : r ≠ 0) (f : SchwartzMap (Space n) ℂ) :
    SchwartzMap (Space n) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realDilationEquiv n r hr) f
theorem eLpNorm_dilate {n : ℕ} (f : Space n → ℂ) (hf : Measurable f) (p : ℝ≥0∞)
    {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x ↦ f (r • x)) p (volume : Measure (Space n)) =
      ENNReal.ofReal ((r ^ n)⁻¹) ^ (1 / p.toReal) * eLpNorm f p (volume : Measure (Space n)) := by
  have hcont : Continuous (fun x : Space n ↦ r • x) := by fun_prop
  have hm : AEMeasurable (fun x : Space n ↦ r • x) (volume : Measure (Space n)) :=
    hcont.measurable.aemeasurable
  have h := (eLpNorm_map_measure (p := p) (g := f) hf.aestronglyMeasurable hm).symm
  rw [Measure.map_addHaar_smul (volume : Measure (Space n)) hr.ne'] at h
  simp only [Space, finrank_euclideanSpace_fin,
    abs_of_pos (inv_pos.mpr (pow_pos hr n))] at h
  rw [eLpNorm_smul_measure_of_ne_zero (by positivity) _ _ _] at h
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one, smul_eq_mul] using h
end
section
-- OAI.Analysis.Fourier.BochnerRiesz.Kernel
open scoped ContDiff
/-- Uniform nonstationary phase with a smoothly varying amplitude.
This form applies to compact families of annular Sobolev multipliers. -/
theorem uniform_rapid_decay_joint_amplitude
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {U K : Set P} {S : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hS : IsCompact S) {φ : P → E → ℝ} {d : P × E → ℝ} {v : P → E} {a : P × E → ℂ}
    (hφc : ∀ p ∈ U, Continuous (φ p)) (hv : ContDiff ℝ ∞ v)
    (hφ : ∀ p ∈ U, ∀ ξ ∈ S, HasLineDerivAt ℝ (φ p) (d (p, ξ)) ξ (v p))
    (hd : ∀ q ∈ U ×ˢ S, ContDiffAt ℝ ∞ (fun q => (d q : ℂ)) q)
    (hd₀ : ∀ q ∈ U ×ˢ S, d q ≠ 0)
    (ha : ContDiffOn ℝ ∞ a (U ×ˢ Set.univ)) (hs : tsupport a ⊆ Set.univ ×ˢ S) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ h : ℝ, 0 < h →
      ‖∫ ξ, oscillation (φ p) h ξ * a (p, ξ) ∂μ‖ ≤ h ^ N * C := by
  let A := jointAmplitude (fun q => (d q : ℂ)) v a
  let B := fun k => quotientAmplitude (fun q => (d q : ℂ)) (A k)
  have hdn : ∀ q ∈ U ×ˢ S, (d q : ℂ) ≠ 0 := by
    intro q hq
    exact_mod_cast hd₀ q hq
  have hA (k : ℕ) : ContDiffOn ℝ ∞ (A k) (U ×ˢ Set.univ) ∧
      tsupport (A k) ⊆ Set.univ ×ˢ S := jointAmplitude_regular hU ha hv hs hd hdn k
  have hB (k : ℕ) : ContDiffOn ℝ ∞ (B k) (U ×ˢ Set.univ) ∧
      tsupport (B k) ⊆ Set.univ ×ˢ S :=
    ⟨joint_quotient_contDiffOn hU (hA k).1 (hA k).2 hd hdn,
      (tsupport_quotientAmplitude_subset _ _).trans (hA k).2⟩
  have hcont : ContinuousOn (A N) (K ×ˢ S) :=
    (hA N).1.continuousOn.mono (fun q hq => ⟨hKU hq.1, trivial⟩)
  obtain ⟨C, hCp, hC⟩ := ((hK.prod hS).image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  refine ⟨C * μ.real S, mul_nonneg hCp.le ENNReal.toReal_nonneg, ?_⟩
  intro p hp h hh
  have hpU := hKU hp
  have hslice (k : ℕ) : tsupport (fun ξ => A k (p, ξ)) ⊆ S :=
    tsupport_slice_subset hS.isClosed (hA k).2 p
  have hbslice (k : ℕ) : tsupport (fun ξ => B k (p, ξ)) ⊆ S :=
    tsupport_slice_subset hS.isClosed (hB k).2 p
  have hdecay : ‖∫ ξ, oscillation (φ p) h ξ * a (p, ξ) ∂μ‖ ≤
      h ^ N * ∫ ξ, ‖A N (p, ξ)‖ ∂μ := by
    apply norm_integral_oscillation_mul_le (a := fun k ξ => A k (p, ξ))
      (b := fun k ξ => B k (p, ξ)) (d := fun ξ => d (p, ξ)) hh (v p) N
    · intro k _ ξ hξ
      exact hφ p hpU ξ (hbslice k hξ)
    · intro k _ ξ
      have hdiff := ((hB k).1.contDiffAt
        ((hU.prod isOpen_univ).mem_nhds (show (p, ξ) ∈ U ×ˢ Set.univ from ⟨hpU, trivial⟩))).differentiableAt (by simp)
      simpa [HasLineDerivAt, A, jointAmplitude, jointAmplitudeStep] using
        hdiff.hasFDerivAt.hasLineDerivAt (0, v p)
    · intro k _ ξ
      dsimp [B, quotientAmplitude]
      by_cases hξ : ξ ∈ S
      · field_simp [hdn (p, ξ) ⟨hpU, hξ⟩]
      · have hz : A k (p, ξ) = 0 := image_eq_zero_of_notMem_tsupport
          (fun hmem => hξ ((hA k).2 hmem).2)
        simp [hz]
    · intro k _
      have hsa : HasCompactSupport (fun ξ => A k (p, ξ)) :=
        hS.of_isClosed_subset (isClosed_tsupport _) (hslice k)
      exact ((continuous_oscillation (hφc p hpU) h).mul
        (contDiff_slice hU (hA k).1 hpU).continuous).integrable_of_hasCompactSupport hsa.mul_left
    · intro k _
      have hsb : HasCompactSupport (fun ξ => B k (p, ξ)) :=
        hS.of_isClosed_subset (isClosed_tsupport _) (hbslice k)
      exact ((continuous_oscillation (hφc p hpU) h).mul
        (contDiff_slice hU (hB k).1 hpU).continuous).integrable_of_hasCompactSupport hsb.mul_left
  apply hdecay.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hh.le N)
  apply integral_norm_le_of_compact_support_bound hS
    (subset_trans (subset_tsupport _) (hslice N))
  intro ξ hξ
  exact hC _ ⟨(p, ξ), ⟨hp, hξ⟩, rfl⟩
/-- Compact smooth families with a common compact support have uniform
Fourier decay. The direction of the Fourier variable is another compact
parameter; integration by parts differentiates in that direction. -/
theorem uniform_fourier_integral_decay
    {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {K : Set Q} {S : Set E} (hK : IsCompact K) (hS : IsCompact S)
    {a : Q × E → ℂ} (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ Set.univ ×ˢ S) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ x : E, x ≠ 0 →
      ‖∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ) ∂μ‖ ≤
        (‖x‖⁻¹) ^ N * C := by
  let U : Set (E × Q) := {p | 0 < ‖p.1‖}
  let K' : Set (E × Q) := Metric.sphere (0 : E) 1 ×ˢ K
  let a' : (E × Q) × E → ℂ := fun z ↦ a (z.1.2, z.2)
  have hU : IsOpen U := isOpen_lt continuous_const continuous_fst.norm
  have hK' : IsCompact K' := (isCompact_sphere (0 : E) 1).prod hK
  have hKU : K' ⊆ U := by
    intro p hp
    have hu : ‖p.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp.1
    change 0 < ‖p.1‖
    rw [hu]
    norm_num
  have ha' : ContDiff ℝ ∞ a' := ha.comp (contDiff_fst.snd.prodMk contDiff_snd)
  have hs' : tsupport a' ⊆ Set.univ ×ˢ S := by
    intro z hz
    refine ⟨trivial, ?_⟩
    exact (hs (tsupport_comp_subset_preimage a (continuous_fst.snd.prodMk continuous_snd) hz)).2
  obtain ⟨C, hC, hb⟩ := uniform_rapid_decay_joint_amplitude (μ := μ) hU hK' hKU hS
    (φ := fun p ξ ↦ inner ℝ p.1 ξ) (d := fun z ↦ inner ℝ z.1.1 z.1.1)
    (v := fun p ↦ p.1) (a := a')
    (fun _ _ ↦ continuous_const.inner continuous_id) contDiff_fst
    (fun p _ ξ _ ↦ (innerSL ℝ p.1).hasFDerivAt.hasLineDerivAt p.1)
    (by
      intro z _
      have hdreal : ContDiff ℝ ∞ (fun z : (E × Q) × E ↦ inner ℝ z.1.1 z.1.1) :=
        ContDiff.inner (𝕜 := ℝ) contDiff_fst.fst contDiff_fst.fst
      exact (Complex.ofRealCLM.contDiff.comp hdreal).contDiffAt)
    (by
      intro z hz
      rw [real_inner_self_eq_norm_sq]
      exact pow_ne_zero _ (ne_of_gt hz.1))
    ha'.contDiffOn hs' N
  refine ⟨C, hC, ?_⟩
  intro q hq x hx
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let u : E := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hnorm.ne']
  have hp : (u, q) ∈ K' := ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using hu, hq⟩
  have hbound := hb (u, q) hp (‖x‖⁻¹) (inv_pos.mpr hnorm)
  have heq (ξ : E) : oscillation (fun ξ ↦ inner ℝ u ξ) (‖x‖⁻¹) ξ =
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) := by
    have hreal : inner ℝ u ξ / ‖x‖⁻¹ = inner ℝ x ξ := by
      dsimp only [u]
      rw [real_inner_smul_left]
      field_simp
    unfold oscillation
    rw [hreal]
    congr 1
    ring
  simpa only [heq, a'] using hbound
theorem bounded_and_power_decay {a F B D : ℝ} (ha : 0 ≤ a) (_ : 0 ≤ F)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (N : ℕ) (hsmall : F ≤ B)
    (hlarge : 0 < a → F ≤ (a⁻¹) ^ N * D) :
    F ≤ (2 ^ N * (B + D)) * (1 + a) ^ (-(N : ℝ)) := by
  have htwo : 0 ≤ (2 : ℝ) ^ N := by positivity
  have hmul : F * (1 + a) ^ N ≤ 2 ^ N * (B + D) := by
    by_cases haone : a ≤ 1
    · calc
        F * (1 + a) ^ N ≤ B * 2 ^ N :=
          mul_le_mul hsmall (pow_le_pow_left₀ (by linarith) (by linarith) N) (by positivity) hB
        _ ≤ 2 ^ N * (B + D) := by nlinarith
    · have hapos : 0 < a := by linarith
      calc
        F * (1 + a) ^ N ≤ ((a⁻¹) ^ N * D) * (2 * a) ^ N :=
          mul_le_mul (hlarge hapos) (pow_le_pow_left₀ (by linarith) (by linarith) N)
            (by positivity) (by positivity)
        _ = 2 ^ N * D := by rw [mul_pow, inv_pow]; field_simp
        _ ≤ 2 ^ N * (B + D) := by nlinarith
  rw [Real.rpow_neg (by linarith : 0 ≤ 1 + a), Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos (by linarith) N)).mpr hmul
theorem uniform_fourier_integral_bound
    {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {K : Set Q} {S : Set E} (hK : IsCompact K) (hS : IsCompact S)
    {a : Q × E → ℂ} (ha : Continuous a) (hs : tsupport a ⊆ Set.univ ×ˢ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ x : E,
      ‖∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ) ∂μ‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := ((hK.prod hS).image ha).isBounded.exists_pos_norm_le
  refine ⟨B * μ.real S, mul_nonneg hB.le ENNReal.toReal_nonneg, ?_⟩
  intro q hq x
  calc
    _ ≤ ∫ ξ, ‖Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ, ‖a (q, ξ)‖ ∂μ := by
      congr 1
      ext ξ
      simp [Complex.norm_exp]
    _ ≤ B * μ.real S := by
      apply integral_norm_le_of_compact_support_bound hS
        ((subset_tsupport _).trans (tsupport_slice_subset hS.isClosed hs q))
      intro ξ hξ
      exact hb _ ⟨(q, ξ), ⟨hq, hξ⟩, rfl⟩
theorem uniform_fourier_integral_polynomial_decay
    {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {K : Set Q} {S : Set E} (hK : IsCompact K) (hS : IsCompact S)
    {a : Q × E → ℂ} (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ Set.univ ×ˢ S) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ x : E,
      ‖∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ) ∂μ‖ ≤
        C * (1 + ‖x‖) ^ (-(N : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := uniform_fourier_integral_bound (μ := μ) hK hS ha.continuous hs
  obtain ⟨D, hD, hd⟩ := uniform_fourier_integral_decay (μ := μ) hK hS ha hs N
  refine ⟨2 ^ N * (B + D), by positivity, ?_⟩
  intro q hq x
  exact bounded_and_power_decay (norm_nonneg _) (norm_nonneg _) hB hD N (hb q hq x)
    (fun hx ↦ hd q hq x (norm_pos_iff.mp hx))
theorem continuous_positive_fourier_integral
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {g : E → ℂ}
    (hg : Integrable g μ) :
    Continuous (fun x : E ↦ ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g ξ ∂μ) := by
  have hnorm (x ξ : E) : ‖Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g ξ‖ = ‖g ξ‖ := by
    simp [Complex.norm_exp]
  have hi (x : E) : Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g ξ) μ := by
    have hc : Continuous (fun ξ : E ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))) := by fun_prop
    exact hg.mono (hc.aestronglyMeasurable.mul hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ ↦ (hnorm x ξ).le)
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_integral_filter_of_dominated_convergence (fun ξ ↦ ‖g ξ‖)
  · exact Filter.Eventually.of_forall fun z ↦ (hi z).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z ↦ Filter.Eventually.of_forall fun ξ ↦ (hnorm z ξ).le
  · exact hg.norm
  · exact Filter.Eventually.of_forall fun ξ ↦ Continuous.tendsto (by fun_prop) x
/-- A compact smooth family of compactly supported symbols has inverse
Fourier kernels with uniformly bounded L¹ norms. -/
theorem uniform_fourier_integral_L1
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] {n : ℕ}
    {K : Set Q} {S : Set (Space n)} (hK : IsCompact K) (hS : IsCompact S)
    {a : Q × Space n → ℂ} (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ Set.univ ×ˢ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K,
      Integrable (fun x : Space n ↦ ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ)) ∧
      (∫ x : Space n, ‖∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ)‖) ≤ C := by
  obtain ⟨D, hD, hb⟩ := uniform_fourier_integral_polynomial_decay (μ := (volume : Measure (Space n)))
    hK hS ha hs (n + 1)
  let w : Space n → ℝ := fun x ↦ D * (1 + ‖x‖) ^ (-((n + 1 : ℕ) : ℝ))
  have hw : Integrable w := by
    apply Integrable.const_mul
    apply integrable_one_add_norm
    simp [Space]
  refine ⟨∫ x, w x, integral_nonneg (fun x ↦ mul_nonneg hD (Real.rpow_nonneg (by positivity) _)), ?_⟩
  intro q hq
  have hslice : HasCompactSupport (fun ξ ↦ a (q, ξ)) :=
    hS.of_isClosed_subset (isClosed_tsupport _) (tsupport_slice_subset hS.isClosed hs q)
  have hqa : Integrable (fun ξ ↦ a (q, ξ)) :=
    (ha.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport hslice
  have hi : Integrable (fun x : Space n ↦ ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ)) :=
    hw.mono' (continuous_positive_fourier_integral hqa).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ hb q hq x)
  exact ⟨hi, integral_mono_ae hi.norm hw (Filter.Eventually.of_forall fun x ↦ hb q hq x)⟩
end
section
-- OAI.Analysis.Fourier.WavePackets.ConvolutionIdentity
open scoped ContDiff RealInnerProductSpace
theorem scaled_wave_integral {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) (X : EuclideanSpace ℝ (Fin n)) :
    (∫ ξ, oscillation (euclideanWavePhase X T) 1 ξ * φ (h • ξ)) =
      semiclassicalWaveKernel volume φ h T X := by
  have hp (ξ : EuclideanSpace ℝ (Fin n)) :
      oscillation (euclideanWavePhase X T) 1 ξ =
        oscillation (euclideanWavePhase X T) h (h • ξ) := by
    unfold oscillation euclideanWavePhase
    congr 2
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    field_simp
  simp_rw [hp]
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun ξ => oscillation (euclideanWavePhase X T) h ξ * φ ξ) h (hR := hh.le)]
  simp only [semiclassicalWaveKernel, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
theorem wave_phase_factorization {n : ℕ} (X Y ξ : EuclideanSpace ℝ (Fin n)) (T : ℝ) :
    Complex.exp (Complex.I * (⟪X, ξ⟫ : ℂ)) *
        (Complex.exp (-Complex.I * ((T * ‖ξ‖ : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * (⟪Y, ξ⟫ : ℂ))) =
      oscillation (euclideanWavePhase (X - Y) T) 1 ξ := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  unfold oscillation euclideanWavePhase
  congr 1
  simp only [inner_sub_left, div_one]
  push_cast
  ring
/-- Frequency localization makes the Fourier/convolution interchange absolutely
integrable for every `L¹` input, not just for Schwartz data. -/
theorem frequencyHalfWave_eq_integral_kernel {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : Continuous φ) (hs : HasCompactSupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Integrable f) (X : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun Y => semiclassicalWaveKernel volume φ h T (X - Y) * f Y) ∧
    frequencyHalfWave φ h T f X =
      (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ *
        ∫ Y, semiclassicalWaveKernel volume φ h T (X - Y) * f Y := by
  let G : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℂ := fun q =>
    oscillation (euclideanWavePhase (X - q.2) T) 1 q.1 * φ (h • q.1) * f q.2
  have hcut : Integrable (fun ξ => φ (h • ξ)) :=
    (hφ.comp (continuous_const.smul continuous_id)).integrable_of_hasCompactSupport
      (hs.comp_smul hh.ne')
  have hosc : Continuous (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      oscillation (euclideanWavePhase (X - q.2) T) 1 q.1) := by
    unfold oscillation euclideanWavePhase
    fun_prop
  have hG : Integrable G (volume.prod volume) := by
    apply (hcut.norm.mul_prod hf.norm).mono
      ((hosc.aestronglyMeasurable.mul hcut.aestronglyMeasurable.comp_fst).mul
        hf.aestronglyMeasurable.comp_snd)
    filter_upwards [] with q
    simp [norm_mul, norm_oscillation]
  have hinner (Y : EuclideanSpace ℝ (Fin n)) :
      (∫ ξ, G (ξ, Y)) = semiclassicalWaveKernel volume φ h T (X - Y) * f Y := by
    dsimp [G]
    rw [integral_mul_const, scaled_wave_integral φ hh]
  refine ⟨?_, ?_⟩
  · simpa only [hinner] using hG.integral_prod_right
  · unfold frequencyHalfWave angularInverse angularFourier
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
    congr 1
    trans ∫ ξ, ∫ Y, G (ξ, Y)
    · apply integral_congr_ae
      filter_upwards [] with ξ
      simp_rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with Y
      dsimp [G]
      rw [← wave_phase_factorization X Y ξ T]
      ring
    · rw [integral_integral_swap hG]
      apply integral_congr_ae
      filter_upwards [] with Y
      exact hinner Y
end
section
-- OAI.Analysis.Fourier.BochnerRiesz.Multiplier
open scoped RealInnerProductSpace ENNReal ContDiff
theorem eLpNorm_normalized_dilate_one {n : ℕ} (K : Space n → ℂ) (hK : Measurable K)
    {h : ℝ} (hh : 0 < h) :
    eLpNorm (fun x ↦ (h ^ n)⁻¹ • K (h⁻¹ • x)) 1 volume = eLpNorm K 1 volume := by
  change eLpNorm ((h ^ n)⁻¹ • (fun x ↦ K (h⁻¹ • x))) 1 volume = _
  rw [eLpNorm_const_smul, eLpNorm_dilate K hK 1 (inv_pos.mpr hh)]
  simp only [ENNReal.toReal_one, div_one, ENNReal.rpow_one, inv_pow, inv_inv]
  rw [Real.enorm_eq_ofReal (inv_nonneg.mpr (pow_nonneg hh.le n)), ← mul_assoc,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hh.le n))]
  simp [hh.ne']
theorem continuous_angularInverse {n : ℕ} {g : Space n → ℂ} (hg : Integrable g) :
    Continuous (angularInverse g) := by
  change Continuous ((((2 * Real.pi) ^ n)⁻¹ : ℝ) •
    (fun x : Space n ↦ ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g ξ))
  exact (continuous_positive_fourier_integral hg).const_smul _
theorem eLpNorm_angularInverse_dilate_one {n : ℕ} {φ : Space n → ℂ}
    (hφ : Integrable φ) {h : ℝ} (hh : 0 < h) :
    eLpNorm (angularInverse (fun ξ ↦ φ (h • ξ))) 1 volume =
      eLpNorm (angularInverse φ) 1 volume := by
  have heq : angularInverse (fun ξ ↦ φ (h • ξ)) =
      fun x ↦ (h ^ n)⁻¹ • angularInverse φ (h⁻¹ • x) :=
    funext (angularInverse_dilate φ hh)
  rw [heq]
  exact eLpNorm_normalized_dilate_one _ (continuous_angularInverse hφ).measurable hh
theorem uniform_angularInverse_L1 {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {n : ℕ} {K : Set Q} {S : Set (Space n)} (hK : IsCompact K) (hS : IsCompact S)
    {a : Q × Space n → ℂ} (ha : ContDiff ℝ ∞ a)
    (hs : tsupport a ⊆ Set.univ ×ˢ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K,
      Integrable (angularInverse (fun ξ ↦ a (q, ξ))) ∧
      eLpNorm (angularInverse (fun ξ ↦ a (q, ξ))) 1 volume ≤ ENNReal.ofReal C := by
  obtain ⟨B, hB, hb⟩ := uniform_fourier_integral_L1 hK hS ha hs
  let κ : ℝ := ((2 * Real.pi) ^ n)⁻¹
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  refine ⟨κ * B, mul_nonneg hκ hB, ?_⟩
  intro q hq
  obtain ⟨hi, hn⟩ := hb q hq
  refine ⟨hi.smul κ, ?_⟩
  change eLpNorm (κ • (fun x : Space n ↦ ∫ ξ,
    Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ))) 1 volume ≤ _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hκ,
    eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hi, ENNReal.ofReal_mul hκ]
  gcongr
end
section
-- OAI.Analysis.Fourier.BochnerRiesz.TimeReversal
open scoped ENNReal ContDiff ComplexConjugate Topology
theorem angularFourier_conj {n : ℕ} (f : Space n → ℂ) (ξ : Space n) :
    angularFourier (fun x ↦ conj (f x)) ξ = conj (angularFourier f (-ξ)) := by
  unfold angularFourier
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [← Complex.exp_conj]
theorem angularInverse_conj {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    angularInverse (fun ξ ↦ conj (g ξ)) x = conj (angularInverse g (-x)) := by
  unfold angularInverse
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  rw [← integral_conj]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp [← Complex.exp_conj]
theorem angularInverse_neg {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    angularInverse (fun ξ ↦ g (-ξ)) x = angularInverse g (-x) := by
  unfold angularInverse
  congr 1
  have h := integral_neg_eq_self (fun ξ : Space n ↦
    Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g (-ξ)) volume
  simpa only [neg_neg, inner_neg_right, inner_neg_left] using h.symm
def schwartzConj {n : ℕ} (f : SchwartzMap (Space n) ℂ) : SchwartzMap (Space n) ℂ :=
  f.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)
end
section
-- OAI.Analysis.Fourier.BochnerRiesz.Projection
open scoped ENNReal ContDiff
theorem integrable_angularInverse_cutoff {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) : Integrable (angularInverse χ) := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  let g : SchwartzMap (Space n) ℂ := schwartzDilate (2 * Real.pi) hp (hc.toSchwartzMap hχ)
  have he : angularInverse χ = (𝓕⁻ g : SchwartzMap (Space n) ℂ) := by
    funext x
    rw [angularInverse_eq_fourierInv_scaled, SchwartzMap.fourierInv_coe]
    rfl
  rw [he]
  exact (𝓕⁻ g : SchwartzMap (Space n) ℂ).integrable
end
section
-- OAI.Analysis.Fourier.BochnerRiesz.MaximalSummation
open scoped ENNReal
theorem eLpNorm_rpow_eq_lintegral {X E : Type*} [MeasurableSpace X]
    [TopologicalSpace E] [ContinuousENorm E] {μ : Measure X} {f : X → E}
    {p : ℝ} (hp : 0 < p) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal p) μ ^ p = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul]
  have h : (1 / p) * p = 1 := by field_simp
  rw [h, ENNReal.rpow_one]
end
section
-- OAI.Analysis.Fourier.WavePackets.Half.Wave.NormalizedKernel
open scoped ContDiff Topology FourierTransform ENNReal RealInnerProductSpace
/-- Exact identification of the kernel with the normalization used in
the actual half-wave convolution formula. -/
theorem normalized_semiclassicalWaveKernel_eq_angularInverse {n : ℕ}
    (φ : Space n → ℂ) {h : ℝ} (hh : 0 < h) (T : ℝ) (x : Space n) :
    (((2*Real.pi : ℝ) : ℂ)^n)⁻¹*semiclassicalWaveKernel volume φ h T x =
      angularInverse (fun ξ => waveAmplitude φ h T (h • ξ)) x := by
  rw [← scaled_wave_integral φ hh T x]
  simp only [angularInverse,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  have hphase : (T/h)*(h*‖ξ‖) = T*‖ξ‖ := by field_simp
  simp only [waveAmplitude,norm_smul,Real.norm_eq_abs,abs_of_pos hh,hphase]
  rw [← mul_assoc,← Complex.exp_add]
  unfold oscillation euclideanWavePhase
  congr 2
  push_cast
  ring
end
section
-- OAI.Analysis.Fourier.WavePackets.Half.Wave.LowFamily
open scoped ContDiff Topology FourierTransform ENNReal
theorem contDiff_exp_dslope : ContDiff ℝ ∞ (dslope Complex.exp 0) := by
  have H : ContDiff ℂ ∞ (dslope Complex.exp 0) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z = 0
    · subst z
      obtain ⟨p,hp⟩ := (analyticAt_cexp : AnalyticAt ℂ Complex.exp 0)
      exact hp.has_fpower_series_dslope_fslope.analyticAt.contDiffAt
    · apply ContDiffAt.congr_of_eventuallyEq _ (dslope_eventuallyEq_slope_of_ne Complex.exp hz)
      change ContDiffAt ℂ ∞ (fun x : ℂ => (x-0)⁻¹ • (Complex.exp x-Complex.exp 0)) z
      simpa only [sub_zero, smul_eq_mul] using!
        (contDiffAt_id.inv hz).smul
          (Complex.contDiff_exp.contDiffAt.sub (contDiffAt_const (c := Complex.exp 0)))
  exact H.restrict_scalars ℝ
/-- The removable exponential quotient, already divided by its small parameter. -/
def lowWaveFamily {n : ℕ} (b χ : Space n → ℂ)
    (p : (ℝ × ℝ) × Space n) : ℂ :=
  b p.2 * χ (p.1.2 • p.2) * (-Complex.I * (p.1.1 * ‖p.2‖ : ℝ)) *
    dslope Complex.exp 0 (-Complex.I * (p.1.1 * p.1.2 * ‖p.2‖ : ℝ))
theorem lowWaveFamily_identity {n : ℕ} (b χ : Space n → ℂ)
    (T r : ℝ) (ξ : Space n) :
    (r : ℂ) * lowWaveFamily b χ ((T,r),ξ) =
      b ξ * χ (r • ξ) * (Complex.exp (-Complex.I * (T*r*‖ξ‖ : ℝ)) - 1) := by
  have h := sub_smul_dslope Complex.exp (0 : ℂ) (-Complex.I * (T*r*‖ξ‖ : ℝ))
  simp only [sub_zero, smul_eq_mul, Complex.exp_zero] at h
  unfold lowWaveFamily
  rw [← h]
  push_cast
  ring
theorem contDiff_lowWaveFamily {n : ℕ} {b χ : Space n → ℂ}
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (hz : 0 ∉ tsupport b) :
    ContDiff ℝ ∞ (lowWaveFamily b χ) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2 = 0
  · have he := (notMem_tsupport_iff_eventuallyEq.mp (hp ▸ hz)).comp_tendsto
      (continuous_snd.continuousAt : ContinuousAt (fun q : (ℝ × ℝ) × Space n => q.2) p)
    apply (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _ : (ℝ × ℝ) × Space n => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [he] with q hq
    change b q.2 = 0 at hq
    simp only [lowWaveFamily,hq,zero_mul]
  · have hnorm := (contDiffAt_snd : ContDiffAt ℝ ∞
        (fun q : (ℝ × ℝ) × Space n => q.2) p).norm ℝ hp
    have hsmall : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ) × Space n =>
        -Complex.I * (q.1.1*q.1.2*‖q.2‖ : ℝ)) p :=
      contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p
        ((contDiffAt_fst.fst.mul contDiffAt_fst.snd).mul hnorm))
    have hlarge : ContDiffAt ℝ ∞ (fun q : (ℝ × ℝ) × Space n =>
        -Complex.I * (q.1.1*‖q.2‖ : ℝ)) p :=
      contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p
        (contDiffAt_fst.fst.mul hnorm))
    exact (((hb.comp contDiff_snd).contDiffAt.mul
      (hχ.comp (contDiff_fst.snd.smul contDiff_snd)).contDiffAt).mul hlarge).mul
      (contDiff_exp_dslope.contDiffAt.comp p hsmall)
theorem lowWaveFamily_support {n : ℕ} (b χ : Space n → ℂ) :
    tsupport (lowWaveFamily b χ) ⊆ univ ×ˢ tsupport b := by
  intro p hp
  have hsub : tsupport (lowWaveFamily b χ) ⊆ tsupport (fun q : (ℝ × ℝ) × Space n => b q.2) := by
    unfold lowWaveFamily
    exact tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans tsupport_mul_subset_left)
  exact ⟨mem_univ _,tsupport_comp_subset_preimage b continuous_snd (hsub hp)⟩
end
section
-- OAI.Analysis.Fourier.WavePackets.Half.Wave.LowAnnulus
open scoped ContDiff Topology FourierTransform ENNReal
def lowWaveAnnulus {n : ℕ} (b χ : Space n → ℂ) (r T : ℝ) (ξ : Space n) : ℂ :=
  b (r⁻¹ • ξ) * χ ξ * (Complex.exp (-Complex.I * (T*‖ξ‖ : ℝ)) - 1)
theorem lowWaveAnnulus_eq_dilate {n : ℕ} (b χ : Space n → ℂ)
    {r : ℝ} (hr : 0 < r) (T : ℝ) :
    lowWaveAnnulus b χ r T = fun ξ => r • lowWaveFamily b χ ((T,r),r⁻¹ • ξ) := by
  funext ξ
  rw [Complex.real_smul,lowWaveFamily_identity]
  simp only [smul_inv_smul₀ hr.ne',norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr),lowWaveAnnulus]
  congr 3
  field_simp
/-- The small-frequency phase remainder gains one complete dyadic scale. -/
theorem uniform_lowWaveAnnulus_kernel {n : ℕ} {b χ : Space n → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) (hz : 0 ∉ tsupport b)
    (hχ : ContDiff ℝ ∞ χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ T ∈ Icc (1 : ℝ) 2,
      eLpNorm (angularInverse (lowWaveAnnulus b χ r T)) 1 volume ≤ ENNReal.ofReal (r*C) := by
  obtain ⟨C,hC,hbound⟩ := uniform_angularInverse_L1
    (isCompact_Icc.prod isCompact_Icc) hc (contDiff_lowWaveFamily hb hχ hz)
    (lowWaveFamily_support b χ)
  refine ⟨C,hC,?_⟩
  intro r hr hr1 T hT
  have hi : Integrable (fun ξ => lowWaveFamily b χ ((T,r),ξ)) := by
    apply ((contDiff_lowWaveFamily hb hχ hz).continuous.comp
      (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    intro ξ hξ
    exact ((lowWaveFamily_support b χ) (tsupport_comp_subset_preimage _
      (continuous_const.prodMk continuous_id) hξ)).2
  have he : angularInverse (lowWaveAnnulus b χ r T) = fun x =>
      r • angularInverse (fun ξ => lowWaveFamily b χ ((T,r),r⁻¹ • ξ)) x := by
    rw [lowWaveAnnulus_eq_dilate b χ hr T]
    exact funext (angularInverse_smul_real r _)
  rw [he]
  change eLpNorm (r • (angularInverse (fun ξ => lowWaveFamily b χ ((T,r),r⁻¹ • ξ))))
    1 volume ≤ _
  rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hr.le,
    eLpNorm_angularInverse_dilate_one hi (inv_pos.mpr hr),
    ENNReal.ofReal_mul hr.le]
  exact mul_le_mul' le_rfl (hbound (T,r) ⟨hT,hr.le,hr1⟩).2
end
section
-- OAI.Analysis.Fourier.WavePackets.Half.Wave.LowPartition
open scoped ContDiff Topology FourierTransform ENNReal
def inwardAnnulus {n : ℕ} (ξ : Space n) : ℂ := smoothingAnnularCutoff ((2:ℝ) • ξ)
theorem inwardAnnulus_eq {n : ℕ} (ξ : Space n) :
    inwardAnnulus ξ = smoothingLowCutoff ξ-smoothingLowCutoff ((2:ℝ) • ξ) := by
  simp [inwardAnnulus,smoothingAnnularCutoff,smul_smul]
theorem contDiff_inwardAnnulus (n : ℕ) : ContDiff ℝ ∞ (@inwardAnnulus n) :=
  (contDiff_smoothingAnnularCutoff n).comp (contDiff_id.const_smul _)
theorem hasCompactSupport_inwardAnnulus (n : ℕ) : HasCompactSupport (@inwardAnnulus n) :=
  (hasCompactSupport_smoothingAnnularCutoff n).comp_smul (by norm_num)
theorem zero_notMem_tsupport_inwardAnnulus (n : ℕ) :
    (0 : Space n) ∉ tsupport inwardAnnulus := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [Metric.ball_mem_nhds (0 : Space n) (by norm_num : (0:ℝ)<1/2)] with ξ hξ
  have hn : ‖ξ‖ < 1/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hξ
  change smoothingAnnularCutoff ((2:ℝ) • ξ) = 0
  apply smoothingAnnularCutoff_eq_zero
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith
def lowRemainder {n : ℕ} (χ : Space n → ℂ) (T : ℝ) (ξ : Space n) : ℂ :=
  χ ξ * (Complex.exp (-Complex.I * (T*‖ξ‖ : ℝ))-1) * smoothingLowCutoff ξ
theorem lowWaveAnnulus_sum {n : ℕ} (χ : Space n → ℂ) (T : ℝ) (N : ℕ) (ξ : Space n) :
    ∑ k ∈ Finset.range N, lowWaveAnnulus inwardAnnulus χ (smoothingDyadicScale k) T ξ =
      χ ξ * (Complex.exp (-Complex.I * (T*‖ξ‖ : ℝ))-1) *
        (smoothingLowCutoff ξ-smoothingLowCutoff ((2:ℝ)^N • ξ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ,ih]
      simp only [lowWaveAnnulus,inwardAnnulus_eq,smoothingDyadicScale,inv_pow,inv_inv,
        smul_smul,pow_succ]
      ring_nf
theorem eventually_smoothingLowCutoff_inward_zero {n : ℕ} {ξ : Space n} (hξ : ξ ≠ 0) :
    ∀ᶠ N : ℕ in atTop, smoothingLowCutoff ((2:ℝ)^N • ξ) = 0 := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hg : Tendsto (fun N : ℕ => (2:ℝ)^N*‖ξ‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const hn
  filter_upwards [hg.eventually (eventually_ge_atTop (16:ℝ))] with N hN
  unfold smoothingLowCutoff
  rw [(smoothingLowBump n).zero_of_le_dist]
  · simp
  · simpa only [smoothingLowBump,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) N)] using hN
theorem tendsto_lowWaveAnnulus_sum {n : ℕ} (χ : Space n → ℂ) (T : ℝ) (ξ : Space n) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
      lowWaveAnnulus inwardAnnulus χ (smoothingDyadicScale k) T ξ)
      atTop (𝓝 (lowRemainder χ T ξ)) := by
  simp only [lowWaveAnnulus_sum]
  by_cases hξ : ξ = 0
  · subst ξ
    simp [lowRemainder]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_smoothingLowCutoff_inward_zero hξ] with N hN
    simp only [lowRemainder,hN,sub_zero]
theorem norm_lowWaveAnnulus_sum_le {n : ℕ} (χ : Space n → ℂ) (T : ℝ) (N : ℕ) (ξ : Space n) :
    ‖∑ k ∈ Finset.range N,lowWaveAnnulus inwardAnnulus χ (smoothingDyadicScale k) T ξ‖ ≤
      4*‖χ ξ‖ := by
  rw [lowWaveAnnulus_sum,norm_mul,norm_mul]
  have he : ‖Complex.exp (-Complex.I * (T*‖ξ‖ : ℝ))-1‖ ≤ 2 := by
    have H := norm_sub_le (Complex.exp (-Complex.I * (T*‖ξ‖ : ℝ))) (1:ℂ)
    norm_num [Complex.norm_exp] at H
    simpa only [Complex.ofReal_mul,neg_mul] using H
  have hl : ‖smoothingLowCutoff ξ-smoothingLowCutoff ((2:ℝ)^N • ξ)‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [norm_smoothingLowCutoff_le_one ξ,
      norm_smoothingLowCutoff_le_one ((2:ℝ)^N • ξ)])
  calc
    _ ≤ (‖χ ξ‖*2)*2 := mul_le_mul
      (mul_le_mul_of_nonneg_left he (norm_nonneg _)) hl (norm_nonneg _) (by positivity)
    _ = _ := by ring
end
section
-- OAI.Analysis.Fourier.WavePackets.Half.Wave.LowSummation
open scoped ContDiff Topology FourierTransform ENNReal
theorem continuous_lowWaveAnnulus {n : ℕ} {b χ : Space n → ℂ}
    (hb : Continuous b) (hχ : Continuous χ) (r T : ℝ) :
    Continuous (lowWaveAnnulus b χ r T) := by
  unfold lowWaveAnnulus
  fun_prop
theorem integrable_lowWaveAnnulus {n : ℕ} {b χ : Space n → ℂ}
    (hb : Continuous b) (hχ : Continuous χ) (hc : HasCompactSupport χ) (r T : ℝ) :
    Integrable (lowWaveAnnulus b χ r T) := by
  apply (continuous_lowWaveAnnulus hb hχ r T).integrable_of_hasCompactSupport
  exact (hc.mul_left).mul_right
theorem angularInverse_finset_sum {n : ℕ} {I : Type*} (s : Finset I)
    (f : I → Space n → ℂ) (hf : ∀ i ∈ s, Integrable (f i)) :
    angularInverse (fun ξ => ∑ i ∈ s,f i ξ) = fun x => ∑ i ∈ s, angularInverse (f i) x := by
  funext x
  simp only [angularInverse,Finset.mul_sum,integral_finsetSum s
    (fun i hi => integrable_angularKernel_mul (hf i hi) x),Finset.smul_sum]
theorem integrable_lowRemainder {n : ℕ} {χ : Space n → ℂ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (T : ℝ) :
    Integrable (lowRemainder χ T) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold lowRemainder
    have := (contDiff_smoothingLowCutoff n).continuous
    fun_prop
  · exact hc.mul_right.mul_right
theorem tendsto_angularInverse_low_sum {n : ℕ} {χ : Space n → ℂ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (T : ℝ) (x : Space n) :
    Tendsto (fun N : ℕ => angularInverse (fun ξ => ∑ k ∈ Finset.range N,
      lowWaveAnnulus inwardAnnulus χ (smoothingDyadicScale k) T ξ) x)
      atTop (𝓝 (angularInverse (lowRemainder χ T) x)) := by
  unfold angularInverse
  apply Tendsto.const_smul
  apply tendsto_integral_of_dominated_convergence (fun ξ => 4*‖χ ξ‖)
  · intro N
    apply (integrable_angularKernel_mul _ x).aestronglyMeasurable
    exact integrable_finsetSum _ (fun k _ => integrable_lowWaveAnnulus
      (contDiff_inwardAnnulus n).continuous hχ hc _ T)
  · exact (hχ.integrable_of_hasCompactSupport hc).norm.const_mul 4
  · intro N
    filter_upwards [] with ξ
    simpa [norm_mul,Complex.norm_exp] using norm_lowWaveAnnulus_sum_le χ T N ξ
  · filter_upwards [] with ξ
    exact tendsto_const_nhds.mul (tendsto_lowWaveAnnulus_sum χ T ξ)
/-- The singularity at zero is removed by a geometrically summable
dyadic gain, not by assuming that the wave symbol is smooth there. -/
theorem uniform_lowRemainder_kernel {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T ∈ Icc (1:ℝ) 2,
      eLpNorm (angularInverse (lowRemainder χ T)) 1 volume ≤ ENNReal.ofReal C := by
  obtain ⟨C,hC,hbound⟩ := uniform_lowWaveAnnulus_kernel
    (contDiff_inwardAnnulus n) (hasCompactSupport_inwardAnnulus n)
    (zero_notMem_tsupport_inwardAnnulus n) hχ
  refine ⟨2*C,mul_nonneg (by norm_num) hC,?_⟩
  intro T hT
  let f : ℕ → Space n → ℂ := fun k => lowWaveAnnulus inwardAnnulus χ (smoothingDyadicScale k) T
  have hi (k : ℕ) : Integrable (f k) := integrable_lowWaveAnnulus
    (contDiff_inwardAnnulus n).continuous hχ.continuous hc _ T
  have hsum (N : ℕ) : (∑ k ∈ Finset.range N,smoothingDyadicScale k) ≤ 2 := by
    have ht : (∑ k ∈ Finset.range N,smoothingDyadicScale k) = 2*(1-smoothingDyadicScale N) := by
      induction N with
      | zero => simp [smoothingDyadicScale]
      | succ N ih => rw [Finset.sum_range_succ,ih,smoothingDyadicScale_succ]; ring
    rw [ht]
    linarith [smoothingDyadicScale_pos N]
  have hpartial (N : ℕ) :
      eLpNorm (angularInverse (fun ξ => ∑ k ∈ Finset.range N,f k ξ)) 1 volume ≤
        ENNReal.ofReal (2*C) := by
    rw [angularInverse_finset_sum _ f (fun k _ => hi k)]
    calc
      _ ≤ ∑ k ∈ Finset.range N,eLpNorm (angularInverse (f k)) 1 volume := by
        simpa only [Finset.sum_fn] using
          (eLpNorm_sum_le (s := Finset.range N) (f := fun k => angularInverse (f k)) (fun k _ => (continuous_angularInverse (hi k)).aestronglyMeasurable) le_rfl)
      _ ≤ ∑ k ∈ Finset.range N,ENNReal.ofReal (smoothingDyadicScale k*C) :=
        Finset.sum_le_sum (fun k _ => hbound _ (smoothingDyadicScale_pos k)
          (smoothingDyadicScale_le_one k) T hT)
      _ = ENNReal.ofReal ((∑ k ∈ Finset.range N,smoothingDyadicScale k)*C) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ =>
          mul_nonneg (smoothingDyadicScale_pos k).le hC),Finset.sum_mul]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hsum N) hC)
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall hpartial)
  · intro N
    exact (continuous_angularInverse
      (integrable_finsetSum _ (fun k _ => hi k))).aestronglyMeasurable
  · exact Eventually.of_forall (tendsto_angularInverse_low_sum hχ.continuous hc T)
end
section
-- OAI.Analysis.Fourier.WavePackets.Half.Wave.LowKernel
open scoped ContDiff Topology FourierTransform ENNReal
theorem angularInverse_add_integrable {n : ℕ} {f g : Space n → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    angularInverse (f+g) = angularInverse f+angularInverse g := by
  funext x
  simp only [angularInverse,mul_add,integral_add (integrable_angularKernel_mul hf x)
    (integrable_angularKernel_mul hg x),smul_add,Pi.add_apply]
def lowCore {n : ℕ} (χ : Space n → ℂ) (ξ : Space n) := χ ξ*smoothingLowCutoff ξ
def highCore {n : ℕ} (χ : Space n → ℂ) (ξ : Space n) := χ ξ*(1-smoothingLowCutoff ξ)
theorem lowCore_smooth {n : ℕ} {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (lowCore χ) := hχ.mul (contDiff_smoothingLowCutoff _)
theorem highCore_smooth {n : ℕ} {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (highCore χ) := hχ.mul (contDiff_const.sub (contDiff_smoothingLowCutoff _))
theorem lowCore_compact {n : ℕ} {χ : Space n → ℂ} (hc : HasCompactSupport χ) :
    HasCompactSupport (lowCore χ) := hc.mul_right
theorem highCore_compact {n : ℕ} {χ : Space n → ℂ} (hc : HasCompactSupport χ) :
    HasCompactSupport (highCore χ) := hc.mul_right
theorem highCore_away {n : ℕ} (χ : Space n → ℂ) : (0 : Space n) ∉ tsupport (highCore χ) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [Metric.ball_mem_nhds (0 : Space n) (by norm_num : (0:ℝ)<1)] with ξ hξ
  have hnorm : ‖ξ‖ ≤ 1 := (by simpa only [Metric.mem_ball,dist_zero_right] using hξ : ‖ξ‖<1).le
  simp only [highCore,smoothingLowCutoff_eq_one hnorm,sub_self,mul_zero,Pi.zero_apply]
theorem waveAmplitude_low_decomposition {n : ℕ} (χ : Space n → ℂ) (T : ℝ) :
    waveAmplitude χ 1 T = (lowCore χ+lowRemainder χ T)+waveAmplitude (highCore χ) 1 T := by
  funext ξ
  simp only [lowCore,highCore,lowRemainder,waveAmplitude,div_one,Pi.add_apply]
  ring
theorem inverse_kernel_triple_bound {n : ℕ} {f g h : Space n → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h) {A B D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hfa : eLpNorm (angularInverse f) 1 volume ≤ .ofReal A)
    (hgb : eLpNorm (angularInverse g) 1 volume ≤ .ofReal B)
    (hhd : eLpNorm (angularInverse h) 1 volume ≤ .ofReal D) :
    eLpNorm (angularInverse ((f+g)+h)) 1 volume ≤ .ofReal (A+B+D) := by
  rw [angularInverse_add_integrable (hf.add hg) hh,angularInverse_add_integrable hf hg]
  have F := (continuous_angularInverse hf).aestronglyMeasurable (μ := volume)
  have G := (continuous_angularInverse hg).aestronglyMeasurable (μ := volume)
  have H := (continuous_angularInverse hh).aestronglyMeasurable (μ := volume)
  exact ((eLpNorm_add_le (F.add G) H le_rfl).trans (add_le_add (eLpNorm_add_le F G le_rfl) le_rfl)).trans
    ((add_le_add (add_le_add hfa hgb) hhd).trans_eq (by
      rw [ENNReal.ofReal_add (add_nonneg hA hB) hD,ENNReal.ofReal_add hA hB]))
theorem fixed_smooth_kernel_bound {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ A : ℝ, 0 ≤ A ∧ eLpNorm (angularInverse χ) 1 volume ≤ .ofReal A := by
  have ht := (memLp_one_iff_integrable.mpr
    (integrable_angularInverse_cutoff hχ hc)).eLpNorm_ne_top
  exact ⟨_,ENNReal.toReal_nonneg,le_of_eq (ENNReal.ofReal_toReal ht).symm⟩
end
section
-- OAI.Analysis.Fourier.LocalSmoothing.TimeReversal
open scoped ENNReal ComplexConjugate ContDiff Topology
theorem angular_real_even_multiplier_conj {n : ℕ}
    (m : Space n → ℝ) (hm : ∀ ξ, m (-ξ) = m ξ) (f : Space n → ℂ) (x : Space n) :
    angularInverse (fun ξ => m ξ • angularFourier (fun y => conj (f y)) ξ) x =
      conj (angularInverse (fun ξ => m ξ • angularFourier f ξ) x) := by
  let g : Space n → ℂ := fun ξ => m ξ • angularFourier f ξ
  have he : (fun ξ => m ξ • angularFourier (fun y => conj (f y)) ξ) =
      (fun ξ => conj (g (-ξ))) := by
    funext ξ
    rw [angularFourier_conj]
    simp only [g, hm, Complex.real_smul, map_mul, Complex.conj_ofReal]
  rw [he, angularInverse_conj, angularInverse_neg, neg_neg]
theorem besselPotential_conj {n : ℕ} (s : ℝ) (f : Space n → ℂ) (x : Space n) :
    besselPotential s (fun y => conj (f y)) x = conj (besselPotential s f x) := by
  apply angular_real_even_multiplier_conj
  intro ξ
  simp only [norm_neg]
theorem eLpNorm_besselPotential_schwartzConj {n : ℕ}
    (s : ℝ) (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    eLpNorm (besselPotential s (schwartzConj f)) p volume =
      eLpNorm (besselPotential s f) p volume := by
  have he : besselPotential s (schwartzConj f) =
      (fun x => conj (besselPotential s f x)) := funext (besselPotential_conj s f)
  rw [he]
  exact eLpNorm_conj (besselPotential s f) p volume
theorem frequencyHalfWave_conj {n : ℕ} (φ f : Space n → ℂ) (h t : ℝ) (x : Space n) :
    frequencyHalfWave (fun ξ => conj (φ (-ξ))) h t (fun y => conj (f y)) x =
      conj (frequencyHalfWave φ h (-t) f x) := by
  let g : Space n → ℂ := fun ξ => Complex.exp (-Complex.I * ((-t) * ‖ξ‖ : ℝ)) *
    φ (h • ξ) * angularFourier f ξ
  have he : (fun ξ => Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
      conj (φ (-(h • ξ))) * angularFourier (fun y => conj (f y)) ξ) =
      (fun ξ => conj (g (-ξ))) := by
    funext ξ
    rw [angularFourier_conj]
    simp [g, ← Complex.exp_conj, smul_neg]
  rw [frequencyHalfWave, he, angularInverse_conj,
    angularInverse_neg, neg_neg]
  rfl
theorem eLpNorm_frequencyHalfWave_schwartzConj {n : ℕ} (φ : Space n → ℂ)
    (h : ℝ) (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun z : Space n × ℝ => frequencyHalfWave (fun ξ => conj (φ (-ξ)))
      h z.2 (schwartzConj f) z.1) p (observationMeasure n) =
    eLpNorm (fun z : Space n × ℝ => frequencyHalfWave φ h (-z.2) f z.1)
      p (observationMeasure n) := by
  have he : (fun z : Space n × ℝ => frequencyHalfWave (fun ξ => conj (φ (-ξ)))
      h z.2 (schwartzConj f) z.1) =
      (fun z => conj (frequencyHalfWave φ h (-z.2) f z.1)) := by
    funext z
    exact frequencyHalfWave_conj φ f h z.2 z.1
  rw [he]
  exact eLpNorm_conj (fun z : Space n × ℝ => frequencyHalfWave φ h (-z.2) f z.1)
    p (observationMeasure n)
end
section
-- OAI.Analysis.Fourier.WavePackets.Assembly
open scoped ENNReal ContDiff
theorem measurable_frequencyHalfWave_spacetime {n : ℕ}
    {φ f : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : Continuous φ)
    (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h) (hm : Measurable f) (hf : Integrable f) :
    Measurable (fun q : ℝ × EuclideanSpace ℝ (Fin n) => frequencyHalfWave φ h q.1 f q.2) := by
  have he : (fun q : ℝ × EuclideanSpace ℝ (Fin n) => frequencyHalfWave φ h q.1 f q.2) =
      (fun q => (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ *
        ∫ Y, semiclassicalWaveKernel volume φ h q.1 (q.2 - Y) * f Y) := by
    funext q
    exact (frequencyHalfWave_eq_integral_kernel hφ hs hh q.1 hf q.2).2
  rw [he]
  apply measurable_const.mul
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right' (f := fun q :
    (ℝ × EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) =>
      semiclassicalWaveKernel volume φ h q.1.1 (q.1.2 - q.2) * f q.2)
  apply Measurable.stronglyMeasurable
  exact ((continuous_semiclassicalWaveKernel_spacetime hφ hs h).measurable.comp
    ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).sub measurable_snd))).mul
    (hm.comp measurable_snd)
end
section
-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Wave
open scoped ENNReal ContDiff
def waveKernel {n : ℕ} (φ : Space n → ℂ) (h t : ℝ) (x : Space n) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ * semiclassicalWaveKernel volume φ h t x
theorem continuous_waveKernel {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) (h t : ℝ) :
    Continuous (waveKernel φ h t) := by
  have hc : Continuous (fun z : ℝ × Space n => semiclassicalWaveKernel volume φ h z.1 z.2) :=
    continuous_semiclassicalWaveKernel_spacetime (E := Space n) (μ := volume) hφ hs h
  have ht : Continuous (fun x : Space n => (t,x)) := continuous_const.prodMk continuous_id
  simpa only [waveKernel, Function.comp_def] using!
    (hc.comp ht).const_mul ((((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹)
theorem frequencyHalfWave_eq_convolveKernel {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (t : ℝ) {f : Space n → ℂ} (hf : Integrable f) :
    frequencyHalfWave φ h t f = convolveKernel (waveKernel φ h t) f := by
  funext x
  rw [(frequencyHalfWave_eq_integral_kernel hφ hs hh t hf x).2]
  unfold convolveKernel waveKernel
  simp_rw [smul_eq_mul, ← mul_assoc, mul_comm (f _) (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹,
    mul_assoc, mul_comm (f _) (semiclassicalWaveKernel _ _ _ _ _)]
  rw [integral_const_mul]
theorem measurable_frequencyWave {n : ℕ} {φ f : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (hf : Measurable f) (hi : Integrable f) :
    Measurable (fun z : Space n × ℝ => frequencyHalfWave φ h z.2 f z.1) := by
  have H : Measurable (fun z : ℝ × Space n => frequencyHalfWave φ h z.1 f z.2) :=
    measurable_frequencyHalfWave_spacetime (n := n) hφ hs hh hf hi
  simpa only [Function.comp_def, Prod.swap] using
    H.comp (show Measurable (Prod.swap : Space n × ℝ → ℝ × Space n) from measurable_swap)
theorem frequencyWave_slice_young {n : ℕ} {φ f : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (hf : Measurable f) (hi : Integrable f) (t : ℝ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (frequencyHalfWave φ h t f) p volume ≤
      eLpNorm (waveKernel φ h t) 1 volume * eLpNorm f p volume := by
  rw [frequencyHalfWave_eq_convolveKernel hφ hs hh t hi]
  exact eLpNorm_convolveKernel_le (continuous_waveKernel hφ hs h t) hf hp hpt
end
section
-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Product
open scoped ENNReal
theorem observation_norm_le_of_slices {n : ℕ} {u : Space n × ℝ → ℂ}
    (hu : Measurable u) {p : ℝ} (hp : 0 < p) {A : ℝ≥0∞}
    (hbound : ∀ t ∈ Icc (1 : ℝ) 2, eLpNorm (fun x => u (x,t)) (.ofReal p) volume ≤ A) :
    eLpNorm u (.ofReal p) (observationMeasure n) ≤ A := by
  have H : (∫⁻ z, ‖u z‖ₑ ^ p ∂observationMeasure n) ≤ A ^ p := by
    rw [observationMeasure, lintegral_prod_symm' _ (hu.enorm.pow_const p)]
    calc
      _ ≤ ∫⁻ t in Icc (1 : ℝ) 2, A ^ p := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have h := ENNReal.rpow_le_rpow (hbound t ht) hp.le
        have hm : Measurable (fun x : Space n => u (x,t)) :=
          hu.comp (measurable_id.prodMk measurable_const)
        rwa [eLpNorm_rpow_eq_lintegral hp hm.aestronglyMeasurable] at h
      _ = _ := by norm_num [Real.volume_Icc]
  have H' := ENNReal.rpow_le_rpow H (show 0 ≤ 1 / p by positivity)
  simpa only [← eLpNorm_rpow_eq_lintegral hp hu.aestronglyMeasurable,
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one] using H'
end
section
-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Young
open scoped ENNReal ContDiff
theorem frequencyWave_spacetime_young {n : ℕ} {φ f : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (hf : Measurable f) (hi : Integrable f) {p : ℝ} (hp : 1 ≤ p) {A : ℝ≥0∞}
    (hK : ∀ t ∈ Icc (1 : ℝ) 2, eLpNorm (waveKernel φ h t) 1 volume ≤ A) :
    eLpNorm (fun z : Space n × ℝ => frequencyHalfWave φ h z.2 f z.1)
      (.ofReal p) (observationMeasure n) ≤ A * eLpNorm f (.ofReal p) volume := by
  apply observation_norm_le_of_slices (measurable_frequencyWave hφ hs hh hf hi) (by linarith)
  intro t ht
  exact (frequencyWave_slice_young hφ hs hh hf hi t (by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    ENNReal.ofReal_ne_top).trans (mul_le_mul' (hK t ht) le_rfl)
end
section
-- OAI.Analysis.Fourier.BesselPotential.SchwartzMultiplier
open scoped ContDiff ENNReal
theorem angularFourier_angularSchwartzMultiplier {n : ℕ} {m : Space n → ℝ}
    (hm : m.HasTemperateGrowth) (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    angularFourier (angularSchwartzMultiplier m f) ξ = m ξ • angularFourier f ξ := by
  have hp : (2*Real.pi : ℝ) ≠ 0 := by positivity
  have he : (2*Real.pi) • ((2*Real.pi)⁻¹ • ξ) = ξ := by
    rw [smul_smul,mul_inv_cancel₀ hp,one_smul]
  conv_lhs => rw [← he]
  rw [angularFourier_scaled]
  change (𝓕 (angularSchwartzMultiplier m f) : SchwartzMap (Space n) ℂ)
    ((2*Real.pi)⁻¹ • ξ) = _
  rw [angularSchwartzMultiplier,SchwartzMap.fourierMultiplierCLM_apply,
    FourierTransform.fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply (angularSchwartzMultiplier_temperate hm),he]
  congr 1
  rw [SchwartzMap.fourier_coe,← angularFourier_scaled,he]
end
section
-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.LocalSmoothingLowFrequencyCore
open scoped ENNReal ContDiff
def unweightedCutoff {n : ℕ} (χ : Space n → ℂ) (m : Space n → ℝ) (ξ : Space n) : ℂ :=
  (m ξ)⁻¹ • χ ξ
theorem contDiff_unweightedCutoff {n : ℕ} {χ : Space n → ℂ} {m : Space n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hm : m.HasTemperateGrowth) (hne : ∀ ξ, m ξ ≠ 0) :
    ContDiff ℝ ∞ (unweightedCutoff χ m) := by
  exact (hm.1.inv hne).smul hχ
theorem hasCompactSupport_unweightedCutoff {n : ℕ} {χ : Space n → ℂ} (m : Space n → ℝ)
    (hχ : HasCompactSupport χ) : HasCompactSupport (unweightedCutoff χ m) := by
  simpa only [unweightedCutoff, Pi.smul_apply] using!
    (hχ.smul_left (f := fun ξ : Space n => (m ξ)⁻¹))
theorem frequencyHalfWave_unweight {n : ℕ} (χ : Space n → ℂ) {m : Space n → ℝ}
    (hm : m.HasTemperateGrowth) (hne : ∀ ξ, m ξ ≠ 0)
    (f : SchwartzMap (Space n) ℂ) (t : ℝ) :
    frequencyHalfWave (unweightedCutoff χ m) 1 t (angularSchwartzMultiplier m f) =
      frequencyHalfWave χ 1 t f := by
  unfold frequencyHalfWave
  congr 1
  funext ξ
  rw [angularFourier_angularSchwartzMultiplier hm]
  simp only [one_smul, unweightedCutoff, Complex.real_smul, Complex.ofReal_inv]
  have hc : (m ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hne ξ)
  field_simp
end
section
-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.LocalSmoothingLowFrequencyWeights
open scoped ENNReal ContDiff
theorem fixedFrequency_weighted_bound_of_kernel {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {m : Space n → ℝ} (hm : m.HasTemperateGrowth) (hne : ∀ ξ, m ξ ≠ 0)
    (hkernel : ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (1 : ℝ) 2,
      eLpNorm (waveKernel (unweightedCutoff χ m) 1 t) 1 volume ≤ .ofReal C) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => frequencyHalfWave χ 1 z.2 f z.1)
        (.ofReal p) (observationMeasure n) ≤ .ofReal C *
          eLpNorm (angularSchwartzMultiplier m f) (.ofReal p) volume := by
  have hd := contDiff_unweightedCutoff hχ hm hne
  have hs := hasCompactSupport_unweightedCutoff m hc
  obtain ⟨C,hC,hkernel⟩ := hkernel
  refine ⟨C,hC,?_⟩
  intro f
  have H := frequencyWave_spacetime_young hd.continuous hs (by norm_num : (0:ℝ)<1)
    (angularSchwartzMultiplier m f).continuous.measurable
    (angularSchwartzMultiplier m f).integrable hp hkernel
  simpa only [frequencyHalfWave_unweight χ hm hne f] using H
theorem lowFrequency_bessel_bound_of_kernel {n : ℕ} {p : ℝ} (hp : 1 ≤ p) (σ : ℝ)
    (hkernel : ∀ χ : Space n → ℂ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (1 : ℝ) 2,
        eLpNorm (waveKernel χ 1 t) 1 volume ≤ .ofReal C) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => frequencyHalfWave smoothingLowCutoff 1 z.2 f z.1)
        (.ofReal p) (observationMeasure n) ≤
      .ofReal C * eLpNorm (besselPotential σ f) (.ofReal p) volume := by
  have hm := Function.hasTemperateGrowth_one_add_norm_sq_rpow (Space n) (σ/2)
  have hne (ξ : Space n) : (1+‖ξ‖^2)^(σ/2) ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hχ := contDiff_smoothingLowCutoff n
  have hc := hasCompactSupport_smoothingLowCutoff n
  obtain ⟨C,hC,hb⟩ := fixedFrequency_weighted_bound_of_kernel hp hχ hc hm hne
    (hkernel _ (contDiff_unweightedCutoff hχ hm hne) (hasCompactSupport_unweightedCutoff _ hc))
  refine ⟨C,hC,?_⟩
  intro f
  have H := hb f
  change _ ≤ .ofReal C * eLpNorm (besselPotentialSchwartz σ f) (.ofReal p) volume at H
  simpa only [besselPotentialSchwartz_eq] using H
end
end LSLeaf.LowPart
noncomputable section
namespace LSLeaf.LowPart
open OMA.S_wpc_local_smoothing_conjecture MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology ComplexConjugate

theorem fixedAway {n : ℕ} {b : Space n → ℂ} (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport b) (hz : 0 ∉ tsupport b) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc (1:ℝ) 2,
      eLpNorm (angularInverse (waveAmplitude b 1 t)) 1 volume ≤ .ofReal D := by
  let a := fun q : ℝ × Space n => Complex.exp (-Complex.I * (q.1 * ‖q.2‖ : ℝ)) * b q.2
  have ha : ContDiff ℝ ∞ a := by
    rw [contDiff_iff_contDiffAt]; intro p
    by_cases hp : p.2 = 0
    · have he := (notMem_tsupport_iff_eventuallyEq.mp (hp ▸ hz)).comp_tendsto
        (continuous_snd.continuousAt : ContinuousAt (fun q : ℝ × Space n => q.2) p)
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ × Space n => (0 : ℂ)) p).congr_of_eventuallyEq
      filter_upwards [he] with q hq
      change b q.2 = 0 at hq
      simp only [a,hq,mul_zero]
    · have H := (contDiffAt_snd : ContDiffAt ℝ ∞ (fun q : ℝ × Space n => q.2) p).norm ℝ hp
      exact (Complex.contDiff_exp.contDiffAt.comp p (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiffAt_fst.mul H)))).mul (hb.comp contDiff_snd).contDiffAt
  have hs : tsupport a ⊆ univ ×ˢ tsupport b := by
    intro q hq
    exact ⟨mem_univ _, tsupport_comp_subset_preimage b continuous_snd ((tsupport_mul_subset_right : tsupport a ⊆ tsupport (fun q : ℝ × Space n => b q.2)) hq)⟩
  obtain ⟨D,hD,hd⟩ := uniform_angularInverse_L1 (K := Icc (1:ℝ) 2) isCompact_Icc hc ha hs
  refine ⟨D,hD,fun t ht => ?_⟩
  have he : waveAmplitude b 1 t = fun ξ => a (t,ξ) := by funext ξ; simp only [waveAmplitude,div_one,a]
  rw [he]; exact (hd t ht).2

theorem fixedKernelLow {n : ℕ} (χ : Space n → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (1:ℝ) 2, eLpNorm (waveKernel χ 1 t) 1 volume ≤ .ofReal C := by
  obtain ⟨A,hA,ha⟩ := fixed_smooth_kernel_bound (lowCore_smooth hχ) (lowCore_compact hc)
  obtain ⟨B,hB,hb⟩ := uniform_lowRemainder_kernel hχ hc
  obtain ⟨D,hD,hd⟩ := fixedAway (highCore_smooth hχ) (highCore_compact hc) (highCore_away χ)
  refine ⟨A+B+D+1,by linarith,fun t ht => ?_⟩
  have he : waveKernel χ 1 t = angularInverse (waveAmplitude χ 1 t) := by
    funext x
    simpa only [waveKernel, one_smul] using normalized_semiclassicalWaveKernel_eq_angularInverse χ (by norm_num : (0:ℝ)<1) t x
  rw [he,waveAmplitude_low_decomposition]
  apply le_trans _ (ENNReal.ofReal_le_ofReal (show A+B+D ≤ A+B+D+1 by linarith))
  apply inverse_kernel_triple_bound ((lowCore_smooth hχ).continuous.integrable_of_hasCompactSupport (lowCore_compact hc)) (integrable_lowRemainder hχ.continuous hc t) _ hA hB hD ha (hb t ht) (hd t ht)
  apply Continuous.integrable_of_hasCompactSupport
  · unfold waveAmplitude
    have H := (highCore_smooth hχ).continuous
    fun_prop
  · exact (highCore_compact hc).mul_left

theorem low_proof : Low := by
  intro n hn p α hp _
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n:ℝ)-1 := by linarith
  have hc' := (div_le_iff₀ hd).mp hp
  have hp1 : 1 ≤ p := by by_contra! h; nlinarith [mul_lt_mul_of_pos_right h hd]
  obtain ⟨C,hC,h⟩ := lowFrequency_bessel_bound_of_kernel (n:=n) hp1 α fixedKernelLow
  refine ⟨C,hC.le,fun f => ?_⟩
  have H := h (schwartzConj f)
  have he : (fun ξ : Space n => conj (smoothingLowCutoff (-ξ))) = smoothingLowCutoff := by
    funext ξ; simp only [smoothingLowCutoff,(smoothingLowBump n).neg, Complex.conj_ofReal]
  rw [← eLpNorm_frequencyHalfWave_schwartzConj, he]
  rwa [eLpNorm_besselPotential_schwartzConj] at H
end LSLeaf.LowPart
theorem OMA.solution : OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1.H1 := by
  intro n hn p α hp hα
  obtain ⟨C,hC,h⟩ := LSLeaf.LowPart.low_proof n hn p α hp hα
  exact ⟨C,hC, fun f => ⟨(LSLeaf.memLp_besselPotential α f _).eLpNorm_lt_top,h f⟩⟩
