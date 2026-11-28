import OMAReductions.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1
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
/- Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). -/
noncomputable section
namespace LSLeaf.InvAux
open OMA.S_wpc_local_smoothing_conjecture MeasureTheory Set Metric Filter FourierTransform
open scoped ENNReal NNReal ContDiff Topology RealInnerProductSpace ComplexConjugate
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
/-- Complex convolution, written explicitly to expose the operator used by
the Euclidean transfer argument. -/
noncomputable def complexConvolution (k f : G → ℂ) (μ : Measure G) (x : G) : ℂ :=
  ∫ y, k y * f (x - y) ∂μ
theorem complexConvolution_rpow_integral_le {k f : G → ℂ}
    (hk : Measurable k) (hf : Measurable f) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, ‖complexConvolution k f μ x‖ₑ ^ p ∂μ) ≤
      (∫⁻ y, ‖k y‖ₑ ∂μ) ^ p * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  apply le_trans ?_ (lintegral_convolution_rpow_le hk.enorm hf.enorm hp)
  apply lintegral_mono
  intro x
  apply ENNReal.rpow_le_rpow ?_ (by linarith)
  simpa only [complexConvolution, enorm_mul] using
    enorm_integral_le_lintegral_enorm (fun y => k y * f (x - y))
/-- The finite-exponent `L¹ × Lᵖ → Lᵖ` Young inequality. -/
theorem eLpNorm_complexConvolution_le_of_measurable {k f : G → ℂ}
    (hk : Measurable k) (hf : Measurable f) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    eLpNorm (complexConvolution k f μ) p μ ≤ eLpNorm k 1 μ * eLpNorm f p μ := by
  have hp₀ : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).mpr hp
  have hpr₀ : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hpr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top, eLpNorm_one_eq_lintegral_enorm, eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top]
  have hb := ENNReal.rpow_le_rpow (complexConvolution_rpow_integral_le (μ := μ) hk hf hpr)
    (show 0 ≤ 1 / p.toReal by positivity)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ 1 / p.toReal by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hpr₀.ne', ENNReal.rpow_one] using hb
/-- Young's inequality for a.e.-strongly-measurable inputs. -/
theorem eLpNorm_complexConvolution_le {k f : G → ℂ}
    (hk : AEStronglyMeasurable k μ) (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    eLpNorm (complexConvolution k f μ) p μ ≤ eLpNorm k 1 μ * eLpNorm f p μ := by
  have heq : complexConvolution k f μ = complexConvolution (hk.mk k) (hf.mk f) μ :=
    convolution_congr (ContinuousLinearMap.mul ℂ ℂ) hk.ae_eq_mk hf.ae_eq_mk
  rw [heq, eLpNorm_congr_ae hk.ae_eq_mk, eLpNorm_congr_ae hf.ae_eq_mk]
  exact eLpNorm_complexConvolution_le_of_measurable hk.stronglyMeasurable_mk.measurable
    hf.stronglyMeasurable_mk.measurable hp hp_top
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]
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
theorem frequencyHalfWave_eq_complexConvolution {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : Continuous φ) (hs : HasCompactSupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Integrable f) (X : EuclideanSpace ℝ (Fin n)) :
    frequencyHalfWave φ h T f X = (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ *
      complexConvolution (semiclassicalWaveKernel volume φ h T) f volume X := by
  rw [(frequencyHalfWave_eq_integral_kernel hφ hs hh T hf X).2]
  congr 1
  simpa only [complexConvolution, sub_sub_cancel] using
    (integral_sub_left_eq_self
      (fun Y => semiclassicalWaveKernel volume φ h T (X - Y) * f Y) volume X).symm
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
theorem angularInverse_scaled_eq_waveKernel {n : ℕ} (φ : Space n → ℂ)
    {h : ℝ} (hh : 0 < h) (x : Space n) :
    angularInverse (fun ξ ↦ φ (h • ξ)) x =
      (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ *
        semiclassicalWaveKernel volume φ h 0 x := by
  rw [← scaled_wave_integral φ hh 0 x]
  simp only [angularInverse, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [oscillation, euclideanWavePhase, zero_mul, sub_zero, div_one]
  rw [mul_comm (inner ℝ x ξ : ℂ) Complex.I]
theorem frequencyHalfWave_zero_eq_convolution {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    {f : Space n → ℂ} (hf : Integrable f) (x : Space n) :
    frequencyHalfWave φ h 0 f x = complexConvolution
      (angularInverse (fun ξ ↦ φ (h • ξ))) f volume x := by
  rw [frequencyHalfWave_eq_complexConvolution hφ hc hh 0 hf]
  simp only [complexConvolution, angularInverse_scaled_eq_waveKernel φ hh,
    mul_assoc, integral_const_mul]
theorem eLpNorm_angularInverse_dilate_one {n : ℕ} {φ : Space n → ℂ}
    (hφ : Integrable φ) {h : ℝ} (hh : 0 < h) :
    eLpNorm (angularInverse (fun ξ ↦ φ (h • ξ))) 1 volume =
      eLpNorm (angularInverse φ) 1 volume := by
  have heq : angularInverse (fun ξ ↦ φ (h • ξ)) =
      fun x ↦ (h ^ n)⁻¹ • angularInverse φ (h⁻¹ • x) :=
    funext (angularInverse_dilate φ hh)
  rw [heq]
  exact eLpNorm_normalized_dilate_one _ (continuous_angularInverse hφ).measurable hh
theorem eLpNorm_frequencyHalfWave_zero_le {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    {f : Space n → ℂ} (hf : Integrable f) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    eLpNorm (frequencyHalfWave φ h 0 f) p volume ≤
      eLpNorm (angularInverse φ) 1 volume * eLpNorm f p volume := by
  have hφint : Integrable φ := hφ.integrable_of_hasCompactSupport hc
  have hscaled : Integrable (fun ξ ↦ φ (h • ξ)) :=
    (hφ.comp (continuous_const.smul continuous_id)).integrable_of_hasCompactSupport
      (hc.comp_smul hh.ne')
  have heq : frequencyHalfWave φ h 0 f = complexConvolution
      (angularInverse (fun ξ ↦ φ (h • ξ))) f volume := by
    funext x
    exact frequencyHalfWave_zero_eq_convolution hφ hc hh hf x
  rw [heq, ← eLpNorm_angularInverse_dilate_one hφint hh]
  exact eLpNorm_complexConvolution_le
    (continuous_angularInverse hscaled).aestronglyMeasurable hf.aestronglyMeasurable hp hp_top
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
theorem uniform_frequencyHalfWave_zero_bound {Q : Type*} [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] {n : ℕ} {K : Set Q} {S : Set (Space n)}
    (hK : IsCompact K) (hS : IsCompact S) {a : Q × Space n → ℂ}
    (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ Set.univ ×ˢ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ h : ℝ, 0 < h → ∀ f : Space n → ℂ,
      Integrable f → ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (frequencyHalfWave (fun ξ ↦ a (q, ξ)) h 0 f) p volume ≤
        ENNReal.ofReal C * eLpNorm f p volume := by
  obtain ⟨C, hC, hc⟩ := uniform_angularInverse_L1 hK hS ha hs
  refine ⟨C, hC, ?_⟩
  intro q hq h hh f hf p hp hptop
  have hcont : Continuous (fun ξ ↦ a (q, ξ)) :=
    ha.continuous.comp (continuous_const.prodMk continuous_id)
  have hcompact : HasCompactSupport (fun ξ ↦ a (q, ξ)) := by
    apply hS.of_isClosed_subset (isClosed_tsupport _)
    intro ξ hξ
    exact (hs (tsupport_comp_subset_preimage a
      (continuous_const.prodMk continuous_id) hξ)).2
  exact (eLpNorm_frequencyHalfWave_zero_le hcont hcompact hh hf hp hptop).trans
    (mul_le_mul' (hc q hq).2 le_rfl)
end
section
-- OAI.Analysis.Fourier.BochnerRiesz.Annular
open scoped ENNReal ContDiff Topology
/-- The compact family obtained by normalizing a Bessel potential on an
annulus. The parameter λ will be the reciprocal of the frequency scale. -/
def annularSobolevSymbol {n : ℕ} (χ : Space n → ℂ) (σ : ℝ) (z : ℝ × Space n) : ℂ :=
  ((z.1 ^ 2 + ‖z.2‖ ^ 2) ^ (σ / 2) : ℝ) * χ z.2
theorem tsupport_annularSobolevSymbol {n : ℕ} (χ : Space n → ℂ) (σ : ℝ) :
    tsupport (annularSobolevSymbol χ σ) ⊆ Set.univ ×ˢ tsupport χ := by
  intro z hz
  refine ⟨trivial, ?_⟩
  exact tsupport_comp_subset_preimage χ continuous_snd
    (tsupport_mul_subset_right (f := fun z : ℝ × Space n ↦
      (((z.1 ^ 2 + ‖z.2‖ ^ 2) ^ (σ / 2) : ℝ) : ℂ)) hz)
theorem contDiff_annularSobolevSymbol {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hzero : (0 : Space n) ∉ tsupport χ) (σ : ℝ) :
    ContDiff ℝ ∞ (annularSobolevSymbol χ σ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.2 ∈ tsupport χ
  · have hx : z.2 ≠ 0 := by intro h; exact hzero (h ▸ hz)
    have hpos : 0 < z.1 ^ 2 + ‖z.2‖ ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr hx))
    have hb : ContDiffAt ℝ ∞ (fun z : ℝ × Space n ↦ z.1 ^ 2 + ‖z.2‖ ^ 2) z :=
      (contDiffAt_fst.pow 2).add (ContDiffAt.norm_sq (𝕜 := ℝ) contDiffAt_snd)
    have hp := hb.rpow_const_of_ne (p := σ / 2) hpos.ne'
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hp).mul (hχ.contDiffAt.comp z contDiffAt_snd)
  · have hnear := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto (continuous_snd.tendsto z)
    have heq : annularSobolevSymbol χ σ =ᶠ[𝓝 z] (fun _ ↦ 0) := by
      filter_upwards [hnear] with q hq
      change χ q.2 = 0 at hq
      simp [annularSobolevSymbol, hq]
    exact contDiffAt_const.congr_of_eventuallyEq heq
theorem annularSobolevSymbol_scaling {n : ℕ} (χ : Space n → ℂ) (σ : ℝ)
    {h : ℝ} (hh : 0 < h) (ξ : Space n) :
    annularSobolevSymbol χ σ (h, h • ξ) =
      (h ^ σ : ℝ) * ((1 + ‖ξ‖ ^ 2) ^ (σ / 2) : ℝ) * χ (h • ξ) := by
  have hs : h ^ 2 + ‖h • ξ‖ ^ 2 = h ^ 2 * (1 + ‖ξ‖ ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    ring
  have hp : (h ^ 2 : ℝ) ^ (σ / 2) = h ^ σ := by
    rw [← Real.rpow_natCast_mul hh.le]
    congr 1
    ring
  simp only [annularSobolevSymbol, hs,
    Real.mul_rpow (sq_nonneg h) (show 0 ≤ 1 + ‖ξ‖ ^ 2 by positivity), hp,
    Complex.ofReal_mul]
end
section
-- OAI.Analysis.Fourier.BochnerRiesz.Projection
open scoped ENNReal ContDiff
/-- A smooth annular cutoff, applied in the manuscript's angular-frequency convention. -/
def annularProject {n : ℕ} (χ : Space n → ℂ) (h : ℝ) (f : SchwartzMap (Space n) ℂ) :
    SchwartzMap (Space n) ℂ :=
  SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ χ (h • ((2 * Real.pi) • ξ))) f
theorem annularProject_symbol_temperate {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h) :
    Function.HasTemperateGrowth (fun ξ ↦ χ (h • ((2 * Real.pi) • ξ))) := by
  have hs : HasCompactSupport (fun ξ ↦ χ ((h * (2 * Real.pi)) • ξ)) :=
    hc.comp_smul (mul_ne_zero hh.ne' (by positivity))
  have hd : ContDiff ℝ ∞ (fun ξ ↦ χ ((h * (2 * Real.pi)) • ξ)) :=
    hχ.comp (by fun_prop)
  simpa only [smul_smul] using hs.hasTemperateGrowth hd
theorem fourier_annularProject {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    (𝓕 (annularProject χ h f) : SchwartzMap (Space n) ℂ) ξ =
      χ (h • ((2 * Real.pi) • ξ)) * (𝓕 f : SchwartzMap (Space n) ℂ) ξ := by
  rw [annularProject, SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply (annularProject_symbol_temperate hχ hc hh)]
  rfl
theorem angularFourier_annularProject {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    angularFourier (annularProject χ h f) ξ = χ (h • ξ) * angularFourier f ξ := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have he : (2 * Real.pi) • ((2 * Real.pi)⁻¹ • ξ) = ξ := by
    rw [smul_smul, mul_inv_cancel₀ hp, one_smul]
  conv_lhs => rw [← he]
  rw [angularFourier_scaled]
  change (𝓕 (annularProject χ h f) : SchwartzMap (Space n) ℂ) ((2 * Real.pi)⁻¹ • ξ) = _
  rw [fourier_annularProject hχ hc hh f, he]
  congr 1
  rw [SchwartzMap.fourier_coe, ← angularFourier_scaled, he]
theorem annularProject_eq_frequencyHalfWave {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    annularProject χ h f x = frequencyHalfWave χ h 0 f x := by
  rw [annularProject, SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.fourierInv_coe]
  rw [frequencyHalfWave, angularInverse_eq_fourierInv_scaled]
  apply Real.fourierInv_congr_ae
  exact Filter.Eventually.of_forall fun ξ ↦ by
    rw [SchwartzMap.smulLeftCLM_apply_apply (annularProject_symbol_temperate hχ hc hh)]
    simp only [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
      angularFourier_scaled, smul_eq_mul, SchwartzMap.fourier_coe]
end
section
-- OAI.Analysis.Fourier.BochnerRiesz.Cutoff
open scoped ContDiff
/-- A smooth compact annular cutoff, with explicitly separated inner
and outer plateaux. -/
theorem exists_annular_cutoff {n : ℕ} {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    ∃ χ : Space n → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (0 : Space n) ∉ tsupport χ ∧
      (∀ ξ, b ≤ ‖ξ‖ → ‖ξ‖ ≤ c → χ ξ = 1) ∧
      (∀ ξ, χ ξ ≠ 0 → a < ‖ξ‖ ∧ ‖ξ‖ < d) := by
  let inner : ContDiffBump (0 : Space n) := ⟨a, b, ha, hab⟩
  let outer : ContDiffBump (0 : Space n) := ⟨c, d, lt_of_lt_of_le (ha.trans hab) hbc, hcd⟩
  let χ : Space n → ℂ := fun ξ ↦ ((1 - inner ξ) * outer ξ : ℝ)
  have hsm : ContDiff ℝ ∞ χ := by
    exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.sub inner.contDiff).mul outer.contDiff)
  have hband (ξ : Space n) (hξ : χ ξ ≠ 0) : a < ‖ξ‖ ∧ ‖ξ‖ < d := by
    constructor
    · by_contra! hsmall
      have hi : inner ξ = 1 := inner.one_of_mem_closedBall (by
        simpa only [mem_closedBall, dist_zero_right] using hsmall)
      exact hξ (by simp [χ, hi])
    · have ho : outer ξ ≠ 0 := by
        intro hz
        exact hξ (by simp [χ, hz])
      have hm : ξ ∈ Function.support outer := ho
      rw [outer.support_eq] at hm
      simpa only [mem_ball, dist_zero_right] using hm
  have hs : tsupport χ ⊆ closedBall (0 : Space n) d := by
    apply closure_minimal _ isClosed_closedBall
    intro ξ hξ
    exact mem_closedBall.mpr (by simpa only [dist_zero_right] using (hband ξ hξ).2.le)
  have hlow : tsupport χ ⊆ {ξ : Space n | a ≤ ‖ξ‖} := by
    apply closure_minimal _ (isClosed_le continuous_const continuous_norm)
    intro ξ hξ
    exact (hband ξ hξ).1.le
  have hc : HasCompactSupport χ :=
    (isCompact_closedBall (0 : Space n) d).of_isClosed_subset isClosed_closure hs
  refine ⟨χ, hsm, hc, ?_, ?_, hband⟩
  · intro hz
    have h := hlow hz
    simp only [Set.mem_ofPred_eq, norm_zero, not_le.mpr ha] at h
  · intro ξ hb' hc'
    have hi : inner ξ = 0 := inner.zero_of_le_dist (by
      simpa only [dist_zero_right] using hb')
    have ho : outer ξ = 1 := outer.one_of_mem_closedBall (by
      simpa only [mem_closedBall, dist_zero_right] using hc')
    simp [χ, hi, ho]
end
section
-- OAI.Analysis.Fourier.LocalSmoothing.DyadicSupport
open scoped ContDiff
theorem smoothingLowCutoff_eq_one_of_norm_le_eight {n : ℕ} {ξ : Space n}
    (hξ : ‖ξ‖ ≤ 8) : smoothingLowCutoff ξ = 1 := by
  have h := (smoothingLowBump n).one_of_mem_closedBall (by
    simpa only [mem_closedBall, dist_zero_right, smoothingLowBump] using hξ)
  simp only [smoothingLowCutoff, h, Complex.ofReal_one]
theorem smoothingLowCutoff_eq_zero_of_sixteen_le_norm {n : ℕ} {ξ : Space n}
    (hξ : 16 ≤ ‖ξ‖) : smoothingLowCutoff ξ = 0 := by
  have h := (smoothingLowBump n).zero_of_le_dist (by
    simpa only [dist_zero_right, smoothingLowBump] using hξ)
  simp only [smoothingLowCutoff, h, Complex.ofReal_zero]
theorem smoothingAnnularCutoff_eq_zero_of_norm_le_eight {n : ℕ} {ξ : Space n}
    (hξ : ‖ξ‖ ≤ 8) : smoothingAnnularCutoff ξ = 0 := by
  have hh : ‖(1 / 2 : ℝ) • ξ‖ ≤ 8 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [norm_nonneg ξ]
  simp only [smoothingAnnularCutoff, smoothingLowCutoff_eq_one_of_norm_le_eight hh,
    smoothingLowCutoff_eq_one_of_norm_le_eight hξ, sub_self]
theorem smoothingAnnularCutoff_eq_zero_of_thirtyTwo_le_norm {n : ℕ} {ξ : Space n}
    (hξ : 32 ≤ ‖ξ‖) : smoothingAnnularCutoff ξ = 0 := by
  have hh : 16 ≤ ‖(1 / 2 : ℝ) • ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  simp only [smoothingAnnularCutoff, smoothingLowCutoff_eq_zero_of_sixteen_le_norm hh,
    smoothingLowCutoff_eq_zero_of_sixteen_le_norm (by linarith : 16 ≤ ‖ξ‖), sub_self]
theorem tsupport_smoothingAnnularCutoff_subset (n : ℕ) :
    tsupport (@smoothingAnnularCutoff n) ⊆ {ξ : Space n | 8 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 32} := by
  apply closure_minimal _
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
  intro ξ hξ
  change 8 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 32
  constructor
  · by_contra! hsmall
    exact hξ (smoothingAnnularCutoff_eq_zero_of_norm_le_eight hsmall.le)
  · by_contra! hlarge
    exact hξ (smoothingAnnularCutoff_eq_zero_of_thirtyTwo_le_norm hlarge.le)
/-- An enlarged annular cutoff, separated far enough from zero for the
logarithmic normalizing family used in Sobolev summation. -/
theorem exists_smoothing_enlarged_cutoff (n : ℕ) :
    ∃ χ : Space n → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (0 : Space n) ∉ tsupport χ ∧
      (∀ ξ, smoothingAnnularCutoff ξ ≠ 0 → χ ξ = 1) ∧
      (∀ ξ, ‖ξ‖ ≤ 4 → χ ξ = 0) := by
  obtain ⟨χ, hχ, hc, hz, hone, hband⟩ := exists_annular_cutoff
    (n := n) (a := 4) (b := 8) (c := 32) (d := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨χ, hχ, hc, hz, ?_, ?_⟩
  · intro ξ hξ
    have h := tsupport_smoothingAnnularCutoff_subset n (subset_closure hξ)
    exact hone ξ h.1 h.2
  · intro ξ hξ
    by_contra hn
    exact (not_lt_of_ge hξ) (hband ξ hn).1
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
theorem angularFourier_besselPotential {n : ℕ} (s : ℝ)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    angularFourier (besselPotential s f) ξ =
      ((1+‖ξ‖^2)^(s/2) : ℝ) • angularFourier f ξ := by
  rw [← besselPotentialSchwartz_eq]
  exact angularFourier_angularSchwartzMultiplier
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow (Space n) (s/2)) f ξ
end
section
-- OAI.Analysis.Fourier.BesselPotential.Annular
open scoped ContDiff ENNReal
/-- Exact cancellation of the normalized inverse Bessel symbol on an annulus. -/
theorem inverse_annular_bessel_symbol {n : ℕ} (χ : Space n → ℂ) (σ : ℝ)
    {h : ℝ} (hh : 0 < h) (ξ : Space n) :
    (h^σ : ℝ) • (annularSobolevSymbol χ (-σ) (h,h • ξ) *
      (((1+‖ξ‖^2)^(σ/2) : ℝ) • (1 : ℂ))) = χ (h • ξ) := by
  have hbase : 0 < 1+‖ξ‖^2 := by positivity
  have h₁ : (h^σ : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hh σ).ne'
  have h₂ : ((1+‖ξ‖^2)^(σ/2) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hbase _).ne'
  rw [annularSobolevSymbol_scaling χ (-σ) hh]
  rw [Real.rpow_neg hh.le,show -σ/2 = -(σ/2) by ring,Real.rpow_neg hbase.le]
  simp only [Complex.real_smul,Complex.ofReal_inv,mul_one]
  field_simp [Complex.ofReal_ne_zero.mpr h₁,Complex.ofReal_ne_zero.mpr h₂]
/-- Applying an annular cutoff to the input is the normalized inverse
Bessel multiplier applied to its actual Bessel potential. -/
theorem frequencyHalfWave_eq_inverse_bessel {n : ℕ} (χ : Space n → ℂ) (σ : ℝ)
    {h : ℝ} (hh : 0 < h) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    frequencyHalfWave χ h 0 f x = h^σ •
      frequencyHalfWave (fun ξ => annularSobolevSymbol χ (-σ) (h,ξ))
        h 0 (besselPotential σ f) x := by
  simp only [frequencyHalfWave,zero_mul,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,one_mul]
  rw [← angularInverse_smul_real]
  congr 1
  funext ξ
  rw [angularFourier_besselPotential]
  have hc := inverse_annular_bessel_symbol χ σ hh ξ
  simp only [Complex.real_smul,mul_one] at hc ⊢
  calc
    χ (h • ξ) * angularFourier f ξ =
      ((h^σ : ℝ) : ℂ) * (annularSobolevSymbol χ (-σ) (h,h • ξ) *
        (((1+‖ξ‖^2)^(σ/2) : ℝ) : ℂ)) * angularFourier f ξ := by rw [hc]
    _ = _ := by ring
/-- The annular inverse estimate, uniform in the scale and in the finite
Lp exponent. The cutoff need not equal one anywhere. -/
theorem annularProject_inverse_bessel_bound {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hzero : (0 : Space n) ∉ tsupport χ) (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ, ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (annularProject χ h f) p volume ≤
        ENNReal.ofReal (C*h^σ) * eLpNorm (besselPotential σ f) p volume := by
  obtain ⟨C,hC,hbound⟩ := uniform_frequencyHalfWave_zero_bound isCompact_Icc hc
    (contDiff_annularSobolevSymbol hχ hzero (-σ))
    (tsupport_annularSobolevSymbol χ (-σ))
  refine ⟨C,hC,?_⟩
  intro h hh hone f p hp hptop
  have hint : Integrable (besselPotential σ f) := by
    rw [← besselPotentialSchwartz_eq]
    exact (besselPotentialSchwartz σ f).integrable
  have heq : (annularProject χ h f : Space n → ℂ) = h^σ •
      frequencyHalfWave (fun ξ => annularSobolevSymbol χ (-σ) (h,ξ))
        h 0 (besselPotential σ f) := by
    funext x
    rw [annularProject_eq_frequencyHalfWave hχ hc hh]
    exact frequencyHalfWave_eq_inverse_bessel χ σ hh f x
  rw [heq,eLpNorm_const_smul,Real.enorm_eq_ofReal (Real.rpow_nonneg hh.le _)]
  calc
    _ ≤ ENNReal.ofReal (h^σ) * (ENNReal.ofReal C *
        eLpNorm (besselPotential σ f) p volume) :=
      mul_le_mul' le_rfl (hbound h ⟨hh.le,hone⟩ h hh _ hint p hp hptop)
    _ = _ := by rw [ENNReal.ofReal_mul hC]; ac_rfl
end
section
-- OAI.Analysis.Fourier.LocalSmoothing.DyadicEstimates
open scoped ENNReal ContDiff
theorem frequencyHalfWave_annularProject {n : ℕ} {φ χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (heq : ∀ ξ, φ ξ ≠ 0 → χ ξ = 1) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) (t : ℝ) (x : Space n) :
    frequencyHalfWave φ h t (annularProject χ h f) x =
      frequencyHalfWave φ h t f x := by
  unfold frequencyHalfWave
  congr 1
  funext ξ
  rw [angularFourier_annularProject hχ hc hh f]
  by_cases hz : φ (h • ξ) = 0
  · simp only [hz, mul_zero, zero_mul]
  · rw [heq (h • ξ) hz, one_mul]
end
end LSLeaf.InvAux
namespace LSLeaf
open OMA.S_wpc_local_smoothing_conjecture MeasureTheory
open scoped ENNReal
theorem inverseBand (n : ℕ) (α : ℝ) (p : ℝ≥0∞) (hp : 1 ≤ p) (ht : p ≠ ⊤) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, ∀ f : SchwartzMap (Space n) ℂ,
      ∃ g : SchwartzMap (Space n) ℂ,
        (∀ t x, frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) t g x =
          frequencyHalfWave smoothingAnnularCutoff (smoothingDyadicScale j) t f x) ∧
        eLpNorm g p volume ≤ ENNReal.ofReal (B * smoothingDyadicScale j ^ α) *
          eLpNorm (besselPotential α f) p volume := by
  obtain ⟨χ,hχ,hc,hz,he,_⟩ := InvAux.exists_smoothing_enlarged_cutoff n
  obtain ⟨B,hB,h⟩ := InvAux.annularProject_inverse_bessel_bound hχ hc hz α
  refine ⟨B,hB,fun j f ↦ ⟨InvAux.annularProject χ (smoothingDyadicScale j) f, ?_, ?_⟩⟩
  · exact InvAux.frequencyHalfWave_annularProject hχ hc he (smoothingDyadicScale_pos j) f
  · exact h _ (smoothingDyadicScale_pos j) (smoothingDyadicScale_le_one j) f p hp ht
end LSLeaf

theorem OMA.solution : OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1.H2 := LSLeaf.inverseBand
