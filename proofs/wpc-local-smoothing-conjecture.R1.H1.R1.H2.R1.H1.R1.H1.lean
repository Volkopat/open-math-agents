import OMAReductions.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1_H1_R1
/- Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). Interpolation only; the critical estimate is supplied as a hypothesis. -/
-- OAI.Analysis.Fourier.Wave.Basic
section
open _root_.MeasureTheory FourierTransform
open scoped Real
noncomputable section
namespace OAI.Analysis.Fourier.Wave
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev WaveL2 (n : ℕ) := Lp (α := Space n) ℂ 2
def wavePhase {n : ℕ} (t : ℝ) (ξ : Space n) : ℂ :=
  Complex.exp (((-2 * Real.pi * t * ‖ξ‖ : ℝ) : ℂ) * Complex.I)
@[simp] theorem norm_wavePhase {n : ℕ} (t : ℝ) (ξ : Space n) :
    ‖wavePhase t ξ‖ = 1 := by
  simp [wavePhase, Complex.norm_exp]
theorem continuous_wavePhase {n : ℕ} (t : ℝ) :
    Continuous (wavePhase (n := n) t) := by
  unfold wavePhase
  fun_prop
private theorem memLp_wavePhase_mul {n : ℕ} (t : ℝ) (f : WaveL2 n) :
    MemLp (fun ξ ↦ wavePhase t ξ * f ξ) 2 := by
  apply (Lp.memLp f).congr_norm
    ((continuous_wavePhase t).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun ξ ↦ by simp
def phaseMultiply {n : ℕ} (t : ℝ) (f : WaveL2 n) : WaveL2 n :=
  (memLp_wavePhase_mul t f).toLp _
theorem phaseMultiply_coe {n : ℕ} (t : ℝ) (f : WaveL2 n) :
    (phaseMultiply t f : Space n → ℂ) =ᵐ[volume] fun ξ ↦ wavePhase t ξ * f ξ :=
  MemLp.coeFn_toLp _
@[simp] theorem norm_phaseMultiply {n : ℕ} (t : ℝ) (f : WaveL2 n) :
    ‖phaseMultiply t f‖ = ‖f‖ := by
  rw [phaseMultiply, Lp.norm_toLp, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  exact Filter.Eventually.of_forall fun ξ ↦ by simp
def halfWaveL2 {n : ℕ} (t : ℝ) (f : WaveL2 n) : WaveL2 n :=
  (Lp.fourierTransformₗᵢ (Space n) ℂ).symm
    (phaseMultiply t ((Lp.fourierTransformₗᵢ (Space n) ℂ) f))
@[simp] theorem norm_halfWaveL2 {n : ℕ} (t : ℝ) (f : WaveL2 n) :
    ‖halfWaveL2 t f‖ = ‖f‖ := by
  simp [halfWaveL2]
end OAI.Analysis.Fourier.Wave
end
end

-- OAI.Analysis.Fourier.LocalSmoothing.Definitions
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped RealInnerProductSpace ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing
def criticalExponent (n : ℕ) : ℝ := 2 * n / (n - 1)
def smoothingOrder (n : ℕ) (p : ℝ) : ℝ := max 0 (((n : ℝ) - 1) / 2 - n / p)
def angularFourier {n : ℕ} (f : Space n → ℂ) (ξ : Space n) : ℂ :=
  ∫ x, Complex.exp (-Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * f x
def angularInverse {n : ℕ} (g : Space n → ℂ) (x : Space n) : ℂ :=
  (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
    ∫ ξ, Complex.exp (Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * g ξ
def halfWaveIntegral {n : ℕ} (t : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦ Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
    angularFourier f ξ)
def besselPotential {n : ℕ} (s : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦ ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) • angularFourier f ξ)
def frequencyHalfWave {n : ℕ} (φ : Space n → ℂ) (h t : ℝ)
    (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦ Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
    φ (h • ξ) * angularFourier f ξ)
def observationMeasure (n : ℕ) : Measure (Space n × ℝ) :=
  volume.prod (volume.restrict (Set.Icc 1 2))
def EuclideanLocalSmoothing : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p ε : ℝ, 2 ≤ p → (0 < ε ∨ (p = 2 ∧ ε = 0)) →
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (besselPotential (smoothingOrder n p + ε) f) (ENNReal.ofReal p) ∧
      MemLp (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (observationMeasure n) ≤
      ENNReal.ofReal C *
        eLpNorm (besselPotential (smoothingOrder n p + ε) f) (ENNReal.ofReal p) volume
def LogarithmicRefinement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ φ : Space n → ℂ,
    ContDiff ℝ ∞ φ → HasCompactSupport φ → 0 ∉ tsupport φ →
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (fun z : Space n × ℝ ↦ frequencyHalfWave φ h z.2 f z.1)
        (ENNReal.ofReal (criticalExponent n)) (observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ frequencyHalfWave φ h z.2 f z.1)
        (ENNReal.ofReal (criticalExponent n)) (observationMeasure n) ≤
      ENNReal.ofReal (C * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
        eLpNorm f (ENNReal.ofReal (criticalExponent n)) volume
end OAI.Analysis.Fourier.LocalSmoothing
end
end

-- OAI.Analysis.Fourier.SquareFunction.ConvolutionDensity
section
open OAI.Analysis.Fourier.Wave
namespace OAI.Analysis.Fourier.SquareFunction
open _root_.MeasureTheory Set
open scoped ENNReal NNReal
theorem exists_schwartz_eLpNorm_sub_le {n : ℕ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) {f : Space n → ℂ} (hf : MemLp f p volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : SchwartzMap (Space n) ℂ,
      eLpNorm (f - (g : Space n → ℂ)) p volume ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hc, hd, hbound⟩ := MemLp.exist_eLpNorm_sub_le hpt hp hf hε
  exact ⟨hc.toSchwartzMap hd, hbound⟩
theorem exists_pos_mul_ofReal_le {C : ℝ≥0∞} (hC : C ≠ ⊤)
    {ε : ℝ≥0} (hε : 0 < ε) : ∃ η : ℝ, 0 < η ∧ C * ENNReal.ofReal η ≤ ε := by
  have he : 0 < (ε : ℝ) := hε
  refine ⟨(ε : ℝ) / (C.toReal + 1), by positivity, ?_⟩
  have hb : C.toReal * ((ε : ℝ) / (C.toReal + 1)) ≤ ε := by
    calc
      _ ≤ (C.toReal + 1) * ((ε : ℝ) / (C.toReal + 1)) := by
        gcongr
        linarith
      _ = ε := mul_div_cancel₀ _ (by positivity)
  rw [← ENNReal.ofReal_toReal hC, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  simpa only [ENNReal.ofReal_coe_nnreal, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    using ENNReal.ofReal_le_ofReal hb
end OAI.Analysis.Fourier.SquareFunction
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Density
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
theorem bound_of_schwartz_dense {n : ℕ} {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (T : (Space n → ℂ) → Y → ℂ)
    (hTm : ∀ g, Measurable g → Integrable g → AEStronglyMeasurable (T g) ν)
    (hadd : ∀ g h, Integrable g → Integrable h → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) {A B : ℝ≥0∞}
    (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hsharp : ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (T g) p ν ≤ A * eLpNorm g p volume)
    (hrough : ∀ g, Measurable g → Integrable g → MemLp g p volume →
      eLpNorm (T g) p ν ≤ B * eLpNorm g p volume)
    {f : Space n → ℂ} (hfm : Measurable f) (hfi : Integrable f) (hfp : MemLp f p volume) :
    eLpNorm (T f) p ν ≤ A * eLpNorm f p volume := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨η,hη,herror⟩ := OAI.Analysis.Fourier.SquareFunction.exists_pos_mul_ofReal_le
    (C := A + B) (ENNReal.add_ne_top.mpr ⟨hA,hB⟩) hε
  obtain ⟨g,hg⟩ := OAI.Analysis.Fourier.SquareFunction.exists_schwartz_eLpNorm_sub_le hp hpt hfp hη
  have hnormg : eLpNorm g p volume ≤ eLpNorm f p volume + ENNReal.ofReal η := by
    have hid : (g : Space n → ℂ) = f - (f - (g : Space n → ℂ)) := by ext x; simp
    rw [hid]
    exact (eLpNorm_sub_le hfm.aestronglyMeasurable (hfm.sub g.continuous.measurable).aestronglyMeasurable hp).trans (add_le_add le_rfl hg)
  have hid : (fun x => g x + (f - (g : Space n → ℂ)) x) = f := by ext x; simp
  have hsum : T f = fun y => T g y + T (f - (g : Space n → ℂ)) y := by
    funext y
    simpa only [hid] using hadd g (f - (g : Space n → ℂ)) g.integrable (hfi.sub g.integrable) y
  rw [hsum]
  calc
    _ ≤ eLpNorm (T g) p ν + eLpNorm (T (f - (g : Space n → ℂ))) p ν := eLpNorm_add_le (hTm _ g.continuous.measurable g.integrable) (hTm _ (hfm.sub g.continuous.measurable) (hfi.sub g.integrable)) hp
    _ ≤ A * eLpNorm g p volume + B * eLpNorm (f - (g : Space n → ℂ)) p volume :=
      add_le_add (hsharp g) (hrough _ (hfm.sub g.continuous.measurable)
        (hfi.sub g.integrable) (hfp.sub (g.memLp p volume)))
    _ ≤ A * (eLpNorm f p volume + ENNReal.ofReal η) + B * ENNReal.ofReal η := by gcongr
    _ = A * eLpNorm f p volume + (A + B) * ENNReal.ofReal η := by ring
    _ ≤ _ := add_le_add le_rfl herror
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Exponents
section
open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
theorem criticalExponent_gt_two {n : ℕ} (hn : 2 ≤ n) : 2 < OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  apply (lt_div_iff₀ (by linarith : 0 < (n:ℝ)-1)).mpr
  nlinarith
theorem smoothingOrder_of_le_critical {n : ℕ} (hn : 2 ≤ n) {p : ℝ}
    (hp : 0 < p) (hpq : p ≤ OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p = 0 := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hmul := (le_div_iff₀ (by linarith : 0 < (n:ℝ)-1)).mp hpq
  have hdiv : ((n:ℝ)-1)/2 ≤ n/p := (le_div_iff₀ hp).mpr (by nlinarith)
  exact max_eq_left (sub_nonpos.mpr hdiv)
theorem smoothingOrder_of_ge_critical {n : ℕ} (hn : 2 ≤ n) {p : ℝ}
    (hqp : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n ≤ p) : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p = ((n:ℝ)-1)/2-n/p := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < p := lt_trans (by norm_num) ((criticalExponent_gt_two hn).trans_le hqp)
  have hmul := (div_le_iff₀ (by linarith : 0 < (n:ℝ)-1)).mp hqp
  have hdiv : (n:ℝ)/p ≤ (n-1)/2 := (div_le_iff₀ hp).mpr (by nlinarith)
  exact max_eq_right (sub_nonneg.mpr hdiv)
theorem high_frequency_exponent {n : ℕ} (hn : 2 ≤ n) {p : ℝ}
    (hqp : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n ≤ p) :
    (-((n:ℝ)-1)/2) * (1-OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n/p) = -OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < p := lt_trans (by norm_num) ((criticalExponent_gt_two hn).trans_le hqp)
  rw [smoothingOrder_of_ge_critical hn hqp]
  unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  have hn0 : (n:ℝ)-1 ≠ 0 := by linarith
  field_simp [hn0, hp.ne']
theorem interpolation_factor_le {C D L h a θ : ℝ} {k : ℕ}
    (hC : 0 < C) (hD : 0 < D) (hL : 1 ≤ L) (hh : 0 < h)
    (_ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (C * L ^ k) ^ θ * (D * h ^ a) ^ (1-θ) ≤
      (C ^ θ * D ^ (1-θ)) * h ^ (a*(1-θ)) * L ^ k := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  rw [Real.mul_rpow hC.le (pow_nonneg hL0 _),
    Real.mul_rpow hD.le (Real.rpow_nonneg hh.le _),
    ← Real.rpow_natCast L k, ← Real.rpow_mul hL0, ← Real.rpow_mul hh.le]
  have hb : L ^ ((k:ℝ)*θ) ≤ L ^ (k:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (mul_le_of_le_one_right (Nat.cast_nonneg k) hθ1)
  calc
    _ = (C^θ * D^(1-θ)) * h^(a*(1-θ)) * L^((k:ℝ)*θ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
theorem logarithm_weight_one_le {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) :
    1 ≤ 1 + Real.log (1/h) := by
  have hi : 1 ≤ 1/h := (le_div_iff₀ hh).mpr (by simpa using h1)
  linarith [Real.log_nonneg hi]
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end

-- OAI.Analysis.Fourier.Wave.AngularTransform
section
open _root_.MeasureTheory FourierTransform
noncomputable section
namespace OAI.Analysis.Fourier.Wave
theorem angularFourier_scaled {n : ℕ} (f : Space n → ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ((2 * Real.pi) • ξ) = 𝓕 f ξ := by
  rw [OAI.Analysis.Fourier.LocalSmoothing.angularFourier, Real.fourier_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    simp only [inner_smul_right, Complex.ofReal_mul, Complex.ofReal_neg, smul_eq_mul]
    congr 2
    push_cast
    ring
theorem angularInverse_eq_fourierInv_scaled {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse g x = 𝓕⁻ (fun ξ ↦ g ((2 * Real.pi) • ξ)) x := by
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hchange := Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n))
    (fun ξ ↦ Complex.exp (Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * g ξ)
    (2 * Real.pi) (hR := hπ)
  calc
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse g x =
      ∫ ξ, Complex.exp (Complex.I * ((inner ℝ x ((2 * Real.pi) • ξ) : ℝ) : ℂ)) *
        g ((2 * Real.pi) • ξ) := by
      simpa [OAI.Analysis.Fourier.LocalSmoothing.angularInverse, Space] using hchange.symm
    _ = 𝓕⁻ (fun ξ ↦ g ((2 * Real.pi) • ξ)) x := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ ↦ by
        simp only [inner_smul_right, real_inner_comm x ξ, Complex.ofReal_mul, smul_eq_mul]
        congr 2
        push_cast
        ring
theorem halfWaveIntegral_eq_fourierInv {n : ℕ} (t : ℝ) (f : Space n → ℂ) :
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f = 𝓕⁻ (fun ξ ↦ wavePhase t ξ * 𝓕 f ξ) := by
  funext x
  rw [OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral, angularInverse_eq_fourierInv_scaled]
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ ↦ by
    have hphase : Complex.exp (-Complex.I * (t * ‖(2 * Real.pi) • ξ‖ : ℝ)) =
        wavePhase t ξ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      unfold wavePhase
      congr 1
      push_cast
      ring
    dsimp only
    rw [hphase, angularFourier_scaled]
end OAI.Analysis.Fourier.Wave
end
end

-- OAI.Analysis.Fourier.BochnerRiesz.Dilation
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz
theorem angularFourier_dilate {n : ℕ} (f : Space n → ℂ) {r : ℝ} (hr : 0 < r)
    (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ f (r • x)) ξ = (r ^ n)⁻¹ • OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (r⁻¹ • ξ) := by
  have hchange := Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n))
    (fun y ↦ Complex.exp (-Complex.I * ((inner ℝ y (r⁻¹ • ξ) : ℝ) : ℂ)) * f y)
    r (hR := hr.le)
  have hid (x : Space n) : inner ℝ (r • x) (r⁻¹ • ξ) = inner ℝ x ξ := by
    rw [real_inner_smul_left, inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  simpa only [OAI.Analysis.Fourier.LocalSmoothing.angularFourier, hid, Space, finrank_euclideanSpace_fin] using hchange
theorem angularInverse_dilate {n : ℕ} (g : Space n → ℂ) {r : ℝ} (hr : 0 < r)
    (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ g (r • ξ)) x = (r ^ n)⁻¹ • OAI.Analysis.Fourier.LocalSmoothing.angularInverse g (r⁻¹ • x) := by
  have hchange := Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n))
    (fun ξ ↦ Complex.exp (Complex.I * ((inner ℝ (r⁻¹ • x) ξ : ℝ) : ℂ)) * g ξ)
    r (hR := hr.le)
  have hid (ξ : Space n) : inner ℝ (r⁻¹ • x) (r • ξ) = inner ℝ x ξ := by
    rw [real_inner_smul_left, inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  simp only [hid, Space, finrank_euclideanSpace_fin] at hchange
  simp only [OAI.Analysis.Fourier.LocalSmoothing.angularInverse]
  rw [hchange]
  exact smul_comm _ _ _
theorem angularInverse_smul_real {n : ℕ} (c : ℝ) (g : Space n → ℂ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ c • g ξ) x = c • OAI.Analysis.Fourier.LocalSmoothing.angularInverse g x := by
  simp only [OAI.Analysis.Fourier.LocalSmoothing.angularInverse, mul_smul_comm, integral_smul]
  exact smul_comm _ _ _
theorem halfWaveIntegral_dilate {n : ℕ} (f : Space n → ℂ) {r : ℝ} (hr : 0 < r)
    (t : ℝ) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t (fun y ↦ f (r • y)) x = OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (r * t) f (r • x) := by
  let g : Space n → ℂ := fun ξ ↦ Complex.exp (-Complex.I * ((r * t) * ‖ξ‖ : ℝ)) *
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ
  have hphase (ξ : Space n) : (r * t) * ‖r⁻¹ • ξ‖ = t * ‖ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    field_simp
  have heq : (fun ξ ↦ Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
      OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun y ↦ f (r • y)) ξ) =
      (fun ξ ↦ (r ^ n)⁻¹ • g (r⁻¹ • ξ)) := by
    funext ξ
    rw [angularFourier_dilate f hr ξ]
    dsimp only [g]
    rw [hphase, mul_smul_comm]
  rw [OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral, heq, angularInverse_smul_real,
    angularInverse_dilate g (inv_pos.mpr hr)]
  simp only [inv_pow, inv_inv, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_smul]
  rfl
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
end OAI.Analysis.Fourier.BochnerRiesz
end
end

-- OAI.Analysis.Fourier.WavePackets.Oscillatory
section
namespace OAI.Analysis.Fourier.WavePackets
open _root_.MeasureTheory
open scoped RealInnerProductSpace ContDiff
theorem hasLineDerivAt_euclidean_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ξ v : E) (hξ : ξ ≠ 0) :
    HasLineDerivAt ℝ (fun y : E => ‖y‖) (⟪ξ, v⟫ / ‖ξ‖) ξ v := by
  have hline : HasDerivAt (fun t : ℝ => ξ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ξ
  have hnorm := hline.norm_sq
  have hsqrt := hnorm.sqrt (by simp [hξ])
  change HasDerivAt (fun t : ℝ => ‖ξ + t • v‖) _ 0
  convert hsqrt using 1
  · ext t
    simp
  · simp
    ring
noncomputable def euclideanWavePhase {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : E) (T : ℝ) (ξ : E) : ℝ :=
  ⟪X, ξ⟫ - T * ‖ξ‖
theorem hasLineDerivAt_euclideanWavePhase {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X ξ v : E) (T : ℝ) (hξ : ξ ≠ 0) :
    HasLineDerivAt ℝ (euclideanWavePhase X T)
      (⟪X, v⟫ - T * (⟪ξ, v⟫ / ‖ξ‖)) ξ v := by
  have hline : HasDerivAt (fun t : ℝ => ξ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ξ
  have hi := (innerSL ℝ X).hasFDerivAt.comp_hasDerivAt 0 hline
  have hn := hasLineDerivAt_euclidean_norm ξ v hξ
  change HasDerivAt (fun t : ℝ => ‖ξ + t • v‖) _ 0 at hn
  change HasDerivAt (fun t : ℝ => ⟪X, ξ + t • v⟫ - T * ‖ξ + t • v‖) _ 0
  exact hi.sub (hn.const_mul T)
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
end OAI.Analysis.Fourier.WavePackets
end

-- OAI.Analysis.Fourier.WavePackets.Uniform
section
namespace OAI.Analysis.Fourier.WavePackets
open _root_.MeasureTheory
open scoped RealInnerProductSpace ContDiff
section JointAmplitudes
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
end JointAmplitudes
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
theorem uniform_rapid_decay_of_nonstationary_phase
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {U K : Set P} {S : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hS : IsCompact S) {φ : P → E → ℝ} {d : P × E → ℝ} {v : P → E} {a : E → ℂ}
    (hφc : ∀ p ∈ U, Continuous (φ p)) (hv : ContDiff ℝ ∞ v)
    (hφ : ∀ p ∈ U, ∀ ξ ∈ S, HasLineDerivAt ℝ (φ p) (d (p, ξ)) ξ (v p))
    (hd : ∀ q ∈ U ×ˢ S, ContDiffAt ℝ ∞ (fun q => (d q : ℂ)) q)
    (hd₀ : ∀ q ∈ U ×ˢ S, d q ≠ 0)
    (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ S) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ h : ℝ, 0 < h →
      ‖∫ ξ, oscillation (φ p) h ξ * a ξ ∂μ‖ ≤ h ^ N * C := by
  let A := jointAmplitude (fun q => (d q : ℂ)) v (fun q : P × E => a q.2)
  let B := fun k => quotientAmplitude (fun q => (d q : ℂ)) (A k)
  have hdn : ∀ q ∈ U ×ˢ S, (d q : ℂ) ≠ 0 := by
    intro q hq
    exact_mod_cast hd₀ q hq
  have hstart : tsupport (fun q : P × E => a q.2) ⊆ Set.univ ×ˢ S := by
    intro q hq
    exact ⟨trivial, hs (tsupport_comp_subset_preimage a continuous_snd hq)⟩
  have hA (k : ℕ) : ContDiffOn ℝ ∞ (A k) (U ×ˢ Set.univ) ∧
      tsupport (A k) ⊆ Set.univ ×ˢ S :=
    jointAmplitude_regular hU (ha.comp contDiff_snd).contDiffOn hv hstart hd hdn k
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
  have hdecay : ‖∫ ξ, oscillation (φ p) h ξ * a ξ ∂μ‖ ≤
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
        (contDiff_slice hU (hA k).1 hpU).continuous).integrable_of_hasCompactSupport
        hsa.mul_left
    · intro k _
      have hsb : HasCompactSupport (fun ξ => B k (p, ξ)) :=
        hS.of_isClosed_subset (isClosed_tsupport _) (hbslice k)
      exact ((continuous_oscillation (hφc p hpU) h).mul
        (contDiff_slice hU (hB k).1 hpU).continuous).integrable_of_hasCompactSupport
        hsb.mul_left
  apply hdecay.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hh.le N)
  apply integral_norm_le_of_compact_support_bound hS
    (subset_trans (subset_tsupport _) (hslice N))
  intro ξ hξ
  exact hC _ ⟨(p, ξ), ⟨hp, hξ⟩, rfl⟩
section WaveParameters
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def waveParameterDomain : Set (E × ℝ) :=
  {p | (3 : ℝ) / 4 < ‖p.1‖ ∧ |p.2| < (7 : ℝ) / 10}
def waveParameterCompact : Set (E × ℝ) :=
  Metric.sphere 0 1 ×ˢ Set.Icc 0 ((2 : ℝ) / 3)
noncomputable def jointWaveSlope (q : (E × ℝ) × E) : ℝ :=
  ‖q.1.1‖ ^ 2 - q.1.2 * (⟪q.2, q.1.1⟫ / ‖q.2‖)
omit [InnerProductSpace ℝ E] in
theorem isOpen_waveParameterDomain : IsOpen (waveParameterDomain (E := E)) := by
  apply (isOpen_lt continuous_const (continuous_norm.comp continuous_fst)).inter
  exact isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
omit [InnerProductSpace ℝ E] in
theorem waveParameterCompact_subset_domain :
    waveParameterCompact (E := E) ⊆ waveParameterDomain := by
  intro p hp
  have hn : ‖p.1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hp.1
  change (3 : ℝ) / 4 < ‖p.1‖ ∧ |p.2| < (7 : ℝ) / 10
  rw [hn, abs_of_nonneg hp.2.1]
  constructor <;> linarith [hp.2.2]
theorem jointWaveSlope_pos {p : E × ℝ} (hp : p ∈ waveParameterDomain) (ξ : E) :
    0 < jointWaveSlope (p, ξ) := by
  have hr : |⟪ξ, p.1⟫ / ‖ξ‖| ≤ ‖p.1‖ := by
    by_cases hz : ξ = 0
    · simp [hz]
    · rw [abs_div, abs_of_pos (norm_pos_iff.mpr hz)]
      apply (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
      simpa only [mul_comm] using abs_real_inner_le_norm ξ p.1
  have hm := mul_le_mul_of_nonneg_left hr (abs_nonneg p.2)
  have ht : p.2 * (⟪ξ, p.1⟫ / ‖ξ‖) ≤ |p.2| * ‖p.1‖ := by
    calc
      _ ≤ |p.2 * (⟪ξ, p.1⟫ / ‖ξ‖)| := le_abs_self _
      _ ≤ _ := by simpa only [abs_mul] using hm
  have hn : 0 < ‖p.1‖ := by have := hp.1; linarith
  have hd : |p.2| < ‖p.1‖ := by have := hp.1; have := hp.2; linarith
  have hprod := mul_lt_mul_of_pos_right hd hn
  dsimp [jointWaveSlope]
  nlinarith
theorem jointWaveSlope_contDiffAt {q : (E × ℝ) × E} (hq : q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q => (jointWaveSlope q : ℂ)) q := by
  have hw : ContDiffAt ℝ ∞ (fun q : (E × ℝ) × E => q.1.1) q := contDiffAt_fst.fst
  have ht : ContDiffAt ℝ ∞ (fun q : (E × ℝ) × E => q.1.2) q := contDiffAt_fst.snd
  have hξ : ContDiffAt ℝ ∞ (fun q : (E × ℝ) × E => q.2) q := contDiffAt_snd
  have hn := (contDiffAt_norm ℝ hq).comp q hξ
  have hs : ContDiffAt ℝ ∞ jointWaveSlope q :=
    (hw.norm_sq ℝ).sub (ht.mul ((hξ.inner ℝ hw).div hn (norm_ne_zero_iff.mpr hq)))
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp q hs
theorem uniform_normalized_wave_decay [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {a : E → ℂ} (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (omega : E) (t : ℝ), ‖omega‖ = 1 → 0 ≤ t → t ≤ (2 : ℝ) / 3 →
      ∀ h : ℝ, 0 < h →
        ‖∫ ξ, oscillation (euclideanWavePhase omega t) h ξ * a ξ ∂μ‖ ≤ h ^ N * C := by
  have hk : IsCompact (waveParameterCompact (E := E)) :=
    (isCompact_sphere 0 1).prod isCompact_Icc
  obtain ⟨C, hC, hb⟩ := uniform_rapid_decay_of_nonstationary_phase
    (μ := μ) (φ := fun p => euclideanWavePhase p.1 p.2) (d := jointWaveSlope)
    (v := fun p : E × ℝ => p.1) isOpen_waveParameterDomain hk
    waveParameterCompact_subset_domain hs
    (by intro p _; unfold euclideanWavePhase; fun_prop) contDiff_fst
    (by
      intro p _ ξ hξ
      have hξ₀ : ξ ≠ 0 := by intro hz; exact hzero (hz ▸ hξ)
      simpa only [jointWaveSlope, real_inner_self_eq_norm_sq] using
        hasLineDerivAt_euclideanWavePhase p.1 ξ p.1 p.2 hξ₀)
    (by
      intro q hq
      apply jointWaveSlope_contDiffAt
      intro hz
      exact hzero (hz ▸ hq.2))
    (by intro q hq; exact (jointWaveSlope_pos hq.1 q.2).ne') ha (Set.Subset.refl _) N
  refine ⟨C, hC, ?_⟩
  intro omega t homega ht₀ ht₁ h hh
  apply hb (omega, t) ?_ h hh
  exact ⟨by simpa [Metric.mem_sphere, dist_zero_right] using homega, ht₀, ht₁⟩
theorem uniform_wave_integral_off_cone [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {a : E → ℂ} (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : E) (T h : ℝ), 3 ≤ ‖X‖ → 0 ≤ T → T ≤ 2 → 0 < h →
      ‖∫ ξ, oscillation (euclideanWavePhase X T) h ξ * a ξ ∂μ‖ ≤ (h / ‖X‖) ^ N * C := by
  obtain ⟨C, hC, hb⟩ := uniform_normalized_wave_decay (μ := μ) ha hzero hs N
  refine ⟨C, hC, ?_⟩
  intro X T h hX hT₀ hT₁ hh
  have hr : 0 < ‖X‖ := by linarith
  let omega : E := ‖X‖⁻¹ • X
  let t : ℝ := T / ‖X‖
  have homega : ‖omega‖ = 1 := by
    simp only [omega, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  have ht₀ : 0 ≤ t := div_nonneg hT₀ hr.le
  have ht₁ : t ≤ (2 : ℝ) / 3 := by
    apply (div_le_iff₀ hr).mpr
    nlinarith
  have heq (ξ : E) : oscillation (euclideanWavePhase omega t) (h / ‖X‖) ξ =
      oscillation (euclideanWavePhase X T) h ξ := by
    have hp : euclideanWavePhase omega t ξ / (h / ‖X‖) = euclideanWavePhase X T ξ / h := by
      simp only [euclideanWavePhase, omega, t, real_inner_smul_left]
      field_simp
    simp only [oscillation, hp]
  simpa only [heq] using hb omega t homega ht₀ ht₁ (h / ‖X‖) (div_pos hh hr)
noncomputable def semiclassicalWaveKernel [MeasurableSpace E]
    (μ : Measure E) (a : E → ℂ) (h T : ℝ) (X : E) : ℂ :=
  ((h : ℂ) ^ Module.finrank ℝ E)⁻¹ *
    ∫ ξ, oscillation (euclideanWavePhase X T) h ξ * a ξ ∂μ
end WaveParameters
end OAI.Analysis.Fourier.WavePackets
end

-- OAI.Analysis.Fourier.BochnerRiesz.Kernel
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz
open OAI.Analysis.Fourier.WavePackets
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
      ‖∫ ξ, OAI.Analysis.Fourier.WavePackets.oscillation (φ p) h ξ * a (p, ξ) ∂μ‖ ≤ h ^ N * C := by
  let A := OAI.Analysis.Fourier.WavePackets.jointAmplitude (fun q => (d q : ℂ)) v a
  let B := fun k => OAI.Analysis.Fourier.WavePackets.quotientAmplitude (fun q => (d q : ℂ)) (A k)
  have hdn : ∀ q ∈ U ×ˢ S, (d q : ℂ) ≠ 0 := by
    intro q hq
    exact_mod_cast hd₀ q hq
  have hA (k : ℕ) : ContDiffOn ℝ ∞ (A k) (U ×ˢ Set.univ) ∧
      tsupport (A k) ⊆ Set.univ ×ˢ S := OAI.Analysis.Fourier.WavePackets.jointAmplitude_regular hU ha hv hs hd hdn k
  have hB (k : ℕ) : ContDiffOn ℝ ∞ (B k) (U ×ˢ Set.univ) ∧
      tsupport (B k) ⊆ Set.univ ×ˢ S :=
    ⟨OAI.Analysis.Fourier.WavePackets.joint_quotient_contDiffOn hU (hA k).1 (hA k).2 hd hdn,
      (OAI.Analysis.Fourier.WavePackets.tsupport_quotientAmplitude_subset _ _).trans (hA k).2⟩
  have hcont : ContinuousOn (A N) (K ×ˢ S) :=
    (hA N).1.continuousOn.mono (fun q hq => ⟨hKU hq.1, trivial⟩)
  obtain ⟨C, hCp, hC⟩ := ((hK.prod hS).image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  refine ⟨C * μ.real S, mul_nonneg hCp.le ENNReal.toReal_nonneg, ?_⟩
  intro p hp h hh
  have hpU := hKU hp
  have hslice (k : ℕ) : tsupport (fun ξ => A k (p, ξ)) ⊆ S :=
    OAI.Analysis.Fourier.WavePackets.tsupport_slice_subset hS.isClosed (hA k).2 p
  have hbslice (k : ℕ) : tsupport (fun ξ => B k (p, ξ)) ⊆ S :=
    OAI.Analysis.Fourier.WavePackets.tsupport_slice_subset hS.isClosed (hB k).2 p
  have hdecay : ‖∫ ξ, OAI.Analysis.Fourier.WavePackets.oscillation (φ p) h ξ * a (p, ξ) ∂μ‖ ≤
      h ^ N * ∫ ξ, ‖A N (p, ξ)‖ ∂μ := by
    apply OAI.Analysis.Fourier.WavePackets.norm_integral_oscillation_mul_le (a := fun k ξ => A k (p, ξ))
      (b := fun k ξ => B k (p, ξ)) (d := fun ξ => d (p, ξ)) hh (v p) N
    · intro k _ ξ hξ
      exact hφ p hpU ξ (hbslice k hξ)
    · intro k _ ξ
      have hdiff := ((hB k).1.contDiffAt
        ((hU.prod isOpen_univ).mem_nhds (show (p, ξ) ∈ U ×ˢ Set.univ from ⟨hpU, trivial⟩))).differentiableAt (by simp)
      simpa [HasLineDerivAt, A, OAI.Analysis.Fourier.WavePackets.jointAmplitude, OAI.Analysis.Fourier.WavePackets.jointAmplitudeStep] using
        hdiff.hasFDerivAt.hasLineDerivAt (0, v p)
    · intro k _ ξ
      dsimp [B, OAI.Analysis.Fourier.WavePackets.quotientAmplitude]
      by_cases hξ : ξ ∈ S
      · field_simp [hdn (p, ξ) ⟨hpU, hξ⟩]
      · have hz : A k (p, ξ) = 0 := image_eq_zero_of_notMem_tsupport
          (fun hmem => hξ ((hA k).2 hmem).2)
        simp [hz]
    · intro k _
      have hsa : HasCompactSupport (fun ξ => A k (p, ξ)) :=
        hS.of_isClosed_subset (isClosed_tsupport _) (hslice k)
      exact ((OAI.Analysis.Fourier.WavePackets.continuous_oscillation (hφc p hpU) h).mul
        (OAI.Analysis.Fourier.WavePackets.contDiff_slice hU (hA k).1 hpU).continuous).integrable_of_hasCompactSupport hsa.mul_left
    · intro k _
      have hsb : HasCompactSupport (fun ξ => B k (p, ξ)) :=
        hS.of_isClosed_subset (isClosed_tsupport _) (hbslice k)
      exact ((OAI.Analysis.Fourier.WavePackets.continuous_oscillation (hφc p hpU) h).mul
        (OAI.Analysis.Fourier.WavePackets.contDiff_slice hU (hB k).1 hpU).continuous).integrable_of_hasCompactSupport hsb.mul_left
  apply hdecay.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hh.le N)
  apply OAI.Analysis.Fourier.WavePackets.integral_norm_le_of_compact_support_bound hS
    (subset_trans (subset_tsupport _) (hslice N))
  intro ξ hξ
  exact hC _ ⟨(p, ξ), ⟨hp, hξ⟩, rfl⟩
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
  have heq (ξ : E) : OAI.Analysis.Fourier.WavePackets.oscillation (fun ξ ↦ inner ℝ u ξ) (‖x‖⁻¹) ξ =
      Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) := by
    have hreal : inner ℝ u ξ / ‖x‖⁻¹ = inner ℝ x ξ := by
      dsimp only [u]
      rw [real_inner_smul_left]
      field_simp
    unfold OAI.Analysis.Fourier.WavePackets.oscillation
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
      apply OAI.Analysis.Fourier.WavePackets.integral_norm_le_of_compact_support_bound hS
        ((subset_tsupport _).trans (OAI.Analysis.Fourier.WavePackets.tsupport_slice_subset hS.isClosed hs q))
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
    hS.of_isClosed_subset (isClosed_tsupport _) (OAI.Analysis.Fourier.WavePackets.tsupport_slice_subset hS.isClosed hs q)
  have hqa : Integrable (fun ξ ↦ a (q, ξ)) :=
    (ha.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport hslice
  have hi : Integrable (fun x : Space n ↦ ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * a (q, ξ)) :=
    hw.mono' (continuous_positive_fourier_integral hqa).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ hb q hq x)
  exact ⟨hi, integral_mono_ae hi.norm hw (Filter.Eventually.of_forall fun x ↦ hb q hq x)⟩
end OAI.Analysis.Fourier.BochnerRiesz
end
end

-- OAI.Analysis.Fourier.WavePackets.Young
section
namespace OAI.Analysis.Fourier.WavePackets
open _root_.MeasureTheory
open scoped ENNReal NNReal
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
theorem lintegral_weighted_rpow_le {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {k f : α → ℝ≥0∞} (hk : Measurable k) (hf : Measurable f)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, k x * f x ∂ν) ^ p ≤
      (∫⁻ x, k x ∂ν) ^ (p - 1) * ∫⁻ x, k x * f x ^ p ∂ν := by
  have hb := lintegral_rpow_le_mass_mul (ν := ν.withDensity k) hf hp
  simpa only [lintegral_withDensity_eq_lintegral_mul _ hk hf,
    lintegral_withDensity_eq_lintegral_mul _ hk (hf.pow_const p),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, Pi.mul_apply] using hb
section Convolution
variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
  [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
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
theorem eLpNorm_complexConvolution_le_of_measurable {k f : G → ℂ}
    (hk : Measurable k) (hf : Measurable f) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    eLpNorm (complexConvolution k f μ) p μ ≤ eLpNorm k 1 μ * eLpNorm f p μ := by
  have hp₀ : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).mpr hp
  have hpr₀ : 0 < p.toReal := lt_of_lt_of_le zero_lt_one hpr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top,
    eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top]
  have hb := ENNReal.rpow_le_rpow (complexConvolution_rpow_integral_le (μ := μ) hk hf hpr)
    (show 0 ≤ 1 / p.toReal by positivity)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ 1 / p.toReal by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hpr₀.ne', ENNReal.rpow_one] using hb
theorem eLpNorm_complexConvolution_le {k f : G → ℂ}
    (hk : AEStronglyMeasurable k μ) (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    eLpNorm (complexConvolution k f μ) p μ ≤ eLpNorm k 1 μ * eLpNorm f p μ := by
  have heq : complexConvolution k f μ = complexConvolution (hk.mk k) (hf.mk f) μ :=
    convolution_congr (ContinuousLinearMap.mul ℂ ℂ) hk.ae_eq_mk hf.ae_eq_mk
  rw [heq, eLpNorm_congr_ae hk.ae_eq_mk, eLpNorm_congr_ae hf.ae_eq_mk]
  exact eLpNorm_complexConvolution_le_of_measurable hk.stronglyMeasurable_mk.measurable
    hf.stronglyMeasurable_mk.measurable hp hp_top
end Convolution
section WaveTail
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]
end WaveTail
end OAI.Analysis.Fourier.WavePackets
end

-- OAI.Analysis.Fourier.WavePackets.Spacetime
section
namespace OAI.Analysis.Fourier.WavePackets
open _root_.MeasureTheory
open scoped ENNReal
section WaveTail
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
end WaveTail
end OAI.Analysis.Fourier.WavePackets
end

-- OAI.Analysis.Fourier.WavePackets.KernelIdentity
section
namespace OAI.Analysis.Fourier.WavePackets
open _root_.MeasureTheory
open scoped ContDiff RealInnerProductSpace FourierTransform
noncomputable def waveAmplitude {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (h T : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  Complex.exp (-Complex.I * (((T / h) * ‖ξ‖ : ℝ) : ℂ)) * φ ξ
theorem hasCompactSupport_waveAmplitude {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℂ}
    (hs : HasCompactSupport φ) (h T : ℝ) : HasCompactSupport (waveAmplitude φ h T) :=
  hs.mul_left
theorem contDiff_waveAmplitude {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    (h T : ℝ) : ContDiff ℝ ∞ (waveAmplitude φ h T) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    have hz : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport (waveAmplitude φ h T) := by
      exact fun hz => hzero (tsupport_mul_subset_right hz)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hz)
  · have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp ξ
      ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin n) => T / h) ξ).mul
        (contDiffAt_norm ℝ hξ))
    exact (((contDiffAt_const.mul hc).cexp).mul hφ.contDiffAt)
end OAI.Analysis.Fourier.WavePackets
end

-- OAI.Analysis.Fourier.WavePackets.ConvolutionIdentity
section
namespace OAI.Analysis.Fourier.WavePackets
open _root_.MeasureTheory
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
theorem frequencyHalfWave_eq_integral_kernel {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : Continuous φ) (hs : HasCompactSupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : Integrable f) (X : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun Y => semiclassicalWaveKernel volume φ h T (X - Y) * f Y) ∧
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h T f X =
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
  · unfold OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave OAI.Analysis.Fourier.LocalSmoothing.angularInverse OAI.Analysis.Fourier.LocalSmoothing.angularFourier
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
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h T f X = (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ *
      complexConvolution (semiclassicalWaveKernel volume φ h T) f volume X := by
  rw [(frequencyHalfWave_eq_integral_kernel hφ hs hh T hf X).2]
  congr 1
  simpa only [complexConvolution, sub_sub_cancel] using
    (integral_sub_left_eq_self
      (fun Y => semiclassicalWaveKernel volume φ h T (X - Y) * f Y) volume X).symm
end OAI.Analysis.Fourier.WavePackets
end

-- OAI.Analysis.Fourier.BochnerRiesz.Multiplier
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz
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
    Continuous (OAI.Analysis.Fourier.LocalSmoothing.angularInverse g) := by
  change Continuous ((((2 * Real.pi) ^ n)⁻¹ : ℝ) •
    (fun x : Space n ↦ ∫ ξ, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * g ξ))
  exact (continuous_positive_fourier_integral hg).const_smul _
theorem angularInverse_scaled_eq_waveKernel {n : ℕ} (φ : Space n → ℂ)
    {h : ℝ} (hh : 0 < h) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ φ (h • ξ)) x =
      (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ *
        OAI.Analysis.Fourier.WavePackets.semiclassicalWaveKernel volume φ h 0 x := by
  rw [← OAI.Analysis.Fourier.WavePackets.scaled_wave_integral φ hh 0 x]
  simp only [OAI.Analysis.Fourier.LocalSmoothing.angularInverse, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [OAI.Analysis.Fourier.WavePackets.oscillation, OAI.Analysis.Fourier.WavePackets.euclideanWavePhase, zero_mul, sub_zero, div_one]
  rw [mul_comm (inner ℝ x ξ : ℂ) Complex.I]
theorem frequencyHalfWave_zero_eq_convolution {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    {f : Space n → ℂ} (hf : Integrable f) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h 0 f x = OAI.Analysis.Fourier.WavePackets.complexConvolution
      (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ φ (h • ξ))) f volume x := by
  rw [OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_complexConvolution hφ hc hh 0 hf]
  simp only [OAI.Analysis.Fourier.WavePackets.complexConvolution, angularInverse_scaled_eq_waveKernel φ hh,
    mul_assoc, integral_const_mul]
theorem eLpNorm_angularInverse_dilate_one {n : ℕ} {φ : Space n → ℂ}
    (hφ : Integrable φ) {h : ℝ} (hh : 0 < h) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ φ (h • ξ))) 1 volume =
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ) 1 volume := by
  have heq : OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ φ (h • ξ)) =
      fun x ↦ (h ^ n)⁻¹ • OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ (h⁻¹ • x) :=
    funext (angularInverse_dilate φ hh)
  rw [heq]
  exact eLpNorm_normalized_dilate_one _ (continuous_angularInverse hφ).measurable hh
theorem eLpNorm_frequencyHalfWave_zero_le {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    {f : Space n → ℂ} (hf : Integrable f) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h 0 f) p volume ≤
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ) 1 volume * eLpNorm f p volume := by
  have hφint : Integrable φ := hφ.integrable_of_hasCompactSupport hc
  have hscaled : Integrable (fun ξ ↦ φ (h • ξ)) :=
    (hφ.comp (continuous_const.smul continuous_id)).integrable_of_hasCompactSupport
      (hc.comp_smul hh.ne')
  have heq : OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h 0 f = OAI.Analysis.Fourier.WavePackets.complexConvolution
      (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ φ (h • ξ))) f volume := by
    funext x
    exact frequencyHalfWave_zero_eq_convolution hφ hc hh hf x
  rw [heq, ← eLpNorm_angularInverse_dilate_one hφint hh]
  exact OAI.Analysis.Fourier.WavePackets.eLpNorm_complexConvolution_le
    (continuous_angularInverse hscaled).aestronglyMeasurable hf.aestronglyMeasurable hp hp_top
theorem uniform_angularInverse_L1 {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {n : ℕ} {K : Set Q} {S : Set (Space n)} (hK : IsCompact K) (hS : IsCompact S)
    {a : Q × Space n → ℂ} (ha : ContDiff ℝ ∞ a)
    (hs : tsupport a ⊆ Set.univ ×ˢ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K,
      Integrable (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ a (q, ξ))) ∧
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ a (q, ξ))) 1 volume ≤ ENNReal.ofReal C := by
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
end OAI.Analysis.Fourier.BochnerRiesz
end
end

-- OAI.Analysis.Fourier.BochnerRiesz.Projection
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory FourierTransform
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz
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
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (annularProject χ h f) ξ = χ (h • ξ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have he : (2 * Real.pi) • ((2 * Real.pi)⁻¹ • ξ) = ξ := by
    rw [smul_smul, mul_inv_cancel₀ hp, one_smul]
  conv_lhs => rw [← he]
  rw [OAI.Analysis.Fourier.Wave.angularFourier_scaled]
  change (𝓕 (annularProject χ h f) : SchwartzMap (Space n) ℂ) ((2 * Real.pi)⁻¹ • ξ) = _
  rw [fourier_annularProject hχ hc hh f, he]
  congr 1
  rw [SchwartzMap.fourier_coe, ← OAI.Analysis.Fourier.Wave.angularFourier_scaled, he]
theorem annularProject_eq_frequencyHalfWave {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    annularProject χ h f x = OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ h 0 f x := by
  rw [annularProject, SchwartzMap.fourierMultiplierCLM_apply, SchwartzMap.fourierInv_coe]
  rw [OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave, OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  apply Real.fourierInv_congr_ae
  exact Filter.Eventually.of_forall fun ξ ↦ by
    rw [SchwartzMap.smulLeftCLM_apply_apply (annularProject_symbol_temperate hχ hc hh)]
    simp only [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
      OAI.Analysis.Fourier.Wave.angularFourier_scaled, smul_eq_mul, SchwartzMap.fourier_coe]
theorem eLpNorm_annularProject_le {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤) :
    eLpNorm (annularProject χ h f) p volume ≤
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) 1 volume * eLpNorm f p volume := by
  have he : (annularProject χ h f : Space n → ℂ) = OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ h 0 f :=
    funext (annularProject_eq_frequencyHalfWave hχ hc hh f)
  rw [he]
  exact eLpNorm_frequencyHalfWave_zero_le hχ.continuous hc hh f.integrable hp hptop
theorem integrable_angularInverse_cutoff {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) : Integrable (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  let g : SchwartzMap (Space n) ℂ := schwartzDilate (2 * Real.pi) hp (hc.toSchwartzMap hχ)
  have he : OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ = (𝓕⁻ g : SchwartzMap (Space n) ℂ) := by
    funext x
    rw [OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled, SchwartzMap.fourierInv_coe]
    rfl
  rw [he]
  exact (𝓕⁻ g : SchwartzMap (Space n) ℂ).integrable
theorem annularProject_uniform_bound {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ A : ℝ, 0 < A ∧ ∀ h : ℝ, 0 < h → ∀ f : SchwartzMap (Space n) ℂ,
      ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (annularProject χ h f) p volume ≤ ENNReal.ofReal A * eLpNorm f p volume := by
  let D := eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse χ) 1 volume
  have hD : D ≠ ⊤ := (memLp_one_iff_integrable.mpr (integrable_angularInverse_cutoff hχ hc)).eLpNorm_ne_top
  have hd : D ≤ ENNReal.ofReal (D.toReal + 1) := by
    calc
      D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨D.toReal + 1, by positivity, ?_⟩
  intro h hh f p hp hptop
  exact (eLpNorm_annularProject_le hχ hc hh f hp hptop).trans (mul_le_mul' hd le_rfl)
end OAI.Analysis.Fourier.BochnerRiesz
end
end

-- OAI.Analysis.Fourier.Wave.Compatibility
section
open _root_.MeasureTheory FourierTransform
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Wave
theorem inverseFourier_integral_pairing {n : ℕ} (g : Space n → ℂ)
    (hg : Integrable g) (φ : SchwartzMap (Space n) ℂ) :
    (∫ ξ, (𝓕⁻ φ) ξ * g ξ) = ∫ x, φ x * (𝓕⁻ g) x := by
  have hL : (-(innerₗ (Space n))).flip = -(innerₗ (Space n)) := by
    ext x y
    simp [real_inner_comm]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := -(innerₗ (Space n)))
    (μ := volume) (ν := volume)
    Real.continuous_fourierChar
    (by
      change Continuous (fun z : Space n × Space n ↦ -(inner ℝ z.1 z.2))
      exact continuous_inner.neg)
    φ.integrable hg
  rw [hL] at h
  have hφ (ξ : Space n) : (𝓕⁻ φ) ξ = (𝓕⁻ (φ : Space n → ℂ)) ξ :=
    congrFun (SchwartzMap.fourierInv_coe φ) ξ
  simp_rw [hφ]
  change (∫ ξ, VectorFourier.fourierIntegral Real.fourierChar volume
    (-(innerₗ (Space n))) φ ξ * g ξ) =
    ∫ x, φ x * VectorFourier.fourierIntegral Real.fourierChar volume
      (-(innerₗ (Space n))) g x
  simpa only [smul_eq_mul] using h
theorem inverseFourierL2_integral_pairing {n : ℕ} (g : WaveL2 n)
    (φ : SchwartzMap (Space n) ℂ) :
    (∫ x, φ x * ((Lp.fourierTransformₗᵢ (Space n) ℂ).symm g) x) =
      ∫ ξ, (𝓕⁻ φ) ξ * g ξ := by
  have h := congrArg (fun T : TemperedDistribution (Space n) ℂ ↦ T φ)
    (Lp.fourierInv_toTemperedDistribution_eq g)
  simp only [TemperedDistribution.fourierInv_apply,
    Lp.toTemperedDistribution_apply, smul_eq_mul] at h
  change (∫ ξ, (𝓕⁻ φ) ξ * g ξ) =
    ∫ x, φ x * ((Lp.fourierTransformₗᵢ (Space n) ℂ).symm g) x at h
  exact h.symm
theorem inverseFourierL2_coe {n : ℕ} (g : WaveL2 n)
    (hg : Integrable (g : Space n → ℂ)) :
    (fun x ↦ ((Lp.fourierTransformₗᵢ (Space n) ℂ).symm g) x) =ᵐ[volume]
      𝓕⁻ (g : Space n → ℂ) := by
  have hc : Continuous (𝓕⁻ (g : Space n → ℂ)) := by
    rw [← Real.Lp.fourierTransformInv_toLp (memLp_one_iff_integrable.mpr hg)]
    exact (Real.Lp.fourierTransformInv _).continuous
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp ((Lp.fourierTransformₗᵢ (Space n) ℂ).symm g)).locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro ψ hψ hsψ
  have hsc : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hsψ.comp_left rfl
  have hdiff : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) := by fun_prop
  let φ := hsc.toSchwartzMap hdiff
  have h := (inverseFourierL2_integral_pairing g φ).trans
    (inverseFourier_integral_pairing (g : Space n → ℂ) hg φ)
  simpa [φ, Complex.real_smul] using h
end OAI.Analysis.Fourier.Wave
end
end

-- OAI.Analysis.Fourier.Wave.Continuity
section
open _root_.MeasureTheory
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Wave
theorem waveL2_norm_sq_integral {n : ℕ} (f : WaveL2 n) :
    ‖f‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 := by
  calc
    ‖f‖ ^ 2 = inner ℝ f f := (real_inner_self_eq_norm_sq f).symm
    _ = ∫ ξ, inner ℝ (f ξ) (f ξ) := rfl
    _ = _ := by simp_rw [real_inner_self_eq_norm_sq]
end OAI.Analysis.Fourier.Wave
end
end

-- OAI.Analysis.Fourier.Wave.Schwartz
section
open _root_.MeasureTheory FourierTransform
noncomputable section
namespace OAI.Analysis.Fourier.Wave
theorem integrable_wavePhase_mul {n : ℕ} (t : ℝ) (g : Space n → ℂ)
    (hg : Integrable g) : Integrable (fun ξ ↦ wavePhase t ξ * g ξ) := by
  have hm : AEStronglyMeasurable (fun ξ : Space n ↦ wavePhase t ξ * g ξ)
      (volume : Measure (Space n)) :=
    (continuous_wavePhase t).aestronglyMeasurable.mul hg.aestronglyMeasurable
  rw [← integrable_norm_iff hm]
  simpa only [norm_mul, norm_wavePhase, one_mul] using hg.norm
theorem halfWaveL2_schwartz_coe {n : ℕ} (t : ℝ) (f : SchwartzMap (Space n) ℂ) :
    (fun x ↦ halfWaveL2 t (f.toLp 2) x) =ᵐ[volume] OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f := by
  have hF : (Lp.fourierTransformₗᵢ (Space n) ℂ) (f.toLp 2) = (𝓕 f).toLp 2 := by
    change 𝓕 (f.toLp 2) = (𝓕 f).toLp 2
    exact SchwartzMap.toLp_fourier_eq f
  let g : WaveL2 n := phaseMultiply t ((𝓕 f).toLp 2)
  have hcoe : (g : Space n → ℂ) =ᵐ[volume]
      fun ξ ↦ wavePhase t ξ * (𝓕 f) ξ := by
    filter_upwards [phaseMultiply_coe t ((𝓕 f).toLp 2),
      (𝓕 f).coeFn_toLp 2 volume] with ξ h₁ h₂
    dsimp only [g]
    rw [h₁, h₂]
  have hg : Integrable (g : Space n → ℂ) :=
    (integrable_wavePhase_mul t (⇑(𝓕 f : SchwartzMap (Space n) ℂ))
      (𝓕 f).integrable).congr hcoe.symm
  have hInv := inverseFourierL2_coe g hg
  have heq : halfWaveL2 t (f.toLp 2) =
      (Lp.fourierTransformₗᵢ (Space n) ℂ).symm g := by
    simp only [halfWaveL2, hF, g]
  rw [heq, halfWaveIntegral_eq_fourierInv]
  filter_upwards [hInv] with x hx
  rw [hx, Real.fourierInv_congr_ae hcoe x]
  simp only [SchwartzMap.fourier_coe]
theorem memLp_halfWaveIntegral_two {n : ℕ} (t : ℝ) (f : SchwartzMap (Space n) ℂ) :
    MemLp (OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f) 2 := by
  let u : WaveL2 n := halfWaveL2 t (f.toLp 2 volume)
  have hcoe : (u : Space n → ℂ) =ᵐ[volume] OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f :=
    halfWaveL2_schwartz_coe t f
  exact (memLp_congr_ae (p := (2 : ENNReal)) hcoe).mp (Lp.memLp u)
theorem halfWaveIntegral_energy {n : ℕ} (t : ℝ) (f : SchwartzMap (Space n) ℂ) :
    (∫ x, ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 := by
  let f₂ : WaveL2 n := f.toLp 2 volume
  let u₂ : WaveL2 n := halfWaveL2 t f₂
  have hcoe : (fun x : Space n ↦ u₂ x) =ᵐ[volume] OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f :=
    halfWaveL2_schwartz_coe t f
  calc
    (∫ x, ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ ^ 2) =
        ∫ x, ‖u₂ x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hcoe] with x hx
      rw [hx]
    _ = ‖u₂‖ ^ 2 := (waveL2_norm_sq_integral u₂).symm
    _ = ‖f₂‖ ^ 2 := by simp only [u₂, norm_halfWaveL2]
    _ = ∫ x, ‖f₂ x‖ ^ 2 := waveL2_norm_sq_integral f₂
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [f.coeFn_toLp 2 volume] with x hx
      rw [hx]
end OAI.Analysis.Fourier.Wave
end
end

-- OAI.Analysis.Fourier.LocalSmoothing.L2
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory FourierTransform
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing
@[simp] theorem smoothingOrder_two (n : ℕ) : smoothingOrder n 2 = 0 := by
  unfold smoothingOrder
  have h : ((n : ℝ) - 1) / 2 - n / 2 = -(1 / 2 : ℝ) := by ring
  rw [h]
  norm_num
@[simp] theorem besselPotential_zero {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    besselPotential 0 f = f := by
  have hF : Integrable (𝓕 (f : Space n → ℂ)) := by
    simpa only [← SchwartzMap.fourier_coe] using (𝓕 f).integrable
  funext x
  simp only [besselPotential, zero_div, Real.rpow_zero, one_smul]
  rw [OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  simp_rw [OAI.Analysis.Fourier.Wave.angularFourier_scaled]
  exact f.integrable.fourierInv_fourier_eq hF f.continuous.continuousAt
theorem continuous_halfWaveIntegral {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    Continuous (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) := by
  let F : (Space n × ℝ) → Space n → ℂ := fun z ξ ↦
    Complex.exp (((2 * Real.pi * inner ℝ ξ z.1 : ℝ) : ℂ) * Complex.I) *
      OAI.Analysis.Fourier.Wave.wavePhase z.2 ξ * (𝓕 f) ξ
  have hrep : (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) =
      fun z ↦ ∫ ξ, F z ξ := by
    funext z
    rw [OAI.Analysis.Fourier.Wave.halfWaveIntegral_eq_fourierInv, Real.fourierInv_eq']
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ ↦ by
      simp only [F, smul_eq_mul, mul_assoc, SchwartzMap.fourier_coe]
  rw [hrep]
  apply continuous_of_dominated (bound := fun ξ ↦ ‖(𝓕 f) ξ‖)
  · intro z
    have hleft : Continuous (fun ξ : Space n ↦
        Complex.exp (((2 * Real.pi * inner ℝ ξ z.1 : ℝ) : ℂ) * Complex.I) *
          OAI.Analysis.Fourier.Wave.wavePhase z.2 ξ) := by
      unfold OAI.Analysis.Fourier.Wave.wavePhase
      fun_prop
    exact (hleft.mul (𝓕 f).continuous).aestronglyMeasurable
  · intro z
    exact Filter.Eventually.of_forall fun ξ ↦ by
      simp [F, Complex.norm_exp]
  · exact (𝓕 f).integrable.norm
  · exact Filter.Eventually.of_forall fun ξ ↦ by
      unfold F OAI.Analysis.Fourier.Wave.wavePhase
      fun_prop
theorem memLp_halfWaveIntegral_spacetime_two {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    MemLp (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) 2
      (observationMeasure n) := by
  have hm : AEStronglyMeasurable
      (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) (observationMeasure n) :=
    (continuous_halfWaveIntegral f).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hsq : AEStronglyMeasurable
      (fun z : Space n × ℝ ↦ ‖halfWaveIntegral z.2 f z.1‖ ^ 2) (observationMeasure n) :=
    ((continuous_halfWaveIntegral f).norm.pow 2).aestronglyMeasurable
  apply (integrable_prod_iff' hsq).mpr
  constructor
  · exact Filter.Eventually.of_forall fun t ↦
      (memLp_two_iff_integrable_sq_norm
        ((continuous_halfWaveIntegral f).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable).mp
        (OAI.Analysis.Fourier.Wave.memLp_halfWaveIntegral_two t f)
  · simp only [norm_pow, norm_norm, OAI.Analysis.Fourier.Wave.halfWaveIntegral_energy]
    exact integrable_const _
theorem halfWaveIntegral_spacetime_energy {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    (∫ z : Space n × ℝ, ‖halfWaveIntegral z.2 f z.1‖ ^ 2 ∂observationMeasure n) =
      ∫ x, ‖f x‖ ^ 2 := by
  have hsq := (memLp_two_iff_integrable_sq_norm
    ((continuous_halfWaveIntegral f).aestronglyMeasurable :
      AEStronglyMeasurable (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1)
        (observationMeasure n))).mp (memLp_halfWaveIntegral_spacetime_two f)
  rw [observationMeasure, integral_prod_symm _ hsq]
  simp only [OAI.Analysis.Fourier.Wave.halfWaveIntegral_energy, integral_const]
  norm_num [Measure.real, Real.volume_Icc]
theorem halfWaveIntegral_spacetime_eLpNorm_two {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1) 2 (observationMeasure n) =
      eLpNorm f 2 volume := by
  rw [(memLp_halfWaveIntegral_spacetime_two f).eLpNorm_eq_integral_rpow_norm
      (by norm_num) (by norm_num),
    (f.memLp 2 volume).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [halfWaveIntegral_spacetime_energy]
end OAI.Analysis.Fourier.LocalSmoothing
end
end

-- OAI.Analysis.Fourier.SquareFunction.ConvolutionRegularity
section
open OAI.Analysis.Fourier.Wave
namespace OAI.Analysis.Fourier.SquareFunction
open _root_.MeasureTheory Set
open scoped ENNReal Convolution
noncomputable def convolveKernel {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (K : Space n → H) (f : Space n → ℂ) (x : Space n) : H :=
  ∫ y, f y • K (x - y)
end OAI.Analysis.Fourier.SquareFunction
end

-- OAI.Analysis.Fourier.SquareFunction.VectorYoung
section
open OAI.Analysis.Fourier.Wave
namespace OAI.Analysis.Fourier.SquareFunction
open _root_.MeasureTheory
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
    apply le_trans ?_ (OAI.Analysis.Fourier.WavePackets.lintegral_convolution_rpow_le
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
end OAI.Analysis.Fourier.SquareFunction
end

-- OAI.Analysis.Fourier.WavePackets.Assembly
section
namespace OAI.Analysis.Fourier.WavePackets
open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
theorem measurable_frequencyHalfWave_spacetime {n : ℕ}
    {φ f : EuclideanSpace ℝ (Fin n) → ℂ} (hφ : Continuous φ)
    (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h) (hm : Measurable f) (hf : Integrable f) :
    Measurable (fun q : ℝ × EuclideanSpace ℝ (Fin n) => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h q.1 f q.2) := by
  have he : (fun q : ℝ × EuclideanSpace ℝ (Fin n) => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h q.1 f q.2) =
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
end OAI.Analysis.Fourier.WavePackets
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Wave
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
open OAI.Analysis.Fourier.WavePackets
def waveKernel {n : ℕ} (φ : Space n → ℂ) (h t : ℝ) (x : Space n) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ * OAI.Analysis.Fourier.WavePackets.semiclassicalWaveKernel volume φ h t x
theorem continuous_waveKernel {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) (h t : ℝ) :
    Continuous (waveKernel φ h t) := by
  have hc : Continuous (fun z : ℝ × Space n => OAI.Analysis.Fourier.WavePackets.semiclassicalWaveKernel volume φ h z.1 z.2) :=
    OAI.Analysis.Fourier.WavePackets.continuous_semiclassicalWaveKernel_spacetime (E := Space n) (μ := volume) hφ hs h
  have ht : Continuous (fun x : Space n => (t,x)) := continuous_const.prodMk continuous_id
  simpa only [waveKernel, Function.comp_def] using!
    (hc.comp ht).const_mul ((((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹)
theorem frequencyHalfWave_eq_convolveKernel {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (t : ℝ) {f : Space n → ℂ} (hf : Integrable f) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t f = OAI.Analysis.Fourier.SquareFunction.convolveKernel (waveKernel φ h t) f := by
  funext x
  rw [(OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_integral_kernel hφ hs hh t hf x).2]
  unfold OAI.Analysis.Fourier.SquareFunction.convolveKernel waveKernel
  simp_rw [smul_eq_mul, ← mul_assoc, mul_comm (f _) (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹,
    mul_assoc, mul_comm (f _) (OAI.Analysis.Fourier.WavePackets.semiclassicalWaveKernel _ _ _ _ _)]
  rw [integral_const_mul]
theorem frequencyHalfWave_add {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (t : ℝ) {f g : Space n → ℂ} (hf : Integrable f) (hg : Integrable g) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t (fun y => f y + g y) x =
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t f x + OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t g x := by
  change OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t (f + g) x = _
  rw [(OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_integral_kernel hφ hs hh t (hf.add hg) x).2,
    (OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_integral_kernel hφ hs hh t hf x).2,
    (OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_integral_kernel hφ hs hh t hg x).2]
  simp_rw [Pi.add_apply, mul_add]
  rw [integral_add (OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_integral_kernel hφ hs hh t hf x).1
    (OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_integral_kernel hφ hs hh t hg x).1, mul_add]
theorem measurable_frequencyWave {n : ℕ} {φ f : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (hf : Measurable f) (hi : Integrable f) :
    Measurable (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1) := by
  have H : Measurable (fun z : ℝ × Space n => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.1 f z.2) :=
    OAI.Analysis.Fourier.WavePackets.measurable_frequencyHalfWave_spacetime (n := n) hφ hs hh hf hi
  simpa only [Function.comp_def, Prod.swap] using
    H.comp (show Measurable (Prod.swap : Space n × ℝ → ℝ × Space n) from measurable_swap)
theorem halfWave_annularProject {n : ℕ} {φ : Space n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) (t : ℝ) :
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t (OAI.Analysis.Fourier.BochnerRiesz.annularProject φ h f) = OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t f := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave
  congr 1
  funext ξ
  rw [OAI.Analysis.Fourier.BochnerRiesz.angularFourier_annularProject hφ hs hh]
  exact (mul_assoc _ _ _).symm
theorem frequencyWave_two {n : ℕ} {φ : Space n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    ∃ A : ℝ, 0 < A ∧ ∀ h : ℝ, 0 < h → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1) 2
        (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1) 2
        (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ .ofReal A * eLpNorm f 2 volume := by
  obtain ⟨A,hA,hbound⟩ := OAI.Analysis.Fourier.BochnerRiesz.annularProject_uniform_bound hφ hs
  refine ⟨A,hA,?_⟩
  intro h hh f
  have he : (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1) =
      fun z => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 (OAI.Analysis.Fourier.BochnerRiesz.annularProject φ h f) z.1 := by
    funext z
    exact congrFun (halfWave_annularProject hφ hs hh f z.2).symm z.1
  rw [he]
  refine ⟨OAI.Analysis.Fourier.LocalSmoothing.memLp_halfWaveIntegral_spacetime_two _, ?_⟩
  rw [OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral_spacetime_eLpNorm_two]
  exact hbound h hh f 2 (by norm_num) (by norm_num)
theorem frequencyWave_slice_young {n : ℕ} {φ f : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (hf : Measurable f) (hi : Integrable f) (t : ℝ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t f) p volume ≤
      eLpNorm (waveKernel φ h t) 1 volume * eLpNorm f p volume := by
  rw [frequencyHalfWave_eq_convolveKernel hφ hs hh t hi]
  exact OAI.Analysis.Fourier.SquareFunction.eLpNorm_convolveKernel_le (continuous_waveKernel hφ hs h t) hf hp hpt
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end

-- OAI.Analysis.Fourier.BochnerRiesz.MaximalSummation
section
open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz
theorem eLpNorm_rpow_eq_lintegral {X E : Type*} [MeasurableSpace X]
    [TopologicalSpace E] [ContinuousENorm E] {μ : Measure X} {f : X → E}
    {p : ℝ} (hp : 0 < p) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal p) μ ^ p = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul]
  have h : (1 / p) * p = 1 := by field_simp
  rw [h, ENNReal.rpow_one]
end OAI.Analysis.Fourier.BochnerRiesz
end
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Product
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
theorem observation_norm_le_of_slices {n : ℕ} {u : Space n × ℝ → ℂ}
    (hu : Measurable u) {p : ℝ} (hp : 0 < p) {A : ℝ≥0∞}
    (hbound : ∀ t ∈ Icc (1 : ℝ) 2, eLpNorm (fun x => u (x,t)) (.ofReal p) volume ≤ A) :
    eLpNorm u (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ A := by
  have H : (∫⁻ z, ‖u z‖ₑ ^ p ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ A ^ p := by
    rw [OAI.Analysis.Fourier.LocalSmoothing.observationMeasure, lintegral_prod_symm' _ (hu.enorm.pow_const p)]
    calc
      _ ≤ ∫⁻ t in Icc (1 : ℝ) 2, A ^ p := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have h := ENNReal.rpow_le_rpow (hbound t ht) hp.le
        have hm : Measurable (fun x : Space n => u (x,t)) :=
          hu.comp (measurable_id.prodMk measurable_const)
        rwa [OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hm.aestronglyMeasurable] at h
      _ = _ := by norm_num [Real.volume_Icc]
  have H' := ENNReal.rpow_le_rpow H (show 0 ≤ 1 / p by positivity)
  simpa only [← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hu.aestronglyMeasurable,
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one] using H'
theorem observation_ae_time {n : ℕ} :
    ∀ᵐ z : Space n × ℝ ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n, z.2 ∈ Icc (1 : ℝ) 2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)).mpr
  exact Filter.Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Icc
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end

-- OAI.Analysis.Fourier.WavePackets.AngularGrid
section
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets
open Set
open scoped ContDiff
def angularGridBump (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1) - Real.smoothTransition x
theorem contDiff_angularGridBump : ContDiff ℝ ∞ angularGridBump :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff
theorem angularGridBump_eq_zero {x : ℝ} (hx : x ≤ -1 ∨ 1 ≤ x) :
    angularGridBump x = 0 := by
  rcases hx with hx | hx
  · simp only [angularGridBump,
      Real.smoothTransition.zero_of_nonpos (show x + 1 ≤ 0 by linarith),
      Real.smoothTransition.zero_of_nonpos (show x ≤ 0 by linarith), sub_self]
  · simp only [angularGridBump,
      Real.smoothTransition.one_of_one_le (show 1 ≤ x + 1 by linarith),
      Real.smoothTransition.one_of_one_le hx, sub_self]
theorem angularGridBump_ne_zero {x : ℝ} (hx : angularGridBump x ≠ 0) :
    |x| < 1 := by
  by_contra hn
  have hn := le_of_not_gt hn
  exact hx (angularGridBump_eq_zero (by
    rcases le_abs.mp hn with h | h
    · exact Or.inr h
    · exact Or.inl (by linarith)))
theorem sum_angularGridBump_range (N : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range N, angularGridBump (x - j) =
      Real.smoothTransition (x + 1) - Real.smoothTransition (x - N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, angularGridBump]
    have he : x - (↑(N + 1) : ℝ) + 1 = x - N := by push_cast; ring
    rw [he]
    ring
theorem sum_angularGridBump_fin (M : ℕ) {x : ℝ} (hx : |x| ≤ M) :
    ∑ j : Fin (2 * M + 1), angularGridBump (x - ((j : ℕ) - (M : ℝ))) = 1 := by
  have he (j : ℕ) : x - (j - (M : ℝ)) = (x + M) - j := by ring
  simp_rw [he]
  rw [← Finset.sum_range (fun j : ℕ => angularGridBump (x + M - j)),
    sum_angularGridBump_range]
  have hlo : 1 ≤ x + M + 1 := by have := (abs_le.mp hx).1; linarith
  have hhi : x + M - (↑(2 * M + 1) : ℝ) + 1 ≤ 0 := by
    have := (abs_le.mp hx).2
    push_cast
    linarith
  rw [Real.smoothTransition.one_of_one_le hlo, Real.smoothTransition.zero_of_nonpos hhi]
  norm_num
def angularGridProduct {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  ∏ i, angularGridBump (x i)
theorem contDiff_angularGridProduct (d : ℕ) :
    ContDiff ℝ ∞ (angularGridProduct (d := d)) := by
  apply contDiff_prod
  intro i _
  exact contDiff_angularGridBump.comp (contDiff_apply ℝ ℝ i)
theorem angularGridProduct_ne_zero {d : ℕ} {x : Fin d → ℝ}
    (hx : angularGridProduct x ≠ 0) (i : Fin d) : |x i| < 1 := by
  apply angularGridBump_ne_zero
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)
theorem sum_angularGridProduct (d M : ℕ) {x : Fin d → ℝ}
    (hx : ∀ i, |x i| ≤ M) :
    ∑ k : Fin d → Fin (2 * M + 1),
      angularGridProduct (fun i => x i - ((k i : ℕ) - (M : ℝ))) = 1 := by
  unfold angularGridProduct
  dsimp only
  rw [← Fintype.prod_sum (fun i (j : Fin (2 * M + 1)) =>
    angularGridBump (x i - ((j : ℕ) - (M : ℝ))))]
  simp_rw [sum_angularGridBump_fin M (hx _)]
  simp
def angularGridSize (R γ : ℝ) : ℕ := ⌈R / γ⌉₊
def angularGridCenter {d : ℕ} (R γ : ℝ)
    (k : Fin d → Fin (2 * angularGridSize R γ + 1)) (i : Fin d) : ℝ :=
  γ * ((k i : ℕ) - (angularGridSize R γ : ℝ))
theorem angularGrid_card_bound (d : ℕ) {R γ : ℝ} (hR : 0 ≤ R)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (Fintype.card (Fin d → Fin (2 * angularGridSize R γ + 1)) : ℝ) ≤
      ((2 * R + 3) / γ) ^ d := by
  have hM := (Nat.ceil_lt_add_one (div_nonneg hR hγ.le)).le
  change (angularGridSize R γ : ℝ) ≤ R / γ + 1 at hM
  have hb : (2 * angularGridSize R γ + 1 : ℝ) ≤ (2 * R + 3) / γ := by
    apply (le_div_iff₀ hγ).mpr
    have hm := (mul_le_mul_of_nonneg_right hM hγ.le)
    rw [add_mul, div_mul_cancel₀ _ hγ.ne'] at hm
    nlinarith
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  exact pow_le_pow_left₀ (by positivity) hb d
theorem angularGridCenter_bound {d : ℕ} {R γ : ℝ} (hR : 0 ≤ R)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (k : Fin d → Fin (2 * angularGridSize R γ + 1)) (i : Fin d) :
    |angularGridCenter R γ k i| ≤ R + 1 := by
  have hk : (k i : ℕ) ≤ 2 * angularGridSize R γ := Nat.le_of_lt_succ (k i).isLt
  have hk' : ((k i : ℕ) : ℝ) ≤ 2 * (angularGridSize R γ : ℝ) := by exact_mod_cast hk
  have hk0 : 0 ≤ ((k i : ℕ) : ℝ) := by positivity
  have hd : |((k i : ℕ) : ℝ) - angularGridSize R γ| ≤ angularGridSize R γ :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hM := (Nat.ceil_lt_add_one (div_nonneg hR hγ.le)).le
  change (angularGridSize R γ : ℝ) ≤ R / γ + 1 at hM
  have hm := mul_le_mul_of_nonneg_left hM hγ.le
  rw [mul_add, mul_div_cancel₀ _ hγ.ne', mul_one] at hm
  dsimp [angularGridCenter]
  rw [abs_mul, abs_of_pos hγ]
  exact (mul_le_mul_of_nonneg_left hd hγ.le).trans (by linarith)
theorem sum_scaled_angularGridProduct {d : ℕ} {R γ : ℝ} (hγ : 0 < γ)
    {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ R) :
    ∑ k : Fin d → Fin (2 * angularGridSize R γ + 1),
      angularGridProduct (fun i => (x i - angularGridCenter R γ k i) / γ) = 1 := by
  have he (k : Fin d → Fin (2 * angularGridSize R γ + 1)) (i : Fin d) :
      (x i - angularGridCenter R γ k i) / γ =
        x i / γ - ((k i : ℕ) - (angularGridSize R γ : ℝ)) := by
    dsimp [angularGridCenter]
    field_simp
  simp_rw [he]
  apply sum_angularGridProduct
  intro i
  rw [abs_div, abs_of_pos hγ]
  exact (div_le_div_of_nonneg_right (hx i) hγ.le).trans (Nat.le_ceil _)
end OAI.Analysis.Fourier.WavePackets
end
end

-- OAI.Analysis.Fourier.WavePackets.LinearKernel
section
namespace OAI.Analysis.Fourier.WavePackets
open _root_.MeasureTheory
open scoped ENNReal FourierTransform RealInnerProductSpace
theorem det_adjoint_real {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n)) : LinearMap.det A.adjoint = LinearMap.det A := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  rw [← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint b b,
    Matrix.det_conjTranspose, LinearMap.det_toMatrix]
  simp
theorem fourierInv_comp_linearEquiv {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    𝓕⁻ (φ ∘ A) x = |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| •
      𝓕⁻ φ (A.symm.toLinearEquiv.toLinearMap.adjoint x) := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  let g := fun ξ : EuclideanSpace ℝ (Fin n) =>
    Real.fourierChar ⟪A.symm ξ, x⟫ • φ ξ
  have hchange := A.toHomeomorph.measurableEmbedding.integral_map (μ := volume) g
  change (∫ ξ, g ξ ∂Measure.map A volume) = ∫ ξ, g (A ξ) at hchange
  have hd : LinearMap.det A.toLinearEquiv.toLinearMap ≠ 0 :=
    A.toLinearEquiv.isUnit_det'.ne_zero
  have hmap : Measure.map A volume =
      ENNReal.ofReal |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at hchange
  calc
    _ = ∫ ξ, g (A ξ) := by simp [g]
    _ = |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| • ∫ ξ, g ξ := hchange.symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      dsimp [g]
      rw [LinearMap.adjoint_inner_right]
      rfl
theorem eLpNorm_normalized_linear_kernel {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {K : EuclideanSpace ℝ (Fin n) → ℂ} (hK : Measurable K) :
    eLpNorm (fun x => |(LinearMap.det A.toLinearEquiv.toLinearMap)⁻¹| •
      K (A.symm.toLinearEquiv.toLinearMap.adjoint x)) 1 volume = eLpNorm K 1 volume := by
  let B := A.symm.toLinearEquiv.toLinearMap.adjoint
  let d := LinearMap.det A.toLinearEquiv.toLinearMap
  have hd : d ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  have hB : LinearMap.det B = d⁻¹ := by
    rw [det_adjoint_real]
    exact A.toLinearEquiv.det_coe_symm
  have hBm : Measurable B := B.continuous_of_finiteDimensional.measurable
  have hmap : Measure.map B volume = ENNReal.ofReal |d| • volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hB]; exact inv_ne_zero hd), hB, inv_inv]
  change eLpNorm (|d⁻¹| • (fun x => K (B x))) 1 volume = _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (abs_nonneg _),
    eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_one_eq_lintegral_enorm]
  rw [← lintegral_map hK.enorm hBm, hmap, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  simp [hd]
theorem eLpNorm_fourierInv_comp_linearEquiv {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (hφ : Measurable (𝓕⁻ φ)) :
    eLpNorm (𝓕⁻ (φ ∘ A)) 1 volume = eLpNorm (𝓕⁻ φ) 1 volume := by
  have he := funext (fourierInv_comp_linearEquiv A φ)
  rw [he]
  exact eLpNorm_normalized_linear_kernel A hφ
end OAI.Analysis.Fourier.WavePackets
end

-- OAI.Analysis.Fourier.WavePackets.UniformSectorKernel
section
open OAI.Analysis.Fourier.Wave
namespace OAI.Analysis.Fourier.WavePackets
open _root_.MeasureTheory
open scoped ENNReal FourierTransform ContDiff RealInnerProductSpace
theorem fourierInv_eq_normalized_angularInverse {n : ℕ} (φ : Space n → ℂ) (x : Space n) :
    𝓕⁻ φ x = ((2 * Real.pi) ^ n) • OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ ((2 * Real.pi) • x) := by
  rw [OAI.Analysis.Fourier.LocalSmoothing.angularInverse, smul_smul, mul_inv_cancel₀ (pow_ne_zero n (by positivity)), one_smul,
    Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [] with ξ
  simp only [inner_smul_left, starRingEnd_apply, star_trivial, smul_eq_mul, Complex.ofReal_mul]
  rw [real_inner_comm ξ x]
  congr 2
  ring
theorem eLpNorm_fourierInv_eq_angularInverse {n : ℕ} {φ : Space n → ℂ}
    (hφ : Integrable φ) : eLpNorm (𝓕⁻ φ) 1 volume = eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ) 1 volume := by
  let h : ℝ := (2 * Real.pi)⁻¹
  have hh : 0 < h := by dsimp [h]; positivity
  have he : 𝓕⁻ φ = fun x => (h ^ n)⁻¹ • OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ (h⁻¹ • x) := by
    funext x
    rw [fourierInv_eq_normalized_angularInverse]
    simp only [h, inv_pow, inv_inv]
  rw [he]
  exact OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_normalized_dilate_one _
    (OAI.Analysis.Fourier.BochnerRiesz.continuous_angularInverse hφ).measurable hh
theorem uniform_linearly_rescaled_inverse_kernel_bound {Q : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] {n : ℕ}
    {K : Set Q} {S : Set (Space n)} (hK : IsCompact K) (hS : IsCompact S)
    {a : Q × Space n → ℂ} (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ Set.univ ×ˢ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ A : Space n ≃L[ℝ] Space n,
      eLpNorm (𝓕⁻ (fun ξ => a (q, A ξ))) 1 volume ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hc⟩ := OAI.Analysis.Fourier.BochnerRiesz.uniform_angularInverse_L1 hK hS ha hs
  refine ⟨C, hC, ?_⟩
  intro q hq A
  let φ : Space n → ℂ := fun ξ => a (q, ξ)
  have hcont : ContDiff ℝ ∞ φ := ha.comp (contDiff_const.prodMk contDiff_id)
  have hcompact : HasCompactSupport φ := by
    apply hS.of_isClosed_subset (isClosed_tsupport _)
    intro ξ hξ
    exact (hs (tsupport_comp_subset_preimage a (continuous_const.prodMk continuous_id) hξ)).2
  have hφint : Integrable φ := hcont.continuous.integrable_of_hasCompactSupport hcompact
  have hmeas : Measurable (𝓕⁻ φ) := by
    have he : ((𝓕⁻ (hcompact.toSchwartzMap hcont) : SchwartzMap (Space n) ℂ) : Space n → ℂ) =
        𝓕⁻ φ := by rw [SchwartzMap.fourierInv_coe]; rfl
    rw [← he]
    exact (𝓕⁻ (hcompact.toSchwartzMap hcont)).continuous.measurable
  change eLpNorm (𝓕⁻ (φ ∘ A)) 1 volume ≤ ENNReal.ofReal C
  rw [eLpNorm_fourierInv_comp_linearEquiv A φ hmeas, eLpNorm_fourierInv_eq_angularInverse hφint]
  exact (hc q hq).2
section Periodic

noncomputable local instance uniformSectorCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance uniformSectorCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance uniformSectorCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
end Periodic
end OAI.Analysis.Fourier.WavePackets
end

-- OAI.Analysis.Fourier.WavePackets.AngularRescaling
section
open OAI.Analysis.Fourier.Wave
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets
open Set Filter
open scoped ContDiff Topology ENNReal FourierTransform
def angularChartRescale {d : ℕ} (γ : ℝ) (c : Fin d → ℝ)
    (ξ : Space (d + 1)) : Space (d + 1) :=
  WithLp.toLp 2 (Fin.cases (ξ 0) (fun i => γ * ξ i.succ + c i * ξ 0))
@[simp] theorem angularChartRescale_zero {d : ℕ} (γ : ℝ) (c : Fin d → ℝ)
    (ξ : Space (d + 1)) : angularChartRescale γ c ξ 0 = ξ 0 := rfl
@[simp] theorem angularChartRescale_succ {d : ℕ} (γ : ℝ) (c : Fin d → ℝ)
    (ξ : Space (d + 1)) (i : Fin d) :
    angularChartRescale γ c ξ i.succ = γ * ξ i.succ + c i * ξ 0 := by
  simp [angularChartRescale]
theorem contDiff_angularChartRescale (d : ℕ) :
    ContDiff ℝ ∞ (fun q : (ℝ × (Fin d → ℝ)) × Space (d + 1) =>
      angularChartRescale q.1.1 q.1.2 q.2) := by
  have heval (j : Fin (d + 1)) : ContDiff ℝ ∞ (fun ξ : Space (d + 1) => ξ j) := by
    fun_prop
  apply (contDiff_piLp 2).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [angularChartRescale_zero, Function.comp_def] using
      ((heval 0).comp contDiff_snd :
        ContDiff ℝ ∞ (fun q : (ℝ × (Fin d → ℝ)) × Space (d + 1) => q.2 0))
  · simp only [angularChartRescale_succ]
    exact (contDiff_fst.fst.mul ((heval j.succ).comp contDiff_snd)).add
      (((contDiff_apply ℝ ℝ j).comp contDiff_fst.snd).mul
        ((heval 0).comp contDiff_snd))
def angularChartLinearEquiv {d : ℕ} (γ : ℝ) (hγ : γ ≠ 0) (c : Fin d → ℝ) :
    Space (d + 1) ≃L[ℝ] Space (d + 1) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := angularChartRescale γ c
    invFun := angularChartRescale γ⁻¹ (fun i => -γ⁻¹ * c i)
    map_add' := by
      intro x y
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [angularChartRescale_succ, PiLp.add_apply]
        ring
    map_smul' := by
      intro r x
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [angularChartRescale_succ, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring
    left_inv := by
      intro x
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [angularChartRescale_succ, angularChartRescale_zero]
        field_simp
        ring
    right_inv := by
      intro x
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [angularChartRescale_succ, angularChartRescale_zero]
        field_simp
        ring }
def angularChartFamily {d : ℕ} (b : Space (d + 1) → ℂ)
    (q : (ℝ × (Fin d → ℝ)) × Space (d + 1)) : ℂ :=
  b (angularChartRescale q.1.1 q.1.2 q.2) *
    (angularGridProduct (fun i => q.2 i.succ / q.2 0) : ℂ)
def angularChartSymbol {d : ℕ} (b : Space (d + 1) → ℂ)
    (γ : ℝ) (c : Fin d → ℝ) (ξ : Space (d + 1)) : ℂ :=
  b ξ * (angularGridProduct (fun i => (ξ i.succ / ξ 0 - c i) / γ) : ℂ)
theorem contDiff_angularChartFamily {d : ℕ} {b : Space (d + 1) → ℂ}
    (hb : ContDiff ℝ ∞ b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) :
    ContDiff ℝ ∞ (angularChartFamily b) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q.2 0 = 0
  · have hnot : angularChartRescale q.1.1 q.1.2 q.2 ∉ tsupport b := by
      intro hm
      have := hs _ hm
      simp only [angularChartRescale_zero, hq] at this
      linarith
    apply (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _ : (ℝ × (Fin d → ℝ)) × Space (d + 1) => (0 : ℂ)) q).congr_of_eventuallyEq
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto
      (contDiff_angularChartRescale d).continuous.continuousAt] with p hp
    change b (angularChartRescale p.1.1 p.1.2 p.2) = 0 at hp
    simp only [angularChartFamily, hp, zero_mul]
  · apply (hb.comp (contDiff_angularChartRescale d)).contDiffAt.mul
    apply Complex.ofRealCLM.contDiff.contDiffAt.comp
    apply (contDiff_angularGridProduct d).contDiffAt.comp
    apply contDiffAt_pi.mpr
    intro i
    have hi : ContDiffAt ℝ ∞ (fun p : (ℝ × (Fin d → ℝ)) × Space (d + 1) =>
        p.2 i.succ) q := by fun_prop
    have h0 : ContDiffAt ℝ ∞ (fun p : (ℝ × (Fin d → ℝ)) × Space (d + 1) =>
        p.2 0) q := by fun_prop
    exact hi.div h0 hq
theorem angularChartFamily_common_support {d : ℕ} {b : Space (d + 1) → ℂ}
    {B : ℝ} (hs : ∀ ξ ∈ tsupport b, ξ 0 ≠ 0 ∧ |ξ 0| ≤ B) :
    tsupport (angularChartFamily b) ⊆ Set.univ ×ˢ
      (WithLp.toLp 2 '' Set.Icc (fun _ : Fin (d + 1) => -B) (fun _ => B)) := by
  have hc : IsClosed (WithLp.toLp 2 ''
      Set.Icc (fun _ : Fin (d + 1) => -B) (fun _ => B)) :=
    (isCompact_Icc.image (PiLp.continuous_toLp 2 (fun _ : Fin (d + 1) => ℝ))).isClosed
  apply closure_minimal _ (isClosed_univ.prod hc)
  rintro ⟨q, ξ⟩ hξ
  have hb : b (angularChartRescale q.1 q.2 ξ) ≠ 0 := by
    intro hz
    exact hξ (by simp [angularChartFamily, hz])
  have hg : angularGridProduct (fun i => ξ i.succ / ξ 0) ≠ 0 := by
    intro hz
    exact hξ (by simp [angularChartFamily, hz])
  have hslab : ξ 0 ≠ 0 ∧ |ξ 0| ≤ B := by simpa using hs _ (subset_tsupport b hb)
  have h0 : |ξ 0| ≤ B := hslab.2
  refine ⟨Set.mem_univ _, ξ.ofLp, ?_, by simp⟩
  have hall (i : Fin (d + 1)) : |ξ i| ≤ B := by
    refine Fin.cases h0 (fun j => ?_) i
    have hratio := (angularGridProduct_ne_zero hg j).le
    rw [abs_div] at hratio
    have habs : 0 < |ξ 0| := abs_pos.mpr hslab.1
    exact ((div_le_iff₀ habs).mp hratio).trans (by simpa using h0)
  exact ⟨fun i => (abs_le.mp (hall i)).1, fun i => (abs_le.mp (hall i)).2⟩
theorem angularChartSymbol_eq_rescaled {d : ℕ} {b : Space (d + 1) → ℂ}
    (hb0 : ∀ ξ, ξ 0 = 0 → b ξ = 0) {γ : ℝ} (hγ : γ ≠ 0) (c : Fin d → ℝ) :
    angularChartSymbol b γ c = fun ξ =>
      angularChartFamily b ((γ, c), (angularChartLinearEquiv γ hγ c).symm ξ) := by
  funext ξ
  let A := angularChartLinearEquiv γ hγ c
  have hA : angularChartRescale γ c (A.symm ξ) = ξ := A.apply_symm_apply ξ
  change b ξ * _ = b (angularChartRescale γ c (A.symm ξ)) * _
  rw [hA]
  by_cases hξ : ξ 0 = 0
  · simp [hb0 ξ hξ]
  · congr 2
    congr 1
    funext i
    change (ξ i.succ / ξ 0 - c i) / γ =
      (γ⁻¹ * ξ i.succ + (-γ⁻¹ * c i) * ξ 0) / ξ 0
    field_simp
    ring
theorem uniform_angularChartSymbol_kernel {d : ℕ} {b : Space (d + 1) → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
      ∀ c : Fin d → ℝ, (∀ i, |c i| ≤ R) →
      MeasureTheory.eLpNorm (𝓕⁻ (angularChartSymbol b γ c)) 1 MeasureTheory.volume ≤
        ENNReal.ofReal C := by
  obtain ⟨B, hB, hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hslab : ∀ ξ ∈ tsupport b, ξ 0 ≠ 0 ∧ |ξ 0| ≤ B := by
    intro ξ hξ
    refine ⟨ne_of_gt (ha.trans_le (hs ξ hξ)), ?_⟩
    have hcoord : |ξ 0| ≤ ‖ξ‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ 0
    exact hcoord.trans (hbound ξ hξ)
  let K : Set (ℝ × (Fin d → ℝ)) := Icc 0 1 ×ˢ Icc (fun _ => -R) (fun _ => R)
  let S : Set (Space (d + 1)) :=
    WithLp.toLp 2 '' Icc (fun _ : Fin (d + 1) => -B) (fun _ => B)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hS : IsCompact S := isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  obtain ⟨C, hC, hkernel⟩ := uniform_linearly_rescaled_inverse_kernel_bound hK hS
    (contDiff_angularChartFamily hb ha hs) (angularChartFamily_common_support hslab)
  refine ⟨C, hC, ?_⟩
  intro γ hγ hγ1 c hcR
  have hb0 : ∀ ξ, ξ 0 = 0 → b ξ = 0 := by
    intro ξ hξ
    by_contra hn
    have hh := hs ξ (subset_tsupport b hn)
    rw [hξ] at hh
    linarith
  rw [angularChartSymbol_eq_rescaled hb0 hγ.ne' c]
  apply hkernel (γ, c)
  exact ⟨⟨hγ.le, hγ1⟩, ⟨fun i => (abs_le.mp (hcR i)).1, fun i => (abs_le.mp (hcR i)).2⟩⟩
end OAI.Analysis.Fourier.WavePackets
end
end

-- OAI.Analysis.Fourier.WavePackets.AngularChart
section
open OAI.Analysis.Fourier.Wave
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets
open Set Filter
open scoped ContDiff Topology ENNReal FourierTransform
theorem tsupport_angularChartSymbol_subset {d : ℕ}
    (b : Space (d + 1) → ℂ) (γ : ℝ) (c : Fin d → ℝ) :
    tsupport (angularChartSymbol b γ c) ⊆ tsupport b := by
  apply closure_minimal _ (isClosed_tsupport b)
  intro ξ hξ
  apply subset_tsupport b
  intro hz
  exact hξ (by simp [angularChartSymbol, hz])
theorem contDiff_angularChartSymbol {d : ℕ} {b : Space (d + 1) → ℂ}
    (hb : ContDiff ℝ ∞ b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) {γ : ℝ} (hγ : γ ≠ 0) (c : Fin d → ℝ) :
    ContDiff ℝ ∞ (angularChartSymbol b γ c) := by
  have hb0 : ∀ ξ, ξ 0 = 0 → b ξ = 0 := by
    intro ξ hξ
    by_contra hn
    have h := hs ξ (subset_tsupport b hn)
    rw [hξ] at h
    linarith
  rw [angularChartSymbol_eq_rescaled hb0 hγ c]
  exact (contDiff_angularChartFamily hb ha hs).comp
    (contDiff_const.prodMk (angularChartLinearEquiv γ hγ c).symm.contDiff)
theorem angularChartSymbol_narrow {d : ℕ} {b : Space (d + 1) → ℂ}
    {a : ℝ} (ha : 0 < a) (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0)
    {γ : ℝ} (hγ : 0 < γ) (c : Fin d → ℝ) {ξ : Space (d + 1)}
    (hξ : ξ ∈ tsupport (angularChartSymbol b γ c)) (i : Fin d) :
    |ξ i.succ - c i * ξ 0| ≤ γ * ξ 0 := by
  have hclosed : IsClosed {η : Space (d + 1) | |η i.succ - c i * η 0| ≤ γ * η 0} := by
    apply isClosed_le <;> fun_prop
  apply closure_minimal ?_ hclosed hξ
  intro η hη
  have hb : b η ≠ 0 := by intro hz; exact hη (by simp [angularChartSymbol, hz])
  have h0 : 0 < η 0 := ha.trans_le (hs η (subset_tsupport b hb))
  have hg : angularGridProduct (fun j => (η j.succ / η 0 - c j) / γ) ≠ 0 := by
    intro hz
    exact hη (by simp [angularChartSymbol, hz])
  have hi := (angularGridProduct_ne_zero hg i).le
  rw [abs_div, abs_of_pos hγ] at hi
  have hi' : |η i.succ / η 0 - c i| ≤ γ := by
    simpa only [one_mul] using (div_le_iff₀ hγ).mp hi
  have he : η i.succ - c i * η 0 = (η i.succ / η 0 - c i) * η 0 := by
    field_simp
  change |η i.succ - c i * η 0| ≤ γ * η 0
  rw [he, abs_mul, abs_of_pos h0]
  exact mul_le_mul_of_nonneg_right hi' h0.le
theorem sum_angularChartSymbol {d : ℕ} {b : Space (d + 1) → ℂ}
    {R γ : ℝ} (hγ : 0 < γ)
    (hR : ∀ ξ ∈ tsupport b, ∀ i : Fin d, |ξ i.succ / ξ 0| ≤ R) :
    (fun ξ => ∑ k : Fin d → Fin (2 * angularGridSize R γ + 1),
      angularChartSymbol b γ (angularGridCenter R γ k) ξ) = b := by
  funext ξ
  by_cases hb : b ξ = 0
  · simp [angularChartSymbol, hb]
  · have hp := sum_scaled_angularGridProduct hγ (hR ξ (subset_tsupport b hb))
    simp only [angularChartSymbol, ← Finset.mul_sum, ← Complex.ofReal_sum]
    rw [hp]
    simp
theorem angular_chart_partition {d : ℕ} {b : Space (d + 1) → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) :
    ∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧ ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
      let I := Fin d → Fin (2 * angularGridSize R γ + 1)
      let φ := fun k : I => angularChartSymbol b γ (angularGridCenter R γ k)
      (Fintype.card I : ℝ) ≤ ((2 * R + 3) / γ) ^ d ∧
      (fun ξ => ∑ k : I, φ k ξ) = b ∧
      ∀ k : I, ContDiff ℝ ∞ (φ k) ∧ HasCompactSupport (φ k) ∧
        tsupport (φ k) ⊆ tsupport b ∧
        MeasureTheory.eLpNorm (𝓕⁻ (φ k)) 1 MeasureTheory.volume ≤ ENNReal.ofReal C ∧
        ∀ ξ ∈ tsupport (φ k), ∀ i : Fin d,
          |ξ i.succ - angularGridCenter R γ k i * ξ 0| ≤ γ * ξ 0 := by
  obtain ⟨B, hB, hbound⟩ := hc.isBounded.exists_pos_norm_le
  let R := B / a
  have hR : 0 ≤ R := div_nonneg hB.le ha.le
  have hratio : ∀ ξ ∈ tsupport b, ∀ i : Fin d, |ξ i.succ / ξ 0| ≤ R := by
    intro ξ hξ i
    have h0 : 0 < ξ 0 := ha.trans_le (hs ξ hξ)
    have hi : |ξ i.succ| ≤ B := by
      have hh : |ξ i.succ| ≤ ‖ξ‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ i.succ
      exact hh.trans (hbound ξ hξ)
    rw [abs_div, abs_of_pos h0]
    exact div_le_div₀ hB.le hi ha (hs ξ hξ)
  obtain ⟨C, hC, hk⟩ := uniform_angularChartSymbol_kernel hb hc ha hs (R + 1)
  refine ⟨R, C, hR, hC, ?_⟩
  intro γ hγ hγ1
  dsimp only
  refine ⟨angularGrid_card_bound d hR hγ hγ1, sum_angularChartSymbol hγ hratio, ?_⟩
  intro k
  refine ⟨contDiff_angularChartSymbol hb ha hs hγ.ne' _, ?_,
    tsupport_angularChartSymbol_subset _ _ _, ?_, ?_⟩
  · exact hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_angularChartSymbol_subset _ _ _)
  · exact hk γ hγ hγ1 _ (angularGridCenter_bound hR hγ hγ1 k)
  · exact fun ξ hξ i => angularChartSymbol_narrow ha hs hγ _ hξ i
end OAI.Analysis.Fourier.WavePackets
end
end

-- OAI.Analysis.Fourier.WavePackets.AngularAtlas
section
open OAI.Analysis.Fourier.Wave
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets
open Set
open scoped ContDiff Manifold
theorem exists_positive_axis_rotation {d : ℕ} {ξ : Space (d + 1)} (hξ : ξ ≠ 0) :
    ∃ R : Space (d + 1) ≃ₗᵢ[ℝ] Space (d + 1), 0 < R ξ 0 := by
  let e : Space (d + 1) := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hn : ‖ξ‖ = ‖‖ξ‖ • e‖ := by simp [norm_smul, he]
  let R : Space (d + 1) ≃ₗᵢ[ℝ] Space (d + 1) :=
    Submodule.reflection (ℝ ∙ (ξ - ‖ξ‖ • e))ᗮ
  have hR : R ξ = ‖ξ‖ • e := Submodule.reflection_sub hn
  refine ⟨R, ?_⟩
  rw [hR]
  simpa [e] using norm_pos_iff.mpr hξ
theorem compact_positive_axis_lower_bound {d : ℕ} {b : Space (d + 1) → ℂ}
    (hc : HasCompactSupport b) (hp : ∀ ξ ∈ tsupport b, 0 < ξ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ ξ ∈ tsupport b, a ≤ ξ 0 := by
  by_cases hne : (tsupport b).Nonempty
  · have he : ContinuousOn (fun ξ : Space (d + 1) => ξ 0) (tsupport b) := by
      fun_prop
    obtain ⟨ξ, hξ, hmin⟩ := hc.exists_isMinOn hne he
    exact ⟨ξ 0, hp ξ hξ, hmin⟩
  · exact ⟨1, by norm_num, fun ξ hξ => False.elim (hne ⟨ξ, hξ⟩)⟩
theorem finite_angular_atlas {d : ℕ} {φ : Space (d + 1) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ s : Finset (Space (d + 1) ≃ₗᵢ[ℝ] Space (d + 1)),
      ∃ b : s → Space (d + 1) → ℂ, ∃ a : s → ℝ,
      (∀ i, ContDiff ℝ ∞ (b i) ∧ HasCompactSupport (b i) ∧
        0 < a i ∧ (∀ ξ ∈ tsupport (b i), a i ≤ ξ 0) ∧
        tsupport (fun ξ => b i (i.val ξ)) ⊆ tsupport φ) ∧
      (fun ξ => ∑ i : s, b i (i.val ξ)) = φ := by
  classical
  let U := fun R : Space (d + 1) ≃ₗᵢ[ℝ] Space (d + 1) =>
    {ξ : Space (d + 1) | 0 < R ξ 0}
  have hU : ∀ R, IsOpen (U R) := by
    intro R
    apply isOpen_lt continuous_const
    fun_prop
  have hcover : tsupport φ ⊆ ⋃ R, U R := by
    intro ξ hξ
    have hξ0 : ξ ≠ 0 := by intro he; subst ξ; exact hz hξ
    obtain ⟨R, hR⟩ := exists_positive_axis_rotation hξ0
    exact mem_iUnion.mpr ⟨R, hR⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover U hU hcover
  have hcover' : tsupport φ ⊆ ⋃ i : s, U i.val := by
    intro ξ hξ
    obtain ⟨R, hR⟩ := mem_iUnion.mp (hs hξ)
    obtain ⟨hRs, hξR⟩ := mem_iUnion.mp hR
    exact mem_iUnion.mpr ⟨⟨R, hRs⟩, hξR⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ, Space (d + 1))) (isClosed_tsupport φ) (fun i : s => U i.val)
      (fun i => hU i.val) hcover'
  let g : s → Space (d + 1) → ℂ := fun i ξ => (ρ i ξ : ℂ) * φ ξ
  have hg (i : s) : ContDiff ℝ ∞ (g i) := by
    have hr : ContDiff ℝ ∞ (ρ i) := contMDiff_iff_contDiff.mp (ρ i).contMDiff
    exact (Complex.ofRealCLM.contDiff.comp hr).mul hφ
  have hgc (i : s) : HasCompactSupport (g i) := hc.mul_left
  have hgφ (i : s) : tsupport (g i) ⊆ tsupport φ := tsupport_mul_subset_right
  have hgU (i : s) : tsupport (g i) ⊆ U i.val := by
    apply Set.Subset.trans ?_ (hρ i)
    apply closure_minimal _ (isClosed_tsupport (ρ i))
    intro ξ hξ
    apply subset_tsupport (ρ i)
    intro he
    exact hξ (by simp [g, he])
  let b : s → Space (d + 1) → ℂ := fun i ξ => g i (i.val.symm ξ)
  have hbc (i : s) : HasCompactSupport (b i) :=
    (hgc i).comp_homeomorph i.val.symm.toHomeomorph
  have hbp (i : s) : ∀ ξ ∈ tsupport (b i), 0 < ξ 0 := by
    intro ξ hξ
    have hgξ : i.val.symm ξ ∈ tsupport (g i) :=
      tsupport_comp_subset_preimage (g i) i.val.symm.continuous hξ
    have ht := hgU i hgξ
    change 0 < i.val (i.val.symm ξ) 0 at ht
    simpa using ht
  choose a ha hamin using fun i => compact_positive_axis_lower_bound (hbc i) (hbp i)
  refine ⟨s, b, a, ?_, ?_⟩
  · intro i
    refine ⟨(hg i).comp i.val.symm.contDiff, hbc i, ha i, hamin i, ?_⟩
    have he : (fun ξ => b i (i.val ξ)) = g i := by
      funext ξ
      simp [b]
    rw [he]
    exact hgφ i
  · funext ξ
    change (∑ i : s, (ρ i (i.val.symm (i.val ξ)) : ℂ) *
      φ (i.val.symm (i.val ξ))) = φ ξ
    simp only [LinearIsometryEquiv.symm_apply_apply, ← Finset.sum_mul, ← Complex.ofReal_sum]
    by_cases hξ : φ ξ = 0
    · simp [hξ]
    · have hsum := ρ.sum_eq_one (subset_tsupport φ hξ)
      rw [finsum_eq_sum_of_fintype] at hsum
      rw [hsum]
      simp
end OAI.Analysis.Fourier.WavePackets
end
end

-- OAI.Analysis.Fourier.WavePackets.AngularCompact
section
open OAI.Analysis.Fourier.Wave
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets
open Set _root_.MeasureTheory
open scoped ContDiff ENNReal FourierTransform
theorem eLpNorm_fourierInv_comp_smooth {n : ℕ} {φ : Space n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (R : Space n ≃L[ℝ] Space n) :
    eLpNorm (𝓕⁻ (φ ∘ R)) 1 volume = eLpNorm (𝓕⁻ φ) 1 volume := by
  apply eLpNorm_fourierInv_comp_linearEquiv R φ
  have he : ((𝓕⁻ (hc.toSchwartzMap hφ) : SchwartzMap (Space n) ℂ) : Space n → ℂ) =
      𝓕⁻ φ := by rw [SchwartzMap.fourierInv_coe]; rfl
  rw [← he]
  exact (𝓕⁻ (hc.toSchwartzMap hφ)).continuous.measurable
end OAI.Analysis.Fourier.WavePackets
end
end

-- OAI.Analysis.Fourier.SquareFunction.Shell
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction
def spatialPhase {n : ℕ} (x ξ : Space n) : ℂ :=
  Complex.exp ((2 * Real.pi * inner ℝ ξ x : ℝ) * Complex.I)
@[simp] theorem norm_spatialPhase {n : ℕ} (x ξ : Space n) : ‖spatialPhase x ξ‖ = 1 := by
  simp [spatialPhase, Complex.norm_exp]
theorem continuous_spatialPhase {n : ℕ} (x : Space n) : Continuous (spatialPhase x) := by
  unfold spatialPhase
  fun_prop
end OAI.Analysis.Fourier.SquareFunction
end
end

-- OAI.Analysis.Fourier.SquareFunction.KernelHilbert
section
open OAI.Analysis.Fourier.Wave
namespace OAI.Analysis.Fourier.SquareFunction
open _root_.MeasureTheory FourierTransform
theorem integrable_spatialPhase_smul {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (x : Space n)
    {a : Space n → E} (ha : Integrable a) :
    Integrable (fun ξ => spatialPhase x ξ • a ξ) := by
  have hmeas : AEStronglyMeasurable (fun ξ => spatialPhase x ξ • a ξ) volume :=
    (continuous_spatialPhase x).aestronglyMeasurable.smul ha.aestronglyMeasurable
  have hn (ξ : Space n) : ‖spatialPhase x ξ • a ξ‖ ≤ ‖a ξ‖ := by
    rw [norm_smul, norm_spatialPhase, one_mul]
  exact ha.mono hmeas (Filter.Eventually.of_forall hn)
theorem fourierInv_eq_spatialPhase_smul {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (a : Space n → E) (x : Space n) :
    𝓕⁻ a x = ∫ ξ, spatialPhase x ξ • a ξ := by
  rw [Real.fourierInv_eq']
  rfl
end OAI.Analysis.Fourier.SquareFunction
end

-- OAI.Analysis.Fourier.BochnerRiesz.FiniteFourier
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory FourierTransform
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz
theorem fourierInv_finset_sum {n : ℕ} {I : Type*} (s : Finset I) (a : I → Space n → ℂ)
    (ha : ∀ i ∈ s, Integrable (a i)) :
    𝓕⁻ (fun ξ ↦ ∑ i ∈ s, a i ξ) = fun x ↦ ∑ i ∈ s, 𝓕⁻ (a i) x := by
  funext x
  simp only [OAI.Analysis.Fourier.SquareFunction.fourierInv_eq_spatialPhase_smul, Finset.smul_sum]
  exact integral_finsetSum s (fun i hi ↦ OAI.Analysis.Fourier.SquareFunction.integrable_spatialPhase_smul x (ha i hi))
end OAI.Analysis.Fourier.BochnerRiesz
end
end

-- OAI.Analysis.Fourier.WavePackets.Half.Wave.CapPhase
section
open OAI.Analysis.Fourier.Wave
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets
open Set Filter
open scoped ContDiff Topology RealInnerProductSpace
def capAxis {d : ℕ} (c : Fin d → ℝ) : Space (d+1) :=
  WithLp.toLp 2 (Fin.cases 1 c)
def capTransverse {d : ℕ} (ξ : Space (d+1)) : Space (d+1) :=
  WithLp.toLp 2 (Fin.cases 0 (fun i => ξ i.succ))
@[simp] theorem capAxis_zero {d : ℕ} (c : Fin d → ℝ) : capAxis c 0 = 1 := rfl
@[simp] theorem capTransverse_zero {d : ℕ} (ξ : Space (d+1)) : capTransverse ξ 0 = 0 := rfl
@[simp] theorem capAxis_succ {d : ℕ} (c : Fin d → ℝ) (i : Fin d) : capAxis c i.succ = c i := by
  simp [capAxis]
@[simp] theorem capTransverse_succ {d : ℕ} (ξ : Space (d+1)) (i : Fin d) :
    capTransverse ξ i.succ = ξ i.succ := by simp [capTransverse]
theorem capAxis_ne_zero {d : ℕ} (c : Fin d → ℝ) : capAxis c ≠ 0 := by
  intro h
  have := congrArg (fun z : Space (d+1) => z 0) h
  simp at this
theorem angularChartRescale_eq_axis {d : ℕ} (γ : ℝ) (c : Fin d → ℝ) (ξ : Space (d+1)) :
    angularChartRescale γ c ξ = (ξ 0) • capAxis c + γ • capTransverse ξ := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [angularChartRescale_succ,PiLp.add_apply,PiLp.smul_apply,
      capAxis_succ,capTransverse_succ,smul_eq_mul]
    ring
def capLinearPhase {d : ℕ} (γ : ℝ) (c : Fin d → ℝ) (ξ : Space (d+1)) : ℝ :=
  (ξ 0)*‖capAxis c‖ + γ*(inner ℝ (capAxis c) (capTransverse ξ)/‖capAxis c‖)
def capPhaseRemainder {d : ℕ} (γ : ℝ) (c : Fin d → ℝ) (ξ : Space (d+1)) : ℝ :=
  let r := (ξ 0)*‖capAxis c‖
  let q := inner ℝ (capAxis c) (capTransverse ξ)/‖capAxis c‖
  let D := ‖angularChartRescale γ c ξ‖+r
  ‖capTransverse ξ‖^2/D-q*(2*r*q+γ*‖capTransverse ξ‖^2)/D^2
private theorem quadratic_remainder_identity (N r q b γ : ℝ)
    (hD : N+r ≠ 0) (hsq : N^2 = r^2+2*γ*r*q+γ^2*b) :
    N-r-γ*q = γ^2*(b/(N+r)-q*(2*r*q+γ*b)/(N+r)^2) := by
  field_simp
  linear_combination (N+r-γ*q)*hsq
theorem norm_angularChartRescale_expansion {d : ℕ} (γ : ℝ) (c : Fin d → ℝ)
    (ξ : Space (d+1)) :
    ‖angularChartRescale γ c ξ‖^2 = ((ξ 0)*‖capAxis c‖)^2 +
      2*γ*((ξ 0)*‖capAxis c‖)*(inner ℝ (capAxis c) (capTransverse ξ)/‖capAxis c‖) +
      γ^2*‖capTransverse ξ‖^2 := by
  rw [angularChartRescale_eq_axis, norm_add_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,real_inner_smul_left,real_inner_smul_right,
    mul_pow,sq_abs]
  have hc : ‖capAxis c‖ ≠ 0 := norm_ne_zero_iff.mpr (capAxis_ne_zero c)
  field_simp
theorem capPhaseRemainder_identity {d : ℕ} (γ : ℝ) (c : Fin d → ℝ)
    (ξ : Space (d+1)) (hξ : 0 < ξ 0) :
    ‖angularChartRescale γ c ξ‖-capLinearPhase γ c ξ = γ^2*capPhaseRemainder γ c ξ := by
  have hr : 0 < (ξ 0)*‖capAxis c‖ := mul_pos hξ (norm_pos_iff.mpr (capAxis_ne_zero c))
  have hD : ‖angularChartRescale γ c ξ‖+(ξ 0)*‖capAxis c‖ ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (norm_nonneg _) hr)
  simpa only [capLinearPhase,capPhaseRemainder,sub_add_eq_sub_sub] using
    quadratic_remainder_identity _ _ _ _ γ hD (norm_angularChartRescale_expansion γ c ξ)
theorem contDiff_capAxis (d : ℕ) : ContDiff ℝ ∞ (@capAxis d) := by
  apply (contDiff_piLp 2).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : Fin d → ℝ => (1 : ℝ)))
  · simpa using (contDiff_apply ℝ ℝ j : ContDiff ℝ ∞ (fun c : Fin d → ℝ => c j))
theorem contDiff_capTransverse (d : ℕ) : ContDiff ℝ ∞ (@capTransverse d) := by
  apply (contDiff_piLp 2).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : Space (d+1) => (0 : ℝ)))
  · simpa using (show ContDiff ℝ ∞ (fun ξ : Space (d+1) => ξ j.succ) by fun_prop)
end OAI.Analysis.Fourier.WavePackets
end
end

-- OAI.Analysis.Fourier.WavePackets.Half.Wave.CapSmooth
section
open OAI.Analysis.Fourier.Wave
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets
open Set Filter
open scoped ContDiff Topology
theorem contDiffAt_capPhaseRemainder {d : ℕ}
    (p : (ℝ × (Fin d → ℝ)) × Space (d+1)) (hp : 0 < p.2 0) :
    ContDiffAt ℝ ∞ (fun q : (ℝ × (Fin d → ℝ)) × Space (d+1) =>
      capPhaseRemainder q.1.1 q.1.2 q.2) p := by
  have haxis : ContDiff ℝ ∞ (fun q : (ℝ × (Fin d → ℝ)) × Space (d+1) => capAxis q.1.2) :=
    (contDiff_capAxis d).comp contDiff_fst.snd
  have haxisnorm := haxis.contDiffAt.norm ℝ (capAxis_ne_zero p.1.2)
  have hzero : ContDiff ℝ ∞ (fun q : (ℝ × (Fin d → ℝ)) × Space (d+1) => q.2 0) := by
    fun_prop
  have htrans := (contDiff_capTransverse d).comp
    (contDiff_snd : ContDiff ℝ ∞ (fun q : (ℝ × (Fin d → ℝ)) × Space (d+1) => q.2))
  have htranssq := htrans.norm_sq ℝ
  have hq := (haxis.contDiffAt.inner ℝ htrans.contDiffAt).div haxisnorm
    (norm_ne_zero_iff.mpr (capAxis_ne_zero p.1.2))
  have hneq : angularChartRescale p.1.1 p.1.2 p.2 ≠ 0 := by
    intro he
    have := congrArg (fun z : Space (d+1) => z 0) he
    simpa only [angularChartRescale_zero,PiLp.zero_apply] using hp.ne' this
  have hN := (contDiff_angularChartRescale d).contDiffAt.norm ℝ hneq
  have hr := hzero.contDiffAt.mul haxisnorm
  have hD := hN.add hr
  have hD0 : ‖angularChartRescale p.1.1 p.1.2 p.2‖+p.2 0*‖capAxis p.1.2‖ ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (norm_nonneg _)
      (mul_pos hp (norm_pos_iff.mpr (capAxis_ne_zero p.1.2))))
  unfold capPhaseRemainder
  exact (htranssq.contDiffAt.div hD hD0).sub
    ((hq.mul (((contDiffAt_const.mul hr).mul hq).add
      (contDiffAt_fst.fst.mul htranssq.contDiffAt))).div (hD.pow 2) (pow_ne_zero 2 hD0))
def capWaveFamily {d : ℕ} (b : Space (d+1) → ℂ)
    (p : (ℝ × (ℝ × (Fin d → ℝ))) × Space (d+1)) : ℂ :=
  angularChartFamily b (p.1.2,p.2) *
    Complex.exp (-Complex.I * (p.1.1*capPhaseRemainder p.1.2.1 p.1.2.2 p.2 : ℝ))
theorem contDiff_capWaveFamily {d : ℕ} {b : Space (d+1) → ℂ}
    (hb : ContDiff ℝ ∞ b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) : ContDiff ℝ ∞ (capWaveFamily b) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have harg : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × (Fin d → ℝ))) × Space (d+1) =>
      (q.1.2,q.2)) := contDiff_fst.snd.prodMk contDiff_snd
  by_cases hp : 0 < p.2 0
  · have hphase := (contDiffAt_capPhaseRemainder (p.1.2,p.2) hp).comp p harg.contDiffAt
    apply ((contDiff_angularChartFamily hb ha hs).comp harg).contDiffAt.mul
    exact (contDiffAt_const.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiffAt_fst.fst.mul hphase))).cexp
  · have hnot : angularChartRescale p.1.2.1 p.1.2.2 p.2 ∉ tsupport b := by
      intro hx
      have := hs _ hx
      rw [angularChartRescale_zero] at this
      exact hp (ha.trans_le this)
    have he := (notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto
      ((contDiff_angularChartRescale d).comp harg).continuous.continuousAt
    apply (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _ : (ℝ × (ℝ × (Fin d → ℝ))) × Space (d+1) => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [he] with q hq
    change b (angularChartRescale q.1.2.1 q.1.2.2 q.2) = 0 at hq
    simp only [capWaveFamily,angularChartFamily,hq,zero_mul]
end OAI.Analysis.Fourier.WavePackets
end
end

-- OAI.Analysis.Fourier.WavePackets.Half.Wave.Modulation
section
open OAI.Analysis.Fourier.Wave
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets
open Set Filter _root_.MeasureTheory InnerProductSpace
open scoped Topology ContDiff FourierTransform RealInnerProductSpace
theorem angularInverse_modulate {n : ℕ} (φ : Space n → ℂ) (v x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => Complex.exp (-Complex.I*(inner ℝ v ξ : ℝ))*φ ξ) x =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ (x-v) := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.angularInverse
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [← mul_assoc,← Complex.exp_add]
  congr 2
  simp only [inner_sub_left,Complex.ofReal_sub]
  ring
theorem eLpNorm_angularInverse_modulate {n : ℕ} {φ : Space n → ℂ}
    (hφ : Integrable φ) (v : Space n) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => Complex.exp (-Complex.I*(inner ℝ v ξ : ℝ))*φ ξ))
      1 volume = eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ) 1 volume := by
  have he : OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => Complex.exp (-Complex.I*(inner ℝ v ξ : ℝ))*φ ξ) =
      fun x => OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ (x-v) := funext (angularInverse_modulate φ v)
  rw [he]
  exact eLpNorm_comp_measurePreserving
    (OAI.Analysis.Fourier.BochnerRiesz.continuous_angularInverse hφ).aestronglyMeasurable
    (measurePreserving_sub_right volume v)
theorem eLpNorm_fourierInv_modulate {n : ℕ} {φ : Space n → ℂ}
    (hφ : Integrable φ) (v : Space n) :
    eLpNorm (𝓕⁻ (fun ξ => Complex.exp (-Complex.I*(inner ℝ v ξ : ℝ))*φ ξ))
      1 volume = eLpNorm (𝓕⁻ φ) 1 volume := by
  have hm : Integrable (fun ξ => Complex.exp (-Complex.I*(inner ℝ v ξ : ℝ))*φ ξ) := by
    apply hφ.norm.mono'
      (((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul hφ.aestronglyMeasurable)
    filter_upwards [] with ξ
    simp [Complex.norm_exp]
  rw [eLpNorm_fourierInv_eq_angularInverse hm,eLpNorm_fourierInv_eq_angularInverse hφ]
  exact eLpNorm_angularInverse_modulate hφ v
theorem capTransverse_add {d : ℕ} (x y : Space (d+1)) :
    capTransverse (x+y) = capTransverse x+capTransverse y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp
theorem capTransverse_smul {d : ℕ} (c : ℝ) (x : Space (d+1)) :
    capTransverse (c • x) = c • capTransverse x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp
def capLinearPhaseLinear {d : ℕ} (γ : ℝ) (c : Fin d → ℝ) : Space (d+1) →ₗ[ℝ] ℝ where
  toFun := capLinearPhase γ c
  map_add' x y := by
    simp only [capLinearPhase,PiLp.add_apply,capTransverse_add,inner_add_right,add_div]
    ring
  map_smul' a x := by
    simp only [capLinearPhase,PiLp.smul_apply,capTransverse_smul,real_inner_smul_right,
      smul_eq_mul,RingHom.id_apply]
    ring
def capLinearPhaseCLM {d : ℕ} (γ : ℝ) (c : Fin d → ℝ) : Space (d+1) →L[ℝ] ℝ :=
  (capLinearPhaseLinear γ c).toContinuousLinearMap
theorem eLpNorm_fourierInv_cap_modulate {d : ℕ} {φ : Space (d+1) → ℂ}
    (hφ : Integrable φ) (t γ : ℝ) (c : Fin d → ℝ) :
    eLpNorm (𝓕⁻ (fun ξ => Complex.exp (-Complex.I*(t*capLinearPhase γ c ξ : ℝ))*φ ξ))
      1 volume = eLpNorm (𝓕⁻ φ) 1 volume := by
  let v := (toDual ℝ (Space (d+1))).symm (t • capLinearPhaseCLM γ c)
  have hv (ξ : Space (d+1)) : inner ℝ v ξ = t*capLinearPhase γ c ξ := toDual_symm_apply
  simpa only [hv] using eLpNorm_fourierInv_modulate hφ v
end OAI.Analysis.Fourier.WavePackets
end
end

-- OAI.Analysis.Fourier.WavePackets.Half.Wave.CapKernel
section
open OAI.Analysis.Fourier.Wave
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets
open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology FourierTransform ENNReal
theorem capWaveFamily_common_support {d : ℕ} {b : Space (d+1) → ℂ}
    {B : ℝ} (hs : ∀ ξ ∈ tsupport b, ξ 0 ≠ 0 ∧ |ξ 0| ≤ B) :
    tsupport (capWaveFamily b) ⊆ Set.univ ×ˢ
      (WithLp.toLp 2 '' Set.Icc (fun _ : Fin (d+1) => -B) (fun _ => B)) := by
  intro p hp
  have hx : p ∈ tsupport (fun q : (ℝ × (ℝ × (Fin d → ℝ))) × Space (d+1) =>
      angularChartFamily b (q.1.2,q.2)) := tsupport_mul_subset_left hp
  have hpre := tsupport_comp_subset_preimage (angularChartFamily b)
    (continuous_fst.snd.prodMk continuous_snd) hx
  exact ⟨trivial,(angularChartFamily_common_support hs hpre).2⟩
theorem waveAmplitude_chart_rescale {d : ℕ} {b : Space (d+1) → ℂ}
    {a : ℝ} (ha : 0 < a) (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0)
    {γ : ℝ} (hγ : γ ≠ 0) (c : Fin d → ℝ) (T : ℝ) :
    (waveAmplitude (angularChartSymbol b γ c) (γ^2) T ∘ angularChartLinearEquiv γ hγ c) =
      fun ξ => Complex.exp (-Complex.I*((T/γ^2)*capLinearPhase γ c ξ : ℝ))*
        capWaveFamily b ((T,γ,c),ξ) := by
  have hb0 : ∀ ξ, ξ 0 = 0 → b ξ = 0 := by
    intro ξ hξ
    by_contra hh
    have := hs ξ (subset_tsupport b hh)
    rw [hξ] at this
    linarith
  funext ξ
  have hsym : angularChartSymbol b γ c (angularChartLinearEquiv γ hγ c ξ) =
      angularChartFamily b ((γ,c),ξ) := by
    rw [angularChartSymbol_eq_rescaled hb0 hγ]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  simp only [Function.comp_apply,waveAmplitude,hsym,capWaveFamily]
  by_cases hbξ : b (angularChartRescale γ c ξ) = 0
  · simp [angularChartFamily,hbξ]
  · have hξ : 0 < ξ 0 := by
      have hx := hs (angularChartRescale γ c ξ) (subset_tsupport b hbξ)
      simpa only [angularChartRescale_zero] using ha.trans_le hx
    have hphase : (T/γ^2)*‖angularChartRescale γ c ξ‖ =
        (T/γ^2)*capLinearPhase γ c ξ + T*capPhaseRemainder γ c ξ := by
      have he := capPhaseRemainder_identity γ c ξ hξ
      field_simp
      linear_combination T*he
    change Complex.exp (-Complex.I*((T/γ^2)*‖angularChartRescale γ c ξ‖ : ℝ))*_ = _
    rw [hphase,Complex.ofReal_add,mul_add,Complex.exp_add]
    ring
theorem uniform_wave_angularChart_kernel {d : ℕ} {b : Space (d+1) → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
      ∀ c : Fin d → ℝ, (∀ i, |c i| ≤ R) → ∀ T ∈ Icc (1 : ℝ) 2,
      eLpNorm (𝓕⁻ (waveAmplitude (angularChartSymbol b γ c) (γ^2) T)) 1 volume ≤
        ENNReal.ofReal C := by
  obtain ⟨B,hB,hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hslab : ∀ ξ ∈ tsupport b, ξ 0 ≠ 0 ∧ |ξ 0| ≤ B := by
    intro ξ hξ
    exact ⟨ne_of_gt (ha.trans_le (hs ξ hξ)),
      (show |ξ 0| ≤ ‖ξ‖ from PiLp.norm_apply_le ξ 0).trans (hbound ξ hξ)⟩
  let K : Set (ℝ × (ℝ × (Fin d → ℝ))) := Icc 1 2 ×ˢ (Icc 0 1 ×ˢ Icc (fun _ => -R) (fun _ => R))
  let S : Set (Space (d+1)) := WithLp.toLp 2 '' Icc (fun _ : Fin (d+1) => -B) (fun _ => B)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hS : IsCompact S := isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  have hsupp := capWaveFamily_common_support hslab
  have hfamily := contDiff_capWaveFamily hb ha hs
  obtain ⟨C,hC,hkernel⟩ := uniform_linearly_rescaled_inverse_kernel_bound hK hS hfamily hsupp
  refine ⟨C,hC,?_⟩
  intro γ hγ hγ1 c hcR T hT
  let A := angularChartLinearEquiv γ hγ.ne' c
  let f : Space (d+1) → ℂ := fun ξ => capWaveFamily b ((T,γ,c),ξ)
  have hf : ContDiff ℝ ∞ f := hfamily.comp (contDiff_const.prodMk contDiff_id)
  have hfc : HasCompactSupport f := by
    apply hS.of_isClosed_subset (isClosed_tsupport _)
    intro ξ hξ
    exact (hsupp (tsupport_comp_subset_preimage (capWaveFamily b)
      (continuous_const.prodMk continuous_id) hξ)).2
  have hfi : Integrable f volume := hf.continuous.integrable_of_hasCompactSupport hfc
  have hbγ := contDiff_angularChartSymbol hb ha hs hγ.ne' c
  have hcγ := hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_angularChartSymbol_subset b γ c)
  have hzγ : (0 : Space (d+1)) ∉ tsupport (angularChartSymbol b γ c) := by
    intro h
    have := hs 0 (tsupport_angularChartSymbol_subset b γ c h)
    simp only [PiLp.zero_apply] at this
    linarith
  rw [← eLpNorm_fourierInv_comp_smooth (contDiff_waveAmplitude hbγ hzγ (γ^2) T)
    (hasCompactSupport_waveAmplitude hcγ (γ^2) T) A,
    waveAmplitude_chart_rescale ha hs hγ.ne' c T,
    eLpNorm_fourierInv_cap_modulate hfi]
  simpa only [ContinuousLinearEquiv.refl_apply] using hkernel (T,γ,c)
    ⟨hT,⟨hγ.le,hγ1⟩,⟨fun i => (abs_le.mp (hcR i)).1,fun i => (abs_le.mp (hcR i)).2⟩⟩
    (ContinuousLinearEquiv.refl ℝ (Space (d+1)))
end OAI.Analysis.Fourier.WavePackets
end
end

-- OAI.Analysis.Fourier.WavePackets.Half.Wave.ChartSum
section
open OAI.Analysis.Fourier.Wave
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets
open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology FourierTransform ENNReal
theorem fourierInv_sum_eLpNorm_le {n : ℕ} {I : Type*} [Fintype I]
    (f : I → Space n → ℂ) (hf : ∀ i, Integrable (f i)) :
    eLpNorm (𝓕⁻ (fun ξ => ∑ i, f i ξ)) 1 volume ≤
      ∑ i, eLpNorm (𝓕⁻ (f i)) 1 volume := by
  classical
  have he := OAI.Analysis.Fourier.BochnerRiesz.fourierInv_finset_sum Finset.univ f (fun i _ => hf i)
  rw [he]
  simpa only [Finset.sum_apply, Finset.sum_fn] using
    (eLpNorm_sum_le (p := (1 : ℝ≥0∞)) (μ := volume) (f := fun i => 𝓕⁻ (f i))
      (s := Finset.univ) (fun i _ => by
        have H : Continuous (𝓕 (f i)) := VectorFourier.fourierIntegral_continuous
          Real.continuous_fourierChar (innerSL ℝ).continuous₂ (hf i)
        exact (show Continuous (𝓕⁻ (f i)) by
          simpa only [show 𝓕⁻ (f i) = (𝓕 (f i)) ∘ Neg.neg from funext (Real.fourierInv_eq_fourier_neg _)] using H.comp continuous_neg).aestronglyMeasurable) le_rfl)
theorem waveAmplitude_integrable {n : ℕ} {b : Space n → ℂ}
    (hb : Continuous b) (hc : HasCompactSupport b) (h T : ℝ) :
    Integrable (waveAmplitude b h T) := by
  apply Continuous.integrable_of_hasCompactSupport _ (hasCompactSupport_waveAmplitude hc h T)
  unfold waveAmplitude
  fun_prop
theorem uniform_wave_positive_chart_kernel {d : ℕ} {b : Space (d+1) → ℂ}
    (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b) {a : ℝ} (ha : 0 < a)
    (hs : ∀ ξ ∈ tsupport b, a ≤ ξ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ T ∈ Icc (1 : ℝ) 2,
      eLpNorm (𝓕⁻ (waveAmplitude b (γ^2) T)) 1 volume ≤ ENNReal.ofReal (C*(γ⁻¹)^d) := by
  classical
  obtain ⟨R,C₀,hR,hC₀,hpart⟩ := angular_chart_partition hb hc ha hs
  obtain ⟨C,hC,hkernel⟩ := uniform_wave_angularChart_kernel hb hc ha hs (R+1)
  refine ⟨(2*R+3)^d*C,mul_nonneg (pow_nonneg (by linarith) d) hC,?_⟩
  intro γ hγ hγ1 T hT
  let I := Fin d → Fin (2*angularGridSize R γ+1)
  let f : I → Space (d+1) → ℂ := fun k =>
    waveAmplitude (angularChartSymbol b γ (angularGridCenter R γ k)) (γ^2) T
  have hd := hpart γ hγ hγ1
  have hfi : ∀ k, Integrable (f k) := fun k =>
    waveAmplitude_integrable (hd.2.2 k).1.continuous (hd.2.2 k).2.1 (γ^2) T
  have he : waveAmplitude b (γ^2) T = fun ξ => ∑ k, f k ξ := by
    funext ξ
    simp only [f,waveAmplitude,← Finset.mul_sum]
    rw [congrFun hd.2.1 ξ]
  rw [he]
  calc
    _ ≤ ∑ k : I, eLpNorm (𝓕⁻ (f k)) 1 volume := fourierInv_sum_eLpNorm_le f hfi
    _ ≤ ∑ _k : I, ENNReal.ofReal C := Finset.sum_le_sum (fun k _ =>
      hkernel γ hγ hγ1 _ (angularGridCenter_bound hR hγ hγ1 k) T hT)
    _ = ENNReal.ofReal ((Fintype.card I : ℝ)*C) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp
    _ ≤ ENNReal.ofReal (((2*R+3)/γ)^d*C) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hd.1 hC)
    _ = ENNReal.ofReal (((2*R+3)^d*C)*(γ⁻¹)^d) := by
      congr 1
      rw [div_eq_mul_inv,mul_pow]
      ring
end OAI.Analysis.Fourier.WavePackets
end
end

-- OAI.Analysis.Fourier.WavePackets.Half.Wave.AnnularKernel
section
open OAI.Analysis.Fourier.Wave
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets
open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology FourierTransform ENNReal
theorem uniform_wave_annular_kernel_sqrt {d : ℕ} {φ : Space (d+1) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ T ∈ Icc (1 : ℝ) 2,
      eLpNorm (𝓕⁻ (waveAmplitude φ (γ^2) T)) 1 volume ≤ ENNReal.ofReal (C*(γ⁻¹)^d) := by
  classical
  obtain ⟨s,b,a,hb,hsum⟩ := finite_angular_atlas hφ hc hz
  choose C hC hkernel using fun i : s =>
    uniform_wave_positive_chart_kernel (hb i).1 (hb i).2.1 (hb i).2.2.1 (hb i).2.2.2.1
  have hCsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC i)
  refine ⟨1+∑ i,C i,by linarith,?_⟩
  intro γ hγ hγ1 T hT
  let f : s → Space (d+1) → ℂ := fun i ξ => waveAmplitude (b i) (γ^2) T (i.val ξ)
  have hfi (i : s) : Integrable (f i) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (contDiff_waveAmplitude (hb i).1 (by
        intro h
        have := (hb i).2.2.2.1 0 h
        simp only [PiLp.zero_apply] at this
        linarith [(hb i).2.2.1]) (γ^2) T).continuous.comp i.val.continuous
    · exact (hasCompactSupport_waveAmplitude (hb i).2.1 (γ^2) T).comp_homeomorph i.val.toHomeomorph
  have he : waveAmplitude φ (γ^2) T = fun ξ => ∑ i, f i ξ := by
    funext ξ
    simp only [f,waveAmplitude,LinearIsometryEquiv.norm_map,← Finset.mul_sum]
    rw [congrFun hsum ξ]
  have hbound (i : s) : eLpNorm (𝓕⁻ (f i)) 1 volume ≤ ENNReal.ofReal (C i*(γ⁻¹)^d) := by
    have hzi : (0 : Space (d+1)) ∉ tsupport (b i) := by
      intro h
      have := (hb i).2.2.2.1 0 h
      simp only [PiLp.zero_apply] at this
      linarith [(hb i).2.2.1]
    change eLpNorm (𝓕⁻ (waveAmplitude (b i) (γ^2) T ∘ i.val)) 1 volume ≤ _
    have hcomp := eLpNorm_fourierInv_comp_smooth
      (contDiff_waveAmplitude (hb i).1 hzi (γ^2) T)
      (hasCompactSupport_waveAmplitude (hb i).2.1 (γ^2) T) i.val.toContinuousLinearEquiv
    simpa only using! hcomp.trans_le (hkernel i γ hγ hγ1 T hT)
  rw [he]
  calc
    _ ≤ ∑ i, eLpNorm (𝓕⁻ (f i)) 1 volume := fourierInv_sum_eLpNorm_le f hfi
    _ ≤ ∑ i, ENNReal.ofReal (C i*(γ⁻¹)^d) := Finset.sum_le_sum (fun i _ => hbound i)
    _ = ENNReal.ofReal ((∑ i,C i)*(γ⁻¹)^d) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hC i) (by positivity)),
        Finset.sum_mul]
    _ ≤ ENNReal.ofReal ((1+∑ i,C i)*(γ⁻¹)^d) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
theorem inv_sqrt_pow_eq_rpow {h : ℝ} (hh : 0 < h) (d : ℕ) :
    ((Real.sqrt h)⁻¹)^d = h^(-(d : ℝ)/2) := by
  rw [← Real.rpow_natCast,Real.inv_rpow (Real.sqrt_nonneg h),Real.sqrt_eq_rpow,
    ← Real.rpow_mul hh.le,← Real.rpow_neg hh.le]
  congr 1
  ring
theorem uniform_wave_annular_kernel {d : ℕ} {φ : Space (d+1) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ T ∈ Icc (1 : ℝ) 2,
      eLpNorm (𝓕⁻ (waveAmplitude φ h T)) 1 volume ≤ ENNReal.ofReal (C*h^(-(d : ℝ)/2)) := by
  obtain ⟨C,hC,hkernel⟩ := uniform_wave_annular_kernel_sqrt hφ hc hz
  refine ⟨C,hC,?_⟩
  intro h hh hh1 T hT
  have hsq1 : Real.sqrt h ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hh1
  have H := hkernel (Real.sqrt h) (Real.sqrt_pos.2 hh) hsq1 T hT
  simpa only [Real.sq_sqrt hh.le,inv_sqrt_pow_eq_rpow hh d] using H
end OAI.Analysis.Fourier.WavePackets
end
end

-- OAI.Analysis.Fourier.WavePackets.Half.Wave.NormalizedKernel
section
open OAI.Analysis.Fourier.Wave
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets
open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology FourierTransform ENNReal RealInnerProductSpace
theorem normalized_semiclassicalWaveKernel_eq_angularInverse {n : ℕ}
    (φ : Space n → ℂ) {h : ℝ} (hh : 0 < h) (T : ℝ) (x : Space n) :
    (((2*Real.pi : ℝ) : ℂ)^n)⁻¹*semiclassicalWaveKernel volume φ h T x =
      OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => waveAmplitude φ h T (h • ξ)) x := by
  rw [← scaled_wave_integral φ hh T x]
  simp only [OAI.Analysis.Fourier.LocalSmoothing.angularInverse,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
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
theorem eLpNorm_normalized_semiclassicalWaveKernel {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {h : ℝ} (hh : 0 < h) (T : ℝ) :
    eLpNorm (fun x => (((2*Real.pi : ℝ) : ℂ)^n)⁻¹*semiclassicalWaveKernel volume φ h T x)
      1 volume = eLpNorm (𝓕⁻ (waveAmplitude φ h T)) 1 volume := by
  have he := funext (normalized_semiclassicalWaveKernel_eq_angularInverse φ hh T)
  rw [he,OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_angularInverse_dilate_one (waveAmplitude_integrable hφ hc h T) hh,
    eLpNorm_fourierInv_eq_angularInverse (waveAmplitude_integrable hφ hc h T)]
theorem uniform_semiclassicalWaveKernel_L1 {d : ℕ} {φ : Space (d+1) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ T ∈ Icc (1 : ℝ) 2,
      eLpNorm (fun x => (((2*Real.pi : ℝ) : ℂ)^(d+1))⁻¹*
        semiclassicalWaveKernel volume φ h T x) 1 volume ≤ ENNReal.ofReal (C*h^(-(d : ℝ)/2)) := by
  obtain ⟨C,hC,hbound⟩ := uniform_wave_annular_kernel hφ hc hz
  exact ⟨C,hC,fun h hh hh1 T hT =>
    (eLpNorm_normalized_semiclassicalWaveKernel hφ.continuous hc hh T).trans_le
      (hbound h hh hh1 T hT)⟩
end OAI.Analysis.Fourier.WavePackets
end
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Young
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
theorem norm_convolveKernel_le {n : ℕ} {K f : Space n → ℂ}
    (hK : Continuous K) {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hKN : eLpNorm K 1 volume ≤ .ofReal B) (hf : ∀ x, ‖f x‖ ≤ M) (x : Space n) :
    ‖OAI.Analysis.Fourier.SquareFunction.convolveKernel K f x‖ ≤ B * M := by
  have H : ‖OAI.Analysis.Fourier.SquareFunction.convolveKernel K f x‖ₑ ≤ .ofReal (B * M) := by
    rw [OAI.Analysis.Fourier.SquareFunction.convolveKernel_commuted]
    calc
      _ ≤ ∫⁻ y, ‖f (x-y) • K y‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y, .ofReal M * ‖K y‖ₑ := by
        apply lintegral_mono
        intro y
        dsimp only
        rw [enorm_smul]
        exact mul_le_mul' (by simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hf (x-y))) le_rfl
      _ = .ofReal M * eLpNorm K 1 volume := by
        rw [lintegral_const_mul _ hK.enorm.measurable,
          eLpNorm_one_eq_lintegral_enorm]
      _ ≤ .ofReal M * .ofReal B := mul_le_mul' le_rfl hKN
      _ = _ := by rw [← ENNReal.ofReal_mul hM, mul_comm]
  rw [← ofReal_norm] at H
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB hM)).mp H
theorem frequencyWave_spacetime_young {n : ℕ} {φ f : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (hf : Measurable f) (hi : Integrable f) {p : ℝ} (hp : 1 ≤ p) {A : ℝ≥0∞}
    (hK : ∀ t ∈ Icc (1 : ℝ) 2, eLpNorm (waveKernel φ h t) 1 volume ≤ A) :
    eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
      (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ A * eLpNorm f (.ofReal p) volume := by
  apply observation_norm_le_of_slices (measurable_frequencyWave hφ hs hh hf hi) (by linarith)
  intro t ht
  exact (frequencyWave_slice_young hφ hs hh hf hi t (by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    ENNReal.ofReal_ne_top).trans (mul_le_mul' (hK t ht) le_rfl)
theorem frequencyWave_ae_bounded {n : ℕ} {φ f : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (hi : Integrable f) {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hK : ∀ t ∈ Icc (1 : ℝ) 2, eLpNorm (waveKernel φ h t) 1 volume ≤ .ofReal B)
    (hf : ∀ x, ‖f x‖ ≤ M) :
    ∀ᵐ z : Space n × ℝ ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n, ‖OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1‖ ≤ B * M := by
  filter_upwards [observation_ae_time (n := n)] with z hz
  rw [frequencyHalfWave_eq_convolveKernel hφ hs hh z.2 hi]
  exact norm_convolveKernel_le (continuous_waveKernel hφ hs h z.2) hM hB (hK z.2 hz) hf z.1
theorem uniform_waveKernel_L1 {n : ℕ} (hn : 0 < n) {φ : Space n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ t ∈ Icc (1 : ℝ) 2,
      eLpNorm (waveKernel φ h t) 1 volume ≤ .ofReal (C * h ^ (-((n:ℝ)-1)/2)) := by
  cases n with
  | zero => omega
  | succ d =>
    obtain ⟨C,hC,hb⟩ := OAI.Analysis.Fourier.WavePackets.uniform_semiclassicalWaveKernel_L1 hφ hs hz
    refine ⟨C,hC,?_⟩
    intro h hh h1 t ht
    simpa only [waveKernel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using! hb h hh h1 t ht
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Endpoints
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
theorem frequencyWave_schwartz_bound_extends {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    {p : ℝ} (hp : 1 ≤ p) {A K : ℝ≥0∞} (hA : A ≠ ⊤) (hK : K ≠ ⊤)
    (hkernel : ∀ t ∈ Icc (1 : ℝ) 2, eLpNorm (waveKernel φ h t) 1 volume ≤ K)
    (hsharp : ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 g z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ A * eLpNorm g (.ofReal p) volume)
    {f : Space n → ℂ} (hf : Measurable f) (hi : Integrable f) (hfp : MemLp f (.ofReal p) volume) :
    eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
      (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ A * eLpNorm f (.ofReal p) volume := by
  apply bound_of_schwartz_dense (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n)
    (fun g z => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 g z.1)
    (fun g hg hi => (measurable_frequencyWave hφ hs hh hg hi).aestronglyMeasurable)
    (fun g k hg hk z => frequencyHalfWave_add hφ hs hh z.2 hg hk z.1)
    (by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    ENNReal.ofReal_ne_top hA hK hsharp
    (fun g hg hi _ => frequencyWave_spacetime_young hφ hs hh hg hi hp hkernel) hf hi hfp
structure FrequencyEndpoints (n : ℕ) (φ : Space n → ℂ) where
  twoConstant : ℝ
  criticalConstant : ℝ
  infinityConstant : ℝ
  two_pos : 0 < twoConstant
  critical_pos : 0 < criticalConstant
  infinity_pos : 0 < infinityConstant
  two : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : Space n → ℂ,
    Measurable f → Integrable f → MemLp f 2 volume →
    eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1) 2 (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal twoConstant * eLpNorm f 2 volume
  critical : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : Space n → ℂ,
    Measurable f → Integrable f → MemLp f (.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume →
    eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
      (.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal (criticalConstant * (1 + Real.log (1/h)) ^ (2*n+5)) *
        eLpNorm f (.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume
  infinity : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : Space n → ℂ,
    Measurable f → Integrable f → ∀ M : ℝ, 0 < M → (∀ x, ‖f x‖ ≤ M) →
    ∀ᵐ z : Space n × ℝ ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n, ‖OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1‖ ≤
      (infinityConstant * h ^ (-((n:ℝ)-1)/2)) * M
theorem frequency_endpoints_of_logarithmicRefinement (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {φ : Space n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    Nonempty (FrequencyEndpoints n φ) := by
  obtain ⟨A,hA,h2⟩ := frequencyWave_two hφ hs
  obtain ⟨B,hB,hc⟩ := hlog n hn φ hφ hs hz
  obtain ⟨K,hK,hk⟩ := uniform_waveKernel_L1 (by omega : 0 < n) hφ hs hz
  refine ⟨⟨A,B,K,hA,hB,hK,?_,?_,?_⟩⟩
  · intro h hh h1 f hf hi hp
    have H := frequencyWave_schwartz_bound_extends hφ.continuous hs hh
      (p := 2) (by norm_num) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      (hk h hh h1) (fun g => by simpa using (h2 h hh g).2) hf hi (by simpa using hp)
    simpa using H
  · intro h hh h1 f hf hi hp
    exact frequencyWave_schwartz_bound_extends hφ.continuous hs hh
      (by linarith [criticalExponent_gt_two hn]) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      (hk h hh h1) (fun g => (hc h hh h1 g).2) hf hi hp
  · intro h hh h1 f hf hi M hM hb
    exact frequencyWave_ae_bounded hφ.continuous hs hh hi hM.le
      (mul_nonneg hK.le (Real.rpow_nonneg hh.le _)) (hk h hh h1) hb
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end

-- OAI.Analysis.Fourier.Restriction.InterpolationHead
section
open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction
theorem lintegral_power_Ici {b q : ℝ} (hb : 0 < b) (hq : q < -1) :
    (∫⁻ t : ℝ in Ici b, ENNReal.ofReal t ^ q) =
      ENNReal.ofReal (b ^ (q + 1) / (-q - 1)) := by
  rw [← restrict_Ioi_eq_restrict_Ici]
  have hi := integrableOn_Ioi_rpow_of_lt hq hb
  calc
    _ = ∫⁻ t : ℝ in Ioi b, ENNReal.ofReal (t ^ q) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact ENNReal.ofReal_rpow_of_pos (hb.trans ht)
    _ = ENNReal.ofReal (∫ t : ℝ in Ioi b, t ^ q) :=
      (ofReal_integral_eq_lintegral_ofReal hi (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact Real.rpow_nonneg (hb.trans ht).le _)).symm
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt hq hb]
      congr 1
      rw [show -q - 1 = -(q + 1) by ring, div_neg, neg_div]
end OAI.Analysis.Fourier.Restriction
end
end

-- OAI.Analysis.Fourier.SquareFunction.Maximal
section
namespace OAI.Analysis.Fourier.SquareFunction
open _root_.MeasureTheory Set intervalIntegral
open scoped ENNReal
private theorem primitive_power {p : ℝ} (hp : 0 < p) (b : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..b, p * t ^ (p - 1)) = b ^ p := by
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : -1 < p - 1))]
  simp only [sub_add_cancel, Real.zero_rpow (ne_of_gt hp), sub_zero]
  field_simp
theorem lintegral_power_layercake {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ), μ {x | t < f x} *
        ENNReal.ofReal p * ENNReal.ofReal t ^ (p - 1) := by
  have h := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (Filter.Eventually.of_forall hfn) hf.aemeasurable
    (g := fun t : ℝ => p * t ^ (p - 1))
    (fun t ht => (intervalIntegrable_rpow' (by linarith : -1 < p - 1)).const_mul p)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg hp.le (Real.rpow_nonneg ht.le _))
  simp_rw [primitive_power hp] at h
  calc
    _ = ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ := by
      apply lintegral_congr; intro x
      exact ENNReal.ofReal_rpow_of_nonneg (hfn x) hp.le
    _ = _ := h.trans (lintegral_congr_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_rpow_of_pos ht]
      exact (mul_assoc _ _ _).symm))
theorem lintegral_power_Ioo {b q : ℝ} (hb : 0 ≤ b) (hq : -1 < q) :
    (∫⁻ t : ℝ in Ioo 0 b, ENNReal.ofReal t ^ q) =
      ENNReal.ofReal (b ^ (q + 1) / (q + 1)) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ q) (Ioo 0 b) :=
    (intervalIntegrable_rpow' hq (a := 0) (b := b)).1.mono_set Ioo_subset_Ioc_self
  have hn : ∀ᵐ t : ℝ ∂volume.restrict (Ioo 0 b), 0 ≤ t ^ q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _
  calc
    _ = ∫⁻ t : ℝ in Ioo 0 b, ENNReal.ofReal (t ^ q) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact ENNReal.ofReal_rpow_of_pos ht.1
    _ = ENNReal.ofReal (∫ t : ℝ in Ioo 0 b, t ^ q) := (ofReal_integral_eq_lintegral_ofReal hi hn).symm
    _ = _ := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb,
        integral_rpow (Or.inl hq)]
      simp [Real.zero_rpow (by linarith : q + 1 ≠ 0)]
end OAI.Analysis.Fourier.SquareFunction
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Moments
section
open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
theorem weighted_tail_power {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {p q : ℝ} (hq : 0 < q) (hqp : q < p) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q ∂μ) *
        ENNReal.ofReal t ^ (p - q - 1)) =
      ENNReal.ofReal (1 / (p - q)) * ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  let F : X × ℝ → ℝ≥0∞ := {z | z.2 < f z.1}.indicator
    (fun z => ENNReal.ofReal (f z.1) ^ q * ENNReal.ofReal z.2 ^ (p - q - 1))
  have hF : Measurable F :=
    (((hf.comp measurable_fst).ennreal_ofReal.pow_const q).mul
      (measurable_snd.ennreal_ofReal.pow_const (p - q - 1))).indicator
      (measurableSet_lt measurable_snd (hf.comp measurable_fst))
  have hleft (t : ℝ) : (∫⁻ x, F (x,t) ∂μ) =
      (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q ∂μ) *
        ENNReal.ofReal t ^ (p - q - 1) := by
    change (∫⁻ x, {x | t < f x}.indicator
      (fun x => ENNReal.ofReal (f x) ^ q * ENNReal.ofReal t ^ (p - q - 1)) x ∂μ) = _
    rw [lintegral_indicator (measurableSet_lt measurable_const hf),
      lintegral_mul_const _ (hf.ennreal_ofReal.pow_const q)]
  have hright (x : X) : (∫⁻ t in Ioi (0 : ℝ), F (x,t)) =
      ENNReal.ofReal (1 / (p - q)) * ENNReal.ofReal (f x) ^ p := by
    change (∫⁻ t in Ioi (0 : ℝ), (Iio (f x)).indicator
      (fun t => ENNReal.ofReal (f x) ^ q * ENNReal.ofReal t ^ (p - q - 1)) t) = _
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      inter_comm (Iio (f x)), Ioi_inter_Iio,
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top),
      OAI.Analysis.Fourier.SquareFunction.lintegral_power_Ioo (hfn x) (by linarith)]
    have hd : 0 < p - q := sub_pos.mpr hqp
    simp only [show p - q - 1 + 1 = p - q by ring]
    rw [ENNReal.ofReal_div_of_pos hd, ← ENNReal.ofReal_rpow_of_nonneg (hfn x) hd.le,
      ENNReal.ofReal_div_of_pos hd, ENNReal.ofReal_one]
    have he : ENNReal.ofReal (f x) ^ q * ENNReal.ofReal (f x) ^ (p - q) =
        ENNReal.ofReal (f x) ^ p := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hq.le hd.le]
      congr 1
      ring
    simp only [div_eq_mul_inv,one_mul]
    rw [← mul_assoc,he,mul_comm]
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, F (x,t) ∂μ := by simp_rw [hleft]
    _ = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), F (x,t)) ∂μ :=
      (lintegral_lintegral_swap (μ := μ) (ν := volume.restrict (Ioi (0 : ℝ)))
        (f := fun x t => F (x,t)) hF.aemeasurable).symm
    _ = _ := by
      simp_rw [hright]
      exact lintegral_const_mul _ (hf.ennreal_ofReal.pow_const p)
theorem weighted_head_power {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ q ∂μ) *
        ENNReal.ofReal t ^ (p - q - 1)) =
      ENNReal.ofReal (1 / (q - p)) * ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  let F : X × ℝ → ℝ≥0∞ := {z | f z.1 ≤ z.2}.indicator
    (fun z => ENNReal.ofReal (f z.1) ^ q * ENNReal.ofReal z.2 ^ (p - q - 1))
  have hq : 0 < q := hp.trans hpq
  have hF : Measurable F :=
    (((hf.comp measurable_fst).ennreal_ofReal.pow_const q).mul
      (measurable_snd.ennreal_ofReal.pow_const (p - q - 1))).indicator
      (measurableSet_le (hf.comp measurable_fst) measurable_snd)
  have hleft (t : ℝ) : (∫⁻ x, F (x,t) ∂μ) =
      (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ q ∂μ) *
        ENNReal.ofReal t ^ (p - q - 1) := by
    change (∫⁻ x, {x | f x ≤ t}.indicator
      (fun x => ENNReal.ofReal (f x) ^ q * ENNReal.ofReal t ^ (p - q - 1)) x ∂μ) = _
    rw [lintegral_indicator (measurableSet_le hf measurable_const),
      lintegral_mul_const _ (hf.ennreal_ofReal.pow_const q)]
  have hright (x : X) : (∫⁻ t in Ioi (0 : ℝ), F (x,t)) =
      ENNReal.ofReal (1 / (q - p)) * ENNReal.ofReal (f x) ^ p := by
    by_cases hx0 : f x = 0
    · simp [F,Set.indicator_apply,hx0,hp,hq]
    have hx : 0 < f x := lt_of_le_of_ne (hfn x) (Ne.symm hx0)
    change (∫⁻ t in Ioi (0 : ℝ), (Ici (f x)).indicator
      (fun t => ENNReal.ofReal (f x) ^ q * ENNReal.ofReal t ^ (p - q - 1)) t) = _
    rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.mpr (by intro t ht; exact hx.trans_le ht),
      lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top),
      OAI.Analysis.Fourier.Restriction.lintegral_power_Ici hx (by linarith)]
    have hd : 0 < q - p := sub_pos.mpr hpq
    simp only [show p - q - 1 + 1 = p - q by ring,
      show -(p - q - 1) - 1 = q - p by ring]
    rw [ENNReal.ofReal_div_of_pos hd, ← ENNReal.ofReal_rpow_of_pos hx,
      ENNReal.ofReal_div_of_pos hd, ENNReal.ofReal_one]
    have he : ENNReal.ofReal (f x) ^ q * ENNReal.ofReal (f x) ^ (p - q) =
        ENNReal.ofReal (f x) ^ p := by
      rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr hx) ENNReal.ofReal_ne_top]
      congr 1
      ring
    simp only [div_eq_mul_inv,one_mul]
    rw [← mul_assoc,he,mul_comm]
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, F (x,t) ∂μ := by simp_rw [hleft]
    _ = ∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), F (x,t)) ∂μ :=
      (lintegral_lintegral_swap (μ := μ) (ν := volume.restrict (Ioi (0 : ℝ)))
        (f := fun x t => F (x,t)) hF.aemeasurable).symm
    _ = _ := by
      simp_rw [hright]
      exact lintegral_const_mul _ (hf.ennreal_ofReal.pow_const p)
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end

-- OAI.Analysis.Fourier.Restriction.WeakInterpolation
section
open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction
theorem measurable_tailMoment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f) (a : ℝ) :
    Measurable (fun t : ℝ ↦ ∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ a ∂μ) := by
  let F : ℝ × X → ℝ≥0∞ := {z | z.1 < f z.2}.indicator
    (fun z ↦ ENNReal.ofReal (f z.2) ^ a)
  have hF : Measurable F := ((hf.comp measurable_snd).ennreal_ofReal.pow_const a).indicator
    (measurableSet_lt measurable_fst (hf.comp measurable_snd))
  have h := hF.lintegral_prod_right' (ν := μ)
  convert h using 1
  funext t
  change _ = ∫⁻ x, {x | t < f x}.indicator (fun x ↦ ENNReal.ofReal (f x) ^ a) x ∂μ
  rw [lintegral_indicator (measurableSet_lt measurable_const hf)]
theorem measurable_headMoment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ} (hf : Measurable f) (a : ℝ) :
    Measurable (fun t : ℝ ↦ ∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ a ∂μ) := by
  let F : ℝ × X → ℝ≥0∞ := {z | f z.2 ≤ z.1}.indicator
    (fun z ↦ ENNReal.ofReal (f z.2) ^ a)
  have hF : Measurable F := ((hf.comp measurable_snd).ennreal_ofReal.pow_const a).indicator
    (measurableSet_le (hf.comp measurable_snd) measurable_fst)
  have h := hF.lintegral_prod_right' (ν := μ)
  convert h using 1
  funext t
  change _ = ∫⁻ x, {x | f x ≤ t}.indicator (fun x ↦ ENNReal.ofReal (f x) ^ a) x ∂μ
  rw [lintegral_indicator (measurableSet_le hf measurable_const)]
end OAI.Analysis.Fourier.Restriction
end
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Weak
section
open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
theorem power_moment_le_of_tail
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    {f : X → ℝ} {u : Y → ℝ} (hf : Measurable f) (hu : Measurable u)
    (hfn : ∀ x, 0 ≤ f x) (hun : ∀ y, 0 ≤ u y)
    {p q : ℝ} (hq : 0 < q) (hqp : q < p) {A : ℝ≥0∞}
    (hweak : ∀ t > 0, ν {y | t < u y} ≤
      A / ENNReal.ofReal t ^ q * ∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q ∂μ) :
    (∫⁻ y, ENNReal.ofReal (u y) ^ p ∂ν) ≤
      (A * ENNReal.ofReal (p / (p - q))) * ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  have hp : 0 < p := hq.trans hqp
  have ht : Measurable (fun t : ℝ =>
      (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q ∂μ) *
        ENNReal.ofReal t ^ (p - q - 1)) :=
    (OAI.Analysis.Fourier.Restriction.measurable_tailMoment μ hf q).mul
      (measurable_id.ennreal_ofReal.pow_const (p - q - 1))
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ν {y | t < u y} * ENNReal.ofReal p *
        ENNReal.ofReal t ^ (p - 1) := OAI.Analysis.Fourier.SquareFunction.lintegral_power_layercake ν hu hun hp
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (A * ENNReal.ofReal p) *
        ((∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q ∂μ) *
          ENNReal.ofReal t ^ (p - q - 1)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
      have he : ENNReal.ofReal t ^ (p - q - 1) =
          ENNReal.ofReal t ^ (p - 1) / ENNReal.ofReal t ^ q := by
        simpa only [show p - 1 - q = p - q - 1 by ring] using
          ENNReal.rpow_sub (p - 1) q (ENNReal.ofReal_ne_zero_iff.mpr ht0) ENNReal.ofReal_ne_top
      calc
        _ ≤ (A / ENNReal.ofReal t ^ q * ∫⁻ x in {x | t < f x},
            ENNReal.ofReal (f x) ^ q ∂μ) * ENNReal.ofReal p * ENNReal.ofReal t ^ (p - 1) := by
              gcongr; exact hweak t ht0
        _ = _ := by rw [he]; simp only [div_eq_mul_inv]; ring
    _ = _ := by
      rw [lintegral_const_mul _ ht,weighted_tail_power μ hf hfn hq hqp]
      have he : ENNReal.ofReal p * ENNReal.ofReal (1 / (p - q)) =
          ENNReal.ofReal (p / (p - q)) := by
        rw [← ENNReal.ofReal_mul hp.le]
        congr 1
        ring
      rw [← mul_assoc, mul_assoc A,he]
theorem power_moment_le_of_two_tails
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    {f : X → ℝ} {u : Y → ℝ} (hf : Measurable f) (hu : Measurable u)
    (hfn : ∀ x, 0 ≤ f x) (hun : ∀ y, 0 ≤ u y)
    {p q₀ q₁ : ℝ} (hq₀ : 0 < q₀) (h₀p : q₀ < p) (hp₁ : p < q₁)
    {A B : ℝ≥0∞}
    (hweak : ∀ t > 0, ν {y | t < u y} ≤
      A / ENNReal.ofReal t ^ q₀ * (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q₀ ∂μ) +
      B / ENNReal.ofReal t ^ q₁ * (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ q₁ ∂μ)) :
    (∫⁻ y, ENNReal.ofReal (u y) ^ p ∂ν) ≤
      (A * ENNReal.ofReal (p / (p - q₀)) + B * ENNReal.ofReal (p / (q₁ - p))) *
        ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ := by
  have hp : 0 < p := hq₀.trans h₀p
  have ht : Measurable (fun t : ℝ =>
      (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q₀ ∂μ) *
        ENNReal.ofReal t ^ (p - q₀ - 1)) :=
    (OAI.Analysis.Fourier.Restriction.measurable_tailMoment μ hf q₀).mul
      (measurable_id.ennreal_ofReal.pow_const _)
  have hh : Measurable (fun t : ℝ =>
      (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ q₁ ∂μ) *
        ENNReal.ofReal t ^ (p - q₁ - 1)) :=
    (OAI.Analysis.Fourier.Restriction.measurable_headMoment μ hf q₁).mul
      (measurable_id.ennreal_ofReal.pow_const _)
  have hAt : Measurable (fun t : ℝ => (A * ENNReal.ofReal p) *
      ((∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q₀ ∂μ) *
        ENNReal.ofReal t ^ (p - q₀ - 1))) := measurable_const.mul ht
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), ν {y | t < u y} * ENNReal.ofReal p *
        ENNReal.ofReal t ^ (p - 1) := OAI.Analysis.Fourier.SquareFunction.lintegral_power_layercake ν hu hun hp
    _ ≤ ∫⁻ t in Ioi (0 : ℝ),
        (A * ENNReal.ofReal p) * ((∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q₀ ∂μ) *
          ENNReal.ofReal t ^ (p - q₀ - 1)) +
        (B * ENNReal.ofReal p) * ((∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ q₁ ∂μ) *
          ENNReal.ofReal t ^ (p - q₁ - 1)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
      have he (q : ℝ) : ENNReal.ofReal t ^ (p - q - 1) =
          ENNReal.ofReal t ^ (p - 1) / ENNReal.ofReal t ^ q := by
        simpa only [show p - 1 - q = p - q - 1 by ring] using
          ENNReal.rpow_sub (p - 1) q (ENNReal.ofReal_ne_zero_iff.mpr ht0) ENNReal.ofReal_ne_top
      calc
        _ ≤ (A / ENNReal.ofReal t ^ q₀ * (∫⁻ x in {x | t < f x}, ENNReal.ofReal (f x) ^ q₀ ∂μ) +
            B / ENNReal.ofReal t ^ q₁ * (∫⁻ x in {x | f x ≤ t}, ENNReal.ofReal (f x) ^ q₁ ∂μ)) *
              ENNReal.ofReal p * ENNReal.ofReal t ^ (p - 1) := by
          gcongr; exact hweak t ht0
        _ = _ := by rw [he q₀,he q₁]; simp only [div_eq_mul_inv]; ring
    _ = _ := by
      rw [lintegral_add_left hAt,lintegral_const_mul _ ht,lintegral_const_mul _ hh,
        weighted_tail_power μ hf hfn hq₀ h₀p,weighted_head_power μ hf hfn hp hp₁]
      have he (q : ℝ) : ENNReal.ofReal p * ENNReal.ofReal (1 / q) =
          ENNReal.ofReal (p / q) := by
        rw [← ENNReal.ofReal_mul hp.le]
        congr 1
        ring
      simp only [← mul_assoc,add_mul]
      rw [mul_assoc A (ENNReal.ofReal p),he,mul_assoc B (ENNReal.ofReal p),he]
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end

-- OAI.Analysis.Fourier.Restriction.Markov
section
open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction
theorem measure_norm_gt_le_moment {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) {g : Y → ℂ} (hg : Measurable g)
    {p t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    ν {y | t < ‖g y‖} ≤ (∫⁻ y, ‖g y‖ₑ ^ p ∂ν) / ENNReal.ofReal t ^ p := by
  have hsubset : {y | t < ‖g y‖} ⊆ {y | ENNReal.ofReal t ^ p ≤ ‖g y‖ₑ ^ p} := by
    intro y hy
    apply ENNReal.rpow_le_rpow _ hp.le
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hy.le
  exact (measure_mono hsubset).trans (meas_ge_le_lintegral_div
    (hg.enorm.pow_const p).aemeasurable (by positivity)
    (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top))
end OAI.Analysis.Fourier.Restriction
end
end

-- OAI.Analysis.Fourier.Restriction.OperatorInterpolation
section
open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction
theorem eLpNorm_le_of_half_moment
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y)
    {f : X → ℂ} {u : Y → ℂ} (hf : AEStronglyMeasurable f μ) (hu : Measurable u)
    {p : ℝ} (hp : 0 < p) {C : ℝ≥0∞}
    (h : (∫⁻ y, ENNReal.ofReal (‖u y‖ / 2) ^ p ∂ν) ≤
      C * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) :
    eLpNorm u (ENNReal.ofReal p) ν ≤
      2 * C ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) μ := by
  have hm : Measurable (fun y ↦ ENNReal.ofReal (‖u y‖ / 2) ^ p) :=
    (hu.norm.div_const 2).ennreal_ofReal.pow_const p
  have H : eLpNorm u (ENNReal.ofReal p) ν ^ p ≤
      ((2 : ℝ≥0∞) ^ p * C) * eLpNorm f (ENNReal.ofReal p) μ ^ p := by
    rw [OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hu.aestronglyMeasurable,
      OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hf]
    calc
      _ = ∫⁻ y, (2 : ℝ≥0∞) ^ p * ENNReal.ofReal (‖u y‖ / 2) ^ p ∂ν := by
        apply lintegral_congr
        intro y
        have hx : ENNReal.ofReal ‖u y‖ = ENNReal.ofReal (2 : ℝ) *
            ENNReal.ofReal (‖u y‖ / 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
        rw [ofReal_norm, ENNReal.ofReal_ofNat] at hx
        rw [hx, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      _ = (2 : ℝ≥0∞) ^ p * ∫⁻ y, ENNReal.ofReal (‖u y‖ / 2) ^ p ∂ν :=
        lintegral_const_mul _ hm
      _ ≤ (2 : ℝ≥0∞) ^ p * (C * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) := by gcongr
      _ = _ := by ring
  have H' := ENNReal.rpow_le_rpow H (le_of_lt (one_div_pos.mpr hp))
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (one_div_pos.mpr hp)),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one] using H'
end OAI.Analysis.Fourier.Restriction
end
end

-- OAI.Analysis.Fourier.Restriction.Truncation
section
open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction
def amplitudeLow {X : Type*} (f : X → ℂ) (t : ℝ) : X → ℂ :=
  {x | ‖f x‖ ≤ t}.indicator f
def amplitudeHigh {X : Type*} (f : X → ℂ) (t : ℝ) : X → ℂ :=
  {x | t < ‖f x‖}.indicator f
theorem amplitudeHigh_add_low {X : Type*} (f : X → ℂ) (t : ℝ) :
    (fun x ↦ amplitudeHigh f t x + amplitudeLow f t x) = f := by
  funext x
  by_cases hx : ‖f x‖ ≤ t
  · simp [amplitudeHigh, amplitudeLow, hx, not_lt.mpr hx]
  · simp [amplitudeHigh, amplitudeLow, hx, lt_of_not_ge hx]
theorem integrable_amplitudeLow {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : Measurable f) (hf1 : Integrable f μ) (t : ℝ) :
    Integrable (amplitudeLow f t) μ :=
  hf1.indicator (measurableSet_le hf.norm measurable_const)
theorem integrable_amplitudeHigh {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : Measurable f) (hf1 : Integrable f μ) (t : ℝ) :
    Integrable (amplitudeHigh f t) μ :=
  hf1.indicator (measurableSet_lt measurable_const hf.norm)
end OAI.Analysis.Fourier.Restriction
end
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Operator
section
open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
theorem moment_amplitudeHigh {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ} (hf : Measurable f) (t : ℝ) {q : ℝ} (hq : 0 < q) :
    (∫⁻ x, ‖OAI.Analysis.Fourier.Restriction.amplitudeHigh f t x‖ₑ ^ q ∂μ) =
      ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ^ q ∂μ := by
  rw [← lintegral_indicator (measurableSet_lt measurable_const hf.norm)]
  congr 1
  funext x
  by_cases hx : t < ‖f x‖ <;> simp [OAI.Analysis.Fourier.Restriction.amplitudeHigh,hx,hq]
theorem moment_amplitudeLow {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ} (hf : Measurable f) (t : ℝ) {q : ℝ} (hq : 0 < q) :
    (∫⁻ x, ‖OAI.Analysis.Fourier.Restriction.amplitudeLow f t x‖ₑ ^ q ∂μ) =
      ∫⁻ x in {x | ‖f x‖ ≤ t}, ‖f x‖ₑ ^ q ∂μ := by
  rw [← lintegral_indicator (measurableSet_le hf.norm measurable_const)]
  congr 1
  funext x
  by_cases hx : ‖f x‖ ≤ t <;> simp [OAI.Analysis.Fourier.Restriction.amplitudeLow,hx,hq]
theorem operator_two_moment_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    (T : (X → ℂ) → Y → ℂ)
    (hTm : ∀ g, Measurable g → Integrable g μ → Measurable (T g))
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    {p q₀ q₁ : ℝ} (hq₀ : 0 < q₀) (h₀p : q₀ < p) (hp₁ : p < q₁)
    {A B : ℝ≥0∞}
    (h0 : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q₀) μ → MemLp g (.ofReal q₁) μ →
      (∫⁻ y, ‖T g y‖ₑ ^ q₀ ∂ν) ≤ A * ∫⁻ x, ‖g x‖ₑ ^ q₀ ∂μ)
    (h1 : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q₀) μ → MemLp g (.ofReal q₁) μ →
      (∫⁻ y, ‖T g y‖ₑ ^ q₁ ∂ν) ≤ B * ∫⁻ x, ‖g x‖ₑ ^ q₁ ∂μ)
    {f : X → ℂ} (hf : Measurable f) (hfi : Integrable f μ)
    (hf0 : MemLp f (.ofReal q₀) μ) (hf1 : MemLp f (.ofReal q₁) μ) :
    eLpNorm (T f) (.ofReal p) ν ≤
      2 * (A * .ofReal (p / (p - q₀)) + B * .ofReal (p / (q₁ - p))) ^ (1 / p) *
        eLpNorm f (.ofReal p) μ := by
  have hp : 0 < p := hq₀.trans h₀p
  have hq₁ : 0 < q₁ := hp.trans hp₁
  apply OAI.Analysis.Fourier.Restriction.eLpNorm_le_of_half_moment μ ν hf.aestronglyMeasurable (hTm f hf hfi) hp
  have H := power_moment_le_of_two_tails μ ν hf.norm ((hTm f hf hfi).norm.div_const 2)
    (fun x => norm_nonneg _) (fun y => by positivity) hq₀ h₀p hp₁ (A := A) (B := B)
  simp only [ofReal_norm] at H
  apply H
  intro t ht
  have hsH : MeasurableSet {x | t < ‖f x‖} := measurableSet_lt measurable_const hf.norm
  have hsL : MeasurableSet {x | ‖f x‖ ≤ t} := measurableSet_le hf.norm measurable_const
  have hmH : Measurable (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) := hf.indicator hsH
  have hmL : Measurable (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) := hf.indicator hsL
  have hiH := OAI.Analysis.Fourier.Restriction.integrable_amplitudeHigh hf hfi t
  have hiL := OAI.Analysis.Fourier.Restriction.integrable_amplitudeLow hf hfi t
  have hH := h0 _ hmH hiH (hf0.indicator hsH) (hf1.indicator hsH)
  have hL := h1 _ hmL hiL (hf0.indicator hsL) (hf1.indicator hsL)
  have high : ν {y | t < ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖} ≤
      A / .ofReal t ^ q₀ * ∫⁻ x in {x | t < ‖f x‖}, ‖f x‖ₑ ^ q₀ ∂μ := by
    calc
      _ ≤ (∫⁻ y, ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖ₑ ^ q₀ ∂ν) / .ofReal t ^ q₀ :=
        OAI.Analysis.Fourier.Restriction.measure_norm_gt_le_moment ν (hTm _ hmH hiH) hq₀ ht
      _ ≤ (A * ∫⁻ x, ‖OAI.Analysis.Fourier.Restriction.amplitudeHigh f t x‖ₑ ^ q₀ ∂μ) / .ofReal t ^ q₀ := by gcongr
      _ = _ := by rw [moment_amplitudeHigh μ hf t hq₀]; simp only [div_eq_mul_inv]; ring
  have low : ν {y | t < ‖T (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) y‖} ≤
      B / .ofReal t ^ q₁ * ∫⁻ x in {x | ‖f x‖ ≤ t}, ‖f x‖ₑ ^ q₁ ∂μ := by
    calc
      _ ≤ (∫⁻ y, ‖T (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) y‖ₑ ^ q₁ ∂ν) / .ofReal t ^ q₁ :=
        OAI.Analysis.Fourier.Restriction.measure_norm_gt_le_moment ν (hTm _ hmL hiL) hq₁ ht
      _ ≤ (B * ∫⁻ x, ‖OAI.Analysis.Fourier.Restriction.amplitudeLow f t x‖ₑ ^ q₁ ∂μ) / .ofReal t ^ q₁ := by gcongr
      _ = _ := by rw [moment_amplitudeLow μ hf t hq₁]; simp only [div_eq_mul_inv]; ring
  calc
    _ ≤ ν ({y | t < ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖} ∪ {y | t < ‖T (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) y‖}) := by
      apply measure_mono
      intro y hy
      have he := hadd (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) hiH hiL y
      rw [OAI.Analysis.Fourier.Restriction.amplitudeHigh_add_low] at he
      have hn := norm_add_le (T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y) (T (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) y)
      rw [← he] at hn
      by_contra hc
      have hc' := not_or.mp hc
      have hh : ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖ ≤ t := le_of_not_gt hc'.1
      have hl : ‖T (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) y‖ ≤ t := le_of_not_gt hc'.2
      change t < ‖T f y‖ / 2 at hy
      linarith
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add high low)
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Infinity
section
open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
theorem operator_infinity_moment_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    (T : (X → ℂ) → Y → ℂ)
    (hTm : ∀ g, Measurable g → Integrable g μ → Measurable (T g))
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    {p q : ℝ} (hq : 0 < q) (hqp : q < p) {A : ℝ≥0∞}
    (hqbound : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q) μ →
      (∫⁻ y, ‖T g y‖ₑ ^ q ∂ν) ≤ A * ∫⁻ x, ‖g x‖ₑ ^ q ∂μ)
    (hinf : ∀ g, Measurable g → Integrable g μ → ∀ t : ℝ, 0 < t →
      (∀ x, ‖g x‖ ≤ t) → ∀ᵐ y ∂ν, ‖T g y‖ ≤ t)
    {f : X → ℂ} (hf : Measurable f) (hfi : Integrable f μ) (hfq : MemLp f (.ofReal q) μ) :
    eLpNorm (T f) (.ofReal p) ν ≤
      2 * (A * .ofReal (p / (p - q))) ^ (1 / p) * eLpNorm f (.ofReal p) μ := by
  have hp : 0 < p := hq.trans hqp
  apply OAI.Analysis.Fourier.Restriction.eLpNorm_le_of_half_moment μ ν hf.aestronglyMeasurable (hTm f hf hfi) hp
  have H := power_moment_le_of_tail μ ν hf.norm ((hTm f hf hfi).norm.div_const 2)
    (fun x => norm_nonneg _) (fun y => by positivity) hq hqp (A := A)
  simp only [ofReal_norm] at H
  apply H
  intro t ht
  have hsH : MeasurableSet {x | t < ‖f x‖} := measurableSet_lt measurable_const hf.norm
  have hsL : MeasurableSet {x | ‖f x‖ ≤ t} := measurableSet_le hf.norm measurable_const
  have hmH : Measurable (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) := hf.indicator hsH
  have hmL : Measurable (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) := hf.indicator hsL
  have hiH := OAI.Analysis.Fourier.Restriction.integrable_amplitudeHigh hf hfi t
  have hiL := OAI.Analysis.Fourier.Restriction.integrable_amplitudeLow hf hfi t
  have hH := hqbound _ hmH hiH (hfq.indicator hsH)
  have hL := hinf _ hmL hiL t ht (fun x => by
    by_cases hx : ‖f x‖ ≤ t
    · simp [OAI.Analysis.Fourier.Restriction.amplitudeLow, hx]
    · simpa [OAI.Analysis.Fourier.Restriction.amplitudeLow, hx] using ht.le)
  calc
    _ ≤ ν {y | t < ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖} := by
      apply measure_mono_ae
      filter_upwards [hL] with y hlow
      intro hy
      have he := hadd (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) hiH hiL y
      rw [OAI.Analysis.Fourier.Restriction.amplitudeHigh_add_low] at he
      have hn := norm_add_le (T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y) (T (OAI.Analysis.Fourier.Restriction.amplitudeLow f t) y)
      rw [← he] at hn
      change t < ‖T f y‖ / 2 at hy
      change t < ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖
      linarith
    _ ≤ (∫⁻ y, ‖T (OAI.Analysis.Fourier.Restriction.amplitudeHigh f t) y‖ₑ ^ q ∂ν) / .ofReal t ^ q :=
      OAI.Analysis.Fourier.Restriction.measure_norm_gt_le_moment ν (hTm _ hmH hiH) hq ht
    _ ≤ (A * ∫⁻ x, ‖OAI.Analysis.Fourier.Restriction.amplitudeHigh f t x‖ₑ ^ q ∂μ) / .ofReal t ^ q := by gcongr
    _ = _ := by rw [moment_amplitudeHigh μ hf t hq]; simp only [div_eq_mul_inv]; ring
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Scale
section
open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
theorem moment_le_of_norm_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {f : X → ℂ} {g : Y → ℂ}
    (hf : Measurable f) (hg : Measurable g) {q : ℝ} (hq : 0 < q) {A : ℝ≥0∞}
    (hb : eLpNorm g (.ofReal q) ν ≤ A * eLpNorm f (.ofReal q) μ) :
    (∫⁻ y, ‖g y‖ₑ ^ q ∂ν) ≤ A ^ q * ∫⁻ x, ‖f x‖ₑ ^ q ∂μ := by
  have H := ENNReal.rpow_le_rpow hb hq.le
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hq.le,
    OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hq hf.aestronglyMeasurable,
    OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hq hg.aestronglyMeasurable] using H
theorem norm_real_normalized_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (p : ℝ≥0∞) {M : ℝ} (hM : 0 < M)
    {A N : ℝ≥0∞} (hf : eLpNorm f p μ ≤ A * N) :
    eLpNorm (M⁻¹ • f) p μ ≤ (.ofReal M)⁻¹ * A * N := by
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (inv_nonneg.mpr hM.le),
    ENNReal.ofReal_inv_of_pos hM]
  exact (mul_le_mul' le_rfl hf).trans_eq (mul_assoc _ _ _).symm
theorem norm_restore_real_scale {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (p : ℝ≥0∞) {M : ℝ} (hM : 0 < M) :
    eLpNorm f p μ = .ofReal M * eLpNorm (M⁻¹ • f) p μ := by
  have he : f = M • (M⁻¹ • f) := by simp [smul_smul, hM.ne']
  conv_lhs => rw [he]
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hM.le]
def finiteInterpolationConstant (q₀ p q₁ : ℝ) : ℝ≥0∞ :=
  2 * (.ofReal (p / (p - q₀)) + .ofReal (p / (q₁ - p))) ^ (1 / p)
theorem finiteInterpolationConstant_ne_top {q₀ p q₁ : ℝ} (hp : 0 < p) :
    finiteInterpolationConstant q₀ p q₁ ≠ ⊤ := by
  exact ENNReal.mul_ne_top (by norm_num) (ENNReal.rpow_ne_top_of_nonneg
    (by positivity) (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,ENNReal.ofReal_ne_top⟩))
theorem operator_common_endpoint_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    (T : (X → ℂ) → Y → ℂ)
    (hTm : ∀ g, Measurable g → Integrable g μ → Measurable (T g))
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    {q₀ p q₁ M : ℝ} (hq₀ : 0 < q₀) (h0p : q₀ < p) (hp1 : p < q₁) (hM : 0 < M)
    (hbound₀ : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q₀) μ →
      MemLp g (.ofReal q₁) μ → eLpNorm (T g) (.ofReal q₀) ν ≤ .ofReal M * eLpNorm g (.ofReal q₀) μ)
    (hbound₁ : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q₀) μ →
      MemLp g (.ofReal q₁) μ → eLpNorm (T g) (.ofReal q₁) ν ≤ .ofReal M * eLpNorm g (.ofReal q₁) μ)
    {f : X → ℂ} (hf : Measurable f) (hfi : Integrable f μ)
    (hf₀ : MemLp f (.ofReal q₀) μ) (hf₁ : MemLp f (.ofReal q₁) μ) :
    eLpNorm (T f) (.ofReal p) ν ≤
      finiteInterpolationConstant q₀ p q₁ * .ofReal M * eLpNorm f (.ofReal p) μ := by
  let S : (X → ℂ) → Y → ℂ := fun g => M⁻¹ • T g
  have hSm : ∀ g, Measurable g → Integrable g μ → Measurable (S g) :=
    fun g hg hi => (hTm g hg hi).const_smul _
  have hSa : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      S (fun x => g x + h x) y = S g y + S h y := by
    intro g h hg hh y
    change M⁻¹ • T (fun x => g x + h x) y = M⁻¹ • T g y + M⁻¹ • T h y
    rw [hadd g h hg hh, smul_add]
  have hn {q : ℝ} {g : X → ℂ}
      (hb : eLpNorm (T g) (.ofReal q) ν ≤ .ofReal M * eLpNorm g (.ofReal q) μ) :
      eLpNorm (S g) (.ofReal q) ν ≤ 1 * eLpNorm g (.ofReal q) μ := by
    exact (norm_real_normalized_le ν (T g) (.ofReal q) hM hb).trans_eq (by
      rw [ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top])
  have H := operator_two_moment_bound μ ν S hSm hSa hq₀ h0p hp1
    (A := 1) (B := 1)
    (fun g hg hi h0 h1 => by
      simpa only [ENNReal.one_rpow] using (moment_le_of_norm_le μ ν hg (hSm g hg hi)
        hq₀ (hn (hbound₀ g hg hi h0 h1))))
    (fun g hg hi h0 h1 => by
      simpa only [ENNReal.one_rpow] using (moment_le_of_norm_le μ ν hg (hSm g hg hi)
        (hq₀.trans (h0p.trans hp1)) (hn (hbound₁ g hg hi h0 h1))))
    hf hfi hf₀ hf₁
  rw [norm_restore_real_scale ν (T f) (.ofReal p) hM]
  have H' := mul_le_mul' (le_refl (.ofReal M)) H
  simpa only [S, one_mul, finiteInterpolationConstant] using H'.trans_eq (by ring_nf)
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.High
section
open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
def infinityInterpolationConstant (q p : ℝ) : ℝ≥0∞ :=
  2 * (.ofReal (p / (p - q))) ^ (1 / p)
theorem infinityInterpolationConstant_ne_top {q p : ℝ} (hp : 0 < p) :
    infinityInterpolationConstant q p ≠ ⊤ := by
  exact ENNReal.mul_ne_top (by norm_num) (ENNReal.rpow_ne_top_of_nonneg
    (by positivity) ENNReal.ofReal_ne_top)
theorem operator_finite_infinity_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [SFinite μ] (ν : Measure Y)
    (T : (X → ℂ) → Y → ℂ)
    (hTm : ∀ g, Measurable g → Integrable g μ → Measurable (T g))
    (hadd : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      T (fun x => g x + h x) y = T g y + T h y)
    {q p A B : ℝ} (hq : 0 < q) (hqp : q < p) (hA : 0 < A) (hB : 0 < B)
    (hbound : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q) μ →
      eLpNorm (T g) (.ofReal q) ν ≤ .ofReal A * eLpNorm g (.ofReal q) μ)
    (hinf : ∀ g, Measurable g → Integrable g μ → ∀ t : ℝ, 0 < t →
      (∀ x, ‖g x‖ ≤ t) → ∀ᵐ y ∂ν, ‖T g y‖ ≤ B * t)
    {f : X → ℂ} (hf : Measurable f) (hfi : Integrable f μ) (hfq : MemLp f (.ofReal q) μ) :
    eLpNorm (T f) (.ofReal p) ν ≤ infinityInterpolationConstant q p *
      .ofReal (A ^ (q / p) * B ^ (1 - q / p)) * eLpNorm f (.ofReal p) μ := by
  let S : (X → ℂ) → Y → ℂ := fun g => B⁻¹ • T g
  have hSm : ∀ g, Measurable g → Integrable g μ → Measurable (S g) :=
    fun g hg hi => (hTm g hg hi).const_smul _
  have hSa : ∀ g h, Integrable g μ → Integrable h μ → ∀ y,
      S (fun x => g x + h x) y = S g y + S h y := by
    intro g h hg hh y
    change B⁻¹ • T (fun x => g x + h x) y = B⁻¹ • T g y + B⁻¹ • T h y
    rw [hadd g h hg hh, smul_add]
  have hSb : ∀ g, Measurable g → Integrable g μ → MemLp g (.ofReal q) μ →
      (∫⁻ y, ‖S g y‖ₑ ^ q ∂ν) ≤ (.ofReal (B⁻¹ * A)) ^ q * ∫⁻ x, ‖g x‖ₑ ^ q ∂μ := by
    intro g hg hi hqg
    apply moment_le_of_norm_le μ ν hg (hSm g hg hi) hq
    have H := norm_real_normalized_le ν (T g) (.ofReal q) hB (hbound g hg hi hqg)
    simpa only [S, ENNReal.ofReal_mul (inv_nonneg.mpr hB.le),
      ENNReal.ofReal_inv_of_pos hB] using H
  have hSi : ∀ g, Measurable g → Integrable g μ → ∀ t : ℝ, 0 < t →
      (∀ x, ‖g x‖ ≤ t) → ∀ᵐ y ∂ν, ‖S g y‖ ≤ t := by
    intro g hg hi t ht hb
    filter_upwards [hinf g hg hi t ht hb] with y hy
    change ‖B⁻¹ • T g y‖ ≤ t
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
    calc
      _ ≤ B⁻¹ * (B * t) := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hB.le)
      _ = t := by field_simp
  have H := operator_infinity_moment_bound μ ν S hSm hSa hq hqp hSb hSi hf hfi hfq
  rw [norm_restore_real_scale ν (T f) (.ofReal p) hB]
  refine (mul_le_mul' (le_refl (.ofReal B)) H).trans_eq ?_
  have hp : 0 < p := hq.trans hqp
  have hc : B * (B⁻¹ * A) ^ (q / p) = A ^ (q / p) * B ^ (1 - q / p) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hB.le) hA.le, Real.inv_rpow hB.le,
      Real.rpow_sub hB]
    simp only [Real.rpow_one]
    ring
  rw [ENNReal.mul_rpow_of_nonneg _ _ (show 0 ≤ 1 / p by positivity),
    ← ENNReal.rpow_mul]
  rw [show q * (1 / p) = q / p by ring]
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (inv_nonneg.mpr hB.le) hA.le)
    (div_nonneg hq.le hp.le)]
  unfold infinityInterpolationConstant
  rw [show .ofReal B * (2 * (.ofReal ((B⁻¹ * A) ^ (q / p)) *
      (.ofReal (p / (p - q))) ^ (1 / p)) * eLpNorm f (.ofReal p) μ) =
      (2 * (.ofReal (p / (p - q))) ^ (1 / p)) *
        (.ofReal B * .ofReal ((B⁻¹ * A) ^ (q / p))) * eLpNorm f (.ofReal p) μ by ring]
  rw [← ENNReal.ofReal_mul hB.le, hc]
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Bounds
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
theorem finite_constant_majorant {A : ℝ≥0∞} (hA : A ≠ ⊤) :
    ∃ C : ℝ, 0 < C ∧ A ≤ .ofReal C := by
  refine ⟨A.toReal+1,by positivity,?_⟩
  calc
    A = .ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
theorem frequency_bound_below_critical {n : ℕ} (hn : 2 ≤ n) {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) (E : FrequencyEndpoints n φ)
    {p : ℝ} (hp : 2 < p) (hpq : p < OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal (C * h ^ (-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) * (1+Real.log (1/h)) ^ (2*n+5)) *
        eLpNorm f (.ofReal p) volume := by
  obtain ⟨D,hD,hKD⟩ := finite_constant_majorant
    (finiteInterpolationConstant_ne_top (q₀ := 2) (q₁ := OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) (by linarith : 0 < p))
  refine ⟨D*(E.twoConstant+E.criticalConstant),mul_pos hD (add_pos E.two_pos E.critical_pos),?_⟩
  intro h hh h1 f
  let L := 1+Real.log (1/h)
  have hL : 1 ≤ L := logarithm_weight_one_le hh h1
  have hpow : 1 ≤ L ^ (2*n+5) := one_le_pow₀ hL
  have hpw : 0 < L ^ (2*n+5) := lt_of_lt_of_le zero_lt_one hpow
  let M := (E.twoConstant+E.criticalConstant)*L^(2*n+5)
  have hM : 0 < M := mul_pos (add_pos E.two_pos E.critical_pos) hpw
  have h2M : E.twoConstant ≤ M := by
    calc
      _ ≤ E.twoConstant+E.criticalConstant := le_add_of_nonneg_right E.critical_pos.le
      _ ≤ M := le_mul_of_one_le_right (add_pos E.two_pos E.critical_pos).le hpow
  have hcM : E.criticalConstant*L^(2*n+5) ≤ M :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left E.two_pos.le) hpw.le
  have H := operator_common_endpoint_bound volume (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n)
    (fun g z => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 g z.1)
    (fun g hg hi => measurable_frequencyWave hφ hs hh hg hi)
    (fun g k hg hk z => frequencyHalfWave_add hφ hs hh z.2 hg hk z.1)
    (by norm_num : (0:ℝ)<2) hp hpq hM
    (fun g hg hi h2 _ => by
      have H2 := E.two h hh h1 g hg hi (by simpa using h2)
      exact (by simpa using H2 : eLpNorm (fun z : Space n × ℝ => frequencyHalfWave φ h z.2 g z.1)
        (.ofReal 2) (observationMeasure n) ≤ .ofReal E.twoConstant * eLpNorm g (.ofReal 2) volume).trans
          (mul_le_mul' (ENNReal.ofReal_le_ofReal h2M) le_rfl))
    (fun g hg hi _ hq => (E.critical h hh h1 g hg hi hq).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hcM) le_rfl))
    f.continuous.measurable f.integrable (f.memLp _ volume) (f.memLp _ volume)
  have hcoef : finiteInterpolationConstant 2 p (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) * .ofReal M ≤
      .ofReal (D*(E.twoConstant+E.criticalConstant)*L^(2*n+5)) := by
    calc
      _ ≤ ENNReal.ofReal D * ENNReal.ofReal M := mul_le_mul' hKD le_rfl
      _ = _ := by rw [← ENNReal.ofReal_mul hD.le]; congr 1; dsimp [M]; ring
  have H' := H.trans (mul_le_mul' hcoef le_rfl)
  simpa only [smoothingOrder_of_le_critical hn (by linarith) hpq.le,
    neg_zero, Real.rpow_zero, mul_one, L] using H'
theorem frequency_bound_above_critical {n : ℕ} (hn : 2 ≤ n) {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) (E : FrequencyEndpoints n φ)
    {p : ℝ} (hqp : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal (C * h ^ (-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) * (1+Real.log (1/h)) ^ (2*n+5)) *
        eLpNorm f (.ofReal p) volume := by
  have hq : 0 < OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := lt_trans (by norm_num) (criticalExponent_gt_two hn)
  have hp : 0 < p := hq.trans hqp
  let θ := OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n/p
  have ht : 0 ≤ θ := div_nonneg hq.le hp.le
  have ht1 : θ ≤ 1 := (div_le_one hp).mpr hqp.le
  obtain ⟨D,hD,hKD⟩ := finite_constant_majorant (infinityInterpolationConstant_ne_top (q := OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) hp)
  let C := D * (E.criticalConstant^θ * E.infinityConstant^(1-θ))
  have hC : 0 < C := mul_pos hD (mul_pos (Real.rpow_pos_of_pos E.critical_pos _)
    (Real.rpow_pos_of_pos E.infinity_pos _))
  refine ⟨C,hC,?_⟩
  intro h hh h1 f
  let L := 1+Real.log (1/h)
  have hL : 1 ≤ L := logarithm_weight_one_le hh h1
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have H := operator_finite_infinity_bound volume (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n)
    (fun g z => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 g z.1)
    (fun g hg hi => measurable_frequencyWave hφ hs hh hg hi)
    (fun g k hg hk z => frequencyHalfWave_add hφ hs hh z.2 hg hk z.1)
    hq hqp (mul_pos E.critical_pos (pow_pos hLp _))
    (mul_pos E.infinity_pos (Real.rpow_pos_of_pos hh _))
    (fun g hg hi hqg => E.critical h hh h1 g hg hi hqg)
    (fun g hg hi M hM hb => E.infinity h hh h1 g hg hi M hM hb)
    f.continuous.measurable f.integrable (f.memLp _ volume)
  have hb := interpolation_factor_le (a := -((n:ℝ)-1)/2) (k := 2*n+5)
    E.critical_pos E.infinity_pos hL hh ht ht1
  rw [high_frequency_exponent hn hqp.le] at hb
  have hc : infinityInterpolationConstant (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) p *
      .ofReal ((E.criticalConstant*L^(2*n+5))^θ *
        (E.infinityConstant*h^(-((n:ℝ)-1)/2))^(1-θ)) ≤
      .ofReal (C*h^(-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p)*L^(2*n+5)) := by
    calc
      _ ≤ .ofReal D * .ofReal ((E.criticalConstant^θ*E.infinityConstant^(1-θ))*
          h^(-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p)*L^(2*n+5)) := mul_le_mul' hKD (ENNReal.ofReal_le_ofReal hb)
      _ = _ := by rw [← ENNReal.ofReal_mul hD.le]; congr 1; dsimp [C]; ring
  exact H.trans (mul_le_mul' hc le_rfl)
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end

-- OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Basic
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation
theorem frequency_bound_of_logarithmicRefinement (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 2 ≤ p) {φ : Space n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal (C * h ^ (-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) * (1+Real.log (1/h)) ^ (2*n+5)) *
        eLpNorm f (.ofReal p) volume := by
  obtain ⟨E⟩ := frequency_endpoints_of_logarithmicRefinement hlog hn hφ hs hz
  have Hb : ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal (C * h ^ (-OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) * (1+Real.log (1/h)) ^ (2*n+5)) *
        eLpNorm f (.ofReal p) volume := by
    rcases eq_or_lt_of_le hp with rfl | hp
    · refine ⟨E.twoConstant,E.two_pos,?_⟩
      intro h hh h1 f
      have H := E.two h hh h1 f f.continuous.measurable f.integrable (f.memLp _ volume)
      have hweight : 1 ≤ (1+Real.log (1/h))^(2*n+5) := one_le_pow₀ (logarithm_weight_one_le hh h1)
      have hc : E.twoConstant ≤ E.twoConstant*(1+Real.log (1/h))^(2*n+5) :=
        le_mul_of_one_le_right E.two_pos.le hweight
      simpa only [ENNReal.ofReal_ofNat,OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder_two,neg_zero,Real.rpow_zero,mul_one] using
        H.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl)
    · rcases lt_trichotomy p (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) with hpq | rfl | hqp
      · exact frequency_bound_below_critical hn hφ.continuous hs E hp hpq
      · refine ⟨E.criticalConstant,E.critical_pos,?_⟩
        intro h hh h1 f
        simpa only [smoothingOrder_of_le_critical hn (by linarith [criticalExponent_gt_two hn]) le_rfl,
          neg_zero,Real.rpow_zero,mul_one] using
          E.critical h hh h1 f f.continuous.measurable f.integrable (f.memLp _ volume)
      · exact frequency_bound_above_critical hn hφ.continuous hs E hqp
  obtain ⟨C,hC,hb⟩ := Hb
  refine ⟨C,hC,?_⟩
  intro h hh h1 f
  have H := hb h hh h1 f
  refine ⟨⟨(measurable_frequencyWave hφ.continuous hs hh f.continuous.measurable f.integrable).aestronglyMeasurable, H.trans_lt ?_⟩,H⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp _ volume).eLpNorm_lt_top
end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
end
end
open MeasureTheory OMA.S_wpc_local_smoothing_conjecture
open scoped RealInnerProductSpace ContDiff ENNReal Topology
noncomputable section
namespace LSLeaf
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
def frequencyHalfWave {n : ℕ} (φ : Space n → ℂ) (h t : ℝ)
    (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦ Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
    φ (h • ξ) * angularFourier f ξ)
def order (n : ℕ) (p : ℝ) := ((n:ℝ)-1)*(1/2-1/p)-1/p
end LSLeaf
open LSLeaf
theorem OMA.solution : OMA.R_wpc_local_smoothing_conjecture_R1_H1_R1_H2_R1_H1_R1.H1 := by
  intro hlog n hn p hp
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n:ℝ)-1 := by linarith
  have hc := (div_le_iff₀ hd).mp hp
  have hp2 : 2 ≤ p := by by_contra! h; nlinarith [mul_lt_mul_of_pos_right h hd]
  have hp0 : 0 < p := by linarith
  have hn_div : (n:ℝ)/p ≤ (n-1)/2 := (div_le_iff₀ hp0).mpr (by nlinarith)
  have he : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p = order n p := by
    rw [OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder, max_eq_right (sub_nonneg.mpr hn_div), order]
    field_simp <;> ring
  obtain ⟨C,hC,H⟩ := OAI.Analysis.Fourier.LocalSmoothing.Interpolation.frequency_bound_of_logarithmicRefinement hlog hn hp2 (contDiff_smoothingAnnularCutoff n)
    (hasCompactSupport_smoothingAnnularCutoff n) (zero_notMem_tsupport_smoothingAnnularCutoff n)
  refine ⟨C,hC.le,fun h hh h1 f => ?_⟩
  change eLpNorm _ _ _ ≤ .ofReal (C * h ^ (-order n p) * _) * _
  rw [← he]
  exact (H h hh h1 f).2
