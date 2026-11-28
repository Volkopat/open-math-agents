import OMAReductions.R_Kakeya_kakeya_set_conjecture_R3
import Mathlib

/-!
Hypothesis H2 of the reduction Kakeya.kakeya_set_conjecture.R3.

The mathematical development below is the Lean formalization by OpenAI
(github.com/openai/math, directory lean/OAI/MeasureTheory/Kakeya and the files it imports
from lean/OAI/Analysis/Fourier), released under the Apache License 2.0. It is ported here
to this Mathlib with small edits and concatenated into one file. The final theorem is glue
code connecting the OpenAI endpoint kakeyaMaximal_implies_kakeya to the hypothesis H2.
-/

theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    (if hc : c then a hc else b hc) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    (if hc : c then a hc else b hc) = b h := dif_neg h
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
theorem halfWaveL2_time_energy {n : ℕ} (f : WaveL2 n) :
    (∫ t : ℝ in (1 : ℝ)..2, ‖halfWaveL2 t f‖ ^ 2) = ‖f‖ ^ 2 := by
  simp only [norm_halfWaveL2, intervalIntegral.integral_const, smul_eq_mul]
  norm_num
@[simp] theorem wavePhase_zero {n : ℕ} (ξ : Space n) : wavePhase 0 ξ = 1 := by
  simp [wavePhase]
theorem wavePhase_add {n : ℕ} (s t : ℝ) (ξ : Space n) :
    wavePhase (s + t) ξ = wavePhase s ξ * wavePhase t ξ := by
  simp only [wavePhase, mul_add, add_mul, Complex.ofReal_add, Complex.exp_add]
@[simp] theorem phaseMultiply_zero {n : ℕ} (f : WaveL2 n) :
    phaseMultiply 0 f = f := by
  apply Lp.ext
  filter_upwards [phaseMultiply_coe 0 f] with ξ hξ
  simpa using hξ
theorem phaseMultiply_add {n : ℕ} (s t : ℝ) (f : WaveL2 n) :
    phaseMultiply (s + t) f = phaseMultiply s (phaseMultiply t f) := by
  apply Lp.ext
  filter_upwards [phaseMultiply_coe (s + t) f,
    phaseMultiply_coe s (phaseMultiply t f), phaseMultiply_coe t f] with ξ h₁ h₂ h₃
  rw [h₁, h₂, h₃, wavePhase_add, mul_assoc]
theorem phaseMultiply_map_add {n : ℕ} (t : ℝ) (f g : WaveL2 n) :
    phaseMultiply t (f + g) = phaseMultiply t f + phaseMultiply t g := by
  apply Lp.ext
  filter_upwards [phaseMultiply_coe t (f + g), phaseMultiply_coe t f,
    phaseMultiply_coe t g, Lp.coeFn_add f g,
    Lp.coeFn_add (phaseMultiply t f) (phaseMultiply t g)] with ξ h h₁ h₂ h₃ h₄
  simp only [h, h₄, h₃, Pi.add_apply, h₁, h₂, mul_add]
theorem phaseMultiply_map_smul {n : ℕ} (t : ℝ) (c : ℂ) (f : WaveL2 n) :
    phaseMultiply t (c • f) = c • phaseMultiply t f := by
  apply Lp.ext
  filter_upwards [phaseMultiply_coe t (c • f), phaseMultiply_coe t f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (phaseMultiply t f)] with ξ h h₁ h₂ h₃
  simp only [h, h₃, h₂, Pi.smul_apply, h₁, smul_eq_mul]
  ring
def phaseMultiplyEquiv {n : ℕ} (t : ℝ) : WaveL2 n ≃ₗᵢ[ℂ] WaveL2 n where
  toFun := phaseMultiply t
  invFun := phaseMultiply (-t)
  left_inv f := by rw [← phaseMultiply_add]; simp
  right_inv f := by rw [← phaseMultiply_add]; simp
  map_add' := phaseMultiply_map_add t
  map_smul' := phaseMultiply_map_smul t
  norm_map' := norm_phaseMultiply t
def halfWaveEquiv {n : ℕ} (t : ℝ) : WaveL2 n ≃ₗᵢ[ℂ] WaveL2 n :=
  (Lp.fourierTransformₗᵢ (Space n) ℂ).trans
    ((phaseMultiplyEquiv t).trans (Lp.fourierTransformₗᵢ (Space n) ℂ).symm)
@[simp] theorem halfWaveEquiv_apply {n : ℕ} (t : ℝ) (f : WaveL2 n) :
    halfWaveEquiv t f = halfWaveL2 t f := rfl
@[simp] theorem halfWaveL2_zero {n : ℕ} (f : WaveL2 n) : halfWaveL2 0 f = f := by
  simp [halfWaveL2]
theorem halfWaveL2_add {n : ℕ} (s t : ℝ) (f : WaveL2 n) :
    halfWaveL2 (s + t) f = halfWaveL2 s (halfWaveL2 t f) := by
  simp [halfWaveL2, phaseMultiply_add]
end OAI.Analysis.Fourier.Wave
end
end
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
def logBesselPotential {n : ℕ} (s B : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦
    ((1 + ‖ξ‖ ^ 2) ^ (s / 2) *
      Real.log (2 + Real.sqrt (1 + ‖ξ‖ ^ 2)) ^ B : ℝ) • angularFourier f ξ)
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
def LogarithmicSobolev : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p B : ℝ, 2 < p → 2 * n + 6 < B →
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (logBesselPotential (smoothingOrder n p) B f) (ENNReal.ofReal p) ∧
      MemLp (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (observationMeasure n) ≤
      ENNReal.ofReal C *
        eLpNorm (logBesselPotential (smoothingOrder n p) B f) (ENNReal.ofReal p) volume
end OAI.Analysis.Fourier.LocalSmoothing
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction
def sphereMeasure (n : ℕ) : Measure (Space n) :=
  (volume : Measure (Space n)).toSphere.map Subtype.val
def sphericalExtension {n : ℕ} (g : Space n → ℂ) (x : Space n) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω ∂sphereMeasure n
def conjugateExponent (a : ℝ≥0∞) : ℝ :=
  if a = ∞ then 1 else a.toReal / (a.toReal - 1)
def SphericalRestrictionConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ a : ℝ≥0∞, 1 < a → ∀ b : ℝ,
    OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < b →
    ((n : ℝ) + 1) / ((n : ℝ) - 1) * conjugateExponent a < b →
    ∃ C : ℝ, 0 < C ∧ ∀ g : Space n → ℂ, MemLp g a (sphereMeasure n) →
      MemLp (sphericalExtension g) (ENNReal.ofReal b) ∧
      eLpNorm (sphericalExtension g) (ENNReal.ofReal b) volume ≤
        ENNReal.ofReal C * eLpNorm g a (sphereMeasure n)
end OAI.Analysis.Fourier.Restriction
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz
def bochnerRieszSymbol {n : ℕ} (δ R : ℝ) (ξ : Space n) : ℝ :=
  (max (1 - (‖ξ‖ / R) ^ 2) 0) ^ δ
def bochnerRiesz {n : ℕ} (δ R : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ bochnerRieszSymbol δ R ξ • OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ)
def bochnerRieszMaximal {n : ℕ} (δ : ℝ) (f : Space n → ℂ) (x : Space n) : ℝ≥0∞ :=
  ⨆ R : ℝ, ⨆ (_ : 0 < R), ‖bochnerRiesz δ R f x‖ₑ
def bochnerRieszIndex (n : ℕ) (p : ℝ≥0∞) : ℝ :=
  max ((n : ℝ) * |(p⁻¹).toReal - 1 / 2| - 1 / 2) 0
def BochnerRieszConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p : ℝ≥0∞, 1 ≤ p → ∀ δ : ℝ,
    bochnerRieszIndex n p < δ → ∃ C : ℝ, 0 < C ∧
      ∀ R : ℝ, 0 < R → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (bochnerRiesz δ R f) p ∧
      eLpNorm (bochnerRiesz δ R f) p volume ≤
        ENNReal.ofReal C * eLpNorm f p volume
def MaximalBochnerRieszConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p δ : ℝ, 2 ≤ p → OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ →
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (bochnerRieszMaximal δ f) (ENNReal.ofReal p) ∧
      eLpNorm (bochnerRieszMaximal δ f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume
end OAI.Analysis.Fourier.BochnerRiesz
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace OAI.MeasureTheory.Kakeya
def unitSegment {n : ℕ} (ω x : Space n) : Set (Space n) :=
  {y | ∃ t ∈ Set.Icc (- (1 / 2 : ℝ)) (1 / 2), y = x + t • ω}
def tube {n : ℕ} (δ : ℝ) (ω x : Space n) : Set (Space n) :=
  ⋃ t ∈ Set.Icc (- (1 / 2 : ℝ)) (1 / 2), Metric.ball (x + t • ω) δ
def kakeyaMaximal {n : ℕ} (δ : ℝ) (f : Space n → ℂ) (ω : Space n) : ℝ≥0∞ :=
  ⨆ x : Space n,
    (∫⁻ y in tube δ ω x, ‖f y‖ₑ) / volume (tube δ ω x)
def KakeyaMaximalConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ f : Space n → ℂ, MemLp f n →
    MemLp (kakeyaMaximal δ f) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ∧
    eLpNorm (kakeyaMaximal δ f) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ENNReal.ofReal (C * δ ^ (-ε)) * eLpNorm f n volume
def IsKakeyaSet {n : ℕ} (F : Set (Space n)) : Prop :=
  ∀ ω : Space n, ‖ω‖ = 1 → ∃ x, unitSegment ω x ⊆ F
def KakeyaConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ F : Set (Space n), IsKakeyaSet F →
    dimH F = n
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction
def radiusDerivativeSymbol {n : ℕ} (α r : ℝ) (ξ : Space n) : ℝ :=
  if ‖ξ‖ < r then
    2 * α * (‖ξ‖ ^ 2 / r ^ 2) * (1 - ‖ξ‖ ^ 2 / r ^ 2) ^ (α - 1)
  else 0
def radiusDerivative {n : ℕ} (α r : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ radiusDerivativeSymbol α r ξ • OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ)
def steinSquareFunction {n : ℕ} (α : ℝ) (f : Space n → ℂ) (x : Space n) : ℝ≥0∞ :=
  (∫⁻ r in Set.Ioi (0 : ℝ), ‖radiusDerivative α r f x‖ₑ ^ 2 /
    ENNReal.ofReal r) ^ (1 / 2 : ℝ)
def SteinSquareConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p α : ℝ, 2 ≤ p →
    max (1 / 2) ((n : ℝ) * (1 / 2 - 1 / p)) < α →
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (steinSquareFunction α f) (ENNReal.ofReal p) ∧
      eLpNorm (steinSquareFunction α f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume
end OAI.Analysis.Fourier.SquareFunction
end
end
section
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace OAI.MeasureTheory.Kakeya
theorem isOpen_tube {n : ℕ} (δ : ℝ) (ω x : Space n) : IsOpen (OAI.MeasureTheory.Kakeya.tube δ ω x) :=
  isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball
theorem measurableSet_tube {n : ℕ} (δ : ℝ) (ω x : Space n) :
    MeasurableSet (OAI.MeasureTheory.Kakeya.tube δ ω x) := (isOpen_tube δ ω x).measurableSet
theorem mem_tube_iff {n : ℕ} {δ : ℝ} {ω x y : Space n} :
    y ∈ OAI.MeasureTheory.Kakeya.tube δ ω x ↔
      ∃ t ∈ Set.Icc (- (1 / 2 : ℝ)) (1 / 2), dist y (x + t • ω) < δ := by
  simp [OAI.MeasureTheory.Kakeya.tube, Metric.mem_ball]
theorem center_ball_subset_tube {n : ℕ} (δ : ℝ) (ω x : Space n) :
    Metric.ball x δ ⊆ OAI.MeasureTheory.Kakeya.tube δ ω x := by
  intro y hy
  apply mem_tube_iff.mpr
  exact ⟨0, by norm_num, by simpa using hy⟩
theorem unitSegment_subset_tube {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (ω x : Space n) :
    OAI.MeasureTheory.Kakeya.unitSegment ω x ⊆ OAI.MeasureTheory.Kakeya.tube δ ω x := by
  rintro y ⟨t, ht, rfl⟩
  exact mem_tube_iff.mpr ⟨t, ht, by simpa using hδ⟩
theorem tube_mono {n : ℕ} {δ η : ℝ} (hδη : δ ≤ η) (ω x : Space n) :
    OAI.MeasureTheory.Kakeya.tube δ ω x ⊆ OAI.MeasureTheory.Kakeya.tube η ω x := by
  intro y hy
  rcases mem_tube_iff.mp hy with ⟨t, ht, hyt⟩
  exact mem_tube_iff.mpr ⟨t, ht, hyt.trans_le hδη⟩
theorem corresponding_segment_points_close {n : ℕ} {η t : ℝ} {ω v x : Space n}
    (ht : t ∈ Set.Icc (- (1 / 2 : ℝ)) (1 / 2)) (hωv : dist ω v ≤ η) :
    dist (x + t • ω) (x + t • v) ≤ η / 2 := by
  rw [dist_add_left, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
  have ht' : |t| ≤ 1 / 2 := abs_le.mpr ht
  have hnorm : ‖ω - v‖ ≤ η := by simpa only [dist_eq_norm] using hωv
  calc
    |t| * ‖ω - v‖ ≤ (1 / 2) * ‖ω - v‖ :=
      mul_le_mul_of_nonneg_right ht' (norm_nonneg _)
    _ ≤ (1 / 2) * η := mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = η / 2 := by ring
theorem tube_direction_inclusion {n : ℕ} {δ η : ℝ} {ω v x : Space n}
    (hωv : dist ω v ≤ η) : OAI.MeasureTheory.Kakeya.tube δ ω x ⊆ OAI.MeasureTheory.Kakeya.tube (δ + η / 2) v x := by
  intro y hy
  rcases mem_tube_iff.mp hy with ⟨t, ht, hyt⟩
  apply mem_tube_iff.mpr
  refine ⟨t, ht, ?_⟩
  calc
    dist y (x + t • v) ≤ dist y (x + t • ω) + dist (x + t • ω) (x + t • v) :=
      dist_triangle _ _ _
    _ < δ + η / 2 := add_lt_add_of_lt_of_le hyt (corresponding_segment_points_close ht hωv)
theorem tube_direction_inclusion_double {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    {ω v x : Space n} (hωv : dist ω v ≤ δ) : OAI.MeasureTheory.Kakeya.tube δ ω x ⊆ OAI.MeasureTheory.Kakeya.tube (2 * δ) v x :=
  (tube_direction_inclusion hωv).trans (tube_mono (by linarith) _ _)
theorem tube_subset_ball {n : ℕ} (δ : ℝ) (ω x : Space n) :
    OAI.MeasureTheory.Kakeya.tube δ ω x ⊆ Metric.ball x (δ + ‖ω‖ / 2) := by
  intro y hy
  rcases mem_tube_iff.mp hy with ⟨t, ht, hyt⟩
  have hp : dist (x + t • ω) x ≤ ‖ω‖ / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have hta : |t| ≤ 1 / 2 := abs_le.mpr ht
    nlinarith [mul_le_mul_of_nonneg_right hta (norm_nonneg ω)]
  exact lt_of_le_of_lt (dist_triangle _ _ _) (add_lt_add_of_lt_of_le hyt hp)
theorem volume_tube_lt_top {n : ℕ} (δ : ℝ) (ω x : Space n) :
    volume (OAI.MeasureTheory.Kakeya.tube δ ω x) < ∞ :=
  (measure_mono (tube_subset_ball δ ω x)).trans_lt measure_ball_lt_top
theorem volume_tube_pos {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (ω x : Space n) :
    0 < volume (OAI.MeasureTheory.Kakeya.tube δ ω x) :=
  (Metric.measure_ball_pos volume x hδ).trans_le (measure_mono (center_ball_subset_tube δ ω x))
theorem one_le_kakeyaMaximal_indicator {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {A : Set (Space n)} {ω x : Space n} (hA : OAI.MeasureTheory.Kakeya.tube δ ω x ⊆ A) :
    1 ≤ OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (A.indicator (fun _ ↦ (1 : ℂ))) ω := by
  have hi : (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) =
      volume (OAI.MeasureTheory.Kakeya.tube δ ω x) := by
    calc
      (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) =
          ∫⁻ _y in OAI.MeasureTheory.Kakeya.tube δ ω x, (1 : ℝ≥0∞) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_tube δ ω x)] with y hy
        simp [Set.indicator_of_mem (hA hy)]
      _ = _ := by simp
  have hq : (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) /
      volume (OAI.MeasureTheory.Kakeya.tube δ ω x) = 1 := by
    rw [hi, ENNReal.div_self (ne_of_gt (volume_tube_pos hδ ω x)) (volume_tube_lt_top δ ω x).ne]
  exact hq.symm.le.trans (le_iSup (fun x ↦
    (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ ω x)) x)
theorem sphere_phase_identity {n : ℕ} {ω v : Space n} (hω : ‖ω‖ = 1) (hv : ‖v‖ = 1) :
    inner ℝ v (ω - v) = -(‖ω - v‖ ^ 2) / 2 := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  have h := norm_sub_sq_real ω v
  rw [hω, hv] at h
  rw [hv]
  nlinarith [real_inner_comm ω v]
theorem cap_packet_phase_bound {n : ℕ} {δ c t : ℝ} {ω v z : Space n}
    (hδ : 0 < δ) (hc : 0 ≤ c) (hω : ‖ω‖ = 1) (hv : ‖v‖ = 1)
    (ht : |t| ≤ 1 / 2) (hz : ‖z‖ ≤ 2 * δ) (hcap : ‖ω - v‖ ≤ c * δ) :
    |inner ℝ (t • v + z) (ω - v) / δ ^ 2| ≤ c ^ 2 / 4 + 2 * c := by
  have hq := norm_nonneg (ω - v)
  have hq2 : ‖ω - v‖ ^ 2 ≤ (c * δ) ^ 2 := sq_le_sq₀ hq (mul_nonneg hc hδ.le) |>.mpr hcap
  have hqmul : δ * ‖ω - v‖ ≤ c * δ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hcap hδ.le]
  rw [abs_div, abs_of_pos (sq_pos_of_pos hδ)]
  apply (div_le_iff₀ (sq_pos_of_pos hδ)).mpr
  calc
    |inner ℝ (t • v + z) (ω - v)| ≤
      |inner ℝ (t • v) (ω - v)| + |inner ℝ z (ω - v)| := by
        rw [inner_add_left]
        exact abs_add_le _ _
    _ = |t| * (‖ω - v‖ ^ 2 / 2) + |inner ℝ z (ω - v)| := by
      rw [real_inner_smul_left, sphere_phase_identity hω hv, abs_mul, neg_div, abs_neg,
        abs_of_nonneg (by positivity : 0 ≤ ‖ω - v‖ ^ 2 / 2)]
    _ ≤ (1 / 2) * (‖ω - v‖ ^ 2 / 2) + (2 * δ) * ‖ω - v‖ := by
      apply add_le_add (mul_le_mul_of_nonneg_right ht (by positivity))
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hz hq)
    _ ≤ (c ^ 2 / 4 + 2 * c) * δ ^ 2 := by nlinarith
theorem cap_packet_phase_bound_small {n : ℕ} {δ t : ℝ} {ω v z : Space n}
    (hδ : 0 < δ) (hω : ‖ω‖ = 1) (hv : ‖v‖ = 1)
    (ht : |t| ≤ 1 / 2) (hz : ‖z‖ ≤ 2 * δ) (hcap : ‖ω - v‖ ≤ δ / 32) :
    |inner ℝ (t • v + z) (ω - v) / δ ^ 2| < 1 / 4 := by
  have h := cap_packet_phase_bound hδ (by norm_num : (0 : ℝ) ≤ 1 / 32)
    hω hv ht hz (by simpa only [one_div_mul_eq_div] using hcap)
  norm_num at h ⊢
  exact h.trans_lt (by norm_num)
end OAI.MeasureTheory.Kakeya
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.Restriction
instance sphereMeasure_isFinite (n : ℕ) : IsFiniteMeasure (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  unfold OAI.Analysis.Fourier.Restriction.sphereMeasure
  infer_instance
theorem norm_spherical_character {n : ℕ} (x ω : Space n) :
    ‖Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ))‖ = 1 := by
  simp [Complex.norm_exp]
theorem norm_spherical_integrand {n : ℕ} (g : Space n → ℂ) (x ω : Space n) :
    ‖Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω‖ = ‖g ω‖ := by
  rw [norm_mul, norm_spherical_character, one_mul]
theorem spherical_integrand_integrable {n : ℕ} {g : Space n → ℂ}
    (hg : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) (x : Space n) :
    Integrable (fun ω ↦ Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω)
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  apply hg.norm.mono'
  · have hchar : Continuous (fun ω : Space n ↦
        Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ))) := by fun_prop
    exact hchar.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · exact Eventually.of_forall fun ω ↦ (norm_spherical_integrand g x ω).le
theorem norm_sphericalExtension_le {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖ ≤ ∫ ω, ‖g ω‖ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
  unfold OAI.Analysis.Fourier.Restriction.sphericalExtension
  calc
    ‖∫ ω, Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n‖ ≤
      ∫ ω, ‖Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω‖ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n :=
        norm_integral_le_integral_norm _
    _ = ∫ ω, ‖g ω‖ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by simp only [norm_spherical_integrand]
theorem continuous_sphericalExtension {n : ℕ} {g : Space n → ℂ}
    (hg : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) : Continuous (OAI.Analysis.Fourier.Restriction.sphericalExtension g) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_integral_filter_of_dominated_convergence (fun ω ↦ ‖g ω‖)
  · exact Eventually.of_forall fun z ↦ (spherical_integrand_integrable hg z).aestronglyMeasurable
  · exact Eventually.of_forall fun z ↦
      Eventually.of_forall fun ω ↦ (norm_spherical_integrand g z ω).le
  · exact hg.norm
  · exact Eventually.of_forall fun ω ↦ Continuous.tendsto (by fun_prop) x
theorem enorm_sphericalExtension_le {n : ℕ} (g : Space n → ℂ) (x : Space n) :
    ‖OAI.Analysis.Fourier.Restriction.sphericalExtension g x‖ₑ ≤ ∫⁻ ω, ‖g ω‖ₑ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
  unfold OAI.Analysis.Fourier.Restriction.sphericalExtension
  calc
    ‖∫ ω, Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n‖ₑ ≤
      ∫⁻ ω, ‖Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω‖ₑ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ω, ‖g ω‖ₑ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      congr 1
      funext ω
      simp only [← ofReal_norm, norm_spherical_integrand]
theorem sphericalExtension_L1_Linfty {n : ℕ} {g : Space n → ℂ}
    (hg : MemLp g 1 (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) :
    MemLp (OAI.Analysis.Fourier.Restriction.sphericalExtension g) ∞ ∧
    eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) ∞ volume ≤ eLpNorm g 1 (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  have hgi : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := memLp_one_iff_integrable.mp hg
  have hm := (continuous_sphericalExtension hgi).aestronglyMeasurable (μ := volume)
  have hb : eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) ∞ volume ≤ eLpNorm g 1 (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    rw [eLpNorm_exponent_top, eLpNorm_one_eq_lintegral_enorm]
    exact eLpNormEssSup_le_of_ae_enorm_bound
      (Eventually.of_forall (enorm_sphericalExtension_le g))
  exact ⟨⟨hm, hb.trans_lt hg.eLpNorm_lt_top⟩, hb⟩
theorem sphericalExtension_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → Space n → ℂ) (hg : ∀ i ∈ s, Integrable (g i) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    (x : Space n) :
    OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ ∑ i ∈ s, g i ω) x = ∑ i ∈ s, OAI.Analysis.Fourier.Restriction.sphericalExtension (g i) x := by
  simp only [OAI.Analysis.Fourier.Restriction.sphericalExtension, Finset.mul_sum]
  exact integral_finsetSum s fun i hi ↦ spherical_integrand_integrable (hg i hi) x
theorem sphericalExtension_const_mul {n : ℕ} (c : ℂ) (g : Space n → ℂ) (x : Space n) :
    OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ c * g ω) x = c * OAI.Analysis.Fourier.Restriction.sphericalExtension g x := by
  unfold OAI.Analysis.Fourier.Restriction.sphericalExtension
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω ↦ by ring
theorem integral_norm_rpow_le_of_eLpNorm_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → ℂ} {g : β → ℂ}
    {p q C : ℝ} (hp : 0 < p) (hq : 0 < q) (hC : 0 ≤ C)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal q) ν)
    (hbound : eLpNorm g (ENNReal.ofReal q) ν ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) μ) :
    (∫ y, ‖g y‖ ^ q ∂ν) ≤ C ^ q * (∫ x, ‖f x‖ ^ p ∂μ) ^ (q / p) := by
  have hr := (ENNReal.toReal_le_toReal hg.eLpNorm_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top)).mpr hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at hr
  rw [toReal_eLpNorm hg.aestronglyMeasurable, toReal_eLpNorm hf.aestronglyMeasurable] at hr
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hpower := Real.rpow_le_rpow (lpNorm_nonneg (f := g)) hr hq.le
  rw [Real.mul_rpow hC lpNorm_nonneg] at hpower
  rw [lpNorm_eq_integral_norm_rpow_toReal hq0 ENNReal.ofReal_ne_top hg.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal hp0 ENNReal.ofReal_ne_top hf.aestronglyMeasurable] at hpower
  simp only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le] at hpower
  rw [← Real.rpow_mul (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _),
    inv_mul_cancel₀ hq.ne', Real.rpow_one,
    ← Real.rpow_mul (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)] at hpower
  convert hpower using 1
  congr 2
  ring
theorem small_phase_integral_lower_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (θ : α → ℝ) (hθ : Measurable θ)
    (hsmall : ∀ᵐ a ∂μ, |θ a| ≤ 1 / 4) :
    μ.real Set.univ / 2 ≤ ‖∫ a, Complex.exp (Complex.I * (θ a : ℂ)) ∂μ‖ := by
  have hn (a : α) : ‖Complex.exp (Complex.I * (θ a : ℂ))‖ = 1 := by
    simp [Complex.norm_exp]
  have hi : Integrable (fun a ↦ Complex.exp (Complex.I * (θ a : ℂ))) μ := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact ((Complex.measurable_ofReal.comp hθ).const_mul Complex.I).cexp.aestronglyMeasurable
    · exact Eventually.of_forall fun a ↦ (hn a).le
  have hre : ∀ᵐ a ∂μ, (1 / 2 : ℝ) ≤
      (Complex.exp (Complex.I * (θ a : ℂ))).re := by
    filter_upwards [hsmall] with a ha
    have habs := abs_le.mp ha
    have hcos := Real.one_sub_sq_div_two_le_cos (x := θ a)
    have hr : (Complex.exp (Complex.I * (θ a : ℂ))).re = Real.cos (θ a) := by
      simp [Complex.exp_re]
    rw [hr]
    nlinarith
  calc
    μ.real Set.univ / 2 = ∫ _ : α, (1 / 2 : ℝ) ∂μ := by
      simp [integral_const, smul_eq_mul, div_eq_mul_inv]
    _ ≤ ∫ a, (Complex.exp (Complex.I * (θ a : ℂ))).re ∂μ :=
      integral_mono_ae (integrable_const _) hi.re hre
    _ = (∫ a, Complex.exp (Complex.I * (θ a : ℂ)) ∂μ).re := integral_re hi
    _ ≤ ‖∫ a, Complex.exp (Complex.I * (θ a : ℂ)) ∂μ‖ := Complex.re_le_norm _
end OAI.Analysis.Fourier.Restriction
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace OAI.MeasureTheory.Kakeya
def packetCap {n : ℕ} (δ : ℝ) (v : Space n) : Set (Space n) :=
  {ω | ‖ω‖ = 1 ∧ ‖ω - v‖ ≤ δ / 32}
theorem measurableSet_packetCap {n : ℕ} (δ : ℝ) (v : Space n) :
    MeasurableSet (packetCap δ v) := by
  have hc : Continuous (fun ω : Space n ↦ ‖ω - v‖) := by fun_prop
  exact (isClosed_eq continuous_norm continuous_const).measurableSet.inter
    (isClosed_le hc continuous_const).measurableSet
theorem packetCaps_disjoint {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {v w : Space n} (hsep : δ ≤ dist v w) :
    Disjoint (packetCap δ v) (packetCap δ w) := by
  apply Set.disjoint_left.mpr
  intro ω hωv hωw
  have ht := dist_triangle v ω w
  have hv : dist v ω ≤ δ / 32 := by simpa only [dist_comm v ω, dist_eq_norm] using hωv.2
  have hw : dist ω w ≤ δ / 32 := by simpa only [dist_eq_norm] using hωw.2
  linarith
def capPacket {n : ℕ} (δ : ℝ) (v x : Space n) : Space n → ℂ :=
  (packetCap δ v).indicator (fun ω ↦
    Complex.exp (-Complex.I * ((inner ℝ x ω / δ ^ 2 : ℝ) : ℂ)))
theorem integrable_capPacket {n : ℕ} (δ : ℝ) (v x : Space n) :
    Integrable (capPacket δ v x) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  have hm : AEStronglyMeasurable
      (fun ω : Space n ↦ Complex.exp (-Complex.I * ((inner ℝ x ω / δ ^ 2 : ℝ) : ℂ)))
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by fun_prop
  apply Integrable.indicator _ (measurableSet_packetCap δ v)
  apply (integrable_const (1 : ℝ)).mono' hm
  exact Filter.Eventually.of_forall fun ω ↦ by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, zero_mul, mul_zero, sub_zero, Real.exp_zero, le_refl]
theorem norm_capPacket {n : ℕ} (δ : ℝ) (v x ω : Space n) :
    ‖capPacket δ v x ω‖ = (packetCap δ v).indicator (fun _ ↦ (1 : ℝ)) ω := by
  by_cases hω : ω ∈ packetCap δ v
  · simp only [capPacket, Set.indicator_of_mem hω, Complex.norm_exp, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, neg_zero, zero_mul, mul_zero, sub_zero, Real.exp_zero]
  · simp [capPacket, hω]
theorem norm_mul_capPacket_rpow {n : ℕ} (δ : ℝ) (v x ω : Space n)
    (c : ℂ) {p : ℝ} (hp : 0 < p) :
    ‖c * capPacket δ v x ω‖ ^ p =
      (packetCap δ v).indicator (fun _ ↦ ‖c‖ ^ p) ω := by
  rw [norm_mul, norm_capPacket]
  by_cases hω : ω ∈ packetCap δ v <;> simp [hω, Real.zero_rpow hp.ne']
theorem integrable_norm_mul_capPacket_rpow {n : ℕ} (δ : ℝ) (v x : Space n)
    (c : ℂ) {p : ℝ} (hp : 0 < p) :
    Integrable (fun ω ↦ ‖c * capPacket δ v x ω‖ ^ p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  simp_rw [norm_mul_capPacket_rpow δ v x _ c hp]
  exact (integrable_const _).indicator (measurableSet_packetCap δ v)
theorem integral_norm_mul_capPacket_rpow {n : ℕ} (δ : ℝ) (v x : Space n)
    (c : ℂ) {p : ℝ} (hp : 0 < p) :
    (∫ ω, ‖c * capPacket δ v x ω‖ ^ p ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
      ‖c‖ ^ p * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ v) := by
  simp_rw [norm_mul_capPacket_rpow δ v x _ c hp]
  rw [integral_indicator (measurableSet_packetCap δ v), setIntegral_const]
  simp only [smul_eq_mul, mul_comm]
theorem packet_phase_factorization {n : ℕ} (δ : ℝ) (x y v ω : Space n) :
    Complex.exp (Complex.I * ((inner ℝ ((δ ^ 2)⁻¹ • y) ω : ℝ) : ℂ)) *
      Complex.exp (-Complex.I * ((inner ℝ x ω / δ ^ 2 : ℝ) : ℂ)) =
    Complex.exp (Complex.I * ((inner ℝ (y - x) v / δ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((inner ℝ (y - x) (ω - v) / δ ^ 2 : ℝ) : ℂ)) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [real_inner_smul_left, inner_sub_left, inner_sub_right]
  push_cast
  ring
theorem norm_extension_capPacket {n : ℕ} (δ : ℝ) (v x y : Space n) :
    ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (capPacket δ v x) ((δ ^ 2)⁻¹ • y)‖ =
      ‖∫ ω in packetCap δ v,
        Complex.exp (Complex.I * ((inner ℝ (y - x) (ω - v) / δ ^ 2 : ℝ) : ℂ))
          ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n‖ := by
  have heq : OAI.Analysis.Fourier.Restriction.sphericalExtension (capPacket δ v x) ((δ ^ 2)⁻¹ • y) =
      Complex.exp (Complex.I * ((inner ℝ (y - x) v / δ ^ 2 : ℝ) : ℂ)) *
      ∫ ω in packetCap δ v,
        Complex.exp (Complex.I * ((inner ℝ (y - x) (ω - v) / δ ^ 2 : ℝ) : ℂ))
          ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
    calc
      OAI.Analysis.Fourier.Restriction.sphericalExtension (capPacket δ v x) ((δ ^ 2)⁻¹ • y) =
        ∫ ω in packetCap δ v,
          Complex.exp (Complex.I * ((inner ℝ ((δ ^ 2)⁻¹ • y) ω : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * ((inner ℝ x ω / δ ^ 2 : ℝ) : ℂ)) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
            rw [OAI.Analysis.Fourier.Restriction.sphericalExtension, ← integral_indicator (measurableSet_packetCap δ v)]
            apply integral_congr_ae
            exact Eventually.of_forall fun ω ↦ by
              by_cases hω : ω ∈ packetCap δ v <;> simp [capPacket, hω]
      _ = _ := by
        simp_rw [packet_phase_factorization δ x y v]
        exact integral_const_mul _ _
  rw [heq, norm_mul]
  have hnorm : ‖Complex.exp (Complex.I * ((inner ℝ (y - x) v / δ ^ 2 : ℝ) : ℂ))‖ = 1 := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Real.exp_zero]
  rw [hnorm, one_mul]
theorem cap_packet_lower_bound {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {v x y : Space n} (hv : ‖v‖ = 1) (hy : y ∈ OAI.MeasureTheory.Kakeya.tube (2 * δ) v x) :
    (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ v) / 2 ≤
      ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (capPacket δ v x) ((δ ^ 2)⁻¹ • y)‖ := by
  rcases mem_tube_iff.mp hy with ⟨t, ht, hyt⟩
  let z := y - (x + t • v)
  have hz : ‖z‖ ≤ 2 * δ := by simpa only [z, dist_eq_norm] using hyt.le
  have hyz : y - x = t • v + z := by dsimp [z]; abel
  have hsmall : ∀ᵐ ω ∂(OAI.Analysis.Fourier.Restriction.sphereMeasure n).restrict (packetCap δ v),
      |inner ℝ (y - x) (ω - v) / δ ^ 2| ≤ 1 / 4 := by
    filter_upwards [ae_restrict_mem (measurableSet_packetCap δ v)] with ω hω
    rw [hyz]
    exact (cap_packet_phase_bound_small hδ hω.1 hv (abs_le.mpr ht) hz hω.2).le
  have h := OAI.Analysis.Fourier.Restriction.small_phase_integral_lower_bound
    ((OAI.Analysis.Fourier.Restriction.sphereMeasure n).restrict (packetCap δ v))
    (fun ω ↦ inner ℝ (y - x) (ω - v) / δ ^ 2) (by fun_prop) hsmall
  rw [norm_extension_capPacket]
  simpa [Measure.real] using h
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Set Metric
open scoped ENNReal Pointwise
noncomputable section
namespace OAI.Analysis.Fourier.Restriction
theorem sphereMeasure_packetCap {n : ℕ} (δ : ℝ) (v : Space n) :
    OAI.Analysis.Fourier.Restriction.sphereMeasure n (OAI.MeasureTheory.Kakeya.packetCap δ v) =
      (n : ℝ≥0∞) * volume (Ioo (0 : ℝ) 1 • OAI.MeasureTheory.Kakeya.packetCap δ v) := by
  have himage : (Subtype.val : sphere (0 : Space n) 1 → Space n) ''
      ((Subtype.val : sphere (0 : Space n) 1 → Space n) ⁻¹' OAI.MeasureTheory.Kakeya.packetCap δ v) =
      OAI.MeasureTheory.Kakeya.packetCap δ v := by
    apply Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      refine ⟨⟨x, ?_⟩, hx, rfl⟩
      simpa only [mem_sphere, dist_zero_right] using hx.1
  rw [OAI.Analysis.Fourier.Restriction.sphereMeasure, Measure.map_apply measurable_subtype_coe (OAI.MeasureTheory.Kakeya.measurableSet_packetCap δ v),
    Measure.toSphere_apply' _ ((OAI.MeasureTheory.Kakeya.measurableSet_packetCap δ v).preimage measurable_subtype_coe),
    himage]
  simp [Space]
theorem norm_normalize_sub_unit_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x v : E} (hx : x ≠ 0) (hv : ‖v‖ = 1) {r : ℝ} (hr : 0 < r) :
    r * ‖‖x‖⁻¹ • x - v‖ ≤ 2 * ‖x - r • v‖ := by
  let u : E := ‖x‖⁻¹ • x
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, hxnorm]
  have hux : ‖x‖ • u = x := by simp [u, smul_smul, hxnorm]
  have hid : r • (u - v) = (r - ‖x‖) • u + (x - r • v) := by
    rw [sub_smul, hux, smul_sub]
    abel
  have hnormrv : ‖r • v‖ = r := by simp [norm_smul, hv, abs_of_pos hr]
  have hrev : |r - ‖x‖| ≤ ‖x - r • v‖ := by
    simpa only [hnormrv, norm_sub_rev] using abs_norm_sub_norm_le (r • v) x
  calc
    r * ‖‖x‖⁻¹ • x - v‖ = ‖r • (u - v)‖ := by simp [norm_smul, abs_of_pos hr, u]
    _ = ‖(r - ‖x‖) • u + (x - r • v)‖ := by rw [hid]
    _ ≤ ‖(r - ‖x‖) • u‖ + ‖x - r • v‖ := norm_add_le _ _
    _ = |r - ‖x‖| + ‖x - r • v‖ := by simp [norm_smul, hu]
    _ ≤ 2 * ‖x - r • v‖ := by linarith
theorem ball_subset_packetCap_cone {n : ℕ} {δ r : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1)
    (hrlo : 1 / 2 ≤ r) (hrhi : r ≤ 3 / 4) :
    ball (r • v) (δ / 512) ⊆ Ioo (0 : ℝ) 1 • OAI.MeasureTheory.Kakeya.packetCap δ v := by
  intro x hx
  have hdist : ‖x - r • v‖ < δ / 512 := hx
  have hr : 0 < r := by linarith
  have hnormrv : ‖r • v‖ = r := by simp [norm_smul, hv, abs_of_pos hr]
  have hx0 : x ≠ 0 := by
    intro hx0
    simp only [hx0, zero_sub, norm_neg, hnormrv] at hdist
    linarith
  have hx1 : ‖x‖ < 1 := by
    have ht := norm_add_le (x - r • v) (r • v)
    rw [sub_add_cancel, hnormrv] at ht
    linarith
  have hunit : ‖‖x‖⁻¹ • x‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr hx0]
  have hcap : ‖‖x‖⁻¹ • x - v‖ ≤ δ / 32 := by
    have ht := norm_normalize_sub_unit_mul hx0 hv hr
    have hn := norm_nonneg (‖x‖⁻¹ • x - v)
    nlinarith
  refine ⟨‖x‖, ⟨norm_pos_iff.mpr hx0, hx1⟩, ‖x‖⁻¹ • x, ⟨hunit, hcap⟩, ?_⟩
  simp [smul_smul, norm_ne_zero_iff.mpr hx0]
def capPackingCenter {n : ℕ} (δ : ℝ) (v : Space n) (j : ℕ) : Space n :=
  (1 / 2 + (j : ℝ) * δ / 4) • v
theorem capPacking_count_lower {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    1 / (2 * δ) ≤ (⌊1 / δ⌋₊ : ℝ) := by
  have hge : (1 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by simpa)
  have hfloor : 1 ≤ ⌊1 / δ⌋₊ := Nat.le_floor (by simpa using hge)
  have hfloor' : (1 : ℝ) ≤ (⌊1 / δ⌋₊ : ℝ) := by exact_mod_cast hfloor
  have hlt := Nat.lt_floor_add_one (1 / δ)
  have heq : 1 / (2 * δ) = (1 / δ) / 2 := by ring
  rw [heq]
  linarith
theorem capPacking_ball_subset {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1)
    {j : ℕ} (hj : j < ⌊1 / δ⌋₊) :
    ball (capPackingCenter δ v j) (δ / 512) ⊆ Ioo (0 : ℝ) 1 • OAI.MeasureTheory.Kakeya.packetCap δ v := by
  have hjle : (j : ℝ) ≤ 1 / δ :=
    (Nat.cast_le.mpr hj.le).trans (Nat.floor_le (by positivity))
  have hjmul : (j : ℝ) * δ ≤ 1 := (le_div_iff₀ hδ).mp hjle
  apply ball_subset_packetCap_cone hδ hδone hv
  · have hnonneg : 0 ≤ (j : ℝ) * δ / 4 := by positivity
    linarith
  · linarith
theorem capPacking_balls_disjoint {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (ball (capPackingCenter δ v i) (δ / 512))
      (ball (capPackingCenter δ v j) (δ / 512)) := by
  have hdiff : 1 ≤ |(i : ℝ) - j| := by
    rcases lt_or_gt_of_ne hij with h | h
    · have hcast : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
      have hlt : (i : ℝ) < j := by exact_mod_cast h
      rw [abs_of_neg (sub_neg.mpr hlt)]
      linarith
    · have hcast : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
      have hlt : (j : ℝ) < i := by exact_mod_cast h
      rw [abs_of_pos (sub_pos.mpr hlt)]
      linarith
  have hsep : δ / 4 ≤ dist (capPackingCenter δ v i) (capPackingCenter δ v j) := by
    rw [capPackingCenter, capPackingCenter, dist_eq_norm, ← sub_smul, norm_smul, hv,
      mul_one, Real.norm_eq_abs]
    have heq : (1 / 2 + (i : ℝ) * δ / 4) - (1 / 2 + (j : ℝ) * δ / 4) =
        ((i : ℝ) - j) * (δ / 4) := by ring
    rw [heq, abs_mul, abs_of_pos (by positivity : 0 < δ / 4)]
    nlinarith
  apply Metric.ball_disjoint_ball
  linarith
theorem capPacking_measure_le {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) :
    (∑ j ∈ Finset.range ⌊1 / δ⌋₊,
      volume (ball (capPackingCenter δ v j) (δ / 512))) ≤
      volume (Ioo (0 : ℝ) 1 • OAI.MeasureTheory.Kakeya.packetCap δ v) := by
  rw [← measure_biUnion_finset (fun i _ j _ hij ↦ capPacking_balls_disjoint hδ hv hij)
    (fun _ _ ↦ measurableSet_ball)]
  apply measure_mono
  intro x hx
  obtain ⟨j, hj, hx⟩ := mem_iUnion₂.mp hx
  exact capPacking_ball_subset hδ hδone hv (Finset.mem_range.mp hj) hx
theorem packetCap_measure_lower_floor {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) :
    (n : ℝ≥0∞) * (⌊1 / δ⌋₊ : ℝ≥0∞) * ENNReal.ofReal ((δ / 512) ^ n) *
      volume (ball (0 : Space n) 1) ≤ OAI.Analysis.Fourier.Restriction.sphereMeasure n (OAI.MeasureTheory.Kakeya.packetCap δ v) := by
  rw [sphereMeasure_packetCap]
  have h := capPacking_measure_le hδ hδone hv
  simp_rw [(volume : Measure (Space n)).addHaar_ball_of_pos _
    (show 0 < δ / 512 by positivity)] at h
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ (n : ℝ≥0∞) by positivity)
  simpa [Space, nsmul_eq_mul, mul_assoc] using hm
theorem packetCap_real_lower_floor {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) :
    (n : ℝ) * (⌊1 / δ⌋₊ : ℝ) * ((δ / 512) ^ n) *
      volume.real (ball (0 : Space n) 1) ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap δ v) := by
  have h := ENNReal.toReal_mono (measure_ne_top (OAI.Analysis.Fourier.Restriction.sphereMeasure n) _)
    (packetCap_measure_lower_floor hδ hδone hv)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (show 0 ≤ (δ / 512) ^ n by positivity), Measure.real] using h
theorem packetCap_real_lower {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) :
    ((n : ℝ) * volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n)) * δ ^ (n - 1) ≤
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap δ v) := by
  have hfloor := capPacking_count_lower hδ hδone
  have hvol : 0 ≤ volume.real (ball (0 : Space n) 1) := ENNReal.toReal_nonneg
  have hmono : (n : ℝ) * (1 / (2 * δ)) * ((δ / 512) ^ n) *
      volume.real (ball (0 : Space n) 1) ≤
      (n : ℝ) * (⌊1 / δ⌋₊ : ℝ) * ((δ / 512) ^ n) * volume.real (ball (0 : Space n) 1) := by
    gcongr
  have hp : δ ^ n = δ ^ (n - 1) * δ := by
    simpa only [Nat.sub_add_cancel hn] using pow_succ δ (n - 1)
  have heq : (n : ℝ) * (1 / (2 * δ)) * ((δ / 512) ^ n) *
      volume.real (ball (0 : Space n) 1) =
      ((n : ℝ) * volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n)) * δ ^ (n - 1) := by
    rw [div_pow, hp]
    field_simp
  rw [heq] at hmono
  exact hmono.trans (packetCap_real_lower_floor hδ hδone hv)
theorem packetCap_lower_coefficient_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < (n : ℝ) * volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hv : 0 < volume.real (ball (0 : Space n) 1) :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume _ zero_lt_one))
      measure_ball_lt_top.ne
  positivity
theorem packetCap_cone_subset_cover {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) :
    Ioo (0 : ℝ) 1 • OAI.MeasureTheory.Kakeya.packetCap δ v ⊆
      ⋃ j ∈ Finset.range (⌊1 / δ⌋₊ + 1), ball (((j : ℝ) * δ) • v) (2 * δ) := by
  rintro x ⟨r, hr, ω, hω, rfl⟩
  let j : ℕ := ⌊r / δ⌋₊
  have hj : j < ⌊1 / δ⌋₊ + 1 := by
    apply Nat.lt_succ_of_le
    exact Nat.floor_mono (div_le_div_of_nonneg_right hr.2.le hδ.le)
  have hjlo : (j : ℝ) * δ ≤ r := by
    exact (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg hr.1.le hδ.le))
  have hjhi : r < (j : ℝ) * δ + δ := by
    have ht := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (r / δ))
    dsimp [j]
    linarith
  apply mem_iUnion₂.mpr
  refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
  rw [mem_ball, dist_eq_norm]
  have hid : r • ω - ((j : ℝ) * δ) • v =
      r • (ω - v) + (r - (j : ℝ) * δ) • v := by
    rw [smul_sub, sub_smul]
    abel
  rw [hid]
  have hnorm : ‖r • (ω - v)‖ ≤ δ / 32 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
    calc r * ‖ω - v‖ ≤ 1 * (δ / 32) := mul_le_mul hr.2.le hω.2 (norm_nonneg _) (by norm_num)
         _ = δ / 32 := one_mul _
  have hnorm' : ‖(r - (j : ℝ) * δ) • v‖ < δ := by
    rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hjlo)]
    linarith
  exact (norm_add_le _ _).trans_lt (by linarith)
theorem capCover_count_upper {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) :
    (⌊1 / δ⌋₊ + 1 : ℝ) ≤ 2 / δ := by
  have hfloor := Nat.floor_le (by positivity : 0 ≤ 1 / δ)
  have hge : (1 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by simpa)
  have heq : 2 / δ = 2 * (1 / δ) := by ring
  rw [heq]
  linarith
theorem packetCap_measure_upper_floor {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) :
    OAI.Analysis.Fourier.Restriction.sphereMeasure n (OAI.MeasureTheory.Kakeya.packetCap δ v) ≤
      (n : ℝ≥0∞) * ((⌊1 / δ⌋₊ + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((2 * δ) ^ n) *
        volume (ball (0 : Space n) 1) := by
  rw [sphereMeasure_packetCap]
  have h := (measure_mono (packetCap_cone_subset_cover hδ hv)).trans
    (measure_biUnion_finset_le (μ := (volume : Measure (Space n))) _ _)
  simp_rw [(volume : Measure (Space n)).addHaar_ball_of_pos _
    (show 0 < 2 * δ by positivity)] at h
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ (n : ℝ≥0∞) by positivity)
  simpa [Space, nsmul_eq_mul, mul_assoc] using hm
theorem packetCap_real_upper_floor {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) :
    (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap δ v) ≤
      (n : ℝ) * (⌊1 / δ⌋₊ + 1 : ℝ) * ((2 * δ) ^ n) *
        volume.real (ball (0 : Space n) 1) := by
  have h := packetCap_measure_upper_floor hδ hv
  have hfin : (n : ℝ≥0∞) * ((⌊1 / δ⌋₊ + 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal ((2 * δ) ^ n) * volume (ball (0 : Space n) 1) ≠ ⊤ := by
    finiteness
  have ht := ENNReal.toReal_mono hfin h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_add,
    ENNReal.toReal_ofReal (show 0 ≤ (2 * δ) ^ n by positivity), Measure.real] using ht
theorem packetCap_real_upper {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) :
    (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap δ v) ≤
      ((n : ℝ) * 2 ^ (n + 1) * volume.real (ball (0 : Space n) 1)) * δ ^ (n - 1) := by
  have hfloor := capCover_count_upper hδ hδone
  have hvol : 0 ≤ volume.real (ball (0 : Space n) 1) := ENNReal.toReal_nonneg
  have hmono : (n : ℝ) * (⌊1 / δ⌋₊ + 1 : ℝ) * ((2 * δ) ^ n) *
      volume.real (ball (0 : Space n) 1) ≤
      (n : ℝ) * (2 / δ) * ((2 * δ) ^ n) * volume.real (ball (0 : Space n) 1) := by
    gcongr
  have hp : δ ^ n = δ ^ (n - 1) * δ := by
    simpa only [Nat.sub_add_cancel hn] using pow_succ δ (n - 1)
  have heq : (n : ℝ) * (2 / δ) * ((2 * δ) ^ n) * volume.real (ball (0 : Space n) 1) =
      ((n : ℝ) * 2 ^ (n + 1) * volume.real (ball (0 : Space n) 1)) * δ ^ (n - 1) := by
    rw [mul_pow, hp, pow_succ]
    field_simp
  exact (packetCap_real_upper_floor hδ hv).trans (hmono.trans_eq heq)
theorem packetCap_real_comparable {n : ℕ} (hn : 1 ≤ n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (δ : ℝ) (v : Space n), 0 < δ → δ ≤ 1 → ‖v‖ = 1 →
      c * δ ^ (n - 1) ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap δ v) ∧
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap δ v) ≤ C * δ ^ (n - 1) := by
  refine ⟨(n : ℝ) * volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n),
    (n : ℝ) * 2 ^ (n + 1) * volume.real (ball (0 : Space n) 1),
    packetCap_lower_coefficient_pos hn, ?_, ?_⟩
  · have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hv : 0 < volume.real (ball (0 : Space n) 1) :=
      ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume _ zero_lt_one))
        measure_ball_lt_top.ne
    positivity
  · intro δ v hδ hδone hv
    exact ⟨packetCap_real_lower hn hδ hδone hv, packetCap_real_upper hn hδ hδone hv⟩
end OAI.Analysis.Fourier.Restriction
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Set Metric
open scoped ENNReal Pointwise
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem preimage_add_tube_center {n : ℕ} (δ : ℝ) (v x : Space n) :
    (fun y ↦ x + y) ⁻¹' OAI.MeasureTheory.Kakeya.tube δ v x = OAI.MeasureTheory.Kakeya.tube δ v 0 := by
  ext y
  simp only [mem_preimage, mem_tube_iff, zero_add, dist_add_left]
theorem volume_tube_center_eq {n : ℕ} (δ : ℝ) (v x : Space n) :
    volume (OAI.MeasureTheory.Kakeya.tube δ v x) = volume (OAI.MeasureTheory.Kakeya.tube δ v 0) := by
  have h := measure_preimage_add (volume : Measure (Space n)) x (OAI.MeasureTheory.Kakeya.tube δ v x)
  rw [preimage_add_tube_center] at h
  exact h.symm
theorem volume_real_tube_center_eq {n : ℕ} (δ : ℝ) (v x : Space n) :
    volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) = volume.real (OAI.MeasureTheory.Kakeya.tube δ v 0) := by
  exact congrArg ENNReal.toReal (volume_tube_center_eq δ v x)
theorem packetCap_cone_volume_le_tube {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (v x : Space n) :
    volume (Ioo (0 : ℝ) 1 • packetCap δ v) ≤ volume (OAI.MeasureTheory.Kakeya.tube δ v x) := by
  have hsub : Ioo (0 : ℝ) 1 • packetCap δ v ⊆
      (fun y ↦ (x - (1 / 2 : ℝ) • v) + y) ⁻¹' OAI.MeasureTheory.Kakeya.tube δ v x := by
    rintro y ⟨r, hr, ω, hω, rfl⟩
    apply mem_tube_iff.mpr
    refine ⟨r - 1 / 2, ⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
    rw [dist_eq_norm]
    have hid : x - (1 / 2 : ℝ) • v + r • ω - (x + (r - 1 / 2) • v) =
        r • (ω - v) := by
      rw [smul_sub, sub_smul]
      abel
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
    have hle : r * ‖ω - v‖ ≤ δ / 32 := by
      calc r * ‖ω - v‖ ≤ 1 * (δ / 32) :=
             mul_le_mul hr.2.le hω.2 (norm_nonneg _) (by norm_num)
           _ = δ / 32 := one_mul _
    linarith
  have h := measure_mono (μ := (volume : Measure (Space n))) hsub
  rwa [measure_preimage_add] at h
theorem volume_tube_real_lower {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) (x : Space n) :
    (volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n)) * δ ^ (n - 1) ≤
      volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := ENNReal.toReal_mono (volume_tube_lt_top δ v x).ne
    (packetCap_cone_volume_le_tube hδ v x)
  change volume.real (Ioo (0 : ℝ) 1 • packetCap δ v) ≤ volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) at hm
  have heq : (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ v) =
      (n : ℝ) * volume.real (Ioo (0 : ℝ) 1 • packetCap δ v) := by
    simp only [Measure.real, OAI.Analysis.Fourier.Restriction.sphereMeasure_packetCap, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hl := OAI.Analysis.Fourier.Restriction.packetCap_real_lower hn hδ hδone hv
  rw [heq] at hl
  apply (mul_le_mul_iff_right₀ hn').mp
  calc
    (n : ℝ) * (volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n) * δ ^ (n - 1)) =
        ((n : ℝ) * volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n)) * δ ^ (n - 1) := by ring
    _ ≤ (n : ℝ) * volume.real (Ioo (0 : ℝ) 1 • packetCap δ v) := hl
    _ ≤ (n : ℝ) * volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) := mul_le_mul_of_nonneg_left hm hn'.le
theorem exists_volume_tube_real_lower {n : ℕ} (hn : 1 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ (δ : ℝ) (v x : Space n), 0 < δ → δ ≤ 1 → ‖v‖ = 1 →
      c * δ ^ (n - 1) ≤ volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) := by
  refine ⟨volume.real (ball (0 : Space n) 1) / (2 * 512 ^ n), ?_, ?_⟩
  · have hv : 0 < volume.real (ball (0 : Space n) 1) :=
      ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume _ zero_lt_one))
        measure_ball_lt_top.ne
    positivity
  · intro δ v x hδ hδone hv
    exact volume_tube_real_lower hn hδ hδone hv x
theorem tube_subset_ball_cover {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) (x : Space n) :
    OAI.MeasureTheory.Kakeya.tube δ v x ⊆ ⋃ j ∈ Finset.range (⌊1 / δ⌋₊ + 1),
      ball (x + ((j : ℝ) * δ - 1 / 2) • v) (2 * δ) := by
  intro y hy
  obtain ⟨t, ht, hyt⟩ := mem_tube_iff.mp hy
  let r : ℝ := t + 1 / 2
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [ht.1]
  have hr1 : r ≤ 1 := by dsimp [r]; linarith [ht.2]
  let j : ℕ := ⌊r / δ⌋₊
  have hj : j < ⌊1 / δ⌋₊ + 1 :=
    Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right hr1 hδ.le))
  have hjlo : (j : ℝ) * δ ≤ r :=
    (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg hr0 hδ.le))
  have hjhi : r < (j : ℝ) * δ + δ := by
    have h := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (r / δ))
    dsimp [j]
    linarith
  have hdist : dist (x + t • v) (x + ((j : ℝ) * δ - 1 / 2) • v) < δ := by
    rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.norm_eq_abs]
    have hlo : 0 ≤ t - ((j : ℝ) * δ - 1 / 2) := by dsimp [r] at hjlo; linarith
    rw [abs_of_nonneg hlo]
    dsimp [r] at hjhi
    linarith
  exact mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj,
    (dist_triangle y (x + t • v) _).trans_lt (by linarith)⟩
theorem volume_tube_upper_floor {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) (x : Space n) :
    volume (OAI.MeasureTheory.Kakeya.tube δ v x) ≤ ((⌊1 / δ⌋₊ + 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal ((2 * δ) ^ n) * volume (ball (0 : Space n) 1) := by
  have h := (measure_mono (tube_subset_ball_cover hδ hv x)).trans
    (measure_biUnion_finset_le (μ := (volume : Measure (Space n))) _ _)
  simp_rw [(volume : Measure (Space n)).addHaar_ball_of_pos _
    (show 0 < 2 * δ by positivity)] at h
  simpa [Space, nsmul_eq_mul, mul_assoc] using h
theorem volume_tube_real_upper_floor {n : ℕ} {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hv : ‖v‖ = 1) (x : Space n) :
    volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) ≤ (⌊1 / δ⌋₊ + 1 : ℝ) * ((2 * δ) ^ n) *
      volume.real (ball (0 : Space n) 1) := by
  have hfin : ((⌊1 / δ⌋₊ + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((2 * δ) ^ n) *
      volume (ball (0 : Space n) 1) ≠ ⊤ := by finiteness
  have h := ENNReal.toReal_mono hfin (volume_tube_upper_floor hδ hv x)
  simpa [ENNReal.toReal_mul, ENNReal.toReal_add,
    ENNReal.toReal_ofReal (show 0 ≤ (2 * δ) ^ n by positivity), Measure.real] using h
theorem volume_tube_real_upper {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} {v : Space n}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hv : ‖v‖ = 1) (x : Space n) :
    volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) ≤
      (2 ^ (n + 1) * volume.real (ball (0 : Space n) 1)) * δ ^ (n - 1) := by
  have hfloor := OAI.Analysis.Fourier.Restriction.capCover_count_upper hδ hδone
  have hvol : 0 ≤ volume.real (ball (0 : Space n) 1) := ENNReal.toReal_nonneg
  have hmono : (⌊1 / δ⌋₊ + 1 : ℝ) * ((2 * δ) ^ n) * volume.real (ball (0 : Space n) 1) ≤
      (2 / δ) * ((2 * δ) ^ n) * volume.real (ball (0 : Space n) 1) := by gcongr
  have hp : δ ^ n = δ ^ (n - 1) * δ := by
    simpa only [Nat.sub_add_cancel hn] using pow_succ δ (n - 1)
  have heq : (2 / δ) * ((2 * δ) ^ n) * volume.real (ball (0 : Space n) 1) =
      (2 ^ (n + 1) * volume.real (ball (0 : Space n) 1)) * δ ^ (n - 1) := by
    rw [mul_pow, hp, pow_succ]
    field_simp
  exact (volume_tube_real_upper_floor hδ hv x).trans (hmono.trans_eq heq)
theorem exists_volume_tube_real_upper {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ) (v x : Space n), 0 < δ → δ ≤ 1 → ‖v‖ = 1 →
      volume.real (OAI.MeasureTheory.Kakeya.tube δ v x) ≤ C * δ ^ (n - 1) := by
  refine ⟨2 ^ (n + 1) * volume.real (ball (0 : Space n) 1), ?_, ?_⟩
  · have hv : 0 < volume.real (ball (0 : Space n) 1) :=
      ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume _ zero_lt_one)) measure_ball_lt_top.ne
    positivity
  · intro δ v x hδ hδone hv
    exact volume_tube_real_upper hn hδ hδone hv x
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem lowerSemicontinuous_lintegral_family
    {P α : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [MeasurableSpace α] {μ : Measure α} (F : P → α → ℝ≥0∞)
    (hm : ∀ p, AEMeasurable (F p) μ) (hl : ∀ a, LowerSemicontinuous (fun p ↦ F p a)) :
    LowerSemicontinuous (fun p ↦ ∫⁻ a, F p a ∂μ) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro p
  calc
    (∫⁻ a, F p a ∂μ) ≤ ∫⁻ a, liminf (fun p ↦ F p a) (𝓝 p) ∂μ :=
      lintegral_mono fun a ↦ (hl a).le_liminf p
    _ ≤ liminf (fun p ↦ ∫⁻ a, F p a ∂μ) (𝓝 p) := lintegral_liminf_le' hm
theorem isOpen_tube_parameter_set {n : ℕ} (δ : ℝ) (y : Space n) :
    IsOpen {z : Space n × Space n | y ∈ OAI.MeasureTheory.Kakeya.tube δ z.1 z.2} := by
  have heq : {z : Space n × Space n | y ∈ OAI.MeasureTheory.Kakeya.tube δ z.1 z.2} =
      ⋃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
        {z : Space n × Space n | dist y (z.2 + t • z.1) < δ} := by
    ext z
    simp only [Set.mem_ofPred_eq, OAI.MeasureTheory.Kakeya.tube, Set.mem_iUnion, Metric.mem_ball]
  rw [heq]
  apply isOpen_iUnion
  intro t
  apply isOpen_iUnion
  intro _
  exact isOpen_lt (by fun_prop) continuous_const
def tubeMass {n : ℕ} (δ : ℝ) (f : Space n → ℂ) (v x : Space n) : ℝ≥0∞ :=
  ∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ v x, ‖f y‖ₑ
theorem lowerSemicontinuous_tubeMass {n : ℕ} (δ : ℝ) (f : Space n → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure (Space n))) :
    LowerSemicontinuous (fun z : Space n × Space n ↦ tubeMass δ f z.1 z.2) := by
  let F : (Space n × Space n) → Space n → ℝ≥0∞ :=
    fun z y ↦ (OAI.MeasureTheory.Kakeya.tube δ z.1 z.2).indicator (fun y ↦ ‖f y‖ₑ) y
  have hm (z : Space n × Space n) : AEMeasurable (F z) (volume : Measure (Space n)) :=
    hf.enorm.indicator (measurableSet_tube _ _ _)
  have hl (y : Space n) : LowerSemicontinuous (fun z ↦ F z y) := by
    change LowerSemicontinuous
      ({z : Space n × Space n | y ∈ OAI.MeasureTheory.Kakeya.tube δ z.1 z.2}.indicator (fun _ ↦ ‖f y‖ₑ))
    exact (isOpen_tube_parameter_set δ y).lowerSemicontinuous_indicator bot_le
  have h := lowerSemicontinuous_lintegral_family F hm hl
  convert h using 1
  funext z
  exact (lintegral_indicator (measurableSet_tube _ _ _) _).symm
theorem lowerSemicontinuous_iSup_slices {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (F : P × X → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    LowerSemicontinuous (fun p ↦ ⨆ x : X, F (p, x)) := by
  have hs (x : X) : LowerSemicontinuous (fun p : P ↦ F (p, x)) :=
    hF.comp (continuous_id.prodMk continuous_const)
  exact lowerSemicontinuous_iSup hs
theorem lowerSemicontinuous_sup_tubeMass {n : ℕ} (δ : ℝ) (f : Space n → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure (Space n))) :
    LowerSemicontinuous (fun v ↦ ⨆ x : Space n, tubeMass δ f v x) := by
  exact lowerSemicontinuous_iSup_slices (fun z : Space n × Space n ↦ tubeMass δ f z.1 z.2)
    (lowerSemicontinuous_tubeMass δ f hf)
theorem lowerSemicontinuous_volume_tube {n : ℕ} (δ : ℝ) :
    LowerSemicontinuous (fun v : Space n ↦ volume (OAI.MeasureTheory.Kakeya.tube δ v 0)) := by
  have h := (lowerSemicontinuous_tubeMass δ (fun _ : Space n ↦ (1 : ℂ))
    aestronglyMeasurable_const).comp
      (show Continuous (fun v : Space n ↦ (v, (0 : Space n))) by fun_prop)
  simpa [Function.comp_def, tubeMass] using h
theorem measurable_kakeyaMaximal {n : ℕ} (δ : ℝ) (f : Space n → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure (Space n))) :
    Measurable (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f) := by
  have heq : OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f = fun v ↦
      (⨆ x : Space n, tubeMass δ f v x) / volume (OAI.MeasureTheory.Kakeya.tube δ v 0) := by
    funext v
    change (⨆ x : Space n, tubeMass δ f v x / volume (OAI.MeasureTheory.Kakeya.tube δ v x)) = _
    simp_rw [volume_tube_center_eq]
    exact (ENNReal.iSup_div _ _).symm
  rw [heq]
  exact (lowerSemicontinuous_sup_tubeMass δ f hf).measurable.div
    (lowerSemicontinuous_volume_tube δ).measurable
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem line_ball_times_subset_interval {n : ℕ} {δ : ℝ} {ω x y : Space n}
    (hω : ‖ω‖ = 1) :
    {t : ℝ | y ∈ Metric.ball (x + t • ω) δ} ⊆
      Set.Ioo (inner ℝ (y - x) ω - δ) (inner ℝ (y - x) ω + δ) := by
  intro t ht
  change y ∈ Metric.ball (x + t • ω) δ at ht
  have he : inner ℝ (y - (x + t • ω)) ω = inner ℝ (y - x) ω - t := by
    rw [show y - (x + t • ω) = (y - x) - t • ω by abel,
      inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hω]
    ring
  have h := abs_real_inner_le_norm (y - (x + t • ω)) ω
  rw [he, hω, mul_one] at h
  have ha : |inner ℝ (y - x) ω - t| < δ := h.trans_lt (by
    simpa only [Metric.mem_ball, dist_eq_norm] using ht)
  obtain ⟨hleft, hright⟩ := abs_lt.mp ha
  exact ⟨by linarith, by linarith⟩
theorem line_ball_occupancy {n : ℕ} {δ : ℝ} (_hδ : 0 < δ)
    {ω x : Space n} (hω : ‖ω‖ = 1) {E : Set ℝ} (hE : MeasurableSet E)
    (hEI : E ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    {A : Set (Space n)} (hA : MeasurableSet A)
    (hthick : ∀ t ∈ E, Metric.ball (x + t • ω) δ ⊆ A) :
    volume E * volume (Metric.ball (0 : Space n) δ) ≤
      ENNReal.ofReal (2 * δ) * volume (A ∩ OAI.MeasureTheory.Kakeya.tube δ ω x) := by
  let S : Set (ℝ × Space n) :=
    {z | z.1 ∈ E ∧ z.2 ∈ Metric.ball (x + z.1 • ω) δ}
  have hS : MeasurableSet S := by
    apply (hE.preimage measurable_fst).inter
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  let F : ℝ → Space n → ℝ≥0∞ := fun t y ↦ S.indicator (fun _ ↦ 1) (t, y)
  have hF : Measurable (Function.uncurry F) := measurable_const.indicator hS
  have hfirst (t : ℝ) : (∫⁻ y, F t y) =
      E.indicator (fun _ ↦ volume (Metric.ball (0 : Space n) δ)) t := by
    by_cases ht : t ∈ E
    · have heq : F t = (Metric.ball (x + t • ω) δ).indicator (fun _ ↦ 1) := by
        funext y
        simp [F, S, Set.indicator, ht]
      rw [heq, lintegral_indicator measurableSet_ball]
      simp [ht, Measure.addHaar_ball_center]
    · have heq : F t = 0 := by funext y; simp [F, S, Set.indicator, ht]
      simp [heq, ht]
  have hsecond (y : Space n) : (∫⁻ t, F t y) ≤
      (A ∩ OAI.MeasureTheory.Kakeya.tube δ ω x).indicator (fun _ ↦ ENNReal.ofReal (2 * δ)) y := by
    by_cases hy : y ∈ A ∩ OAI.MeasureTheory.Kakeya.tube δ ω x
    · rw [Set.indicator_of_mem hy]
      calc
        (∫⁻ t, F t y) ≤ ∫⁻ t, (Set.Ioo (inner ℝ (y - x) ω - δ)
            (inner ℝ (y - x) ω + δ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) t := by
          apply lintegral_mono
          intro t
          by_cases ht : (t, y) ∈ S
          · have hi := line_ball_times_subset_interval hω ht.2
            simp [F, ht, hi]
          · simp [F, ht]
        _ = ENNReal.ofReal (2 * δ) := by
          rw [lintegral_indicator measurableSet_Ioo]
          simp only [lintegral_const, one_mul, Measure.restrict_apply_univ,
            Real.volume_Ioo]
          congr 1
          ring
    · have heq : (fun t ↦ F t y) = 0 := by
        funext t
        have ht : (t, y) ∉ S := by
          intro ht
          exact hy ⟨hthick t ht.1 ht.2, mem_tube_iff.mpr ⟨t, hEI ht.1, ht.2⟩⟩
        simp [F, ht]
      rw [heq, Set.indicator_of_notMem hy]
      change (∫⁻ t : ℝ, (0 : ℝ≥0∞)) ≤ 0
      simp
  calc
    volume E * volume (Metric.ball (0 : Space n) δ) = ∫⁻ t, ∫⁻ y, F t y := by
      simp_rw [hfirst]
      rw [lintegral_indicator hE]
      simp [mul_comm]
    _ = ∫⁻ y, ∫⁻ t, F t y := lintegral_lintegral_swap hF.aemeasurable
    _ ≤ ∫⁻ y, (A ∩ OAI.MeasureTheory.Kakeya.tube δ ω x).indicator (fun _ ↦ ENNReal.ofReal (2 * δ)) y :=
      lintegral_mono hsecond
    _ = _ := by rw [lintegral_indicator (hA.inter (measurableSet_tube _ _ _))]; simp
def lineOccupancyConstant (n : ℕ) : ℝ := 1 / 2 ^ (n + 2)
theorem lineOccupancyConstant_pos (n : ℕ) : 0 < lineOccupancyConstant n := by
  unfold lineOccupancyConstant
  positivity
theorem scaled_occupancy_average_le {e b t a d c : ℝ≥0∞}
    (ht : t ≠ 0) (ht' : t ≠ ∞) (hd : d ≠ 0) (hd' : d ≠ ∞)
    (hocc : e * b ≤ d * a) (hscale : d * c * t ≤ b) : c * e ≤ a / t := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl ht) (Or.inl ht')).mpr
  apply (ENNReal.mul_le_mul_iff_right hd hd').mp
  calc
    d * (c * e * t) = e * (d * c * t) := by ring
    _ ≤ e * b := mul_le_mul' le_rfl hscale
    _ ≤ d * a := hocc
theorem lineOccupancyConstant_volume_bound {n : ℕ} (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) {ω : Space n} (hω : ‖ω‖ = 1)
    (x : Space n) :
    ENNReal.ofReal (2 * δ) * ENNReal.ofReal (lineOccupancyConstant n) * volume (OAI.MeasureTheory.Kakeya.tube δ ω x) ≤
      volume (Metric.ball (0 : Space n) δ) := by
  have hvol : volume (OAI.MeasureTheory.Kakeya.tube δ ω x) ≤ ENNReal.ofReal
      ((2 ^ (n + 1) * volume.real (Metric.ball (0 : Space n) 1)) * δ ^ (n - 1)) := by
    calc
      _ = ENNReal.ofReal (volume.real (OAI.MeasureTheory.Kakeya.tube δ ω x)) :=
        (ENNReal.ofReal_toReal (volume_tube_lt_top _ _ _).ne).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (volume_tube_real_upper hn hδ hδone hω x)
  have hpow : δ ^ n = δ ^ (n - 1) * δ := by
    simpa only [Nat.sub_add_cancel hn] using pow_succ δ (n - 1)
  have heq : (2 * δ) * lineOccupancyConstant n *
      ((2 ^ (n + 1) * volume.real (Metric.ball (0 : Space n) 1)) * δ ^ (n - 1)) =
      δ ^ n * volume.real (Metric.ball (0 : Space n) 1) := by
    unfold lineOccupancyConstant
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, hpow]
    field_simp
  calc
    _ ≤ ENNReal.ofReal (2 * δ) * ENNReal.ofReal (lineOccupancyConstant n) * ENNReal.ofReal
        ((2 ^ (n + 1) * volume.real (Metric.ball (0 : Space n) 1)) * δ ^ (n - 1)) := by gcongr
    _ = ENNReal.ofReal (δ ^ n * volume.real (Metric.ball (0 : Space n) 1)) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * δ),
        ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (lineOccupancyConstant_pos n).le), heq]
    _ = volume (Metric.ball (0 : Space n) δ) := by
      rw [Measure.addHaar_ball_of_pos volume _ hδ]
      simp only [Space, finrank_euclideanSpace_fin]
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact ENNReal.ofReal_toReal measure_ball_lt_top.ne
theorem kakeya_indicator_ge_line_measure {n : ℕ} (hn : 1 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    {ω x : Space n} (hω : ‖ω‖ = 1) {E : Set ℝ} (hE : MeasurableSet E)
    (hEI : E ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    {A : Set (Space n)} (hA : MeasurableSet A)
    (hthick : ∀ t ∈ E, Metric.ball (x + t • ω) δ ⊆ A) :
    ENNReal.ofReal (lineOccupancyConstant n) * volume E ≤
      OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (A.indicator (fun _ ↦ (1 : ℂ))) ω := by
  have h := scaled_occupancy_average_le
    (volume_tube_pos hδ ω x).ne' (volume_tube_lt_top δ ω x).ne
    (by positivity : ENNReal.ofReal (2 * δ) ≠ 0) ENNReal.ofReal_ne_top
    (line_ball_occupancy hδ hω hE hEI hA hthick)
    (lineOccupancyConstant_volume_bound hn hδ hδone hω x)
  have hmass : (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) =
      volume (A ∩ OAI.MeasureTheory.Kakeya.tube δ ω x) := by
    have heq : (fun y ↦ ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) =
        A.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
      funext y
      by_cases hy : y ∈ A <;> simp [hy]
    rw [heq, lintegral_indicator hA]
    simp [Measure.restrict_apply hA]
  calc
    _ ≤ volume (A ∩ OAI.MeasureTheory.Kakeya.tube δ ω x) / volume (OAI.MeasureTheory.Kakeya.tube δ ω x) := h
    _ = (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ ω x) := by rw [hmass]
    _ ≤ _ := le_iSup (fun x : Space n ↦
      (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω x, ‖A.indicator (fun _ ↦ (1 : ℂ)) y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ ω x)) x
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace OAI.MeasureTheory.Kakeya
def openNeighborhood {n : ℕ} (δ : ℝ) (F : Set (Space n)) : Set (Space n) :=
  ⋃ x ∈ F, Metric.ball x δ
theorem isOpen_openNeighborhood {n : ℕ} (δ : ℝ) (F : Set (Space n)) :
    IsOpen (openNeighborhood δ F) :=
  isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball
theorem tube_subset_openNeighborhood {n : ℕ} {δ : ℝ} {F : Set (Space n)}
    {ω x : Space n} (hF : OAI.MeasureTheory.Kakeya.unitSegment ω x ⊆ F) :
    OAI.MeasureTheory.Kakeya.tube δ ω x ⊆ openNeighborhood δ F := by
  intro y hy
  rcases mem_tube_iff.mp hy with ⟨t, ht, hyt⟩
  exact Set.mem_iUnion.mpr ⟨x + t • ω,
    Set.mem_iUnion.mpr ⟨hF ⟨t, ht, rfl⟩, hyt⟩⟩
theorem ae_sphereMeasure_norm (n : ℕ) :
    ∀ᵐ ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n, ‖ω‖ = 1 := by
  unfold OAI.Analysis.Fourier.Restriction.sphereMeasure
  apply (ae_map_iff measurable_subtype_coe.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet).mpr
  exact Eventually.of_forall fun ω ↦ by
    simpa only [Metric.mem_sphere, dist_zero_right] using ω.property
theorem kakeya_neighborhood_maximal_lower {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {F : Set (Space n)} (hF : OAI.MeasureTheory.Kakeya.IsKakeyaSet F) :
    ∀ᵐ ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n,
      1 ≤ OAI.MeasureTheory.Kakeya.kakeyaMaximal δ ((openNeighborhood δ F).indicator (fun _ ↦ (1 : ℂ))) ω := by
  filter_upwards [ae_sphereMeasure_norm n] with ω hω
  obtain ⟨x, hx⟩ := hF ω hω
  exact one_le_kakeyaMaximal_indicator hδ (tube_subset_openNeighborhood hx)
theorem kakeyaMaximal_implies_neighborhood_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ F : Set (Space n),
      OAI.MeasureTheory.Kakeya.IsKakeyaSet F → volume (openNeighborhood δ F) ≠ ∞ →
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ) ^ (1 / (n : ℝ)) ≤
        ENNReal.ofReal (C * δ ^ (-ε)) *
          volume (openNeighborhood δ F) ^ (1 / (n : ℝ)) := by
  obtain ⟨C, hC, hCf⟩ := hK n hn ε hε
  refine ⟨C, hC, fun δ hδ hδ1 F hF hfinite ↦ ?_⟩
  have hmeas := (isOpen_openNeighborhood δ F).measurableSet
  let f : Space n → ℂ := (openNeighborhood δ F).indicator (fun _ ↦ 1)
  have hf : MemLp f n := memLp_indicator_const n hmeas 1 (.inr hfinite)
  obtain ⟨_, hbound⟩ := hCf δ hδ hδ1 f hf
  have hlo : eLpNorm (fun _ : Space n ↦ (1 : ℝ≥0∞)) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      eLpNorm (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    apply eLpNorm_mono_enorm_ae
    exact kakeya_neighborhood_maximal_lower hδ hF
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hninf : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
  have hnorm : eLpNorm f n volume = volume (openNeighborhood δ F) ^ (1 / (n : ℝ)) := by
    simpa only [f, enorm_one, one_mul, ENNReal.toReal_natCast] using
      (eLpNorm_indicator_const₀ (c := (1 : ℂ)) hmeas.nullMeasurableSet hn0 hninf)
  have hone : eLpNorm (fun _ : Space n ↦ (1 : ℝ≥0∞)) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
      OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ ^ (1 / (n : ℝ)) := by
    simpa only [enorm_eq_self, one_mul, ENNReal.toReal_natCast] using
      (eLpNorm_const' (μ := OAI.Analysis.Fourier.Restriction.sphereMeasure n) (1 : ℝ≥0∞) hn0 hninf)
  rw [← hone, ← hnorm]
  exact hlo.trans hbound
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.MeasureTheory.Kakeya
def dyadicRadius (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k
theorem dyadicRadius_pos (k : ℕ) : 0 < dyadicRadius k := by unfold dyadicRadius; positivity
theorem dyadicRadius_le_one (k : ℕ) : dyadicRadius k ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)
def dyadicIndices (r : ℕ → ℝ) (k : ℕ) : Set ℕ :=
  {j | dyadicRadius (k + 1) < r j ∧ r j ≤ dyadicRadius k}
def dyadicCoverSet {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ) (k : ℕ) : Set (Space n) :=
  ⋃ j ∈ dyadicIndices r k, Metric.ball (x j) (r j)
def dyadicExpandedSet {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ) (k : ℕ) : Set (Space n) :=
  ⋃ j ∈ dyadicIndices r k, Metric.ball (x j) (3 * dyadicRadius k)
theorem isOpen_dyadicCoverSet {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ) (k : ℕ) :
    IsOpen (dyadicCoverSet x r k) := isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball
theorem isOpen_dyadicExpandedSet {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ) (k : ℕ) :
    IsOpen (dyadicExpandedSet x r k) := isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball
theorem ball_subset_dyadicExpandedSet {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ)
    (k : ℕ) {y : Space n} (hy : y ∈ dyadicCoverSet x r k) :
    Metric.ball y (dyadicRadius k) ⊆ dyadicExpandedSet x r k := by
  obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.mp hy
  intro z hz
  apply Set.mem_iUnion₂.mpr
  refine ⟨j, hj, ?_⟩
  have hzy : dist z y < dyadicRadius k := hz
  have hyj : dist y (x j) < r j := hy
  have htriangle := dist_triangle z y (x j)
  have hrad := hj.2
  have hpos := dyadicRadius_pos k
  change dist z (x j) < 3 * dyadicRadius k
  linarith
theorem ball_union_subset_dyadicCoverSet {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ)
    (hr : ∀ j, r j ≤ 1) : (⋃ j, Metric.ball (x j) (r j)) ⊆ ⋃ k, dyadicCoverSet x r k := by
  intro y hy
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
  have hjpos : 0 < r j := lt_of_le_of_lt dist_nonneg (show dist y (x j) < r j from hj)
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near_of_lt_one hjpos (hr j)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion₂.mpr ⟨j, ⟨hklo, hkhi⟩, hj⟩⟩
def dyadicLineTimes {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ) (ω a : Space n) (k : ℕ) : Set ℝ :=
  Set.Icc (-(1 / 2)) (1 / 2) ∩ (fun t : ℝ ↦ a + t • ω) ⁻¹' dyadicCoverSet x r k
theorem measurableSet_dyadicLineTimes {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ)
    (ω a : Space n) (k : ℕ) : MeasurableSet (dyadicLineTimes x r ω a k) := by
  exact measurableSet_Icc.inter ((isOpen_dyadicCoverSet x r k).preimage
    (continuous_const.add (continuous_id.smul continuous_const))).measurableSet
theorem unit_line_injective {n : ℕ} {ω a : Space n} (hω : ‖ω‖ = 1) :
    Function.Injective (fun t : ℝ ↦ a + t • ω) := by
  intro t u h
  have heq : t • ω = u • ω := add_left_cancel h
  have hz : ‖(t - u) • ω‖ = 0 := by rw [sub_smul, heq, sub_self, norm_zero]
  rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_eq_zero] at hz
  exact sub_eq_zero.mp hz
theorem one_le_sum_dyadicLineTimes {n : ℕ} (x : ℕ → Space n) (r : ℕ → ℝ)
    (hr : ∀ j, r j ≤ 1) {Z : Set (Space n)} (hZ : Z.Countable) {ω a : Space n}
    (hω : ‖ω‖ = 1) (hcover : OAI.MeasureTheory.Kakeya.unitSegment ω a ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j)) :
    (1 : ℝ≥0∞) ≤ ∑' k, volume (dyadicLineTimes x r ω a k) := by
  let P : Set ℝ := (fun t : ℝ ↦ a + t • ω) ⁻¹' Z
  have hP : volume P = 0 := (hZ.preimage (unit_line_injective hω)).measure_zero volume
  have hinc : Set.Icc (-(1 / 2) : ℝ) (1 / 2) ⊆ P ∪ ⋃ k, dyadicLineTimes x r ω a k := by
    intro t ht
    have hseg : a + t • ω ∈ OAI.MeasureTheory.Kakeya.unitSegment ω a := ⟨t, ht, rfl⟩
    rcases hcover hseg with hz | hb
    · exact Or.inl hz
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (ball_union_subset_dyadicCoverSet x r hr hb)
      exact Or.inr (Set.mem_iUnion.mpr ⟨k, ht, hk⟩)
  calc
    (1 : ℝ≥0∞) = volume (Set.Icc (-(1 / 2) : ℝ) (1 / 2)) := by rw [Real.volume_Icc]; norm_num
    _ ≤ volume (P ∪ ⋃ k, dyadicLineTimes x r ω a k) := measure_mono hinc
    _ ≤ volume P + volume (⋃ k, dyadicLineTimes x r ω a k) := measure_union_le _ _
    _ ≤ volume P + ∑' k, volume (dyadicLineTimes x r ω a k) := add_le_add le_rfl (measure_iUnion_le _)
    _ = ∑' k, volume (dyadicLineTimes x r ω a k) := by rw [hP, zero_add]
theorem dyadic_occupancy_sum_lower {n : ℕ} (hn : 1 ≤ n) (x : ℕ → Space n) (r : ℕ → ℝ)
    (hr : ∀ j, r j ≤ 1) {Z : Set (Space n)} (hZ : Z.Countable) {F : Set (Space n)}
    (hF : OAI.MeasureTheory.Kakeya.IsKakeyaSet F) (hcover : F ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j))
    {ω : Space n} (hω : ‖ω‖ = 1) :
    ENNReal.ofReal (lineOccupancyConstant n) ≤ ∑' k,
      OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k) ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ))) ω := by
  obtain ⟨a, ha⟩ := hF ω hω
  have hsum := one_le_sum_dyadicLineTimes x r hr hZ hω (ha.trans hcover)
  calc
    ENNReal.ofReal (lineOccupancyConstant n) = ENNReal.ofReal (lineOccupancyConstant n) * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal (lineOccupancyConstant n) * ∑' k, volume (dyadicLineTimes x r ω a k) := mul_le_mul' le_rfl hsum
    _ = ∑' k, ENNReal.ofReal (lineOccupancyConstant n) * volume (dyadicLineTimes x r ω a k) := (ENNReal.tsum_mul_left).symm
    _ ≤ ∑' k, OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k) ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ))) ω := by
      apply ENNReal.tsum_le_tsum
      intro k
      apply kakeya_indicator_ge_line_measure hn (dyadicRadius_pos k) (dyadicRadius_le_one k) hω
        (measurableSet_dyadicLineTimes x r ω a k) (fun _ h ↦ h.1)
        (isOpen_dyadicExpandedSet x r k).measurableSet
      intro t ht
      exact ball_subset_dyadicExpandedSet x r k ht.2
theorem dyadic_occupancy_integral_lower {n : ℕ} (hn : 1 ≤ n) (x : ℕ → Space n)
    (r : ℕ → ℝ) (hr : ∀ j, r j ≤ 1) {Z : Set (Space n)} (hZ : Z.Countable)
    {F : Set (Space n)} (hF : OAI.MeasureTheory.Kakeya.IsKakeyaSet F)
    (hcover : F ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j)) :
    ENNReal.ofReal (lineOccupancyConstant n) * OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ ≤
      ∑' k, ∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k)
        ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ))) ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
  have hm (k : ℕ) : Measurable (OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k)
      ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ)))) :=
    measurable_kakeyaMaximal _ _ ((measurable_const.indicator
      (isOpen_dyadicExpandedSet x r k).measurableSet).aestronglyMeasurable)
  calc
    _ = ∫⁻ _ : Space n, ENNReal.ofReal (lineOccupancyConstant n) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n :=
      (lintegral_const _).symm
    _ ≤ ∫⁻ ω, ∑' k, OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k)
        ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ))) ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      apply lintegral_mono_ae
      filter_upwards [ae_sphereMeasure_norm n] with ω hω
      exact dyadic_occupancy_sum_lower hn x r hr hZ hF hcover hω
    _ = _ := lintegral_tsum (fun k ↦ (hm k).aemeasurable)
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.MeasureTheory.Kakeya
def ballCoverCost (s : ℝ) (r : ℕ → ℝ) : ℝ≥0∞ := ∑' j, ENNReal.ofReal (r j) ^ s
theorem dyadic_ball_volume_scale {n : ℕ} {s δ r : ℝ} (hs : 0 < s) (hδ : 0 < δ)
    (hr : δ / 2 < r) :
    (3 * δ) ^ n ≤ (3 ^ n * 2 ^ s * δ ^ ((n : ℝ) - s)) * r ^ s := by
  have hrpos : 0 < r := lt_trans (by positivity) hr
  have hsplit : δ ^ n = δ ^ ((n : ℝ) - s) * δ ^ s := by
    rw [← Real.rpow_add hδ, sub_add_cancel, Real.rpow_natCast]
  have hpow : δ ^ s ≤ (2 * r) ^ s :=
    Real.rpow_le_rpow hδ.le (by linarith) hs.le
  calc
    (3 * δ) ^ n = 3 ^ n * (δ ^ ((n : ℝ) - s) * δ ^ s) := by rw [mul_pow, hsplit]
    _ ≤ 3 ^ n * (δ ^ ((n : ℝ) - s) * (2 * r) ^ s) := by gcongr
    _ = (3 ^ n * 2 ^ s * δ ^ ((n : ℝ) - s)) * r ^ s := by
      rw [Real.mul_rpow (by norm_num) hrpos.le]
      ring
theorem volume_dyadicExpandedSet_le {n : ℕ} {s : ℝ} (hs : 0 < s)
    (x : ℕ → Space n) (r : ℕ → ℝ) (k : ℕ) :
    volume (dyadicExpandedSet x r k) ≤
      (ENNReal.ofReal (3 ^ n * 2 ^ s * dyadicRadius k ^ ((n : ℝ) - s)) *
        volume (Metric.ball (0 : Space n) 1)) * ballCoverCost s r := by
  have hd := dyadicRadius_pos k
  let B : ℝ≥0∞ := ENNReal.ofReal (3 ^ n * 2 ^ s * dyadicRadius k ^ ((n : ℝ) - s)) *
        volume (Metric.ball (0 : Space n) 1)
  have hterm (j : ℕ) : volume (⋃ _ : j ∈ dyadicIndices r k,
      Metric.ball (x j) (3 * dyadicRadius k)) ≤ B * ENNReal.ofReal (r j) ^ s := by
    by_cases hj : j ∈ dyadicIndices r k
    · have hjlo : dyadicRadius k / 2 < r j := by
        simpa only [dyadicRadius, pow_succ, mul_one_div] using hj.1
      have hjpos : 0 < r j := lt_trans (by exact div_pos (dyadicRadius_pos k) (by norm_num)) hjlo
      have hb : volume (Metric.ball (x j) (3 * dyadicRadius k)) ≤ B * ENNReal.ofReal (r j) ^ s := by
        rw [Measure.addHaar_ball_of_pos volume _ (by positivity : 0 < 3 * dyadicRadius k)]
        simp only [Space, finrank_euclideanSpace_fin]
        rw [ENNReal.ofReal_rpow_of_nonneg hjpos.le hs.le]
        calc
          _ ≤ ENNReal.ofReal ((3 ^ n * 2 ^ s * dyadicRadius k ^ ((n : ℝ) - s)) * r j ^ s) *
              volume (Metric.ball (0 : Space n) 1) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (dyadic_ball_volume_scale hs (dyadicRadius_pos k) hjlo)) le_rfl
          _ = _ := by
            rw [ENNReal.ofReal_mul (by positivity)]
            dsimp only [B]
            ring
      simpa [hj] using hb
    · simp [hj]
  calc
    volume (dyadicExpandedSet x r k) ≤ ∑' j, volume (⋃ _ : j ∈ dyadicIndices r k,
        Metric.ball (x j) (3 * dyadicRadius k)) := measure_iUnion_le _
    _ ≤ ∑' j, B * ENNReal.ofReal (r j) ^ s := ENNReal.tsum_le_tsum hterm
    _ = B * ballCoverCost s r := ENNReal.tsum_mul_left
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem maximal_indicator_L1_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture) {n : ℕ} (hn : 2 ≤ n)
    {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ A : Set (Space n),
      MeasurableSet A → volume A ≠ ∞ →
      (∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (A.indicator (fun _ ↦ (1 : ℂ))) ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        ENNReal.ofReal (C * δ ^ (-η)) * volume A ^ (1 / (n : ℝ)) *
          OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ ^ (1 - 1 / (n : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := hK n hn η hη
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδone A hA hAfin
  have hf : MemLp (A.indicator (fun _ ↦ (1 : ℂ))) n (volume : Measure (Space n)) :=
    memLp_indicator_const _ hA _ (Or.inr hAfin)
  obtain ⟨hKm, hKn⟩ := hbound δ hδ hδone _ hf
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (1 : ℝ≥0∞) ≤ n by exact_mod_cast (show 1 ≤ n by omega)) hKm.aestronglyMeasurable
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hninf : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
  have hfNorm : eLpNorm (A.indicator (fun _ ↦ (1 : ℂ))) n (volume : Measure (Space n)) =
      volume A ^ (1 / (n : ℝ)) := by
    rw [eLpNorm_indicator_const₀ hA.nullMeasurableSet hn0 hninf]
    simp
  rw [hfNorm] at hKn
  have hnorm : eLpNorm (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (A.indicator (fun _ ↦ (1 : ℂ)))) 1 (OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
      ∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (A.indicator (fun _ ↦ (1 : ℂ))) ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp only [enorm_eq_self]
  rw [hnorm] at hcmp
  simp only [ENNReal.toReal_one, ENNReal.toReal_natCast, div_one] at hcmp
  exact hcmp.trans (mul_le_mul' hKn le_rfl)
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem dyadic_rpow_sum_lt_top {η : ℝ} (hη : 0 < η) :
    (∑' k, ENNReal.ofReal (dyadicRadius k ^ η)) < ∞ := by
  have heq (k : ℕ) : ENNReal.ofReal (dyadicRadius k ^ η) =
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ η)) ^ k := by
    rw [dyadicRadius, ← Real.rpow_natCast_mul (by norm_num), mul_comm,
      Real.rpow_mul_natCast (by norm_num), ENNReal.ofReal_pow (by positivity)]
  simp_rw [heq]
  apply tsum_geometric_lt_top.mpr
  apply ENNReal.ofReal_lt_one.mpr
  exact Real.rpow_lt_one (by norm_num) (by norm_num) hη
theorem cover_loss_scale_identity {n : ℕ} (hn : 0 < n) {s δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (δ ^ (-( (n : ℝ) - s) / (2 * n))) *
        (ENNReal.ofReal (δ ^ ((n : ℝ) - s))) ^ (1 / (n : ℝ)) =
      ENNReal.ofReal (δ ^ (((n : ℝ) - s) / (2 * n))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
  congr 2
  field_simp
  ring
theorem maximal_implies_cover_sum_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture) {n : ℕ}
    (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (hsn : s < n) :
    ∃ D : ℝ≥0∞, D < ∞ ∧ ∀ (x : ℕ → Space n) (r : ℕ → ℝ), ballCoverCost s r < ∞ →
      (∑' k, ∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k)
        ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ))) ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
          D * ballCoverCost s r ^ (1 / (n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 ≤ 1 / (n : ℝ) := by positivity
  have hH : 0 ≤ 1 - 1 / (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact sub_nonneg.mpr ((div_le_one hnpos).mpr this)
  let η : ℝ := ((n : ℝ) - s) / (2 * n)
  have hη : 0 < η := div_pos (sub_pos.mpr hsn) (by positivity)
  obtain ⟨C, hC, hbound⟩ := maximal_indicator_L1_bound hK hn hη
  let B : ℝ≥0∞ := ENNReal.ofReal (3 ^ n * 2 ^ s) * volume (Metric.ball (0 : Space n) 1)
  let H : ℝ≥0∞ := OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ ^ (1 - 1 / (n : ℝ))
  let D₀ : ℝ≥0∞ := ENNReal.ofReal C * B ^ (1 / (n : ℝ)) * H
  let G : ℝ≥0∞ := ∑' k, ENNReal.ofReal (dyadicRadius k ^ η)
  have hB : B < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
  have hHfin : H < ∞ := ENNReal.rpow_lt_top_of_nonneg hH (measure_ne_top _ _)
  have hD₀ : D₀ < ∞ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.rpow_lt_top_of_nonneg hq hB.ne)) hHfin
  have hG : G < ∞ := dyadic_rpow_sum_lt_top hη
  refine ⟨D₀ * G, ENNReal.mul_lt_top hD₀ hG, ?_⟩
  intro x r hcost
  have hvol (k : ℕ) : volume (dyadicExpandedSet x r k) ≤
      (B * ballCoverCost s r) * ENNReal.ofReal (dyadicRadius k ^ ((n : ℝ) - s)) := by
    have h := volume_dyadicExpandedSet_le hs x r k
    rw [ENNReal.ofReal_mul (by positivity)] at h
    convert h using 1 ; dsimp only [B] ; ring
  have hterm (k : ℕ) :
      (∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal (dyadicRadius k)
        ((dyadicExpandedSet x r k).indicator (fun _ ↦ (1 : ℂ))) ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
          D₀ * ENNReal.ofReal (dyadicRadius k ^ η) * ballCoverCost s r ^ (1 / (n : ℝ)) := by
    have hδ := dyadicRadius_pos k
    have hAfin : volume (dyadicExpandedSet x r k) ≠ ∞ :=
      (lt_of_le_of_lt (hvol k) (ENNReal.mul_lt_top (ENNReal.mul_lt_top hB hcost) ENNReal.ofReal_lt_top)).ne
    have hbase := hbound (dyadicRadius k) hδ (dyadicRadius_le_one k)
      (dyadicExpandedSet x r k) (isOpen_dyadicExpandedSet x r k).measurableSet hAfin
    have hpow := ENNReal.rpow_le_rpow (hvol k) hq
    calc
      _ ≤ ENNReal.ofReal (C * dyadicRadius k ^ (-η)) *
          (((B * ballCoverCost s r) * ENNReal.ofReal (dyadicRadius k ^ ((n : ℝ) - s))) ^
            (1 / (n : ℝ))) * H :=
        hbase.trans (mul_le_mul' (mul_le_mul' le_rfl hpow) le_rfl)
      _ = (ENNReal.ofReal C * B ^ (1 / (n : ℝ)) * H) *
          (ENNReal.ofReal (dyadicRadius k ^ (-η)) *
            (ENNReal.ofReal (dyadicRadius k ^ ((n : ℝ) - s))) ^ (1 / (n : ℝ))) *
          ballCoverCost s r ^ (1 / (n : ℝ)) := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.mul_rpow_of_nonneg _ _ hq,
          ENNReal.mul_rpow_of_nonneg _ _ hq]
        ring
      _ = _ := by
        have hid := cover_loss_scale_identity (show 0 < n by omega) (s := s) hδ
        have heta : -η = -((n : ℝ) - s) / (2 * n) := by dsimp [η]; ring
        rw [heta, hid]
  calc
    _ ≤ ∑' k, D₀ * ENNReal.ofReal (dyadicRadius k ^ η) * ballCoverCost s r ^ (1 / (n : ℝ)) :=
      ENNReal.tsum_le_tsum hterm
    _ = (D₀ * G) * ballCoverCost s r ^ (1 / (n : ℝ)) := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem nonempty_ediam_rpow {E : Type*} [EMetricSpace E] {s : ℝ} (hs : 0 < s) (T : Set E) :
    (⨆ _ : T.Nonempty, ediam T ^ s) = ediam T ^ s := by
  by_cases hT : T.Nonempty
  · simp [hT]
  · simp [Set.not_nonempty_iff_eq_empty.mp hT, hs]
theorem hausdorff_null_small_set_cover {E : Type*} [EMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] {s : ℝ} (hs : 0 < s) {F : Set E}
    (hF : Measure.hausdorffMeasure s F = 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ T : ℕ → Set E, F ⊆ ⋃ j, T j ∧ (∀ j, ediam (T j) ≤ (1 / 2 : ℝ≥0∞)) ∧
      (∑' j, ediam (T j) ^ s) < ε := by
  have hbound : (⨅ (T : ℕ → Set E) (_ : F ⊆ ⋃ j, T j)
      (_ : ∀ j, ediam (T j) ≤ (1 / 2 : ℝ≥0∞)), ∑' j, ⨆ _ : (T j).Nonempty, ediam (T j) ^ s) ≤
      Measure.hausdorffMeasure s F := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup_of_le (1 / 2 : ℝ≥0∞)
      (le_iSup_of_le (by norm_num : (0 : ℝ≥0∞) < 1 / 2) le_rfl)
  have hlt := hbound.trans_lt (hF ▸ hε)
  obtain ⟨T, hcover, hdiam, hcost⟩ := (by simpa only [iInf_lt_iff] using hlt)
  refine ⟨T, hcover, hdiam, ?_⟩
  simpa only [nonempty_ediam_rpow hs] using hcost
theorem hausdorff_null_ball_cover {n : ℕ} {s : ℝ} (hs : 0 < s) {F : Set (Space n)}
    (hF : Measure.hausdorffMeasure s F = 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (x : ℕ → Space n) (r : ℕ → ℝ) (Z : Set (Space n)),
      Z.Countable ∧ F ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j) ∧
      (∀ j, 0 ≤ r j ∧ r j ≤ 1) ∧
      (∑' j, ENNReal.ofReal (r j) ^ s) ≤ (2 : ℝ≥0∞) ^ s * ε := by
  classical
  obtain ⟨T, hcover, hdiam, hcost⟩ := hausdorff_null_small_set_cover hs hF hε
  have hfin (j : ℕ) : ediam (T j) ≠ ∞ := ne_top_of_le_ne_top (by norm_num) (hdiam j)
  let x : ℕ → Space n := fun j ↦ if h : (T j).Nonempty then h.choose else 0
  let r : ℕ → ℝ := fun j ↦ 2 * (ediam (T j)).toReal
  let Z : Set (Space n) := ⋃ j, if ediam (T j) = 0 then T j else ∅
  have hZ : Z.Countable := by
    apply Set.countable_iUnion
    intro j
    by_cases hj : ediam (T j) = 0
    · simpa only [ite_eq_left hj] using (ediam_eq_zero_iff.mp hj).countable
    · simp [hj]
  refine ⟨x, r, Z, hZ, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover hy)
    by_cases hzero : ediam (T j) = 0
    · left
      exact Set.mem_iUnion.mpr ⟨j, by simpa [hzero] using hj⟩
    · right
      have hT : (T j).Nonempty := ⟨y, hj⟩
      have hx : x j ∈ T j := by simpa only [x, dif_pos hT] using hT.choose_spec
      have hdpos : 0 < (ediam (T j)).toReal := ENNReal.toReal_pos hzero (hfin j)
      have hd := ENNReal.toReal_mono (hfin j) (edist_le_ediam_of_mem hj hx)
      have hdist : dist y (x j) ≤ (ediam (T j)).toReal := by
        simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using hd
      exact Set.mem_iUnion.mpr ⟨j, by change dist y (x j) < 2 * (ediam (T j)).toReal; linarith⟩
  · intro j
    have h := ENNReal.toReal_mono (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ∞) (hdiam j)
    norm_num at h
    exact ⟨by positivity, by dsimp [r]; linarith⟩
  · have heq (j : ℕ) : ENNReal.ofReal (r j) ^ s = (2 : ℝ≥0∞) ^ s * ediam (T j) ^ s := by
      dsimp only [r]
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_toReal (hfin j), ENNReal.mul_rpow_of_nonneg _ _ hs.le]
    simp_rw [heq]
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul' le_rfl hcost.le
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal NNReal Pointwise
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem compact_finite_separated_net {E : Type*} [MetricSpace E]
    {A : Set E} (hA : IsCompact A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (m : ℕ) (v : Fin m → E), (∀ i, v i ∈ A) ∧
      (∀ i j, i ≠ j → δ < dist (v i) (v j)) ∧
      ∀ y ∈ A, ∃ i, dist y (v i) ≤ δ := by
  let ε : ℝ≥0 := ⟨δ, hδ.le⟩
  have hε : ε ≠ 0 := fun h ↦ hδ.ne' (congrArg (fun a : ℝ≥0 ↦ (a : ℝ)) h)
  obtain ⟨N, _, hNfin, hNcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact (ε := ε / 2) (by positivity) hA
  have hpack : Metric.packingNumber ε A ≠ ⊤ := by
    apply ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hNfin)
    have h := (Metric.packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A).trans
      hNcover.externalCoveringNumber_le_encard
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ≥0) ≠ 0)] using h
  let C := Metric.maximalSeparatedSet ε A
  have hCfin : C.Finite := Set.encard_ne_top_iff.mp (by
    change (Metric.maximalSeparatedSet ε A).encard ≠ ⊤
    rw [Metric.encard_maximalSeparatedSet hpack]
    exact hpack)
  let : Fintype C := hCfin.fintype
  let e := (Fintype.equivFin C).symm
  refine ⟨Fintype.card C, fun i ↦ (e i).val, ?_, ?_, ?_⟩
  · intro i
    exact Metric.maximalSeparatedSet_subset (e i).property
  · intro i j hij
    have hne : (e i).val ≠ (e j).val := fun h ↦ hij (e.injective (Subtype.ext h))
    have h := Metric.isSeparated_maximalSeparatedSet (e i).property (e j).property hne
    rw [← ENNReal.ofReal_coe_nnreal, edist_dist] at h
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hδ.le).mp h
  · intro y hy
    obtain ⟨z, hz, hdist⟩ := Metric.isCover_maximalSeparatedSet hpack hy
    refine ⟨e.symm ⟨z, hz⟩, ?_⟩
    change edist y z ≤ (ε : ℝ≥0∞) at hdist
    rw [← ENNReal.ofReal_coe_nnreal, edist_dist] at hdist
    simpa using (ENNReal.ofReal_le_ofReal_iff hδ.le).mp hdist
theorem unit_sphere_finite_separated_net {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    ∃ (m : ℕ) (v : Fin m → Space n), (∀ i, ‖v i‖ = 1) ∧
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) ∧
      ∀ y : Space n, ‖y‖ = 1 → ∃ i, dist y (v i) ≤ δ := by
  obtain ⟨m, v, hv, hsep, hcover⟩ :=
    compact_finite_separated_net (isCompact_sphere (0 : Space n) 1) hδ
  refine ⟨m, v, ?_, fun i j hij ↦ (hsep i j hij).le, ?_⟩
  · intro i
    simpa using hv i
  · intro y hy
    exact hcover y (by simpa using hy)
theorem tube_four_mul_subset_smul {n : ℕ} {δ : ℝ} (v : Space n) :
    OAI.MeasureTheory.Kakeya.tube (4 * δ) v 0 ⊆ (4 : ℝ) • OAI.MeasureTheory.Kakeya.tube δ v 0 := by
  intro y hy
  obtain ⟨t, ht, hyt⟩ := mem_tube_iff.mp hy
  refine Set.mem_smul_set.mpr ⟨(1 / 4 : ℝ) • y, ?_, by simp [smul_smul]⟩
  apply mem_tube_iff.mpr
  refine ⟨t / 4, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  have heq : (1 / 4 : ℝ) • y - ((0 : Space n) + (t / 4) • v) =
      (1 / 4 : ℝ) • (y - ((0 : Space n) + t • v)) := by
    simp [smul_sub, smul_smul, div_eq_mul_inv, mul_comm]
  rw [dist_eq_norm, heq, norm_smul]
  rw [dist_eq_norm] at hyt
  norm_num at *
  linarith
theorem volume_tube_four_mul_le {n : ℕ} (δ : ℝ) (v x : Space n) :
    volume (OAI.MeasureTheory.Kakeya.tube (4 * δ) v x) ≤ ENNReal.ofReal ((4 : ℝ) ^ n) * volume (OAI.MeasureTheory.Kakeya.tube δ v x) := by
  rw [volume_tube_center_eq, volume_tube_center_eq δ]
  calc
    _ ≤ volume ((4 : ℝ) • OAI.MeasureTheory.Kakeya.tube δ v 0) := measure_mono (tube_four_mul_subset_smul v)
    _ = _ := by simp [Measure.addHaar_smul, Space]
theorem volume_tube_near_direction {n : ℕ} {δ : ℝ} {ω v : Space n}
    (hωv : dist ω v ≤ δ) (x : Space n) :
    volume (OAI.MeasureTheory.Kakeya.tube (2 * δ) v x) ≤
      ENNReal.ofReal ((4 : ℝ) ^ n) * volume (OAI.MeasureTheory.Kakeya.tube δ ω x) := by
  have hi : OAI.MeasureTheory.Kakeya.tube (δ / 2) v x ⊆ OAI.MeasureTheory.Kakeya.tube δ ω x := by
    have h := tube_direction_inclusion (δ := δ / 2) (ω := v) (v := ω) (x := x)
      (by simpa only [dist_comm] using hωv)
    simpa only [add_halves] using h
  calc
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ n) * volume (OAI.MeasureTheory.Kakeya.tube (δ / 2) v x) := by
      have heq : 4 * (δ / 2) = 2 * δ := by ring
      simpa only [heq] using volume_tube_four_mul_le (δ / 2) v x
    _ ≤ _ := by gcongr
theorem ennreal_div_le_mul_div {a b A B c : ℝ≥0∞}
    (hA : A ≠ 0) (hA' : A ≠ ∞) (hB : B ≠ 0) (hB' : B ≠ ∞)
    (hab : a ≤ b) (hvol : B ≤ c * A) : a / A ≤ c * (b / B) := by
  apply (ENNReal.div_le_iff hA hA').mpr
  calc
    a ≤ b := hab
    _ = (b / B) * B := (ENNReal.div_mul_cancel hB hB').symm
    _ ≤ (b / B) * (c * A) := by gcongr
    _ = _ := by ring
theorem kakeyaMaximal_near_direction {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (f : Space n → ℂ) {ω v : Space n} (hωv : dist ω v ≤ δ) :
    OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ≤ ENNReal.ofReal ((4 : ℝ) ^ n) * OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f v := by
  apply iSup_le
  intro x
  calc
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ n) *
        ((∫⁻ y in OAI.MeasureTheory.Kakeya.tube (2 * δ) v x, ‖f y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube (2 * δ) v x)) := by
      apply ennreal_div_le_mul_div
        (volume_tube_pos hδ ω x).ne' (volume_tube_lt_top δ ω x).ne
        (volume_tube_pos (by linarith) v x).ne' (volume_tube_lt_top (2 * δ) v x).ne
      · exact lintegral_mono_set (tube_direction_inclusion_double hδ.le hωv)
      · exact volume_tube_near_direction hωv x
    _ ≤ _ := mul_le_mul' le_rfl (le_iSup
      (fun x : Space n ↦ (∫⁻ y in OAI.MeasureTheory.Kakeya.tube (2 * δ) v x, ‖f y‖ₑ) /
        volume (OAI.MeasureTheory.Kakeya.tube (2 * δ) v x)) x)
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped BigOperators
noncomputable section
namespace OAI.MeasureTheory.Kakeya
def splitSigns (n : ℕ) : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun ε := (ε 0, fun i ↦ ε i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv ε := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  right_inv p := by ext <;> simp
theorem sum_signs_succ {β : Type*} [AddCommMonoid β] (n : ℕ)
    (F : (Fin (n + 1) → Bool) → β) :
    ∑ ε, F ε = ∑ b : Bool, ∑ ε : Fin n → Bool, F (Fin.cons b ε) := by
  have h := (splitSigns n).symm.sum_comp F
  simpa only [Fintype.sum_prod_type, splitSigns, Equiv.coe_fn_symm_mk] using h.symm
def signedSum {m : ℕ} (z : Fin m → ℂ) (ε : Fin m → Bool) : ℂ :=
  ∑ i, if ε i then z i else -z i
theorem signedSum_cons {m : ℕ} (z : Fin (m + 1) → ℂ) (b : Bool) (ε : Fin m → Bool) :
    signedSum z (Fin.cons b ε) = (if b then z 0 else -z 0) + signedSum (fun i ↦ z i.succ) ε := by
  simp [signedSum, Fin.sum_univ_succ]
theorem norm_signedSum_rpow_disjoint {m : ℕ} (z : Fin m → ℂ) (ε : Fin m → Bool)
    {p : ℝ} (hp : 0 < p) (hdis : ∀ i j, i ≠ j → z i = 0 ∨ z j = 0) :
    ‖signedSum z ε‖ ^ p = ∑ i, ‖z i‖ ^ p := by
  classical
  by_cases hz : ∀ i, z i = 0
  · simp [signedSum, hz, Real.zero_rpow hp.ne']
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    have hzero (j : Fin m) (hji : j ≠ i) : z j = 0 :=
      (hdis j i hji).resolve_right hi
    have hs : signedSum z ε = if ε i then z i else -z i := by
      unfold signedSum
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [hzero j hji]
      · simp
    have hr : (∑ j, ‖z j‖ ^ p) = ‖z i‖ ^ p := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [hzero j hji, Real.zero_rpow hp.ne']
      · simp
    rw [hs, hr]
    cases ε i <;> simp
theorem norm_signedPackets_rpow {n m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (v x : Fin m → Space n) (c : Fin m → ℂ) (ε : Fin m → Bool)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j))
    {p : ℝ} (hp : 0 < p) (ω : Space n) :
    ‖signedSum (fun i ↦ c i * capPacket δ (v i) (x i) ω) ε‖ ^ p =
      ∑ i, ‖c i * capPacket δ (v i) (x i) ω‖ ^ p := by
  apply norm_signedSum_rpow_disjoint _ _ hp
  intro i j hij
  by_cases hωi : ω ∈ packetCap δ (v i)
  · right
    have hωj : ω ∉ packetCap δ (v j) := fun hj ↦
      Set.disjoint_left.mp (packetCaps_disjoint hδ (hsep i j hij)) hωi hj
    simp [capPacket, hωj]
  · left
    simp [capPacket, hωi]
theorem integral_norm_signedPackets_rpow {n m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (v x : Fin m → Space n) (c : Fin m → ℂ) (ε : Fin m → Bool)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j))
    {p : ℝ} (hp : 0 < p) :
    (∫ ω, ‖signedSum (fun i ↦ c i * capPacket δ (v i) (x i) ω) ε‖ ^ p
      ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
      ∑ i, ‖c i‖ ^ p * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) := by
  simp_rw [norm_signedPackets_rpow hδ v x c ε hsep hp]
  rw [integral_finsetSum Finset.univ
    (fun i _ ↦ integrable_norm_mul_capPacket_rpow δ (v i) (x i) (c i) hp)]
  simp_rw [integral_norm_mul_capPacket_rpow δ _ _ _ hp]
theorem integrable_signedPackets {n m : ℕ} (δ : ℝ)
    (v x : Fin m → Space n) (c : Fin m → ℂ) (ε : Fin m → Bool) :
    Integrable (fun ω ↦ signedSum (fun i ↦ c i * capPacket δ (v i) (x i) ω) ε)
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  apply integrable_finsetSum
  intro i _
  cases hε : ε i
  · simpa [hε] using ((integrable_capPacket δ (v i) (x i)).const_mul (c i)).neg
  · simpa [hε] using (integrable_capPacket δ (v i) (x i)).const_mul (c i)
theorem memLp_signedPackets {n m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (v x : Fin m → Space n) (c : Fin m → ℂ) (ε : Fin m → Bool)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j))
    {p : ℝ} (hp : 0 < p) :
    MemLp (fun ω ↦ signedSum (fun i ↦ c i * capPacket δ (v i) (x i) ω) ε)
      (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  have hm := (integrable_signedPackets δ v x c ε).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp
  simp only [ENNReal.toReal_ofReal hp.le]
  simp_rw [norm_signedPackets_rpow hδ v x c ε hsep hp]
  exact integrable_finsetSum Finset.univ
    (fun i _ ↦ integrable_norm_mul_capPacket_rpow δ (v i) (x i) (c i) hp)
theorem sphericalExtension_signedSum {n m : ℕ} (g : Fin m → Space n → ℂ)
    (hg : ∀ i, Integrable (g i) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) (ε : Fin m → Bool) (x : Space n) :
    OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ signedSum (fun i ↦ g i ω) ε) x =
      signedSum (fun i ↦ OAI.Analysis.Fourier.Restriction.sphericalExtension (g i) x) ε := by
  have hint (i : Fin m) : Integrable (fun ω ↦ if ε i then g i ω else -g i ω)
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    cases hε : ε i
    · simpa [hε] using (hg i).neg
    · simpa [hε] using hg i
  unfold signedSum
  rw [OAI.Analysis.Fourier.Restriction.sphericalExtension_sum Finset.univ _ (fun i _ ↦ hint i)]
  apply Finset.sum_congr rfl
  intro i _
  cases hε : ε i
  · simp only [Bool.false_eq_true, ↓reduceIte]
    simpa only [neg_one_mul] using OAI.Analysis.Fourier.Restriction.sphericalExtension_const_mul (-1) (g i) x
  · simp
theorem sign_square_sum (m : ℕ) (z : Fin m → ℂ) :
    ∑ ε : Fin m → Bool, ‖signedSum z ε‖ ^ 2 = (2 : ℝ) ^ m * ∑ i, ‖z i‖ ^ 2 := by
  induction m with
  | zero => simp [signedSum]
  | succ m ih =>
    rw [sum_signs_succ]
    simp only [signedSum_cons]
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← Finset.sum_add_distrib]
    have hpar (ε : Fin m → Bool) :
        ‖z 0 + signedSum (fun i ↦ z i.succ) ε‖ ^ 2 +
          ‖-z 0 + signedSum (fun i ↦ z i.succ) ε‖ ^ 2 =
        2 * (‖z 0‖ ^ 2 + ‖signedSum (fun i ↦ z i.succ) ε‖ ^ 2) := by
      have h := parallelogram_law_with_norm ℂ (signedSum (fun i ↦ z i.succ) ε) (z 0)
      simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    simp_rw [hpar, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [ih]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, Fin.sum_univ_succ, pow_succ]
    ring
theorem finite_average_rpow_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {q : ℝ} (hq : 1 ≤ q) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ((∑ i, a i) / Fintype.card ι) ^ q ≤ (∑ i, a i ^ q) / Fintype.card ι := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hw : (∑ _i : ι, (Fintype.card ι : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard.ne'
  have h := (convexOn_rpow hq).map_sum_le
    (t := Finset.univ) (w := fun _ : ι ↦ (Fintype.card ι : ℝ)⁻¹)
    (p := a) (fun _ _ ↦ inv_nonneg.mpr hcard.le) hw (fun i _ ↦ ha i)
  calc
    ((∑ i, a i) / Fintype.card ι) ^ q =
        ((Fintype.card ι : ℝ)⁻¹ * ∑ i, a i) ^ q := by congr 1; ring
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, a i ^ q := by
      simpa only [smul_eq_mul, ← Finset.mul_sum] using h
    _ = (∑ i, a i ^ q) / Fintype.card ι := by ring
theorem sign_randomization_lower {m : ℕ} (z : Fin m → ℂ) {p : ℝ} (hp : 2 ≤ p) :
    (∑ i, ‖z i‖ ^ 2) ^ (p / 2) ≤
      (∑ ε : Fin m → Bool, ‖signedSum z ε‖ ^ p) / (2 : ℝ) ^ m := by
  have h := finite_average_rpow_le (by linarith : 1 ≤ p / 2)
    (fun ε : Fin m → Bool ↦ ‖signedSum z ε‖ ^ 2) (fun _ ↦ sq_nonneg _)
  have hcard : (Fintype.card (Fin m → Bool) : ℝ) = (2 : ℝ) ^ m := by simp
  rw [hcard, sign_square_sum] at h
  have hcancel : ((2 : ℝ) ^ m * ∑ i, ‖z i‖ ^ 2) / 2 ^ m = ∑ i, ‖z i‖ ^ 2 := by
    field_simp
  rw [hcancel] at h
  have hrpow (ε : Fin m → Bool) :
      (‖signedSum z ε‖ ^ 2) ^ (p / 2) = ‖signedSum z ε‖ ^ p := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _) 2]
    congr 1
    push_cast
    ring
  simpa only [hrpow] using h
theorem integral_sign_randomization_lower {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {m : ℕ} (z : Fin m → α → ℂ) {p : ℝ} (hp : 2 ≤ p)
    (hz : ∀ i, AEStronglyMeasurable (z i) μ)
    (hints : ∀ ε : Fin m → Bool,
      Integrable (fun x ↦ ‖signedSum (fun i ↦ z i x) ε‖ ^ p) μ) :
    Integrable (fun x ↦ (∑ i, ‖z i x‖ ^ 2) ^ (p / 2)) μ ∧
    (∫ x, (∑ i, ‖z i x‖ ^ 2) ^ (p / 2) ∂μ) ≤
      (∑ ε : Fin m → Bool, ∫ x, ‖signedSum (fun i ↦ z i x) ε‖ ^ p ∂μ) / (2 : ℝ) ^ m := by
  have hmean : Integrable
      (fun x ↦ (∑ ε : Fin m → Bool, ‖signedSum (fun i ↦ z i x) ε‖ ^ p) / (2 : ℝ) ^ m) μ :=
    (integrable_finsetSum Finset.univ (fun ε _ ↦ hints ε)).div_const _
  have hmeas : AEStronglyMeasurable (fun x ↦ (∑ i, ‖z i x‖ ^ 2) ^ (p / 2)) μ := by
    have hsum : AEStronglyMeasurable (fun x ↦ ∑ i, ‖z i x‖ ^ 2) μ := by fun_prop
    exact (Real.continuous_rpow_const (by linarith : 0 ≤ p / 2)).comp_aestronglyMeasurable hsum
  have hbound (x : α) : (∑ i, ‖z i x‖ ^ 2) ^ (p / 2) ≤
      (∑ ε : Fin m → Bool, ‖signedSum (fun i ↦ z i x) ε‖ ^ p) / (2 : ℝ) ^ m :=
    sign_randomization_lower (fun i ↦ z i x) hp
  have hi : Integrable (fun x ↦ (∑ i, ‖z i x‖ ^ 2) ^ (p / 2)) μ := by
    apply hmean.mono' hmeas
    exact Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact hbound x
  refine ⟨hi, ?_⟩
  calc
    (∫ x, (∑ i, ‖z i x‖ ^ 2) ^ (p / 2) ∂μ) ≤
      ∫ x, (∑ ε : Fin m → Bool, ‖signedSum (fun i ↦ z i x) ε‖ ^ p) / (2 : ℝ) ^ m ∂μ :=
        integral_mono hi hmean hbound
    _ = _ := by
      rw [integral_div, integral_finsetSum Finset.univ (fun ε _ ↦ hints ε)]
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem restriction_implies_packet_square_estimate
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {r q : ℝ} (hr : 1 < r) (hq : 2 ≤ q)
    (hcrit : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < q)
    (hdiag : ((n : ℝ) + 1) / ((n : ℝ) - 1) *
      OAI.Analysis.Fourier.Restriction.conjugateExponent (ENNReal.ofReal r) < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ →
      ∀ (v x : Fin m → Space n) (c : Fin m → ℂ),
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      Integrable (fun y ↦ (∑ i, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension
        (fun ω ↦ c i * capPacket δ (v i) (x i) ω) y‖ ^ 2) ^ (q / 2)) volume ∧
      (∫ y, (∑ i, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension
        (fun ω ↦ c i * capPacket δ (v i) (x i) ω) y‖ ^ 2) ^ (q / 2)) ≤
        C ^ q * (∑ i, ‖c i‖ ^ r * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ^ (q / r) := by
  obtain ⟨C, hC, hbound⟩ := hR n hn (ENNReal.ofReal r) (ENNReal.one_lt_ofReal.mpr hr)
    q hcrit hdiag
  refine ⟨C, hC, ?_⟩
  intro m δ hδ v x c hsep
  let g : Fin m → Space n → ℂ := fun i ω ↦ c i * capPacket δ (v i) (x i) ω
  let z : Fin m → Space n → ℂ := fun i y ↦ OAI.Analysis.Fourier.Restriction.sphericalExtension (g i) y
  let f : (Fin m → Bool) → Space n → ℂ := fun ε ω ↦ signedSum (fun i ↦ g i ω) ε
  have hr0 : 0 < r := by linarith
  have hq0 : 0 < q := by linarith
  have hg (i : Fin m) : Integrable (g i) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
    (integrable_capPacket δ (v i) (x i)).const_mul (c i)
  have hf (ε : Fin m → Bool) : MemLp (f ε) (ENNReal.ofReal r) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
    memLp_signedPackets hδ v x c ε hsep hr0
  have hE (ε : Fin m → Bool) : OAI.Analysis.Fourier.Restriction.sphericalExtension (f ε) =
      fun y ↦ signedSum (fun i ↦ z i y) ε := by
    funext y
    exact sphericalExtension_signedSum g hg ε y
  have hi (ε : Fin m → Bool) :
      Integrable (fun y ↦ ‖signedSum (fun i ↦ z i y) ε‖ ^ q) volume := by
    have h := (hbound (f ε) (hf ε)).1.integrable_norm_rpow
      (ENNReal.ofReal_pos.mpr hq0).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hq0.le, hE ε] using h
  have hpow (ε : Fin m → Bool) :
      (∫ y, ‖signedSum (fun i ↦ z i y) ε‖ ^ q) ≤
        C ^ q * (∑ i, ‖c i‖ ^ r * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ^ (q / r) := by
    have h := OAI.Analysis.Fourier.Restriction.integral_norm_rpow_le_of_eLpNorm_le hr0 hq0 hC.le (hf ε)
      (hbound (f ε) (hf ε)).1 (hbound (f ε) (hf ε)).2
    rw [hE ε] at h
    change (∫ y, ‖signedSum (fun i ↦ z i y) ε‖ ^ q) ≤
      C ^ q * (∫ ω, ‖signedSum (fun i ↦ c i * capPacket δ (v i) (x i) ω) ε‖ ^ r
        ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ^ (q / r) at h
    rw [integral_norm_signedPackets_rpow hδ v x c ε hsep hr0] at h
    exact h
  have hJ := integral_sign_randomization_lower z hq
    (fun i ↦ (OAI.Analysis.Fourier.Restriction.continuous_sphericalExtension (hg i)).aestronglyMeasurable) hi
  refine ⟨hJ.1, hJ.2.trans ?_⟩
  calc
    (∑ ε : Fin m → Bool, ∫ y, ‖signedSum (fun i ↦ z i y) ε‖ ^ q) / (2 : ℝ) ^ m ≤
      (∑ _ε : Fin m → Bool,
        C ^ q * (∑ i, ‖c i‖ ^ r * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ^ (q / r)) /
          (2 : ℝ) ^ m :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun ε _ ↦ hpow ε) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem criticalExponent_gt_two {n : ℕ} (hn : 2 ≤ n) : 2 < OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  rw [lt_div_iff₀ (by linarith : 0 < (n : ℝ) - 1)]
  linarith
theorem diagonal_restriction_range {n : ℕ} (hn : 2 ≤ n) {q : ℝ}
    (hq : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < q) :
    ((n : ℝ) + 1) / ((n : ℝ) - 1) * OAI.Analysis.Fourier.Restriction.conjugateExponent (ENNReal.ofReal q) < q := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq2 : 2 < q := (criticalExponent_gt_two hn).trans hq
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hq0 : 0 < q := by linarith
  have hqm1 : 0 < q - 1 := by linarith
  have hmul : 2 * (n : ℝ) < q * ((n : ℝ) - 1) := (div_lt_iff₀ hn1).mp hq
  have hA : ((n : ℝ) + 1) / ((n : ℝ) - 1) < q - 1 :=
    (div_lt_iff₀ hn1).mpr (by nlinarith)
  simp only [OAI.Analysis.Fourier.Restriction.conjugateExponent, ENNReal.ofReal_ne_top, ↓reduceIte,
    ENNReal.toReal_ofReal hq0.le]
  rw [← mul_div_assoc, div_lt_iff₀ hqm1]
  simpa only [mul_comm] using mul_lt_mul_of_pos_right hA hq0
def packetTubeOverlap {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n) (c : Fin m → ℂ)
    (y : Space n) : ℝ :=
  ∑ i, (OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i)).indicator
    (fun _ ↦ (‖c i‖ * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) / 2) ^ 2) y
theorem packetTubeOverlap_nonneg {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n)
    (c : Fin m → ℂ) (y : Space n) : 0 ≤ packetTubeOverlap δ v x c y := by
  apply Finset.sum_nonneg
  intro i _
  apply Set.indicator_nonneg
  intro _ _
  positivity
theorem measurable_packetTubeOverlap {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n)
    (c : Fin m → ℂ) : Measurable (packetTubeOverlap δ v x c) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.indicator (measurableSet_tube _ _ _)
theorem packetTubeOverlap_le {n m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (v x : Fin m → Space n) (c : Fin m → ℂ) (hv : ∀ i, ‖v i‖ = 1) (y : Space n) :
    packetTubeOverlap δ v x c y ≤
      ∑ i, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ c i * capPacket δ (v i) (x i) ω)
        ((δ ^ 2)⁻¹ • y)‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hy : y ∈ OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i)
  · rw [Set.indicator_of_mem hy]
    have hpacket := cap_packet_lower_bound hδ (hv i) hy
    have hw : ‖c i‖ * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) / 2 ≤
        ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ c i * capPacket δ (v i) (x i) ω)
          ((δ ^ 2)⁻¹ • y)‖ := by
      rw [OAI.Analysis.Fourier.Restriction.sphericalExtension_const_mul, norm_mul]
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hpacket (norm_nonneg (c i))
    exact pow_le_pow_left₀ (by positivity) hw 2
  · rw [Set.indicator_of_notMem hy]
    positivity
theorem restriction_implies_weighted_tube_overlap
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {r q : ℝ} (hr : 1 < r) (hq : 2 ≤ q) (hcrit : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < q)
    (hdiag : ((n : ℝ) + 1) / ((n : ℝ) - 1) *
      OAI.Analysis.Fourier.Restriction.conjugateExponent (ENNReal.ofReal r) < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ →
      ∀ (v x : Fin m → Space n) (c : Fin m → ℂ), (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      Integrable (fun y ↦ packetTubeOverlap δ v x c y ^ (q / 2)) volume ∧
      (∫ y, packetTubeOverlap δ v x c y ^ (q / 2)) ≤
        (δ ^ 2) ^ n * (C ^ q *
          (∑ i, ‖c i‖ ^ r * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ^ (q / r)) := by
  obtain ⟨C, hC, hbound⟩ := restriction_implies_packet_square_estimate hR n hn hr hq hcrit hdiag
  refine ⟨C, hC, ?_⟩
  intro m δ hδ v x c hv hsep
  obtain ⟨henergy, hestimate⟩ := hbound m δ hδ v x c hsep
  let energy : Space n → ℝ := fun y ↦
    (∑ i, ‖OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ c i * capPacket δ (v i) (x i) ω) y‖ ^ 2) ^ (q / 2)
  have hi : Integrable (fun y ↦ energy ((δ ^ 2)⁻¹ • y)) volume :=
    henergy.comp_smul (inv_ne_zero (pow_ne_zero 2 hδ.ne'))
  have hdom (y : Space n) : packetTubeOverlap δ v x c y ^ (q / 2) ≤
      energy ((δ ^ 2)⁻¹ • y) :=
    Real.rpow_le_rpow (packetTubeOverlap_nonneg δ v x c y)
      (packetTubeOverlap_le hδ v x c hv y) (by linarith)
  have hm : AEStronglyMeasurable (fun y ↦ packetTubeOverlap δ v x c y ^ (q / 2)) volume :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ q / 2)).comp_aestronglyMeasurable
      (measurable_packetTubeOverlap δ v x c).aestronglyMeasurable
  have ho : Integrable (fun y ↦ packetTubeOverlap δ v x c y ^ (q / 2)) volume := by
    apply hi.mono' hm
    exact Filter.Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (Real.rpow_nonneg (packetTubeOverlap_nonneg δ v x c y) _)]
      exact hdom y
  refine ⟨ho, (integral_mono ho hi hdom).trans ?_⟩
  rw [Measure.integral_comp_inv_smul_of_nonneg volume energy (sq_nonneg δ)]
  have hdim : Module.finrank ℝ (Space n) = n := by simp [Space]
  rw [hdim, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hestimate (by positivity)
theorem restriction_implies_diagonal_packet_bound
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {q : ℝ} (hq : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ →
      ∀ (v x : Fin m → Space n) (c : Fin m → ℂ), (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      Integrable (fun y ↦ packetTubeOverlap δ v x c y ^ (q / 2)) volume ∧
      (∫ y, packetTubeOverlap δ v x c y ^ (q / 2)) ≤
        (δ ^ 2) ^ n * (C ^ q * ∑ i, ‖c i‖ ^ q *
          (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) := by
  have hq2 := (criticalExponent_gt_two hn).trans hq
  have hq0 : q ≠ 0 := by linarith
  obtain ⟨C, hC, hbound⟩ := restriction_implies_weighted_tube_overlap hR n hn
    (by linarith : 1 < q) hq2.le hq (diagonal_restriction_range hn hq)
  refine ⟨C, hC, ?_⟩
  simpa only [div_self hq0, Real.rpow_one] using hbound
end OAI.MeasureTheory.Kakeya
end
end
section
open _root_.MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem finsetSum_iSup_independent {m : ℕ} {β : Type*} [Nonempty β]
    (F : Fin m → β → ℝ≥0∞) :
    (∑ i, ⨆ b, F i b) = ⨆ b : Fin m → β, ∑ i, F i (b i) := by
  classical
  have heval (i : Fin m) : (⨆ b : Fin m → β, F i (b i)) = ⨆ b, F i b := by
    apply le_antisymm
    · exact iSup_le fun b ↦ le_iSup (F i) (b i)
    · exact iSup_le fun b ↦ le_iSup (fun b' : Fin m → β ↦ F i (b' i)) (fun _ ↦ b)
  simp_rw [← heval]
  apply ENNReal.finsetSum_iSup
  intro u v
  refine ⟨fun i ↦ if F i (u i) ≤ F i (v i) then v i else u i, ?_⟩
  intro i
  dsimp only
  split_ifs with h
  · exact ⟨h, le_rfl⟩
  · exact ⟨le_rfl, le_of_not_ge h⟩
theorem finite_lp_duality_nonneg {m : ℕ} {p q B : ℝ} (hpq : p.HolderConjugate q)
    (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) (hB : 0 ≤ B)
    (hdual : ∀ a : Fin m → ℝ, (∀ i, 0 ≤ a i) →
      (∑ i, a i * y i) ≤ B * (∑ i, a i ^ q) ^ (1 / q)) :
    (∑ i, y i ^ p) ^ (1 / p) ≤ B := by
  let S : ℝ := ∑ i, y i ^ p
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hy i) p
  by_cases hzero : S = 0
  · change S ^ (1 / p) ≤ B
    rw [hzero, Real.zero_rpow hpq.one_div_ne_zero]
    exact hB
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
  have hopt (i : Fin m) : y i ^ (p - 1) * y i = y i ^ p := by
    by_cases hi : y i = 0
    · simp [hi, Real.zero_rpow hpq.sub_one_ne_zero, Real.zero_rpow hpq.ne_zero]
    · calc
        y i ^ (p - 1) * y i = y i ^ (p - 1) * y i ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = y i ^ ((p - 1) + 1) := (Real.rpow_add (lt_of_le_of_ne (hy i) (Ne.symm hi)) _ _).symm
        _ = y i ^ p := by congr 1; ring
  have hnorm (i : Fin m) : (y i ^ (p - 1)) ^ q = y i ^ p := by
    rw [← Real.rpow_mul (hy i), hpq.sub_one_mul_conj]
  have h := hdual (fun i ↦ y i ^ (p - 1)) (fun i ↦ Real.rpow_nonneg (hy i) _)
  simp only [hopt, hnorm] at h
  change S ≤ B * S ^ (1 / q) at h
  have hd : S / S ^ (1 / q) ≤ B := (div_le_iff₀ (Real.rpow_pos_of_pos hSpos _)).mpr h
  have he : 1 - 1 / q = 1 / p := by simpa only [one_div] using hpq.symm.one_sub_inv
  have hquot : S / S ^ (1 / q) = S ^ (1 / p) := by
    conv_lhs => lhs; rw [← Real.rpow_one S]
    rw [← Real.rpow_sub hSpos, he]
  rw [hquot] at hd
  exact hd
theorem finite_set_integrals_of_overlap
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {m : ℕ}
    {p q B : ℝ} (hpq : p.HolderConjugate q) (hB : 0 ≤ B)
    (T : Fin m → Set α) (hT : ∀ i, MeasurableSet (T i))
    (hTfin : ∀ i, μ (T i) < ∞)
    (hoverlap : ∀ a : Fin m → ℝ, (∀ i, 0 ≤ a i) →
      MemLp (fun x ↦ ∑ i, (T i).indicator (fun _ ↦ a i) x) (ENNReal.ofReal q) μ ∧
      (∫ x, (∑ i, (T i).indicator (fun _ ↦ a i) x) ^ q ∂μ) ^ (1 / q) ≤
        B * (∑ i, a i ^ q) ^ (1 / q))
    {f : α → ℂ} (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∑ i, (∫ x in T i, ‖f x‖ ∂μ) ^ p) ^ (1 / p) ≤
      B * (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) := by
  have hi (i : Fin m) : IntegrableOn (fun x ↦ ‖f x‖) (T i) μ := by
    have : IsFiniteMeasure (μ.restrict (T i)) := ⟨by simpa using hTfin i⟩
    exact (hf.norm.mono_measure Measure.restrict_le_self).integrable
      (ENNReal.one_le_ofReal.mpr hpq.lt.le)
  apply finite_lp_duality_nonneg hpq
    (fun i ↦ ∫ x in T i, ‖f x‖ ∂μ)
    (fun i ↦ integral_nonneg fun x ↦ norm_nonneg (f x))
    (mul_nonneg hB (Real.rpow_nonneg (integral_nonneg fun x ↦
      Real.rpow_nonneg (norm_nonneg (f x)) _) _))
  intro a ha
  let φ : α → ℝ := fun x ↦ ∑ i, (T i).indicator (fun _ ↦ a i) x
  obtain ⟨hφ, hφbound⟩ := hoverlap a ha
  have hφnonneg (x : α) : 0 ≤ φ x := by
    exact Finset.sum_nonneg fun i _ ↦ Set.indicator_nonneg (fun _ _ ↦ ha i) x
  have hind (i : Fin m) : Integrable ((T i).indicator (fun x ↦ a i * ‖f x‖)) μ :=
    (integrable_indicator_iff (hT i)).mpr ((hi i).const_mul (a i))
  have heq : (fun x ↦ ‖f x‖ * φ x) =
      fun x ↦ ∑ i, (T i).indicator (fun x ↦ a i * ‖f x‖) x := by
    funext x
    simp only [φ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ T i <;> simp [hx, mul_comm]
  have hpair : (∫ x, ‖f x‖ * φ x ∂μ) = ∑ i, a i * ∫ x in T i, ‖f x‖ ∂μ := by
    rw [heq, integral_finsetSum Finset.univ (fun i _ ↦ hind i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator (hT i), integral_const_mul]
  rw [← hpair]
  calc
    (∫ x, ‖f x‖ * φ x ∂μ) ≤
        (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) * (∫ x, φ x ^ q ∂μ) ^ (1 / q) :=
      integral_mul_le_Lp_mul_Lq_of_nonneg hpq
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
        (Filter.Eventually.of_forall hφnonneg) hf.norm hφ
    _ ≤ (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) * (B * (∑ i, a i ^ q) ^ (1 / q)) :=
      mul_le_mul_of_nonneg_left hφbound (Real.rpow_nonneg
        (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg (f x)) _) _)
    _ = _ := by ring
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.MeasureTheory.Kakeya
def tubeOverlap {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n) (a : Fin m → ℝ)
    (y : Space n) : ℝ := ∑ i, (OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i)).indicator (fun _ ↦ a i) y
theorem tubeOverlap_nonneg {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n)
    (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (y : Space n) : 0 ≤ tubeOverlap δ v x a y :=
  Finset.sum_nonneg fun i _ ↦ Set.indicator_nonneg (fun _ _ ↦ ha i) y
theorem memLp_tubeOverlap {n m : ℕ} (δ : ℝ) (v x : Fin m → Space n)
    (a : Fin m → ℝ) (s : ℝ≥0∞) : MemLp (tubeOverlap δ v x a) s volume := by
  apply memLp_finsetSum
  intro i _
  exact memLp_indicator_const s (measurableSet_tube _ _ _) (a i)
    (Or.inr (volume_tube_lt_top _ _ _).ne)
theorem scaled_sqrt_norm {a L : ℝ} (_ha : 0 ≤ a) (hL : 0 < L) :
    ‖((2 / L * Real.sqrt a : ℝ) : ℂ)‖ = 2 / L * Real.sqrt a := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
theorem scaled_sqrt_rpow {a L q : ℝ} (ha : 0 ≤ a) (hL : 0 < L) :
    ‖((2 / L * Real.sqrt a : ℝ) : ℂ)‖ ^ q = (2 / L) ^ q * a ^ (q / 2) := by
  rw [scaled_sqrt_norm ha hL, Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)]
  congr 1
  calc
    Real.sqrt a ^ q = Real.sqrt a ^ ((2 : ℝ) * (q / 2)) := by congr 1; ring
    _ = (Real.sqrt a ^ (2 : ℕ)) ^ (q / 2) := by
      simpa using Real.rpow_natCast_mul (Real.sqrt_nonneg a) 2 (q / 2)
    _ = a ^ (q / 2) := by rw [Real.sq_sqrt ha]
theorem tubeOverlap_le_scaled_packetTubeOverlap {n m : ℕ} (δ : ℝ)
    (v x : Fin m → Space n) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    {L : ℝ} (hL : 0 < L) (hlower : ∀ i, L ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)))
    (y : Space n) :
    tubeOverlap δ v x a y ≤ packetTubeOverlap δ v x
      (fun i ↦ ((2 / L * Real.sqrt (a i) : ℝ) : ℂ)) y := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hy : y ∈ OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i)
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, scaled_sqrt_norm (ha i) hL]
    have hroot : Real.sqrt (a i) ≤
        2 / L * Real.sqrt (a i) * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) / 2 := by
      calc
        Real.sqrt (a i) = (2 / L * Real.sqrt (a i)) * L / 2 := by field_simp [hL.ne']
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hlower i) (by positivity)) (by norm_num)
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
    rwa [Real.sq_sqrt (ha i)] at hs
  · simp only [Set.indicator_of_notMem hy, le_refl]
theorem tubeOverlap_bound_of_packet_bound {n m : ℕ} (δ : ℝ)
    (v x : Fin m → Space n) {q C L U : ℝ} (hq : 0 < q) (hC : 0 ≤ C) (hL : 0 < L)
    (hU : 0 ≤ U)
    (hlower : ∀ i, L ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)))
    (hupper : ∀ i, (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) ≤ U)
    (hpacket : ∀ c : Fin m → ℂ,
      Integrable (fun y ↦ packetTubeOverlap δ v x c y ^ (q / 2)) volume ∧
      (∫ y, packetTubeOverlap δ v x c y ^ (q / 2)) ≤
        (δ ^ 2) ^ n * (C ^ q * ∑ i, ‖c i‖ ^ q *
          (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))))
    (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∫ y, tubeOverlap δ v x a y ^ (q / 2)) ^ (1 / (q / 2)) ≤
      ((δ ^ 2) ^ n * C ^ q * U * (2 / L) ^ q) ^ (1 / (q / 2)) *
        (∑ i, a i ^ (q / 2)) ^ (1 / (q / 2)) := by
  let c : Fin m → ℂ := fun i ↦ ((2 / L * Real.sqrt (a i) : ℝ) : ℂ)
  have hs : 0 < q / 2 := by linarith
  have hψ := memLp_tubeOverlap δ v x a (ENNReal.ofReal (q / 2))
  have hint : Integrable (fun y ↦ tubeOverlap δ v x a y ^ (q / 2)) volume := by
    have hi := hψ.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hs.le,
      Real.norm_of_nonneg (tubeOverlap_nonneg δ v x a ha _)] using hi
  obtain ⟨hpacketInt, hpacketBound⟩ := hpacket c
  have hinput : (∑ i, ‖c i‖ ^ q * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) ≤
      ((2 / L) ^ q * U) * ∑ i, a i ^ (q / 2) := by
    simp only [c, scaled_sqrt_rpow (ha _) hL]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hai := ha i
    calc
      (2 / L) ^ q * a i ^ (q / 2) * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) ≤
          (2 / L) ^ q * a i ^ (q / 2) * U :=
        mul_le_mul_of_nonneg_left (hupper i) (by positivity)
      _ = _ := by ring
  have hpow : (∫ y, tubeOverlap δ v x a y ^ (q / 2)) ≤
      ((δ ^ 2) ^ n * C ^ q * U * (2 / L) ^ q) * ∑ i, a i ^ (q / 2) := by
    calc
      (∫ y, tubeOverlap δ v x a y ^ (q / 2)) ≤
          ∫ y, packetTubeOverlap δ v x c y ^ (q / 2) :=
        integral_mono hint hpacketInt (fun y ↦ Real.rpow_le_rpow
          (tubeOverlap_nonneg δ v x a ha y)
          (tubeOverlap_le_scaled_packetTubeOverlap δ v x a ha hL hlower y) hs.le)
      _ ≤ (δ ^ 2) ^ n * (C ^ q * ∑ i, ‖c i‖ ^ q *
          (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) := hpacketBound
      _ ≤ (δ ^ 2) ^ n * (C ^ q * (((2 / L) ^ q * U) * ∑ i, a i ^ (q / 2))) := by
        gcongr
      _ = _ := by ring
  have hresult := Real.rpow_le_rpow
    (integral_nonneg fun y ↦ Real.rpow_nonneg (tubeOverlap_nonneg δ v x a ha y) _) hpow
    (le_of_lt (one_div_pos.mpr hs))
  rwa [Real.mul_rpow (by positivity)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (ha i) _)] at hresult
theorem double_dual_gt_critical {n : ℕ} (hn : 2 ≤ n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (hpn : p < n) : OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < 2 * q := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  rw [div_lt_iff₀ (by linarith : 0 < (n : ℝ) - 1)]
  have h := mul_lt_mul_of_pos_right hpn hpq.symm.sub_one_pos
  have heq := hpq.mul_eq_add
  nlinarith
theorem restriction_implies_finite_tube_integrals_with_cap_bounds
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hpn : p < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ →
      ∀ (v x : Fin m → Space n), (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      ∀ L U : ℝ, 0 < L → 0 ≤ U →
      (∀ i, L ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i))) →
      (∀ i, (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) ≤ U) →
      ∀ f : Space n → ℂ, MemLp f (ENNReal.ofReal p) volume →
      (∑ i, (∫ y in OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i), ‖f y‖) ^ p) ^ (1 / p) ≤
        ((δ ^ 2) ^ n * C ^ (2 * q) * U * (2 / L) ^ (2 * q)) ^ (1 / q) *
          (∫ y, ‖f y‖ ^ p) ^ (1 / p) := by
  obtain ⟨C, hC, hbound⟩ := restriction_implies_diagonal_packet_bound hR n hn
    (double_dual_gt_critical hn hpq hpn)
  refine ⟨C, hC, ?_⟩
  intro m δ hδ v x hv hsep L U hL hU hlower hupper f hf
  apply finite_set_integrals_of_overlap (μ := (volume : Measure (Space n))) hpq (by positivity)
    (fun i ↦ OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i))
    (fun i ↦ measurableSet_tube _ _ _) (fun i ↦ volume_tube_lt_top _ _ _) ?_ hf
  intro a ha
  refine ⟨memLp_tubeOverlap δ v x a (ENNReal.ofReal q), ?_⟩
  have hhalf : 2 * q / 2 = q := by ring
  have h := tubeOverlap_bound_of_packet_bound δ v x (mul_pos (by norm_num) hpq.symm.pos)
    hC.le hL hU hlower hupper (fun c ↦ hbound m δ hδ v x c hv hsep) a ha
  simpa only [hhalf, tubeOverlap] using h
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem cap_coefficient_scale {δ C L U q a b : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hL : 0 < L) (hU : 0 ≤ U) (hq : 0 < q) :
    (δ ^ a * C ^ (2 * q) * (U * δ ^ b) * (2 / (L * δ ^ b)) ^ (2 * q)) ^ (1 / q) =
      (C ^ (2 * q) * U * (2 / L) ^ (2 * q)) ^ (1 / q) *
        δ ^ ((a + b) / q - 2 * b) := by
  have hdiv : 2 / (L * δ ^ b) = (2 / L) / δ ^ b := by ring
  have hinner : δ ^ a * C ^ (2 * q) * (U * δ ^ b) * (2 / (L * δ ^ b)) ^ (2 * q) =
      (C ^ (2 * q) * U * (2 / L) ^ (2 * q)) * δ ^ (a + b - b * (2 * q)) := by
    rw [hdiv, Real.div_rpow (by positivity) (by positivity), ← Real.rpow_mul hδ.le]
    rw [Real.rpow_sub hδ, Real.rpow_add hδ]
    ring
  rw [hinner, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hδ.le]
  congr 2
  field_simp
theorem restriction_implies_finite_tube_integrals
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hpn : p < n) :
    ∃ A : ℝ, 0 < A ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ (v x : Fin m → Space n), (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      ∀ f : Space n → ℂ, MemLp f (ENNReal.ofReal p) volume →
      (∑ i, (∫ y in OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) (x i), ‖f y‖) ^ p) ^ (1 / p) ≤
        A * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 2 * (n - 1 : ℕ)) *
          (∫ y, ‖f y‖ ^ p) ^ (1 / p) := by
  obtain ⟨C, hC, hbound⟩ := restriction_implies_finite_tube_integrals_with_cap_bounds hR n hn hpq hpn
  obtain ⟨L, U, hL, hU, hcap⟩ := OAI.Analysis.Fourier.Restriction.packetCap_real_comparable (n := n) (by omega)
  refine ⟨(C ^ (2 * q) * U * (2 / L) ^ (2 * q)) ^ (1 / q), by positivity, ?_⟩
  intro m δ hδ hδone v x hv hsep f hf
  have h := hbound m δ hδ v x hv hsep (L * δ ^ (n - 1)) (U * δ ^ (n - 1))
    (by positivity) (by positivity)
    (fun i ↦ (hcap δ (v i) hδ hδone (hv i)).1)
    (fun i ↦ (hcap δ (v i) hδ hδone (hv i)).2) f hf
  have hdim : (δ ^ 2) ^ n = δ ^ (2 * (n : ℝ)) := by
    rw [← pow_mul]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Real.rpow_natCast δ (2 * n)).symm
  have hd : δ ^ (n - 1) = δ ^ ((n - 1 : ℕ) : ℝ) := (Real.rpow_natCast δ (n - 1)).symm
  rw [hdim, hd, cap_coefficient_scale hδ hC.le hL hU.le hpq.symm.pos] at h
  exact h
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem ennreal_rpow_iSup {ι : Type*} (f : ι → ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    (⨆ i, f i) ^ p = ⨆ i, f i ^ p :=
  (ENNReal.orderIsoRpow p hp).map_iSup f
theorem finite_power_sup_le {m : ℕ} {X : Type*} [Nonempty X]
    (F : Fin m → X → ℝ≥0∞) {p : ℝ} (hp : 0 < p) {B : ℝ≥0∞}
    (h : ∀ x : Fin m → X, ∑ i, F i (x i) ^ p ≤ B) :
    ∑ i, (⨆ x, F i x) ^ p ≤ B := by
  simp_rw [ennreal_rpow_iSup _ hp]
  rw [finsetSum_iSup_independent]
  exact iSup_le h
theorem normalized_finite_moment_le {m : ℕ} (I : Fin m → ℝ)
    (J : Fin m → ℝ≥0∞) {p k B : ℝ} (hp : 0 < p) (hk : 0 < k)
    (hB : 0 ≤ B) (hI : ∀ i, 0 ≤ I i)
    (hJ : ∀ i, J i ≤ ENNReal.ofReal (I i / k))
    (hbound : (∑ i, I i ^ p) ^ (1 / p) ≤ B) :
    ∑ i, J i ^ p ≤ ENNReal.ofReal ((B / k) ^ p) := by
  have hsum : 0 ≤ ∑ i, I i ^ p := Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hI i) _
  have hs : ∑ i, I i ^ p ≤ B ^ p := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hsum _) hbound hp.le
    simpa only [← Real.rpow_mul hsum, one_div_mul_cancel hp.ne', Real.rpow_one] using h
  calc
    ∑ i, J i ^ p ≤ ∑ i, ENNReal.ofReal ((I i / k) ^ p) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← ENNReal.ofReal_rpow_of_nonneg (div_nonneg (hI i) hk.le) hp.le]
      exact ENNReal.rpow_le_rpow (hJ i) hp.le
    _ = ENNReal.ofReal ((∑ i, I i ^ p) / k ^ p) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦
        Real.rpow_nonneg (div_nonneg (hI i) hk.le) _)]
      congr 1
      simp_rw [Real.div_rpow (hI _) hk.le]
      rw [Finset.sum_div]
    _ ≤ ENNReal.ofReal (B ^ p / k ^ p) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hs (Real.rpow_nonneg hk.le _))
    _ = ENNReal.ofReal ((B / k) ^ p) := by rw [Real.div_rpow hB hk.le]
theorem finite_kakeya_moment_of_integral_bound {n m : ℕ} {δ p k B : ℝ}
    (hp : 1 ≤ p) (hk : 0 < k) (hB : 0 ≤ B) (v : Fin m → Space n)
    (f : Space n → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume)
    (hvol : ∀ i x, ENNReal.ofReal k ≤ volume (OAI.MeasureTheory.Kakeya.tube δ (v i) x))
    (hbound : ∀ x : Fin m → Space n,
      (∑ i, (∫ y in OAI.MeasureTheory.Kakeya.tube δ (v i) (x i), ‖f y‖) ^ p) ^ (1 / p) ≤ B) :
    ∑ i, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f (v i) ^ p ≤ ENNReal.ofReal ((B / k) ^ p) := by
  apply finite_power_sup_le (fun i x ↦ tubeMass δ f (v i) x / volume (OAI.MeasureTheory.Kakeya.tube δ (v i) x))
    (by linarith : 0 < p)
  intro x
  apply normalized_finite_moment_le
    (fun i ↦ ∫ y in OAI.MeasureTheory.Kakeya.tube δ (v i) (x i), ‖f y‖)
    (fun i ↦ tubeMass δ f (v i) (x i) / volume (OAI.MeasureTheory.Kakeya.tube δ (v i) (x i)))
    (by linarith) hk hB (fun i ↦ integral_nonneg fun y ↦ norm_nonneg (f y))
    _ (hbound x)
  intro i
  have hfin : IsFiniteMeasure (volume.restrict (OAI.MeasureTheory.Kakeya.tube δ (v i) (x i))) :=
    ⟨by simpa using volume_tube_lt_top δ (v i) (x i)⟩
  have hi : IntegrableOn f (OAI.MeasureTheory.Kakeya.tube δ (v i) (x i)) volume :=
    (hf.mono_measure Measure.restrict_le_self).integrable (ENNReal.one_le_ofReal.mpr hp)
  have heq : tubeMass δ f (v i) (x i) =
      ENNReal.ofReal (∫ y in OAI.MeasureTheory.Kakeya.tube δ (v i) (x i), ‖f y‖) :=
    (ofReal_integral_norm_eq_lintegral_enorm hi).symm
  rw [heq, ENNReal.ofReal_div_of_pos hk]
  exact ENNReal.div_le_div_left (hvol i (x i)) _
theorem restriction_implies_discrete_kakeya
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hpn : p < n) :
    ∃ D : ℝ, 0 < D ∧ ∀ (m : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ v : Fin m → Space n, (∀ i, ‖v i‖ = 1) →
      (∀ i j, i ≠ j → δ ≤ dist (v i) (v j)) →
      ∀ f : Space n → ℂ, MemLp f (ENNReal.ofReal p) volume →
      ∑ i, OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f (v i) ^ p ≤
        ENNReal.ofReal ((D * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q -
          3 * (n - 1 : ℕ)) * (∫ y, ‖f y‖ ^ p) ^ (1 / p)) ^ p) := by
  obtain ⟨A, hA, hraw⟩ := restriction_implies_finite_tube_integrals hR n hn hpq hpn
  obtain ⟨c, hc, hvolume⟩ := exists_volume_tube_real_lower (n := n) (by omega)
  refine ⟨A / c, div_pos hA hc, ?_⟩
  intro m δ hδ hδone v hv hsep f hf
  have hvol (i : Fin m) (x : Space n) :
      ENNReal.ofReal (c * δ ^ (n - 1)) ≤ volume (OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) x) := by
    calc
      _ ≤ ENNReal.ofReal (volume.real (OAI.MeasureTheory.Kakeya.tube δ (v i) x)) :=
        ENNReal.ofReal_le_ofReal (hvolume δ (v i) x hδ hδone (hv i))
      _ = volume (OAI.MeasureTheory.Kakeya.tube δ (v i) x) :=
        ENNReal.ofReal_toReal (volume_tube_lt_top δ (v i) x).ne
      _ ≤ volume (OAI.MeasureTheory.Kakeya.tube (2 * δ) (v i) x) :=
        measure_mono (tube_mono (by linarith) (v i) x)
  have h := finite_kakeya_moment_of_integral_bound hpq.lt.le
    (by positivity : 0 < c * δ ^ (n - 1))
    (by positivity : 0 ≤ A * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q -
      2 * (n - 1 : ℕ)) * (∫ y, ‖f y‖ ^ p) ^ (1 / p))
    v f hf hvol (fun x ↦ hraw m δ hδ hδone v x hv hsep f hf)
  have heq : (A * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 2 * (n - 1 : ℕ)) *
      (∫ y, ‖f y‖ ^ p) ^ (1 / p)) / (c * δ ^ (n - 1)) =
      (A / c) * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ)) *
        (∫ y, ‖f y‖ ^ p) ^ (1 / p) := by
    have he : (2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ) =
        ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 2 * (n - 1 : ℕ)) - (n - 1 : ℕ) := by ring
    rw [he]
    conv_rhs => rw [Real.rpow_sub hδ, Real.rpow_natCast]
    ring
  simpa only [heq] using h
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem packetCap_real_upper_all_scales {n : ℕ} (hn : 1 ≤ n) :
    ∃ U : ℝ, 0 < U ∧ ∀ (δ : ℝ) (v : Space n), 0 < δ → ‖v‖ = 1 →
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ v) ≤ U * δ ^ (n - 1) := by
  obtain ⟨L, C, hL, hC, hcap⟩ := OAI.Analysis.Fourier.Restriction.packetCap_real_comparable hn
  refine ⟨C + (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real Set.univ, by positivity, ?_⟩
  intro δ v hδ hv
  by_cases hδone : δ ≤ 1
  · exact (hcap δ v hδ hδone hv).2.trans (by
      gcongr
      exact le_add_of_nonneg_right (measureReal_nonneg))
  · have hpow : 1 ≤ δ ^ (n - 1) := one_le_pow₀ (by linarith)
    calc
      _ ≤ (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real Set.univ := measureReal_mono (Set.subset_univ _)
      _ ≤ C + (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real Set.univ := le_add_of_nonneg_left hC.le
      _ ≤ (C + (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real Set.univ) * δ ^ (n - 1) :=
        le_mul_of_one_le_right (by positivity) hpow
theorem lintegral_kakeya_le_net {n m : ℕ} {δ p : ℝ} (hδ : 0 < δ) (hp : 0 ≤ p)
    (f : Space n → ℂ) (v : Fin m → Space n)
    (hcover : ∀ ω : Space n, ‖ω‖ = 1 → ∃ i, dist ω (v i) ≤ δ) :
    (∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ p ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ∑ i, OAI.Analysis.Fourier.Restriction.sphereMeasure n (packetCap (32 * δ) (v i)) *
        (ENNReal.ofReal ((4 : ℝ) ^ n) * OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f (v i)) ^ p := by
  let a : Fin m → ℝ≥0∞ := fun i ↦
    (ENNReal.ofReal ((4 : ℝ) ^ n) * OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f (v i)) ^ p
  let F : Fin m → Space n → ℝ≥0∞ := fun i ↦
    (packetCap (32 * δ) (v i)).indicator (fun _ ↦ a i)
  have hpt : ∀ᵐ ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ p ≤ ∑ i, F i ω := by
    filter_upwards [ae_sphereMeasure_norm n] with ω hω
    obtain ⟨i, hi⟩ := hcover ω hω
    have hmem : ω ∈ packetCap (32 * δ) (v i) := by
      refine ⟨hω, ?_⟩
      simpa only [mul_div_cancel_left₀ δ (by norm_num : (32 : ℝ) ≠ 0), ← dist_eq_norm] using hi
    calc
      _ ≤ a i := ENNReal.rpow_le_rpow (kakeyaMaximal_near_direction hδ f hi) hp
      _ = F i ω := by simp only [F, Set.indicator_of_mem hmem]
      _ ≤ ∑ j, F j ω := Finset.single_le_sum (f := fun j ↦ F j ω)
        (fun j _ ↦ bot_le) (Finset.mem_univ i)
  calc
    _ ≤ ∫⁻ ω, ∑ i, F i ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := lintegral_mono_ae hpt
    _ = ∑ i, OAI.Analysis.Fourier.Restriction.sphereMeasure n (packetCap (32 * δ) (v i)) * a i := by
      rw [lintegral_finsetSum _ (fun i _ ↦ measurable_const.indicator (measurableSet_packetCap _ _))]
      apply Finset.sum_congr rfl
      intro i _
      simp [lintegral_indicator (measurableSet_packetCap _ _), mul_comm]
    _ = _ := rfl
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem lintegral_average_enorm_rpow_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : AEStronglyMeasurable f μ) (hμ : μ Set.univ ≠ 0) (hμ' : μ Set.univ ≠ ∞)
    {r : ℝ} (hr : 1 ≤ r) :
    ((∫⁻ x, ‖f x‖ₑ ∂μ) / μ Set.univ) ^ r ≤
      (∫⁻ x, ‖f x‖ₑ ^ r ∂μ) / μ Set.univ := by
  let ν : Measure α := (μ Set.univ)⁻¹ • μ
  have : IsProbabilityMeasure ν := ⟨by
    simp only [ν, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hμ hμ']⟩
  have hm : AEStronglyMeasurable f ν := hf.smul_measure _
  have hrpos : 0 < r := by linarith
  have h := eLpNorm_le_eLpNorm_of_exponent_le (f := f) (μ := ν)
    (ENNReal.one_le_ofReal.mpr hr) hm
  rw [eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hrpos.le] at h
  have hp := ENNReal.rpow_le_rpow h hrpos.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hrpos.ne', ENNReal.rpow_one] at hp
  simpa only [ν, lintegral_smul_measure, smul_eq_mul, div_eq_mul_inv, mul_comm] using hp
def kakeyaPowerInput {n : ℕ} (r : ℝ) (f : Space n → ℂ) (x : Space n) : ℂ :=
  (‖f x‖ ^ r : ℝ)
theorem norm_kakeyaPowerInput {n : ℕ} (r : ℝ) (f : Space n → ℂ) (x : Space n) :
    ‖kakeyaPowerInput r f x‖ = ‖f x‖ ^ r := by
  simp [kakeyaPowerInput, Real.rpow_nonneg (norm_nonneg _)]
theorem enorm_kakeyaPowerInput {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (f : Space n → ℂ) (x : Space n) :
    ‖kakeyaPowerInput r f x‖ₑ = ‖f x‖ₑ ^ r := by
  rw [← ofReal_norm, norm_kakeyaPowerInput, ← ofReal_norm,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr]
theorem memLp_kakeyaPowerInput {n : ℕ} {p r : ℝ} (hp : 0 < p) (hr : 0 < r)
    {f : Space n → ℂ} (hf : MemLp f (ENNReal.ofReal (p * r)) volume) :
    MemLp (kakeyaPowerInput r f) (ENNReal.ofReal p) volume := by
  have h : MemLp (fun x : Space n ↦ ((‖f x‖ ^ (ENNReal.ofReal r).toReal : ℝ) : ℂ))
      (ENNReal.ofReal (p * r) / ENNReal.ofReal r) (volume : Measure (Space n)) :=
    (hf.norm_rpow_div (ENNReal.ofReal r)).ofReal (K := ℂ)
  change MemLp (fun x : Space n ↦ ((‖f x‖ ^ r : ℝ) : ℂ)) (ENNReal.ofReal p)
    (volume : Measure (Space n))
  simpa only [ENNReal.toReal_ofReal hr.le,
    ENNReal.ofReal_mul hp.le, ENNReal.mul_div_cancel_right (by positivity : ENNReal.ofReal r ≠ 0)
      ENNReal.ofReal_ne_top] using h
theorem kakeyaMaximal_rpow_le_powerInput {n : ℕ} {δ r : ℝ}
    (hδ : 0 < δ) (hr : 1 ≤ r) {f : Space n → ℂ}
    (hf : AEStronglyMeasurable f (volume : Measure (Space n))) (ω : Space n) :
    OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ r ≤ OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (kakeyaPowerInput r f) ω := by
  have hrpos : 0 < r := by linarith
  rw [OAI.MeasureTheory.Kakeya.kakeyaMaximal, ennreal_rpow_iSup _ hrpos]
  apply iSup_le
  intro x
  have h := lintegral_average_enorm_rpow_le
    (hf.mono_measure Measure.restrict_le_self)
    (μ := volume.restrict (OAI.MeasureTheory.Kakeya.tube δ ω x))
    (by simpa using (volume_tube_pos hδ ω x).ne')
    (by simpa using (volume_tube_lt_top δ ω x).ne) hr
  have heq : (fun y ↦ ‖f y‖ₑ ^ r) = fun y ↦ ‖kakeyaPowerInput r f y‖ₑ := by
    funext y
    exact (enorm_kakeyaPowerInput hrpos.le f y).symm
  rw [heq, Measure.restrict_apply_univ] at h
  exact h.trans (le_iSup (fun z : Space n ↦
    (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω z, ‖kakeyaPowerInput r f y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ ω z)) x)
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem kakeya_subcritical_scale {n : ℕ} (hn : 1 ≤ n) {p q D U δ I : ℝ}
    (hpq : p.HolderConjugate q) (hD : 0 < D) (_hU : 0 < U) (hδ : 0 < δ) (hI : 0 ≤ I) :
    (U * (32 * δ) ^ (n - 1)) * ((4 : ℝ) ^ n) ^ p *
        ((D * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ)) *
          I ^ (1 / p)) ^ p) =
      (U * 32 ^ (n - 1) * ((4 : ℝ) ^ n) ^ p * D ^ p) * δ ^ (2 * p - 2 * n) * I := by
  have hpqdiv : p / q = p - 1 := by
    apply (div_eq_iff hpq.symm.pos.ne').mpr
    nlinarith [hpq.mul_eq_add]
  have hnat : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
  have he : (n - 1 : ℕ) +
      ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ)) * p = 2 * p - 2 * n := by
    calc
      _ = (n - 1 : ℕ) + (2 * (n : ℝ) + (n - 1 : ℕ)) * (p / q) -
          3 * (n - 1 : ℕ) * p := by ring
      _ = _ := by rw [hpqdiv, hnat]; ring
  have hpower : ((D * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ)) *
          I ^ (1 / p)) ^ p) = D ^ p *
      δ ^ (((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ)) * p) * I := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hD.le (by positivity), ← Real.rpow_mul hδ.le,
      ← Real.rpow_mul hI, one_div_mul_cancel hpq.pos.ne', Real.rpow_one]
  have hδpowers : δ ^ (n - 1) *
      δ ^ (((2 * (n : ℝ) + (n - 1 : ℕ)) / q - 3 * (n - 1 : ℕ)) * p) =
      δ ^ (2 * p - 2 * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hδ, he]
  calc
    _ = (U * 32 ^ (n - 1) * ((4 : ℝ) ^ n) ^ p * D ^ p) *
        (δ ^ (n - 1) * δ ^ (((2 * (n : ℝ) + (n - 1 : ℕ)) / q -
          3 * (n - 1 : ℕ)) * p)) * I := by rw [hpower, mul_pow]; ring
    _ = _ := by rw [hδpowers]
theorem restriction_implies_subcritical_kakeya_moment
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {p q : ℝ} (hpq : p.HolderConjugate q) (hpn : p < n) :
    ∃ J : ℝ, 0 < J ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : Space n → ℂ, MemLp f (ENNReal.ofReal p) volume →
      (∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ p ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        ENNReal.ofReal (J * δ ^ (2 * p - 2 * n) * ∫ y, ‖f y‖ ^ p) := by
  obtain ⟨D, hD, hdiscrete⟩ := restriction_implies_discrete_kakeya hR n hn hpq hpn
  obtain ⟨U, hU, hcap⟩ := packetCap_real_upper_all_scales (n := n) (by omega)
  refine ⟨U * 32 ^ (n - 1) * ((4 : ℝ) ^ n) ^ p * D ^ p, by positivity, ?_⟩
  intro δ hδ hδone f hf
  obtain ⟨m, v, hv, hsep, hcover⟩ := unit_sphere_finite_separated_net (n := n) hδ
  have hcapbound (i : Fin m) : OAI.Analysis.Fourier.Restriction.sphereMeasure n (packetCap (32 * δ) (v i)) ≤
      ENNReal.ofReal (U * (32 * δ) ^ (n - 1)) := by
    calc
      _ = ENNReal.ofReal ((OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap (32 * δ) (v i))) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hcap (32 * δ) (v i) (by positivity) (hv i))
  have hsum := hdiscrete m δ hδ hδone v hv hsep f hf
  have hI : 0 ≤ ∫ y, ‖f y‖ ^ p := integral_nonneg fun y ↦ Real.rpow_nonneg (norm_nonneg _) _
  calc
    _ ≤ ∑ i, OAI.Analysis.Fourier.Restriction.sphereMeasure n (packetCap (32 * δ) (v i)) *
        (ENNReal.ofReal ((4 : ℝ) ^ n) * OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f (v i)) ^ p :=
      lintegral_kakeya_le_net hδ hpq.pos.le f v hcover
    _ ≤ ∑ i, ENNReal.ofReal (U * (32 * δ) ^ (n - 1)) *
        (ENNReal.ofReal ((4 : ℝ) ^ n) * OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f (v i)) ^ p := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul' (hcapbound i) le_rfl
    _ = (ENNReal.ofReal (U * (32 * δ) ^ (n - 1)) * ENNReal.ofReal ((4 : ℝ) ^ n) ^ p) *
        ∑ i, OAI.MeasureTheory.Kakeya.kakeyaMaximal (2 * δ) f (v i) ^ p := by
      simp only [ENNReal.mul_rpow_of_nonneg _ _ hpq.pos.le, Finset.mul_sum, mul_assoc]
    _ ≤ (ENNReal.ofReal (U * (32 * δ) ^ (n - 1)) * ENNReal.ofReal ((4 : ℝ) ^ n) ^ p) *
        ENNReal.ofReal ((D * δ ^ ((2 * (n : ℝ) + (n - 1 : ℕ)) / q -
          3 * (n - 1 : ℕ)) * (∫ y, ‖f y‖ ^ p) ^ (1 / p)) ^ p) :=
      mul_le_mul' le_rfl hsum
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hpq.pos.le,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact kakeya_subcritical_scale (by omega) hpq hD hU hδ hI
theorem restriction_implies_critical_kakeya_moment
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) (n : ℕ) (hn : 2 ≤ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℝ, 0 < J ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ f : Space n → ℂ, MemLp f n volume →
      (∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ (n : ℝ) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        ENNReal.ofReal (J * δ ^ (-ε * n) * ∫ y, ‖f y‖ ^ (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let p : ℝ := max (((n : ℝ) + 1) / 2) ((n : ℝ) - ε * n / 2)
  have hp1 : 1 < p := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hp : 0 < p := by linarith
  have hpn : p < n := max_lt (by linarith) (by nlinarith)
  have hpexp : -ε * n ≤ 2 * p - 2 * n := by
    have h := le_max_right (((n : ℝ) + 1) / 2) ((n : ℝ) - ε * n / 2)
    change (n : ℝ) - ε * n / 2 ≤ p at h
    linarith
  obtain ⟨J, hJ, hbound⟩ := restriction_implies_subcritical_kakeya_moment hR n hn
    (Real.HolderConjugate.conjExponent hp1) hpn
  refine ⟨J, hJ, ?_⟩
  intro δ hδ hδone f hf
  have hr : 1 ≤ (n : ℝ) / p := (le_div_iff₀ hp).mpr (by linarith)
  have hrpos : 0 < (n : ℝ) / p := by positivity
  have hpr : p * ((n : ℝ) / p) = n := by field_simp
  have hrp : ((n : ℝ) / p) * p = n := div_mul_cancel₀ _ hp.ne'
  have hfin : MemLp f (ENNReal.ofReal (p * ((n : ℝ) / p))) volume := by
    simpa only [hpr, ENNReal.ofReal_natCast] using hf
  have hg := memLp_kakeyaPowerInput hp hrpos hfin
  have hmoment := hbound δ hδ hδone (kakeyaPowerInput ((n : ℝ) / p) f) hg
  have heq : (fun y ↦ ‖kakeyaPowerInput ((n : ℝ) / p) f y‖ ^ p) =
      fun y ↦ ‖f y‖ ^ (n : ℝ) := by
    funext y
    rw [norm_kakeyaPowerInput, ← Real.rpow_mul (norm_nonneg _), hrp]
  rw [heq] at hmoment
  calc
    _ ≤ ∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (kakeyaPowerInput ((n : ℝ) / p) f) ω ^ p ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      apply lintegral_mono
      intro ω
      calc
        _ = (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ ((n : ℝ) / p)) ^ p := by
          rw [← ENNReal.rpow_mul, hrp]
        _ ≤ _ := ENNReal.rpow_le_rpow
          (kakeyaMaximal_rpow_le_powerInput hδ hr hf.aestronglyMeasurable ω) hp.le
    _ ≤ ENNReal.ofReal (J * δ ^ (2 * p - 2 * n) * ∫ y, ‖f y‖ ^ (n : ℝ)) := hmoment
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun y ↦ Real.rpow_nonneg (norm_nonneg _) _)
      apply mul_le_mul_of_nonneg_left _ hJ.le
      exact Real.rpow_le_rpow_of_exponent_ge hδ hδone hpexp
theorem kakeya_moment_implies_norm_bound {n : ℕ} (hn : 1 ≤ n)
    {δ ε J : ℝ} (hδ : 0 < δ) (hJ : 0 < J)
    {f : Space n → ℂ} (hf : MemLp f n volume)
    (hmoment : (∫⁻ ω, OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ (n : ℝ) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ENNReal.ofReal (J * δ ^ (-ε * n) * ∫ y, ‖f y‖ ^ (n : ℝ))) :
    MemLp (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ∧
      eLpNorm (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        ENNReal.ofReal (J ^ (1 / (n : ℝ)) * δ ^ (-ε)) * eLpNorm f n volume := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hnR.ne'
  have hI : 0 ≤ ∫ y, ‖f y‖ ^ (n : ℝ) :=
    integral_nonneg fun y ↦ Real.rpow_nonneg (norm_nonneg _) _
  have hm : AEStronglyMeasurable (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
    (measurable_kakeyaMaximal δ f hf.aestronglyMeasurable).aestronglyMeasurable
  have hfnorm : ENNReal.ofReal ((∫ y, ‖f y‖ ^ (n : ℝ)) ^ (1 / (n : ℝ))) =
      eLpNorm f n volume := by
    rw [← ofReal_lpNorm hf, lpNorm_eq_integral_norm_rpow_toReal hn0 (by simp)
      hf.aestronglyMeasurable]
    simp only [ENNReal.toReal_natCast, one_div]
  have hroot : (J * δ ^ (-ε * n) * ∫ y, ‖f y‖ ^ (n : ℝ)) ^ (1 / (n : ℝ)) =
      (J ^ (1 / (n : ℝ)) * δ ^ (-ε)) *
        (∫ y, ‖f y‖ ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by
    have he : (-ε * n) * (1 / (n : ℝ)) = -ε := by field_simp
    rw [Real.mul_rpow (by positivity) hI, Real.mul_rpow hJ.le (by positivity),
      ← Real.rpow_mul hδ.le, he]
  have hnorm : eLpNorm (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ENNReal.ofReal (J ^ (1 / (n : ℝ)) * δ ^ (-ε)) * eLpNorm f n volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hn0 (by simp)]
    simp only [ENNReal.toReal_natCast, enorm_eq_self]
    have h := ENNReal.rpow_le_rpow hmoment (by positivity : 0 ≤ 1 / (n : ℝ))
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), hroot,
      ENNReal.ofReal_mul (by positivity), hfnorm] at h
    exact h
  refine ⟨?_, hnorm⟩
  exact ⟨hm, hnorm.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)⟩
theorem restriction_implies_kakeyaMaximal
    (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture := by
  intro n hn ε hε
  obtain ⟨J, hJ, hmoment⟩ := restriction_implies_critical_kakeya_moment hR n hn hε
  refine ⟨J ^ (1 / (n : ℝ)), by positivity, ?_⟩
  intro δ hδ hδone f hf
  exact kakeya_moment_implies_norm_bound (by omega) hδ hJ hf (hmoment δ hδ hδone f hf)
end OAI.MeasureTheory.Kakeya
end
end
section
open OAI.Analysis.Fourier.Wave
open _root_.MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.MeasureTheory.Kakeya
theorem sphereMeasure_univ_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ := by
  let v : Space n := EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℝ)
  have hv : ‖v‖ = 1 := by simp [v]
  have hcap := OAI.Analysis.Fourier.Restriction.packetCap_real_lower hn (δ := 1) zero_lt_one le_rfl hv
  simp only [one_pow, mul_one] at hcap
  have hreal : 0 < (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap 1 v) :=
    (OAI.Analysis.Fourier.Restriction.packetCap_lower_coefficient_pos hn).trans_le hcap
  have hpos : 0 < OAI.Analysis.Fourier.Restriction.sphereMeasure n (packetCap 1 v) := (ENNReal.toReal_pos_iff.mp hreal).1
  exact hpos.trans_le (measure_mono (Set.subset_univ _))
theorem maximal_implies_hausdorffMeasure_ne_zero (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s) (hsn : s < n)
    {F : Set (Space n)} (hF : OAI.MeasureTheory.Kakeya.IsKakeyaSet F) :
    Measure.hausdorffMeasure s F ≠ 0 := by
  intro hnull
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 < 1 / (n : ℝ) := by positivity
  obtain ⟨D, hD, hbound⟩ := maximal_implies_cover_sum_bound hK hn hs hsn
  let A : ℝ≥0∞ := (2 : ℝ≥0∞) ^ s
  have hA : A < ∞ := ENNReal.rpow_lt_top_of_nonneg hs.le (by norm_num)
  have hsmall (m : ℕ) :
      ENNReal.ofReal (lineOccupancyConstant n) * OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ ≤
        D * (A * (1 / 2 : ℝ≥0∞) ^ m) ^ (1 / (n : ℝ)) := by
    have hε : 0 < (1 / 2 : ℝ≥0∞) ^ m := pos_iff_ne_zero.mpr (pow_ne_zero m (by norm_num))
    obtain ⟨x, r, Z, hZ, hcover, hr, hcost⟩ := hausdorff_null_ball_cover hs hnull hε
    have hcostfin : ballCoverCost s r < ∞ :=
      lt_of_le_of_lt hcost (ENNReal.mul_lt_top hA (by finiteness))
    have hlo := dyadic_occupancy_integral_lower (show 1 ≤ n by omega) x r
      (fun j ↦ (hr j).2) hZ hF hcover
    exact hlo.trans ((hbound x r hcostfin).trans
      (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hcost hq.le)))
  have hgeo : Tendsto (fun m : ℕ ↦ (1 / 2 : ℝ≥0∞) ^ m) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have harg : Tendsto (fun m : ℕ ↦ A * (1 / 2 : ℝ≥0∞) ^ m) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hgeo (Or.inr hA.ne)
  have hlim : Tendsto (fun m : ℕ ↦ D * (A * (1 / 2 : ℝ≥0∞) ^ m) ^ (1 / (n : ℝ)))
      atTop (𝓝 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hD.ne hq).comp harg
  have hzero : ENNReal.ofReal (lineOccupancyConstant n) * OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall hsmall)
  have hpositive : 0 < ENNReal.ofReal (lineOccupancyConstant n) * OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (lineOccupancyConstant_pos n)).ne'
      (sphereMeasure_univ_pos (show 1 ≤ n by omega)).ne'
  exact hpositive.not_ge hzero
theorem kakeyaMaximal_implies_kakeya (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture) : OAI.MeasureTheory.Kakeya.KakeyaConjecture := by
  intro n hn F hF
  apply le_antisymm
  · calc
      dimH F ≤ dimH (Set.univ : Set (Space n)) := dimH_mono (Set.subset_univ F)
      _ = n := by rw [Real.dimH_univ_eq_finrank]; simp only [Space, finrank_euclideanSpace_fin]
  · apply ENNReal.le_of_forall_nnreal_lt
    intro d hd
    by_cases hd0 : d = 0
    · simp [hd0]
    · have hdpos : 0 < (d : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd0)
      have hdn : (d : ℝ) < n := by exact_mod_cast hd
      exact le_dimH_of_hausdorffMeasure_ne_zero
        (maximal_implies_hausdorffMeasure_ne_zero hK hn hdpos hdn hF)
theorem restriction_implies_kakeya (hR : OAI.Analysis.Fourier.Restriction.SphericalRestrictionConjecture) : OAI.MeasureTheory.Kakeya.KakeyaConjecture :=
  kakeyaMaximal_implies_kakeya (restriction_implies_kakeyaMaximal hR)
end OAI.MeasureTheory.Kakeya
end
end

theorem OMA.solution : OMA.R_Kakeya_kakeya_set_conjecture_R3.H2 := by
  intro hK
  exact OAI.MeasureTheory.Kakeya.kakeyaMaximal_implies_kakeya hK
