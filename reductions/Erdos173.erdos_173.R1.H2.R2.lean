import OMAReductions.R_Erdos173_erdos_173_R1
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Dynamics.Ergodic.Action.OfMinimal
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Function.AEMeasurableSequence
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Erdős 173, reduction of the two-scale step

The far-scale branch integrates a uniform pair bound for the Bessel kernel. The
nearby-scale branch thresholds a jointly measurable version of a continuous
bounded sign field and applies irrational rotation at a density boundary.

Adapted from Jacob Parish and Plasma AI, plasma-ai/erdos-173 at
4a368a652753fab53272f7a747755876f04bc2cc, Apache-2.0, with the angular
measure definitions adapted from OpenAI, openai/math at adc7f124, Apache-2.0.
The normalization and sampling assembly follow Marcus Buffett’s merged
reductions (#3825 and #4452). The joint representative and zero-moment
lemmas follow Salofe’s merged proofs (#5520 and #5889). The development
is adapted to Lean v4.33.1.
-/

-- OAI.Geometry.PlaneColoring.Coloring
section
section

namespace OAI

namespace EuclideanFiveColor

private def ProperColoring (k : ℕ) (c : ℂ → Fin k) : Prop :=
  ∀ x y : ℂ, ‖x - y‖ = 1 → c x ≠ c y

end EuclideanFiveColor
noncomputable section
open MeasureTheory
namespace EuclideanFiveColor
private instance anglePeriodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
private abbrev Angles := AddCircle (2*Real.pi)
private def angularMeasure : Measure Angles := AddCircle.haarAddCircle
private def direction (t : Angles) : ℂ := AddCircle.toCircle t
private instance : IsProbabilityMeasure angularMeasure := inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 2*Real.pi)))
private instance : angularMeasure.IsAddHaarMeasure := inferInstanceAs (AddCircle.haarAddCircle (T := 2*Real.pi)).IsAddHaarMeasure
lemma direction_continuous : Continuous direction := continuous_subtype_val.comp AddCircle.continuous_toCircle
@[simp] lemma direction_norm (t : Angles) : ‖direction t‖ = 1 := Circle.norm_coe _
@[simp] lemma direction_real (t : ℝ) : direction (t : Angles) = (Circle.exp t : ℂ) := by
  simp [direction,AddCircle.toCircle_apply_mk,Real.pi_ne_zero]

private def WeakColoring (k : ℕ) (c : ℂ → Fin k) : Prop :=
  AEMeasurable c (volume : Measure ℂ) ∧ ∀ᵐ p ∂(volume : Measure ℂ).prod angularMeasure,
    c p.1 ≠ c (p.1+direction p.2)
end EuclideanFiveColor
end

end OAI
end

-- Erdos173.Basic
section
section

noncomputable section

namespace Erdos173

open MeasureTheory OAI.EuclideanFiveColor

private def ζ : ℂ := ⟨1 / 2, √3 / 2⟩

lemma norm_ζ : ‖ζ‖ = 1 := by
  rw [Complex.norm_def, Real.sqrt_eq_one]
  simp [ζ, Complex.normSq]
  ring_nf
  norm_num

lemma norm_one_sub_ζ : ‖1 - ζ‖ = 1 := by
  rw [Complex.norm_def, Real.sqrt_eq_one]
  simp [ζ, Complex.normSq]
  ring_nf
  norm_num

lemma norm_ζ_sub_one : ‖ζ - 1‖ = 1 := by
  rw [norm_sub_rev, norm_one_sub_ζ]

lemma direction_add (s t : Angles) : direction (s + t) = direction s * direction t := by
  simp [direction, AddCircle.toCircle_add]

private def MonoCopy (c : ℂ → Fin 2) (a b p u : ℂ) : Prop :=
  c (p + u * a) = c p ∧ c (p + u * b) = c p

private def Avoids (c : ℂ → Fin 2) (a b : ℂ) : Prop :=
  ∀ p u : ℂ, ‖u‖ = 1 → ¬ MonoCopy c a b p u

private def WeaklyAvoids (c : ℂ → Fin 2) (a b : ℂ) : Prop :=
  ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure, ¬ MonoCopy c a b q.1 (direction q.2)

private def AvoidsEq (c : ℂ → Fin 2) (r : ℝ) : Prop :=
  Avoids c r (r * ζ)

private def WeaklyAvoidsEq (c : ℂ → Fin 2) (r : ℝ) : Prop :=
  WeaklyAvoids c r (r * ζ)

end Erdos173

end
end

-- Erdos173.Measurable.Density
section
section

noncomputable section

namespace Erdos173
open MeasureTheory Metric Set Filter Topology OAI.EuclideanFiveColor

private def DensityZero (K : Set ℂ) (p : ℂ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ ρ, 0 < ρ → ρ < δ →
    volume (K ∩ closedBall p ρ) ≤ ENNReal.ofReal (ε * ρ ^ 2)

private def boundary (c : ℂ → Fin 2) : Set ℂ :=
  {p | ∀ i, ¬ DensityZero {z | c z = i} p}

lemma measurable_measure_inter_closedBall {K : Set ℂ} (hK : MeasurableSet K) (ρ : ℝ) :
    Measurable fun p => volume (K ∩ closedBall p ρ) := by
  have hs : MeasurableSet {q : ℂ × ℂ | q.2 ∈ K ∧ dist q.2 q.1 ≤ ρ} :=
    (hK.preimage measurable_snd).inter
      (measurableSet_le (continuous_snd.dist continuous_fst).measurable measurable_const)
  exact measurable_measure_prodMk_left hs

lemma densityZero_of_seq {K : Set ℂ} {p : ℂ}
    (h : ∀ n : ℕ, ∃ m : ℕ, ∀ k, m ≤ k →
      volume (K ∩ closedBall p (1 / (k + 1))) ≤
        ENNReal.ofReal (1 / (n + 1) * (1 / (k + 1)) ^ 2)) :
    DensityZero K p := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by positivity : 0 < ε / 4)
  obtain ⟨m, hm⟩ := h n
  refine ⟨1 / (m + 1), by positivity, fun ρ hρ hρδ => ?_⟩
  have hinv : (m + 1 : ℝ) < ρ⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) hρ]; simpa using hρδ
  set j := ⌊ρ⁻¹⌋₊ with hj
  have hj1 : (m + 1 : ℝ) ≤ j := by
    have : m + 1 ≤ j := Nat.le_floor (by push_cast; linarith)
    exact_mod_cast this
  have hjle : (j : ℝ) ≤ ρ⁻¹ := Nat.floor_le (by positivity)
  have hjlt : ρ⁻¹ < j + 1 := Nat.lt_floor_add_one _
  have hjpos : (1 : ℝ) ≤ j := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hjnat : 1 ≤ j := by exact_mod_cast hjpos
  have hk : m ≤ j - 1 := by
    have : m + 1 ≤ j := by exact_mod_cast hj1
    omega
  have hcast : ((j - 1 : ℕ) : ℝ) + 1 = j := by
    rw [Nat.cast_sub hjnat]; push_cast; ring
  have key := hm (j - 1) hk
  rw [hcast] at key
  have hρj : ρ ≤ 1 / j := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hjle hρ.le
    rw [mul_inv_cancel₀ hρ.ne'] at this
    linarith [mul_comm ρ (j : ℝ)]
  have hj2 : 1 / (j : ℝ) < 2 * ρ := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : 1 < ρ * (j + 1) := by
      have := mul_lt_mul_of_pos_left hjlt hρ
      rwa [mul_inv_cancel₀ hρ.ne'] at this
    nlinarith
  calc volume (K ∩ closedBall p ρ)
      ≤ volume (K ∩ closedBall p (1 / j)) := by
        gcongr
    _ ≤ ENNReal.ofReal (1 / (n + 1) * (1 / j) ^ 2) := key
    _ ≤ ENNReal.ofReal (ε * ρ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have h0 : 0 ≤ 1 / (j : ℝ) := by positivity
        have hsq : (1 / (j : ℝ)) ^ 2 ≤ 4 * ρ ^ 2 := by nlinarith
        have hn' : (1 : ℝ) / (n + 1) ≤ ε / 4 := hn.le
        calc 1 / ((n : ℝ) + 1) * (1 / j) ^ 2 ≤ ε / 4 * (4 * ρ ^ 2) := by
              gcongr
          _ = ε * ρ ^ 2 := by ring

theorem measurableSet_densityZero {K : Set ℂ} (hK : MeasurableSet K) :
    MeasurableSet {p | DensityZero K p} := by
  have heq : {p | DensityZero K p} = ⋂ n : ℕ, ⋃ m : ℕ, ⋂ k : ℕ, ⋂ (_ : m ≤ k),
      {p | volume (K ∩ closedBall p (1 / (k + 1))) ≤
        ENNReal.ofReal (1 / (n + 1) * (1 / (k + 1)) ^ 2)} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · intro h n
      obtain ⟨δ, hδ, hp⟩ := h (1 / (n + 1)) (by positivity)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      refine ⟨m, fun k hk => hp _ (by positivity) (lt_of_le_of_lt ?_ hm)⟩
      gcongr
    · exact densityZero_of_seq
  rw [heq]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m =>
    MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le (measurable_measure_inter_closedBall hK _) measurable_const

theorem ae_densityZero {K : Set ℂ} (hK : MeasurableSet K) :
    ∀ᵐ p, p ∉ K → DensityZero K p := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hK]
    with p hp hpK
  rw [indicator_of_notMem hpK] at hp
  intro ε hε
  have hev := (ENNReal.tendsto_nhds_zero.1 hp) (ENNReal.ofReal (ε / 4)) (by positivity)
  obtain ⟨δ, hδ, hP⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev
  refine ⟨δ, hδ, fun ρ hρ hρδ => ?_⟩
  have hball : volume (closedBall p ρ) = ENNReal.ofReal (Real.pi * ρ ^ 2) := by
    rw [Complex.volume_closedBall, ENNReal.ofReal_mul Real.pi_pos.le,
      ENNReal.ofReal_pow hρ.le, mul_comm]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  have h1 := hP ⟨hρ, hρδ⟩
  rw [ENNReal.div_le_iff
    (by rw [hball]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)
    (by rw [hball]; simp)] at h1
  refine h1.trans ?_
  rw [hball, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have := Real.pi_le_four
  have : 0 ≤ ε * ρ ^ 2 := by positivity
  nlinarith

theorem measurableSet_boundary {c : ℂ → Fin 2} (hc : Measurable c) :
    MeasurableSet (boundary c) := by
  have : boundary c = ⋂ i, {p | DensityZero {z | c z = i} p}ᶜ := by
    ext p; simp [boundary]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_densityZero (measurableSet_eq_fun hc measurable_const)).compl

theorem volume_boundary {c : ℂ → Fin 2} (hc : Measurable c) : volume (boundary c) = 0 := by
  have h : ∀ᵐ p, ∀ i, p ∉ {z | c z = i} → DensityZero {z | c z = i} p :=
    ae_all_iff.2 fun i => ae_densityZero (measurableSet_eq_fun hc measurable_const)
  refine measure_mono_null (fun p hp => ?_) (ae_iff.1 h)
  intro hall
  refine hp (c p + 1) (hall _ ?_)
  change c p ≠ c p + 1
  generalize c p = a
  fin_cases a <;> decide

lemma ae_prod_add_notMem {N : Set ℂ} (hN : MeasurableSet N) (hN0 : volume N = 0)
    {w : Angles → ℂ} (hw : Continuous w) :
    ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure, q.1 + w q.2 ∉ N := by
  rw [ae_iff]
  simp only [not_not]
  have hm : MeasurableSet {q : ℂ × Angles | q.1 + w q.2 ∈ N} :=
    hN.preimage (by fun_prop)
  rw [Measure.prod_apply_symm hm]
  refine (lintegral_congr fun t => ?_).trans lintegral_zero
  change volume ((· + w t) ⁻¹' N) = 0
  rw [measure_preimage_add_right]
  exact hN0

theorem volume_ne_zero_of_weaklyAvoids {c : ℂ → Fin 2} (hc : Measurable c) {a b : ℂ}
    (h : WeaklyAvoids c a b) (i : Fin 2) : volume {z | c z = i} ≠ 0 := by
  intro h0
  have hN : MeasurableSet {z | c z = i} := measurableSet_eq_fun hc measurable_const
  have h1 := ae_prod_add_notMem hN h0 (w := fun _ => 0) continuous_const
  have h2 := ae_prod_add_notMem hN h0 (w := fun t => direction t * a)
    (direction_continuous.mul continuous_const)
  have h3 := ae_prod_add_notMem hN h0 (w := fun t => direction t * b)
    (direction_continuous.mul continuous_const)
  have hfalse : ∀ᵐ _q ∂(volume : Measure ℂ).prod angularMeasure, False := by
    filter_upwards [h, h1, h2, h3] with q hq hq1 hq2 hq3
    apply hq
    simp only [add_zero] at hq1 hq2 hq3
    constructor
    · generalize c (q.1 + direction q.2 * a) = x at hq2
      generalize c q.1 = y at hq1
      fin_cases i <;> fin_cases x <;> fin_cases y <;> simp_all
    · generalize c (q.1 + direction q.2 * b) = x at hq3
      generalize c q.1 = y at hq1
      fin_cases i <;> fin_cases x <;> fin_cases y <;> simp_all
  rw [ae_iff] at hfalse
  simp only [not_false_eq_true] at hfalse
  have huniv : (volume.prod angularMeasure) (univ : Set (ℂ × Angles)) = 0 := hfalse
  rw [← univ_prod_univ, Measure.prod_prod] at huniv
  simp at huniv
end Erdos173

end
end

-- Erdos173.Measurable.Apex
section
section

noncomputable section

namespace Erdos173

open MeasureTheory Metric Set Filter OAI.EuclideanFiveColor

theorem apex_density {c : ℂ → Fin 2} (hc : Measurable c) {a b : ℂ} (h : WeaklyAvoids c a b)
    {i : Fin 2} {p : ℂ} (hp : ¬ DensityZero {z | c z = i} p) (t₀ : Angles)
    (ha : DensityZero {z | c z ≠ i} (p + direction t₀ * a))
    (hb : DensityZero {z | c z ≠ i} (p + direction t₀ * b)) : False := by
  set K : Set ℂ := {z | c z = i} with hK
  set L : ℝ := ‖a‖ + ‖b‖ + 1 with hL
  have hL0 : 0 < L := by rw [hL]; positivity
  unfold DensityZero at hp
  push Not at hp
  obtain ⟨ε, hε, hp⟩ := hp
  obtain ⟨δa, hδa, ha⟩ := ha (ε / 16) (by positivity)
  obtain ⟨δb, hδb, hb⟩ := hb (ε / 16) (by positivity)
  obtain ⟨r, hr, hrδ, hgood⟩ := hp (min δa δb / 2) (by positivity)
  have h2a : 2 * r < δa := by have := min_le_left δa δb; linarith
  have h2b : 2 * r < δb := by have := min_le_right δa δb; linarith
  set T : Set Angles := {t | dist (direction t) (direction t₀) < r / L} with hT
  have hTo : IsOpen T :=
    isOpen_lt (direction_continuous.dist continuous_const) continuous_const
  have hTpos : angularMeasure T ≠ 0 :=
    (hTo.measure_pos _ ⟨t₀, by simp only [hT, mem_ofPred_eq, dist_self]; positivity⟩).ne'
  have hTfin : angularMeasure T ≠ ⊤ := measure_ne_top _ _

  have hbad : ∀ w : ℂ, ‖w‖ ≤ L → ∀ C,
      volume ({z | c z ≠ i} ∩ closedBall (p + direction t₀ * w) (2 * r)) ≤ C →
      (volume.prod angularMeasure)
        {q : ℂ × Angles | q.1 ∈ closedBall p r ∧ q.2 ∈ T ∧ c (q.1 + direction q.2 * w) ≠ i}
        ≤ C * angularMeasure T := by
    intro w hw C hC
    have hm : MeasurableSet {q : ℂ × Angles |
        q.1 ∈ closedBall p r ∧ q.2 ∈ T ∧ c (q.1 + direction q.2 * w) ≠ i} := by
      refine (measurableSet_closedBall.preimage measurable_fst).inter
        ((hTo.measurableSet.preimage measurable_snd).inter ?_)
      refine (measurableSet_eq_fun (hc.comp ?_) measurable_const).compl
      exact (continuous_fst.add
        ((direction_continuous.comp continuous_snd).mul continuous_const)).measurable
    rw [Measure.prod_apply_symm hm, ← lintegral_indicator_const hTo.measurableSet]
    refine lintegral_mono fun t => ?_
    by_cases ht : t ∈ T
    · rw [indicator_of_mem ht]
      refine le_trans (measure_mono (t := (· + direction t * w) ⁻¹'
        ({z | c z ≠ i} ∩ closedBall (p + direction t₀ * w) (2 * r))) ?_) ?_
      · rintro x ⟨hx, -, hcx⟩
        refine ⟨hcx, ?_⟩
        rw [mem_closedBall] at hx ⊢
        have htd : dist (direction t) (direction t₀) < r / L := ht
        calc dist (x + direction t * w) (p + direction t₀ * w)
            ≤ dist x p + dist (direction t * w) (direction t₀ * w) := dist_add_add_le _ _ _ _
          _ ≤ r + r := by
            gcongr
            rw [dist_eq_norm, ← sub_mul, norm_mul, ← dist_eq_norm]
            calc dist (direction t) (direction t₀) * ‖w‖ ≤ r / L * L := by
                  gcongr
              _ = r := by field_simp
          _ = 2 * r := by ring
      · rw [measure_preimage_add_right]
        exact hC
    · rw [indicator_of_notMem ht]
      exact le_of_eq (measure_mono_null (fun x hx => (ht hx.2.1).elim) measure_empty)
  have hmono : (volume.prod angularMeasure)
      {q : ℂ × Angles | MonoCopy c a b q.1 (direction q.2)} = 0 := by
    simpa using ae_iff.1 h
  set C := ENNReal.ofReal (ε / 16 * (2 * r) ^ 2) with hC
  have hA := hbad a (by rw [hL]; linarith [norm_nonneg b]) C (ha (2 * r) (by positivity) h2a)
  have hB := hbad b (by rw [hL]; linarith [norm_nonneg a]) C (hb (2 * r) (by positivity) h2b)
  have hsub : (K ∩ closedBall p r) ×ˢ T ⊆
      {q : ℂ × Angles | MonoCopy c a b q.1 (direction q.2)} ∪
        {q : ℂ × Angles | q.1 ∈ closedBall p r ∧ q.2 ∈ T ∧ c (q.1 + direction q.2 * a) ≠ i} ∪
        {q : ℂ × Angles | q.1 ∈ closedBall p r ∧ q.2 ∈ T ∧ c (q.1 + direction q.2 * b) ≠ i} := by
    rintro ⟨x, t⟩ ⟨⟨hxK, hxr⟩, ht⟩
    by_contra hq
    simp only [mem_union, mem_ofPred_eq, not_or, not_and, not_not] at hq
    obtain ⟨⟨hm, hqa⟩, hqb⟩ := hq
    have hxK' : c x = i := hxK
    exact hm ⟨(hqa hxr ht).trans hxK'.symm, (hqb hxr ht).trans hxK'.symm⟩
  have hle : volume (K ∩ closedBall p r) * angularMeasure T ≤ (C + C) * angularMeasure T := by
    rw [← Measure.prod_prod, add_mul]
    calc _ ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := add_le_add_left (measure_union_le _ _) _
      _ ≤ 0 + C * angularMeasure T + C * angularMeasure T := by
        rw [hmono]
        gcongr
      _ = _ := by rw [zero_add]
  rw [ENNReal.mul_le_mul_iff_left hTpos hTfin] at hle
  have hCC : C + C < ENNReal.ofReal (ε * r ^ 2) := by
    rw [hC, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    nlinarith [sq_nonneg r, mul_pos hε (pow_pos hr 2)]
  exact absurd (hle.trans_lt (hCC.trans hgood)) (lt_irrefl _)
end Erdos173

end
end

-- Erdos173.Measurable.Boundary
section
section

noncomputable section

namespace Erdos173

open MeasureTheory Metric Set Filter Topology
open scoped symmDiff

private def square (p : ℂ) (s : ℝ) : Set ℂ :=
  {z | p.re ≤ z.re ∧ z.re ≤ p.re + s ∧ p.im ≤ z.im ∧ z.im ≤ p.im + s}

lemma mem_square_self (p : ℂ) {s : ℝ} (hs : 0 ≤ s) : p ∈ square p s :=
  ⟨le_rfl, by linarith, le_rfl, by linarith⟩

lemma square_eq_preimage (p : ℂ) (s : ℝ) :
    square p s = Complex.measurableEquivRealProd ⁻¹'
      (Icc p.re (p.re + s) ×ˢ Icc p.im (p.im + s)) := by
  ext z
  simp [square, Complex.measurableEquivRealProd]
  tauto

lemma volume_square (p : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    volume (square p s) = ENNReal.ofReal (s ^ 2) := by
  rw [square_eq_preimage, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

lemma isClosed_square (p : ℂ) (s : ℝ) : IsClosed (square p s) :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))

lemma convex_square (p : ℂ) (s : ℝ) : Convex ℝ (square p s) := by
  have : square p s = Complex.reLm ⁻¹' Icc p.re (p.re + s) ∩
      Complex.imLm ⁻¹' Icc p.im (p.im + s) := by
    ext z
    simp [square]
    tauto
  rw [this]
  exact ((convex_Icc _ _).linear_preimage _).inter ((convex_Icc _ _).linear_preimage _)

lemma square_subset_closedBall {p z : ℂ} {s : ℝ} (hz : z ∈ square p s) :
    square p s ⊆ closedBall z (2 * s) := by
  rintro w ⟨h1, h2, h3, h4⟩
  obtain ⟨g1, g2, g3, g4⟩ := hz
  rw [mem_closedBall, dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]
  have hre : |w.re - z.re| ≤ s := abs_le.2 ⟨by linarith, by linarith⟩
  have him : |w.im - z.im| ≤ s := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

lemma isCompact_square (p : ℂ) (s : ℝ) : IsCompact (square p s) := by
  rcases (square p s).eq_empty_or_nonempty with he | ⟨z, hz⟩
  · rw [he]
    exact isCompact_empty
  · exact Metric.isCompact_of_isClosed_isBounded (isClosed_square p s)
      (isBounded_closedBall.subset (square_subset_closedBall hz))

lemma volume_square_ne_top (p : ℂ) (s : ℝ) : volume (square p s) ≠ ⊤ :=
  (isCompact_square p s).measure_lt_top.ne

lemma volume_inter_square_ne_top (K : Set ℂ) (p : ℂ) (s : ℝ) :
    volume (K ∩ square p s) ≠ ⊤ :=
  ne_top_of_le_ne_top (volume_square_ne_top p s) (measure_mono inter_subset_right)

lemma square_eq_preimage_sub (p : ℂ) (s : ℝ) :
    square p s = (fun z => z - p) ⁻¹' square 0 s := by
  ext z
  simp only [square, mem_ofPred_eq, mem_preimage, Complex.sub_re, Complex.sub_im,
    Complex.zero_re, Complex.zero_im, zero_add]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

lemma tendsto_volume_square_symmDiff (s : ℝ) (p₀ : ℂ) :
    Tendsto (fun p => volume (square p s ∆ square p₀ s)) (𝓝 p₀) (𝓝 0) := by
  let f : ℂ → C(ℂ, ℂ) := fun p => ⟨fun z => z - p, by fun_prop⟩
  have hf : Continuous f :=
    ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.sub continuous_fst)
  have h := tendsto_measure_symmDiff_preimage_nhds_zero (μ := volume) (ν := volume)
    (s := square 0 s) (hf.tendsto p₀)
    (Eventually.of_forall fun p => measurePreserving_sub_right volume p)
    (measurePreserving_sub_right volume p₀) (isClosed_square 0 s).measurableSet.nullMeasurableSet
    (volume_square_ne_top 0 s)
  convert h using 3 with p
  rw [square_eq_preimage_sub p, square_eq_preimage_sub p₀]
  rfl

lemma abs_sub_toReal_le {A X Y : Set ℂ} (hX : volume X ≠ ⊤) (hY : volume Y ≠ ⊤) :
    |(volume (A ∩ X)).toReal - (volume (A ∩ Y)).toReal| ≤ (volume (X ∆ Y)).toReal := by
  have hXY : volume (X ∆ Y) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hX, hY⟩)
    ((measure_mono symmDiff_subset_union).trans (measure_union_le _ _))
  have hAX : volume (A ∩ X) ≠ ⊤ := ne_top_of_le_ne_top hX (measure_mono inter_subset_right)
  have hAY : volume (A ∩ Y) ≠ ⊤ := ne_top_of_le_ne_top hY (measure_mono inter_subset_right)
  have key : ∀ X Y : Set ℂ, volume (A ∩ X) ≤ volume (A ∩ Y) + volume (X ∆ Y) := by
    intro X Y
    calc volume (A ∩ X) ≤ volume ((A ∩ Y) ∪ (X ∆ Y)) := by
          refine measure_mono fun z ⟨hzA, hzX⟩ => ?_
          by_cases hzY : z ∈ Y
          · exact Or.inl ⟨hzA, hzY⟩
          · exact Or.inr (mem_symmDiff.2 (Or.inl ⟨hzX, hzY⟩))
      _ ≤ _ := measure_union_le _ _
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hAY, hXY⟩) (key X Y)
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hAX, hXY⟩)
    ((key Y X).trans_eq (by rw [symmDiff_comm]))
  rw [ENNReal.toReal_add hAY hXY] at h1
  rw [ENNReal.toReal_add hAX hXY] at h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

lemma continuous_volume_inter_square (A : Set ℂ) (s : ℝ) :
    Continuous fun p => (volume (A ∩ square p s)).toReal := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun p => (volume (square p s ∆ square p₀ s)).toReal)
    (fun _ => dist_nonneg) (fun p => ?_) ?_
  · rw [Real.dist_eq]
    exact abs_sub_toReal_le (volume_square_ne_top p s) (volume_square_ne_top p₀ s)
  · have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_volume_square_symmDiff s p₀)
    exact this

lemma toReal_inter_add_compl {A : Set ℂ} (hA : MeasurableSet A) (p : ℂ) {s : ℝ}
    (hs : 0 ≤ s) :
    (volume (A ∩ square p s)).toReal + (volume (Aᶜ ∩ square p s)).toReal = s ^ 2 := by
  rw [← ENNReal.toReal_add (volume_inter_square_ne_top _ _ _) (volume_inter_square_ne_top _ _ _),
    inter_comm A, inter_comm Aᶜ, ← sdiff_eq, measure_inter_add_sdiff _ hA, volume_square p hs,
    ENNReal.toReal_ofReal (by positivity)]

lemma exists_balanced_mem_segment (A : Set ℂ) (s : ℝ) {q₁ q₂ : ℂ}
    (h₁ : (volume (Aᶜ ∩ square q₁ s)).toReal ≤ (volume (A ∩ square q₁ s)).toReal)
    (h₂ : (volume (A ∩ square q₂ s)).toReal ≤ (volume (Aᶜ ∩ square q₂ s)).toReal) :
    ∃ q ∈ segment ℝ q₁ q₂,
      (volume (A ∩ square q s)).toReal = (volume (Aᶜ ∩ square q s)).toReal := by
  set g : ℂ → ℝ := fun q => (volume (A ∩ square q s)).toReal - (volume (Aᶜ ∩ square q s)).toReal
    with hg
  have hgc : Continuous g :=
    (continuous_volume_inter_square A s).sub (continuous_volume_inter_square Aᶜ s)
  obtain ⟨q, hq, hq0⟩ := (convex_segment q₁ q₂).isPreconnected.intermediate_value
    (right_mem_segment ℝ q₁ q₂) (left_mem_segment ℝ q₁ q₂) hgc.continuousOn
    (show (0 : ℝ) ∈ Icc (g q₂) (g q₁) from
      ⟨by simp only [hg]; linarith, by simp only [hg]; linarith⟩)
  exact ⟨q, hq, by simp only [hg] at hq0; linarith⟩

lemma exists_balanced_subsquare {A : Set ℂ} (hA : MeasurableSet A) {p : ℂ} {s : ℝ}
    (hs : 0 ≤ s)
    (h : (volume (A ∩ square p s)).toReal = (volume (Aᶜ ∩ square p s)).toReal) :
    ∃ q, square q (s / 2) ⊆ square p s ∧
      (volume (A ∩ square q (s / 2))).toReal = (volume (Aᶜ ∩ square q (s / 2))).toReal := by
  set t := s / 2 with ht
  have ht0 : 0 ≤ t := by positivity
  set c₁ := p
  set c₂ := p + (t : ℂ)
  set c₃ := p + (t : ℂ) * Complex.I
  set c₄ := p + (t : ℂ) + (t : ℂ) * Complex.I
  have hcorner : ∀ c ∈ ({c₁, c₂, c₃, c₄} : Set ℂ), c ∈ square p t := by
    simp only [mem_insert_iff, mem_singleton_iff]
    rintro c (rfl | rfl | rfl | rfl) <;>
      simp [c₂, c₃, c₄, square, ht0]
  have hcov : square p s ⊆ square c₁ t ∪ square c₂ t ∪ square c₃ t ∪ square c₄ t := by
    rintro z ⟨h1, h2, h3, h4⟩
    simp only [mem_union, square, mem_ofPred_eq, c₁, c₂, c₃, c₄, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    rcases le_total z.re (p.re + t) with hr | hr <;>
      rcases le_total z.im (p.im + t) with hi | hi
    · exact Or.inl (Or.inl (Or.inl ⟨h1, hr, h3, hi⟩))
    · exact Or.inl (Or.inr ⟨h1, hr, by linarith, by linarith⟩)
    · exact Or.inl (Or.inl (Or.inr ⟨hr, by linarith, h3, hi⟩))
    · exact Or.inr ⟨hr, by linarith, hi, by linarith⟩
  have hsub : ∀ K : Set ℂ, (volume (K ∩ square p s)).toReal ≤
      (volume (K ∩ square c₁ t)).toReal + (volume (K ∩ square c₂ t)).toReal +
        (volume (K ∩ square c₃ t)).toReal + (volume (K ∩ square c₄ t)).toReal := by
    intro K
    have hf := fun c => volume_inter_square_ne_top K c t
    have h12 := ENNReal.add_ne_top.2 ⟨hf c₁, hf c₂⟩
    have h123 := ENNReal.add_ne_top.2 ⟨h12, hf c₃⟩
    rw [← ENNReal.toReal_add (hf _) (hf _), ← ENNReal.toReal_add h12 (hf _),
      ← ENNReal.toReal_add h123 (hf _)]
    refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h123, hf c₄⟩) ?_
    calc volume (K ∩ square p s)
        ≤ volume ((K ∩ square c₁ t) ∪ (K ∩ square c₂ t) ∪ (K ∩ square c₃ t) ∪
            (K ∩ square c₄ t)) := by
          refine measure_mono fun z ⟨hzK, hz⟩ => ?_
          rcases hcov hz with ((h | h) | h) | h
          · exact Or.inl (Or.inl (Or.inl ⟨hzK, h⟩))
          · exact Or.inl (Or.inl (Or.inr ⟨hzK, h⟩))
          · exact Or.inl (Or.inr ⟨hzK, h⟩)
          · exact Or.inr ⟨hzK, h⟩
      _ ≤ _ := by
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
          exact measure_union_le _ _
  have hsumA := hsub A
  have hsumB := hsub Aᶜ
  have hbig := toReal_inter_add_compl hA p hs
  have hq := fun c => toReal_inter_add_compl hA c ht0
  have hts : s ^ 2 = 4 * t ^ 2 := by rw [ht]; ring

  have hex₁ : ∃ c ∈ ({c₁, c₂, c₃, c₄} : Set ℂ),
      (volume (Aᶜ ∩ square c t)).toReal ≤ (volume (A ∩ square c t)).toReal := by
    by_contra hno
    push Not at hno
    have e1 := hno c₁ (by simp)
    have e2 := hno c₂ (by simp)
    have e3 := hno c₃ (by simp)
    have e4 := hno c₄ (by simp)
    linarith [hq c₁, hq c₂, hq c₃, hq c₄]
  have hex₂ : ∃ c ∈ ({c₁, c₂, c₃, c₄} : Set ℂ),
      (volume (A ∩ square c t)).toReal ≤ (volume (Aᶜ ∩ square c t)).toReal := by
    by_contra hno
    push Not at hno
    have e1 := hno c₁ (by simp)
    have e2 := hno c₂ (by simp)
    have e3 := hno c₃ (by simp)
    have e4 := hno c₄ (by simp)
    linarith [hq c₁, hq c₂, hq c₃, hq c₄]
  obtain ⟨d₁, hd₁, hle₁⟩ := hex₁
  obtain ⟨d₂, hd₂, hle₂⟩ := hex₂
  obtain ⟨q, hqseg, hqbal⟩ := exists_balanced_mem_segment A t hle₁ hle₂
  have hqmem : q ∈ square p t :=
    (convex_square p t).segment_subset (hcorner d₁ hd₁) (hcorner d₂ hd₂) hqseg
  refine ⟨q, ?_, hqbal⟩
  obtain ⟨g1, g2, g3, g4⟩ := hqmem
  rintro z ⟨h1, h2, h3, h4⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem exists_not_densityZero {A : Set ℂ} (hA : MeasurableSet A) {a b : ℂ}
    (ha : DensityZero Aᶜ a) (hb : DensityZero A b) :
    ∃ z, ¬ DensityZero A z ∧ ¬ DensityZero Aᶜ z := by

  have hsmall : ∀ (K : Set ℂ) (x : ℂ) (δ : ℝ),
      (∀ ρ, 0 < ρ → ρ < δ → volume (K ∩ closedBall x ρ) ≤ ENNReal.ofReal (1 / 16 * ρ ^ 2)) →
      ∀ (q : ℂ) (t : ℝ), 0 < t → 2 * t < δ → x ∈ square q t →
        (volume (K ∩ square q t)).toReal ≤ t ^ 2 / 4 := by
    intro K x δ hK q t ht htδ hx
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    calc volume (K ∩ square q t) ≤ volume (K ∩ closedBall x (2 * t)) :=
          measure_mono (inter_subset_inter_right _ (square_subset_closedBall hx))
      _ ≤ ENNReal.ofReal (1 / 16 * (2 * t) ^ 2) := hK _ (by positivity) htδ
      _ = ENNReal.ofReal (t ^ 2 / 4) := by congr 1; ring

  obtain ⟨δa, hδa, ha'⟩ := ha (1 / 16) (by norm_num)
  obtain ⟨δb, hδb, hb'⟩ := hb (1 / 16) (by norm_num)
  set s := min δa δb / 4 with hsdef
  have hs : 0 < s := by positivity
  have h2sa : 2 * s < δa := by have := min_le_left δa δb; linarith
  have h2sb : 2 * s < δb := by have := min_le_right δa δb; linarith
  have hla := hsmall Aᶜ a δa ha' a s hs h2sa (mem_square_self a hs.le)
  have hlb := hsmall A b δb hb' b s hs h2sb (mem_square_self b hs.le)
  have hsa := toReal_inter_add_compl hA a hs.le
  have hsb := toReal_inter_add_compl hA b hs.le
  obtain ⟨p₀, -, hp₀⟩ := exists_balanced_mem_segment A s (q₁ := a) (q₂ := b)
    (by nlinarith) (by nlinarith)

  have step : ∀ (n : ℕ) (p : ℂ),
      (volume (A ∩ square p (s / 2 ^ n))).toReal = (volume (Aᶜ ∩ square p (s / 2 ^ n))).toReal →
      ∃ q, square q (s / 2 ^ (n + 1)) ⊆ square p (s / 2 ^ n) ∧
        (volume (A ∩ square q (s / 2 ^ (n + 1)))).toReal =
          (volume (Aᶜ ∩ square q (s / 2 ^ (n + 1)))).toReal := by
    intro n p hp
    have := exists_balanced_subsquare hA (by positivity) hp
    rwa [show s / 2 ^ n / 2 = s / 2 ^ (n + 1) by rw [pow_succ]; ring] at this
  choose! next hnext_sub hnext_bal using step
  let seq : ℕ → ℂ := fun n => Nat.rec p₀ (fun n q => next n q) n
  have hseq : ∀ n, (volume (A ∩ square (seq n) (s / 2 ^ n))).toReal =
      (volume (Aᶜ ∩ square (seq n) (s / 2 ^ n))).toReal := by
    intro n
    induction n with
    | zero => simpa [seq] using hp₀
    | succ n ih => exact hnext_bal n _ ih
  have hnest : ∀ n, square (seq (n + 1)) (s / 2 ^ (n + 1)) ⊆ square (seq n) (s / 2 ^ n) :=
    fun n => hnext_sub n _ (hseq n)
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => square (seq n) (s / 2 ^ n)) hnest
    (fun n => ⟨seq n, mem_square_self _ (by positivity)⟩) (isCompact_square _ _)
    (fun n => isClosed_square _ _)
  rw [mem_iInter] at hz

  have hnot : ∀ K : Set ℂ, (∀ n, (volume (K ∩ square (seq n) (s / 2 ^ n))).toReal =
      (s / 2 ^ n) ^ 2 / 2) → ¬ DensityZero K z := by
    intro K hK hz0
    obtain ⟨δ, hδ, hzδ⟩ := hz0 (1 / 16) (by norm_num)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < δ / (2 * s) by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    have hsn : s / 2 ^ n = s * (1 / 2) ^ n := by rw [one_div_pow]; ring
    have hn' : 2 * (s / 2 ^ n) < δ := by
      rw [hsn]
      rw [lt_div_iff₀ (by positivity)] at hn
      linarith
    have hpos : 0 < s / 2 ^ n := by positivity
    have := hsmall K z δ hzδ (seq n) (s / 2 ^ n) hpos hn' (hz n)
    rw [hK n] at this
    nlinarith
  refine ⟨z, hnot A fun n => ?_, hnot Aᶜ fun n => ?_⟩
  · have := toReal_inter_add_compl hA (seq n) (show 0 ≤ s / 2 ^ n by positivity)
    linarith [hseq n]
  · have := toReal_inter_add_compl hA (seq n) (show 0 ≤ s / 2 ^ n by positivity)
    linarith [hseq n]
end Erdos173

end
end

-- Erdos173.Measurable.CircleAlternation
section
section
noncomputable section

namespace Erdos173

open MeasureTheory Set Real OAI.EuclideanFiveColor

lemma preimage_add_ae_le_compl {R : Set Angles} {s : Angles}
    (h : angularMeasure (R ∩ (· + s) ⁻¹' R) = 0) :
    (· + s) ⁻¹' R ≤ᵐ[angularMeasure] Rᶜ := by
  apply (ae_le_set (s := (· + s) ⁻¹' R) (t := Rᶜ)).2
  rwa [sdiff_compl, inter_comm]

set_option maxHeartbeats 700000 in
theorem circle_alternation {R : Set Angles} (hR : MeasurableSet R) {γ : ℝ}
    (hγ : Irrational (γ / π))
    (h₁ : angularMeasure (R ∩ (· + ((π / 3 : ℝ) : Angles)) ⁻¹' R) = 0)
    (h₂ : angularMeasure (Rᶜ ∩ (· + ((π / 3 : ℝ) : Angles)) ⁻¹' Rᶜ) = 0)
    (h₃ : angularMeasure (R ∩ (· + (γ : Angles)) ⁻¹' R) = 0) : False := by
  set s : Angles := ((π / 3 : ℝ) : Angles) with hs
  set g : Angles := (γ : Angles) with hg
  have hmp : ∀ x : Angles, MeasurePreserving (· + x) angularMeasure angularMeasure :=
    fun x => measurePreserving_add_right angularMeasure x
  have hmeas : ∀ x : Angles, angularMeasure ((· + x) ⁻¹' R) = angularMeasure R :=
    fun x => (hmp x).measure_preimage hR.nullMeasurableSet
  have hmeas' : ∀ x : Angles, angularMeasure ((· + x) ⁻¹' Rᶜ) = angularMeasure Rᶜ :=
    fun x => (hmp x).measure_preimage hR.compl.nullMeasurableSet
  have hle₁ := preimage_add_ae_le_compl h₁
  have hle₂ : ((· + s) ⁻¹' Rᶜ : Set Angles) ≤ᵐ[angularMeasure] R := by
    apply (ae_le_set (s := (· + s) ⁻¹' Rᶜ) (t := R)).2
    rwa [Set.sdiff_eq, inter_comm]
  have hRc : angularMeasure R ≤ angularMeasure Rᶜ := (hmeas s).symm.le.trans (measure_mono_ae hle₁)
  have hcR : angularMeasure Rᶜ ≤ angularMeasure R := (hmeas' s).symm.le.trans (measure_mono_ae hle₂)
  have hnull : ∀ x : Angles, NullMeasurableSet ((· + x) ⁻¹' R) angularMeasure :=
    fun x => (hR.preimage (measurable_add_const x)).nullMeasurableSet
  have heq_s : (· + s) ⁻¹' R =ᵐ[angularMeasure] Rᶜ :=
    ae_eq_of_ae_subset_of_measure_ge hle₁ ((hmeas s).symm ▸ hcR) (hnull s) (measure_ne_top _ _)
  have heq_g : (· + g) ⁻¹' R =ᵐ[angularMeasure] Rᶜ :=
    ae_eq_of_ae_subset_of_measure_ge (preimage_add_ae_le_compl h₃) ((hmeas g).symm ▸ hcR)
      (hnull g) (measure_ne_top _ _)

  have hinv : (fun x => (g - s) + x) ⁻¹' R =ᵐ[angularMeasure] R := by
    have h := (hmp (-s)).quasiMeasurePreserving.preimage_ae_eq (heq_g.trans heq_s.symm)
    have e1 : (· + -s) ⁻¹' ((· + g) ⁻¹' R) = (fun x => (g - s) + x) ⁻¹' R := by
      ext t; simp only [mem_preimage]; congr! 1; abel
    have e2 : (· + -s) ⁻¹' ((· + s) ⁻¹' R) = R := by
      ext t; simp
    rwa [e1, e2] at h
  have hdense : DenseRange (fun n : ℤ => n • (g - s)) := by
    rw [hg, hs, ← AddCircle.coe_sub, AddCircle.denseRange_zsmul_coe_iff]
    have h' : Irrational (γ / π * ((1 / 2 : ℚ) : ℝ) - ((1 / 6 : ℚ) : ℝ)) :=
      (hγ.mul_ratCast (by norm_num)).sub_ratCast _
    convert h' using 1
    field_simp
    ring
  have herg := ergodic_add_left_of_denseRange_zsmul hdense angularMeasure
  have hsum : angularMeasure R + angularMeasure Rᶜ = 1 := by
    rw [measure_add_measure_compl hR, measure_univ]
  have hRR : angularMeasure Rᶜ = angularMeasure R := le_antisymm hcR hRc
  rw [hRR] at hsum
  rcases herg.ae_empty_or_univ_of_preimage_ae_le hR.nullMeasurableSet hinv.le with h0 | h1
  · rw [measure_congr h0, measure_empty] at hsum
    simp at hsum
  · rw [measure_congr h1, measure_univ] at hsum
    norm_num at hsum
end Erdos173

end
end

-- Erdos173.Measurable.Cyclotomic
section
section

noncomputable section

namespace Erdos173

open Real Polynomial

lemma pow_add_pow_eq_two_cos {m : ℕ} (hm : 0 < m) (j n : ℕ) :
    (Complex.exp (2 * π * Complex.I / m) ^ j) ^ n +
        (Complex.exp (2 * π * Complex.I / m) ^ j) ^ ((m - 1) * n) =
      ((2 * cos (2 * π * (j * n) / m) : ℝ) : ℂ) := by
  set ω := Complex.exp (2 * π * Complex.I / m) with hω
  have hprim : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m hm.ne'
  have hz : (ω ^ j) ^ n = Complex.exp (↑(2 * π * (j * n) / m) * Complex.I) := by
    rw [← pow_mul, hω, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hinv : (ω ^ j) ^ ((m - 1) * n) = ((ω ^ j) ^ n)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_add, ← add_one_mul, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm.ne'), ← pow_mul,
      show j * (m * n) = m * (j * n) by ring, pow_mul, hprim.pow_eq_one, one_pow]
  rw [hinv, hz, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos, neg_mul]

lemma two_cos_sub_two_cos_of_coprime {m a b : ℕ} (hm : 0 < m)
    (h : 2 * cos (2 * π * a / m) - 2 * cos (2 * π * b / m) = 1) {k : ℕ} (hk : k.Coprime m) :
    2 * cos (2 * π * (k * a) / m) - 2 * cos (2 * π * (k * b) / m) = 1 := by
  set ω := Complex.exp (2 * π * Complex.I / m) with hω
  have hprim : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m hm.ne'
  have hprimk : IsPrimitiveRoot (ω ^ k) m := hprim.pow_of_coprime k hk
  have hmin : minpoly ℚ (ω ^ k) = minpoly ℚ ω := by
    rw [← cyclotomic_eq_minpoly_rat hprim hm, ← cyclotomic_eq_minpoly_rat hprimk hm]
  set P : ℚ[X] := X ^ a + X ^ ((m - 1) * a) - X ^ b - X ^ ((m - 1) * b) - 1 with hP
  have hev : ∀ j : ℕ, aeval (ω ^ j) P =
      ((2 * cos (2 * π * (j * a) / m) - 2 * cos (2 * π * (j * b) / m) - 1 : ℝ) : ℂ) := by
    intro j
    have ha := pow_add_pow_eq_two_cos hm j a
    have hb := pow_add_pow_eq_two_cos hm j b
    simp only [hP, map_sub, map_add, map_pow, aeval_X, map_one]
    push_cast at ha hb ⊢
    rw [← ha, ← hb]
    ring
  have h1 : aeval ω P = 0 := by
    have := hev 1
    rw [pow_one] at this
    rw [this]
    simp only [Nat.cast_one, one_mul, h, sub_self, Complex.ofReal_zero]
  obtain ⟨Q, hQ⟩ := minpoly.dvd ℚ ω h1
  have hk0 : aeval (ω ^ k) P = 0 := by
    rw [hQ, map_mul, ← hmin, minpoly.aeval, zero_mul]
  rw [hev k] at hk0
  have := Complex.ofReal_eq_zero.1 hk0
  linarith

lemma exists_coprime_middle_third {m : ℕ} (hm : 11 ≤ m) :
    ∃ j : ℕ, j.Coprime m ∧ m < 3 * j ∧ 3 * j < 2 * m := by
  obtain ⟨l, rfl | rfl | rfl | rfl⟩ : ∃ l, m = 4 * l ∨ m = 4 * l + 1 ∨ m = 4 * l + 2 ∨
      m = 4 * l + 3 := ⟨m / 4, by omega⟩
  · refine ⟨2 * l + 1, ?_, by omega, by omega⟩
    rw [show 4 * l = 2 * (2 * l) by ring]
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
    · exact Nat.coprime_self_add_left.2 (Nat.coprime_one_left _)
  · refine ⟨2 * l, ?_, by omega, by omega⟩
    rw [show 4 * l + 1 = 2 * (2 * l) + 1 by ring, Nat.coprime_mul_right_add_right]
    exact Nat.coprime_one_right _
  · refine ⟨2 * l + 3, ?_, by omega, by omega⟩
    rw [show 4 * l + 2 = 2 * (2 * l + 1) by ring]
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
    · rw [show 2 * l + 3 = (2 * l + 1) + 2 by ring, Nat.coprime_self_add_left,
        Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
  · refine ⟨2 * l + 1, ?_, by omega, by omega⟩
    rw [show 4 * l + 3 = 2 * (2 * l + 1) + 1 by ring, Nat.coprime_mul_right_add_right]
    exact Nat.coprime_one_right _

lemma cos_lt_neg_half {θ : ℝ} (h₁ : 2 * π / 3 < θ) (h₂ : θ < 4 * π / 3) :
    cos θ < -1 / 2 := by
  have hc : cos θ = -cos (θ - π) := by rw [cos_sub_pi]; ring
  rw [hc]
  have : 1 / 2 < cos (θ - π) := by
    rw [← cos_pi_div_three]
    rcases le_total 0 (θ - π) with h | h
    · exact cos_lt_cos_of_nonneg_of_le_pi h (by linarith [pi_pos]) (by linarith)
    · rw [← cos_neg (θ - π)]
      exact cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos]) (by linarith)
  linarith

lemma cos_eq_of_dvd_sub {m : ℕ} (hm : 0 < m) {x y : ℤ} (h : (m : ℤ) ∣ y - x) :
    cos (2 * π * x / m) = cos (2 * π * y / m) := by
  obtain ⟨t, ht⟩ := h
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hy : (y : ℝ) = x + m * t := by
    have : ((y - x : ℤ) : ℝ) = ((m * t : ℤ) : ℝ) := by rw [ht]
    push_cast at this
    linarith
  rw [hy, show 2 * π * (x + m * t) / m = 2 * π * x / m + t * (2 * π) by field_simp,
    cos_add_int_mul_two_pi]

lemma cos_two_pi_div_le {m a : ℕ} (hm : 0 < m) (ha : ¬ m ∣ a) :
    cos (2 * π * a / m) ≤ cos (2 * π / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set r := a % m with hr
  set q := a / m with hq
  have hr1 : 1 ≤ r := Nat.pos_of_ne_zero fun h => ha (Nat.dvd_of_mod_eq_zero h)
  have hr2 : r + 1 ≤ m := Nat.mod_lt _ hm
  have hadd : (a : ℝ) = r + m * q := by exact_mod_cast (Nat.mod_add_div a m).symm
  rw [hadd, show 2 * π * (r + m * q) / m = 2 * π * r / m + q * (2 * π) by field_simp,
    cos_add_nat_mul_two_pi]
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hr2' : (r : ℝ) + 1 ≤ m := by exact_mod_cast hr2
  have h1 : 2 * π / m ≤ 2 * π * r / m := by
    apply div_le_div_of_nonneg_right _ hmR.le
    nlinarith [pi_pos]
  have h2 : 2 * π * r / m ≤ 2 * π - 2 * π / m := by
    rw [div_le_iff₀ hmR, sub_mul, div_mul_cancel₀ _ hmR.ne']
    nlinarith [pi_pos]
  rcases le_total (2 * π * r / m) π with h | h
  · exact cos_le_cos_of_nonneg_of_le_pi (by positivity) h h1
  · rw [← cos_two_pi_sub (2 * π * r / m)]
    exact cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)

lemma exists_coprime_cos_lt {m a : ℕ} (hm : 0 < m)
    (h₁ : (1 + √5) / 4 < cos (2 * π * a / m)) (h₂ : cos (2 * π * a / m) ≠ 1) :
    ∃ k : ℕ, k.Coprime m ∧ cos (2 * π * (k * a) / m) < -1 / 2 := by
  obtain ⟨a₁, m₁, hcop, ha, hmm⟩ := Nat.exists_coprime a m
  set g := a.gcd m with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right a hm
  have hm₁ : 0 < m₁ := by
    rcases Nat.eq_zero_or_pos m₁ with h | h
    · rw [h, zero_mul] at hmm; omega
    · exact h
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hm₁R : (0 : ℝ) < m₁ := by exact_mod_cast hm₁

  have hangle : ∀ k : ℕ, 2 * π * (k * a) / m = 2 * π * (k * a₁) / m₁ := by
    intro k
    rw [ha, hmm]
    push_cast
    field_simp
  have h1' := hangle 1
  simp only [Nat.cast_one, one_mul] at h1'
  rw [h1'] at h₁ h₂

  have h11 : 11 ≤ m₁ := by
    by_contra hlt
    push Not at hlt
    by_cases hdvd : m₁ ∣ a₁
    · have h1 : m₁ = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm hdvd
      apply h₂
      rw [h1, Nat.cast_one, div_one]
      obtain ⟨t, rfl⟩ := hdvd
      rw [h1, one_mul, mul_comm]
      exact_mod_cast cos_nat_mul_two_pi t
    · have hm₁2 : 2 ≤ m₁ := by
        rcases Nat.lt_or_ge m₁ 2 with h | h
        · exact absurd (by interval_cases m₁; exact one_dvd a₁) hdvd
        · exact h
      have hle := cos_two_pi_div_le hm₁ hdvd
      have hm₁le : (m₁ : ℝ) ≤ 10 := by exact_mod_cast (Nat.lt_succ_iff.1 hlt)
      have hm₁2' : (2 : ℝ) ≤ m₁ := by exact_mod_cast hm₁2
      have : cos (2 * π / m₁) ≤ cos (π / 5) := by
        apply cos_le_cos_of_nonneg_of_le_pi (by positivity)
        · rw [div_le_iff₀ hm₁R]; nlinarith [pi_pos]
        · rw [div_le_div_iff₀ (by norm_num) hm₁R]; nlinarith [pi_pos]
      rw [cos_pi_div_five] at this
      linarith
  obtain ⟨j, hj, hj₁, hj₂⟩ := exists_coprime_middle_third h11

  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero m₁ := ⟨hm₁.ne'⟩
  have hdvd : m₁ ∣ m := ⟨g, by rw [hmm]⟩
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hdvd
    (ZMod.unitOfCoprime j hj * (ZMod.unitOfCoprime a₁ hcop)⁻¹)
  refine ⟨(v : ZMod m).val, ZMod.val_coe_unit_coprime v, ?_⟩
  have hcong : ((((v : ZMod m).val * a₁ : ℕ)) : ZMod m₁) = (j : ZMod m₁) := by
    have hv' : ((ZMod.unitsMap hdvd v : (ZMod m₁)ˣ) : ZMod m₁) = ZMod.cast (v : ZMod m) := rfl
    rw [Nat.cast_mul, ZMod.natCast_val, ← hv', hv, ← ZMod.coe_unitOfCoprime a₁ hcop,
      ← Units.val_mul, inv_mul_cancel_right, ZMod.coe_unitOfCoprime]
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).1 hcong
  rw [hangle]
  have hcos := cos_eq_of_dvd_sub hm₁ (x := ((v : ZMod m).val * a₁ : ℕ)) (y := (j : ℕ))
    ((Nat.modEq_iff_dvd).1 hmod)
  push_cast at hcos
  rw [hcos]
  have hj₁' : (m₁ : ℝ) < 3 * j := by exact_mod_cast hj₁
  have hj₂' : 3 * (j : ℝ) < 2 * m₁ := by exact_mod_cast hj₂
  apply cos_lt_neg_half
  · rw [lt_div_iff₀ hm₁R]; nlinarith [pi_pos]
  · rw [div_lt_div_iff₀ hm₁R (by norm_num)]; nlinarith [pi_pos]

lemma exists_nat_cos_eq_int {m : ℕ} (hm : 0 < m) (N : ℤ) :
    ∃ a : ℕ, cos (2 * π * N / m) = cos (2 * π * a / m) := by
  have hm' : (0 : ℤ) ≤ N % m := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
  refine ⟨(N % m).toNat, ?_⟩
  have hcast : (((N % m).toNat : ℕ) : ℝ) = ((N % m : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hm']
  rw [hcast]
  exact cos_eq_of_dvd_sub hm (Int.mod_modEq N m).dvd |>.symm

lemma exists_nat_cos_eq (s t : ℚ) :
    ∃ m : ℕ, 0 < m ∧ ∃ a b : ℕ, cos (2 * π * s) = cos (2 * π * a / m) ∧
      cos (2 * π * t) = cos (2 * π * b / m) := by
  have hm : 0 < s.den * t.den := Nat.mul_pos s.den_pos t.den_pos
  refine ⟨s.den * t.den, hm, ?_⟩
  have hsd : (s.den : ℝ) ≠ 0 := by exact_mod_cast s.den_pos.ne'
  have htd : (t.den : ℝ) ≠ 0 := by exact_mod_cast t.den_pos.ne'
  obtain ⟨a, ha⟩ := exists_nat_cos_eq_int hm (s.num * t.den)
  obtain ⟨b, hb⟩ := exists_nat_cos_eq_int hm (t.num * s.den)
  refine ⟨a, b, ?_, ?_⟩
  · rw [← ha, Rat.cast_def]
    congr 1
    push_cast
    field_simp
  · rw [← hb, Rat.cast_def]
    congr 1
    push_cast
    field_simp

theorem irrational_apex_angle {x : ℝ} (hx₁ : 2 / 3 < x) (hx₂ : x < 3 / 2) (hx : x ≠ 1) :
    Irrational (2 * arcsin (x / 2) / π) ∨ Irrational (2 * arcsin (1 / (2 * x)) / π) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  unfold Irrational at h1 h2
  rw [not_not] at h1 h2
  obtain ⟨q₁, hq₁⟩ := h1
  obtain ⟨q₂, hq₂⟩ := h2
  have hx0 : 0 < x := by linarith
  set A := arcsin (x / 2) with hA
  set B := arcsin (1 / (2 * x)) with hB
  set y := 1 / (2 * x) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by positivity)]; linarith
  have hsA : sin A = x / 2 := sin_arcsin (by linarith) (by linarith)
  have hsB : sin B = y := sin_arcsin (by linarith) hy1.le
  have hcA : cos A = √(1 - (x / 2) ^ 2) := cos_arcsin _
  have hcB : cos B = √(1 - y ^ 2) := cos_arcsin _
  have hA' : A = 2 * π * ((q₁ / 4 : ℚ) : ℝ) := by
    push_cast; rw [hq₁]; field_simp; ring
  have hB' : B = 2 * π * ((q₂ / 4 : ℚ) : ℝ) := by
    push_cast; rw [hq₂]; field_simp; ring
  have hu : A - B = 2 * π * (((q₁ - q₂) / 4 : ℚ) : ℝ) := by
    rw [hA', hB']; push_cast; ring
  have hv : A + B = 2 * π * (((q₁ + q₂) / 4 : ℚ) : ℝ) := by
    rw [hA', hB']; push_cast; ring
  obtain ⟨m, hm, a, b, ha, hb⟩ := exists_nat_cos_eq ((q₁ - q₂) / 4) ((q₁ + q₂) / 4)
  have hxy : x * y = 1 / 2 := by rw [hy]; field_simp
  have hkey : 2 * cos (2 * π * a / m) - 2 * cos (2 * π * b / m) = 1 := by
    rw [← ha, ← hb, ← hu, ← hv, cos_sub, cos_add, hsA, hsB]
    linear_combination 2 * hxy
  have hbig : (1 + √5) / 4 < cos (2 * π * a / m) := by
    rw [← ha, ← hu, cos_sub, hsA, hsB, hcA, hcB]
    have hP : 0 ≤ √(1 - (x / 2) ^ 2) * √(1 - y ^ 2) := by positivity
    have hsq : (√(1 - (x / 2) ^ 2) * √(1 - y ^ 2)) ^ 2 = (1 - (x / 2) ^ 2) * (1 - y ^ 2) := by
      rw [mul_pow, sq_sqrt (by nlinarith), sq_sqrt (by nlinarith)]
    have h5 : (√5 / 4) ^ 2 < (√(1 - (x / 2) ^ 2) * √(1 - y ^ 2)) ^ 2 := by
      rw [hsq, div_pow, sq_sqrt (by norm_num)]
      have hy₁ : 1 / 3 < y := by rw [hy, lt_div_iff₀ (by positivity)]; linarith
      have hy₂ : y < 3 / 4 := by rw [hy, div_lt_iff₀ (by positivity)]; linarith
      nlinarith [mul_pos (sub_pos.2 hx₁) (sub_pos.2 hx₂), mul_pos (sub_pos.2 hy₁) (sub_pos.2 hy₂)]
    have := lt_of_pow_lt_pow_left₀ 2 hP h5
    have hxy' : x / 2 * y = 1 / 4 := by linear_combination hxy / 2
    linarith
  have hne : cos (2 * π * a / m) ≠ 1 := by
    rw [← ha, ← hu]
    intro h1
    have hAb := neg_pi_div_two_le_arcsin (x / 2)
    have hAt := arcsin_le_pi_div_two (x / 2)
    have hBb := neg_pi_div_two_le_arcsin y
    have hBt := arcsin_le_pi_div_two y
    have h0 := (cos_eq_one_iff_of_lt_of_lt (by linarith [pi_pos]) (by linarith [pi_pos])).1 h1
    have hAB : A = B := by linarith
    have : x / 2 = y := by rw [← hsA, ← hsB, hAB]
    have hx2 : x * x = 1 := by
      have h' : x / 2 * (2 * x) = y * (2 * x) := by rw [this]
      rw [hy, div_mul_cancel₀ _ (by positivity)] at h'
      linarith
    have hfac : (x - 1) * (x + 1) = 0 := by linear_combination hx2
    rcases mul_eq_zero.1 hfac with h | h
    · exact hx (by linarith)
    · linarith
  obtain ⟨k, hk, hlt⟩ := exists_coprime_cos_lt hm hbig hne
  have := two_cos_sub_two_cos_of_coprime hm hkey hk
  have := neg_one_le_cos (2 * π * (k * b) / m)
  linarith
end Erdos173

end
end

-- Erdos173.Measurable.SelfSupport
section
section

noncomputable section

namespace Erdos173

open MeasureTheory Set Real OAI.EuclideanFiveColor

lemma angularMeasure_eq_zero_of_volume_preimage {Y : Set Angles} (hY : MeasurableSet Y)
    (h : volume ((QuotientAddGroup.mk : ℝ → Angles) ⁻¹' Y ∩ Ioc (-π) π) = 0) :
    angularMeasure Y = 0 := by
  have hmp := AddCircle.measurePreserving_mk (2 * π) (-π)
  have hvol : (volume : Measure Angles) Y = 0 := by
    rw [← hmp.measure_preimage hY.nullMeasurableSet,
      Measure.restrict_apply (hY.preimage hmp.measurable),
      show -π + 2 * π = π by ring]
    exact h
  simp only [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul,
    mul_eq_zero, ENNReal.ofReal_eq_zero] at hvol
  exact hvol.resolve_left (not_le.2 (by positivity))

lemma angularMeasure_mul_mem (N : Set ℂ) (w : ℂ) :
    angularMeasure {t | direction t * w ∈ N} =
      angularMeasure {t | (‖w‖ : ℂ) * direction t ∈ N} := by
  have hw : w = (‖w‖ : ℂ) * direction (Complex.arg w : Angles) := by
    rw [direction_real, Circle.coe_exp, Complex.norm_mul_exp_arg_mul_I]
  have : {t | direction t * w ∈ N} =
      (· + (Complex.arg w : Angles)) ⁻¹' {t | (‖w‖ : ℂ) * direction t ∈ N} := by
    ext t
    simp only [mem_ofPred_eq, mem_preimage, direction_add]
    conv_lhs => rw [hw]
    ring_nf
  rw [this, measure_preimage_add_right]

lemma norm_one_add_exp {α : ℝ} (h₁ : -π ≤ α) (h₂ : α ≤ π) :
    ‖1 + Complex.exp (α * Complex.I)‖ = 2 * cos (α / 2) := by
  have hc : 0 ≤ cos (α / 2) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  rw [Complex.norm_def, Complex.normSq_apply]
  have hre : (1 + Complex.exp (α * Complex.I)).re = 1 + cos α := by
    rw [Complex.add_re, Complex.exp_ofReal_mul_I_re, Complex.one_re]
  have him : (1 + Complex.exp (α * Complex.I)).im = sin α := by
    rw [Complex.add_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, zero_add]
  have hα : α = 2 * (α / 2) := by ring
  rw [hre, him, hα, cos_two_mul, sin_two_mul, show 2 * (α / 2) / 2 = α / 2 by ring]
  rw [show (1 + (2 * cos (α / 2) ^ 2 - 1)) * (1 + (2 * cos (α / 2) ^ 2 - 1)) +
      2 * sin (α / 2) * cos (α / 2) * (2 * sin (α / 2) * cos (α / 2)) =
        (2 * cos (α / 2)) ^ 2 by nlinarith [sin_sq_add_cos_sq (α / 2)]]
  exact sqrt_sq (by positivity)

lemma angularMeasure_norm_one_add_mem {Z : Set ℝ} (hZ : MeasurableSet Z)
    (h0 : volume Z = 0) : angularMeasure {u | ‖1 + direction u‖ ∈ Z} = 0 := by
  have hmeas : MeasurableSet {u : Angles | ‖1 + direction u‖ ∈ Z} :=
    hZ.preimage (continuous_const.add direction_continuous).norm.measurable
  refine angularMeasure_eq_zero_of_volume_preimage hmeas ?_
  set Z₀ := Z ∩ Ioo (-2) 2 with hZ₀
  set g : ℝ → ℝ := fun ρ => 2 * arccos (ρ / 2) with hg
  have hdiff : DifferentiableOn ℝ g Z₀ := by
    intro ρ hρ
    have hρ' : ρ / 2 ≠ -1 ∧ ρ / 2 ≠ 1 := ⟨by linarith [hρ.2.1], by linarith [hρ.2.2]⟩
    have h1 : DifferentiableAt ℝ arccos (ρ / 2) := Real.differentiableAt_arccos.2 hρ'
    have h2 : DifferentiableAt ℝ (fun ρ : ℝ => ρ / 2) ρ := differentiableAt_id.div_const 2
    exact ((h1.comp ρ h2).const_mul 2).differentiableWithinAt
  have hZ₀0 : volume Z₀ = 0 := measure_mono_null inter_subset_left h0
  have h₁ : volume (g '' Z₀) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hZ₀0
  have h₂ : volume ((fun ρ => -g ρ) '' Z₀) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff.neg hZ₀0
  refine measure_mono_null (t := g '' Z₀ ∪ (fun ρ => -g ρ) '' Z₀ ∪ {0}) ?_
    (measure_union_null (measure_union_null h₁ h₂) (measure_singleton 0))
  rintro α ⟨hαZ, hα₁, hα₂⟩
  simp only [mem_preimage, mem_ofPred_eq, direction_real, Circle.coe_exp] at hαZ
  rw [norm_one_add_exp hα₁.le hα₂] at hαZ
  rcases lt_trichotomy α 0 with hneg | rfl | hpos
  · have hc : cos (α / 2) = cos (-α / 2) := by rw [← cos_neg]; ring_nf
    have hcos1 : cos (-α / 2) < 1 := by
      rw [← cos_zero]
      exact cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) (by linarith)
    have hcos0 : 0 ≤ cos (-α / 2) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    refine Or.inl (Or.inr ⟨2 * cos (α / 2), ⟨hαZ, by rw [hc]; linarith, by rw [hc]; linarith⟩, ?_⟩)
    simp only [hg]
    rw [show 2 * cos (α / 2) / 2 = cos (-α / 2) by rw [hc]; ring,
      arccos_cos (by linarith) (by linarith)]
    ring
  · exact Or.inr rfl
  · have hcos1 : cos (α / 2) < 1 := by
      rw [← cos_zero]
      exact cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) (by linarith)
    have hcos0 : 0 ≤ cos (α / 2) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    refine Or.inl (Or.inl ⟨2 * cos (α / 2), ⟨hαZ, by linarith, by linarith⟩, ?_⟩)
    simp only [hg]
    rw [show 2 * cos (α / 2) / 2 = cos (α / 2) by ring, arccos_cos (by linarith) (by linarith)]
    ring

lemma ae_angularMeasure_mul_mem {N : Set ℂ} (hN : MeasurableSet N) (h0 : volume N = 0) :
    ∀ᵐ ρ : ℝ, 0 < ρ → angularMeasure {t | (ρ : ℂ) * direction t ∈ N} = 0 := by
  set F : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) with hF
  have hFm : Measurable F := by fun_prop
  have hint := Complex.lintegral_comp_polarCoord_symm (N.indicator 1)
  rw [lintegral_indicator_one hN, h0] at hint
  simp_rw [Complex.polarCoord_symm_apply] at hint
  have hfm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 • N.indicator (1 : ℂ → ENNReal) (F p) := by
    have h1 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 :=
      ENNReal.measurable_ofReal.comp measurable_fst
    have h2 : Measurable fun p : ℝ × ℝ => N.indicator (1 : ℂ → ENNReal) (F p) :=
      (measurable_one.indicator hN).comp hFm
    exact h1.smul h2
  rw [lintegral_eq_zero_iff' hfm.aemeasurable, Filter.EventuallyEq,
    ae_restrict_iff' (by rw [polarCoord_target]; exact measurableSet_Ioi.prod measurableSet_Ioo)]
    at hint
  set W : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.2 ∈ Ioo (-π) π ∧ F p ∈ N} with hW
  have hWm : MeasurableSet W :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_Ioo.preimage measurable_snd).inter (hN.preimage hFm))
  have hW0 : (volume : Measure (ℝ × ℝ)) W = 0 := by
    refine measure_mono_null (fun p hp => ?_) (ae_iff.1 hint)
    obtain ⟨hp1, hp2, hp3⟩ := hp
    simp only [mem_ofPred_eq, polarCoord_target, Pi.zero_apply, Classical.not_imp]
    refine ⟨⟨hp1, hp2⟩, ?_⟩
    simp only [Set.indicator_of_mem hp3, Pi.one_apply, smul_eq_mul, mul_one]
    exact (ENNReal.ofReal_pos.2 hp1).ne'
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hWm] at hW0
  filter_upwards [hW0] with ρ hρ hρpos
  have hY : MeasurableSet {t : Angles | (ρ : ℂ) * direction t ∈ N} :=
    hN.preimage (continuous_const.mul direction_continuous).measurable
  refine angularMeasure_eq_zero_of_volume_preimage hY ?_
  refine measure_mono_null (t := Prod.mk ρ ⁻¹' W ∪ {π}) ?_
    (measure_union_null hρ (measure_singleton π))
  rintro α ⟨hα, hα₁, hα₂⟩
  rcases hα₂.lt_or_eq with hlt | rfl
  · refine Or.inl ⟨hρpos, ⟨hα₁, hlt⟩, ?_⟩
    simp only [mem_preimage, mem_ofPred_eq, direction_real, Circle.coe_exp] at hα
    simp only [hF]
    convert hα using 2
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  · exact Or.inr rfl

lemma angularMeasure_prod_add_mem {N : Set ℂ} (hN : MeasurableSet N) (h0 : volume N = 0) :
    (angularMeasure.prod angularMeasure)
      {q : Angles × Angles | direction q.1 + direction q.2 ∈ N} = 0 := by
  have hX : MeasurableSet {q : Angles × Angles | direction q.1 + direction q.2 ∈ N} :=
    hN.preimage ((direction_continuous.comp continuous_fst).add
      (direction_continuous.comp continuous_snd)).measurable
  rw [← (measurePreserving_prod_add angularMeasure angularMeasure).measure_preimage
    hX.nullMeasurableSet]
  have hY : MeasurableSet ((fun z : Angles × Angles => (z.1, z.1 + z.2)) ⁻¹'
      {q : Angles × Angles | direction q.1 + direction q.2 ∈ N}) :=
    hX.preimage (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  rw [Measure.prod_apply_symm hY]
  refine (lintegral_congr_ae ?_).trans lintegral_zero

  obtain ⟨Z, hZsub, hZm, hZ0⟩ := exists_measurable_superset_of_null
    (ae_iff.1 (ae_angularMeasure_mul_mem hN h0))
  have hbad := angularMeasure_norm_one_add_mem (hZm.union (measurableSet_singleton 0))
    (measure_union_null hZ0 (measure_singleton 0))
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun u hu => ?_) hbad
  simp only [mem_ofPred_eq] at hu
  have hsec : (fun t => (t, u)) ⁻¹' ((fun z : Angles × Angles => (z.1, z.1 + z.2)) ⁻¹'
      {q : Angles × Angles | direction q.1 + direction q.2 ∈ N}) =
        {t | direction t * (1 + direction u) ∈ N} := by
    ext t
    simp only [mem_preimage, mem_ofPred_eq, direction_add]
    ring_nf
  rw [hsec, angularMeasure_mul_mem] at hu
  simp only [mem_ofPred_eq, mem_union, mem_singleton_iff]
  by_contra hno
  push Not at hno
  apply hu
  have hpos : 0 < ‖1 + direction u‖ := (norm_nonneg _).lt_of_ne (Ne.symm hno.2)
  by_contra hne
  exact hno.1 (hZsub (by simp only [mem_ofPred_eq, Classical.not_imp]; exact ⟨hpos, hne⟩))

theorem eq_empty_of_selfSupporting {S : Set ℂ} (hS : MeasurableSet S) (h0 : volume S = 0)
    {r : ℝ} (hr : 0 < r) (h : ∀ p ∈ S, angularMeasure {t | p + r * direction t ∈ S} ≠ 0) :
    S = ∅ := by
  by_contra hne
  obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.2 hne
  have hcont : Continuous fun t : Angles => p + r * direction t :=
    continuous_const.add (continuous_const.mul direction_continuous)
  set E : Set (Angles × Angles) :=
    {q | p + r * direction q.1 ∈ S ∧ p + r * direction q.1 + r * direction q.2 ∈ S} with hE
  have hEm : MeasurableSet E :=
    (hS.preimage (hcont.comp continuous_fst).measurable).inter
      (hS.preimage ((hcont.comp continuous_fst).add
        (continuous_const.mul (direction_continuous.comp continuous_snd))).measurable)

  have hpos : (angularMeasure.prod angularMeasure) E ≠ 0 := by
    rw [Measure.prod_apply hEm]
    intro hzero
    rw [lintegral_eq_zero_iff (measurable_measure_prodMk_left hEm), Filter.EventuallyEq,
      ae_iff] at hzero
    refine h p hp (measure_mono_null (fun t ht => ?_) hzero)
    simp only [mem_ofPred_eq, Pi.zero_apply]
    have : Prod.mk t ⁻¹' E = {u | (p + r * direction t) + r * direction u ∈ S} := by
      ext u
      simp only [hE, mem_preimage, mem_ofPred_eq, and_iff_right_iff_imp]
      exact fun _ => ht
    rw [this]
    exact h _ ht

  set N : Set ℂ := (fun w => p + (r : ℂ) * w) ⁻¹' S with hN
  have hNm : MeasurableSet N :=
    hS.preimage (continuous_const.add (continuous_const.mul continuous_id)).measurable
  have hN0 : volume N = 0 := by
    have : N = (fun w : ℂ => r • w) ⁻¹' ((fun w => p + w) ⁻¹' S) := by
      ext w
      simp [hN, Complex.real_smul]
    rw [this, Measure.addHaar_preimage_smul volume hr.ne', measure_preimage_add, h0, mul_zero]
  refine hpos (measure_mono_null (fun q hq => ?_) (angularMeasure_prod_add_mem hNm hN0))
  simp only [hN, mem_ofPred_eq, mem_preimage]
  rw [mul_add, ← add_assoc]
  exact hq.2
end Erdos173

end
end

-- Erdos173.Reduction.EightPoint
section
section

noncomputable section

namespace Erdos173

open MeasureTheory OAI.EuclideanFiveColor

namespace EightPoint

lemma ae_motion {P : ℂ → ℂ → Prop} (X w : ℂ) (hw : ‖w‖ = 1)
    (h : ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure, P q.1 (direction q.2)) :
    ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure,
      P (q.1 + direction q.2 * X) (direction q.2 * w) := by
  obtain ⟨t, ht⟩ := Circle.exp_surjective (⟨w, mem_sphere_zero_iff_norm.2 hw⟩ : Circle)
  set φ : Angles := (t : Angles)
  have hφ : direction φ = w := by simp [φ, ht]
  have hS : MeasurePreserving (fun q : Angles × ℂ => (q.1 + φ, q.2 + direction q.1 * X))
      (angularMeasure.prod (volume : Measure ℂ)) (angularMeasure.prod volume) :=
    (measurePreserving_add_right angularMeasure φ).skew_product
      (g := fun θ p => p + direction θ * X)
      (by
        have := direction_continuous
        exact Continuous.measurable (by fun_prop))
      (Filter.Eventually.of_forall fun θ => map_add_right_eq_self volume _)
  have hT : MeasurePreserving
      (fun q : ℂ × Angles => (q.1 + direction q.2 * X, q.2 + φ))
      ((volume : Measure ℂ).prod angularMeasure) ((volume : Measure ℂ).prod angularMeasure) :=
    Measure.measurePreserving_swap.comp (hS.comp Measure.measurePreserving_swap)
  filter_upwards [hT.quasiMeasurePreserving.tendsto_ae.eventually h] with q hq
  simpa [direction, AddCircle.toCircle_add, ← hφ] using hq

lemma monoCopy_iff (c : ℂ → Fin 2) (a b p u t m x y : ℂ) (hx : t + m * a = x)
    (hy : t + m * b = y) :
    MonoCopy c a b (p + u * t) (u * m) ↔
      c (p + u * x) = c (p + u * t) ∧ c (p + u * y) = c (p + u * t) := by
  subst hx hy
  have e₁ : p + u * t + u * m * a = p + u * (t + m * a) := by ring
  have e₂ : p + u * t + u * m * b = p + u * (t + m * b) := by ring
  simp only [MonoCopy, e₁, e₂]

lemma forcing_i : ∀ A B C D B' A' C' D' : Fin 2, B = A → C = A →
    ¬ (B = A ∧ D = A) → ¬ (C = A ∧ B' = A) → ¬ (C = B ∧ D' = B) →
    ¬ (B' = A' ∧ D' = A') → ¬ (C' = A' ∧ B = A') → ¬ (C' = B' ∧ D = B') → False := by
  intro A B C D B' A' C' D'
  omega

lemma forcing_ii : ∀ A B C D B' A' C' D' : Fin 2, B = A → D = A →
    ¬ (D = A ∧ B' = A) → ¬ (B = A ∧ C = A) → ¬ (D = B ∧ C' = B) →
    ¬ (B' = A' ∧ C' = A') → ¬ (D' = A' ∧ B = A') → ¬ (D' = B' ∧ C = B') → False := by
  intro A B C D B' A' C' D'
  omega

end EightPoint

open EightPoint

theorem not_avoids_of_not_avoidsEq (c : ℂ → Fin 2) {a : ℝ} {z : ℂ}
    (h : ¬ AvoidsEq c a) : ¬ Avoids c a z := by
  intro hav
  simp only [AvoidsEq, Avoids, not_forall, not_not] at h
  obtain ⟨p, u, hu, hABC⟩ := h
  have key : ∀ t m x y : ℂ, ‖m‖ = 1 → t + m * a = x → t + m * z = y →
      ¬ (c (p + u * x) = c (p + u * t) ∧ c (p + u * y) = c (p + u * t)) := by
    intro t m x y hm hx hy
    rw [← monoCopy_iff c a z p u t m x y hx hy]
    exact hav _ _ (by rw [norm_mul, hu, hm, one_mul])

  have h₁ := key 0 1 a z (by simp) (by ring) (by ring)
  have h₂ := key 0 ζ (a * ζ) (ζ * z) norm_ζ (by ring) (by ring)
  have h₃ := key a (ζ - 1) (a * ζ) (a - (1 - ζ) * z) norm_ζ_sub_one (by ring) (by ring)
  have h₄ := key (a + ζ * z) (-1) (ζ * z) (a - (1 - ζ) * z) (by simp) (by ring) (by ring)
  have h₅ := key (a + ζ * z) (-ζ) (a * (1 - ζ) + ζ * z) a (by simp [norm_ζ]) (by ring)
    (by ring)
  have h₆ := key (ζ * z) (1 - ζ) (a * (1 - ζ) + ζ * z) z norm_one_sub_ζ (by ring) (by ring)
  simp only [mul_zero, add_zero] at h₁ h₂
  exact forcing_i _ _ _ _ _ _ _ _ hABC.1 hABC.2 h₁ h₂ h₃ h₄ h₅ h₆

theorem weaklyAvoids_of_weaklyAvoidsEq (c : ℂ → Fin 2) {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz0 : z ≠ 0) (hza : z ≠ a) (h₁ : WeaklyAvoidsEq c a) (h₂ : WeaklyAvoidsEq c ‖z‖)
    (h₃ : WeaklyAvoidsEq c ‖z - a‖) : WeaklyAvoids c a z := by
  have key : ∀ {s : ℝ}, 0 < s → WeaklyAvoidsEq c s → ∀ X Y Z : ℂ, ‖Y - X‖ = s →
      Z = X + ζ * (Y - X) → ∀ᵐ q ∂(volume : Measure ℂ).prod angularMeasure,
        ¬ (c (q.1 + direction q.2 * Y) = c (q.1 + direction q.2 * X) ∧
          c (q.1 + direction q.2 * Z) = c (q.1 + direction q.2 * X)) := by
    intro s hs h X Y Z hY hZ
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hw : ‖(Y - X) / s‖ = 1 := by
      rw [norm_div, hY, Complex.norm_real, Real.norm_of_nonneg hs.le, div_self hs.ne']
    filter_upwards [ae_motion (P := fun p u => ¬ MonoCopy c s (s * ζ) p u) X _ hw h]
      with q hq
    rwa [monoCopy_iff c s (s * ζ) q.1 (direction q.2) X ((Y - X) / s) Y Z
      (by field_simp; ring) (by rw [hZ]; field_simp)] at hq
  have hz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hza' : 0 < ‖z - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hza)

  have e₁ := key hz h₂ 0 z (ζ * z) (by simp) (by ring)
  have e₂ := key ha h₁ 0 a (a * ζ) (by simp [ha.le]) (by ring)
  have e₃ := key hza' h₃ a z (a * (1 - ζ) + ζ * z) rfl (by ring)
  have e₄ := key ha h₁ (a + ζ * z) (ζ * z) (a * (1 - ζ) + ζ * z)
    (by rw [show ζ * z - (a + ζ * z) = -(a : ℂ) by ring, norm_neg]; simp [ha.le]) (by ring)
  have e₅ := key hz h₂ (a + ζ * z) (a - (1 - ζ) * z) a
    (by rw [show a - (1 - ζ) * z - (a + ζ * z) = -z by ring, norm_neg]) (by ring)
  have e₆ := key hza' h₃ (ζ * z) (a - (1 - ζ) * z) (a * ζ)
    (by rw [show a - (1 - ζ) * z - ζ * z = a - z by ring, norm_sub_rev]) (by ring)
  filter_upwards [e₁, e₂, e₃, e₄, e₅, e₆] with q h₁ h₂ h₃ h₄ h₅ h₆ hBAD
  simp only [mul_zero, add_zero] at h₁ h₂
  exact forcing_ii _ _ _ _ _ _ _ _ hBAD.1 hBAD.2 h₁ h₂ h₃ h₄ h₅ h₆
end Erdos173

end
end

-- Erdos173.Measurable.Circle
section
section

noncomputable section

namespace Erdos173

open MeasureTheory Set Real OAI.EuclideanFiveColor

lemma direction_pi_div_three : direction ((π / 3 : ℝ) : Angles) = ζ := by
  rw [direction_real, Circle.coe_exp]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, cos_pi_div_three]; simp [ζ]
  · rw [Complex.exp_ofReal_mul_I_im, sin_pi_div_three]; simp [ζ]

lemma norm_direction_two_mul_sub_one {A : ℝ} (hA : 0 ≤ sin A) :
    ‖direction ((2 * A : ℝ) : Angles) - 1‖ = 2 * sin A := by
  rw [direction_real, Circle.coe_exp, Complex.norm_def]
  have hre : (Complex.exp (↑(2 * A) * Complex.I) - 1).re = cos (2 * A) - 1 := by
    rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re]
  have him : (Complex.exp (↑(2 * A) * Complex.I) - 1).im = sin (2 * A) := by
    rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, sub_zero]
  rw [Complex.normSq_apply, hre, him, cos_two_mul, sin_two_mul]
  rw [show (2 * cos A ^ 2 - 1 - 1) * (2 * cos A ^ 2 - 1 - 1) +
      2 * sin A * cos A * (2 * sin A * cos A) = (2 * sin A) ^ 2 by
    nlinarith [sin_sq_add_cos_sq A]]
  exact sqrt_sq (by positivity)

theorem circle_core {c : ℂ → Fin 2} (hc : Measurable c) {r γ : ℝ} (hr : 0 < r)
    (hγ : Irrational (γ / π)) (h₁ : WeaklyAvoids c r (r * direction ((π / 3 : ℝ) : Angles)))
    (h₂ : WeaklyAvoids c r (r * direction (γ : Angles))) : False := by
  set S := boundary c with hSdef
  have hS : MeasurableSet S := measurableSet_boundary hc
  have hS0 : volume S = 0 := volume_boundary hc
  have hcompl0 : {z | c z ≠ 0} = {z | c z = 1} := by
    ext z; simp only [mem_ofPred_eq]; generalize c z = a; fin_cases a <;> decide
  have hcompl1 : {z | c z ≠ 1} = {z | c z = 0} := by
    ext z; simp only [mem_ofPred_eq]; generalize c z = a; fin_cases a <;> decide
  have hmemS : ∀ q, ¬ DensityZero {z | c z ≠ 0} q → ¬ DensityZero {z | c z ≠ 1} q → q ∈ S := by
    intro q h0 h1
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · rw [← hcompl1]; exact h1
    · rw [← hcompl0]; exact h0

  have hsupp : ∀ p ∈ S, angularMeasure {t | p + r * direction t ∈ S} ≠ 0 := by
    intro p hp hΘ
    have hcont : Continuous fun t : Angles => p + r * direction t :=
      continuous_const.add (continuous_const.mul direction_continuous)
    set R : Fin 2 → Set Angles := fun i => {t | DensityZero {z | c z ≠ i} (p + r * direction t)}
      with hRdef
    have hRm : ∀ i, MeasurableSet (R i) := fun i =>
      (measurableSet_densityZero (measurableSet_eq_fun hc measurable_const).compl).preimage
        hcont.measurable

    have hdisj : ∀ (i : Fin 2) (x : Angles), WeaklyAvoids c r (r * direction x) →
        R i ∩ (· + x) ⁻¹' R i = ∅ := by
      intro i x hx
      refine eq_empty_iff_forall_notMem.2 fun t ⟨ht, htx⟩ => ?_
      refine apex_density hc hx (hp i) t ?_ ?_
      · have ht' : DensityZero {z | c z ≠ i} (p + r * direction t) := ht
        rwa [mul_comm] at ht'
      · have htx' : DensityZero {z | c z ≠ i} (p + r * direction (t + x)) := htx
        have : p + r * direction (t + x) = p + direction t * (↑r * direction x) := by
          rw [direction_add]; ring
        rwa [this] at htx'
    have hΘ' : ∀ x : Angles, angularMeasure ((· + x) ⁻¹' {t | p + r * direction t ∈ S}) = 0 :=
      fun x => ((measurePreserving_add_right angularMeasure x).measure_preimage
        (hS.preimage hcont.measurable).nullMeasurableSet).trans hΘ
    refine circle_alternation (hRm 0) hγ ?_ ?_ ?_
    · rw [hdisj 0 _ h₁, measure_empty]
    · refine measure_mono_null (t := (R 1 ∩ (· + ((π / 3 : ℝ) : Angles)) ⁻¹' R 1) ∪
        {t | p + r * direction t ∈ S} ∪
          (· + ((π / 3 : ℝ) : Angles)) ⁻¹' {t | p + r * direction t ∈ S}) ?_ ?_
      · rintro t ⟨ht, htx⟩
        by_cases h1 : t ∈ R 1
        · by_cases h2 : t + ((π / 3 : ℝ) : Angles) ∈ R 1
          · exact Or.inl (Or.inl ⟨h1, h2⟩)
          · exact Or.inr (hmemS _ htx h2)
        · exact Or.inl (Or.inr (hmemS _ ht h1))
      · rw [hdisj 1 _ h₁]
        simp only [empty_union]
        exact measure_union_null hΘ (hΘ' _)
    · rw [hdisj 0 _ h₂, measure_empty]
  have hempty := eq_empty_of_selfSupporting hS hS0 hr hsupp

  have hpt : ∀ i : Fin 2, ∃ q, DensityZero {z | c z ≠ i} q := by
    intro i
    have hK : MeasurableSet {z | c z ≠ i} := (measurableSet_eq_fun hc measurable_const).compl
    have hpos := volume_ne_zero_of_weaklyAvoids hc h₁ i
    by_contra hno
    push Not at hno
    refine hpos (measure_mono_null (fun q hq => ?_) (ae_iff.1 (ae_densityZero hK)))
    simp only [mem_ofPred_eq, Classical.not_imp, not_not]
    exact ⟨hq, hno q⟩
  obtain ⟨a, ha⟩ := hpt 0
  obtain ⟨b, hb⟩ := hpt 1
  have hA : MeasurableSet {z | c z = 0} := measurableSet_eq_fun hc measurable_const
  have hAc : {z | c z = 0}ᶜ = {z | c z = 1} := by rw [← hcompl0]; rfl
  rw [hcompl0, ← hAc] at ha
  rw [hcompl1] at hb
  obtain ⟨z, hz0, hz1⟩ := exists_not_densityZero hA ha hb
  rw [hAc, ← hcompl0] at hz1
  have : z ∈ S := hmemS z hz1 (by rwa [hcompl1])
  rw [hempty] at this
  exact this

theorem circle_exclusion {x : ℝ} (hx₁ : 2 / 3 < x) (hx₂ : x < 3 / 2) (hx : x ≠ 1)
    (c : ℂ → Fin 2) (hc : Measurable c) (h₁ : WeaklyAvoidsEq c 1)
    (h₂ : WeaklyAvoidsEq c x) : False := by
  have hx0 : 0 < x := by linarith
  rcases irrational_apex_angle hx₁ hx₂ hx with h | h
  · 
    set A := arcsin (x / 2) with hA
    have hsinA : sin A = x / 2 := sin_arcsin (by linarith) (by linarith)
    have hchord : ‖direction ((2 * A : ℝ) : Angles) - 1‖ = x := by
      rw [norm_direction_two_mul_sub_one (by rw [hsinA]; positivity), hsinA]; ring
    have hchord' : ‖direction ((2 * A : ℝ) : Angles) - ((1 : ℝ) : ℂ)‖ = x := by
      rw [Complex.ofReal_one]; exact hchord
    have hiso : WeaklyAvoids c (1 : ℝ) (direction ((2 * A : ℝ) : Angles)) :=
      weaklyAvoids_of_weaklyAvoidsEq c one_pos
        (by intro h0; simpa [h0] using direction_norm ((2 * A : ℝ) : Angles))
        (by intro h1; rw [h1, sub_self, norm_zero] at hchord'; linarith)
        h₁ (by rw [direction_norm]; exact h₁) (by rw [hchord']; exact h₂)
    refine circle_core hc (r := 1) one_pos h ?_ ?_
    · rw [direction_pi_div_three]; exact h₁
    · simpa using hiso
  · 
    set B := arcsin (1 / (2 * x)) with hB
    have hsinB : sin B = 1 / (2 * x) :=
      sin_arcsin
        (by
          have : 0 < 1 / (2 * x) := by positivity
          linarith)
        (by rw [div_le_one (by positivity)]; linarith)
    have hchord : ‖direction ((2 * B : ℝ) : Angles) - 1‖ = 1 / x := by
      rw [norm_direction_two_mul_sub_one (by rw [hsinB]; positivity), hsinB]; field_simp
    set z : ℂ := x * direction ((2 * B : ℝ) : Angles) with hz
    have hzn : ‖z‖ = x := by rw [hz, norm_mul, direction_norm]; simp [abs_of_pos hx0]
    have hzx : ‖z - x‖ = 1 := by
      rw [hz, show (x : ℂ) * direction ((2 * B : ℝ) : Angles) - x =
        x * (direction ((2 * B : ℝ) : Angles) - 1) by ring, norm_mul, hchord]
      simp [abs_of_pos hx0, hx0.ne']
    have hiso : WeaklyAvoids c x z :=
      weaklyAvoids_of_weaklyAvoidsEq c hx0
        (by intro h0; rw [h0, norm_zero] at hzn; linarith)
        (by intro h1; rw [h1, sub_self, norm_zero] at hzx; norm_num at hzx)
        h₂ (by rw [hzn]; exact h₂) (by rw [hzx]; exact h₁)
    exact circle_core hc hx0 h (by rw [direction_pi_div_three]; exact h₂) hiso
end Erdos173

end
end

-- Erdos173.Bessel.Basic
section
section

namespace Erdos173

open Real

private noncomputable def besselJ0 (x : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos (x * cos θ)

private noncomputable def besselJ0Deriv (x : ℝ) : ℝ :=
  -((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos θ * sin (x * cos θ))

private noncomputable def besselJ0Deriv2 (x : ℝ) : ℝ :=
  -((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 * cos (x * cos θ))

lemma abs_inv_two_pi_mul_integral_le_one {f : ℝ → ℝ} (hf : ∀ θ, |f θ| ≤ 1) :
    |(2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f θ| ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
    (C := 1) (f := f) fun θ _ => hf θ
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos two_pi_pos, one_mul] at h
  rw [abs_mul, abs_of_pos (inv_pos.mpr two_pi_pos)]
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, f θ| ≤ (2 * π)⁻¹ * (2 * π) := by gcongr
    _ = 1 := inv_mul_cancel₀ two_pi_pos.ne'

theorem abs_besselJ0_le_one (x : ℝ) : |besselJ0 x| ≤ 1 :=
  abs_inv_two_pi_mul_integral_le_one fun _ => abs_cos_le_one _

theorem abs_besselJ0Deriv_le_one (x : ℝ) : |besselJ0Deriv x| ≤ 1 := by
  rw [besselJ0Deriv, abs_neg]
  refine abs_inv_two_pi_mul_integral_le_one fun θ => ?_
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)).trans (abs_sin_le_one _)

theorem hasDerivAt_besselJ0 (x : ℝ) : HasDerivAt besselJ0 (besselJ0Deriv x) x := by
  have h := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x θ => cos (x * cos θ)) (F' := fun x θ => -(cos θ * sin (x * cos θ)))
    (μ := MeasureTheory.volume) (x₀ := x) (bound := fun _ => 1) (a := 0) (b := 2 * π)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (by fun_prop : Continuous fun θ => cos (x * cos θ))
      |>.aestronglyMeasurable)
    ((by fun_prop : Continuous fun θ => cos (x * cos θ)).intervalIntegrable _ _)
    (by fun_prop : Continuous fun θ => -(cos θ * sin (x * cos θ))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ _ y _ => by
      rw [norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _)).trans (abs_sin_le_one _))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ y _ => by
      convert! ((hasDerivAt_mul_const (cos θ)).cos : HasDerivAt (fun y => cos (y * cos θ)) _ y)
        using 1 <;> ring)).2.const_mul (2 * π)⁻¹
  rwa [intervalIntegral.integral_neg, mul_neg] at h

theorem hasDerivAt_besselJ0Deriv (x : ℝ) : HasDerivAt besselJ0Deriv (besselJ0Deriv2 x) x := by
  exact ((intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x θ => cos θ * sin (x * cos θ)) (F' := fun x θ => cos θ ^ 2 * cos (x * cos θ))
    (μ := MeasureTheory.volume) (x₀ := x) (bound := fun _ => 1) (a := 0) (b := 2 * π)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x =>
      (by fun_prop : Continuous fun θ => cos θ * sin (x * cos θ)).aestronglyMeasurable)
    ((by fun_prop : Continuous fun θ => cos θ * sin (x * cos θ)).intervalIntegrable _ _)
    (by fun_prop : Continuous fun θ => cos θ ^ 2 * cos (x * cos θ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ _ y _ => by
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (abs_nonneg _)
        (pow_le_one₀ (abs_nonneg _) (abs_cos_le_one _))).trans (abs_cos_le_one _))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ y _ => by
      convert! ((hasDerivAt_mul_const (cos θ)).sin.const_mul (cos θ) :
        HasDerivAt (fun y => cos θ * sin (y * cos θ)) _ y) using 1 <;> ring)).2.const_mul (2 * π)⁻¹).neg

theorem continuous_besselJ0 : Continuous besselJ0 :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_besselJ0 x).continuousAt

theorem besselJ0_ode (x : ℝ) : x * besselJ0Deriv2 x + besselJ0Deriv x + x * besselJ0 x = 0 := by
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * π), HasDerivAt (fun θ => sin θ * sin (x * cos θ))
      (cos θ * sin (x * cos θ) - x * sin θ ^ 2 * cos (x * cos θ)) θ := fun θ _ => by
    convert! (hasDerivAt_sin θ).mul ((hasDerivAt_cos θ).const_mul x).sin using 1 <;> ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun θ =>
      cos θ * sin (x * cos θ) - x * sin θ ^ 2 * cos (x * cos θ)).intervalIntegrable _ _)
  simp only [sin_two_pi, sin_zero, zero_mul, sub_zero] at hint
  have hsplit : (∫ θ in (0 : ℝ)..2 * π,
      cos θ * sin (x * cos θ) - x * sin θ ^ 2 * cos (x * cos θ)) =
      (∫ θ in (0 : ℝ)..2 * π, cos θ * sin (x * cos θ)) -
        x * ((∫ θ in (0 : ℝ)..2 * π, cos (x * cos θ)) -
          ∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 * cos (x * cos θ)) := by
    have hcongr : (fun θ => cos θ * sin (x * cos θ) - x * sin θ ^ 2 * cos (x * cos θ)) =
        fun θ => cos θ * sin (x * cos θ) -
          x * (cos (x * cos θ) - cos θ ^ 2 * cos (x * cos θ)) := by
      ext θ
      rw [sin_sq]
      ring
    rw [hcongr, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub] <;> exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hsplit] at hint
  simp only [besselJ0, besselJ0Deriv, besselJ0Deriv2]
  linear_combination (-(2 * π)⁻¹) * hint
end Erdos173
end

-- Erdos173.Bessel.Shape
section
section

noncomputable section

namespace Erdos173

open Real Set

theorem abs_besselJ0Deriv2_le_half (x : ℝ) : |besselJ0Deriv2 x| ≤ 1 / 2 := by
  have hπ := two_pi_pos
  have hle : |∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 * cos (x * cos θ)| ≤
      ∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 := by
    refine (intervalIntegral.abs_integral_le_integral_abs hπ.le).trans
      (intervalIntegral.integral_mono_on hπ.le ?_ ?_ fun θ _ => ?_)
    · exact (by fun_prop : Continuous fun θ =>
        |cos θ ^ 2 * cos (x * cos θ)|).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ => cos θ ^ 2).intervalIntegrable _ _
    · rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_right (sq_nonneg _) (abs_cos_le_one _)
  rw [integral_cos_sq] at hle
  simp only [cos_two_pi, sin_two_pi, cos_zero, sin_zero, mul_zero, sub_zero,
    zero_add] at hle
  rw [besselJ0Deriv2, abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hπ)]
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, cos θ ^ 2 * cos (x * cos θ)|
      ≤ (2 * π)⁻¹ * ((2 * π) / 2) := by gcongr
    _ = 1 / 2 := by field_simp

theorem abs_besselJ0Deriv_sub_le (s t : ℝ) :
    |besselJ0Deriv t - besselJ0Deriv s| ≤ |t - s| / 2 := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (G := ℝ)
    (f := besselJ0Deriv) (s := univ) (x := s) (y := t) (C := 1 / 2)
    (fun x _ => (hasDerivAt_besselJ0Deriv x).hasDerivWithinAt)
    (fun x _ => abs_besselJ0Deriv2_le_half x) convex_univ (mem_univ _) (mem_univ _)
  simp only [Real.norm_eq_abs] at h
  linarith

theorem abs_besselJ0_sub_le (s t : ℝ) : |besselJ0 t - besselJ0 s| ≤ |t - s| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (G := ℝ)
    (f := besselJ0) (s := univ) (x := s) (y := t) (C := 1)
    (fun x _ => (hasDerivAt_besselJ0 x).hasDerivWithinAt)
    (fun x _ => abs_besselJ0Deriv_le_one x) convex_univ (mem_univ _) (mem_univ _)
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem besselJ0Deriv_nonpos_of_le_pi {t : ℝ} (ht : 0 ≤ t) (htπ : t ≤ π) :
    besselJ0Deriv t ≤ 0 := by
  rw [besselJ0Deriv, neg_nonpos]
  refine mul_nonneg (inv_nonneg.mpr two_pi_pos.le)
    (intervalIntegral.integral_nonneg two_pi_pos.le fun θ _ => ?_)
  have h1 := neg_one_le_cos θ
  have h2 := cos_le_one θ
  rcases le_or_gt 0 (cos θ) with hc | hc
  · exact mul_nonneg hc (sin_nonneg_of_nonneg_of_le_pi (mul_nonneg ht hc) (by nlinarith))
  · exact mul_nonneg_of_nonpos_of_nonpos hc.le
      (sin_nonpos_of_nonpos_of_neg_pi_le (mul_nonpos_of_nonneg_of_nonpos ht hc.le)
        (by nlinarith))

theorem antitoneOn_besselJ0 {a b : ℝ} (h : ∀ t ∈ Icc a b, besselJ0Deriv t ≤ 0) :
    AntitoneOn besselJ0 (Icc a b) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) continuous_besselJ0.continuousOn
    (fun t _ => (hasDerivAt_besselJ0 t).hasDerivWithinAt) fun t ht => h t (interior_subset ht)

theorem monotoneOn_besselJ0 {a b : ℝ} (h : ∀ t ∈ Icc a b, 0 ≤ besselJ0Deriv t) :
    MonotoneOn besselJ0 (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) continuous_besselJ0.continuousOn
    (fun t _ => (hasDerivAt_besselJ0 t).hasDerivWithinAt) fun t ht => h t (interior_subset ht)

private def besselEnergy (t : ℝ) : ℝ :=
  besselJ0 t ^ 2 + besselJ0Deriv t ^ 2

theorem antitoneOn_besselEnergy {s : ℝ} (hs : 0 < s) : AntitoneOn besselEnergy (Ici s) := by
  have hd (t : ℝ) : HasDerivAt besselEnergy
      (2 * besselJ0 t * besselJ0Deriv t + 2 * besselJ0Deriv t * besselJ0Deriv2 t) t := by
    convert! ((hasDerivAt_besselJ0 t).pow 2).add ((hasDerivAt_besselJ0Deriv t).pow 2) using 1
    norm_num
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici s)
    (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => (hd t).hasDerivWithinAt)
    fun t ht => ?_
  rw [interior_Ici] at ht
  have ht0 : 0 < t := hs.trans ht
  have key : t * (2 * besselJ0 t * besselJ0Deriv t + 2 * besselJ0Deriv t * besselJ0Deriv2 t) =
      -2 * besselJ0Deriv t ^ 2 := by
    linear_combination (2 * besselJ0Deriv t) * besselJ0_ode t
  nlinarith [sq_nonneg (besselJ0Deriv t)]

theorem sq_besselJ0_le_energy {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    besselJ0 t ^ 2 ≤ besselJ0 s ^ 2 + besselJ0Deriv s ^ 2 := by
  have h := antitoneOn_besselEnergy hs self_mem_Ici hst hst
  simp only [besselEnergy] at h
  nlinarith [sq_nonneg (besselJ0Deriv t)]

end Erdos173

end
end

-- Erdos173.Bessel.Taylor
section
section

noncomputable section

namespace Erdos173
open Real Finset

private def cosTaylor (N : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ range N, (-1) ^ k * y ^ (2 * k) / ((2 * k).factorial : ℝ)

private def sinTaylor (N : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ range N, (-1) ^ k * y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)

lemma hasDerivAt_pow_div_factorial (m : ℕ) (y : ℝ) :
    HasDerivAt (fun y => y ^ (m + 1) / ((m + 1).factorial : ℝ))
      (y ^ m / (m.factorial : ℝ)) y := by
  convert! (hasDerivAt_pow (m + 1) y).div_const ((m + 1).factorial : ℝ) using 1
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp
  push_cast
  ring

lemma hasDerivAt_sinTaylor (N : ℕ) (y : ℝ) :
    HasDerivAt (sinTaylor N) (cosTaylor N y) y := by
  have h := HasDerivAt.fun_sum (u := range N) (x := y)
    (A := fun k y => (-1) ^ k * (y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)))
    (A' := fun k => (-1) ^ k * (y ^ (2 * k) / ((2 * k).factorial : ℝ)))
    fun k _ => (hasDerivAt_pow_div_factorial (2 * k) y).const_mul _
  convert! h using 1
  · ext y
    simp only [sinTaylor, mul_div_assoc]
  · simp only [cosTaylor, mul_div_assoc]

lemma hasDerivAt_cosTaylor_succ (N : ℕ) (y : ℝ) :
    HasDerivAt (cosTaylor (N + 1)) (-sinTaylor N y) y := by
  have h := (HasDerivAt.fun_sum (u := range N) (x := y)
    (A := fun k y => (-1) ^ (k + 1) * (y ^ (2 * k + 1 + 1) / ((2 * k + 1 + 1).factorial : ℝ)))
    (A' := fun k => (-1) ^ (k + 1) * (y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)))
    fun k _ => (hasDerivAt_pow_div_factorial (2 * k + 1) y).const_mul _).add_const 1
  convert! h using 1
  · ext y
    simp only [cosTaylor, sum_range_succ', mul_div_assoc]
    norm_num [mul_add, pow_succ]
  · simp only [sinTaylor, ← sum_neg_distrib, mul_div_assoc, pow_succ]
    ring_nf

lemma abs_le_of_abs_deriv_le {f f' : ℝ → ℝ} {m : ℕ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (h0 : f 0 = 0) (hb : ∀ t, |f' t| ≤ |t| ^ m / (m.factorial : ℝ)) (y : ℝ) :
    |f y| ≤ |y| ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  wlog hy : 0 ≤ y generalizing f f' y
  · have h := this (f := fun t => f (-t)) (f' := fun t => -f' (-t))
      (fun t => by
        have := (hf (-t)).comp t (hasDerivAt_neg t)
        simpa [Function.comp_def] using this) (by simpa using h0)
      (fun t => by simpa [abs_neg] using hb (-t)) (-y) (by linarith)
    simpa [abs_neg] using h
  set g : ℝ → ℝ := fun y => y ^ (m + 1) / ((m + 1).factorial : ℝ)
  have hg := hasDerivAt_pow_div_factorial m
  have hmono (s : ℝ) (hs : s = 1 ∨ s = -1) : MonotoneOn (fun t => g t + s * f t) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t _ => ((hg t).add ((hf t).const_mul s)).continuousAt.continuousWithinAt)
      (fun t _ => ((hg t).add ((hf t).const_mul s)).hasDerivWithinAt) fun t ht => ?_
    rw [interior_Ici] at ht
    have hb' := abs_le.mp (hb t)
    rw [abs_of_pos ht] at hb'
    rcases hs with rfl | rfl <;> linarith
  have h1 := hmono 1 (Or.inl rfl) Set.self_mem_Ici hy hy
  have h2 := hmono (-1) (Or.inr rfl) Set.self_mem_Ici hy hy
  simp only [g, h0, mul_zero, add_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, zero_div] at h1 h2
  rw [abs_of_nonneg hy, abs_le]
  constructor <;> linarith

lemma abs_sin_sub_sinTaylor_le_of_cos {N : ℕ}
    (hc : ∀ y, |cos y - cosTaylor N y| ≤ |y| ^ (2 * N) / ((2 * N).factorial : ℝ)) (y : ℝ) :
    |sin y - sinTaylor N y| ≤ |y| ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) :=
  abs_le_of_abs_deriv_le (fun t => (hasDerivAt_sin t).sub (hasDerivAt_sinTaylor N t))
    (by simp [sinTaylor]) hc y

theorem abs_cos_sub_cosTaylor_le (N : ℕ) (y : ℝ) :
    |cos y - cosTaylor N y| ≤ |y| ^ (2 * N) / ((2 * N).factorial : ℝ) := by
  induction N generalizing y with
  | zero => simpa [cosTaylor] using abs_cos_le_one y
  | succ N ih =>
    have h := abs_le_of_abs_deriv_le (m := 2 * N + 1)
      (fun t => (hasDerivAt_cos t).sub (hasDerivAt_cosTaylor_succ N t))
      (by simp [cosTaylor, sum_range_succ']) (fun t => ?_) y
    · simpa [mul_add] using h
    · rw [show -sin t - -sinTaylor N t = -(sin t - sinTaylor N t) by ring, abs_neg]
      exact abs_sin_sub_sinTaylor_le_of_cos ih t

theorem abs_sin_sub_sinTaylor_le (N : ℕ) (y : ℝ) :
    |sin y - sinTaylor N y| ≤ |y| ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) :=
  abs_sin_sub_sinTaylor_le_of_cos (abs_cos_sub_cosTaylor_le N) y

end Erdos173

end
end

-- Erdos173.Bessel.Series
section
section

noncomputable section

namespace Erdos173

open Real Finset

private def j0Partial (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range N, (-1) ^ k * (x / 2) ^ (2 * k) / (k.factorial : ℝ) ^ 2

private def j1Partial (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range N,
    (-1) ^ k * (x / 2) ^ (2 * k + 1) / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))

lemma integral_cos_pow_two_mul (k : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, cos θ ^ (2 * k) =
      2 * π * ((2 * k).factorial : ℝ) / (4 ^ k * (k.factorial : ℝ) ^ 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, integral_cos_pow, ih]
    simp only [sin_zero, sin_two_pi, mul_zero, sub_zero, zero_div, zero_add]
    rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, Nat.factorial_succ (2 * k + 1),
      Nat.factorial_succ (2 * k), Nat.factorial_succ k]
    push_cast
    field_simp
    ring

lemma integral_even_term (k : ℕ) (y : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, y ^ (2 * k) / ((2 * k).factorial : ℝ) * cos θ ^ (2 * k) =
      2 * π * ((y / 2) ^ (2 * k) / (k.factorial : ℝ) ^ 2) := by
  rw [intervalIntegral.integral_const_mul, integral_cos_pow_two_mul, div_pow, pow_mul,
    pow_mul 2]
  field_simp
  norm_num

lemma integral_odd_term (k : ℕ) (y : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π,
      y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) * cos θ ^ (2 * (k + 1)) =
      2 * π * ((y / 2) ^ (2 * k + 1) / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))) := by
  have h2 : (2 : ℝ) ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [intervalIntegral.integral_const_mul, integral_cos_pow_two_mul,
    show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ (2 * k + 1),
    Nat.factorial_succ k, div_pow, h2, pow_succ (4 : ℝ)]
  push_cast
  field_simp
  ring

lemma continuous_cosTaylor (N : ℕ) : Continuous (cosTaylor N) := by
  unfold cosTaylor
  fun_prop

lemma continuous_sinTaylor (N : ℕ) : Continuous (sinTaylor N) := by
  unfold sinTaylor
  fun_prop

lemma integral_cosTaylor (N : ℕ) (x : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, cosTaylor N (x * cos θ) = 2 * π * j0Partial N x := by
  simp only [cosTaylor, j0Partial, mul_sum]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (by fun_prop : Continuous fun θ =>
      (-1) ^ k * (x * cos θ) ^ (2 * k) / ((2 * k).factorial : ℝ)).intervalIntegrable _ _]
  refine sum_congr rfl fun k _ => ?_
  have h : (fun θ => (-1) ^ k * (x * cos θ) ^ (2 * k) / ((2 * k).factorial : ℝ)) =
      fun θ => (-1) ^ k * (x ^ (2 * k) / ((2 * k).factorial : ℝ) * cos θ ^ (2 * k)) := by
    ext θ
    ring
  rw [h, intervalIntegral.integral_const_mul, integral_even_term]
  ring

lemma integral_cos_mul_sinTaylor (N : ℕ) (x : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, cos θ * sinTaylor N (x * cos θ) = 2 * π * j1Partial N x := by
  simp only [sinTaylor, j1Partial, mul_sum]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (by fun_prop : Continuous fun θ =>
      cos θ * ((-1) ^ k * (x * cos θ) ^ (2 * k + 1) /
        ((2 * k + 1).factorial : ℝ))).intervalIntegrable _ _]
  refine sum_congr rfl fun k _ => ?_
  have h : (fun θ => cos θ * ((-1) ^ k * (x * cos θ) ^ (2 * k + 1) /
      ((2 * k + 1).factorial : ℝ))) = fun θ => (-1) ^ k *
        (x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) * cos θ ^ (2 * (k + 1))) := by
    ext θ
    ring
  rw [h, intervalIntegral.integral_const_mul, integral_odd_term]
  ring

theorem abs_besselJ0_sub_j0Partial_le (N : ℕ) (x : ℝ) :
    |besselJ0 x - j0Partial N x| ≤ (x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2 := by
  have hπ := two_pi_pos
  have hc := continuous_cosTaylor N
  have hdiff : besselJ0 x - j0Partial N x = (2 * π)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, (cos (x * cos θ) - cosTaylor N (x * cos θ)) := by
    rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun θ =>
      cos (x * cos θ)).intervalIntegrable _ _) ((by fun_prop : Continuous fun θ =>
        cosTaylor N (x * cos θ)).intervalIntegrable _ _), integral_cosTaylor, besselJ0,
      mul_sub, ← mul_assoc, inv_mul_cancel₀ hπ.ne', one_mul]
  have hle : |∫ θ in (0 : ℝ)..2 * π, (cos (x * cos θ) - cosTaylor N (x * cos θ))| ≤
      ∫ θ in (0 : ℝ)..2 * π, x ^ (2 * N) / ((2 * N).factorial : ℝ) * cos θ ^ (2 * N) := by
    refine (intervalIntegral.abs_integral_le_integral_abs hπ.le).trans
      (intervalIntegral.integral_mono_on hπ.le ?_ ?_ fun θ _ => ?_)
    · exact (by fun_prop : Continuous fun θ =>
        |cos (x * cos θ) - cosTaylor N (x * cos θ)|).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ =>
        x ^ (2 * N) / ((2 * N).factorial : ℝ) * cos θ ^ (2 * N)).intervalIntegrable _ _
    · have h := abs_cos_sub_cosTaylor_le N (x * cos θ)
      rw [(even_two_mul N).pow_abs, mul_pow] at h
      exact h.trans_eq (by ring)
  rw [integral_even_term] at hle
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.mpr hπ)]
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, (cos (x * cos θ) - cosTaylor N (x * cos θ))|
      ≤ (2 * π)⁻¹ * (2 * π * ((x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2)) := by gcongr
    _ = (x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2 := by field_simp

theorem abs_besselJ0Deriv_add_j1Partial_le (N : ℕ) (x : ℝ) :
    |besselJ0Deriv x + j1Partial N x| ≤
      |x / 2| ^ (2 * N + 1) / ((N.factorial : ℝ) * ((N + 1).factorial : ℝ)) := by
  have hπ := two_pi_pos
  have hs := continuous_sinTaylor N
  have hdiff : besselJ0Deriv x + j1Partial N x = -((2 * π)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, cos θ * (sin (x * cos θ) - sinTaylor N (x * cos θ))) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun θ =>
      cos θ * sin (x * cos θ)).intervalIntegrable _ _) ((by fun_prop : Continuous fun θ =>
        cos θ * sinTaylor N (x * cos θ)).intervalIntegrable _ _), integral_cos_mul_sinTaylor,
      besselJ0Deriv, mul_sub, ← mul_assoc, inv_mul_cancel₀ hπ.ne', one_mul]
    ring
  have hle : |∫ θ in (0 : ℝ)..2 * π, cos θ * (sin (x * cos θ) - sinTaylor N (x * cos θ))| ≤
      ∫ θ in (0 : ℝ)..2 * π,
        |x| ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) * cos θ ^ (2 * (N + 1)) := by
    refine (intervalIntegral.abs_integral_le_integral_abs hπ.le).trans
      (intervalIntegral.integral_mono_on hπ.le ?_ ?_ fun θ _ => ?_)
    · exact (by fun_prop : Continuous fun θ =>
        |cos θ * (sin (x * cos θ) - sinTaylor N (x * cos θ))|).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun θ =>
        |x| ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) * cos θ ^ (2 * (N + 1))).intervalIntegrable
          _ _
    · have h := abs_sin_sub_sinTaylor_le N (x * cos θ)
      have hcos : cos θ ^ (2 * (N + 1)) = |cos θ| * |cos θ| ^ (2 * N + 1) := by
        rw [← pow_succ', show 2 * N + 1 + 1 = 2 * (N + 1) by ring,
          (even_two_mul (N + 1)).pow_abs]
      rw [hcos, abs_mul (cos θ)]
      calc |cos θ| * |sin (x * cos θ) - sinTaylor N (x * cos θ)|
          ≤ |cos θ| * (|x| ^ (2 * N + 1) * |cos θ| ^ (2 * N + 1) /
            ((2 * N + 1).factorial : ℝ)) := by gcongr; rwa [abs_mul, mul_pow] at h
        _ = _ := by ring
  rw [integral_odd_term] at hle
  rw [hdiff, abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hπ), abs_div, abs_two]
  calc (2 * π)⁻¹ *
        |∫ θ in (0 : ℝ)..2 * π, cos θ * (sin (x * cos θ) - sinTaylor N (x * cos θ))|
      ≤ (2 * π)⁻¹ * (2 * π * ((|x| / 2) ^ (2 * N + 1) /
        ((N.factorial : ℝ) * ((N + 1).factorial : ℝ)))) := by gcongr
    _ = _ := by field_simp
end Erdos173

end
end

-- Erdos173.Bessel.Values
section
section

noncomputable section

namespace Erdos173

open Finset

lemma le_besselJ0_of_partial {N : ℕ} {x c : ℝ}
    (h : c ≤ j0Partial N x - (x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2) : c ≤ besselJ0 x := by
  linarith [(abs_le.mp (abs_besselJ0_sub_j0Partial_le N x)).1]

lemma besselJ0_le_of_partial {N : ℕ} {x c : ℝ}
    (h : j0Partial N x + (x / 2) ^ (2 * N) / (N.factorial : ℝ) ^ 2 ≤ c) : besselJ0 x ≤ c := by
  linarith [(abs_le.mp (abs_besselJ0_sub_j0Partial_le N x)).2]

lemma le_besselJ0Deriv_of_partial {N : ℕ} {x c : ℝ} (hx : 0 ≤ x)
    (h : c ≤ -j1Partial N x -
      (x / 2) ^ (2 * N + 1) / ((N.factorial : ℝ) * ((N + 1).factorial : ℝ))) :
    c ≤ besselJ0Deriv x := by
  have h' := (abs_le.mp (abs_besselJ0Deriv_add_j1Partial_le N x)).1
  rw [abs_of_nonneg (by positivity : 0 ≤ x / 2)] at h'
  linarith

lemma besselJ0Deriv_le_of_partial {N : ℕ} {x c : ℝ} (hx : 0 ≤ x)
    (h : -j1Partial N x +
      (x / 2) ^ (2 * N + 1) / ((N.factorial : ℝ) * ((N + 1).factorial : ℝ)) ≤ c) :
    besselJ0Deriv x ≤ c := by
  have h' := (abs_le.mp (abs_besselJ0Deriv_add_j1Partial_le N x)).2
  rw [abs_of_nonneg (by positivity : 0 ≤ x / 2)] at h'
  linarith

theorem besselJ0_three : -261 / 1000 ≤ besselJ0 3 :=
  le_besselJ0_of_partial (N := 8) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))

theorem besselJ0Deriv_three : besselJ0Deriv 3 ≤ -33 / 100 :=
  besselJ0Deriv_le_of_partial (N := 8) (by norm_num) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))

theorem besselJ0_sixteen_fifths : -321 / 1000 ≤ besselJ0 (16 / 5) :=
  le_besselJ0_of_partial (N := 9) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))

theorem besselJ0Deriv_seven_halves : besselJ0Deriv (7 / 2) ≤ -13 / 100 :=
  besselJ0Deriv_le_of_partial (N := 9) (by norm_num) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))

theorem besselJ0_fifteen_quarters :
    -4015 / 10000 ≤ besselJ0 (15 / 4) ∧ besselJ0 (15 / 4) ≤ 0 :=
  ⟨le_besselJ0_of_partial (N := 9) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num)),
    besselJ0_le_of_partial (N := 9) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))⟩

theorem besselJ0Deriv_fifteen_quarters :
    -334 / 10000 ≤ besselJ0Deriv (15 / 4) ∧ besselJ0Deriv (15 / 4) ≤ 334 / 10000 :=
  ⟨le_besselJ0Deriv_of_partial (N := 9) (by norm_num) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num)),
    besselJ0Deriv_le_of_partial (N := 9) (by norm_num) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))⟩

theorem besselJ0_nine_halves : -321 / 1000 ≤ besselJ0 (9 / 2) :=
  le_besselJ0_of_partial (N := 10) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))

theorem besselJ0Deriv_nine_halves : 23 / 100 ≤ besselJ0Deriv (9 / 2) :=
  le_besselJ0Deriv_of_partial (N := 10) (by norm_num) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))

theorem besselJ0_twenty_four_fifths : -241 / 1000 ≤ besselJ0 (24 / 5) :=
  le_besselJ0_of_partial (N := 11) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))

theorem besselJ0Deriv_eleven_halves : 34 / 100 ≤ besselJ0Deriv (11 / 2) :=
  le_besselJ0Deriv_of_partial (N := 12) (by norm_num) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))

theorem besselJ0_thirteen_halves : 1 / 4 ≤ besselJ0 (13 / 2) :=
  le_besselJ0_of_partial (N := 13) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))

theorem besselJ0_fifteen_halves : 1 / 4 ≤ besselJ0 (15 / 2) :=
  le_besselJ0_of_partial (N := 15) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))

theorem besselJ0Deriv_seventeen_halves : besselJ0Deriv (17 / 2) ≤ -27 / 100 :=
  besselJ0Deriv_le_of_partial (N := 16) (by norm_num) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))

theorem besselJ0Deriv_nine : besselJ0Deriv 9 ≤ -24 / 100 :=
  besselJ0Deriv_le_of_partial (N := 17) (by norm_num) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))

theorem besselJ0_forty_six_fifths :
    -137 / 1000 ≤ besselJ0 (46 / 5) ∧ besselJ0 (46 / 5) ≤ 0 :=
  ⟨le_besselJ0_of_partial (N := 17) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num)),
    besselJ0_le_of_partial (N := 17) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))⟩

theorem besselJ0Deriv_forty_six_fifths :
    -218 / 1000 ≤ besselJ0Deriv (46 / 5) ∧ besselJ0Deriv (46 / 5) ≤ 218 / 1000 :=
  ⟨le_besselJ0Deriv_of_partial (N := 17) (by norm_num) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num)),
    besselJ0Deriv_le_of_partial (N := 17) (by norm_num) (by (simp only [j0Partial, j1Partial, sum_range_succ, sum_range_zero, Nat.factorial] <;> norm_num))⟩

end Erdos173

end
end

-- Erdos173.Bessel.PairBound
section
section

noncomputable section

namespace Erdos173

open Real Set

lemma besselJ0Deriv_nonpos_of_near {p c t : ℝ} (hp : besselJ0Deriv p ≤ -c)
    (ht : |t - p| ≤ 2 * c) : besselJ0Deriv t ≤ 0 := by
  linarith [(abs_le.mp (abs_besselJ0Deriv_sub_le p t)).2]

lemma besselJ0Deriv_nonneg_of_near {p c t : ℝ} (hp : c ≤ besselJ0Deriv p)
    (ht : |t - p| ≤ 2 * c) : 0 ≤ besselJ0Deriv t := by
  linarith [(abs_le.mp (abs_besselJ0Deriv_sub_le p t)).1]

theorem antitoneOn_besselJ0_zero_fifteen_quarters :
    AntitoneOn besselJ0 (Icc 0 (15 / 4)) := by
  refine antitoneOn_besselJ0 fun t ht => ?_
  rcases le_or_gt t 3 with h3 | h3
  · exact besselJ0Deriv_nonpos_of_le_pi ht.1 (h3.trans pi_gt_three.le)
  rcases le_or_gt t (18 / 5) with h4 | h4
  · exact besselJ0Deriv_nonpos_of_near (p := 3) (c := 33 / 100)
      (by linarith [besselJ0Deriv_three])
      (abs_le.mpr ⟨by linarith, by linarith⟩)
  · exact besselJ0Deriv_nonpos_of_near (p := 7 / 2) (c := 13 / 100)
      (by linarith [besselJ0Deriv_seven_halves])
      (abs_le.mpr ⟨by linarith, by linarith [ht.2]⟩)

theorem monotoneOn_besselJ0_nine_halves_sixty_one_tenths :
    MonotoneOn besselJ0 (Icc (9 / 2) (61 / 10)) := by
  refine monotoneOn_besselJ0 fun t ht => ?_
  rcases le_or_gt t (49 / 10) with h | h
  · exact besselJ0Deriv_nonneg_of_near (p := 9 / 2) (c := 23 / 100)
      (by linarith [besselJ0Deriv_nine_halves])
      (abs_le.mpr ⟨by linarith [ht.1], by linarith⟩)
  · exact besselJ0Deriv_nonneg_of_near (p := 11 / 2) (c := 34 / 100)
      (by linarith [besselJ0Deriv_eleven_halves])
      (abs_le.mpr ⟨by linarith, by linarith [ht.2]⟩)

theorem antitoneOn_besselJ0_eight_forty_six_fifths :
    AntitoneOn besselJ0 (Icc 8 (46 / 5)) := by
  refine antitoneOn_besselJ0 fun t ht => ?_
  rcases le_or_gt t 9 with h | h
  · exact besselJ0Deriv_nonpos_of_near (p := 17 / 2) (c := 27 / 100)
      (by linarith [besselJ0Deriv_seventeen_halves])
      (abs_le.mpr ⟨by linarith [ht.1], by linarith⟩)
  · exact besselJ0Deriv_nonpos_of_near (p := 9) (c := 24 / 100)
      (by linarith [besselJ0Deriv_nine])
      (abs_le.mpr ⟨by linarith, by linarith [ht.2]⟩)

lemma neg_le_besselJ0_of_energy {s t c : ℝ} (hs : 0 < s) (hst : s ≤ t) (hc : 0 ≤ c)
    (hE : besselJ0 s ^ 2 + besselJ0Deriv s ^ 2 ≤ c ^ 2) : -c ≤ besselJ0 t :=
  (abs_le_of_sq_le_sq' ((sq_besselJ0_le_energy hs hst).trans hE) hc).1

theorem le_besselJ0_of_nonneg {t : ℝ} (ht : 0 ≤ t) : -403 / 1000 ≤ besselJ0 t := by
  obtain ⟨hJ₁, hJ₂⟩ := besselJ0_fifteen_quarters
  rcases le_or_gt t (15 / 4) with h | h
  · linarith [antitoneOn_besselJ0_zero_fifteen_quarters ⟨ht, h⟩ ⟨by norm_num, le_rfl⟩ h]
  · obtain ⟨hD₁, hD₂⟩ := besselJ0Deriv_fifteen_quarters
    refine le_trans (le_of_eq (by norm_num))
      (neg_le_besselJ0_of_energy (c := 403 / 1000) (by norm_num) h.le (by norm_num) ?_)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ besselJ0 (15 / 4) + 4015 / 10000)
      (by linarith : (0 : ℝ) ≤ -besselJ0 (15 / 4)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ besselJ0Deriv (15 / 4) + 334 / 10000)
      (by linarith : (0 : ℝ) ≤ 334 / 10000 - besselJ0Deriv (15 / 4))]

theorem le_besselJ0_of_le_three {t : ℝ} (ht : 0 ≤ t) (h3 : t ≤ 3) :
    -261 / 1000 ≤ besselJ0 t :=
  besselJ0_three.trans
    (antitoneOn_besselJ0_zero_fifteen_quarters ⟨ht, by linarith⟩ ⟨by norm_num, by norm_num⟩ h3)

theorem le_besselJ0_of_twenty_four_fifths_le {t : ℝ} (ht : 24 / 5 ≤ t) :
    -261 / 1000 ≤ besselJ0 t := by
  rcases le_or_gt t (61 / 10) with h | h
  · linarith [besselJ0_twenty_four_fifths, monotoneOn_besselJ0_nine_halves_sixty_one_tenths
      ⟨by norm_num, by norm_num⟩ ⟨by linarith, h⟩ ht]
  rcases le_or_gt t 7 with h7 | h7
  · have := (abs_le.mp (abs_besselJ0_sub_le (13 / 2) t)).1
    have := abs_le.mpr (⟨by linarith, by linarith⟩ : -(1 / 2) ≤ t - 13 / 2 ∧ t - 13 / 2 ≤ 1 / 2)
    linarith [besselJ0_thirteen_halves]
  rcases le_or_gt t 8 with h8 | h8
  · have := (abs_le.mp (abs_besselJ0_sub_le (15 / 2) t)).1
    have := abs_le.mpr (⟨by linarith, by linarith⟩ : -(1 / 2) ≤ t - 15 / 2 ∧ t - 15 / 2 ≤ 1 / 2)
    linarith [besselJ0_fifteen_halves]
  obtain ⟨hJ₁, hJ₂⟩ := besselJ0_forty_six_fifths
  rcases le_or_gt t (46 / 5) with h9 | h9
  · linarith [antitoneOn_besselJ0_eight_forty_six_fifths ⟨h8.le, h9⟩ ⟨by norm_num, le_rfl⟩ h9]
  · obtain ⟨hD₁, hD₂⟩ := besselJ0Deriv_forty_six_fifths
    refine le_trans (le_of_eq (by norm_num))
      (neg_le_besselJ0_of_energy (c := 261 / 1000) (by norm_num) h9.le (by norm_num) ?_)
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ besselJ0 (46 / 5) + 137 / 1000)
      (by linarith : (0 : ℝ) ≤ -besselJ0 (46 / 5)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ besselJ0Deriv (46 / 5) + 218 / 1000)
      (by linarith : (0 : ℝ) ≤ 218 / 1000 - besselJ0Deriv (46 / 5))]

theorem besselJ0_add_lower {x : ℝ} (hx : 3 / 2 ≤ x) {t : ℝ} (ht : 0 ≤ t) :
    -83 / 125 ≤ besselJ0 t + besselJ0 (x * t) := by
  have hxt : 3 / 2 * t ≤ x * t := mul_le_mul_of_nonneg_right hx ht
  have hs : 0 ≤ x * t := by linarith
  have hG₁ := le_besselJ0_of_nonneg ht
  have hG₂ := le_besselJ0_of_nonneg hs

  rcases le_or_gt t 3 with h | h₁
  · linarith [le_besselJ0_of_le_three ht h]
  rcases le_or_gt (24 / 5) t with h | h₂
  · linarith [le_besselJ0_of_twenty_four_fifths_le h]
  rcases le_or_gt (x * t) 3 with h | h₃
  · linarith [le_besselJ0_of_le_three hs h]
  rcases le_or_gt (24 / 5) (x * t) with h | h₄
  · linarith [le_besselJ0_of_twenty_four_fifths_le h]

  have hJ₁ := antitoneOn_besselJ0_zero_fifteen_quarters ⟨by linarith, by linarith⟩
    ⟨by norm_num, by norm_num⟩ (by linarith : t ≤ 16 / 5)
  have hJ₂ := monotoneOn_besselJ0_nine_halves_sixty_one_tenths ⟨le_rfl, by norm_num⟩
    ⟨by linarith, by linarith⟩ (by linarith : 9 / 2 ≤ x * t)
  linarith [besselJ0_sixteen_fifths, besselJ0_nine_halves]
end Erdos173

end
end

-- Erdos173.Transfer.MeasurableField
section
section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace Erdos173.Transfer

private noncomputable def gridPt (m : ℕ) (z : ℤ × ℤ) : ℂ := ⟨(z.1 : ℝ) / m, (z.2 : ℝ) / m⟩

private noncomputable def gridCell (m : ℕ) (p : ℂ) : ℤ × ℤ := (⌊p.re * m⌋, ⌊p.im * m⌋)

theorem measurable_gridCell (m : ℕ) : Measurable (gridCell m) :=
  ((Complex.measurable_re.mul_const _).floor).prodMk ((Complex.measurable_im.mul_const _).floor)

theorem floor_div_close (m : ℕ) (hm : 0 < m) (x : ℝ) :
    |(⌊x * m⌋ : ℝ) / m - x| ≤ 1 / m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have e : (⌊x * m⌋ : ℝ) / m - x = ((⌊x * m⌋ : ℝ) - x * m) / m := by
    field_simp
  rw [e, abs_div, abs_of_pos hm', div_le_div_iff_of_pos_right hm', abs_le]
  have h1 := Int.floor_le (x * m)
  have h2 := Int.lt_floor_add_one (x * m)
  constructor <;> linarith

theorem dist_gridPt_le (m : ℕ) (hm : 0 < m) (p : ℂ) :
    dist (gridPt m (gridCell m p)) p ≤ 2 / m := by
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have a := floor_div_close m hm p.re
  have b := floor_div_close m hm p.im
  simp only [gridPt, gridCell, Complex.sub_re, Complex.sub_im]
  have : (2:ℝ) / m = 1 / m + 1 / m := by ring
  rw [this]
  exact add_le_add a b

theorem mesh_choice {E : Type*} [PseudoMetricSpace E] (f : ℂ → E) (hf : Continuous f) (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ p : ℂ, ‖p‖ ≤ n →
      dist (f (gridPt m (gridCell m p))) (f p) < ((1:ℝ)/4)^n := by
  have hK : IsCompact (Metric.closedBall (0:ℂ) (n+1)) := isCompact_closedBall _ _
  have hu := hK.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hδf⟩ := hu (((1:ℝ)/4)^n) (by positivity)
  have hmin : 0 < min δ 1 := lt_min hδ one_pos
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / min δ 1)
  have hmpos : (0:ℝ) < m := lt_trans (by positivity) hm
  have hm0 : 0 < m := by exact_mod_cast hmpos
  have small : 2 / (m:ℝ) < min δ 1 := by
    rw [div_lt_iff₀ hmpos]
    rw [div_lt_iff₀ hmin] at hm
    linarith [mul_comm (m:ℝ) (min δ 1)]
  have hl := min_le_left δ 1
  have hr := min_le_right δ 1
  refine ⟨m, hm0, fun p hp => ?_⟩
  have hd := dist_gridPt_le m hm0 p
  have tri : ‖gridPt m (gridCell m p)‖ ≤ ‖p‖ + dist (gridPt m (gridCell m p)) p := by
    rw [dist_eq_norm]
    have := norm_add_le (gridPt m (gridCell m p) - p) p
    rw [sub_add_cancel] at this
    linarith
  apply hδf
  · rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  · rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  · linarith

theorem measurable_version {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (f : ℂ → Lp ℂ 2 ν)
    (hf : Continuous f) : ∃ F : ℂ × Ω → ℂ, Measurable F ∧
      ∀ p : ℂ, (fun ω => F (p, ω)) =ᵐ[ν] f p := by
  choose m hm0 hm using mesh_choice f hf
  let G : ℕ → ℂ × Ω → ℂ := fun n z => f (gridPt (m n) (gridCell (m n) z.1)) z.2
  have hG : ∀ n, Measurable (G n) := by
    intro n
    have h1 : Measurable (fun w : (ℤ × ℤ) × Ω => f (gridPt (m n) w.1) w.2) :=
      measurable_from_prod_countable_right
        (fun x => (Lp.stronglyMeasurable (f (gridPt (m n) x))).measurable)
    exact h1.comp (((measurable_gridCell (m n)).comp measurable_fst).prodMk measurable_snd)
  refine ⟨fun z => limUnder atTop (fun n => G n z),
    (StronglyMeasurable.limUnder (fun n => (hG n).stronglyMeasurable)).measurable, fun p => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_ge ‖p‖
  let s : ℕ → Set Ω := fun n => if N ≤ n then
    {ω | ENNReal.ofReal (((1:ℝ)/2)^n) ≤ ‖f (gridPt (m n) (gridCell (m n) p)) ω - f p ω‖ₑ} else ∅
  have hs : ∀ n, ν (s n) ≤ ENNReal.ofReal (((1:ℝ)/4)^n) := by
    intro n
    by_cases hn : N ≤ n
    · simp only [s, if_pos hn]
      set η := ENNReal.ofReal (((1:ℝ)/2)^n) with hη
      have cheb := mul_meas_ge_le_pow_eLpNorm' ν (p := 2) two_ne_zero ENNReal.ofNat_ne_top
        ((Lp.aestronglyMeasurable (f (gridPt (m n) (gridCell (m n) p)))).sub
          (Lp.aestronglyMeasurable (f p))) η
      rw [← Lp.edist_def] at cheb
      have hd := hm n p (hN.trans (by exact_mod_cast hn))
      have he := (edist_lt_ofReal.mpr hd).le
      have hq : ENNReal.ofReal (((1:ℝ)/4)^n) = η^2 := by
        rw [hη, ← ENNReal.ofReal_pow (by positivity), ← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [hq] at he ⊢
      have hη0 : η ≠ 0 := by
        rw [hη, Ne, ENNReal.ofReal_eq_zero, not_le]
        positivity
      have hηt : η ≠ ⊤ := ENNReal.ofReal_ne_top
      have h2 : η^2 * ν {ω | η ≤ ‖f (gridPt (m n) (gridCell (m n) p)) ω - f p ω‖ₑ} ≤
          η^2 * η^2 := by
        have t2 : (2:ℝ≥0∞).toReal = (2:ℝ) := by norm_num
        rw [t2, ENNReal.rpow_two, ENNReal.rpow_two] at cheb
        calc _ ≤ _ := cheb
          _ ≤ (η^2)^2 := by gcongr
          _ = η^2 * η^2 := sq _
      exact (ENNReal.mul_le_mul_iff_right (pow_ne_zero 2 hη0) (ENNReal.pow_ne_top hηt)).mp h2
    · simp [s, hn]
  have hsum : (∑' n, ν (s n)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hs)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  show limUnder atTop (fun n => G n (p, ω)) = f p ω
  apply Tendsto.limUnder_eq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1:ℝ)/2) (by norm_num) (by norm_num))
  filter_upwards [hω, eventually_ge_atTop N] with n hn hNn
  simp only [s, if_pos hNn, Set.mem_ofPred_eq, not_le] at hn
  rw [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hn
  exact hn.le

end Erdos173.Transfer

end
end

-- Erdos173.Transfer.SampleNear
section
section
open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace Erdos173.Transfer

theorem qform_nonneg {a b c : ℝ} (ha : -1 ≤ a ∧ a ≤ 1) (hb : -1 ≤ b ∧ b ≤ 1)
    (hc : -1 ≤ c ∧ c ≤ 1) : 0 ≤ 1 + a * b + a * c + b * c := by
  have h1 : 0 ≤ (1 + a) * (1 + b) * (1 + c) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h2 : 0 ≤ (1 - a) * (1 - b) * (1 - c) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  nlinarith

theorem re_inner_eq (z w : ℂ) : (inner ℂ z w).re = z.re * w.re + z.im * w.im := by
  rw [RCLike.inner_apply']
  simp [Complex.mul_re]

theorem re_inner_L2 {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} (X Y : Lp ℂ 2 ν) :
    (inner ℂ X Y).re = ∫ ω, ((X ω).re * (Y ω).re + (X ω).im * (Y ω).im) ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  have h := integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) X Y)
  simp only [RCLike.re_to_complex, re_inner_eq] at h
  exact h.symm

theorem integrable_g {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω} (X Y : Lp ℂ 2 ν) :
    Integrable (fun ω => (X ω).re * (Y ω).re + (X ω).im * (Y ω).im) ν := by
  have h := (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) X Y).re
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [RCLike.re_to_complex, re_inner_eq]

theorem ae_zero_of_integral {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {f1 f2 f3 : Ω → ℝ}
    (i1 : Integrable f1 ν) (i2 : Integrable f2 ν) (i3 : Integrable f3 ν)
    (h : 1 + ∫ ω, f1 ω ∂ν + ∫ ω, f2 ω ∂ν + ∫ ω, f3 ω ∂ν = 0)
    (hnn : ∀ᵐ ω ∂ν, 0 ≤ 1 + f1 ω + f2 ω + f3 ω) :
    ∀ᵐ ω ∂ν, 1 + f1 ω + f2 ω + f3 ω = 0 := by
  have j0 : Integrable (fun _ : Ω => (1 : ℝ)) ν := integrable_const _
  have j1 : Integrable (fun ω => 1 + f1 ω) ν := j0.add i1
  have j2 : Integrable (fun ω => 1 + f1 ω + f2 ω) ν := j1.add i2
  have hint : Integrable (fun ω => 1 + f1 ω + f2 ω + f3 ω) ν := j2.add i3
  have hsum : ∫ ω, (1 + f1 ω + f2 ω + f3 ω) ∂ν = 0 := by
    rw [integral_add (f := fun ω => 1 + f1 ω + f2 ω) (g := f3) j2 i3,
      integral_add (f := fun ω => 1 + f1 ω) (g := f2) j1 i2,
      integral_add (f := fun _ => (1 : ℝ)) (g := f1) j0 i1]
    simpa using h
  have hz := (integral_eq_zero_iff_of_nonneg_ae (f := fun ω => 1 + f1 ω + f2 ω + f3 ω)
    hnn hint).mp hsum
  filter_upwards [hz] with ω hω
  simpa using hω

theorem quadratic_relation {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (A B C : Lp ℂ 2 ν)
    (hA : ∀ᵐ ω ∂ν, (A ω).im = 0 ∧ -1 ≤ (A ω).re ∧ (A ω).re ≤ 1)
    (hB : ∀ᵐ ω ∂ν, (B ω).im = 0 ∧ -1 ≤ (B ω).re ∧ (B ω).re ≤ 1)
    (hC : ∀ᵐ ω ∂ν, (C ω).im = 0 ∧ -1 ≤ (C ω).re ∧ (C ω).re ≤ 1)
    (h0 : (1 + inner ℂ A B + inner ℂ A C + inner ℂ B C).re = 0) :
    ∀ᵐ ω ∂ν, 1 + (A ω).re * (B ω).re + (A ω).re * (C ω).re + (B ω).re * (C ω).re = 0 := by
  simp only [Complex.add_re, Complex.one_re, re_inner_L2] at h0
  have hz := ae_zero_of_integral (integrable_g A B)
    (integrable_g A C) (integrable_g B C) h0 (by
      filter_upwards [hA, hB, hC] with ω ha hb hc
      simp only [ha.1, hb.1, hc.1, mul_zero, add_zero]
      exact qform_nonneg ha.2 hb.2 hc.2)
  filter_upwards [hz, hA, hB, hC] with ω h ha hb hc
  simpa [ha.1, hb.1, hc.1] using h

private theorem two_signs {a b d : ℝ} (h : 1 + a * b + a * d + b * d = 0) :
    let color (z : ℝ) : Fin 2 := if 0 ≤ z then 0 else 1
    ¬ (color b = color a ∧ color d = color a) := by
  dsimp
  intro ⟨hb, hd⟩
  by_cases ha : 0 ≤ a <;> by_cases hb' : 0 ≤ b <;> by_cases hd' : 0 ≤ d <;>
    simp [ha, hb', hd'] at hb hd
  · nlinarith [mul_nonneg ha hb', mul_nonneg ha hd', mul_nonneg hb' hd']
  · have ha' : a < 0 := lt_of_not_ge ha
    have hb'' : b < 0 := lt_of_not_ge hb'
    have hd'' : d < 0 := lt_of_not_ge hd'
    nlinarith [mul_pos_of_neg_of_neg ha' hb'', mul_pos_of_neg_of_neg ha' hd'',
      mul_pos_of_neg_of_neg hb'' hd'']

theorem sample_near_field {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : ℂ → Lp ℂ 2 ν) (hf : Continuous f) {x : ℝ}
    (hbounded : ∀ p : ℂ, ∀ᵐ ω ∂ν, (f p ω).im = 0 ∧ -1 ≤ (f p ω).re ∧ (f p ω).re ≤ 1)
    (hcorrelation : ∀ r : ℝ, (r = 1 ∨ r = x) → ∀ p : ℂ, ∀ u : Circle,
      (1 + inner ℂ (f p) (f (p + u * r)) + inner ℂ (f p) (f (p + u * (r * ζ))) +
        inner ℂ (f (p + u * r)) (f (p + u * (r * ζ)))).re = 0) :
    ∃ d : ℂ → Fin 2, Measurable d ∧ WeaklyAvoidsEq d 1 ∧ WeaklyAvoidsEq d x := by
  obtain ⟨F, hF, hversion⟩ := measurable_version ν f hf
  have hrel (r : ℝ) (hr : r = 1 ∨ r = x) (p : ℂ) (u : Circle) :=
    quadratic_relation ν (f p) (f (p + u * r)) (f (p + u * (r * ζ)))
      (hbounded p) (hbounded _) (hbounded _) (hcorrelation r hr p u)
  let ζ : ℂ := ⟨1 / 2, √3 / 2⟩
  let color (t : ℝ) : Fin 2 := if 0 ≤ t then 0 else 1
  let col (z : ℂ × Ω) := color (F z).re
  have hcolor : Measurable color := Measurable.ite measurableSet_Ici measurable_const measurable_const
  have hcol : Measurable col := hcolor.comp (Complex.measurable_re.comp hF)
  let Ang := AddCircle (2 * Real.pi)
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let M := (volume : Measure ℂ).prod (AddCircle.haarAddCircle : Measure Ang)
  let mono (r : ℝ) (q : (ℂ × Ang) × Ω) :=
    let u : ℂ := AddCircle.toCircle q.1.2
    col (q.1.1 + u * r, q.2) = col (q.1.1, q.2) ∧
      col (q.1.1 + u * (r * ζ), q.2) = col (q.1.1, q.2)
  have hm (r : ℝ) : MeasurableSet {q | ¬ mono r q} := by
    have hp : Measurable fun q : (ℂ × Ang) × Ω => q.1.1 := measurable_fst.fst
    have hu : Measurable fun q : (ℂ × Ang) × Ω => (AddCircle.toCircle q.1.2 : ℂ) :=
      (continuous_subtype_val.comp AddCircle.continuous_toCircle).measurable.comp measurable_fst.snd
    have h0 := hcol.comp (hp.prodMk measurable_snd)
    have h1 := hcol.comp ((hp.add (hu.mul_const (r : ℂ))).prodMk measurable_snd)
    have h2 := hcol.comp ((hp.add (hu.mul_const ((r : ℂ) * ζ))).prodMk measurable_snd)
    exact ((measurableSet_eq_fun h1 h0).inter (measurableSet_eq_fun h2 h0)).compl
  have ha (q : ℂ × Ang) (r : ℝ) (hr : r = 1 ∨ r = x) : ∀ᵐ ω ∂ν, ¬ mono r (q,ω) := by
    let u := AddCircle.toCircle q.2
    filter_upwards [hrel r hr q.1 u, hversion q.1, hversion (q.1 + u * r),
        hversion (q.1 + u * (r * ζ))] with ω hq h0 h1 h2
    change ¬ (color (F (_,ω)).re = color (F (_,ω)).re ∧ color (F (_,ω)).re = color (F (_,ω)).re)
    change F (_,ω) = _ at h0 h1 h2
    rw [h0, h1, h2]
    exact two_signs hq
  have hmBoth : MeasurableSet {q : (ℂ × Ang) × Ω | ¬ mono 1 q ∧ ¬ mono x q} := (hm 1).inter (hm x)
  have ht := (Measure.ae_ae_comm (μ := M) (ν := ν) hmBoth).mp
    (Filter.Eventually.of_forall fun q => (ha q 1 (Or.inl rfl)).and (ha q x (Or.inr rfl)))
  obtain ⟨ω, hω⟩ := ht.exists
  exact ⟨fun z => col (z,ω), hcol.comp (measurable_id.prodMk measurable_const),
    hω.mono fun _ h => h.1, hω.mono fun _ h => h.2⟩

end Erdos173.Transfer

end
end

namespace OMA.R_Erdos173_erdos_173_R1_H2_R1

open MeasureTheory

set_option maxHeartbeats 800000 in
theorem normalized_suffices
    (exclude : ∀ x : ℝ, 0 < x → x ≠ 1 → ∀ c : ℂ → Fin 2,
      (∀ p u : ℂ, ‖u‖ = 1 →
        ¬ (c (p + u * (1 : ℝ)) = c p ∧
          c (p + u * ((1 : ℝ) * (⟨1 / 2, √3 / 2⟩ : ℂ))) = c p)) →
      (∀ p u : ℂ, ‖u‖ = 1 →
        ¬ (c (p + u * x) = c p ∧
          c (p + u * (x * (⟨1 / 2, √3 / 2⟩ : ℂ))) = c p)) →
      False) : OMA.R_Erdos173_erdos_173_R1.H2 := by
  intro c s t hs ht missS missT
  by_contra hst
  let x := t / s
  have hx : 0 < x := div_pos ht hs
  have hx1 : x ≠ 1 := by simpa [x, div_eq_one_iff_eq hs.ne'] using Ne.symm hst
  let ζ : ℂ := ⟨1 / 2, √3 / 2⟩
  have hζ : ‖ζ‖ = 1 := by
    rw [Complex.norm_def, Real.sqrt_eq_one]
    simp [ζ, Complex.normSq]
    ring_nf
    norm_num
  have hζ' : ‖1 - ζ‖ = 1 := by
    rw [Complex.norm_def, Real.sqrt_eq_one]
    simp [ζ, Complex.normSq]
    ring_nf
    norm_num
  let e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  let d (z : ℂ) := c (e ((s : ℂ) * z))
  have miss (r : ℝ) (hr : 0 < r)
      (h : ∀ v : Fin 3 → EuclideanSpace ℝ (Fin 2),
        (∀ i j, i ≠ j → dist (v i) (v j) = s*r) → ¬ ∃ k, ∀ i, c (v i) = k)
      (p u : ℂ) (hu : ‖u‖ = 1) :
      ¬ (d (p + u * r) = d p ∧ d (p + u * (r * ζ)) = d p) := by
    rintro ⟨h₁, h₂⟩
    let f (z : ℂ) := e ((s : ℂ) * (p + u * ((r : ℂ) * z)))
    have hf (a b : ℂ) : dist (f a) (f b) = s * r * ‖a - b‖ := by
      rw [LinearIsometryEquiv.dist_map, dist_eq_norm]
      simp only [← mul_sub, add_sub_add_left_eq_sub, norm_mul, hu, one_mul,
        Complex.norm_real, Real.norm_of_nonneg hs.le, Real.norm_of_nonneg hr.le]
      ring
    let v : Fin 3 → EuclideanSpace ℝ (Fin 2) := fun i => f (![0,1,ζ] i)
    apply h v
    · intro i j hij
      change dist (f _) (f _) = _
      rw [hf]
      fin_cases i <;> fin_cases j <;> simp [hζ, hζ', norm_sub_rev ζ 1] at hij ⊢
    · refine ⟨d p, ?_⟩
      intro i
      fin_cases i
      · simp [v, f, d]
      · simpa [v, f, d] using h₁
      · simpa [v, f, d] using h₂
  have one := miss 1 zero_lt_one (by simpa using missS)
  have other := miss x hx (by simpa [x, mul_div_cancel₀ _ hs.ne'] using missT)
  exact exclude x hx hx1 d one other
end OMA.R_Erdos173_erdos_173_R1_H2_R1

namespace OMA.R_Erdos173_erdos_173_R1_H2_R2

open MeasureTheory Set Erdos173 OAI.EuclideanFiveColor
open scoped InnerProductSpace

private theorem far_measure_exclusion {x : ℝ} (hx : 0 < x)
    (hfar : 3 / 2 ≤ x ∨ x ≤ 2 / 3) (ν : Measure ℂ) [IsFiniteMeasure ν]
    (hmass : ν.real univ ≤ 1)
    (hmom : (∫ ξ : ℂ, (besselJ0 ‖ξ‖ + besselJ0 (x * ‖ξ‖)) ∂ν) ≤ -2 / 3) : False := by
  have hint (s : ℝ) : Integrable (fun ξ : ℂ => besselJ0 (s * ‖ξ‖)) ν :=
    (integrable_const (1 : ℝ)).mono'
      (continuous_besselJ0.comp (continuous_const.mul continuous_norm)).aestronglyMeasurable
      (ae_of_all _ fun ξ => abs_besselJ0_le_one _)
  have hint₁ : Integrable (fun ξ : ℂ => besselJ0 ‖ξ‖) ν := by simpa using hint 1
  have hlow (ξ : ℂ) : -83 / 125 ≤ besselJ0 ‖ξ‖ + besselJ0 (x * ‖ξ‖) := by
    rcases hfar with h | h
    · exact besselJ0_add_lower h (norm_nonneg ξ)
    · have h' : 3 / 2 ≤ 1 / x := by rw [le_div_iff₀ hx]; linarith
      have hb := besselJ0_add_lower h' (mul_nonneg hx.le (norm_nonneg ξ))
      rw [← mul_assoc, one_div_mul_cancel hx.ne', one_mul] at hb
      linarith
  have hi := integral_mono (integrable_const (-83 / 125 : ℝ)) (hint₁.add (hint x)) hlow
  simp only [Pi.add_apply] at hi
  rw [integral_const, smul_eq_mul] at hi
  linarith [hi.trans hmom]

/-- The distant-scale spectral input. Only the sum of the two correlations is needed. -/
def H1 : Prop :=
  let J (t : ℝ) := (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos (t * Real.cos θ)
  let w : ℂ := ⟨1 / 2, √3 / 2⟩
  let avoids (c : ℂ → Fin 2) (r : ℝ) := ∀ p u : ℂ, ‖u‖ = 1 →
    ¬ (c (p + u * r) = c p ∧ c (p + u * (r * w)) = c p)
  ∀ x : ℝ, 0 < x → (3 / 2 ≤ x ∨ x ≤ 2 / 3) →
    ∀ c : ℂ → Fin 2, avoids c 1 → avoids c x →
      ∃ ν : Measure ℂ, IsFiniteMeasure ν ∧ ν.real univ ≤ 1 ∧
        (∫ ξ : ℂ, (J ‖ξ‖ + J (x * ‖ξ‖)) ∂ν) ≤ -2 / 3

/-- The nearby-scale continuous sign-field input. -/
def H2 : Prop :=
  let w : ℂ := ⟨1 / 2, √3 / 2⟩
  let avoids (c : ℂ → Fin 2) (r : ℝ) := ∀ p u : ℂ, ‖u‖ = 1 →
    ¬ (c (p + u * r) = c p ∧ c (p + u * (r * w)) = c p)
  ∀ x : ℝ, 2 / 3 < x → x < 3 / 2 → x ≠ 1 →
    ∀ c : ℂ → Fin 2, avoids c 1 → avoids c x →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (ν : Measure Ω), IsProbabilityMeasure ν ∧
        ∃ f : ℂ → Lp ℂ 2 ν, Continuous f ∧
          (∀ p : ℂ, ∀ᵐ ω ∂ν, (f p ω).im = 0 ∧ -1 ≤ (f p ω).re ∧ (f p ω).re ≤ 1) ∧
          ∀ r : ℝ, (r = 1 ∨ r = x) → ∀ p : ℂ, ∀ u : Circle,
            (1 + inner ℂ (f p) (f (p + u * r)) + inner ℂ (f p) (f (p + u * (r * w))) +
              inner ℂ (f (p + u * r)) (f (p + u * (r * w)))).re = 0

theorem main : H1 → H2 → OMA.R_Erdos173_erdos_173_R1.H2 := by
  intro spectrum transfer
  apply OMA.R_Erdos173_erdos_173_R1_H2_R1.normalized_suffices
  intro x hx hx1 c h₁ h₂
  by_cases hfar : 3 / 2 ≤ x ∨ x ≤ 2 / 3
  · obtain ⟨ν, hν, hmass, hmom⟩ := spectrum x hx hfar c h₁ h₂
    letI := hν
    exact far_measure_exclusion hx hfar ν hmass hmom
  · push Not at hfar
    obtain ⟨Ω, mΩ, ν, hν, f, hf, hbounded, hcorrelation⟩ :=
      transfer x hfar.2 hfar.1 hx1 c h₁ h₂
    letI : MeasurableSpace Ω := mΩ
    letI : IsProbabilityMeasure ν := hν
    obtain ⟨d, hd, ha, hb⟩ := Erdos173.Transfer.sample_near_field ν f hf hbounded hcorrelation
    exact circle_exclusion hfar.2 hfar.1 hx1 d hd ha hb

end OMA.R_Erdos173_erdos_173_R1_H2_R2

