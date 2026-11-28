import OMAStatements.S_mse_490449
import Mathlib
open MeasureTheory Filter Topology

namespace G490449

variable {Ω : Type} [MeasurableSpace Ω]

/-- The level set where `⌊k f⌋ = j`. -/
def lev (f : Ω → ℝ) (k : ℕ) (j : ℤ) : Set Ω := (fun y => ⌊(k : ℝ) * f y⌋) ⁻¹' {j}

/-- The step function `⌊k f⌋ / k`, written as a finite sum of indicators. -/
noncomputable def step (f : Ω → ℝ) (C : ℝ) (k : ℕ) (x : Ω) : ℝ :=
  ∑ j ∈ Finset.Icc (-(⌈(k : ℝ) * C⌉ + 1)) (⌈(k : ℝ) * C⌉ + 1),
    ((j : ℝ) / k) * (lev f k j).indicator 1 x

lemma lev_meas {f : Ω → ℝ} (hf : Measurable f) (k : ℕ) (j : ℤ) : MeasurableSet (lev f k j) :=
  ((hf.const_mul (k : ℝ)).floor) (measurableSet_singleton j)

lemma step_eq (f : Ω → ℝ) (C : ℝ) (hC : ∀ x, |f x| ≤ C) (k : ℕ) (x : Ω) :
    step f C k x = (⌊(k : ℝ) * f x⌋ : ℝ) / k := by
  unfold step
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hb := abs_le.mp (hC x)
  have h1 : (k : ℝ) * f x ≤ k * C := mul_le_mul_of_nonneg_left hb.2 hk
  have h2 : -((k : ℝ) * C) ≤ k * f x := by nlinarith [hb.1]
  have hmem : ⌊(k : ℝ) * f x⌋ ∈ Finset.Icc (-(⌈(k : ℝ) * C⌉ + 1)) (⌈(k : ℝ) * C⌉ + 1) := by
    rw [Finset.mem_Icc]
    constructor
    · have := Int.lt_floor_add_one ((k : ℝ) * f x)
      have h3 := Int.le_ceil ((k : ℝ) * C)
      have : (-(⌈(k : ℝ) * C⌉ + 1) : ℝ) < ⌊(k : ℝ) * f x⌋ := by linarith
      exact_mod_cast this.le
    · have := Int.floor_le ((k : ℝ) * f x)
      have h3 := Int.le_ceil ((k : ℝ) * C)
      have : (⌊(k : ℝ) * f x⌋ : ℝ) ≤ (⌈(k : ℝ) * C⌉ + 1 : ℤ) := by push_cast; linarith
      exact_mod_cast this
  rw [Finset.sum_eq_single_of_mem _ hmem]
  · simp [lev, Set.indicator]
  · intro j _ hj
    have : x ∉ lev f k j := by
      simp only [lev, Set.mem_preimage, Set.mem_singleton_iff]
      exact fun h => hj h.symm
    simp [Set.indicator_of_notMem this]

lemma step_close (f : Ω → ℝ) (C : ℝ) (hC : ∀ x, |f x| ≤ C) (k : ℕ) (hk : 0 < k) (x : Ω) :
    |f x - step f C k x| ≤ 1 / k := by
  rw [step_eq f C hC]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have a1 := Int.floor_le ((k : ℝ) * f x)
  have a2 := Int.lt_floor_add_one ((k : ℝ) * f x)
  have e : f x - (⌊(k : ℝ) * f x⌋ : ℝ) / k = ((k : ℝ) * f x - ⌊(k : ℝ) * f x⌋) / k := by
    field_simp
  rw [e, abs_of_nonneg (div_nonneg (by linarith) hk'.le)]
  exact div_le_div_of_nonneg_right (by linarith) hk'.le

lemma step_meas {f : Ω → ℝ} (hf : Measurable f) (C : ℝ) (k : ℕ) : Measurable (step f C k) := by
  unfold step
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_const.indicator (lev_meas hf k j)).const_mul _

lemma integral_step (ν : Measure Ω) [IsFiniteMeasure ν] {f : Ω → ℝ} (hf : Measurable f) (C : ℝ)
    (k : ℕ) :
    ∫ x, step f C k x ∂ν = ∑ j ∈ Finset.Icc (-(⌈(k : ℝ) * C⌉ + 1)) (⌈(k : ℝ) * C⌉ + 1),
      ((j : ℝ) / k) * (ν (lev f k j)).toReal := by
  unfold step
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_indicator_one (lev_meas hf k j)]
    rfl
  · intro j _
    exact ((integrable_const (1 : ℝ)).indicator (lev_meas hf k j)).const_mul _

lemma integrable_bdd (ν : Measure Ω) [IsFiniteMeasure ν] {f : Ω → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) : Integrable f ν :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

lemma close_integral (ν : Measure Ω) [IsFiniteMeasure ν] {f : Ω → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) (k : ℕ) (hk : 0 < k) :
    |∫ x, f x ∂ν - ∫ x, step f C k x ∂ν| ≤ 1 / k * (ν Set.univ).toReal := by
  have hfi := integrable_bdd ν hf C hC
  have hgi : Integrable (step f C k) ν := by
    refine integrable_bdd ν (step_meas hf C k) (C + 1 / k) fun x => ?_
    have := step_close f C hC k hk x
    have h2 := hC x
    calc |step f C k x| = |f x - (f x - step f C k x)| := by ring_nf
      _ ≤ |f x| + |f x - step f C k x| := abs_sub _ _
      _ ≤ C + 1 / k := by linarith
  rw [← integral_sub hfi hgi]
  have := norm_integral_le_of_norm_le_const (μ := ν) (C := 1 / (k : ℝ))
    (f := fun x => f x - step f C k x) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact step_close f C hC k hk x)
  rw [Real.norm_eq_abs] at this
  exact this

theorem forward (μ : ℕ → Measure Ω) (μ₀ : Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    [IsFiniteMeasure μ₀]
    (hA : ∀ A : Set Ω, MeasurableSet A → Tendsto (fun n => (μ n A).toReal) atTop (𝓝 (μ₀ A).toReal))
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂μ₀)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M : ℝ := (μ₀ Set.univ).toReal + 1 with hM
  have hM0 : 0 < M := by positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (4 * M / ε)
  have hkpos' : (0 : ℝ) < k := lt_trans (by positivity) hk
  have hkpos : 0 < k := by exact_mod_cast hkpos'
  have hMk : 4 * M < k * ε := by
    have := (div_lt_iff₀ hε).mp hk
    linarith
  -- eventually the total mass is below `M`
  have hev1 : ∀ᶠ n in atTop, (μ n Set.univ).toReal < M :=
    (hA Set.univ MeasurableSet.univ).eventually (gt_mem_nhds (by linarith))
  -- the step-function integrals converge
  have hg : Tendsto (fun n => ∫ x, step f C k x ∂(μ n)) atTop (𝓝 (∫ x, step f C k x ∂μ₀)) := by
    simp only [integral_step _ hf C k]
    refine tendsto_finsetSum _ fun j _ => ?_
    exact (hA _ (lev_meas hf k j)).const_mul _
  have hev2 : ∀ᶠ n in atTop,
      dist (∫ x, step f C k x ∂(μ n)) (∫ x, step f C k x ∂μ₀) < ε / 2 :=
    (Metric.tendsto_nhds.mp hg) (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := (hev1.and hev2).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  rw [Real.dist_eq] at h2 ⊢
  have e1 := close_integral (μ n) hf C hC k hkpos
  have e2 := close_integral μ₀ hf C hC k hkpos
  have hm0 : 0 ≤ (μ n Set.univ).toReal := ENNReal.toReal_nonneg
  have b1 : 1 / (k : ℝ) * (μ n Set.univ).toReal ≤ 1 / k * M :=
    mul_le_mul_of_nonneg_left h1.le (by positivity)
  have b2 : 1 / (k : ℝ) * (μ₀ Set.univ).toReal ≤ 1 / k * M :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have b3 : 1 / (k : ℝ) * M < ε / 4 := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hkpos']
    linarith
  calc |∫ x, f x ∂(μ n) - ∫ x, f x ∂μ₀|
      = |(∫ x, f x ∂(μ n) - ∫ x, step f C k x ∂(μ n)) +
          (∫ x, step f C k x ∂(μ n) - ∫ x, step f C k x ∂μ₀) -
          (∫ x, f x ∂μ₀ - ∫ x, step f C k x ∂μ₀)| := by ring_nf
    _ ≤ |∫ x, f x ∂(μ n) - ∫ x, step f C k x ∂(μ n)| +
          |∫ x, step f C k x ∂(μ n) - ∫ x, step f C k x ∂μ₀| +
          |∫ x, f x ∂μ₀ - ∫ x, step f C k x ∂μ₀| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ < ε := by linarith

theorem backward (μ : ℕ → Measure Ω) (μ₀ : Measure Ω) [∀ n, IsFiniteMeasure (μ n)]
    [IsFiniteMeasure μ₀]
    (hF : ∀ f : Ω → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
      Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂μ₀)))
    (A : Set Ω) (hA : MeasurableSet A) :
    Tendsto (fun n => (μ n A).toReal) atTop (𝓝 (μ₀ A).toReal) := by
  have h := hF (A.indicator 1) (measurable_const.indicator hA) ⟨1, fun x => by
    by_cases hx : x ∈ A <;> simp [Set.indicator, hx]⟩
  simp only [integral_indicator_one hA] at h
  exact h

end G490449

theorem OMA.solution : type_of% @OMA.S_mse_490449.main := by
  intro Ω _ μ μ₀ hμ hμ₀
  constructor
  · intro hA f hf ⟨C, hC⟩
    exact G490449.forward μ μ₀ hA f hf C hC
  · intro hF A hA
    exact G490449.backward μ μ₀ hF A hA
