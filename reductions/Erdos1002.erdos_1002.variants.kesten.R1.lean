import FormalConjectures.ErdosProblems.«1002»
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor

/-! Transfer the annealed sawtooth characteristic-function limit to the exact Cauchy CDF. -/

namespace OMA.Erdos1002Cauchy

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- The Cauchy distribution of positive scale has no atoms. -/
theorem cauchy_singleton_zero (x : ℝ) (γ : ℝ≥0) (hγ : γ ≠ 0) (c : ℝ) :
    cauchyMeasure x γ {c} = 0 := by
  rw [cauchyMeasure_of_scale_ne_zero x hγ]
  exact withDensity_absolutelyContinuous volume _ (by simp)

/-- The closed lower rays are continuity sets for the Cauchy distribution. -/
theorem cauchy_frontier_Iic_zero (γ : ℝ) (hγ : 0 < γ) (c : ℝ) :
    cauchyMeasure 0 ⟨γ, hγ.le⟩ (frontier (Iic c)) = 0 := by
  have h0 : (⟨γ, hγ.le⟩ : ℝ≥0) ≠ 0 :=
    fun h => hγ.ne' (congrArg (fun z : ℝ≥0 => (z : ℝ)) h)
  rw [frontier_Iic]
  exact cauchy_singleton_zero 0 _ h0 c

/-- The CDF of a centered Cauchy distribution, with the inverse scale in the upper limit. -/
theorem cauchy_Iic_toReal (γ : ℝ) (hγ : 0 < γ) (c : ℝ) :
    (cauchyMeasure 0 ⟨γ, hγ.le⟩ (Iic c)).toReal =
      (1 / Real.pi) * ∫ t in Iic (γ⁻¹ * c), 1 / (1 + t ^ 2) := by
  let δ : ℝ≥0 := ⟨γ, hγ.le⟩
  have hδ : δ ≠ 0 := fun h => hγ.ne' (congrArg (fun z : ℝ≥0 => (z : ℝ)) h)
  have hden : (cauchyMeasure 0 δ (Iic c)).toReal = ∫ x in Iic c, cauchyPDFReal 0 δ x := by
    rw [cauchyMeasure_of_scale_ne_zero 0 hδ, withDensity_apply _ measurableSet_Iic]
    exact (integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun x => (cauchyPDF_pos 0 hδ x).le)
      (stronglyMeasurable_cauchyPDFReal 0 δ).aestronglyMeasurable).symm
  have hImage : (fun x : ℝ => γ * x) '' Iic (γ⁻¹ * c) = Iic c := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      change t ≤ γ⁻¹ * c at ht
      change γ * t ≤ c
      simpa only [← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul] using
        (mul_le_mul_of_nonneg_left ht hγ.le)
    · intro hx
      refine ⟨γ⁻¹ * x, mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hγ.le), ?_⟩
      change γ * (γ⁻¹ * x) = x
      rw [← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul]
  have hDeriv : ∀ t ∈ Iic (γ⁻¹ * c),
      HasDerivWithinAt (fun x : ℝ => γ * x) γ (Iic (γ⁻¹ * c)) t := by
    intro t _
    simpa using ((hasDerivAt_id t).const_mul γ).hasDerivWithinAt
  have hscale : (∫ x in Iic c, cauchyPDFReal 0 δ x) =
      ∫ t in Iic (γ⁻¹ * c), |γ| • cauchyPDFReal 0 δ (γ * t) := by
    rw [← hImage]
    exact integral_image_eq_integral_abs_deriv_smul measurableSet_Iic hDeriv
      (mul_right_injective₀ hγ.ne').injOn (cauchyPDFReal 0 δ)
  have hpdf (t : ℝ) : |γ| • cauchyPDFReal 0 δ (γ * t) =
      (1 / Real.pi) * (1 / (1 + t ^ 2)) := by
    rw [abs_of_pos hγ, smul_eq_mul, cauchyPDFReal_def', sub_zero]
    change γ * (Real.pi⁻¹ * γ⁻¹ * (1 + (γ * t / γ) ^ 2)⁻¹) = _
    rw [mul_div_cancel_left₀ _ hγ.ne']
    calc
      _ = (γ * γ⁻¹) * (Real.pi⁻¹ * (1 + t ^ 2)⁻¹) := by ring
      _ = _ := by simp [mul_inv_cancel₀ hγ.ne', one_div]
  change (cauchyMeasure 0 δ (Iic c)).toReal = _
  rw [hden, hscale]
  simp only [hpdf, integral_const_mul]

end OMA.Erdos1002Cauchy

namespace OMA.R_Erdos1002_erdos_1002_variants_kesten_R1

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology ENNReal NNReal

theorem square_is_probability : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
  simp [Real.volume_Icc]

theorem index_difference (n : ℕ) (p : ℝ × ℝ) (hn : 2 ≤ n) :
    let d := 1 / Real.log (n : ℝ)
    |d * (∑ k ∈ Finset.Icc 1 n, ((1 / 2 : ℝ) - Int.fract (p.2 + p.1 * (k : ℝ)))) +
        d * (∑ k ∈ Finset.range n, (Int.fract (p.2 + p.1 * (k : ℝ)) - 1 / 2))| ≤ d := by
  let T := (1 / Real.log (n : ℝ)) *
    ∑ k ∈ Finset.Icc 1 n, ((1 / 2 : ℝ) - Int.fract (p.2 + p.1 * (k : ℝ)))
  let S := (1 / Real.log (n : ℝ)) *
    ∑ k ∈ Finset.range n, (Int.fract (p.2 + p.1 * (k : ℝ)) - 1 / 2)
  change |T + S| ≤ 1 / Real.log (n : ℝ)
  let a (k : ℕ) := Int.fract (p.2 + p.1 * (k : ℝ)) - (1 / 2 : ℝ)
  have hidx : insert 0 (Finset.Icc 1 n) = Finset.range (n + 1) := by
    ext i
    simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_range]
    omega
  have hsum : a 0 + ∑ k ∈ Finset.Icc 1 n, a k =
      (∑ k ∈ Finset.range n, a k) + a n := by
    rw [← Finset.sum_insert (show 0 ∉ Finset.Icc 1 n by simp), hidx, Finset.sum_range_succ]
  have hd : T + S =
      (1 / Real.log (n : ℝ)) * (a 0 - a n) := by
    dsimp [T, S]
    have he : ∑ k ∈ Finset.Icc 1 n, ((1 / 2 : ℝ) - Int.fract (p.2 + p.1 * (k : ℝ))) =
        -(∑ k ∈ Finset.Icc 1 n, a k) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by simp [a]
    rw [he, ← mul_add]
    congr 1
    linarith only [hsum]
  have hlog : 0 < 1 / Real.log (n : ℝ) := by
    apply one_div_pos.mpr (Real.log_pos _)
    exact_mod_cast (show 1 < n by omega)
  have ha (k : ℕ) : -(1 / 2 : ℝ) ≤ a k ∧ a k ≤ 1 / 2 := by
    have h0 := Int.fract_nonneg (p.2 + p.1 * (k : ℝ))
    have h1 := Int.fract_lt_one (p.2 + p.1 * (k : ℝ))
    dsimp [a]
    constructor <;> linarith
  have hb : |a 0 - a n| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(ha n).1, (ha n).2, (ha 0).1, (ha 0).2]
  rw [hd, abs_mul, abs_of_pos hlog]
  simpa using mul_le_mul_of_nonneg_left hb hlog.le

theorem exp_ofReal_diff_le (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ |x - y| := by
  have heq : Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I) =
      (Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) - 1) * Complex.exp ((y : ℂ) * Complex.I) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    push_cast
    congr 2
    ring
  rw [heq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, mul_comm _ Complex.I]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)

theorem charFun_map_apply {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : Measurable X) (t : ℝ) :
    charFun (μ.map X) t = ∫ a, Complex.exp ((t : ℂ) * (X a : ℂ) * Complex.I) ∂μ := by
  rw [charFun_apply_real, integral_map hX.aemeasurable (by fun_prop)]

theorem char_difference_of_uniform {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (t ε : ℝ) (h : ∀ x, |X x - Y x| ≤ ε) :
    ‖charFun (μ.map X) t - charFun (μ.map Y) t‖ ≤ |t| * ε := by
  rw [charFun_map_apply hX, charFun_map_apply hY]
  have hInt (Z : Ω → ℝ) (hZ : Measurable Z) :
      Integrable (fun z => Complex.exp ((t : ℂ) * (Z z : ℂ) * Complex.I)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) (by
      exact (show Measurable (fun z => Complex.exp ((t : ℂ) * (Z z : ℂ) * Complex.I)) by fun_prop)
        |>.aestronglyMeasurable) (ae_of_all _ fun z => ?_)
    rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  rw [← integral_sub (hInt X hX) (hInt Y hY)]
  have hA : ∀ x : Ω, ‖Complex.exp ((t : ℂ) * (X x : ℂ) * Complex.I) -
      Complex.exp ((t : ℂ) * (Y x : ℂ) * Complex.I)‖ ≤ |t| * ε := by
    intro x
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    refine (exp_ofReal_diff_le (t * X x) (t * Y x)).trans ?_
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (h x) (abs_nonneg _)
  have hb := norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ hA)
  simpa using hb

theorem reciprocal_log_tendsto : Tendsto
    (fun n : ℕ => (1 : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) := by
  simp only [one_div]
  change Tendsto ((fun r : ℝ => r⁻¹) ∘ Real.log ∘ fun n : ℕ => (n : ℝ)) atTop (𝓝 0)
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private theorem half_open_square_measure :
    (volume : Measure (ℝ × ℝ)).restrict (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) =
      volume.restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  let A := Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1
  let B := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hAB : A ⊆ B := Set.prod_mono Ico_subset_Icc_self Ico_subset_Icc_self
  have hA : volume A = 1 := by
    dsimp only [A]
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp [Real.volume_Ico]
  have hB : volume B = 1 := by
    dsimp only [B]
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp [Real.volume_Icc]
  have hMeas : MeasurableSet A := measurableSet_Ico.prod measurableSet_Ico
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨by rw [sdiff_eq_empty.mpr hAB, measure_empty], ?_⟩
  rw [measure_sdiff hAB hMeas.nullMeasurableSet (by simp [hA]), hB, hA, tsub_self]

private theorem sign_reflect {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Ω → ℝ) (hX : Measurable X) (t : ℝ) :
    charFun (μ.map X) (-t) = charFun (μ.map (fun p => -X p)) t := by
  have hNeg : Measurable (fun p => -X p) := hX.neg
  rw [charFun_map_apply hX, charFun_map_apply hNeg]
  simp only [Complex.ofReal_neg, neg_mul, mul_neg]

private theorem shift_char_limit {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X Y : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n))
    (hY : ∀ n, Measurable (Y n))
    (hE : ∀ n ≥ 2, ∀ p, |Y n p + X n p| ≤ 1 / Real.log (n : ℝ))
    (g : ℝ → ℂ) (heven : ∀ t, g (-t) = g t)
    (hOrig : ∀ t, Tendsto (fun n => charFun (μ.map (X n)) t) atTop (𝓝 (g t))) :
    ∀ t, Tendsto (fun n => charFun (μ.map (Y n)) t) atTop (𝓝 (g t)) := by
  intro t
  have herr (n : ℕ) (hn : 2 ≤ n) : ‖charFun (μ.map (Y n)) t -
      charFun (μ.map (X n)) (-t)‖ ≤ |t| * (1 / Real.log (n : ℝ)) := by
    rw [sign_reflect _ (hX n)]
    have hNeg : Measurable (fun p => -X n p) := (hX n).neg
    refine char_difference_of_uniform _ _ (hY n) hNeg t _ fun p => ?_
    simpa only [sub_neg_eq_add] using hE n hn p
  have hd : Tendsto (fun n => ‖charFun (μ.map (Y n)) t - charFun (μ.map (X n)) (-t)‖)
      atTop (𝓝 0) := by
    have ht := reciprocal_log_tendsto.const_mul |t|
    rw [mul_zero] at ht
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact herr n hn
  have hz : Tendsto (fun n => charFun (μ.map (Y n)) t - charFun (μ.map (X n)) (-t))
      atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hd
  simpa only [sub_add_cancel, zero_add, heven] using hz.add (hOrig (-t))

private theorem cumulative_limit {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hChar : ∀ t, Tendsto (fun n => charFun (μ.map (Y n)) t) atTop (𝓝 (charFun ν t)))
    (c : ℝ) (hBoundary : ν (frontier (Iic c)) = 0) :
    Tendsto (fun n : ℕ => ((μ.map (Y n)) (Iic c)).toReal) atTop
      (𝓝 ((ν (Iic c)).toReal)) := by
  let μn (n : ℕ) : ProbabilityMeasure ℝ :=
    ⟨μ.map (Y n), Measure.isProbabilityMeasure_map (hY n).aemeasurable⟩
  let νp : ProbabilityMeasure ℝ := ⟨ν, inferInstance⟩
  have hWeak : Tendsto μn atTop (𝓝 νp) :=
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr hChar
  have hDist : Tendsto (fun n : ℕ => (μ.map (Y n)) (Iic c)) atTop
      (𝓝 (ν (Iic c))) := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hWeak hBoundary
  exact (ENNReal.tendsto_toReal (measure_ne_top ν _)).comp hDist

/-- Characteristic-function limit for the positive, zero-based sawtooth sums. -/
def H1 : Prop :=
  ∃ γ : ℝ≥0, 0 < γ ∧
    ∀ t : ℝ, Tendsto (fun n : ℕ =>
      charFun ((volume.restrict (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1)).map
        (fun p : ℝ × ℝ => (1 / Real.log (n : ℝ)) *
          ∑ k ∈ Finset.range n, (Int.fract (p.2 + p.1 * (k : ℝ)) - 1 / 2))) t) atTop
      (𝓝 ((Real.exp (-(γ : ℝ) * |t|) : ℝ) : ℂ))

/-- Fourier identity for the centered Cauchy probability measure. -/
def H2 : Prop :=
  ∀ (γ : ℝ≥0), 0 < γ → ∀ t : ℝ,
    charFun (cauchyMeasure 0 γ) t = ((Real.exp (-(γ : ℝ) * |t|) : ℝ) : ℂ)

theorem main : H1 → H2 → type_of% @Erdos1002.erdos_1002.variants.kesten := by
  intro h1 h2
  obtain ⟨γ, hγ, hLag⟩ := h1
  have hγreal : 0 < (γ : ℝ) := by exact_mod_cast hγ
  let μ := (volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  have hProb : IsProbabilityMeasure μ := square_is_probability
  let X (n : ℕ) (p : ℝ × ℝ) : ℝ := (1 / Real.log (n : ℝ)) *
    ∑ k ∈ Finset.range n, (Int.fract (p.2 + p.1 * (k : ℝ)) - 1 / 2)
  let Y (n : ℕ) (p : ℝ × ℝ) : ℝ := (1 / Real.log (n : ℝ)) *
    ∑ k ∈ Finset.Icc 1 n, ((1 / 2 : ℝ) - Int.fract (p.2 + p.1 * (k : ℝ)))
  have hX (n : ℕ) : Measurable (X n) := by
    dsimp only [X]
    exact measurable_const.mul (Finset.measurable_sum _ fun _ _ =>
      (measurable_fract.comp (by fun_prop)).sub measurable_const)
  have hY (n : ℕ) : Measurable (Y n) := by
    dsimp only [Y]
    exact measurable_const.mul (Finset.measurable_sum _ fun _ _ =>
      measurable_const.sub (measurable_fract.comp (by fun_prop)))
  have hE (n : ℕ) (hn : n ≥ 2) (p : ℝ × ℝ) :
      |Y n p + X n p| ≤ 1 / Real.log (n : ℝ) := index_difference n p hn
  let g (t : ℝ) : ℂ := ((Real.exp (-(γ : ℝ) * |t|) : ℝ) : ℂ)
  have hEven (t : ℝ) : g (-t) = g t := by simp [g, abs_neg]
  have hLag' : ∀ t, Tendsto (fun n => charFun (μ.map (X n)) t) atTop (𝓝 (g t)) := by
    simpa only [half_open_square_measure, μ, X, g] using hLag
  have hs := shift_char_limit (μ := μ) X Y hX hY hE g hEven hLag'
  let ν := cauchyMeasure 0 γ
  have hl (t : ℝ) : Tendsto (fun n => charFun (μ.map (Y n)) t) atTop (𝓝 (charFun ν t)) := by
    rw [show charFun ν t = g t from h2 γ hγ t]
    exact hs t
  refine ⟨(γ : ℝ)⁻¹, inv_pos.mpr hγreal, ?_⟩
  dsimp only
  intro c
  have hBoundary : ν (frontier (Iic c)) = 0 :=
    OMA.Erdos1002Cauchy.cauchy_frontier_Iic_zero _ hγreal c
  have hc := cumulative_limit (μ := μ) (ν := ν) Y hY hl c hBoundary
  rw [show (ν (Iic c)).toReal =
      (1 / Real.pi) * ∫ t in Iic ((γ : ℝ)⁻¹ * c), 1 / (1 + t ^ 2) from
    OMA.Erdos1002Cauchy.cauchy_Iic_toReal _ hγreal c] at hc
  convert hc using 1
  ext n
  rw [Measure.map_apply (hY n) measurableSet_Iic]
  dsimp only [μ]
  rw [Measure.restrict_apply (measurableSet_Iic.preimage (hY n))]
  congr 2
  ext p
  rcases p with ⟨a, b⟩
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_prod, Y, mem_ofPred_eq]
  tauto

end OMA.R_Erdos1002_erdos_1002_variants_kesten_R1
