import OMAStatements.S_mo_376819

open Filter Finset MeasureTheory ProbabilityTheory Set
open scoped ENNReal Interval Topology

namespace OMA.Mo376819

private noncomputable abbrev eLaw := expMeasure 1

private instance : IsProbabilityMeasure eLaw := isProbabilityMeasure_expMeasure zero_lt_one

private theorem eLaw_density :
    eLaw = (volume.restrict (Ioi 0)).withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-x))) := by
  change volume.withDensity (exponentialPDF 1) = _
  rw [← withDensity_indicator measurableSet_Ioi]
  apply withDensity_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne (0 : ℝ)] with x hx
  rcases lt_or_gt_of_ne hx with h | h
  · rw [exponentialPDF_of_neg h, indicator_of_notMem (show x ∉ Set.Ioi 0 from not_lt.mpr h.le)]
  · rw [exponentialPDF_of_nonneg h.le, indicator_of_mem (show x ∈ Set.Ioi 0 from h)]
    simp

private theorem eLaw_integral (g : ℝ → ℝ) :
    ∫ x, g x ∂eLaw = ∫ x in Ioi 0, Real.exp (-x) * g x := by
  rw [eLaw_density, integral_withDensity_eq_integral_toReal_smul (by fun_prop)]
  · simp [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
  · exact ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top

private theorem eLaw_integrable_id : Integrable (fun x : ℝ ↦ x) eLaw := by
  rw [eLaw_density, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simpa [IntegrableOn, smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _),
    show (2 : ℝ) - 1 = 1 by norm_num] using (Real.GammaIntegral_convergent (s := 2) (by norm_num))

private theorem eLaw_mean : ∫ x : ℝ, x ∂eLaw = 1 := by
  rw [eLaw_integral]
  have h := Real.Gamma_eq_integral (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  simpa using h.symm

private theorem eLaw_nonneg : ∀ᵐ x ∂eLaw, 0 ≤ x := by
  rw [eLaw_density]
  exact ((ae_restrict_mem measurableSet_Ioi).mono fun _ hx ↦ le_of_lt hx).filter_mono
    (withDensity_absolutelyContinuous _ _).ae_le

private theorem eLaw_no_atoms (x : ℝ) : eLaw {x} = 0 := by
  rw [eLaw_density]
  apply withDensity_absolutelyContinuous _ _
  exact measure_singleton x

private theorem eLaw_tail {b : ℝ} (hb : 0 ≤ b) : eLaw.real (Ici b) = Real.exp (-b) := by
  rw [measureReal_def, ← measure_congr (Ioi_ae_eq_Ici' (eLaw_no_atoms b))]
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
    ENNReal.toReal_sub_of_le (prob_le_one) (by simp), ENNReal.toReal_one,
    ← measureReal_def, ← cdf_eq_real, cdf_expMeasure_eq zero_lt_one b, if_pos hb, one_mul]
  ring

private theorem eLaw_stop_loss {b : ℝ} (hb : 0 ≤ b) :
    ∫ x, max 0 (b - x) ∂eLaw = b - 1 + Real.exp (-b) := by
  rw [eLaw_integral, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    measurableSet_Ioi (show Ioc 0 b ⊆ Ioi 0 from Ioc_subset_Ioi_self)]
  · have heq : ∫ x in Ioc 0 b, Real.exp (-x) * max 0 (b - x) =
        ∫ x in 0..b, Real.exp (-x) * (b - x) := by
      rw [intervalIntegral.integral_of_le hb]
      exact setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ by
        rw [max_eq_right (sub_nonneg.mpr hx.2)]
    rw [heq]
    have hder (x : ℝ) : HasDerivAt (fun y ↦ (y + 1 - b) * Real.exp (-y))
        (Real.exp (-x) * (b - x)) x := by
      have h₁ : HasDerivAt (fun y : ℝ ↦ y + 1 - b) 1 x :=
        ((hasDerivAt_id x).add_const 1).sub_const b
      have h₂ : HasDerivAt (fun y : ℝ ↦ Real.exp (-y)) (-Real.exp (-x)) x := by
        simpa using (hasDerivAt_id x).neg.exp
      have heq : 1 * Real.exp (-x) + (x + 1 - b) * (-Real.exp (-x)) =
          Real.exp (-x) * (b - x) := by ring
      rw [← heq]
      exact h₁.mul h₂
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hder x)
      ((by fun_prop : Continuous (fun x ↦ Real.exp (-x) * (b - x))).intervalIntegrable _ _)]
    simp
    ring
  · intro x hx
    have hxb : b ≤ x := le_of_not_ge fun h ↦ hx.2 ⟨hx.1, h⟩
    simp [max_eq_left (sub_nonpos.mpr hxb)]

private def surplus (a : ℝ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * a - ∑ i ∈ range n, x i

private def workload (a : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, x => max 0 (a - x 0 + workload a n (fun i ↦ x (i + 1)))

private theorem workload_nonneg (a : ℝ) (n : ℕ) (x : ℕ → ℝ) : 0 ≤ workload a n x := by
  cases n
  · rfl
  · exact le_max_left _ _

private theorem workload_measurable (a : ℝ) (n : ℕ) : Measurable (workload a n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun x : ℕ → ℝ ↦ max 0 (a - x 0 + workload a n (fun i ↦ x (i + 1))))
    exact measurable_const.max
      ((measurable_const.sub (measurable_pi_apply 0)).add (ih.comp (measurable_pi_iff.mpr
        fun i ↦ measurable_pi_apply (i + 1))))

private theorem partial_succ (a : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    surplus a x (n + 1) = a - x 0 + surplus a (fun i ↦ x (i + 1)) n := by
  rw [surplus, sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, surplus]
  ring

private theorem workload_le (a : ℝ) (n : ℕ) (x : ℕ → ℝ) (b : ℝ) :
    workload a n x ≤ b ↔ ∀ k ≤ n, surplus a x k ≤ b := by
  induction n generalizing x b with
  | zero => simp [workload, surplus]
  | succ n ih =>
    rw [workload, max_le_iff, ← le_sub_iff_add_le', ih]
    constructor
    · rintro ⟨h0, h⟩ (_ | k) hk
      · simpa [surplus] using h0
      · rw [partial_succ]
        linarith [h k (Nat.le_of_succ_le_succ hk)]
    · intro h
      refine ⟨by simpa [surplus] using h 0 (Nat.zero_le _), fun k hk ↦ ?_⟩
      have := h (k + 1) (Nat.succ_le_succ hk)
      rw [partial_succ] at this
      linarith

private theorem workload_bound {a : ℝ} (ha : 0 ≤ a) {x : ℕ → ℝ}
    (hx : ∀ i, 0 ≤ x i) (n : ℕ) : workload a n x ≤ (n : ℝ) * a := by
  apply (workload_le a n x _).mpr
  intro k hk
  unfold surplus
  exact (sub_le_self _ (Finset.sum_nonneg fun i _ ↦ hx i)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) ha)

private theorem head_tail_indep {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ) :
    IndepFun (X 0) (fun ω i ↦ X (i + 1) ω) μ := by
  let m (i : ℕ) := MeasurableSpace.comap (X i) inferInstance
  have hd : Disjoint ({0} : Set ℕ) (range Nat.succ) := by simp
  have hi' : iIndep m μ := hi
  have h := indep_iSup_of_disjoint
    (m := m) (fun i ↦ (measurable_iff_comap_le.mp (hm i))) hi' hd
  change Indep (m 0) (MeasurableSpace.pi.comap (fun ω i ↦ X (i + 1) ω)) μ
  refine indep_of_indep_of_le h (le_iSup_of_le 0 (le_iSup_of_le (mem_singleton 0) le_rfl)) ?_
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  exact iSup_le fun i ↦ le_iSup_of_le (i + 1) (le_iSup_of_le (mem_range_self i) le_rfl)

private noncomputable def runningMin (x : ℕ → ℝ) : ℝ :=
  ⨅ j : ℕ, (∑ i ∈ range (j + 1), x i) / ((j : ℝ) + 1)

private theorem runningMin_measurable : Measurable runningMin := by
  apply Measurable.iInf
  intro j
  exact (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i).div_const _

private theorem le_runningMin_iff {a : ℝ} {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) :
    a ≤ runningMin x ↔ ∀ n, workload a n x = 0 := by
  have hnonneg (j : ℕ) : 0 ≤ (∑ i ∈ range (j + 1), x i) / ((j : ℝ) + 1) :=
    div_nonneg (Finset.sum_nonneg fun i _ ↦ hx i) (by positivity)
  unfold runningMin
  rw [le_ciInf_iff ⟨0, forall_mem_range.mpr hnonneg⟩]
  constructor
  · intro h n
    apply le_antisymm ((workload_le _ _ _ _).mpr ?_) (workload_nonneg _ _ _)
    rintro (_ | j) _
    · simp [surplus]
    · have hj := (le_div_iff₀ (by positivity : (0 : ℝ) < j + 1)).mp (h j)
      simpa [surplus, Nat.cast_succ, mul_comm a, sub_nonpos] using hj
  · intro h j
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < j + 1)).mpr
    have hj := (workload_le a (j + 1) x 0).mp (h (j + 1)).le (j + 1) le_rfl
    simpa [surplus, Nat.cast_succ, mul_comm a, sub_nonpos] using hj

private theorem normalized_workload_tendsto {a : ℝ} (ha : a < 1) {x : ℕ → ℝ}
    (hmean : Tendsto (fun n : ℕ ↦ (∑ i ∈ range n, x i) / n) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ ↦ workload a n x / n) atTop (𝓝 0) := by
  have hneg : ∀ᶠ n : ℕ in atTop, surplus a x n ≤ 0 := by
    filter_upwards [hmean.eventually_const_lt ha, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hh := (lt_div_iff₀ hpos).mp hn
    unfold surplus
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hneg
  have hbound (n : ℕ) : workload a n x ≤ workload a N x := by
    apply (workload_le _ _ _ _).mpr
    intro k _
    by_cases hk : k ≤ N
    · exact (workload_le _ _ _ _).mp le_rfl k hk
    · exact (hN k (by omega)).trans (workload_nonneg _ _ _)
  exact squeeze_zero (fun n ↦ div_nonneg (workload_nonneg _ _ _) (by positivity))
    (fun n ↦ div_le_div_of_nonneg_right (hbound n) (by positivity))
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)

private theorem workload_step {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hi : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i) = eLaw)
    (hx : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ X i ω) {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    (∫ ω, workload a (n + 1) (fun i ↦ X i ω) ∂μ) -
      μ.real {ω | workload a (n + 1) (fun i ↦ X i ω) = 0} =
    (∫ ω, workload a n (fun i ↦ X i ω) ∂μ) + (a - 1) := by
  let path (ω : Ω) (i : ℕ) := X i ω
  let tail (ω : Ω) (i : ℕ) := X (i + 1) ω
  have mpath : Measurable path := measurable_pi_iff.mpr hm
  have mtail : Measurable tail := measurable_pi_iff.mpr (fun i ↦ hm (i + 1))
  have hpaths : μ.map tail = μ.map path := by
    change μ.map (fun ω i ↦ X (i + 1) ω) = μ.map (fun ω i ↦ X i ω)
    rw [(hi.precomp Nat.succ_injective).map_fun_eq_infinitePi_map (fun i ↦ hm (i + 1)),
      hi.map_fun_eq_infinitePi_map hm]
    simp_rw [hlaw]
  let W := workload a n ∘ path
  let W' := workload a n ∘ tail
  let Wnext := workload a (n + 1) ∘ path
  have mW : Measurable W := (workload_measurable a n).comp mpath
  have mW' : Measurable W' := (workload_measurable a n).comp mtail
  have mWnext : Measurable Wnext := (workload_measurable a (n + 1)).comp mpath
  let ρ := μ.map W
  have hρ : μ.map W' = ρ := by
    rw [show μ.map W' = (μ.map tail).map (workload a n) from
        (Measure.map_map (workload_measurable a n) mtail).symm,
      hpaths, Measure.map_map (workload_measurable a n) mpath]
  have joint : μ.map (fun ω ↦ (W' ω, X 0 ω)) = ρ.prod eLaw := by
    have hI := (head_tail_indep hm hi).symm.comp (workload_measurable a n) measurable_id
    have h := hI.map_prod_eq_prod_map_map mW'.aemeasurable (hm 0).aemeasurable
    simpa only [Function.id_comp, hρ, hlaw] using h
  let E := {ω | Wnext ω = 0}
  have mE : MeasurableSet E := mWnext (measurableSet_singleton 0)
  have intW (k : ℕ) : Integrable (workload a k ∘ path) μ := by
    refine (integrable_const ((k : ℝ) * a)).mono'
      ((workload_measurable a k).comp mpath).aestronglyMeasurable ?_
    filter_upwards [hx] with ω hω
    rw [Function.comp_apply, Real.norm_of_nonneg (workload_nonneg _ _ _)]
    exact workload_bound ha hω k
  have intE : Integrable (E.indicator (fun _ : Ω ↦ (1 : ℝ))) μ :=
    (integrable_const 1).indicator mE
  let R (p : ℝ × ℝ) :=
    max 0 (a + p.1 - p.2) - (if a + p.1 ≤ p.2 then 1 else 0)
  have mR : Measurable R := by
    apply Measurable.sub (by fun_prop)
    exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop))
      measurable_const measurable_const
  have hR (ω : Ω) : R (W' ω, X 0 ω) = Wnext ω - E.indicator (fun _ ↦ 1) ω := by
    have hw : Wnext ω = max 0 (a + W' ω - X 0 ω) := by
      change max 0 (a - X 0 ω + W' ω) = _
      rw [add_sub_right_comm]
    rw [hw]
    change _ = max 0 (a + W' ω - X 0 ω) - E.indicator (fun _ ↦ 1) ω
    have he : ω ∈ E ↔ a + W' ω ≤ X 0 ω := by
      change Wnext ω = 0 ↔ _
      rw [hw, max_eq_left_iff, sub_nonpos]
    simp [R, indicator_apply, he]
  have mPair : Measurable (fun ω ↦ (W' ω, X 0 ω)) := mW'.prodMk (hm 0)
  have intR : Integrable R (ρ.prod eLaw) := by
    rw [← joint, integrable_map_measure mR.aestronglyMeasurable mPair.aemeasurable]
    exact ((intW (n + 1)).sub intE).congr (ae_of_all _ fun ω ↦ (hR ω).symm)
  have hr (w : ℝ) (hw : 0 ≤ w) : (∫ x, R (w, x) ∂eLaw) = w + (a - 1) := by
    let b := a + w
    have hb : 0 ≤ b := add_nonneg ha hw
    have hiMax : Integrable (fun x ↦ max 0 (b - x)) eLaw :=
      (integrable_const b).mono' (by fun_prop) <| by
        filter_upwards [eLaw_nonneg] with x hx
        rw [Real.norm_of_nonneg (le_max_left _ _)]
        exact max_le hb (by linarith)
    have hEq : (fun x ↦ R (w, x)) =
        fun x ↦ max 0 (b - x) - (Ici b).indicator (fun _ ↦ 1) x := by
      funext x
      simp [b, R, indicator_apply]
    rw [hEq, integral_sub hiMax ((integrable_const 1).indicator measurableSet_Ici),
      integral_indicator_const (1 : ℝ) measurableSet_Ici, smul_eq_mul, mul_one,
      eLaw_tail hb, eLaw_stop_loss hb]
    dsimp [b]
    ring
  have hleft : (∫ p, R p ∂ρ.prod eLaw) =
      (∫ ω, Wnext ω ∂μ) - μ.real E := by
    rw [← joint, integral_map mPair.aemeasurable mR.aestronglyMeasurable]
    simp_rw [hR]
    rw [integral_sub (intW (n + 1)) intE, integral_indicator_const (1 : ℝ) mE, smul_eq_mul,
      mul_one]
  have hright : (∫ p, R p ∂ρ.prod eLaw) =
      (∫ ω, W ω ∂μ) + (a - 1) := by
    rw [integral_prod R intR]
    change (∫ w, ∫ x, R (w, x) ∂eLaw ∂μ.map W) = _
    rw [integral_map mW.aemeasurable
      (mR.stronglyMeasurable.integral_prod_right').aestronglyMeasurable]
    calc
      _ = ∫ ω, W ω + (a - 1) ∂μ :=
        integral_congr_ae (ae_of_all _ fun ω ↦ hr (W ω) (workload_nonneg _ _ _))
      _ = _ := by rw [integral_add (intW n) (integrable_const (a - 1))]; simp [W]
  exact hleft.symm.trans hright

private theorem upper_tail {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hi : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i) = eLaw)
    (hx : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ X i ω)
    (hmean : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ i ∈ range n, X i ω) / n) atTop (𝓝 1))
    {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1) :
    μ.real {ω | a ≤ runningMin (fun i ↦ X i ω)} = 1 - a := by
  let W (n : ℕ) (ω : Ω) := workload a n (fun i ↦ X i ω)
  let Z (n : ℕ) := {ω | W n ω = 0}
  let E (n : ℕ) := ∫ ω, W n ω ∂μ
  let L := μ.real (⋂ n, Z n)
  have mW (n : ℕ) : Measurable (W n) :=
    (workload_measurable a n).comp (measurable_pi_iff.mpr hm)
  have hAnti : Antitone Z := by
    intro m n hmn ω hω
    change W m ω = 0
    apply le_antisymm _ (workload_nonneg _ _ _)
    apply (workload_le _ _ _ _).mpr
    intro k hk
    exact (workload_le _ _ _ _).mp hω.le k (hk.trans hmn)
  have hp : Tendsto (fun n ↦ μ.real (Z n)) atTop (𝓝 L) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (tendsto_measure_iInter_atTop (fun n ↦ ((mW n) (measurableSet_singleton 0)).nullMeasurableSet)
        hAnti ⟨0, measure_ne_top _ _⟩)
  have hCes := (hp.comp (tendsto_add_atTop_nat 1)).cesaro
  have hsum (n : ℕ) : E n = (n : ℝ) * (a - 1) + ∑ i ∈ range n, μ.real (Z (i + 1)) := by
    induction n with
    | zero => simp [E, W, workload]
    | succ n ih =>
      have hs : E (n + 1) - μ.real (Z (n + 1)) = E n + (a - 1) :=
        workload_step μ X hm hi hlaw hx ha n
      rw [Nat.cast_succ, sum_range_succ]
      linarith
  have hnormalized : Tendsto (fun n : ℕ ↦ E n / n) atTop (𝓝 0) := by
    have hD := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
      (F := fun n : ℕ ↦ fun ω : Ω ↦ W n ω / n) (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ a)
      (Eventually.of_forall fun n ↦ ((mW n).div_const _).aestronglyMeasurable) ?_
      (integrable_const a) ?_
    · simpa [E, integral_div] using hD
    · apply Eventually.of_forall
      intro n
      filter_upwards [hx] with ω hω
      rw [Real.norm_of_nonneg (div_nonneg (workload_nonneg _ _ _) (by positivity))]
      by_cases hn : n = 0
      · simpa [hn] using ha
      · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn : (0 : ℝ) < n)).mpr
        simpa only [mul_comm] using workload_bound ha hω n
    · exact hmean.mono fun ω hω ↦ normalized_workload_tendsto ha' hω
  have hEq : (fun n : ℕ ↦ (a - 1) + (n⁻¹ : ℝ) * ∑ i ∈ range n, μ.real (Z (i + 1))) =ᶠ[atTop]
      (fun n : ℕ ↦ E n / n) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [hsum]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hLim : Tendsto (fun n : ℕ ↦ E n / n) atTop (𝓝 ((a - 1) + L)) :=
    (tendsto_const_nhds.add hCes).congr' hEq
  have hL := tendsto_nhds_unique hLim hnormalized
  have hset : {ω | a ≤ runningMin (fun i ↦ X i ω)} =ᵐ[μ] (⋂ n, Z n) := by
    filter_upwards [hx] with ω hω
    apply propext
    change a ≤ runningMin (fun i ↦ X i ω) ↔ ω ∈ ⋂ n, Z n
    simp only [mem_iInter, Z, W, Set.mem_ofPred_eq]
    exact le_runningMin_iff hω
  rw [measureReal_def, measure_congr hset, ← measureReal_def]
  change L = 1 - a
  linarith

private theorem uniform_running_min : type_of% @OMA.S_mo_376819.main := by
  intro Ω _ μ _ X hm hi hlaw
  have hx : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ X i ω := by
    rw [ae_all_iff]
    intro i
    apply ae_of_ae_map (hm i).aemeasurable
    rw [hlaw]
    exact eLaw_nonneg
  have hInt : Integrable (X 0) μ := by
    have h : Integrable id (μ.map (X 0)) := by rw [hlaw]; exact eLaw_integrable_id
    exact h.comp_measurable (hm 0)
  have hIntegral : ∫ ω, X 0 ω ∂μ = 1 := by
    have h := integral_map (μ := μ) (hm 0).aemeasurable
      (f := id) continuous_id.aestronglyMeasurable
    change (∫ x : ℝ, x ∂μ.map (X 0)) = _ at h
    rw [hlaw, eLaw_mean] at h
    exact h.symm
  have hSLLN := strong_law_ae_real X hInt (fun _ _ h ↦ hi.indepFun h)
    (fun i ↦ ⟨(hm i).aemeasurable, (hm 0).aemeasurable, (hlaw i).trans (hlaw 0).symm⟩)
  rw [hIntegral] at hSLLN
  let M (ω : Ω) := runningMin (fun i ↦ X i ω)
  have mM : Measurable M := runningMin_measurable.comp (measurable_pi_iff.mpr hm)
  change μ.map M = _
  let : IsFiniteMeasure (μ.map M) := inferInstance
  apply Measure.ext_of_Ici
  intro a
  have hfinite : (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Ici a) ≠ ∞ := by
    rw [Measure.restrict_apply measurableSet_Ici]
    exact ((measure_mono Set.inter_subset_right).trans_lt (by simp [Real.volume_Icc])).ne
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) hfinite).mp
  rw [map_measureReal_apply mM measurableSet_Ici, measureReal_restrict_apply measurableSet_Ici]
  have hset : Ici a ∩ Icc (0 : ℝ) 1 = Icc (max a 0) 1 := by
    ext x
    simp [and_assoc]
  rw [hset, measureReal_def (μ := volume), Real.volume_Icc]
  have htail {b : ℝ} (hb : 0 ≤ b) (hb' : b < 1) : μ.real (M ⁻¹' Ici b) = 1 - b :=
    upper_tail μ X hm hi hlaw hx hSLLN hb hb'
  rcases lt_or_ge a 0 with ha | ha
  · have heq : M ⁻¹' Ici a =ᵐ[μ] (M ⁻¹' Ici 0) := by
      filter_upwards [hx] with ω hω
      have h0 : 0 ≤ M ω := (le_runningMin_iff hω).mpr fun n ↦
        le_antisymm (by simpa using workload_bound (a := 0) le_rfl hω n)
          (workload_nonneg _ _ _)
      change (a ≤ M ω) = (0 ≤ M ω)
      simp [h0, ha.le.trans h0]
    rw [measureReal_def, measure_congr heq, ← measureReal_def, htail le_rfl zero_lt_one,
      max_eq_right ha.le, sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one]
  rcases lt_or_ge a 1 with ha' | ha'
  · rw [htail ha ha', max_eq_left ha, ENNReal.toReal_ofReal (sub_nonneg.mpr ha'.le)]
  rw [max_eq_left ha, ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr ha'), ENNReal.toReal_zero]
  by_contra hp
  have hp0 : 0 < μ.real (M ⁻¹' Ici a) := lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)
  have hp1 : μ.real (M ⁻¹' Ici a) ≤ 1 := measureReal_le_one
  let b := 1 - μ.real (M ⁻¹' Ici a) / 2
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hb' : b < 1 := by dsimp [b]; linarith
  have hsub : M ⁻¹' Ici a ⊆ M ⁻¹' Ici b := preimage_mono (Ici_subset_Ici.mpr (hb'.le.trans ha'))
  have hmono := measureReal_mono (μ := μ) hsub
  rw [htail hb hb'] at hmono
  dsimp [b] at hmono
  linarith

end OMA.Mo376819

theorem OMA.solution : type_of% @OMA.S_mo_376819.main := OMA.Mo376819.uniform_running_min
