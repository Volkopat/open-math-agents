import OMAStatements.S_mo_386651

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Claude386651

open OMA.S_mo_386651

/-- A Lipschitz bump equal to one on `F` and zero off the `δ`-thickening of `F`. -/
noncomputable def bump {n : ℕ} (F : Set (Space n)) (δ : ℝ) (x : Space n) : ℝ :=
  max 0 (1 - Metric.infDist x F / δ)

lemma bump_lip {n : ℕ} (F : Set (Space n)) {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (Real.toNNReal (1 / δ)) (bump F δ) := by
  have h1 : LipschitzWith 1 (fun x : Space n => Metric.infDist x F) := Metric.lipschitz_infDist_pt F
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq]
  have h2 : |Metric.infDist x F - Metric.infDist y F| ≤ dist x y := by
    have := h1.dist_le_mul x y
    simpa [Real.dist_eq] using this
  have h3 : |bump F δ x - bump F δ y| ≤
      |(1 - Metric.infDist x F / δ) - (1 - Metric.infDist y F / δ)| := by
    unfold bump
    rw [max_comm 0, max_comm 0]
    exact abs_max_sub_max_le_abs _ _ (0 : ℝ)
  have h4 : (1 - Metric.infDist x F / δ) - (1 - Metric.infDist y F / δ) =
      -((Metric.infDist x F - Metric.infDist y F) / δ) := by ring
  rw [h4, abs_neg, abs_div, abs_of_pos hδ] at h3
  calc |bump F δ x - bump F δ y| ≤ |Metric.infDist x F - Metric.infDist y F| / δ := h3
    _ ≤ dist x y / δ := by gcongr
    _ = 1 / δ * dist x y := by ring

lemma bump_mem {n : ℕ} (F : Set (Space n)) (δ : ℝ) (x : Space n) :
    0 ≤ bump F δ x ∧ (0 < δ → bump F δ x ≤ 1) := by
  refine ⟨le_max_left _ _, fun hδ => max_le zero_le_one ?_⟩
  have : 0 ≤ Metric.infDist x F / δ := div_nonneg Metric.infDist_nonneg hδ.le
  linarith

lemma bump_of_mem {n : ℕ} {F : Set (Space n)} {δ : ℝ} {x : Space n} (hx : x ∈ F) :
    bump F δ x = 1 := by
  unfold bump
  rw [Metric.infDist_zero_of_mem hx]
  simp

lemma bump_of_notMem {n : ℕ} {F : Set (Space n)} (hF : F.Nonempty) {δ : ℝ} (hδ : 0 < δ) {x : Space n}
    (hx : x ∉ Metric.thickening δ F) : bump F δ x = 0 := by
  have h : δ ≤ Metric.infDist x F := by
    by_contra hlt
    exact hx (by rw [Metric.mem_thickening_iff_infDist_lt hF]; exact not_le.1 hlt)
  unfold bump
  apply max_eq_left
  have : 1 ≤ Metric.infDist x F / δ := by rw [le_div_iff₀ hδ]; linarith
  linarith

/-- One measurable set: a Lipschitz function with values in `[0,1]` that agrees with the
indicator off a set of small measure. -/
lemma one_set {n : ℕ} (μ : Measure (Space n)) [IsFiniteMeasure μ] (E : Set (Space n))
    (hE : MeasurableSet E) (η : ℝ) (hη : 0 < η) :
    ∃ (g : Space n → ℝ) (K : ℝ≥0) (D : Set (Space n)), LipschitzWith K g ∧ MeasurableSet D ∧
      μ D ≤ ENNReal.ofReal η ∧ (∀ x, x ∉ D → g x = E.indicator (fun _ => (1 : ℝ)) x) ∧
      ∀ x, |E.indicator (fun _ => (1 : ℝ)) x - g x| ≤ 1 := by
  have he : ENNReal.ofReal (η / 2) ≠ 0 := by simp; positivity
  obtain ⟨F, hFE, hFc, hF⟩ := hE.exists_isCompact_lt_add (measure_ne_top μ E) he
  obtain ⟨U, hEU, hUo, hU⟩ := E.exists_isOpen_lt_add (measure_ne_top μ E) he
  have hmeas : μ (U \ F) ≤ ENNReal.ofReal η := by
    rw [measure_sdiff_le_iff_le_add hFc.measurableSet.nullMeasurableSet (hFE.trans hEU)
      (measure_ne_top μ F)]
    calc μ U ≤ μ E + ENNReal.ofReal (η / 2) := hU.le
      _ ≤ μ F + ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := by gcongr
      _ = μ F + ENNReal.ofReal η := by
        rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
  rcases F.eq_empty_or_nonempty with hF0 | hFne
  · refine ⟨fun _ => 0, 0, U \ F, LipschitzWith.const 0,
      hUo.measurableSet.diff hFc.measurableSet, hmeas, ?_, ?_⟩
    · intro x hx
      have hxU : x ∉ U := fun h => hx ⟨h, by simp [hF0]⟩
      rw [Set.indicator_of_notMem (fun h => hxU (hEU h))]
    · intro x
      by_cases hxE : x ∈ E
      · simp [Set.indicator_of_mem hxE]
      · simp [Set.indicator_of_notMem hxE]
  obtain ⟨δ, hδ, hδU⟩ := hFc.exists_thickening_subset_open hUo (hFE.trans hEU)
  refine ⟨bump F δ, _, U \ F, bump_lip F hδ, hUo.measurableSet.diff hFc.measurableSet, hmeas, ?_, ?_⟩
  · intro x hx
    by_cases hxF : x ∈ F
    · rw [bump_of_mem hxF, Set.indicator_of_mem (hFE hxF)]
    · have hxU : x ∉ U := fun h => hx ⟨h, hxF⟩
      rw [bump_of_notMem hFne hδ (fun h => hxU (hδU h)),
        Set.indicator_of_notMem (fun h => hxU (hEU h))]
  · intro x
    obtain ⟨h0, h1⟩ := bump_mem F δ x
    have h1 := h1 hδ
    by_cases hxE : x ∈ E
    · rw [Set.indicator_of_mem hxE, abs_le]; constructor <;> linarith
    · rw [Set.indicator_of_notMem hxE, abs_le]; constructor <;> linarith

theorem part1 (n m N : ℕ) (μ : Measure (Space n)) [IsFiniteMeasure μ]
    (E : Fin N → Set (Space n)) (v : Fin N → Space m)
    (hE : ∀ i, MeasurableSet (E i)) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ≥0, ∀ L ≥ K, ∃ g : Space n → Space m,
      LipschitzWith L g ∧ eLpNorm (stepFunction E v - g) 1 μ ≤ ENNReal.ofReal ε := by
  set M : ℝ := ∑ i, ‖v i‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => norm_nonneg _
  set η : ℝ := ε / (1 + M) with hη
  have hηpos : 0 < η := by positivity
  choose g K D hg hDm hD hgD hgb using fun i => one_set μ (E i) (hE i) η hηpos
  set G : Space n → Space m := fun x => ∑ i, g i x • v i with hG
  have hGlip : LipschitzWith (∑ i, K i * ‖v i‖₊) G := by
    have : ∀ s : Finset (Fin N), LipschitzWith (∑ i ∈ s, K i * ‖v i‖₊)
        (fun x => ∑ i ∈ s, g i x • v i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using LipschitzWith.const (0 : Space m)
      | insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        refine LipschitzWith.add ?_ ih
        refine LipschitzWith.of_dist_le_mul fun x y => ?_
        rw [dist_eq_norm, ← sub_smul, norm_smul, NNReal.coe_mul, coe_nnnorm]
        have := (hg a).dist_le_mul x y
        rw [Real.dist_eq] at this
        rw [Real.norm_eq_abs]
        nlinarith [norm_nonneg (v a), mul_le_mul_of_nonneg_right this (norm_nonneg (v a))]
    exact this Finset.univ
  refine ⟨_, fun L hL => ⟨G, hGlip.weaken hL, ?_⟩⟩
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hpt : ∀ x, ‖(stepFunction E v - G) x‖ₑ ≤
      ∑ i, (D i).indicator (fun _ => ‖v i‖ₑ) x := by
    intro x
    have hx : (stepFunction E v - G) x =
        ∑ i, ((E i).indicator (fun _ => (1 : ℝ)) x - g i x) • v i := by
      simp only [Pi.sub_apply, stepFunction, hG, Finset.sum_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : x ∈ E i <;> simp [h, sub_smul]
    rw [hx]
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    by_cases hxD : x ∈ D i
    · rw [Set.indicator_of_mem hxD, enorm_smul]
      calc ‖(E i).indicator (fun _ => (1 : ℝ)) x - g i x‖ₑ * ‖v i‖ₑ ≤ 1 * ‖v i‖ₑ := by
            gcongr
            rw [← ofReal_norm, Real.norm_eq_abs]
            exact ENNReal.ofReal_le_one.2 (hgb i x)
        _ = ‖v i‖ₑ := one_mul _
    · rw [hgD i x hxD, sub_self, zero_smul, enorm_zero]; exact bot_le
  calc ∫⁻ x, ‖(stepFunction E v - G) x‖ₑ ∂μ
      ≤ ∫⁻ x, ∑ i, (D i).indicator (fun _ => ‖v i‖ₑ) x ∂μ := lintegral_mono hpt
    _ = ∑ i, ∫⁻ x, (D i).indicator (fun _ => ‖v i‖ₑ) x ∂μ :=
        lintegral_finset_sum _ fun i _ => measurable_const.indicator (hDm i)
    _ ≤ ∑ i, ‖v i‖ₑ * ENNReal.ofReal η := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc ∫⁻ x, (D i).indicator (fun _ => ‖v i‖ₑ) x ∂μ ≤ ‖v i‖ₑ * μ (D i) :=
              lintegral_indicator_const_le _ _
          _ ≤ ‖v i‖ₑ * ENNReal.ofReal η := by gcongr; exact hD i
    _ = ENNReal.ofReal (M * η) := by
        rw [hM, Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
    _ ≤ ENNReal.ofReal ε := by
        apply ENNReal.ofReal_le_ofReal
        rw [hη, mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

noncomputable def pt (L : ℕ → ℝ≥0) (k : ℕ) : ℝ := 1 / (2 * ((L k : ℝ) + 1))

noncomputable def ν (L : ℕ → ℝ≥0) : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac 0 +
    Measure.sum fun k : ℕ => (2⁻¹ : ℝ≥0∞) ^ (k + 2) • Measure.dirac (pt L k)

lemma half_eq : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

lemma tsum_half : ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 2) = 2⁻¹ := by
  have h : ∀ k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 2) = 2⁻¹ ^ 2 * 2⁻¹ ^ k := fun k => by rw [pow_add, mul_comm]
  rw [tsum_congr h, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, pow_two,
    mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]

theorem part2 (L : ℕ → ℝ≥0) : ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      ∀ (k : ℕ) (g : ℝ → ℝ), LipschitzWith (L k) g →
        (2⁻¹ : ℝ≥0∞) ^ (k + 3) ≤ eLpNorm (singletonStep - g) 1 μ := by
  refine ⟨ν L, ⟨?_⟩, ?_⟩
  · simp only [ν, Measure.add_apply, Measure.smul_apply, Measure.sum_apply _ MeasurableSet.univ,
      measure_univ, smul_eq_mul, mul_one]
    rw [tsum_half, ENNReal.inv_two_add_inv_two]
  · intro k g hg
    rw [eLpNorm_one_eq_lintegral_enorm]
    have hx : 0 < pt L k := by unfold pt; positivity
    set A : ℝ≥0∞ := ‖(singletonStep - g) 0‖ₑ with hA
    set B : ℝ≥0∞ := ‖(singletonStep - g) (pt L k)‖ₑ with hB
    have hint : (2⁻¹ : ℝ≥0∞) * A + 2⁻¹ ^ (k + 2) * B ≤ ∫⁻ x, ‖(singletonStep - g) x‖ₑ ∂(ν L) := by
      unfold ν
      rw [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, lintegral_sum_measure]
      refine add_le_add le_rfl ?_
      refine le_trans ?_ (ENNReal.le_tsum k)
      rw [lintegral_smul_measure, lintegral_dirac]
      rfl
    refine le_trans ?_ hint
    have hAB : (2⁻¹ : ℝ≥0∞) ≤ A + B := by
      have hlip := hg.dist_le_mul 0 (pt L k)
      rw [Real.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hx] at hlip
      have hLx : (L k : ℝ) * pt L k ≤ 1 / 2 := by
        unfold pt
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        have := (L k).coe_nonneg
        linarith
      have h0 : (singletonStep - g) 0 = 1 - g 0 := by simp [singletonStep]
      have h1 : (singletonStep - g) (pt L k) = - g (pt L k) := by
        simp [singletonStep, hx.ne']
      rw [hA, hB, h0, h1, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_neg,
        ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), half_eq]
      apply ENNReal.ofReal_le_ofReal
      have t1 : (1 : ℝ) = (1 - g 0) + (g 0 - g (pt L k)) + g (pt L k) := by ring
      have t2 := abs_add_three (1 - g 0) (g 0 - g (pt L k)) (g (pt L k))
      rw [← t1, abs_one] at t2
      linarith
    have hpow : (2⁻¹ : ℝ≥0∞) ^ (k + 2) ≤ 2⁻¹ :=
      pow_le_of_le_one bot_le (by simp) (by omega)
    calc (2⁻¹ : ℝ≥0∞) ^ (k + 3) = 2⁻¹ ^ (k + 2) * 2⁻¹ := by rw [pow_succ]
      _ ≤ 2⁻¹ ^ (k + 2) * (A + B) := by gcongr
      _ = 2⁻¹ ^ (k + 2) * A + 2⁻¹ ^ (k + 2) * B := mul_add _ _ _
      _ ≤ 2⁻¹ * A + 2⁻¹ ^ (k + 2) * B := by gcongr

end Claude386651

theorem OMA.solution : type_of% @OMA.S_mo_386651.main :=
  ⟨fun n m N μ _ E v hE _ ε hε => Claude386651.part1 n m N μ E v hE ε hε,
    Claude386651.part2⟩
