import OMAStatements.S_mo_471674

open OMA.S_mo_471674

private lemma exists_best {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V : Submodule ℝ E) (x : E) : ∃ v, best V x v := by
  let S : Set E := (V : Set E) ∩ Metric.closedBall x ‖x‖
  have hS_ne : S.Nonempty := ⟨0, V.zero_mem, by simp [Metric.mem_closedBall, dist_zero_left]⟩
  have hS_cpt : IsCompact S :=
    (isCompact_closedBall x ‖x‖).inter_left V.closed_of_finiteDimensional
  have hcont : ContinuousOn (fun w : E => ‖x - w‖) S :=
    (continuous_const.sub continuous_id).norm.continuousOn
  obtain ⟨v, hvS, hvmin⟩ := hS_cpt.exists_isMinOn hS_ne hcont
  refine ⟨v, hvS.1, fun w hwV => ?_⟩
  by_cases hwb : w ∈ Metric.closedBall x ‖x‖
  · exact hvmin ⟨hwV, hwb⟩
  · have h1 : ‖x - v‖ ≤ ‖x - 0‖ := hvmin ⟨V.zero_mem, by simp [Metric.mem_closedBall, dist_zero_left]⟩
    have h2 : ‖x‖ < dist w x := by
      simpa [Metric.mem_closedBall, not_le] using hwb
    rw [dist_eq_norm, norm_sub_rev] at h2
    simp only [sub_zero] at h1
    exact h1.trans h2.le

private lemma someBound_iff_everyBound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (C : ℝ) : someBound E C ↔ everyBound E C := by
  constructor
  · intro hsome V x v hvbest
    by_contra hlt
    push Not at hlt
    by_cases hxv : x = v
    · subst hxv
      obtain ⟨w, hwbest, hwle⟩ := hsome (ℝ ∙ x) x
      have hwx : ‖x - w‖ ≤ ‖x - x‖ := hwbest.2 x (Submodule.mem_span_singleton_self x)
      rw [sub_self, norm_zero] at hwx
      have hw0 : x - w = 0 := norm_le_zero_iff.mp hwx
      have : w = x := (sub_eq_zero.mp hw0).symm
      subst this
      linarith
    · set r := x - v
      have hr_pos : 0 < ‖r‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxv)
      have horth : orth r v := by
        intro s
        have hmem : v - s • v ∈ V := V.sub_mem hvbest.1 (V.smul_mem s hvbest.1)
        have hle := hvbest.2 (v - s • v) hmem
        have heq : x - (v - s • v) = r + s • v := by simp only [r]; abel
        simpa [heq] using hle
      set ε := min (1 / 2 : ℝ) ((‖v‖ - C * ‖x‖) / (2 * ‖r‖))
      have hε_pos : 0 < ε := by
        apply lt_min
        · norm_num
        · exact div_pos (sub_pos.mpr hlt) (mul_pos two_pos hr_pos)
      have hε_lt_one : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
      have hεr : ε * ‖r‖ < ‖v‖ - C * ‖x‖ := by
        have h1 : ε ≤ (‖v‖ - C * ‖x‖) / (2 * ‖r‖) := min_le_right _ _
        calc ε * ‖r‖ ≤ ((‖v‖ - C * ‖x‖) / (2 * ‖r‖)) * ‖r‖ :=
            mul_le_mul_of_nonneg_right h1 hr_pos.le
          _ = (‖v‖ - C * ‖x‖) / 2 := by field_simp [hr_pos.ne']
          _ < ‖v‖ - C * ‖x‖ := half_lt_self (sub_pos.mpr hlt)
      set vε := v + ε • r
      obtain ⟨w, hwbest, hwle⟩ := hsome (ℝ ∙ vε) x
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hwbest.1
      have h_dist_le : ‖x - t • vε‖ ≤ (1 - ε) * ‖r‖ := by
        have h1 := hwbest.2 vε (Submodule.mem_span_singleton_self vε)
        have hxve : x - vε = (1 - ε) • r := by
          have : x = r + v := by simp [r]
          rw [this]
          simp only [vε]
          rw [sub_smul, one_smul]
          abel
        rw [hxve, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hε_lt_one.le)] at h1
        exact h1
      have ht_ge : 1 ≤ t := by
        by_contra ht_lt
        push Not at ht_lt
        have h1te_pos : 0 < 1 - t * ε := by nlinarith
        have h1te_gt : 1 - ε < 1 - t * ε := by nlinarith
        have hx_eq : x - t • vε = (1 - t * ε) • (r + ((1 - t) / (1 - t * ε)) • v) := by
          have hne : 1 - t * ε ≠ 0 := h1te_pos.ne'
          have hx : x = r + v := by simp [r]
          rw [hx]
          simp only [vε, smul_add, smul_smul, mul_div_cancel₀ _ hne]
          rw [sub_smul, one_smul, sub_smul, one_smul]
          abel
        have hlow : (1 - t * ε) * ‖r‖ ≤ ‖x - t • vε‖ := by
          rw [hx_eq, norm_smul, Real.norm_of_nonneg h1te_pos.le]
          exact mul_le_mul_of_nonneg_left (horth ((1 - t) / (1 - t * ε))) h1te_pos.le
        have hstrict : (1 - ε) * ‖r‖ < (1 - t * ε) * ‖r‖ :=
          mul_lt_mul_of_pos_right h1te_gt hr_pos
        linarith
      have ht_pos : 0 ≤ t := by linarith
      have hnorm_vε : ‖v‖ - ε * ‖r‖ ≤ ‖vε‖ := by
        have := norm_sub_le (v + ε • r) (ε • r)
        simp only [add_sub_cancel_right, norm_smul, Real.norm_of_nonneg hε_pos.le] at this
        linarith
      have hnorm_w : ‖v‖ - ε * ‖r‖ ≤ ‖t • vε‖ := by
        rw [norm_smul, Real.norm_of_nonneg ht_pos]
        calc ‖v‖ - ε * ‖r‖ ≤ ‖vε‖ := hnorm_vε
          _ = 1 * ‖vε‖ := (one_mul _).symm
          _ ≤ t * ‖vε‖ := mul_le_mul_of_nonneg_right ht_ge (norm_nonneg _)
      linarith
  · intro hevery V x
    obtain ⟨v, hvbest⟩ := exists_best V x
    exact ⟨v, hvbest, hevery V x v hvbest⟩

private lemma someBound_two {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : someBound E 2 := by
  rw [someBound_iff_everyBound]
  intro V x v hvbest
  have h1 : ‖x - v‖ ≤ ‖x‖ := by simpa using hvbest.2 0 V.zero_mem
  have h2 : ‖v‖ ≤ ‖x - v‖ + ‖x‖ := by
    calc ‖v‖ = ‖x - (x - v)‖ := by simp
      _ ≤ ‖x‖ + ‖x - v‖ := norm_sub_le _ _
      _ = ‖x - v‖ + ‖x‖ := add_comm _ _
  linarith

private lemma someBound_one_iff_orth_symm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : someBound E 1 ↔ ∀ r v : E, orth r v → orth v r := by
  rw [someBound_iff_everyBound]
  constructor
  · intro hevery r v horth t
    by_cases ht : t = 0
    · subst ht; simp
    · have hbest : best (ℝ ∙ v) (v + t • r) v := by
        refine ⟨Submodule.mem_span_singleton_self v, fun w hw => ?_⟩
        obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hw
        have h1 : (v + t • r) - v = t • r := by abel
        have h2 : (v + t • r) - s • v = t • (r + ((1 - s) / t) • v) := by
          rw [smul_add, smul_smul, mul_div_cancel₀ _ ht, sub_smul, one_smul]
          abel
        rw [h1, h2, norm_smul, norm_smul]
        exact mul_le_mul_of_nonneg_left (horth ((1 - s) / t)) (abs_nonneg t)
      have := hevery (ℝ ∙ v) (v + t • r) v hbest
      simpa using this
  · intro hsymm V x v hvbest
    have horth : orth (x - v) v := by
      intro s
      have hmem : v - s • v ∈ V := V.sub_mem hvbest.1 (V.smul_mem s hvbest.1)
      have hle := hvbest.2 (v - s • v) hmem
      have heq : x - (v - s • v) = (x - v) + s • v := by abel
      simpa [heq] using hle
    have h1 := hsymm (x - v) v horth 1
    simpa using h1

private lemma norm_smul_add_of_unit_sum {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖x + y‖ = 2)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : ‖a • x + b • y‖ = a + b := by
  apply le_antisymm
  · calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ = a + b := by rw [hx, hy, mul_one, mul_one]
  · by_cases hab : b ≤ a
    · have h1 : a • (x + y) = (a • x + b • y) + (a - b) • y := by
        rw [smul_add, sub_smul]; abel
      have h2 : ‖a • (x + y)‖ ≤ ‖a • x + b • y‖ + (a - b) := by
        calc ‖a • (x + y)‖ = ‖(a • x + b • y) + (a - b) • y‖ := by rw [h1]
          _ ≤ ‖a • x + b • y‖ + ‖(a - b) • y‖ := norm_add_le _ _
          _ = ‖a • x + b • y‖ + (a - b) := by
            rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hab), hy, mul_one]
      rw [norm_smul, Real.norm_of_nonneg ha, hxy] at h2
      linarith
    · have hba : a ≤ b := le_of_not_ge hab
      have h1 : b • (x + y) = (a • x + b • y) + (b - a) • x := by
        rw [smul_add, sub_smul]; abel
      have h2 : ‖b • (x + y)‖ ≤ ‖a • x + b • y‖ + (b - a) := by
        calc ‖b • (x + y)‖ = ‖(a • x + b • y) + (b - a) • x‖ := by rw [h1]
          _ ≤ ‖a • x + b • y‖ + ‖(b - a) • x‖ := norm_add_le _ _
          _ = ‖a • x + b • y‖ + (b - a) := by
            rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hba), hx, mul_one]
      rw [norm_smul, Real.norm_of_nonneg hb, hxy] at h2
      linarith

private lemma neg_someBound_lt_two_iff_hasSquare {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : (∀ C : ℝ, C < 2 → ¬ someBound E C) ↔ hasSquare E := by
  constructor
  · intro hnot
    have hseq : ∀ n : ℕ, ∃ u w : E, ‖u‖ = 1 ∧ ‖w‖ ≤ 2 ∧
        2 - 1 / ((n : ℝ) + 1) ≤ ‖w‖ ∧ ‖u - w‖ ≤ 1 ∧ orth (u - w) w := by
      intro n
      have hC : 2 - 1 / ((n : ℝ) + 1) < 2 := by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      have hns := hnot _ hC
      rw [someBound_iff_everyBound] at hns
      unfold everyBound at hns
      push Not at hns
      obtain ⟨V, x, v, hvbest, hlt⟩ := hns
      have hx0 : x ≠ 0 := by
        intro hx
        subst hx
        have h1 : ‖0 - v‖ ≤ ‖(0 : E) - 0‖ := hvbest.2 0 V.zero_mem
        simp at h1
        rw [h1] at hlt
        simp at hlt
      have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      refine ⟨‖x‖⁻¹ • x, ‖x‖⁻¹ • v, ?_, ?_, ?_, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx_pos.ne']
      · have hxv : ‖x - v‖ ≤ ‖x‖ := by simpa using hvbest.2 0 V.zero_mem
        have hv2 : ‖v‖ ≤ 2 * ‖x‖ := by
          have : ‖v‖ ≤ ‖x - v‖ + ‖x‖ := by
            calc ‖v‖ = ‖x - (x - v)‖ := by simp
              _ ≤ ‖x‖ + ‖x - v‖ := norm_sub_le _ _
              _ = ‖x - v‖ + ‖x‖ := add_comm _ _
          linarith
        rw [norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hx_pos]
        linarith
      · rw [norm_smul, norm_inv, norm_norm, le_inv_mul_iff₀ hx_pos]
        nlinarith
      · rw [← smul_sub, norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hx_pos, mul_one]
        simpa using hvbest.2 0 V.zero_mem
      · intro t
        have hmem : v - t • v ∈ V := V.sub_mem hvbest.1 (V.smul_mem t hvbest.1)
        have hle := hvbest.2 (v - t • v) hmem
        have heq : x - (v - t • v) = (x - v) + t • v := by abel
        rw [heq] at hle
        have h2 : ‖x‖⁻¹ • (x - v) + t • ‖x‖⁻¹ • v = ‖x‖⁻¹ • ((x - v) + t • v) := by
          rw [smul_add, smul_comm t ‖x‖⁻¹ v]
        rw [← smul_sub, h2, norm_smul, norm_smul]
        exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    choose u w hu hw2 hwlow huw horth using hseq
    let p : ℕ → E × E := fun n => (u n, w n)
    let K : Set (E × E) := Metric.closedBall (0 : E) 1 ×ˢ Metric.closedBall (0 : E) 2
    have hK_cpt : IsCompact K :=
      (isCompact_closedBall (0 : E) 1).prod (isCompact_closedBall (0 : E) 2)
    have hpK : ∀ n, p n ∈ K := fun n => by
      refine ⟨?_, ?_⟩
      · simpa [p, Metric.mem_closedBall, dist_zero_right] using (hu n).le
      · simpa [p, Metric.mem_closedBall, dist_zero_right] using hw2 n
    obtain ⟨⟨a, b⟩, -, φ, hφmono, hφtend⟩ := hK_cpt.tendsto_subseq hpK
    have ha_tend : Filter.Tendsto (fun n => u (φ n)) Filter.atTop (nhds a) :=
      (continuous_fst.tendsto _).comp hφtend
    have hb_tend : Filter.Tendsto (fun n => w (φ n)) Filter.atTop (nhds b) :=
      (continuous_snd.tendsto _).comp hφtend
    have ha_norm : ‖a‖ = 1 := by
      have h1 : Filter.Tendsto (fun n => ‖u (φ n)‖) Filter.atTop (nhds ‖a‖) :=
        ha_tend.norm
      have h2 : (fun _ : ℕ => (1 : ℝ)) = fun n => ‖u (φ n)‖ := funext fun n => (hu (φ n)).symm
      rw [← h2] at h1
      exact (tendsto_const_nhds_iff.mp h1).symm
    have hb_le : ‖b‖ ≤ 2 := by
      exact le_of_tendsto hb_tend.norm (Filter.Eventually.of_forall fun n => hw2 (φ n))
    have hb_ge : 2 ≤ ‖b‖ := by
      have hlow_tend : Filter.Tendsto (fun n : ℕ => 2 - 1 / ((φ n : ℝ) + 1)) Filter.atTop (nhds 2) := by
        have hφ_top : Filter.Tendsto (fun n : ℕ => (φ n : ℝ) + 1) Filter.atTop Filter.atTop :=
          Filter.tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hφmono.tendsto_atTop)
        have hinv : Filter.Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) Filter.atTop (nhds 0) := by
          simp_rw [one_div]
          exact tendsto_inv_atTop_zero.comp hφ_top
        simpa using tendsto_const_nhds.sub hinv
      exact le_of_tendsto_of_tendsto hlow_tend hb_tend.norm
        (Filter.Eventually.of_forall fun n => hwlow (φ n))
    have hb_norm : ‖b‖ = 2 := le_antisymm hb_le hb_ge
    have hab_le : ‖a - b‖ ≤ 1 := by
      exact le_of_tendsto (ha_tend.sub hb_tend).norm
        (Filter.Eventually.of_forall fun n => huw (φ n))
    have hab_ge : 1 ≤ ‖a - b‖ := by
      have h1 : ‖b‖ ≤ ‖b - a‖ + ‖a‖ := by
        calc ‖b‖ = ‖(b - a) + a‖ := by simp
          _ ≤ ‖b - a‖ + ‖a‖ := norm_add_le _ _
      rw [hb_norm, ha_norm, norm_sub_rev] at h1
      linarith
    have hab_norm : ‖a - b‖ = 1 := le_antisymm hab_le hab_ge
    have horth_lim : orth (a - b) b := by
      intro t
      have hLHS : Filter.Tendsto (fun n => ‖u (φ n) - w (φ n)‖) Filter.atTop (nhds ‖a - b‖) :=
        (ha_tend.sub hb_tend).norm
      have hRHS : Filter.Tendsto (fun n => ‖(u (φ n) - w (φ n)) + t • w (φ n)‖)
          Filter.atTop (nhds ‖(a - b) + t • b‖) :=
        ((ha_tend.sub hb_tend).add (hb_tend.const_smul t)).norm
      exact le_of_tendsto_of_tendsto hLHS hRHS
        (Filter.Eventually.of_forall fun n => horth (φ n) t)
    refine ⟨a, b - a, fun c d => ?_⟩
    have hx : ‖a‖ = 1 := ha_norm
    have hy : ‖b - a‖ = 1 := by rw [norm_sub_rev]; exact hab_norm
    have hxy_add : ‖a + (b - a)‖ = 2 := by simpa using hb_norm
    have hxy_sub : ‖a - (b - a)‖ = 2 := by
      apply le_antisymm
      · calc ‖a - (b - a)‖ ≤ ‖a‖ + ‖b - a‖ := norm_sub_le _ _
          _ = 2 := by rw [hx, hy]; norm_num
      · have hhalf := horth_lim (1 / 2 : ℝ)
        have heq : (a - b) + (1 / 2 : ℝ) • b = (1 / 2 : ℝ) • (a - (b - a)) := by
          rw [smul_sub, smul_sub]
          module
        rw [hab_norm, heq, norm_smul, Real.norm_of_nonneg (by norm_num)] at hhalf
        linarith
    rcases le_total 0 c with hc | hc <;> rcases le_total 0 d with hd | hd
    · rw [abs_of_nonneg hc, abs_of_nonneg hd]
      exact norm_smul_add_of_unit_sum hx hy hxy_add hc hd
    · rw [abs_of_nonneg hc, abs_of_nonpos hd]
      have hd' : 0 ≤ -d := neg_nonneg.mpr hd
      have heq : c • a + d • (b - a) = c • a + (-d) • (-(b - a)) := by
        rw [smul_neg, neg_smul, neg_neg]
      rw [heq]
      have hy' : ‖-(b - a)‖ = 1 := by rw [norm_neg, hy]
      have hsum : ‖a + -(b - a)‖ = 2 := by rw [← sub_eq_add_neg, hxy_sub]
      exact norm_smul_add_of_unit_sum hx hy' hsum hc hd'
    · rw [abs_of_nonpos hc, abs_of_nonneg hd]
      have hc' : 0 ≤ -c := neg_nonneg.mpr hc
      have heq : c • a + d • (b - a) = (-c) • (-a) + d • (b - a) := by
        rw [smul_neg, neg_smul, neg_neg]
      rw [heq]
      have hx' : ‖-a‖ = 1 := by rw [norm_neg, hx]
      have hsum : ‖-a + (b - a)‖ = 2 := by
        have : -a + (b - a) = -(a - (b - a)) := by abel
        rw [this, norm_neg, hxy_sub]
      exact norm_smul_add_of_unit_sum hx' hy hsum hc' hd
    · rw [abs_of_nonpos hc, abs_of_nonpos hd]
      have hc' : 0 ≤ -c := neg_nonneg.mpr hc
      have hd' : 0 ≤ -d := neg_nonneg.mpr hd
      have heq : c • a + d • (b - a) = (-c) • (-a) + (-d) • (-(b - a)) := by
        rw [smul_neg, neg_smul, neg_neg, smul_neg, neg_smul, neg_neg]
      rw [heq]
      have hx' : ‖-a‖ = 1 := by rw [norm_neg, hx]
      have hy' : ‖-(b - a)‖ = 1 := by rw [norm_neg, hy]
      have hsum : ‖-a + -(b - a)‖ = 2 := by
        have : -a + -(b - a) = -(a + (b - a)) := by abel
        rw [this, norm_neg, hxy_add]
      exact norm_smul_add_of_unit_sum hx' hy' hsum hc' hd'
  · rintro ⟨x, y, hsq⟩ C hC hsome
    rw [someBound_iff_everyBound] at hsome
    have hbest : best (ℝ ∙ (x + y)) x (x + y) := by
      refine ⟨Submodule.mem_span_singleton_self _, fun w hw => ?_⟩
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have h1 : ‖x - (x + y)‖ = 1 := by
        have : x - (x + y) = (0 : ℝ) • x + (-1 : ℝ) • y := by simp
        rw [this, hsq]
        norm_num
      have h2 : ‖x - t • (x + y)‖ = |1 - t| + |t| := by
        have : x - t • (x + y) = (1 - t) • x + (-t) • y := by
          rw [smul_add, sub_smul, one_smul, neg_smul]; abel
        rw [this, hsq, abs_neg]
      rw [h1, h2]
      linarith [le_abs_self (1 - t), le_abs_self t]
    have hle := hsome (ℝ ∙ (x + y)) x (x + y) hbest
    have hx1 : ‖x‖ = 1 := by simpa using hsq 1 0
    have hxy2 : ‖x + y‖ = 2 := by simpa using (hsq 1 1).trans (by norm_num)
    rw [hx1, hxy2, mul_one] at hle
    linarith

theorem OMA.solution : type_of% @OMA.S_mo_471674.main := by
  intro E _ _ _
  refine ⟨someBound_iff_everyBound, someBound_one_iff_orth_symm, someBound_two,
    neg_someBound_lt_two_iff_hasSquare⟩
