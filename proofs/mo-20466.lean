import OMAStatements.S_mo_20466

open Set Filter

private noncomputable def mo20466_p (t : ℝ) : ℝ × ℝ := (t ^ 2, t ^ 3 - t)

private noncomputable def mo20466_gamma (t : ℝ) : (ℝ × ℝ) × ℝ := (mo20466_p t, t)

private lemma mo20466_continuous_gamma : Continuous mo20466_gamma := by
  refine Continuous.prodMk (Continuous.prodMk ?_ ?_) continuous_id
  · exact continuous_id.pow 2
  · exact (continuous_id.pow 3).sub continuous_id

private lemma mo20466_fiber {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 1)
    {w : (ℝ × ℝ) × ℝ}
    (hw : w ∈ closure (convexHull ℝ (mo20466_gamma '' Icc (-1 : ℝ) 1)))
    (hw1 : w.1 = mo20466_p t₀) : w.2 = t₀ := by
  have ht₀_abs : |t₀| < 1 := abs_lt.mpr ht₀
  have hc_pos : 0 < (1 - |t₀|) ^ 2 := sq_pos_of_pos (sub_pos.mpr ht₀_abs)
  set c : ℝ := (1 - |t₀|) ^ 2
  have h_eps : ∀ ε : ℝ, 0 < ε → |w.2 - t₀| ≤ ε := by
    intro ε hε
    set M : ℝ := (4 * ε * c)⁻¹
    have hM_pos : 0 < M := inv_pos.mpr (by positivity)
    let rhs : (ℝ × ℝ) × ℝ → ℝ := fun u =>
      ε + M * ((t₀ ^ 4 + t₀ ^ 2) - ((3 * t₀ ^ 2 - 1) * u.1.1 - 2 * t₀ * u.1.2))
    let Sε : Set ((ℝ × ℝ) × ℝ) := { u | |u.2 - t₀| ≤ rhs u }
    have hSε_closed : IsClosed Sε := by
      refine isClosed_le ?_ ?_
      · exact (continuous_snd.sub continuous_const).abs
      · exact continuous_const.add (continuous_const.mul
          (continuous_const.sub ((continuous_const.mul (continuous_fst.comp continuous_fst)).sub
            (continuous_const.mul (continuous_snd.comp continuous_fst)))))
    have hSε_conv : Convex ℝ Sε := by
      intro u hu v hv a b ha hb hab
      dsimp only [Sε] at hu hv ⊢
      rw [mem_ofPred_eq, abs_le] at hu hv ⊢
      have h_eq : rhs (a • u + b • v) = a * rhs u + b * rhs v := by
        simp only [rhs, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
        calc ε + M * ((t₀ ^ 4 + t₀ ^ 2) -
              ((3 * t₀ ^ 2 - 1) * (a * u.1.1 + b * v.1.1) - 2 * t₀ * (a * u.1.2 + b * v.1.2)))
            = 1 * ε + M * (1 * (t₀ ^ 4 + t₀ ^ 2) -
              ((3 * t₀ ^ 2 - 1) * (a * u.1.1 + b * v.1.1) - 2 * t₀ * (a * u.1.2 + b * v.1.2))) := by
                ring
          _ = (a + b) * ε + M * ((a + b) * (t₀ ^ 4 + t₀ ^ 2) -
              ((3 * t₀ ^ 2 - 1) * (a * u.1.1 + b * v.1.1) - 2 * t₀ * (a * u.1.2 + b * v.1.2))) := by
                rw [hab]
          _ = a * (ε + M * ((t₀ ^ 4 + t₀ ^ 2) - ((3 * t₀ ^ 2 - 1) * u.1.1 - 2 * t₀ * u.1.2))) +
              b * (ε + M * ((t₀ ^ 4 + t₀ ^ 2) - ((3 * t₀ ^ 2 - 1) * v.1.1 - 2 * t₀ * v.1.2))) := by
                ring
      have hz_eq : (a • u + b • v).2 - t₀ = a * (u.2 - t₀) + b * (v.2 - t₀) := by
        simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        calc a * u.2 + b * v.2 - t₀ = a * u.2 + b * v.2 - 1 * t₀ := by ring
          _ = a * u.2 + b * v.2 - (a + b) * t₀ := by rw [hab]
          _ = a * (u.2 - t₀) + b * (v.2 - t₀) := by ring
      constructor
      · nlinarith [hu.1, hv.1]
      · nlinarith [hu.2, hv.2]
    have h_sub : mo20466_gamma '' Icc (-1 : ℝ) 1 ⊆ Sε := by
      rintro u ⟨t, ht, rfl⟩
      dsimp only [Sε]
      rw [mem_ofPred_eq]
      simp only [mo20466_gamma, mo20466_p, rhs]
      have ht_abs : |t| ≤ 1 := abs_le.mpr ht
      have h_tt₀ : -|t₀| ≤ t₀ * t := by
        have h1 : |t₀ * t| ≤ |t₀| := by
          rw [abs_mul]
          nlinarith [abs_nonneg t₀, ht_abs]
        exact neg_le_of_abs_le h1
      have h_quad : c ≤ t₀ ^ 2 + 2 * t₀ * t + 1 := by
        have hsq : |t₀| ^ 2 = t₀ ^ 2 := sq_abs t₀
        nlinarith [sq_nonneg (1 - |t₀|)]
      have h_id : (t₀ ^ 4 + t₀ ^ 2) - ((3 * t₀ ^ 2 - 1) * t ^ 2 - 2 * t₀ * (t ^ 3 - t)) =
          (t₀ ^ 2 + 2 * t₀ * t + 1) * (t - t₀) ^ 2 := by ring
      have h_lower : c * (t - t₀) ^ 2 ≤
          (t₀ ^ 4 + t₀ ^ 2) - ((3 * t₀ ^ 2 - 1) * t ^ 2 - 2 * t₀ * (t ^ 3 - t)) := by
        rw [h_id]
        exact mul_le_mul_of_nonneg_right h_quad (sq_nonneg (t - t₀))
      have hMc : M * c = (4 * ε)⁻¹ := by
        simp only [M]
        field_simp [hε.ne', hc_pos.ne']
      have h_amgm : |t - t₀| ≤ ε + (4 * ε)⁻¹ * (t - t₀) ^ 2 := by
        rw [abs_le]
        have h_pos4 : 0 < 4 * ε := by linarith
        constructor
        · have : 0 ≤ (4 * ε)⁻¹ * (2 * ε + (t - t₀)) ^ 2 :=
            mul_nonneg (inv_nonneg.mpr h_pos4.le) (sq_nonneg _)
          have h_id1 : (4 * ε)⁻¹ * (2 * ε + (t - t₀)) ^ 2 =
              ε + (4 * ε)⁻¹ * (t - t₀) ^ 2 + (t - t₀) := by
            field_simp [hε.ne']
            ring
          linarith
        · have : 0 ≤ (4 * ε)⁻¹ * (2 * ε - (t - t₀)) ^ 2 :=
            mul_nonneg (inv_nonneg.mpr h_pos4.le) (sq_nonneg _)
          have h_id2 : (4 * ε)⁻¹ * (2 * ε - (t - t₀)) ^ 2 =
              ε + (4 * ε)⁻¹ * (t - t₀) ^ 2 - (t - t₀) := by
            field_simp [hε.ne']
            ring
          linarith
      have h_mul : M * (c * (t - t₀) ^ 2) ≤
          M * ((t₀ ^ 4 + t₀ ^ 2) - ((3 * t₀ ^ 2 - 1) * t ^ 2 - 2 * t₀ * (t ^ 3 - t))) :=
        mul_le_mul_of_nonneg_left h_lower hM_pos.le
      calc |t - t₀| ≤ ε + (4 * ε)⁻¹ * (t - t₀) ^ 2 := h_amgm
        _ = ε + M * (c * (t - t₀) ^ 2) := by rw [← hMc]; ring
        _ ≤ ε + M * ((t₀ ^ 4 + t₀ ^ 2) - ((3 * t₀ ^ 2 - 1) * t ^ 2 - 2 * t₀ * (t ^ 3 - t))) := by
            linarith
    have hw_in : w ∈ Sε := closure_minimal (convexHull_min h_sub hSε_conv) hSε_closed hw
    dsimp only [Sε] at hw_in
    rw [mem_ofPred_eq] at hw_in
    dsimp only [rhs] at hw_in
    rw [hw1] at hw_in
    simp only [mo20466_p] at hw_in
    have h_zero : (t₀ ^ 4 + t₀ ^ 2) - ((3 * t₀ ^ 2 - 1) * t₀ ^ 2 - 2 * t₀ * (t₀ ^ 3 - t₀)) = 0 := by
      ring
    rw [h_zero, mul_zero, add_zero] at hw_in
    exact hw_in
  by_contra hne
  have hpos : 0 < |w.2 - t₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have := h_eps (|w.2 - t₀| / 2) (half_pos hpos)
  linarith

private lemma mo20466_part1 :
    ∃ K : Set ((ℝ × ℝ) × ℝ), K.Nonempty ∧ IsCompact K ∧ Convex ℝ K ∧
      ¬ OMA.S_mo_20466.HasSection K Prod.fst := by
  let K : Set ((ℝ × ℝ) × ℝ) := closure (convexHull ℝ (mo20466_gamma '' Icc (-1 : ℝ) 1))
  refine ⟨K, ?_, ?_, (convex_convexHull ℝ _).closure, ?_⟩
  · refine ⟨mo20466_gamma 0, subset_closure (subset_convexHull _ _ ⟨0, by norm_num, rfl⟩)⟩
  · have h_comp : IsCompact (mo20466_gamma '' Icc (-1 : ℝ) 1) :=
      (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image mo20466_continuous_gamma
    exact isCompact_iff_totallyBounded_isComplete.mpr
      ⟨h_comp.totallyBounded.convexHull.closure, isClosed_closure.isComplete⟩
  · rintro ⟨g, hg_cont, hg_spec⟩
    have hy1_mem : (1, 0) ∈ Prod.fst '' K :=
      ⟨mo20466_gamma 1, subset_closure (subset_convexHull _ _ ⟨1, by norm_num, rfl⟩),
        by simp [mo20466_gamma, mo20466_p]⟩
    let y₁ : Prod.fst '' K := ⟨(1, 0), hy1_mem⟩
    have ht_mem : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ∈ Ioo (-1 : ℝ) 1 := by
      intro n
      have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hle : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num)
        linarith [Nat.cast_nonneg (α := ℝ) n]
      constructor <;> linarith [one_div_pos.mpr hn]
    have hs_mem : ∀ n : ℕ, -1 + 1 / ((n : ℝ) + 2) ∈ Ioo (-1 : ℝ) 1 := by
      intro n
      have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hle : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num)
        linarith [Nat.cast_nonneg (α := ℝ) n]
      constructor <;> linarith [one_div_pos.mpr hn]
    let xseq : ℕ → (Prod.fst '' K) := fun n =>
      ⟨mo20466_p (1 - 1 / ((n : ℝ) + 2)),
        ⟨mo20466_gamma (1 - 1 / ((n : ℝ) + 2)),
          subset_closure (subset_convexHull _ _
            ⟨1 - 1 / ((n : ℝ) + 2), Ioo_subset_Icc_self (ht_mem n), rfl⟩),
          rfl⟩⟩
    let sseq : ℕ → (Prod.fst '' K) := fun n =>
      ⟨mo20466_p (-1 + 1 / ((n : ℝ) + 2)),
        ⟨mo20466_gamma (-1 + 1 / ((n : ℝ) + 2)),
          subset_closure (subset_convexHull _ _
            ⟨-1 + 1 / ((n : ℝ) + 2), Ioo_subset_Icc_self (hs_mem n), rfl⟩),
          rfl⟩⟩
    have h_inv_tendsto : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (nhds 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      convert h using 1
      ext n
      simp [Function.comp_apply]
      ring
    have ht_tendsto : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub h_inv_tendsto
    have hs_tendsto : Tendsto (fun n : ℕ => -1 + 1 / ((n : ℝ) + 2)) atTop (nhds (-1)) := by
      simpa using tendsto_const_nhds.add h_inv_tendsto
    have hp_cont : Continuous mo20466_p :=
      Continuous.prodMk (continuous_id.pow 2) ((continuous_id.pow 3).sub continuous_id)
    have hx_tendsto : Tendsto xseq atTop (nhds y₁) := by
      rw [tendsto_subtype_rng]
      have hp1 : mo20466_p 1 = (1, 0) := by norm_num [mo20466_p]
      change Tendsto (fun n : ℕ => mo20466_p (1 - 1 / ((n : ℝ) + 2))) atTop (nhds (1, 0))
      rw [← hp1]
      exact hp_cont.continuousAt.tendsto.comp ht_tendsto
    have hsx_tendsto : Tendsto sseq atTop (nhds y₁) := by
      rw [tendsto_subtype_rng]
      have hpm1 : mo20466_p (-1) = (1, 0) := by norm_num [mo20466_p]
      change Tendsto (fun n : ℕ => mo20466_p (-1 + 1 / ((n : ℝ) + 2))) atTop (nhds (1, 0))
      rw [← hpm1]
      exact hp_cont.continuousAt.tendsto.comp hs_tendsto
    have hgx_tendsto : Tendsto (fun n : ℕ => (g (xseq n)).2) atTop (nhds (g y₁).2) :=
      (continuous_snd.comp hg_cont).continuousAt.tendsto.comp hx_tendsto
    have hgs_tendsto : Tendsto (fun n : ℕ => (g (sseq n)).2) atTop (nhds (g y₁).2) :=
      (continuous_snd.comp hg_cont).continuousAt.tendsto.comp hsx_tendsto
    have hgx_eq : (fun n : ℕ => (g (xseq n)).2) = fun n : ℕ => 1 - 1 / ((n : ℝ) + 2) := by
      ext n
      exact mo20466_fiber (ht_mem n) (hg_spec (xseq n)).1 (hg_spec (xseq n)).2
    have hgs_eq : (fun n : ℕ => (g (sseq n)).2) = fun n : ℕ => -1 + 1 / ((n : ℝ) + 2) := by
      ext n
      exact mo20466_fiber (hs_mem n) (hg_spec (sseq n)).1 (hg_spec (sseq n)).2
    rw [hgx_eq] at hgx_tendsto
    rw [hgs_eq] at hgs_tendsto
    have h1 : (g y₁).2 = 1 := tendsto_nhds_unique hgx_tendsto ht_tendsto
    have h2 : (g y₁).2 = -1 := tendsto_nhds_unique hgs_tendsto hs_tendsto
    linarith

private lemma mo20466_part2 :
    ∀ n : ℕ, ∀ S : Set (Fin n → ℝ), S.Nonempty → IsCompact S → Convex ℝ S →
      ∀ f : (Fin n → ℝ) →L[ℝ] ℝ, OMA.S_mo_20466.HasSection S f := by
  intro n S hS_ne hS_comp hS_conv f
  have himg_ne : (f '' S).Nonempty := hS_ne.image f
  have himg_comp : IsCompact (f '' S) := hS_comp.image f.continuous
  obtain ⟨a, ha_mem, ha_le⟩ := himg_comp.exists_isLeast himg_ne
  obtain ⟨b, hb_mem, hb_ge⟩ := himg_comp.exists_isGreatest himg_ne
  have hab_le : a ≤ b := ha_le hb_mem
  obtain ⟨xa, hxa_mem, hxa_eq⟩ := ha_mem
  obtain ⟨xb, hxb_mem, hxb_eq⟩ := hb_mem
  by_cases hab : a = b
  · refine ⟨fun _ => xa, continuous_const, fun y => ⟨hxa_mem, ?_⟩⟩
    have hya : a ≤ (y : ℝ) := ha_le y.2
    have hyb : (y : ℝ) ≤ b := hb_ge y.2
    linarith [hxa_eq]
  · have hab_lt : a < b := lt_of_le_of_ne hab_le hab
    have hba_pos : 0 < b - a := sub_pos.mpr hab_lt
    let t : (f '' S) → ℝ := fun y => ((y : ℝ) - a) / (b - a)
    let g : (f '' S) → (Fin n → ℝ) := fun y => (1 - t y) • xa + t y • xb
    have ht_cont : Continuous t :=
      (continuous_subtype_val.sub continuous_const).div_const (b - a)
    have hg_cont : Continuous g :=
      ((continuous_const.sub ht_cont).smul continuous_const).add
        (ht_cont.smul continuous_const)
    refine ⟨g, hg_cont, fun y => ?_⟩
    have hya : a ≤ (y : ℝ) := ha_le y.2
    have hyb : (y : ℝ) ≤ b := hb_ge y.2
    have ht0 : 0 ≤ t y := div_nonneg (sub_nonneg.mpr hya) hba_pos.le
    have ht1 : t y ≤ 1 := (div_le_one hba_pos).mpr (sub_le_sub_right hyb a)
    refine ⟨?_, ?_⟩
    · exact hS_conv hxa_mem hxb_mem (sub_nonneg.mpr ht1) ht0 (sub_add_cancel 1 (t y))
    · simp only [g, map_add, map_smul, smul_eq_mul, hxa_eq, hxb_eq, t]
      field_simp [hba_pos.ne']
      ring

theorem OMA.solution : type_of% @OMA.S_mo_20466.main :=
  ⟨mo20466_part1, mo20466_part2⟩
