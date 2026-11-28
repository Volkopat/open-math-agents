import OMAStatements.S_mo_415722

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace OMA.Mo415722

open OMA.S_mo_415722

private abbrev target := Icc (-1 / 2 : ℝ) (1 / 2)

private theorem target_volume : volume target = 1 := by norm_num [target, Real.volume_Icc]

private def closePairs (c : ℝ) : Set (ℝ × ℝ) := {p | dist p.1 p.2 ≤ c}

private theorem closePairs_measurable (c : ℝ) : MeasurableSet (closePairs c) :=
  measurableSet_le (by fun_prop : Measurable (fun p : ℝ × ℝ ↦ dist p.1 p.2)) measurable_const

private theorem I_eq_pairs (c : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    I c A = ((volume.restrict A).prod (volume.restrict A)) (closePairs c) := by
  let μ := volume.restrict A
  let C := Icc (-c) c
  let D : Set (ℝ × ℝ) := {p | p.2 - p.1 ∈ A}
  have hD : MeasurableSet D := hA.preimage (by fun_prop : Measurable (fun p : ℝ × ℝ ↦ p.2 - p.1))
  have hex : I c A = ((volume.restrict C).prod μ) D := by
    rw [Measure.prod_apply hD]
    apply lintegral_congr
    intro x
    have hx : MeasurableSet (Prod.mk x ⁻¹' D) := hD.preimage (by fun_prop)
    rw [show μ (Prod.mk x ⁻¹' D) = volume ((Prod.mk x ⁻¹' D) ∩ A) from
      Measure.restrict_apply hx, inter_comm]
    rfl
  rw [hex, Measure.prod_apply_symm hD, Measure.prod_apply (closePairs_measurable c)]
  apply lintegral_congr
  intro y
  have hy : MeasurableSet ((fun x : ℝ ↦ (x, y)) ⁻¹' D) := hD.preimage (by fun_prop)
  have hshift : (fun x : ℝ ↦ (x, y)) ⁻¹' D ∩ C =
      (fun x : ℝ ↦ y - x) ⁻¹' (A ∩ Icc (y - c) (y + c)) := by
    ext x
    change (y - x ∈ A ∧ -c ≤ x ∧ x ≤ c) ↔
      (y - x ∈ A ∧ y - c ≤ y - x ∧ y - x ≤ y + c)
    grind
  have hband : Prod.mk y ⁻¹' closePairs c = Icc (y - c) (y + c) := by
    ext x
    change dist y x ≤ c ↔ y - c ≤ x ∧ x ≤ y + c
    rw [Real.dist_eq, abs_le]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linarith, by linarith⟩
  show (volume.restrict C) ((fun x : ℝ ↦ (x, y)) ⁻¹' D) =
    μ (Prod.mk y ⁻¹' closePairs c)
  rw [Measure.restrict_apply hy, hshift, hband,
    (volume.measurePreserving_sub_left y).measure_preimage (hA.inter measurableSet_Icc).nullMeasurableSet,
    show μ (Icc (y - c) (y + c)) = volume (Icc (y - c) (y + c) ∩ A) from
      Measure.restrict_apply measurableSet_Icc, inter_comm]

private theorem cdf_contraction {A : Set ℝ} [IsProbabilityMeasure (volume.restrict A)]
    (x y : ℝ) : dist (cdf (volume.restrict A) x) (cdf (volume.restrict A) y) ≤ dist x y := by
  let μ := volume.restrict A
  have hmono : Monotone (cdf μ) := monotone_cdf μ
  have haux (a b : ℝ) (hab : a ≤ b) : cdf μ b - cdf μ a ≤ b - a := by
    have hset : Iic b \ Iic a = Ioc a b := by ext z; simp [and_comm]
    rw [cdf_eq_real, cdf_eq_real, ← measureReal_sdiff (Iic_subset_Iic.mpr hab)
      measurableSet_Iic, hset]
    have h : μ.real (Ioc a b) = volume.real (Ioc a b ∩ A) :=
      measureReal_restrict_apply measurableSet_Ioc
    rw [h, ← Real.volume_real_Ioc_of_le hab]
    exact measureReal_mono inter_subset_left (by simp [Real.volume_Ioc])
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total x y with h | h
  · rw [abs_sub_comm (cdf μ x), abs_sub_comm x, abs_of_nonneg (sub_nonneg.mpr (hmono h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact haux _ _ h
  · rw [abs_of_nonneg (sub_nonneg.mpr (hmono h)), abs_of_nonneg (sub_nonneg.mpr h)]
    exact haux _ _ h

private theorem cdf_attains {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ : ℝ → ℝ)) {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    ∃ x, cdf μ x = r := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually_lt_const hr).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt hr').exists
  have hab : a ≤ b := by
    by_contra! hh
    linarith [monotone_cdf μ hh.le]
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc hab hc.continuousOn
    (show r ∈ Icc (cdf μ a) (cdf μ b) from ⟨ha.le, hb.le⟩)
  exact ⟨x, hx⟩

private theorem cdf_uniform {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ : ℝ → ℝ)) {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    μ.real {x | cdf μ x ≤ r} = r := by
  let E := {x | cdf μ x ≤ r}
  apply le_antisymm
  · by_contra! h
    have hone : μ.real E ≤ 1 := measureReal_le_one
    let s := (r + μ.real E) / 2
    have hs : 0 < s := by dsimp [s]; linarith
    have hs' : s < 1 := by dsimp [s]; linarith
    obtain ⟨b, hb⟩ := cdf_attains hc hs hs'
    have hsub : E ⊆ Iic b := by
      intro x hx
      change cdf μ x ≤ r at hx
      change x ≤ b
      by_contra! hn
      have hm := monotone_cdf μ hn.le
      rw [hb] at hm
      dsimp [s] at hm
      linarith
    have hh := measureReal_mono (μ := μ) hsub
    rw [← cdf_eq_real, hb] at hh
    dsimp [s] at hh
    linarith
  · rcases eq_or_lt_of_le hr with rfl | hp
    · exact measureReal_nonneg
    obtain ⟨a, ha⟩ := cdf_attains hc hp hr'
    have hsub : Iic a ⊆ E := by
      intro x hx
      exact (monotone_cdf μ hx).trans_eq ha
    have hh := measureReal_mono (μ := μ) hsub
    rwa [← cdf_eq_real, ha] at hh

private theorem centered_uniform {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ : ℝ → ℝ)) :
    μ.map (fun x ↦ cdf μ x - 1 / 2) = volume.restrict target := by
  let T (x : ℝ) := cdf μ x - 1 / 2
  have mT : Measurable T := (hc.sub continuous_const).measurable
  change μ.map T = _
  apply Measure.ext_of_Iic
  intro a
  have hfin : (volume.restrict target) (Iic a) ≠ ∞ := by
    rw [Measure.restrict_apply measurableSet_Iic]
    exact ((measure_mono inter_subset_right).trans_lt (by rw [target_volume]; exact ENNReal.one_lt_top)).ne
  apply (measureReal_eq_measureReal_iff (measure_ne_top _ _) hfin).mp
  rw [map_measureReal_apply mT measurableSet_Iic, measureReal_restrict_apply measurableSet_Iic]
  have hcut : Iic a ∩ target = Icc (-1 / 2 : ℝ) (min a (1 / 2)) := by
    ext x
    simp [target]
    tauto
  rw [hcut, Real.volume_real_Icc]
  have hpre : T ⁻¹' Iic a = {x | cdf μ x ≤ a + 1 / 2} := by
    ext x
    change cdf μ x - (1 / 2 : ℝ) ≤ a ↔ cdf μ x ≤ a + 1 / 2
    exact sub_le_iff_le_add
  rw [hpre]
  rcases lt_or_ge a (-1 / 2) with ha | ha
  · have hempty : {x | cdf μ x ≤ a + 1 / 2} = ∅ := by
      apply eq_empty_of_forall_notMem
      intro x hx
      change cdf μ x ≤ a + 1 / 2 at hx
      linarith [cdf_nonneg μ x]
    rw [hempty, measureReal_empty, min_eq_left (by linarith : a ≤ 1 / 2),
      max_eq_right (by linarith)]
  · rcases lt_or_ge a (1 / 2) with ha' | ha'
    · rw [cdf_uniform hc (by linarith : 0 ≤ a + 1 / 2) (by linarith : a + 1 / 2 < 1),
        min_eq_left ha'.le, max_eq_left (by linarith)]
      ring
    · have huniv : {x | cdf μ x ≤ a + 1 / 2} = univ := by
        apply eq_univ_of_forall
        intro x
        change cdf μ x ≤ a + 1 / 2
        linarith [cdf_le_one μ x]
      rw [huniv, measureReal_def, measure_univ, ENNReal.toReal_one, min_eq_right ha']
      norm_num

private theorem result : type_of% @OMA.S_mo_415722.main := by
  intro c _ A hA hvol
  let μ := volume.restrict A
  let : IsProbabilityMeasure μ := ⟨by simpa [μ] using hvol⟩
  have hcont : Continuous (cdf μ : ℝ → ℝ) :=
    (LipschitzWith.of_dist_le_mul (K := 1) fun x y ↦ by
      simpa using cdf_contraction (A := A) x y).continuous
  let T (x : ℝ) := cdf μ x - 1 / 2
  have mT : Measurable T := (hcont.sub continuous_const).measurable
  have hmap : μ.map T = volume.restrict target := centered_uniform hcont
  rw [I_eq_pairs c hA, I_eq_pairs c measurableSet_Icc, ← hmap,
    Measure.map_prod_map _ _ mT mT, Measure.map_apply (mT.prodMap mT) (closePairs_measurable c)]
  apply measure_mono
  intro p hp
  change dist (T p.1) (T p.2) ≤ c
  change dist p.1 p.2 ≤ c at hp
  have h := cdf_contraction (A := A) p.1 p.2
  simp only [Real.dist_eq, T] at h ⊢
  simpa using h.trans (by simpa [Real.dist_eq] using hp)

end OMA.Mo415722

theorem OMA.solution : type_of% @OMA.S_mo_415722.main := OMA.Mo415722.result
