import FormalConjectures.Wikipedia.MoserWorm
import Mathlib

/-!
# A finite-placement reduction for Moser’s worm upper bound

The fixed rational triangle contains the scaled triangle of Deng (arXiv:2609.04591).
Compactness turns the finite placements into a single placement for the worm.
The cover can then be enlarged to the exact area in the pinned statement.
Thanks to @PABixn for the exact-area padding idea.
-/

open EuclideanGeometry MeasureTheory Set
open scoped ENNReal

namespace OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1

private theorem covered_of_finite {T : Set ℝ²} (hT : IsCompact T)
    (hFinite : ∀ (s : Finset (Set.Icc (0 : ℝ) 1)) (g : ↥s → ℝ²),
      LipschitzWith 1 g →
      ∃ (e : ℝ² ≃ₗᵢ[ℝ] ℝ²) (v : ℝ²), e.toLinearEquiv.det = 1 ∧
        ∀ t, e (g t) + v ∈ T) :
    T ∈ MoserWorm.WormCovers := by
  classical
  refine ⟨hT.isClosed.measurableSet, ?_⟩
  rintro w ⟨f, hf, rfl⟩
  let Z := Set.Icc (0 : ℝ) 1
  let t₀ : Z := ⟨0, by change (0 : ℝ) ∈ Set.Icc 0 1; norm_num⟩
  let U := (ℝ² →L[ℝ] ℝ²) × ℝ²
  let K : Set U := Metric.closedBall 0 1 ×ˢ T
  have hK : IsCompact K := (isCompact_closedBall _ _).prod hT
  let R (s : Finset Z) : Set U := {p ∈ K |
    (∀ x, ‖p.1 x‖ = ‖x‖) ∧ p.1.det = 1 ∧
    ∀ t ∈ s, p.1 (f t - f t₀) + p.2 ∈ T}
  have hClosed (s : Finset Z) : IsClosed (R s) := by
    have hEval (x : ℝ²) : Continuous fun p : U => p.1 x :=
      (ContinuousLinearMap.apply ℝ ℝ² x).continuous.comp continuous_fst
    have hN : IsClosed {p : U | ∀ x, ‖p.1 x‖ = ‖x‖} := by
      rw [Set.ofPred_forall]
      apply isClosed_iInter
      intro x
      exact isClosed_eq (hEval x).norm continuous_const
    have hD : IsClosed {p : U | p.1.det = 1} :=
      isClosed_eq (ContinuousLinearMap.continuous_det.comp continuous_fst) continuous_const
    have hM : IsClosed {p : U | ∀ t ∈ s, p.1 (f t - f t₀) + p.2 ∈ T} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun t => isClosed_iInter fun _ =>
        hT.isClosed.preimage ((hEval (f t - f t₀)).add continuous_snd)
    exact hK.isClosed.inter (hN.inter (hD.inter hM))
  have hCompact (s : Finset Z) : IsCompact (R s) :=
    hK.of_isClosed_subset (hClosed s) (fun _ h => h.1)
  have hDirected : Directed (· ⊇ ·) R := by
    intro s₁ s₂
    refine ⟨s₁ ∪ s₂, ?_, ?_⟩
    · intro p h
      exact ⟨h.1, h.2.1, h.2.2.1, fun t ht => h.2.2.2 t (Finset.mem_union_left _ ht)⟩
    · intro p h
      exact ⟨h.1, h.2.1, h.2.2.1, fun t ht => h.2.2.2 t (Finset.mem_union_right _ ht)⟩
  have hNonempty (s : Finset Z) : (R s).Nonempty := by
    let s' := insert t₀ s
    let g : ↥s' → ℝ² := fun t => f t
    have hg : LipschitzWith 1 g := by
      intro a b
      exact hf a.1 b.1
    obtain ⟨e, v, hd, hmem⟩ := hFinite s' g hg
    let L := e.toLinearIsometry.toContinuousLinearMap
    have hNorm : ∀ x, ‖L x‖ = ‖x‖ := e.norm_map
    have hL : L ∈ Metric.closedBall (0 : ℝ² →L[ℝ] ℝ²) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact L.opNorm_le_bound zero_le_one (fun x => by rw [hNorm, one_mul])
    have hv : e (f t₀) + v ∈ T := hmem ⟨t₀, Finset.mem_insert_self ..⟩
    have hdet : L.det = 1 := by
      change LinearMap.det (e.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²) = 1
      simpa only [LinearEquiv.coe_det, Units.val_one] using
        (congrArg (fun d : ℝˣ => (d : ℝ)) hd)
    refine ⟨(L, e (f t₀) + v), ⟨⟨hL, hv⟩, hNorm, hdet, ?_⟩⟩
    intro t ht
    change e (f t - f t₀) + (e (f t₀) + v) ∈ T
    rw [map_sub, ← add_assoc, sub_add_cancel]
    exact hmem ⟨t, Finset.mem_insert_of_mem ht⟩
  obtain ⟨⟨L, v⟩, hp⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      R hDirected hNonempty hCompact hClosed
  have hAll (s : Finset Z) : (L, v) ∈ R s := Set.mem_iInter.mp hp s
  let li : ℝ² →ₗᵢ[ℝ] ℝ² := ⟨L.toLinearMap, (hAll ∅).2.1⟩
  let e := li.toLinearIsometryEquiv rfl
  have hd : e.toLinearEquiv.det = 1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    exact (hAll ∅).2.2.1
  have hInv : e.symm.toLinearEquiv.det = 1 := by
    change e.toLinearEquiv.symm.det = 1
    rw [LinearEquiv.det_symm, map_inv, hd, inv_one]
  refine ⟨e.symm, f t₀ - e.symm v, hInv, ?_⟩
  rintro _ ⟨t, rfl⟩
  refine ⟨e (f t - f t₀) + v, ?_, ?_⟩
  · exact (hAll {t}).2.2.2 t (by simp)
  · simp only [map_add, LinearIsometryEquiv.symm_apply_apply]
    abel

theorem triangle_subset_ball :
    {x : ℝ² | 0 ≤ x 1 ∧ |x 0| / (129 / 500 : ℝ) + x 1 / (501 / 500 : ℝ) ≤ 1} ⊆
      Metric.closedBall 0 2 := by
  intro x hx
  obtain ⟨hy, hxy⟩ := hx
  have hxabs := abs_nonneg (x 0)
  have hxle : |x 0| ≤ 129 / 500 := by linarith
  have hyle : x 1 ≤ 501 / 500 := by linarith
  have hx2 : x 0 ^ 2 ≤ (129 / 500 : ℝ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ hxabs hxle _
  have hy2 : x 1 ^ 2 ≤ (501 / 500 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hy hyle _
  rw [Metric.mem_closedBall, dist_zero_right]
  have hsq := EuclideanSpace.real_norm_sq_eq x
  rw [Fin.sum_univ_two] at hsq
  nlinarith [norm_nonneg x]

theorem triangle_compact :
    IsCompact {x : ℝ² | 0 ≤ x 1 ∧ |x 0| / (129 / 500 : ℝ) + x 1 / (501 / 500 : ℝ) ≤ 1} := by
  have h0 : Continuous fun x : ℝ² => x 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
  have h1 : Continuous fun x : ℝ² => x 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
  have hsum : Continuous fun x : ℝ² =>
      |x 0| / (129 / 500 : ℝ) + x 1 / (501 / 500 : ℝ) :=
    (h0.abs.div_const _).add (h1.div_const _)
  exact (isCompact_closedBall (0 : ℝ²) 2).of_isClosed_subset
    ((isClosed_le continuous_const h1).inter (isClosed_le hsum continuous_const))
    triangle_subset_ball

theorem deng_triangle_containment :
    let d : ℝ := 82074390584 / 84861020075
    let q : ℝ := Real.sqrt 625565 * d
    {x : ℝ² | 0 ≤ x 1 ∧ |x 0| / (197 / q) + x 1 / (766 / q) ≤ 1} ⊆
      {x : ℝ² | 0 ≤ x 1 ∧ |x 0| / (129 / 500 : ℝ) + x 1 / (501 / 500 : ℝ) ≤ 1} := by
  dsimp only
  let q := Real.sqrt (625565 : ℝ) * (82074390584 / 84861020075)
  have hRoot : (7909 / 10 : ℝ) ≤ Real.sqrt 625565 := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    norm_num
  have hQ : (7909 / 10 : ℝ) * (82074390584 / 84861020075) ≤ q :=
    mul_le_mul_of_nonneg_right hRoot (by positivity)
  have hq : 0 < q := lt_of_lt_of_le (by positivity) hQ
  have ha : 197 / q ≤ (129 / 500 : ℝ) := by
    apply (div_le_iff₀ hq).2
    linarith
  have hb : 766 / q ≤ (501 / 500 : ℝ) := by
    apply (div_le_iff₀ hq).2
    linarith
  intro x hx
  obtain ⟨hy, hxy⟩ := hx
  refine ⟨hy, ?_⟩
  have hleft := div_le_div_of_nonneg_left (abs_nonneg (x 0)) (by positivity : 0 < 197 / q) ha
  have hright := div_le_div_of_nonneg_left hy (by positivity : 0 < 766 / q) hb
  exact (add_le_add hleft hright).trans hxy

/-- Enlarging a measurable planar set by a width-varying rectangle reaches every
desired volume above its initial volume. -/
theorem exists_measurable_superset_volume_eq {X : Set ℝ²} (hX : MeasurableSet X)
    {b : ℝ≥0∞} (hvol : volume X ≤ b) :
    ∃ Y, X ⊆ Y ∧ MeasurableSet Y ∧ volume Y = b := by
  let rect (t : ℝ) : Set ℝ² :=
    (WithLp.ofLp : ℝ² → Fin 2 → ℝ) ⁻¹' Icc 0 ![t, 1]
  have measurable_rect (t : ℝ) : MeasurableSet (rect t) :=
    measurableSet_Icc.preimage (PiLp.volume_preserving_ofLp (Fin 2)).measurable
  have volume_rect (t : ℝ) : volume (rect t) = ENNReal.ofReal t := by
    dsimp only [rect]
    rw [(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
      (measurableSet_Icc (a := (0 : Fin 2 → ℝ)) (b := ![t, 1])).nullMeasurableSet,
      Real.volume_Icc_pi, Fin.prod_univ_two]
    simp
  have rect_mono {s t : ℝ} (hst : s ≤ t) : rect s ⊆ rect t := by
    intro x hx
    change WithLp.ofLp x ∈ Icc (0 : Fin 2 → ℝ) ![s, 1] at hx
    change WithLp.ofLp x ∈ Icc (0 : Fin 2 → ℝ) ![t, 1]
    refine ⟨hx.1, fun i => (hx.2 i).trans ?_⟩
    fin_cases i <;> simp [hst]
  by_cases hb : b = ⊤
  · subst b
    refine ⟨univ, subset_univ _, MeasurableSet.univ, ENNReal.eq_top_of_forall_nnreal_le ?_⟩
    intro r
    simpa only [volume_rect, ENNReal.ofReal_coe_nnreal] using
      (measure_mono (μ := (volume : Measure ℝ²)) (subset_univ (rect (r : ℝ))))
  have hXfin : volume X ≠ ⊤ := ne_of_lt (hvol.trans_lt (lt_top_iff_ne_top.mpr hb))
  have hrfin (t : ℝ) : volume (rect t) ≠ ⊤ := by
    rw [volume_rect]
    exact ENNReal.ofReal_ne_top
  have hufin (t : ℝ) : volume (X ∪ rect t) ≠ ⊤ :=
    measure_union_ne_top hXfin (hrfin t)
  let f (t : ℝ) := (volume : Measure ℝ²).real (X ∪ rect t)
  have hufmono {s t : ℝ} (hst : s ≤ t) : X ∪ rect s ⊆ X ∪ rect t :=
    union_subset_union_right X (rect_mono hst)
  have hfmono {s t : ℝ} (hst : s ≤ t) : f s ≤ f t :=
    measureReal_mono (hufmono hst) (hufin t)
  have hfinc {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : f t - f s ≤ t - s := by
    have hsub : (X ∪ rect t) \ (X ∪ rect s) ⊆ rect t \ rect s := by
      intro x hx
      exact ⟨hx.1.resolve_left (fun hxX => hx.2 (Or.inl hxX)),
        fun hxs => hx.2 (Or.inr hxs)⟩
    have h := measureReal_mono (μ := (volume : Measure ℝ²)) hsub
      (measure_ne_top_of_subset sdiff_subset (hrfin t))
    rw [measureReal_sdiff (hufmono hst) (hX.union (measurable_rect s)) (hufin t),
      measureReal_sdiff (rect_mono hst) (measurable_rect s) (hrfin t)] at h
    simpa only [f, measureReal_def, volume_rect, ENNReal.toReal_ofReal hs,
      ENNReal.toReal_ofReal (hs.trans hst)] using h
  have hdist {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
      dist (f s) (f t) ≤ dist s t := by
    simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hfmono hst)),
      abs_of_nonpos (sub_nonpos.mpr hst)]
    linarith [hfinc hs hst]
  have hcont : ContinuousOn f (Icc 0 b.toReal) := by
    apply LipschitzOnWith.continuousOn (K := 1)
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simp only [NNReal.coe_one, one_mul]
    rcases le_total s t with hst | hts
    · exact hdist hs.1 hst
    · simpa only [dist_comm] using hdist ht.1 hts
  have hzero : f 0 ≤ b.toReal := by
    refine (measureReal_union_le (μ := (volume : Measure ℝ²)) X (rect 0)).trans ?_
    simpa only [measureReal_def, volume_rect, ENNReal.ofReal_zero, ENNReal.toReal_zero, add_zero]
      using ENNReal.toReal_mono hb hvol
  have hbval : b.toReal ≤ f b.toReal := by
    simpa only [f, measureReal_def, volume_rect, ENNReal.ofReal_toReal hb] using
      (measureReal_mono (μ := (volume : Measure ℝ²)) (subset_union_right : rect b.toReal ⊆
        X ∪ rect b.toReal) (hufin b.toReal))
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc ENNReal.toReal_nonneg hcont ⟨hzero, hbval⟩
  refine ⟨X ∪ rect t, subset_union_left, hX.union (measurable_rect t), ?_⟩
  calc
    volume (X ∪ rect t) = ENNReal.ofReal (f t) := (ENNReal.ofReal_toReal (hufin t)).symm
    _ = b := by rw [ht, ENNReal.ofReal_toReal hb]

/-- A measurable worm cover can be enlarged to any prescribed greater or equal volume. -/
theorem pad_worm_cover (X : Set ℝ²) (hX : X ∈ MoserWorm.WormCovers)
    {b : ℝ≥0∞} (hvol : volume X ≤ b) :
    ∃ Y ∈ MoserWorm.WormCovers, volume Y = b := by
  obtain ⟨hm, hcover⟩ := hX
  obtain ⟨Y, hXY, hmY, hvolY⟩ := exists_measurable_superset_volume_eq hm hvol
  refine ⟨Y, ⟨hmY, ?_⟩, hvolY⟩
  intro w hw
  obtain ⟨e, v, hd, hsub⟩ := hcover w hw
  exact ⟨e, v, hd, hsub.trans (image_mono hXY)⟩

/-- A finite sample of a worm fits in the rational enlargement of Deng’s triangle. -/
def H1 : Prop :=
  ∀ (s : Finset (Set.Icc (0 : ℝ) 1)) (g : ↥s → ℝ²), LipschitzWith 1 g →
    ∃ (e : ℝ² ≃ₗᵢ[ℝ] ℝ²) (v : ℝ²), e.toLinearEquiv.det = 1 ∧
      ∀ t, let x := e (g t) + v
        0 ≤ x 1 ∧ |x 0| / (129 / 500 : ℝ) + x 1 / (501 / 500 : ℝ) ≤ 1

private theorem ofScientific_eq_ofReal (m e : ℕ) :
    (OfScientific.ofScientific m true e : ENNReal) =
      ENNReal.ofReal (OfScientific.ofScientific m true e : ℝ) := by
  change ((OfScientific.ofScientific m true e : NNReal) : ENNReal) = _
  rw [ENNReal.coe_nnreal_eq, NNReal.coe_ofScientific]

/-- The triangle area is its half-base times its height. -/
def H2 : Prop :=
  volume {x : ℝ² | 0 ≤ x 1 ∧ |x 0| / (129 / 500 : ℝ) + x 1 / (501 / 500 : ℝ) ≤ 1} =
    ENNReal.ofReal (64629 / 250000 : ℝ)

theorem main : H1 → H2 → type_of% @MoserWorm.mosers_worm_problem_upper_bound := by
  intro hFinite hArea
  let T : Set ℝ² := {x | 0 ≤ x 1 ∧ |x 0| / (129 / 500 : ℝ) + x 1 / (501 / 500 : ℝ) ≤ 1}
  have hCover : T ∈ MoserWorm.WormCovers := covered_of_finite triangle_compact hFinite
  have hLe : volume T ≤ (0.260437 : ℝ≥0∞) := by
    change volume T = ENNReal.ofReal (64629 / 250000 : ℝ) at hArea
    rw [hArea, ofScientific_eq_ofReal]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  exact pad_worm_cover T hCover hLe

end OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1
