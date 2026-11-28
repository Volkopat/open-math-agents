import OMAReductions.R_Erdos114_erdos_114_R1
import Mathlib

/-!
Complete kernel-verified proof of Eremenko-Hayman H1 for Erdos Problem 114
(OMA.R_Erdos114_erdos_114_R1.H1): Lemma 4 (prover-b) + Zero-Beltrami Lemma 5 (prover-a).
-/

section Lemma4Part
/-
Continuity of Hausdorff lemniscate length for fixed-degree monic complex polynomials
(Eremenko-Hayman, Michigan Math. J. 46 (1999), Lemma 4 continuity) and the circle-integral
representation via pointwise inverse-branch convergence.

Private Erdős 114 Prize Squad component (100% original from-scratch Lean 4 formalization).
-/

namespace OMA.Erdos114Lemma4

open Polynomial MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

-- ============================================================================
-- Section 1: 1D Hausdorff measure of injective C^1 curves in ℂ
-- ============================================================================

lemma hausdorffMeasure_one_finite_eq_zero {s : Set ℂ} (hs : s.Finite) :
    (μH[1] : Measure ℂ) s = 0 := by
  have : NullSingletonClass (μH[1] : Measure ℂ) := Measure.nullSingletonClass_hausdorff ℂ one_pos
  exact hs.measure_zero _

lemma hausdorffMeasure_one_image_le_of_norm_le {f : ℝ → ℂ} {s : Set ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hf : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ c * ‖x - y‖) :
    (μH[1] : Measure ℂ) (f '' s) ≤ ENNReal.ofReal c * volume s := by
  have hlip : LipschitzOnWith (Real.toNNReal c) f s := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    simpa [dist_eq_norm, Real.coe_toNNReal c hc] using hf x hx y hy
  have h := hlip.hausdorffMeasure_image_le zero_le_one
  rw [ENNReal.rpow_one, hausdorffMeasure_real] at h
  exact h

lemma le_hausdorffMeasure_one_image_of_norm_ge {f : ℝ → ℂ} {s : Set ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hf : ∀ x ∈ s, ∀ y ∈ s, c * ‖x - y‖ ≤ ‖f x - f y‖) :
    ENNReal.ofReal c * volume s ≤ (μH[1] : Measure ℂ) (f '' s) := by
  rcases eq_or_lt_of_le hc with rfl | hc_pos
  · simp
  · rcases s.eq_empty_or_nonempty with rfl | hs_ne
    · simp
    · let g : ℂ → ℝ := Function.invFunOn f s
      have hleft : ∀ x ∈ s, g (f x) = x := by
        intro x hx
        have hx' : f x ∈ f '' s := ⟨x, hx, rfl⟩
        have hmem : g (f x) ∈ s := Function.invFunOn_mem hx'
        have hfeq : f (g (f x)) = f x := Function.invFunOn_eq hx'
        have hle := hf (g (f x)) hmem x hx
        rw [hfeq, sub_self, norm_zero] at hle
        have h0 : ‖g (f x) - x‖ = 0 :=
          le_antisymm (by nlinarith [norm_nonneg (g (f x) - x)]) (norm_nonneg _)
        exact sub_eq_zero.mp (norm_eq_zero.mp h0)
      have hlip : LipschitzOnWith (Real.toNNReal c⁻¹) g (f '' s) := by
        refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
        rcases hu with ⟨x, hx, rfl⟩
        rcases hv with ⟨y, hy, rfl⟩
        rw [hleft x hx, hleft y hy, dist_eq_norm, dist_eq_norm,
          Real.coe_toNNReal c⁻¹ (inv_nonneg.mpr hc)]
        have h1 := hf x hx y hy
        rw [inv_mul_eq_div, le_div_iff₀ hc_pos, mul_comm]
        exact h1
      have h1 := hlip.hausdorffMeasure_image_le zero_le_one
      rw [ENNReal.rpow_one, hausdorffMeasure_real] at h1
      have himg : g '' (f '' s) = s := by
        ext x
        constructor
        · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
          rwa [hleft y hy]
        · intro hx
          exact ⟨f x, ⟨x, hx, rfl⟩, hleft x hx⟩
      rw [himg] at h1
      have hcoe : ((Real.toNNReal c⁻¹ : ℝ≥0) : ℝ≥0∞) = (ENNReal.ofReal c)⁻¹ :=
        ENNReal.ofReal_inv_of_pos hc_pos
      rw [hcoe] at h1
      have hne0 : ENNReal.ofReal c ≠ 0 := by
        simp [ENNReal.ofReal_eq_zero, not_le.mpr hc_pos]
      have hnetop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
      calc ENNReal.ofReal c * volume s
          ≤ ENNReal.ofReal c * ((ENNReal.ofReal c)⁻¹ * (μH[1] : Measure ℂ) (f '' s)) := by gcongr
        _ = (ENNReal.ofReal c * (ENNReal.ofReal c)⁻¹) * (μH[1] : Measure ℂ) (f '' s) := by
            rw [mul_assoc]
        _ = (μH[1] : Measure ℂ) (f '' s) := by
            rw [ENNReal.mul_inv_cancel hne0 hnetop, one_mul]

/-- Uniform grid partition of `[a, b]` into `M` subintervals `[t_j, t_{j+1}]`. -/
private def gridPt (a b : ℝ) (M : ℕ) (j : ℕ) : ℝ :=
  a + (j : ℝ) * ((b - a) / (M : ℝ))

private lemma gridPt_zero (a b : ℝ) (M : ℕ) : gridPt a b M 0 = a := by
  simp [gridPt]

private lemma gridPt_end (a b : ℝ) {M : ℕ} (hM : 0 < M) : gridPt a b M M = b := by
  unfold gridPt
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

private lemma gridPt_sub_succ (a b : ℝ) (M j : ℕ) :
    gridPt a b M (j + 1) - gridPt a b M j = (b - a) / (M : ℝ) := by
  unfold gridPt; push_cast; ring

private lemma gridPt_mono {a b : ℝ} (hab : a ≤ b) (M : ℕ) {i j : ℕ} (hij : i ≤ j) :
    gridPt a b M i ≤ gridPt a b M j := by
  unfold gridPt
  have hstep : 0 ≤ (b - a) / (M : ℝ) := div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg M)
  have hijR : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
  nlinarith

private lemma gridPt_Icc_subset {a b : ℝ} (hab : a ≤ b) {M : ℕ} (hM : 0 < M)
    {j : ℕ} (hj : j < M) :
    Icc (gridPt a b M j) (gridPt a b M (j + 1)) ⊆ Icc a b := by
  intro x hx
  have hlo : a ≤ gridPt a b M j :=
    (gridPt_zero a b M).symm.trans_le (gridPt_mono hab M (Nat.zero_le j))
  have hhi : gridPt a b M (j + 1) ≤ b :=
    (gridPt_mono hab M (by omega : j + 1 ≤ M)).trans_eq (gridPt_end a b hM)
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

private lemma gridPt_Ioo_subset {a b : ℝ} (hab : a ≤ b) {M : ℕ} (hM : 0 < M)
    {j : ℕ} (hj : j < M) :
    Ioo (gridPt a b M j) (gridPt a b M (j + 1)) ⊆ Ioo a b := by
  intro x hx
  have hlo : a ≤ gridPt a b M j :=
    (gridPt_zero a b M).symm.trans_le (gridPt_mono hab M (Nat.zero_le j))
  have hhi : gridPt a b M (j + 1) ≤ b :=
    (gridPt_mono hab M (by omega : j + 1 ≤ M)).trans_eq (gridPt_end a b hM)
  exact ⟨lt_of_le_of_lt hlo hx.1, lt_of_lt_of_le hx.2 hhi⟩

private lemma Icc_eq_biUnion_grid {a b : ℝ} (hab : a ≤ b) {M : ℕ} (hM : 0 < M) :
    Icc a b = ⋃ j ∈ Finset.range M, Icc (gridPt a b M j) (gridPt a b M (j + 1)) := by
  ext x
  simp only [mem_Icc, mem_iUnion, Finset.mem_range]
  constructor
  · rintro ⟨hax, hxb⟩
    rcases eq_or_lt_of_le hab with rfl | hlt
    · refine ⟨0, hM, ?_, ?_⟩ <;> simp [gridPt, le_antisymm hxb hax]
    · have hstep_pos : 0 < (b - a) / (M : ℝ) :=
        div_pos (sub_pos.mpr hlt) (Nat.cast_pos.mpr hM)
      let k := min (M - 1) (Nat.floor ((x - a) / ((b - a) / (M : ℝ))))
      refine ⟨k, by omega, ?_, ?_⟩
      · unfold gridPt
        have hk : (k : ℝ) ≤ (x - a) / ((b - a) / (M : ℝ)) := by
          have h1 : (k : ℝ) ≤ (Nat.floor ((x - a) / ((b - a) / (M : ℝ))) : ℝ) :=
            Nat.cast_le.mpr (min_le_right _ _)
          exact h1.trans (Nat.floor_le (div_nonneg (sub_nonneg.mpr hax) (le_of_lt hstep_pos)))
        have hmul := (le_div_iff₀ hstep_pos).mp hk
        linarith
      · by_cases htop : M - 1 ≤ Nat.floor ((x - a) / ((b - a) / (M : ℝ)))
        · have hk : k = M - 1 := min_eq_left htop
          rw [hk, show M - 1 + 1 = M by omega, gridPt_end a b hM]
          exact hxb
        · have hk : k = Nat.floor ((x - a) / ((b - a) / (M : ℝ))) := min_eq_right (by omega)
          rw [hk]
          unfold gridPt
          have hltf : (x - a) / ((b - a) / (M : ℝ)) <
              (Nat.floor ((x - a) / ((b - a) / (M : ℝ))) : ℝ) + 1 :=
            Nat.lt_floor_add_one _
          have hmul := (div_lt_iff₀ hstep_pos).mp hltf
          push_cast
          linarith
  · rintro ⟨j, hj, h1, h2⟩
    exact gridPt_Icc_subset hab hM hj ⟨h1, h2⟩

private lemma hausdorffMeasure_one_image_grid_sum {a b : ℝ} (hab : a ≤ b) {M : ℕ} (hM : 0 < M)
    {γ : ℝ → ℂ} (hcont : ContinuousOn γ (Icc a b)) (hinj : InjOn γ (Icc a b)) :
    (μH[1] : Measure ℂ) (γ '' Icc a b) =
      ∑ j ∈ Finset.range M, (μH[1] : Measure ℂ) (γ '' Icc (gridPt a b M j) (gridPt a b M (j + 1))) := by
  let E : Set ℂ := γ '' (Finset.image (gridPt a b M) (Finset.range (M + 1)) : Set ℝ)
  have hE_zero : (μH[1] : Measure ℂ) E = 0 :=
    hausdorffMeasure_one_finite_eq_zero ((Finset.finite_toSet _).image γ)
  have hpiece_eq : ∀ j ∈ Finset.range M,
      (μH[1] : Measure ℂ) (γ '' Icc (gridPt a b M j) (gridPt a b M (j + 1))) =
        (μH[1] : Measure ℂ) (γ '' Ioo (gridPt a b M j) (gridPt a b M (j + 1))) := by
    intro j _
    have hdiff : γ '' Icc (gridPt a b M j) (gridPt a b M (j + 1)) ⊆
        γ '' Ioo (gridPt a b M j) (gridPt a b M (j + 1)) ∪
          {γ (gridPt a b M j), γ (gridPt a b M (j + 1))} := by
      rintro _ ⟨x, hx, rfl⟩
      rcases eq_or_lt_of_le hx.1 with rfl | h1
      · exact Or.inr (Or.inl rfl)
      · rcases eq_or_lt_of_le hx.2 with rfl | h2
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl ⟨x, ⟨h1, h2⟩, rfl⟩
    have hpair_zero : (μH[1] : Measure ℂ) {γ (gridPt a b M j), γ (gridPt a b M (j + 1))} = 0 :=
      hausdorffMeasure_one_finite_eq_zero ((Set.finite_singleton _).insert _)
    refine le_antisymm ?_ (measure_mono (image_mono Ioo_subset_Icc_self))
    calc (μH[1] : Measure ℂ) (γ '' Icc (gridPt a b M j) (gridPt a b M (j + 1)))
        ≤ (μH[1] : Measure ℂ) (γ '' Ioo (gridPt a b M j) (gridPt a b M (j + 1)) ∪
            {γ (gridPt a b M j), γ (gridPt a b M (j + 1))}) := measure_mono hdiff
      _ ≤ (μH[1] : Measure ℂ) (γ '' Ioo (gridPt a b M j) (gridPt a b M (j + 1))) +
            (μH[1] : Measure ℂ) {γ (gridPt a b M j), γ (gridPt a b M (j + 1))} :=
          measure_union_le _ _
      _ = (μH[1] : Measure ℂ) (γ '' Ioo (gridPt a b M j) (gridPt a b M (j + 1))) := by
          rw [hpair_zero, add_zero]
  have hmeas : ∀ j ∈ Finset.range M,
      MeasurableSet (γ '' Ioo (gridPt a b M j) (gridPt a b M (j + 1))) := by
    intro j hj
    have hj' : j < M := Finset.mem_range.mp hj
    have hle : gridPt a b M j ≤ gridPt a b M (j + 1) := gridPt_mono hab M (Nat.le_succ j)
    have hkc : IsCompact (γ '' Icc (gridPt a b M j) (gridPt a b M (j + 1))) :=
      isCompact_Icc.image_of_continuousOn (hcont.mono (gridPt_Icc_subset hab hM hj'))
    have hset : γ '' Ioo (gridPt a b M j) (gridPt a b M (j + 1)) =
        (γ '' Icc (gridPt a b M j) (gridPt a b M (j + 1))) \
          {γ (gridPt a b M j), γ (gridPt a b M (j + 1))} := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨⟨x, Ioo_subset_Icc_self hx, rfl⟩, ?_⟩
        rintro (h1 | h2)
        · have := hinj (gridPt_Icc_subset hab hM hj' (Ioo_subset_Icc_self hx))
            (gridPt_Icc_subset hab hM hj' (left_mem_Icc.mpr hle)) h1
          linarith [hx.1]
        · have := hinj (gridPt_Icc_subset hab hM hj' (Ioo_subset_Icc_self hx))
            (gridPt_Icc_subset hab hM hj' (right_mem_Icc.mpr hle)) h2
          linarith [hx.2]
      · rintro ⟨⟨x, hx, rfl⟩, hne⟩
        refine ⟨x, ⟨?_, ?_⟩, rfl⟩
        · exact lt_of_le_of_ne hx.1 fun h => hne (Or.inl (by rw [h]))
        · exact lt_of_le_of_ne hx.2 fun h => hne (Or.inr (by rw [h]; rfl))
    rw [hset]
    exact hkc.measurableSet.diff ((Set.finite_singleton _).insert _).measurableSet
  have hdisj : PairwiseDisjoint (Finset.range M : Set ℕ)
      (fun j => γ '' Ioo (gridPt a b M j) (gridPt a b M (j + 1))) := by
    intro i hi j hj hij
    dsimp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hi' : i < M := Finset.mem_range.mp hi
    have hj' : j < M := Finset.mem_range.mp hj
    have hxe : x = y := hinj (gridPt_Icc_subset hab hM hi' (Ioo_subset_Icc_self hx))
      (gridPt_Icc_subset hab hM hj' (Ioo_subset_Icc_self hy)) hxy.symm
    subst hxe
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have := gridPt_mono hab M (show i + 1 ≤ j by omega)
      linarith [hx.2, hy.1]
    · have := gridPt_mono hab M (show j + 1 ≤ i by omega)
      linarith [hy.2, hx.1]
  have hunion : γ '' Icc a b ⊆
      (⋃ j ∈ Finset.range M, γ '' Ioo (gridPt a b M j) (gridPt a b M (j + 1))) ∪ E := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Icc_eq_biUnion_grid hab hM] at hx
    rcases mem_iUnion₂.mp hx with ⟨j, hj, hxj⟩
    rw [Finset.mem_range] at hj
    rcases eq_or_lt_of_le hxj.1 with rfl | h1
    · exact Or.inr ⟨gridPt a b M j, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩), rfl⟩
    · rcases eq_or_lt_of_le hxj.2 with rfl | h2
      · exact Or.inr ⟨gridPt a b M (j + 1), Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j + 1, Finset.mem_range.mpr (by omega), rfl⟩), rfl⟩
      · exact Or.inl (mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj, ⟨x, ⟨h1, h2⟩, rfl⟩⟩)
  have hrev : (⋃ j ∈ Finset.range M, γ '' Ioo (gridPt a b M j) (gridPt a b M (j + 1))) ⊆ γ '' Icc a b :=
    iUnion₂_subset fun j hj => image_mono (Ioo_subset_Icc_self.trans (gridPt_Icc_subset hab hM (Finset.mem_range.mp hj)))
  have heq_open : (μH[1] : Measure ℂ) (γ '' Icc a b) =
      (μH[1] : Measure ℂ) (⋃ j ∈ Finset.range M, γ '' Ioo (gridPt a b M j) (gridPt a b M (j + 1))) := by
    refine le_antisymm ?_ (measure_mono hrev)
    calc (μH[1] : Measure ℂ) (γ '' Icc a b)
        ≤ (μH[1] : Measure ℂ) ((⋃ j ∈ Finset.range M, γ '' Ioo (gridPt a b M j) (gridPt a b M (j + 1))) ∪ E) :=
          measure_mono hunion
      _ ≤ (μH[1] : Measure ℂ) (⋃ j ∈ Finset.range M, γ '' Ioo (gridPt a b M j) (gridPt a b M (j + 1))) +
            (μH[1] : Measure ℂ) E := measure_union_le _ _
      _ = _ := by rw [hE_zero, add_zero]
  rw [heq_open, measure_biUnion_finset hdisj hmeas]
  exact Finset.sum_congr rfl fun j hj => (hpiece_eq j hj).symm

/-- Exact 1D Hausdorff measure of an injective C^1 curve `γ : [a, b] → ℂ`. -/
theorem hausdorffMeasure_one_image_Icc_eq_integral {a b : ℝ} (hab : a ≤ b)
    {γ γ' : ℝ → ℂ} (hinj : InjOn γ (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivAt γ (γ' t) t)
    (hcont' : ContinuousOn γ' (Icc a b)) :
    (μH[1] : Measure ℂ) (γ '' Icc a b) = ENNReal.ofReal (∫ t in a..b, ‖γ' t‖) := by
  have hcont : ContinuousOn γ (Icc a b) := fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hint_nn : 0 ≤ ∫ t in a..b, ‖γ' t‖ :=
    intervalIntegral.integral_nonneg hab fun t _ => norm_nonneg _
  rcases eq_or_lt_of_le hab with rfl | hlt
  · rw [Icc_self, image_singleton, hausdorffMeasure_one_finite_eq_zero (Set.finite_singleton _),
      intervalIntegral.integral_same, ENNReal.ofReal_zero]
  have happrox : ∀ ε > 0,
      ENNReal.ofReal ((∫ t in a..b, ‖γ' t‖) - 2 * ε * (b - a)) ≤ (μH[1] : Measure ℂ) (γ '' Icc a b) ∧
      (μH[1] : Measure ℂ) (γ '' Icc a b) ≤ ENNReal.ofReal ((∫ t in a..b, ‖γ' t‖) + 2 * ε * (b - a)) := by
    intro ε hε
    have huc : UniformContinuousOn γ' (Icc a b) := isCompact_Icc.uniformContinuousOn_of_continuous hcont'
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ_pos, hδ⟩ := huc ε hε
    obtain ⟨M, hM_gt⟩ := exists_nat_gt ((b - a) / δ)
    have hM_pos : 0 < M := by
      have : (0 : ℝ) < (b - a) / δ := div_pos (sub_pos.mpr hlt) hδ_pos
      exact Nat.cast_pos.mp (this.trans hM_gt)
    have hstep_pos : 0 < (b - a) / (M : ℝ) := div_pos (sub_pos.mpr hlt) (Nat.cast_pos.mpr hM_pos)
    have hstep_lt : (b - a) / (M : ℝ) < δ := by
      rw [div_lt_iff₀ (Nat.cast_pos.mpr hM_pos)]
      have := (div_lt_iff₀ hδ_pos).mp hM_gt
      linarith
    have hcell : ∀ j ∈ Finset.range M,
        ENNReal.ofReal (max 0 (‖γ' (gridPt a b M j)‖ - ε) * ((b - a) / (M : ℝ))) ≤
          (μH[1] : Measure ℂ) (γ '' Icc (gridPt a b M j) (gridPt a b M (j + 1))) ∧
        (μH[1] : Measure ℂ) (γ '' Icc (gridPt a b M j) (gridPt a b M (j + 1))) ≤
          ENNReal.ofReal ((‖γ' (gridPt a b M j)‖ + ε) * ((b - a) / (M : ℝ))) := by
      intro j hj
      have hj' : j < M := Finset.mem_range.mp hj
      have hsub := gridPt_Icc_subset hab hM_pos hj'
      set t₀ := gridPt a b M j
      set t₁ := gridPt a b M (j + 1)
      have hlen : t₁ - t₀ = (b - a) / (M : ℝ) := gridPt_sub_succ a b M j
      have ht0_mem : t₀ ∈ Icc a b := hsub (left_mem_Icc.mpr (by linarith))
      have hmvt : ∀ x ∈ Icc t₀ t₁, ∀ y ∈ Icc t₀ t₁,
          ‖(γ x - γ y) - ((x - y : ℝ) : ℂ) * γ' t₀‖ ≤ ε * ‖x - y‖ := by
        intro x hx y hy
        let g : ℝ → ℂ := fun t => γ t - (t : ℂ) * γ' t₀
        have hg_deriv : ∀ t ∈ Icc t₀ t₁, HasDerivAt g (γ' t - γ' t₀) t := by
          intro t ht
          have h1 := hderiv t (hsub ht)
          have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * γ' t₀) (γ' t₀) t := by
            have hof : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
            simpa using hof.mul_const (γ' t₀)
          exact h1.sub h2
        have hg_bound : ∀ t ∈ Icc t₀ t₁, ‖deriv g t‖ ≤ ε := by
          intro t ht
          rw [(hg_deriv t ht).deriv]
          have hdist : dist t t₀ < δ := by
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
            linarith [ht.2, hlen]
          exact le_of_lt (by simpa [dist_eq_norm] using hδ t (hsub ht) t₀ ht0_mem hdist)
        have hconv := (convex_Icc t₀ t₁).norm_image_sub_le_of_norm_deriv_le
          (fun t ht => (hg_deriv t ht).differentiableAt) hg_bound hy hx
        have hgeq : g x - g y = (γ x - γ y) - ((x - y : ℝ) : ℂ) * γ' t₀ := by
          simp only [g, Complex.ofReal_sub]; ring
        rwa [hgeq] at hconv
      have hvol : volume (Icc t₀ t₁) = ENNReal.ofReal ((b - a) / (M : ℝ)) := by
        rw [Real.volume_Icc, hlen]
      constructor
      · have hlb := le_hausdorffMeasure_one_image_of_norm_ge (f := γ) (s := Icc t₀ t₁)
          (c := max 0 (‖γ' t₀‖ - ε)) (le_max_left _ _) (fun x hx y hy => ?_)
        · rw [hvol, ← ENNReal.ofReal_mul (le_max_left _ _)] at hlb
          exact hlb
        · rcases le_or_gt (‖γ' t₀‖ - ε) 0 with hneg | hpos
          · rw [max_eq_left hneg, zero_mul]; exact norm_nonneg _
          · rw [max_eq_right (le_of_lt hpos)]
            have hm := hmvt x hx y hy
            have htri : ‖((x - y : ℝ) : ℂ) * γ' t₀‖ - ‖γ x - γ y‖ ≤
                ‖(γ x - γ y) - ((x - y : ℝ) : ℂ) * γ' t₀‖ := by
              have h := norm_sub_norm_le (((x - y : ℝ) : ℂ) * γ' t₀) (γ x - γ y)
              rwa [norm_sub_rev (((x - y : ℝ) : ℂ) * γ' t₀) (γ x - γ y)] at h
            have hnorm_eq : ‖((x - y : ℝ) : ℂ) * γ' t₀‖ = ‖x - y‖ * ‖γ' t₀‖ := by
              rw [norm_mul, Complex.norm_real]
            nlinarith
      · have hub := hausdorffMeasure_one_image_le_of_norm_le (f := γ) (s := Icc t₀ t₁)
          (c := ‖γ' t₀‖ + ε) (by positivity) (fun x hx y hy => ?_)
        · rw [hvol, ← ENNReal.ofReal_mul (by positivity)] at hub
          exact hub
        · have hm := hmvt x hx y hy
          have htri : ‖γ x - γ y‖ ≤ ‖(γ x - γ y) - ((x - y : ℝ) : ℂ) * γ' t₀‖ +
              ‖((x - y : ℝ) : ℂ) * γ' t₀‖ := by
            simpa using norm_add_le ((γ x - γ y) - ((x - y : ℝ) : ℂ) * γ' t₀)
              (((x - y : ℝ) : ℂ) * γ' t₀)
          have hnorm_eq : ‖((x - y : ℝ) : ℂ) * γ' t₀‖ = ‖x - y‖ * ‖γ' t₀‖ := by
            rw [norm_mul, Complex.norm_real]
          nlinarith
    have hint_grid : ∫ t in a..b, ‖γ' t‖ =
        ∑ j ∈ Finset.range M, ∫ t in (gridPt a b M j)..(gridPt a b M (j + 1)), ‖γ' t‖ := by
      have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := fun t => ‖γ' t‖)
        (a := gridPt a b M) (n := M) fun j hj => by
          have hsub_u : uIcc (gridPt a b M j) (gridPt a b M (j + 1)) ⊆ Icc a b := by
            rw [uIcc_of_le (gridPt_mono hab M (Nat.le_succ j))]
            exact gridPt_Icc_subset hab hM_pos hj
          exact (hcont'.norm.mono hsub_u).intervalIntegrable
      rw [gridPt_zero, gridPt_end a b hM_pos] at h
      exact h.symm
    have hriem : ∀ j ∈ Finset.range M,
        (‖γ' (gridPt a b M j)‖ - ε) * ((b - a) / (M : ℝ)) ≤
          ∫ t in (gridPt a b M j)..(gridPt a b M (j + 1)), ‖γ' t‖ ∧
        ∫ t in (gridPt a b M j)..(gridPt a b M (j + 1)), ‖γ' t‖ ≤
          (‖γ' (gridPt a b M j)‖ + ε) * ((b - a) / (M : ℝ)) := by
      intro j hj
      have hj' : j < M := Finset.mem_range.mp hj
      have hsub := gridPt_Icc_subset hab hM_pos hj'
      set t₀ := gridPt a b M j
      set t₁ := gridPt a b M (j + 1)
      have hle : t₀ ≤ t₁ := gridPt_mono hab M (Nat.le_succ j)
      have hlen : t₁ - t₀ = (b - a) / (M : ℝ) := gridPt_sub_succ a b M j
      have ht0_mem : t₀ ∈ Icc a b := hsub (left_mem_Icc.mpr hle)
      have hi1 : IntervalIntegrable (fun t => ‖γ' t‖) volume t₀ t₁ := by
        have hsub_u : uIcc t₀ t₁ ⊆ Icc a b := by rw [uIcc_of_le hle]; exact hsub
        exact (hcont'.norm.mono hsub_u).intervalIntegrable
      have hdiff_le : ∀ t ∈ Icc t₀ t₁, ‖γ' t₀‖ - ε ≤ ‖γ' t‖ ∧ ‖γ' t‖ ≤ ‖γ' t₀‖ + ε := by
        intro t ht
        have hdist : dist t t₀ < δ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
          linarith [ht.2, hlen]
        have h1 : ‖γ' t - γ' t₀‖ < ε := by
          simpa [dist_eq_norm] using hδ t (hsub ht) t₀ ht0_mem hdist
        have h2 : |‖γ' t‖ - ‖γ' t₀‖| ≤ ‖γ' t - γ' t₀‖ := abs_norm_sub_norm_le _ _
        rw [abs_le] at h2
        constructor <;> linarith
      constructor
      · have h := intervalIntegral.integral_mono_on hle intervalIntegrable_const hi1
          fun t ht => (hdiff_le t ht).1
        rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at h
        linarith
      · have h := intervalIntegral.integral_mono_on hle hi1 intervalIntegrable_const
          fun t ht => (hdiff_le t ht).2
        rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at h
        linarith
    rw [hausdorffMeasure_one_image_grid_sum hab hM_pos hcont hinj]
    have hsum_step : ∑ _j ∈ Finset.range M, ((b - a) / (M : ℝ)) = b - a := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
    constructor
    · calc ENNReal.ofReal ((∫ t in a..b, ‖γ' t‖) - 2 * ε * (b - a))
          ≤ ENNReal.ofReal (∑ j ∈ Finset.range M,
              max 0 (‖γ' (gridPt a b M j)‖ - ε) * ((b - a) / (M : ℝ))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hint_grid]
            have h1 : ∑ j ∈ Finset.range M,
                (∫ t in (gridPt a b M j)..(gridPt a b M (j + 1)), ‖γ' t‖) -
                2 * ε * (b - a) =
                ∑ j ∈ Finset.range M,
                  ((∫ t in (gridPt a b M j)..(gridPt a b M (j + 1)), ‖γ' t‖) -
                    2 * ε * ((b - a) / (M : ℝ))) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum_step]
            rw [h1]
            refine Finset.sum_le_sum fun j hj => ?_
            have hr := (hriem j hj).2
            have hm : ‖γ' (gridPt a b M j)‖ - ε ≤ max 0 (‖γ' (gridPt a b M j)‖ - ε) :=
              le_max_right _ _
            nlinarith
        _ = ∑ j ∈ Finset.range M,
              ENNReal.ofReal (max 0 (‖γ' (gridPt a b M j)‖ - ε) * ((b - a) / (M : ℝ))) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            intro j _; exact mul_nonneg (le_max_left _ _) (le_of_lt hstep_pos)
        _ ≤ ∑ j ∈ Finset.range M,
              (μH[1] : Measure ℂ) (γ '' Icc (gridPt a b M j) (gridPt a b M (j + 1))) :=
            Finset.sum_le_sum fun j hj => (hcell j hj).1
    · calc ∑ j ∈ Finset.range M,
              (μH[1] : Measure ℂ) (γ '' Icc (gridPt a b M j) (gridPt a b M (j + 1)))
          ≤ ∑ j ∈ Finset.range M,
              ENNReal.ofReal ((‖γ' (gridPt a b M j)‖ + ε) * ((b - a) / (M : ℝ))) :=
            Finset.sum_le_sum fun j hj => (hcell j hj).2
        _ = ENNReal.ofReal (∑ j ∈ Finset.range M,
              (‖γ' (gridPt a b M j)‖ + ε) * ((b - a) / (M : ℝ))) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            intro j _; positivity
        _ ≤ ENNReal.ofReal ((∫ t in a..b, ‖γ' t‖) + 2 * ε * (b - a)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hint_grid]
            have h1 : ∑ j ∈ Finset.range M,
                (∫ t in (gridPt a b M j)..(gridPt a b M (j + 1)), ‖γ' t‖) +
                2 * ε * (b - a) =
                ∑ j ∈ Finset.range M,
                  ((∫ t in (gridPt a b M j)..(gridPt a b M (j + 1)), ‖γ' t‖) +
                    2 * ε * ((b - a) / (M : ℝ))) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum_step]
            rw [h1]
            refine Finset.sum_le_sum fun j hj => ?_
            have hr := (hriem j hj).1
            nlinarith
  have hfin : (μH[1] : Measure ℂ) (γ '' Icc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (happrox 1 one_pos).2
  apply (ENNReal.toReal_eq_toReal_iff' hfin ENNReal.ofReal_ne_top).mp
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun η hη => ?_
    have hε : 0 < η / (2 * (b - a)) := div_pos hη (by linarith)
    have hub := (happrox _ hε).2
    have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hub
    rw [ENNReal.toReal_ofReal (by positivity)] at htr
    rw [ENNReal.toReal_ofReal hint_nn]
    have hcalc : 2 * (η / (2 * (b - a))) * (b - a) = η := by
      have : b - a ≠ 0 := by linarith
      field_simp
    linarith
  · refine le_of_forall_pos_le_add fun η hη => ?_
    have hε : 0 < η / (2 * (b - a)) := div_pos hη (by linarith)
    have hlb := (happrox _ hε).1
    have htr := ENNReal.toReal_mono hfin hlb
    rw [ENNReal.toReal_ofReal hint_nn]
    have hcalc : 2 * (η / (2 * (b - a))) * (b - a) = η := by
      have : b - a ≠ 0 := by linarith
      field_simp
    rw [hcalc] at htr
    have hle_of : (∫ t in a..b, ‖γ' t‖) - η ≤ (ENNReal.ofReal ((∫ t in a..b, ‖γ' t‖) - η)).toReal := by
      by_cases hneg : 0 ≤ (∫ t in a..b, ‖γ' t‖) - η
      · rw [ENNReal.toReal_ofReal hneg]
      · rw [ENNReal.ofReal_of_nonpos (le_of_not_ge hneg), ENNReal.toReal_zero]
        linarith
    linarith

-- ============================================================================
-- Section 2: Lemma 1 (line intersections <= 2n), Lemma 2 (1D projection),
--            and Weak Cartan Lemma 3 (root-ball covering)
-- ============================================================================

/-- Every horizontal line `Im z = y₀` meets `Erdos114.lemniscate q` in at most `2 * n` points. -/
theorem lemniscate_inter_im_subset_finset {n : ℕ} (hn : 1 ≤ n) {q : ℂ[X]}
    (hq : q.Monic) (hdeg : q.natDegree = n) (y₀ : ℝ) :
    ∃ F : Finset ℂ, F.card ≤ 2 * n ∧ {z ∈ Erdos114.lemniscate q | z.im = y₀} ⊆ (F : Set ℂ) := by
  let qbar : ℂ[X] := q.map (starRingEnd ℂ)
  have hqbar_monic : qbar.Monic := hq.map (starRingEnd ℂ)
  have hqbar_deg : qbar.natDegree = n := by
    rw [Polynomial.natDegree_map_eq_of_injective (starRingEnd ℂ).injective, hdeg]
  let p₁ : ℂ[X] := q.comp (X + C ((y₀ : ℂ) * Complex.I))
  let p₂ : ℂ[X] := qbar.comp (X - C ((y₀ : ℂ) * Complex.I))
  have hp1_monic : p₁.Monic :=
    hq.comp (Polynomial.monic_X_add_C _) (by rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero)
  have hp2_monic : p₂.Monic :=
    hqbar_monic.comp (Polynomial.monic_X_sub_C _) (by rw [Polynomial.natDegree_X_sub_C]; exact one_ne_zero)
  have hp1_deg : p₁.natDegree = n := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, hdeg, mul_one]
  have hp2_deg : p₂.natDegree = n := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, hqbar_deg, mul_one]
  let R : ℂ[X] := p₁ * p₂ - 1
  have hprod_deg : (p₁ * p₂).natDegree = 2 * n := by
    rw [hp1_monic.natDegree_mul hp2_monic, hp1_deg, hp2_deg]; omega
  have hR_deg : R.natDegree = 2 * n := by
    have : (1 : ℂ[X]).natDegree < (p₁ * p₂).natDegree := by simp [hprod_deg]; omega
    exact (Polynomial.natDegree_sub_eq_left_of_natDegree_lt this).trans hprod_deg
  have hR_ne : R ≠ 0 := by
    intro h0; rw [h0, Polynomial.natDegree_zero] at hR_deg; omega
  refine ⟨R.roots.toFinset.image (fun x => x + (y₀ : ℂ) * Complex.I), ?_, ?_⟩
  · calc (R.roots.toFinset.image (fun x => x + (y₀ : ℂ) * Complex.I)).card
        ≤ R.roots.toFinset.card := Finset.card_image_le
      _ ≤ R.roots.card := Multiset.toFinset_card_le _
      _ ≤ R.natDegree := Polynomial.card_roots' R
      _ = 2 * n := hR_deg
  · rintro z ⟨hz_lem, hz_im⟩
    have hz_eq : z = (z.re : ℂ) + (y₀ : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hz_im]
    have hconj : starRingEnd ℂ z = (z.re : ℂ) - (y₀ : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hz_im]
    have hhom : Polynomial.eval₂ (starRingEnd ℂ) (starRingEnd ℂ z) q = starRingEnd ℂ (q.eval z) :=
      (Polynomial.hom_eval₂ q (RingHom.id ℂ) (starRingEnd ℂ) z).symm
    have hR_eval : R.eval (z.re : ℂ) = 0 := by
      simp only [R, p₁, p₂, qbar, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one,
        Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      rw [← hz_eq, ← hconj, Polynomial.eval_map, hhom]
      have hnorm : ‖q.eval z‖ = 1 := hz_lem
      have hmul : q.eval z * starRingEnd ℂ (q.eval z) = ((‖q.eval z‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hmul, hnorm]
      simp
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(z.re : ℂ), ?_, hz_eq.symm⟩)
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hR_ne).mpr hR_eval)

/-- Every vertical line `Re z = x₀` meets `Erdos114.lemniscate q` in at most `2 * n` points. -/
theorem lemniscate_inter_re_subset_finset {n : ℕ} (hn : 1 ≤ n) {q : ℂ[X]}
    (hq : q.Monic) (hdeg : q.natDegree = n) (x₀ : ℝ) :
    ∃ F : Finset ℂ, F.card ≤ 2 * n ∧ {z ∈ Erdos114.lemniscate q | z.re = x₀} ⊆ (F : Set ℂ) := by
  let lin : ℂ[X] := C (-Complex.I) * X
  have hlin_deg : lin.natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul (by simp), Polynomial.natDegree_X]
  have hlin_lc : lin.leadingCoeff = -Complex.I := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X, mul_one]
  let rot : ℂ[X] := C (Complex.I ^ n) * q.comp lin
  have hIn_ne : Complex.I ^ n ≠ 0 := pow_ne_zero n Complex.I_ne_zero
  have hcomp_lc : (q.comp lin).leadingCoeff = (-Complex.I) ^ n := by
    rw [Polynomial.leadingCoeff_comp (by rw [hlin_deg]; exact Nat.one_ne_zero),
      hq.leadingCoeff, one_mul, hdeg, hlin_lc]
  have hrot_deg : rot.natDegree = n := by
    rw [Polynomial.natDegree_C_mul hIn_ne, Polynomial.natDegree_comp, hlin_deg, hdeg, mul_one]
  have hrot_monic : rot.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hcomp_lc, ← mul_pow]
    simp
  obtain ⟨F, hF_card, hF_sub⟩ := lemniscate_inter_im_subset_finset hn hrot_monic hrot_deg x₀
  refine ⟨F.image (fun w => -Complex.I * w), Finset.card_image_le.trans hF_card, ?_⟩
  rintro z ⟨hz_lem, hz_re⟩
  have hw_lem : Complex.I * z ∈ Erdos114.lemniscate rot := by
    change ‖rot.eval (Complex.I * z)‖ = 1
    simp only [rot, lin, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_X]
    have hcancel : -Complex.I * (Complex.I * z) = z := by
      calc -Complex.I * (Complex.I * z) = -(Complex.I * Complex.I) * z := by ring
        _ = z := by simp
    rw [hcancel, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
    exact hz_lem
  have hw_im : (Complex.I * z).im = x₀ := by simp [hz_re]
  have hw_mem : Complex.I * z ∈ F := hF_sub ⟨hw_lem, hw_im⟩
  refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨Complex.I * z, hw_mem, ?_⟩)
  calc -Complex.I * (Complex.I * z) = -(Complex.I * Complex.I) * z := by ring
    _ = z := by simp

private lemma norm_multiset_prod_eq (s : Multiset ℂ) : ‖s.prod‖ = (s.map norm).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

/-- Weak Cartan covering lemma (pigeonhole): if `|q(z) - w₀| ≤ δ` for a monic degree-`n`
polynomial `q`, then `z` lies within `δ^(1/n)` of some root of `q - C w₀`. -/
theorem monic_sub_eval_le_exists_root {n : ℕ} (hn : 1 ≤ n) {q : ℂ[X]}
    (hq : q.Monic) (hdeg : q.natDegree = n) (w₀ : ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    {z : ℂ} (hz : ‖q.eval z - w₀‖ ≤ δ) :
    ∃ r ∈ (q - C w₀).roots, ‖z - r‖ ≤ δ ^ ((n : ℝ)⁻¹) := by
  let p := q - C w₀
  have hp_deg : p.natDegree = n := by
    rw [Polynomial.natDegree_sub_C, hdeg]
  have hp_monic : p.Monic := hq.sub_of_left <| Polynomial.degree_C_le.trans_lt <| by
    rw [Polynomial.degree_eq_natDegree hq.ne_zero, hdeg]
    exact_mod_cast hn
  have hcard : p.roots.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hp_deg]
  have hfac := (IsAlgClosed.splits p).eq_prod_roots_of_monic hp_monic
  have heval : p.eval z = (p.roots.map (fun r => z - r)).prod := by
    conv_lhs => rw [hfac]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun r _ => by simp
  have hprod : (p.roots.map (fun r => ‖z - r‖)).prod ≤ δ := by
    have hnorm : ‖p.eval z‖ = (p.roots.map (fun r => ‖z - r‖)).prod := by
      rw [heval, norm_multiset_prod_eq, Multiset.map_map]
      rfl
    rw [← hnorm]
    simpa [p] using hz
  by_contra hall
  push Not at hall
  have hlt : (p.roots.map (fun _ => δ ^ ((n : ℝ)⁻¹))).prod < (p.roots.map (fun r => ‖z - r‖)).prod := by
    have hne : p.roots ≠ 0 := by
      intro h0; rw [h0, Multiset.card_zero] at hcard; omega
    have aux : ∀ (s : Multiset ℂ), s ≠ 0 → (∀ r ∈ s, δ ^ ((n : ℝ)⁻¹) < ‖z - r‖) →
        (s.map (fun _ => δ ^ ((n : ℝ)⁻¹))).prod < (s.map (fun r => ‖z - r‖)).prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => intro h; exact (h rfl).elim
      | cons a s ih =>
        intro _ hgt
        simp only [Multiset.map_cons, Multiset.prod_cons]
        have ha := hgt a (Multiset.mem_cons_self a s)
        have hnn : 0 ≤ δ ^ ((n : ℝ)⁻¹) := Real.rpow_nonneg hδ _
        by_cases hs : s = 0
        · subst hs; simpa using ha
        · have hs_lt := ih hs fun r hr => hgt r (Multiset.mem_cons_of_mem hr)
          have hs_nn : 0 ≤ (s.map (fun _ => δ ^ ((n : ℝ)⁻¹))).prod :=
            Multiset.prod_nonneg fun x hx => by
              rcases Multiset.mem_map.mp hx with ⟨_, _, rfl⟩; exact hnn
          exact mul_lt_mul_of_nonneg_of_pos' (le_of_lt ha) hs_lt hs_nn (lt_of_le_of_lt hnn ha)
    exact aux p.roots hne hall
  have hconst : (p.roots.map (fun _ => δ ^ ((n : ℝ)⁻¹))).prod = δ := by
    rw [Multiset.map_const', Multiset.prod_replicate, hcard, ← Real.rpow_natCast,
      ← Real.rpow_mul hδ, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega)), Real.rpow_one]
  linarith

/-- Elementary 1D projection / Banach-indicatrix upper bound for a finite family of `C^1` real
functions whose open-interval fibers have combined multiplicity at most `M`. -/
theorem sum_integral_abs_deriv_le {ι : Type*} [Fintype ι]
    {a b : ι → ℝ} (hab : ∀ k, a k ≤ b k)
    {f f' : ι → ℝ → ℝ}
    (hderiv : ∀ k, ∀ t ∈ Icc (a k) (b k), HasDerivAt (f k) (f' k t) t)
    (hcont' : ∀ k, ContinuousOn (f' k) (Icc (a k) (b k)))
    {U : Set ℝ} (hU_meas : MeasurableSet U) (hU_fin : volume U ≠ ⊤)
    {M : ℕ}
    (hU_sub : ∀ k, ∀ t ∈ Ioo (a k) (b k), f k t ∈ U)
    (hmult : ∀ x ∈ U, ∃ S : Finset (ι × ℝ), S.card ≤ M ∧
      ∀ k, ∀ t ∈ Ioo (a k) (b k), f k t = x → (k, t) ∈ S) :
    ∑ k : ι, ∫ t in (a k)..(b k), |f' k t| ≤ (M : ℝ) * (volume U).toReal := by
  have hlen_nn : 0 ≤ ∑ k : ι, (b k - a k) :=
    Finset.sum_nonneg fun k _ => sub_nonneg.mpr (hab k)
  suffices hε : ∀ ε > 0,
      ∑ k : ι, ∫ t in (a k)..(b k), |f' k t| ≤
        (M : ℝ) * (volume U).toReal + 2 * ε * ∑ k : ι, (b k - a k) by
    rcases eq_or_lt_of_le hlen_nn with hzero | hpos
    · have h0 := hε 1 one_pos
      rw [← hzero, mul_zero, add_zero] at h0
      exact h0
    · refine le_of_forall_pos_le_add fun η hη => ?_
      have h1 := hε (η / (2 * ∑ k : ι, (b k - a k))) (div_pos hη (by linarith))
      have hcalc : 2 * (η / (2 * ∑ k : ι, (b k - a k))) * ∑ k : ι, (b k - a k) = η := by
        have : ∑ k : ι, (b k - a k) ≠ 0 := ne_of_gt hpos
        field_simp
      linarith
  intro ε hε
  have hex_grid : ∀ k : ι, ∃ N : ℕ, 0 < N ∧
      ∀ j ∈ Finset.range N, ∀ s ∈ Icc (gridPt (a k) (b k) N j) (gridPt (a k) (b k) N (j + 1)),
        ∀ t ∈ Icc (gridPt (a k) (b k) N j) (gridPt (a k) (b k) N (j + 1)),
          |f' k s - f' k t| < ε / 2 := by
    intro k
    have huc := isCompact_Icc.uniformContinuousOn_of_continuous (hcont' k)
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ_pos, hδ⟩ := huc (ε / 2) (half_pos hε)
    obtain ⟨N, hN_gt⟩ := exists_nat_gt ((b k - a k) / δ + 1)
    have hN_pos : 0 < N := by
      have : (0 : ℝ) < (b k - a k) / δ + 1 := by
        have := div_nonneg (sub_nonneg.mpr (hab k)) (le_of_lt hδ_pos); linarith
      exact Nat.cast_pos.mp (this.trans hN_gt)
    refine ⟨N, hN_pos, fun j hj s hs t ht => ?_⟩
    have hj' : j < N := Finset.mem_range.mp hj
    have hsub := gridPt_Icc_subset (hab k) hN_pos hj'
    have hstep_lt : (b k - a k) / (N : ℝ) < δ := by
      rw [div_lt_iff₀ (Nat.cast_pos.mpr hN_pos)]
      have h1 : (b k - a k) / δ < (N : ℝ) := by linarith
      have := (div_lt_iff₀ hδ_pos).mp h1
      linarith
    have hdist : dist s t < δ := by
      rw [Real.dist_eq, abs_lt]
      have hlen := gridPt_sub_succ (a k) (b k) N j
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    simpa [Real.dist_eq] using hδ s (hsub hs) t (hsub ht) hdist
  choose N hN_pos hN_osc using hex_grid
  let isSteep (k : ι) (j : ℕ) : Prop :=
    a k < b k ∧ ∀ t ∈ Icc (gridPt (a k) (b k) (N k) j) (gridPt (a k) (b k) (N k) (j + 1)),
      ε ≤ |f' k t|
  classical
  have hsteep_cell : ∀ k : ι, ∀ j ∈ Finset.range (N k), isSteep k j →
      ∫ t in (gridPt (a k) (b k) (N k) j)..(gridPt (a k) (b k) (N k) (j + 1)), |f' k t| =
        (volume (f k '' Ioo (gridPt (a k) (b k) (N k) j) (gridPt (a k) (b k) (N k) (j + 1)))).toReal ∧
      MeasurableSet (f k '' Ioo (gridPt (a k) (b k) (N k) j) (gridPt (a k) (b k) (N k) (j + 1))) := by
    intro k j hj hst
    have hj' : j < N k := Finset.mem_range.mp hj
    have hsub := gridPt_Icc_subset (hab k) (hN_pos k) hj'
    set t₀ := gridPt (a k) (b k) (N k) j
    set t₁ := gridPt (a k) (b k) (N k) (j + 1)
    have ht_lt : t₀ < t₁ := by
      have hlen := gridPt_sub_succ (a k) (b k) (N k) j
      have : 0 < (b k - a k) / (N k : ℝ) := div_pos (sub_pos.mpr hst.1) (Nat.cast_pos.mpr (hN_pos k))
      linarith
    have hosc := hN_osc k j hj
    have hsign : (∀ t ∈ Icc t₀ t₁, 0 < f' k t) ∨ (∀ t ∈ Icc t₀ t₁, f' k t < 0) := by
      have ht0_ge := hst.2 t₀ (left_mem_Icc.mpr (le_of_lt ht_lt))
      rcases le_or_gt 0 (f' k t₀) with hpos | hneg
      · left
        intro t ht
        have ho := hosc t ht t₀ (left_mem_Icc.mpr (le_of_lt ht_lt))
        rw [abs_of_nonneg hpos] at ht0_ge
        rw [abs_lt] at ho
        linarith
      · right
        intro t ht
        have ho := hosc t ht t₀ (left_mem_Icc.mpr (le_of_lt ht_lt))
        rw [abs_of_neg hneg] at ht0_ge
        rw [abs_lt] at ho
        linarith
    have hint' : IntervalIntegrable (f' k) volume t₀ t₁ := by
      have hsub_u : uIcc t₀ t₁ ⊆ Icc (a k) (b k) := by rw [uIcc_of_le (le_of_lt ht_lt)]; exact hsub
      exact ((hcont' k).mono hsub_u).intervalIntegrable
    have hcont_f : ContinuousOn (f k) (Icc t₀ t₁) :=
      fun t ht => (hderiv k t (hsub ht)).continuousAt.continuousWithinAt
    rcases hsign with hpos | hneg
    · have hmono : StrictMonoOn (f k) (Icc t₀ t₁) :=
        strictMonoOn_of_deriv_pos (convex_Icc t₀ t₁) hcont_f fun t ht => by
          rw [interior_Icc] at ht
          rw [(hderiv k t (hsub (Ioo_subset_Icc_self ht))).deriv]
          exact hpos t (Ioo_subset_Icc_self ht)
      have himg : f k '' Ioo t₀ t₁ = Ioo (f k t₀) (f k t₁) := by
        ext y
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨hmono (left_mem_Icc.mpr (le_of_lt ht_lt)) (Ioo_subset_Icc_self ht) ht.1,
            hmono (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr (le_of_lt ht_lt)) ht.2⟩
        · intro hy
          exact intermediate_value_Ioo (le_of_lt ht_lt) hcont_f hy
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hderiv k t (hsub (by rwa [uIcc_of_le (le_of_lt ht_lt)] at ht))) hint'
      have habs_eq : ∫ t in t₀..t₁, |f' k t| = ∫ t in t₀..t₁, f' k t :=
        intervalIntegral.integral_congr fun t ht => by
          rw [uIcc_of_le (le_of_lt ht_lt)] at ht
          exact abs_of_pos (hpos t ht)
      rw [habs_eq, hftc, himg, Real.volume_Ioo,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (le_of_lt (hmono (left_mem_Icc.mpr (le_of_lt ht_lt))
          (right_mem_Icc.mpr (le_of_lt ht_lt)) ht_lt)))]
      exact ⟨rfl, measurableSet_Ioo⟩
    · have hanti : StrictAntiOn (f k) (Icc t₀ t₁) :=
        strictAntiOn_of_deriv_neg (convex_Icc t₀ t₁) hcont_f fun t ht => by
          rw [interior_Icc] at ht
          rw [(hderiv k t (hsub (Ioo_subset_Icc_self ht))).deriv]
          exact hneg t (Ioo_subset_Icc_self ht)
      have himg : f k '' Ioo t₀ t₁ = Ioo (f k t₁) (f k t₀) := by
        ext y
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨hanti (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr (le_of_lt ht_lt)) ht.2,
            hanti (left_mem_Icc.mpr (le_of_lt ht_lt)) (Ioo_subset_Icc_self ht) ht.1⟩
        · intro hy
          exact intermediate_value_Ioo' (le_of_lt ht_lt) hcont_f hy
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hderiv k t (hsub (by rwa [uIcc_of_le (le_of_lt ht_lt)] at ht))) hint'
      have habs_eq : ∫ t in t₀..t₁, |f' k t| = -(∫ t in t₀..t₁, f' k t) := by
        rw [← intervalIntegral.integral_neg]
        exact intervalIntegral.integral_congr fun t ht => by
          rw [uIcc_of_le (le_of_lt ht_lt)] at ht
          exact abs_of_neg (hneg t ht)
      rw [habs_eq, hftc, neg_sub, himg, Real.volume_Ioo,
        ENNReal.toReal_ofReal (sub_nonneg.mpr (le_of_lt (hanti (left_mem_Icc.mpr (le_of_lt ht_lt))
          (right_mem_Icc.mpr (le_of_lt ht_lt)) ht_lt)))]
      exact ⟨rfl, measurableSet_Ioo⟩
  have hflat_cell : ∀ k : ι, ∀ j ∈ Finset.range (N k), ¬ isSteep k j →
      ∫ t in (gridPt (a k) (b k) (N k) j)..(gridPt (a k) (b k) (N k) (j + 1)), |f' k t| ≤
        2 * ε * ((b k - a k) / (N k : ℝ)) := by
    intro k j hj hnot
    have hj' : j < N k := Finset.mem_range.mp hj
    set t₀ := gridPt (a k) (b k) (N k) j
    set t₁ := gridPt (a k) (b k) (N k) (j + 1)
    rcases eq_or_lt_of_le (hab k) with heq | hlt
    · simp [t₀, t₁, gridPt, heq]
    · have hle : t₀ ≤ t₁ := gridPt_mono (hab k) (N k) (Nat.le_succ j)
      have hlen : t₁ - t₀ = (b k - a k) / (N k : ℝ) := gridPt_sub_succ (a k) (b k) (N k) j
      have hex : ∃ s ∈ Icc t₀ t₁, |f' k s| < ε := by
        by_contra hall; push Not at hall; exact hnot ⟨hlt, hall⟩
      obtain ⟨s, hs, hs_lt⟩ := hex
      have hsub := gridPt_Icc_subset (hab k) (hN_pos k) hj'
      have hi1 : IntervalIntegrable (fun t => |f' k t|) volume t₀ t₁ := by
        have hsub_u : uIcc t₀ t₁ ⊆ Icc (a k) (b k) := by rw [uIcc_of_le hle]; exact hsub
        exact (((hcont' k).abs).mono hsub_u).intervalIntegrable
      have hbd : ∀ t ∈ Icc t₀ t₁, |f' k t| ≤ 2 * ε := by
        intro t ht
        have ho := hN_osc k j hj t ht s hs
        have htri : |f' k t| - |f' k s| ≤ |f' k t - f' k s| := abs_sub_abs_le_abs_sub _ _
        linarith
      have h := intervalIntegral.integral_mono_on hle hi1 intervalIntegrable_const hbd
      rw [intervalIntegral.integral_const, smul_eq_mul, hlen] at h
      linarith
  let steepPairs : Finset (Σ k : ι, ℕ) :=
    Finset.univ.sigma (fun k => (Finset.range (N k)).filter (fun j => isSteep k j))
  have hsteep_sum :
      ∑ p ∈ steepPairs,
        (volume (f p.1 '' Ioo (gridPt (a p.1) (b p.1) (N p.1) p.2)
          (gridPt (a p.1) (b p.1) (N p.1) (p.2 + 1)))).toReal ≤
        (M : ℝ) * (volume U).toReal := by
    let img (p : Σ k : ι, ℕ) : Set ℝ :=
      f p.1 '' Ioo (gridPt (a p.1) (b p.1) (N p.1) p.2) (gridPt (a p.1) (b p.1) (N p.1) (p.2 + 1))
    have hpt : ∀ x : ℝ, (∑ p ∈ steepPairs, (img p).indicator (1 : ℝ → ℝ≥0∞) x) ≤
        (M : ℝ≥0∞) * U.indicator (1 : ℝ → ℝ≥0∞) x := by
      intro x
      by_cases hxU : x ∈ U
      · rw [indicator_of_mem hxU, Pi.one_apply, mul_one]
        obtain ⟨S, hS_card, hS_mem⟩ := hmult x hxU
        let hit := steepPairs.filter (fun p => x ∈ img p)
        have hsum_hit : ∑ p ∈ steepPairs, (img p).indicator (1 : ℝ → ℝ≥0∞) x = (hit.card : ℝ≥0∞) := by
          rw [← Finset.sum_filter_add_sum_filter_not (s := steepPairs) (p := fun p => x ∈ img p)]
          have h0 : ∑ p ∈ steepPairs.filter (fun p => x ∉ img p),
              (img p).indicator (1 : ℝ → ℝ≥0∞) x = 0 :=
            Finset.sum_eq_zero fun p hp => indicator_of_notMem (Finset.mem_filter.mp hp).2 _
          have h1 : ∑ p ∈ hit, (img p).indicator (1 : ℝ → ℝ≥0∞) x = (hit.card : ℝ≥0∞) := by
            calc ∑ p ∈ hit, (img p).indicator (1 : ℝ → ℝ≥0∞) x
                = ∑ _p ∈ hit, (1 : ℝ≥0∞) :=
                  Finset.sum_congr rfl fun p hp => by rw [indicator_of_mem (Finset.mem_filter.mp hp).2]; rfl
              _ = (hit.card : ℝ≥0∞) := by simp
          rw [h0, add_zero, h1]
        rw [hsum_hit]
        have hcard_le : hit.card ≤ S.card := by
          have hchoose : ∀ p : Σ k : ι, ℕ, p ∈ hit →
              ∃ t ∈ Ioo (gridPt (a p.1) (b p.1) (N p.1) p.2)
                (gridPt (a p.1) (b p.1) (N p.1) (p.2 + 1)), f p.1 t = x :=
            fun p hp => (Finset.mem_filter.mp hp).2
          let wit : (p : Σ k : ι, ℕ) → ι × ℝ := fun p =>
            if hp : p ∈ hit then (p.1, (hchoose p hp).choose) else (p.1, 0)
          refine Finset.card_le_card_of_injOn wit ?_ ?_
          · intro p hp
            have hpmem : p ∈ hit := hp
            dsimp only [wit]; rw [dif_pos hpmem]
            have hsp : p ∈ steepPairs := (Finset.mem_filter.mp hpmem).1
            simp only [steepPairs, Finset.mem_sigma, Finset.mem_univ, true_and,
              Finset.mem_filter, Finset.mem_range] at hsp
            have htw := (hchoose p hpmem).choose_spec
            exact hS_mem p.1 _ (gridPt_Ioo_subset (hab p.1) (hN_pos p.1) hsp.1 htw.1) htw.2
          · intro p₁ hp₁ p₂ hp₂ heq
            have hp1 : p₁ ∈ hit := hp₁
            have hp2 : p₂ ∈ hit := hp₂
            dsimp only [wit] at heq
            rw [dif_pos hp1, dif_pos hp2] at heq
            have hk_eq : p₁.1 = p₂.1 := congrArg Prod.fst heq
            rcases p₁ with ⟨k₁, j₁⟩; rcases p₂ with ⟨k₂, j₂⟩
            dsimp only at hk_eq; subst hk_eq
            have ht_eq : (hchoose ⟨k₁, j₁⟩ hp1).choose = (hchoose ⟨k₁, j₂⟩ hp2).choose :=
              congrArg Prod.snd heq
            have ht1 := (hchoose ⟨k₁, j₁⟩ hp1).choose_spec.1
            have ht2 := (hchoose ⟨k₁, j₂⟩ hp2).choose_spec.1
            rw [ht_eq] at ht1
            have hj_eq : j₁ = j₂ := by
              by_contra hne
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · have := gridPt_mono (hab k₁) (N k₁) (show j₁ + 1 ≤ j₂ by omega)
                linarith [ht1.2, ht2.1]
              · have := gridPt_mono (hab k₁) (N k₁) (show j₂ + 1 ≤ j₁ by omega)
                linarith [ht2.2, ht1.1]
            subst hj_eq; rfl
        exact_mod_cast hcard_le.trans hS_card
      · rw [indicator_of_notMem hxU, mul_zero]
        have hzero : ∑ p ∈ steepPairs, (img p).indicator (1 : ℝ → ℝ≥0∞) x = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          apply indicator_of_notMem
          rintro ⟨t, ht, rfl⟩
          simp only [steepPairs, Finset.mem_sigma, Finset.mem_univ, true_and,
            Finset.mem_filter, Finset.mem_range] at hp
          exact hxU (hU_sub p.1 t (gridPt_Ioo_subset (hab p.1) (hN_pos p.1) hp.1 ht))
        rw [hzero]
    have hlint : (∑ p ∈ steepPairs, volume (img p)) ≤ (M : ℝ≥0∞) * volume U := by
      have hmeas_p : ∀ p ∈ steepPairs, MeasurableSet (img p) := by
        intro p hp
        simp only [steepPairs, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_filter] at hp
        exact (hsteep_cell p.1 p.2 hp.1 hp.2).2
      calc ∑ p ∈ steepPairs, volume (img p)
          = ∑ p ∈ steepPairs, ∫⁻ x, (img p).indicator (1 : ℝ → ℝ≥0∞) x ∂volume := by
            refine Finset.sum_congr rfl fun p hp => ?_
            rw [lintegral_indicator_one (hmeas_p p hp)]
        _ = ∫⁻ x, ∑ p ∈ steepPairs, (img p).indicator (1 : ℝ → ℝ≥0∞) x ∂volume := by
            rw [lintegral_finsetSum]
            intro p hp
            exact measurable_const.indicator (hmeas_p p hp)
        _ ≤ ∫⁻ x, (M : ℝ≥0∞) * U.indicator (1 : ℝ → ℝ≥0∞) x ∂volume :=
            lintegral_mono hpt
        _ = (M : ℝ≥0∞) * volume U := by
            rw [lintegral_const_mul _ (measurable_one.indicator hU_meas),
              lintegral_indicator_one hU_meas]
    have hfin_rhs : (M : ℝ≥0∞) * volume U ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top M) hU_fin
    have hfin_p : ∀ p ∈ steepPairs, volume (img p) ≠ ⊤ := fun p hp =>
      ne_top_of_le_ne_top hfin_rhs ((Finset.single_le_sum (fun _ _ => bot_le) hp).trans hlint)
    calc ∑ p ∈ steepPairs, (volume (img p)).toReal
        = (∑ p ∈ steepPairs, volume (img p)).toReal := (ENNReal.toReal_sum hfin_p).symm
      _ ≤ ((M : ℝ≥0∞) * volume U).toReal := ENNReal.toReal_mono hfin_rhs hlint
      _ = (M : ℝ) * (volume U).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hsplit_all : ∀ k : ι,
      ∫ t in (a k)..(b k), |f' k t| ≤
        (∑ j ∈ (Finset.range (N k)).filter (fun j => isSteep k j),
          (volume (f k '' Ioo (gridPt (a k) (b k) (N k) j) (gridPt (a k) (b k) (N k) (j + 1)))).toReal) +
        2 * ε * (b k - a k) := by
    intro k
    have hgrid := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t => |f' k t|) (a := gridPt (a k) (b k) (N k)) (n := N k) fun j hj => by
        have hsub_u : uIcc (gridPt (a k) (b k) (N k) j) (gridPt (a k) (b k) (N k) (j + 1)) ⊆
            Icc (a k) (b k) := by
          rw [uIcc_of_le (gridPt_mono (hab k) (N k) (Nat.le_succ j))]
          exact gridPt_Icc_subset (hab k) (hN_pos k) hj
        exact (((hcont' k).abs).mono hsub_u).intervalIntegrable
    rw [gridPt_zero, gridPt_end (a k) (b k) (hN_pos k)] at hgrid
    rw [← hgrid, ← Finset.sum_filter_add_sum_filter_not (s := Finset.range (N k)) (p := isSteep k)]
    refine add_le_add ?_ ?_
    · refine Finset.sum_le_sum fun j hj => ?_
      rw [Finset.mem_filter] at hj
      exact le_of_eq (hsteep_cell k j hj.1 hj.2).1
    · calc ∑ j ∈ (Finset.range (N k)).filter (fun j => ¬ isSteep k j),
              ∫ t in (gridPt (a k) (b k) (N k) j)..(gridPt (a k) (b k) (N k) (j + 1)), |f' k t|
          ≤ ∑ _j ∈ (Finset.range (N k)).filter (fun j => ¬ isSteep k j),
              2 * ε * ((b k - a k) / (N k : ℝ)) :=
            Finset.sum_le_sum fun j hj => by
              rw [Finset.mem_filter] at hj
              exact hflat_cell k j hj.1 hj.2
        _ ≤ ∑ _j ∈ Finset.range (N k), 2 * ε * ((b k - a k) / (N k : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
              mul_nonneg (by linarith) (div_nonneg (sub_nonneg.mpr (hab k)) (Nat.cast_nonneg _))
        _ = 2 * ε * (b k - a k) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            have hN0 : (N k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hN_pos k; omega)
            field_simp
  calc ∑ k : ι, ∫ t in (a k)..(b k), |f' k t|
      ≤ ∑ k : ι, ((∑ j ∈ (Finset.range (N k)).filter (fun j => isSteep k j),
          (volume (f k '' Ioo (gridPt (a k) (b k) (N k) j)
            (gridPt (a k) (b k) (N k) (j + 1)))).toReal) + 2 * ε * (b k - a k)) :=
        Finset.sum_le_sum fun k _ => hsplit_all k
    _ = (∑ p ∈ steepPairs,
          (volume (f p.1 '' Ioo (gridPt (a p.1) (b p.1) (N p.1) p.2)
            (gridPt (a p.1) (b p.1) (N p.1) (p.2 + 1)))).toReal) +
        2 * ε * ∑ k : ι, (b k - a k) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sigma]
    _ ≤ (M : ℝ) * (volume U).toReal + 2 * ε * ∑ k : ι, (b k - a k) := by
        linarith

-- ============================================================================
-- Section 3: Monic polynomial coordinates, complex IFT, local inverse branches,
--            and circle-integral representation on regular arcs
-- ============================================================================

/-- The monic degree-`n` polynomial `X^n + ∑_{j < n} a_j X^j`. -/
def monicPoly (n : ℕ) (a : Fin n → ℂ) : ℂ[X] :=
  X ^ n + ∑ j : Fin n, C (a j) * X ^ (j : ℕ)

/-- Critical values of a complex polynomial `p`. -/
def critVals (p : ℂ[X]) : Set ℂ :=
  {w | ∃ z : ℂ, p.derivative.eval z = 0 ∧ p.eval z = w}

/-- The subset of the lemniscate of `p` mapping into the unit-circle arc `{e^{iθ} : θ ∈ I}`. -/
def arcSet (p : ℂ[X]) (I : Set ℝ) : Set ℂ :=
  {z : ℂ | ∃ θ ∈ I, p.eval z = Complex.exp ((θ : ℂ) * Complex.I)}

/-- Circle-integral integrand in `ℝ≥0∞` (taking `∞` at critical values). -/
def circleIntegrandENN (p : ℂ[X]) (θ : ℝ) : ℝ≥0∞ :=
  ((p - C (Complex.exp ((θ : ℂ) * Complex.I))).roots.map
    (fun z => (ENNReal.ofReal ‖p.derivative.eval z‖)⁻¹)).sum

/-- Real-valued circle-integral integrand (equals `∑ 1/|p'(z)|` away from critical values). -/
def circleIntegrand (p : ℂ[X]) (θ : ℝ) : ℝ :=
  ((p - C (Complex.exp ((θ : ℂ) * Complex.I))).roots.map
    (fun z => ‖p.derivative.eval z‖⁻¹)).sum

lemma monicPoly_eval (n : ℕ) (a : Fin n → ℂ) (z : ℂ) :
    (monicPoly n a).eval z = z ^ n + ∑ j : Fin n, a j * z ^ (j : ℕ) := by
  simp [monicPoly, Polynomial.eval_finsetSum]

lemma monicPoly_natDegree_lt_sum (n : ℕ) (a : Fin n → ℂ) :
    (∑ j : Fin n, C (a j) * X ^ (j : ℕ)).degree < (X ^ n : ℂ[X]).degree := by
  rw [Polynomial.degree_X_pow]
  refine (Polynomial.degree_sum_le _ _).trans_lt ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun j _ => ?_
  calc (C (a j) * X ^ (j : ℕ)).degree
      ≤ (C (a j)).degree + (X ^ (j : ℕ)).degree := Polynomial.degree_mul_le _ _
    _ ≤ 0 + (j : ℕ) := add_le_add Polynomial.degree_C_le (by rw [Polynomial.degree_X_pow])
    _ < (n : WithBot ℕ) := by rw [zero_add]; exact_mod_cast j.isLt

lemma monicPoly_monic (n : ℕ) (a : Fin n → ℂ) : (monicPoly n a).Monic :=
  (Polynomial.monic_X_pow n).add_of_left (monicPoly_natDegree_lt_sum n a)

lemma monicPoly_natDegree (n : ℕ) (a : Fin n → ℂ) : (monicPoly n a).natDegree = n := by
  have hlt := monicPoly_natDegree_lt_sum n a
  have hdeg : (monicPoly n a).degree = (n : WithBot ℕ) := by
    unfold monicPoly
    rw [Polynomial.degree_add_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
  exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

lemma monicPoly_coeff (n : ℕ) (a : Fin n → ℂ) (k : Fin n) :
    (monicPoly n a).coeff (k : ℕ) = a k := by
  simp only [monicPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [if_neg (ne_of_lt k.isLt), zero_add]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    have hne : (k : ℕ) ≠ (j : ℕ) := fun h => hjk (Fin.ext h.symm)
    simp [hne]
  · intro hk; exact (hk (Finset.mem_univ k)).elim

lemma eq_monicPoly_of_monic {n : ℕ} {p : ℂ[X]} (hp : p.Monic) (hdeg : p.natDegree = n) :
    p = monicPoly n (fun j => p.coeff (j : ℕ)) := by
  have hsum := hp.as_sum
  rw [hdeg] at hsum
  conv_lhs => rw [hsum]
  rw [monicPoly]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j => C (p.coeff j) * X ^ j) n).symm

lemma monicPoly_derivative_eval (n : ℕ) (a : Fin n → ℂ) (z : ℂ) :
    (monicPoly n a).derivative.eval z =
      (n : ℂ) * z ^ (n - 1) + ∑ j : Fin n, a j * ((j : ℕ) : ℂ) * z ^ ((j : ℕ) - 1) := by
  have h1 : HasDerivAt (fun w => (monicPoly n a).eval w) ((monicPoly n a).derivative.eval z) z :=
    (monicPoly n a).hasDerivAt z
  have h2 : HasDerivAt (fun w => w ^ n + ∑ j : Fin n, a j * w ^ (j : ℕ))
      ((n : ℂ) * z ^ (n - 1) + ∑ j : Fin n, a j * ((j : ℕ) : ℂ) * z ^ ((j : ℕ) - 1)) z := by
    refine (hasDerivAt_pow n z).add ?_
    have hsum : HasDerivAt (fun w => ∑ j : Fin n, a j * w ^ (j : ℕ))
        (∑ j : Fin n, a j * (((j : ℕ) : ℂ) * z ^ ((j : ℕ) - 1))) z :=
      HasDerivAt.fun_sum fun j _ => (hasDerivAt_pow (j : ℕ) z).const_mul (a j)
    simpa [mul_assoc] using hsum
  have heq : (fun w => (monicPoly n a).eval w) = (fun w => w ^ n + ∑ j : Fin n, a j * w ^ (j : ℕ)) := by
    funext w; exact monicPoly_eval n a w
  rw [heq] at h1
  exact h1.unique h2

lemma continuous_monicPoly_eval (n : ℕ) :
    Continuous (fun p : (Fin n → ℂ) × ℂ => (monicPoly n p.1).eval p.2) := by
  have h : (fun p : (Fin n → ℂ) × ℂ => (monicPoly n p.1).eval p.2) =
      fun p => p.2 ^ n + ∑ j : Fin n, p.1 j * p.2 ^ (j : ℕ) := by
    funext p; exact monicPoly_eval n p.1 p.2
  rw [h]
  exact (continuous_snd.pow n).add (continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp continuous_fst).mul (continuous_snd.pow (j : ℕ)))

lemma continuous_monicPoly_deriv_eval (n : ℕ) :
    Continuous (fun p : (Fin n → ℂ) × ℂ => (monicPoly n p.1).derivative.eval p.2) := by
  have h : (fun p : (Fin n → ℂ) × ℂ => (monicPoly n p.1).derivative.eval p.2) =
      fun p => (n : ℂ) * p.2 ^ (n - 1) + ∑ j : Fin n, p.1 j * ((j : ℕ) : ℂ) * p.2 ^ ((j : ℕ) - 1) := by
    funext p; exact monicPoly_derivative_eval n p.1 p.2
  rw [h]
  exact (continuous_const.mul (continuous_snd.pow (n - 1))).add
    (continuous_finsetSum _ fun j _ =>
      (((continuous_apply j).comp continuous_fst).mul continuous_const).mul
        (continuous_snd.pow ((j : ℕ) - 1)))

/-- The smooth map `(a, z) ↦ (a, p_a(z))` used for the complex Implicit Function Theorem. -/
private def polyMap (n : ℕ) (p : (Fin n → ℂ) × ℂ) : (Fin n → ℂ) × ℂ :=
  (p.1, (monicPoly n p.1).eval p.2)

private lemma contDiff_polyMap (n : ℕ) : ContDiff ℂ 1 (polyMap n) := by
  have h : polyMap n = fun p => (p.1, p.2 ^ n + ∑ j : Fin n, p.1 j * p.2 ^ (j : ℕ)) := by
    funext p; simp [polyMap, monicPoly_eval]
  rw [h]
  refine contDiff_fst.prodMk ?_
  refine (contDiff_snd.pow n).add (ContDiff.sum fun j _ => ?_)
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).contDiff.comp contDiff_fst).mul
    (contDiff_snd.pow (j : ℕ))

private def polyMapLin (n : ℕ) (z₀ : ℂ) : (Fin n → ℂ) →L[ℂ] ℂ :=
  ∑ j : Fin n, (z₀ ^ (j : ℕ)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j

private lemma polyMapLin_apply (n : ℕ) (z₀ : ℂ) (da : Fin n → ℂ) :
    polyMapLin n z₀ da = ∑ j : Fin n, da j * z₀ ^ (j : ℕ) := by
  simp [polyMapLin, mul_comm]

private def polyMapDerivEquiv (n : ℕ) (a₀ : Fin n → ℂ) (z₀ : ℂ)
    (hd : (monicPoly n a₀).derivative.eval z₀ ≠ 0) :
    ((Fin n → ℂ) × ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ) where
  toFun v := (v.1, polyMapLin n z₀ v.1 + (monicPoly n a₀).derivative.eval z₀ * v.2)
  invFun v := (v.1, ((monicPoly n a₀).derivative.eval z₀)⁻¹ * (v.2 - polyMapLin n z₀ v.1))
  map_add' u v := by
    ext <;> simp [map_add, mul_add]; ring
  map_smul' c v := by
    ext <;> simp [map_smul, smul_eq_mul]; ring
  left_inv v := by
    ext
    · rfl
    · dsimp only
      rw [add_sub_cancel_left, inv_mul_cancel_left₀ hd]
  right_inv v := by
    ext
    · rfl
    · dsimp only
      rw [mul_inv_cancel_left₀ hd, add_sub_cancel]
  continuous_toFun :=
    continuous_fst.prodMk (((polyMapLin n z₀).continuous.comp continuous_fst).add
      (continuous_const.mul continuous_snd))
  continuous_invFun :=
    continuous_fst.prodMk (continuous_const.mul
      (continuous_snd.sub ((polyMapLin n z₀).continuous.comp continuous_fst)))

private lemma hasFDerivAt_polyMap (n : ℕ) (a₀ : Fin n → ℂ) (z₀ : ℂ)
    (hd : (monicPoly n a₀).derivative.eval z₀ ≠ 0) :
    HasFDerivAt (polyMap n) ((polyMapDerivEquiv n a₀ z₀ hd : ((Fin n → ℂ) × ℂ) →L[ℂ] ((Fin n → ℂ) × ℂ)))
      (a₀, z₀) := by
  have heval : HasFDerivAt (fun p : (Fin n → ℂ) × ℂ => (monicPoly n p.1).eval p.2)
      ((polyMapLin n z₀).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ) +
        ((monicPoly n a₀).derivative.eval z₀) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ) (a₀, z₀) := by
    have hfun : (fun p : (Fin n → ℂ) × ℂ => (monicPoly n p.1).eval p.2) =
        fun p => p.2 ^ n + ∑ j : Fin n, p.1 j * p.2 ^ (j : ℕ) := by
      funext p; exact monicPoly_eval n p.1 p.2
    rw [hfun]
    have hpow : HasFDerivAt (fun p : (Fin n → ℂ) × ℂ => p.2 ^ n)
        (((n : ℂ) * z₀ ^ (n - 1)) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ) (a₀, z₀) := by
      have h1 := ((hasDerivAt_pow n z₀).hasFDerivAt).comp (a₀, z₀)
        (hasFDerivAt_snd (𝕜 := ℂ) (E := Fin n → ℂ) (F := ℂ))
      exact h1.congr_fderiv (ContinuousLinearMap.ext fun v => by simp [smul_eq_mul]; ring)
    have hterm : ∀ j : Fin n,
        HasFDerivAt (fun p : (Fin n → ℂ) × ℂ => p.1 j * p.2 ^ (j : ℕ))
          ((z₀ ^ (j : ℕ)) • ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).comp
              (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)) +
            (a₀ j * ((j : ℕ) : ℂ) * z₀ ^ ((j : ℕ) - 1)) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ)
          (a₀, z₀) := by
      intro j
      have hf1 : HasFDerivAt (fun p : (Fin n → ℂ) × ℂ => p.1 j)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).comp
            (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ))
          (a₀, z₀) :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).hasFDerivAt).comp (a₀, z₀)
          (hasFDerivAt_fst (𝕜 := ℂ) (E := Fin n → ℂ) (F := ℂ))
      have hf2 : HasFDerivAt (fun p : (Fin n → ℂ) × ℂ => p.2 ^ (j : ℕ))
          ((((j : ℕ) : ℂ) * z₀ ^ ((j : ℕ) - 1)) • ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ) (a₀, z₀) := by
        have h1 := ((hasDerivAt_pow (j : ℕ) z₀).hasFDerivAt).comp (a₀, z₀)
          (hasFDerivAt_snd (𝕜 := ℂ) (E := Fin n → ℂ) (F := ℂ))
        exact h1.congr_fderiv (ContinuousLinearMap.ext fun v => by simp [smul_eq_mul]; ring)
      refine (hf1.mul hf2).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
      simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.proj_apply, smul_eq_mul]
      ring
    have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => hterm j
    refine (hpow.add hsum).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      smul_apply, sum_apply, ContinuousLinearMap.proj_apply, polyMapLin_apply,
      monicPoly_derivative_eval, smul_eq_mul]
    rw [Finset.sum_add_distrib, add_mul, Finset.sum_mul]
    ring
  have hprod := (hasFDerivAt_fst (𝕜 := ℂ) (E := Fin n → ℂ) (F := ℂ) (p := (a₀, z₀))).prodMk heval
  refine hprod.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  ext <;> simp [polyMapDerivEquiv, smul_eq_mul]

/-- Local smooth inverse branch around a single simple root `(a₀, z₀)` of `monicPoly n a₀`. -/
private lemma exists_single_local_branch {n : ℕ} (a₀ : Fin n → ℂ) (z₀ : ℂ)
    (hd : (monicPoly n a₀).derivative.eval z₀ ≠ 0) {r : ℝ} (hr : 0 < r) :
    ∃ (U : Set (Fin n → ℂ)) (V : Set ℂ) (g : (Fin n → ℂ) → ℂ → ℂ),
      IsOpen U ∧ a₀ ∈ U ∧ IsOpen V ∧ (monicPoly n a₀).eval z₀ ∈ V ∧
      ContinuousOn (fun p : (Fin n → ℂ) × ℂ => g p.1 p.2) (U ×ˢ V) ∧
      g a₀ ((monicPoly n a₀).eval z₀) = z₀ ∧
      (∀ a ∈ U, ∀ w ∈ V, g a w ∈ Metric.ball z₀ r) ∧
      (∀ a ∈ U, ∀ w ∈ V, (monicPoly n a).eval (g a w) = w) ∧
      (∀ a ∈ U, ∀ w ∈ V, (monicPoly n a).derivative.eval (g a w) ≠ 0) ∧
      (∀ a ∈ U, ∀ w ∈ V, HasDerivAt (g a) (((monicPoly n a).derivative.eval (g a w))⁻¹) w) := by
  have hcd : ContDiffAt ℂ 1 (polyMap n) (a₀, z₀) := (contDiff_polyMap n).contDiffAt
  have hf' := hasFDerivAt_polyMap n a₀ z₀ hd
  have h1ne0 : (1 : WithTop ℕ∞) ≠ 0 := by simp
  let e := hcd.toOpenPartialHomeomorph (polyMap n) hf' h1ne0
  set w₀ := (monicPoly n a₀).eval z₀
  have hmem_tgt : (a₀, w₀) ∈ e.target :=
    hcd.image_mem_toOpenPartialHomeomorph_target hf' h1ne0
  have hsymm_cd : ContDiffAt ℂ 1 e.symm (a₀, w₀) :=
    hcd.to_localInverse hf' h1ne0
  have hsymm_at0 : e.symm (a₀, w₀) = (a₀, z₀) :=
    hcd.localInverse_apply_image hf' h1ne0
  have hev_cd : ∀ᶠ y in 𝓝 (a₀, w₀), ContDiffAt ℂ 1 e.symm y :=
    hsymm_cd.eventually (by simp)
  have hev_tgt : ∀ᶠ y in 𝓝 (a₀, w₀), y ∈ e.target := e.open_target.mem_nhds hmem_tgt
  have hev_ball : ∀ᶠ y in 𝓝 (a₀, w₀), (e.symm y).2 ∈ Metric.ball z₀ r := by
    have hc : ContinuousAt (fun y => (e.symm y).2) (a₀, w₀) :=
      continuous_snd.continuousAt.comp hsymm_cd.continuousAt
    exact hc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by rw [hsymm_at0]; exact Metric.mem_ball_self hr))
  have hev_dne : ∀ᶠ y in 𝓝 (a₀, w₀), (monicPoly n (e.symm y).1).derivative.eval (e.symm y).2 ≠ 0 := by
    have hc : ContinuousAt (fun y => (monicPoly n (e.symm y).1).derivative.eval (e.symm y).2) (a₀, w₀) :=
      (continuous_monicPoly_deriv_eval n).continuousAt.comp hsymm_cd.continuousAt
    exact hc.eventually_ne (by simpa [hsymm_at0] using hd)
  have hev_all := hev_cd.and (hev_tgt.and (hev_ball.and hev_dne))
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at hev_all
  obtain ⟨pa, hpa, pw, hpw, hprod⟩ := hev_all
  obtain ⟨U, hU_sub, hU_open, ha₀_U⟩ := mem_nhds_iff.mp hpa
  obtain ⟨V, hV_sub, hV_open, hw₀_V⟩ := mem_nhds_iff.mp hpw
  let g : (Fin n → ℂ) → ℂ → ℂ := fun a w => (e.symm (a, w)).2
  have hUV : ∀ a ∈ U, ∀ w ∈ V,
      ContDiffAt ℂ 1 e.symm (a, w) ∧ (a, w) ∈ e.target ∧
        g a w ∈ Metric.ball z₀ r ∧ (monicPoly n (e.symm (a, w)).1).derivative.eval (g a w) ≠ 0 :=
    fun a ha w hw => hprod (hU_sub ha) (hV_sub hw)
  have hfst_eq : ∀ a ∈ U, ∀ w ∈ V, (e.symm (a, w)).1 = a ∧ (monicPoly n a).eval (g a w) = w := by
    intro a ha w hw
    have hrt := e.right_inv (hUV a ha w hw).2.1
    have h1 : polyMap n (e.symm (a, w)) = (a, w) := hrt
    have hf1 : (e.symm (a, w)).1 = a := congrArg Prod.fst h1
    have hf2 : (monicPoly n (e.symm (a, w)).1).eval (e.symm (a, w)).2 = w := congrArg Prod.snd h1
    rw [hf1] at hf2
    exact ⟨hf1, hf2⟩
  refine ⟨U, V, g, hU_open, ha₀_U, hV_open, hw₀_V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (continuous_snd.continuousAt.comp (hUV p.1 hp.1 p.2 hp.2).1.continuousAt).continuousWithinAt
  · simp [g, hsymm_at0]
  · intro a ha w hw; exact (hUV a ha w hw).2.2.1
  · intro a ha w hw; exact (hfst_eq a ha w hw).2
  · intro a ha w hw
    have hne := (hUV a ha w hw).2.2.2
    rwa [(hfst_eq a ha w hw).1] at hne
  · intro a ha w hw
    have hcd' := (hUV a ha w hw).1
    have hdiff_g : DifferentiableAt ℂ (g a) w := by
      have h1 : DifferentiableAt ℂ e.symm (a, w) := hcd'.differentiableAt (by simp)
      have h2 : DifferentiableAt ℂ (fun ζ : ℂ => (a, ζ)) w :=
        (differentiableAt_const a).prodMk differentiableAt_id
      exact differentiableAt_snd.comp w (h1.comp w h2)
    have hderiv_g : HasDerivAt (g a) (deriv (g a) w) w := hdiff_g.hasDerivAt
    have hcomp : HasDerivAt (fun ζ => (monicPoly n a).eval (g a ζ))
        ((monicPoly n a).derivative.eval (g a w) * deriv (g a) w) w :=
      ((monicPoly n a).hasDerivAt (g a w)).comp w hderiv_g
    have hev_id : (fun ζ => (monicPoly n a).eval (g a ζ)) =ᶠ[𝓝 w] id := by
      filter_upwards [hV_open.mem_nhds hw] with ζ hζ
      exact (hfst_eq a ha ζ hζ).2
    have hid : HasDerivAt (fun ζ => (monicPoly n a).eval (g a ζ)) 1 w :=
      (hasDerivAt_id w).congr_of_eventuallyEq hev_id
    have hmul : (monicPoly n a).derivative.eval (g a w) * deriv (g a) w = 1 :=
      hcomp.unique hid
    have hd_eq : deriv (g a) w = ((monicPoly n a).derivative.eval (g a w))⁻¹ :=
      eq_inv_of_mul_eq_one_right hmul
    rwa [hd_eq] at hderiv_g

private lemma rootMultiplicity_eq_one_of_deriv_ne_zero {p : ℂ[X]} {z : ℂ}
    (hr : p.eval z = 0) (hd : p.derivative.eval z ≠ 0) :
    p.rootMultiplicity z = 1 := by
  have hp_ne : p ≠ 0 := by
    intro h0; rw [h0, Polynomial.derivative_zero, Polynomial.eval_zero] at hd; exact hd rfl
  have hge1 : 1 ≤ p.rootMultiplicity z :=
    Nat.succ_le_of_lt ((Polynomial.rootMultiplicity_pos hp_ne).mpr hr)
  have hd_mult : p.derivative.rootMultiplicity z = 0 :=
    Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hd)
  have hrel := Polynomial.derivative_rootMultiplicity_of_root hr
  omega

/-- All `n` smooth local inverse branches simultaneously on a neighborhood `U ×ˢ V` around any
`(a₀, w₀)` where `w₀` is not a critical value of `monicPoly n a₀`. -/
theorem exists_local_inverse_branches {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n → ℂ) (w₀ : ℂ)
    (hreg : w₀ ∉ critVals (monicPoly n a₀)) :
    ∃ (U : Set (Fin n → ℂ)) (V : Set ℂ) (g : Fin n → (Fin n → ℂ) → ℂ → ℂ),
      IsOpen U ∧ a₀ ∈ U ∧ IsOpen V ∧ w₀ ∈ V ∧
      (∀ j, ContinuousOn (fun p : (Fin n → ℂ) × ℂ => g j p.1 p.2) (U ×ˢ V)) ∧
      (∀ a ∈ U, ∀ w ∈ V, Function.Injective (fun j => g j a w)) ∧
      (∀ j, ∀ a ∈ U, ∀ w ∈ V, (monicPoly n a).eval (g j a w) = w) ∧
      (∀ j, ∀ a ∈ U, ∀ w ∈ V, (monicPoly n a).derivative.eval (g j a w) ≠ 0) ∧
      (∀ j, ∀ a ∈ U, ∀ w ∈ V, HasDerivAt (g j a) (((monicPoly n a).derivative.eval (g j a w))⁻¹) w) ∧
      (∀ a ∈ U, ∀ w ∈ V, (monicPoly n a - C w).roots = Finset.univ.val.map (fun j => g j a w)) := by
  let q₀ := monicPoly n a₀ - C w₀
  have hq0_deg : q₀.natDegree = n := by
    rw [Polynomial.natDegree_sub_C, monicPoly_natDegree]
  have hq0_monic : q₀.Monic :=
    (monicPoly_monic n a₀).sub_of_left <| Polynomial.degree_C_le.trans_lt <| by
      rw [Polynomial.degree_eq_natDegree (monicPoly_monic n a₀).ne_zero, monicPoly_natDegree]
      exact_mod_cast hn
  have hq0_card : q₀.roots.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hq0_deg]
  have hq0_nodup : q₀.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro ζ
    by_cases hmem : ζ ∈ q₀.roots
    · have hev : (monicPoly n a₀).eval ζ = w₀ := by
        have := (Polynomial.mem_roots hq0_monic.ne_zero).mp hmem
        simpa [q₀, sub_eq_zero] using this
      have hd_ne : (monicPoly n a₀).derivative.eval ζ ≠ 0 :=
        fun hd0 => hreg ⟨ζ, hd0, hev⟩
      have hq_deriv : q₀.derivative = (monicPoly n a₀).derivative := by
        simp [q₀]
      have hmult1 : q₀.rootMultiplicity ζ = 1 :=
        rootMultiplicity_eq_one_of_deriv_ne_zero ((Polynomial.mem_roots hq0_monic.ne_zero).mp hmem)
          (by rwa [hq_deriv])
      rw [Polynomial.count_roots, hmult1]
    · rw [Multiset.count_eq_zero.mpr hmem]; exact Nat.zero_le 1
  -- Enumerate the n distinct roots of q₀
  have hcard_finset : q₀.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hq0_nodup, hq0_card]
  let zEquiv : Fin n ≃ q₀.roots.toFinset := (Fintype.equivFinOfCardEq (by simpa using hcard_finset)).symm
  let z : Fin n → ℂ := fun j => (zEquiv j).1
  have hz_inj : Function.Injective z := fun i j hij => zEquiv.injective (Subtype.ext hij)
  have hz_eval : ∀ j, (monicPoly n a₀).eval (z j) = w₀ := by
    intro j
    have hmem : z j ∈ q₀.roots := Multiset.mem_toFinset.mp (zEquiv j).2
    have := (Polynomial.mem_roots hq0_monic.ne_zero).mp hmem
    simpa [q₀, sub_eq_zero] using this
  have hz_dne : ∀ j, (monicPoly n a₀).derivative.eval (z j) ≠ 0 :=
    fun j hd0 => hreg ⟨z j, hd0, hz_eval j⟩
  -- Pick r > 0 so balls B(z j, r) are pairwise disjoint
  have hex_r : ∃ r : ℝ, 0 < r ∧ ∀ i j : Fin n, i ≠ j → 2 * r ≤ dist (z i) (z j) := by
    let pairs := (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 ≠ p.2)
    by_cases hpe : pairs.Nonempty
    · let dmin := pairs.inf' hpe (fun p => dist (z p.1) (z p.2))
      have hd_pos : 0 < dmin := by
        rw [Finset.lt_inf'_iff]
        intro p hp
        have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
        exact dist_pos.mpr fun h => hne (hz_inj h)
      refine ⟨dmin / 2, half_pos hd_pos, fun i j hij => ?_⟩
      have hmem : (i, j) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hij⟩
      have hle : dmin ≤ dist (z i) (z j) := Finset.inf'_le _ hmem
      linarith
    · refine ⟨1, one_pos, fun i j hij => ?_⟩
      exfalso; exact hpe ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hij⟩⟩
  obtain ⟨r, hr_pos, hr_sep⟩ := hex_r
  have hsingle : ∀ j : Fin n, ∃ (Uj : Set (Fin n → ℂ)) (Vj : Set ℂ) (gj : (Fin n → ℂ) → ℂ → ℂ),
      IsOpen Uj ∧ a₀ ∈ Uj ∧ IsOpen Vj ∧ w₀ ∈ Vj ∧
      ContinuousOn (fun p : (Fin n → ℂ) × ℂ => gj p.1 p.2) (Uj ×ˢ Vj) ∧
      (∀ a ∈ Uj, ∀ w ∈ Vj, gj a w ∈ Metric.ball (z j) r) ∧
      (∀ a ∈ Uj, ∀ w ∈ Vj, (monicPoly n a).eval (gj a w) = w) ∧
      (∀ a ∈ Uj, ∀ w ∈ Vj, (monicPoly n a).derivative.eval (gj a w) ≠ 0) ∧
      (∀ a ∈ Uj, ∀ w ∈ Vj, HasDerivAt (gj a) (((monicPoly n a).derivative.eval (gj a w))⁻¹) w) := by
    intro j
    obtain ⟨Uj, Vj, gj, hUo, haU, hVo, hwV, hcont, _, hball, hev, hdne, hder⟩ :=
      exists_single_local_branch a₀ (z j) (hz_dne j) hr_pos
    rw [hz_eval j] at hwV
    exact ⟨Uj, Vj, gj, hUo, haU, hVo, hwV, hcont, hball, hev, hdne, hder⟩
  choose Uj Vj g hUo haU hVo hwV hcont hball hev hdne hder using hsingle
  let U : Set (Fin n → ℂ) := ⋂ j : Fin n, Uj j
  let V : Set ℂ := ⋂ j : Fin n, Vj j
  have hU_open : IsOpen U := isOpen_iInter_of_finite hUo
  have ha₀_U : a₀ ∈ U := mem_iInter.mpr haU
  have hV_open : IsOpen V := isOpen_iInter_of_finite hVo
  have hw₀_V : w₀ ∈ V := mem_iInter.mpr hwV
  have hU_sub : ∀ j, U ⊆ Uj j := fun j => iInter_subset _ j
  have hV_sub : ∀ j, V ⊆ Vj j := fun j => iInter_subset _ j
  have hg_inj : ∀ a ∈ U, ∀ w ∈ V, Function.Injective (fun j => g j a w) := by
    intro a ha w hw i j hij
    dsimp only at hij
    by_contra hne
    have hi : dist (g i a w) (z i) < r := Metric.mem_ball.mp (hball i a (hU_sub i ha) w (hV_sub i hw))
    have hj : dist (g j a w) (z j) < r := Metric.mem_ball.mp (hball j a (hU_sub j ha) w (hV_sub j hw))
    have htri := dist_triangle (z i) (g i a w) (z j)
    rw [dist_comm (z i) (g i a w)] at htri
    rw [hij] at hi htri
    linarith [hr_sep i j hne]
  refine ⟨U, V, g, hU_open, ha₀_U, hV_open, hw₀_V, ?_, hg_inj, ?_, ?_, ?_, ?_⟩
  · intro j; exact (hcont j).mono (prod_mono (hU_sub j) (hV_sub j))
  · intro j a ha w hw; exact hev j a (hU_sub j ha) w (hV_sub j hw)
  · intro j a ha w hw; exact hdne j a (hU_sub j ha) w (hV_sub j hw)
  · intro j a ha w hw; exact hder j a (hU_sub j ha) w (hV_sub j hw)
  · intro a ha w hw
    let q := monicPoly n a - C w
    have hq_deg : q.natDegree = n := by rw [Polynomial.natDegree_sub_C, monicPoly_natDegree]
    have hq_monic : q.Monic :=
      (monicPoly_monic n a).sub_of_left <| Polynomial.degree_C_le.trans_lt <| by
        rw [Polynomial.degree_eq_natDegree (monicPoly_monic n a).ne_zero, monicPoly_natDegree]
        exact_mod_cast hn
    have hq_card : q.roots.card = n := by rw [IsAlgClosed.card_roots_eq_natDegree, hq_deg]
    let m : Multiset ℂ := Finset.univ.val.map (fun j => g j a w)
    have hm_nodup : m.Nodup :=
      Multiset.Nodup.map (hg_inj a ha w hw) Finset.univ.nodup
    have hm_le : m ≤ q.roots := by
      rw [Multiset.le_iff_subset hm_nodup]
      intro ζ hζ
      rcases Multiset.mem_map.mp hζ with ⟨j, _, rfl⟩
      exact (Polynomial.mem_roots hq_monic.ne_zero).mpr
        (by simp [q, hev j a (hU_sub j ha) w (hV_sub j hw)])
    have hm_card : m.card = q.roots.card := by
      simp [m, hq_card]
    exact (Multiset.eq_of_le_of_card_le hm_le (le_of_eq hm_card.symm)).symm

private lemma exp_mul_I_injOn_Ioo : InjOn (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I))
    (Ioo (0 : ℝ) (2 * Real.pi)) := by
  intro θ₁ h₁ θ₂ h₂ heq
  rw [Complex.exp_eq_exp_iff_exists_int] at heq
  rcases heq with ⟨k, hk⟩
  have hreal : θ₁ = θ₂ + (k : ℝ) * (2 * Real.pi) := by
    have hmul : ((θ₁ : ℂ) - (θ₂ : ℂ) - (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I = 0 := by
      push_cast
      linear_combination hk
    have h0 : (θ₁ : ℂ) - (θ₂ : ℂ) - (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) = 0 :=
      (mul_eq_zero.mp hmul).resolve_right Complex.I_ne_zero
    have hre := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith
  have hk0 : k = 0 := by
    by_contra hne
    have hpi : 0 < Real.pi := Real.pi_pos
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hk_le : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
      nlinarith [h₁.1, h₂.2]
    · have hk_ge : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hgt
      nlinarith [h₁.2, h₂.1]
  rw [hk0] at hreal; simp at hreal; exact hreal

private lemma finite_preimage_eval {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]}
    (_hp : p.Monic) (hdeg : p.natDegree = n) {S : Set ℂ} (hS : S.Finite) :
    {z : ℂ | p.eval z ∈ S}.Finite := by
  have h1 : ∀ w : ℂ, {z : ℂ | p.eval z = w}.Finite := by
    intro w
    have hq_ne : p - C w ≠ 0 := by
      have hd : (p - C w).natDegree = n := by rw [Polynomial.natDegree_sub_C, hdeg]
      intro h0; rw [h0, Polynomial.natDegree_zero] at hd; omega
    refine ((p - C w).roots.toFinset.finite_toSet).subset fun z hz => ?_
    exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq_ne).mpr (by simpa [sub_eq_zero] using hz)))
  have heq : {z : ℂ | p.eval z ∈ S} = ⋃ w ∈ S, {z : ℂ | p.eval z = w} := by
    ext z; simp
  rw [heq]
  exact hS.biUnion fun w _ => h1 w

private lemma arcSet_Icc_eq_integral_of_branch {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℂ)
    {u v : ℝ} (huv : u ≤ v) (hsub : Icc u v ⊆ Ioo (0 : ℝ) (2 * Real.pi))
    {g : Fin n → ℂ → ℂ}
    (hcont : ∀ j, ContinuousOn (fun t : ℝ => g j (Complex.exp ((t : ℂ) * Complex.I))) (Icc u v))
    (hinj_j : ∀ t ∈ Icc u v, Function.Injective (fun j => g j (Complex.exp ((t : ℂ) * Complex.I))))
    (hev : ∀ j, ∀ t ∈ Icc u v, (monicPoly n a).eval (g j (Complex.exp ((t : ℂ) * Complex.I))) =
      Complex.exp ((t : ℂ) * Complex.I))
    (hdne : ∀ j, ∀ t ∈ Icc u v, (monicPoly n a).derivative.eval (g j (Complex.exp ((t : ℂ) * Complex.I))) ≠ 0)
    (hder : ∀ j, ∀ t ∈ Icc u v, HasDerivAt (g j)
      (((monicPoly n a).derivative.eval (g j (Complex.exp ((t : ℂ) * Complex.I))))⁻¹)
      (Complex.exp ((t : ℂ) * Complex.I)))
    (hroots : ∀ t ∈ Icc u v, (monicPoly n a - C (Complex.exp ((t : ℂ) * Complex.I))).roots =
      Finset.univ.val.map (fun j => g j (Complex.exp ((t : ℂ) * Complex.I)))) :
    (μH[1] : Measure ℂ) (arcSet (monicPoly n a) (Icc u v)) =
      ENNReal.ofReal (∫ t in u..v, circleIntegrand (monicPoly n a) t) := by
  let γ : Fin n → ℝ → ℂ := fun j t => g j (Complex.exp ((t : ℂ) * Complex.I))
  let γ' : Fin n → ℝ → ℂ := fun j t =>
    ((monicPoly n a).derivative.eval (γ j t))⁻¹ * (Complex.exp ((t : ℂ) * Complex.I) * Complex.I)
  have hγ_deriv : ∀ j, ∀ t ∈ Icc u v, HasDerivAt (γ j) (γ' j t) t := by
    intro j t ht
    have hexp : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t := by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
      exact (Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp t h1
    exact (hder j t ht).comp t hexp
  have hγ'_norm : ∀ j, ∀ t ∈ Icc u v, ‖γ' j t‖ = ‖(monicPoly n a).derivative.eval (γ j t)‖⁻¹ := by
    intro j t _
    simp only [γ', norm_mul, norm_inv, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one]
  have hγ'_cont : ∀ j, ContinuousOn (γ' j) (Icc u v) := by
    intro j
    have h1 : ContinuousOn (fun t : ℝ => (monicPoly n a).derivative.eval (γ j t)) (Icc u v) :=
      ((monicPoly n a).derivative.continuous.comp_continuousOn (hcont j))
    have h2 : ContinuousOn (fun t : ℝ => ((monicPoly n a).derivative.eval (γ j t))⁻¹) (Icc u v) :=
      h1.inv₀ fun t ht => hdne j t ht
    have h3 : ContinuousOn (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) * Complex.I) (Icc u v) :=
      ((Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).mul
        continuous_const).continuousOn
    exact h2.mul h3
  have hγ_inj : ∀ j, InjOn (γ j) (Icc u v) := by
    intro j t₁ ht₁ t₂ ht₂ heq
    dsimp only [γ] at heq
    have h1 := hev j t₁ ht₁
    have h2 := hev j t₂ ht₂
    rw [heq] at h1
    exact exp_mul_I_injOn_Ioo (hsub ht₁) (hsub ht₂) (h1.symm.trans h2)
  have harc_eq : arcSet (monicPoly n a) (Icc u v) = ⋃ j : Fin n, γ j '' Icc u v := by
    ext z
    constructor
    · rintro ⟨t, ht, htz⟩
      have hq_ne : monicPoly n a - C (Complex.exp ((t : ℂ) * Complex.I)) ≠ 0 := by
        have hd : (monicPoly n a - C (Complex.exp ((t : ℂ) * Complex.I))).natDegree = n := by
          rw [Polynomial.natDegree_sub_C, monicPoly_natDegree]
        intro h0; rw [h0, Polynomial.natDegree_zero] at hd; omega
      have hmem : z ∈ (monicPoly n a - C (Complex.exp ((t : ℂ) * Complex.I))).roots :=
        (Polynomial.mem_roots hq_ne).mpr (by simp [htz])
      rw [hroots t ht] at hmem
      rcases Multiset.mem_map.mp hmem with ⟨j, _, rfl⟩
      exact mem_iUnion.mpr ⟨j, ⟨t, ht, rfl⟩⟩
    · intro hz
      rcases mem_iUnion.mp hz with ⟨j, t, ht, rfl⟩
      exact ⟨t, ht, hev j t ht⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun j : Fin n => γ j '' Icc u v) := by
    intro i j hij
    dsimp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro z ⟨t₁, ht₁, rfl⟩ ⟨t₂, ht₂, h2⟩
    dsimp only [γ] at h2
    have he1 := hev i t₁ ht₁
    have he2 := hev j t₂ ht₂
    rw [h2] at he2
    have ht_eq : t₁ = t₂ := exp_mul_I_injOn_Ioo (hsub ht₁) (hsub ht₂) (he1.symm.trans he2)
    subst ht_eq
    exact hij (hinj_j t₁ ht₁ h2.symm)
  have hmeas : ∀ j : Fin n, MeasurableSet (γ j '' Icc u v) := fun j =>
    (isCompact_Icc.image_of_continuousOn (hcont j)).measurableSet
  have hci_eq : ∀ t ∈ Icc u v, circleIntegrand (monicPoly n a) t = ∑ j : Fin n, ‖γ' j t‖ := by
    intro t ht
    unfold circleIntegrand
    rw [hroots t ht, Multiset.map_map]
    change (Finset.univ.val.map (fun j : Fin n => ‖(monicPoly n a).derivative.eval (γ j t)‖⁻¹)).sum = _
    change ∑ j : Fin n, ‖(monicPoly n a).derivative.eval (γ j t)‖⁻¹ = ∑ j : Fin n, ‖γ' j t‖
    exact Finset.sum_congr rfl fun j _ => (hγ'_norm j t ht).symm
  rw [harc_eq, measure_iUnion hdisj hmeas, tsum_fintype]
  have hsum_meas : ∑ j : Fin n, (μH[1] : Measure ℂ) (γ j '' Icc u v) =
      ∑ j : Fin n, ENNReal.ofReal (∫ t in u..v, ‖γ' j t‖) :=
    Finset.sum_congr rfl fun j _ =>
      hausdorffMeasure_one_image_Icc_eq_integral huv (hγ_inj j) (hγ_deriv j) (hγ'_cont j)
  rw [hsum_meas, ← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    intervalIntegral.integral_nonneg huv fun t _ => norm_nonneg _)]
  congr 1
  rw [← intervalIntegral.integral_finsetSum]
  · exact intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le huv] at ht; exact (hci_eq t ht).symm
  · intro j _
    have hsub_u : uIcc u v ⊆ Icc u v := by rw [uIcc_of_le huv]
    exact ((hγ'_cont j).norm.mono hsub_u).intervalIntegrable

private lemma arcSet_Icc_grid_sum {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]}
    (hp : p.Monic) (hdeg : p.natDegree = n)
    {α β : ℝ} (hαβ : α ≤ β) (hsub : Icc α β ⊆ Ioo (0 : ℝ) (2 * Real.pi))
    {M : ℕ} (hM_pos : 0 < M) :
    (μH[1] : Measure ℂ) (arcSet p (Icc α β)) =
      ∑ k ∈ Finset.range M,
        (μH[1] : Measure ℂ) (arcSet p (Icc (gridPt α β M k) (gridPt α β M (k + 1)))) := by
  have hcont_exp : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  let Epts : Set ℂ := {z : ℂ | p.eval z ∈
    (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) ''
      (Finset.image (gridPt α β M) (Finset.range (M + 1)) : Set ℝ)}
  have hEpts_zero : (μH[1] : Measure ℂ) Epts = 0 :=
    hausdorffMeasure_one_finite_eq_zero (finite_preimage_eval hn hp hdeg ((Finset.finite_toSet _).image _))
  have hpiece_eq : ∀ k ∈ Finset.range M,
      (μH[1] : Measure ℂ) (arcSet p (Icc (gridPt α β M k) (gridPt α β M (k + 1)))) =
        (μH[1] : Measure ℂ) (arcSet p (Ioo (gridPt α β M k) (gridPt α β M (k + 1)))) := by
    intro k hk
    have hk' : k < M := Finset.mem_range.mp hk
    have hdiff : arcSet p (Icc (gridPt α β M k) (gridPt α β M (k + 1))) ⊆
        arcSet p (Ioo (gridPt α β M k) (gridPt α β M (k + 1))) ∪ Epts := by
      rintro z ⟨t, ht, htz⟩
      rcases eq_or_lt_of_le ht.1 with rfl | h1
      · exact Or.inr ⟨gridPt α β M k, Finset.mem_coe.mpr (Finset.mem_image.mpr
          ⟨k, Finset.mem_range.mpr (by omega), rfl⟩), htz.symm⟩
      · rcases eq_or_lt_of_le ht.2 with rfl | h2
        · exact Or.inr ⟨gridPt α β M (k + 1), Finset.mem_coe.mpr (Finset.mem_image.mpr
            ⟨k + 1, Finset.mem_range.mpr (by omega), rfl⟩), htz.symm⟩
        · exact Or.inl ⟨t, ⟨h1, h2⟩, htz⟩
    refine le_antisymm ?_ (measure_mono fun z ⟨t, ht, htz⟩ => ⟨t, Ioo_subset_Icc_self ht, htz⟩)
    calc (μH[1] : Measure ℂ) (arcSet p (Icc (gridPt α β M k) (gridPt α β M (k + 1))))
        ≤ (μH[1] : Measure ℂ) (arcSet p (Ioo (gridPt α β M k) (gridPt α β M (k + 1))) ∪ Epts) :=
          measure_mono hdiff
      _ ≤ (μH[1] : Measure ℂ) (arcSet p (Ioo (gridPt α β M k) (gridPt α β M (k + 1)))) +
            (μH[1] : Measure ℂ) Epts := measure_union_le _ _
      _ = _ := by rw [hEpts_zero, add_zero]
  have hmeas_oo : ∀ k ∈ Finset.range M,
      MeasurableSet (arcSet p (Ioo (gridPt α β M k) (gridPt α β M (k + 1)))) := by
    intro k hk
    have hk' : k < M := Finset.mem_range.mp hk
    have hcell_sub := gridPt_Icc_subset hαβ hM_pos hk'
    have hpre : arcSet p (Ioo (gridPt α β M k) (gridPt α β M (k + 1))) =
        (fun z => p.eval z) ⁻¹'
          ((fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) ''
            Ioo (gridPt α β M k) (gridPt α β M (k + 1))) := by
      ext z; simp [arcSet, eq_comm]
    rw [hpre]
    have hset : (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) ''
          Ioo (gridPt α β M k) (gridPt α β M (k + 1)) =
        ((fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) ''
          Icc (gridPt α β M k) (gridPt α β M (k + 1))) \
        {Complex.exp ((gridPt α β M k : ℂ) * Complex.I),
          Complex.exp ((gridPt α β M (k + 1) : ℂ) * Complex.I)} := by
      have hle : gridPt α β M k ≤ gridPt α β M (k + 1) := gridPt_mono hαβ M (Nat.le_succ k)
      ext w
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨⟨t, Ioo_subset_Icc_self ht, rfl⟩, ?_⟩
        rintro (h1 | h2)
        · have := exp_mul_I_injOn_Ioo (hsub (hcell_sub (Ioo_subset_Icc_self ht)))
            (hsub (hcell_sub (left_mem_Icc.mpr hle))) h1
          linarith [ht.1]
        · have := exp_mul_I_injOn_Ioo (hsub (hcell_sub (Ioo_subset_Icc_self ht)))
            (hsub (hcell_sub (right_mem_Icc.mpr hle))) h2
          linarith [ht.2]
      · rintro ⟨⟨t, ht, rfl⟩, hne⟩
        refine ⟨t, ⟨?_, ?_⟩, rfl⟩
        · exact lt_of_le_of_ne ht.1 fun h => hne (Or.inl (by rw [h]))
        · exact lt_of_le_of_ne ht.2 fun h => hne (Or.inr (by rw [h]; rfl))
    have hmeas_img : MeasurableSet ((fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) ''
        Ioo (gridPt α β M k) (gridPt α β M (k + 1))) := by
      rw [hset]
      exact (isCompact_Icc.image hcont_exp).measurableSet.diff
        ((Set.finite_singleton _).insert _).measurableSet
    exact hmeas_img.preimage p.continuous.measurable
  have hdisj_oo : PairwiseDisjoint (Finset.range M : Set ℕ)
      (fun k => arcSet p (Ioo (gridPt α β M k) (gridPt α β M (k + 1)))) := by
    intro i hi j hj hij
    dsimp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro z ⟨t₁, ht₁, h1⟩ ⟨t₂, ht₂, h2⟩
    have hi' : i < M := Finset.mem_range.mp hi
    have hj' : j < M := Finset.mem_range.mp hj
    have ht_eq : t₁ = t₂ := exp_mul_I_injOn_Ioo
      (hsub (gridPt_Icc_subset hαβ hM_pos hi' (Ioo_subset_Icc_self ht₁)))
      (hsub (gridPt_Icc_subset hαβ hM_pos hj' (Ioo_subset_Icc_self ht₂))) (h1.symm.trans h2)
    subst ht_eq
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have := gridPt_mono hαβ M (show i + 1 ≤ j by omega); linarith [ht₁.2, ht₂.1]
    · have := gridPt_mono hαβ M (show j + 1 ≤ i by omega); linarith [ht₂.2, ht₁.1]
  have hunion : arcSet p (Icc α β) ⊆
      (⋃ k ∈ Finset.range M, arcSet p (Ioo (gridPt α β M k) (gridPt α β M (k + 1)))) ∪ Epts := by
    rintro z ⟨t, ht, htz⟩
    rw [Icc_eq_biUnion_grid hαβ hM_pos] at ht
    rcases mem_iUnion₂.mp ht with ⟨k, hk, htk⟩
    rw [Finset.mem_range] at hk
    rcases eq_or_lt_of_le htk.1 with rfl | h1
    · exact Or.inr ⟨gridPt α β M k, Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨k, Finset.mem_range.mpr (by omega), rfl⟩), htz.symm⟩
    · rcases eq_or_lt_of_le htk.2 with rfl | h2
      · exact Or.inr ⟨gridPt α β M (k + 1), Finset.mem_coe.mpr (Finset.mem_image.mpr
          ⟨k + 1, Finset.mem_range.mpr (by omega), rfl⟩), htz.symm⟩
      · exact Or.inl (mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hk, ⟨t, ⟨h1, h2⟩, htz⟩⟩)
  have hrev : (⋃ k ∈ Finset.range M, arcSet p (Ioo (gridPt α β M k) (gridPt α β M (k + 1)))) ⊆
      arcSet p (Icc α β) :=
    iUnion₂_subset fun k hk z ⟨t, ht, htz⟩ =>
      ⟨t, gridPt_Icc_subset hαβ hM_pos (Finset.mem_range.mp hk) (Ioo_subset_Icc_self ht), htz⟩
  have heq : (μH[1] : Measure ℂ) (arcSet p (Icc α β)) =
      (μH[1] : Measure ℂ) (⋃ k ∈ Finset.range M,
        arcSet p (Ioo (gridPt α β M k) (gridPt α β M (k + 1)))) := by
    refine le_antisymm ?_ (measure_mono hrev)
    calc (μH[1] : Measure ℂ) (arcSet p (Icc α β))
        ≤ (μH[1] : Measure ℂ) ((⋃ k ∈ Finset.range M,
            arcSet p (Ioo (gridPt α β M k) (gridPt α β M (k + 1)))) ∪ Epts) :=
          measure_mono hunion
      _ ≤ (μH[1] : Measure ℂ) (⋃ k ∈ Finset.range M,
            arcSet p (Ioo (gridPt α β M k) (gridPt α β M (k + 1)))) +
            (μH[1] : Measure ℂ) Epts := measure_union_le _ _
      _ = _ := by rw [hEpts_zero, add_zero]
  rw [heq, measure_biUnion_finset hdisj_oo hmeas_oo]
  exact Finset.sum_congr rfl fun k hk => (hpiece_eq k hk).symm

private structure RegularBranchBall (n : ℕ) (a₀ : Fin n → ℂ) (θ : ℝ) where
  U : Set (Fin n → ℂ)
  δ : ℝ
  g : Fin n → (Fin n → ℂ) → ℂ → ℂ
  hU_open : IsOpen U
  ha₀_U : a₀ ∈ U
  hδ_pos : 0 < δ
  hcont : ∀ j, ContinuousOn (fun p : (Fin n → ℂ) × ℝ => g j p.1 (Complex.exp ((p.2 : ℂ) * Complex.I)))
    (U ×ˢ Metric.ball θ δ)
  hinj : ∀ a ∈ U, ∀ t ∈ Metric.ball θ δ, Function.Injective (fun j => g j a (Complex.exp ((t : ℂ) * Complex.I)))
  hev : ∀ j, ∀ a ∈ U, ∀ t ∈ Metric.ball θ δ,
    (monicPoly n a).eval (g j a (Complex.exp ((t : ℂ) * Complex.I))) = Complex.exp ((t : ℂ) * Complex.I)
  hdne : ∀ j, ∀ a ∈ U, ∀ t ∈ Metric.ball θ δ,
    (monicPoly n a).derivative.eval (g j a (Complex.exp ((t : ℂ) * Complex.I))) ≠ 0
  hder : ∀ j, ∀ a ∈ U, ∀ t ∈ Metric.ball θ δ,
    HasDerivAt (g j a) (((monicPoly n a).derivative.eval (g j a (Complex.exp ((t : ℂ) * Complex.I))))⁻¹)
      (Complex.exp ((t : ℂ) * Complex.I))
  hroots : ∀ a ∈ U, ∀ t ∈ Metric.ball θ δ,
    (monicPoly n a - C (Complex.exp ((t : ℂ) * Complex.I))).roots =
      Finset.univ.val.map (fun j => g j a (Complex.exp ((t : ℂ) * Complex.I)))

private lemma exists_regularBranchBall {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n → ℂ) (θ : ℝ)
    (hreg : Complex.exp ((θ : ℂ) * Complex.I) ∉ critVals (monicPoly n a₀)) :
    Nonempty (RegularBranchBall n a₀ θ) := by
  have hcont_exp : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  obtain ⟨Uθ, Vθ, g, hUo, haU, hVo, hwV, hcont, hinj, hev, hdne, hder, hroots⟩ :=
    exists_local_inverse_branches hn a₀ (Complex.exp ((θ : ℂ) * Complex.I)) hreg
  have hpre_open : IsOpen ((fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) ⁻¹' Vθ) :=
    hVo.preimage hcont_exp
  obtain ⟨δθ, hδ_pos, hball_sub⟩ := Metric.isOpen_iff.mp hpre_open θ hwV
  refine ⟨⟨Uθ, δθ, g, hUo, haU, hδ_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j
    have hmap : Continuous (fun p : (Fin n → ℂ) × ℝ => (p.1, Complex.exp ((p.2 : ℂ) * Complex.I))) :=
      continuous_fst.prodMk (hcont_exp.comp continuous_snd)
    refine (hcont j).comp hmap.continuousOn ?_
    rintro ⟨a, t⟩ ⟨ha, ht⟩
    exact ⟨ha, hball_sub ht⟩
  · intro a ha t ht; exact hinj a ha _ (hball_sub ht)
  · intro j a ha t ht; exact hev j a ha _ (hball_sub ht)
  · intro j a ha t ht; exact hdne j a ha _ (hball_sub ht)
  · intro j a ha t ht; exact hder j a ha _ (hball_sub ht)
  · intro a ha t ht; exact hroots a ha _ (hball_sub ht)

private lemma continuousOn_snd_of_prod {α β γ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace γ] {f : α → β → γ} {s : Set α} {t : Set β}
    {a : α} (ha : a ∈ s) (hf : ContinuousOn (fun p : α × β => f p.1 p.2) (s ×ˢ t)) :
    ContinuousOn (f a) t :=
  hf.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hb => ⟨ha, hb⟩

private lemma regular_Icc_continuous_and_reg {n : ℕ} (hn : 1 ≤ n) {a₀ : Fin n → ℂ} {α β : ℝ}
    (B : (θ : Icc α β) → RegularBranchBall n a₀ θ.1)
    {s : Finset (Icc α β)} (hs_cov : Icc α β ⊆ ⋃ θ ∈ s, Metric.ball θ.1 ((B θ).δ / 2)) :
    let U : Set (Fin n → ℂ) := ⋂ θ ∈ s, (B θ).U
    ContinuousOn (fun p : (Fin n → ℂ) × ℝ => circleIntegrand (monicPoly n p.1) p.2) (U ×ˢ Icc α β) ∧
    (∀ a ∈ U, ∀ θ ∈ Icc α β, Complex.exp ((θ : ℂ) * Complex.I) ∉ critVals (monicPoly n a)) := by
  intro U
  have hU_sub : ∀ θ ∈ s, U ⊆ (B θ).U := fun θ hθ => biInter_subset_of_mem hθ
  constructor
  · intro ⟨a, t⟩ ⟨ha, ht⟩
    have ht_cov := hs_cov ht
    simp only [mem_iUnion] at ht_cov
    rcases ht_cov with ⟨θ, hθs, ht_ball⟩
    have ht_ball' : t ∈ Metric.ball θ.1 (B θ).δ :=
      Metric.ball_subset_ball (by linarith [(B θ).hδ_pos]) ht_ball
    let F : (Fin n → ℂ) × ℝ → ℝ := fun p =>
      ∑ j : Fin n, ‖(monicPoly n p.1).derivative.eval ((B θ).g j p.1 (Complex.exp ((p.2 : ℂ) * Complex.I)))‖⁻¹
    have hF_cont : ContinuousOn F ((B θ).U ×ˢ Metric.ball θ.1 (B θ).δ) := by
      refine continuousOn_finsetSum _ fun j _ => ?_
      have h1 : ContinuousOn (fun p : (Fin n → ℂ) × ℝ =>
          (monicPoly n p.1).derivative.eval ((B θ).g j p.1 (Complex.exp ((p.2 : ℂ) * Complex.I))))
          ((B θ).U ×ˢ Metric.ball θ.1 (B θ).δ) :=
        (continuous_monicPoly_deriv_eval n).comp_continuousOn
          (continuous_fst.continuousOn.prodMk ((B θ).hcont j))
      exact h1.norm.inv₀ fun p hp => norm_ne_zero_iff.mpr ((B θ).hdne j p.1 hp.1 p.2 hp.2)
    have heq_on : EqOn (fun p : (Fin n → ℂ) × ℝ => circleIntegrand (monicPoly n p.1) p.2) F
        ((B θ).U ×ˢ Metric.ball θ.1 (B θ).δ) := by
      rintro ⟨a', t'⟩ ⟨ha', ht'⟩
      dsimp only [circleIntegrand, F]
      rw [(B θ).hroots a' ha' t' ht', Multiset.map_map]
      rfl
    have hopen_nbhd : IsOpen ((B θ).U ×ˢ Metric.ball θ.1 (B θ).δ) :=
      (B θ).hU_open.prod Metric.isOpen_ball
    have hmem_nbhd : (a, t) ∈ (B θ).U ×ˢ Metric.ball θ.1 (B θ).δ := ⟨hU_sub θ hθs ha, ht_ball'⟩
    exact ((hF_cont.congr heq_on).continuousAt (hopen_nbhd.mem_nhds hmem_nbhd)).continuousWithinAt
  · intro a ha t ht ⟨ζ, hd0, hevζ⟩
    have ht_cov := hs_cov ht
    simp only [mem_iUnion] at ht_cov
    rcases ht_cov with ⟨θ, hθs, ht_ball⟩
    have ht_ball' : t ∈ Metric.ball θ.1 (B θ).δ :=
      Metric.ball_subset_ball (by linarith [(B θ).hδ_pos]) ht_ball
    have hq_ne : monicPoly n a - C (Complex.exp ((t : ℂ) * Complex.I)) ≠ 0 := by
      have hd : (monicPoly n a - C (Complex.exp ((t : ℂ) * Complex.I))).natDegree = n := by
        rw [Polynomial.natDegree_sub_C, monicPoly_natDegree]
      intro h0; rw [h0, Polynomial.natDegree_zero] at hd; omega
    have hmem : ζ ∈ (monicPoly n a - C (Complex.exp ((t : ℂ) * Complex.I))).roots :=
      (Polynomial.mem_roots hq_ne).mpr (by simp [hevζ])
    rw [(B θ).hroots a (hU_sub θ hθs ha) t ht_ball'] at hmem
    rcases Multiset.mem_map.mp hmem with ⟨j, _, rfl⟩
    exact (B θ).hdne j a (hU_sub θ hθs ha) t ht_ball' hd0

/-- On a regular compact interval `[α, β] ⊆ (0, 2π)` avoiding critical values of `monicPoly n a₀`,
there is an open neighborhood `U ∋ a₀` where `arcSet` has exact Hausdorff measure equal to
the circle integral, and the integrand is jointly continuous on `U ×ˢ [α, β]`. -/
theorem regular_Icc_measure_and_continuity {n : ℕ} (hn : 1 ≤ n) (a₀ : Fin n → ℂ)
    {α β : ℝ} (hαβ : α ≤ β) (hsub : Icc α β ⊆ Ioo (0 : ℝ) (2 * Real.pi))
    (hreg : ∀ θ ∈ Icc α β, Complex.exp ((θ : ℂ) * Complex.I) ∉ critVals (monicPoly n a₀)) :
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧ a₀ ∈ U ∧
      ContinuousOn (fun p : (Fin n → ℂ) × ℝ => circleIntegrand (monicPoly n p.1) p.2) (U ×ˢ Icc α β) ∧
      (∀ a ∈ U, ∀ θ ∈ Icc α β, Complex.exp ((θ : ℂ) * Complex.I) ∉ critVals (monicPoly n a)) ∧
      (∀ a ∈ U, (μH[1] : Measure ℂ) (arcSet (monicPoly n a) (Icc α β)) =
        ENNReal.ofReal (∫ θ in α..β, circleIntegrand (monicPoly n a) θ)) := by
  obtain ⟨B⟩ : Nonempty ((θ : Icc α β) → RegularBranchBall n a₀ θ.1) :=
    ⟨fun θ => Classical.choice (exists_regularBranchBall hn a₀ θ.1 (hreg θ.1 θ.2))⟩
  have hcov : Icc α β ⊆ ⋃ θ : Icc α β, Metric.ball θ.1 ((B θ).δ / 2) := fun t ht =>
    mem_iUnion.mpr ⟨⟨t, ht⟩, Metric.mem_ball_self (half_pos (B ⟨t, ht⟩).hδ_pos)⟩
  obtain ⟨s, hs_cov⟩ := isCompact_Icc.elim_finite_subcover
    (fun θ : Icc α β => Metric.ball θ.1 ((B θ).δ / 2))
    (fun _ => Metric.isOpen_ball) hcov
  have hs_ne : s.Nonempty := by
    have hα_mem := hs_cov (left_mem_Icc.mpr hαβ)
    simp only [mem_iUnion] at hα_mem
    rcases hα_mem with ⟨θ, hθs, _⟩
    exact ⟨θ, hθs⟩
  let U : Set (Fin n → ℂ) := ⋂ θ ∈ s, (B θ).U
  have hU_open : IsOpen U := isOpen_biInter_finset fun θ _ => (B θ).hU_open
  have ha₀_U : a₀ ∈ U := mem_iInter₂.mpr fun θ _ => (B θ).ha₀_U
  have hU_sub : ∀ θ ∈ s, U ⊆ (B θ).U := fun θ hθ => biInter_subset_of_mem hθ
  obtain ⟨hci_cont, hreg_U⟩ := regular_Icc_continuous_and_reg hn B hs_cov
  let δmin : ℝ := s.inf' hs_ne (fun θ => (B θ).δ / 2)
  have hδmin_pos : 0 < δmin := (Finset.lt_inf'_iff hs_ne).mpr fun θ _ => half_pos (B θ).hδ_pos
  obtain ⟨M, hM_gt⟩ := exists_nat_gt ((β - α) / δmin + 1)
  have hM_pos : 0 < M := by
    have : (0 : ℝ) < (β - α) / δmin + 1 := by
      have := div_nonneg (sub_nonneg.mpr hαβ) (le_of_lt hδmin_pos); linarith
    exact Nat.cast_pos.mp (this.trans hM_gt)
  have hstep_lt : (β - α) / (M : ℝ) < δmin := by
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hM_pos)]
    have h1 : (β - α) / δmin < (M : ℝ) := by linarith
    have := (div_lt_iff₀ hδmin_pos).mp h1
    linarith
  refine ⟨U, hU_open, ha₀_U, hci_cont, hreg_U, ?_⟩
  intro a ha
  have hcell_meas : ∀ k ∈ Finset.range M,
      (μH[1] : Measure ℂ) (arcSet (monicPoly n a) (Icc (gridPt α β M k) (gridPt α β M (k + 1)))) =
        ENNReal.ofReal (∫ t in (gridPt α β M k)..(gridPt α β M (k + 1)), circleIntegrand (monicPoly n a) t) := by
    intro k hk
    have hk' : k < M := Finset.mem_range.mp hk
    have hcell_sub := gridPt_Icc_subset hαβ hM_pos hk'
    have hle : gridPt α β M k ≤ gridPt α β M (k + 1) := gridPt_mono hαβ M (Nat.le_succ k)
    have ht0_cov := hs_cov (hcell_sub (left_mem_Icc.mpr hle))
    simp only [mem_iUnion] at ht0_cov
    rcases ht0_cov with ⟨θ, hθs, ht0_ball⟩
    have hcell_ball : Icc (gridPt α β M k) (gridPt α β M (k + 1)) ⊆ Metric.ball θ.1 (B θ).δ := by
      intro t ht
      have hdt0 : dist t (gridPt α β M k) < δmin := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
        have hlen := gridPt_sub_succ α β M k
        linarith [ht.2, hstep_lt]
      have hdmin_le : δmin ≤ (B θ).δ / 2 := Finset.inf'_le _ hθs
      have htri := dist_triangle t (gridPt α β M k) θ.1
      rw [Metric.mem_ball] at ht0_ball ⊢
      linarith
    have haθ : a ∈ (B θ).U := hU_sub θ hθs ha
    exact arcSet_Icc_eq_integral_of_branch hn a hle (hcell_sub.trans hsub)
      (fun j => (((B θ).hcont j).comp (continuous_const.prodMk continuous_id).continuousOn
        fun t ht => ⟨haθ, hcell_ball ht⟩))
      (fun t ht => (B θ).hinj a haθ t (hcell_ball ht))
      (fun j t ht => (B θ).hev j a haθ t (hcell_ball ht))
      (fun j t ht => (B θ).hdne j a haθ t (hcell_ball ht))
      (fun j t ht => (B θ).hder j a haθ t (hcell_ball ht))
      (fun t ht => (B θ).hroots a haθ t (hcell_ball ht))
  have htot_meas := arcSet_Icc_grid_sum hn (monicPoly_monic n a) (monicPoly_natDegree n a) hαβ hsub hM_pos
  have hci_nn : ∀ t, 0 ≤ circleIntegrand (monicPoly n a) t := fun t => by
    unfold circleIntegrand
    exact Multiset.sum_nonneg fun x hx => by
      rcases Multiset.mem_map.mp hx with ⟨_, _, rfl⟩
      exact inv_nonneg.mpr (norm_nonneg _)
  have hci_cont_a : ContinuousOn (fun t : ℝ => circleIntegrand (monicPoly n a) t) (Icc α β) :=
    continuousOn_snd_of_prod (f := fun a' t => circleIntegrand (monicPoly n a') t) ha hci_cont
  have hint_grid : ∫ t in α..β, circleIntegrand (monicPoly n a) t =
      ∑ k ∈ Finset.range M,
        ∫ t in (gridPt α β M k)..(gridPt α β M (k + 1)), circleIntegrand (monicPoly n a) t := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun t => circleIntegrand (monicPoly n a) t) (a := gridPt α β M) (n := M) fun k hk => by
        have hsub_u : uIcc (gridPt α β M k) (gridPt α β M (k + 1)) ⊆ Icc α β := by
          rw [uIcc_of_le (gridPt_mono hαβ M (Nat.le_succ k))]
          exact gridPt_Icc_subset hαβ hM_pos hk
        exact (hci_cont_a.mono hsub_u).intervalIntegrable
    rw [gridPt_zero, gridPt_end α β hM_pos] at h
    exact h.symm
  rw [htot_meas, Finset.sum_congr rfl hcell_meas, ← ENNReal.ofReal_sum_of_nonneg (fun k _ =>
    intervalIntegral.integral_nonneg (gridPt_mono hαβ M (Nat.le_succ k)) fun t _ => hci_nn t),
    ← hint_grid]

-- ============================================================================
-- Section 4: Universal ball-cover bound, circle-integral identity,
--            Eremenko-Hayman Lemma 4 continuity & extremizer existence
-- ============================================================================

private lemma critVals_finite {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]}
    (hp : p.Monic) (hdeg : p.natDegree = n) : (critVals p).Finite := by
  have hd_ne : p.derivative ≠ 0 := by
    intro h0
    have hc : p.derivative.coeff (n - 1) = (n : ℂ) := by
      have h1 : n - 1 + 1 = n := by omega
      rw [Polynomial.coeff_derivative, h1, show p.coeff n = 1 from hdeg ▸ hp.coeff_natDegree, one_mul]
      norm_cast
    rw [h0, Polynomial.coeff_zero] at hc
    exact Nat.cast_ne_zero.mpr (by omega) hc.symm
  refine ((p.derivative.roots.toFinset.finite_toSet).image p.eval).subset ?_
  rintro w ⟨z, hz0, rfl⟩
  exact ⟨z, Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd_ne).mpr hz0)), rfl⟩

private lemma badAngles_finite {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]}
    (hp : p.Monic) (hdeg : p.natDegree = n) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 2 * Real.pi) :
    {θ ∈ Ioo α β | Complex.exp ((θ : ℂ) * Complex.I) ∈ critVals p}.Finite := by
  let S := {θ ∈ Ioo α β | Complex.exp ((θ : ℂ) * Complex.I) ∈ critVals p}
  have hS_sub : S ⊆ Ioo (0 : ℝ) (2 * Real.pi) := fun θ ⟨⟨h1, h2⟩, _⟩ =>
    ⟨lt_of_le_of_lt hα h1, lt_of_lt_of_le h2 hβ⟩
  have hImg_sub : (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' S ⊆ critVals p := by
    rintro w ⟨θ, ⟨_, hcrit⟩, rfl⟩; exact hcrit
  exact Set.Finite.of_finite_image ((critVals_finite hn hp hdeg).subset hImg_sub)
    (exp_mul_I_injOn_Ioo.mono hS_sub)

/-- Partition an open interval `(α, β)` minus a finite set `B ⊆ (α, β)` into `m ≥ 1`
adjacent pairwise-disjoint open subintervals `(c 0, c 1), ..., (c (m-1), c m)`. -/
private lemma partition_Ioo_diff_finset :
    ∀ (k : ℕ) (α β : ℝ) (B : Finset ℝ), B.card = k → α < β → (∀ x ∈ B, x ∈ Ioo α β) →
      ∃ (m : ℕ) (c : ℕ → ℝ), 1 ≤ m ∧ c 0 = α ∧ c m = β ∧
        (∀ s < m, c s < c (s + 1)) ∧
        (∀ s < m, Disjoint (Ioo (c s) (c (s + 1))) (B : Set ℝ)) ∧
        Ioo α β \ (B : Set ℝ) = ⋃ s ∈ Finset.range m, Ioo (c s) (c (s + 1)) := by
  intro k
  induction k with
  | zero =>
    intro α β B hcard hαβ _
    have hB : B = ∅ := Finset.card_eq_zero.mp hcard
    subst hB
    refine ⟨1, fun s => if s = 0 then α else β, le_rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro s hs; have : s = 0 := by omega
      subst this; simpa using hαβ
    · intro s _; simp
    · ext x; simp [Finset.range_one]
  | succ k ih =>
    intro α β B hcard hαβ hBsub
    have hne : B.Nonempty := Finset.card_pos.mp (by omega)
    let xmax := B.max' hne
    have hxmax_mem : xmax ∈ B := Finset.max'_mem B hne
    have hxmax_Ioo : xmax ∈ Ioo α β := hBsub xmax hxmax_mem
    let B' := B.erase xmax
    have hB'_card : B'.card = k := by
      rw [Finset.card_erase_of_mem hxmax_mem, hcard]; omega
    have hB'_sub : ∀ x ∈ B', x ∈ Ioo α xmax := by
      intro x hx
      have hxB : x ∈ B := Finset.mem_of_mem_erase hx
      have hxne : x ≠ xmax := Finset.ne_of_mem_erase hx
      have hxle : x ≤ xmax := Finset.le_max' B x hxB
      exact ⟨(hBsub x hxB).1, lt_of_le_of_ne hxle hxne⟩
    obtain ⟨m, c, hm, hc0, hcm, hinc, hdisj, hunion⟩ := ih α xmax B' hB'_card hxmax_Ioo.1 hB'_sub
    let c' : ℕ → ℝ := fun s => if s ≤ m then c s else β
    refine ⟨m + 1, c', by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp [c', hc0]
    · simp [c']
    · intro s hs
      by_cases hsm : s < m
      · simp only [c', if_pos (le_of_lt hsm), if_pos (show s + 1 ≤ m by omega)]
        exact hinc s hsm
      · have hs_eq : s = m := by omega
        subst s
        simp only [c', le_refl, if_true, if_neg (show ¬ m + 1 ≤ m by omega), hcm]
        exact hxmax_Ioo.2
    · intro s hs
      by_cases hsm : s < m
      · simp only [c', if_pos (le_of_lt hsm), if_pos (show s + 1 ≤ m by omega)]
        rw [Set.disjoint_left]
        intro x hx hxB
        by_cases hxeq : x = xmax
        · subst hxeq
          have hle : c (s + 1) ≤ c m := by
            have hmono : ∀ a b, a ≤ b → b ≤ m → c a ≤ c b := by
              intro a b hab hbm
              induction hab with
              | refl => exact le_rfl
              | @step b' hab' ih' => exact (ih' (by omega)).trans (le_of_lt (hinc b' (by omega)))
            exact hmono (s + 1) m (by omega) le_rfl
          linarith [hx.2, hcm]
        · exact Set.disjoint_left.mp (hdisj s hsm) hx (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hxeq, hxB⟩))
      · have hs_eq : s = m := by omega
        subst s
        simp only [c', le_refl, if_true, if_neg (show ¬ m + 1 ≤ m by omega), hcm]
        rw [Set.disjoint_left]
        intro x hx hxB
        have := Finset.le_max' B x hxB
        linarith [hx.1]
    · ext x
      simp only [Set.mem_sdiff, mem_Ioo, mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨⟨hαx, hxβ⟩, hxnotB⟩
        have hne_max : x ≠ xmax := fun h => hxnotB (h ▸ hxmax_mem)
        rcases lt_or_gt_of_ne hne_max with hlt | hgt
        · have hxmem : x ∈ Ioo α xmax \ (B' : Set ℝ) :=
            ⟨⟨hαx, hlt⟩, fun h => hxnotB (Finset.mem_of_mem_erase h)⟩
          rw [hunion] at hxmem
          simp only [mem_iUnion, Finset.mem_range, mem_Ioo] at hxmem
          rcases hxmem with ⟨s, hsm, hs1, hs2⟩
          refine ⟨s, by omega, ?_, ?_⟩ <;> simp [c', le_of_lt hsm, show s + 1 ≤ m by omega, hs1, hs2]
        · refine ⟨m, by omega, ?_, ?_⟩
          · simp [c', hcm, hgt]
          · simp [c', hxβ]
      · rintro ⟨s, hs, hs1, hs2⟩
        by_cases hsm : s < m
        · simp only [c', if_pos (le_of_lt hsm), if_pos (show s + 1 ≤ m by omega)] at hs1 hs2
          have hxmem : x ∈ ⋃ s ∈ Finset.range m, Ioo (c s) (c (s + 1)) :=
            mem_iUnion₂.mpr ⟨s, Finset.mem_range.mpr hsm, ⟨hs1, hs2⟩⟩
          rw [← hunion] at hxmem
          refine ⟨⟨hxmem.1.1, hxmem.1.2.trans hxmax_Ioo.2⟩, fun hxB => ?_⟩
          by_cases hxeq : x = xmax
          · linarith [hxmem.1.2]
          · exact hxmem.2 (Finset.mem_erase.mpr ⟨hxeq, hxB⟩)
        · have hs_eq : s = m := by omega
          subst s
          simp only [c', le_refl, if_true, if_neg (show ¬ m + 1 ≤ m by omega), hcm] at hs1 hs2
          refine ⟨⟨hxmax_Ioo.1.trans hs1, hs2⟩, fun hxB => ?_⟩
          linarith [Finset.le_max' B x hxB]

/-- Split a single regular compact interval `[u, v]` into `Ms` smooth grid branch cells. -/
private lemma regular_Icc_grid_branches {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℂ) {u v : ℝ}
    (huv : u ≤ v)
    (hreg : ∀ θ ∈ Icc u v, Complex.exp ((θ : ℂ) * Complex.I) ∉ critVals (monicPoly n a)) :
    ∃ (Ms : ℕ) (γs : Fin Ms → Fin n → ℝ → ℂ) (γs' : Fin Ms → Fin n → ℝ → ℂ),
      0 < Ms ∧
      (∀ k : Fin Ms, ∀ j : Fin n, ∀ t ∈ Icc (gridPt u v Ms k.1) (gridPt u v Ms (k.1 + 1)),
        HasDerivAt (γs k j) (γs' k j t) t ∧
        (monicPoly n a).eval (γs k j t) = Complex.exp ((t : ℂ) * Complex.I) ∧
        ‖γs' k j t‖ = ‖(monicPoly n a).derivative.eval (γs k j t)‖⁻¹) ∧
      (∀ k : Fin Ms, ∀ j : Fin n, ContinuousOn (γs' k j)
        (Icc (gridPt u v Ms k.1) (gridPt u v Ms (k.1 + 1)))) ∧
      (∀ k : Fin Ms, ∀ t ∈ Icc (gridPt u v Ms k.1) (gridPt u v Ms (k.1 + 1)),
        Function.Injective (fun j => γs k j t)) ∧
      ∫ θ in u..v, circleIntegrand (monicPoly n a) θ =
        ∑ k : Fin Ms, ∑ j : Fin n,
          ∫ t in (gridPt u v Ms k.1)..(gridPt u v Ms (k.1 + 1)), ‖γs' k j t‖ := by
  obtain ⟨B⟩ : Nonempty ((θ : Icc u v) → RegularBranchBall n a θ.1) :=
    ⟨fun θ => Classical.choice (exists_regularBranchBall hn a θ.1 (hreg θ.1 θ.2))⟩
  have hcov : Icc u v ⊆ ⋃ θ : Icc u v, Metric.ball θ.1 ((B θ).δ / 2) := fun t ht =>
    mem_iUnion.mpr ⟨⟨t, ht⟩, Metric.mem_ball_self (half_pos (B ⟨t, ht⟩).hδ_pos)⟩
  obtain ⟨sf, hsf_cov⟩ := isCompact_Icc.elim_finite_subcover
    (fun θ : Icc u v => Metric.ball θ.1 ((B θ).δ / 2))
    (fun _ => Metric.isOpen_ball) hcov
  have hsf_ne : sf.Nonempty := by
    have hmem := hsf_cov (left_mem_Icc.mpr huv)
    simp only [mem_iUnion] at hmem; rcases hmem with ⟨θ, hθ, _⟩; exact ⟨θ, hθ⟩
  let δmin := sf.inf' hsf_ne (fun θ => (B θ).δ / 2)
  have hδmin_pos : 0 < δmin := (Finset.lt_inf'_iff hsf_ne).mpr fun θ _ => half_pos (B θ).hδ_pos
  obtain ⟨Ms, hMs_gt⟩ := exists_nat_gt ((v - u) / δmin + 1)
  have hMs_pos : 0 < Ms := by
    have : (0 : ℝ) < (v - u) / δmin + 1 := by
      have := div_nonneg (sub_nonneg.mpr huv) (le_of_lt hδmin_pos); linarith
    exact Nat.cast_pos.mp (this.trans hMs_gt)
  have hstep_lt : (v - u) / (Ms : ℝ) < δmin := by
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hMs_pos)]
    have h1 : (v - u) / δmin < (Ms : ℝ) := by linarith
    have := (div_lt_iff₀ hδmin_pos).mp h1
    linarith
  have hpick : ∀ k : Fin Ms, ∃ θ ∈ sf,
      Icc (gridPt u v Ms k.1) (gridPt u v Ms (k.1 + 1)) ⊆ Metric.ball θ.1 (B θ).δ := by
    intro k
    have hcell_sub := gridPt_Icc_subset huv hMs_pos k.isLt
    have hle := gridPt_mono huv Ms (Nat.le_succ k.1)
    have hmem := hsf_cov (hcell_sub (left_mem_Icc.mpr hle))
    simp only [mem_iUnion] at hmem
    rcases hmem with ⟨θ, hθs, ht0_ball⟩
    refine ⟨θ, hθs, fun t ht => ?_⟩
    have hdt0 : dist t (gridPt u v Ms k.1) < δmin := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
      have hlen := gridPt_sub_succ u v Ms k.1
      linarith [ht.2, hstep_lt]
    have hdmin_le : δmin ≤ (B θ).δ / 2 := Finset.inf'_le _ hθs
    have htri := dist_triangle t (gridPt u v Ms k.1) θ.1
    rw [Metric.mem_ball] at ht0_ball ⊢
    linarith
  choose θk hθk_mem hθk_ball using hpick
  let γs : Fin Ms → Fin n → ℝ → ℂ := fun k j t =>
    (B (θk k)).g j a (Complex.exp ((t : ℂ) * Complex.I))
  let γs' : Fin Ms → Fin n → ℝ → ℂ := fun k j t =>
    ((monicPoly n a).derivative.eval (γs k j t))⁻¹ * (Complex.exp ((t : ℂ) * Complex.I) * Complex.I)
  have hγs_der : ∀ k : Fin Ms, ∀ j : Fin n,
      ∀ t ∈ Icc (gridPt u v Ms k.1) (gridPt u v Ms (k.1 + 1)),
        HasDerivAt (γs k j) (γs' k j t) t ∧
        (monicPoly n a).eval (γs k j t) = Complex.exp ((t : ℂ) * Complex.I) ∧
        ‖γs' k j t‖ = ‖(monicPoly n a).derivative.eval (γs k j t)‖⁻¹ := by
    intro k j t ht
    have ht_b := hθk_ball k ht
    have hexp : HasDerivAt (fun τ : ℝ => Complex.exp ((τ : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t := by
      have h1 : HasDerivAt (fun τ : ℝ => (τ : ℂ) * Complex.I) Complex.I t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
      exact (Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp t h1
    refine ⟨((B (θk k)).hder j a (B (θk k)).ha₀_U t ht_b).comp t hexp,
      (B (θk k)).hev j a (B (θk k)).ha₀_U t ht_b, ?_⟩
    simp only [γs', norm_mul, norm_inv, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one]
  have hγs'_cont : ∀ k : Fin Ms, ∀ j : Fin n, ContinuousOn (γs' k j)
      (Icc (gridPt u v Ms k.1) (gridPt u v Ms (k.1 + 1))) := by
    intro k j
    have hcont_g : ContinuousOn (γs k j) (Icc (gridPt u v Ms k.1) (gridPt u v Ms (k.1 + 1))) :=
      ((B (θk k)).hcont j).comp (continuous_const.prodMk continuous_id).continuousOn
        fun t ht => ⟨(B (θk k)).ha₀_U, hθk_ball k ht⟩
    have h1 := (monicPoly n a).derivative.continuous.comp_continuousOn hcont_g
    have h2 := h1.inv₀ fun t ht => (B (θk k)).hdne j a (B (θk k)).ha₀_U t (hθk_ball k ht)
    have h3 : ContinuousOn (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) * Complex.I)
        (Icc (gridPt u v Ms k.1) (gridPt u v Ms (k.1 + 1))) :=
      ((Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).mul
        continuous_const).continuousOn
    exact h2.mul h3
  obtain ⟨hci_cont, _⟩ := regular_Icc_continuous_and_reg hn B hsf_cov
  have hci_cont_a : ContinuousOn (fun t : ℝ => circleIntegrand (monicPoly n a) t) (Icc u v) :=
    continuousOn_snd_of_prod (f := fun a' t => circleIntegrand (monicPoly n a') t)
      (mem_iInter₂.mpr fun θ _ => (B θ).ha₀_U) hci_cont
  refine ⟨Ms, γs, γs', hMs_pos, hγs_der, hγs'_cont,
    fun k t ht => (B (θk k)).hinj a (B (θk k)).ha₀_U t (hθk_ball k ht), ?_⟩
  have hgrid := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun t => circleIntegrand (monicPoly n a) t) (a := gridPt u v Ms) (n := Ms) fun k hk => by
      have hsub_u : uIcc (gridPt u v Ms k) (gridPt u v Ms (k + 1)) ⊆ Icc u v := by
        rw [uIcc_of_le (gridPt_mono huv Ms (Nat.le_succ k))]
        exact gridPt_Icc_subset huv hMs_pos hk
      exact (hci_cont_a.mono hsub_u).intervalIntegrable
  rw [gridPt_zero, gridPt_end u v hMs_pos] at hgrid
  rw [← hgrid, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hle := gridPt_mono huv Ms (Nat.le_succ k.1)
  rw [← intervalIntegral.integral_finsetSum]
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hle] at ht
    unfold circleIntegrand
    rw [(B (θk k)).hroots a (B (θk k)).ha₀_U t (hθk_ball k ht), Multiset.map_map]
    change ∑ j : Fin n, ‖(monicPoly n a).derivative.eval (γs k j t)‖⁻¹ = ∑ j : Fin n, ‖γs' k j t‖
    exact Finset.sum_congr rfl fun j _ => (hγs_der k j t ht).2.2.symm
  · intro j _
    have hsub_u : uIcc (gridPt u v Ms k.1) (gridPt u v Ms (k.1 + 1)) ⊆
        Icc (gridPt u v Ms k.1) (gridPt u v Ms (k.1 + 1)) := by rw [uIcc_of_le hle]
    exact ((hγs'_cont k j).norm.mono hsub_u).intervalIntegrable

/-- Universal ball-cover projection bound on a finite collection of pairwise-disjoint regular
compact intervals `Icc (u s) (v s) ⊆ Ioo 0 (2π)`. -/
private lemma regular_Icc_finset_ball_bound {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℂ)
    {m : ℕ} {u v : Fin m → ℝ}
    (huv : ∀ s, u s ≤ v s)
    (hsub : ∀ s, Icc (u s) (v s) ⊆ Ioo (0 : ℝ) (2 * Real.pi))
    (hdisj_uv : Pairwise (Function.onFun Disjoint fun s : Fin m => Ioo (u s) (v s)))
    (hreg : ∀ s, ∀ θ ∈ Icc (u s) (v s), Complex.exp ((θ : ℂ) * Complex.I) ∉ critVals (monicPoly n a))
    {Z : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hcov_ball : ∀ s, ∀ z ∈ arcSet (monicPoly n a) (Icc (u s) (v s)), ∃ i : Fin n, ‖z - Z i‖ ≤ r) :
    ∑ s : Fin m, ∫ θ in (u s)..(v s), circleIntegrand (monicPoly n a) θ ≤ 8 * (n : ℝ) ^ 2 * r := by
  choose Ms γs γs' hMs_pos hγs_der hγs'_cont hγs_inj hγs_sum using
    fun s : Fin m => regular_Icc_grid_branches hn a (huv s) (hreg s)
  -- Assemble all branches into one Fintype ι = (s : Fin m) × (Fin (Ms s) × Fin n)
  let ι := (s : Fin m) × (Fin (Ms s) × Fin n)
  let lo : ι → ℝ := fun idx => gridPt (u idx.1) (v idx.1) (Ms idx.1) idx.2.1.1
  let hi : ι → ℝ := fun idx => gridPt (u idx.1) (v idx.1) (Ms idx.1) (idx.2.1.1 + 1)
  let Γ : ι → ℝ → ℂ := fun idx => γs idx.1 idx.2.1 idx.2.2
  let Γ' : ι → ℝ → ℂ := fun idx => γs' idx.1 idx.2.1 idx.2.2
  have hlohi : ∀ idx : ι, lo idx ≤ hi idx := fun idx => gridPt_mono (huv idx.1) (Ms idx.1) (Nat.le_succ _)
  -- Global injectivity of (idx, t) ↦ Γ idx t on open intervals Ioo (lo idx) (hi idx)
  have hΓ_inj : ∀ idx₁ idx₂ : ι, ∀ t₁ ∈ Ioo (lo idx₁) (hi idx₁), ∀ t₂ ∈ Ioo (lo idx₂) (hi idx₂),
      Γ idx₁ t₁ = Γ idx₂ t₂ → idx₁ = idx₂ ∧ t₁ = t₂ := by
    intro ⟨s₁, k₁, j₁⟩ ⟨s₂, k₂, j₂⟩ t₁ ht₁ t₂ ht₂ heq
    have h1 := (hγs_der s₁ k₁ j₁ t₁ (Ioo_subset_Icc_self ht₁)).2.1
    have h2 := (hγs_der s₂ k₂ j₂ t₂ (Ioo_subset_Icc_self ht₂)).2.1
    have ht1_Ioo : t₁ ∈ Ioo (u s₁) (v s₁) := gridPt_Ioo_subset (huv s₁) (hMs_pos s₁) k₁.isLt ht₁
    have ht2_Ioo : t₂ ∈ Ioo (u s₂) (v s₂) := gridPt_Ioo_subset (huv s₂) (hMs_pos s₂) k₂.isLt ht₂
    dsimp only [Γ] at heq
    rw [heq] at h1
    have ht_eq : t₁ = t₂ := exp_mul_I_injOn_Ioo (hsub s₁ (Ioo_subset_Icc_self ht1_Ioo))
      (hsub s₂ (Ioo_subset_Icc_self ht2_Ioo)) (h1.symm.trans h2)
    subst ht_eq
    have hs_eq : s₁ = s₂ := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj_uv hne) ht1_Ioo ht2_Ioo
    subst hs_eq
    have hk_eq : k₁ = k₂ := by
      ext
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := gridPt_mono (huv s₁) (Ms s₁) (show k₁.1 + 1 ≤ k₂.1 by omega)
        linarith [ht₁.2, ht₂.1]
      · have := gridPt_mono (huv s₁) (Ms s₁) (show k₂.1 + 1 ≤ k₁.1 by omega)
        linarith [ht₂.2, ht₁.1]
    subst hk_eq
    have hj_eq : j₁ = j₂ := hγs_inj s₁ k₁ t₁ (Ioo_subset_Icc_self ht₁) heq
    subst hj_eq
    exact ⟨rfl, rfl⟩
  have hΓ_lem : ∀ idx : ι, ∀ t ∈ Ioo (lo idx) (hi idx), Γ idx t ∈ Erdos114.lemniscate (monicPoly n a) := by
    intro idx t ht
    change ‖(monicPoly n a).eval (Γ idx t)‖ = 1
    rw [(hγs_der idx.1 idx.2.1 idx.2.2 t (Ioo_subset_Icc_self ht)).2.1, Complex.norm_exp_ofReal_mul_I]
  have hΓ_arc : ∀ idx : ι, ∀ t ∈ Ioo (lo idx) (hi idx),
      Γ idx t ∈ arcSet (monicPoly n a) (Icc (u idx.1) (v idx.1)) := by
    intro idx t ht
    exact ⟨t, gridPt_Icc_subset (huv idx.1) (hMs_pos idx.1) idx.2.1.isLt (Ioo_subset_Icc_self ht),
      (hγs_der idx.1 idx.2.1 idx.2.2 t (Ioo_subset_Icc_self ht)).2.1⟩
  -- Bound Re projection sum
  let Ure : Set ℝ := ⋃ i : Fin n, Icc ((Z i).re - r) ((Z i).re + r)
  have hUre_meas : MeasurableSet Ure := MeasurableSet.iUnion fun _ => measurableSet_Icc
  have hUre_vol : volume Ure ≤ ENNReal.ofReal (2 * (n : ℝ) * r) := by
    calc volume Ure
        ≤ ∑ i : Fin n, volume (Icc ((Z i).re - r) ((Z i).re + r)) := measure_iUnion_fintype_le _ _
      _ = ∑ _i : Fin n, ENNReal.ofReal (2 * r) := by
          refine Finset.sum_congr rfl fun i _ => by rw [Real.volume_Icc]; congr 1; ring
      _ = ENNReal.ofReal (2 * (n : ℝ) * r) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
          congr 1; ring
  have hre_bound : ∑ idx : ι, ∫ t in (lo idx)..(hi idx), |(Γ' idx t).re| ≤ 4 * (n : ℝ) ^ 2 * r := by
    have h1 := sum_integral_abs_deriv_le (ι := ι) hlohi
      (f := fun idx t => (Γ idx t).re) (f' := fun idx t => (Γ' idx t).re)
      (fun idx t ht => Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hγs_der idx.1 idx.2.1 idx.2.2 t ht).1)
      (fun idx => Complex.continuous_re.comp_continuousOn (hγs'_cont idx.1 idx.2.1 idx.2.2))
      hUre_meas (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hUre_vol) (M := 2 * n)
      (fun idx t ht => by
        obtain ⟨i, hi_r⟩ := hcov_ball idx.1 (Γ idx t) (hΓ_arc idx t ht)
        refine mem_iUnion.mpr ⟨i, ?_⟩
        have habs : |(Γ idx t).re - (Z i).re| ≤ r :=
          (Complex.abs_re_le_norm (Γ idx t - Z i)).trans hi_r
        rw [abs_le] at habs
        exact ⟨by linarith, by linarith⟩)
      (fun x _ => by
        obtain ⟨F, hF_card, hF_sub⟩ := lemniscate_inter_re_subset_finset hn
          (monicPoly_monic n a) (monicPoly_natDegree n a) x
        classical
        let P (z : ℂ) : Prop := ∃ p : ι × ℝ, p.2 ∈ Ioo (lo p.1) (hi p.1) ∧ Γ p.1 p.2 = z
        by_cases hP_ne : ∃ z ∈ F, P z
        · obtain ⟨z₀, _, hz₀⟩ := hP_ne
          let lift' : ℂ → ι × ℝ := fun z => if h : P z then h.choose else hz₀.choose
          refine ⟨F.image lift', Finset.card_image_le.trans hF_card, fun idx t ht htx => ?_⟩
          have hz_mem : Γ idx t ∈ F := hF_sub ⟨hΓ_lem idx t ht, htx⟩
          have hPz : P (Γ idx t) := ⟨(idx, t), ht, rfl⟩
          have heq_p : lift' (Γ idx t) = (idx, t) := by
            dsimp only [lift']; rw [dif_pos hPz]
            have hspec := hPz.choose_spec
            have huniq := hΓ_inj hPz.choose.1 idx hPz.choose.2 hspec.1 t ht hspec.2
            exact Prod.ext huniq.1 huniq.2
          exact Finset.mem_image.mpr ⟨Γ idx t, hz_mem, heq_p⟩
        · refine ⟨∅, by simp, fun idx t ht htx => ?_⟩
          have hz_mem : Γ idx t ∈ F := hF_sub ⟨hΓ_lem idx t ht, htx⟩
          exfalso; exact hP_ne ⟨Γ idx t, hz_mem, ⟨(idx, t), ht, rfl⟩⟩)
    have hvol_tr : (volume Ure).toReal ≤ 2 * (n : ℝ) * r := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hUre_vol
      rwa [ENNReal.toReal_ofReal (by positivity)] at h
    calc ∑ idx : ι, ∫ t in (lo idx)..(hi idx), |(Γ' idx t).re|
        ≤ ((2 * n : ℕ) : ℝ) * (volume Ure).toReal := h1
      _ ≤ ((2 * n : ℕ) : ℝ) * (2 * (n : ℝ) * r) := mul_le_mul_of_nonneg_left hvol_tr (Nat.cast_nonneg _)
      _ = 4 * (n : ℝ) ^ 2 * r := by push_cast; ring
  -- Bound Im projection sum identically
  let Uim : Set ℝ := ⋃ i : Fin n, Icc ((Z i).im - r) ((Z i).im + r)
  have hUim_meas : MeasurableSet Uim := MeasurableSet.iUnion fun _ => measurableSet_Icc
  have hUim_vol : volume Uim ≤ ENNReal.ofReal (2 * (n : ℝ) * r) := by
    calc volume Uim
        ≤ ∑ i : Fin n, volume (Icc ((Z i).im - r) ((Z i).im + r)) := measure_iUnion_fintype_le _ _
      _ = ∑ _i : Fin n, ENNReal.ofReal (2 * r) := by
          refine Finset.sum_congr rfl fun i _ => by rw [Real.volume_Icc]; congr 1; ring
      _ = ENNReal.ofReal (2 * (n : ℝ) * r) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
          congr 1; ring
  have him_bound : ∑ idx : ι, ∫ t in (lo idx)..(hi idx), |(Γ' idx t).im| ≤ 4 * (n : ℝ) ^ 2 * r := by
    have h1 := sum_integral_abs_deriv_le (ι := ι) hlohi
      (f := fun idx t => (Γ idx t).im) (f' := fun idx t => (Γ' idx t).im)
      (fun idx t ht => Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hγs_der idx.1 idx.2.1 idx.2.2 t ht).1)
      (fun idx => Complex.continuous_im.comp_continuousOn (hγs'_cont idx.1 idx.2.1 idx.2.2))
      hUim_meas (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hUim_vol) (M := 2 * n)
      (fun idx t ht => by
        obtain ⟨i, hi_r⟩ := hcov_ball idx.1 (Γ idx t) (hΓ_arc idx t ht)
        refine mem_iUnion.mpr ⟨i, ?_⟩
        have habs : |(Γ idx t).im - (Z i).im| ≤ r :=
          (Complex.abs_im_le_norm (Γ idx t - Z i)).trans hi_r
        rw [abs_le] at habs
        exact ⟨by linarith, by linarith⟩)
      (fun y _ => by
        obtain ⟨F, hF_card, hF_sub⟩ := lemniscate_inter_im_subset_finset hn
          (monicPoly_monic n a) (monicPoly_natDegree n a) y
        classical
        let P (z : ℂ) : Prop := ∃ p : ι × ℝ, p.2 ∈ Ioo (lo p.1) (hi p.1) ∧ Γ p.1 p.2 = z
        by_cases hP_ne : ∃ z ∈ F, P z
        · obtain ⟨z₀, _, hz₀⟩ := hP_ne
          let lift' : ℂ → ι × ℝ := fun z => if h : P z then h.choose else hz₀.choose
          refine ⟨F.image lift', Finset.card_image_le.trans hF_card, fun idx t ht hty => ?_⟩
          have hz_mem : Γ idx t ∈ F := hF_sub ⟨hΓ_lem idx t ht, hty⟩
          have hPz : P (Γ idx t) := ⟨(idx, t), ht, rfl⟩
          have heq_p : lift' (Γ idx t) = (idx, t) := by
            dsimp only [lift']; rw [dif_pos hPz]
            have hspec := hPz.choose_spec
            have huniq := hΓ_inj hPz.choose.1 idx hPz.choose.2 hspec.1 t ht hspec.2
            exact Prod.ext huniq.1 huniq.2
          exact Finset.mem_image.mpr ⟨Γ idx t, hz_mem, heq_p⟩
        · refine ⟨∅, by simp, fun idx t ht hty => ?_⟩
          have hz_mem : Γ idx t ∈ F := hF_sub ⟨hΓ_lem idx t ht, hty⟩
          exfalso; exact hP_ne ⟨Γ idx t, hz_mem, ⟨(idx, t), ht, rfl⟩⟩)
    have hvol_tr : (volume Uim).toReal ≤ 2 * (n : ℝ) * r := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hUim_vol
      rwa [ENNReal.toReal_ofReal (by positivity)] at h
    calc ∑ idx : ι, ∫ t in (lo idx)..(hi idx), |(Γ' idx t).im|
        ≤ ((2 * n : ℕ) : ℝ) * (volume Uim).toReal := h1
      _ ≤ ((2 * n : ℕ) : ℝ) * (2 * (n : ℝ) * r) := mul_le_mul_of_nonneg_left hvol_tr (Nat.cast_nonneg _)
      _ = 4 * (n : ℝ) ^ 2 * r := by push_cast; ring
  -- Combine via ‖w‖ ≤ |w.re| + |w.im|
  have hsum_eq : ∑ s : Fin m, ∫ θ in (u s)..(v s), circleIntegrand (monicPoly n a) θ =
      ∑ idx : ι, ∫ t in (lo idx)..(hi idx), ‖Γ' idx t‖ := by
    rw [Finset.sum_congr rfl fun s _ => hγs_sum s]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Fintype.sum_prod_type]
  rw [hsum_eq]
  have hnorm_le : ∀ idx : ι,
      ∫ t in (lo idx)..(hi idx), ‖Γ' idx t‖ ≤
        (∫ t in (lo idx)..(hi idx), |(Γ' idx t).re|) + (∫ t in (lo idx)..(hi idx), |(Γ' idx t).im|) := by
    intro idx
    have hsub_u : uIcc (lo idx) (hi idx) ⊆ Icc (lo idx) (hi idx) := by rw [uIcc_of_le (hlohi idx)]
    have hcont := hγs'_cont idx.1 idx.2.1 idx.2.2
    have hi_norm : IntervalIntegrable (fun t => ‖Γ' idx t‖) volume (lo idx) (hi idx) :=
      (hcont.norm.mono hsub_u).intervalIntegrable
    have hi_re : IntervalIntegrable (fun t => |(Γ' idx t).re|) volume (lo idx) (hi idx) :=
      (((Complex.continuous_re.comp_continuousOn hcont).abs).mono hsub_u).intervalIntegrable
    have hi_im : IntervalIntegrable (fun t => |(Γ' idx t).im|) volume (lo idx) (hi idx) :=
      (((Complex.continuous_im.comp_continuousOn hcont).abs).mono hsub_u).intervalIntegrable
    rw [← intervalIntegral.integral_add hi_re hi_im]
    exact intervalIntegral.integral_mono_on (hlohi idx) hi_norm (hi_re.add hi_im) fun t _ =>
      Complex.norm_le_abs_re_add_abs_im (Γ' idx t)
  calc ∑ idx : ι, ∫ t in (lo idx)..(hi idx), ‖Γ' idx t‖
      ≤ ∑ idx : ι, ((∫ t in (lo idx)..(hi idx), |(Γ' idx t).re|) +
          (∫ t in (lo idx)..(hi idx), |(Γ' idx t).im|)) := Finset.sum_le_sum fun idx _ => hnorm_le idx
    _ = (∑ idx : ι, ∫ t in (lo idx)..(hi idx), |(Γ' idx t).re|) +
          (∑ idx : ι, ∫ t in (lo idx)..(hi idx), |(Γ' idx t).im|) := Finset.sum_add_distrib
    _ ≤ 4 * (n : ℝ) ^ 2 * r + 4 * (n : ℝ) ^ 2 * r := add_le_add hre_bound him_bound
    _ = 8 * (n : ℝ) ^ 2 * r := by ring

private lemma ofReal_multiset_sum_of_nonneg {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) :
    ENNReal.ofReal s.sum = (s.map ENNReal.ofReal).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    have ha : 0 ≤ a := hs a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
      ENNReal.ofReal_add ha (Multiset.sum_nonneg ht), ih ht]

private lemma circleIntegrandENN_eq_ofReal_of_reg {p : ℂ[X]} {θ : ℝ}
    (hreg : Complex.exp ((θ : ℂ) * Complex.I) ∉ critVals p) (hp_ne : p - C (Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0) :
    circleIntegrandENN p θ = ENNReal.ofReal (circleIntegrand p θ) := by
  unfold circleIntegrandENN circleIntegrand
  rw [ofReal_multiset_sum_of_nonneg]
  · congr 1
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun z hz => ?_
    have hev : p.eval z = Complex.exp ((θ : ℂ) * Complex.I) := by
      have := (Polynomial.mem_roots hp_ne).mp hz
      simpa [sub_eq_zero] using this
    have hd_ne : p.derivative.eval z ≠ 0 := fun h0 => hreg ⟨z, h0, hev⟩
    exact (ENNReal.ofReal_inv_of_pos (norm_pos_iff.mpr hd_ne)).symm
  · intro x hx
    rcases Multiset.mem_map.mp hx with ⟨_, _, rfl⟩
    exact inv_nonneg.mpr (norm_nonneg _)

/-- On a single regular open interval `(c, d) ⊆ (0, 2π)` avoiding `critVals p`,
the Hausdorff measure of `arcSet p (Ioo c d)` equals the `lintegral` of `circleIntegrandENN p`. -/
private lemma arcSet_measure_regular_Ioo_eq_lintegral {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]}
    (hp : p.Monic) (hdeg : p.natDegree = n) {c d : ℝ} (hcd : c < d)
    (hsub : Ioo c d ⊆ Ioo (0 : ℝ) (2 * Real.pi))
    (hreg : ∀ θ ∈ Ioo c d, Complex.exp ((θ : ℂ) * Complex.I) ∉ critVals p) :
    (μH[1] : Measure ℂ) (arcSet p (Ioo c d)) = ∫⁻ θ in Ioo c d, circleIntegrandENN p θ := by
  let a : Fin n → ℂ := fun j => p.coeff (j : ℕ)
  have hp_eq : p = monicPoly n a := eq_monicPoly_of_monic hp hdeg
  let u : ℕ → ℝ := fun k => c + (d - c) / ((k : ℝ) + 3)
  let v : ℕ → ℝ := fun k => d - (d - c) / ((k : ℝ) + 3)
  have huv_lt : ∀ k : ℕ, u k < v k := by
    intro k
    have hk : (3 : ℝ) ≤ (k : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hstep : (d - c) / ((k : ℝ) + 3) ≤ (d - c) / 3 :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr (le_of_lt hcd)) (by norm_num) hk
    dsimp only [u, v]; linarith
  have hJ_sub : ∀ k : ℕ, Icc (u k) (v k) ⊆ Ioo c d := by
    intro k θ hθ
    have hstep : 0 < (d - c) / ((k : ℝ) + 3) := div_pos (sub_pos.mpr hcd) (by positivity)
    exact ⟨lt_of_lt_of_le (by dsimp only [u]; linarith) hθ.1,
      lt_of_le_of_lt hθ.2 (by dsimp only [v]; linarith)⟩
  have hJ_mono : Monotone (fun k : ℕ => Icc (u k) (v k)) := by
    intro i j hij θ hθ
    have hle : (d - c) / ((j : ℝ) + 3) ≤ (d - c) / ((i : ℝ) + 3) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr (le_of_lt hcd)) (by positivity) (by gcongr)
    exact ⟨(by dsimp only [u]; linarith : u j ≤ u i).trans hθ.1,
      hθ.2.trans (by dsimp only [v]; linarith : v i ≤ v j)⟩
  have hJ_union : (⋃ k : ℕ, Icc (u k) (v k)) = Ioo c d := by
    ext θ
    simp only [mem_iUnion, mem_Icc, mem_Ioo]
    constructor
    · rintro ⟨k, hk⟩; exact hJ_sub k hk
    · rintro ⟨hcθ, hθd⟩
      let δ := min (θ - c) (d - θ)
      have hδ_pos : 0 < δ := lt_min (sub_pos.mpr hcθ) (sub_pos.mpr hθd)
      obtain ⟨k, hk⟩ := exists_nat_gt ((d - c) / δ)
      refine ⟨k, ?_, ?_⟩
      · have h1 : (d - c) / ((k : ℝ) + 3) < δ := by
          rw [div_lt_iff₀ (by positivity)]
          have h2 := (div_lt_iff₀ hδ_pos).mp hk
          nlinarith
        have : δ ≤ θ - c := min_le_left _ _
        dsimp only [u]; linarith
      · have h1 : (d - c) / ((k : ℝ) + 3) < δ := by
          rw [div_lt_iff₀ (by positivity)]
          have h2 := (div_lt_iff₀ hδ_pos).mp hk
          nlinarith
        have : δ ≤ d - θ := min_le_right _ _
        dsimp only [v]; linarith
  have harc_union : arcSet p (Ioo c d) = ⋃ k : ℕ, arcSet p (Icc (u k) (v k)) := by
    ext z; simp only [arcSet, mem_iUnion, mem_ofPred_eq, ← hJ_union]; tauto
  have harc_mono : Monotone (fun k : ℕ => arcSet p (Icc (u k) (v k))) :=
    fun i j hij z ⟨θ, hθ, hz⟩ => ⟨θ, hJ_mono hij hθ, hz⟩
  have hstep_and_cont : ∀ k : ℕ,
      ContinuousOn (circleIntegrand p) (Icc (u k) (v k)) ∧
      (μH[1] : Measure ℂ) (arcSet p (Icc (u k) (v k))) =
        ∫⁻ θ in Icc (u k) (v k), circleIntegrandENN p θ := by
    intro k
    obtain ⟨U, _, ha_U, hci_cont, _, hmeas⟩ := regular_Icc_measure_and_continuity hn a
      (le_of_lt (huv_lt k)) ((hJ_sub k).trans hsub)
      (fun θ hθ => by rw [← hp_eq]; exact hreg θ (hJ_sub k hθ))
    have hci_cont_p : ContinuousOn (circleIntegrand p) (Icc (u k) (v k)) := by
      rw [hp_eq]
      exact continuousOn_snd_of_prod (f := fun a' θ => circleIntegrand (monicPoly n a') θ) ha_U hci_cont
    refine ⟨hci_cont_p, ?_⟩
    rw [hp_eq, hmeas a ha_U, ← hp_eq]
    have hci_nn : ∀ θ, 0 ≤ circleIntegrand p θ := fun θ => by
      unfold circleIntegrand
      exact Multiset.sum_nonneg fun x hx => by
        rcases Multiset.mem_map.mp hx with ⟨_, _, rfl⟩; exact inv_nonneg.mpr (norm_nonneg _)
    rw [intervalIntegral.integral_of_le (le_of_lt (huv_lt k)),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hci_cont_p.integrableOn_Icc)
        (Filter.Eventually.of_forall hci_nn)]
    refine setLIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    have hp_ne : p - C (Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := by
      have hd : (p - C (Complex.exp ((θ : ℂ) * Complex.I))).natDegree = n := by
        rw [Polynomial.natDegree_sub_C, hdeg]
      intro h0; rw [h0, Polynomial.natDegree_zero] at hd; omega
    exact (circleIntegrandENN_eq_ofReal_of_reg (hreg θ (hJ_sub k hθ)) hp_ne).symm
  have hmeas_ind : ∀ k : ℕ, AEMeasurable ((Icc (u k) (v k)).indicator (fun θ => ENNReal.ofReal (circleIntegrand p θ))) volume :=
    fun k => (aemeasurable_indicator_iff measurableSet_Icc).mpr
      ((ENNReal.continuous_ofReal.comp_continuousOn (hstep_and_cont k).1).aemeasurable measurableSet_Icc)
  have hlint_iSup : ∫⁻ θ in Ioo c d, circleIntegrandENN p θ =
      ⨆ k : ℕ, ∫⁻ θ in Icc (u k) (v k), circleIntegrandENN p θ := by
    have hmono_ind : ∀ θ : ℝ, Monotone (fun k : ℕ => (Icc (u k) (v k)).indicator (fun τ => ENNReal.ofReal (circleIntegrand p τ)) θ) := by
      intro θ i j hij
      dsimp only
      by_cases hθ : θ ∈ Icc (u i) (v i)
      · rw [indicator_of_mem hθ, indicator_of_mem (hJ_mono hij hθ)]
      · rw [indicator_of_notMem hθ]; exact zero_le
    have hpt_sup : ∀ θ : ℝ,
        (Ioo c d).indicator (circleIntegrandENN p) θ =
          ⨆ k : ℕ, (Icc (u k) (v k)).indicator (fun τ => ENNReal.ofReal (circleIntegrand p τ)) θ := by
      intro θ
      by_cases hθ : θ ∈ Ioo c d
      · rw [indicator_of_mem hθ]
        rw [← hJ_union] at hθ
        rcases mem_iUnion.mp hθ with ⟨k₀, hk₀⟩
        have hp_ne : p - C (Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := by
          have hd : (p - C (Complex.exp ((θ : ℂ) * Complex.I))).natDegree = n := by
            rw [Polynomial.natDegree_sub_C, hdeg]
          intro h0; rw [h0, Polynomial.natDegree_zero] at hd; omega
        have heq_enn := circleIntegrandENN_eq_ofReal_of_reg (hreg θ (hJ_sub k₀ hk₀)) hp_ne
        refine le_antisymm ?_ ?_
        · refine le_iSup_of_le k₀ ?_
          rw [indicator_of_mem hk₀, heq_enn]
        · refine iSup_le fun k => ?_
          by_cases hk : θ ∈ Icc (u k) (v k)
          · rw [indicator_of_mem hk, heq_enn]
          · rw [indicator_of_notMem hk]; exact zero_le
      · rw [indicator_of_notMem hθ]
        symm
        exact le_antisymm (iSup_le fun k => by rw [indicator_of_notMem (fun hk => hθ (hJ_sub k hk))]) zero_le
    rw [← lintegral_indicator measurableSet_Ioo]
    simp_rw [hpt_sup]
    rw [lintegral_iSup' hmeas_ind (Filter.Eventually.of_forall hmono_ind)]
    refine iSup_congr fun k => ?_
    rw [lintegral_indicator measurableSet_Icc]
    refine setLIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    have hp_ne : p - C (Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := by
      have hd : (p - C (Complex.exp ((θ : ℂ) * Complex.I))).natDegree = n := by
        rw [Polynomial.natDegree_sub_C, hdeg]
      intro h0; rw [h0, Polynomial.natDegree_zero] at hd; omega
    exact (circleIntegrandENN_eq_ofReal_of_reg (hreg θ (hJ_sub k hθ)) hp_ne).symm
  rw [harc_union, harc_mono.measure_iUnion, hlint_iSup]
  exact iSup_congr fun k => (hstep_and_cont k).2

/-- For any monic degree-`n` polynomial `p` and any open angle interval `(α, β) ⊆ (0, 2π)`
(even containing critical values!), the Hausdorff measure of `arcSet p (Ioo α β)` equals
the `lintegral` of `circleIntegrandENN p` on `(α, β)`. -/
theorem arcSet_measure_Ioo_eq_lintegral {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]}
    (hp : p.Monic) (hdeg : p.natDegree = n) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 2 * Real.pi) :
    (μH[1] : Measure ℂ) (arcSet p (Ioo α β)) = ∫⁻ θ in Ioo α β, circleIntegrandENN p θ := by
  by_cases hαβ : α < β
  · let Bset := {θ ∈ Ioo α β | Complex.exp ((θ : ℂ) * Complex.I) ∈ critVals p}
    have hB_fin : Bset.Finite := badAngles_finite hn hp hdeg hα hβ
    let B : Finset ℝ := hB_fin.toFinset
    have hB_sub : ∀ x ∈ B, x ∈ Ioo α β := fun x hx => (hB_fin.mem_toFinset.mp hx).1
    obtain ⟨m, c, hm, hc0, hcm, hinc, hdisjB, hunion⟩ :=
      partition_Ioo_diff_finset B.card α β B rfl hαβ hB_sub
    have hmono_c : ∀ i j, i ≤ j → j ≤ m → c i ≤ c j := by
      intro i j hij hjm
      induction hij with
      | refl => exact le_rfl
      | @step j' hij' ih' => exact (ih' (by omega)).trans (le_of_lt (hinc j' (by omega)))
    have hIoo_sub : ∀ s ∈ Finset.range m, Ioo (c s) (c (s + 1)) ⊆ Ioo (0 : ℝ) (2 * Real.pi) := by
      intro s hs θ hθ
      rw [Finset.mem_range] at hs
      have hlo : α ≤ c s := hc0 ▸ hmono_c 0 s (Nat.zero_le s) (by omega)
      have hhi : c (s + 1) ≤ β := hcm ▸ hmono_c (s + 1) m (by omega) le_rfl
      exact ⟨lt_of_le_of_lt (hα.trans hlo) hθ.1, lt_of_lt_of_le hθ.2 (hhi.trans hβ)⟩
    have hreg_s : ∀ s ∈ Finset.range m, ∀ θ ∈ Ioo (c s) (c (s + 1)),
        Complex.exp ((θ : ℂ) * Complex.I) ∉ critVals p := by
      intro s hs θ hθ hcrit
      rw [Finset.mem_range] at hs
      have hlo : α ≤ c s := hc0 ▸ hmono_c 0 s (Nat.zero_le s) (by omega)
      have hhi : c (s + 1) ≤ β := hcm ▸ hmono_c (s + 1) m (by omega) le_rfl
      have hmemB : θ ∈ B := hB_fin.mem_toFinset.mpr ⟨⟨lt_of_le_of_lt hlo hθ.1, lt_of_lt_of_le hθ.2 hhi⟩, hcrit⟩
      exact Set.disjoint_left.mp (hdisjB s hs) hθ (Finset.mem_coe.mpr hmemB)
    have hdisj_Ioo : PairwiseDisjoint (Finset.range m : Set ℕ) (fun s => Ioo (c s) (c (s + 1))) := by
      intro i hi j hj hij
      dsimp only [Function.onFun]
      rw [Set.disjoint_left]
      intro x hxi hxj
      rw [Finset.mem_coe, Finset.mem_range] at hi hj
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have := hmono_c (i + 1) j (by omega) (by omega); linarith [hxi.2, hxj.1]
      · have := hmono_c (j + 1) i (by omega) (by omega); linarith [hxj.2, hxi.1]
    have hdisj_arc : PairwiseDisjoint (Finset.range m : Set ℕ)
        (fun s => arcSet p (Ioo (c s) (c (s + 1)))) := by
      intro i hi j hj hij
      dsimp only [Function.onFun]
      rw [Set.disjoint_left]
      rintro z ⟨t₁, ht₁, h1⟩ ⟨t₂, ht₂, h2⟩
      have ht_eq : t₁ = t₂ := exp_mul_I_injOn_Ioo (hIoo_sub i hi ht₁) (hIoo_sub j hj ht₂) (h1.symm.trans h2)
      subst ht_eq
      exact Set.disjoint_left.mp (hdisj_Ioo hi hj hij) ht₁ ht₂
    have hmeas_arc : ∀ s ∈ Finset.range m, MeasurableSet (arcSet p (Ioo (c s) (c (s + 1)))) := by
      intro s hs
      have hcont_exp : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) :=
        Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
      have hpre : arcSet p (Ioo (c s) (c (s + 1))) =
          (fun z => p.eval z) ⁻¹' ((fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) '' Ioo (c s) (c (s + 1))) := by
        ext z; simp [arcSet, eq_comm]
      rw [hpre]
      have hlt_s : c s < c (s + 1) := hinc s (Finset.mem_range.mp hs)
      -- Express Ioo as countable union of Icc so image is F_sigma (measurable!)
      let u : ℕ → ℝ := fun k => c s + (c (s + 1) - c s) / ((k : ℝ) + 3)
      let v : ℕ → ℝ := fun k => c (s + 1) - (c (s + 1) - c s) / ((k : ℝ) + 3)
      have hJ_u : (⋃ k : ℕ, Icc (u k) (v k)) = Ioo (c s) (c (s + 1)) := by
        ext θ
        simp only [mem_iUnion, mem_Icc, mem_Ioo]
        constructor
        · rintro ⟨k, hk1, hk2⟩
          have hstep : 0 < (c (s + 1) - c s) / ((k : ℝ) + 3) := div_pos (sub_pos.mpr hlt_s) (by positivity)
          exact ⟨lt_of_lt_of_le (by dsimp only [u]; linarith) hk1,
            lt_of_le_of_lt hk2 (by dsimp only [v]; linarith)⟩
        · rintro ⟨h1, h2⟩
          let δ := min (θ - c s) (c (s + 1) - θ)
          have hδ : 0 < δ := lt_min (sub_pos.mpr h1) (sub_pos.mpr h2)
          obtain ⟨k, hk⟩ := exists_nat_gt ((c (s + 1) - c s) / δ)
          have hstep : (c (s + 1) - c s) / ((k : ℝ) + 3) < δ := by
            rw [div_lt_iff₀ (by positivity)]
            have := (div_lt_iff₀ hδ).mp hk
            nlinarith
          exact ⟨k, by dsimp only [u]; linarith [min_le_left (θ - c s) (c (s + 1) - θ)],
            by dsimp only [v]; linarith [min_le_right (θ - c s) (c (s + 1) - θ)]⟩
      have himg_u : ((fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) '' Ioo (c s) (c (s + 1))) =
          ⋃ k : ℕ, ((fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) '' Icc (u k) (v k)) := by
        rw [← hJ_u, image_iUnion]
      have hmeas_img : MeasurableSet ((fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) '' Ioo (c s) (c (s + 1))) := by
        rw [himg_u]
        exact MeasurableSet.iUnion fun k => (isCompact_Icc.image hcont_exp).measurableSet
      exact hmeas_img.preimage p.continuous.measurable
    -- Split μH[1] (arcSet p (Ioo α β))
    have hE_zero : (μH[1] : Measure ℂ) (arcSet p (B : Set ℝ)) = 0 := by
      refine hausdorffMeasure_one_finite_eq_zero ?_
      have hsubE : arcSet p (B : Set ℝ) ⊆ {z | p.eval z ∈ (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) '' (B : Set ℝ)} := by
        rintro z ⟨t, ht, hz⟩; exact ⟨t, ht, hz.symm⟩
      exact (finite_preimage_eval hn hp hdeg (B.finite_toSet.image _)).subset hsubE
    have harc_lhs : (μH[1] : Measure ℂ) (arcSet p (Ioo α β)) =
        ∑ s ∈ Finset.range m, (μH[1] : Measure ℂ) (arcSet p (Ioo (c s) (c (s + 1)))) := by
      have hunion_arc : arcSet p (Ioo α β) ⊆
          (⋃ s ∈ Finset.range m, arcSet p (Ioo (c s) (c (s + 1)))) ∪ arcSet p (B : Set ℝ) := by
        rintro z ⟨t, ht, hz⟩
        by_cases htB : t ∈ (B : Set ℝ)
        · exact Or.inr ⟨t, htB, hz⟩
        · have ht' : t ∈ Ioo α β \ (B : Set ℝ) := ⟨ht, htB⟩
          rw [hunion] at ht'
          rcases mem_iUnion₂.mp ht' with ⟨s, hs, hts⟩
          exact Or.inl (mem_iUnion₂.mpr ⟨s, hs, ⟨t, hts, hz⟩⟩)
      have hrev_arc : (⋃ s ∈ Finset.range m, arcSet p (Ioo (c s) (c (s + 1)))) ⊆ arcSet p (Ioo α β) :=
        iUnion₂_subset fun s hs z ⟨t, ht, hz⟩ => by
          have ht' : t ∈ Ioo α β \ (B : Set ℝ) := by
            rw [hunion]; exact mem_iUnion₂.mpr ⟨s, hs, ht⟩
          exact ⟨t, ht'.1, hz⟩
      have heq_u : (μH[1] : Measure ℂ) (arcSet p (Ioo α β)) =
          (μH[1] : Measure ℂ) (⋃ s ∈ Finset.range m, arcSet p (Ioo (c s) (c (s + 1)))) := by
        refine le_antisymm ?_ (measure_mono hrev_arc)
        calc (μH[1] : Measure ℂ) (arcSet p (Ioo α β))
            ≤ (μH[1] : Measure ℂ) ((⋃ s ∈ Finset.range m, arcSet p (Ioo (c s) (c (s + 1)))) ∪ arcSet p (B : Set ℝ)) :=
              measure_mono hunion_arc
          _ ≤ (μH[1] : Measure ℂ) (⋃ s ∈ Finset.range m, arcSet p (Ioo (c s) (c (s + 1)))) +
                (μH[1] : Measure ℂ) (arcSet p (B : Set ℝ)) := measure_union_le _ _
          _ = _ := by rw [hE_zero, add_zero]
      rw [heq_u, measure_biUnion_finset hdisj_arc hmeas_arc]
    -- Split lintegral on Ioo α β
    have hlint_rhs : ∫⁻ θ in Ioo α β, circleIntegrandENN p θ =
        ∑ s ∈ Finset.range m, ∫⁻ θ in Ioo (c s) (c (s + 1)), circleIntegrandENN p θ := by
      have hae : (Ioo α β \ (B : Set ℝ) : Set ℝ) =ᵐ[volume] Ioo α β := by
        rw [MeasureTheory.ae_eq_set]
        refine ⟨by simp, measure_mono_null (fun x hx => by by_contra h; exact hx.2 ⟨hx.1, h⟩)
          (B.finite_toSet.measure_zero volume)⟩
      rw [← setLIntegral_congr hae, hunion, lintegral_biUnion_finset hdisj_Ioo (fun _ _ => measurableSet_Ioo)]
    rw [harc_lhs, hlint_rhs]
    refine Finset.sum_congr rfl fun s hs =>
      arcSet_measure_regular_Ioo_eq_lintegral hn hp hdeg (hinc s (Finset.mem_range.mp hs))
        (hIoo_sub s hs) (hreg_s s hs)
  · have hemp : Ioo α β = ∅ := Ioo_eq_empty hαβ
    simp [hemp, arcSet]

/-- Universal ball-cover projection bound for ANY open interval `(α, β) ⊆ (0, 2π)` (even containing
critical values of `p`): if `arcSet p (Ioo α β)` is covered by `n` closed balls of radius `r`,
then its 1D Hausdorff measure is at most `8 * n^2 * r`. -/
theorem arcSet_measure_Ioo_le_of_ball_cover {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]}
    (hp : p.Monic) (hdeg : p.natDegree = n) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 2 * Real.pi)
    {Z : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hcov : ∀ z ∈ arcSet p (Ioo α β), ∃ i : Fin n, ‖z - Z i‖ ≤ r) :
    (μH[1] : Measure ℂ) (arcSet p (Ioo α β)) ≤ ENNReal.ofReal (8 * (n : ℝ) ^ 2 * r) := by
  by_cases hαβ : α < β
  · let a : Fin n → ℂ := fun j => p.coeff (j : ℕ)
    have hp_eq : p = monicPoly n a := eq_monicPoly_of_monic hp hdeg
    let Bset := {θ ∈ Ioo α β | Complex.exp ((θ : ℂ) * Complex.I) ∈ critVals p}
    have hB_fin : Bset.Finite := badAngles_finite hn hp hdeg hα hβ
    let B : Finset ℝ := hB_fin.toFinset
    have hB_sub : ∀ x ∈ B, x ∈ Ioo α β := fun x hx => (hB_fin.mem_toFinset.mp hx).1
    obtain ⟨m, c, hm, hc0, hcm, hinc, hdisjB, hunion⟩ :=
      partition_Ioo_diff_finset B.card α β B rfl hαβ hB_sub
    have hmono_c : ∀ i j, i ≤ j → j ≤ m → c i ≤ c j := by
      intro i j hij hjm
      induction hij with
      | refl => exact le_rfl
      | @step j' hij' ih' => exact (ih' (by omega)).trans (le_of_lt (hinc j' (by omega)))
    have hIoo_sub : ∀ s : Fin m, Ioo (c s.1) (c (s.1 + 1)) ⊆ Ioo α β := by
      intro s θ hθ
      have hlo : α ≤ c s.1 := hc0 ▸ hmono_c 0 s.1 (Nat.zero_le s.1) (by omega)
      have hhi : c (s.1 + 1) ≤ β := hcm ▸ hmono_c (s.1 + 1) m (by omega) le_rfl
      exact ⟨lt_of_le_of_lt hlo hθ.1, lt_of_lt_of_le hθ.2 hhi⟩
    have hreg_s : ∀ s : Fin m, ∀ θ ∈ Ioo (c s.1) (c (s.1 + 1)),
        Complex.exp ((θ : ℂ) * Complex.I) ∉ critVals p := by
      intro s θ hθ hcrit
      have hmemB : θ ∈ B := hB_fin.mem_toFinset.mpr ⟨hIoo_sub s hθ, hcrit⟩
      exact Set.disjoint_left.mp (hdisjB s.1 s.isLt) hθ (Finset.mem_coe.mpr hmemB)
    -- Shrunk compact intervals u_k s, v_k s inside Ioo (c s) (c (s + 1))
    let uk : ℕ → Fin m → ℝ := fun k s => c s.1 + (c (s.1 + 1) - c s.1) / ((k : ℝ) + 3)
    let vk : ℕ → Fin m → ℝ := fun k s => c (s.1 + 1) - (c (s.1 + 1) - c s.1) / ((k : ℝ) + 3)
    have huk_lt : ∀ k s, uk k s < vk k s := by
      intro k s
      have hcd := hinc s.1 s.isLt
      have hk3 : (3 : ℝ) ≤ (k : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have hstep : (c (s.1 + 1) - c s.1) / ((k : ℝ) + 3) ≤ (c (s.1 + 1) - c s.1) / 3 :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr (le_of_lt hcd)) (by norm_num) hk3
      dsimp only [uk, vk]; linarith
    have hJ_sub : ∀ k s, Icc (uk k s) (vk k s) ⊆ Ioo (c s.1) (c (s.1 + 1)) := by
      intro k s θ hθ
      have hstep : 0 < (c (s.1 + 1) - c s.1) / ((k : ℝ) + 3) :=
        div_pos (sub_pos.mpr (hinc s.1 s.isLt)) (by positivity)
      exact ⟨lt_of_lt_of_le (by dsimp only [uk]; linarith) hθ.1,
        lt_of_le_of_lt hθ.2 (by dsimp only [vk]; linarith)⟩
    have hk_bound : ∀ k : ℕ,
        ∑ s : Fin m, (μH[1] : Measure ℂ) (arcSet p (Icc (uk k s) (vk k s))) ≤
          ENNReal.ofReal (8 * (n : ℝ) ^ 2 * r) := by
      intro k
      have hterm : ∀ s : Fin m,
          (μH[1] : Measure ℂ) (arcSet p (Icc (uk k s) (vk k s))) =
            ENNReal.ofReal (∫ θ in (uk k s)..(vk k s), circleIntegrand (monicPoly n a) θ) := by
        intro s
        have hIoo_02 : Ioo (c s.1) (c (s.1 + 1)) ⊆ Ioo (0 : ℝ) (2 * Real.pi) := fun θ hθ =>
          ⟨lt_of_le_of_lt hα (hIoo_sub s hθ).1, lt_of_lt_of_le (hIoo_sub s hθ).2 hβ⟩
        obtain ⟨U, _, ha_U, _, _, hmeas⟩ := regular_Icc_measure_and_continuity hn a
          (le_of_lt (huk_lt k s)) ((hJ_sub k s).trans hIoo_02)
          (fun θ hθ => by rw [← hp_eq]; exact hreg_s s θ (hJ_sub k s hθ))
        rw [hp_eq, hmeas a ha_U]
      rw [Finset.sum_congr rfl fun s _ => hterm s,
        ← ENNReal.ofReal_sum_of_nonneg (fun s _ =>
          intervalIntegral.integral_nonneg (le_of_lt (huk_lt k s)) fun θ _ => by
            unfold circleIntegrand
            exact Multiset.sum_nonneg fun x hx => by
              rcases Multiset.mem_map.mp hx with ⟨_, _, rfl⟩; exact inv_nonneg.mpr (norm_nonneg _))]
      refine ENNReal.ofReal_le_ofReal ?_
      refine regular_Icc_finset_ball_bound hn a (fun s => le_of_lt (huk_lt k s))
        (fun s => (hJ_sub k s).trans fun θ hθ =>
          ⟨lt_of_le_of_lt hα (hIoo_sub s hθ).1, lt_of_lt_of_le (hIoo_sub s hθ).2 hβ⟩)
        (fun s₁ s₂ hne => by
          dsimp only [Function.onFun]
          rw [Set.disjoint_left]
          intro x hx1 hx2
          have h1 := hJ_sub k s₁ (Ioo_subset_Icc_self hx1)
          have h2 := hJ_sub k s₂ (Ioo_subset_Icc_self hx2)
          have hne_val : s₁.1 ≠ s₂.1 := fun h => hne (Fin.ext h)
          rcases lt_or_gt_of_ne hne_val with hlt | hgt
          · have := hmono_c (s₁.1 + 1) s₂.1 (by omega) (by omega); linarith [h1.2, h2.1]
          · have := hmono_c (s₂.1 + 1) s₁.1 (by omega) (by omega); linarith [h2.2, h1.1])
        (fun s θ hθ => by rw [← hp_eq]; exact hreg_s s θ (hJ_sub k s hθ)) hr
        (fun s z ⟨θ, hθ, hz⟩ => hcov z ⟨θ, hIoo_sub s (hJ_sub k s hθ), by rwa [hp_eq]⟩)
    -- Pass to the limit k → ∞ for each piece and sum over s : Fin m
    have hlim_s : ∀ s : Fin m,
        Tendsto (fun k : ℕ => (μH[1] : Measure ℂ) (arcSet p (Icc (uk k s) (vk k s))))
          atTop (𝓝 ((μH[1] : Measure ℂ) (arcSet p (Ioo (c s.1) (c (s.1 + 1)))))) := by
      intro s
      have hmono_k : Monotone (fun k : ℕ => arcSet p (Icc (uk k s) (vk k s))) := by
        intro i j hij z ⟨θ, hθ, hz⟩
        have hle : (c (s.1 + 1) - c s.1) / ((j : ℝ) + 3) ≤ (c (s.1 + 1) - c s.1) / ((i : ℝ) + 3) :=
          div_le_div_of_nonneg_left (sub_nonneg.mpr (le_of_lt (hinc s.1 s.isLt))) (by positivity) (by gcongr)
        exact ⟨θ, ⟨(show uk j s ≤ uk i s by dsimp only [uk]; linarith).trans hθ.1,
          hθ.2.trans (show vk i s ≤ vk j s by dsimp only [vk]; linarith)⟩, hz⟩
      have hunion_k : (⋃ k : ℕ, arcSet p (Icc (uk k s) (vk k s))) = arcSet p (Ioo (c s.1) (c (s.1 + 1))) := by
        ext z
        simp only [mem_iUnion, arcSet, mem_ofPred_eq]
        constructor
        · rintro ⟨k, θ, hθ, hz⟩; exact ⟨θ, hJ_sub k s hθ, hz⟩
        · rintro ⟨θ, ⟨h1, h2⟩, hz⟩
          let δ := min (θ - c s.1) (c (s.1 + 1) - θ)
          have hδ : 0 < δ := lt_min (sub_pos.mpr h1) (sub_pos.mpr h2)
          obtain ⟨k, hk⟩ := exists_nat_gt ((c (s.1 + 1) - c s.1) / δ)
          have hstep : (c (s.1 + 1) - c s.1) / ((k : ℝ) + 3) < δ := by
            rw [div_lt_iff₀ (by positivity)]
            have := (div_lt_iff₀ hδ).mp hk; nlinarith
          exact ⟨k, θ, ⟨by dsimp only [uk]; linarith [min_le_left (θ - c s.1) (c (s.1 + 1) - θ)],
            by dsimp only [vk]; linarith [min_le_right (θ - c s.1) (c (s.1 + 1) - θ)]⟩, hz⟩
      rw [← hunion_k, hmono_k.measure_iUnion]
      exact tendsto_atTop_iSup (fun i j hij => measure_mono (hmono_k hij))
    have hlim_sum : Tendsto (fun k : ℕ => ∑ s : Fin m, (μH[1] : Measure ℂ) (arcSet p (Icc (uk k s) (vk k s))))
        atTop (𝓝 (∑ s : Fin m, (μH[1] : Measure ℂ) (arcSet p (Ioo (c s.1) (c (s.1 + 1)))))) :=
      tendsto_finsetSum _ fun s _ => hlim_s s
    have hsum_le : ∑ s : Fin m, (μH[1] : Measure ℂ) (arcSet p (Ioo (c s.1) (c (s.1 + 1)))) ≤
        ENNReal.ofReal (8 * (n : ℝ) ^ 2 * r) :=
      le_of_tendsto hlim_sum (Filter.Eventually.of_forall hk_bound)
    have hE_zero : (μH[1] : Measure ℂ) (arcSet p (B : Set ℝ)) = 0 := by
      refine hausdorffMeasure_one_finite_eq_zero ?_
      have hsubE : arcSet p (B : Set ℝ) ⊆ {z | p.eval z ∈ (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) '' (B : Set ℝ)} := by
        rintro z ⟨t, ht, hz⟩; exact ⟨t, ht, hz.symm⟩
      exact (finite_preimage_eval hn hp hdeg (B.finite_toSet.image _)).subset hsubE
    have hcov_arc : arcSet p (Ioo α β) ⊆
        (⋃ s : Fin m, arcSet p (Ioo (c s.1) (c (s.1 + 1)))) ∪ arcSet p (B : Set ℝ) := by
      rintro z ⟨t, ht, hz⟩
      by_cases htB : t ∈ (B : Set ℝ)
      · exact Or.inr ⟨t, htB, hz⟩
      · have ht' : t ∈ Ioo α β \ (B : Set ℝ) := ⟨ht, htB⟩
        rw [hunion] at ht'
        rcases mem_iUnion₂.mp ht' with ⟨s, hs, hts⟩
        exact Or.inl (mem_iUnion.mpr ⟨⟨s, Finset.mem_range.mp hs⟩, ⟨t, hts, hz⟩⟩)
    calc (μH[1] : Measure ℂ) (arcSet p (Ioo α β))
        ≤ (μH[1] : Measure ℂ) ((⋃ s : Fin m, arcSet p (Ioo (c s.1) (c (s.1 + 1)))) ∪ arcSet p (B : Set ℝ)) :=
          measure_mono hcov_arc
      _ ≤ (μH[1] : Measure ℂ) (⋃ s : Fin m, arcSet p (Ioo (c s.1) (c (s.1 + 1)))) +
            (μH[1] : Measure ℂ) (arcSet p (B : Set ℝ)) := measure_union_le _ _
      _ = (μH[1] : Measure ℂ) (⋃ s : Fin m, arcSet p (Ioo (c s.1) (c (s.1 + 1)))) := by rw [hE_zero, add_zero]
      _ ≤ ∑ s : Fin m, (μH[1] : Measure ℂ) (arcSet p (Ioo (c s.1) (c (s.1 + 1)))) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ENNReal.ofReal (8 * (n : ℝ) ^ 2 * r) := hsum_le
  · have hemp : Ioo α β = ∅ := Ioo_eq_empty hαβ
    simp [hemp, arcSet]

/-- Uniform small-arc tail bound (independent of the monic degree-`n` polynomial `p`):
if `β - α ≤ δ`, then `μH[1] (arcSet p (Ioo α β)) ≤ 8 * n^2 * δ^(1/n)`. -/
theorem arcSet_measure_Ioo_le {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]}
    (hp : p.Monic) (hdeg : p.natDegree = n) {α β δ : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 2 * Real.pi) (hδ : 0 ≤ δ) (hwidth : β - α ≤ δ) :
    (μH[1] : Measure ℂ) (arcSet p (Ioo α β)) ≤ ENNReal.ofReal (8 * (n : ℝ) ^ 2 * δ ^ ((n : ℝ)⁻¹)) := by
  let θ₀ : ℝ := (α + β) / 2
  let w₀ : ℂ := Complex.exp ((θ₀ : ℂ) * Complex.I)
  let q := p - C w₀
  have hq_deg : q.natDegree = n := by rw [Polynomial.natDegree_sub_C, hdeg]
  have hq_card : q.roots.card = n := by rw [IsAlgClosed.card_roots_eq_natDegree, hq_deg]
  obtain ⟨l, hl⟩ := Quotient.exists_rep q.roots
  change (l : Multiset ℂ) = q.roots at hl
  have hlen : l.length = n := by rw [← Multiset.coe_card, hl, hq_card]
  let Z : Fin n → ℂ := fun i => l[i.1]'(by omega)
  have hZ_mem : ∀ r ∈ q.roots, ∃ i : Fin n, Z i = r := by
    intro r hr
    rw [← hl, Multiset.mem_coe] at hr
    rcases List.getElem_of_mem hr with ⟨k, hk, rfl⟩
    exact ⟨⟨k, by omega⟩, rfl⟩
  refine arcSet_measure_Ioo_le_of_ball_cover hn hp hdeg hα hβ (Z := Z) (Real.rpow_nonneg hδ _) ?_
  rintro z ⟨θ, hθ, hz⟩
  have hdist : ‖p.eval z - w₀‖ ≤ δ := by
    rw [hz]
    have hlip : ∀ x y : ℝ, ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ ‖x - y‖ := by
      intro x y
      have hconv := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
        (f := fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) (C := 1)
        (fun t _ => ((Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp t
          (by simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I)).differentiableAt)
        (fun t _ => by
          have hd : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I))
              (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t :=
            (Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp t
              (by simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I)
          rw [hd.deriv, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one])
        (mem_univ y) (mem_univ x)
      simpa using hconv
    have h2 : |θ - θ₀| ≤ δ := by
      rw [abs_le]
      dsimp only [θ₀]; constructor <;> linarith [hθ.1, hθ.2]
    exact (hlip θ θ₀).trans (by simpa [Real.norm_eq_abs] using h2)
  obtain ⟨r, hr_mem, hr_le⟩ := monic_sub_eval_le_exists_root hn hp hdeg w₀ hδ hdist
  obtain ⟨i, rfl⟩ := hZ_mem r hr_mem
  exact ⟨i, hr_le⟩

lemma lemniscateLength_eq_arcSet_Ioo {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]}
    (hp : p.Monic) (hdeg : p.natDegree = n) :
    Erdos114.lemniscateLength p = (μH[1] : Measure ℂ) (arcSet p (Ioo (0 : ℝ) (2 * Real.pi))) := by
  have h1_zero : (μH[1] : Measure ℂ) {z : ℂ | p.eval z = 1} = 0 := by
    have hfin := finite_preimage_eval hn hp hdeg (Set.finite_singleton (1 : ℂ))
    exact hausdorffMeasure_one_finite_eq_zero (by simpa using hfin)
  have hsub1 : arcSet p (Ioo (0 : ℝ) (2 * Real.pi)) ⊆ Erdos114.lemniscate p := by
    rintro z ⟨θ, _, hz⟩
    change ‖p.eval z‖ = 1
    rw [hz, Complex.norm_exp_ofReal_mul_I]
  have hsub2 : Erdos114.lemniscate p ⊆ arcSet p (Ioo (0 : ℝ) (2 * Real.pi)) ∪ {z : ℂ | p.eval z = 1} := by
    intro z hz
    change ‖p.eval z‖ = 1 at hz
    by_cases h1 : p.eval z = 1
    · exact Or.inr h1
    · left
      have harg := Complex.norm_mul_exp_arg_mul_I (p.eval z)
      rw [hz, Complex.ofReal_one, one_mul] at harg
      have harg_ne0 : Complex.arg (p.eval z) ≠ 0 := by
        intro h0; rw [h0] at harg; simp at harg; exact h1 harg.symm
      by_cases hpos : 0 < Complex.arg (p.eval z)
      · refine ⟨Complex.arg (p.eval z), ⟨hpos, ?_⟩, harg.symm⟩
        linarith [Complex.arg_le_pi (p.eval z), Real.pi_pos]
      · have hneg : Complex.arg (p.eval z) < 0 := lt_of_le_of_ne (le_of_not_gt hpos) harg_ne0
        refine ⟨Complex.arg (p.eval z) + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
        · linarith [Complex.neg_pi_lt_arg (p.eval z), Real.pi_pos]
        · linarith
        · rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
            show (2 : ℂ) * (Real.pi : ℂ) * Complex.I = 2 * Real.pi * Complex.I by ring,
            Complex.exp_two_pi_mul_I, mul_one, harg]
  unfold Erdos114.lemniscateLength
  refine le_antisymm ?_ (measure_mono hsub1)
  calc (μH[1] : Measure ℂ) (Erdos114.lemniscate p)
      ≤ (μH[1] : Measure ℂ) (arcSet p (Ioo (0 : ℝ) (2 * Real.pi)) ∪ {z : ℂ | p.eval z = 1}) :=
        measure_mono hsub2
    _ ≤ (μH[1] : Measure ℂ) (arcSet p (Ioo (0 : ℝ) (2 * Real.pi))) +
          (μH[1] : Measure ℂ) {z : ℂ | p.eval z = 1} := measure_union_le _ _
    _ = _ := by rw [h1_zero, add_zero]

/-- Circle-integral identity in `ℝ≥0∞` for every nonconstant monic polynomial `p`. -/
theorem lemniscateLength_eq_lintegral {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]}
    (hp : p.Monic) (hdeg : p.natDegree = n) :
    Erdos114.lemniscateLength p =
      ∫⁻ θ in Ioo (0 : ℝ) (2 * Real.pi), circleIntegrandENN p θ := by
  rw [lemniscateLength_eq_arcSet_Ioo hn hp hdeg]
  exact arcSet_measure_Ioo_eq_lintegral hn hp hdeg le_rfl le_rfl

/-- Every nonconstant monic polynomial has finite lemniscate length. -/
theorem lemniscateLength_lt_top {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]}
    (hp : p.Monic) (hdeg : p.natDegree = n) :
    Erdos114.lemniscateLength p < ⊤ := by
  rw [lemniscateLength_eq_arcSet_Ioo hn hp hdeg]
  refine lt_of_le_of_lt (arcSet_measure_Ioo_le hn hp hdeg le_rfl le_rfl
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (by linarith)) ENNReal.ofReal_lt_top

/-- Real-valued Bochner circle-integral identity + `IntegrableOn` for every nonconstant monic `p`. -/
theorem lemniscateLength_eq_ofReal_integral {n : ℕ} (hn : 1 ≤ n) {p : ℂ[X]}
    (hp : p.Monic) (hdeg : p.natDegree = n) :
    IntegrableOn (circleIntegrand p) (Ioo (0 : ℝ) (2 * Real.pi)) volume ∧
    Erdos114.lemniscateLength p =
      ENNReal.ofReal (∫ θ in Ioo (0 : ℝ) (2 * Real.pi), circleIntegrand p θ) := by
  let a : Fin n → ℂ := fun j => p.coeff (j : ℕ)
  have hp_eq : p = monicPoly n a := eq_monicPoly_of_monic hp hdeg
  have hB_fin := badAngles_finite hn hp hdeg (le_refl 0) (le_refl (2 * Real.pi))
  have hae_reg : ∀ᵐ (θ : ℝ) ∂(volume.restrict (Ioo (0 : ℝ) (2 * Real.pi))),
      Complex.exp ((θ : ℂ) * Complex.I) ∉ critVals p := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    have hnull : volume {θ ∈ Ioo (0 : ℝ) (2 * Real.pi) | Complex.exp ((θ : ℂ) * Complex.I) ∈ critVals p} = 0 :=
      hB_fin.measure_zero volume
    filter_upwards [compl_mem_ae_iff.mpr hnull] with θ hθ hmem hcrit
    exact hθ ⟨hmem, hcrit⟩
  have hci_nn : ∀ θ, 0 ≤ circleIntegrand p θ := fun θ => by
    unfold circleIntegrand
    exact Multiset.sum_nonneg fun x hx => by
      rcases Multiset.mem_map.mp hx with ⟨_, _, rfl⟩; exact inv_nonneg.mpr (norm_nonneg _)
  have hae_eq : (fun θ => ENNReal.ofReal (circleIntegrand p θ)) =ᵐ[volume.restrict (Ioo (0 : ℝ) (2 * Real.pi))]
      circleIntegrandENN p := by
    filter_upwards [hae_reg] with θ hreg
    have hp_ne : p - C (Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := by
      have hd : (p - C (Complex.exp ((θ : ℂ) * Complex.I))).natDegree = n := by
        rw [Polynomial.natDegree_sub_C, hdeg]
      intro h0; rw [h0, Polynomial.natDegree_zero] at hd; omega
    exact (circleIntegrandENN_eq_ofReal_of_reg hreg hp_ne).symm
  -- AEStronglyMeasurable of circleIntegrand p on Ioo 0 (2π) via continuity on regular pieces
  have hmeas : AEStronglyMeasurable (circleIntegrand p) (volume.restrict (Ioo (0 : ℝ) (2 * Real.pi))) := by
    let B : Finset ℝ := hB_fin.toFinset
    have hB_sub : ∀ x ∈ B, x ∈ Ioo (0 : ℝ) (2 * Real.pi) := fun x hx => (hB_fin.mem_toFinset.mp hx).1
    obtain ⟨m, c, _, hc0, hcm, hinc, hdisjB, hunion⟩ :=
      partition_Ioo_diff_finset B.card 0 (2 * Real.pi) B rfl Real.two_pi_pos hB_sub
    have hmono_c : ∀ i j, i ≤ j → j ≤ m → c i ≤ c j := by
      intro i j hij hjm
      induction hij with
      | refl => exact le_rfl
      | @step j' hij' ih' => exact (ih' (by omega)).trans (le_of_lt (hinc j' (by omega)))
    have hpiece_cont : ∀ s ∈ Finset.range m,
        ContinuousOn (circleIntegrand p) (Ioo (c s) (c (s + 1))) := by
      intro s hs θ hθ
      rw [Finset.mem_range] at hs
      have hlo : 0 ≤ c s := hc0 ▸ hmono_c 0 s (Nat.zero_le s) (by omega)
      have hhi : c (s + 1) ≤ 2 * Real.pi := hcm ▸ hmono_c (s + 1) m (by omega) le_rfl
      have hθ02 : θ ∈ Ioo (0 : ℝ) (2 * Real.pi) := ⟨lt_of_le_of_lt hlo hθ.1, lt_of_lt_of_le hθ.2 hhi⟩
      have hreg_θ : Complex.exp ((θ : ℂ) * Complex.I) ∉ critVals p := fun hcrit =>
        Set.disjoint_left.mp (hdisjB s hs) hθ (Finset.mem_coe.mpr (hB_fin.mem_toFinset.mpr ⟨hθ02, hcrit⟩))
      obtain ⟨U, _, ha_U, hci_cont, _, _⟩ := regular_Icc_measure_and_continuity hn a
        le_rfl (by simpa using hθ02) (by intro t ht; simp at ht; subst ht; rwa [← hp_eq])
      -- Actually use a tiny open interval around θ inside Ioo (c s) (c (s + 1))
      let η := min (θ - c s) (c (s + 1) - θ) / 2
      have hη_pos : 0 < η := half_pos (lt_min (sub_pos.mpr hθ.1) (sub_pos.mpr hθ.2))
      have hIcc_sub : Icc (θ - η) (θ + η) ⊆ Ioo (c s) (c (s + 1)) := by
        intro t ht
        have h1 : η ≤ (θ - c s) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        have h2 : η ≤ (c (s + 1) - θ) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        exact ⟨by linarith [ht.1, hθ.1], by linarith [ht.2, hθ.2]⟩
      obtain ⟨U', _, ha_U', hci_cont', _, _⟩ := regular_Icc_measure_and_continuity hn a
        (by linarith) (hIcc_sub.trans fun t ht => ⟨lt_of_le_of_lt hlo ht.1, lt_of_lt_of_le ht.2 hhi⟩)
        (fun t ht => by
          rw [← hp_eq]
          have ht' := hIcc_sub ht
          exact fun hcrit => Set.disjoint_left.mp (hdisjB s hs) ht'
            (Finset.mem_coe.mpr (hB_fin.mem_toFinset.mpr ⟨⟨lt_of_le_of_lt hlo ht'.1, lt_of_lt_of_le ht'.2 hhi⟩, hcrit⟩)))
      have hc' : ContinuousOn (circleIntegrand p) (Icc (θ - η) (θ + η)) := by
        rw [hp_eq]
        exact continuousOn_snd_of_prod (f := fun a' t => circleIntegrand (monicPoly n a') t) ha_U' hci_cont'
      exact (hc'.continuousAt (Icc_mem_nhds (by linarith) (by linarith))).continuousWithinAt
    have hcont_diff : ContinuousOn (circleIntegrand p) (Ioo (0 : ℝ) (2 * Real.pi) \ (B : Set ℝ)) := by
      rw [hunion]
      intro θ hθ
      rcases mem_iUnion₂.mp hθ with ⟨s, hs, hθs⟩
      exact ((hpiece_cont s hs).continuousAt (isOpen_Ioo.mem_nhds hθs)).continuousWithinAt
    have hmeas_diff : AEStronglyMeasurable (circleIntegrand p)
        (volume.restrict (Ioo (0 : ℝ) (2 * Real.pi) \ (B : Set ℝ))) :=
      hcont_diff.aestronglyMeasurable (measurableSet_Ioo.diff B.finite_toSet.measurableSet)
    have hae_set : (Ioo (0 : ℝ) (2 * Real.pi) \ (B : Set ℝ) : Set ℝ) =ᵐ[volume] Ioo (0 : ℝ) (2 * Real.pi) := by
      rw [MeasureTheory.ae_eq_set]
      refine ⟨by simp, measure_mono_null (fun x hx => by by_contra h; exact hx.2 ⟨hx.1, h⟩)
        (B.finite_toSet.measure_zero volume)⟩
    rwa [Measure.restrict_congr_set hae_set] at hmeas_diff
  have hlint_lt : ∫⁻ θ in Ioo (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (circleIntegrand p θ) < ⊤ := by
    rw [lintegral_congr_ae hae_eq, ← lemniscateLength_eq_lintegral hn hp hdeg]
    exact lemniscateLength_lt_top hn hp hdeg
  have hint : IntegrableOn (circleIntegrand p) (Ioo (0 : ℝ) (2 * Real.pi)) volume := by
    refine ⟨hmeas, ?_⟩
    rw [HasFiniteIntegral]
    have hnorm : ∀ θ, ‖circleIntegrand p θ‖ₑ = ENNReal.ofReal (circleIntegrand p θ) := fun θ => by
      rw [Real.enorm_eq_ofReal (hci_nn θ)]
    simpa only [hnorm] using hlint_lt
  refine ⟨hint, ?_⟩
  rw [lemniscateLength_eq_lintegral hn hp hdeg, ← lintegral_congr_ae hae_eq,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hci_nn)]

private lemma exists_integral_close_nbhd {n : ℕ} {a₀ : Fin n → ℂ} {α β : ℝ} (hαβ : α < β)
    {U : Set (Fin n → ℂ)} (hUo : IsOpen U) (haU : a₀ ∈ U)
    (hci : ContinuousOn (fun p : (Fin n → ℂ) × ℝ => circleIntegrand (monicPoly n p.1) p.2) (U ×ˢ Icc α β))
    {δ_eps : ℝ} (hδ_eps : 0 < δ_eps) :
    ∃ W : Set (Fin n → ℂ), IsOpen W ∧ a₀ ∈ W ∧ W ⊆ U ∧
      ∀ a ∈ W,
        |(∫ θ in α..β, circleIntegrand (monicPoly n a) θ) -
          (∫ θ in α..β, circleIntegrand (monicPoly n a₀) θ)| < δ_eps := by
  let J := Icc α β
  have hJ_le : α ≤ β := le_of_lt hαβ
  have hJ_len_pos : 0 < β - α := sub_pos.mpr hαβ
  let eps0 : ℝ := δ_eps / (2 * (β - α))
  have heps0_pos : 0 < eps0 := div_pos hδ_eps (by positivity)
  have hloc : ∀ θ ∈ J, ∃ (Va : Set (Fin n → ℂ)) (Vt : Set ℝ),
      IsOpen Va ∧ a₀ ∈ Va ∧ Va ⊆ U ∧ IsOpen Vt ∧ θ ∈ Vt ∧
      ∀ a ∈ Va, ∀ t ∈ Vt ∩ J,
        |circleIntegrand (monicPoly n a) t - circleIntegrand (monicPoly n a₀) t| < eps0 := by
    intro θ hθ
    have hc_at : ContinuousWithinAt
        (fun p : (Fin n → ℂ) × ℝ => circleIntegrand (monicPoly n p.1) p.2) (U ×ˢ J) (a₀, θ) :=
      hci (a₀, θ) ⟨haU, hθ⟩
    have hnbhd := Metric.continuousWithinAt_iff.mp hc_at (eps0 / 2) (half_pos heps0_pos)
    obtain ⟨δ, hδ_pos, hδ⟩ := hnbhd
    refine ⟨Metric.ball a₀ δ ∩ U, Metric.ball θ δ,
      Metric.isOpen_ball.inter hUo, ⟨Metric.mem_ball_self hδ_pos, haU⟩, inter_subset_right,
      Metric.isOpen_ball, Metric.mem_ball_self hδ_pos, ?_⟩
    intro a ⟨ha_b, ha_U⟩ t ⟨ht_b, ht_J⟩
    have h1 : |circleIntegrand (monicPoly n a) t - circleIntegrand (monicPoly n a₀) θ| < eps0 / 2 := by
      have hd : dist (a, t) (a₀, θ) < δ := max_lt ha_b ht_b
      simpa [Real.dist_eq] using hδ ⟨ha_U, ht_J⟩ hd
    have h2 : |circleIntegrand (monicPoly n a₀) t - circleIntegrand (monicPoly n a₀) θ| < eps0 / 2 := by
      have hd : dist (a₀, t) (a₀, θ) < δ := max_lt (Metric.mem_ball_self hδ_pos) ht_b
      simpa [Real.dist_eq] using hδ ⟨haU, ht_J⟩ hd
    have htri : |circleIntegrand (monicPoly n a) t - circleIntegrand (monicPoly n a₀) t| ≤
        |circleIntegrand (monicPoly n a) t - circleIntegrand (monicPoly n a₀) θ| +
        |circleIntegrand (monicPoly n a₀) t - circleIntegrand (monicPoly n a₀) θ| := by
      have := abs_sub_le (circleIntegrand (monicPoly n a) t)
        (circleIntegrand (monicPoly n a₀) θ) (circleIntegrand (monicPoly n a₀) t)
      rwa [abs_sub_comm (circleIntegrand (monicPoly n a₀) θ)] at this
    linarith
  choose Va Vt hVa_o haVa hVa_sub hVt_o hθVt hdiff using fun (θ : J) => hloc θ.1 θ.2
  obtain ⟨sf, hsf⟩ := isCompact_Icc.elim_finite_subcover (fun θ : J => Vt θ) hVt_o
    fun t ht => mem_iUnion.mpr ⟨⟨t, ht⟩, hθVt ⟨t, ht⟩⟩
  let W : Set (Fin n → ℂ) := U ∩ ⋂ θ ∈ sf, Va θ
  refine ⟨W, hUo.inter (isOpen_biInter_finset fun θ _ => hVa_o θ),
    ⟨haU, mem_iInter₂.mpr fun θ _ => haVa θ⟩, inter_subset_left, ?_⟩
  intro a ha
  have hpt : ∀ t ∈ J, |circleIntegrand (monicPoly n a) t - circleIntegrand (monicPoly n a₀) t| ≤ eps0 := by
    intro t ht
    have hcov_t := hsf ht
    simp only [mem_iUnion] at hcov_t
    rcases hcov_t with ⟨θ, hθsf, ht_Vt⟩
    exact le_of_lt (hdiff θ a (mem_iInter₂.mp ha.2 θ hθsf) t ⟨ht_Vt, ht⟩)
  have hca : ContinuousOn (fun t => circleIntegrand (monicPoly n a) t) J :=
    continuousOn_snd_of_prod (f := fun a' t => circleIntegrand (monicPoly n a') t) ha.1 hci
  have hc0' : ContinuousOn (fun t => circleIntegrand (monicPoly n a₀) t) J :=
    continuousOn_snd_of_prod (f := fun a' t => circleIntegrand (monicPoly n a') t) haU hci
  have hsub_u : uIcc α β = J := uIcc_of_le hJ_le
  have hi_a : IntervalIntegrable (fun t => circleIntegrand (monicPoly n a) t) volume α β :=
    (hsub_u ▸ hca).intervalIntegrable
  have hi_0 : IntervalIntegrable (fun t => circleIntegrand (monicPoly n a₀) t) volume α β :=
    (hsub_u ▸ hc0').intervalIntegrable
  rw [← intervalIntegral.integral_sub hi_a hi_0]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (C := eps0) (f := fun t =>
    circleIntegrand (monicPoly n a) t - circleIntegrand (monicPoly n a₀) t) fun t ht => by
      rw [uIoc_of_le hJ_le] at ht
      simpa [Real.norm_eq_abs] using hpt t (Ioc_subset_Icc_self ht)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hJ_le)] at hnorm
  have hcalc : eps0 * (β - α) = δ_eps / 2 := by
    dsimp only [eps0]
    have hne : β - α ≠ 0 := ne_of_gt hJ_len_pos
    field_simp
  linarith

/-- **Eremenko–Hayman Lemma 4 (Continuity in coefficient coordinates):**
For every degree `n ≥ 1`, `a ↦ Erdos114.lemniscateLength (monicPoly n a)` is continuous
from `Fin n → ℂ` to `ℝ≥0∞`. -/
theorem continuous_lemniscateLength_monicPoly (n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun a : Fin n → ℂ => Erdos114.lemniscateLength (monicPoly n a)) := by
  rw [continuous_iff_continuousAt]
  intro a₀
  have hfin0 : Erdos114.lemniscateLength (monicPoly n a₀) < ⊤ :=
    lemniscateLength_lt_top hn (monicPoly_monic n a₀) (monicPoly_natDegree n a₀)
  -- Show Tendsto via toReal since all values are finite
  suffices hreal : Tendsto (fun a : Fin n → ℂ => (Erdos114.lemniscateLength (monicPoly n a)).toReal)
      (𝓝 a₀) (𝓝 (Erdos114.lemniscateLength (monicPoly n a₀)).toReal) by
    have hof := (ENNReal.continuous_ofReal.tendsto _).comp hreal
    have heq : (fun a : Fin n → ℂ => ENNReal.ofReal (Erdos114.lemniscateLength (monicPoly n a)).toReal) =
        fun a => Erdos114.lemniscateLength (monicPoly n a) := by
      funext a
      exact ENNReal.ofReal_toReal (lemniscateLength_lt_top hn (monicPoly_monic n a) (monicPoly_natDegree n a)).ne
    rw [Function.comp_def, heq, ENNReal.ofReal_toReal hfin0.ne] at hof
    exact hof
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Partition (0, 2π) \ badAngles(p₀) into m ≥ 1 open intervals (c 0, c 1), ..., (c (m-1), c m)
  let p₀ := monicPoly n a₀
  have hB_fin := badAngles_finite hn (monicPoly_monic n a₀) (monicPoly_natDegree n a₀)
    (le_refl 0) (le_refl (2 * Real.pi))
  let B : Finset ℝ := hB_fin.toFinset
  have hB_sub : ∀ x ∈ B, x ∈ Ioo (0 : ℝ) (2 * Real.pi) := fun x hx => (hB_fin.mem_toFinset.mp hx).1
  obtain ⟨m, c, hm, hc0, hcm, hinc, hdisjB, hunion⟩ :=
    partition_Ioo_diff_finset B.card 0 (2 * Real.pi) B rfl Real.two_pi_pos hB_sub
  have hmono_c : ∀ i j, i ≤ j → j ≤ m → c i ≤ c j := by
    intro i j hij hjm
    induction hij with
    | refl => exact le_rfl
    | @step j' hij' ih' => exact (ih' (by omega)).trans (le_of_lt (hinc j' (by omega)))
  -- Pick η > 0 small enough that:
  -- (1) 2 * η < c (s + 1) - c s for all s < m
  -- (2) 2 * m * (8 * n^2 * η^(1/n)) < ε / 3
  let minGap : ℝ := (Finset.univ : Finset (Fin m)).inf'
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (fun s => c (s.1 + 1) - c s.1)
  have hminGap_pos : 0 < minGap :=
    (Finset.lt_inf'_iff _).mpr fun s _ => sub_pos.mpr (hinc s.1 s.isLt)
  let tailC : ℝ := 2 * (m : ℝ) * (8 * (n : ℝ) ^ 2)
  have htailC_pos : 0 < tailC := by positivity
  let η : ℝ := min (minGap / 4) ((ε / (4 * tailC)) ^ n)
  have hη_pos : 0 < η := lt_min (by linarith) (pow_pos (div_pos hε (by linarith)) n)
  have hη_gap : ∀ s : Fin m, 2 * η < c (s.1 + 1) - c s.1 := by
    intro s
    have hle1 : η ≤ minGap / 4 := min_le_left _ _
    have hle2 : minGap ≤ c (s.1 + 1) - c s.1 := Finset.inf'_le _ (Finset.mem_univ s)
    linarith
  have hη_tail : 2 * (m : ℝ) * (8 * (n : ℝ) ^ 2 * η ^ ((n : ℝ)⁻¹)) < ε / 3 := by
    have hle : η ≤ (ε / (4 * tailC)) ^ n := min_le_right _ _
    have hpow : η ^ ((n : ℝ)⁻¹) ≤ ε / (4 * tailC) := by
      calc η ^ ((n : ℝ)⁻¹)
          ≤ ((ε / (4 * tailC)) ^ n) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow (le_of_lt hη_pos) hle (by positivity)
        _ = ε / (4 * tailC) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
              mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (by omega)), Real.rpow_one]
    have hcalc : 2 * (m : ℝ) * (8 * (n : ℝ) ^ 2 * (ε / (4 * tailC))) = ε / 4 := by
      dsimp only [tailC]
      have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
    have hmul : 2 * (m : ℝ) * (8 * (n : ℝ) ^ 2 * η ^ ((n : ℝ)⁻¹)) ≤
        2 * (m : ℝ) * (8 * (n : ℝ) ^ 2 * (ε / (4 * tailC))) := by gcongr
    linarith
  -- Apply regular_Icc_measure_and_continuity to each shrunk compact interval J s = Icc (c s + η) (c (s+1) - η)
  have hreg_J : ∀ s : Fin m, ∃ Us : Set (Fin n → ℂ), IsOpen Us ∧ a₀ ∈ Us ∧
      ContinuousOn (fun p : (Fin n → ℂ) × ℝ => circleIntegrand (monicPoly n p.1) p.2)
        (Us ×ˢ Icc (c s.1 + η) (c (s.1 + 1) - η)) ∧
      (∀ a ∈ Us, (μH[1] : Measure ℂ) (arcSet (monicPoly n a) (Icc (c s.1 + η) (c (s.1 + 1) - η))) =
        ENNReal.ofReal (∫ θ in (c s.1 + η)..(c (s.1 + 1) - η), circleIntegrand (monicPoly n a) θ)) := by
    intro s
    have hlo : 0 ≤ c s.1 := hc0 ▸ hmono_c 0 s.1 (Nat.zero_le s.1) (by omega)
    have hhi : c (s.1 + 1) ≤ 2 * Real.pi := hcm ▸ hmono_c (s.1 + 1) m (by omega) le_rfl
    have hJ_Ioo : Icc (c s.1 + η) (c (s.1 + 1) - η) ⊆ Ioo (c s.1) (c (s.1 + 1)) := fun θ hθ =>
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hJ_02 : Icc (c s.1 + η) (c (s.1 + 1) - η) ⊆ Ioo (0 : ℝ) (2 * Real.pi) := fun θ hθ =>
      ⟨lt_of_le_of_lt hlo (hJ_Ioo hθ).1, lt_of_lt_of_le (hJ_Ioo hθ).2 hhi⟩
    have hreg_s : ∀ θ ∈ Icc (c s.1 + η) (c (s.1 + 1) - η),
        Complex.exp ((θ : ℂ) * Complex.I) ∉ critVals (monicPoly n a₀) := by
      intro θ hθ hcrit
      have hmemB : θ ∈ B := hB_fin.mem_toFinset.mpr ⟨hJ_02 hθ, hcrit⟩
      exact Set.disjoint_left.mp (hdisjB s.1 s.isLt) (hJ_Ioo hθ) (Finset.mem_coe.mpr hmemB)
    obtain ⟨Us, hUo, haU, hci, _, hmeas⟩ :=
      regular_Icc_measure_and_continuity hn a₀ (by linarith [hη_gap s]) hJ_02 hreg_s
    exact ⟨Us, hUo, haU, hci, hmeas⟩
  choose Us hUo haU hci_s hmeas_s using hreg_J
  -- For each s, uniform continuity on compact {a₀} ×ˢ J s gives an open nbhd W_s ⊆ U_s where integral varies < ε / (3 * m)
  choose Ws hWo haW hW_sub hW_close using fun s : Fin m =>
    exists_integral_close_nbhd (by linarith [hη_gap s]) (hUo s) (haU s) (hci_s s)
      (div_pos hε (by positivity : (0 : ℝ) < 3 * (m : ℝ)))
  let W : Set (Fin n → ℂ) := ⋂ s : Fin m, Ws s
  have hW_open : IsOpen W := isOpen_iInter_of_finite hWo
  have ha₀_W : a₀ ∈ W := mem_iInter.mpr haW
  -- For EVERY a ∈ W, decompose lemniscateLength (monicPoly n a) = good + tail
  have hdecomp : ∀ a ∈ W,
      (∑ s : Fin m, ∫ θ in (c s.1 + η)..(c (s.1 + 1) - η), circleIntegrand (monicPoly n a) θ) ≤
        (Erdos114.lemniscateLength (monicPoly n a)).toReal ∧
      (Erdos114.lemniscateLength (monicPoly n a)).toReal ≤
        (∑ s : Fin m, ∫ θ in (c s.1 + η)..(c (s.1 + 1) - η), circleIntegrand (monicPoly n a) θ) +
          ε / 3 := by
    intro a ha
    let pa := monicPoly n a
    have hpa_m := monicPoly_monic n a
    have hpa_d := monicPoly_natDegree n a
    have hfin_a : Erdos114.lemniscateLength pa ≠ ⊤ := (lemniscateLength_lt_top hn hpa_m hpa_d).ne
    have hgood_eq : (μH[1] : Measure ℂ) (⋃ s : Fin m, arcSet pa (Icc (c s.1 + η) (c (s.1 + 1) - η))) =
        ENNReal.ofReal (∑ s : Fin m, ∫ θ in (c s.1 + η)..(c (s.1 + 1) - η), circleIntegrand pa θ) := by
      have hdisj : Pairwise (Function.onFun Disjoint fun s : Fin m =>
          arcSet pa (Icc (c s.1 + η) (c (s.1 + 1) - η))) := by
        intro s₁ s₂ hne
        dsimp only [Function.onFun]
        rw [Set.disjoint_left]
        rintro z ⟨t₁, ht₁, h1⟩ ⟨t₂, ht₂, h2⟩
        have hlo1 : 0 ≤ c s₁.1 := hc0 ▸ hmono_c 0 s₁.1 (Nat.zero_le s₁.1) (by omega)
        have hhi1 : c (s₁.1 + 1) ≤ 2 * Real.pi := hcm ▸ hmono_c (s₁.1 + 1) m (by omega) le_rfl
        have hlo2 : 0 ≤ c s₂.1 := hc0 ▸ hmono_c 0 s₂.1 (Nat.zero_le s₂.1) (by omega)
        have hhi2 : c (s₂.1 + 1) ≤ 2 * Real.pi := hcm ▸ hmono_c (s₂.1 + 1) m (by omega) le_rfl
        have ht1_02 : t₁ ∈ Ioo (0 : ℝ) (2 * Real.pi) :=
          ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
        have ht2_02 : t₂ ∈ Ioo (0 : ℝ) (2 * Real.pi) :=
          ⟨by linarith [ht₂.1], by linarith [ht₂.2]⟩
        have ht_eq : t₁ = t₂ := exp_mul_I_injOn_Ioo ht1_02 ht2_02 (h1.symm.trans h2)
        subst ht_eq
        have hne_v : s₁.1 ≠ s₂.1 := fun h => hne (Fin.ext h)
        rcases lt_or_gt_of_ne hne_v with hlt | hgt
        · have := hmono_c (s₁.1 + 1) s₂.1 (by omega) (by omega); linarith [ht₁.2, ht₂.1]
        · have := hmono_c (s₂.1 + 1) s₁.1 (by omega) (by omega); linarith [ht₂.2, ht₁.1]
      have hmeas : ∀ s : Fin m, MeasurableSet (arcSet pa (Icc (c s.1 + η) (c (s.1 + 1) - η))) := by
        intro s
        have hcont_exp : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) :=
          Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
        have hpre : arcSet pa (Icc (c s.1 + η) (c (s.1 + 1) - η)) =
            (fun z => pa.eval z) ⁻¹' ((fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) ''
              Icc (c s.1 + η) (c (s.1 + 1) - η)) := by ext z; simp [arcSet, eq_comm]
        rw [hpre]
        exact (isCompact_Icc.image hcont_exp).measurableSet.preimage pa.continuous.measurable
      rw [measure_iUnion hdisj hmeas, tsum_fintype,
        Finset.sum_congr rfl fun s _ => hmeas_s s a (hW_sub s (mem_iInter.mp ha s)),
        ← ENNReal.ofReal_sum_of_nonneg fun s _ =>
          intervalIntegral.integral_nonneg (by linarith [hη_gap s]) fun θ _ => by
            unfold circleIntegrand
            exact Multiset.sum_nonneg fun x hx => by
              rcases Multiset.mem_map.mp hx with ⟨_, _, rfl⟩; exact inv_nonneg.mpr (norm_nonneg _)]
    have hgood_nn : 0 ≤ ∑ s : Fin m, ∫ θ in (c s.1 + η)..(c (s.1 + 1) - η), circleIntegrand pa θ :=
      Finset.sum_nonneg fun s _ => intervalIntegral.integral_nonneg (by linarith [hη_gap s]) fun θ _ => by
        unfold circleIntegrand
        exact Multiset.sum_nonneg fun x hx => by
          rcases Multiset.mem_map.mp hx with ⟨_, _, rfl⟩; exact inv_nonneg.mpr (norm_nonneg _)
    -- Tail: Ioo 0 (2π) ⊆ (⋃ s, J s) ∪ (⋃ s, Ioo (c s) (c s + η)) ∪ (⋃ s, Ioo (c (s+1) - η) (c (s+1))) ∪ B ∪ endpoints
    let Efin : Set ℝ := (B : Set ℝ) ∪
      ((Finset.univ.image (fun s : Fin m => c s.1 + η) : Finset ℝ) : Set ℝ) ∪
      ((Finset.univ.image (fun s : Fin m => c (s.1 + 1) - η) : Finset ℝ) : Set ℝ)
    have hEfin_zero : (μH[1] : Measure ℂ) (arcSet pa Efin) = 0 := by
      have hfin : Efin.Finite := (B.finite_toSet.union (Finset.finite_toSet _)).union (Finset.finite_toSet _)
      refine hausdorffMeasure_one_finite_eq_zero ?_
      have hsubE : arcSet pa Efin ⊆ {z | pa.eval z ∈ (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) '' Efin} := by
        rintro z ⟨t, ht, hz⟩; exact ⟨t, ht, hz.symm⟩
      exact (finite_preimage_eval hn hpa_m hpa_d (hfin.image _)).subset hsubE
    have hcov_all : arcSet pa (Ioo (0 : ℝ) (2 * Real.pi)) ⊆
        (⋃ s : Fin m, arcSet pa (Icc (c s.1 + η) (c (s.1 + 1) - η))) ∪
        ((⋃ s : Fin m, arcSet pa (Ioo (c s.1) (c s.1 + η))) ∪
          (⋃ s : Fin m, arcSet pa (Ioo (c (s.1 + 1) - η) (c (s.1 + 1))))) ∪
        arcSet pa Efin := by
      rintro z ⟨θ, hθ, hz⟩
      by_cases hθB : θ ∈ (B : Set ℝ)
      · exact Or.inr ⟨θ, Or.inl (Or.inl hθB), hz⟩
      · have hθ' : θ ∈ Ioo (0 : ℝ) (2 * Real.pi) \ (B : Set ℝ) := ⟨hθ, hθB⟩
        rw [hunion] at hθ'
        rcases mem_iUnion₂.mp hθ' with ⟨s, hs, hθs⟩
        let sf : Fin m := ⟨s, Finset.mem_range.mp hs⟩
        by_cases h1 : θ < c sf.1 + η
        · exact Or.inl (Or.inr (Or.inl (mem_iUnion.mpr ⟨sf, ⟨θ, ⟨hθs.1, h1⟩, hz⟩⟩)))
        · by_cases h2 : c (sf.1 + 1) - η < θ
          · exact Or.inl (Or.inr (Or.inr (mem_iUnion.mpr ⟨sf, ⟨θ, ⟨h2, hθs.2⟩, hz⟩⟩)))
          · exact Or.inl (Or.inl (mem_iUnion.mpr ⟨sf, ⟨θ, ⟨le_of_not_gt h1, le_of_not_gt h2⟩, hz⟩⟩))
    have htail_le : (μH[1] : Measure ℂ)
        ((⋃ s : Fin m, arcSet pa (Ioo (c s.1) (c s.1 + η))) ∪
          (⋃ s : Fin m, arcSet pa (Ioo (c (s.1 + 1) - η) (c (s.1 + 1))))) ≤
        ENNReal.ofReal (ε / 3) := by
      have h1 : (μH[1] : Measure ℂ) (⋃ s : Fin m, arcSet pa (Ioo (c s.1) (c s.1 + η))) ≤
          ∑ _s : Fin m, ENNReal.ofReal (8 * (n : ℝ) ^ 2 * η ^ ((n : ℝ)⁻¹)) := by
        refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
        have hlo : 0 ≤ c s.1 := hc0 ▸ hmono_c 0 s.1 (Nat.zero_le s.1) (by omega)
        have hhi : c s.1 + η ≤ 2 * Real.pi := by
          have := hcm ▸ hmono_c (s.1 + 1) m (by omega) le_rfl
          linarith [hη_gap s]
        exact arcSet_measure_Ioo_le hn hpa_m hpa_d hlo hhi (le_of_lt hη_pos) (by linarith)
      have h2 : (μH[1] : Measure ℂ) (⋃ s : Fin m, arcSet pa (Ioo (c (s.1 + 1) - η) (c (s.1 + 1)))) ≤
          ∑ _s : Fin m, ENNReal.ofReal (8 * (n : ℝ) ^ 2 * η ^ ((n : ℝ)⁻¹)) := by
        refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
        have hlo : 0 ≤ c (s.1 + 1) - η := by
          have := hc0 ▸ hmono_c 0 s.1 (Nat.zero_le s.1) (by omega)
          linarith [hη_gap s]
        have hhi : c (s.1 + 1) ≤ 2 * Real.pi := hcm ▸ hmono_c (s.1 + 1) m (by omega) le_rfl
        exact arcSet_measure_Ioo_le hn hpa_m hpa_d hlo hhi (le_of_lt hη_pos) (by linarith)
      have hsum_eq : (∑ _s : Fin m, ENNReal.ofReal (8 * (n : ℝ) ^ 2 * η ^ ((n : ℝ)⁻¹))) +
          (∑ _s : Fin m, ENNReal.ofReal (8 * (n : ℝ) ^ 2 * η ^ ((n : ℝ)⁻¹))) =
          ENNReal.ofReal (2 * (m : ℝ) * (8 * (n : ℝ) ^ 2 * η ^ ((n : ℝ)⁻¹))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← two_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
      calc (μH[1] : Measure ℂ) ((⋃ s : Fin m, arcSet pa (Ioo (c s.1) (c s.1 + η))) ∪
              (⋃ s : Fin m, arcSet pa (Ioo (c (s.1 + 1) - η) (c (s.1 + 1)))))
          ≤ (μH[1] : Measure ℂ) (⋃ s : Fin m, arcSet pa (Ioo (c s.1) (c s.1 + η))) +
              (μH[1] : Measure ℂ) (⋃ s : Fin m, arcSet pa (Ioo (c (s.1 + 1) - η) (c (s.1 + 1)))) :=
            measure_union_le _ _
        _ ≤ _ := add_le_add h1 h2
        _ = ENNReal.ofReal (2 * (m : ℝ) * (8 * (n : ℝ) ^ 2 * η ^ ((n : ℝ)⁻¹))) := hsum_eq
        _ ≤ ENNReal.ofReal (ε / 3) := ENNReal.ofReal_le_ofReal (le_of_lt hη_tail)
    constructor
    · have hsub_good : (⋃ s : Fin m, arcSet pa (Icc (c s.1 + η) (c (s.1 + 1) - η))) ⊆
          arcSet pa (Ioo (0 : ℝ) (2 * Real.pi)) :=
        iUnion_subset fun s z ⟨θ, hθ, hz⟩ => by
          have hlo : 0 ≤ c s.1 := hc0 ▸ hmono_c 0 s.1 (Nat.zero_le s.1) (by omega)
          have hhi : c (s.1 + 1) ≤ 2 * Real.pi := hcm ▸ hmono_c (s.1 + 1) m (by omega) le_rfl
          exact ⟨θ, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, hz⟩
      have hle_enn : ENNReal.ofReal (∑ s : Fin m, ∫ θ in (c s.1 + η)..(c (s.1 + 1) - η), circleIntegrand pa θ) ≤
          Erdos114.lemniscateLength pa := by
        rw [lemniscateLength_eq_arcSet_Ioo hn hpa_m hpa_d, ← hgood_eq]
        exact measure_mono hsub_good
      have htr := ENNReal.toReal_mono hfin_a hle_enn
      rwa [ENNReal.toReal_ofReal hgood_nn] at htr
    · have hle_enn : Erdos114.lemniscateLength pa ≤
          ENNReal.ofReal ((∑ s : Fin m, ∫ θ in (c s.1 + η)..(c (s.1 + 1) - η), circleIntegrand pa θ) + ε / 3) := by
        rw [lemniscateLength_eq_arcSet_Ioo hn hpa_m hpa_d,
          ENNReal.ofReal_add hgood_nn (by positivity), ← hgood_eq]
        calc (μH[1] : Measure ℂ) (arcSet pa (Ioo (0 : ℝ) (2 * Real.pi)))
            ≤ (μH[1] : Measure ℂ) ((⋃ s : Fin m, arcSet pa (Icc (c s.1 + η) (c (s.1 + 1) - η))) ∪
                ((⋃ s : Fin m, arcSet pa (Ioo (c s.1) (c s.1 + η))) ∪
                  (⋃ s : Fin m, arcSet pa (Ioo (c (s.1 + 1) - η) (c (s.1 + 1))))) ∪
                arcSet pa Efin) := measure_mono hcov_all
          _ ≤ (μH[1] : Measure ℂ) ((⋃ s : Fin m, arcSet pa (Icc (c s.1 + η) (c (s.1 + 1) - η))) ∪
                ((⋃ s : Fin m, arcSet pa (Ioo (c s.1) (c s.1 + η))) ∪
                  (⋃ s : Fin m, arcSet pa (Ioo (c (s.1 + 1) - η) (c (s.1 + 1)))))) +
                (μH[1] : Measure ℂ) (arcSet pa Efin) := measure_union_le _ _
          _ ≤ (μH[1] : Measure ℂ) (⋃ s : Fin m, arcSet pa (Icc (c s.1 + η) (c (s.1 + 1) - η))) +
                (μH[1] : Measure ℂ) ((⋃ s : Fin m, arcSet pa (Ioo (c s.1) (c s.1 + η))) ∪
                  (⋃ s : Fin m, arcSet pa (Ioo (c (s.1 + 1) - η) (c (s.1 + 1))))) := by
              rw [hEfin_zero, add_zero]; exact measure_union_le _ _
          _ ≤ _ := by gcongr
      have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle_enn
      rwa [ENNReal.toReal_ofReal (by positivity)] at htr
  -- Finish: for all a ∈ W, dist < ε
  filter_upwards [hW_open.mem_nhds ha₀_W] with a ha
  rw [Real.dist_eq]
  have hd_a := hdecomp a ha
  have hd_0 := hdecomp a₀ ha₀_W
  have hsum_diff :
      |(∑ s : Fin m, ∫ θ in (c s.1 + η)..(c (s.1 + 1) - η), circleIntegrand (monicPoly n a) θ) -
        (∑ s : Fin m, ∫ θ in (c s.1 + η)..(c (s.1 + 1) - η), circleIntegrand (monicPoly n a₀) θ)| <
        ε / 3 := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ s : Fin m, ((∫ θ in (c s.1 + η)..(c (s.1 + 1) - η), circleIntegrand (monicPoly n a) θ) -
            (∫ θ in (c s.1 + η)..(c (s.1 + 1) - η), circleIntegrand (monicPoly n a₀) θ))|
        ≤ ∑ s : Fin m, |(∫ θ in (c s.1 + η)..(c (s.1 + 1) - η), circleIntegrand (monicPoly n a) θ) -
            (∫ θ in (c s.1 + η)..(c (s.1 + 1) - η), circleIntegrand (monicPoly n a₀) θ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _s : Fin m, (ε / (3 * (m : ℝ))) :=
          Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
            fun s _ => hW_close s a (mem_iInter.mp ha s)
      _ = ε / 3 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          field_simp
  rw [abs_lt] at hsum_diff ⊢
  constructor <;> linarith

/-- Sequential form of Eremenko–Hayman Lemma 4 continuity: coefficientwise convergence of
monic degree-`n` polynomials implies convergence of Hausdorff lemniscate lengths. -/
theorem tendsto_lemniscateLength_of_tendsto_coeff {n : ℕ} (hn : 1 ≤ n)
    {p : ℕ → ℂ[X]} {p₀ : ℂ[X]}
    (hp : ∀ k, (p k).Monic) (hdeg : ∀ k, (p k).natDegree = n)
    (hp₀ : p₀.Monic) (hdeg₀ : p₀.natDegree = n)
    (hcoeff : ∀ j : Fin n, Tendsto (fun k => (p k).coeff (j : ℕ)) atTop (𝓝 (p₀.coeff (j : ℕ)))) :
    Tendsto (fun k => Erdos114.lemniscateLength (p k)) atTop (𝓝 (Erdos114.lemniscateLength p₀)) := by
  have ha : Tendsto (fun k => (fun j : Fin n => (p k).coeff (j : ℕ))) atTop
      (𝓝 (fun j : Fin n => p₀.coeff (j : ℕ))) :=
    tendsto_pi_nhds.mpr hcoeff
  have hc := ((continuous_lemniscateLength_monicPoly n hn).tendsto _).comp ha
  have h1 : (fun k => Erdos114.lemniscateLength (monicPoly n (fun j : Fin n => (p k).coeff (j : ℕ)))) =
      fun k => Erdos114.lemniscateLength (p k) := by
    funext k; rw [← eq_monicPoly_of_monic (hp k) (hdeg k)]
  have h0 : monicPoly n (fun j : Fin n => p₀.coeff (j : ℕ)) = p₀ :=
    (eq_monicPoly_of_monic hp₀ hdeg₀).symm
  rwa [Function.comp_def, h1, h0] at hc

/-- Root-coordinate polynomial `∏ i : Fin n, (X - C (Z i))` (matches `RootCover.rootPoly`). -/
def rootPoly {n : ℕ} (Z : Fin n → ℂ) : ℂ[X] :=
  ∏ i : Fin n, (X - C (Z i))

lemma continuous_rootPoly_coeff (n : ℕ) (j : ℕ) :
    Continuous (fun Z : Fin n → ℂ => (rootPoly Z).coeff j) := by
  induction n generalizing j with
  | zero =>
    have : (fun Z : Fin 0 → ℂ => (rootPoly Z).coeff j) = fun _ => (1 : ℂ[X]).coeff j := by
      funext Z; simp [rootPoly]
    rw [this]; exact continuous_const
  | succ n ih =>
    have hsplit : ∀ Z : Fin (n + 1) → ℂ,
        rootPoly Z = (X - C (Z 0)) * rootPoly (fun i : Fin n => Z i.succ) := fun Z => by
      simp [rootPoly, Fin.prod_univ_succ]
    have hcoeff : ∀ Z : Fin (n + 1) → ℂ,
        (rootPoly Z).coeff j =
          (if j = 0 then 0 else (rootPoly (fun i : Fin n => Z i.succ)).coeff (j - 1)) -
            Z 0 * (rootPoly (fun i : Fin n => Z i.succ)).coeff j := by
      intro Z
      rw [hsplit Z, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      cases j with
      | zero => simp
      | succ j' => simp
    simp_rw [hcoeff]
    have htail : Continuous (fun Z : Fin (n + 1) → ℂ => fun i : Fin n => Z i.succ) :=
      continuous_pi fun i => continuous_apply i.succ
    refine Continuous.sub ?_ ((continuous_apply 0).mul ((ih j).comp htail))
    by_cases hj : j = 0
    · simp [hj, continuous_const]
    · simp only [if_neg hj]
      exact (ih (j - 1)).comp htail

/-- Continuity of `Erdos114.lemniscateLength` in root coordinates (exact `hc` hypothesis of
`LemniscateCompactness.extremizer_of_compact_control` in `RootCover.lean`). -/
theorem continuous_lemniscateLength_rootPoly {n : ℕ} (hn : 1 ≤ n) :
    Continuous (fun Z : Fin n → ℂ => Erdos114.lemniscateLength (rootPoly Z)) := by
  have heq : (fun Z : Fin n → ℂ => Erdos114.lemniscateLength (rootPoly Z)) =
      fun Z => Erdos114.lemniscateLength (monicPoly n (fun j : Fin n => (rootPoly Z).coeff (j : ℕ))) := by
    funext Z
    have hm : (rootPoly Z).Monic := Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _
    have hd : (rootPoly Z).natDegree = n := by simp [rootPoly]
    rw [← eq_monicPoly_of_monic hm hd]
  rw [heq]
  exact (continuous_lemniscateLength_monicPoly n hn).comp
    (continuous_pi fun j => continuous_rootPoly_coeff n j.1)

/-- The lemniscate of `X ^ n` (`n ≥ 1`) is the unit circle, with exact 1D Hausdorff measure `2π`. -/
theorem lemniscateLength_X_pow {n : ℕ} (hn : 1 ≤ n) :
    Erdos114.lemniscateLength (X ^ n : ℂ[X]) = ENNReal.ofReal (2 * Real.pi) := by
  have hm : (X ^ n : ℂ[X]).Monic := Polynomial.monic_X_pow n
  have hd : (X ^ n : ℂ[X]).natDegree = n := Polynomial.natDegree_X_pow n
  have hlem_eq : Erdos114.lemniscate (X ^ n : ℂ[X]) =
      (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' Icc (0 : ℝ) (2 * Real.pi) := by
    ext z
    change ‖(X ^ n : ℂ[X]).eval z‖ = 1 ↔ _
    rw [Polynomial.eval_pow, Polynomial.eval_X, norm_pow]
    have hnorm1 : ‖z‖ ^ n = 1 ↔ ‖z‖ = 1 := pow_eq_one_iff_of_nonneg (norm_nonneg z) (by omega)
    rw [hnorm1]
    constructor
    · intro hz
      have harg := Complex.norm_mul_exp_arg_mul_I z
      rw [hz, Complex.ofReal_one, one_mul] at harg
      by_cases hnn : 0 ≤ Complex.arg z
      · exact ⟨Complex.arg z, ⟨hnn, by linarith [Complex.arg_le_pi z, Real.pi_pos]⟩, harg⟩
      · refine ⟨Complex.arg z + 2 * Real.pi, ⟨by linarith [Complex.neg_pi_lt_arg z], by linarith⟩, ?_⟩
        dsimp only
        rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
          show (2 : ℂ) * (Real.pi : ℂ) * Complex.I = 2 * Real.pi * Complex.I by ring,
          Complex.exp_two_pi_mul_I, mul_one, harg]
    · rintro ⟨θ, _, rfl⟩
      exact Complex.norm_exp_ofReal_mul_I θ
  -- Apply Section 1 to the two halves [0, π] and [π, 2π] (injective on each!)
  have hinj1 : InjOn (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) (Icc 0 Real.pi) := by
    intro θ₁ h₁ θ₂ h₂ heq
    rw [Complex.exp_eq_exp_iff_exists_int] at heq
    rcases heq with ⟨k, hk⟩
    have hmul : ((θ₁ : ℂ) - (θ₂ : ℂ) - (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I = 0 := by
      push_cast; linear_combination hk
    have h0 := (mul_eq_zero.mp hmul).resolve_right Complex.I_ne_zero
    have hre := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
    have hk0 : k = 0 := by
      by_contra hne
      have hpi := Real.pi_pos
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        nlinarith [h₁.1, h₂.2]
      · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hgt
        nlinarith [h₁.2, h₂.1]
    rw [hk0] at hre; simp at hre; linarith
  have hinj2 : InjOn (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) (Icc Real.pi (2 * Real.pi)) := by
    intro θ₁ h₁ θ₂ h₂ heq
    dsimp only at heq
    have h := hinj1 (show θ₁ - Real.pi ∈ Icc 0 Real.pi by constructor <;> linarith [h₁.1, h₁.2])
      (show θ₂ - Real.pi ∈ Icc 0 Real.pi by constructor <;> linarith [h₂.1, h₂.2]) (by
        dsimp only
        rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, Complex.ofReal_sub, sub_mul, Complex.exp_sub, heq])
    linarith
  have hder : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) θ := fun θ =>
    (Complex.hasDerivAt_exp ((θ : ℂ) * Complex.I)).comp θ
      (by simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I)
  have hcont' : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) * Complex.I) :=
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const
  have hm1 : (μH[1] : Measure ℂ) ((fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' Icc 0 Real.pi) =
      ENNReal.ofReal Real.pi := by
    rw [hausdorffMeasure_one_image_Icc_eq_integral Real.pi_pos.le hinj1 (fun t _ => hder t) hcont'.continuousOn]
    simp [Complex.norm_exp_ofReal_mul_I]
  have hm2 : (μH[1] : Measure ℂ) ((fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' Icc Real.pi (2 * Real.pi)) =
      ENNReal.ofReal Real.pi := by
    rw [hausdorffMeasure_one_image_Icc_eq_integral (by linarith [Real.pi_pos]) hinj2 (fun t _ => hder t) hcont'.continuousOn]
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one,
      intervalIntegral.integral_const, smul_eq_mul]
    congr 1; ring
  have hsplit : (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' Icc 0 (2 * Real.pi) =
      ((fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' Icc 0 Real.pi) ∪
      ((fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' Icc Real.pi (2 * Real.pi)) := by
    rw [← image_union, Icc_union_Icc_eq_Icc Real.pi_pos.le (by linarith [Real.pi_pos])]
  have hinter_sub : ((fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' Icc 0 Real.pi) ∩
      ((fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' Icc Real.pi (2 * Real.pi)) ⊆ {1, -1} := by
    rintro z ⟨⟨θ₁, h₁, rfl⟩, ⟨θ₂, h₂, h2⟩⟩
    rw [Complex.exp_eq_exp_iff_exists_int] at h2
    rcases h2 with ⟨k, hk⟩
    have hmul : ((θ₂ : ℂ) - (θ₁ : ℂ) - (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) * Complex.I = 0 := by
      push_cast; linear_combination hk
    have h0 := (mul_eq_zero.mp hmul).resolve_right Complex.I_ne_zero
    have hre := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
    have hpi := Real.pi_pos
    rcases le_or_gt k 0 with hk0 | hk1
    · rcases eq_or_lt_of_le hk0 with rfl | hneg
      · have hθ : θ₁ = Real.pi := by simp at hre; linarith [h₁.2, h₂.1]
        right; dsimp only; rw [hθ, Complex.exp_pi_mul_I]; rfl
      · have : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hneg
        nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]
    · rcases eq_or_lt_of_le (Int.add_one_le_iff.mpr hk1) with hk_eq | hk2
      · have : (k : ℝ) = 1 := by exact_mod_cast hk_eq.symm
        have hθ : θ₁ = 0 := by rw [this] at hre; linarith [h₁.1, h₂.2]
        left; rw [hθ]; simp
      · have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
        nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]
  have hinter_zero : (μH[1] : Measure ℂ) (((fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' Icc 0 Real.pi) ∩
      ((fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' Icc Real.pi (2 * Real.pi))) = 0 :=
    measure_mono_null hinter_sub (hausdorffMeasure_one_finite_eq_zero ((Set.finite_singleton _).insert _))
  have hmeas2 : MeasurableSet ((fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' Icc Real.pi (2 * Real.pi)) :=
    (isCompact_Icc.image (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))).measurableSet
  unfold Erdos114.lemniscateLength
  rw [hlem_eq, hsplit]
  have hadd := measure_union_add_inter
    ((fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) '' Icc 0 Real.pi) hmeas2 (μ := (μH[1] : Measure ℂ))
  rw [hinter_zero, add_zero, hm1, hm2, ← ENNReal.ofReal_add Real.pi_pos.le Real.pi_pos.le, ← two_mul] at hadd
  exact hadd

/-- Separated-roots length cutoff (`hcut` hypothesis of `RootCover.extremizer_of_compact_control`):
for `R = 3 * (2 * n^2)^(n - 1)`, any centered root vector `Z` with `Z 0 = 0` and some `‖Z i‖ > R`
has lemniscate length `≤ lemniscateLength (rootPoly 0) = 2π`. -/
theorem lemniscateLength_rootPoly_le_of_far_root {n : ℕ} (hn : 1 ≤ n) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ Z : Fin n → ℂ, Z ⟨0, by omega⟩ = 0 → (∃ i : Fin n, R < ‖Z i‖) →
        Erdos114.lemniscateLength (rootPoly Z) ≤ Erdos114.lemniscateLength (rootPoly (0 : Fin n → ℂ)) := by
  let r : ℝ := (2 * (n : ℝ) ^ 2)⁻¹
  have hr_pos : 0 < r := inv_pos.mpr (by positivity)
  let R : ℝ := 3 * (2 * (n : ℝ) ^ 2) ^ (n - 1)
  refine ⟨R, by positivity, fun Z hZ0 ⟨i, hiR⟩ => ?_⟩
  have hsep : 2 < dist (Z ⟨0, by omega⟩) (Z i) * r ^ (n - 1) := by
    rw [hZ0, dist_zero_left]
    have hmul : R * r ^ (n - 1) = 3 := by
      dsimp only [R, r]
      rw [inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by positivity)), mul_one]
    have hlt : R * r ^ (n - 1) < ‖Z i‖ * r ^ (n - 1) :=
      mul_lt_mul_of_pos_right hiR (pow_pos hr_pos _)
    linarith
  have hcover : ∀ z ∈ arcSet (rootPoly Z) (Ioo (0 : ℝ) (2 * Real.pi)), ∃ j : Fin n, ‖z - Z j‖ ≤ r := by
    rintro z ⟨θ, _, hz⟩
    have hnorm1 : ‖∏ j : Fin n, (z - Z j)‖ ≤ 1 := by
      have hev : (rootPoly Z).eval z = ∏ j : Fin n, (z - Z j) := by
        simp [rootPoly, Polynomial.eval_prod]
      rw [← hev, hz, Complex.norm_exp_ofReal_mul_I]
    by_contra hall
    push Not at hall
    have ht := dist_triangle (Z ⟨0, by omega⟩) z (Z i)
    rw [dist_comm (Z ⟨0, by omega⟩) z] at ht
    obtain ⟨k, hk⟩ : ∃ k : Fin n, dist (Z ⟨0, by omega⟩) (Z i) ≤ 2 * dist z (Z k) := by
      rcases le_total (dist z (Z ⟨0, by omega⟩)) (dist z (Z i)) with h | h
      · exact ⟨i, by linarith⟩
      · exact ⟨⟨0, by omega⟩, by linarith⟩
    let S := (Finset.univ : Finset (Fin n)).erase k
    have hcard : S.card = n - 1 := by simp [S, Finset.card_erase_of_mem]
    have hprod : r ^ (n - 1) ≤ ∏ j ∈ S, dist z (Z j) := by
      calc r ^ (n - 1) = ∏ _j ∈ S, r := by simp [hcard]
        _ ≤ ∏ j ∈ S, dist z (Z j) := Finset.prod_le_prod (fun _ _ => hr_pos.le) fun j _ =>
            by rw [dist_eq_norm]; exact le_of_lt (hall j)
    have htot : dist z (Z k) * ∏ j ∈ S, dist z (Z j) ≤ 1 := by
      dsimp only [S]
      rw [Finset.mul_prod_erase Finset.univ (fun j => dist z (Z j)) (Finset.mem_univ k)]
      simpa [dist_eq_norm, norm_prod] using hnorm1
    have t1 := mul_le_mul_of_nonneg_right hk (pow_nonneg hr_pos.le (n - 1))
    have t2 := mul_le_mul_of_nonneg_left hprod (dist_nonneg (x := z) (y := Z k))
    linarith
  have hmZ : (rootPoly Z).Monic := Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _
  have hdZ : (rootPoly Z).natDegree = n := by simp [rootPoly]
  have hle4 : Erdos114.lemniscateLength (rootPoly Z) ≤ ENNReal.ofReal 4 := by
    rw [lemniscateLength_eq_arcSet_Ioo hn hmZ hdZ]
    refine (arcSet_measure_Ioo_le_of_ball_cover hn hmZ hdZ le_rfl le_rfl hr_pos.le hcover).trans ?_
    have hcalc : 8 * (n : ℝ) ^ 2 * r = 4 := by
      dsimp only [r]
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp; ring
    rw [hcalc]
  have hzero_poly : rootPoly (0 : Fin n → ℂ) = X ^ n := by
    simp [rootPoly]
  rw [hzero_poly, lemniscateLength_X_pow hn]
  exact hle4.trans (ENNReal.ofReal_le_ofReal (by linarith [Real.pi_gt_three]))

/-- **Full Eremenko–Hayman Lemma 4 (Existence of an extremal monic polynomial in every degree `n ≥ 1`):** -/
theorem exists_extremal_monic_poly (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℂ[X], p.Monic ∧ p.natDegree = n ∧
      ∀ q : ℂ[X], q.Monic → q.natDegree = n →
        Erdos114.lemniscateLength q ≤ Erdos114.lemniscateLength p := by
  obtain ⟨R, hR, hcut⟩ := lemniscateLength_rootPoly_le_of_far_root hn
  have hcont := continuous_lemniscateLength_rootPoly hn
  have htrans : ∀ Z : Fin n → ℂ,
      Erdos114.lemniscateLength (rootPoly (fun i => Z i - Z ⟨0, by omega⟩)) =
        Erdos114.lemniscateLength (rootPoly Z) := by
    intro Z
    let c := Z ⟨0, by omega⟩
    let f : ℂ ≃ᵢ ℂ := IsometryEquiv.addRight c
    have hs : Erdos114.lemniscate (rootPoly (fun i => Z i - c)) = f ⁻¹' Erdos114.lemniscate (rootPoly Z) := by
      ext z
      change ‖(rootPoly _).eval z‖ = 1 ↔ ‖(rootPoly Z).eval (z + c)‖ = 1
      simp only [rootPoly, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      have hh : ∀ i : Fin n, z - (Z i - c) = z + c - Z i := fun i => by ring
      simp only [hh]
    rw [Erdos114.lemniscateLength, Erdos114.lemniscateLength, hs, IsometryEquiv.hausdorffMeasure_preimage]
  let K : Set (Fin n → ℂ) := Metric.closedBall 0 R ∩ {Z : Fin n → ℂ | Z ⟨0, by omega⟩ = 0}
  have hK : IsCompact K := (isCompact_closedBall (0 : Fin n → ℂ) R).inter_right
    (isClosed_eq (continuous_apply (⟨0, by omega⟩ : Fin n)) continuous_const)
  have hz : (0 : Fin n → ℂ) ∈ K := ⟨by simpa [Metric.mem_closedBall] using hR, rfl⟩
  obtain ⟨Z, _, hZmax⟩ := hK.exists_isMaxOn ⟨0, hz⟩ hcont.continuousOn
  have hZall : ∀ W : Fin n → ℂ, Erdos114.lemniscateLength (rootPoly W) ≤ Erdos114.lemniscateLength (rootPoly Z) := by
    intro W
    let V : Fin n → ℂ := fun i => W i - W ⟨0, by omega⟩
    have hv : V ⟨0, by omega⟩ = 0 := sub_self _
    rw [← htrans W]
    change Erdos114.lemniscateLength (rootPoly V) ≤ Erdos114.lemniscateLength (rootPoly Z)
    by_cases hV : V ∈ K
    · exact hZmax hV
    · have hlarge : ∃ i : Fin n, R < ‖V i‖ := by
        by_contra hall; push Not at hall
        apply hV
        refine ⟨?_, hv⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (pi_norm_le_iff_of_nonneg hR).mpr hall
      exact (hcut V hv hlarge).trans (hZmax hz)
  refine ⟨rootPoly Z, Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _,
    by simp [rootPoly], fun q hqm hqd => ?_⟩
  have hsplit := IsAlgClosed.splits q
  have hcard : q.roots.card = n := by rw [IsAlgClosed.card_roots_eq_natDegree, hqd]
  obtain ⟨l, hl⟩ := Quotient.exists_rep q.roots
  change (l : Multiset ℂ) = q.roots at hl
  have hlen : l.length = n := by rw [← Multiset.coe_card, hl, hcard]
  let W : Fin n → ℂ := fun i => l[i.1]'(by omega)
  have hWq : rootPoly W = q := by
    have hfac := hsplit.eq_prod_roots_of_monic hqm
    have hlist : rootPoly W = (l.map (fun r => X - C r)).prod := by
      unfold rootPoly
      rw [← List.prod_ofFn]
      congr 1
      apply List.ext_getElem (by simp [hlen])
      intro i hi1 hi2
      simp [W]
    rw [hlist, ← Multiset.prod_coe, ← Multiset.map_coe, hl, ← hfac]
  rw [← hWq]
  exact hZall W

end

end OMA.Erdos114Lemma4
end Lemma4Part

section Lemma5Part
/-
Eremenko-Hayman Lemma 5 (Zero-Beltrami Finite-Dimensional Proof)

We prove that for every degree `n ≥ 1`, every monic degree-`n` polynomial `p₀` maximizing
`Erdos114.lemniscateLength` has all of its finite critical values on the unit circle `S¹`:

  `∀ x : ℂ, p₀.derivative.IsRoot x → ‖p₀.eval x‖ = 1`.

This proof avoids the Measurable Riemann Mapping Theorem / Beltrami equation entirely:
1. Subharmonic mean-value inequality on a disk via Mathlib's Herglotz-Riesz / Poisson integral.
2. Strict equality rigidity for circle averages of norms of holomorphic functions.
3. Finite-dimensional holomorphic IFT on the critical-value map `(ζ₂,…,ζᵣ,c) ↦ (P(ζ₁),…,P(ζᵣ))`.
4. Local holomorphic root branches via 2D triangular IFT on `(lam, z) ↦ (lam, (p lam).eval z)`.
5. Tonelli swap against the circle-integral length formula + equality rigidity forcing
   `(p lam).comp (X + C (c lam)) = p₀` on a disk, contradicting finiteness of critical values.
-/

open Polynomial MeasureTheory Metric Set Topology Complex Real
open scoped ENNReal

namespace OMA.Erdos114Lemma5

/-- Sum of `‖p'(z)‖⁻¹` over the roots `z` of `p(z) = w` (counted with multiplicity). -/
noncomputable def fiberInvDerivSum (p : ℂ[X]) (w : ℂ) : ℝ :=
  ((p - C w).roots.map (fun z => ‖p.derivative.eval z‖⁻¹)).sum

/-- Circle integrand matching `OMA.Erdos114Lemma4.circleIntegrand`. -/
noncomputable def circleIntegrand (p : ℂ[X]) (θ : ℝ) : ℝ :=
  ((p - C (Complex.exp ((θ : ℂ) * Complex.I))).roots.map
    (fun z => ‖p.derivative.eval z‖⁻¹)).sum

lemma circleIntegrand_eq_fiberInvDerivSum (p : ℂ[X]) (θ : ℝ) :
    circleIntegrand p θ = fiberInvDerivSum p (Complex.exp ((θ : ℂ) * Complex.I)) := rfl

lemma fiberInvDerivSum_nonneg (p : ℂ[X]) (w : ℂ) : 0 ≤ fiberInvDerivSum p w := by
  unfold fiberInvDerivSum
  exact Multiset.sum_nonneg fun x hx => by
    rcases Multiset.mem_map.mp hx with ⟨z, _, rfl⟩
    positivity

/- Section 1: Poisson Integral & Subharmonic Mean-Value Inequality on a Disk -/

private lemma circleAverage_norm_sq (w₀ : ℂ) (ρ : ℝ) :
    Real.circleAverage (fun z : ℂ => ‖z‖ ^ 2) w₀ ρ = ‖w₀‖ ^ 2 + ρ ^ 2 := by
  rw [Real.circleAverage_def, smul_eq_mul]
  have hfn : ∀ θ : ℝ, ‖circleMap w₀ ρ θ‖ ^ 2 =
      (‖w₀‖ ^ 2 + ρ ^ 2) + (2 * ρ * w₀.re) * Real.cos θ + (2 * ρ * w₀.im) * Real.sin θ := by
    intro θ
    rw [circleMap, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero]
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hcs := Real.cos_sq_add_sin_sq θ
    nlinarith
  simp_rw [hfn]
  have h1 : IntervalIntegrable (fun _ : ℝ => ‖w₀‖ ^ 2 + ρ ^ 2) volume 0 (2 * Real.pi) :=
    intervalIntegrable_const
  have h2 : IntervalIntegrable (fun θ : ℝ => (2 * ρ * w₀.re) * Real.cos θ) volume 0 (2 * Real.pi) :=
    (Real.continuous_cos.const_mul _).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun θ : ℝ => (2 * ρ * w₀.im) * Real.sin θ) volume 0 (2 * Real.pi) :=
    (Real.continuous_sin.const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos, integral_sin]
  simp only [Real.sin_two_pi, Real.sin_zero, sub_self, mul_zero, Real.cos_two_pi, Real.cos_zero,
    add_zero, sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

private lemma circleAverage_poissonKernel_eq_one {R : ℝ} {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    Real.circleAverage (poissonKernel 0 w) 0 R = 1 := by
  have hconst : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) (ball 0 R) :=
    (differentiableOn_const (1 : ℂ)).diffContOnCl
  have h := hconst.circleAverage_poissonKernel_smul hw
  have hre := congrArg Complex.re h
  have hint : CircleIntegrable (poissonKernel 0 w • fun _ : ℂ => (1 : ℂ)) 0 R := by
    apply ContinuousOn.circleIntegrable (pos_of_mem_ball hw).le
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    have hkc : ContinuousOn (fun z => (herglotzRieszKernel 0 w z).re) (sphere 0 R) := by
      have hc := continuousOn_herglotzRieszKernel_sphere hw
      rw [abs_of_pos (pos_of_mem_ball hw)] at hc
      exact Complex.continuous_re.comp_continuousOn hc
    exact hkc.smul continuousOn_const
  rw [← Complex.reCLM_apply, ← Complex.reCLM.circleAverage_comp_comm hint] at hre
  simpa [Function.comp_def] using hre

private lemma poissonKernel_pos_on_sphere {R : ℝ} {w ζ : ℂ}
    (hw : w ∈ ball (0 : ℂ) R) (hζ : ζ ∈ sphere (0 : ℂ) R) :
    0 < poissonKernel 0 w ζ := by
  rw [poissonKernel_def]
  simp only [sub_zero]
  have hR : 0 < R := pos_of_mem_ball hw
  have hζn : ‖ζ‖ = R := by simpa [mem_sphere_zero_iff_norm] using hζ
  have hwn : ‖w‖ < R := by simpa [mem_ball_zero_iff] using hw
  have hnum : 0 < ‖ζ‖ ^ 2 - ‖w‖ ^ 2 := by
    rw [hζn]; nlinarith [norm_nonneg w]
  have hden : 0 < ‖ζ - w‖ ^ 2 := by
    have hne : ζ - w ≠ 0 := by
      intro h; have : ‖ζ‖ = ‖w‖ := by rw [sub_eq_zero.mp h]
      linarith
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  exact div_pos hnum hden

open Classical in
private noncomputable def poissonExt (u : ℂ → ℝ) (R : ℝ) (w : ℂ) : ℝ :=
  if w ∈ ball (0 : ℂ) R then Real.circleAverage (poissonKernel 0 w • u) 0 R else u w

private lemma poissonExt_of_mem {u : ℂ → ℝ} {R : ℝ} {w : ℂ} (hw : w ∈ ball (0 : ℂ) R) :
    poissonExt u R w = Real.circleAverage (poissonKernel 0 w • u) 0 R := by
  classical simp [poissonExt, hw]

private lemma poissonExt_of_not_mem {u : ℂ → ℝ} {R : ℝ} {w : ℂ} (hw : w ∉ ball (0 : ℂ) R) :
    poissonExt u R w = u w := by
  classical simp [poissonExt, hw]

private lemma poissonExt_circleAverage_eq {u : ℂ → ℝ} {R : ℝ}
    (hu : ContinuousOn u (closedBall 0 R)) {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closedBall z ρ ⊆ ball 0 R) :
    Real.circleAverage (poissonExt u R) z ρ = poissonExt u R z := by
  have hz : z ∈ ball (0 : ℂ) R := hsub (mem_closedBall_self hρ.le)
  have hR : 0 < R := pos_of_mem_ball hz
  have huc : CircleIntegrable (fun ζ : ℂ => (u ζ : ℂ)) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact Complex.continuous_ofReal.comp_continuousOn (hu.mono sphere_subset_closedBall)
  have hur : CircleIntegrable u 0 R :=
    (hu.mono sphere_subset_closedBall).circleIntegrable hR.le
  let F : ℂ → ℂ := fun w =>
    Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (u ζ : ℂ)) 0 R
  have hFdiff : DifferentiableOn ℂ F (ball 0 R) :=
    differentiableOn_circleAverage_herglotzRieszKernel_smul huc
  have hFball : DiffContOnCl ℂ F (ball z |ρ|) := by
    rw [abs_of_pos hρ]
    refine ⟨hFdiff.mono (ball_subset_closedBall.trans hsub), ?_⟩
    rw [closure_ball z hρ.ne']
    exact (hFdiff.mono hsub).continuousOn
  have hFavg : Real.circleAverage F z ρ = F z := hFball.circleAverage
  have hFre : ∀ w ∈ ball (0 : ℂ) R, (F w).re = poissonExt u R w := by
    intro w hw
    rw [poissonExt_of_mem hw]
    dsimp only [F]
    rw [re_circleAverage_herglotzRieszKernel_smul hur hw, poissonKernel_eq_re_herglotzRieszKernel]
  have hFint : CircleIntegrable F z ρ :=
    ((hFdiff.mono hsub).continuousOn.mono sphere_subset_closedBall).circleIntegrable hρ.le
  have hcomm := Complex.reCLM.circleAverage_comp_comm hFint
  have hcongr : Real.circleAverage (poissonExt u R) z ρ =
      Real.circleAverage (Complex.reCLM ∘ F) z ρ := by
    apply Real.circleAverage_congr_sphere
    intro x hx
    rw [abs_of_pos hρ] at hx
    exact (hFre x (hsub (sphere_subset_closedBall hx))).symm
  rw [hcongr, hcomm, hFavg]
  exact hFre z hz

private lemma poissonExt_continuousOn {u : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hu : ContinuousOn u (closedBall 0 R)) :
    ContinuousOn (poissonExt u R) (closedBall 0 R) := by
  have hur : CircleIntegrable u 0 R :=
    (hu.mono sphere_subset_closedBall).circleIntegrable hR.le
  have huc : CircleIntegrable (fun ζ : ℂ => (u ζ : ℂ)) 0 R :=
    (Complex.continuous_ofReal.comp_continuousOn
      (hu.mono sphere_subset_closedBall)).circleIntegrable hR.le
  let F : ℂ → ℂ := fun w =>
    Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (u ζ : ℂ)) 0 R
  have hFcont : ContinuousOn F (ball 0 R) :=
    (differentiableOn_circleAverage_herglotzRieszKernel_smul huc).continuousOn
  have hFre : ∀ w ∈ ball (0 : ℂ) R, (F w).re = poissonExt u R w := by
    intro w hw
    rw [poissonExt_of_mem hw]
    dsimp only [F]
    rw [re_circleAverage_herglotzRieszKernel_smul hur hw, poissonKernel_eq_re_herglotzRieszKernel]
  intro w₀ hw₀
  by_cases hwin : w₀ ∈ ball (0 : ℂ) R
  · have hcontF : ContinuousAt (fun w => (F w).re) w₀ :=
      (Complex.continuous_re.comp_continuousOn hFcont).continuousAt (isOpen_ball.mem_nhds hwin)
    have heq : poissonExt u R =ᶠ[𝓝 w₀] fun w => (F w).re := by
      filter_upwards [isOpen_ball.mem_nhds hwin] with w hw
      exact (hFre w hw).symm
    exact (hcontF.congr heq.symm).continuousWithinAt
  · have hζ₀ : w₀ ∈ sphere (0 : ℂ) R := by
      rw [mem_closedBall, dist_zero_right] at hw₀
      rw [mem_ball, dist_zero_right, not_lt] at hwin
      rw [mem_sphere_zero_iff_norm]; linarith
    have hval0 : poissonExt u R w₀ = u w₀ := poissonExt_of_not_mem hwin
    rw [ContinuousWithinAt, hval0, Metric.tendsto_nhds]
    intro ε hε
    have huw₀ := Metric.continuousWithinAt_iff.mp (hu w₀ hw₀) (ε / 2) (by linarith)
    rcases huw₀ with ⟨δ, hδpos, hδ⟩
    have hcomp : IsCompact (sphere (0 : ℂ) R) := isCompact_sphere 0 R
    have hcont_diff : ContinuousOn (fun ζ => |u ζ - u w₀|) (sphere 0 R) :=
      ((hu.mono sphere_subset_closedBall).sub continuousOn_const).abs
    obtain ⟨M₀, hM₀⟩ := hcomp.exists_bound_of_continuousOn hcont_diff
    let M : ℝ := max M₀ 1
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hMbd : ∀ ζ ∈ sphere (0 : ℂ) R, |u ζ - u w₀| ≤ M := by
      intro ζ hζ
      have h1 := hM₀ ζ hζ
      rw [Real.norm_eq_abs, abs_abs] at h1
      exact h1.trans (le_max_left _ _)
    have hcont_rad : ContinuousAt (fun w : ℂ => 4 * M * (R ^ 2 - ‖w‖ ^ 2) / δ ^ 2) w₀ := by
      fun_prop
    have hrad0 : 4 * M * (R ^ 2 - ‖w₀‖ ^ 2) / δ ^ 2 = 0 := by
      rw [mem_sphere_zero_iff_norm.mp hζ₀]; ring
    have hη_ev : ∀ᶠ w in 𝓝 w₀, dist (4 * M * (R ^ 2 - ‖w‖ ^ 2) / δ ^ 2) 0 < ε / 2 := by
      have := Metric.tendsto_nhds.mp hcont_rad.tendsto (ε / 2) (by linarith)
      filter_upwards [this] with w hw
      rwa [hrad0] at hw
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds w₀ (by linarith : 0 < δ / 2)),
      nhdsWithin_le_nhds hη_ev, self_mem_nhdsWithin] with w hwball hwrad hwcl
    by_cases hwb : w ∈ ball (0 : ℂ) R
    · rw [poissonExt_of_mem hwb, Real.dist_eq]
      have hP1 : Real.circleAverage (poissonKernel 0 w) 0 R = 1 :=
        circleAverage_poissonKernel_eq_one hwb
      have hPcont : ContinuousOn (poissonKernel 0 w) (sphere 0 R) := by
        rw [poissonKernel_eq_re_herglotzRieszKernel]
        have hc := continuousOn_herglotzRieszKernel_sphere hwb
        rw [abs_of_pos hR] at hc
        exact Complex.continuous_re.comp_continuousOn hc
      have hPu_int : CircleIntegrable (poissonKernel 0 w • u) 0 R :=
        (hPcont.smul (hu.mono sphere_subset_closedBall)).circleIntegrable hR.le
      have hPc_int : CircleIntegrable (fun ζ => poissonKernel 0 w ζ * u w₀) 0 R :=
        (hPcont.mul continuousOn_const).circleIntegrable hR.le
      have hsub_eq : Real.circleAverage (poissonKernel 0 w • u) 0 R - u w₀ =
          Real.circleAverage (fun ζ => poissonKernel 0 w ζ * (u ζ - u w₀)) 0 R := by
        have h2 : Real.circleAverage (fun ζ => poissonKernel 0 w ζ * u w₀) 0 R = u w₀ := by
          have : (fun ζ => poissonKernel 0 w ζ * u w₀) = fun ζ => u w₀ • poissonKernel 0 w ζ := by
            ext ζ; simp [mul_comm]
          rw [this, Real.circleAverage_fun_smul, hP1, smul_eq_mul, mul_one]
        calc Real.circleAverage (poissonKernel 0 w • u) 0 R - u w₀
            = Real.circleAverage (poissonKernel 0 w • u) 0 R -
                Real.circleAverage (fun ζ => poissonKernel 0 w ζ * u w₀) 0 R := by rw [h2]
          _ = Real.circleAverage (fun ζ => (poissonKernel 0 w • u) ζ -
                poissonKernel 0 w ζ * u w₀) 0 R := (Real.circleAverage_fun_sub hPu_int hPc_int).symm
          _ = Real.circleAverage (fun ζ => poissonKernel 0 w ζ * (u ζ - u w₀)) 0 R := by
                congr 1; ext ζ; simp only [smul_eq_mul, Pi.mul_apply]; ring
      rw [hsub_eq]
      have habs_le := Real.abs_circleAverage_le_circleAverage_abs
        (f := fun ζ => poissonKernel 0 w ζ * (u ζ - u w₀)) (c := 0) (R := R)
      let C : ℝ := 4 * M * (R ^ 2 - ‖w‖ ^ 2) / δ ^ 2
      have hCnn : 0 ≤ C := by
        have hwn : ‖w‖ < R := by simpa [mem_ball_zero_iff] using hwb
        have hsq : 0 ≤ R ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
        positivity
      have hpt : ∀ ζ ∈ sphere (0 : ℂ) |R|,
          |poissonKernel 0 w ζ * (u ζ - u w₀)| ≤ (ε / 2) * poissonKernel 0 w ζ + C := by
        intro ζ hζ
        rw [abs_of_pos hR] at hζ
        have hPpos : 0 < poissonKernel 0 w ζ := poissonKernel_pos_on_sphere hwb hζ
        rw [abs_mul, abs_of_pos hPpos]
        by_cases hclose : dist ζ w₀ < δ
        · have hud : |u ζ - u w₀| < ε / 2 := by
            simpa [Real.dist_eq] using hδ (sphere_subset_closedBall hζ) hclose
          nlinarith
        · push Not at hclose
          have hwdist : dist w w₀ < δ / 2 := by simpa [Metric.mem_ball] using hwball
          have htri := dist_triangle ζ w w₀
          have hζw : δ / 2 ≤ ‖ζ - w‖ := by
            rw [← dist_eq_norm]; linarith
          have hPbd : poissonKernel 0 w ζ ≤ (R ^ 2 - ‖w‖ ^ 2) / (δ / 2) ^ 2 := by
            rw [poissonKernel_def]
            simp only [sub_zero, mem_sphere_zero_iff_norm.mp hζ]
            have hwn : ‖w‖ < R := by simpa [mem_ball_zero_iff] using hwb
            have hsq : 0 ≤ R ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
            gcongr
          have hbd1 : poissonKernel 0 w ζ * |u ζ - u w₀| ≤ C := by
            have h1 : poissonKernel 0 w ζ * |u ζ - u w₀| ≤
                ((R ^ 2 - ‖w‖ ^ 2) / (δ / 2) ^ 2) * M :=
              mul_le_mul hPbd (hMbd ζ hζ) (abs_nonneg _) (by
                have hwn : ‖w‖ < R := by simpa [mem_ball_zero_iff] using hwb
                have hsq : 0 ≤ R ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
                positivity)
            have h2 : ((R ^ 2 - ‖w‖ ^ 2) / (δ / 2) ^ 2) * M = C := by
              dsimp only [C]; field_simp [hδpos.ne']; ring
            linarith
          nlinarith
      have hint_l : CircleIntegrable (fun ζ => |poissonKernel 0 w ζ * (u ζ - u w₀)|) 0 R :=
        ((hPcont.mul ((hu.mono sphere_subset_closedBall).sub continuousOn_const)).abs).circleIntegrable hR.le
      have hint_r : CircleIntegrable (fun ζ => (ε / 2) * poissonKernel 0 w ζ + C) 0 R :=
        ((hPcont.const_mul (ε / 2)).add continuousOn_const).circleIntegrable hR.le
      have hmono := Real.circleAverage_mono hint_l hint_r hpt
      have hrhs : Real.circleAverage (fun ζ => (ε / 2) * poissonKernel 0 w ζ + C) 0 R =
          ε / 2 + C := by
        rw [Real.circleAverage_fun_add ((hPcont.const_mul _).circleIntegrable hR.le)
          (continuousOn_const.circleIntegrable hR.le),
          Real.circleAverage_const]
        have : Real.circleAverage (fun ζ => (ε / 2) * poissonKernel 0 w ζ) 0 R = ε / 2 := by
          change Real.circleAverage (fun ζ => (ε / 2) • poissonKernel 0 w ζ) 0 R = ε / 2
          rw [Real.circleAverage_fun_smul, hP1, smul_eq_mul, mul_one]
        rw [this]
      have hC_lt : C < ε / 2 := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hCnn] at hwrad; exact hwrad
      calc |Real.circleAverage (fun ζ => poissonKernel 0 w ζ * (u ζ - u w₀)) 0 R|
          ≤ Real.circleAverage (fun ζ => |poissonKernel 0 w ζ * (u ζ - u w₀)|) 0 R := habs_le
        _ ≤ ε / 2 + C := by rw [← hrhs]; exact hmono
        _ < ε := by linarith
    · rw [poissonExt_of_not_mem hwb]
      have hwdist : dist w w₀ < δ := by
        have h1 : dist w w₀ < δ / 2 := by simpa [Metric.mem_ball] using hwball
        linarith
      have := hδ hwcl hwdist
      linarith

private theorem subharmonic_le_poissonExt {u : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hu : ContinuousOn u (closedBall 0 R))
    (hsub : ∀ z ∈ ball (0 : ℂ) R, ∃ ρ₀ > 0, ∀ ρ, 0 < ρ → ρ < ρ₀ →
      closedBall z ρ ⊆ ball 0 R → u z ≤ Real.circleAverage u z ρ) :
    ∀ w ∈ closedBall (0 : ℂ) R, u w ≤ poissonExt u R w := by
  have hPcont : ContinuousOn (poissonExt u R) (closedBall 0 R) :=
    poissonExt_continuousOn hR hu
  intro w hw
  suffices hε : ∀ ε : ℝ, 0 < ε → u w - poissonExt u R w + ε * ‖w‖ ^ 2 ≤ ε * R ^ 2 by
    by_contra hlt
    push Not at hlt
    let ε : ℝ := (u w - poissonExt u R w) / (2 * R ^ 2)
    have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
    have h1 := hε ε hεpos
    have h2 : ε * R ^ 2 = (u w - poissonExt u R w) / 2 := by
      dsimp only [ε]; field_simp [hR.ne']
    have h3 : 0 ≤ ε * ‖w‖ ^ 2 := by positivity
    linarith
  intro ε hε
  let v : ℂ → ℝ := fun z => u z - poissonExt u R z + ε * ‖z‖ ^ 2
  have hv_cont : ContinuousOn v (closedBall 0 R) :=
    (hu.sub hPcont).add ((continuous_norm.pow 2).continuousOn.const_mul ε)
  obtain ⟨w₀, hw₀_mem, hw₀_max⟩ :=
    (isCompact_closedBall (0 : ℂ) R).exists_isMaxOn ⟨0, mem_closedBall_self hR.le⟩ hv_cont
  have hw₀_not_in : w₀ ∉ ball (0 : ℂ) R := by
    intro hw₀_in
    obtain ⟨ρ₀, hρ₀_pos, hρ₀⟩ := hsub w₀ hw₀_in
    have hdist : 0 < R - ‖w₀‖ := by
      have : ‖w₀‖ < R := by simpa [mem_ball_zero_iff] using hw₀_in
      linarith
    let ρ : ℝ := min (ρ₀ / 2) ((R - ‖w₀‖) / 2)
    have hρpos : 0 < ρ := lt_min (by linarith) (by linarith)
    have hρlt : ρ < ρ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hcb : closedBall w₀ ρ ⊆ ball 0 R := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [mem_ball_zero_iff]
      have hρ2 : ρ ≤ (R - ‖w₀‖) / 2 := min_le_right _ _
      calc ‖z‖ = ‖(z - w₀) + w₀‖ := by ring_nf
        _ ≤ ‖z - w₀‖ + ‖w₀‖ := norm_add_le _ _
        _ ≤ ρ + ‖w₀‖ := by linarith
        _ < R := by linarith
    have hu_le : u w₀ ≤ Real.circleAverage u w₀ ρ := hρ₀ ρ hρpos hρlt hcb
    have hP_eq : Real.circleAverage (poissonExt u R) w₀ ρ = poissonExt u R w₀ :=
      poissonExt_circleAverage_eq hu hρpos hcb
    have hsq_eq : Real.circleAverage (fun z => ε * ‖z‖ ^ 2) w₀ ρ = ε * (‖w₀‖ ^ 2 + ρ ^ 2) := by
      change Real.circleAverage (fun z => ε • ‖z‖ ^ 2) w₀ ρ = ε * (‖w₀‖ ^ 2 + ρ ^ 2)
      rw [Real.circleAverage_fun_smul, circleAverage_norm_sq, smul_eq_mul]
    have hsp_sub : sphere w₀ ρ ⊆ closedBall 0 R :=
      (sphere_subset_closedBall.trans hcb).trans ball_subset_closedBall
    have hiu : CircleIntegrable u w₀ ρ := (hu.mono hsp_sub).circleIntegrable hρpos.le
    have hiP : CircleIntegrable (poissonExt u R) w₀ ρ := (hPcont.mono hsp_sub).circleIntegrable hρpos.le
    have hiDiff : CircleIntegrable (fun z => u z - poissonExt u R z) w₀ ρ := hiu.sub hiP
    have hisq : CircleIntegrable (fun z => ε * ‖z‖ ^ 2) w₀ ρ :=
      ((continuous_norm.pow 2).continuousOn.const_mul ε).circleIntegrable hρpos.le
    have hv_avg : Real.circleAverage v w₀ ρ =
        Real.circleAverage u w₀ ρ - Real.circleAverage (poissonExt u R) w₀ ρ +
          Real.circleAverage (fun z => ε * ‖z‖ ^ 2) w₀ ρ := by
      change Real.circleAverage (fun z => (u z - poissonExt u R z) + ε * ‖z‖ ^ 2) w₀ ρ = _
      rw [Real.circleAverage_fun_add hiDiff hisq, Real.circleAverage_fun_sub hiu hiP]
    have hv_le : Real.circleAverage v w₀ ρ ≤ v w₀ := by
      apply Real.circleAverage_mono_on_of_le_circle (hiDiff.add hisq)
      intro x hx
      rw [abs_of_pos hρpos] at hx
      exact hw₀_max (hsp_sub hx)
    have hstrict : v w₀ < Real.circleAverage v w₀ ρ := by
      rw [hv_avg, hP_eq, hsq_eq]
      dsimp only [v]
      nlinarith [sq_pos_of_pos hρpos]
    linarith
  have hw₀_norm : ‖w₀‖ = R := by
    rw [mem_closedBall, dist_zero_right] at hw₀_mem
    rw [mem_ball, dist_zero_right, not_lt] at hw₀_not_in
    linarith
  have hv_w₀ : v w₀ = ε * R ^ 2 := by
    dsimp only [v]
    rw [poissonExt_of_not_mem hw₀_not_in, sub_self, zero_add, hw₀_norm]
  calc u w - poissonExt u R w + ε * ‖w‖ ^ 2 = v w := rfl
    _ ≤ v w₀ := hw₀_max hw
    _ = ε * R ^ 2 := hv_w₀

private theorem subharmonic_mean_value {u : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hu : ContinuousOn u (closedBall 0 R))
    (hsub : ∀ z ∈ ball (0 : ℂ) R, ∃ ρ₀ > 0, ∀ ρ, 0 < ρ → ρ < ρ₀ →
      closedBall z ρ ⊆ ball 0 R → u z ≤ Real.circleAverage u z ρ) :
    u 0 ≤ Real.circleAverage u 0 R := by
  have h := subharmonic_le_poissonExt hR hu hsub 0 (mem_closedBall_self hR.le)
  rw [poissonExt_of_mem (mem_ball_self hR)] at h
  have hcongr : Real.circleAverage (poissonKernel 0 0 • u) 0 R = Real.circleAverage u 0 R := by
    apply Real.circleAverage_congr_sphere
    intro ζ hζ
    rw [abs_of_pos hR, mem_sphere_zero_iff_norm] at hζ
    simp [poissonKernel_def, hζ, hR.ne']
  rwa [hcongr] at h

private theorem subharmonic_local_circleAverage_eq {u : ℂ → ℝ} {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρR : ρ < R)
    (hu : ContinuousOn u (closedBall 0 R))
    (hsub : ∀ z ∈ ball (0 : ℂ) R, ∃ ρ₀ > 0, ∀ r, 0 < r → r < ρ₀ →
      closedBall z r ⊆ ball 0 R → u z ≤ Real.circleAverage u z r)
    (heq : u 0 = Real.circleAverage u 0 R)
    (hloc : u 0 ≤ Real.circleAverage u 0 ρ) :
    u 0 = Real.circleAverage u 0 ρ := by
  have hPcont : ContinuousOn (poissonExt u R) (closedBall 0 R) :=
    poissonExt_continuousOn hR hu
  have hcb : closedBall (0 : ℂ) ρ ⊆ ball 0 R := closedBall_subset_ball hρR
  have hsp : sphere (0 : ℂ) ρ ⊆ closedBall 0 R :=
    (sphere_subset_closedBall.trans hcb).trans ball_subset_closedBall
  have hmono : Real.circleAverage u 0 ρ ≤ Real.circleAverage (poissonExt u R) 0 ρ := by
    apply Real.circleAverage_mono ((hu.mono hsp).circleIntegrable hρ.le)
      ((hPcont.mono hsp).circleIntegrable hρ.le)
    intro x hx
    rw [abs_of_pos hρ] at hx
    exact subharmonic_le_poissonExt hR hu hsub x (hsp hx)
  have hPavg : Real.circleAverage (poissonExt u R) 0 ρ = poissonExt u R 0 :=
    poissonExt_circleAverage_eq hu hρ hcb
  have hP0 : poissonExt u R 0 = Real.circleAverage u 0 R := by
    rw [poissonExt_of_mem (mem_ball_self hR)]
    apply Real.circleAverage_congr_sphere
    intro ζ hζ
    rw [abs_of_pos hR, mem_sphere_zero_iff_norm] at hζ
    simp [poissonKernel_def, hζ, hR.ne']
  linarith

/- Section 2: Strict Equality Rigidity for Holomorphic Circle Averages -/

private lemma norm_le_circleAverage_norm {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : DiffContOnCl ℂ f (ball c ρ)) :
    ‖f c‖ ≤ Real.circleAverage (fun z => ‖f z‖) c ρ := by
  have hf' : DiffContOnCl ℂ f (ball c |ρ|) := by rwa [abs_of_pos hρ]
  have havg : Real.circleAverage f c ρ = f c := hf'.circleAverage
  rw [← havg, Real.circleAverage_def, Real.circleAverage_def, smul_eq_mul, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr Real.two_pi_pos)]
  gcongr
  exact intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le

private lemma const_of_norm_circleAverage_eq {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : DiffContOnCl ℂ f (ball 0 ρ)) (hf0 : f 0 ≠ 0)
    (heq : ‖f 0‖ = Real.circleAverage (fun z => ‖f z‖) 0 ρ) :
    ∀ w ∈ ball (0 : ℂ) ρ, f w = f 0 := by
  let g : ℂ → ℂ := fun z => f z / f 0
  have hg : DiffContOnCl ℂ g (ball 0 ρ) := ⟨hf.1.div_const (f 0), hf.2.div_const (f 0)⟩
  have hg0 : g 0 = 1 := div_self hf0
  have hg_cont_sp : ContinuousOn g (sphere 0 ρ) := by
    have h1 := hg.continuousOn
    rw [closure_ball 0 hρ.ne'] at h1
    exact h1.mono sphere_subset_closedBall
  have hgnorm_avg : Real.circleAverage (fun z => ‖g z‖) 0 ρ = 1 := by
    have : (fun z => ‖g z‖) = fun z => ‖f 0‖⁻¹ • ‖f z‖ := by
      ext z; simp [g, div_eq_inv_mul]
    rw [this, Real.circleAverage_fun_smul, ← heq, smul_eq_mul,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hf0)]
  have hgre_avg : Real.circleAverage (fun z => (g z).re) 0 ρ = 1 := by
    have hg' : DiffContOnCl ℂ g (ball 0 |ρ|) := by rwa [abs_of_pos hρ]
    have havg : Real.circleAverage g 0 ρ = g 0 := hg'.circleAverage
    have hcomm := Complex.reCLM.circleAverage_comp_comm (hg_cont_sp.circleIntegrable hρ.le)
    have := congrArg Complex.re havg
    rw [← Complex.reCLM_apply, ← hcomm, hg0] at this
    simpa [Function.comp_def] using this
  have hdiff_zero : Real.circleAverage (fun z => ‖g z‖ - (g z).re) 0 ρ = 0 := by
    have hre_int : CircleIntegrable (fun z => (g z).re) 0 ρ :=
      (Complex.continuous_re.comp_continuousOn hg_cont_sp).circleIntegrable hρ.le
    rw [Real.circleAverage_fun_sub (hg_cont_sp.norm.circleIntegrable hρ.le) hre_int,
      hgnorm_avg, hgre_avg, sub_self]
  have him_sphere : ∀ z ∈ sphere (0 : ℂ) ρ, (g z).im = 0 := by
    have hint0 : ∫ θ in (0 : ℝ)..2 * Real.pi,
        (‖g (circleMap 0 ρ θ)‖ - (g (circleMap 0 ρ θ)).re) = 0 := by
      rw [Real.circleAverage_def, smul_eq_mul, mul_eq_zero] at hdiff_zero
      exact hdiff_zero.resolve_left (inv_ne_zero Real.two_pi_pos.ne')
    have hcont_θ : ContinuousOn (fun θ : ℝ => ‖g (circleMap 0 ρ θ)‖ - (g (circleMap 0 ρ θ)).re)
        (Set.Icc 0 (2 * Real.pi)) := by
      have hcm : ContinuousOn (fun θ => g (circleMap 0 ρ θ)) (Set.Icc 0 (2 * Real.pi)) :=
        hg_cont_sp.comp (continuous_circleMap 0 ρ).continuousOn fun θ _ =>
          circleMap_mem_sphere 0 hρ.le θ
      exact hcm.norm.sub (Complex.continuous_re.comp_continuousOn hcm)
    have hae : (fun θ : ℝ => ‖g (circleMap 0 ρ θ)‖ - (g (circleMap 0 ρ θ)).re)
        =ᵐ[volume.restrict (Set.Ioc 0 (2 * Real.pi))] 0 := by
      have h1 := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
        (ae_of_all _ fun θ => sub_nonneg.mpr (Complex.re_le_norm _))
        (hcont_θ.intervalIntegrable_of_Icc Real.two_pi_pos.le)).mp hint0
      simpa [min_eq_left Real.two_pi_pos.le, max_eq_right Real.two_pi_pos.le] using h1
    have hzero_θ : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        ‖g (circleMap 0 ρ θ)‖ - (g (circleMap 0 ρ θ)).re = 0 := by
      intro θ hθ
      by_contra hne
      have hnn : 0 ≤ ‖g (circleMap 0 ρ θ)‖ - (g (circleMap 0 ρ θ)).re :=
        sub_nonneg.mpr (Complex.re_le_norm _)
      have hpos : 0 < ‖g (circleMap 0 ρ θ)‖ - (g (circleMap 0 ρ θ)).re :=
        lt_of_le_of_ne hnn (Ne.symm hne)
      have hcont_at := Metric.continuousWithinAt_iff.mp (hcont_θ θ hθ)
        ((‖g (circleMap 0 ρ θ)‖ - (g (circleMap 0 ρ θ)).re) / 2) (by linarith)
      rcases hcont_at with ⟨δ, hδpos, hδ⟩
      let a := max 0 (θ - δ / 2)
      let b := min (2 * Real.pi) (θ + δ / 2)
      have hab : a < b := by
        have h0 : 0 ≤ θ := hθ.1
        have h2 : θ ≤ 2 * Real.pi := hθ.2
        have hpi := Real.two_pi_pos
        simp only [a, b, lt_min_iff, max_lt_iff]
        constructor <;> constructor <;> linarith
      have hsub : Set.Ioo a b ⊆ Set.Ioc 0 (2 * Real.pi) := fun x hx =>
        ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, le_of_lt (lt_of_lt_of_le hx.2 (min_le_left _ _))⟩
      have hvol : 0 < volume (Set.Ioo a b) := by
        rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
      have hzero_set : volume {x ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) |
          ‖g (circleMap 0 ρ x)‖ - (g (circleMap 0 ρ x)).re ≠ 0} = 0 := by
        have h2 := hae
        rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc, Filter.Eventually, mem_ae_iff] at h2
        convert h2 using 2
        ext x
        simp [and_assoc]
      have hinc : Set.Ioo a b ⊆ {x ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) |
          ‖g (circleMap 0 ρ x)‖ - (g (circleMap 0 ρ x)).re ≠ 0} := by
        intro x hx
        refine ⟨hsub hx, ?_⟩
        have hxd : dist x θ < δ := by
          rw [Real.dist_eq, abs_lt]
          have h1 : θ - δ / 2 < x := lt_of_le_of_lt (le_max_right _ _) hx.1
          have h2 : x < θ + δ / 2 := lt_of_lt_of_le hx.2 (min_le_right _ _)
          constructor <;> linarith
        have hxmem : x ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := Set.Ioc_subset_Icc_self (hsub hx)
        have hdist := hδ hxmem hxd
        rw [Real.dist_eq] at hdist
        intro h0; rw [h0, zero_sub, abs_neg, abs_of_pos hpos] at hdist; linarith
      have hle := measure_mono (μ := volume) hinc
      rw [hzero_set, nonpos_iff_eq_zero] at hle
      exact hvol.ne' hle
    intro z hz
    have hzimg : z ∈ circleMap 0 ρ '' Set.Ioc 0 (2 * Real.pi) := by
      have h1 := (periodic_circleMap 0 ρ).image_Ioc Real.two_pi_pos 0
      rw [zero_add, range_circleMap, abs_of_pos hρ] at h1
      rwa [h1]
    rcases hzimg with ⟨θ, hθmem, rfl⟩
    have h0 := hzero_θ θ ⟨hθmem.1.le, hθmem.2⟩
    have hre_eq : ‖g (circleMap 0 ρ θ)‖ = (g (circleMap 0 ρ θ)).re := sub_eq_zero.mp h0
    have hsq := Complex.sq_norm (g (circleMap 0 ρ θ))
    rw [Complex.normSq_apply, hre_eq] at hsq
    nlinarith
  have him_ball : ∀ w ∈ ball (0 : ℂ) ρ, (g w).im = 0 := by
    intro w hw
    have hp := hg.circleAverage_poissonKernel_smul hw
    have hPcont : ContinuousOn (poissonKernel 0 w) (sphere 0 ρ) := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      have hc := continuousOn_herglotzRieszKernel_sphere hw
      rw [abs_of_pos hρ] at hc
      exact Complex.continuous_re.comp_continuousOn hc
    have hint : CircleIntegrable (poissonKernel 0 w • g) 0 ρ :=
      (hPcont.smul hg_cont_sp).circleIntegrable hρ.le
    have hcomm := Complex.imCLM.circleAverage_comp_comm hint
    have h1 := congrArg Complex.im hp
    rw [← Complex.imCLM_apply, ← hcomm] at h1
    rw [← h1]
    apply Real.circleAverage_const_on_circle
    intro z hz
    rw [abs_of_pos hρ] at hz
    simp [him_sphere z hz]
  have hderiv_zero : ∀ w ∈ ball (0 : ℂ) ρ, deriv g w = 0 := by
    intro w hw
    have hdiff : DifferentiableAt ℂ g w := (hg.1 w hw).differentiableAt (isOpen_ball.mem_nhds hw)
    have hd : HasDerivAt g (deriv g w) w := hdiff.hasDerivAt
    have hreal : HasDerivAt (fun t : ℝ => (g (w + (t : ℂ))).im) (deriv g w).im 0 := by
      have h1 : HasDerivAt (fun t : ℝ => w + (t : ℂ)) (1 : ℂ) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_add w
      have hd1 : HasDerivAt g (deriv g w) (w + ((0 : ℝ) : ℂ)) := by simpa using hd
      have h2 := (hd1.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) h1
      have h3 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
      simpa [Function.comp_def] using h3
    have himag : HasDerivAt (fun t : ℝ => (g (w + (t : ℂ) * Complex.I)).im) (deriv g w).re 0 := by
      have h1 : HasDerivAt (fun t : ℝ => w + (t : ℂ) * Complex.I) Complex.I 0 := by
        simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).const_add w
      have hd2 : HasDerivAt g (deriv g w) (w + ((0 : ℝ) : ℂ) * Complex.I) := by simpa using hd
      have h2 := (hd2.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) h1
      have h3 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
      simpa [Function.comp_def, Complex.mul_im] using h3
    have h1z : (fun t : ℝ => (g (w + (t : ℂ))).im) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
      have hcont : ContinuousAt (fun t : ℝ => w + (t : ℂ)) 0 := by fun_prop
      filter_upwards [hcont.preimage_mem_nhds (by simpa using isOpen_ball.mem_nhds hw)] with t ht
      exact him_ball _ ht
    have h2z : (fun t : ℝ => (g (w + (t : ℂ) * Complex.I)).im) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
      have hcont : ContinuousAt (fun t : ℝ => w + (t : ℂ) * Complex.I) 0 := by fun_prop
      filter_upwards [hcont.preimage_mem_nhds (by simpa using isOpen_ball.mem_nhds hw)] with t ht
      exact him_ball _ ht
    have him0 : (deriv g w).im = 0 :=
      (hreal.congr_of_eventuallyEq h1z.symm).unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have hre0 : (deriv g w).re = 0 :=
      (himag.congr_of_eventuallyEq h2z.symm).unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    exact Complex.ext hre0 him0
  intro w hw
  have hgw : g w = g 0 := by
    apply (convex_ball (0 : ℂ) ρ).is_const_of_fderivWithin_eq_zero hg.1
    · intro x hx
      rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hx)
        ((hg.1 x hx).differentiableAt (isOpen_ball.mem_nhds hx))]
      ext
      have hd := ((hg.1 x hx).differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt.hasFDerivAt
      rw [hd.fderiv]
      simp [hderiv_zero x hx]
    · exact hw
    · exact mem_ball_self hρ
  rw [hg0] at hgw
  exact (div_eq_one_iff_eq hf0).mp hgw

private lemma const_of_sum_norm_circleAverage_eq {m : ℕ} {f : Fin m → ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ∀ k, DiffContOnCl ℂ (f k) (ball 0 ρ))
    (hf0 : ∀ k, f k 0 ≠ 0)
    (heq : ∑ k : Fin m, ‖f k 0‖ = Real.circleAverage (fun z => ∑ k : Fin m, ‖f k z‖) 0 ρ) :
    ∀ k (w : ℂ), w ∈ ball (0 : ℂ) ρ → f k w = f k 0 := by
  have hint : ∀ k : Fin m, CircleIntegrable (fun z => ‖f k z‖) 0 ρ := fun k => by
    have h1 := (hf k).continuousOn
    rw [closure_ball 0 hρ.ne'] at h1
    exact (h1.mono sphere_subset_closedBall).norm.circleIntegrable hρ.le
  rw [Real.circleAverage_fun_sum (fun k _ => hint k)] at heq
  have hle : ∀ k ∈ (Finset.univ : Finset (Fin m)),
      ‖f k 0‖ ≤ Real.circleAverage (fun z => ‖f k z‖) 0 ρ := fun k _ =>
    norm_le_circleAverage_norm hρ (hf k)
  have heq_each := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro k w hw
  exact const_of_norm_circleAverage_eq hρ (hf k) (hf0 k) (heq_each k (Finset.mem_univ k)) w hw

/- Section 3: Finite-Dimensional Holomorphic Critical-Value Deformation -/

private noncomputable def antiderivN (n : ℕ) (q : ℂ[X]) (c : ℂ) : ℂ[X] :=
  C c + ∑ k ∈ Finset.range n, C (q.coeff k / ((k + 1 : ℕ) : ℂ)) * X ^ (k + 1)

private lemma antiderivN_coeff (n : ℕ) (q : ℂ[X]) (c : ℂ) (j : ℕ) :
    (antiderivN n q c).coeff j =
      if j = 0 then c else if j ≤ n then q.coeff (j - 1) / (j : ℂ) else 0 := by
  unfold antiderivN
  rw [coeff_add, coeff_C, Polynomial.finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rcases j with _ | j
  · simp
  · simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add, Nat.add_one_sub_one]
    by_cases hjn : j < n
    · rw [Finset.sum_eq_single j]
      · simp [Nat.succ_le_iff.mpr hjn]
      · intro k _ hkj; simp [Ne.symm hkj]
      · intro h; exact absurd (Finset.mem_range.mpr hjn) h
    · have hle : ¬ j + 1 ≤ n := by omega
      rw [if_neg hle]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkn : k < n := Finset.mem_range.mp hk
      have hne' : j ≠ k := by omega
      simp [hne']

private lemma antiderivN_eval_zero (n : ℕ) (q : ℂ[X]) (c : ℂ) :
    (antiderivN n q c).eval 0 = c := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, antiderivN_coeff]
  simp

private lemma antiderivN_derivative {n : ℕ} {q : ℂ[X]} (hq : ∀ k, n ≤ k → q.coeff k = 0) (c : ℂ) :
    (antiderivN n q c).derivative = q := by
  ext k
  rw [coeff_derivative, antiderivN_coeff]
  by_cases hkn : k < n
  · have hle : k + 1 ≤ n := hkn
    have hne : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    simp only [Nat.succ_ne_zero, ↓reduceIte, hle, Nat.add_one_sub_one]
    push_cast at hne ⊢
    field_simp [hne]
  · have hle : ¬ k + 1 ≤ n := by omega
    simp only [Nat.succ_ne_zero, ↓reduceIte, hle, zero_mul]
    exact (hq k (by omega)).symm

private lemma eq_antiderivN_of_derivative {n : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ n) :
    p = antiderivN n p.derivative (p.eval 0) := by
  ext k
  rw [antiderivN_coeff]
  rcases k with _ | k
  · simp [Polynomial.coeff_zero_eq_eval_zero]
  · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_one_sub_one]
    by_cases hkn : k + 1 ≤ n
    · rw [if_pos hkn, coeff_derivative]
      have hne : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      push_cast at hne ⊢
      field_simp [hne]
    · rw [if_neg hkn]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

private lemma antiderivN_monic_and_degree {n : ℕ} (hn : 1 ≤ n) {q : ℂ[X]}
    (hq_deg : q.natDegree = n - 1) (hq_lc : q.leadingCoeff = (n : ℂ)) (c : ℂ) :
    (antiderivN n q c).Monic ∧ (antiderivN n q c).natDegree = n := by
  have hcoeff_n : (antiderivN n q c).coeff n = 1 := by
    rw [antiderivN_coeff]
    have hn0 : n ≠ 0 := by omega
    simp only [hn0, ↓reduceIte, le_refl]
    rw [← hq_deg, ← Polynomial.leadingCoeff, hq_lc]
    exact div_self (Nat.cast_ne_zero.mpr hn0)
  have hcoeff_gt : ∀ k, n < k → (antiderivN n q c).coeff k = 0 := by
    intro k hk
    rw [antiderivN_coeff]
    have hk0 : k ≠ 0 := by omega
    have hkn : ¬ k ≤ n := by omega
    simp [hk0, hkn]
  have hdeg : (antiderivN n q c).natDegree = n := by
    apply le_antisymm
    · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hcoeff_gt
    · exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff_n]; exact one_ne_zero)
  refine ⟨?_, hdeg⟩
  rw [Polynomial.Monic, Polynomial.leadingCoeff, hdeg, hcoeff_n]

private lemma prod_X_sub_C_pow_coeff_top {ι : Type*} (s : Finset ι) (a : ι → ℂ) (m : ι → ℕ) :
    let d := ∑ j ∈ s, m j
    let P : ℂ[X] := ∏ j ∈ s, (X - C (a j)) ^ (m j)
    P.Monic ∧ P.natDegree = d ∧
      (1 ≤ d → P.coeff (d - 1) = -∑ j ∈ s, (m j : ℂ) * a j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert i s hi ih =>
    rcases ih with ⟨ih_monic, ih_deg, ih_next⟩
    let d := ∑ j ∈ s, m j
    let P : ℂ[X] := ∏ j ∈ s, (X - C (a j)) ^ (m j)
    let Q : ℂ[X] := (X - C (a i)) ^ (m i)
    have hQ_monic : Q.Monic := (Polynomial.monic_X_sub_C (a i)).pow (m i)
    have hQ_deg : Q.natDegree = m i := by simp [Q]
    have hQ_next : ∀ k : ℕ, 1 ≤ k → ((X - C (a i)) ^ k).coeff (k - 1) = -(k : ℂ) * a i := by
      intro k
      induction k with
      | zero => intro h; omega
      | succ k ihk =>
        intro _
        simp only [Nat.add_one_sub_one]
        rw [pow_succ, mul_sub, coeff_sub, coeff_mul_C]
        cases k with
        | zero => simp
        | succ k' =>
          rw [coeff_mul_X]
          have h1 := ihk (by omega)
          have hlead : ((X - C (a i)) ^ (k' + 1)).coeff (k' + 1) = 1 := by
            let R : ℂ[X] := (X - C (a i)) ^ (k' + 1)
            have hm : R.Monic := (Polynomial.monic_X_sub_C (a i)).pow (k' + 1)
            have hd : R.natDegree = k' + 1 := by
              rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
            calc R.coeff (k' + 1) = R.leadingCoeff := by rw [Polynomial.leadingCoeff, hd]
              _ = 1 := hm.leadingCoeff
          simp only [Nat.add_one_sub_one] at h1
          rw [h1, hlead]
          push_cast; ring
    have hprod : ∏ j ∈ insert i s, (X - C (a j)) ^ (m j) = Q * P :=
      Finset.prod_insert hi
    have hsum : ∑ j ∈ insert i s, m j = m i + d := Finset.sum_insert hi
    have hM : (Q * P).Monic := hQ_monic.mul ih_monic
    have hD : (Q * P).natDegree = m i + d := by
      rw [hQ_monic.natDegree_mul ih_monic, hQ_deg, ih_deg]
    refine ⟨by rw [hprod]; exact hM, by rw [hprod, hsum]; exact hD, ?_⟩
    rw [hprod, hsum, Finset.sum_insert hi]
    intro hd1
    rcases Nat.eq_zero_or_pos (m i) with hmi0 | hmipos
    · have hQ1 : Q = 1 := by simp [Q, hmi0]
      rw [hQ1, hmi0, zero_add, one_mul]
      have hdpos : 1 ≤ d := by omega
      simp only [Nat.cast_zero, zero_mul, zero_add]
      exact ih_next hdpos
    · rcases Nat.eq_zero_or_pos d with hd0 | hdpos
      · have hP1 : P = 1 := by
          have : P.natDegree = 0 := by rw [ih_deg]; exact hd0
          exact Polynomial.eq_one_of_monic_natDegree_zero ih_monic this
        have hs0 : ∑ j ∈ s, (m j : ℂ) * a j = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          have hmj : m j = 0 := by
            have hle : m j ≤ ∑ k ∈ s, m k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
            omega
          simp [hmj]
        rw [hP1, hd0, add_zero, hs0, add_zero, mul_one]
        simpa [Q, neg_mul] using hQ_next (m i) hmipos
      · rw [Polynomial.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => Q.coeff k * P.coeff l)]
        have honly : ∀ k ∈ Finset.range (m i + d - 1 + 1),
            Q.coeff k * P.coeff (m i + d - 1 - k) ≠ 0 →
            k = m i ∨ k = m i - 1 := by
          intro k _ hne
          have hk : k ≤ m i := by
            by_contra h; push Not at h
            have : Q.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQ_deg]; omega)
            exact hne (by simp [this])
          have hl : m i + d - 1 - k ≤ d := by
            by_contra h; push Not at h
            have : P.coeff (m i + d - 1 - k) = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [ih_deg]; omega)
            exact hne (by simp [this])
          omega
        have hmem1 : m i ∈ Finset.range (m i + d - 1 + 1) := by rw [Finset.mem_range]; omega
        have hmem2 : m i - 1 ∈ Finset.range (m i + d - 1 + 1) := by rw [Finset.mem_range]; omega
        have hne12 : m i ≠ m i - 1 := by omega
        rw [← Finset.sum_subset (s₁ := {m i, m i - 1})
          (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption)
          (by intro x hx hnot
              by_contra hne
              rcases honly x hx hne with rfl | rfl <;> simp at hnot)]
        rw [Finset.sum_pair hne12]
        have hsub1 : m i + d - 1 - m i = d - 1 := by omega
        have hsub2 : m i + d - 1 - (m i - 1) = d := by omega
        rw [hsub1, hsub2]
        have hQ_lead : Q.coeff (m i) = 1 := by
          calc Q.coeff (m i) = Q.leadingCoeff := by rw [Polynomial.leadingCoeff, hQ_deg]
            _ = 1 := hQ_monic.leadingCoeff
        have hP_lead : P.coeff d = 1 := by
          calc P.coeff d = P.leadingCoeff := by rw [Polynomial.leadingCoeff, ih_deg]
            _ = 1 := ih_monic.leadingCoeff
        rw [hQ_lead, one_mul, hP_lead, mul_one, ih_next hdpos, hQ_next (m i) hmipos]
        ring

private lemma contDiff_coeff_prod_X_sub_C_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) (a : ι → E → ℂ) (m : ι → ℕ)
    (ha : ∀ j ∈ s, ContDiff ℂ (1 : ℕ∞) (a j)) (k : ℕ) :
    ContDiff ℂ (1 : ℕ∞) (fun u : E => (∏ j ∈ s, (X - C (a j u)) ^ (m j)).coeff k) := by
  classical
  have hmul : ∀ {f g : E → ℂ[X]},
      (∀ l, ContDiff ℂ (1 : ℕ∞) (fun u => (f u).coeff l)) →
      (∀ l, ContDiff ℂ (1 : ℕ∞) (fun u => (g u).coeff l)) →
      ∀ l, ContDiff ℂ (1 : ℕ∞) (fun u => (f u * g u).coeff l) := by
    intro f g hf hg l
    simp_rw [Polynomial.coeff_mul]
    exact ContDiff.sum fun ab _ => (hf ab.1).mul (hg ab.2)
  have hlin : ∀ {g : E → ℂ}, ContDiff ℂ (1 : ℕ∞) g →
      ∀ l, ContDiff ℂ (1 : ℕ∞) (fun u => (X - C (g u)).coeff l) := by
    intro g hg l
    rcases l with _ | l
    · simpa using hg.neg
    · rcases l with _ | l
      · simpa using contDiff_const
      · simp [contDiff_const]
  have hpow : ∀ {g : E → ℂ} (d : ℕ), ContDiff ℂ (1 : ℕ∞) g →
      ∀ l, ContDiff ℂ (1 : ℕ∞) (fun u => ((X - C (g u)) ^ d).coeff l) := by
    intro g d hg
    induction d with
    | zero =>
      intro l; simp [contDiff_const]
    | succ d ihd =>
      intro l
      simp_rw [pow_succ]
      exact hmul ihd (hlin hg) l
  revert k
  induction s using Finset.induction_on with
  | empty =>
    intro k; simp [contDiff_const]
  | @insert i s hi ih =>
    intro k
    simp_rw [Finset.prod_insert hi]
    exact hmul (hpow (m i) (ha i (Finset.mem_insert_self i s)))
      (ih fun j hj => ha j (Finset.mem_insert_of_mem hj)) k

private lemma hasDerivAt_eval_prod_linear {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ℂ)
    (a δ : ι → ℂ) (m : ι → ℕ) :
    HasDerivAt (fun t : ℂ => ∏ j ∈ s, (z - (a j + t * δ j)) ^ (m j))
      (-∑ j ∈ s, (m j : ℂ) * δ j * (z - a j) ^ (m j - 1) *
        ∏ k ∈ s.erase j, (z - a k) ^ (m k)) 0 := by
  have hterm : ∀ j ∈ s,
      HasDerivAt (fun t : ℂ => (z - (a j + t * δ j)) ^ (m j))
        (-((m j : ℂ) * δ j * (z - a j) ^ (m j - 1))) 0 := by
    intro j _
    rcases Nat.eq_zero_or_pos (m j) with h0 | hpos
    · simp only [h0, pow_zero, Nat.cast_zero, zero_mul, neg_zero]
      exact hasDerivAt_const (0 : ℂ) (1 : ℂ)
    · have h1 : HasDerivAt (fun t : ℂ => z - (a j + t * δ j)) (-δ j) 0 := by
        have := (((hasDerivAt_id (0 : ℂ)).mul_const (δ j)).const_add (a j)).const_sub z
        exact this.congr_deriv (by ring)
      have h2 := h1.pow (m j)
      exact h2.congr_deriv (by simp only [zero_mul, add_zero]; ring)
  have hprod := HasDerivAt.finsetProd hterm
  have hfn : (∏ j ∈ s, fun t : ℂ => (z - (a j + t * δ j)) ^ (m j)) =
      fun t : ℂ => ∏ j ∈ s, (z - (a j + t * δ j)) ^ (m j) := by
    ext t; simp [Finset.prod_apply]
  exact (hfn ▸ hprod).congr_deriv (by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [zero_mul, add_zero, smul_eq_mul]
    ring)

private lemma pow_dvd_iff_le_rootMult {Q : ℂ[X]} (hQ : Q ≠ 0) (a : ℂ) (k : ℕ) :
    (X - C a) ^ k ∣ Q ↔ k ≤ Q.rootMultiplicity a := by
  constructor
  · intro hdvd
    by_contra hlt
    push Not at hlt
    obtain ⟨g, hQg, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ a
    let m := Q.rootMultiplicity a
    have h1 : (X - C a) ^ (m + 1) ∣ Q := (pow_dvd_pow (X - C a) hlt).trans hdvd
    rw [pow_succ] at h1
    have h2 : (X - C a) ^ m * (X - C a) ∣ (X - C a) ^ m * g := hQg ▸ h1
    have hpow_ne : (X - C a) ^ m ≠ 0 := pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)
    exact hndvd ((mul_dvd_mul_iff_left hpow_ne).mp h2)
  · intro hle
    exact (pow_dvd_pow (X - C a) hle).trans (Polynomial.pow_rootMultiplicity_dvd Q a)

private lemma dvd_of_eval_zero_and_dvd_derivative {Q : ℂ[X]} {a : ℂ} {k : ℕ}
    (hk : 1 ≤ k) (hQ0 : Q.eval a = 0) (hdvd : (X - C a) ^ (k - 1) ∣ Q.derivative) :
    (X - C a) ^ k ∣ Q := by
  by_cases hQ : Q = 0
  · subst hQ; exact dvd_zero _
  by_cases hQd : Q.derivative = 0
  · have hdeg : Q.natDegree = 0 := by
      by_contra hne
      have hne' : ((Q.natDegree - 1 : ℕ) : ℂ) + 1 ≠ 0 := by
        have : Q.natDegree - 1 + 1 ≠ 0 := by omega
        exact_mod_cast this
      have hlc : Q.derivative.coeff (Q.natDegree - 1) ≠ 0 := by
        rw [coeff_derivative, Nat.sub_add_cancel (Nat.pos_of_ne_zero hne)]
        exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hQ) hne'
      rw [hQd, coeff_zero] at hlc; exact hlc rfl
    have hC : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    rw [hC, eval_C] at hQ0
    rw [hC, hQ0, map_zero]
    exact dvd_zero _
  have hmult : k - 1 ≤ Q.derivative.rootMultiplicity a :=
    (pow_dvd_iff_le_rootMult hQd a (k - 1)).mp hdvd
  have hrel := Polynomial.derivative_rootMultiplicity_of_root (p := Q) (t := a) hQ0
  have hroot : 1 ≤ Q.rootMultiplicity a :=
    (Polynomial.rootMultiplicity_pos hQ).mpr hQ0
  have hk_le : k ≤ Q.rootMultiplicity a := by omega
  exact (pow_dvd_iff_le_rootMult hQ a k).mpr hk_le

private lemma isCoprime_X_sub_C {a b : ℂ} (hab : a ≠ b) :
    IsCoprime (X - C a) (X - C b) := by
  refine ⟨C (b - a)⁻¹, -C (b - a)⁻¹, ?_⟩
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  calc C (b - a)⁻¹ * (X - C a) + -C (b - a)⁻¹ * (X - C b)
      = C (b - a)⁻¹ * C (b - a) := by simp only [map_sub]; ring
    _ = C ((b - a)⁻¹ * (b - a)) := by rw [← map_mul]
    _ = 1 := by rw [inv_mul_cancel₀ hne, map_one]

private lemma exists_critical_value_deformation
    {n : ℕ} (hn : 2 ≤ n) (p₀ : ℂ[X]) (hp₀_monic : p₀.Monic) (hp₀_deg : p₀.natDegree = n)
    (ζ_bad : ℂ) (hζ_bad : p₀.derivative.IsRoot ζ_bad) (hval_ne : ‖p₀.eval ζ_bad‖ ≠ 1) :
    ∃ (δ : ℝ) (p : ℂ → ℂ[X]) (S : Finset ℂ),
      0 < δ ∧
      p 0 = p₀ ∧
      (∀ lam ∈ ball (0 : ℂ) δ, (p lam).Monic ∧ (p lam).natDegree = n) ∧
      (∀ k : ℕ, ContDiffOn ℂ (1 : ℕ∞) (fun lam => (p lam).coeff k) (ball 0 δ)) ∧
      (∀ lam ∈ ball (0 : ℂ) δ, ∃ x : ℂ,
        (p lam).derivative.IsRoot x ∧ (p lam).eval x = p₀.eval ζ_bad + lam) ∧
      (∀ lam ∈ ball (0 : ℂ) δ, ∀ w ∈ sphere (0 : ℂ) 1, w ∉ S →
        ∀ x : ℂ, (p lam).derivative.IsRoot x → (p lam).eval x ≠ w) := by
  classical
  have hp₀_coeff_n : p₀.coeff n = 1 := by
    calc p₀.coeff n = p₀.leadingCoeff := by rw [Polynomial.leadingCoeff, hp₀_deg]
      _ = 1 := hp₀_monic.leadingCoeff
  have hp'_ne : p₀.derivative ≠ 0 := by
    intro h0
    have hlc : p₀.derivative.coeff (n - 1) = (n : ℂ) := by
      rw [coeff_derivative, Nat.sub_add_cancel (by omega), hp₀_coeff_n, one_mul]
      exact_mod_cast (Nat.sub_add_cancel (by omega))
    rw [h0, coeff_zero] at hlc
    exact (Nat.cast_ne_zero (R := ℂ).mpr (by omega)) hlc.symm
  have hp'_deg : p₀.derivative.natDegree = n - 1 := by
    rw [Polynomial.natDegree_derivative, hp₀_deg]
  have hp'_lc : p₀.derivative.leadingCoeff = (n : ℂ) := by
    rw [Polynomial.leadingCoeff, hp'_deg, coeff_derivative, Nat.sub_add_cancel (by omega),
      hp₀_coeff_n, one_mul]
    exact_mod_cast (Nat.sub_add_cancel (by omega))
  let Scrit : Finset ℂ := p₀.derivative.roots.toFinset
  have hζ_mem : ζ_bad ∈ Scrit :=
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp'_ne).mpr hζ_bad)
  let r : ℕ := Scrit.card
  have hr_pos : 0 < r := Finset.card_pos.mpr ⟨ζ_bad, hζ_mem⟩
  have : NeZero r := ⟨hr_pos.ne'⟩
  let e0 : Fin r ≃ Scrit := (Fintype.equivFinOfCardEq (by simp [r])).symm
  let idx0 : Fin r := e0.symm ⟨ζ_bad, hζ_mem⟩
  let e : Fin r ≃ Scrit := (Equiv.swap (0 : Fin r) idx0).trans e0
  let ζ₀ : Fin r → ℂ := fun j => (e j).1
  have hζ₀_0 : ζ₀ 0 = ζ_bad := by
    dsimp only [ζ₀, e, idx0]
    simp
  have hζ₀_inj : Function.Injective ζ₀ := fun j₁ j₂ h =>
    e.injective (Subtype.ext h)
  let m : Fin r → ℕ := fun j => p₀.derivative.rootMultiplicity (ζ₀ j)
  have hm_pos : ∀ j : Fin r, 1 ≤ m j := fun j =>
    (Polynomial.rootMultiplicity_pos hp'_ne).mpr
      ((Polynomial.mem_roots hp'_ne).mp (Multiset.mem_toFinset.mp (e j).2))
  have hm0_ne : (m 0 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hm_pos 0; omega)
  have hp'_fac : p₀.derivative = C (n : ℂ) * ∏ j : Fin r, (X - C (ζ₀ j)) ^ (m j) := by
    have hsplit := (IsAlgClosed.splits p₀.derivative).eq_prod_roots
    rw [hp'_lc] at hsplit
    rw [hsplit]
    congr 1
    rw [Finset.prod_multiset_map_count]
    simp_rw [Polynomial.count_roots]
    rw [← Finset.prod_coe_sort Scrit (fun a : ℂ => (X - C a) ^ p₀.derivative.rootMultiplicity a)]
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  have hm_sum : ∑ j : Fin r, m j = n - 1 := by
    have htop := prod_X_sub_C_pow_coeff_top (Finset.univ : Finset (Fin r)) ζ₀ m
    have h1 : p₀.derivative.natDegree = (∏ j : Fin r, (X - C (ζ₀ j)) ^ (m j)).natDegree := by
      rw [hp'_fac, Polynomial.natDegree_C_mul (Nat.cast_ne_zero.mpr (by omega))]
    rw [hp'_deg, htop.2.1] at h1
    exact h1.symm
  -- Parameterization of the centered critical-point manifold H ≃ (Fin r → ℂ)
  let S₀ : ℂ := ∑ j : Fin r, (m j : ℂ) * ζ₀ j
  let critPt (u : Fin r → ℂ) (j : Fin r) : ℂ :=
    if j = 0 then (S₀ - ∑ k ∈ Finset.univ.erase (0 : Fin r), (m k : ℂ) * u k) / (m 0 : ℂ)
    else u j
  let u₀ : Fin r → ℂ := fun j => if j = 0 then p₀.eval 0 else ζ₀ j
  have hcritPt_u₀ : critPt u₀ = ζ₀ := by
    ext j
    by_cases hj : j = 0
    · subst hj
      simp only [critPt, ↓reduceIte]
      have hsum_er : ∑ k ∈ Finset.univ.erase (0 : Fin r), (m k : ℂ) * u₀ k =
          ∑ k ∈ Finset.univ.erase (0 : Fin r), (m k : ℂ) * ζ₀ k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
        simp [u₀, hk0]
      rw [hsum_er]
      have hsplit : (m 0 : ℂ) * ζ₀ 0 + ∑ k ∈ Finset.univ.erase (0 : Fin r), (m k : ℂ) * ζ₀ k = S₀ :=
        Finset.add_sum_erase Finset.univ (fun k => (m k : ℂ) * ζ₀ k) (Finset.mem_univ 0)
      have hsub : S₀ - ∑ k ∈ Finset.univ.erase (0 : Fin r), (m k : ℂ) * ζ₀ k = (m 0 : ℂ) * ζ₀ 0 := by
        linear_combination -hsplit
      rw [hsub, mul_div_cancel_left₀ _ hm0_ne]
    · simp [critPt, u₀, hj]
  have hcritPt_sum : ∀ u : Fin r → ℂ, ∑ j : Fin r, (m j : ℂ) * critPt u j = S₀ := by
    intro u
    rw [← Finset.add_sum_erase Finset.univ (fun j => (m j : ℂ) * critPt u j) (Finset.mem_univ 0)]
    have h1 : (m 0 : ℂ) * critPt u 0 =
        S₀ - ∑ k ∈ Finset.univ.erase (0 : Fin r), (m k : ℂ) * u k := by
      simp only [critPt, ↓reduceIte]
      exact mul_div_cancel₀ _ hm0_ne
    have h2 : ∑ k ∈ Finset.univ.erase (0 : Fin r), (m k : ℂ) * critPt u k =
        ∑ k ∈ Finset.univ.erase (0 : Fin r), (m k : ℂ) * u k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
      simp [critPt, hk0]
    rw [h1, h2]; ring
  have hcritPt_cd : ∀ j : Fin r, ContDiff ℂ (1 : ℕ∞) (fun u : Fin r → ℂ => critPt u j) := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp only [critPt, ↓reduceIte]
      refine (contDiff_const.sub ?_).div_const _
      exact ContDiff.sum fun k _ => contDiff_const.mul (contDiff_apply ℂ ℂ k)
    · simp only [critPt, hj, ↓reduceIte]
      exact contDiff_apply ℂ ℂ j
  let derivPoly (u : Fin r → ℂ) : ℂ[X] :=
    C (n : ℂ) * ∏ j : Fin r, (X - C (critPt u j)) ^ (m j)
  let paramPoly (u : Fin r → ℂ) : ℂ[X] :=
    antiderivN n (derivPoly u) (u 0)
  have hderivPoly_props : ∀ u : Fin r → ℂ,
      (derivPoly u).natDegree = n - 1 ∧ (derivPoly u).leadingCoeff = (n : ℂ) ∧
      (derivPoly u).coeff (n - 2) = -(n : ℂ) * S₀ := by
    intro u
    have htop := prod_X_sub_C_pow_coeff_top (Finset.univ : Finset (Fin r)) (critPt u) m
    have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hdeg : (derivPoly u).natDegree = n - 1 := by
      rw [Polynomial.natDegree_C_mul hn_ne, htop.2.1, hm_sum]
    have hlc : (derivPoly u).leadingCoeff = (n : ℂ) := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, htop.1.leadingCoeff, mul_one]
    have hnext : (derivPoly u).coeff (n - 2) = -(n : ℂ) * S₀ := by
      dsimp only [derivPoly]
      rw [coeff_C_mul]
      have hsub := htop.2.2 (by rw [hm_sum]; omega)
      rw [hm_sum] at hsub
      have hidx : n - 1 - 1 = n - 2 := by omega
      rw [hidx, hcritPt_sum u] at hsub
      rw [hsub]; ring
    exact ⟨hdeg, hlc, hnext⟩
  have hparamPoly_props : ∀ u : Fin r → ℂ,
      (paramPoly u).Monic ∧ (paramPoly u).natDegree = n ∧
      (paramPoly u).derivative = derivPoly u := by
    intro u
    rcases hderivPoly_props u with ⟨hd, hlc, _⟩
    obtain ⟨hm, hdeg⟩ := antiderivN_monic_and_degree (by omega) hd hlc (u 0)
    have hder : (paramPoly u).derivative = derivPoly u := by
      apply antiderivN_derivative
      intro k hk
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    exact ⟨hm, hdeg, hder⟩
  have hparamPoly_u₀ : paramPoly u₀ = p₀ := by
    have h1 : derivPoly u₀ = p₀.derivative := by
      dsimp only [derivPoly]; rw [hcritPt_u₀, hp'_fac]
    have h2 : u₀ 0 = p₀.eval 0 := by simp [u₀]
    dsimp only [paramPoly]
    rw [h1, h2]
    exact (eq_antiderivN_of_derivative hp₀_deg.le).symm
  have hderivPoly_cd : ∀ k : ℕ, ContDiff ℂ (1 : ℕ∞) (fun u : Fin r → ℂ => (derivPoly u).coeff k) := by
    intro k
    have : (fun u : Fin r → ℂ => (derivPoly u).coeff k) =
        fun u => (n : ℂ) * (∏ j : Fin r, (X - C (critPt u j)) ^ (m j)).coeff k := by
      ext u; simp [derivPoly]
    rw [this]
    exact contDiff_const.mul (contDiff_coeff_prod_X_sub_C_pow Finset.univ
      (fun j u => critPt u j) m (fun j _ => hcritPt_cd j) k)
  have hparamPoly_cd : ∀ k : ℕ, ContDiff ℂ (1 : ℕ∞) (fun u : Fin r → ℂ => (paramPoly u).coeff k) := by
    intro k
    have : (fun u : Fin r → ℂ => (paramPoly u).coeff k) =
        fun u => if k = 0 then u 0 else if k ≤ n then (derivPoly u).coeff (k - 1) / (k : ℂ) else 0 := by
      ext u; exact antiderivN_coeff n (derivPoly u) (u 0) k
    rw [this]
    split_ifs
    · exact contDiff_apply ℂ ℂ 0
    · exact (hderivPoly_cd (k - 1)).div_const _
    · exact contDiff_const
  -- Critical-value map Ψ : (Fin r → ℂ) → (Fin r → ℂ)
  let Ψ : (Fin r → ℂ) → (Fin r → ℂ) := fun u j => (paramPoly u).eval (critPt u j)
  have hΨ_cd : ContDiff ℂ (1 : ℕ∞) Ψ := by
    rw [contDiff_pi]
    intro j
    have hev : (fun u => Ψ u j) =
        fun u => ∑ k ∈ Finset.range (n + 1), (paramPoly u).coeff k * (critPt u j) ^ k := by
      ext u
      dsimp only [Ψ]
      exact Polynomial.eval_eq_sum_range' (n := n + 1) (by rw [(hparamPoly_props u).2.1]; omega) (critPt u j)
    rw [hev]
    exact ContDiff.sum fun k _ => (hparamPoly_cd k).mul ((hcritPt_cd j).pow k)
  -- Step 2: Prove fderiv ℂ Ψ u₀ is injective
  have hfderiv_inj : Function.Injective (fderiv ℂ Ψ u₀) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    let γ : ℂ → (Fin r → ℂ) := fun t => u₀ + t • v
    have hγ : HasDerivAt γ v 0 := by
      simpa [γ] using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add u₀
    have hγ0 : γ 0 = u₀ := by simp [γ]
    let δζ : Fin r → ℂ := fun j =>
      if j = 0 then (-(∑ k ∈ Finset.univ.erase (0 : Fin r), (m k : ℂ) * v k)) / (m 0 : ℂ)
      else v j
    have hcritPt_γ : ∀ (j : Fin r) (t : ℂ), critPt (γ t) j = ζ₀ j + t * δζ j := by
      intro j t
      by_cases hj : j = 0
      · subst hj
        have h0 := congrFun hcritPt_u₀ 0
        simp only [critPt, ↓reduceIte] at h0 ⊢
        rw [← h0]
        dsimp only [γ, δζ]
        simp only [↓reduceIte, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
          Finset.sum_add_distrib]
        have hsum_er : ∑ k ∈ Finset.univ.erase (0 : Fin r), (m k : ℂ) * (t * v k) =
            t * ∑ k ∈ Finset.univ.erase (0 : Fin r), (m k : ℂ) * v k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [hsum_er]
        field_simp [hm0_ne]
        ring
      · simp [critPt, γ, δζ, u₀, hj]
    have hcoeff_diff : ∀ k : ℕ, DifferentiableAt ℂ (fun t => (paramPoly (γ t)).coeff k) 0 := fun k => by
      have hd1 : DifferentiableAt ℂ (fun u => (paramPoly u).coeff k) (γ 0) := by
        rw [hγ0]; exact (hparamPoly_cd k).differentiable (by simp) u₀
      exact hd1.comp (0 : ℂ) hγ.differentiableAt
    let Q : ℂ[X] :=
      ∑ k ∈ Finset.range (n + 1), C (deriv (fun t : ℂ => (paramPoly (γ t)).coeff k) 0) * X ^ k
    have hQ_coeff : ∀ k : ℕ, Q.coeff k =
        if k < n + 1 then deriv (fun t : ℂ => (paramPoly (γ t)).coeff k) 0 else 0 := by
      intro k
      dsimp only [Q]
      rw [Polynomial.finsetSum_coeff]
      simp_rw [coeff_C_mul_X_pow]
      by_cases hk : k < n + 1
      · rw [if_pos hk, Finset.sum_eq_single k]
        · simp
        · intro l _ hlk; simp [Ne.symm hlk]
        · intro h; exact absurd (Finset.mem_range.mpr hk) h
      · rw [if_neg hk]
        refine Finset.sum_eq_zero fun l hl => ?_
        have hln : l < n + 1 := Finset.mem_range.mp hl
        have hne : k ≠ l := by omega
        simp [hne]
    have hQ_coeff0 : Q.coeff 0 = v 0 := by
      rw [hQ_coeff, if_pos (by omega)]
      have heq : (fun t : ℂ => (paramPoly (γ t)).coeff 0) = fun t => u₀ 0 + t * v 0 := by
        ext t; simp [paramPoly, antiderivN_coeff, γ]
      rw [heq]
      have hd : HasDerivAt (fun t : ℂ => u₀ 0 + t * v 0) (v 0) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (v 0)).const_add (u₀ 0)
      exact hd.deriv
    have hQ_high : ∀ k : ℕ, n - 1 ≤ k → Q.coeff k = 0 := by
      intro k hk
      rw [hQ_coeff]
      split_ifs with hkn
      · have hconst : ∃ c : ℂ, ∀ t : ℂ, (paramPoly (γ t)).coeff k = c := by
          by_cases hk1 : k = n - 1
          · refine ⟨(-(n : ℂ) * S₀) / ((n - 1 : ℕ) : ℂ), fun t => ?_⟩
            dsimp only [paramPoly]
            rw [hk1, antiderivN_coeff]
            have hne0 : n - 1 ≠ 0 := by omega
            have hle : n - 1 ≤ n := by omega
            simp only [hne0, ↓reduceIte, hle]
            have hsub : n - 1 - 1 = n - 2 := by omega
            rw [hsub, (hderivPoly_props (γ t)).2.2]
          · have hkn' : k = n := by omega
            refine ⟨1, fun t => ?_⟩
            rw [hkn', ← (hparamPoly_props (γ t)).2.1, ← Polynomial.leadingCoeff,
              (hparamPoly_props (γ t)).1.leadingCoeff]
        rcases hconst with ⟨c, hc⟩
        simp [hc]
      · rfl
    have hQ_eval_zero : ∀ j : Fin r, Q.eval (ζ₀ j) = 0 := by
      intro j
      have hd1 : HasDerivAt (fun t => Ψ (γ t) j) (Q.eval (ζ₀ j)) 0 := by
        have hsum_eq : (fun t => Ψ (γ t) j) =
            fun t => ∑ k ∈ Finset.range (n + 1), (paramPoly (γ t)).coeff k * (ζ₀ j + t * δζ j) ^ k := by
          ext t
          dsimp only [Ψ]
          rw [hcritPt_γ j t]
          exact Polynomial.eval_eq_sum_range' (by rw [(hparamPoly_props (γ t)).2.1]; omega) (ζ₀ j + t * δζ j)
        rw [hsum_eq]
        have hterm : ∀ k ∈ Finset.range (n + 1),
            HasDerivAt (fun t : ℂ => (paramPoly (γ t)).coeff k * (ζ₀ j + t * δζ j) ^ k)
              (Q.coeff k * (ζ₀ j) ^ k +
                (p₀.coeff k * ((k : ℂ) * (ζ₀ j) ^ (k - 1) * δζ j))) 0 := by
          intro k hk
          have h1 : HasDerivAt (fun t => (paramPoly (γ t)).coeff k) (Q.coeff k) 0 := by
            rw [hQ_coeff, if_pos (Finset.mem_range.mp hk)]
            exact (hcoeff_diff k).hasDerivAt
          have h2 : HasDerivAt (fun t : ℂ => (ζ₀ j + t * δζ j) ^ k)
              ((k : ℂ) * (ζ₀ j) ^ (k - 1) * δζ j) 0 := by
            have hl : HasDerivAt (fun t : ℂ => ζ₀ j + t * δζ j) (δζ j) 0 :=
              (((hasDerivAt_id (0 : ℂ)).mul_const (δζ j)).const_add (ζ₀ j)).congr_deriv (one_mul _)
            exact (hl.pow k).congr_deriv (by simp only [zero_mul, add_zero])
          have hm := h1.mul h2
          exact hm.congr_deriv (by simp only [hγ0, hparamPoly_u₀, zero_mul, add_zero])
        have hsum_d := HasDerivAt.sum hterm
        have hfn_sum : (∑ k ∈ Finset.range (n + 1),
              fun t : ℂ => (paramPoly (γ t)).coeff k * (ζ₀ j + t * δζ j) ^ k) =
            fun t : ℂ => ∑ k ∈ Finset.range (n + 1), (paramPoly (γ t)).coeff k * (ζ₀ j + t * δζ j) ^ k := by
          ext t; simp [Finset.sum_apply]
        refine (hfn_sum ▸ hsum_d).congr_deriv ?_
        rw [Finset.sum_add_distrib]
        have hQev : Q.eval (ζ₀ j) = ∑ k ∈ Finset.range (n + 1), Q.coeff k * (ζ₀ j) ^ k := by
          apply Polynomial.eval_eq_sum_range'
          by_cases hQ0 : Q = 0
          · simp [hQ0]
          · have hle : Q.natDegree ≤ n - 1 := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
              (fun k hk => hQ_high k (by omega))
            omega
        have hp'ev : ∑ k ∈ Finset.range (n + 1),
            p₀.coeff k * ((k : ℂ) * (ζ₀ j) ^ (k - 1) * δζ j) =
            p₀.derivative.eval (ζ₀ j) * δζ j := by
          rw [Finset.sum_range_succ']
          simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_one_sub_one]
          have hder : p₀.derivative.eval (ζ₀ j) =
              ∑ k ∈ Finset.range n, p₀.derivative.coeff k * (ζ₀ j) ^ k :=
            Polynomial.eval_eq_sum_range' (by rw [hp'_deg]; omega) (ζ₀ j)
          rw [hder, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [coeff_derivative]
          push_cast; ring
        have hcrit0 : p₀.derivative.eval (ζ₀ j) = 0 :=
          (Polynomial.mem_roots hp'_ne).mp (Multiset.mem_toFinset.mp (e j).2)
        rw [← hQev, hp'ev, hcrit0, zero_mul, add_zero]
      have hd2 : HasDerivAt (fun t => Ψ (γ t) j) 0 0 := by
        have hcomp := ((hΨ_cd.differentiable (by simp) (γ 0)).hasFDerivAt).comp_hasDerivAt 0 hγ
        have hproj := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) j).hasFDerivAt.comp_hasDerivAt 0 hcomp
        exact hproj.congr_deriv (by simp [hγ0, hv])
      exact hd1.unique hd2
    -- Identify Q.derivative explicitly via product differentiation
    let Rpoly : ℂ[X] :=
      -C (n : ℂ) * ∑ j : Fin r, C ((m j : ℂ) * δζ j) * (X - C (ζ₀ j)) ^ (m j - 1) *
        ∏ k ∈ Finset.univ.erase j, (X - C (ζ₀ k)) ^ (m k)
    have hQder_eq : Q.derivative = Rpoly := by
      have hev_eq : ∀ z : ℂ, Q.derivative.eval z = Rpoly.eval z := by
        intro z
        have hd1 : HasDerivAt (fun t => (derivPoly (γ t)).eval z) (Q.derivative.eval z) 0 := by
          have hsum_eq : (fun t => (derivPoly (γ t)).eval z) =
              fun t => ∑ k ∈ Finset.range n, (derivPoly (γ t)).coeff k * z ^ k := by
            ext t
            exact Polynomial.eval_eq_sum_range' (by rw [(hderivPoly_props (γ t)).1]; omega) z
          rw [hsum_eq]
          have hterm : ∀ k ∈ Finset.range n,
              HasDerivAt (fun t => (derivPoly (γ t)).coeff k * z ^ k)
                (Q.derivative.coeff k * z ^ k) 0 := by
            intro k hk
            have hkn : k < n := Finset.mem_range.mp hk
            have hk_eq : ∀ t : ℂ, (derivPoly (γ t)).coeff k =
                ((k + 1 : ℕ) : ℂ) * (paramPoly (γ t)).coeff (k + 1) := by
              intro t
              dsimp only [paramPoly]
              rw [antiderivN_coeff]
              have hle : k + 1 ≤ n := hkn
              have hne : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
              simp only [Nat.succ_ne_zero, ↓reduceIte, hle, Nat.add_one_sub_one]
              exact (mul_div_cancel₀ _ hne).symm
            simp_rw [hk_eq]
            have h1 : HasDerivAt (fun t => (paramPoly (γ t)).coeff (k + 1)) (Q.coeff (k + 1)) 0 := by
              rw [hQ_coeff, if_pos (by omega)]
              exact (hcoeff_diff (k + 1)).hasDerivAt
            have h2 := (h1.const_mul ((k + 1 : ℕ) : ℂ)).mul_const (z ^ k)
            exact h2.congr_deriv (by rw [coeff_derivative]; push_cast; ring)
          have hsum_d := HasDerivAt.sum hterm
          have hfn_sum2 : (∑ k ∈ Finset.range n, fun t : ℂ => (derivPoly (γ t)).coeff k * z ^ k) =
              fun t : ℂ => ∑ k ∈ Finset.range n, (derivPoly (γ t)).coeff k * z ^ k := by
            ext t; simp [Finset.sum_apply]
          refine (hfn_sum2 ▸ hsum_d).congr_deriv ?_
          symm
          apply Polynomial.eval_eq_sum_range'
          by_cases hQd0 : Q.derivative = 0
          · simp [hQd0]; omega
          · have hle : Q.natDegree ≤ n - 1 := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
              (fun k hk => hQ_high k (by omega))
            have hdl : Q.derivative.natDegree ≤ Q.natDegree - 1 := Polynomial.natDegree_derivative_le Q
            omega
        have hd2 : HasDerivAt (fun t => (derivPoly (γ t)).eval z) (Rpoly.eval z) 0 := by
          have heq : (fun t => (derivPoly (γ t)).eval z) =
              fun t => (n : ℂ) * ∏ j : Fin r, (z - (ζ₀ j + t * δζ j)) ^ (m j) := by
            ext t
            simp only [derivPoly, eval_mul, eval_C, eval_prod, eval_pow, eval_sub, eval_X,
              hcritPt_γ]
          rw [heq]
          have hp := (hasDerivAt_eval_prod_linear Finset.univ z ζ₀ δζ m).const_mul (n : ℂ)
          exact hp.congr_deriv (by
            simp only [Rpoly, eval_mul, eval_neg, eval_C, eval_finsetSum, eval_pow, eval_sub,
              eval_X, eval_prod]
            ring)
        exact hd1.unique hd2
      by_contra hne
      have hsub_ne : Q.derivative - Rpoly ≠ 0 := sub_ne_zero.mpr hne
      have hfin : Set.Finite { z : ℂ | (Q.derivative - Rpoly).IsRoot z } :=
        ((Q.derivative - Rpoly).roots.toFinset).finite_toSet.subset fun z hz =>
          Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hsub_ne).mpr hz)
      have hall : { z : ℂ | (Q.derivative - Rpoly).IsRoot z } = Set.univ := by
        ext z; simp [Polynomial.IsRoot, hev_eq z]
      rw [hall] at hfin
      exact Set.infinite_univ hfin
    -- Divisibility of Q by ∏ j, (X - C (ζ₀ j)) ^ (m j) forces Q = 0
    have hQ_dvd_each : ∀ j : Fin r, (X - C (ζ₀ j)) ^ (m j) ∣ Q := by
      intro j
      apply dvd_of_eval_zero_and_dvd_derivative (hm_pos j) (hQ_eval_zero j)
      rw [hQder_eq]
      apply dvd_mul_of_dvd_right
      apply Finset.dvd_sum
      intro l _
      by_cases hlj : l = j
      · subst hlj
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right dvd_rfl _) _
      · apply dvd_mul_of_dvd_right
        have hjmem : j ∈ Finset.univ.erase l := Finset.mem_erase.mpr ⟨Ne.symm hlj, Finset.mem_univ j⟩
        exact (pow_dvd_pow (X - C (ζ₀ j)) (Nat.sub_le (m j) 1)).trans
          (Finset.dvd_prod_of_mem _ hjmem)
    have hQ_dvd_prod : (∏ j : Fin r, (X - C (ζ₀ j)) ^ (m j)) ∣ Q := by
      apply Finset.prod_dvd_of_coprime
      · intro j₁ _ j₂ _ hne
        exact (isCoprime_X_sub_C (fun h => hne (hζ₀_inj h))).pow
      · intro j _; exact hQ_dvd_each j
    have hQ_zero : Q = 0 := by
      by_contra hQne
      have hdeg_le := Polynomial.natDegree_le_of_dvd hQ_dvd_prod hQne
      have htop := prod_X_sub_C_pow_coeff_top (Finset.univ : Finset (Fin r)) ζ₀ m
      rw [htop.2.1, hm_sum] at hdeg_le
      have hQ_lt : Q.natDegree ≤ n - 2 :=
        Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => hQ_high k (by omega))
      omega
    have hv0 : v 0 = 0 := by rw [← hQ_coeff0, hQ_zero, coeff_zero]
    -- Rpoly = 0 forces δζ = 0, hence v = 0
    have hR0 : Rpoly = 0 := by rw [← hQder_eq, hQ_zero, derivative_zero]
    let Tpoly : ℂ[X] :=
      ∑ j : Fin r, C ((m j : ℂ) * δζ j) * ∏ k ∈ Finset.univ.erase j, (X - C (ζ₀ k))
    have hR_fac : Rpoly = -C (n : ℂ) * (∏ k : Fin r, (X - C (ζ₀ k)) ^ (m k - 1)) * Tpoly := by
      dsimp only [Rpoly, Tpoly]
      rw [mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsplit : ∏ k : Fin r, (X - C (ζ₀ k)) ^ (m k - 1) =
          (X - C (ζ₀ j)) ^ (m j - 1) * ∏ k ∈ Finset.univ.erase j, (X - C (ζ₀ k)) ^ (m k - 1) :=
        (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm
      rw [hsplit]
      have hprod_eq : (∏ k ∈ Finset.univ.erase j, (X - C (ζ₀ k)) ^ (m k - 1)) *
          (∏ k ∈ Finset.univ.erase j, (X - C (ζ₀ k))) =
          ∏ k ∈ Finset.univ.erase j, (X - C (ζ₀ k)) ^ (m k) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← pow_succ, Nat.sub_add_cancel (hm_pos k)]
      calc C ((m j : ℂ) * δζ j) * (X - C (ζ₀ j)) ^ (m j - 1) *
              ∏ k ∈ Finset.univ.erase j, (X - C (ζ₀ k)) ^ (m k)
          = C ((m j : ℂ) * δζ j) * (X - C (ζ₀ j)) ^ (m j - 1) *
              ((∏ k ∈ Finset.univ.erase j, (X - C (ζ₀ k)) ^ (m k - 1)) *
               (∏ k ∈ Finset.univ.erase j, (X - C (ζ₀ k)))) := by rw [hprod_eq]
        _ = (X - C (ζ₀ j)) ^ (m j - 1) *
              (∏ k ∈ Finset.univ.erase j, (X - C (ζ₀ k)) ^ (m k - 1)) *
              (C ((m j : ℂ) * δζ j) * ∏ k ∈ Finset.univ.erase j, (X - C (ζ₀ k))) := by ring
    have hT0 : Tpoly = 0 := by
      rw [hR_fac] at hR0
      have hne1 : (-C (n : ℂ) : ℂ[X]) ≠ 0 := by
        simp [Nat.cast_ne_zero.mpr (by omega : n ≠ 0)]
      have hne2 : (∏ k : Fin r, (X - C (ζ₀ k)) ^ (m k - 1)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
      exact (mul_eq_zero.mp hR0).resolve_left (mul_ne_zero hne1 hne2)
    have hδζ0 : ∀ j : Fin r, δζ j = 0 := by
      intro j
      have hev := congrArg (Polynomial.eval (ζ₀ j)) hT0
      simp only [Tpoly, eval_zero, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub,
        eval_X] at hev
      rw [Finset.sum_eq_single j] at hev
      · have hm_ne : (m j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := hm_pos j; omega)
        have hprod_ne : (∏ k ∈ Finset.univ.erase j, (ζ₀ j - ζ₀ k)) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr fun k hk =>
            sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hk).1 (hζ₀_inj h.symm)
        have h1 := (mul_eq_zero.mp hev).resolve_right hprod_ne
        exact (mul_eq_zero.mp h1).resolve_left hm_ne
      · intro l _ hlj
        have hjmem : j ∈ Finset.univ.erase l := Finset.mem_erase.mpr ⟨Ne.symm hlj, Finset.mem_univ j⟩
        have h0 : ∏ k ∈ Finset.univ.erase l, (ζ₀ j - ζ₀ k) = 0 :=
          Finset.prod_eq_zero hjmem (sub_self _)
        rw [h0, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    ext j
    by_cases hj : j = 0
    · subst hj; exact hv0
    · simpa [δζ, hj] using hδζ0 j
  -- Step 3: Apply finite-dimensional Holomorphic Inverse Function Theorem
  let L : (Fin r → ℂ) ≃L[ℂ] (Fin r → ℂ) :=
    (LinearEquiv.ofBijective (fderiv ℂ Ψ u₀).toLinearMap
      ⟨hfderiv_inj, LinearMap.injective_iff_surjective.mp hfderiv_inj⟩).toContinuousLinearEquiv
  have hL_eq : (L : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ)) = fderiv ℂ Ψ u₀ :=
    ContinuousLinearMap.ext fun x => rfl
  have hL_fderiv : HasFDerivAt Ψ (L : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ)) u₀ := by
    rw [hL_eq]
    exact (hΨ_cd.differentiable (by simp) u₀).hasFDerivAt
  have hΨ_at : ContDiffAt ℂ (1 : ℕ∞) Ψ u₀ := hΨ_cd.contDiffAt
  let Ψinv : (Fin r → ℂ) → (Fin r → ℂ) := hΨ_at.localInverse hL_fderiv one_ne_zero
  have hΨinv_cd : ContDiffAt ℂ (1 : ℕ∞) Ψinv (Ψ u₀) := hΨ_at.to_localInverse hL_fderiv one_ne_zero
  have hΨinv_0 : Ψinv (Ψ u₀) = u₀ := hΨ_at.localInverse_apply_image hL_fderiv one_ne_zero
  have hΨinv_right : ∀ᶠ y in 𝓝 (Ψ u₀), Ψ (Ψinv y) = y :=
    (hΨ_at.hasStrictFDerivAt' hL_fderiv one_ne_zero).eventually_right_inverse
  obtain ⟨U, hU_nhds, hU_cd⟩ :=
    (contDiffWithinAt_iff_contDiffOn_nhds (by simp)).mp (hΨinv_cd.contDiffWithinAt (s := Set.univ))
  simp only [Set.insert_eq_of_mem (Set.mem_univ _), nhdsWithin_univ] at hU_nhds
  have hU_ev : ∀ᶠ y in 𝓝 (Ψ u₀), y ∈ U := hU_nhds
  have hcomb : ∀ᶠ y in 𝓝 (Ψ u₀), y ∈ U ∧ Ψ (Ψinv y) = y := hU_ev.and hΨinv_right
  rcases Metric.eventually_nhds_iff.mp hcomb with ⟨δ₁, hδ₁pos, hδ₁⟩
  have hgap : 0 < |‖p₀.eval ζ_bad‖ - 1| := abs_pos.mpr (sub_ne_zero.mpr hval_ne)
  let δ : ℝ := min δ₁ (|‖p₀.eval ζ_bad‖ - 1| / 2)
  have hδpos : 0 < δ := lt_min hδ₁pos (by linarith)
  let e₀ : Fin r → ℂ := fun j => if j = 0 then 1 else 0
  let u : ℂ → (Fin r → ℂ) := fun lam => Ψinv (Ψ u₀ + lam • e₀)
  let p : ℂ → ℂ[X] := fun lam => paramPoly (u lam)
  let S : Finset ℂ := (Finset.univ.erase (0 : Fin r)).image (fun j => p₀.eval (ζ₀ j))
  have hdist_y : ∀ lam ∈ ball (0 : ℂ) δ, dist (Ψ u₀ + lam • e₀) (Ψ u₀) < δ₁ := by
    intro lam hlam
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
    have he₀ : ‖e₀‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro j; dsimp only [e₀]; split_ifs <;> simp
    have hln : ‖lam‖ < δ := by simpa [mem_ball_zero_iff] using hlam
    have hδle : δ ≤ δ₁ := min_le_left _ _
    nlinarith [norm_nonneg lam]
  have hu_cd : ContDiffOn ℂ (1 : ℕ∞) u (ball 0 δ) := by
    refine hU_cd.comp (contDiffOn_const.add (contDiffOn_id.smul contDiffOn_const)) ?_
    intro lam hlam
    exact (hδ₁ (hdist_y lam hlam)).1
  have hΨ_u : ∀ lam ∈ ball (0 : ℂ) δ, Ψ (u lam) = Ψ u₀ + lam • e₀ := fun lam hlam =>
    (hδ₁ (hdist_y lam hlam)).2
  have hΨ_u₀_val : ∀ j : Fin r, Ψ u₀ j = p₀.eval (ζ₀ j) := fun j => by
    simp only [Ψ, hparamPoly_u₀, hcritPt_u₀]
  refine ⟨δ, p, S, hδpos, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [p, u]
    rw [zero_smul, add_zero, hΨinv_0, hparamPoly_u₀]
  · intro lam _
    exact ⟨(hparamPoly_props (u lam)).1, (hparamPoly_props (u lam)).2.1⟩
  · intro k
    exact (hparamPoly_cd k).comp_contDiffOn hu_cd
  · intro lam hlam
    refine ⟨critPt (u lam) 0, ?_, ?_⟩
    · show (p lam).derivative.eval (critPt (u lam) 0) = 0
      rw [(hparamPoly_props (u lam)).2.2]
      simp only [derivPoly, eval_mul, eval_C, eval_prod, eval_pow, eval_sub, eval_X]
      have h0 : (critPt (u lam) 0 - critPt (u lam) 0) ^ (m 0) = 0 := by
        rw [sub_self, zero_pow (by have := hm_pos 0; omega)]
      rw [Finset.prod_eq_zero (Finset.mem_univ (0 : Fin r)) h0, mul_zero]
    · have h := congrFun (hΨ_u lam hlam) 0
      simpa [Ψ, p, e₀, hΨ_u₀_val 0, hζ₀_0] using h
  · intro lam hlam w hw hwS x hx
    change (p lam).derivative.eval x = 0 at hx
    rw [(hparamPoly_props (u lam)).2.2] at hx
    simp only [derivPoly, eval_mul, eval_C, eval_prod, eval_pow, eval_sub, eval_X,
      mul_eq_zero] at hx
    have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rcases Finset.prod_eq_zero_iff.mp (hx.resolve_left hn_ne) with ⟨j, _, hj0⟩
    have hxj : x = critPt (u lam) j := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hj0)
    rw [hxj]
    have hval := congrFun (hΨ_u lam hlam) j
    change (p lam).eval (critPt (u lam) j) = Ψ u₀ j + lam * e₀ j at hval
    rw [hval, hΨ_u₀_val j]
    by_cases hj0' : j = 0
    · subst hj0'
      simp only [e₀, ↓reduceIte, mul_one, hζ₀_0]
      intro heqw
      have hwn : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
      have hln : ‖lam‖ < |‖p₀.eval ζ_bad‖ - 1| / 2 :=
        lt_of_lt_of_le (mem_ball_zero_iff.mp hlam) (min_le_right _ _)
      have htri : |‖p₀.eval ζ_bad + lam‖ - ‖p₀.eval ζ_bad‖| ≤ ‖lam‖ := by
        simpa [add_sub_cancel_left] using abs_norm_sub_norm_le (p₀.eval ζ_bad + lam) (p₀.eval ζ_bad)
      rw [heqw, hwn, abs_sub_comm] at htri
      linarith
    · simp only [e₀, hj0', ↓reduceIte, mul_zero, add_zero]
      intro heqw
      apply hwS
      rw [← heqw]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hj0', Finset.mem_univ j⟩, rfl⟩

/- Section 4: Local Holomorphic Root Branches via 2D Triangular IFT -/

private lemma exists_local_root_branches
    {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (p : ℂ → ℂ[X])
    (_hp_monic : ∀ lam ∈ ball (0 : ℂ) δ, (p lam).Monic)
    (hp_deg : ∀ lam ∈ ball (0 : ℂ) δ, (p lam).natDegree = n)
    (hp_cd : ∀ k : ℕ, ContDiffOn ℂ (1 : ℕ∞) (fun lam => (p lam).coeff k) (ball 0 δ))
    {lam₀ w₀ : ℂ} (hlam₀ : lam₀ ∈ ball (0 : ℂ) δ)
    (hreg : ∀ x : ℂ, (p lam₀).derivative.IsRoot x → (p lam₀).eval x ≠ w₀) :
    ∃ (ρ ε : ℝ) (φ : Fin n → ℂ → ℂ → ℂ),
      0 < ρ ∧ 0 < ε ∧
      closedBall lam₀ ρ ⊆ ball 0 δ ∧
      (∀ k : Fin n, ContDiffOn ℂ (1 : ℕ∞) (fun q : ℂ × ℂ => φ k q.1 q.2)
        (ball lam₀ ρ ×ˢ ball w₀ ε)) ∧
      (∀ lam ∈ ball lam₀ ρ, ∀ w ∈ ball w₀ ε,
        (∀ k : Fin n, (p lam).eval (φ k lam w) = w ∧ (p lam).derivative.eval (φ k lam w) ≠ 0) ∧
        Function.Injective (fun k : Fin n => φ k lam w) ∧
        (p lam - C w).roots = Finset.univ.val.map (fun k : Fin n => φ k lam w) ∧
        fiberInvDerivSum (p lam) w = ∑ k : Fin n, ‖((p lam).derivative.eval (φ k lam w))⁻¹‖) := by
  classical
  -- Step 1: Enumerate the n distinct simple roots of p lam₀ - C w₀
  let q₀ : ℂ[X] := p lam₀ - C w₀
  have hq₀_deg : q₀.natDegree = n := by
    rw [Polynomial.natDegree_sub_C, hp_deg lam₀ hlam₀]
  have hq₀_ne : q₀ ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hq₀_deg; omega
  have hq₀_card : q₀.roots.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hq₀_deg]
  have hq₀_nodup : q₀.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro z
    rw [Polynomial.count_roots]
    by_cases hzr : q₀.IsRoot z
    · have hder_ne : q₀.derivative.eval z ≠ 0 := by
        simp only [q₀, derivative_sub, derivative_C, sub_zero]
        intro hder0
        have hev : (p lam₀).eval z = w₀ := by
          simpa [q₀, Polynomial.IsRoot, sub_eq_zero] using hzr
        exact hreg z hder0 hev
      have hrel := Polynomial.derivative_rootMultiplicity_of_root (p := q₀) (t := z) hzr
      have h0 : q₀.derivative.rootMultiplicity z = 0 :=
        Polynomial.rootMultiplicity_eq_zero_iff.mpr (fun h => absurd h hder_ne)
      omega
    · rw [Polynomial.rootMultiplicity_eq_zero_iff.mpr (fun h => absurd h hzr)]
      exact Nat.zero_le 1
  have hfin_card : q₀.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hq₀_nodup, hq₀_card]
  let eR : Fin n ≃ q₀.roots.toFinset :=
    (Fintype.equivFinOfCardEq (by simp [hfin_card])).symm
  let z₀ : Fin n → ℂ := fun k => (eR k).1
  have hz₀_inj : Function.Injective z₀ := fun k₁ k₂ h => eR.injective (Subtype.ext h)
  have hz₀_eval : ∀ k : Fin n, (p lam₀).eval (z₀ k) = w₀ := fun k => by
    have hmem := (Polynomial.mem_roots hq₀_ne).mp (Multiset.mem_toFinset.mp (eR k).2)
    simpa [q₀, Polynomial.IsRoot, sub_eq_zero] using hmem
  have hz₀_der_ne : ∀ k : Fin n, (p lam₀).derivative.eval (z₀ k) ≠ 0 := fun k h0 =>
    hreg (z₀ k) h0 (hz₀_eval k)
  -- Step 2: Apply 2D triangular holomorphic IFT to G (lam, z) = (lam, (p lam).eval z) at each (lam₀, z₀ k)
  let G : ℂ × ℂ → ℂ × ℂ := fun q => (q.1, (p q.1).eval q.2)
  have hG_cd : ContDiffOn ℂ (1 : ℕ∞) G (ball 0 δ ×ˢ Set.univ) := by
    refine contDiffOn_fst.prodMk ?_
    refine (ContDiffOn.sum (s := Finset.range (n + 1)) fun j _ =>
      ((hp_cd j).comp contDiffOn_fst (fun q hq => hq.1)).mul
        (contDiffOn_snd.pow j)).congr ?_
    intro ⟨lam, z⟩ hq
    exact Polynomial.eval_eq_sum_range' (n := n + 1) (by rw [hp_deg lam hq.1]; omega) z
  have hG_fderiv : ∀ k : Fin n, ∃ (α : ℂ),
      HasFDerivAt G
        ((ContinuousLinearMap.fst ℂ ℂ ℂ).prod
          (α • ContinuousLinearMap.fst ℂ ℂ ℂ +
            ((p lam₀).derivative.eval (z₀ k)) • ContinuousLinearMap.snd ℂ ℂ ℂ))
        (lam₀, z₀ k) := by
    intro k
    have hcoeff_da : ∀ j : ℕ, DifferentiableAt ℂ (fun lam => (p lam).coeff j) lam₀ := fun j =>
      ((hp_cd j).differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hlam₀)
    let α : ℂ := ∑ j ∈ Finset.range (n + 1),
      deriv (fun lam => (p lam).coeff j) lam₀ * (z₀ k) ^ j
    refine ⟨α, ?_⟩
    have hfst : HasFDerivAt (fun q : ℂ × ℂ => q.1) (ContinuousLinearMap.fst ℂ ℂ ℂ) (lam₀, z₀ k) :=
      hasFDerivAt_fst
    have hsnd : HasFDerivAt (fun q : ℂ × ℂ => (p q.1).eval q.2)
        (α • ContinuousLinearMap.fst ℂ ℂ ℂ +
          ((p lam₀).derivative.eval (z₀ k)) • ContinuousLinearMap.snd ℂ ℂ ℂ) (lam₀, z₀ k) := by
      have hev_nhds : (fun q : ℂ × ℂ => (p q.1).eval q.2) =ᶠ[𝓝 (lam₀, z₀ k)]
          fun q => ∑ j ∈ Finset.range (n + 1), (p q.1).coeff j * q.2 ^ j := by
        have hopen : IsOpen (ball (0 : ℂ) δ ×ˢ (Set.univ : Set ℂ)) := isOpen_ball.prod isOpen_univ
        filter_upwards [hopen.mem_nhds ⟨hlam₀, Set.mem_univ _⟩] with ⟨lam, z⟩ hq
        exact Polynomial.eval_eq_sum_range' (by rw [hp_deg lam hq.1]; omega) z
      refine (HasFDerivAt.congr_of_eventuallyEq ?_ hev_nhds)
      have hterm : ∀ j ∈ Finset.range (n + 1),
          HasFDerivAt (fun q : ℂ × ℂ => (p q.1).coeff j * q.2 ^ j)
            (((deriv (fun lam => (p lam).coeff j) lam₀ * (z₀ k) ^ j) •
                ContinuousLinearMap.fst ℂ ℂ ℂ) +
              (((p lam₀).coeff j * ((j : ℂ) * (z₀ k) ^ (j - 1))) •
                ContinuousLinearMap.snd ℂ ℂ ℂ)) (lam₀, z₀ k) := by
        intro j _
        have h1 : HasFDerivAt (fun q : ℂ × ℂ => (p q.1).coeff j)
            (deriv (fun lam => (p lam).coeff j) lam₀ • ContinuousLinearMap.fst ℂ ℂ ℂ) (lam₀, z₀ k) := by
          have h1' := (hcoeff_da j).hasDerivAt.hasFDerivAt.comp (lam₀, z₀ k) (hasFDerivAt_fst (𝕜 := ℂ))
          have hL : ContinuousLinearMap.toSpanSingleton ℂ (deriv (fun lam => (p lam).coeff j) lam₀) ∘L
                ContinuousLinearMap.fst ℂ ℂ ℂ =
              deriv (fun lam => (p lam).coeff j) lam₀ • ContinuousLinearMap.fst ℂ ℂ ℂ :=
            ContinuousLinearMap.ext fun ⟨a, b⟩ => by simp [mul_comm]
          exact hL ▸ h1'
        have h2 : HasFDerivAt (fun q : ℂ × ℂ => q.2 ^ j)
            (((j : ℂ) * (z₀ k) ^ (j - 1)) • ContinuousLinearMap.snd ℂ ℂ ℂ) (lam₀, z₀ k) := by
          have h2' := (hasDerivAt_pow j (z₀ k)).hasFDerivAt.comp (lam₀, z₀ k) (hasFDerivAt_snd (𝕜 := ℂ))
          have hL : ContinuousLinearMap.toSpanSingleton ℂ ((j : ℂ) * (z₀ k) ^ (j - 1)) ∘L
                ContinuousLinearMap.snd ℂ ℂ ℂ =
              ((j : ℂ) * (z₀ k) ^ (j - 1)) • ContinuousLinearMap.snd ℂ ℂ ℂ :=
            ContinuousLinearMap.ext fun ⟨a, b⟩ => by simp [mul_comm]
          exact hL ▸ h2'
        have hm := h1.mul h2
        have hLm : ((p lam₀).coeff j • (((j : ℂ) * (z₀ k) ^ (j - 1)) • ContinuousLinearMap.snd ℂ ℂ ℂ) +
              (z₀ k) ^ j • (deriv (fun lam => (p lam).coeff j) lam₀ • ContinuousLinearMap.fst ℂ ℂ ℂ)) =
            (((deriv (fun lam => (p lam).coeff j) lam₀ * (z₀ k) ^ j) •
                ContinuousLinearMap.fst ℂ ℂ ℂ) +
              (((p lam₀).coeff j * ((j : ℂ) * (z₀ k) ^ (j - 1))) •
                ContinuousLinearMap.snd ℂ ℂ ℂ)) :=
          ContinuousLinearMap.ext fun ⟨a, b⟩ => by simp; ring
        exact hLm ▸ hm
      have hsum := HasFDerivAt.sum hterm
      have hfn_s : (∑ j ∈ Finset.range (n + 1), fun q : ℂ × ℂ => (p q.1).coeff j * q.2 ^ j) =
          fun q : ℂ × ℂ => ∑ j ∈ Finset.range (n + 1), (p q.1).coeff j * q.2 ^ j := by
        ext q; simp [Finset.sum_apply]
      have hLs : (∑ j ∈ Finset.range (n + 1),
            (((deriv (fun lam => (p lam).coeff j) lam₀ * (z₀ k) ^ j) •
                ContinuousLinearMap.fst ℂ ℂ ℂ) +
              (((p lam₀).coeff j * ((j : ℂ) * (z₀ k) ^ (j - 1))) •
                ContinuousLinearMap.snd ℂ ℂ ℂ))) =
          (α • ContinuousLinearMap.fst ℂ ℂ ℂ +
            ((p lam₀).derivative.eval (z₀ k)) • ContinuousLinearMap.snd ℂ ℂ ℂ) := by
        refine ContinuousLinearMap.ext fun ⟨a, b⟩ => ?_
        simp only [FunLike.coe_sum, Finset.sum_apply,
          FunLike.coe_add, Pi.add_apply,
          FunLike.coe_smul, Pi.smul_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
          smul_eq_mul, Finset.sum_add_distrib, ← Finset.sum_mul]
        congr 1
        congr 1
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_one_sub_one]
        have hder : (p lam₀).derivative.eval (z₀ k) =
            ∑ j ∈ Finset.range n, (p lam₀).derivative.coeff j * (z₀ k) ^ j := by
          apply Polynomial.eval_eq_sum_range'
          have h1 : (p lam₀).derivative.natDegree ≤ n - 1 := by
            rw [← hp_deg lam₀ hlam₀]; exact Polynomial.natDegree_derivative_le _
          omega
        rw [hder]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [coeff_derivative]
        push_cast; ring
      exact hLs ▸ (hfn_s ▸ hsum)
    exact hfst.prodMk hsnd
  -- Construct each local inverse branch φ_k
  have hbranch_each : ∀ k : Fin n, ∃ (ρk εk : ℝ) (φk : ℂ → ℂ → ℂ),
      0 < ρk ∧ 0 < εk ∧
      closedBall lam₀ ρk ⊆ ball 0 δ ∧
      φk lam₀ w₀ = z₀ k ∧
      ContDiffOn ℂ (1 : ℕ∞) (fun q : ℂ × ℂ => φk q.1 q.2) (ball lam₀ ρk ×ˢ ball w₀ εk) ∧
      (∀ lam ∈ ball lam₀ ρk, ∀ w ∈ ball w₀ εk,
        (p lam).eval (φk lam w) = w ∧ (p lam).derivative.eval (φk lam w) ≠ 0) := by
    intro k
    obtain ⟨α, hGd⟩ := hG_fderiv k
    let β : ℂ := (p lam₀).derivative.eval (z₀ k)
    have hβ : β ≠ 0 := hz₀_der_ne k
    let Lf : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
      (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
        (α • ContinuousLinearMap.fst ℂ ℂ ℂ + β • ContinuousLinearMap.snd ℂ ℂ ℂ)
    let Lg : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
      (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
        ((-β⁻¹ * α) • ContinuousLinearMap.fst ℂ ℂ ℂ + β⁻¹ • ContinuousLinearMap.snd ℂ ℂ ℂ)
    let Le : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
      ContinuousLinearEquiv.equivOfInverse Lf Lg
        (fun ⟨a, b⟩ => by
          ext
          · simp [Lf, Lg]
          · simp only [Lf, Lg, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst']
            change (-β⁻¹ * α) * a + β⁻¹ * (α * a + β * b) = b
            field_simp [hβ]; ring)
        (fun ⟨a, b⟩ => by
          ext
          · simp [Lf, Lg]
          · simp only [Lf, Lg, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst']
            change α * a + β * ((-β⁻¹ * α) * a + β⁻¹ * b) = b
            field_simp [hβ]; ring)
    have hG_at : ContDiffAt ℂ (1 : ℕ∞) G (lam₀, z₀ k) :=
      hG_cd.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨hlam₀, Set.mem_univ _⟩)
    have hG_fd : HasFDerivAt G (Le : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (lam₀, z₀ k) := hGd
    let Ginv : ℂ × ℂ → ℂ × ℂ := hG_at.localInverse hG_fd one_ne_zero
    have hG0 : G (lam₀, z₀ k) = (lam₀, w₀) := Prod.ext rfl (hz₀_eval k)
    have hGinv_cd : ContDiffAt ℂ (1 : ℕ∞) Ginv (lam₀, w₀) := by
      rw [← hG0]; exact hG_at.to_localInverse hG_fd one_ne_zero
    have hGinv_0 : Ginv (lam₀, w₀) = (lam₀, z₀ k) := by
      rw [← hG0]; exact hG_at.localInverse_apply_image hG_fd one_ne_zero
    have hGinv_right : ∀ᶠ y in 𝓝 (lam₀, w₀), G (Ginv y) = y := by
      rw [← hG0]
      exact (hG_at.hasStrictFDerivAt' hG_fd one_ne_zero).eventually_right_inverse
    obtain ⟨U, hU_nhds, hU_cd⟩ :=
      (contDiffWithinAt_iff_contDiffOn_nhds (by simp)).mp (hGinv_cd.contDiffWithinAt (s := Set.univ))
    simp only [Set.insert_eq_of_mem (Set.mem_univ _), nhdsWithin_univ] at hU_nhds
    have hU_ev : ∀ᶠ y in 𝓝 (lam₀, w₀), y ∈ U := hU_nhds
    -- Also (p lam).derivative.eval (Ginv (lam, w)).2 ≠ 0 near (lam₀, w₀) by continuity
    have hder_cont : ContinuousAt (fun y : ℂ × ℂ => (p y.1).derivative.eval (Ginv y).2) (lam₀, w₀) := by
      have hev : (fun y : ℂ × ℂ => (p y.1).derivative.eval (Ginv y).2) =ᶠ[𝓝 (lam₀, w₀)]
          fun y => ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℂ) * (p y.1).coeff (j + 1) * (Ginv y).2 ^ j := by
        filter_upwards [(isOpen_ball.prod isOpen_univ).mem_nhds ⟨hlam₀, Set.mem_univ _⟩] with y hy
        have hd : (p y.1).derivative.natDegree < n := by
          have := Polynomial.natDegree_derivative_le (p := p y.1)
          rw [hp_deg y.1 hy.1] at this; omega
        rw [Polynomial.eval_eq_sum_range' hd]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [coeff_derivative]; push_cast; ring
      refine ContinuousAt.congr ?_ hev.symm
      have hGinv_cont : ContinuousAt Ginv (lam₀, w₀) := hGinv_cd.continuousAt
      refine tendsto_finsetSum _ fun j _ => ?_
      have hc : ContinuousAt (fun y : ℂ × ℂ => (p y.1).coeff (j + 1)) (lam₀, w₀) :=
        ((hp_cd (j + 1)).continuousOn.continuousAt (isOpen_ball.mem_nhds hlam₀)).comp
          (f := Prod.fst) (x := (lam₀, w₀)) continuousAt_fst
      exact (continuousAt_const.mul hc).mul ((continuousAt_snd.comp hGinv_cont).pow j)
    have hder_ne0 : ∀ᶠ y in 𝓝 (lam₀, w₀), (p y.1).derivative.eval (Ginv y).2 ≠ 0 :=
      hder_cont.eventually_ne (by rw [hGinv_0]; exact hβ)
    have hball_nhds : ∀ᶠ y : ℂ × ℂ in 𝓝 (lam₀, w₀), y.1 ∈ ball (0 : ℂ) δ :=
      continuousAt_fst.preimage_mem_nhds (isOpen_ball.mem_nhds hlam₀)
    have hall := hU_ev.and (hGinv_right.and (hder_ne0.and hball_nhds))
    rcases Metric.eventually_nhds_iff.mp hall with ⟨r₁, hr₁pos, hr₁⟩
    obtain ⟨r₂, hr₂pos, hr₂sub⟩ := Metric.isOpen_iff.mp isOpen_ball lam₀ hlam₀
    let r₀ : ℝ := min (r₁ / 2) (r₂ / 2)
    have hr₀pos : 0 < r₀ := lt_min (by linarith) (by linarith)
    refine ⟨r₀, r₀, fun lam w => (Ginv (lam, w)).2, hr₀pos, hr₀pos, ?_, ?_, ?_, ?_⟩
    · intro lam hlam
      apply hr₂sub
      rw [mem_closedBall] at hlam
      rw [mem_ball]
      have : r₀ ≤ r₂ / 2 := min_le_right _ _
      linarith
    · exact congrArg Prod.snd hGinv_0
    · refine contDiffOn_snd.comp (hU_cd.mono ?_) (fun _ _ => Set.mem_univ _)
      intro ⟨lam, w⟩ ⟨hlam, hw⟩
      have hd : dist (lam, w) (lam₀, w₀) < r₁ := by
        rw [Prod.dist_eq, max_lt_iff]
        have : r₀ ≤ r₁ / 2 := min_le_left _ _
        exact ⟨lt_of_lt_of_le (mem_ball.mp hlam) (by linarith),
               lt_of_lt_of_le (mem_ball.mp hw) (by linarith)⟩
      exact (hr₁ hd).1
    · intro lam hlam w hw
      have hd : dist (lam, w) (lam₀, w₀) < r₁ := by
        rw [Prod.dist_eq, max_lt_iff]
        have : r₀ ≤ r₁ / 2 := min_le_left _ _
        exact ⟨lt_of_lt_of_le (mem_ball.mp hlam) (by linarith),
               lt_of_lt_of_le (mem_ball.mp hw) (by linarith)⟩
      obtain ⟨_, hGr, hdn, _⟩ := hr₁ hd
      have hfst : (Ginv (lam, w)).1 = lam := congrArg Prod.fst hGr
      have hsnd : (p (Ginv (lam, w)).1).eval (Ginv (lam, w)).2 = w := congrArg Prod.snd hGr
      rw [hfst] at hsnd
      exact ⟨hsnd, hdn⟩
  choose ρk εk φ hρk hεk hcbk hφ0 hφcd hφprop using hbranch_each
  -- Shrink ρ, ε so all n branches stay pairwise distinct
  have hsep : ∃ r_sep > 0, ∀ k₁ k₂ : Fin n, k₁ ≠ k₂ →
      ∀ lam ∈ ball lam₀ r_sep, ∀ w ∈ ball w₀ r_sep, φ k₁ lam w ≠ φ k₂ lam w := by
    have hpair : ∀ k₁ k₂ : Fin n, k₁ ≠ k₂ →
        ∃ r' > 0, ∀ lam ∈ ball lam₀ r', ∀ w ∈ ball w₀ r', φ k₁ lam w ≠ φ k₂ lam w := by
      intro k₁ k₂ hne
      have hc1 : ContinuousAt (fun q : ℂ × ℂ => φ k₁ q.1 q.2) (lam₀, w₀) :=
        (hφcd k₁).continuousOn.continuousAt
          ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self (hρk k₁), mem_ball_self (hεk k₁)⟩)
      have hc2 : ContinuousAt (fun q : ℂ × ℂ => φ k₂ q.1 q.2) (lam₀, w₀) :=
        (hφcd k₂).continuousOn.continuousAt
          ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self (hρk k₂), mem_ball_self (hεk k₂)⟩)
      have hne0 : φ k₁ lam₀ w₀ ≠ φ k₂ lam₀ w₀ := by
        rw [hφ0 k₁, hφ0 k₂]; exact fun h => hne (hz₀_inj h)
      have hev := (hc1.sub hc2).eventually_ne (sub_ne_zero.mpr hne0)
      rcases Metric.eventually_nhds_iff.mp hev with ⟨r', hr'pos, hr'⟩
      refine ⟨r', hr'pos, fun lam hlam w hw => ?_⟩
      have hd : dist (lam, w) (lam₀, w₀) < r' := by
        rw [Prod.dist_eq, max_lt_iff]; exact ⟨mem_ball.mp hlam, mem_ball.mp hw⟩
      exact sub_ne_zero.mp (hr' hd)
    let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter fun ab => ab.1 ≠ ab.2
    by_cases hpne : pairs.Nonempty
    · choose rpair hrpair_pos hrpair using fun (ab : { ab : Fin n × Fin n // ab.1 ≠ ab.2 }) =>
        hpair ab.1.1 ab.1.2 ab.2
      let r_min := Finset.univ.inf'
        (by
          rcases hpne with ⟨ab, hab⟩
          exact ⟨⟨ab, (Finset.mem_filter.mp hab).2⟩, Finset.mem_univ _⟩)
        (fun ab : { ab : Fin n × Fin n // ab.1 ≠ ab.2 } => rpair ab)
      have hrmin_pos : 0 < r_min := by
        rw [Finset.lt_inf'_iff]; intro ab _; exact hrpair_pos ab
      refine ⟨r_min, hrmin_pos, fun k₁ k₂ hne lam hlam w hw => ?_⟩
      have hle : r_min ≤ rpair ⟨(k₁, k₂), hne⟩ := Finset.inf'_le _ (Finset.mem_univ _)
      exact hrpair ⟨(k₁, k₂), hne⟩ lam (Metric.ball_subset_ball hle hlam) w
        (Metric.ball_subset_ball hle hw)
    · refine ⟨1, zero_lt_one, fun k₁ k₂ hne _ _ _ _ => ?_⟩
      exact absurd ⟨(k₁, k₂), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩⟩ hpne
  rcases hsep with ⟨r_sep, hr_sep_pos, hsep_prop⟩
  have hne_fin : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  let ρ : ℝ := min r_sep (Finset.univ.inf' hne_fin ρk)
  let ε : ℝ := min r_sep (Finset.univ.inf' hne_fin εk)
  have hρpos : 0 < ρ := lt_min hr_sep_pos (by rw [Finset.lt_inf'_iff]; intro k _; exact hρk k)
  have hεpos : 0 < ε := lt_min hr_sep_pos (by rw [Finset.lt_inf'_iff]; intro k _; exact hεk k)
  have hρle : ∀ k : Fin n, ρ ≤ ρk k := fun k => (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ k))
  have hεle : ∀ k : Fin n, ε ≤ εk k := fun k => (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ k))
  refine ⟨ρ, ε, φ, hρpos, hεpos, ?_, ?_, ?_⟩
  · exact (Metric.closedBall_subset_closedBall (hρle ⟨0, by omega⟩)).trans (hcbk ⟨0, by omega⟩)
  · intro k
    exact (hφcd k).mono (Set.prod_mono (Metric.ball_subset_ball (hρle k))
      (Metric.ball_subset_ball (hεle k)))
  · intro lam hlam w hw
    have hlam_in : lam ∈ ball (0 : ℂ) δ :=
      (Metric.closedBall_subset_closedBall (hρle ⟨0, by omega⟩)).trans (hcbk ⟨0, by omega⟩)
        (ball_subset_closedBall hlam)
    have hprops : ∀ k : Fin n, (p lam).eval (φ k lam w) = w ∧
        (p lam).derivative.eval (φ k lam w) ≠ 0 := fun k =>
      hφprop k lam (Metric.ball_subset_ball (hρle k) hlam) w (Metric.ball_subset_ball (hεle k) hw)
    have hinj : Function.Injective (fun k : Fin n => φ k lam w) := fun k₁ k₂ heq => by
      by_contra hne
      exact hsep_prop k₁ k₂ hne lam (Metric.ball_subset_ball (min_le_left _ _) hlam)
        w (Metric.ball_subset_ball (min_le_left _ _) hw) heq
    have hroots : (p lam - C w).roots = Finset.univ.val.map (fun k : Fin n => φ k lam w) := by
      have hdeg_q : (p lam - C w).natDegree = n := by
        rw [Polynomial.natDegree_sub_C, hp_deg lam hlam_in]
      have hne_q : p lam - C w ≠ 0 := by
        intro h; rw [h, natDegree_zero] at hdeg_q; omega
      have hnodup : (Finset.univ.val.map (fun k : Fin n => φ k lam w)).Nodup :=
        Finset.univ.nodup.map hinj
      have hle_ms : Finset.univ.val.map (fun k : Fin n => φ k lam w) ≤ (p lam - C w).roots := by
        rw [Multiset.le_iff_subset hnodup]
        intro z hz
        rcases Multiset.mem_map.mp hz with ⟨k, _, rfl⟩
        rw [Polynomial.mem_roots hne_q, Polynomial.IsRoot, eval_sub, eval_C, (hprops k).1, sub_self]
      have hcard_eq : (p lam - C w).roots.card ≤
          (Finset.univ.val.map (fun k : Fin n => φ k lam w)).card := by
        rw [IsAlgClosed.card_roots_eq_natDegree, hdeg_q, Multiset.card_map]
        simp
      exact (Multiset.eq_of_le_of_card_le hle_ms hcard_eq).symm
    refine ⟨hprops, hinj, hroots, ?_⟩
    unfold fiberInvDerivSum
    rw [hroots, Multiset.map_map]
    change ∑ k : Fin n, ‖(p lam).derivative.eval (φ k lam w)‖⁻¹ = _
    refine Finset.sum_congr rfl fun k _ => by rw [norm_inv]

/- Section 5: Tonelli + Equality Rigidity → Eremenko-Hayman Lemma 5 -/

theorem extremizer_critical_values_on_unit_circle
    {n : ℕ} (hn : 1 ≤ n)
    (p₀ : ℂ[X]) (hp₀_monic : p₀.Monic) (hp₀_deg : p₀.natDegree = n)
    (hmax : ∀ p : ℂ[X], p.Monic → p.natDegree = n →
      Erdos114.lemniscateLength p ≤ Erdos114.lemniscateLength p₀)
    (hlength_formula : ∀ p : ℂ[X], p.Monic → p.natDegree = n →
      IntegrableOn (circleIntegrand p) (Set.Ioo (0 : ℝ) (2 * Real.pi)) volume ∧
      Erdos114.lemniscateLength p =
        ENNReal.ofReal (∫ θ in Set.Ioo (0 : ℝ) (2 * Real.pi), circleIntegrand p θ)) :
    ∀ x : ℂ, p₀.derivative.IsRoot x → ‖p₀.eval x‖ = 1 := by
  classical
  -- Degree n = 1 has no critical points
  rcases eq_or_lt_of_le hn with rfl | hn2
  · intro x hx
    have hdeg1 : p₀ = X + C (p₀.coeff 0) := by
      have h := hp₀_monic.as_sum
      rw [hp₀_deg] at h
      simpa [Finset.sum_range_one] using h
    have hder : p₀.derivative = 1 := by rw [hdeg1]; simp
    change p₀.derivative.eval x = 0 at hx
    rw [hder, eval_one] at hx
    exact absurd hx one_ne_zero
  -- For n ≥ 2, assume for contradiction there is a critical point ζ_bad with ‖p₀.eval ζ_bad‖ ≠ 1
  intro ζ_bad hζ_bad
  by_contra hval_ne
  obtain ⟨δ, p, S, hδpos, hp0, hp_md, hp_cd, hcrit_move, hcrit_avoid⟩ :=
    exists_critical_value_deformation hn2 p₀ hp₀_monic hp₀_deg ζ_bad hζ_bad hval_ne
  let R : ℝ := δ / 2
  have hRpos : 0 < R := by dsimp only [R]; linarith
  have hcb_R : closedBall (0 : ℂ) R ⊆ ball 0 δ := closedBall_subset_ball (by dsimp [R]; linarith)
  -- For every w ∈ sphere 0 1 \ S, lam ↦ fiberInvDerivSum (p lam) w is continuous and locally subharmonic on ball 0 δ
  have hu_cont : ∀ w ∈ sphere (0 : ℂ) 1, w ∉ S →
      ContinuousOn (fun lam => fiberInvDerivSum (p lam) w) (ball 0 δ) := by
    intro w hw hwS lam₀ hlam₀
    obtain ⟨ρ, ε, φ, hρpos, hεpos, _, hφcd, hφprop⟩ :=
      exists_local_root_branches hn p (fun lam h => (hp_md lam h).1)
        (fun lam h => (hp_md lam h).2) hp_cd hlam₀ (hcrit_avoid lam₀ hlam₀ w hw hwS)
    have hcont_at : ContinuousAt (fun lam => ∑ k : Fin n, ‖((p lam).derivative.eval (φ k lam w))⁻¹‖) lam₀ := by
      refine tendsto_finsetSum _ fun k _ => ContinuousAt.norm (ContinuousAt.inv₀ ?_ ?_)
      · have hev : (fun lam => (p lam).derivative.eval (φ k lam w)) =ᶠ[𝓝 lam₀]
            fun lam => ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℂ) * (p lam).coeff (j + 1) * (φ k lam w) ^ j := by
          filter_upwards [isOpen_ball.mem_nhds hlam₀] with lam hlam
          have hd : (p lam).derivative.natDegree < n := by
            have := Polynomial.natDegree_derivative_le (p := p lam)
            rw [(hp_md lam hlam).2] at this; omega
          rw [Polynomial.eval_eq_sum_range' hd]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [coeff_derivative]; push_cast; ring
        refine ContinuousAt.congr ?_ hev.symm
        have hφ_c : ContinuousAt (fun lam => φ k lam w) lam₀ :=
          ((hφcd k).continuousOn.continuousAt
            ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hρpos, mem_ball_self hεpos⟩)).comp
            (continuousAt_id.prodMk continuousAt_const)
        refine tendsto_finsetSum _ fun j _ => ?_
        have hc : ContinuousAt (fun lam => (p lam).coeff (j + 1)) lam₀ :=
          (hp_cd (j + 1)).continuousOn.continuousAt (isOpen_ball.mem_nhds hlam₀)
        exact (continuousAt_const.mul hc).mul (hφ_c.pow j)
      · exact ((hφprop lam₀ (mem_ball_self hρpos) w (mem_ball_self hεpos)).1 k).2
    have heq_nhds : (fun lam => fiberInvDerivSum (p lam) w) =ᶠ[𝓝 lam₀]
        fun lam => ∑ k : Fin n, ‖((p lam).derivative.eval (φ k lam w))⁻¹‖ := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρpos)] with lam hlam
      exact (hφprop lam hlam w (mem_ball_self hεpos)).2.2.2
    exact (hcont_at.congr heq_nhds.symm).continuousWithinAt
  have hu_sub : ∀ w ∈ sphere (0 : ℂ) 1, w ∉ S →
      ∀ z ∈ ball (0 : ℂ) R, ∃ ρ₀ > 0, ∀ ρ, 0 < ρ → ρ < ρ₀ →
        closedBall z ρ ⊆ ball 0 R →
        fiberInvDerivSum (p z) w ≤ Real.circleAverage (fun lam => fiberInvDerivSum (p lam) w) z ρ := by
    intro w hw hwS z hz
    have hzδ : z ∈ ball (0 : ℂ) δ := hcb_R (ball_subset_closedBall hz)
    obtain ⟨ρ₀, ε, φ, hρ₀pos, hεpos, hcb₀, hφcd, hφprop⟩ :=
      exists_local_root_branches hn p (fun lam h => (hp_md lam h).1)
        (fun lam h => (hp_md lam h).2) hp_cd hzδ (hcrit_avoid z hzδ w hw hwS)
    refine ⟨ρ₀, hρ₀pos, fun ρ hρpos hρlt _ => ?_⟩
    let f : Fin n → ℂ → ℂ := fun k lam => ((p lam).derivative.eval (φ k lam w))⁻¹
    have hf_diff : ∀ k : Fin n, DifferentiableOn ℂ (f k) (ball z ρ₀) := by
      intro k
      have hder_diff : DifferentiableOn ℂ (fun lam => (p lam).derivative.eval (φ k lam w)) (ball z ρ₀) := by
        have hsum_diff : DifferentiableOn ℂ
            (fun lam => ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℂ) * (p lam).coeff (j + 1) * (φ k lam w) ^ j)
            (ball z ρ₀) := by
          have hφ_d : DifferentiableOn ℂ (fun lam => φ k lam w) (ball z ρ₀) :=
            ((hφcd k).differentiableOn (by simp)).comp
              (differentiableOn_id.prodMk (differentiableOn_const w))
              (fun lam hlam => ⟨hlam, mem_ball_self hεpos⟩)
          refine DifferentiableOn.fun_sum fun j _ => ?_
          have hc_d : DifferentiableOn ℂ (fun lam => (p lam).coeff (j + 1)) (ball z ρ₀) :=
            ((hp_cd (j + 1)).differentiableOn (by simp)).mono (ball_subset_closedBall.trans hcb₀)
          exact ((differentiableOn_const _).mul hc_d).mul (hφ_d.pow j)
        refine hsum_diff.congr fun lam hlam => ?_
        have hlamδ : lam ∈ ball (0 : ℂ) δ := hcb₀ (ball_subset_closedBall hlam)
        have hd : (p lam).derivative.natDegree < n := by
          have := Polynomial.natDegree_derivative_le (p := p lam)
          rw [(hp_md lam hlamδ).2] at this; omega
        rw [Polynomial.eval_eq_sum_range' hd]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [coeff_derivative]; push_cast; ring
      exact hder_diff.inv fun lam hlam => ((hφprop lam hlam w (mem_ball_self hεpos)).1 k).2
    have hf_dc : ∀ k : Fin n, DiffContOnCl ℂ (f k) (ball z ρ) := fun k => by
      refine ⟨(hf_diff k).mono (Metric.ball_subset_ball hρlt.le), ?_⟩
      rw [closure_ball z hρpos.ne']
      exact ((hf_diff k).mono (closedBall_subset_ball hρlt)).continuousOn
    have hval_z : fiberInvDerivSum (p z) w = ∑ k : Fin n, ‖f k z‖ :=
      (hφprop z (mem_ball_self hρ₀pos) w (mem_ball_self hεpos)).2.2.2
    have hval_sp : Set.EqOn (fun lam => fiberInvDerivSum (p lam) w)
        (fun lam => ∑ k : Fin n, ‖f k lam‖) (sphere z |ρ|) := fun lam hlam => by
      rw [abs_of_pos hρpos] at hlam
      exact (hφprop lam (closedBall_subset_ball hρlt (sphere_subset_closedBall hlam))
        w (mem_ball_self hεpos)).2.2.2
    rw [hval_z, Real.circleAverage_congr_sphere hval_sp]
    have hint : ∀ k : Fin n, CircleIntegrable (fun lam => ‖f k lam‖) z ρ := fun k => by
      have h1 := (hf_dc k).continuousOn
      rw [closure_ball z hρpos.ne'] at h1
      exact (h1.mono sphere_subset_closedBall).norm.circleIntegrable hρpos.le
    rw [Real.circleAverage_fun_sum fun k _ => hint k]
    exact Finset.sum_le_sum fun k _ => norm_le_circleAverage_norm hρpos (hf_dc k)
  -- Subharmonic mean value inequality for every w ∈ sphere 0 1 \ S
  have hmv : ∀ w ∈ sphere (0 : ℂ) 1, w ∉ S →
      fiberInvDerivSum (p 0) w ≤ Real.circleAverage (fun lam => fiberInvDerivSum (p lam) w) 0 R := by
    intro w hw hwS
    exact subharmonic_mean_value hRpos ((hu_cont w hw hwS).mono hcb_R) (hu_sub w hw hwS)
  -- Joint continuity on the good set Gset = { θ ∈ Ioo 0 (2π) | exp (θ * I) ∉ S }
  let badθ : Set ℝ := { θ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) | Complex.exp ((θ : ℂ) * Complex.I) ∈ S }
  have hbad_fin : badθ.Finite := by
    have hinj : Set.InjOn (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I))
        (Set.Ioo (0 : ℝ) (2 * Real.pi)) := by
      intro θ₁ hθ₁ θ₂ hθ₂ heq
      rw [Complex.exp_eq_exp_iff_exists_int] at heq
      rcases heq with ⟨k, hk⟩
      have him : θ₁ = θ₂ + (k : ℝ) * (2 * Real.pi) := by
        have h1 := congrArg Complex.im hk
        simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero, sub_zero,
          Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat] at h1
        linarith
      have hk0 : k = 0 := by
        by_contra hkne
        rcases lt_or_gt_of_ne hkne with hlt | hgt
        · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
          nlinarith [hθ₁.1, hθ₂.2, Real.two_pi_pos]
        · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hgt
          nlinarith [hθ₁.2, hθ₂.1, Real.two_pi_pos]
      rw [hk0] at him; simp at him; exact him
    exact Set.Finite.of_finite_image
      (S.finite_toSet.subset (by rintro _ ⟨_, hθ, rfl⟩; exact hθ.2)) (hinj.mono fun θ hθ => hθ.1)
  let goodθ : Set ℝ := Set.Ioo (0 : ℝ) (2 * Real.pi) \ badθ
  have hgood_meas : MeasurableSet goodθ :=
    measurableSet_Ioo.diff hbad_fin.measurableSet
  have hbad_vol : volume badθ = 0 := hbad_fin.measure_zero volume
  have hrest_eq : volume.restrict goodθ = volume.restrict (Set.Ioo (0 : ℝ) (2 * Real.pi)) := by
    apply MeasureTheory.Measure.restrict_congr_set
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · have hemp : goodθ \ Set.Ioo (0 : ℝ) (2 * Real.pi) = ∅ := by
        ext x; simp [goodθ]
      rw [hemp, measure_empty]
    · have hsub : Set.Ioo (0 : ℝ) (2 * Real.pi) \ goodθ ⊆ badθ := by
        intro x hx; simp only [goodθ, Set.mem_sdiff, not_and, not_not] at hx; exact hx.2 hx.1
      exact measure_mono_null hsub hbad_vol
  have hjoint_cont : ContinuousOn
      (fun q : ℝ × ℝ => fiberInvDerivSum (p (circleMap 0 R q.1)) (Complex.exp ((q.2 : ℂ) * Complex.I)))
      (Set.univ ×ˢ goodθ) := by
    intro ⟨φ₀, θ₀⟩ ⟨_, hθ₀⟩
    have hlam₀ : circleMap 0 R φ₀ ∈ ball (0 : ℂ) δ := by
      have : circleMap 0 R φ₀ ∈ sphere (0 : ℂ) R := circleMap_mem_sphere 0 hRpos.le φ₀
      exact hcb_R (sphere_subset_closedBall this)
    have hw₀ : Complex.exp ((θ₀ : ℂ) * Complex.I) ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]
    have hw₀S : Complex.exp ((θ₀ : ℂ) * Complex.I) ∉ S := fun h =>
      hθ₀.2 ⟨hθ₀.1, h⟩
    obtain ⟨ρ, ε, φb, hρpos, hεpos, _, hφcd, hφprop⟩ :=
      exists_local_root_branches hn p (fun lam h => (hp_md lam h).1)
        (fun lam h => (hp_md lam h).2) hp_cd hlam₀ (hcrit_avoid _ hlam₀ _ hw₀ hw₀S)
    let mapP : ℝ × ℝ → ℂ × ℂ := fun q => (circleMap 0 R q.1, Complex.exp ((q.2 : ℂ) * Complex.I))
    have hmapP_cont : Continuous mapP :=
      ((continuous_circleMap 0 R).comp continuous_fst).prodMk
        ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))
    have hUopen : IsOpen (mapP ⁻¹' (ball (circleMap 0 R φ₀) ρ ×ˢ ball (Complex.exp ((θ₀ : ℂ) * Complex.I)) ε)) :=
      (isOpen_ball.prod isOpen_ball).preimage hmapP_cont
    have hmemU : (φ₀, θ₀) ∈ mapP ⁻¹' (ball (circleMap 0 R φ₀) ρ ×ˢ ball (Complex.exp ((θ₀ : ℂ) * Complex.I)) ε) :=
      ⟨mem_ball_self hρpos, mem_ball_self hεpos⟩
    have hcont_at : ContinuousAt
        (fun q : ℝ × ℝ => ∑ k : Fin n, ‖((p (mapP q).1).derivative.eval (φb k (mapP q).1 (mapP q).2))⁻¹‖)
        (φ₀, θ₀) := by
      refine tendsto_finsetSum _ fun k _ => ContinuousAt.norm (ContinuousAt.inv₀ ?_ ?_)
      · have hev : (fun q : ℝ × ℝ => (p (mapP q).1).derivative.eval (φb k (mapP q).1 (mapP q).2))
            =ᶠ[𝓝 (φ₀, θ₀)] fun q => ∑ j ∈ Finset.range n,
              ((j + 1 : ℕ) : ℂ) * (p (mapP q).1).coeff (j + 1) * (φb k (mapP q).1 (mapP q).2) ^ j := by
          filter_upwards [(isOpen_ball.preimage ((continuous_circleMap 0 R).comp continuous_fst)).mem_nhds hlam₀]
            with q hq
          have hd : (p (mapP q).1).derivative.natDegree < n := by
            have hq' : (mapP q).1 ∈ ball (0 : ℂ) δ := hq
            have := Polynomial.natDegree_derivative_le (p := p (mapP q).1)
            rw [(hp_md _ hq').2] at this; omega
          rw [Polynomial.eval_eq_sum_range' hd]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [coeff_derivative]; push_cast; ring
        refine ContinuousAt.congr ?_ hev.symm
        have hφ_c : ContinuousAt (fun q : ℝ × ℝ => φb k (mapP q).1 (mapP q).2) (φ₀, θ₀) :=
          ((hφcd k).continuousOn.continuousAt
            ((isOpen_ball.prod isOpen_ball).mem_nhds hmemU)).comp hmapP_cont.continuousAt
        refine tendsto_finsetSum _ fun j _ => ?_
        have hc : ContinuousAt (fun q : ℝ × ℝ => (p (mapP q).1).coeff (j + 1)) (φ₀, θ₀) :=
          ((hp_cd (j + 1)).continuousOn.continuousAt (isOpen_ball.mem_nhds hlam₀)).comp
            (f := fun q : ℝ × ℝ => (mapP q).1) (x := (φ₀, θ₀))
            (((continuous_circleMap 0 R).comp continuous_fst).continuousAt)
        exact (continuousAt_const.mul hc).mul (hφ_c.pow j)
      · exact ((hφprop _ (mem_ball_self hρpos) _ (mem_ball_self hεpos)).1 k).2
    have heq_nhds : (fun q : ℝ × ℝ => fiberInvDerivSum (p (mapP q).1) (mapP q).2)
        =ᶠ[𝓝 (φ₀, θ₀)]
        fun q => ∑ k : Fin n, ‖((p (mapP q).1).derivative.eval (φb k (mapP q).1 (mapP q).2))⁻¹‖ := by
      filter_upwards [hUopen.mem_nhds hmemU] with q hq
      exact (hφprop _ hq.1 _ hq.2).2.2.2
    exact (hcont_at.congr heq_nhds.symm).continuousWithinAt
  -- Convert length formula to lintegral over goodθ
  have hlen_lint : ∀ lam ∈ ball (0 : ℂ) δ,
      Erdos114.lemniscateLength (p lam) =
        ∫⁻ θ in goodθ, ENNReal.ofReal (fiberInvDerivSum (p lam) (Complex.exp ((θ : ℂ) * Complex.I))) := by
    intro lam hlam
    obtain ⟨hint, hlen⟩ := hlength_formula (p lam) (hp_md lam hlam).1 (hp_md lam hlam).2
    rw [hlen, hrest_eq]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun θ => fiberInvDerivSum_nonneg _ _)
  -- Rewrite circleAverage as ENNReal lintegral for each θ ∈ goodθ
  have hmv_enn : ∀ θ ∈ goodθ,
      ENNReal.ofReal (fiberInvDerivSum (p 0) (Complex.exp ((θ : ℂ) * Complex.I))) ≤
        ENNReal.ofReal (2 * Real.pi)⁻¹ *
          ∫⁻ φ in Set.Ioo (0 : ℝ) (2 * Real.pi),
            ENNReal.ofReal (fiberInvDerivSum (p (circleMap 0 R φ)) (Complex.exp ((θ : ℂ) * Complex.I))) := by
    intro θ hθ
    have hw : Complex.exp ((θ : ℂ) * Complex.I) ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]
    have hwS : Complex.exp ((θ : ℂ) * Complex.I) ∉ S := fun h => hθ.2 ⟨hθ.1, h⟩
    have h1 := hmv _ hw hwS
    have h2 : ENNReal.ofReal (fiberInvDerivSum (p 0) (Complex.exp ((θ : ℂ) * Complex.I))) ≤
        ENNReal.ofReal (Real.circleAverage
          (fun lam => fiberInvDerivSum (p lam) (Complex.exp ((θ : ℂ) * Complex.I))) 0 R) :=
      ENNReal.ofReal_le_ofReal h1
    rw [Real.circleAverage_def, smul_eq_mul,
      ENNReal.ofReal_mul (inv_nonneg.mpr Real.two_pi_pos.le),
      intervalIntegral.integral_of_le Real.two_pi_pos.le,
      MeasureTheory.integral_Ioc_eq_integral_Ioo] at h2
    have hcont_φ : ContinuousOn
        (fun φ : ℝ => fiberInvDerivSum (p (circleMap 0 R φ)) (Complex.exp ((θ : ℂ) * Complex.I)))
        (Set.Icc 0 (2 * Real.pi)) :=
      ((hu_cont _ hw hwS).mono (sphere_subset_closedBall.trans hcb_R)).comp
        (continuous_circleMap 0 R).continuousOn fun φ _ => circleMap_mem_sphere 0 hRpos.le φ
    have hint_φ : IntegrableOn
        (fun φ : ℝ => fiberInvDerivSum (p (circleMap 0 R φ)) (Complex.exp ((θ : ℂ) * Complex.I)))
        (Set.Ioo 0 (2 * Real.pi)) volume :=
      (hcont_φ.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    rwa [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_φ
      (ae_of_all _ fun φ => fiberInvDerivSum_nonneg _ _)] at h2
  -- Tonelli swap on (Ioo 0 (2π)) × goodθ
  let μI : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) (2 * Real.pi))
  let μG : Measure ℝ := volume.restrict goodθ
  let F : ℝ → ℝ → ℝ≥0∞ := fun φ θ =>
    ENNReal.ofReal (fiberInvDerivSum (p (circleMap 0 R φ)) (Complex.exp ((θ : ℂ) * Complex.I)))
  have hF_aem : AEMeasurable (Function.uncurry F) (μI.prod μG) := by
    have hprod_eq : μI.prod μG = volume.restrict (Set.Ioo (0 : ℝ) (2 * Real.pi) ×ˢ goodθ) :=
      Measure.prod_restrict _ _
    rw [hprod_eq]
    have hcont_sub : ContinuousOn (Function.uncurry F) (Set.Ioo (0 : ℝ) (2 * Real.pi) ×ˢ goodθ) :=
      ENNReal.continuous_ofReal.comp_continuousOn
        (hjoint_cont.mono (Set.prod_mono (Set.subset_univ _) subset_rfl))
    exact hcont_sub.aemeasurable (measurableSet_Ioo.prod hgood_meas)
  let RHS_fn : ℝ → ℝ≥0∞ := fun θ => ENNReal.ofReal (2 * Real.pi)⁻¹ * ∫⁻ φ, F φ θ ∂μI
  have htonelli : ∫⁻ θ, RHS_fn θ ∂μG =
      ENNReal.ofReal (2 * Real.pi)⁻¹ * ∫⁻ φ, (∫⁻ θ, F φ θ ∂μG) ∂μI := by
    dsimp only [RHS_fn]
    have hFaem_left : AEMeasurable (fun θ => ∫⁻ φ, F φ θ ∂μI) μG := hF_aem.lintegral_prod_left'
    rw [lintegral_const_mul'' _ hFaem_left]
    congr 1
    exact (MeasureTheory.lintegral_lintegral_swap hF_aem).symm
  have hLHS_le_RHS : Erdos114.lemniscateLength p₀ ≤ ∫⁻ θ, RHS_fn θ ∂μG := by
    rw [← hp0, hlen_lint 0 (mem_ball_self hδpos)]
    exact lintegral_mono_ae ((ae_restrict_mem hgood_meas).mono fun θ hθ => hmv_enn θ hθ)
  have hRHS_le_LHS : ∫⁻ θ, RHS_fn θ ∂μG ≤ Erdos114.lemniscateLength p₀ := by
    rw [htonelli]
    have hbound : ∀ φ : ℝ, ∫⁻ θ, F φ θ ∂μG ≤ Erdos114.lemniscateLength p₀ := fun φ => by
      have hlam : circleMap 0 R φ ∈ ball (0 : ℂ) δ :=
        hcb_R (sphere_subset_closedBall (circleMap_mem_sphere 0 hRpos.le φ))
      rw [← hlen_lint (circleMap 0 R φ) hlam]
      exact hmax (p (circleMap 0 R φ)) (hp_md _ hlam).1 (hp_md _ hlam).2
    calc ENNReal.ofReal (2 * Real.pi)⁻¹ * ∫⁻ φ, (∫⁻ θ, F φ θ ∂μG) ∂μI
        ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ * ∫⁻ _φ, Erdos114.lemniscateLength p₀ ∂μI := by
          gcongr with φ; exact hbound φ
      _ = ENNReal.ofReal (2 * Real.pi)⁻¹ * (Erdos114.lemniscateLength p₀ * μI Set.univ) := by
          rw [lintegral_const]
      _ = Erdos114.lemniscateLength p₀ := by
          have hvol : μI Set.univ = ENNReal.ofReal (2 * Real.pi) := by
            simp [μI, Real.volume_Ioo]
          rw [hvol, mul_comm (Erdos114.lemniscateLength p₀), ← mul_assoc,
            ← ENNReal.ofReal_mul (inv_nonneg.mpr Real.two_pi_pos.le),
            inv_mul_cancel₀ Real.two_pi_pos.ne', ENNReal.ofReal_one, one_mul]
  have hlen_fin : Erdos114.lemniscateLength p₀ ≠ ⊤ := by
    rw [(hlength_formula p₀ hp₀_monic hp₀_deg).2]
    exact ENNReal.ofReal_ne_top
  -- Deduce a.e. equality on goodθ
  let LHS_fn : ℝ → ℝ≥0∞ := fun θ =>
    ENNReal.ofReal (fiberInvDerivSum (p 0) (Complex.exp ((θ : ℂ) * Complex.I)))
  have hLHS_aem : AEMeasurable LHS_fn μG := by
    have hc : ContinuousOn LHS_fn goodθ := by
      intro θ hθ
      have hw : Complex.exp ((θ : ℂ) * Complex.I) ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]
      have hwS : Complex.exp ((θ : ℂ) * Complex.I) ∉ S := fun h => hθ.2 ⟨hθ.1, h⟩
      obtain ⟨ρ, ε, φb, hρpos, hεpos, _, hφcd, hφprop⟩ :=
        exists_local_root_branches hn p (fun lam h => (hp_md lam h).1)
          (fun lam h => (hp_md lam h).2) hp_cd (mem_ball_self hδpos)
          (hcrit_avoid 0 (mem_ball_self hδpos) _ hw hwS)
      have hcont_at : ContinuousAt
          (fun t : ℝ => ∑ k : Fin n, ‖((p 0).derivative.eval (φb k 0 (Complex.exp ((t : ℂ) * Complex.I))))⁻¹‖) θ := by
        refine tendsto_finsetSum _ fun k _ => ContinuousAt.norm (ContinuousAt.inv₀ ?_ ?_)
        · have hφ_c : ContinuousAt (fun t : ℝ => φb k 0 (Complex.exp ((t : ℂ) * Complex.I))) θ :=
            ((hφcd k).continuousOn.continuousAt
              ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hρpos, mem_ball_self hεpos⟩)).comp
              (continuousAt_const.prodMk (by fun_prop))
          exact (p 0).derivative.continuous.continuousAt.comp hφ_c
        · exact ((hφprop 0 (mem_ball_self hρpos) _ (mem_ball_self hεpos)).1 k).2
      have hUopen : IsOpen ((fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) ⁻¹'
          ball (Complex.exp ((θ : ℂ) * Complex.I)) ε) :=
        isOpen_ball.preimage (by fun_prop)
      have heq_nhds : (fun t : ℝ => fiberInvDerivSum (p 0) (Complex.exp ((t : ℂ) * Complex.I)))
          =ᶠ[𝓝 θ] fun t => ∑ k : Fin n, ‖((p 0).derivative.eval (φb k 0 (Complex.exp ((t : ℂ) * Complex.I))))⁻¹‖ := by
        filter_upwards [hUopen.mem_nhds (mem_ball_self hεpos)] with t ht
        exact (hφprop 0 (mem_ball_self hρpos) _ ht).2.2.2
      exact (ENNReal.continuous_ofReal.continuousAt.comp (hcont_at.congr heq_nhds.symm)).continuousWithinAt
    exact hc.aemeasurable hgood_meas
  have hRHS_aem : AEMeasurable RHS_fn μG :=
    (hF_aem.lintegral_prod_left').const_mul _
  have hle_ae : LHS_fn ≤ᵐ[μG] RHS_fn :=
    (ae_restrict_mem hgood_meas).mono fun θ hθ => hmv_enn θ hθ
  have hsub_zero : ∫⁻ θ, (RHS_fn θ - LHS_fn θ) ∂μG = 0 := by
    have hL_eq : ∫⁻ θ, LHS_fn θ ∂μG = Erdos114.lemniscateLength p₀ := by
      rw [← hp0]; exact (hlen_lint 0 (mem_ball_self hδpos)).symm
    have hR_eq : ∫⁻ θ, RHS_fn θ ∂μG = Erdos114.lemniscateLength p₀ :=
      le_antisymm hRHS_le_LHS hLHS_le_RHS
    rw [MeasureTheory.lintegral_sub' hLHS_aem (by rw [hL_eq]; exact hlen_fin) hle_ae,
      hR_eq, hL_eq, tsub_self]
  have hae_eq : ∀ᵐ θ ∂μG, LHS_fn θ = RHS_fn θ := by
    have hz := (MeasureTheory.lintegral_eq_zero_iff' (hRHS_aem.sub hLHS_aem)).mp hsub_zero
    filter_upwards [hz, hle_ae] with θ hsub hle
    exact le_antisymm hle (tsub_eq_zero_iff_le.mp hsub)
  -- Pick an open arc (θ₁, θ₂) ⊆ goodθ inside a single local-branch neighborhood around (0, w₀)
  have hgood_open : IsOpen goodθ := isOpen_Ioo.sdiff hbad_fin.isClosed
  have hgood_ne : goodθ.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hvol0 : volume (Set.Ioo (0 : ℝ) (2 * Real.pi)) = 0 := by
      have : volume.restrict goodθ Set.univ = 0 := by simp [hemp]
      rw [hrest_eq] at this
      simpa using this
    rw [Real.volume_Ioo] at hvol0
    exact (ENNReal.ofReal_pos.mpr (by linarith [Real.two_pi_pos])).ne' hvol0
  obtain ⟨θ₀, hθ₀_good⟩ := hgood_ne
  let w₀ : ℂ := Complex.exp ((θ₀ : ℂ) * Complex.I)
  have hw₀ : w₀ ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]
  have hw₀S : w₀ ∉ S := fun h => hθ₀_good.2 ⟨hθ₀_good.1, h⟩
  obtain ⟨ρ₁, ε₁, φ₀, hρ₁pos, hε₁pos, hcb₁, hφ₀_cd, hφ₀_prop⟩ :=
    exists_local_root_branches hn p (fun lam h => (hp_md lam h).1)
      (fun lam h => (hp_md lam h).2) hp_cd (mem_ball_self hδpos)
      (hcrit_avoid 0 (mem_ball_self hδpos) w₀ hw₀ hw₀S)
  let ρ : ℝ := min (ρ₁ / 2) (R / 2)
  have hρpos : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρ_lt_R : ρ < R := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hρ_lt_ρ₁ : ρ < ρ₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hopen_θ : IsOpen (goodθ ∩ (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) ⁻¹' ball w₀ ε₁) :=
    hgood_open.inter (isOpen_ball.preimage (by fun_prop))
  obtain ⟨η, hηpos, hηsub⟩ := Metric.isOpen_iff.mp hopen_θ θ₀ ⟨hθ₀_good, mem_ball_self hε₁pos⟩
  let θ₁ : ℝ := θ₀ - η / 2
  let θ₂ : ℝ := θ₀ + η / 2
  have hθ12 : θ₁ < θ₂ := by dsimp [θ₁, θ₂]; linarith
  have hIoo_sub : Set.Ioo θ₁ θ₂ ⊆ goodθ ∩ (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) ⁻¹' ball w₀ ε₁ := by
    intro θ hθ
    apply hηsub
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp only [θ₁, θ₂] at hθ
    constructor <;> linarith [hθ.1, hθ.2]
  -- Equality holds on a dense subset E_eq of Ioo θ₁ θ₂
  let E_eq : Set ℝ := { θ ∈ Set.Ioo θ₁ θ₂ |
    fiberInvDerivSum (p 0) (Complex.exp ((θ : ℂ) * Complex.I)) =
      Real.circleAverage (fun lam => fiberInvDerivSum (p lam) (Complex.exp ((θ : ℂ) * Complex.I))) 0 R }
  have hE_ae : ∀ᵐ θ ∂volume.restrict (Set.Ioo θ₁ θ₂), θ ∈ E_eq := by
    have hsub_good : Set.Ioo θ₁ θ₂ ⊆ goodθ := fun θ hθ => (hIoo_sub hθ).1
    have h1 := ae_restrict_of_ae_restrict_of_subset hsub_good hae_eq
    filter_upwards [h1, ae_restrict_mem measurableSet_Ioo] with θ hLR hθIoo
    refine ⟨hθIoo, ?_⟩
    have hθg : θ ∈ goodθ := (hIoo_sub hθIoo).1
    have hw : Complex.exp ((θ : ℂ) * Complex.I) ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]
    have hwS : Complex.exp ((θ : ℂ) * Complex.I) ∉ S := fun h => hθg.2 ⟨hθg.1, h⟩
    have hcont_φ : ContinuousOn
        (fun φ : ℝ => fiberInvDerivSum (p (circleMap 0 R φ)) (Complex.exp ((θ : ℂ) * Complex.I)))
        (Set.Icc 0 (2 * Real.pi)) :=
      ((hu_cont _ hw hwS).mono (sphere_subset_closedBall.trans hcb_R)).comp
        (continuous_circleMap 0 R).continuousOn fun φ _ => circleMap_mem_sphere 0 hRpos.le φ
    have hint_φ : IntegrableOn
        (fun φ : ℝ => fiberInvDerivSum (p (circleMap 0 R φ)) (Complex.exp ((θ : ℂ) * Complex.I)))
        (Set.Ioo 0 (2 * Real.pi)) volume :=
      (hcont_φ.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have hRHS_eq : RHS_fn θ = ENNReal.ofReal (Real.circleAverage
        (fun lam => fiberInvDerivSum (p lam) (Complex.exp ((θ : ℂ) * Complex.I))) 0 R) := by
      dsimp only [RHS_fn, F, μI]
      rw [Real.circleAverage_def, smul_eq_mul,
        ENNReal.ofReal_mul (inv_nonneg.mpr Real.two_pi_pos.le),
        intervalIntegral.integral_of_le Real.two_pi_pos.le,
        MeasureTheory.integral_Ioc_eq_integral_Ioo,
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_φ
          (ae_of_all _ fun φ => fiberInvDerivSum_nonneg _ _)]
    rw [hRHS_eq] at hLR
    have hnn1 : 0 ≤ fiberInvDerivSum (p 0) (Complex.exp ((θ : ℂ) * Complex.I)) :=
      fiberInvDerivSum_nonneg _ _
    have hnn2 : 0 ≤ Real.circleAverage
        (fun lam => fiberInvDerivSum (p lam) (Complex.exp ((θ : ℂ) * Complex.I))) 0 R :=
      Real.circleAverage_nonneg_of_nonneg fun _ _ => fiberInvDerivSum_nonneg _ _
    exact (ENNReal.ofReal_eq_ofReal_iff hnn1 hnn2).mp hLR
  -- Rigidity for every θ ∈ E_eq and every lam ∈ ball 0 ρ: branch 0 has constant inverse derivative
  let k0 : Fin n := ⟨0, by omega⟩
  have hrigid_E : ∀ θ ∈ E_eq, ∀ lam ∈ ball (0 : ℂ) ρ,
      ((p lam).derivative.eval (φ₀ k0 lam (Complex.exp ((θ : ℂ) * Complex.I))))⁻¹ =
        ((p 0).derivative.eval (φ₀ k0 0 (Complex.exp ((θ : ℂ) * Complex.I))))⁻¹ := by
    intro θ hθE lam hlam
    have hθg : θ ∈ goodθ := (hIoo_sub hθE.1).1
    have hθw : Complex.exp ((θ : ℂ) * Complex.I) ∈ ball w₀ ε₁ := (hIoo_sub hθE.1).2
    have hw : Complex.exp ((θ : ℂ) * Complex.I) ∈ sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]
    have hwS : Complex.exp ((θ : ℂ) * Complex.I) ∉ S := fun h => hθg.2 ⟨hθg.1, h⟩
    let w := Complex.exp ((θ : ℂ) * Complex.I)
    let f : Fin n → ℂ → ℂ := fun k z => ((p z).derivative.eval (φ₀ k z w))⁻¹
    have hf_diff : ∀ k : Fin n, DifferentiableOn ℂ (f k) (ball 0 ρ₁) := by
      intro k
      have hder_diff : DifferentiableOn ℂ (fun z => (p z).derivative.eval (φ₀ k z w)) (ball 0 ρ₁) := by
        have hφ_d : DifferentiableOn ℂ (fun z => φ₀ k z w) (ball 0 ρ₁) :=
          ((hφ₀_cd k).differentiableOn (by simp)).comp
            (differentiableOn_id.prodMk (differentiableOn_const w))
            (fun z hz => ⟨hz, hθw⟩)
        have hsum_d : DifferentiableOn ℂ
            (fun z => ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℂ) * (p z).coeff (j + 1) * (φ₀ k z w) ^ j)
            (ball 0 ρ₁) := by
          refine DifferentiableOn.fun_sum fun j _ => ?_
          have hc_d : DifferentiableOn ℂ (fun z => (p z).coeff (j + 1)) (ball 0 ρ₁) :=
            ((hp_cd (j + 1)).differentiableOn (by simp)).mono (ball_subset_closedBall.trans hcb₁)
          exact ((differentiableOn_const _).mul hc_d).mul (hφ_d.pow j)
        refine hsum_d.congr fun z hz => ?_
        have hzδ : z ∈ ball (0 : ℂ) δ := hcb₁ (ball_subset_closedBall hz)
        have hd : (p z).derivative.natDegree < n := by
          have := Polynomial.natDegree_derivative_le (p := p z)
          rw [(hp_md z hzδ).2] at this; omega
        rw [Polynomial.eval_eq_sum_range' hd]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [coeff_derivative]; push_cast; ring
      exact hder_diff.inv fun z hz => ((hφ₀_prop z hz w hθw).1 k).2
    have hf_dc : ∀ k : Fin n, DiffContOnCl ℂ (f k) (ball 0 ρ) := fun k => by
      refine ⟨(hf_diff k).mono (Metric.ball_subset_ball hρ_lt_ρ₁.le), ?_⟩
      rw [closure_ball 0 hρpos.ne']
      exact ((hf_diff k).mono (closedBall_subset_ball hρ_lt_ρ₁)).continuousOn
    have hval_sp : Set.EqOn (fun z => fiberInvDerivSum (p z) w)
        (fun z => ∑ k : Fin n, ‖f k z‖) (sphere 0 |ρ|) := fun z hz => by
      rw [abs_of_pos hρpos] at hz
      exact (hφ₀_prop z (closedBall_subset_ball hρ_lt_ρ₁ (sphere_subset_closedBall hz)) w hθw).2.2.2
    have hval_0 : fiberInvDerivSum (p 0) w = ∑ k : Fin n, ‖f k 0‖ :=
      (hφ₀_prop 0 (mem_ball_self hρ₁pos) w hθw).2.2.2
    have hloc_le : fiberInvDerivSum (p 0) w ≤
        Real.circleAverage (fun z => fiberInvDerivSum (p z) w) 0 ρ := by
      rw [hval_0, Real.circleAverage_congr_sphere hval_sp]
      have hint : ∀ k : Fin n, CircleIntegrable (fun z => ‖f k z‖) 0 ρ := fun k => by
        have h1 := (hf_dc k).continuousOn
        rw [closure_ball 0 hρpos.ne'] at h1
        exact (h1.mono sphere_subset_closedBall).norm.circleIntegrable hρpos.le
      rw [Real.circleAverage_fun_sum fun k _ => hint k]
      exact Finset.sum_le_sum fun k _ => norm_le_circleAverage_norm hρpos (hf_dc k)
    have hloc_eq : fiberInvDerivSum (p 0) w =
        Real.circleAverage (fun z => fiberInvDerivSum (p z) w) 0 ρ :=
      subharmonic_local_circleAverage_eq hRpos hρpos hρ_lt_R
        ((hu_cont w hw hwS).mono hcb_R) (hu_sub w hw hwS) hθE.2 hloc_le
    rw [hval_0, Real.circleAverage_congr_sphere hval_sp] at hloc_eq
    have hf0_ne : ∀ k : Fin n, f k 0 ≠ 0 := fun k =>
      inv_ne_zero ((hφ₀_prop 0 (mem_ball_self hρ₁pos) w hθw).1 k).2
    exact const_of_sum_norm_circleAverage_eq hρpos hf_dc hf0_ne hloc_eq k0 lam hlam
  -- Extend equality from the full-measure set E_eq to ALL θ ∈ Ioo θ₁ θ₂ by continuity
  have hrigid_all : ∀ lam ∈ ball (0 : ℂ) ρ, ∀ θ ∈ Set.Ioo θ₁ θ₂,
      ((p lam).derivative.eval (φ₀ k0 lam (Complex.exp ((θ : ℂ) * Complex.I))))⁻¹ =
        ((p 0).derivative.eval (φ₀ k0 0 (Complex.exp ((θ : ℂ) * Complex.I))))⁻¹ := by
    intro lam hlam θ hθ
    have hlam_ρ₁ : lam ∈ ball (0 : ℂ) ρ₁ := Metric.ball_subset_ball hρ_lt_ρ₁.le hlam
    have hc_lhs : ContinuousOn
        (fun t : ℝ => ((p lam).derivative.eval (φ₀ k0 lam (Complex.exp ((t : ℂ) * Complex.I))))⁻¹)
        (Set.Ioo θ₁ θ₂) := by
      intro t ht
      have hwt : Complex.exp ((t : ℂ) * Complex.I) ∈ ball w₀ ε₁ := Set.mem_preimage.mp (hIoo_sub ht).2
      have hφ_c : ContinuousAt (fun s : ℝ => φ₀ k0 lam (Complex.exp ((s : ℂ) * Complex.I))) t :=
        ((hφ₀_cd k0).continuousOn.continuousAt
          ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hlam_ρ₁, hwt⟩)).comp
          (continuousAt_const.prodMk (by fun_prop))
      exact (((p lam).derivative.continuous.continuousAt.comp hφ_c).inv₀
        ((hφ₀_prop lam hlam_ρ₁ _ hwt).1 k0).2).continuousWithinAt
    have hc_rhs : ContinuousOn
        (fun t : ℝ => ((p 0).derivative.eval (φ₀ k0 0 (Complex.exp ((t : ℂ) * Complex.I))))⁻¹)
        (Set.Ioo θ₁ θ₂) := by
      intro t ht
      have hwt : Complex.exp ((t : ℂ) * Complex.I) ∈ ball w₀ ε₁ := Set.mem_preimage.mp (hIoo_sub ht).2
      have hφ_c : ContinuousAt (fun s : ℝ => φ₀ k0 0 (Complex.exp ((s : ℂ) * Complex.I))) t :=
        ((hφ₀_cd k0).continuousOn.continuousAt
          ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hρ₁pos, hwt⟩)).comp
          (continuousAt_const.prodMk (by fun_prop))
      exact (((p 0).derivative.continuous.continuousAt.comp hφ_c).inv₀
        ((hφ₀_prop 0 (mem_ball_self hρ₁pos) _ hwt).1 k0).2).continuousWithinAt
    by_contra hne
    have hdiff_c := (hc_lhs.sub hc_rhs) θ hθ
    let dθ : ℂ := ((p lam).derivative.eval (φ₀ k0 lam (Complex.exp ((θ : ℂ) * Complex.I))))⁻¹ -
        ((p 0).derivative.eval (φ₀ k0 0 (Complex.exp ((θ : ℂ) * Complex.I))))⁻¹
    have hpos : 0 < ‖dθ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    rcases Metric.continuousWithinAt_iff.mp hdiff_c (‖dθ‖ / 2) (by linarith) with ⟨δc, hδcpos, hδc⟩
    let a := max θ₁ (θ - δc / 2)
    let b := min θ₂ (θ + δc / 2)
    have hab : a < b := by
      simp only [a, b, lt_min_iff, max_lt_iff]
      exact ⟨⟨hθ12, by linarith [hθ.2]⟩, ⟨by linarith [hθ.1], by linarith⟩⟩
    have hsub_ab : Set.Ioo a b ⊆ Set.Ioo θ₁ θ₂ := fun t ht =>
      ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    have hvol : 0 < volume (Set.Ioo a b) := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
    have hzero_compl : volume { t ∈ Set.Ioo θ₁ θ₂ | t ∉ E_eq } = 0 := by
      have h2 := hE_ae
      rw [ae_restrict_iff' measurableSet_Ioo, Filter.Eventually, mem_ae_iff] at h2
      convert h2 using 2
      ext t
      simp [and_assoc]
    have hinc : Set.Ioo a b ⊆ { t ∈ Set.Ioo θ₁ θ₂ | t ∉ E_eq } := by
      intro t ht
      refine ⟨hsub_ab ht, fun htE => ?_⟩
      have htd : dist t θ < δc := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [lt_of_le_of_lt (le_max_right θ₁ (θ - δc / 2)) ht.1],
               by linarith [lt_of_lt_of_le ht.2 (min_le_right θ₂ (θ + δc / 2))]⟩
      have h1 := hδc (hsub_ab ht) htd
      rw [dist_eq_norm] at h1
      dsimp only [Pi.sub_apply] at h1
      rw [hrigid_E t htE lam hlam, sub_self, zero_sub, norm_neg] at h1
      change ‖dθ‖ < ‖dθ‖ / 2 at h1
      linarith
    have hle := measure_mono (μ := volume) hinc
    rw [hzero_compl, nonpos_iff_eq_zero] at hle
    exact hvol.ne' hle
  -- For each lam ∈ ball 0 ρ, integrate in θ to get p lam (z + c) = p₀ z, hence v₀ + lam ∈ critVals(p₀)
  have hcrit_mem : ∀ lam ∈ ball (0 : ℂ) ρ,
      p₀.eval ζ_bad + lam ∈ (p₀.derivative.roots.map (fun z => p₀.eval z)).toFinset := by
    intro lam hlam
    have hlam_ρ₁ : lam ∈ ball (0 : ℂ) ρ₁ := Metric.ball_subset_ball hρ_lt_ρ₁.le hlam
    have hlam_δ : lam ∈ ball (0 : ℂ) δ := hcb₁ (ball_subset_closedBall hlam_ρ₁)
    let ψ : ℝ → ℂ := fun θ =>
      φ₀ k0 lam (Complex.exp ((θ : ℂ) * Complex.I)) - φ₀ k0 0 (Complex.exp ((θ : ℂ) * Complex.I))
    have hderiv_φ : ∀ (z₀' : ℂ) (hz₀' : z₀' ∈ ball (0 : ℂ) ρ₁) (θ : ℝ) (hθ : θ ∈ Set.Ioo θ₁ θ₂),
        HasDerivAt (fun t : ℝ => φ₀ k0 z₀' (Complex.exp ((t : ℂ) * Complex.I)))
          (((p z₀').derivative.eval (φ₀ k0 z₀' (Complex.exp ((θ : ℂ) * Complex.I))))⁻¹ *
            (Complex.I * Complex.exp ((θ : ℂ) * Complex.I))) θ := by
      intro z₀' hz₀' θ hθ
      have hw : Complex.exp ((θ : ℂ) * Complex.I) ∈ ball w₀ ε₁ := (hIoo_sub hθ).2
      have hdiff_w : DifferentiableAt ℂ (fun w => φ₀ k0 z₀' w) (Complex.exp ((θ : ℂ) * Complex.I)) :=
        (((hφ₀_cd k0).differentiableOn (by simp)).differentiableAt
          ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hz₀', hw⟩)).comp _
          (differentiableAt_const z₀' |>.prodMk differentiableAt_id)
      have hcomp_id : (fun w => (p z₀').eval (φ₀ k0 z₀' w)) =ᶠ[𝓝 (Complex.exp ((θ : ℂ) * Complex.I))] id := by
        filter_upwards [isOpen_ball.mem_nhds hw] with w hw'
        exact ((hφ₀_prop z₀' hz₀' w hw').1 k0).1
      have hder_comp : HasDerivAt (fun w => (p z₀').eval (φ₀ k0 z₀' w))
          ((p z₀').derivative.eval (φ₀ k0 z₀' (Complex.exp ((θ : ℂ) * Complex.I))) *
            deriv (fun w => φ₀ k0 z₀' w) (Complex.exp ((θ : ℂ) * Complex.I)))
          (Complex.exp ((θ : ℂ) * Complex.I)) :=
        (Polynomial.hasDerivAt (p z₀') _).comp _ hdiff_w.hasDerivAt
      have h1 : (p z₀').derivative.eval (φ₀ k0 z₀' (Complex.exp ((θ : ℂ) * Complex.I))) *
          deriv (fun w => φ₀ k0 z₀' w) (Complex.exp ((θ : ℂ) * Complex.I)) = 1 :=
        (hder_comp.congr_of_eventuallyEq hcomp_id.symm).unique (hasDerivAt_id _)
      have hdw : HasDerivAt (fun w => φ₀ k0 z₀' w)
          (((p z₀').derivative.eval (φ₀ k0 z₀' (Complex.exp ((θ : ℂ) * Complex.I))))⁻¹)
          (Complex.exp ((θ : ℂ) * Complex.I)) := by
        have hne : (p z₀').derivative.eval (φ₀ k0 z₀' (Complex.exp ((θ : ℂ) * Complex.I))) ≠ 0 :=
          ((hφ₀_prop z₀' hz₀' _ hw).1 k0).2
        have hdeq : deriv (fun w => φ₀ k0 z₀' w) (Complex.exp ((θ : ℂ) * Complex.I)) =
            ((p z₀').derivative.eval (φ₀ k0 z₀' (Complex.exp ((θ : ℂ) * Complex.I))))⁻¹ := by
          apply mul_left_cancel₀ hne; rw [h1, mul_inv_cancel₀ hne]
        rw [← hdeq]; exact hdiff_w.hasDerivAt
      have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
          (Complex.I * Complex.exp ((θ : ℂ) * Complex.I)) θ := by
        have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ :=
          (((hasDerivAt_id θ).ofReal_comp).mul_const Complex.I).congr_deriv (one_mul _)
        have h2 := ((Complex.hasDerivAt_exp ((θ : ℂ) * Complex.I)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt θ hlin
        exact h2.congr_deriv (by simp [mul_comm])
      have hres := (hdw.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt θ hexp
      exact hres.congr_deriv (by simp [mul_comm])
    have hψ_deriv0 : ∀ θ ∈ Set.Ioo θ₁ θ₂, HasDerivAt ψ 0 θ := by
      intro θ hθ
      have h1 := hderiv_φ lam hlam_ρ₁ θ hθ
      have h2 := hderiv_φ 0 (mem_ball_self hρ₁pos) θ hθ
      have hsub := h1.sub h2
      rw [hrigid_all lam hlam θ hθ, sub_self] at hsub
      exact hsub
    have hψ_const : ∀ θ ∈ Set.Ioo θ₁ θ₂, ψ θ = ψ θ₀ := by
      have hreal_const : ∀ (f : ℝ → ℝ), (∀ t ∈ Set.Ioo θ₁ θ₂, HasDerivAt f 0 t) →
          ∀ a ∈ Set.Ioo θ₁ θ₂, ∀ b ∈ Set.Ioo θ₁ θ₂, a < b → f b = f a := by
        intro f hf a ha b hb hab
        have hsub : Set.Icc a b ⊆ Set.Ioo θ₁ θ₂ := fun t ht =>
          ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hb.2⟩
        obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hab
          (fun t ht => (hf t (hsub ht)).continuousAt.continuousWithinAt)
          (fun t ht => hf t (hsub (Set.Ioo_subset_Icc_self ht)))
        have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
        have : f b - f a = 0 := by
          have := (div_eq_zero_iff.mp hc.symm).resolve_right hne
          exact this
        linarith
      have hψ_re : ∀ t ∈ Set.Ioo θ₁ θ₂, HasDerivAt (fun s => (ψ s).re) 0 t := fun t ht =>
        (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hψ_deriv0 t ht)).congr_deriv (by simp)
      have hψ_im : ∀ t ∈ Set.Ioo θ₁ θ₂, HasDerivAt (fun s => (ψ s).im) 0 t := fun t ht =>
        (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hψ_deriv0 t ht)).congr_deriv (by simp)
      have hθ₀_in : θ₀ ∈ Set.Ioo θ₁ θ₂ := by dsimp [θ₁, θ₂]; constructor <;> linarith
      intro θ hθ
      rcases lt_trichotomy θ θ₀ with hlt | rfl | hgt
      · exact Complex.ext (hreal_const _ hψ_re θ hθ θ₀ hθ₀_in hlt).symm
          (hreal_const _ hψ_im θ hθ θ₀ hθ₀_in hlt).symm
      · rfl
      · exact Complex.ext (hreal_const _ hψ_re θ₀ hθ₀_in θ hθ hgt)
          (hreal_const _ hψ_im θ₀ hθ₀_in θ hθ hgt)
    let c : ℂ := ψ θ₀
    have hpoly_eq : (p lam).comp (X + C c) = p₀ := by
      by_contra hne
      have hdiff_ne : (p lam).comp (X + C c) - p₀ ≠ 0 := sub_ne_zero.mpr hne
      have hroot : ∀ θ ∈ Set.Ioo θ₁ θ₂,
          ((p lam).comp (X + C c) - p₀).IsRoot (φ₀ k0 0 (Complex.exp ((θ : ℂ) * Complex.I))) := by
        intro θ hθ
        have hψθ : φ₀ k0 lam (Complex.exp ((θ : ℂ) * Complex.I)) =
            φ₀ k0 0 (Complex.exp ((θ : ℂ) * Complex.I)) + c := by
          have := hψ_const θ hθ; dsimp only [ψ] at this; linear_combination this
        simp only [Polynomial.IsRoot, eval_sub, eval_comp, eval_add, eval_X, eval_C]
        rw [← hψθ, ((hφ₀_prop lam hlam_ρ₁ _ (Set.mem_preimage.mp (hIoo_sub hθ).2)).1 k0).1, ← hp0,
          ((hφ₀_prop 0 (mem_ball_self hρ₁pos) _ (Set.mem_preimage.mp (hIoo_sub hθ).2)).1 k0).1, sub_self]
      have hinj_z : Set.InjOn (fun θ : ℝ => φ₀ k0 0 (Complex.exp ((θ : ℂ) * Complex.I)))
          (Set.Ioo θ₁ θ₂) := by
        intro a ha b hb heq
        dsimp only at heq
        have hwa : Complex.exp ((a : ℂ) * Complex.I) ∈ ball w₀ ε₁ := Set.mem_preimage.mp (hIoo_sub ha).2
        have hwb : Complex.exp ((b : ℂ) * Complex.I) ∈ ball w₀ ε₁ := Set.mem_preimage.mp (hIoo_sub hb).2
        have hev : Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) := by
          rw [← ((hφ₀_prop 0 (mem_ball_self hρ₁pos) _ hwa).1 k0).1,
              ← ((hφ₀_prop 0 (mem_ball_self hρ₁pos) _ hwb).1 k0).1, heq]
        have haI : a ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) := (hIoo_sub ha).1.1
        have hbI : b ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) := (hIoo_sub hb).1.1
        rw [Complex.exp_eq_exp_iff_exists_int] at hev
        rcases hev with ⟨k, hk⟩
        have him : a = b + (k : ℝ) * (2 * Real.pi) := by
          have h1 := congrArg Complex.im hk
          simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero, sub_zero,
            Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat] at h1
          linarith
        have hk0 : k = 0 := by
          by_contra hkne
          rcases lt_or_gt_of_ne hkne with hlt | hgt
          · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
            nlinarith [haI.1, hbI.2, Real.two_pi_pos]
          · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hgt
            nlinarith [haI.2, hbI.1, Real.two_pi_pos]
        rw [hk0] at him; simp at him; exact him
      have hinf : (Set.Ioo θ₁ θ₂).Infinite := Set.Ioo_infinite hθ12
      have hinf_img : ((fun θ : ℝ => φ₀ k0 0 (Complex.exp ((θ : ℂ) * Complex.I))) '' Set.Ioo θ₁ θ₂).Infinite :=
        hinf.image hinj_z
      have hfin_roots : ((fun θ : ℝ => φ₀ k0 0 (Complex.exp ((θ : ℂ) * Complex.I))) '' Set.Ioo θ₁ θ₂).Finite :=
        (((p lam).comp (X + C c) - p₀).roots.toFinset).finite_toSet.subset fun z hz => by
          rcases hz with ⟨θ, hθ, rfl⟩
          exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hdiff_ne).mpr (hroot θ hθ))
      exact hinf_img hfin_roots
    -- Every critical value of p lam is a critical value of p₀
    obtain ⟨x, hx_crit, hx_val⟩ := hcrit_move lam hlam_δ
    have hder_eq : (p lam).derivative.comp (X + C c) = p₀.derivative := by
      have h := congrArg Polynomial.derivative hpoly_eq
      rw [Polynomial.derivative_comp, derivative_add, derivative_X, derivative_C, add_zero, one_mul] at h
      exact h
    have hx_p0_crit : p₀.derivative.IsRoot (x - c) := by
      change p₀.derivative.eval (x - c) = 0
      rw [← hder_eq, eval_comp, eval_add, eval_X, eval_C, sub_add_cancel]
      exact hx_crit
    have hx_p0_val : p₀.eval (x - c) = p₀.eval ζ_bad + lam := by
      calc p₀.eval (x - c) = ((p lam).comp (X + C c)).eval (x - c) := by rw [hpoly_eq]
        _ = (p lam).eval x := by rw [eval_comp, eval_add, eval_X, eval_C, sub_add_cancel]
        _ = p₀.eval ζ_bad + lam := hx_val
    have hp₀'_ne : p₀.derivative ≠ 0 := by
      intro h0
      have hp₀_coeff_n : p₀.coeff n = 1 := by
        calc p₀.coeff n = p₀.leadingCoeff := by rw [Polynomial.leadingCoeff, hp₀_deg]
          _ = 1 := hp₀_monic.leadingCoeff
      have hlc : p₀.derivative.coeff (n - 1) = (n : ℂ) := by
        rw [coeff_derivative, Nat.sub_add_cancel (by omega), hp₀_coeff_n, one_mul]
        exact_mod_cast (Nat.sub_add_cancel (by omega))
      rw [h0, coeff_zero] at hlc
      exact (Nat.cast_ne_zero (R := ℂ).mpr (by omega)) hlc.symm
    rw [← hx_p0_val, Multiset.mem_toFinset]
    exact Multiset.mem_map.mpr ⟨x - c, (Polynomial.mem_roots hp₀'_ne).mpr hx_p0_crit, rfl⟩
  -- Contradiction: { p₀.eval ζ_bad + lam | lam ∈ ball 0 ρ } is infinite, yet subset of a Finset
  have hinf_ball : ((fun lam : ℂ => p₀.eval ζ_bad + lam) '' ball (0 : ℂ) ρ).Infinite := by
    let seq : ℕ → ℂ := fun m => (((ρ / 2) / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)
    have hseq_mem : ∀ m : ℕ, seq m ∈ ball (0 : ℂ) ρ := fun m => by
      rw [mem_ball_zero_iff]
      have hmpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
      have hnn : 0 ≤ (ρ / 2) / ((m + 1 : ℕ) : ℝ) := by positivity
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      have h1 : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
      have hdiv : (ρ / 2) / ((m + 1 : ℕ) : ℝ) ≤ ρ / 2 := div_le_self (by linarith) h1
      linarith
    have hseq_inj : Function.Injective (fun m : ℕ => p₀.eval ζ_bad + seq m) := by
      intro m₁ m₂ heq
      have h1 : seq m₁ = seq m₂ := add_left_cancel heq
      have h2 : (ρ / 2) / ((m₁ + 1 : ℕ) : ℝ) = (ρ / 2) / ((m₂ + 1 : ℕ) : ℝ) :=
        Complex.ofReal_injective h1
      have h3 : ((m₁ + 1 : ℕ) : ℝ) = ((m₂ + 1 : ℕ) : ℝ) := by
        have hρ2 : ρ / 2 ≠ 0 := by linarith
        have hm1 : ((m₁ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hm2 : ((m₂ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hρ2, hm1, hm2] at h2
        linarith
      have h4 : m₁ + 1 = m₂ + 1 := by exact_mod_cast h3
      omega
    exact (Set.infinite_range_of_injective hseq_inj).mono (by
      rintro _ ⟨m, rfl⟩
      exact ⟨seq m, hseq_mem m, rfl⟩)
  have hfin_ball : ((fun lam : ℂ => p₀.eval ζ_bad + lam) '' ball (0 : ℂ) ρ).Finite :=
    ((p₀.derivative.roots.map (fun z => p₀.eval z)).toFinset).finite_toSet.subset (by
      rintro _ ⟨lam, hlam, rfl⟩
      exact hcrit_mem lam hlam)
  exact hinf_ball hfin_ball

/-- Eremenko-Hayman H1 (`pr6299.diff` exact signature) from Lemma 4 extremizer existence
    and the circle-integral length formula. -/
theorem erdos114_H1_of_extremizer
    (hexist : ∀ n : ℕ, 0 < n →
      ∃ q : ℂ[X], q.Monic ∧ q.natDegree = n ∧
        ∀ p : ℂ[X], p.Monic → p.natDegree = n →
          Erdos114.lemniscateLength p ≤ Erdos114.lemniscateLength q)
    (hlength_formula : ∀ n : ℕ, 1 ≤ n → ∀ p : ℂ[X], p.Monic → p.natDegree = n →
      IntegrableOn (circleIntegrand p) (Set.Ioo (0 : ℝ) (2 * Real.pi)) volume ∧
      Erdos114.lemniscateLength p =
        ENNReal.ofReal (∫ θ in Set.Ioo (0 : ℝ) (2 * Real.pi), circleIntegrand p θ)) :
    ∀ n : ℕ, 0 < n → ∀ p : ℂ[X], p.Monic → p.natDegree = n →
      ∃ q : ℂ[X], q.Monic ∧ q.natDegree = n ∧
        Erdos114.lemniscateLength p ≤ Erdos114.lemniscateLength q ∧
        ∀ x : ℂ, q.derivative.IsRoot x → ‖q.eval x‖ = 1 := by
  intro n hn p hp hdeg
  obtain ⟨q, hq_monic, hq_deg, hq_max⟩ := hexist n hn
  refine ⟨q, hq_monic, hq_deg, hq_max p hp hdeg, ?_⟩
  exact extremizer_critical_values_on_unit_circle hn q hq_monic hq_deg hq_max (hlength_formula n hn)

end OMA.Erdos114Lemma5
end Lemma5Part


namespace OMA.Erdos114H1

open Polynomial MeasureTheory

/-- Full Eremenko-Hayman H1 (exact signature of OMA.R_Erdos114_erdos_114_R1.H1 in PR 6299):
    in every positive degree, every monic polynomial is majorized in lemniscate length by a
    monic polynomial of the same degree whose critical values all lie on the unit circle. -/
theorem erdos114_H1 :
    ∀ n : ℕ, 0 < n → ∀ p : ℂ[X], p.Monic → p.natDegree = n →
      ∃ q : ℂ[X], q.Monic ∧ q.natDegree = n ∧
        Erdos114.lemniscateLength p ≤ Erdos114.lemniscateLength q ∧
        ∀ x : ℂ, q.derivative.IsRoot x → ‖q.eval x‖ = 1 :=
  OMA.Erdos114Lemma5.erdos114_H1_of_extremizer
    OMA.Erdos114Lemma4.exists_extremal_monic_poly
    (fun _ hn _ hp hdeg => OMA.Erdos114Lemma4.lemniscateLength_eq_ofReal_integral hn hp hdeg)

end OMA.Erdos114H1

theorem OMA.solution : OMA.R_Erdos114_erdos_114_R1.H1 :=
  OMA.Erdos114H1.erdos114_H1
