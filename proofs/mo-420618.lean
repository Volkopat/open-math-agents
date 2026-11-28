import OMAStatements.S_mo_420618

namespace OMA.P_mo_420618

open OMA.S_mo_420618 Set Metric Filter
open scoped Topology ENNReal

private lemma weight_pos (j : ℕ) : 0 < weight j := by
  unfold weight
  positivity

private lemma two_pow_mul_weight (j : ℕ) : (2 : ℝ) ^ j * weight j = 1 := by
  unfold weight
  rw [← mul_pow]
  norm_num

private lemma lp_norm_eq_tsum_abs (x : E) : ‖x‖ = ∑' j : ℕ, |x j| := by
  have hp : 0 < (1 : ℝ≥0∞).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow hp]
  simp [Real.norm_eq_abs]

private lemma lp_summable_abs (x : E) : Summable (fun j : ℕ => |x j|) := by
  have hp : 0 < (1 : ℝ≥0∞).toReal := by norm_num
  have h := (memℓp_gen_iff hp).mp (lp.memℓp x)
  simpa [Real.norm_eq_abs] using h

private lemma lp_memℓp_of_summable_abs {f : ℕ → ℝ} (hf : Summable (fun j => |f j|)) :
    Memℓp f 1 := by
  have hp : 0 < (1 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp]
  simpa [Real.norm_eq_abs] using hf

private lemma continuous_coord (j : ℕ) : Continuous (fun x : E => x j) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
  have h := lp.norm_apply_le_norm (by norm_num : (1 : ℝ≥0∞) ≠ 0) (x - y) j
  simpa [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, lp.coeFn_sub] using h

private lemma axis_apply (j i : ℕ) : axis j i = if i = j then 1 else 0 := by
  unfold axis
  simp [lp.single_apply, Pi.single_apply]

private lemma norm_axis (j : ℕ) : ‖axis j‖ = 1 := by
  unfold axis
  simp [lp.norm_single]

private lemma gauge_zero : S_mo_420618.gauge 0 = 0 := by
  unfold S_mo_420618.gauge
  simp

private lemma gauge_add_le (x y : E) :
    S_mo_420618.gauge (x + y) ≤ S_mo_420618.gauge x + S_mo_420618.gauge y := by
  unfold S_mo_420618.gauge
  refine iSup_le fun j => ?_
  have hle : (2 : ℝ) ^ j * |(x + y) j| ≤ (2 : ℝ) ^ j * |x j| + (2 : ℝ) ^ j * |y j| := by
    rw [lp.coeFn_add, Pi.add_apply, ← mul_add]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
  calc
    ENNReal.ofReal ((2 : ℝ) ^ j * |(x + y) j|)
      ≤ ENNReal.ofReal ((2 : ℝ) ^ j * |x j| + (2 : ℝ) ^ j * |y j|) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal ((2 : ℝ) ^ j * |x j|) + ENNReal.ofReal ((2 : ℝ) ^ j * |y j|) :=
        ENNReal.ofReal_add (by positivity) (by positivity)
    _ ≤ (⨆ k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ k * |x k|)) +
        (⨆ k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ k * |y k|)) :=
        add_le_add (le_iSup (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ k * |x k|)) j)
          (le_iSup (fun k : ℕ => ENNReal.ofReal ((2 : ℝ) ^ k * |y k|)) j)

private lemma gauge_smul (r : ℝ) (x : E) :
    S_mo_420618.gauge (r • x) = ENNReal.ofReal |r| * S_mo_420618.gauge x := by
  by_cases hr : r = 0
  · subst hr
    simp [gauge_zero]
  · unfold S_mo_420618.gauge
    rw [ENNReal.mul_iSup]
    congr 1
    ext j
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, abs_mul]
    rw [← ENNReal.ofReal_mul (abs_nonneg r)]
    congr 1
    ring

private lemma lowerSemicontinuous_gauge : LowerSemicontinuous S_mo_420618.gauge := by
  unfold S_mo_420618.gauge
  refine lowerSemicontinuous_iSup fun j => ?_
  exact (ENNReal.continuous_ofReal.comp
    (continuous_const.mul (continuous_abs.comp (continuous_coord j)))).lowerSemicontinuous

private lemma mem_unitBall_iff (x : E) : x ∈ unitBall ↔ ∀ j : ℕ, |x j| ≤ weight j := by
  change S_mo_420618.gauge x ≤ 1 ↔ ∀ j : ℕ, |x j| ≤ weight j
  unfold S_mo_420618.gauge
  rw [iSup_le_iff]
  refine forall_congr' fun j => ?_
  have hle1 : ∀ r : ℝ, ENNReal.ofReal r ≤ 1 ↔ r ≤ 1 := fun r => by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one]
  rw [hle1]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  constructor
  · intro h
    calc
      |x j| = ((2 : ℝ) ^ j * |x j|) * weight j := by
        linear_combination -|x j| * two_pow_mul_weight j
      _ ≤ 1 * weight j := mul_le_mul_of_nonneg_right h (le_of_lt (weight_pos j))
      _ = weight j := one_mul _
  · intro h
    calc
      (2 : ℝ) ^ j * |x j| ≤ (2 : ℝ) ^ j * weight j := mul_le_mul_of_nonneg_left h (le_of_lt h2)
      _ = 1 := two_pow_mul_weight j

private lemma tsum_split_range {f : ℕ → ℝ} (hf : Summable f) (N : ℕ) :
    (∑ j ∈ Finset.range N, f j) + (∑' j : ℕ, if j < N then (0 : ℝ) else f j) = ∑' j : ℕ, f j := by
  have h1 : Summable (fun j : ℕ => if j < N then f j else 0) :=
    summable_of_ne_finset_zero (s := Finset.range N) fun j hj => by
      simp [Finset.mem_range] at hj
      simp [hj]
  have h2 : Summable (fun j : ℕ => if j < N then (0 : ℝ) else f j) := by
    have heq : (fun j : ℕ => if j < N then (0 : ℝ) else f j) =
        fun j => f j - (if j < N then f j else 0) := by
      ext j
      split_ifs <;> ring
    rw [heq]
    exact hf.sub h1
  have hsum1 : ∑' j : ℕ, (if j < N then f j else 0) = ∑ j ∈ Finset.range N, f j := by
    rw [tsum_eq_sum (s := Finset.range N)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp [Finset.mem_range.mp hj]
    · intro j hj
      simp [Finset.mem_range] at hj
      simp [hj]
  rw [← hsum1, ← h1.tsum_add h2]
  congr 1
  ext j
  split_ifs <;> ring

private lemma tendsto_tail_zero {f : ℕ → ℝ} (hf : Summable f) :
    Tendsto (fun N : ℕ => ∑' j : ℕ, if j < N then (0 : ℝ) else f j) atTop (𝓝 0) := by
  have heq : (fun N : ℕ => ∑' j : ℕ, if j < N then (0 : ℝ) else f j) =
      fun N => (∑' j : ℕ, f j) - ∑ j ∈ Finset.range N, f j := by
    ext N
    linarith [tsum_split_range hf N]
  rw [heq]
  have h := hf.hasSum.tendsto_sum_nat
  simpa using (tendsto_const_nhds (x := ∑' j : ℕ, f j)).sub h

private lemma dense_finite_gauge : Dense {x : E | S_mo_420618.gauge x < ⊤} := by
  rw [Metric.dense_iff]
  intro x ε hε
  have hf := lp_summable_abs x
  have ht := tendsto_tail_zero hf
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N, hN⟩ := ht ε hε
  let yfun : ℕ → ℝ := fun j => if j < N then x j else 0
  have hy_sum : Summable (fun j => |yfun j|) :=
    summable_of_ne_finset_zero (s := Finset.range N) fun j hj => by
      simp [Finset.mem_range] at hj
      simp [yfun, hj]
  let y : E := ⟨yfun, lp_memℓp_of_summable_abs hy_sum⟩
  refine ⟨y, ?_, ?_⟩
  · change dist y x < ε
    rw [dist_comm, dist_eq_norm, lp_norm_eq_tsum_abs]
    have hdiff : (fun j : ℕ => |(x - y) j|) = fun j => if j < N then 0 else |x j| := by
      ext j
      change |x j - yfun j| = _
      dsimp [yfun]
      split_ifs <;> simp
    rw [hdiff]
    have hdist := hN N le_rfl
    rw [Real.dist_eq, sub_zero] at hdist
    exact lt_of_le_of_lt (le_abs_self _) hdist
  · change S_mo_420618.gauge y < ⊤
    let M : ℝ := ∑ j ∈ Finset.range N, (2 : ℝ) ^ j * |x j|
    have hM_nonneg : 0 ≤ M := Finset.sum_nonneg fun j _ => by positivity
    have hle : S_mo_420618.gauge y ≤ ENNReal.ofReal M := by
      unfold S_mo_420618.gauge
      refine iSup_le fun j => ENNReal.ofReal_le_ofReal ?_
      change (2 : ℝ) ^ j * |yfun j| ≤ M
      dsimp [yfun]
      split_ifs with hj
      · exact Finset.single_le_sum (f := fun k => (2 : ℝ) ^ k * |x k|)
          (fun k _ => by positivity) (Finset.mem_range.mpr hj)
      · simp [hM_nonneg]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

private abbrev Cube := ∀ j : ℕ, Icc (-weight j) (weight j)

private lemma summable_weight : Summable weight := by
  unfold weight
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

private noncomputable def fromCube (u : Cube) : E :=
  ⟨fun j => (u j : ℝ), lp_memℓp_of_summable_abs <|
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
      (fun j => abs_le.mpr (u j).2) summable_weight⟩

private lemma range_fromCube : Set.range fromCube = unitBall := by
  ext x
  rw [mem_unitBall_iff]
  constructor
  · rintro ⟨u, rfl⟩ j
    exact abs_le.mpr (u j).2
  · intro hx
    refine ⟨fun j => ⟨x j, abs_le.mp (hx j)⟩, ?_⟩
    ext j
    rfl

private lemma continuous_fromCube : Continuous fromCube := by
  rw [continuous_iff_continuousAt]
  intro u
  rw [Metric.continuousAt_iff']
  intro ε hε
  have h2w : Summable (fun j : ℕ => 2 * weight j) := summable_weight.mul_left 2
  have ht := tendsto_tail_zero h2w
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N, hN⟩ := ht (ε / 2) (half_pos hε)
  let M := N + 1
  have htail : (∑' j : ℕ, if j < M then (0 : ℝ) else 2 * weight j) < ε / 2 := by
    have hdist := hN M (Nat.le_succ N)
    rw [Real.dist_eq, sub_zero] at hdist
    exact lt_of_le_of_lt (le_abs_self _) hdist
  let δ : ℝ := ε / (2 * (M : ℝ))
  have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
  have hδ : 0 < δ := by positivity
  let U : Set Cube := ⋂ j ∈ Finset.range M, {v : Cube | |(v j : ℝ) - (u j : ℝ)| < δ}
  have hU_mem : U ∈ 𝓝 u := by
    refine (Filter.biInter_finset_mem (Finset.range M)).mpr fun j _ => ?_
    have hopen : IsOpen {v : Cube | |(v j : ℝ) - (u j : ℝ)| < δ} := by
      have hc : Continuous (fun v : Cube => |(v j : ℝ) - (u j : ℝ)|) :=
        continuous_abs.comp ((continuous_subtype_val.comp (continuous_apply j)).sub continuous_const)
      exact isOpen_lt hc continuous_const
    refine hopen.mem_nhds ?_
    simp [hδ]
  refine Filter.mem_of_superset hU_mem fun v hv => ?_
  change dist (fromCube v) (fromCube u) < ε
  rw [dist_eq_norm, lp_norm_eq_tsum_abs]
  have hdiff_sum : Summable (fun j : ℕ => |(fromCube v - fromCube u) j|) :=
    lp_summable_abs (fromCube v - fromCube u)
  rw [← tsum_split_range hdiff_sum M]
  have h1 : (∑ j ∈ Finset.range M, |(fromCube v - fromCube u) j|) < ε / 2 := by
    have hmem : ∀ j ∈ Finset.range M, |(fromCube v - fromCube u) j| < δ := by
      intro j hj
      have hvj : v ∈ {w : Cube | |(w j : ℝ) - (u j : ℝ)| < δ} :=
        Set.mem_iInter₂.mp hv j hj
      exact hvj
    calc
      ∑ j ∈ Finset.range M, |(fromCube v - fromCube u) j|
        < ∑ _j ∈ Finset.range M, δ :=
          Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero N)) hmem
      _ = (M : ℝ) * δ := by simp
      _ = ε / 2 := by
          dsimp [δ]
          field_simp [ne_of_gt hMpos]
  have h2 : (∑' j : ℕ, if j < M then (0 : ℝ) else |(fromCube v - fromCube u) j|) ≤
      ∑' j : ℕ, if j < M then (0 : ℝ) else 2 * weight j := by
    have hs1 : Summable (fun j : ℕ => if j < M then (0 : ℝ) else |(fromCube v - fromCube u) j|) := by
      have hfin : Summable (fun j : ℕ => if j < M then |(fromCube v - fromCube u) j| else 0) :=
        summable_of_ne_finset_zero (s := Finset.range M) fun j hj => by
          simp [Finset.mem_range] at hj
          simp [hj]
      have heq : (fun j : ℕ => if j < M then (0 : ℝ) else |(fromCube v - fromCube u) j|) =
          fun j => |(fromCube v - fromCube u) j| -
            (if j < M then |(fromCube v - fromCube u) j| else 0) := by
        ext j
        split_ifs <;> ring
      rw [heq]
      exact hdiff_sum.sub hfin
    have hs2 : Summable (fun j : ℕ => if j < M then (0 : ℝ) else 2 * weight j) := by
      have hfin : Summable (fun j : ℕ => if j < M then 2 * weight j else 0) :=
        summable_of_ne_finset_zero (s := Finset.range M) fun j hj => by
          simp [Finset.mem_range] at hj
          simp [hj]
      have heq : (fun j : ℕ => if j < M then (0 : ℝ) else 2 * weight j) =
          fun j => 2 * weight j - (if j < M then 2 * weight j else 0) := by
        ext j
        split_ifs <;> ring
      rw [heq]
      exact h2w.sub hfin
    refine hs1.tsum_le_tsum (fun j => ?_) hs2
    split_ifs
    · exact le_rfl
    · change |(v j : ℝ) - (u j : ℝ)| ≤ 2 * weight j
      have hvj : |(v j : ℝ)| ≤ weight j := abs_le.mpr (v j).2
      have huj : |(u j : ℝ)| ≤ weight j := abs_le.mpr (u j).2
      calc
        |(v j : ℝ) - (u j : ℝ)| ≤ |(v j : ℝ)| + |(u j : ℝ)| := abs_sub _ _
        _ ≤ weight j + weight j := add_le_add hvj huj
        _ = 2 * weight j := by ring
  linarith

private lemma isCompact_unitBall : IsCompact unitBall := by
  rw [← range_fromCube]
  exact isCompact_range continuous_fromCube

private lemma convex_unitBall : Convex ℝ unitBall := by
  intro x hx y hy a b ha hb hab
  rw [mem_unitBall_iff] at hx hy ⊢
  intro j
  rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul]
  calc
    |a * x j + b * y j| ≤ |a * x j| + |b * y j| := abs_add_le _ _
    _ = a * |x j| + b * |y j| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * weight j + b * weight j :=
        add_le_add (mul_le_mul_of_nonneg_left (hx j) ha) (mul_le_mul_of_nonneg_left (hy j) hb)
    _ = (a + b) * weight j := by ring
    _ = weight j := by rw [hab, one_mul]

private lemma balanced_unitBall : Balanced ℝ unitBall := by
  intro r hr y hy
  rcases hy with ⟨x, hx, rfl⟩
  rw [mem_unitBall_iff] at hx ⊢
  intro j
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, abs_mul]
  have hr' : |r| ≤ 1 := by simpa [Real.norm_eq_abs] using hr
  calc
    |r| * |x j| ≤ 1 * weight j := mul_le_mul hr' (hx j) (abs_nonneg _) zero_le_one
    _ = weight j := one_mul _

private lemma tilt_apply (n j : ℕ) :
    tilt n j = (if j = 0 then (1 : ℝ) else 0) +
      2 * weight (n + 1) * (if j = n + 1 then (1 : ℝ) else 0) := by
  unfold tilt
  rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    axis_apply, axis_apply]

private lemma smul_tilt_mem_unitBall_iff (n : ℕ) (r : ℝ) :
    r • tilt n ∈ unitBall ↔ r ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
  rw [mem_unitBall_iff]
  constructor
  · intro h
    have hn := h (n + 1)
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, tilt_apply] at hn
    simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add, mul_one] at hn
    rw [abs_mul, abs_of_pos (mul_pos zero_lt_two (weight_pos (n + 1)))] at hn
    have hpos : 0 < weight (n + 1) := weight_pos (n + 1)
    have hr : |r| ≤ 1 / 2 := by nlinarith
    have habs := abs_le.mp hr
    exact ⟨by linarith, by linarith⟩
  · intro hr j
    have habs : |r| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, tilt_apply]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [↓reduceIte, Nat.zero_ne_add_one, mul_zero, add_zero, mul_one]
      have hw0 : weight 0 = 1 := by simp [weight]
      rw [hw0]
      linarith
    · by_cases hjn : j = n + 1
      · subst hjn
        simp only [hj0, ↓reduceIte, zero_add, mul_one]
        rw [abs_mul, abs_of_pos (mul_pos zero_lt_two (weight_pos (n + 1)))]
        have hpos : 0 ≤ weight (n + 1) := le_of_lt (weight_pos (n + 1))
        nlinarith
      · simp only [hj0, hjn, ↓reduceIte, mul_zero, add_zero, mul_zero, abs_zero]
        exact le_of_lt (weight_pos j)

private lemma line_inter_unitBall (n : ℕ) :
    (line n : Set E) ∩ unitBall = (fun r : ℝ => r • tilt n) '' Icc (-1 / 2 : ℝ) (1 / 2) := by
  ext x
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_image]
  constructor
  · rintro ⟨hxline, hxball⟩
    rw [line, Submodule.mem_span_singleton] at hxline
    rcases hxline with ⟨r, rfl⟩
    exact ⟨r, (smul_tilt_mem_unitBall_iff n r).mp hxball, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    refine ⟨?_, (smul_tilt_mem_unitBall_iff n r).mpr hr⟩
    rw [line, Submodule.mem_span_singleton]
    exact ⟨r, rfl⟩

private lemma line_props (n : ℕ) :
    IsClosed (line n : Set E) ∧
      (Submodule.span ℝ ((line n : Set E) ∩ unitBall)).topologicalClosure = line n := by
  have hfin : FiniteDimensional ℝ (line n) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_singleton (tilt n))
  have hclosed : IsClosed (line n : Set E) := Submodule.closed_of_finiteDimensional (line n)
  refine ⟨hclosed, ?_⟩
  have hspan : Submodule.span ℝ ((line n : Set E) ∩ unitBall) = line n := by
    refine le_antisymm (Submodule.span_le.mpr Set.inter_subset_left) ?_
    change Submodule.span ℝ {tilt n} ≤ Submodule.span ℝ ((line n : Set E) ∩ unitBall)
    rw [Submodule.span_singleton_le_iff_mem]
    have hhalf : (1 / 2 : ℝ) • tilt n ∈ (line n : Set E) ∩ unitBall := by
      rw [line_inter_unitBall]
      refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
    have hmem : (1 / 2 : ℝ) • tilt n ∈ Submodule.span ℝ ((line n : Set E) ∩ unitBall) :=
      Submodule.subset_span hhalf
    have h2 := Submodule.smul_mem _ (2 : ℝ) hmem
    simpa [smul_smul] using h2
  rw [hspan]
  exact le_antisymm (Submodule.topologicalClosure_minimal (line n) le_rfl hclosed)
    (Submodule.le_topologicalClosure _)

private lemma isCompact_limitSet : IsCompact limitSet :=
  isCompact_Icc.image (continuous_id.smul continuous_const)

private lemma axis0_mem_unitBall : axis 0 ∈ unitBall := by
  rw [mem_unitBall_iff]
  intro j
  rw [axis_apply]
  split_ifs with hj
  · subst hj
    simp [weight]
  · simp [le_of_lt (weight_pos j)]

private lemma limitSet_subset_unitBall : limitSet ⊆ unitBall := by
  rintro x ⟨r, hr, rfl⟩
  have h1 : |r| ≤ 1 := abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
  exact balanced_unitBall r (by simpa [Real.norm_eq_abs] using h1) ⟨axis 0, axis0_mem_unitBall, rfl⟩

private lemma tendsto_hausdorffDist_limitSet :
    Tendsto (fun n => hausdorffDist ((line n : Set E) ∩ unitBall) limitSet) atTop (𝓝 0) := by
  have hle : ∀ n : ℕ, hausdorffDist ((line n : Set E) ∩ unitBall) limitSet ≤ weight (n + 1) := by
    intro n
    rw [line_inter_unitBall]
    have hdist_r : ∀ r ∈ Icc (-1 / 2 : ℝ) (1 / 2),
        dist (r • tilt n) (r • axis 0) ≤ weight (n + 1) := by
      intro r hr
      have habs : |r| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩
      rw [dist_eq_norm, ← smul_sub]
      have hsub : tilt n - axis 0 = (2 * weight (n + 1)) • axis (n + 1) := by
        unfold tilt
        abel
      rw [hsub, norm_smul, norm_smul, norm_axis, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (mul_pos zero_lt_two (weight_pos (n + 1)))]
      have hpos : 0 ≤ weight (n + 1) := le_of_lt (weight_pos (n + 1))
      nlinarith
    refine Metric.hausdorffDist_le_of_mem_dist (le_of_lt (weight_pos (n + 1))) ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      exact ⟨r • axis 0, ⟨r, hr, rfl⟩, hdist_r r hr⟩
    · rintro _ ⟨r, hr, rfl⟩
      exact ⟨r • tilt n, ⟨r, hr, rfl⟩, by rw [dist_comm]; exact hdist_r r hr⟩
  have ht : Tendsto (fun n : ℕ => weight (n + 1)) atTop (𝓝 0) := by
    unfold weight
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => hausdorffDist_nonneg) hle

private lemma axis0_mem_closure_span_limitSet :
    axis 0 ∈ unitBall ∩ ((Submodule.span ℝ limitSet).topologicalClosure : Set E) := by
  refine ⟨axis0_mem_unitBall, ?_⟩
  have hhalf : (1 / 2 : ℝ) • axis 0 ∈ limitSet :=
    ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hmem : (1 / 2 : ℝ) • axis 0 ∈ Submodule.span ℝ limitSet :=
    Submodule.subset_span hhalf
  have h2 := Submodule.smul_mem _ (2 : ℝ) hmem
  have haxis : axis 0 ∈ Submodule.span ℝ limitSet := by
    simpa [smul_smul] using h2
  exact Submodule.le_topologicalClosure _ haxis

private lemma axis0_not_mem_limitSet : axis 0 ∉ limitSet := by
  rintro ⟨r, hr, hreq⟩
  have h0 := congr_arg (fun x : E => x 0) hreq
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, axis_apply] at h0
  simp only [↓reduceIte, mul_one] at h0
  linarith [hr.2]

theorem main_proof : type_of% @OMA.S_mo_420618.main :=
  ⟨⟨gauge_zero, gauge_add_le, gauge_smul⟩,
    lowerSemicontinuous_gauge,
    dense_finite_gauge,
    isCompact_unitBall,
    convex_unitBall,
    balanced_unitBall,
    line_props,
    isCompact_limitSet,
    limitSet_subset_unitBall,
    tendsto_hausdorffDist_limitSet,
    axis0_mem_closure_span_limitSet,
    axis0_not_mem_limitSet⟩

end OMA.P_mo_420618

theorem OMA.solution : type_of% @OMA.S_mo_420618.main :=
  OMA.P_mo_420618.main_proof
