import OMAReductions.R_erdos_634_R1_H2_R1_H1_R1_H3_R1

/-!
# Erdos 634, step R1.H2.R1.H1.R1.H3.R1.H3: theorem:notprime120 given the rationality of the tile and its core step

Flattened from the Lean port of Beeson-Rosu / Bonfioli (formalizations of the triangle tiling
papers), restricted to the declarations this step uses.
-/

section
open scoped ENNReal
namespace Erdos634.Geometry
open MeasureTheory Set
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)
structure Tri where
  pts : Fin 3 → Plane
  indep : AffineIndependent ℝ pts
namespace Tri
def carrier (T : Tri) : Set Plane := convexHull ℝ (Set.range T.pts)
theorem convex (T : Tri) : Convex ℝ T.carrier := convex_convexHull ℝ _
theorem isCompact (T : Tri) : IsCompact T.carrier :=
  (Set.finite_range _).isCompact_convexHull ℝ
theorem measurableSet (T : Tri) : MeasurableSet T.carrier := T.isCompact.measurableSet
theorem nullMeasurableSet (T : Tri) : NullMeasurableSet T.carrier volume :=
  T.measurableSet.nullMeasurableSet
theorem volume_frontier (T : Tri) : volume (frontier T.carrier) = 0 :=
  T.convex.addHaar_frontier volume
theorem affineSpan_eq_top (T : Tri) : affineSpan ℝ T.carrier = ⊤ := by
  have h : affineSpan ℝ T.carrier = affineSpan ℝ (Set.range T.pts) :=
    affineSpan_convexHull _
  rw [h]
  exact T.indep.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
theorem interior_nonempty (T : Tri) : (interior T.carrier).Nonempty :=
  T.convex.interior_nonempty_iff_affineSpan_eq_top.mpr T.affineSpan_eq_top
theorem volume_pos (T : Tri) : 0 < volume T.carrier :=
  (isOpen_interior.measure_pos volume T.interior_nonempty).trans_le
    (measure_mono interior_subset)
end Tri
structure Dissection (N : ℕ) where
  target : Tri
  tile : Fin N → Tri
  covers : (⋃ i, (tile i).carrier) = target.carrier
  interiors_disjoint :
    Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier)
namespace Dissection
variable {N : ℕ}
theorem aedisjoint (D : Dissection N) {i j : Fin N} (hij : i ≠ j) :
    AEDisjoint volume (D.tile i).carrier (D.tile j).carrier := by
  have hsub : (D.tile i).carrier ∩ (D.tile j).carrier ⊆
      frontier (D.tile i).carrier ∪ frontier (D.tile j).carrier := by
    rintro x ⟨hxi, hxj⟩
    by_cases h1 : x ∈ interior (D.tile i).carrier
    · by_cases h2 : x ∈ interior (D.tile j).carrier
      · exfalso
        have hd : Disjoint (interior (D.tile i).carrier) (interior (D.tile j).carrier) :=
          D.interiors_disjoint hij
        exact Set.disjoint_left.mp hd h1 h2
      · exact Or.inr ⟨subset_closure hxj, h2⟩
    · exact Or.inl ⟨subset_closure hxi, h1⟩
  refine measure_mono_null hsub ?_
  exact measure_union_null (D.tile i).volume_frontier (D.tile j).volume_frontier
theorem volume_target (D : Dissection N) :
    volume D.target.carrier = ∑ i, volume (D.tile i).carrier := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N))) (f := fun i => (D.tile i).carrier)
    (fun _ _ _ _ hij => D.aedisjoint hij)
    (fun i _ => (D.tile i).nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), (D.tile i).carrier) = D.target.carrier := by
    rw [← D.covers]; simp
  rw [hU] at h
  exact h
theorem volume_target_of_congruent (D : Dissection N) (v : ℝ≥0∞)
    (hv : ∀ i, volume (D.tile i).carrier = v) :
    volume D.target.carrier = (N : ℝ≥0∞) * v := by
  rw [D.volume_target]
  simp [hv]
end Dissection
noncomputable def cornerAngle (p q r : Plane) : ℝ :=
  EuclideanGeometry.angle (V := Plane) p q r
theorem cornerAngle_sum (T : Tri) :
    cornerAngle (T.pts 1) (T.pts 0) (T.pts 2)
      + cornerAngle (T.pts 2) (T.pts 1) (T.pts 0)
      + cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi := by
  have h10 : T.pts 1 ≠ T.pts 0 := by
    intro h
    have : (1 : Fin 3) = 0 := T.indep.injective h
    exact absurd this (by decide)
  have key := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (V := Plane) (p₁ := T.pts 0) (p₂ := T.pts 1) (T.pts 2) h10
  unfold cornerAngle
  rw [EuclideanGeometry.angle_comm (V := Plane) (T.pts 1) (T.pts 0) (T.pts 2),
      EuclideanGeometry.angle_comm (V := Plane) (T.pts 2) (T.pts 1) (T.pts 0),
      EuclideanGeometry.angle_comm (V := Plane) (T.pts 0) (T.pts 2) (T.pts 1)]
  linarith [key]
def HasAngleSums {N : ℕ} (D : Dissection N) (angleAt : Plane → Fin N → ℝ) : Prop :=
  (∀ v ∈ interior D.target.carrier, ∑ i, angleAt v i = 2 * Real.pi) ∧
  (∀ v ∈ frontier D.target.carrier, v ∉ Set.range D.target.pts →
    ∑ i, angleAt v i = Real.pi) ∧
  (∀ k : Fin 3, ∑ i, angleAt (D.target.pts k) i
    = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)))
theorem tile_subset_target (D : Dissection N) (j : Fin N) :
    (D.tile j).carrier ⊆ D.target.carrier := by
  rw [← D.covers]; exact Set.subset_iUnion (fun i => (D.tile i).carrier) j
noncomputable def Tri.basis (T : Tri) : AffineBasis (Fin 3) ℝ Plane :=
  AffineBasis.mk T.pts T.indep (by
    have := T.affineSpan_eq_top
    rwa [Tri.carrier, affineSpan_convexHull] at this)
theorem Tri.carrier_eq_nonneg_coord (T : Tri) :
    T.carrier = {y | ∀ i, 0 ≤ T.basis.coord i y} := by
  have h : Set.range T.pts = Set.range (T.basis : Fin 3 → Plane) := rfl
  rw [Tri.carrier, h]
  exact T.basis.convexHull_eq_nonneg_coord
theorem Tri.inter_ball_eq_halfplane (T : Tri) (k : Fin 3) {x : Plane}
    (h1 : 0 < T.basis.coord (k + 1) x) (h2 : 0 < T.basis.coord (k + 2) x) :
    ∃ r > 0, T.carrier ∩ Metric.ball x r
           = {y | 0 ≤ T.basis.coord k y} ∩ Metric.ball x r := by
  have hfin : ∀ j i : Fin 3, i = j ∨ i = j + 1 ∨ i = j + 2 := by decide
  have hc1 : Continuous (T.basis.coord (k + 1)) := AffineMap.continuous_of_finiteDimensional _
  have hc2 : Continuous (T.basis.coord (k + 2)) := AffineMap.continuous_of_finiteDimensional _
  have hopen : IsOpen {y | 0 < T.basis.coord (k + 1) y ∧ 0 < T.basis.coord (k + 2) y} :=
    (isOpen_lt continuous_const hc1).inter (isOpen_lt continuous_const hc2)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x ⟨h1, h2⟩
  refine ⟨r, hr, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, T.carrier_eq_nonneg_coord]
  constructor
  · rintro ⟨hy, hyb⟩; exact ⟨hy k, hyb⟩
  · rintro ⟨hyk, hyb⟩
    refine ⟨fun i => ?_, hyb⟩
    obtain ⟨hp1, hp2⟩ := hball hyb
    rcases hfin k i with rfl | rfl | rfl
    · exact hyk
    · exact hp1.le
    · exact hp2.le
theorem Tri.ball_subset_of_pos (T : Tri) {x : Plane}
    (hpos : ∀ i, 0 < T.basis.coord i x) :
    ∃ r > 0, Metric.ball x r ⊆ T.carrier := by
  have hopen : IsOpen {y : Plane | ∀ i, 0 < T.basis.coord i y} := by
    have : {y : Plane | ∀ i, 0 < T.basis.coord i y} = ⋂ i, {y | 0 < T.basis.coord i y} := by
      ext y; simp [Set.mem_iInter]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (AffineMap.continuous_of_finiteDimensional _)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hpos
  refine ⟨r, hr, fun y hy => ?_⟩
  rw [T.carrier_eq_nonneg_coord]
  exact fun i => (hball hy i).le
theorem Tri.ball_disjoint_of_neg (T : Tri) {x : Plane} {k : Fin 3}
    (hneg : T.basis.coord k x < 0) :
    ∃ r > 0, Metric.ball x r ∩ T.carrier = ∅ := by
  have hopen : IsOpen {y : Plane | T.basis.coord k y < 0} :=
    isOpen_lt (AffineMap.continuous_of_finiteDimensional _) continuous_const
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hneg
  refine ⟨r, hr, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro y ⟨hy1, hy2⟩
  rw [T.carrier_eq_nonneg_coord] at hy2
  exact absurd (hy2 k) (not_le.mpr (hball hy1))
theorem volume_halfspace_inter_ball (L : Plane →ₗ[ℝ] ℝ) (hL : L ≠ 0) (r : ℝ) :
    2 * volume ({v : Plane | 0 ≤ L v} ∩ Metric.ball 0 r) = volume (Metric.ball (0 : Plane) r) := by
  classical
  have hcont : Continuous L := L.continuous_of_finiteDimensional
  set A : Set Plane := {v | 0 ≤ L v} ∩ Metric.ball 0 r with hAdef
  set B : Set Plane := {v | L v ≤ 0} ∩ Metric.ball 0 r with hBdef
  have hBmeas : MeasurableSet B :=
    ((isClosed_le hcont continuous_const).measurableSet).inter Metric.isOpen_ball.measurableSet
  have hBA : B = (fun v : Plane => (-1 : ℝ) • v) ⁻¹' A := by
    ext v
    simp only [hAdef, hBdef, Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq,
      Metric.mem_ball, dist_zero_right, neg_one_smul, map_neg, norm_neg, neg_nonneg]
  have hvolB : volume B = volume A := by
    rw [hBA, Measure.addHaar_preimage_smul volume (by norm_num : (-1 : ℝ) ≠ 0)]
    simp
  have hunion : A ∪ B = Metric.ball (0 : Plane) r := by
    ext v
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    · intro hv
      rcases le_total (0 : ℝ) (L v) with h | h
      · exact Or.inl ⟨h, hv⟩
      · exact Or.inr ⟨h, hv⟩
  have hker : LinearMap.ker L ≠ ⊤ := fun h => hL (LinearMap.ker_eq_top.mp h)
  have hinter : volume (A ∩ B) = 0 := by
    refine measure_mono_null (fun v hv => ?_) (Measure.addHaar_submodule volume _ hker)
    exact le_antisymm hv.2.1 hv.1.1
  have hie := measure_union_add_inter (μ := volume) A hBmeas
  rw [hunion, hinter, hvolB, add_zero] at hie
  rw [hie, two_mul]
theorem volume_halfplane_inter_ball_at (g : Plane →ᵃ[ℝ] ℝ) (hL : g.linear ≠ 0)
    {x : Plane} (hx : g x = 0) (r : ℝ) :
    2 * volume ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r) = volume (Metric.ball x r) := by
  have hg : ∀ v : Plane, g (x + v) = g.linear v := by
    intro v
    have h := g.map_vadd x v
    simpa [add_comm, hx] using h
  have hballpre : (fun v : Plane => x + v) ⁻¹' Metric.ball x r = Metric.ball 0 r := by
    ext v; simp [Metric.mem_ball, dist_eq_norm, dist_zero_right]
  have hpre : (fun v : Plane => x + v) ⁻¹' ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r)
            = {v : Plane | 0 ≤ g.linear v} ∩ Metric.ball 0 r := by
    rw [Set.preimage_inter, hballpre]
    congr 1
    ext v; simp only [Set.mem_preimage, Set.mem_setOf_eq, hg]
  calc 2 * volume ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r)
      = 2 * volume ((fun v : Plane => x + v) ⁻¹' ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r)) := by
        rw [measure_preimage_add]
    _ = 2 * volume ({v : Plane | 0 ≤ g.linear v} ∩ Metric.ball 0 r) := by rw [hpre]
    _ = volume (Metric.ball (0 : Plane) r) := volume_halfspace_inter_ball _ hL r
    _ = volume (Metric.ball x r) := by rw [← hballpre, measure_preimage_add]
theorem Tri.coord_linear_ne_zero (T : Tri) (k : Fin 3) : (T.basis.coord k).linear ≠ 0 := by
  intro h
  have hne : ∀ j : Fin 3, j ≠ j + 1 := by decide
  have e1 : T.basis.coord k (T.pts k) = 1 := T.basis.coord_apply_eq k
  have e2 : T.basis.coord k (T.pts (k + 1)) = 0 := T.basis.coord_apply_ne (hne k)
  have hdiff : T.basis.coord k (T.pts k) - T.basis.coord k (T.pts (k + 1)) = 0 := by
    have hv := (T.basis.coord k).linearMap_vsub (T.pts k) (T.pts (k + 1))
    rw [h] at hv
    simpa using hv.symm
  rw [e1, e2] at hdiff
  norm_num at hdiff
theorem inter_ball_mono {A B : Set Plane} {x : Plane} {r : ℝ}
    (h : A ∩ Metric.ball x r = B ∩ Metric.ball x r) {r' : ℝ} (hr' : r' ≤ r) :
    A ∩ Metric.ball x r' = B ∩ Metric.ball x r' := by
  have hsub : Metric.ball x r' ⊆ Metric.ball x r := Metric.ball_subset_ball hr'
  ext y
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨hy, hb⟩; exact ⟨((Set.ext_iff.mp h y).mp ⟨hy, hsub hb⟩).1, hb⟩
  · rintro ⟨hy, hb⟩; exact ⟨((Set.ext_iff.mp h y).mpr ⟨hy, hsub hb⟩).1, hb⟩
theorem Tri.volume_inter_ball_edge (T : Tri) (k : Fin 3) {x : Plane}
    (h0 : T.basis.coord k x = 0)
    (h1 : 0 < T.basis.coord (k + 1) x) (h2 : 0 < T.basis.coord (k + 2) x) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      2 * volume (T.carrier ∩ Metric.ball x r') = volume (Metric.ball x r') := by
  obtain ⟨r, hr, hEq⟩ := T.inter_ball_eq_halfplane k h1 h2
  refine ⟨r, hr, fun r' _ hle => ?_⟩
  rw [inter_ball_mono hEq hle]
  exact volume_halfplane_inter_ball_at (T.basis.coord k) (T.coord_linear_ne_zero k) h0 r'
theorem Tri.volume_inter_ball_interior (T : Tri) {x : Plane}
    (hpos : ∀ i, 0 < T.basis.coord i x) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball x r') = volume (Metric.ball x r') := by
  obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
  refine ⟨r, hr, fun r' _ hle => ?_⟩
  congr 1
  exact Set.inter_eq_self_of_subset_right
    (fun y hy => hsub (Metric.ball_subset_ball hle hy))
theorem Tri.volume_inter_ball_exterior (T : Tri) {x : Plane} {k : Fin 3}
    (hneg : T.basis.coord k x < 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball x r') = 0 := by
  obtain ⟨r, hr, hemp⟩ := T.ball_disjoint_of_neg hneg
  refine ⟨r, hr, fun r' _ hle => ?_⟩
  have : T.carrier ∩ Metric.ball x r' = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy1, hy2⟩
    have : y ∈ Metric.ball x r ∩ T.carrier := ⟨Metric.ball_subset_ball hle hy2, hy1⟩
    rw [hemp] at this
    exact this
  rw [this, measure_empty]
theorem Tri.eq_vertex_of_two_coords_zero (T : Tri) {x : Plane} {j k : Fin 3} (hjk : j ≠ k)
    (hj : T.basis.coord j x = 0) (hk : T.basis.coord k x = 0) :
    ∃ m, x = T.pts m := by
  classical
  have key : ∀ u v : Fin 3, u ≠ v →
      ∃ m : Fin 3, m ≠ u ∧ m ≠ v ∧ ∀ b : Fin 3, b ≠ m → b = u ∨ b = v := by decide
  obtain ⟨m, hmj, hmk, hall⟩ := key j k hjk
  have hzero : ∀ b : Fin 3, b ≠ m → T.basis.coord b x = 0 := by
    intro b hb; rcases hall b hb with rfl | rfl
    · exact hj
    · exact hk
  have hm : T.basis.coord m x = 1 := by
    rw [← T.basis.sum_coord_apply_eq_one x]
    exact (Finset.sum_eq_single_of_mem m (Finset.mem_univ m)
      (fun b _ hb => hzero b hb)).symm
  refine ⟨m, T.basis.ext_elem (fun i => ?_)⟩
  by_cases hi : i = m
  · rw [hi, hm]; exact (T.basis.coord_apply_eq m).symm
  · rw [hzero i hi]; exact (T.basis.coord_apply_ne hi).symm
theorem Tri.classify (T : Tri) {x : Plane} (hx : ∀ k, x ≠ T.pts k) :
    (∀ i, 0 < T.basis.coord i x)
  ∨ (∃ k, T.basis.coord k x = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j x)
  ∨ (∃ k, T.basis.coord k x < 0) := by
  classical
  by_cases hneg : ∃ k, T.basis.coord k x < 0
  · exact Or.inr (Or.inr hneg)
  push_neg at hneg
  by_cases hpos : ∀ i, 0 < T.basis.coord i x
  · exact Or.inl hpos
  push_neg at hpos
  obtain ⟨k, hk⟩ := hpos
  have hk0 : T.basis.coord k x = 0 := le_antisymm hk (hneg k)
  refine Or.inr (Or.inl ⟨k, hk0, fun j hj => ?_⟩)
  rcases (hneg j).lt_or_eq with h | h
  · exact h
  · 
    exact absurd (T.eq_vertex_of_two_coords_zero hj h.symm hk0) (by
      rintro ⟨m, rfl⟩; exact hx m rfl)
theorem exists_common_radius {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ r > 0, ∀ i, r ≤ f i := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne f, ?_, fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
  rw [gt_iff_lt, Finset.lt_inf'_iff]
  exact fun i _ => hf i
noncomputable def Tri.det (T : Tri) : ℝ :=
  (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1 - (T.pts 1 - T.pts 0) 1 * (T.pts 2 - T.pts 0) 0
def cross (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0
@[simp] theorem cross_neg_left (u v : Plane) : cross (-u) v = - cross u v := by
  simp only [cross]; simp; ring
@[simp] theorem cross_self (u : Plane) : cross u u = 0 := by simp only [cross]; ring
@[simp] theorem cross_zero_right (u : Plane) : cross u 0 = 0 := by simp only [cross]; simp
theorem cross_add_right (u v w : Plane) : cross u (v + w) = cross u v + cross u w := by
  simp only [cross]; simp; ring
theorem cross_smul_right (t : ℝ) (u v : Plane) : cross u (t • v) = t * cross u v := by
  simp only [cross]; simp; ring
theorem cross_sum_right {n : ℕ} (u : Plane) (g : Fin n → Plane) :
    cross u (∑ i, g i) = ∑ i, cross u (g i) := by
  classical
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_castSucc, cross_add_right, ih, Fin.sum_univ_castSucc]
theorem Tri.det_cyclic (T : Tri) (k : Fin 3) :
    cross (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k) = T.det := by
  fin_cases k <;> simp [cross, Tri.det] <;> ring
theorem Tri.coord_mul_det (T : Tri) (k : Fin 3) (y : Plane) :
    T.basis.coord (k + 2) y * T.det = cross (T.pts (k + 1) - T.pts k) (y - T.pts k) := by
  have hsum : ∑ i, T.basis.coord i y = 1 := T.basis.sum_coord_apply_eq_one y
  have hy : ∑ i, T.basis.coord i y • T.pts i = y := T.basis.linear_combination_coord_eq_self y
  have hdec : y - T.pts k = ∑ i, T.basis.coord i y • (T.pts i - T.pts k) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hy, ← Finset.sum_smul, hsum, one_smul]
  rw [hdec, cross_sum_right]
  have hk   : cross (T.pts (k + 1) - T.pts k) (T.pts k - T.pts k) = 0 := by simp
  have hk1  : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 1) - T.pts k) = 0 := cross_self _
  have hk2  := T.det_cyclic k
  have hfin : ∀ j : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by
    have : ∀ u v : Fin 3, v = u ∨ v = u + 1 ∨ v = u + 2 := by decide
    exact fun j => this k j
  rw [Finset.sum_eq_single (k + 2)]
  · rw [cross_smul_right, hk2]
  · intro j _ hj
    rcases hfin j with rfl | rfl | rfl
    · rw [cross_smul_right, hk, mul_zero]
    · rw [cross_smul_right, hk1, mul_zero]
    · exact absurd rfl hj
  · intro h; exact absurd (Finset.mem_univ _) h
theorem Tri.det_ne_zero (T : Tri) : T.det ≠ 0 := by
  intro h
  have hall : ∀ w : Plane, cross (T.pts 1 - T.pts 0) w = 0 := by
    intro w
    have hid := T.coord_mul_det 0 (T.pts 0 + w)
    simp only [h, mul_zero, add_sub_cancel_left] at hid
    exact hid.symm
  have h0 : (T.pts 1 - T.pts 0) 0 = 0 := by
    have hw := hall (EuclideanSpace.single 1 (1 : ℝ))
    simpa [cross] using hw
  have h1 : (T.pts 1 - T.pts 0) 1 = 0 := by
    have hw := hall (EuclideanSpace.single 0 (1 : ℝ))
    simp [cross] at hw
    simp only [PiLp.sub_apply]
    linarith
  have hzero : T.pts 1 - T.pts 0 = 0 := by
    ext i; fin_cases i
    · simpa using h0
    · simpa using h1
  have hne : (0 : Fin 3) ≠ 1 := by decide
  exact hne (T.indep.injective (sub_eq_zero.mp hzero).symm)
noncomputable def crossL (u : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun := cross u
  map_add' := cross_add_right u
  map_smul' := fun t v => cross_smul_right t u v
@[simp] theorem crossL_apply (u v : Plane) : crossL u v = cross u v := rfl
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
open MeasureTheory Set
theorem cross_sub_right (u a b : Plane) : cross u (a - b) = cross u a - cross u b := by
  simp only [cross, PiLp.sub_apply]; ring
theorem cross_smul_left (t : ℝ) (u v : Plane) : cross (t • u) v = t * cross u v := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring
theorem parallel_of_cross_eq_zero {a b : Plane} (ha : a ≠ 0) (h : cross a b = 0) :
    ∃ τ : ℝ, b = τ • a := by
  have hcomp : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact ha (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  simp only [cross] at h
  rcases hcomp with h0 | h1
  · refine ⟨b 0 / a 0, ?_⟩
    have key0 : b 0 = b 0 / a 0 * a 0 := by field_simp
    have key1 : b 1 = b 0 / a 0 * a 1 := by field_simp; linear_combination h
    ext i
    fin_cases i
    · simpa [smul_eq_mul] using key0
    · simpa [smul_eq_mul] using key1
  · refine ⟨b 1 / a 1, ?_⟩
    have key0 : b 0 = b 1 / a 1 * a 0 := by field_simp; linear_combination -h
    have key1 : b 1 = b 1 / a 1 * a 1 := by field_simp
    ext i
    fin_cases i
    · simpa [smul_eq_mul] using key0
    · simpa [smul_eq_mul] using key1
theorem move_in_ball {x v : Plane} (hv : v ≠ 0) {r : ℝ} (hr : 0 < r) :
    x + (r / (2 * ‖v‖)) • v ∈ Metric.ball x r ∧ 0 < r / (2 * ‖v‖) := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have htpos : 0 < r / (2 * ‖v‖) := by positivity
  refine ⟨?_, htpos⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hxy : x + (r / (2 * ‖v‖)) • v - x = (r / (2 * ‖v‖)) • v := by abel
  rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  have hval : r / (2 * ‖v‖) * ‖v‖ = r / 2 := by field_simp
  rw [hval]; linarith
theorem Tri.interior_coord_pos (T : Tri) {y : Plane} (hy : y ∈ interior T.carrier) :
    ∀ j, 0 < T.basis.coord j y := by
  intro j
  have hnn : 0 ≤ T.basis.coord j y := by
    have hmem := interior_subset hy
    rw [T.carrier_eq_nonneg_coord] at hmem
    exact hmem j
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hy
    obtain ⟨w, hw⟩ : ∃ w, (T.basis.coord j).linear w ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact T.coord_linear_ne_zero j (LinearMap.ext fun w => by simpa using hc w)
    obtain ⟨v, hv⟩ : ∃ v, (T.basis.coord j).linear v < 0 := by
      rcases lt_or_gt_of_ne hw with h' | h'
      · exact ⟨w, h'⟩
      · exact ⟨-w, by rw [map_neg]; linarith⟩
    have hvne : v ≠ 0 := by
      rintro rfl
      rw [map_zero] at hv
      exact absurd hv (lt_irrefl 0)
    obtain ⟨hmem, htpos⟩ := move_in_ball (x := y) hvne hr
    have hin : y + (r / (2 * ‖v‖)) • v ∈ T.carrier := interior_subset (hball hmem)
    rw [T.carrier_eq_nonneg_coord] at hin
    have hcoord : T.basis.coord j (y + (r / (2 * ‖v‖)) • v)
        = (T.basis.coord j).linear ((r / (2 * ‖v‖)) • v) + T.basis.coord j y := by
      have h1 := (T.basis.coord j).map_vadd y ((r / (2 * ‖v‖)) • v)
      simp only [vadd_eq_add] at h1
      rw [add_comm ((r / (2 * ‖v‖)) • v) y] at h1
      exact h1
    have hneg : T.basis.coord j (y + (r / (2 * ‖v‖)) • v) < 0 := by
      rw [hcoord, map_smul, smul_eq_mul, h.symm, add_zero]
      exact mul_neg_of_pos_of_neg htpos hv
    exact absurd (hin j) (not_le.mpr hneg)
end Erdos634.Geometry
end

section
open MeasureTheory Set
namespace Erdos634.SectorArea
def polarBox (θ : ℝ) : Set (ℝ × ℝ) := Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) θ
def sector (θ : ℝ) : Set (ℝ × ℝ) := polarCoord.symm '' polarBox θ
theorem polarBox_subset_target {θ : ℝ} (hθ' : θ < Real.pi) :
    polarBox θ ⊆ polarCoord.target := by
  rintro ⟨r, φ⟩ ⟨⟨hr0, hr1⟩, hφ0, hφθ⟩
  exact ⟨hr0, by linarith [Real.pi_pos], by linarith⟩
theorem lintegral_id_Ioo : ∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal r = ENNReal.ofReal (1/2) := by
  have hmeas : MeasurableSet (Ioo (0:ℝ) 1) := measurableSet_Ioo
  have hint : IntegrableOn (fun r : ℝ => r) (Ioo (0:ℝ) 1) :=
    (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0:ℝ) 1)] fun r : ℝ => r := by
    filter_upwards [ae_restrict_mem hmeas] with r hr using le_of_lt hr.1
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_id]
  norm_num
theorem lintegral_jacobian {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫⁻ p in polarBox θ, ENNReal.ofReal p.1 = ENNReal.ofReal (θ / 2) := by
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (polarBox θ)
      = ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioo (0:ℝ) θ))) := by
    rw [Measure.prod_restrict, polarBox, ← Measure.volume_eq_prod]
  rw [hprod, MeasureTheory.lintegral_prod _ (by fun_prop)]
  have hinner : ∀ r : ℝ, ∫⁻ _ in Ioo (0:ℝ) θ, ENNReal.ofReal r
      = ENNReal.ofReal r * ENNReal.ofReal θ := by
    intro r
    rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo]
    congr 1
    rw [ENNReal.ofReal_eq_ofReal_iff (by linarith) hθ]
    ring
  simp_rw [hinner]
  rw [MeasureTheory.lintegral_mul_const _ (by fun_prop), lintegral_id_Ioo,
      ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring
theorem volume_sector {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < Real.pi) :
    volume (sector θ) = ENNReal.ofReal (θ / 2) := by
  have hsub := polarBox_subset_target hθ'
  have hboxOpen : IsOpen (polarBox θ) := isOpen_Ioo.prod isOpen_Ioo
  have hbox : MeasurableSet (polarBox θ) := hboxOpen.measurableSet
  have hsec : MeasurableSet (sector θ) :=
    (OpenPartialHomeomorph.isOpen_image_symm_of_subset_target polarCoord hboxOpen hsub).measurableSet
  have key := lintegral_comp_polarCoord_symm ((sector θ).indicator (fun _ => (1 : ENNReal)))
  rw [lintegral_indicator hsec, setLIntegral_one] at key
  have hpt : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • (sector θ).indicator (fun _ => (1 : ENNReal)) (polarCoord.symm p)
        = (polarBox θ).indicator (fun q => ENNReal.ofReal q.1) p := by
    intro p hp
    by_cases hpb : p ∈ polarBox θ
    · have hmem : polarCoord.symm p ∈ sector θ := mem_image_of_mem _ hpb
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hpb, smul_eq_mul, mul_one]
    · have hnot : polarCoord.symm p ∉ sector θ := by
        rintro ⟨q, hq, hqp⟩
        exact hpb (polarCoord.symm.injOn (hsub hq) hp hqp ▸ hq)
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hpb, smul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt,
    setLIntegral_indicator hbox, Set.inter_eq_self_of_subset_left hsub,
    lintegral_jacobian hθ] at key
  exact key.symm
end Erdos634.SectorArea
end

section
open Set Real
namespace Erdos634.Wedge
def polarBox (θ : ℝ) : Set (ℝ × ℝ) := Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) θ
def sector (θ : ℝ) : Set (ℝ × ℝ) := polarCoord.symm '' polarBox θ
theorem symm_apply (r φ : ℝ) : polarCoord.symm (r, φ) = (r * Real.cos φ, r * Real.sin φ) := rfl
theorem sector_subset_halfplanes {θ : ℝ} (hπ : θ < Real.pi) :
    sector θ ⊆ {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
             ∩ {p : ℝ × ℝ | 0 < p.2}
             ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2} := by
  rintro _ ⟨⟨r, φ⟩, ⟨hr, hφ⟩, rfl⟩
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hφ0, hφθ⟩ := hφ
  have hφπ : φ < Real.pi := lt_trans hφθ hπ
  have hsinφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφπ
  rw [symm_apply]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · 
    have : (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ
      nlinarith [this]
    rw [this]
    nlinarith
  · 
    exact mul_pos hr0 hsinφ
  · 
    have hexp : Real.sin θ * (r * Real.cos φ) - Real.cos θ * (r * Real.sin φ)
        = r * Real.sin (θ - φ) := by
      rw [Real.sin_sub]; ring
    rw [hexp]
    have : 0 < Real.sin (θ - φ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    exact mul_pos hr0 this
theorem pos_of_sin_pos {x : ℝ} (hlo : -Real.pi < x) (hs : 0 < Real.sin x) : 0 < x := by
  by_contra h
  simp only [not_lt] at h
  have : Real.sin x ≤ 0 := by
    rcases eq_or_lt_of_le h with rfl | hneg
    · simp
    · have h1 : 0 < -x := by linarith
      have h2 : -x < Real.pi := by linarith
      have := Real.sin_pos_of_pos_of_lt_pi h1 h2
      rw [Real.sin_neg] at this; linarith
  linarith
theorem halfplanes_subset_sector {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
      ∩ {p : ℝ × ℝ | 0 < p.2}
      ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2} ⊆ sector θ := by
  rintro p ⟨⟨hball, hy⟩, hwedge⟩
  simp only [Set.mem_setOf_eq] at hball hy hwedge
  have hsrc : p ∈ polarCoord.source := Or.inr (by simpa using ne_of_gt hy)
  set q := polarCoord p with hq
  have hinv : polarCoord.symm q = p := polarCoord.left_inv hsrc
  have hqt : q ∈ polarCoord.target := polarCoord.map_source hsrc
  obtain ⟨hr, hφ⟩ := hqt
  simp only [Set.mem_Ioi] at hr
  simp only [Set.mem_Ioo] at hφ
  have hp1 : p.1 = q.1 * Real.cos q.2 := by rw [← hinv]; rfl
  have hp2 : p.2 = q.1 * Real.sin q.2 := by rw [← hinv]; rfl
  have hsinφ : 0 < Real.sin q.2 := by
    by_contra h
    simp only [not_lt] at h
    rw [hp2] at hy
    nlinarith
  have hφpos : 0 < q.2 := pos_of_sin_pos hφ.1 hsinφ
  have hkey : Real.sin θ * p.1 - Real.cos θ * p.2 = q.1 * Real.sin (θ - q.2) := by
    rw [hp1, hp2, Real.sin_sub]; ring
  have hsinsub : 0 < Real.sin (θ - q.2) := by
    by_contra h
    simp only [not_lt] at h
    rw [hkey] at hwedge
    nlinarith
  have hφθ : q.2 < θ := by
    have := pos_of_sin_pos (by linarith [hφ.2]) hsinsub
    linarith
  have hrad : q.1 < 1 := by
    have hsq : q.1 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
      rw [hp1, hp2]; nlinarith [Real.sin_sq_add_cos_sq q.2]
    nlinarith
  exact ⟨q, ⟨⟨hr, hrad⟩, ⟨hφpos, hφθ⟩⟩, hinv⟩
theorem sector_eq_halfplanes {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    sector θ = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
             ∩ {p : ℝ × ℝ | 0 < p.2}
             ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2} :=
  Set.Subset.antisymm (sector_subset_halfplanes hπ) (halfplanes_subset_sector h0 hπ)
end Erdos634.Wedge
end

section
open MeasureTheory Set
namespace Erdos634.E2Join
theorem sector_agree (θ : ℝ) : Wedge.sector θ = SectorArea.sector θ := rfl
theorem volume_halfplane_wedge {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    volume ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
          ∩ {p : ℝ × ℝ | 0 < p.2}
          ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2})
      = ENNReal.ofReal (θ / 2) := by
  rw [← Wedge.sector_eq_halfplanes h0 hπ, sector_agree]
  exact SectorArea.volume_sector (le_of_lt h0) hπ
def toPair (p : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ :=
  MeasurableEquiv.finTwoArrow (WithLp.ofLp p)
theorem measurePreserving_toPair : MeasurePreserving toPair :=
  (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
def wedge (θ : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  toPair ⁻¹' ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
            ∩ {p : ℝ × ℝ | 0 < p.2}
            ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2})
theorem volume_wedge {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    volume (wedge θ) = ENNReal.ofReal (θ / 2) := by
  have hopen : IsOpen ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
      ∩ {p : ℝ × ℝ | 0 < p.2} ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2}) := by
    refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
    · exact isOpen_lt (by fun_prop) continuous_const
    · exact isOpen_lt continuous_const (by fun_prop)
    · exact isOpen_lt continuous_const (by fun_prop)
  rw [wedge, measurePreserving_toPair.measure_preimage hopen.measurableSet.nullMeasurableSet]
  exact volume_halfplane_wedge h0 hπ
end Erdos634.E2Join
end

section
namespace Erdos634.Geometry
open MeasureTheory Set Metric InnerProductGeometry
open scoped RealInnerProductSpace Pointwise
theorem inner_coords (x y : Plane) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Fin.sum_univ_two]
  ring
theorem norm_sq_coords (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coords]
  ring
theorem cross_swap (u v : Plane) : cross u v = - cross v u := by
  simp only [cross]; ring
theorem mem_ball_sq (y : Plane) : y ∈ Metric.ball (0 : Plane) 1 ↔ y 0 ^ 2 + y 1 ^ 2 < 1 := by
  rw [Metric.mem_ball, dist_zero_right, ← norm_sq_coords]
  constructor
  · intro h
    nlinarith [norm_nonneg y]
  · intro h
    nlinarith [norm_nonneg y]
noncomputable def rot90 (u : Plane) : Plane :=
  EuclideanSpace.single 0 (-(u 1)) + EuclideanSpace.single 1 (u 0)
@[simp] theorem rot90_apply0 (u : Plane) : rot90 u 0 = -(u 1) := by
  simp [rot90]
@[simp] theorem rot90_apply1 (u : Plane) : rot90 u 1 = u 0 := by
  simp [rot90]
noncomputable def frame (u n : Plane) : Plane →ₗ[ℝ] Plane where
  toFun q := q 0 • u + q 1 • n
  map_add' a b := by
    show ((a + b) 0) • u + ((a + b) 1) • n = (a 0 • u + a 1 • n) + (b 0 • u + b 1 • n)
    simp only [PiLp.add_apply]
    module
  map_smul' c a := by
    show ((c • a) 0) • u + ((c • a) 1) • n = c • (a 0 • u + a 1 • n)
    simp only [PiLp.smul_apply, smul_eq_mul]
    module
theorem frame_apply (u n q : Plane) (i : Fin 2) :
    frame u n q i = q 0 * u i + q 1 * n i := by
  show (q 0 • u + q 1 • n) i = _
  simp [PiLp.add_apply, PiLp.smul_apply]
theorem frame_det (u n : Plane) : LinearMap.det (frame u n) = u 0 * n 1 - n 0 * u 1 := by
  classical
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (frame u n),
    Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, frame_apply, PiLp.single_apply]
  norm_num
theorem inner_sq_add_cross_sq (u v : Plane) :
    ⟪u, v⟫ ^ 2 + cross u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [inner_coords, norm_sq_coords, norm_sq_coords]
  simp only [cross]
  ring
theorem cos_angle_eq_inner (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Real.cos (angle u v) = ⟪u, v⟫ := by
  rw [cos_angle, hu, hv]
  norm_num
theorem sin_angle_eq_cross (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < cross u v) : Real.sin (angle u v) = cross u v := by
  have h := sin_angle_mul_norm_mul_norm u v
  rw [hu, hv] at h
  have hlag : ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ * ⟪u, v⟫ = cross u v ^ 2 := by
    have hl := inner_sq_add_cross_sq u v
    rw [hu, hv] at hl
    have huu : ⟪u, u⟫ = (1:ℝ) := by
      rw [real_inner_self_eq_norm_sq, hu]; norm_num
    have hvv : ⟪v, v⟫ = (1:ℝ) := by
      rw [real_inner_self_eq_norm_sq, hv]; norm_num
    rw [huu, hvv]
    linear_combination - hl
  rw [hlag] at h
  rw [Real.sqrt_sq hpos.le] at h
  simpa using h
theorem angle_mem_Ioo (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < cross u v) : 0 < angle u v ∧ angle u v < Real.pi := by
  have hsin : 0 < Real.sin (angle u v) := by
    rw [sin_angle_eq_cross u v hu hv hpos]; exact hpos
  constructor
  · rcases (angle_nonneg u v).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, Real.sin_zero] at hsin
      exact lt_irrefl 0 hsin
  · rcases (angle_le_pi u v).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [h, Real.sin_pi] at hsin
      exact lt_irrefl 0 hsin
theorem mem_wedge_iff (θ : ℝ) (q : Plane) :
    q ∈ Erdos634.E2Join.wedge θ ↔
      q 0 ^ 2 + q 1 ^ 2 < 1 ∧ 0 < q 1 ∧ 0 < Real.sin θ * q 0 - Real.cos θ * q 1 := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by simpa [pow_two, Erdos634.E2Join.toPair] using h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by simpa [pow_two, Erdos634.E2Join.toPair] using h1, h2⟩, h3⟩
theorem frame_image_wedge (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < cross u v) :
    frame u (rot90 u) '' Erdos634.E2Join.wedge (angle u v)
      = {y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
          ∩ Metric.ball (0 : Plane) 1 := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [← norm_sq_coords, hu]; norm_num
  have hsin := sin_angle_eq_cross u v hu hv hpos
  have hcos := cos_angle_eq_inner u v hu hv
  have hF0 : ∀ q : Plane, frame u (rot90 u) q 0 = q 0 * u 0 - q 1 * u 1 := by
    intro q; rw [frame_apply, rot90_apply0]; ring
  have hF1 : ∀ q : Plane, frame u (rot90 u) q 1 = q 0 * u 1 + q 1 * u 0 := by
    intro q; rw [frame_apply, rot90_apply1]
  have hnorm : ∀ q : Plane,
      (frame u (rot90 u) q) 0 ^ 2 + (frame u (rot90 u) q) 1 ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
    intro q
    rw [hF0, hF1]
    linear_combination (q 0 ^ 2 + q 1 ^ 2) * hu2
  have hcru : ∀ q : Plane, cross u (frame u (rot90 u) q) = q 1 := by
    intro q
    simp only [cross]
    rw [hF0, hF1]
    linear_combination (q 1) * hu2
  have hcrv : ∀ q : Plane, cross (frame u (rot90 u) q) v
      = Real.sin (angle u v) * q 0 - Real.cos (angle u v) * q 1 := by
    intro q
    rw [hsin, hcos, inner_coords]
    simp only [cross]
    rw [hF0, hF1]
    ring
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_wedge_iff] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show 0 < cross u (frame u (rot90 u) q)
      rw [hcru]; exact h2
    · show 0 < cross (frame u (rot90 u) q) v
      rw [hcrv]; exact h3
    · rw [mem_ball_sq, hnorm]; exact h1
  · rintro ⟨⟨hy1, hy2⟩, hy3⟩
    set q : Plane := EuclideanSpace.single (0 : Fin 2) (u 0 * y 0 + u 1 * y 1)
      + EuclideanSpace.single (1 : Fin 2) (cross u y) with hqdef
    have hq0 : q 0 = u 0 * y 0 + u 1 * y 1 := by
      rw [hqdef]; simp
    have hq1 : q 1 = cross u y := by
      rw [hqdef]; simp
    have hcuy : cross u y = u 0 * y 1 - u 1 * y 0 := rfl
    have hy2' : 0 < y 0 * v 1 - y 1 * v 0 := hy2
    have hy1' : 0 < cross u y := hy1
    refine ⟨q, ?_, ?_⟩
    · rw [mem_wedge_iff]
      rw [mem_ball_sq] at hy3
      refine ⟨?_, ?_, ?_⟩
      · rw [hq0, hq1, hcuy]
        have hid : (u 0 * y 0 + u 1 * y 1) ^ 2 + (u 0 * y 1 - u 1 * y 0) ^ 2
            = y 0 ^ 2 + y 1 ^ 2 := by
          linear_combination (y 0 ^ 2 + y 1 ^ 2) * hu2
        rw [hid]
        exact hy3
      · rw [hq1]; exact hy1'
      · rw [hq0, hq1, hsin, hcos, inner_coords, hcuy]
        have hid : cross u v * (u 0 * y 0 + u 1 * y 1)
            - (u 0 * v 0 + u 1 * v 1) * (u 0 * y 1 - u 1 * y 0)
            = y 0 * v 1 - y 1 * v 0 := by
          simp only [cross]
          linear_combination (y 0 * v 1 - y 1 * v 0) * hu2
        rw [hid]
        exact hy2'
    · ext i
      fin_cases i
      · show frame u (rot90 u) q 0 = y 0
        rw [hF0, hq0, hq1, hcuy]
        linear_combination (y 0) * hu2
      · show frame u (rot90 u) q 1 = y 1
        rw [hF1, hq0, hq1, hcuy]
        linear_combination (y 1) * hu2
def vertexCone (u v : Plane) : Set Plane :=
  {y | 0 ≤ cross u y * cross u v ∧ 0 ≤ cross y v * cross u v}
theorem vertexCone_swap (u v : Plane) : vertexCone v u = vertexCone u v := by
  ext y
  simp only [vertexCone, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · calc (0:ℝ) ≤ cross y u * cross v u := h2
        _ = cross u y * cross u v := by rw [cross_swap y u, cross_swap v u]; ring
    · calc (0:ℝ) ≤ cross v y * cross v u := h1
        _ = cross y v * cross u v := by rw [cross_swap v y, cross_swap v u]; ring
  · rintro ⟨h1, h2⟩
    constructor
    · calc (0:ℝ) ≤ cross y v * cross u v := h2
        _ = cross v y * cross v u := by rw [cross_swap v y, cross_swap v u]; ring
    · calc (0:ℝ) ≤ cross u y * cross u v := h1
        _ = cross y u * cross v u := by rw [cross_swap y u, cross_swap v u]; ring
theorem nonneg_of_mul_nonneg_left' {a c : ℝ} (h : 0 ≤ c * a) (hc : 0 < c) : 0 ≤ a := by
  nlinarith
theorem vertexCone_smul (u v : Plane) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    vertexCone (s • u) (t • v) = vertexCone u v := by
  have e1 : ∀ y : Plane, cross (s • u) y * cross (s • u) (t • v)
      = (s * s * t) * (cross u y * cross u v) := by
    intro y
    rw [cross_smul_left, cross_smul_left, cross_smul_right]
    ring
  have e2 : ∀ y : Plane, cross y (t • v) * cross (s • u) (t • v)
      = (s * t * t) * (cross y v * cross u v) := by
    intro y
    rw [cross_smul_right, cross_smul_left, cross_smul_right]
    ring
  have h1 : (0:ℝ) < s * s * t := by positivity
  have h2 : (0:ℝ) < s * t * t := by positivity
  ext y
  simp only [vertexCone, Set.mem_setOf_eq, e1, e2]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨nonneg_of_mul_nonneg_left' ha h1, nonneg_of_mul_nonneg_left' hb h2⟩
  · rintro ⟨ha, hb⟩
    exact ⟨mul_nonneg h1.le ha, mul_nonneg h2.le hb⟩
theorem volume_cross_zero (u v : Plane) (hne : cross u v ≠ 0) :
    volume {y : Plane | cross u y = 0} = 0 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hne
    show (0:Plane) 0 * v 1 - (0:Plane) 1 * v 0 = 0
    simp
  have hsub : {y : Plane | cross u y = 0} ⊆ (Submodule.span ℝ {u} : Submodule ℝ Plane) := by
    intro y hy
    obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero hu0 hy
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    exact ⟨τ, hτ.symm⟩
  have htop : (Submodule.span ℝ ({u} : Set Plane)) ≠ ⊤ := by
    intro htop
    have hv : v ∈ Submodule.span ℝ ({u} : Set Plane) := by
      rw [htop]; trivial
    obtain ⟨τ, hτ⟩ := Submodule.mem_span_singleton.mp hv
    apply hne
    rw [← hτ, cross_smul_right, cross_self, mul_zero]
  have hnull := MeasureTheory.Measure.addHaar_submodule (volume : Measure Plane) _ htop
  have hle : volume {y : Plane | cross u y = 0}
      ≤ volume ((Submodule.span ℝ ({u} : Set Plane) : Submodule ℝ Plane) : Set Plane) :=
    measure_mono hsub
  rw [hnull] at hle
  exact nonpos_iff_eq_zero.mp hle
theorem volume_vertexCone_unit_pos (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < cross u v) :
    volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1)
      = ENNReal.ofReal (angle u v / 2) := by
  set θ := angle u v with hθ
  obtain ⟨hθ0, hθπ⟩ := angle_mem_Ioo u v hu hv hpos
  have hopen : volume ({y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
      ∩ Metric.ball (0 : Plane) 1) = ENNReal.ofReal (θ / 2) := by
    rw [← frame_image_wedge u v hu hv hpos,
      Measure.addHaar_image_linearMap volume (frame u (rot90 u))]
    have hdet : LinearMap.det (frame u (rot90 u)) = 1 := by
      rw [frame_det, rot90_apply0, rot90_apply1]
      have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [← norm_sq_coords, hu]; norm_num
      linear_combination hu2
    rw [hdet]
    simp only [abs_one, ENNReal.ofReal_one, one_mul]
    exact Erdos634.E2Join.volume_wedge hθ0 hθπ
  have hCpos : vertexCone u v = {y : Plane | 0 ≤ cross u y ∧ 0 ≤ cross y v} := by
    ext y
    simp only [vertexCone, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · nlinarith [h1, hpos]
      · nlinarith [h2, hpos]
    · rintro ⟨h1, h2⟩
      exact ⟨mul_nonneg h1 hpos.le, mul_nonneg h2 hpos.le⟩
  have hsplit : vertexCone u v ∩ Metric.ball (0 : Plane) 1
      ⊆ ({y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
          ∩ Metric.ball (0 : Plane) 1)
        ∪ ({y : Plane | cross u y = 0} ∪ {y : Plane | cross y v = 0}) := by
    rintro y ⟨hy, hyb⟩
    rw [hCpos] at hy
    obtain ⟨h1, h2⟩ := hy
    rcases h1.lt_or_eq with h1' | h1'
    · rcases h2.lt_or_eq with h2' | h2'
      · exact Or.inl ⟨⟨h1', h2'⟩, hyb⟩
      · exact Or.inr (Or.inr h2'.symm)
    · exact Or.inr (Or.inl h1'.symm)
  have hnull1 : volume {y : Plane | cross u y = 0} = 0 :=
    volume_cross_zero u v hpos.ne'
  have hnull2 : volume {y : Plane | cross y v = 0} = 0 := by
    have hvu : cross v u ≠ 0 := by
      rw [cross_swap v u]
      simpa using hpos.ne'
    have h := volume_cross_zero v u hvu
    have hEq : {y : Plane | cross y v = 0} = {y : Plane | cross v y = 0} := by
      ext y
      simp only [Set.mem_setOf_eq]
      rw [cross_swap y v]
      constructor <;> intro h' <;> linarith
    rw [hEq]
    exact h
  have hle1 : volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1)
      ≤ ENNReal.ofReal (θ / 2) := by
    calc volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1)
        ≤ volume (({y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
            ∩ Metric.ball (0 : Plane) 1)
          ∪ ({y : Plane | cross u y = 0} ∪ {y : Plane | cross y v = 0})) :=
          measure_mono hsplit
      _ ≤ volume ({y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
            ∩ Metric.ball (0 : Plane) 1)
          + volume ({y : Plane | cross u y = 0} ∪ {y : Plane | cross y v = 0}) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (θ / 2) + (volume {y : Plane | cross u y = 0}
          + volume {y : Plane | cross y v = 0}) := by
          rw [hopen]
          have hun : volume ({y : Plane | cross u y = 0} ∪ {y : Plane | cross y v = 0})
              ≤ volume {y : Plane | cross u y = 0} + volume {y : Plane | cross y v = 0} :=
            measure_union_le _ _
          exact add_le_add le_rfl hun
      _ = ENNReal.ofReal (θ / 2) := by rw [hnull1, hnull2, add_zero, add_zero]
  have hle2 : ENNReal.ofReal (θ / 2)
      ≤ volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1) := by
    rw [← hopen]
    refine measure_mono ?_
    rintro y ⟨⟨h1, h2⟩, hyb⟩
    refine ⟨?_, hyb⟩
    rw [hCpos]
    exact ⟨h1.le, h2.le⟩
  exact le_antisymm hle1 hle2
theorem volume_vertexCone_unit (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hne : cross u v ≠ 0) :
    volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1)
      = ENNReal.ofReal (angle u v / 2) := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hpos' : 0 < cross v u := by
      rw [cross_swap v u]; linarith
    rw [← vertexCone_swap, angle_comm]
    exact volume_vertexCone_unit_pos v u hv hu hpos'
  · exact volume_vertexCone_unit_pos u v hu hv hpos
theorem vertexCone_ball_smul (u v : Plane) {r : ℝ} (hr : 0 < r) :
    vertexCone u v ∩ Metric.ball (0 : Plane) r
      = r • (vertexCone u v ∩ Metric.ball (0 : Plane) 1) := by
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  simp only [vertexCone, Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_ball,
    dist_zero_right, cross_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hrinv]
  have hcl : ∀ z : Plane, cross (r⁻¹ • y) z = r⁻¹ * cross y z := fun z =>
    cross_smul_left r⁻¹ y z
  rw [hcl]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · calc (0:ℝ) ≤ r⁻¹ * (cross u y * cross u v) := by positivity
        _ = r⁻¹ * cross u y * cross u v := by ring
    · calc (0:ℝ) ≤ r⁻¹ * (cross y v * cross u v) := by positivity
        _ = r⁻¹ * cross y v * cross u v := by ring
    · calc r⁻¹ * ‖y‖ < r⁻¹ * r := mul_lt_mul_of_pos_left h3 hrinv
        _ = 1 := inv_mul_cancel₀ hr.ne'
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h1' : 0 ≤ r * (r⁻¹ * cross u y * cross u v) := by positivity
      calc (0:ℝ) ≤ r * (r⁻¹ * cross u y * cross u v) := h1'
        _ = cross u y * cross u v := by
            field_simp
    · have h2' : 0 ≤ r * (r⁻¹ * cross y v * cross u v) := by positivity
      calc (0:ℝ) ≤ r * (r⁻¹ * cross y v * cross u v) := h2'
        _ = cross y v * cross u v := by
            field_simp
    · have := mul_lt_mul_of_pos_left h3 hr
      rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_one] at this
      exact this
theorem volume_vertexCone_ball (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hne : cross u v ≠ 0) {r : ℝ} (hr : 0 < r) :
    volume (vertexCone u v ∩ Metric.ball (0 : Plane) r)
      = ENNReal.ofReal (angle u v / 2 * r ^ 2) := by
  rw [vertexCone_ball_smul u v hr, Measure.addHaar_smul,
    volume_vertexCone_unit u v hu hv hne]
  have hfr : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
  rw [hfr]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ 2)]
  ring
noncomputable def Tri.edgeVec (T : Tri) (j : Fin 3) : Plane := T.pts (j + 1) - T.pts j
theorem Tri.edgeVec_ne_zero (T : Tri) (j : Fin 3) : T.edgeVec j ≠ 0 := by
  rw [Tri.edgeVec, sub_ne_zero]
  intro h
  have h1 : j + 1 = j := T.indep.injective h
  have h2 : ∀ m : Fin 3, m + 1 ≠ m := by decide
  exact h2 j h1
noncomputable def Tri.edgeVec' (T : Tri) (j : Fin 3) : Plane := T.pts (j + 2) - T.pts j
theorem Tri.edgeVec'_ne_zero (T : Tri) (j : Fin 3) : T.edgeVec' j ≠ 0 := by
  rw [Tri.edgeVec', sub_ne_zero]
  intro h
  have h1 : j + 2 = j := T.indep.injective h
  have h2 : ∀ m : Fin 3, m + 2 ≠ m := by decide
  exact h2 j h1
theorem Tri.cross_edgeVec (T : Tri) (j : Fin 3) :
    cross (T.edgeVec j) (T.edgeVec' j) = T.det := T.det_cyclic j
theorem Tri.inter_ball_eq_vertexCone (T : Tri) (j : Fin 3) :
    ∃ r > 0, T.carrier ∩ Metric.ball (T.pts j) r
      = {y : Plane | y - T.pts j ∈ vertexCone (T.edgeVec j) (T.edgeVec' j)}
        ∩ Metric.ball (T.pts j) r := by
  have hcont : Continuous (T.basis.coord j) := AffineMap.continuous_of_finiteDimensional _
  have hj1 : T.basis.coord j (T.pts j) = 1 := T.basis.coord_apply_eq j
  have hopen : IsOpen {y : Plane | 0 < T.basis.coord j y} :=
    isOpen_lt continuous_const hcont
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (T.pts j) (by
    rw [Set.mem_setOf_eq, hj1]; norm_num)
  refine ⟨r, hr, ?_⟩
  have hfin : ∀ m : Fin 3, (m + 2) + 2 = m + 1 ∧ (m + 2) + 1 = m := by decide
  have hc2 : ∀ y : Plane, T.basis.coord (j + 2) y * T.det
      = cross (T.edgeVec j) (y - T.pts j) := fun y => T.coord_mul_det j y
  have hc1 : ∀ y : Plane, T.basis.coord (j + 1) y * T.det
      = cross (y - T.pts j) (T.edgeVec' j) := by
    intro y
    have h := T.coord_mul_det (j + 2) y
    rw [(hfin j).1, (hfin j).2] at h
    rw [h]
    have hsplit : y - T.pts (j + 2) = (y - T.pts j) - T.edgeVec' j := by
      rw [Tri.edgeVec']; abel
    have h1 : T.pts j - T.pts (j + 2) = -(T.edgeVec' j) := by
      rw [Tri.edgeVec']; abel
    rw [hsplit, cross_sub_right, h1, cross_neg_left, cross_neg_left, cross_self,
      neg_zero, sub_zero]
    rw [cross_swap (T.edgeVec' j) ((y - T.pts j))]
    ring
  have hsq : (0:ℝ) < T.det ^ 2 := by
    have := T.det_ne_zero
    positivity
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, T.carrier_eq_nonneg_coord, vertexCone]
  constructor
  · rintro ⟨hy, hyb⟩
    refine ⟨⟨?_, ?_⟩, hyb⟩
    · rw [T.cross_edgeVec j]
      have h := hc2 y
      have hcd : cross (T.edgeVec j) (y - T.pts j) * T.det
          = T.basis.coord (j + 2) y * T.det ^ 2 := by rw [← h]; ring
      rw [hcd]
      exact mul_nonneg (hy (j + 2)) hsq.le
    · rw [T.cross_edgeVec j]
      have h := hc1 y
      have hcd : cross (y - T.pts j) (T.edgeVec' j) * T.det
          = T.basis.coord (j + 1) y * T.det ^ 2 := by rw [← h]; ring
      rw [hcd]
      exact mul_nonneg (hy (j + 1)) hsq.le
  · rintro ⟨⟨h1, h2⟩, hyb⟩
    rw [T.cross_edgeVec j] at h1 h2
    refine ⟨fun i => ?_, hyb⟩
    have hexh : ∀ m i : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    rcases hexh j i with rfl | rfl | rfl
    · exact (hball hyb).le
    · have h := hc1 y
      have hcd : cross (y - T.pts j) (T.edgeVec' j) * T.det
          = T.basis.coord (j + 1) y * T.det ^ 2 := by rw [← h]; ring
      rw [hcd] at h2
      nlinarith [h2, hsq]
    · have h := hc2 y
      have hcd : cross (T.edgeVec j) (y - T.pts j) * T.det
          = T.basis.coord (j + 2) y * T.det ^ 2 := by rw [← h]; ring
      rw [hcd] at h1
      nlinarith [h1, hsq]
theorem Tri.cornerAngle_eq_angle (T : Tri) (j : Fin 3) :
    cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))
      = angle (T.edgeVec j) (T.edgeVec' j) := by
  rw [cornerAngle, EuclideanGeometry.angle, Tri.edgeVec, Tri.edgeVec']
  simp [vsub_eq_sub]
theorem Tri.volume_inter_ball_vertex (T : Tri) (j : Fin 3) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball (T.pts j) r')
        = ENNReal.ofReal
            (cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) / 2 * r' ^ 2) := by
  obtain ⟨r, hr, hEq⟩ := T.inter_ball_eq_vertexCone j
  refine ⟨r, hr, fun r' hr' hle => ?_⟩
  rw [inter_ball_mono hEq hle]
  set u := T.edgeVec j with hudef
  set v := T.edgeVec' j with hvdef
  have hu0 : u ≠ 0 := T.edgeVec_ne_zero j
  have hv0 : v ≠ 0 := T.edgeVec'_ne_zero j
  have hun : (0:ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  have hvn : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  have hsupos : 0 < ‖u‖⁻¹ := inv_pos.mpr hun
  have hsvpos : 0 < ‖v‖⁻¹ := inv_pos.mpr hvn
  have hunorm : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsupos, inv_mul_cancel₀ hun.ne']
  have hvnorm : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsvpos, inv_mul_cancel₀ hvn.ne']
  have hcone : vertexCone u v = vertexCone (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) :=
    (vertexCone_smul u v hsupos hsvpos).symm
  have hangle : angle (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) = angle u v := by
    rw [angle_smul_left_of_pos _ _ hsupos, angle_smul_right_of_pos _ _ hsvpos]
  have hcross : cross (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) ≠ 0 := by
    rw [cross_smul_left, cross_smul_right, T.cross_edgeVec j]
    have hd := T.det_ne_zero
    positivity
  have htrans : (fun z : Plane => T.pts j + z) ⁻¹'
      ({y : Plane | y - T.pts j ∈ vertexCone u v} ∩ Metric.ball (T.pts j) r')
      = vertexCone u v ∩ Metric.ball (0 : Plane) r' := by
    ext z
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_ball]
    rw [add_sub_cancel_left, dist_eq_norm, add_sub_cancel_left, dist_zero_right]
  calc volume ({y : Plane | y - T.pts j ∈ vertexCone u v} ∩ Metric.ball (T.pts j) r')
      = volume ((fun z : Plane => T.pts j + z) ⁻¹'
          ({y : Plane | y - T.pts j ∈ vertexCone u v} ∩ Metric.ball (T.pts j) r')) := by
        rw [measure_preimage_add]
    _ = volume (vertexCone u v ∩ Metric.ball (0 : Plane) r') := by rw [htrans]
    _ = volume (vertexCone (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) ∩ Metric.ball (0 : Plane) r') := by
        rw [← hcone]
    _ = ENNReal.ofReal (angle (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) / 2 * r' ^ 2) :=
        volume_vertexCone_ball _ _ hunorm hvnorm hcross hr'
    _ = ENNReal.ofReal
          (cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) / 2 * r' ^ 2) := by
        rw [hangle, hudef, hvdef, ← T.cornerAngle_eq_angle j]
theorem volume_ball_plane (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [EuclideanSpace.volume_ball]
  have hcard : Fintype.card (Fin 2) = 2 := by simp
  rw [hcard]
  have hg : Real.Gamma (1 + 1) = 1 := by
    have h := Real.Gamma_add_one (s := 1) one_ne_zero
    rw [Real.Gamma_one] at h
    simpa using h
  rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  rw [show (2 : ℝ) / 2 + 1 = 1 + 1 by norm_num, hg, Real.sq_sqrt Real.pi_pos.le]
  ring
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
open MeasureTheory Set Metric
open scoped ENNReal
open Classical in
noncomputable def Tri.localAngle (T : Tri) (p : Plane) : ℝ :=
  if h : ∃ j, p = T.pts j then
    cornerAngle (T.pts (h.choose + 1)) (T.pts h.choose) (T.pts (h.choose + 2))
  else if ∀ j, 0 < T.basis.coord j p then 2 * Real.pi
  else if ∃ k, T.basis.coord k p = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j p then Real.pi
  else 0
theorem Tri.localAngle_nonneg (T : Tri) (p : Plane) : 0 ≤ T.localAngle p := by
  classical
  rw [Tri.localAngle]
  split
  · exact EuclideanGeometry.angle_nonneg _ _ _
  · split
    · positivity
    · split
      · exact Real.pi_pos.le
      · exact le_refl 0
theorem Tri.volume_inter_ball_localAngle (T : Tri) (p : Plane) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball p r')
        = ENNReal.ofReal (T.localAngle p / 2 * r' ^ 2) := by
  classical
  by_cases hv : ∃ j, p = T.pts j
  · 
    obtain ⟨r, hr, h⟩ := T.volume_inter_ball_vertex hv.choose
    refine ⟨r, hr, fun r' h1 h2 => ?_⟩
    rw [Tri.localAngle, dif_pos hv]
    have hspec := hv.choose_spec
    set j0 := hv.choose with hj0
    rw [hspec]
    exact h r' h1 h2
  · push_neg at hv
    rcases T.classify hv with hpos | ⟨k, hk0, hkpos⟩ | ⟨k, hkneg⟩
    · 
      obtain ⟨r, hr, h⟩ := T.volume_inter_ball_interior hpos
      refine ⟨r, hr, fun r' h1 h2 => ?_⟩
      rw [Tri.localAngle, dif_neg (not_exists.mpr hv), if_pos hpos,
        h r' h1 h2, volume_ball_plane p h1.le]
      congr 1
      ring
    · 
      have hne : ∀ j : Fin 3, j + 1 ≠ j ∧ j + 2 ≠ j := by decide
      obtain ⟨r, hr, h⟩ := T.volume_inter_ball_edge k hk0
        (hkpos _ (hne k).1) (hkpos _ (hne k).2)
      refine ⟨r, hr, fun r' h1 h2 => ?_⟩
      have hIn : ¬ ∀ j, 0 < T.basis.coord j p := fun hI => absurd hk0 (ne_of_gt (hI k))
      rw [Tri.localAngle, dif_neg (not_exists.mpr hv), if_neg hIn,
        if_pos ⟨k, hk0, hkpos⟩]
      have h2v := h r' h1 h2
      rw [volume_ball_plane p h1.le] at h2v
      have hhalf : (2 : ℝ≥0∞) * ENNReal.ofReal (Real.pi / 2 * r' ^ 2)
          = ENNReal.ofReal (Real.pi * r' ^ 2) := by
        rw [show ((2 : ℝ≥0∞)) = ENNReal.ofReal (2 : ℝ) by simp,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring
      rw [← hhalf] at h2v
      exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h2v
    · 
      obtain ⟨r, hr, h⟩ := T.volume_inter_ball_exterior hkneg
      refine ⟨r, hr, fun r' h1 h2 => ?_⟩
      have hIn : ¬ ∀ j, 0 < T.basis.coord j p := fun hI =>
        absurd (hI k) (not_lt.mpr hkneg.le)
      have hOn : ¬ ∃ m, T.basis.coord m p = 0 ∧ ∀ j, j ≠ m → 0 < T.basis.coord j p := by
        rintro ⟨m, hm, hrest⟩
        by_cases hmk : k = m
        · rw [hmk] at hkneg; exact absurd hm (ne_of_lt hkneg)
        · exact absurd (hrest k hmk) (not_lt.mpr hkneg.le)
      rw [Tri.localAngle, dif_neg (not_exists.mpr hv), if_neg hIn, if_neg hOn,
        h r' h1 h2]
      simp
theorem Tri.mem_interior_iff_coord_pos (T : Tri) (p : Plane) :
    p ∈ interior T.carrier ↔ ∀ j, 0 < T.basis.coord j p := by
  constructor
  · exact fun hp => T.interior_coord_pos hp
  · intro hpos
    obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
    exact mem_interior.mpr ⟨Metric.ball p r, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
theorem Tri.localAngle_vertex (T : Tri) (k : Fin 3) :
    T.localAngle (T.pts k)
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
  classical
  have hv : ∃ j, T.pts k = T.pts j := ⟨k, rfl⟩
  rw [Tri.localAngle, dif_pos hv]
  have hk : hv.choose = k := T.indep.injective hv.choose_spec.symm
  rw [hk]
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
def Tri.Congruent (T U : Tri) : Prop :=
  ∃ (f : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3)), ∀ k, f (T.pts k) = U.pts (σ k)
theorem Tri.det_pos_or_neg (T : Tri) : 0 < T.det ∨ T.det < 0 :=
  (lt_or_gt_of_ne T.det_ne_zero).symm
noncomputable def Tri.relabel (T : Tri) (τ : Equiv.Perm (Fin 3)) : Tri where
  pts := T.pts ∘ τ
  indep := T.indep.comp_embedding τ.toEmbedding
theorem Tri.relabel_pts (T : Tri) (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (T.relabel τ).pts k = T.pts (τ k) := rfl
structure CongruentDissection (N : ℕ) extends Dissection N where
  model : Tri
  tiles_congruent : ∀ i, (tile i).Congruent model
namespace CongruentDissection
end CongruentDissection
end Erdos634.Geometry
end

section
namespace Erdos634.CongruentArea
open Erdos634.Geometry MeasureTheory
open scoped ENNReal
theorem measurePreserving_isometryEquiv (f : Plane ≃ᵢ Plane) :
    MeasurePreserving f volume volume := by
  have hdecomp : (f : Plane → Plane) = (fun y => y + f 0) ∘ (f.toRealLinearIsometryEquiv) := by
    funext x
    simp
  have hlin : MeasurePreserving (f.toRealLinearIsometryEquiv) volume volume :=
    LinearIsometryEquiv.measurePreserving _
  have htr : MeasurePreserving (fun y : Plane => y + f 0) volume volume :=
    measurePreserving_add_right volume (f 0)
  rw [show (f : Plane → Plane) = (fun y => y + f 0) ∘ (f.toRealLinearIsometryEquiv) from hdecomp]
  exact htr.comp hlin
theorem volume_image_isometryEquiv (f : Plane ≃ᵢ Plane) (s : Set Plane)
    (hs : NullMeasurableSet s volume) :
    volume (f '' s) = volume s := by
  have himg : f '' s = (f.symm) ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hy; exact ⟨f.symm y, hy, by simp⟩
  rw [himg]
  exact (measurePreserving_isometryEquiv f.symm).measure_preimage hs
theorem image_carrier_of_congruent {T U : Tri} {f : Plane ≃ᵢ Plane} {σ : Equiv.Perm (Fin 3)}
    (hf : ∀ k, f (T.pts k) = U.pts (σ k)) :
    f '' T.carrier = U.carrier := by
  have hpts : f '' (Set.range T.pts) = Set.range U.pts := by
    ext y
    constructor
    · rintro ⟨x, ⟨k, rfl⟩, rfl⟩
      exact ⟨σ k, (hf k).symm⟩
    · rintro ⟨j, rfl⟩
      refine ⟨T.pts (σ.symm j), ⟨σ.symm j, rfl⟩, ?_⟩
      rw [hf (σ.symm j), Equiv.apply_symm_apply]
  have haff : ⇑f.toRealAffineIsometryEquiv.toAffineMap = ⇑f := rfl
  rw [Erdos634.Geometry.Tri.carrier, Erdos634.Geometry.Tri.carrier, ← hpts, ← haff,
    AffineMap.image_convexHull]
theorem volume_congruent {T U : Tri} (h : T.Congruent U) :
    volume T.carrier = volume U.carrier := by
  obtain ⟨f, σ, hf⟩ := h
  rw [← image_carrier_of_congruent hf, volume_image_isometryEquiv f _ T.nullMeasurableSet]
theorem congruentDissection_volume_target {N : ℕ} (D : CongruentDissection N) :
    volume D.target.carrier = (N : ℝ≥0∞) * volume D.model.carrier :=
  D.toDissection.volume_target_of_congruent (volume D.model.carrier)
    (fun i => volume_congruent (D.tiles_congruent i))
end Erdos634.CongruentArea
end

section
namespace Erdos634.AreaDet
open Erdos634.Geometry MeasureTheory
noncomputable def pb : Module.Basis (Fin 2) ℝ Plane := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
noncomputable def edgeMap (T : Tri) : Plane →ₗ[ℝ] Plane :=
  pb.constr ℝ (fun i : Fin 2 => T.pts i.succ - T.pts 0)
noncomputable def detTri (T : Tri) : ℝ := LinearMap.det (edgeMap T)
noncomputable def stdCarrier : Set Plane :=
  convexHull ℝ (Set.range ![(0 : Plane), pb 0, pb 1])
noncomputable def placeMap (T : Tri) : Plane →ᵃ[ℝ] Plane :=
  (AffineEquiv.constVAdd ℝ Plane (T.pts 0)).toAffineMap.comp (edgeMap T).toAffineMap
theorem placeMap_apply (T : Tri) (x : Plane) : placeMap T x = T.pts 0 + edgeMap T x := by
  rfl
theorem edgeMap_basis (T : Tri) (i : Fin 2) : edgeMap T (pb i) = T.pts i.succ - T.pts 0 := by
  simp [edgeMap, Module.Basis.constr_basis]
theorem placeMap_range (T : Tri) :
    (placeMap T) '' (Set.range ![(0 : Plane), pb 0, pb 1]) = Set.range T.pts := by
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  have hv : ∀ i : Fin 3, placeMap T (![(0 : Plane), pb 0, pb 1] i) = T.pts i := by
    intro i
    rcases htri i with rfl | rfl | rfl
    · show placeMap T 0 = T.pts 0
      simp [placeMap_apply]
    · show placeMap T (pb 0) = T.pts 1
      rw [placeMap_apply, edgeMap_basis]
      show T.pts 0 + (T.pts 1 - T.pts 0) = T.pts 1
      abel
    · show placeMap T (pb 1) = T.pts 2
      rw [placeMap_apply, edgeMap_basis]
      show T.pts 0 + (T.pts 2 - T.pts 0) = T.pts 2
      abel
  rw [← Set.range_comp]
  exact congrArg Set.range (funext hv)
theorem placeMap_stdCarrier (T : Tri) : (placeMap T) '' stdCarrier = T.carrier := by
  rw [stdCarrier, AffineMap.image_convexHull, placeMap_range, Erdos634.Geometry.Tri.carrier]
theorem volume_eq_det_mul (T : Tri) :
    volume T.carrier = ENNReal.ofReal |detTri T| * volume stdCarrier := by
  rw [← placeMap_stdCarrier T]
  have hcomp : (placeMap T) '' stdCarrier
      = (fun h => T.pts 0 + h) '' (edgeMap T '' stdCarrier) := by
    rw [← Set.image_comp]
    exact congrArg (· '' stdCarrier) (funext fun x => placeMap_apply T x)
  have hpre : (fun h : Plane => T.pts 0 + h) '' (edgeMap T '' stdCarrier)
      = (fun h : Plane => (-T.pts 0) + h) ⁻¹' (edgeMap T '' stdCarrier) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hy; exact ⟨(-T.pts 0) + y, hy, by abel⟩
  rw [hcomp, hpre, measure_preimage_add, Measure.addHaar_image_linearMap]
  rfl
theorem pb_repr (v : Plane) (i : Fin 2) : pb.repr v i = v i := by
  simp [pb]
theorem detTri_eq (T : Tri) :
    detTri T = (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1
             - (T.pts 2 - T.pts 0) 0 * (T.pts 1 - T.pts 0) 1 := by
  rw [detTri, ← LinearMap.det_toMatrix pb, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, edgeMap_basis, pb_repr]
theorem isCompact_stdCarrier : IsCompact stdCarrier :=
  (Set.finite_range _).isCompact_convexHull ℝ
end Erdos634.AreaDet
end

section
namespace Erdos634.Subdivision
open Erdos634.Geometry
variable (A B C : Plane)
theorem Tri.coord_eq_of_combo (T : Tri) (x : Plane) (w : Fin 3 → ℝ)
    (hsum : w 0 + w 1 + w 2 = 1)
    (hx : x = w 0 • T.pts 0 + w 1 • T.pts 1 + w 2 • T.pts 2) (k : Fin 3) :
    T.basis.coord k x = w k := by
  have hw : Finset.univ.sum w = 1 := by rw [Fin.sum_univ_three]; exact hsum
  have hcomb : Finset.univ.affineCombination ℝ T.pts w = x := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw, Fin.sum_univ_three, hx]
  have hcoe : (⇑T.basis : Fin 3 → Plane) = T.pts := rfl
  have h2 := T.basis.coord_apply_combination_of_mem (i := k) (Finset.mem_univ k) hw
  rw [hcoe, hcomb] at h2
  exact h2
end Erdos634.Subdivision
end

section
namespace Erdos634.CertGeom
open Erdos634.Geometry Metric
theorem mem_carrier_of_combo (T : Tri) (x : Plane) (w : Fin 3 → ℝ)
    (hsum : w 0 + w 1 + w 2 = 1) (hnn : ∀ k, 0 ≤ w k)
    (hx : x = w 0 • T.pts 0 + w 1 • T.pts 1 + w 2 • T.pts 2) :
    x ∈ T.carrier := by
  rw [T.carrier_eq_nonneg_coord]
  intro k
  rw [Erdos634.Subdivision.Tri.coord_eq_of_combo T x w hsum hx k]
  exact hnn k
noncomputable def lineFun (px py qx qy : ℝ) : Plane →ᵃ[ℝ] ℝ where
  toFun v := (qx - px) * (v 1 - py) - (v 0 - px) * (qy - py)
  linear :=
    { toFun := fun w => (qx - px) * w 1 - w 0 * (qy - py)
      map_add' := by intro w z; simp only [PiLp.add_apply]; ring
      map_smul' := by intro c w; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_vadd' := by
    intro v w
    simp only [vadd_eq_add, PiLp.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring
@[simp] theorem lineFun_apply (px py qx qy : ℝ) (v : Plane) :
    lineFun px py qx qy v = (qx - px) * (v 1 - py) - (v 0 - px) * (qy - py) := rfl
end Erdos634.CertGeom
end

section
namespace Erdos634.CertCoord
open Erdos634.Geometry
noncomputable def mkPt (x y : ℝ) : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]
@[simp] theorem mkPt_zero (x y : ℝ) : mkPt x y 0 = x := by simp [mkPt, EuclideanSpace.equiv]
@[simp] theorem mkPt_one (x y : ℝ) : mkPt x y 1 = y := by simp [mkPt, EuclideanSpace.equiv]
def det3 (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) : ℝ := (x₁ - x₀) * (y₂ - y₀) - (x₂ - x₀) * (y₁ - y₀)
theorem not_collinear_of_det {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ} (hdet : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    ¬ Collinear ℝ ({mkPt x₀ y₀, mkPt x₁ y₁, mkPt x₂ y₂} : Set Plane) := by
  intro hc
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hc
  obtain ⟨q, v, hv⟩ := hc
  obtain ⟨r₀, h₀⟩ := hv (mkPt x₀ y₀) (by simp)
  obtain ⟨r₁, h₁⟩ := hv (mkPt x₁ y₁) (by simp)
  obtain ⟨r₂, h₂⟩ := hv (mkPt x₂ y₂) (by simp)
  have hx : ∀ (a b : ℝ) (r : ℝ), mkPt a b = r • v +ᵥ q → a = r * v 0 + q 0 := by
    intro a b r h
    have := congrArg (fun pt : Plane => pt 0) h
    simpa [mkPt, EuclideanSpace.equiv] using this
  have hy : ∀ (a b : ℝ) (r : ℝ), mkPt a b = r • v +ᵥ q → b = r * v 1 + q 1 := by
    intro a b r h
    have := congrArg (fun pt : Plane => pt 1) h
    simpa [mkPt, EuclideanSpace.equiv] using this
  have e₀ := hx _ _ _ h₀; have f₀ := hy _ _ _ h₀
  have e₁ := hx _ _ _ h₁; have f₁ := hy _ _ _ h₁
  have e₂ := hx _ _ _ h₂; have f₂ := hy _ _ _ h₂
  apply hdet
  rw [det3, e₀, e₁, e₂, f₀, f₁, f₂]
  ring
noncomputable def mkTri (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (hdet : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) : Tri where
  pts := ![mkPt x₀ y₀, mkPt x₁ y₁, mkPt x₂ y₂]
  indep := (affineIndependent_iff_not_collinear_of_ne
    (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide)).mpr (not_collinear_of_det hdet)
@[simp] theorem mkTri_pts (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (hdet : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    (mkTri x₀ y₀ x₁ y₁ x₂ y₂ hdet).pts = ![mkPt x₀ y₀, mkPt x₁ y₁, mkPt x₂ y₂] := rfl
end Erdos634.CertCoord
end

section
namespace Erdos634.DissectionMap
open Erdos634.Geometry
noncomputable def mapTri (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) : Tri where
  pts := e ∘ T.pts
  indep := T.indep.map' e.toAffineMap e.injective
theorem mapTri_carrier (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) :
    (mapTri e T).carrier = e '' T.carrier := by
  simp only [mapTri, Tri.carrier]
  rw [Set.range_comp]
  exact (AffineMap.image_convexHull (𝕜 := ℝ) e.toAffineMap (Set.range T.pts)).symm
end Erdos634.DissectionMap
end

section
open scoped Classical
namespace Erdos634.Geometry
noncomputable def Tri.angleAt (T : Tri) (k : Fin 3) : ℝ :=
  cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
noncomputable def Tri.oppLen (T : Tri) (k : Fin 3) : ℝ := dist (T.pts (k + 1)) (T.pts (k + 2))
theorem Tri.angleAt_sum (T : Tri) : T.angleAt 0 + T.angleAt 1 + T.angleAt 2 = Real.pi := by
  have h := cornerAngle_sum T
  unfold Tri.angleAt
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact h
end Erdos634.Geometry
end

section
namespace Erdos634.PinPlumbing
open Erdos634.Geometry
theorem localAngle_cases (T : Tri) (p : Plane) :
    (∃ j : Fin 3, p = T.pts j ∧
        T.localAngle p = cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) ∨
    T.localAngle p = 2 * Real.pi ∨ T.localAngle p = Real.pi ∨ T.localAngle p = 0 := by
  classical
  by_cases h : ∃ j, p = T.pts j
  · left
    exact ⟨h.choose, h.choose_spec, by rw [Tri.localAngle, dif_pos h]⟩
  · by_cases h2 : ∀ j, 0 < T.basis.coord j p
    · right; left
      rw [Tri.localAngle, dif_neg h, if_pos h2]
    · by_cases h3 : ∃ k, T.basis.coord k p = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j p
      · right; right; left
        rw [Tri.localAngle, dif_neg h, if_neg h2, if_pos h3]
      · right; right; right
        rw [Tri.localAngle, dif_neg h, if_neg h2, if_neg h3]
end Erdos634.PinPlumbing
end

section
namespace Erdos634.TilePlacement
open Erdos634.Geometry Finset
theorem range_pts_eq (T : Tri) (j : Fin 3) :
    Set.range T.pts = {T.pts (j + 1), T.pts j, T.pts (j + 2)} := by
  have hfin : ∀ a b : Fin 3, a = b ∨ a = b + 1 ∨ a = b + 2 := by decide
  have hfin' : ∀ i : Fin 3, i = j ∨ i = j + 1 ∨ i = j + 2 := fun i => hfin i j
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases hfin' i with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨j + 1, rfl⟩
    · exact ⟨j, rfl⟩
    · exact ⟨j + 2, rfl⟩
theorem strict_triangle (T : Tri) (j : Fin 3) :
    dist (T.pts (j + 1)) (T.pts (j + 2))
      < dist (T.pts (j + 1)) (T.pts j) + dist (T.pts j) (T.pts (j + 2)) := by
  rcases lt_or_eq_of_le (dist_triangle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) with h | h
  · exact h
  · exfalso
    have hw : Wbtw ℝ (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) :=
      dist_add_dist_eq_iff.mp h.symm
    have hcol : Collinear ℝ (Set.range T.pts) := by
      rw [range_pts_eq T j]; exact hw.collinear
    exact (affineIndependent_iff_not_collinear.mp T.indep) hcol
noncomputable def sideOpp (T : Tri) (j : Fin 3) : ℝ := dist (T.pts (j + 1)) (T.pts (j + 2))
noncomputable def angleAt (T : Tri) (j : Fin 3) : ℝ :=
  cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))
theorem strict_triangle_pts (T : Tri) (j : Fin 3) :
    dist (T.pts j) (T.pts (j + 1))
      < dist (T.pts (j + 1)) (T.pts (j + 2)) + dist (T.pts j) (T.pts (j + 2)) := by
  have hsh1 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have hsh2 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have h := strict_triangle T (j + 2)
  rw [hsh1 j, hsh2 j] at h
  have e1 : dist (T.pts j) (T.pts (j + 2)) = dist (T.pts (j + 2)) (T.pts j) := dist_comm _ _
  have e2 : dist (T.pts (j + 1)) (T.pts (j + 2)) = dist (T.pts (j + 2)) (T.pts (j + 1)) :=
    dist_comm _ _
  rw [e1, e2]
  have e3 : dist (T.pts (j + 2)) (T.pts (j + 1)) = dist (T.pts (j + 1)) (T.pts (j + 2)) :=
    dist_comm _ _
  linarith [h]
end Erdos634.TilePlacement
end

section
namespace Erdos634.TriLawSin
open Erdos634.Geometry Erdos634.TilePlacement
theorem sin_angleAt_mul_sideOpp (T : Tri) (j : Fin 3) :
    Real.sin (angleAt T (j + 1)) * sideOpp T j
      = Real.sin (angleAt T j) * sideOpp T (j + 1) := by
  fin_cases j
  · simpa [angleAt, sideOpp, cornerAngle, EuclideanGeometry.angle_comm] using
      EuclideanGeometry.law_sin (T.pts 0) (T.pts 1) (T.pts 2)
  · simpa [angleAt, sideOpp, cornerAngle, EuclideanGeometry.angle_comm] using
      EuclideanGeometry.law_sin (T.pts 1) (T.pts 2) (T.pts 0)
  · simpa [angleAt, sideOpp, cornerAngle, EuclideanGeometry.angle_comm] using
      EuclideanGeometry.law_sin (T.pts 2) (T.pts 0) (T.pts 1)
end Erdos634.TriLawSin
end

section
namespace Erdos634.MarchFlank
open Erdos634.Geometry Erdos634.TilePlacement
theorem cornerAngle_pos (T : Tri) (j : Fin 3) :
    0 < cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) := by
  rcases eq_or_lt_of_le (EuclideanGeometry.angle_nonneg
    (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) with h | h
  · exfalso
    have hz : cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) = 0 := h.symm
    rw [Erdos634.Geometry.cornerAngle] at hz
    have hdeg := EuclideanGeometry.dist_eq_abs_sub_dist_of_angle_eq_zero hz
    have hstrict := strict_triangle_pts T j
    rcases abs_cases (dist (T.pts (j + 1)) (T.pts j) - dist (T.pts (j + 2)) (T.pts j)) with
      ⟨he, _⟩ | ⟨he, _⟩
    · rw [he, dist_comm (T.pts (j + 1)) (T.pts j),
        dist_comm (T.pts (j + 2)) (T.pts j)] at hdeg
      linarith
    · 
      have h2 := strict_triangle_pts T (j + 2)
      have e1 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
      have e2 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
      rw [e1, e2] at h2
      rw [he, dist_comm (T.pts (j + 1)) (T.pts j),
        dist_comm (T.pts (j + 2)) (T.pts j)] at hdeg
      rw [dist_comm (T.pts (j + 2)) (T.pts j),
        dist_comm (T.pts (j + 2)) (T.pts (j + 1))] at h2
      linarith
  · exact h
private theorem third_index : ∀ j k : Fin 3, j ≠ k → ∃ m, m ≠ j ∧ m ≠ k := by decide
private theorem index_trichotomy :
    ∀ i j k m : Fin 3, j ≠ k → m ≠ j → m ≠ k → i ≠ m → i = j ∨ i = k := by decide
theorem localAngle_ne_zero_of_mem (T : Tri) {p : Plane} (hp : p ∈ T.carrier) :
    T.localAngle p ≠ 0 := by
  classical
  have hnn : ∀ i, 0 ≤ T.basis.coord i p := by
    rw [T.carrier_eq_nonneg_coord] at hp; exact hp
  rw [Tri.localAngle]
  split
  · exact ne_of_gt (cornerAngle_pos T _)
  · rename_i hv
    split
    · positivity
    · rename_i hpos
      push_neg at hpos
      obtain ⟨k, hk⟩ := hpos
      have hk0 : T.basis.coord k p = 0 := le_antisymm hk (hnn k)
      have huniq : ∀ j, j ≠ k → 0 < T.basis.coord j p := by
        intro j hj
        rcases lt_or_eq_of_le (hnn j) with h | h
        · exact h
        · exfalso
          have hsum := T.basis.sum_coord_apply_eq_one (k := ℝ) p
          obtain ⟨m, hmj, hmk⟩ := third_index j k hj
          have hm1 : T.basis.coord m p = 1 := by
            rw [Fin.sum_univ_three] at hsum
            fin_cases j <;> fin_cases k <;> fin_cases m <;> simp_all <;> linarith
          have hpm : p = T.pts m := by
            refine T.basis.ext_elem fun i => ?_
            have hci : T.basis.coord i (T.pts m) = if i = m then 1 else 0 :=
              AffineBasis.coord_apply T.basis i m
            rw [hci]
            by_cases him : i = m
            · subst him; simp [hm1]
            · have hz : T.basis.coord i p = 0 := by
                rcases index_trichotomy i j k m hj hmj hmk him with h' | h'
                · rw [h', ← h]
                · rw [h', hk0]
              simp [him, hz]
          exact hv ⟨m, hpm⟩
      split
      · exact Real.pi_ne_zero
      · rename_i hedge
        exact absurd ⟨k, hk0, huniq⟩ hedge
end Erdos634.MarchFlank
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ}
theorem Tri.lawSin (T : Tri) (i j : Fin 3) :
    Real.sin (T.angleAt i) * T.oppLen j = Real.sin (T.angleAt j) * T.oppLen i := by
  have h0 : Real.sin (T.angleAt 1) * T.oppLen 0 = Real.sin (T.angleAt 0) * T.oppLen 1 :=
    Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 0
  have h1 : Real.sin (T.angleAt 2) * T.oppLen 1 = Real.sin (T.angleAt 1) * T.oppLen 2 :=
    Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 1
  have h2 : Real.sin (T.angleAt 0) * T.oppLen 2 = Real.sin (T.angleAt 2) * T.oppLen 0 :=
    Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 2
  fin_cases i <;> fin_cases j
  · rfl
  · exact h0.symm
  · exact h2
  · exact h0
  · rfl
  · exact h1.symm
  · exact h2.symm
  · exact h1
  · rfl
theorem Tri.angleAt_pos' (T : Tri) (j : Fin 3) : 0 < T.angleAt j :=
  Erdos634.MarchFlank.cornerAngle_pos T j
theorem Tri.oppLen_pos (T : Tri) (k : Fin 3) : 0 < T.oppLen k := by
  unfold Tri.oppLen
  have hne : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  exact dist_pos.mpr fun h => hne (T.indep.injective h)
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ}
theorem Tri.oppLen_succ (T : Tri) (v : Fin 3) : T.oppLen (v + 1) = dist (T.pts (v + 2)) (T.pts v) := by
  unfold Tri.oppLen
  rw [show v + 1 + 1 = v + 2 by fin_cases v <;> rfl, show v + 1 + 2 = v by fin_cases v <;> rfl]
theorem Tri.oppLen_succ2 (T : Tri) (v : Fin 3) : T.oppLen (v + 2) = dist (T.pts (v + 1)) (T.pts v) := by
  unfold Tri.oppLen
  rw [show v + 2 + 1 = v by fin_cases v <;> rfl, show v + 2 + 2 = v + 1 by fin_cases v <;> rfl,
    dist_comm]
theorem Tri.sum_rot (T : Tri) (n : ℕ) (v : Fin 3) :
    ∑ k, T.oppLen k ^ n = T.oppLen v ^ n + T.oppLen (v + 1) ^ n + T.oppLen (v + 2) ^ n := by
  rw [Fin.sum_univ_three]
  have hv : v = 0 ∨ v = 1 ∨ v = 2 := by fin_cases v <;> simp
  rcases hv with rfl | rfl | rfl
  · rfl
  · show _ = T.oppLen 1 ^ n + T.oppLen 2 ^ n + T.oppLen 0 ^ n; ring
  · show _ = T.oppLen 2 ^ n + T.oppLen 0 ^ n + T.oppLen 1 ^ n; ring
theorem Tri.sum_perm (T : Tri) (n : ℕ) (σ : Equiv.Perm (Fin 3)) :
    ∑ k, T.oppLen k ^ n = T.oppLen (σ 0) ^ n + T.oppLen (σ 1) ^ n + T.oppLen (σ 2) ^ n := by
  rw [← Equiv.sum_comp σ (fun k => T.oppLen k ^ n), Fin.sum_univ_three]
theorem Tri.lawCos (T : Tri) (v : Fin 3) :
    T.oppLen v ^ 2 = T.oppLen (v + 1) ^ 2 + T.oppLen (v + 2) ^ 2
      - 2 * T.oppLen (v + 1) * T.oppLen (v + 2) * Real.cos (T.angleAt v) := by
  have hlaw :=
    EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
      (T.pts (v + 1)) (T.pts v) (T.pts (v + 2))
  rw [T.oppLen_succ, T.oppLen_succ2]
  show dist (T.pts (v + 1)) (T.pts (v + 2)) ^ 2 = _ - _ * Real.cos
    (EuclideanGeometry.angle (T.pts (v + 1)) (T.pts v) (T.pts (v + 2)))
  linear_combination hlaw
theorem Tri.lawCos_perm (T : Tri) (σ : Equiv.Perm (Fin 3)) :
    T.oppLen (σ 2) ^ 2 = T.oppLen (σ 0) ^ 2 + T.oppLen (σ 1) ^ 2
      - 2 * T.oppLen (σ 0) * T.oppLen (σ 1) * Real.cos (T.angleAt (σ 2)) := by
  have hl := T.lawCos (σ 2)
  have r1 := T.sum_rot 1 (σ 2)
  have p1 := T.sum_perm 1 σ
  have r2 := T.sum_rot 2 (σ 2)
  have p2 := T.sum_perm 2 σ
  simp only [pow_one] at r1 p1
  set x := T.oppLen (σ 2 + 1)
  set y := T.oppLen (σ 2 + 2)
  set A := T.oppLen (σ 0)
  set B := T.oppLen (σ 1)
  set C := T.oppLen (σ 2)
  set co := Real.cos (T.angleAt (σ 2))
  have hs1 : x + y = A + B := by linarith
  have hs2 : x ^ 2 + y ^ 2 = A ^ 2 + B ^ 2 := by linarith
  linear_combination hl + (1 + co) * hs2 - co * (x + y + A + B) * hs1
end Erdos634.Geometry
end

section
namespace Erdos634.SssCongruent
open Erdos634.Geometry RealInnerProductSpace
noncomputable def ev (T : Tri) : Fin 2 → Plane := ![T.pts 1 - T.pts 0, T.pts 2 - T.pts 0]
theorem ev_indep (T : Tri) : LinearIndependent ℝ (ev T) := by
  rw [ev, LinearIndependent.pair_iff]
  intro s t hst
  have haff := affineIndependent_iff.mp T.indep Finset.univ ![-s - t, s, t]
  have hw : ∑ i, (![-s - t, s, t] : Fin 3 → ℝ) i = 0 := by
    simp [Fin.sum_univ_three]; ring
  have hp : ∑ i, (![-s - t, s, t] : Fin 3 → ℝ) i • T.pts i = 0 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    have h : s • (T.pts 1 - T.pts 0) + t • (T.pts 2 - T.pts 0) = 0 := hst
    rw [smul_sub, smul_sub] at h
    rw [sub_smul, neg_smul]
    linear_combination (norm := module) h
  have hz := haff hw hp
  have h1 := hz 1 (Finset.mem_univ _)
  have h2 := hz 2 (Finset.mem_univ _)
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at h1 h2
  exact ⟨h1, h2⟩
noncomputable def evBasis (T : Tri) : Module.Basis (Fin 2) ℝ Plane :=
  basisOfLinearIndependentOfCardEqFinrank (ev_indep T) (by simp)
@[simp] theorem evBasis_apply (T : Tri) (i : Fin 2) : evBasis T i = ev T i := by
  simp [evBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
theorem inner_ev_eq {T U : Tri} (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j))
    (i j : Fin 2) : ⟪ev T i, ev T j⟫ = ⟪ev U i, ev U j⟫ := by
  have hnorm : ∀ (V : Tri) (a b : Fin 3), ‖V.pts a - V.pts b‖ = dist (V.pts a) (V.pts b) :=
    fun V a b => (dist_eq_norm _ _).symm
  have key : ∀ (V : Tri) (a b : Fin 2),
      ⟪ev V a, ev V b⟫
        = (dist (V.pts a.succ) (V.pts 0) ^ 2 + dist (V.pts b.succ) (V.pts 0) ^ 2
            - dist (V.pts a.succ) (V.pts b.succ) ^ 2) / 2 := by
    intro V a b
    have hsub : ev V a - ev V b = V.pts a.succ - V.pts b.succ := by
      fin_cases a <;> fin_cases b <;> simp [ev] <;> abel
    have hpol : ⟪ev V a, ev V b⟫ = (‖ev V a‖ ^ 2 + ‖ev V b‖ ^ 2 - ‖ev V a - ev V b‖ ^ 2) / 2 := by
      rw [@norm_sub_sq_real]; ring
    rw [hpol, hsub]
    have hea : ev V a = V.pts a.succ - V.pts 0 := by fin_cases a <;> simp [ev]
    have heb : ev V b = V.pts b.succ - V.pts 0 := by fin_cases b <;> simp [ev]
    rw [hea, heb, hnorm, hnorm, hnorm]
  rw [key T, key U, hd, hd, hd]
noncomputable def evMap (T U : Tri) : Plane →ₗ[ℝ] Plane := (evBasis T).constr ℝ (ev U)
theorem evMap_basis (T U : Tri) (i : Fin 2) : evMap T U (ev T i) = ev U i := by
  rw [evMap, ← evBasis_apply T i, Module.Basis.constr_basis]
theorem expand (T : Tri) (x : Plane) :
    x = (evBasis T).repr x 0 • ev T 0 + (evBasis T).repr x 1 • ev T 1 := by
  conv_lhs => rw [← (evBasis T).sum_repr x]
  rw [Fin.sum_univ_two, evBasis_apply, evBasis_apply]
theorem evMap_expand (T U : Tri) (x : Plane) :
    evMap T U x = (evBasis T).repr x 0 • ev U 0 + (evBasis T).repr x 1 • ev U 1 := by
  conv_lhs => rw [expand T x]
  rw [map_add, map_smul, map_smul, evMap_basis, evMap_basis]
theorem evMap_inner {T U : Tri} (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j))
    (x y : Plane) : ⟪evMap T U x, evMap T U y⟫ = ⟪x, y⟫ := by
  conv_lhs => rw [evMap_expand, evMap_expand]
  conv_rhs => rw [expand T x, expand T y]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    ← inner_ev_eq hd]
noncomputable def evEquiv (T U : Tri) : Plane ≃ₗ[ℝ] Plane :=
  (evBasis T).equiv (evBasis U) (Equiv.refl (Fin 2))
theorem evEquiv_eq (T U : Tri) (x : Plane) : evEquiv T U x = evMap T U x := by
  have hb : ∀ i, (evEquiv T U).toLinearMap (evBasis T i) = evMap T U (evBasis T i) := by
    intro i
    show evEquiv T U (evBasis T i) = evMap T U (evBasis T i)
    rw [evEquiv, Module.Basis.equiv_apply]
    simp only [Equiv.refl_apply, evBasis_apply, evMap_basis]
  exact congrFun (congrArg DFunLike.coe ((evBasis T).ext hb)) x
noncomputable def evIso {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) : Plane ≃ₗᵢ[ℝ] Plane :=
  (evEquiv T U).isometryOfInner (by
    intro x y
    rw [evEquiv_eq, evEquiv_eq]
    exact evMap_inner hd x y)
@[simp] theorem evIso_apply {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) (x : Plane) :
    evIso hd x = evMap T U x := by
  rw [evIso, LinearEquiv.coe_isometryOfInner, evEquiv_eq]
noncomputable def sssIso {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) : Plane ≃ᵢ Plane :=
  ((IsometryEquiv.addRight (-T.pts 0)).trans (evIso hd).toIsometryEquiv).trans
    (IsometryEquiv.addRight (U.pts 0))
theorem sssIso_apply {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) (x : Plane) :
    sssIso hd x = evMap T U (x + -T.pts 0) + U.pts 0 := by
  show evIso hd (x + -T.pts 0) + U.pts 0 = _
  rw [evIso_apply]
theorem congruent_of_dist {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) : T.Congruent U := by
  refine ⟨sssIso hd, Equiv.refl _, ?_⟩
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  intro k
  show sssIso hd (T.pts k) = U.pts k
  rcases htri k with rfl | rfl | rfl
  · rw [sssIso_apply]
    have h0 : T.pts 0 + -T.pts 0 = (0 : Plane) := by abel
    rw [h0, map_zero, zero_add]
  · rw [sssIso_apply]
    have h1 : T.pts 1 + -T.pts 0 = ev T 0 := by simp [ev]; abel
    rw [h1, evMap_basis]
    show U.pts 1 - U.pts 0 + U.pts 0 = U.pts 1
    abel
  · rw [sssIso_apply]
    have h2 : T.pts 2 + -T.pts 0 = ev T 1 := by simp [ev]; abel
    rw [h2, evMap_basis]
    show U.pts 2 - U.pts 0 + U.pts 0 = U.pts 2
    abel
end Erdos634.SssCongruent
end

section
namespace Erdos634.RouteOneVertexKill
open Erdos634.Geometry
theorem cornerAngle_lt_pi (T : Tri) (j : Fin 3) :
    cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) < Real.pi := by
  rw [Erdos634.Geometry.cornerAngle]
  rcases lt_or_eq_of_le (EuclideanGeometry.angle_le_pi
    (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) with h | h
  · exact h
  · exfalso
    have hcol : Collinear ℝ ({T.pts (j + 1), T.pts j, T.pts (j + 2)} : Set Plane) :=
      EuclideanGeometry.collinear_of_angle_eq_pi h
    have hidx : ∀ i j : Fin 3, i = j ∨ i = j + 1 ∨ i = j + 2 := by decide
    have hsub : Set.range T.pts ⊆ ({T.pts (j + 1), T.pts j, T.pts (j + 2)} : Set Plane) := by
      rintro _ ⟨i, rfl⟩
      have := hidx i j
      rcases this with rfl | rfl | rfl <;> simp
    have hrange : Collinear ℝ (Set.range T.pts) := hcol.subset hsub
    exact (affineIndependent_iff_not_collinear.mp T.indep) hrange
end Erdos634.RouteOneVertexKill
end

section
open Complex
namespace Erdos634.KConj
open Erdos634.Geometry Erdos634.DissectionMap Erdos634.CertCoord
variable {N : ℕ}
noncomputable def vc (T : Tri) (p : Plane) : ℝ := ∑ v, if T.pts v = p then T.angleAt v else 0
theorem vc_of_vertex (T : Tri) (v0 : Fin 3) : vc T (T.pts v0) = T.localAngle (T.pts v0) := by
  rw [vc, Tri.localAngle_vertex]
  have : ∀ v, (T.pts v = T.pts v0) ↔ v = v0 := fun v => T.indep.injective.eq_iff
  simp only [this]
  rw [Finset.sum_ite_eq']; simp; rfl
theorem vc_of_nonvertex (T : Tri) (p : Plane) (h : ∀ v, p ≠ T.pts v) : vc T p = 0 := by
  rw [vc]; exact Finset.sum_eq_zero (fun v _ => if_neg (fun h' => h v h'.symm))
end Erdos634.KConj
end

section
namespace Erdos634.Draft.LaczFormal.Graph
abbrev V2 : Type := ℝ × ℝ
def crs (u v : V2) : ℝ := u.1 * v.2 - u.2 * v.1
def dt (u v : V2) : ℝ := u.1 * v.1 + u.2 * v.2
def nsq (u : V2) : ℝ := u.1 ^ 2 + u.2 ^ 2
def SecOK (p q : V2) : Prop := 0 < crs p q ∨ (crs p q = 0 ∧ dt p q < 0)
def inCone (p q z : V2) : Prop := 0 ≤ crs p z ∧ 0 ≤ crs z q
def inInt (p q z : V2) : Prop := 0 < crs p z ∧ 0 < crs z q
def Par (u v : V2) : Prop := crs u v = 0 ∧ 0 < dt u v
theorem nsq_nonneg (u : V2) : 0 ≤ nsq u := by unfold nsq; positivity
theorem nsq_pos {u : V2} (h : u ≠ 0) : 0 < nsq u := by
  unfold nsq
  rcases lt_or_ge 0 (u.1 ^ 2 + u.2 ^ 2) with h1 | h1
  · exact h1
  · exfalso; apply h
    have h1' : u.1 ^ 2 + u.2 ^ 2 = 0 := le_antisymm h1 (by positivity)
    have : u.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
    have h2 : u.2 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
    exact Prod.ext this h2
theorem crs_dt_sq (u v : V2) : crs u v ^ 2 + dt u v ^ 2 = nsq u * nsq v := by
  unfold crs dt nsq; ring
theorem id_crs (p q r : V2) : nsq q * crs p r = dt q r * crs p q + crs q r * dt p q := by
  unfold crs dt nsq; ring
theorem id_dt (p q r : V2) : nsq q * dt p r = dt p q * dt q r - crs p q * crs q r := by
  unfold crs dt nsq; ring
theorem SecOK.ne_p {p q : V2} (h : SecOK p q) : p ≠ 0 := by
  rintro rfl
  unfold SecOK crs dt at h
  simp at h
theorem SecOK.ne_q {p q : V2} (h : SecOK p q) : q ≠ 0 := by
  rintro rfl
  unfold SecOK crs dt at h
  simp at h
theorem eq_zero_of_crs_dt {u v : V2} (hv : v ≠ 0) (h1 : crs u v = 0) (h2 : dt u v = 0) : u = 0 := by
  have := crs_dt_sq u v
  rw [h1, h2] at this
  have hn : nsq u * nsq v = 0 := by linarith
  rcases mul_eq_zero.mp hn with h | h
  · by_contra hu
    exact absurd h (nsq_pos hu).ne'
  · exact absurd h (nsq_pos hv).ne'
theorem Par.ne_left {u v : V2} (h : Par u v) : u ≠ 0 := by
  rintro rfl; unfold Par dt at h; simp at h
theorem Par.ne_right {u v : V2} (h : Par u v) : v ≠ 0 := by
  rintro rfl; unfold Par dt at h; simp at h
theorem Par.symm {u v : V2} (h : Par u v) : Par v u := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · unfold crs at h1 ⊢; linarith
  · unfold dt at h2 ⊢; linarith
theorem Par.trans {u v w : V2} (h1 : Par u v) (h2 : Par v w) : Par u w := by
  have hv : 0 < nsq v := nsq_pos h1.ne_right
  obtain ⟨c1, d1⟩ := h1
  obtain ⟨c2, d2⟩ := h2
  have e1 := id_crs u v w
  have e2 := id_dt u v w
  refine ⟨?_, ?_⟩
  · have : nsq v * crs u w = 0 := by rw [e1, c1, c2]; ring
    exact (mul_eq_zero.mp this).resolve_left hv.ne'
  · have : nsq v * dt u w = dt u v * dt v w := by rw [e2, c1]; ring
    have hpos : 0 < nsq v * dt u w := by rw [this]; exact mul_pos d1 d2
    exact (mul_pos_iff_of_pos_left hv).mp hpos
theorem Par.smul {u v : V2} (h : Par u v) : ∃ c : ℝ, 0 < c ∧ u = (c * v.1, c * v.2) := by
  have hv : 0 < nsq v := nsq_pos h.ne_right
  refine ⟨dt u v / nsq v, div_pos h.2 hv, ?_⟩
  have h0 : u.1 * v.2 - u.2 * v.1 = 0 := h.1
  ext
  · show u.1 = (dt u v / nsq v) * v.1
    rw [div_mul_eq_mul_div, eq_div_iff hv.ne']
    unfold dt nsq; linear_combination v.2 * h0
  · show u.2 = (dt u v / nsq v) * v.2
    rw [div_mul_eq_mul_div, eq_div_iff hv.ne']
    unfold dt nsq; linear_combination (-v.1) * h0
theorem inInt_smul {p q z : V2} {c : ℝ} (hc : 0 < c) (h : inInt p q z) :
    inInt p q (c * z.1, c * z.2) := by
  unfold inInt crs at *
  constructor <;> nlinarith [h.1, h.2]
theorem inInt_smul_iff {p q z : V2} {c : ℝ} (hc : 0 < c) :
    inInt p q (c * z.1, c * z.2) ↔ inInt p q z := by
  refine ⟨fun h => ?_, inInt_smul hc⟩
  have := inInt_smul (inv_pos.mpr hc) h
  have e : ((c⁻¹ * (c * z.1), c⁻¹ * (c * z.2)) : V2) = z := by
    ext <;> simp <;> field_simp
  simpa [e] using this
theorem affine_pos_small (A B : ℝ) (hA : 0 < A) : ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → 0 < A + ε * B := by
  refine ⟨A / (|B| + 1), by positivity, fun ε hε hεδ => ?_⟩
  have h1 : ε * (|B| + 1) < A := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < |B| + 1)).mp hεδ
    linarith
  have h2 : -(ε * |B|) ≤ ε * B := by
    have := neg_abs_le B
    nlinarith
  nlinarith [abs_nonneg B]
def zplus (q : V2) (ε : ℝ) : V2 := (q.1 - ε * q.2, q.2 + ε * q.1)
def zminus (q : V2) (ε : ℝ) : V2 := (q.1 + ε * q.2, q.2 - ε * q.1)
theorem minus_ray_int {p q : V2} (hs : SecOK p q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → inInt p q (zminus q ε) := by
  have hq := nsq_pos hs.ne_q
  have e1 : ∀ ε, crs p (zminus q ε) = crs p q - ε * dt p q := by
    intro ε; unfold crs dt zminus; ring
  have e2 : ∀ ε, crs (zminus q ε) q = ε * nsq q := by
    intro ε; unfold crs zminus nsq; ring
  rcases hs with h | ⟨h0, hd⟩
  · obtain ⟨δ, hδ, H⟩ := affine_pos_small (crs p q) (-(dt p q)) h
    refine ⟨δ, hδ, fun ε hε hεδ => ⟨?_, ?_⟩⟩
    · rw [e1]; have := H ε hε hεδ; linarith
    · rw [e2]; positivity
  · refine ⟨1, one_pos, fun ε hε _ => ⟨?_, ?_⟩⟩
    · rw [e1, h0]; nlinarith
    · rw [e2]; positivity
theorem minus_ray_int_of_int {p q r : V2} (h1 : 0 < crs p r) (h2 : 0 < crs r q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → inInt p q (zminus r ε) := by
  have e1 : ∀ ε, crs p (zminus r ε) = crs p r + ε * (-(dt p r)) := by
    intro ε; unfold crs dt zminus; ring
  have e2 : ∀ ε, crs (zminus r ε) q = crs r q + ε * dt r q := by
    intro ε; unfold crs dt zminus; ring
  obtain ⟨d1, hd1, H1⟩ := affine_pos_small (crs p r) (-(dt p r)) h1
  obtain ⟨d2, hd2, H2⟩ := affine_pos_small (crs r q) (dt r q) h2
  refine ⟨min d1 d2, lt_min hd1 hd2, fun ε hε hεδ => ⟨?_, ?_⟩⟩
  · rw [e1]; exact H1 ε hε (lt_of_lt_of_le hεδ (min_le_left _ _))
  · rw [e2]; exact H2 ε hε (lt_of_lt_of_le hεδ (min_le_right _ _))
theorem affine_limit (A B : ℝ) (h : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ 0 ≤ A + (1 / ((n : ℝ) + 1)) * B) : 0 ≤ A := by
  by_contra hA
  push_neg at hA
  obtain ⟨N, hN⟩ := exists_nat_gt (|B| / (-A))
  obtain ⟨n, hnN, hn⟩ := h N
  have hn1 : (N : ℝ) < n := by exact_mod_cast hnN
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have h1 : |B| / (-A) < (n : ℝ) + 1 := by linarith
  have h2 : |B| < ((n : ℝ) + 1) * (-A) := by
    have := (div_lt_iff₀ (by linarith : (0:ℝ) < -A)).mp h1
    linarith
  have h3 : (1 / ((n : ℝ) + 1)) * B ≤ (1 / ((n : ℝ) + 1)) * |B| :=
    mul_le_mul_of_nonneg_left (le_abs_self B) (by positivity)
  have h4 : (1 / ((n : ℝ) + 1)) * |B| < -A := by
    rw [one_div, inv_mul_lt_iff₀ hpos]; linarith
  linarith
theorem affine_interval {A B ε0 : ℝ} (hA : 0 ≤ A) (h0 : 0 ≤ A + ε0 * B) (hε0 : 0 < ε0) :
    ∀ ε : ℝ, 0 < ε → ε ≤ ε0 → 0 ≤ A + ε * B := by
  intro ε hε hle
  rcases le_total 0 B with hB | hB
  · nlinarith
  · nlinarith
section Family
variable {ι : Type*} [Fintype ι] (p q : ι → V2)
def Covers : Prop := ∀ z : V2, ∃ s, inCone (p s) (q s) z
def Disjoint' : Prop := ∀ s t, s ≠ t → ∀ z, ¬ (inInt (p s) (q s) z ∧ inInt (p t) (q t) z)
def AllOK : Prop := ∀ s, SecOK (p s) (q s)
theorem end_cover (hcov : Covers p q) (r : V2) :
    ∃ t, ∃ δ > 0, 0 ≤ crs (p t) r ∧ 0 ≤ crs r (q t) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → inCone (p t) (q t) (zplus r ε) := by
  classical
  choose s hs using fun n : ℕ => hcov (zplus r (1 / ((n : ℝ) + 1)))
  haveI : Nonempty ι := ⟨s 0⟩
  obtain ⟨t, ht⟩ := Finite.exists_infinite_fiber s
  have hinf : (s ⁻¹' {t}).Infinite := Set.infinite_coe_iff.mp ht
  have hmem : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ inCone (p t) (q t) (zplus r (1 / ((n : ℝ) + 1))) := by
    intro N
    obtain ⟨n, hn, hnN⟩ := hinf.exists_gt N
    refine ⟨n, hnN, ?_⟩
    have : s n = t := hn
    rw [← this]; exact hs n
  have f1 : ∀ ε : ℝ, crs (p t) (zplus r ε) = crs (p t) r + ε * dt (p t) r := by
    intro ε; unfold crs dt zplus; ring
  have f2 : ∀ ε : ℝ, crs (zplus r ε) (q t) = crs r (q t) + ε * (-(dt r (q t))) := by
    intro ε; unfold crs dt zplus; ring
  have hA1 : 0 ≤ crs (p t) r := affine_limit _ (dt (p t) r) (fun N => by
    obtain ⟨n, hn, h⟩ := hmem N
    exact ⟨n, hn, by rw [← f1]; exact h.1⟩)
  have hA2 : 0 ≤ crs r (q t) := affine_limit _ (-(dt r (q t))) (fun N => by
    obtain ⟨n, hn, h⟩ := hmem N
    exact ⟨n, hn, by rw [← f2]; exact h.2⟩)
  obtain ⟨n0, -, h0⟩ := hmem 0
  refine ⟨t, 1 / ((n0 : ℝ) + 1), by positivity, hA1, hA2, fun ε hε hle => ⟨?_, ?_⟩⟩
  · rw [f1]
    have h01 : 0 ≤ crs (p t) r + (1 / ((n0 : ℝ) + 1)) * dt (p t) r := by rw [← f1]; exact h0.1
    exact affine_interval hA1 h01 (by positivity) ε hε hle
  · rw [f2]
    have h02 : 0 ≤ crs r (q t) + (1 / ((n0 : ℝ) + 1)) * (-(dt r (q t))) := by rw [← f2]; exact h0.2
    exact affine_interval hA2 h02 (by positivity) ε hε hle
theorem succ_ray_aux {ps qs pt qt : V2} (hs : SecOK ps qs) (ht : SecOK pt qt)
    (hdisj : 0 < crs qs qt → ∀ z, ¬ (inInt ps qs z ∧ inInt pt qt z))
    (A1 : 0 ≤ crs pt qs) (A2 : 0 ≤ crs qs qt) (δ : ℝ) (hδ : 0 < δ)
    (hmem : ∀ ε : ℝ, 0 < ε → ε ≤ δ → inCone pt qt (zplus qs ε)) :
    Par pt qs := by
  have hq : qs ≠ 0 := hs.ne_q
  have hp : pt ≠ 0 := ht.ne_p
  have f1 : ∀ ε : ℝ, crs pt (zplus qs ε) = crs pt qs + ε * dt pt qs := by
    intro ε; unfold crs dt zplus; ring
  have f2 : ∀ ε : ℝ, crs (zplus qs ε) qt = crs qs qt + ε * (-(dt qs qt)) := by
    intro ε; unfold crs dt zplus; ring
  have m1 := (hmem δ hδ le_rfl).1
  have m2 := (hmem δ hδ le_rfl).2
  rw [f1] at m1
  rw [f2] at m2
  rcases A1.eq_or_lt with hA1 | hA1
  · 
    refine ⟨hA1.symm, ?_⟩
    rw [← hA1] at m1
    have hd0 : 0 ≤ dt pt qs := by nlinarith
    rcases hd0.eq_or_lt with hd | hd
    · exfalso; exact hp (eq_zero_of_crs_dt hq hA1.symm hd.symm)
    · exact hd
  · exfalso
    rcases A2.eq_or_lt with hA2 | hA2
    · have htq := ht.ne_q
      have hd : dt qs qt ≤ 0 := by rw [← hA2] at m2; nlinarith
      have e := id_crs pt qs qt
      rw [← hA2] at e
      have hq' := nsq_pos hq
      have hqt : crs qt qs = 0 := by unfold crs at hA2 ⊢; linarith
      rcases ht with h | ⟨h0, _⟩
      · have : nsq qs * crs pt qt ≤ 0 := by rw [e]; nlinarith
        nlinarith [mul_pos hq' h]
      · have h3 : dt qs qt * crs pt qs = 0 := by rw [h0, mul_zero] at e; linarith
        have h4 : dt qs qt = 0 := (mul_eq_zero.mp h3).resolve_right hA1.ne'
        have h5 : dt qt qs = 0 := by unfold dt at h4 ⊢; linarith
        exact htq (eq_zero_of_crs_dt hq hqt h5)
    · 
      have hst := hdisj hA2
      obtain ⟨d1, hd1, H1⟩ := minus_ray_int hs
      obtain ⟨d2, hd2, H2⟩ := minus_ray_int_of_int hA1 hA2
      set ε := min d1 d2 / 2 with hε
      have hεpos : 0 < ε := by have := lt_min hd1 hd2; positivity
      have hε1 : ε < d1 := by have := min_le_left d1 d2; linarith [lt_min hd1 hd2]
      have hε2 : ε < d2 := by have := min_le_right d1 d2; linarith [lt_min hd1 hd2]
      exact hst (zminus qs ε) ⟨H1 ε hεpos hε1, H2 ε hεpos hε2⟩
theorem succ_exists (hok : AllOK p q) (hcov : Covers p q) (hdis : Disjoint' p q) (s : ι) :
    ∃ t, Par (p t) (q s) := by
  obtain ⟨t, δ, hδ, A1, A2, hmem⟩ := end_cover p q hcov (q s)
  refine ⟨t, succ_ray_aux (hok s) (hok t) ?_ A1 A2 δ hδ hmem⟩
  intro hpos z
  have hst : s ≠ t := by
    rintro rfl
    unfold crs at hpos
    linarith
  exact hdis s t hst z
theorem end_inj (hok : AllOK p q) (hdis : Disjoint' p q) {s s' : ι} (hss : s ≠ s') :
    ¬ Par (q s') (q s) := by
  intro hpar
  obtain ⟨c, hc, hcq⟩ := hpar.smul
  obtain ⟨d1, hd1, H1⟩ := minus_ray_int (hok s)
  obtain ⟨d2, hd2, H2⟩ := minus_ray_int (hok s')
  set ε := min d1 d2 / 2 with hε
  have hεpos : 0 < ε := by have := lt_min hd1 hd2; positivity
  have hε1 : ε < d1 := by have := min_le_left d1 d2; linarith [lt_min hd1 hd2]
  have hε2 : ε < d2 := by have := min_le_right d1 d2; linarith [lt_min hd1 hd2]
  have h1 := H1 ε hεpos hε1
  have h2 := H2 ε hεpos hε2
  have hz : zminus (q s') ε = (c * (zminus (q s) ε).1, c * (zminus (q s) ε).2) := by
    rw [hcq]; unfold zminus; ext <;> simp <;> ring
  rw [hz] at h2
  exact hdis s s' hss (zminus (q s) ε) ⟨h1, (inInt_smul_iff hc).mp h2⟩
theorem succ_map (hok : AllOK p q) (hcov : Covers p q) (hdis : Disjoint' p q) :
    ∃ σ : ι → ι, (∀ s, Par (p (σ s)) (q s)) ∧ Function.Bijective σ := by
  choose σ hσ using succ_exists p q hok hcov hdis
  refine ⟨σ, hσ, ?_⟩
  have hinj : Function.Injective σ := by
    intro s s' h
    by_contra hne
    apply end_inj p q hok hdis hne
    have h1 := hσ s
    have h2 := hσ s'
    rw [← h] at h2
    exact h2.symm.trans h1
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
end Family
noncomputable def wd (p q : V2) : ℝ := Complex.arg ⟨dt p q, crs p q⟩
theorem wd_pos {p q : V2} (h : SecOK p q) : 0 < wd p q := by
  unfold wd
  rcases h with h | ⟨h0, hd⟩
  · have h1 : 0 ≤ Complex.arg ⟨dt p q, crs p q⟩ := Complex.arg_nonneg_iff.mpr (le_of_lt h)
    rcases h1.eq_or_lt with h2 | h2
    · exfalso
      have := (Complex.arg_eq_zero_iff).mp h2.symm
      simp at this
      linarith [this.2]
    · exact h2
  · have : Complex.arg ⟨dt p q, crs p q⟩ = Real.pi := by
      rw [Complex.arg_eq_pi_iff]; exact ⟨hd, h0⟩
    rw [this]; exact Real.pi_pos
theorem cycle_angle_sum (m : ℕ) (u v : ℕ → V2) (hu : ∀ j, u j ≠ 0)
    (hpar : ∀ j, Par (u (j + 1)) (v j)) (hper : u m = u 0) :
    ∃ k : ℤ, ∑ j ∈ Finset.range m, wd (u j) (v j) = 2 * Real.pi * k := by
  classical
  set U : ℕ → ℂ := fun j => ⟨(u j).1, (u j).2⟩ with hU
  set W : ℕ → ℂ := fun j => ⟨dt (u j) (v j), crs (u j) (v j)⟩ with hW
  choose c hc hcu using fun j => (hpar j).smul
  have hUne : ∀ j, U j ≠ 0 := by
    intro j h
    apply hu j
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [hU] at h1 h2
    exact Prod.ext h1 h2
  have hstep : ∀ j, (starRingEnd ℂ) (U j) * U (j + 1) = (c j : ℂ) * W j := by
    intro j
    have h1 := congrArg Prod.fst (hcu j)
    have h2 := congrArg Prod.snd (hcu j)
    apply Complex.ext
    · simp [hU, hW, dt]
      rw [h1, h2]; ring
    · simp [hU, hW, crs]
      rw [h1, h2]; ring
  have hprod1 : ∏ j ∈ Finset.range m, (starRingEnd ℂ) (U j) * U (j + 1)
      = ∏ j ∈ Finset.range m, (starRingEnd ℂ) (U j) * U j := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    congr 1
    have e1 := Finset.prod_range_succ (fun j => U j) m
    have e2 := Finset.prod_range_succ' (fun j => U j) m
    have hUm : U m = U 0 := by simp [hU, hper]
    have : (∏ j ∈ Finset.range m, U (j + 1)) * U 0 = (∏ j ∈ Finset.range m, U j) * U 0 := by
      rw [← e2, ← hUm, ← e1]
    exact mul_right_cancel₀ (hUne 0) this
  have hnn : ∀ j, (starRingEnd ℂ) (U j) * U j = ((‖U j‖ ^ 2 : ℝ) : ℂ) := by
    intro j; rw [Complex.conj_mul']; push_cast; rfl
  simp only [hstep, hnn] at hprod1
  rw [Finset.prod_mul_distrib] at hprod1
  have hW' : ∀ j, ((‖W j‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg (W j) : ℂ) * Complex.I) = W j := fun j =>
    Complex.norm_mul_exp_arg_mul_I (W j)
  have hWprod : ∏ j ∈ Finset.range m, W j
      = ((∏ j ∈ Finset.range m, ‖W j‖ : ℝ) : ℂ) * Complex.exp (((∑ j ∈ Finset.range m, Complex.arg (W j) : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [Finset.prod_congr rfl (fun j _ => (hW' j).symm)]
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    push_cast
    rw [Finset.sum_mul]
  have hargs : ∀ j, Complex.arg (W j) = wd (u j) (v j) := fun j => rfl
  simp only [hargs] at hWprod
  set S : ℝ := ∑ j ∈ Finset.range m, wd (u j) (v j) with hS
  have hmain : ((∏ j ∈ Finset.range m, c j : ℝ) : ℂ) * (((∏ j ∈ Finset.range m, ‖W j‖ : ℝ) : ℂ) * Complex.exp ((S : ℂ) * Complex.I))
      = ((∏ j ∈ Finset.range m, ‖U j‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hWprod]; push_cast at hprod1 ⊢; exact hprod1
  have hcpos : 0 < ∏ j ∈ Finset.range m, c j := Finset.prod_pos (fun j _ => hc j)
  have hWpos : 0 < ∏ j ∈ Finset.range m, ‖W j‖ := by
    apply Finset.prod_pos
    intro j _
    have : W j ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      have h2 := congrArg Complex.im h0
      simp [hW] at h1 h2
      exact hu j (eq_zero_of_crs_dt (hpar j).ne_right h2 h1)
    exact norm_pos_iff.mpr this
  set R1 : ℝ := (∏ j ∈ Finset.range m, c j) * ∏ j ∈ Finset.range m, ‖W j‖ with hR1def
  set R2 : ℝ := ∏ j ∈ Finset.range m, ‖U j‖ ^ 2 with hR2def
  have hR1 : 0 < R1 := mul_pos hcpos hWpos
  have hR2 : 0 ≤ R2 := Finset.prod_nonneg (fun _ _ => by positivity)
  have hmain' : (R1 : ℂ) * Complex.exp ((S : ℂ) * Complex.I) = (R2 : ℂ) := by
    rw [← hmain, hR1def]; push_cast; ring
  have hnorm := congrArg (fun z : ℂ => ‖z‖) hmain'
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hnorm
  rw [abs_of_pos hR1, abs_of_nonneg hR2] at hnorm
  have hexp : Complex.exp ((S : ℂ) * Complex.I) = 1 := by
    have h1 : (R1 : ℂ) * Complex.exp ((S : ℂ) * Complex.I) = (R1 : ℂ) * 1 := by
      rw [hmain', ← hnorm]; ring
    exact mul_left_cancel₀ (by exact_mod_cast hR1.ne') h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have him := congrArg Complex.im hn
  simp at him
  exact ⟨n, by linarith⟩
section Cycle
variable {ι : Type*} [Fintype ι] (p q : ι → V2)
theorem fan_cycle [Nonempty ι] (hok : AllOK p q) (hcov : Covers p q) (hdis : Disjoint' p q)
    (hsum : ∑ s, wd (p s) (q s) = 2 * Real.pi) :
    ∃ e : ℕ → ι, (∀ n, Par (p (e (n + 1))) (q (e n))) ∧ (∀ n, e (n + Fintype.card ι) = e n) ∧
      Set.InjOn e (Set.Iio (Fintype.card ι)) ∧ (∀ s, ∃ j < Fintype.card ι, e j = s) := by
  classical
  obtain ⟨σ, hσ, hb⟩ := succ_map p q hok hcov hdis
  obtain ⟨s0⟩ := ‹Nonempty ι›
  set σe : Equiv.Perm ι := Equiv.ofBijective σ hb with hσe
  have hfix : σ^[orderOf σe] s0 = s0 := by
    have h1 : (σe ^ orderOf σe) s0 = s0 := by rw [pow_orderOf_eq_one]; rfl
    have h2 := congrArg (fun g : ι → ι => g s0) (Equiv.Perm.iterate_eq_pow σe (orderOf σe))
    exact h2.trans h1
  have hperiodic : Function.IsPeriodicPt σ (orderOf σe) s0 := hfix
  have hmpos : 0 < Function.minimalPeriod σ s0 :=
    hperiodic.minimalPeriod_pos (orderOf_pos σe)
  set m := Function.minimalPeriod σ s0 with hm
  set e : ℕ → ι := fun j => σ^[j] s0 with he
  have hem : e m = e 0 := Function.isPeriodicPt_minimalPeriod σ s0
  have hstep : ∀ n, e (n + 1) = σ (e n) := fun n => Function.iterate_succ_apply' σ n s0
  have hPar : ∀ n, Par (p (e (n + 1))) (q (e n)) := fun n => by rw [hstep]; exact hσ _
  have hshift : ∀ n, e (n + m) = e n := fun n => by
    show σ^[n + m] s0 = σ^[n] s0
    rw [Function.iterate_add_apply]
    exact congrArg (σ^[n]) (Function.isPeriodicPt_minimalPeriod σ s0)
  have hinj : Set.InjOn e (Set.Iio m) := Function.iterate_injOn_Iio_minimalPeriod
  obtain ⟨k, hk⟩ := cycle_angle_sum m (fun j => p (e j)) (fun j => q (e j)) (fun j => (hok (e j)).ne_p)
    hPar (by show p (e m) = p (e 0); rw [hem])
  have hwpos : ∀ s, 0 < wd (p s) (q s) := fun s => wd_pos (hok s)
  have hSpos : 0 < ∑ j ∈ Finset.range m, wd (p (e j)) (q (e j)) :=
    Finset.sum_pos (fun j _ => hwpos _) ⟨0, Finset.mem_range.mpr hmpos⟩
  rw [hk] at hSpos
  have hk1 : 1 ≤ k := by
    by_contra h
    push_neg at h
    have : (k : ℝ) ≤ 0 := by exact_mod_cast (by omega : k ≤ 0)
    nlinarith [Real.pi_pos]
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  set O : Finset ι := (Finset.range m).image e with hO
  have hinjR : Set.InjOn e (↑(Finset.range m) : Set ℕ) := by
    intro a ha b hb' h
    exact hinj (by simpa using ha) (by simpa using hb') h
  have hOsum : ∑ s ∈ O, wd (p s) (q s) = ∑ j ∈ Finset.range m, wd (p (e j)) (q (e j)) :=
    Finset.sum_image hinjR
  have hsd := Finset.sum_sdiff (f := fun s => wd (p s) (q s)) (Finset.subset_univ O)
  have hall : ∀ s, s ∈ O := by
    intro s
    by_contra hs
    have hsm : s ∈ Finset.univ \ O := by simp [hs]
    have h1 : wd (p s) (q s) ≤ ∑ x ∈ Finset.univ \ O, wd (p x) (q x) :=
      Finset.single_le_sum (f := fun x => wd (p x) (q x)) (fun x _ => (hwpos x).le) hsm
    have h2 := hwpos s
    rw [hOsum, hk] at hsd
    nlinarith [Real.pi_pos]
  have hcard : Fintype.card ι = m := by
    have : O = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [← Finset.card_univ, ← this, hO, Finset.card_image_of_injOn hinjR, Finset.card_range]
  refine ⟨e, hPar, ?_, ?_, ?_⟩
  · intro n; rw [hcard]; exact hshift n
  · rw [hcard]; exact hinj
  · intro s
    obtain ⟨j, hj, hjs⟩ := Finset.mem_image.mp (hall s)
    exact ⟨j, by rw [hcard]; exact Finset.mem_range.mp hj, hjs⟩
end Cycle
end Erdos634.Draft.LaczFormal.Graph
end

section
namespace Erdos634.Draft.LaczFormal.Graph
open Erdos634.Geometry
def toV2 (x : Plane) : V2 := (x 0, x 1)
theorem crs_toV2 (u v : Plane) : crs (toV2 u) (toV2 v) = cross u v := rfl
theorem dt_toV2 (u v : Plane) : dt (toV2 u) (toV2 v) = inner ℝ u v := by
  rw [Erdos634.Geometry.inner_coords]; rfl
theorem toV2_ne_zero {u : Plane} (hu : u ≠ 0) : toV2 u ≠ 0 := by
  intro h
  apply hu
  have h0 : u 0 = 0 := congrArg Prod.fst h
  have h1 : u 1 = 0 := congrArg Prod.snd h
  ext i; fin_cases i <;> simp [h0, h1]
theorem nsq_toV2 (u : Plane) : nsq (toV2 u) = ‖u‖ ^ 2 := by
  rw [Erdos634.Geometry.norm_sq_coords]; rfl
theorem wd_eq_angle {u w : Plane} (hu : u ≠ 0) (hw : w ≠ 0) (hc : 0 ≤ cross u w) :
    wd (toV2 u) (toV2 w) = InnerProductGeometry.angle u w := by
  unfold wd
  have hz : (⟨dt (toV2 u) (toV2 w), crs (toV2 u) (toV2 w)⟩ : ℂ) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    exact toV2_ne_zero hu (eq_zero_of_crs_dt (toV2_ne_zero hw) h2 h1)
  rw [Complex.arg_of_im_nonneg_of_ne_zero (by simpa [crs_toV2] using hc) hz]
  unfold InnerProductGeometry.angle
  congr 1
  have hn : ‖(⟨dt (toV2 u) (toV2 w), crs (toV2 u) (toV2 w)⟩ : ℂ)‖ = ‖u‖ * ‖w‖ := by
    have h1 : ‖(⟨dt (toV2 u) (toV2 w), crs (toV2 u) (toV2 w)⟩ : ℂ)‖ ^ 2 = (‖u‖ * ‖w‖) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_mk, mul_pow, ← nsq_toV2, ← nsq_toV2, ← crs_dt_sq]
      ring
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1
  rw [hn]
  show dt (toV2 u) (toV2 w) / (‖u‖ * ‖w‖) = _
  rw [dt_toV2]
theorem wd_eq_angle_swap {u w : Plane} (hu : u ≠ 0) (hw : w ≠ 0) (hc : cross u w ≤ 0) :
    wd (toV2 w) (toV2 u) = InnerProductGeometry.angle u w := by
  rw [InnerProductGeometry.angle_comm]
  exact wd_eq_angle hw hu (by rw [cross_swap]; linarith)
def LocalCone (T : Tri) (V : Plane) (p q : V2) : Prop :=
  ∃ r > 0, ∀ y : Plane, dist y V < r → (y ∈ T.carrier ↔ inCone p q (toV2 (y - V)))
def SectorSpec (T : Tri) (V : Plane) (p q : V2) : Prop :=
  (∃ k : Fin 3, T.pts k = V ∧
      ((p = toV2 (T.pts (k + 1) - V) ∧ q = toV2 (T.pts (k + 2) - V)) ∨
       (p = toV2 (T.pts (k + 2) - V) ∧ q = toV2 (T.pts (k + 1) - V)))) ∨
  ((∀ k, T.pts k ≠ V) ∧ ∃ m : Fin 3, T.basis.coord m V = 0 ∧ (∀ j, j ≠ m → 0 < T.basis.coord j V) ∧
      q = (-p.1, -p.2) ∧ (p = toV2 (T.pts (m + 2) - T.pts (m + 1)) ∨ p = toV2 (T.pts (m + 1) - T.pts (m + 2))))
theorem vertexCone_iff_pos {u w : Plane} (hc : 0 < cross u w) (z : Plane) :
    z ∈ vertexCone u w ↔ inCone (toV2 u) (toV2 w) (toV2 z) := by
  unfold vertexCone inCone
  simp only [Set.mem_setOf_eq, crs_toV2]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mul_nonneg_iff_of_pos_right hc).mp h1, (mul_nonneg_iff_of_pos_right hc).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_nonneg h1 hc.le, mul_nonneg h2 hc.le⟩
theorem vertexCone_iff_neg {u w : Plane} (hc : cross u w < 0) (z : Plane) :
    z ∈ vertexCone u w ↔ inCone (toV2 w) (toV2 u) (toV2 z) := by
  unfold vertexCone inCone
  simp only [Set.mem_setOf_eq, crs_toV2]
  have e1 : cross w z = - cross z w := cross_swap w z
  have e2 : cross z u = - cross u z := cross_swap z u
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [e1]; nlinarith
    · rw [e2]; nlinarith
  · rintro ⟨h1, h2⟩
    rw [e1] at h1; rw [e2] at h2
    constructor <;> nlinarith
theorem corner_sector (T : Tri) (j : Fin 3) :
    ∃ p q : V2, SecOK p q ∧ LocalCone T (T.pts j) p q ∧ wd p q = T.localAngle (T.pts j) ∧
      SectorSpec T (T.pts j) p q := by
  obtain ⟨r, hr, hEq⟩ := T.inter_ball_eq_vertexCone j
  have hu : T.edgeVec j ≠ 0 := T.edgeVec_ne_zero j
  have hv : T.edgeVec' j ≠ 0 := T.edgeVec'_ne_zero j
  have hD : cross (T.edgeVec j) (T.edgeVec' j) = T.det := T.cross_edgeVec j
  have hdet : T.det ≠ 0 := T.det_ne_zero
  have hang : T.localAngle (T.pts j) = InnerProductGeometry.angle (T.edgeVec j) (T.edgeVec' j) := by
    rw [T.localAngle_vertex, T.cornerAngle_eq_angle]
  have hmem : ∀ y : Plane, dist y (T.pts j) < r →
      (y ∈ T.carrier ↔ y - T.pts j ∈ vertexCone (T.edgeVec j) (T.edgeVec' j)) := by
    intro y hy
    have h : y ∈ T.carrier ∩ Metric.ball (T.pts j) r ↔
        y ∈ {y : Plane | y - T.pts j ∈ vertexCone (T.edgeVec j) (T.edgeVec' j)} ∩ Metric.ball (T.pts j) r := by
      rw [hEq]
    have hb : y ∈ Metric.ball (T.pts j) r := by simpa [Metric.mem_ball] using hy
    simpa [hb] using h
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · refine ⟨toV2 (T.edgeVec' j), toV2 (T.edgeVec j), Or.inl ?_, ⟨r, hr, fun y hy => ?_⟩, ?_, Or.inl ⟨j, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
    · rw [crs_toV2, cross_swap, hD]; linarith
    · rw [hmem y hy, vertexCone_iff_neg (by rw [hD]; exact hneg)]
    · rw [hang]
      exact wd_eq_angle_swap hu hv (by rw [hD]; exact hneg.le)
  · refine ⟨toV2 (T.edgeVec j), toV2 (T.edgeVec' j), Or.inl ?_, ⟨r, hr, fun y hy => ?_⟩, ?_, Or.inl ⟨j, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
    · rw [crs_toV2, hD]; exact hpos
    · rw [hmem y hy, vertexCone_iff_pos (by rw [hD]; exact hpos)]
    · rw [hang]
      exact wd_eq_angle hu hv (by rw [hD]; exact hpos.le)
theorem inCone_straight_iff (p : V2) (z : V2) : inCone p (-p.1, -p.2) z ↔ 0 ≤ crs p z := by
  unfold inCone crs
  constructor
  · rintro ⟨h, _⟩; exact h
  · intro h; exact ⟨h, by nlinarith⟩
theorem fin3_add_ne (j : Fin 3) : j + 1 ≠ j + 2 := by revert j; decide
theorem fin3_ne_one (j : Fin 3) : j + 1 ≠ j := by revert j; decide
theorem fin3_ne_two (j : Fin 3) : j + 2 ≠ j := by revert j; decide
theorem fin3_e1 (m : Fin 3) : (m + 1) + 2 = m := by revert m; decide
theorem fin3_e2 (m : Fin 3) : (m + 1) + 1 = m + 2 := by revert m; decide
theorem localAngle_of_edge_coords (T : Tri) (m : Fin 3) (V : Plane) (h0 : T.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < T.basis.coord j V) : T.localAngle V = Real.pi := by
  classical
  have hv : ¬ ∃ j, V = T.pts j := by
    rintro ⟨j, hj⟩
    have h1 : T.basis.coord (j + 1) V = 0 := by rw [hj]; exact T.basis.coord_apply_ne (fin3_ne_one j)
    have h2 : T.basis.coord (j + 2) V = 0 := by rw [hj]; exact T.basis.coord_apply_ne (fin3_ne_two j)
    by_cases hm1 : j + 1 = m
    · have hm2 : j + 2 ≠ m := fun h => fin3_add_ne j (hm1.trans h.symm)
      exact absurd h2 (hpos _ hm2).ne'
    · exact absurd h1 (hpos _ hm1).ne'
  have hIn : ¬ ∀ j, 0 < T.basis.coord j V := fun h => absurd h0 (ne_of_gt (h m))
  rw [Tri.localAngle, dif_neg hv, if_neg hIn, if_pos ⟨m, h0, hpos⟩]
theorem crs_straight (p : V2) : crs p (-p.1, -p.2) = 0 := by unfold crs; ring
theorem dt_straight_neg {p : V2} (hp : p ≠ 0) : dt p (-p.1, -p.2) < 0 := by
  have := nsq_pos hp
  unfold dt; unfold nsq at this; nlinarith
theorem wd_straight {p : V2} (hp : p ≠ 0) : wd p (-p.1, -p.2) = Real.pi := by
  unfold wd
  rw [Complex.arg_eq_pi_iff]
  exact ⟨dt_straight_neg hp, crs_straight p⟩
theorem wd_ext {a : V2} (ha : a ≠ 0) : wd (-a.1, -a.2) a = Real.pi := by
  have hp : ((-a.1, -a.2) : V2) ≠ 0 := by
    intro h; apply ha
    have h1 : -a.1 = 0 := congrArg Prod.fst h
    have h2 : -a.2 = 0 := congrArg Prod.snd h
    exact Prod.ext (show a.1 = 0 by linarith) (show a.2 = 0 by linarith)
  have := wd_straight hp
  simpa using this
theorem straight_sector (T : Tri) (m : Fin 3) (V : Plane) (h0 : T.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < T.basis.coord j V) :
    ∃ p q : V2, SecOK p q ∧ LocalCone T V p q ∧ wd p q = T.localAngle V ∧ SectorSpec T V p q := by
  classical
  set e : Plane := T.pts (m + 2) - T.pts (m + 1) with hedef
  have he : e ≠ 0 := by
    rw [hedef, sub_ne_zero]
    intro h
    exact (fin3_add_ne m) (T.indep.injective h).symm
  have hdet : T.det ≠ 0 := T.det_ne_zero
  have hcd : ∀ y : Plane, T.basis.coord m y * T.det = cross e (y - T.pts (m + 1)) := by
    intro y
    have := T.coord_mul_det (m + 1) y
    rw [fin3_e1, fin3_e2] at this
    exact this
  have hcdV : cross e (V - T.pts (m + 1)) = 0 := by rw [← hcd V, h0, zero_mul]
  have hcr : ∀ y : Plane, cross e (y - V) = T.basis.coord m y * T.det := by
    intro y
    have : cross e (y - V) = cross e (y - T.pts (m + 1)) - cross e (V - T.pts (m + 1)) := by
      simp only [cross, PiLp.sub_apply]; ring
    rw [this, hcdV, ← hcd y]; ring
  obtain ⟨r, hr, hEq⟩ := T.inter_ball_eq_halfplane m (x := V) (hpos _ (fin3_ne_one m))
    (hpos _ (fin3_ne_two m))
  have hmem : ∀ y : Plane, dist y V < r → (y ∈ T.carrier ↔ 0 ≤ T.basis.coord m y) := by
    intro y hy
    have h : y ∈ T.carrier ∩ Metric.ball V r ↔ y ∈ {y | 0 ≤ T.basis.coord m y} ∩ Metric.ball V r := by
      rw [hEq]
    have hb : y ∈ Metric.ball V r := by simpa [Metric.mem_ball] using hy
    simpa [hb] using h
  have hang : T.localAngle V = Real.pi := localAngle_of_edge_coords T m V h0 hpos
  have hv : ¬ ∃ j, V = T.pts j := by
    rintro ⟨j, hj⟩
    have h1 : T.basis.coord (j + 1) V = 0 := by rw [hj]; exact T.basis.coord_apply_ne (fin3_ne_one j)
    have h2 : T.basis.coord (j + 2) V = 0 := by rw [hj]; exact T.basis.coord_apply_ne (fin3_ne_two j)
    by_cases hm1 : j + 1 = m
    · have hm2 : j + 2 ≠ m := fun h => fin3_add_ne j (hm1.trans h.symm)
      exact absurd h2 (hpos _ hm2).ne'
    · exact absurd h1 (hpos _ hm1).ne'
  have hvne : ∀ k, T.pts k ≠ V := fun k hk => hv ⟨k, hk.symm⟩
  have hpne : toV2 e ≠ 0 := toV2_ne_zero he
  have hcrs0 : ∀ p : V2, crs p (-p.1, -p.2) = 0 := by intro p; unfold crs; ring
  have hdtn : ∀ p : V2, p ≠ 0 → dt p (-p.1, -p.2) < 0 := by
    intro p hp
    have := nsq_pos hp
    unfold dt; unfold nsq at this; nlinarith
  have hwd : ∀ p : V2, p ≠ 0 → wd p (-p.1, -p.2) = Real.pi := by
    intro p hp
    unfold wd
    rw [Complex.arg_eq_pi_iff]
    exact ⟨hdtn p hp, hcrs0 p⟩
  rcases lt_or_gt_of_ne hdet with hneg | hposd
  · set pp : V2 := toV2 (T.pts (m + 1) - T.pts (m + 2)) with hppdef
    have hneg_e : T.pts (m + 1) - T.pts (m + 2) = -e := by rw [hedef, neg_sub]
    have hpp : pp ≠ 0 := by rw [hppdef, hneg_e]; exact toV2_ne_zero (neg_ne_zero.mpr he)
    refine ⟨pp, (-pp.1, -pp.2), Or.inr ⟨hcrs0 pp, hdtn pp hpp⟩, ⟨r, hr, fun y hy => ?_⟩, ?_,
      Or.inr ⟨hvne, m, h0, hpos, rfl, Or.inr rfl⟩⟩
    · rw [hmem y hy, inCone_straight_iff, hppdef, crs_toV2, hneg_e, cross_neg_left, hcr y]
      constructor
      · intro h; nlinarith [mul_nonneg h (neg_nonneg.mpr hneg.le)]
      · intro h; by_contra hc; push_neg at hc; nlinarith [mul_pos_of_neg_of_neg hc hneg]
    · rw [hang]; exact hwd pp hpp
  · set pp : V2 := toV2 e with hppdef
    have hpp : pp ≠ 0 := hpne
    refine ⟨pp, (-pp.1, -pp.2), Or.inr ⟨hcrs0 pp, hdtn pp hpp⟩, ⟨r, hr, fun y hy => ?_⟩, ?_,
      Or.inr ⟨hvne, m, h0, hpos, rfl, Or.inl rfl⟩⟩
    · rw [hmem y hy, inCone_straight_iff, hppdef, crs_toV2, hcr y]
      constructor
      · intro h; nlinarith [mul_nonneg h hposd.le]
      · intro h; by_contra hc; push_neg at hc; nlinarith [mul_neg_of_neg_of_pos hc hposd]
    · rw [hang]; exact hwd pp hpp
theorem Tri.localAngle_eq_zero_of_not_mem (T : Tri) {V : Plane} (h : V ∉ T.carrier) : T.localAngle V = 0 := by
  classical
  rw [Tri.localAngle]
  split
  · rename_i hv
    have hvmem : V ∈ Set.range T.pts := ⟨hv.choose, hv.choose_spec.symm⟩
    exact absurd (subset_convexHull ℝ _ hvmem) h
  · split
    · rename_i hall
      have hint : V ∈ interior T.carrier := (T.mem_interior_iff_coord_pos _).mpr hall
      exact absurd (interior_subset hint) h
    · split
      · rename_i hedge
        obtain ⟨kk, hkk1, hkk2⟩ := hedge
        have hmem : V ∈ T.carrier := by
          rw [T.carrier_eq_nonneg_coord]
          intro j
          rcases eq_or_ne j kk with rfl | hne
          · exact hkk1.ge
          · exact (hkk2 j hne).le
        exact absurd hmem h
      · rfl
theorem local_sector (T : Tri) {V : Plane} (hV : V ∈ T.carrier) (hint : V ∉ interior T.carrier) :
    ∃ p q : V2, SecOK p q ∧ LocalCone T V p q ∧ wd p q = T.localAngle V ∧ SectorSpec T V p q := by
  classical
  by_cases hvert : ∃ j, V = T.pts j
  · obtain ⟨j, rfl⟩ := hvert; exact corner_sector T j
  · push_neg at hvert
    rcases T.classify (fun k h => hvert k h) with hpos | ⟨k, hk0, hk⟩ | ⟨k, hkneg⟩
    · exact absurd ((T.mem_interior_iff_coord_pos V).mpr hpos) hint
    · exact straight_sector T k V hk0 hk
    · rw [T.carrier_eq_nonneg_coord] at hV; exact absurd (hV k) (not_le.mpr hkneg)
variable {N : ℕ}
theorem inCone_smul_iff {p q z : V2} {c : ℝ} (hc : 0 < c) :
    inCone p q (c * z.1, c * z.2) ↔ inCone p q z := by
  unfold inCone crs
  simp only
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra h; push_neg at h; nlinarith [mul_pos hc (neg_pos.mpr h)]
    · by_contra h; push_neg at h; nlinarith [mul_pos hc (neg_pos.mpr h)]
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith [mul_nonneg hc.le h1, mul_nonneg hc.le h2]
open Erdos634.CertCoord in
noncomputable def ptOf (V : Plane) (z : V2) (ε : ℝ) : Plane := V + ε • mkPt z.1 z.2
open Erdos634.CertCoord in
theorem toV2_ptOf (V : Plane) (z : V2) (ε : ℝ) : toV2 (ptOf V z ε - V) = (ε * z.1, ε * z.2) := by
  simp [toV2, ptOf]
open Erdos634.CertCoord in
theorem exists_ptOf_small (V : Plane) (z : V2) {r : ℝ} (hr : 0 < r) :
    ∃ ε > 0, dist (ptOf V z ε) V < r := by
  refine ⟨r / (2 * (‖mkPt z.1 z.2‖ + 1)), by positivity, ?_⟩
  rw [dist_eq_norm]
  have : ptOf V z (r / (2 * (‖mkPt z.1 z.2‖ + 1))) - V = (r / (2 * (‖mkPt z.1 z.2‖ + 1))) • mkPt z.1 z.2 := by
    simp [ptOf]
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hn := norm_nonneg (mkPt z.1 z.2)
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith
theorem exists_min_pos {ι : Type*} [Finite ι] (r : ι → ℝ) (hr : ∀ i, 0 < r i) : ∃ r0 > 0, ∀ i, r0 ≤ r i := by
  by_cases hne : Nonempty ι
  · obtain ⟨i0, hi0⟩ := Finite.exists_min r
    exact ⟨r i0, hr i0, hi0⟩
  · exact ⟨1, one_pos, fun i => absurd ⟨i⟩ hne⟩
theorem mem_interior_of_inInt {T : Tri} {V : Plane} {p q : V2} {r : ℝ}
    (hr : ∀ y : Plane, dist y V < r → (y ∈ T.carrier ↔ inCone p q (toV2 (y - V))))
    {y : Plane} (hy : dist y V < r) (hi : inInt p q (toV2 (y - V))) : y ∈ interior T.carrier := by
  have c0 : Continuous (fun y : Plane => y 0) := by fun_prop
  have c1 : Continuous (fun y : Plane => y 1) := by fun_prop
  have hc1 : Continuous (fun y : Plane => crs p (toV2 (y - V))) := by
    unfold crs toV2; simp only [PiLp.sub_apply]; fun_prop
  have hc2 : Continuous (fun y : Plane => crs (toV2 (y - V)) q) := by
    unfold crs toV2; simp only [PiLp.sub_apply]; fun_prop
  have hopen : IsOpen {y : Plane | dist y V < r ∧ (0 < crs p (toV2 (y - V)) ∧ 0 < crs (toV2 (y - V)) q)} :=
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
      ((isOpen_lt continuous_const hc1).inter (isOpen_lt continuous_const hc2))
  refine interior_maximal ?_ hopen ⟨hy, hi.1, hi.2⟩
  intro y ⟨hy1, hy2, hy3⟩
  exact (hr y hy1).mpr ⟨hy2.le, hy3.le⟩
end Erdos634.Draft.LaczFormal.Graph
end

section
namespace Erdos634.Draft.LaczFormal.Graph
open Erdos634.Geometry
variable {N : ℕ}
theorem edge_coords_not_vertex (T : Tri) (m : Fin 3) (V : Plane) (h0 : T.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < T.basis.coord j V) : ∀ k, T.pts k ≠ V := by
  intro k hk
  have h1 : T.basis.coord (k + 1) V = 0 := by rw [← hk]; exact T.basis.coord_apply_ne (fin3_ne_one k)
  have h2 : T.basis.coord (k + 2) V = 0 := by rw [← hk]; exact T.basis.coord_apply_ne (fin3_ne_two k)
  by_cases hm1 : k + 1 = m
  · have hm2 : k + 2 ≠ m := fun h => fin3_add_ne k (hm1.trans h.symm)
    exact absurd h2 (hpos _ hm2).ne'
  · exact absurd h1 (hpos _ hm1).ne'
theorem secOK_ext {a : V2} (ha : a ≠ 0) : SecOK (-a.1, -a.2) a := by
  have hp : ((-a.1, -a.2) : V2) ≠ 0 := by
    intro h; apply ha
    have h1 : -a.1 = 0 := congrArg Prod.fst h
    have h2 : -a.2 = 0 := congrArg Prod.snd h
    exact Prod.ext (show a.1 = 0 by linarith) (show a.2 = 0 by linarith)
  right
  have h1 := crs_straight (-a.1, -a.2)
  have h2 := dt_straight_neg hp
  simp only [neg_neg] at h1 h2
  exact ⟨h1, h2⟩
end Erdos634.Draft.LaczFormal.Graph
end

section
open Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
theorem perm_opp (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (σ (k + 2) + 1 = σ k ∧ σ (k + 2) + 2 = σ (k + 1)) ∨ (σ (k + 2) + 1 = σ (k + 1) ∧ σ (k + 2) + 2 = σ k) := by
  revert σ k; decide
theorem fin3_p2p1 (k : Fin 3) : k + 2 + 1 = k := by revert k; decide
theorem fin3_p2p2 (k : Fin 3) : k + 2 + 2 = k + 1 := by revert k; decide
theorem nsq_toV2_sub (x y : Plane) : nsq (toV2 (x - y)) = dist x y ^ 2 := by
  rw [nsq_toV2, ← dist_eq_norm]
theorem perm_adj (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (σ (k + 1) = σ k + 1 ∧ σ (k + 2) = σ k + 2) ∨ (σ (k + 1) = σ k + 2 ∧ σ (k + 2) = σ k + 1) := by
  revert σ k; decide
end Erdos634.Draft.LaczFormal.Graph
end

section
open Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
theorem cyc_mod {ι : Type*} (e : ℕ → ι) (k : ℕ) (hper : ∀ n, e (n + k) = e n) (x : ℕ) : e x = e (x % k) := by
  have hmul : ∀ q' x, e (x + q' * k) = e x := by
    intro q'
    induction q' with
    | zero => intro x; simp
    | succ q ih => intro x; rw [Nat.succ_mul, ← add_assoc, hper (x + q * k), ih]
  have := hmul (x / k) (x % k)
  rw [show x % k + x / k * k = x by rw [mul_comm]; exact Nat.mod_add_div x k] at this
  exact this
def armP (kk : Fin 3) (fl : Bool) : Fin 3 := if fl then kk + 2 else kk + 1
def armQ (kk : Fin 3) (fl : Bool) : Fin 3 := if fl then kk + 1 else kk + 2
theorem spec_corner_data {T : Tri} {V : Plane} {p q : V2} (hspec : SectorSpec T V p q) (hv : ∃ k, T.pts k = V) :
    ∃ (kk : Fin 3) (fl : Bool), T.pts kk = V ∧ p = toV2 (T.pts (armP kk fl) - V) ∧ q = toV2 (T.pts (armQ kk fl) - V) := by
  rcases hspec with ⟨k, hk, hpq⟩ | ⟨hnv, -⟩
  · rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨k, false, hk, by simp [armP, h1], by simp [armQ, h2]⟩
    · exact ⟨k, true, hk, by simp [armP, h1], by simp [armQ, h2]⟩
  · obtain ⟨k, hk⟩ := hv
    exact absurd hk (hnv k)
theorem armP_ne (kk : Fin 3) (fl : Bool) : armP kk fl ≠ kk := by
  cases fl
  · exact fin3_ne_one kk
  · exact fin3_ne_two kk
theorem armQ_ne (kk : Fin 3) (fl : Bool) : armQ kk fl ≠ kk := by
  cases fl
  · exact fin3_ne_two kk
  · exact fin3_ne_one kk
theorem armPQ_ne (kk : Fin 3) (fl : Bool) : armP kk fl ≠ armQ kk fl := by
  cases fl
  · exact fin3_add_ne kk
  · exact (fin3_add_ne kk).symm
theorem fin3_arm (kk a : Fin 3) (h : a ≠ kk) : a = kk + 1 ∨ a = kk + 2 := by
  revert kk a; decide
end Erdos634.Draft.LaczFormal.Graph
end

section
namespace Erdos634.Draft.LaczFormal.Graph
open Erdos634.Geometry
variable {N : ℕ}
theorem wd_neg_left {p q : V2} (h : 0 < crs p q) : wd (-q.1, -q.2) p = Real.pi - wd p q := by
  unfold wd
  have hz : (⟨dt p q, crs p q⟩ : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have h2 : (⟨dt (-q.1, -q.2) p, crs (-q.1, -q.2) p⟩ : ℂ) = ⟨-dt p q, crs p q⟩ := by
    apply Complex.ext
    · simp [dt]; ring
    · simp [crs]; ring
  rw [h2, Complex.arg_of_im_pos (by simpa using h), Complex.arg_of_im_pos (by simpa using h)]
  have hn : ‖(⟨-dt p q, crs p q⟩ : ℂ)‖ = ‖(⟨dt p q, crs p q⟩ : ℂ)‖ := by
    have e : ‖(⟨-dt p q, crs p q⟩ : ℂ)‖ ^ 2 = ‖(⟨dt p q, crs p q⟩ : ℂ)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_mk, Complex.normSq_mk]; ring
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp e
  rw [hn]
  simp only [Complex.re_ofReal_mul]
  rw [show (-dt p q) / ‖(⟨dt p q, crs p q⟩ : ℂ)‖ = -(dt p q / ‖(⟨dt p q, crs p q⟩ : ℂ)‖) by ring, Real.arccos_neg]
theorem crs_pos_of_corner {T : Tri} {V : Plane} {p q : V2} (hok : SecOK p q)
    (hspec : SectorSpec T V p q) (hv : ∃ k, T.pts k = V) : 0 < crs p q := by
  rcases hspec with ⟨k, hk, hpq⟩ | ⟨hnv, _⟩
  · have hD : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k) = T.det := T.det_cyclic k
    have hdet : T.det ≠ 0 := T.det_ne_zero
    subst hk
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2
      rcases hok with h | ⟨h0, _⟩
      · exact h
      · rw [crs_toV2, hD] at h0; exact absurd h0 hdet
    · subst h1 h2
      rcases hok with h | ⟨h0, _⟩
      · exact h
      · rw [crs_toV2, cross_swap, hD] at h0
        exact absurd (neg_eq_zero.mp h0) hdet
  · obtain ⟨k, hk⟩ := hv
    exact absurd hk (hnv k)
end Erdos634.Draft.LaczFormal.Graph
end

section
open Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
def TriStep (T : Tri) (d : V2) (U U' : Plane) : Prop :=
  ∃ kk f g : Fin 3, T.pts kk = U ∧ T.pts f = U' ∧ f ≠ kk ∧ g ≠ kk ∧ g ≠ f ∧
    Par (toV2 (U' - U)) d ∧ 0 < crs d (toV2 (T.pts g - U))
theorem triStep_of_start {T : Tri} {d : V2} {U : Plane} (kk : Fin 3) (fl : Bool) (hk : T.pts kk = U) {p q : V2}
    (hp : p = toV2 (T.pts (armP kk fl) - U)) (hq : q = toV2 (T.pts (armQ kk fl) - U))
    (hcrs : 0 < crs p q) (hpar : Par p d) : TriStep T d U (T.pts (armP kk fl)) := by
  obtain ⟨c, hc, hcp⟩ := hpar.smul
  refine ⟨kk, armP kk fl, armQ kk fl, hk, rfl, armP_ne kk fl, armQ_ne kk fl, (armPQ_ne kk fl).symm, ?_, ?_⟩
  · rw [← hp]; exact hpar
  · have h1 : crs p q = c * crs d q := by rw [hcp]; unfold crs; ring
    rw [← hq]
    rw [h1] at hcrs
    exact (mul_pos_iff_of_pos_left hc).mp hcrs
theorem no_straight_of_sum {ι : Type*} [Fintype ι] (p q : ι → V2) (hok : ∀ s, SecOK (p s) (q s))
    {s t : ι} (hst : s ≠ t) (hs : wd (p s) (q s) = Real.pi) (hsum : ∑ x, wd (p x) (q x) ≤ Real.pi) : False := by
  classical
  have h1 : wd (p s) (q s) + wd (p t) (q t) ≤ ∑ x, wd (p x) (q x) := by
    have hpair : wd (p s) (q s) + wd (p t) (q t) = ∑ x ∈ ({s, t} : Finset ι), wd (p x) (q x) :=
      (Finset.sum_pair (f := fun x => wd (p x) (q x)) hst).symm
    rw [hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => (wd_pos (hok x)).le)
  have := wd_pos (hok t)
  linarith
theorem dist_of_toV2 {x y : Plane} {c : ℝ} (hc : 0 ≤ c) {d : V2} (h : toV2 (y - x) = (c * d.1, c * d.2)) :
    dist y x = c * Real.sqrt (nsq d) := by
  have h1 : dist y x ^ 2 = (c * Real.sqrt (nsq d)) ^ 2 := by
    rw [← nsq_toV2_sub, h, mul_pow, Real.sq_sqrt (nsq_nonneg d)]
    unfold nsq; simp only; ring
  exact (pow_left_inj₀ dist_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) two_ne_zero).mp h1
end Erdos634.Draft.LaczFormal.Graph
end

section
open Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
theorem inCone_convex {p q x y : V2} (hx : inCone p q x) (hy : inCone p q y) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : inCone p q ((a * x.1 + b * y.1, a * x.2 + b * y.2) : V2) := by
  unfold inCone crs at *
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor <;> simp only <;> nlinarith [mul_nonneg ha hx1, mul_nonneg hb hy1, mul_nonneg ha hx2, mul_nonneg hb hy2]
namespace ExtFan
end ExtFan
end Erdos634.Draft.LaczFormal.Graph
end

section
namespace Erdos634.RegionDissection
open Erdos634.Geometry
variable {M N : ℕ}
structure RegionDissection (N : ℕ) where
  region : Set Plane
  tile : Fin N → Tri
  covers : (⋃ i, (tile i).carrier) = region
  interiors_disjoint :
    Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier)
def _root_.Erdos634.Geometry.Dissection.toRegion (D : Dissection N) : RegionDissection N where
  region := D.target.carrier
  tile := D.tile
  covers := D.covers
  interiors_disjoint := D.interiors_disjoint
namespace RegionDissection
theorem tile_interior_subset (R : RegionDissection N) (i : Fin N) :
    interior (R.tile i).carrier ⊆ interior R.region :=
  interior_mono (by rw [← R.covers]; exact Set.subset_iUnion (fun k => (R.tile k).carrier) i)
end RegionDissection
def unionRegion (R1 : RegionDissection M) (R2 : RegionDissection N)
    (hdisj : Disjoint (interior R1.region) (interior R2.region)) :
    RegionDissection (M + N) where
  region := R1.region ∪ R2.region
  tile := Fin.append R1.tile R2.tile
  covers := by
    rw [← R1.covers, ← R2.covers]
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      induction i using Fin.addCases with
      | left j => left; exact ⟨j, by rwa [Fin.append_left] at hi⟩
      | right j => right; exact ⟨j, by rwa [Fin.append_right] at hi⟩
    · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
      · exact ⟨Fin.castAdd N j, by rwa [Fin.append_left]⟩
      · exact ⟨Fin.natAdd M j, by rwa [Fin.append_right]⟩
  interiors_disjoint := by
    intro i j hij
    induction i using Fin.addCases with
    | left i' =>
      induction j using Fin.addCases with
      | left j' =>
        simp only [Fin.append_left]; exact R1.interiors_disjoint (by simpa using hij)
      | right j' =>
        simp only [Fin.append_left, Fin.append_right]
        exact hdisj.mono (R1.tile_interior_subset i') (R2.tile_interior_subset j')
    | right i' =>
      induction j using Fin.addCases with
      | left j' =>
        simp only [Fin.append_left, Fin.append_right]
        exact hdisj.symm.mono (R2.tile_interior_subset i') (R1.tile_interior_subset j')
      | right j' =>
        simp only [Fin.append_right]; exact R2.interiors_disjoint (by simpa using hij)
@[simp] theorem unionRegion_region (R1 : RegionDissection M) (R2 : RegionDissection N)
    (hdisj : Disjoint (interior R1.region) (interior R2.region)) :
    (unionRegion R1 R2 hdisj).region = R1.region ∪ R2.region := rfl
structure CongruentRegionDissection (N : ℕ) extends RegionDissection N where
  model : Tri
  tiles_congruent : ∀ i, (tile i).Congruent model
def _root_.Erdos634.Geometry.CongruentDissection.toRegion (D : CongruentDissection N) :
    CongruentRegionDissection N where
  toRegionDissection := D.toDissection.toRegion
  model := D.model
  tiles_congruent := D.tiles_congruent
def emptyRegion : RegionDissection 0 where
  region := ∅
  tile := fun i => absurd i.isLt (by omega)
  covers := by simp
  interiors_disjoint := by intro i; exact absurd i.isLt (by omega)
theorem emptyRegion_disjoint (R : RegionDissection N) :
    Disjoint (interior R.region) (interior emptyRegion.region) := by
  simp [emptyRegion]
@[simp] theorem unionRegion_empty (R : RegionDissection N) :
    (unionRegion R emptyRegion (emptyRegion_disjoint R)).region = R.region := by
  simp [emptyRegion]
variable {N : ℕ}
noncomputable def mapRegionDissection {N : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (R : RegionDissection N) :
    RegionDissection N where
  region := e '' R.region
  tile := fun i => Erdos634.DissectionMap.mapTri e (R.tile i)
  covers := by
    simp only [Erdos634.DissectionMap.mapTri_carrier]
    rw [← Set.image_iUnion, R.covers]
  interiors_disjoint := by
    intro i j hij
    have h := R.interiors_disjoint hij
    have hcont : Continuous e := AffineEquiv.continuous_of_finiteDimensional e
    have hcont' : Continuous e.symm := AffineEquiv.continuous_of_finiteDimensional e.symm
    let eh : Plane ≃ₜ Plane := ⟨e.toEquiv, hcont, hcont'⟩
    have himg : ∀ S : Set Plane, interior (e '' S) = e '' interior S := fun S => (eh.image_interior S).symm
    simp only [Erdos634.DissectionMap.mapTri_carrier, himg]
    exact (Set.disjoint_image_iff e.injective).mpr h
@[simp] theorem mapRegionDissection_region {N : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (R : RegionDissection N) :
    (mapRegionDissection e R).region = e '' R.region := rfl
@[simp] theorem mapRegionDissection_tile {N : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (R : RegionDissection N)
    (i : Fin N) :
    (mapRegionDissection e R).tile i = Erdos634.DissectionMap.mapTri e (R.tile i) := rfl
end Erdos634.RegionDissection
end

section
open MeasureTheory Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
theorem not_interior_of_mem_other (D : RegionDissection N) {i j : Fin N} (hij : i ≠ j) {V : Plane}
    (hi : V ∈ (D.tile i).carrier) : V ∉ interior (D.tile j).carrier := by
  intro hj
  have hcl : V ∈ closure (interior (D.tile i).carrier) := by
    rw [(D.tile i).convex.closure_interior_eq_closure_of_nonempty_interior (D.tile i).interior_nonempty,
      (D.tile i).isCompact.isClosed.closure_eq]
    exact hi
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hcl _ isOpen_interior hj
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hy2 hy1
theorem not_interior_of_vertex (D : RegionDissection N) {V : Plane} (hv : ∃ i k, (D.tile i).pts k = V)
    (j : Fin N) : V ∉ interior (D.tile j).carrier := by
  obtain ⟨i, k, hk⟩ := hv
  have hmem : V ∈ (D.tile i).carrier := hk ▸ subset_convexHull ℝ _ ⟨k, rfl⟩
  by_cases hij : i = j
  · subst hij
    intro hint
    have h1 := (D.tile i).mem_interior_iff_coord_pos V |>.mp hint
    have h2 : (D.tile i).basis.coord (k + 1) V = 0 := by
      rw [← hk]; exact (D.tile i).basis.coord_apply_ne (fin3_ne_one k)
    exact absurd h2 (h1 _).ne'
  · exact not_interior_of_mem_other D hij hmem
def AtV (D : RegionDissection N) (V : Plane) : Type := {i : Fin N // V ∈ (D.tile i).carrier}
noncomputable instance (D : RegionDissection N) (V : Plane) : Fintype (AtV D V) := by
  classical unfold AtV; exact Subtype.fintype _
theorem common_radius (D : RegionDissection N) (V : Plane) (p q : AtV D V → V2)
    (hloc : ∀ s : AtV D V, LocalCone (D.tile s.1) V (p s) (q s)) :
    ∃ r > 0, (∀ s : AtV D V, ∀ y : Plane, dist y V < r →
        (y ∈ (D.tile s.1).carrier ↔ inCone (p s) (q s) (toV2 (y - V)))) ∧
      (∀ i : Fin N, V ∉ (D.tile i).carrier → ∀ y : Plane, dist y V < r → y ∉ (D.tile i).carrier) := by
  classical
  choose rs hrs hiff using hloc
  have hρ : ∀ i : Fin N, ∃ ρ > 0, V ∉ (D.tile i).carrier →
      ∀ y : Plane, dist y V < ρ → y ∉ (D.tile i).carrier := by
    intro i
    by_cases h : V ∈ (D.tile i).carrier
    · exact ⟨1, one_pos, fun h' => absurd h h'⟩
    · have hopen : IsOpen ((D.tile i).carrier)ᶜ := (D.tile i).isCompact.isClosed.isOpen_compl
      obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen V h
      exact ⟨ρ, hρ, fun _ y hy => hball (by simpa [Metric.mem_ball] using hy)⟩
  choose ρ hρpos hρ' using hρ
  obtain ⟨r1, hr1, hle1⟩ := exists_min_pos rs hrs
  obtain ⟨r2, hr2, hle2⟩ := exists_min_pos ρ hρpos
  exact ⟨min r1 r2, lt_min hr1 hr2,
    fun s y hy => hiff s y (lt_of_lt_of_le hy ((min_le_left _ _).trans (hle1 s))),
    fun i hi y hy => hρ' i hi y (lt_of_lt_of_le hy ((min_le_right _ _).trans (hle2 i)))⟩
theorem tiles_disjoint (D : RegionDissection N) (V : Plane) (p q : AtV D V → V2)
    (hloc : ∀ s : AtV D V, LocalCone (D.tile s.1) V (p s) (q s)) :
    Disjoint' p q := by
  intro s t hst z ⟨hzs, hzt⟩
  obtain ⟨rs, hrs, hs⟩ := hloc s
  obtain ⟨rt, hrt, ht⟩ := hloc t
  obtain ⟨ε, hε, hd⟩ := exists_ptOf_small V z (lt_min hrs hrt)
  have hds : dist (ptOf V z ε) V < rs := lt_of_lt_of_le hd (min_le_left _ _)
  have hdt : dist (ptOf V z ε) V < rt := lt_of_lt_of_le hd (min_le_right _ _)
  rw [← inInt_smul_iff hε, ← toV2_ptOf V z ε] at hzs hzt
  have h1 := mem_interior_of_inInt hs hds hzs
  have h2 := mem_interior_of_inInt ht hdt hzt
  have hne : s.1 ≠ t.1 := fun h => hst (Subtype.ext h)
  exact Set.disjoint_left.mp (D.interiors_disjoint hne) h1 h2
theorem tiles_cover (D : RegionDissection N) (V : Plane) (p q : AtV D V → V2)
    (hloc : ∀ s : AtV D V, LocalCone (D.tile s.1) V (p s) (q s))
    (Tgt : Set V2) (R : ℝ) (hR : 0 < R)
    (hT : ∀ y : Plane, dist y V < R → (y ∈ D.region ↔ toV2 (y - V) ∈ Tgt))
    (hTs : ∀ z ∈ Tgt, ∀ t : ℝ, 0 < t → ((t * z.1, t * z.2) : V2) ∈ Tgt) :
    ∀ z ∈ Tgt, ∃ s : AtV D V, inCone (p s) (q s) z := by
  intro z hz
  obtain ⟨r, hr, hiff, hout⟩ := common_radius D V p q hloc
  obtain ⟨ε, hε, hd⟩ := exists_ptOf_small V z (lt_min hr hR)
  have hd1 : dist (ptOf V z ε) V < r := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : dist (ptOf V z ε) V < R := lt_of_lt_of_le hd (min_le_right _ _)
  have hy : ptOf V z ε ∈ D.region := by
    rw [hT _ hd2, toV2_ptOf]; exact hTs z hz ε hε
  rw [← D.covers] at hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
  have hVi : V ∈ (D.tile i).carrier := by
    by_contra hnot
    exact hout i hnot _ hd1 hi
  refine ⟨⟨i, hVi⟩, ?_⟩
  have := (hiff ⟨i, hVi⟩ _ hd1).mp hi
  rw [toV2_ptOf] at this
  exact (inCone_smul_iff hε).mp this
theorem tiles_angle_sum (D : RegionDissection N) (V : Plane) (p q : AtV D V → V2)
    (hwd : ∀ s : AtV D V, wd (p s) (q s) = (D.tile s.1).localAngle V) :
    ∑ s : AtV D V, wd (p s) (q s) = ∑ i, (D.tile i).localAngle V := by
  classical
  simp only [hwd]
  have h1 := Finset.sum_subtype (Finset.univ.filter fun i : Fin N => V ∈ (D.tile i).carrier)
    (p := fun i => V ∈ (D.tile i).carrier) (F := (inferInstance : Fintype (AtV D V))) (by simp) (fun i => (D.tile i).localAngle V)
  have h2 : ∑ s : AtV D V, (D.tile s.1).localAngle V
      = ∑ i ∈ Finset.univ.filter (fun i : Fin N => V ∈ (D.tile i).carrier), (D.tile i).localAngle V := h1.symm
  rw [h2]
  apply Finset.sum_filter_of_ne
  intro i _ hne
  by_contra hmem
  exact hne (Tri.localAngle_eq_zero_of_not_mem _ hmem)
theorem aedisjoint (D : RegionDissection N) {i j : Fin N} (hij : i ≠ j) :
    AEDisjoint volume (D.tile i).carrier (D.tile j).carrier := by
  have hsub : (D.tile i).carrier ∩ (D.tile j).carrier ⊆
      frontier (D.tile i).carrier ∪ frontier (D.tile j).carrier := by
    rintro x ⟨hxi, hxj⟩
    by_cases h1 : x ∈ interior (D.tile i).carrier
    · by_cases h2 : x ∈ interior (D.tile j).carrier
      · exact absurd h2 (Set.disjoint_left.mp (D.interiors_disjoint hij) h1)
      · exact Or.inr ⟨subset_closure hxj, h2⟩
    · exact Or.inl ⟨subset_closure hxi, h1⟩
  exact measure_mono_null hsub (measure_union_null (D.tile i).volume_frontier (D.tile j).volume_frontier)
theorem volume_inter_ball_eq_sum (D : RegionDissection N) (x : Plane) (r : ℝ) :
    volume (D.region ∩ Metric.ball x r) = ∑ i, volume ((D.tile i).carrier ∩ Metric.ball x r) := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => (D.tile i).carrier ∩ Metric.ball x r)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) (aedisjoint D hij))
    (fun i _ => ((D.tile i).nullMeasurableSet).inter
      Metric.isOpen_ball.measurableSet.nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), ((D.tile i).carrier ∩ Metric.ball x r))
          = D.region ∩ Metric.ball x r := by
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [← Set.iUnion_inter, D.covers]
  rw [hU] at h
  exact h
theorem sum_localAngle_of_vol (D : RegionDissection N) (hN : 0 < N) (V : Plane) (θ : ℝ) (hθ : 0 ≤ θ) (ρ : ℝ) (hρ : 0 < ρ)
    (hvol : ∀ r, 0 < r → r ≤ ρ → volume (D.region ∩ Metric.ball V r) = ENNReal.ofReal (θ / 2 * r ^ 2)) :
    ∑ i, (D.tile i).localAngle V = θ := by
  classical
  choose ri hri hcontrib using fun i => (D.tile i).volume_inter_ball_localAngle V
  obtain ⟨r0, hr0, hr0le⟩ := exists_common_radius hN ri hri
  set r : ℝ := min ρ r0 with hrdef
  have hrpos : 0 < r := lt_min hρ hr0
  have hsum := volume_inter_ball_eq_sum D V r
  rw [hvol r hrpos (min_le_left _ _)] at hsum
  have htiles : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      volume ((D.tile i).carrier ∩ Metric.ball V r)
        = ENNReal.ofReal ((D.tile i).localAngle V / 2 * r ^ 2) := fun i _ =>
    hcontrib i r hrpos ((min_le_right _ _).trans (hr0le i))
  rw [Finset.sum_congr rfl htiles,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      have := (D.tile i).localAngle_nonneg V
      positivity)] at hsum
  have hreal := (ENNReal.ofReal_eq_ofReal_iff
    (by positivity)
    (Finset.sum_nonneg fun i _ => by
      have := (D.tile i).localAngle_nonneg V
      positivity)).mp hsum
  have hfact : ∑ i, (D.tile i).localAngle V / 2 * r ^ 2
      = (∑ i, (D.tile i).localAngle V) * (r ^ 2 / 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfact] at hreal
  have hr2 : (0:ℝ) < r ^ 2 / 2 := by positivity
  have hkey : (∑ i, (D.tile i).localAngle V) * (r ^ 2 / 2) = θ * (r ^ 2 / 2) := by
    rw [← hreal]; ring
  exact mul_right_cancel₀ hr2.ne' hkey
theorem sum_localAngle_interior (D : RegionDissection N) (hN : 0 < N) {V : Plane} (hV : V ∈ interior D.region) :
    ∑ i, (D.tile i).localAngle V = 2 * Real.pi := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior V hV
  refine sum_localAngle_of_vol D hN V (2 * Real.pi) (by positivity) ρ hρ (fun r hr hrρ => ?_)
  have : D.region ∩ Metric.ball V r = Metric.ball V r := by
    apply Set.inter_eq_right.mpr
    intro y hy
    exact interior_subset (hball (Metric.ball_subset_ball hrρ hy))
  rw [this, volume_ball_plane V hr.le]
  congr 1; ring
theorem sum_localAngle_tri (D : RegionDissection N) (hN : 0 < N) {V : Plane} (T : Tri) {ρ : ℝ} (hρ : 0 < ρ)
    (hiff : ∀ y, dist y V < ρ → (y ∈ D.region ↔ y ∈ T.carrier)) :
    ∑ i, (D.tile i).localAngle V = T.localAngle V := by
  obtain ⟨rT, hrT, hT⟩ := T.volume_inter_ball_localAngle V
  refine sum_localAngle_of_vol D hN V (T.localAngle V) (T.localAngle_nonneg V) (min ρ rT) (lt_min hρ hrT) (fun r hr hrle => ?_)
  have : D.region ∩ Metric.ball V r = T.carrier ∩ Metric.ball V r := by
    ext y
    simp only [Set.mem_inter_iff, Metric.mem_ball]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hiff y (lt_of_lt_of_le h2 (hrle.trans (min_le_left _ _)))).mp h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hiff y (lt_of_lt_of_le h2 (hrle.trans (min_le_left _ _)))).mpr h1, h2⟩
  rw [this]
  exact hT r hr (hrle.trans (min_le_right _ _))
end Erdos634.Draft.LaczFormal.RG
end

section
open MeasureTheory Erdos634.Geometry Erdos634.AreaDet Erdos634.RegionDissection Erdos634.TilePlacement
open scoped ENNReal
namespace Erdos634.Draft.LaczFormal.Thm21
def cross2 (u w : Plane) : ℝ := u 0 * w 1 - u 1 * w 0
theorem sin_angleAt_pos (T : Tri) (j : Fin 3) : 0 < Real.sin (angleAt T j) :=
  Real.sin_pos_of_pos_of_lt_pi (MarchFlank.cornerAngle_pos T j) (Erdos634.RouteOneVertexKill.cornerAngle_lt_pi T j)
end Erdos634.Draft.LaczFormal.Thm21
end

section
open MeasureTheory Erdos634.Geometry Erdos634.AreaDet Erdos634.RegionDissection Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.Thm21
structure ConvPoly (M : ℕ) [NeZero M] where
  v : Fin M → Plane
  three_le : 3 ≤ M
  left : ∀ i j : Fin M, j ≠ i → j ≠ i + 1 → 0 < cross2 (v (i + 1) - v i) (v j - v i)
namespace ConvPoly
variable {M : ℕ} [NeZero M] (P : ConvPoly M)
def carrier : Set Plane := {x | ∀ i : Fin M, 0 ≤ cross2 (P.v (i + 1) - P.v i) (x - P.v i)}
noncomputable def side (i : Fin M) : ℝ := dist (P.v i) (P.v (i + 1))
noncomputable def angle (i : Fin M) : ℝ := cornerAngle (P.v (i - 1)) (P.v i) (P.v (i + 1))
end ConvPoly
def Comm (x y : ℝ) : Prop := ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℝ) * x = q * y
structure PolyTiling (N M : ℕ) [NeZero M] where
  C : CongruentRegionDissection N
  P : ConvPoly M
  region_eq : C.region = P.carrier
noncomputable def cntR {N : ℕ} (C : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (X : Plane) (l : Fin 3) : ℕ :=
  open Classical in (Finset.univ.filter (fun p : Fin N × Fin 3 => (C.tile p.1).pts p.2 = X ∧ idx p.1 p.2 = l)).card
def RegularPQ {N : ℕ} (C : CongruentRegionDissection N) : Prop :=
  ∃ idx : Fin N → Equiv.Perm (Fin 3), (∀ i v, angleAt C.model (idx i v) = angleAt (C.tile i) v) ∧
    ∀ X, cntR C idx X 0 = cntR C idx X 1
theorem cross2_add_right (a b c : Plane) : cross2 a (b + c) = cross2 a b + cross2 a c := by unfold cross2; simp; ring
theorem cross2_smul_left (r : ℝ) (a b : Plane) : cross2 (r • a) b = r * cross2 a b := by unfold cross2; simp; ring
theorem cross2_smul_right (r : ℝ) (a b : Plane) : cross2 a (r • b) = r * cross2 a b := by unfold cross2; simp; ring
theorem cross2_self (a : Plane) : cross2 a a = 0 := by unfold cross2; ring
end Erdos634.Draft.LaczFormal.Thm21
end

section
open MeasureTheory Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal.Thm21
theorem fin_val_two {M : ℕ} [NeZero M] : ((2 : Fin M) : ℕ) = 2 % M := rfl
theorem fin_val_one {M : ℕ} [NeZero M] : ((1 : Fin M) : ℕ) = 1 % M := rfl
theorem fin_val_zero {M : ℕ} [NeZero M] : ((0 : Fin M) : ℕ) = 0 := rfl
theorem fin_one_ne_zero' {M : ℕ} [NeZero M] (h : 2 ≤ M) : (1 : Fin M) ≠ 0 := by
  intro h1
  have := congrArg Fin.val h1
  rw [fin_val_one, fin_val_zero, Nat.mod_eq_of_lt (by omega : 1 < M)] at this
  omega
theorem fin_two_ne_zero' {M : ℕ} [NeZero M] (h : 3 ≤ M) : (2 : Fin M) ≠ 0 := by
  intro h1
  have := congrArg Fin.val h1
  rw [fin_val_two, fin_val_zero, Nat.mod_eq_of_lt (by omega : 2 < M)] at this
  omega
theorem fin_two_ne_one' {M : ℕ} [NeZero M] (h : 3 ≤ M) : (2 : Fin M) ≠ 1 := by
  intro h1
  have := congrArg Fin.val h1
  rw [fin_val_two, fin_val_one, Nat.mod_eq_of_lt (by omega : 1 < M), Nat.mod_eq_of_lt (by omega : 2 < M)] at this
  omega
theorem fin_one_add_one {M : ℕ} [NeZero M] : (1 + 1 : Fin M) = 2 := by
  rw [Fin.ext_iff, Fin.val_add, fin_val_one, fin_val_two]
  exact (Nat.add_mod 1 1 M).symm
namespace ConvPoly
variable {M : ℕ} [NeZero M] (P : ConvPoly M)
def e (i : Fin M) : Plane := P.v (i + 1) - P.v i
def c (i : Fin M) (x : Plane) : ℝ := cross2 (P.e i) (x - P.v i)
theorem c_vertex_pos {j m : Fin M} (h1 : m ≠ j) (h2 : m ≠ j + 1) : 0 < P.c j (P.v m) := P.left j m h1 h2
theorem c_self (j : Fin M) : P.c j (P.v j) = 0 := by simp [c, cross2]
theorem c_next (j : Fin M) : P.c j (P.v (j + 1)) = 0 := by
  simp [c, e, cross2]; ring
theorem c_comb (j : Fin M) (A B : Plane) (t : ℝ) : P.c j ((1 - t) • A + t • B) = (1 - t) * P.c j A + t * P.c j B := by
  unfold c cross2; simp; ring
theorem fin_facts (hM : 3 ≤ M) (i : Fin M) : i + 1 ≠ i ∧ i + 2 ≠ i ∧ i + 2 ≠ i + 1 ∧ i + 1 ≠ i - 1 ∧ i - 1 + 1 = i ∧ i + 1 + 1 = i + 2 := by
  have h1 : (1 : Fin M) ≠ 0 := fin_one_ne_zero' (by omega)
  have h2 : (2 : Fin M) ≠ 0 := fin_two_ne_zero' hM
  have h21 : (2 : Fin M) ≠ 1 := fin_two_ne_one' hM
  refine ⟨fun h => h1 (by simpa using h), fun h => h2 (by simpa using h), fun h => ?_, fun h => ?_, sub_add_cancel i 1, (add_assoc i 1 1).trans (by rw [fin_one_add_one])⟩
  · apply h21
    have : i + 2 = i + 1 := h
    exact add_left_cancel this
  · apply h2
    have : i + 1 = i - 1 := h
    have h3 : (i + 1) - (i - 1) = 1 + 1 := by abel
    rw [fin_one_add_one] at h3
    rw [← h3, this]; simp
end ConvPoly
theorem affineIndependent_of_cross (a b c : Plane) (h : cross2 (b - a) (c - a) ≠ 0) : AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_not_collinear_of_ne (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide)]
  intro hc
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hc
  obtain ⟨q, v, hv⟩ := hc
  obtain ⟨ra, ha⟩ := hv a (by simp)
  obtain ⟨rb, hb⟩ := hv b (by simp)
  obtain ⟨rc, hc⟩ := hv c (by simp)
  apply h
  have e1 : b - a = (rb - ra) • v := by rw [hb, ha]; simp [sub_smul]
  have e2 : c - a = (rc - ra) • v := by rw [hc, ha]; simp [sub_smul]
  rw [e1, e2, cross2_smul_left, cross2_smul_right, cross2_self]; ring
noncomputable def triOf (a b c : Plane) (h : 0 < cross2 (b - a) (c - a)) : Tri where
  pts := ![a, b, c]
  indep := affineIndependent_of_cross a b c h.ne'
theorem halfplane_convex (u w : Plane) : Convex ℝ {z : Plane | 0 ≤ cross2 u (z - w)} := by
  intro z1 hz1 z2 hz2 a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  have : cross2 u (a • z1 + b • z2 - w) = a * cross2 u (z1 - w) + b * cross2 u (z2 - w) := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    unfold cross2; simp; ring
  rw [this]; positivity
theorem triOf_carrier (a b c : Plane) (h : 0 < cross2 (b - a) (c - a)) (y : Plane) :
    y ∈ (triOf a b c h).carrier ↔
      0 ≤ cross2 (b - a) (y - a) ∧ 0 ≤ cross2 (c - b) (y - b) ∧ 0 ≤ cross2 (a - c) (y - c) := by
  constructor
  · intro hy
    have hhull : (triOf a b c h).carrier ⊆ {z | 0 ≤ cross2 (b - a) (z - a)} ∩ {z | 0 ≤ cross2 (c - b) (z - b)} ∩ {z | 0 ≤ cross2 (a - c) (z - c)} := by
      apply convexHull_min
      · rintro _ ⟨k, rfl⟩
        fin_cases k
        · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [triOf, cross2] <;> unfold cross2 at h <;> simp at h <;> nlinarith
        · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [triOf, cross2] <;> unfold cross2 at h <;> simp at h <;> nlinarith
        · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [triOf, cross2] <;> unfold cross2 at h <;> simp at h <;> nlinarith
      · exact ((halfplane_convex _ _).inter (halfplane_convex _ _)).inter (halfplane_convex _ _)
    exact ⟨(hhull hy).1.1, (hhull hy).1.2, (hhull hy).2⟩
  · rintro ⟨k1, k2, k3⟩
    set Ori := cross2 (b - a) (c - a) with hOri
    refine Erdos634.CertGeom.mem_carrier_of_combo (triOf a b c h) y
      ![cross2 (c - b) (y - b) / Ori, cross2 (a - c) (y - c) / Ori, cross2 (b - a) (y - a) / Ori] ?_ ?_ ?_
    · show _ / Ori + _ / Ori + _ / Ori = 1
      rw [← add_div, ← add_div, div_eq_one_iff_eq h.ne']
      rw [hOri]; unfold cross2; simp; ring
    · intro k; fin_cases k
      · exact div_nonneg k2 h.le
      · exact div_nonneg k3 h.le
      · exact div_nonneg k1 h.le
    · show y = _ • a + _ • b + _ • c
      have hOne : Ori ≠ 0 := h.ne'
      ext j; fin_cases j
      · show y 0 = _ / Ori * a 0 + _ / Ori * b 0 + _ / Ori * c 0
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div, eq_div_iff hOne, hOri]
        unfold cross2; simp; ring
      · show y 1 = _ / Ori * a 1 + _ / Ori * b 1 + _ / Ori * c 1
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div, eq_div_iff hOne, hOri]
        unfold cross2; simp; ring
namespace ConvPoly
variable {M : ℕ} [NeZero M] (P : ConvPoly M)
theorem e_ne_zero (hM : 3 ≤ M) (i : Fin M) : P.e i ≠ 0 := by
  obtain ⟨-, h2, h3, -⟩ := fin_facts hM i
  intro h
  have := P.c_vertex_pos (j := i) (m := i + 2) h2 h3
  unfold c at this
  rw [h] at this
  simp [cross2] at this
theorem c_prev_next (hM : 3 ≤ M) (i : Fin M) : P.c (i - 1) (P.v i) = 0 := by
  have := P.c_next (i - 1)
  rwa [(fin_facts hM i).2.2.2.2.1] at this
theorem edge_param (hM : 3 ≤ M) {i : Fin M} {V : Plane} (hV : V ∈ P.carrier) (h0 : P.c i V = 0) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, V = (1 - t) • P.v i + t • P.v (i + 1) := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ := fin_facts hM i
  have hE := P.e_ne_zero hM i
  have hn : P.e i 0 ^ 2 + P.e i 1 ^ 2 ≠ 0 := by
    intro h
    apply hE
    have h0' : P.e i 0 = 0 := by nlinarith [sq_nonneg (P.e i 0), sq_nonneg (P.e i 1)]
    have h1' : P.e i 1 = 0 := by nlinarith [sq_nonneg (P.e i 0), sq_nonneg (P.e i 1)]
    ext j; fin_cases j <;> simp [h0', h1']
  have hcr : P.e i 0 * (V - P.v i) 1 - P.e i 1 * (V - P.v i) 0 = 0 := h0
  set t := ((V - P.v i) 0 * P.e i 0 + (V - P.v i) 1 * P.e i 1) / (P.e i 0 ^ 2 + P.e i 1 ^ 2) with ht
  have hW : V = (1 - t) • P.v i + t • P.v (i + 1) := by
    have hv1 : P.v (i + 1) = P.v i + P.e i := by unfold e; abel
    rw [hv1]
    ext j; fin_cases j
    · show V 0 = (1 - t) * P.v i 0 + t * (P.v i 0 + P.e i 0)
      have : t * P.e i 0 = (V - P.v i) 0 := by
        rw [ht, div_mul_eq_mul_div, div_eq_iff hn]
        simp only [PiLp.sub_apply] at hcr ⊢
        linear_combination (P.e i 1) * hcr
      simp only [PiLp.sub_apply] at this
      linarith
    · show V 1 = (1 - t) * P.v i 1 + t * (P.v i 1 + P.e i 1)
      have : t * P.e i 1 = (V - P.v i) 1 := by
        rw [ht, div_mul_eq_mul_div, div_eq_iff hn]
        simp only [PiLp.sub_apply] at hcr ⊢
        linear_combination (-(P.e i 0)) * hcr
      simp only [PiLp.sub_apply] at this
      linarith
  refine ⟨t, ⟨?_, ?_⟩, hW⟩
  · by_contra hneg
    replace hneg := not_le.mp hneg
    have h1 : 0 ≤ P.c (i - 1) V := hV (i - 1)
    rw [hW, c_comb, P.c_prev_next hM i] at h1
    have h2 := P.c_vertex_pos (j := i - 1) (m := i + 1) hf4 (by rw [hf5]; exact hf1)
    nlinarith
  · by_contra hneg
    replace hneg := not_le.mp hneg
    have h1 : 0 ≤ P.c (i + 1) V := hV (i + 1)
    rw [hW, c_comb, P.c_self] at h1
    have h2 := P.c_vertex_pos (j := i + 1) (m := i) (Ne.symm hf1) (by rw [hf6]; exact Ne.symm hf2)
    nlinarith
theorem c_edge_pos (hM : 3 ≤ M) (i : Fin M) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) {j : Fin M} (hj : j ≠ i)
    (h1 : j = i + 1 → t < 1) (h2 : j = i - 1 → 0 < t) : 0 < P.c j ((1 - t) • P.v i + t • P.v (i + 1)) := by
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ := fin_facts hM i
  rw [c_comb]
  by_cases hA : j = i + 1
  · subst hA
    have hlt := h1 rfl
    have h := P.c_vertex_pos (j := i + 1) (m := i) (Ne.symm hf1) (by rw [hf6]; exact Ne.symm hf2)
    rw [P.c_self]
    nlinarith
  by_cases hB : j = i - 1
  · subst hB
    have hlt := h2 rfl
    have h := P.c_vertex_pos (j := i - 1) (m := i + 1) hf4 (by rw [hf5]; exact hf1)
    rw [P.c_prev_next hM i]
    nlinarith [ht.1]
  have hA1 : P.c j (P.v i) > 0 := P.c_vertex_pos (Ne.symm hj) (fun h => hB (eq_sub_of_add_eq h.symm))
  have hA2 : P.c j (P.v (i + 1)) > 0 := P.c_vertex_pos (Ne.symm hA) (fun h => hj (add_right_cancel h).symm)
  by_cases hh : t ≤ 1 / 2
  · nlinarith [mul_nonneg (sub_nonneg.2 hh) hA1.le, mul_nonneg ht.1 hA2.le]
  · have hh' := not_le.mp hh
    nlinarith [mul_nonneg (sub_nonneg.2 ht.2) hA1.le, mul_pos (by linarith : (0:ℝ) < t) hA2]
theorem continuous_c (j : Fin M) : Continuous (P.c j) := by
  unfold c cross2; fun_prop
theorem ori_pos (hM : 3 ≤ M) (k : Fin M) : 0 < cross2 (P.v (k + 1) - P.v k) (P.v (k + 2) - P.v k) := by
  obtain ⟨-, h2, h3, -⟩ := fin_facts hM k
  exact P.c_vertex_pos (j := k) (m := k + 2) h2 h3
noncomputable def locTri (hM : 3 ≤ M) (k : Fin M) : Tri := triOf (P.v k) (P.v (k + 1)) (P.v (k + 2)) (P.ori_pos hM k)
def chord (k : Fin M) (y : Plane) : ℝ := cross2 (P.v k - P.v (k + 2)) (y - P.v (k + 2))
theorem continuous_chord (k : Fin M) : Continuous (P.chord k) := by
  unfold chord cross2; fun_prop
theorem locTri_carrier (hM : 3 ≤ M) (k : Fin M) (y : Plane) :
    y ∈ (P.locTri hM k).carrier ↔ 0 ≤ P.c k y ∧ 0 ≤ P.c (k + 1) y ∧ 0 ≤ P.chord k y := by
  have h6 := (fin_facts hM k).2.2.2.2.2
  unfold locTri
  rw [triOf_carrier]
  unfold c chord e
  rw [h6]
theorem chord_vertex (hM : 3 ≤ M) (k : Fin M) : P.chord k (P.v (k + 1)) = cross2 (P.v (k + 1) - P.v k) (P.v (k + 2) - P.v k) := by
  unfold chord cross2; simp; ring
theorem chord_self (k : Fin M) : P.chord k (P.v k) = 0 := by
  unfold chord cross2; simp; ring
theorem chord_comb (k : Fin M) (A B : Plane) (t : ℝ) : P.chord k ((1 - t) • A + t • B) = (1 - t) * P.chord k A + t * P.chord k B := by
  unfold chord cross2; simp; ring
theorem local_equiv (hM : 3 ≤ M) (k : Fin M) {V : Plane} (hstrict : ∀ j, j ≠ k → j ≠ k + 1 → 0 < P.c j V)
    (hch : 0 < P.chord k V) :
    ∃ ρ > 0, ∀ y, dist y V < ρ → (y ∈ P.carrier ↔ y ∈ (P.locTri hM k).carrier) := by
  have hev : ∀ᶠ y in nhds V, (∀ j, j ≠ k → j ≠ k + 1 → 0 < P.c j y) ∧ 0 < P.chord k y := by
    refine Filter.Eventually.and ?_ ?_
    · refine Filter.eventually_all.2 fun j => ?_
      by_cases h1 : j = k
      · exact Filter.Eventually.of_forall (fun y hy => absurd h1 hy)
      by_cases h2 : j = k + 1
      · exact Filter.Eventually.of_forall (fun y _ hy => absurd h2 hy)
      exact ((P.continuous_c j).continuousAt.eventually (lt_mem_nhds (hstrict j h1 h2))).mono (fun y hy _ _ => hy)
    · exact (P.continuous_chord k).continuousAt.eventually (lt_mem_nhds hch)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ρ, hρ, fun y hy => ?_⟩
  obtain ⟨hs, hc⟩ := hball hy
  rw [locTri_carrier]
  constructor
  · intro hyP
    exact ⟨hyP k, hyP (k + 1), hc.le⟩
  · rintro ⟨h1, h2, -⟩ j
    by_cases hjk : j = k
    · subst hjk; exact h1
    by_cases hjk1 : j = k + 1
    · subst hjk1; exact h2
    exact (hs j hjk hjk1).le
theorem interior_of_pos {V : Plane} (h : ∀ j, 0 < P.c j V) : V ∈ interior P.carrier := by
  have hopen : IsOpen {y : Plane | ∀ j, 0 < P.c j y} := by
    have : {y : Plane | ∀ j, 0 < P.c j y} = ⋂ j, {y : Plane | 0 < P.c j y} := by ext y; simp
    rw [this]
    exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (P.continuous_c j)
  have hsub : {y : Plane | ∀ j, 0 < P.c j y} ⊆ P.carrier := fun y hy j => (hy j).le
  exact interior_maximal hsub hopen h
theorem vertex_local' (hM : 3 ≤ M) (k : Fin M) :
    ∃ T : Tri, P.v (k + 1) ∈ T.carrier ∧ ∃ ρ > 0, ∀ y, dist y (P.v (k + 1)) < ρ → (y ∈ P.carrier ↔ y ∈ T.carrier) := by
  obtain ⟨hf1, -⟩ := fin_facts hM k
  have hstrict : ∀ j, j ≠ k → j ≠ k + 1 → 0 < P.c j (P.v (k + 1)) := by
    intro j h1 h2
    exact P.c_vertex_pos (Ne.symm h2) (fun h => h1 (add_right_cancel h).symm)
  have hch : 0 < P.chord k (P.v (k + 1)) := by
    rw [P.chord_vertex hM k]; exact P.ori_pos hM k
  obtain ⟨ρ, hρ, hiff⟩ := P.local_equiv hM k hstrict hch
  refine ⟨P.locTri hM k, ?_, ρ, hρ, hiff⟩
  rw [locTri_carrier]
  exact ⟨(P.c_next k).ge, (P.c_self (k + 1)).ge, hch.le⟩
theorem vertex_local (hM : 3 ≤ M) (m : Fin M) :
    ∃ T : Tri, P.v m ∈ T.carrier ∧ ∃ ρ > 0, ∀ y, dist y (P.v m) < ρ → (y ∈ P.carrier ↔ y ∈ T.carrier) := by
  have hm : m - 1 + 1 = m := (fin_facts hM m).2.2.2.2.1
  have := P.vertex_local' hM (m - 1)
  rwa [hm] at this
theorem open_edge_local (hM : 3 ≤ M) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ T : Tri, (1 - t) • P.v i + t • P.v (i + 1) ∈ T.carrier ∧ ∃ ρ > 0, ∀ y, dist y ((1 - t) • P.v i + t • P.v (i + 1)) < ρ →
      (y ∈ P.carrier ↔ y ∈ T.carrier) := by
  have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0.le, ht1.le⟩
  have hstrict : ∀ j, j ≠ i → j ≠ i + 1 → 0 < P.c j ((1 - t) • P.v i + t • P.v (i + 1)) := by
    intro j h1 h2
    exact P.c_edge_pos hM i htI h1 (fun h => absurd h h2) (fun _ => ht0)
  have hch : 0 < P.chord i ((1 - t) • P.v i + t • P.v (i + 1)) := by
    rw [P.chord_comb, P.chord_self, P.chord_vertex hM i]
    have := P.ori_pos hM i
    nlinarith
  obtain ⟨ρ, hρ, hiff⟩ := P.local_equiv hM i hstrict hch
  refine ⟨P.locTri hM i, ?_, ρ, hρ, hiff⟩
  rw [locTri_carrier]
  refine ⟨?_, ?_, hch.le⟩
  · rw [P.c_comb, P.c_self, P.c_next]; simp
  · exact (P.c_edge_pos hM i htI (fin_facts hM i).1 (fun _ => ht1) (fun _ => ht0)).le
theorem vertex_local_T (hM : 3 ≤ M) (k : Fin M) :
    ∃ ρ > 0, ∀ y, dist y (P.v (k + 1)) < ρ → (y ∈ P.carrier ↔ y ∈ (P.locTri hM k).carrier) := by
  have hstrict : ∀ j, j ≠ k → j ≠ k + 1 → 0 < P.c j (P.v (k + 1)) := by
    intro j h1 h2
    exact P.c_vertex_pos (Ne.symm h2) (fun h => h1 (add_right_cancel h).symm)
  have hch : 0 < P.chord k (P.v (k + 1)) := by
    rw [P.chord_vertex hM k]; exact P.ori_pos hM k
  exact P.local_equiv hM k hstrict hch
theorem open_edge_local_T (hM : 3 ≤ M) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ ρ > 0, ∀ y, dist y ((1 - t) • P.v i + t • P.v (i + 1)) < ρ → (y ∈ P.carrier ↔ y ∈ (P.locTri hM i).carrier) := by
  have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0.le, ht1.le⟩
  have hstrict : ∀ j, j ≠ i → j ≠ i + 1 → 0 < P.c j ((1 - t) • P.v i + t • P.v (i + 1)) := by
    intro j h1 h2
    exact P.c_edge_pos hM i htI h1 (fun h => absurd h h2) (fun _ => ht0)
  have hch : 0 < P.chord i ((1 - t) • P.v i + t • P.v (i + 1)) := by
    rw [P.chord_comb, P.chord_self, P.chord_vertex hM i]
    have := P.ori_pos hM i
    nlinarith
  exact P.local_equiv hM i hstrict hch
theorem polygon_local (hM : 3 ≤ M) {V : Plane} (hV : V ∈ P.carrier) :
    V ∈ interior P.carrier ∨
      ∃ T : Tri, V ∈ T.carrier ∧ ∃ ρ > 0, ∀ y, dist y V < ρ → (y ∈ P.carrier ↔ y ∈ T.carrier) := by
  by_cases hpos : ∀ j, 0 < P.c j V
  · exact Or.inl (P.interior_of_pos hpos)
  right
  push Not at hpos
  obtain ⟨i, hi⟩ := hpos
  have h0 : P.c i V = 0 := le_antisymm hi (hV i)
  obtain ⟨t, ⟨ht0, ht1⟩, hVt⟩ := P.edge_param hM hV h0
  rcases ht0.eq_or_lt with h | h
  · subst hVt
    rw [← h] at *
    have := P.vertex_local hM i
    simpa using this
  rcases ht1.eq_or_lt with h' | h'
  · rw [hVt, h']
    have := P.vertex_local hM (i + 1)
    simpa using this
  · rw [hVt]; exact P.open_edge_local hM i h h'
end ConvPoly
end Erdos634.Draft.LaczFormal.Thm21
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
structure ExtFan (D : RegionDissection N) (V : Plane) (κ : Type) [Fintype κ] where
  Tgt : Set V2
  R : ℝ
  hR : 0 < R
  hT : ∀ y : Plane, dist y V < R → (y ∈ D.region ↔ toV2 (y - V) ∈ Tgt)
  hTs : ∀ z ∈ Tgt, ∀ t : ℝ, 0 < t → ((t * z.1, t * z.2) : V2) ∈ Tgt
  hTc : ∀ x ∈ Tgt, ∀ y ∈ Tgt, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    ((a * x.1 + b * y.1, a * x.2 + b * y.2) : V2) ∈ Tgt
  pe : κ → V2
  qe : κ → V2
  hokE : ∀ j, SecOK (pe j) (qe j)
  hextT : ∀ j z, inInt (pe j) (qe j) z → z ∉ Tgt
  hdisjE : ∀ j j', j ≠ j' → ∀ z, ¬ (inInt (pe j) (qe j) z ∧ inInt (pe j') (qe j') z)
  p : AtV D V → V2
  q : AtV D V → V2
  e : ℕ → AtV D V ⊕ κ
  hok : ∀ s, SecOK (p s) (q s)
  hloc : ∀ s, LocalCone (D.tile s.1) V (p s) (q s)
  hwd : ∀ s, wd (p s) (q s) = (D.tile s.1).localAngle V
  hsum : ∑ s, wd (p s) (q s) + ∑ j, wd (pe j) (qe j) = 2 * Real.pi
  hspec : ∀ s, SectorSpec (D.tile s.1) V (p s) (q s)
  hP : ∀ n, Par (Sum.elim p pe (e (n + 1))) (Sum.elim q qe (e n))
  hper : ∀ n, e (n + Fintype.card (AtV D V ⊕ κ)) = e n
  hinj : Set.InjOn e (Set.Iio (Fintype.card (AtV D V ⊕ κ)))
  hsurj : ∀ o, ∃ j < Fintype.card (AtV D V ⊕ κ), e j = o
theorem vertex_fan_ext (D : RegionDissection N) (V : Plane) (hvert : ∃ i k, (D.tile i).pts k = V)
    (Tgt : Set V2) (R : ℝ) (hR : 0 < R)
    (hT : ∀ y : Plane, dist y V < R → (y ∈ D.region ↔ toV2 (y - V) ∈ Tgt))
    (hTs : ∀ z ∈ Tgt, ∀ t : ℝ, 0 < t → ((t * z.1, t * z.2) : V2) ∈ Tgt)
    {κ : Type} [Fintype κ] (pe qe : κ → V2)
    (hokE : ∀ j, SecOK (pe j) (qe j))
    (hcovE : ∀ z : V2, z ∉ Tgt → ∃ j, inCone (pe j) (qe j) z)
    (hdisjE : ∀ j j', j ≠ j' → ∀ z, ¬ (inInt (pe j) (qe j) z ∧ inInt (pe j') (qe j') z))
    (hextT : ∀ j z, inInt (pe j) (qe j) z → z ∉ Tgt)
    (hangle : ∑ i, (D.tile i).localAngle V + ∑ j, wd (pe j) (qe j) = 2 * Real.pi) :
    ∃ (p q : AtV D V → V2) (e : ℕ → AtV D V ⊕ κ),
      (∀ s, SecOK (p s) (q s)) ∧ (∀ s, LocalCone (D.tile s.1) V (p s) (q s)) ∧
      (∀ s, wd (p s) (q s) = (D.tile s.1).localAngle V) ∧ (∀ s, SectorSpec (D.tile s.1) V (p s) (q s)) ∧
      (∀ n, Par (Sum.elim p pe (e (n + 1))) (Sum.elim q qe (e n))) ∧
      (∀ n, e (n + Fintype.card (AtV D V ⊕ κ)) = e n) ∧
      Set.InjOn e (Set.Iio (Fintype.card (AtV D V ⊕ κ))) ∧
      (∀ o, ∃ j < Fintype.card (AtV D V ⊕ κ), e j = o) := by
  classical
  have hex : ∀ s : AtV D V, ∃ pq : V2 × V2, SecOK pq.1 pq.2 ∧ LocalCone (D.tile s.1) V pq.1 pq.2 ∧
      wd pq.1 pq.2 = (D.tile s.1).localAngle V ∧ SectorSpec (D.tile s.1) V pq.1 pq.2 := by
    intro s
    obtain ⟨p, q, h1, h2, h3, h4⟩ := local_sector (D.tile s.1) s.2 (not_interior_of_vertex D hvert s.1)
    exact ⟨(p, q), h1, h2, h3, h4⟩
  choose pq hok hloc hwd hspec using hex
  set p : AtV D V → V2 := fun s => (pq s).1
  set q : AtV D V → V2 := fun s => (pq s).2
  obtain ⟨i0, k0, hk0⟩ := hvert
  haveI : Nonempty (AtV D V) := ⟨⟨i0, hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩⟩⟩
  haveI : Nonempty (AtV D V ⊕ κ) := ⟨Sum.inl (Classical.arbitrary _)⟩
  have hok' : AllOK (Sum.elim p pe) (Sum.elim q qe) := by
    intro o; rcases o with s | j
    · exact hok s
    · exact hokE j
  have hcov : Covers (Sum.elim p pe) (Sum.elim q qe) := by
    intro z
    by_cases hz : z ∈ Tgt
    · obtain ⟨s, hs⟩ := tiles_cover D V p q hloc Tgt R hR hT hTs z hz
      exact ⟨Sum.inl s, hs⟩
    · obtain ⟨j, hj⟩ := hcovE z hz
      exact ⟨Sum.inr j, hj⟩
  have hext : ∀ (t : AtV D V) (j : κ) (z : V2), inInt (pe j) (qe j) z → inInt (p t) (q t) z → False := by
    intro t j z hz1 hz2
    obtain ⟨rt, hrt, ht⟩ := hloc t
    obtain ⟨ε, hε, hd⟩ := exists_ptOf_small V z (lt_min hrt hR)
    have hds : dist (ptOf V z ε) V < rt := lt_of_lt_of_le hd (min_le_left _ _)
    have hdR : dist (ptOf V z ε) V < R := lt_of_lt_of_le hd (min_le_right _ _)
    have hz2' := hz2
    rw [← inInt_smul_iff hε, ← toV2_ptOf V z ε] at hz2'
    have h1 := mem_interior_of_inInt ht hds hz2'
    have h2 : ptOf V z ε ∈ D.region := by
      rw [← D.covers]
      exact Set.mem_iUnion.mpr ⟨t.1, interior_subset h1⟩
    have h3 := (hT _ hdR).mp h2
    rw [toV2_ptOf] at h3
    apply hextT j z hz1
    have hεi := inv_pos.mpr hε
    have := hTs _ h3 ε⁻¹ hεi
    have e : ((ε⁻¹ * (ε * z.1), ε⁻¹ * (ε * z.2)) : V2) = z := by
      ext <;> simp <;> field_simp
    simpa [e] using this
  have hdisj : Disjoint' (Sum.elim p pe) (Sum.elim q qe) := by
    intro o1 o2 hne z ⟨hz1, hz2⟩
    rcases o1 with s | j <;> rcases o2 with t | j'
    · exact tiles_disjoint D V p q hloc s t (fun h => hne (by rw [h])) z ⟨hz1, hz2⟩
    · exact hext s j' z hz2 hz1
    · exact hext t j z hz1 hz2
    · exact hdisjE j j' (fun h => hne (by rw [h])) z ⟨hz1, hz2⟩
  have hsum : ∑ o, wd (Sum.elim p pe o) (Sum.elim q qe o) = 2 * Real.pi := by
    rw [Fintype.sum_sum_type]
    have e1 : ∑ s : AtV D V, wd (Sum.elim p pe (Sum.inl s)) (Sum.elim q qe (Sum.inl s)) = ∑ s : AtV D V, wd (p s) (q s) := rfl
    have e2 : ∑ j : κ, wd (Sum.elim p pe (Sum.inr j)) (Sum.elim q qe (Sum.inr j)) = ∑ j, wd (pe j) (qe j) := rfl
    rw [e1, e2, tiles_angle_sum D V p q hwd]
    linarith
  obtain ⟨e, h1, h2, h3, h4⟩ := fan_cycle (Sum.elim p pe) (Sum.elim q qe) hok' hcov hdisj hsum
  exact ⟨p, q, e, hok, hloc, hwd, hspec, h1, h2, h3, h4⟩
theorem extFan_of (D : RegionDissection N) (V : Plane) (hvert : ∃ i k, (D.tile i).pts k = V)
    (Tgt : Set V2) (R : ℝ) (hR : 0 < R)
    (hT : ∀ y : Plane, dist y V < R → (y ∈ D.region ↔ toV2 (y - V) ∈ Tgt))
    (hTs : ∀ z ∈ Tgt, ∀ t : ℝ, 0 < t → ((t * z.1, t * z.2) : V2) ∈ Tgt)
    (hTc : ∀ x ∈ Tgt, ∀ y ∈ Tgt, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ((a * x.1 + b * y.1, a * x.2 + b * y.2) : V2) ∈ Tgt)
    {κ : Type} [Fintype κ] (pe qe : κ → V2)
    (hokE : ∀ j, SecOK (pe j) (qe j))
    (hcovE : ∀ z : V2, z ∉ Tgt → ∃ j, inCone (pe j) (qe j) z)
    (hdisjE : ∀ j j', j ≠ j' → ∀ z, ¬ (inInt (pe j) (qe j) z ∧ inInt (pe j') (qe j') z))
    (hextT : ∀ j z, inInt (pe j) (qe j) z → z ∉ Tgt)
    (hangle : ∑ i, (D.tile i).localAngle V + ∑ j, wd (pe j) (qe j) = 2 * Real.pi) :
    Nonempty (ExtFan D V κ) := by
  obtain ⟨p, q, e, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    vertex_fan_ext D V hvert Tgt R hR hT hTs pe qe hokE hcovE hdisjE hextT hangle
  have hsumT : ∑ s : AtV D V, wd (p s) (q s) + ∑ j, wd (pe j) (qe j) = 2 * Real.pi := by
    rw [tiles_angle_sum D V p q h3]; exact hangle
  exact ⟨⟨Tgt, R, hR, hT, hTs, hTc, pe, qe, hokE, hextT, hdisjE, p, q, e, h1, h2, h3, hsumT, h4, h5, h6, h7, h8⟩⟩
theorem extFan_of' (D : RegionDissection N) (V : Plane) (hvert : ∃ i k, (D.tile i).pts k = V)
    (Tgt : Set V2) (R : ℝ) (hR : 0 < R)
    (hT : ∀ y : Plane, dist y V < R → (y ∈ D.region ↔ toV2 (y - V) ∈ Tgt))
    (hTs : ∀ z ∈ Tgt, ∀ t : ℝ, 0 < t → ((t * z.1, t * z.2) : V2) ∈ Tgt)
    (hTc : ∀ x ∈ Tgt, ∀ y ∈ Tgt, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ((a * x.1 + b * y.1, a * x.2 + b * y.2) : V2) ∈ Tgt)
    {κ : Type} [Fintype κ] (pe qe : κ → V2)
    (hokE : ∀ j, SecOK (pe j) (qe j))
    (hcovE : ∀ z : V2, z ∉ Tgt → ∃ j, inCone (pe j) (qe j) z)
    (hdisjE : ∀ j j', j ≠ j' → ∀ z, ¬ (inInt (pe j) (qe j) z ∧ inInt (pe j') (qe j') z))
    (hextT : ∀ j z, inInt (pe j) (qe j) z → z ∉ Tgt)
    (hangle : ∑ i, (D.tile i).localAngle V + ∑ j, wd (pe j) (qe j) = 2 * Real.pi) :
    ∃ F : ExtFan D V κ, F.Tgt = Tgt ∧ F.pe = pe ∧ F.qe = qe := by
  obtain ⟨p, q, e, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    vertex_fan_ext D V hvert Tgt R hR hT hTs pe qe hokE hcovE hdisjE hextT hangle
  have hsumT : ∑ s : AtV D V, wd (p s) (q s) + ∑ j, wd (pe j) (qe j) = 2 * Real.pi := by
    rw [tiles_angle_sum D V p q h3]; exact hangle
  exact ⟨⟨Tgt, R, hR, hT, hTs, hTc, pe, qe, hokE, hextT, hdisjE, p, q, e, h1, h2, h3, hsumT, h4, h5, h6, h7, h8⟩, rfl, rfl, rfl⟩
theorem extFan_interior (D : RegionDissection N) (V : Plane) (hvert : ∃ i k, (D.tile i).pts k = V)
    (hV : V ∈ interior D.region) : Nonempty (ExtFan D V Empty) := by
  have hN : 0 < N := by obtain ⟨i, _⟩ := hvert; exact Fin.pos i
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp isOpen_interior V hV
  refine extFan_of D V hvert Set.univ R hR ?_ (fun _ _ _ _ => Set.mem_univ _) (fun _ _ _ _ _ _ _ _ _ => Set.mem_univ _)
    (fun e => e.elim) (fun e => e.elim) (fun j => j.elim) (fun z _ => ?_) (fun j => j.elim) (fun j => j.elim) ?_
  · intro y hy
    simp only [Set.mem_univ, iff_true]
    exact interior_subset (hball (by simpa [Metric.mem_ball] using hy))
  · exact absurd (Set.mem_univ z) ‹_›
  · simp [sum_localAngle_interior D hN hV]
theorem extFan_side_tri (D : RegionDissection N) (V : Plane) (T : Tri) (m : Fin 3) (h0 : T.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < T.basis.coord j V) {ρ : ℝ} (hρ : 0 < ρ)
    (hiff : ∀ y, dist y V < ρ → (y ∈ D.region ↔ y ∈ T.carrier)) (hvert : ∃ i k, (D.tile i).pts k = V) :
    Nonempty (ExtFan D V Unit) := by
  classical
  have hN : 0 < N := by obtain ⟨i, _⟩ := hvert; exact Fin.pos i
  obtain ⟨pT, qT, hokT, hlocT, hwdT, hspecT⟩ := straight_sector T m V h0 hpos
  have hqT : qT = (-pT.1, -pT.2) := by
    rcases hspecT with ⟨k, hk, _⟩ | ⟨_, m', _, _, hq, _⟩
    · exact absurd hk (edge_coords_not_vertex T m V h0 hpos k)
    · exact hq
  subst hqT
  have hpT : pT ≠ 0 := hokT.ne_p
  obtain ⟨R, hR, hRT⟩ := hlocT
  refine extFan_of D V hvert {z | inCone pT (-pT.1, -pT.2) z} (min ρ R) (lt_min hρ hR)
    (fun y hy => by rw [hiff y (lt_of_lt_of_le hy (min_le_left _ _))]; simpa using hRT y (lt_of_lt_of_le hy (min_le_right _ _)))
    (fun z hz t ht => (inCone_smul_iff ht).mpr hz)
    (fun x hx y hy a b ha hb hab => inCone_convex hx hy ha hb hab)
    (fun _ : Unit => (-pT.1, -pT.2)) (fun _ : Unit => pT) (fun _ => secOK_ext hpT) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Set.mem_setOf_eq, inCone_straight_iff, not_le] at hz
    refine ⟨(), ?_, ?_⟩
    · show 0 ≤ crs (-pT.1, -pT.2) z; unfold crs at hz ⊢; nlinarith
    · show 0 ≤ crs z pT; unfold crs at hz ⊢; nlinarith
  · intro j j' hne; exact absurd (Subsingleton.elim j j') hne
  · intro j z hz hin
    simp only [Set.mem_setOf_eq, inCone_straight_iff] at hin
    have := hz.1
    unfold crs at this hin; simp only at this hin; nlinarith
  · rw [sum_localAngle_tri D hN T hρ hiff, Fintype.sum_unique]
    show T.localAngle V + wd (-pT.1, -pT.2) pT = 2 * Real.pi
    rw [wd_ext hpT, localAngle_of_edge_coords T m V h0 hpos]; ring
theorem extFan_corner_tri (D : RegionDissection N) (T : Tri) (j : Fin 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hiff : ∀ y, dist y (T.pts j) < ρ → (y ∈ D.region ↔ y ∈ T.carrier)) (hvert : ∃ i k, (D.tile i).pts k = T.pts j) :
    Nonempty (ExtFan D (T.pts j) Bool) := by
  classical
  have hN : 0 < N := by obtain ⟨i, _⟩ := hvert; exact Fin.pos i
  obtain ⟨pT, qT, hokT, hlocT, hwdT, hspecT⟩ := corner_sector T j
  have hcrs : 0 < crs pT qT := crs_pos_of_corner hokT hspecT ⟨j, rfl⟩
  have hpT : pT ≠ 0 := hokT.ne_p
  have hqT : qT ≠ 0 := hokT.ne_q
  obtain ⟨R, hR, hRT⟩ := hlocT
  set pe : Bool → V2 := fun b => if b then (-qT.1, -qT.2) else qT with hpe
  set qe : Bool → V2 := fun b => if b then pT else (-qT.1, -qT.2) with hqe
  have hok1 : SecOK qT (-qT.1, -qT.2) := Or.inr ⟨crs_straight qT, dt_straight_neg hqT⟩
  have hok2 : SecOK (-qT.1, -qT.2) pT := by
    left
    have : crs (-qT.1, -qT.2) pT = crs pT qT := by unfold crs; ring
    rw [this]; exact hcrs
  refine extFan_of D _ hvert {z | inCone pT qT z} (min ρ R) (lt_min hρ hR)
    (fun y hy => by rw [hiff y (lt_of_lt_of_le hy (min_le_left _ _))]; simpa using hRT y (lt_of_lt_of_le hy (min_le_right _ _)))
    (fun z hz t ht => (inCone_smul_iff ht).mpr hz)
    (fun x hx y hy a b ha hb hab => inCone_convex hx hy ha hb hab) pe qe
    (by intro b; cases b <;> simp [hpe, hqe, hok1, hok2]) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Set.mem_setOf_eq, inCone, not_and_or, not_le] at hz
    by_cases h : 0 ≤ crs qT z
    · exact ⟨false, by
        simp only [hpe, hqe, Bool.false_eq_true, if_false]
        exact (inCone_straight_iff qT z).mpr h⟩
    · push Not at h
      refine ⟨true, ?_, ?_⟩
      · simp only [hpe, hqe, if_true, eq_self_iff_true]
        unfold crs at h hz ⊢
        rcases hz with hz | hz <;> nlinarith
      · simp only [hpe, hqe, if_true, eq_self_iff_true]
        unfold crs at h hz ⊢
        rcases hz with hz | hz <;> nlinarith
  · intro b b' hbb z ⟨hz1, hz2⟩
    cases b <;> cases b' <;> simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true] at hz1 hz2
    · exact hbb rfl
    · obtain ⟨a1, a2⟩ := hz1
      obtain ⟨b1, b2⟩ := hz2
      unfold crs at a1 a2 b1 b2; nlinarith
    · obtain ⟨a1, a2⟩ := hz1
      obtain ⟨b1, b2⟩ := hz2
      unfold crs at a1 a2 b1 b2; nlinarith
    · exact hbb rfl
  · intro b z hz hin
    simp only [Set.mem_setOf_eq, inCone] at hin
    cases b <;> simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true] at hz
    · obtain ⟨a1, a2⟩ := hz; obtain ⟨b1, b2⟩ := hin
      unfold crs at a1 a2 b1 b2; nlinarith
    · obtain ⟨a1, a2⟩ := hz; obtain ⟨b1, b2⟩ := hin
      unfold crs at a1 a2 b1 b2; nlinarith
  · rw [sum_localAngle_tri D hN T hρ hiff, Fintype.sum_bool]
    simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true]
    rw [wd_straight hqT, wd_neg_left hcrs, ← hwdT]
    ring
theorem extFan_exists_poly {M : ℕ} [NeZero M] (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier)
    (V : Plane) (hvert : ∃ i k, (D.tile i).pts k = V) :
    ∃ (κ : Type) (_ : Fintype κ), Nonempty (ExtFan D V κ) := by
  classical
  have hVP : V ∈ P.carrier := by
    obtain ⟨i, k, hk⟩ := hvert
    rw [← hreg, ← D.covers]
    exact Set.mem_iUnion.mpr ⟨i, hk ▸ subset_convexHull ℝ _ ⟨k, rfl⟩⟩
  rcases P.polygon_local P.three_le hVP with hint | ⟨T, hVT, ρ, hρ, hiff'⟩
  · exact ⟨Empty, inferInstance, extFan_interior D V hvert (hreg ▸ hint)⟩
  · have hiff : ∀ y, dist y V < ρ → (y ∈ D.region ↔ y ∈ T.carrier) := by
      intro y hy; rw [hreg]; exact hiff' y hy
    by_cases hcor : ∃ j, V = T.pts j
    · obtain ⟨j, rfl⟩ := hcor
      exact ⟨Bool, inferInstance, extFan_corner_tri D T j hρ hiff hvert⟩
    · push Not at hcor
      rcases T.classify (fun k h => hcor k h) with hpos | ⟨k, hk0, hk⟩ | ⟨k, hkneg⟩
      · refine ⟨Empty, inferInstance, extFan_interior D V hvert ?_⟩
        have hTint : V ∈ interior T.carrier := (T.mem_interior_iff_coord_pos V).mpr hpos
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior V hTint
        rw [mem_interior]
        refine ⟨Metric.ball V (min r ρ), fun y hy => ?_, Metric.isOpen_ball, Metric.mem_ball_self (lt_min hr hρ)⟩
        have hy1 : dist y V < r := lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_left _ _)
        have hy2 : dist y V < ρ := lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right _ _)
        exact (hiff y hy2).mpr (interior_subset (hball (Metric.mem_ball.mpr hy1)))
      · exact ⟨Unit, inferInstance, extFan_side_tri D V T k hk0 hk hρ hiff hvert⟩
      · rw [T.carrier_eq_nonneg_coord] at hVT; exact absurd (hVT k) (not_le.mpr hkneg)
class HasFansC (D : RegionDissection N) : Prop where
  fans : ∀ V : Plane, (∃ i k, (D.tile i).pts k = V) → ∃ (κ : Type) (_ : Fintype κ), Nonempty (ExtFan D V κ)
theorem hasFansC_poly {M : ℕ} [NeZero M] (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) : HasFansC D :=
  ⟨fun V hvert => extFan_exists_poly D P hreg V hvert⟩
namespace ExtFan
end ExtFan
end Erdos634.Draft.LaczFormal.RG
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
inductive WalkT (D : RegionDissection N) (d : V2) : Plane → Plane → List (Fin N × Plane × Plane) → Prop
  | nil (X : Plane) : WalkT D d X X []
  | cons {i : Fin N} {X X' Y : Plane} {L : List (Fin N × Plane × Plane)} :
      TriStep (D.tile i) d X X' → WalkT D d X' Y L → WalkT D d X Y ((i, X, X') :: L)
theorem walkT_progress {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : ∃ T : ℝ, 0 ≤ T ∧ toV2 (Y - X) = (T * d.1, T * d.2) ∧ (L ≠ [] → 0 < T) := by
  induction W with
  | nil X => exact ⟨0, le_rfl, by unfold toV2; ext <;> simp, fun h => absurd rfl h⟩
  | @cons i X X' Y L hS W ih =>
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    obtain ⟨T, hT, hTe, -⟩ := ih
    refine ⟨c + T, by positivity, ?_, fun _ => by positivity⟩
    have : toV2 (Y - X) = ((toV2 (Y - X')).1 + (toV2 (X' - X)).1, (toV2 (Y - X')).2 + (toV2 (X' - X)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hTe, hcw]
    ext <;> simp <;> ring
theorem walkT_dist_sum {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : (L.map fun e => dist e.2.1 e.2.2).sum = dist X Y := by
  induction W with
  | nil X => simp
  | @cons i X X' Y L hS W ih =>
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    obtain ⟨T, hT, hTe, -⟩ := walkT_progress W
    have hXY : toV2 (Y - X) = ((c + T) * d.1, (c + T) * d.2) := by
      have : toV2 (Y - X) = ((toV2 (Y - X')).1 + (toV2 (X' - X)).1, (toV2 (Y - X')).2 + (toV2 (X' - X)).2) := by
        unfold toV2; ext <;> simp
      rw [this, hTe, hcw]; ext <;> simp <;> ring
    have d1 := dist_of_toV2 hc.le hcw
    have d2 := dist_of_toV2 hT hTe
    have d3 := dist_of_toV2 (by positivity : 0 ≤ c + T) hXY
    simp only [List.map_cons, List.sum_cons]
    rw [ih, dist_comm X X', d1, dist_comm X' Y, d2, dist_comm X Y, d3]
    ring
theorem walkT_mem_step {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : ∀ e ∈ L, TriStep (D.tile e.1) d e.2.1 e.2.2 := by
  induction W with
  | nil X => intro e he; exact absurd he (by simp)
  | @cons i X X' Y L hS W ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact hS
    · exact ih e h
end Erdos634.Draft.LaczFormal.RG
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
noncomputable def slen (D : CongruentRegionDissection N) (t : Fin 3) : ℝ := dist (D.model.pts (t + 1)) (D.model.pts (t + 2))
theorem side_len_01 (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) = slen D (idx i (k + 2)) := by
  rw [hidx]
  unfold slen
  rcases perm_opp (idx i) k with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, dist_comm]
  · rw [h1, h2, dist_comm]
theorem side_len_02 (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (i : Fin N) (k : Fin 3) :
    dist ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = slen D (idx i (k + 1)) := by
  have := side_len_01 D idx hidx i (k + 2)
  rw [fin3_p2p1, fin3_p2p2] at this
  rw [dist_comm]; exact this
theorem exists_idx_both (D : CongruentRegionDissection N) :
    ∃ idx : Fin N → Equiv.Perm (Fin 3),
      (∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k'))) ∧
      (∀ i v, TilePlacement.angleAt D.model (idx i v) = TilePlacement.angleAt (D.tile i) v) := by
  choose f σ hf using fun i => D.tiles_congruent i
  refine ⟨σ, fun i k k' => by rw [← hf i k, ← hf i k', (f i).dist_eq], fun i v => ?_⟩
  unfold TilePlacement.angleAt cornerAngle
  have hmap : EuclideanGeometry.angle ((D.tile i).pts (v + 1)) ((D.tile i).pts v) ((D.tile i).pts (v + 2))
      = EuclideanGeometry.angle (D.model.pts (σ i (v + 1))) (D.model.pts (σ i v)) (D.model.pts (σ i (v + 2))) := by
    rw [← hf i (v + 1), ← hf i v, ← hf i (v + 2)]
    have := (f i).toRealAffineIsometryEquiv.toAffineIsometry.angle_map ((D.tile i).pts (v + 1)) ((D.tile i).pts v) ((D.tile i).pts (v + 2))
    simpa using this.symm
  rw [hmap]
  rcases perm_adj (σ i) v with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, EuclideanGeometry.angle_comm]
end Erdos634.Draft.LaczFormal.RG
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
theorem side_len_mem (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    {i : Fin N} {d : V2} {U U' : Plane} (hS : TriStep (D.tile i) d U U') :
    dist U U' = slen D 0 ∨ dist U U' = slen D 1 ∨ dist U U' = slen D 2 := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, -⟩ := hS
  rw [← hk, ← hf]
  rcases fin3_arm kk f hfk with h | h
  · subst h
    rw [side_len_01 D idx hidx]
    generalize idx i (kk + 2) = t
    fin_cases t <;> simp
  · subst h
    rw [side_len_02 D idx hidx]
    generalize idx i (kk + 1) = t
    fin_cases t <;> simp
noncomputable def vtxSet (D : RegionDissection N) : Finset Plane :=
  (Finset.univ : Finset (Fin N × Fin 3)).image (fun p => (D.tile p.1).pts p.2)
theorem mem_vtxSet {D : RegionDissection N} {U : Plane} : U ∈ vtxSet D ↔ ∃ j k, (D.tile j).pts k = U := by
  unfold vtxSet
  constructor
  · intro h
    obtain ⟨⟨j, k⟩, -, hjk⟩ := Finset.mem_image.mp h
    exact ⟨j, k, hjk⟩
  · rintro ⟨j, k, h⟩
    exact Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, h⟩
end Erdos634.Draft.LaczFormal.RG
end

section
open Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
theorem par_refl {v : V2} (hv : v ≠ 0) : Par v v := by
  refine ⟨by unfold crs; ring, ?_⟩
  have := nsq_pos hv
  unfold dt; unfold nsq at this; nlinarith
end Erdos634.Draft.LaczFormal.Graph
end

section
open Erdos634.Geometry Erdos634.RegionDissection
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
noncomputable def cnt (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : Plane) (l : Fin 3) : ℕ :=
  (Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = P ∧ idx p.1 p.2 = l)).card
theorem fiber_sum_P (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (P : Plane)
    (g : Fin 3 → ℝ) :
    ∑ i, ∑ v, (if (D.tile i).pts v = P then g (idx i v) else 0) = ∑ l, (cnt D idx P l : ℝ) * g l := by
  have h1 : ∀ l, (cnt D idx P l : ℝ) * g l = ∑ p : Fin N × Fin 3,
      (if (D.tile p.1).pts p.2 = P ∧ idx p.1 p.2 = l then g l else 0) := by
    intro l
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, cnt]
  calc ∑ i, ∑ v, (if (D.tile i).pts v = P then g (idx i v) else 0)
      = ∑ p : Fin N × Fin 3, (if (D.tile p.1).pts p.2 = P then g (idx p.1 p.2) else 0) :=
        by rw [Fintype.sum_prod_type]
    _ = ∑ p : Fin N × Fin 3, ∑ l, (if (D.tile p.1).pts p.2 = P ∧ idx p.1 p.2 = l then g l else 0) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        by_cases hp : (D.tile p.1).pts p.2 = P
        · simp only [hp, true_and, if_true]
          rw [Finset.sum_ite_eq]; simp
        · simp [hp]
    _ = ∑ l, ∑ p : Fin N × Fin 3, (if (D.tile p.1).pts p.2 = P ∧ idx p.1 p.2 = l then g l else 0) :=
        Finset.sum_comm
    _ = ∑ l, (cnt D idx P l : ℝ) * g l := by simp_rw [h1]
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.KConj
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
theorem vertex_mem {T : Tri} {k : Fin 3} {H : Plane} (h : T.pts k = H) : H ∈ T.carrier :=
  h ▸ subset_convexHull ℝ _ ⟨k, rfl⟩
end Erdos634.Draft.LaczFormal.Graph
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
open scoped Classical
open Erdos634.Geometry Erdos634.KConj
noncomputable def Strn (D : RegionDissection N) (H : Plane) : Finset (Fin N) :=
  Finset.univ.filter (fun i => H ∈ (D.tile i).carrier ∧ ∀ k, (D.tile i).pts k ≠ H)
theorem sum_vc_eq (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (P : Plane) :
    ∑ l, (cnt D idx P l : ℝ) * D.model.angleAt l = ∑ i, vc (D.tile i) P := by
  rw [← fiber_sum_P D idx P D.model.angleAt]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold vc
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs
  · exact hidxA i v
  · rfl
theorem head_angle_sum_gen (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {H : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection H κ) :
    ∑ l, (cnt D idx H l : ℝ) * D.model.angleAt l + Real.pi * (Strn D.toRegionDissection H).card +
      ∑ j, wd (F.pe j) (F.qe j) = 2 * Real.pi := by
  classical
  have hsum := F.hsum
  set g : Fin N → ℝ := fun i => vc (D.tile i) H + if i ∈ Strn D.toRegionDissection H then Real.pi else 0 with hg
  have per : ∀ x : AtV D.toRegionDissection H, wd (F.p x) (F.q x) = g x.1 := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, m, -, -, hq, -⟩
    · have hloc : (D.tile x.1).localAngle H = vc (D.tile x.1) H := by
        have e := vc_of_vertex (D.tile x.1) k
        rw [hk] at e; exact e.symm
      have hnS : x.1 ∉ Strn D.toRegionDissection H := by
        simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_forall, not_not]
        intro _; exact ⟨k, hk⟩
      rw [F.hwd x, hloc, hg]
      simp [hnS]
    · have hvc : vc (D.tile x.1) H = 0 := vc_of_nonvertex _ _ (fun v h => hnv v h.symm)
      have hS : x.1 ∈ Strn D.toRegionDissection H := by
        simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨x.2, hnv⟩
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      rw [hw, hg]
      simp [hvc, hS]
  have h1 : ∑ x : AtV D.toRegionDissection H, wd (F.p x) (F.q x) = ∑ i, g i := by
    calc ∑ x : AtV D.toRegionDissection H, wd (F.p x) (F.q x) = ∑ x : AtV D.toRegionDissection H, g x.1 :=
          Finset.sum_congr rfl (fun x _ => per x)
      _ = ∑ i ∈ Finset.univ.filter (fun i => H ∈ (D.tile i).carrier), g i := by
          symm
          exact Finset.sum_subtype (Finset.univ.filter (fun i => H ∈ (D.tile i).carrier)) (by simp)
            (fun i => g i)
      _ = ∑ i, g i := by
          rw [Finset.sum_filter_of_ne]
          intro i _ hne
          by_contra hnm
          apply hne
          have hvc : vc (D.tile i) H = 0 := vc_of_nonvertex _ _ (fun v h => hnm (vertex_mem h.symm))
          have hS : i ∉ Strn D.toRegionDissection H := fun h => hnm (by simp [Strn] at h; exact h.1)
          simp [hg, hvc, hS]
  have h2 : ∑ i, g i = ∑ i, vc (D.tile i) H + Real.pi * (Strn D.toRegionDissection H).card := by
    rw [hg]; simp only
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [sum_vc_eq D idx hidxA H, ← h2, ← h1]
  exact hsum
theorem head_angle_sum (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {H : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection H κ) (hemp : IsEmpty κ) :
    ∑ l, (cnt D idx H l : ℝ) * D.model.angleAt l + Real.pi * (Strn D.toRegionDissection H).card = 2 * Real.pi := by
  have h := head_angle_sum_gen D idx hidxA F
  have hv : ∑ j, wd (F.pe j) (F.qe j) = 0 := by haveI := hemp; simp
  rw [hv, add_zero] at h
  exact h
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
section Fan
variable {D : RegionDissection N} {H : Plane} {κ : Type} [Fintype κ]
theorem e_inj_shift (F : ExtFan D H κ) (j0 : ℕ) {x y : ℕ} (hx : x < Fintype.card (AtV D H ⊕ κ)) (hy : y < Fintype.card (AtV D H ⊕ κ))
    (h : F.e (j0 + x) = F.e (j0 + y)) : x = y := by
  set L := Fintype.card (AtV D H ⊕ κ) with hL
  have hL0 : 0 < L := by omega
  have h1 : F.e ((j0 + x) % L) = F.e ((j0 + y) % L) := by
    rw [← cyc_mod F.e L F.hper, ← cyc_mod F.e L F.hper]; exact h
  have h2 := F.hinj (Set.mem_Iio.mpr (Nat.mod_lt _ hL0)) (Set.mem_Iio.mpr (Nat.mod_lt _ hL0)) h1
  have h3 : j0 + x ≡ j0 + y [MOD L] := h2
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' j0 h3) hx hy
end Fan
section Fan2
variable {D : RegionDissection N} {H : Plane} {κ : Type} [Fintype κ]
theorem par_or_par_neg_of_crs_zero {u w : V2} (hu : u ≠ 0) (hw : w ≠ 0) (h : crs u w = 0) :
    Par w u ∨ Par w (-u.1, -u.2) := by
  have hdt : dt u w ≠ 0 := fun h2 => hu (eq_zero_of_crs_dt hw h h2)
  rcases lt_or_gt_of_ne hdt with hlt | hgt
  · right
    refine ⟨?_, ?_⟩
    · unfold crs at h ⊢; linarith
    · unfold dt at hlt ⊢; linarith
  · left
    refine ⟨?_, ?_⟩
    · unfold crs at h ⊢; linarith
    · unfold dt at hgt ⊢; linarith
end Fan2
end Erdos634.Draft.LaczFormal.RG
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
theorem extFan_side_shape (D : RegionDissection N) (V : Plane) (T : Tri) (m : Fin 3) (h0 : T.basis.coord m V = 0)
    (hpos : ∀ j, j ≠ m → 0 < T.basis.coord j V) {ρ : ℝ} (hρ : 0 < ρ)
    (hiff : ∀ y, dist y V < ρ → (y ∈ D.region ↔ y ∈ T.carrier)) (hvert : ∃ i k, (D.tile i).pts k = V) :
    ∃ (pT : V2) (F : ExtFan D V Unit), pT ≠ 0 ∧ F.pe () = (-pT.1, -pT.2) ∧ F.qe () = pT ∧ F.Tgt = {z | inCone pT (-pT.1, -pT.2) z} := by
  classical
  have hN : 0 < N := by obtain ⟨i, _⟩ := hvert; exact Fin.pos i
  obtain ⟨pT, qT, hokT, hlocT, hwdT, hspecT⟩ := straight_sector T m V h0 hpos
  have hqT : qT = (-pT.1, -pT.2) := by
    rcases hspecT with ⟨k, hk, _⟩ | ⟨_, m', _, _, hq, _⟩
    · exact absurd hk (edge_coords_not_vertex T m V h0 hpos k)
    · exact hq
  subst hqT
  have hpT : pT ≠ 0 := hokT.ne_p
  obtain ⟨R, hR, hRT⟩ := hlocT
  suffices h : ∃ F : ExtFan D V Unit, F.Tgt = {z | inCone pT (-pT.1, -pT.2) z} ∧ F.pe = (fun _ : Unit => (-pT.1, -pT.2)) ∧ F.qe = (fun _ : Unit => pT) by
    obtain ⟨F, h1, h2, h3⟩ := h
    exact ⟨pT, F, hpT, by rw [h2], by rw [h3], h1⟩
  refine extFan_of' D V hvert {z | inCone pT (-pT.1, -pT.2) z} (min ρ R) (lt_min hρ hR)
    (fun y hy => by rw [hiff y (lt_of_lt_of_le hy (min_le_left _ _))]; simpa using hRT y (lt_of_lt_of_le hy (min_le_right _ _)))
    (fun z hz t ht => (inCone_smul_iff ht).mpr hz)
    (fun x hx y hy a b ha hb hab => inCone_convex hx hy ha hb hab)
    (fun _ : Unit => (-pT.1, -pT.2)) (fun _ : Unit => pT) (fun _ => secOK_ext hpT) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Set.mem_setOf_eq, inCone_straight_iff, not_le] at hz
    refine ⟨(), ?_, ?_⟩
    · show 0 ≤ crs (-pT.1, -pT.2) z; unfold crs at hz ⊢; nlinarith
    · show 0 ≤ crs z pT; unfold crs at hz ⊢; nlinarith
  · intro j j' hne; exact absurd (Subsingleton.elim j j') hne
  · intro j z hz hin
    simp only [Set.mem_setOf_eq, inCone_straight_iff] at hin
    have := hz.1
    unfold crs at this hin; simp only at this hin; nlinarith
  · rw [sum_localAngle_tri D hN T hρ hiff, Fintype.sum_unique]
    show T.localAngle V + wd (-pT.1, -pT.2) pT = 2 * Real.pi
    rw [wd_ext hpT, localAngle_of_edge_coords T m V h0 hpos]; ring
theorem extFan_corner_shape (D : RegionDissection N) (T : Tri) (j : Fin 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hiff : ∀ y, dist y (T.pts j) < ρ → (y ∈ D.region ↔ y ∈ T.carrier)) (hvert : ∃ i k, (D.tile i).pts k = T.pts j) :
    ∃ (pT qT : V2) (F : ExtFan D (T.pts j) Bool), 0 < crs pT qT ∧ F.pe true = (-qT.1, -qT.2) ∧ F.qe true = pT ∧ F.pe false = qT ∧ F.qe false = (-qT.1, -qT.2) ∧ F.Tgt = {z | inCone pT qT z} ∧ SectorSpec T (T.pts j) pT qT := by
  classical
  have hN : 0 < N := by obtain ⟨i, _⟩ := hvert; exact Fin.pos i
  obtain ⟨pT, qT, hokT, hlocT, hwdT, hspecT⟩ := corner_sector T j
  have hcrs : 0 < crs pT qT := crs_pos_of_corner hokT hspecT ⟨j, rfl⟩
  have hpT : pT ≠ 0 := hokT.ne_p
  have hqT : qT ≠ 0 := hokT.ne_q
  obtain ⟨R, hR, hRT⟩ := hlocT
  set pe : Bool → V2 := fun b => if b then (-qT.1, -qT.2) else qT with hpe
  set qe : Bool → V2 := fun b => if b then pT else (-qT.1, -qT.2) with hqe
  have hok1 : SecOK qT (-qT.1, -qT.2) := Or.inr ⟨crs_straight qT, dt_straight_neg hqT⟩
  have hok2 : SecOK (-qT.1, -qT.2) pT := by
    left
    have : crs (-qT.1, -qT.2) pT = crs pT qT := by unfold crs; ring
    rw [this]; exact hcrs
  suffices h : ∃ F : ExtFan D (T.pts j) Bool, F.Tgt = {z | inCone pT qT z} ∧ F.pe = pe ∧ F.qe = qe by
    obtain ⟨F, h1, h2, h3⟩ := h
    exact ⟨pT, qT, F, hcrs, by rw [h2]; simp [hpe], by rw [h3]; simp [hqe], by rw [h2]; simp [hpe], by rw [h3]; simp [hqe], h1, hspecT⟩
  refine extFan_of' D _ hvert {z | inCone pT qT z} (min ρ R) (lt_min hρ hR)
    (fun y hy => by rw [hiff y (lt_of_lt_of_le hy (min_le_left _ _))]; simpa using hRT y (lt_of_lt_of_le hy (min_le_right _ _)))
    (fun z hz t ht => (inCone_smul_iff ht).mpr hz)
    (fun x hx y hy a b ha hb hab => inCone_convex hx hy ha hb hab) pe qe
    (by intro b; cases b <;> simp [hpe, hqe, hok1, hok2]) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Set.mem_setOf_eq, inCone, not_and_or, not_le] at hz
    by_cases h : 0 ≤ crs qT z
    · exact ⟨false, by
        simp only [hpe, hqe, Bool.false_eq_true, if_false]
        exact (inCone_straight_iff qT z).mpr h⟩
    · push Not at h
      refine ⟨true, ?_, ?_⟩
      · simp only [hpe, hqe, if_true, eq_self_iff_true]
        unfold crs at h hz ⊢
        rcases hz with hz | hz <;> nlinarith
      · simp only [hpe, hqe, if_true, eq_self_iff_true]
        unfold crs at h hz ⊢
        rcases hz with hz | hz <;> nlinarith
  · intro b b' hbb z ⟨hz1, hz2⟩
    cases b <;> cases b' <;> simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true] at hz1 hz2
    · exact hbb rfl
    · obtain ⟨a1, a2⟩ := hz1
      obtain ⟨b1, b2⟩ := hz2
      unfold crs at a1 a2 b1 b2; nlinarith
    · obtain ⟨a1, a2⟩ := hz1
      obtain ⟨b1, b2⟩ := hz2
      unfold crs at a1 a2 b1 b2; nlinarith
    · exact hbb rfl
  · intro b z hz hin
    simp only [Set.mem_setOf_eq, inCone] at hin
    cases b <;> simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true] at hz
    · obtain ⟨a1, a2⟩ := hz; obtain ⟨b1, b2⟩ := hin
      unfold crs at a1 a2 b1 b2; nlinarith
    · obtain ⟨a1, a2⟩ := hz; obtain ⟨b1, b2⟩ := hin
      unfold crs at a1 a2 b1 b2; nlinarith
  · rw [sum_localAngle_tri D hN T hρ hiff, Fintype.sum_bool]
    simp only [hpe, hqe, Bool.false_eq_true, Bool.true_eq_false, if_true, if_false, eq_self_iff_true]
    rw [wd_straight hqT, wd_neg_left hcrs, ← hwdT]
    ring
end Erdos634.Draft.LaczFormal.RG
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21
namespace Erdos634.Draft.LaczFormal.RG
variable {N M : ℕ} [NeZero M]
theorem par_of_halfplanes {a b : V2} (ha : a ≠ 0) (hb : b ≠ 0) (h : ∀ z : V2, 0 ≤ crs a z ↔ 0 ≤ crs b z) : Par a b := by
  have h1 : 0 ≤ crs a b := (h b).mpr (by unfold crs; ring_nf; exact le_rfl)
  have h2 : 0 ≤ crs a (-b.1, -b.2) := (h _).mpr (by unfold crs; ring_nf; exact le_rfl)
  have h3 : crs b a = 0 := by unfold crs at h1 h2 ⊢; simp only at h2; linarith
  rcases par_or_par_neg_of_crs_zero hb ha h3 with hp | hp
  · exact hp
  · exfalso
    obtain ⟨c, hc, hca⟩ := hp.smul
    have hn := nsq_pos hb
    unfold nsq at hn
    have hz := (h (-b.2, b.1)).mpr ?_
    · rw [hca] at hz
      unfold crs at hz
      simp only at hz
      nlinarith [mul_pos hc hn]
    · unfold crs; simp only; nlinarith
open Erdos634.CertCoord in
theorem crs_toV2_mkPt (u : Plane) (z : V2) : crs (toV2 u) z = cross2 u (mkPt z.1 z.2) := by
  unfold crs toV2 cross2 mkPt
  simp
theorem poly_near_edge (P : ConvPoly M) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ ρ > 0, ∀ y, dist y ((1 - t) • P.v i + t • P.v (i + 1)) < ρ →
      (y ∈ P.carrier ↔ 0 ≤ cross2 (P.e i) (y - ((1 - t) • P.v i + t • P.v (i + 1)))) := by
  set V : Plane := (1 - t) • P.v i + t • P.v (i + 1) with hV
  have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0.le, ht1.le⟩
  have hstrict : ∀ j, j ≠ i → 0 < P.c j V := fun j hj => P.c_edge_pos P.three_le i htI hj (fun _ => ht1) (fun _ => ht0)
  have hev : ∀ᶠ y in nhds V, ∀ j, j ≠ i → 0 < P.c j y := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall (fun y hy => absurd hj hy)
    · exact ((P.continuous_c j).continuousAt.eventually (lt_mem_nhds (hstrict j hj))).mono (fun y hy _ => hy)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ρ, hρ, fun y hy => ?_⟩
  have hci : P.c i y = cross2 (P.e i) (y - V) := by
    have e1 : y - P.v i = (y - V) + t • P.e i := by
      unfold ConvPoly.e; rw [hV]; module
    unfold ConvPoly.c
    rw [e1, cross2_add_right, cross2_smul_right, cross2_self]; ring
  constructor
  · intro hyP; rw [← hci]; exact hyP i
  · intro h j
    by_cases hj : j = i
    · subst hj; show 0 ≤ P.c j y; rw [hci]; exact h
    · exact (hball hy j hj).le
theorem fan_open_edge (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hvert : ∃ j k, (D.tile j).pts k = (1 - t) • P.v i + t • P.v (i + 1)) :
    ∃ (pT : V2) (F : ExtFan D ((1 - t) • P.v i + t • P.v (i + 1)) Unit), Par pT (toV2 (P.e i)) ∧ F.pe () = (-pT.1, -pT.2) ∧ F.qe () = pT ∧
      F.Tgt = {z | inCone pT (-pT.1, -pT.2) z} := by
  set V : Plane := (1 - t) • P.v i + t • P.v (i + 1) with hV
  obtain ⟨ρ, hρ, hiff⟩ := P.open_edge_local_T P.three_le i ht0 ht1
  have hiffD : ∀ y, dist y V < ρ → (y ∈ D.region ↔ y ∈ (P.locTri P.three_le i).carrier) := by
    intro y hy; rw [hreg]; exact hiff y hy
  set T := P.locTri P.three_le i with hT
  have hco : ∀ k, T.basis.coord k V = ![1 - t, t, 0] k := by
    intro k
    refine Erdos634.Subdivision.Tri.coord_eq_of_combo T V ![1 - t, t, 0] ?_ ?_ k
    · simp
    · simp [hT, ConvPoly.locTri, triOf, hV]
  have h0 : T.basis.coord 2 V = 0 := by rw [hco]; rfl
  have hpos : ∀ j, j ≠ 2 → 0 < T.basis.coord j V := by
    intro j hj
    rw [hco]
    fin_cases j
    · show 0 < 1 - t; linarith
    · show 0 < t; exact ht0
    · exact absurd rfl hj
  obtain ⟨pT, F, hpT, hpe, hqe, hTgt⟩ := extFan_side_shape D V T 2 h0 hpos hρ hiffD hvert
  refine ⟨pT, F, ?_, hpe, hqe, hTgt⟩
  obtain ⟨ρ2, hρ2, hnear⟩ := poly_near_edge P i ht0 ht1
  apply par_of_halfplanes hpT (toV2_ne_zero (P.e_ne_zero P.three_le i))
  intro z
  obtain ⟨ε, hε, hd⟩ := exists_ptOf_small V z (lt_min hρ2 F.hR)
  have hd1 : dist (ptOf V z ε) V < ρ2 := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : dist (ptOf V z ε) V < F.R := lt_of_lt_of_le hd (min_le_right _ _)
  have ha := F.hT _ hd2
  rw [hTgt, toV2_ptOf, Set.mem_setOf_eq, inCone_straight_iff] at ha
  have hb := hnear _ hd1
  rw [← hreg] at hb
  have hyV : ptOf V z ε - V = ε • Erdos634.CertCoord.mkPt z.1 z.2 := by simp [ptOf]
  rw [hyV, cross2_smul_right, ← crs_toV2_mkPt] at hb
  have hc : crs pT (ε * z.1, ε * z.2) = ε * crs pT z := by unfold crs; simp only; ring
  rw [hc] at ha
  have := ha.symm.trans hb
  constructor
  · intro h; exact (mul_nonneg_iff_of_pos_left hε).mp (this.mp ((mul_nonneg_iff_of_pos_left hε).mpr h))
  · intro h; exact (mul_nonneg_iff_of_pos_left hε).mp (this.mpr ((mul_nonneg_iff_of_pos_left hε).mpr h))
theorem fan_vertex_poly (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (k : Fin M)
    (hvert : ∃ j k', (D.tile j).pts k' = P.v (k + 1)) :
    ∃ (pT qT : V2) (F : ExtFan D (P.v (k + 1)) Bool), Par pT (toV2 (P.e (k + 1))) ∧ Par qT (toV2 (P.v k - P.v (k + 1))) ∧ 0 < crs pT qT ∧
      F.pe true = (-qT.1, -qT.2) ∧ F.qe true = pT ∧ F.pe false = qT ∧ F.qe false = (-qT.1, -qT.2) ∧ F.Tgt = {z | inCone pT qT z} := by
  obtain ⟨ρ, hρ, hiff⟩ := P.vertex_local_T P.three_le k
  have hiffD : ∀ y, dist y ((P.locTri P.three_le k).pts 1) < ρ → (y ∈ D.region ↔ y ∈ (P.locTri P.three_le k).carrier) := by
    intro y hy; rw [hreg]; exact hiff y hy
  obtain ⟨pT, qT, F, hcrs, h1, h2, h3, h4, h5, hspec⟩ := extFan_corner_shape D (P.locTri P.three_le k) 1 hρ hiffD hvert
  have hfacts := (ConvPoly.fin_facts P.three_le k)
  have hk2 : k + 1 + 1 = k + 2 := hfacts.2.2.2.2.2
  rcases hspec with ⟨k0, hk0, halt⟩ | ⟨hnv, -⟩
  · have hk01 : k0 = 1 := (P.locTri P.three_le k).indep.injective hk0
    subst hk01
    have hori := P.ori_pos P.three_le k
    have e1 : (P.locTri P.three_le k).pts (1 + 1) = P.v (k + 2) := rfl
    have e2 : (P.locTri P.three_le k).pts (1 + 2) = P.v k := rfl
    have e3 : (P.locTri P.three_le k).pts 1 = P.v (k + 1) := rfl
    rcases halt with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · rw [e1, e3] at hp; rw [e2, e3] at hq
      have hpe : pT = toV2 (P.e (k + 1)) := by rw [hp]; unfold ConvPoly.e; rw [hk2]
      have hv1 : toV2 (P.e (k + 1)) ≠ 0 := toV2_ne_zero (P.e_ne_zero P.three_le (k + 1))
      refine ⟨pT, qT, F, ?_, ?_, hcrs, h1, h2, h3, h4, h5⟩
      · rw [hpe]; exact par_refl hv1
      · rw [hq]
        have : toV2 (P.v k - P.v (k + 1)) ≠ 0 := by
          apply toV2_ne_zero
          intro h
          apply P.e_ne_zero P.three_le k
          unfold ConvPoly.e
          rw [← neg_sub, h]; simp
        exact par_refl this
    · exfalso
      rw [e2, e3] at hp; rw [e1, e3] at hq
      rw [hp, hq] at hcrs
      rw [crs_toV2] at hcrs
      have : cross (P.v k - P.v (k + 1)) (P.v (k + 2) - P.v (k + 1)) = - cross2 (P.v (k + 1) - P.v k) (P.v (k + 2) - P.v k) := by
        unfold cross cross2; simp; ring
      rw [this] at hcrs
      linarith
  · exact absurd rfl (hnv 1)
end Erdos634.Draft.LaczFormal.RG
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
theorem first_step_open (D : RegionDissection N) {V : Plane} (F : ExtFan D V Unit) {pT d : V2}
    (hpe : F.pe () = (-pT.1, -pT.2)) (hqe : F.qe () = pT) (hpd : Par pT d)
    (hvert : ∃ i k, (D.tile i).pts k = V) : ∃ i U', TriStep (D.tile i) d V U' := by
  classical
  have hpT : pT ≠ 0 := hpd.ne_left
  obtain ⟨j0, hj0, hej0⟩ := F.hsurj (Sum.inr ())
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : V ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hLcard : Fintype.card (AtV D V ⊕ Unit) = Fintype.card (AtV D V) + 1 := by
    rw [Fintype.card_sum]; simp
  have hAtV : 0 < Fintype.card (AtV D V) := Fintype.card_pos_iff.mpr ⟨⟨i0, hmem0⟩⟩
  have hP0 := F.hP j0
  rw [hej0] at hP0
  simp only [Sum.elim_inr] at hP0
  rw [hqe] at hP0
  rcases hnext : F.e (j0 + 1) with s | u
  · rw [hnext] at hP0
    simp only [Sum.elim_inl] at hP0
    have hsp : Par (F.p s) d := hP0.trans hpd
    have hsum : ∑ x : AtV D V, wd (F.p x) (F.q x) ≤ Real.pi := by
      have hv : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
        rw [Fintype.sum_unique]
        show wd (F.pe ()) (F.qe ()) = Real.pi
        rw [hpe, hqe, wd_ext hpT]
      have := F.hsum
      linarith
    have hcorner : ∃ k, (D.tile s.1).pts k = V := by
      rcases F.hspec s with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
      · exact ⟨k, hk⟩
      · exfalso
        have ht : (⟨i0, hmem0⟩ : AtV D V) ≠ s := by
          intro h
          have := congrArg Subtype.val h
          simp only at this
          rw [this] at hk0
          exact hnv k0 hk0
        refine no_straight_of_sum F.p F.q F.hok (Ne.symm ht) ?_ hsum
        rw [hq]; exact wd_straight (F.hok s).ne_p
    obtain ⟨kk, fl, hk, hp', hq'⟩ := spec_corner_data (F.hspec s) hcorner
    have hcrs := crs_pos_of_corner (F.hok s) (F.hspec s) hcorner
    exact ⟨s.1, (D.tile s.1).pts (armP kk fl), triStep_of_start kk fl hk hp' hq' hcrs hsp⟩
  · exfalso
    have h1 : F.e (j0 + 1) = F.e (j0 + 0) := by
      show F.e (j0 + 1) = F.e j0
      rw [hnext, hej0]
    have := e_inj_shift F j0 (by omega) (by omega) h1
    omega
theorem wd_lt_pi_of_crs_pos {p q : V2} (h : 0 < crs p q) : wd p q < Real.pi := by
  unfold wd
  rw [Complex.arg_lt_pi_iff]
  right
  simpa using h.ne'
theorem corner_tile_sum (D : RegionDissection N) {V : Plane} (F : ExtFan D V Bool) {pT qT : V2} (hcr : 0 < crs pT qT)
    (h1 : F.pe true = (-qT.1, -qT.2)) (h2 : F.qe true = pT) (h3 : F.pe false = qT) (h4 : F.qe false = (-qT.1, -qT.2)) :
    ∑ x : AtV D V, wd (F.p x) (F.q x) = wd pT qT := by
  have hqT : qT ≠ 0 := by
    intro h; rw [h] at hcr; unfold crs at hcr; simp at hcr
  have := F.hsum
  rw [Fintype.sum_bool, h1, h2, h3, h4, wd_straight hqT, wd_neg_left hcr] at this
  linarith
theorem first_step_corner (D : RegionDissection N) {V : Plane} (F : ExtFan D V Bool) {pT qT d : V2} (hcr : 0 < crs pT qT)
    (h1 : F.pe true = (-qT.1, -qT.2)) (h2 : F.qe true = pT) (h3 : F.pe false = qT) (h4 : F.qe false = (-qT.1, -qT.2))
    (hpd : Par pT d) (hvert : ∃ i k, (D.tile i).pts k = V) : ∃ i U', TriStep (D.tile i) d V U' := by
  classical
  obtain ⟨j0, hj0, hej0⟩ := F.hsurj (Sum.inr true)
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : V ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hsumT := corner_tile_sum D F hcr h1 h2 h3 h4
  have hP0 := F.hP j0
  rw [hej0] at hP0
  simp only [Sum.elim_inr] at hP0
  rw [h2] at hP0
  rcases hnext : F.e (j0 + 1) with s | b
  · rw [hnext] at hP0
    simp only [Sum.elim_inl] at hP0
    have hsp : Par (F.p s) d := hP0.trans hpd
    have hcorner : ∃ k, (D.tile s.1).pts k = V := by
      rcases F.hspec s with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
      · exact ⟨k, hk⟩
      · exfalso
        have hw : wd (F.p s) (F.q s) = Real.pi := by rw [hq]; exact wd_straight (F.hok s).ne_p
        have hle : wd (F.p s) (F.q s) ≤ ∑ x : AtV D V, wd (F.p x) (F.q x) :=
          Finset.single_le_sum (f := fun x => wd (F.p x) (F.q x)) (fun x _ => (wd_pos (F.hok x)).le) (Finset.mem_univ s)
        have := wd_lt_pi_of_crs_pos hcr
        linarith
    obtain ⟨kk, fl, hk, hp', hq'⟩ := spec_corner_data (F.hspec s) hcorner
    have hcrs := crs_pos_of_corner (F.hok s) (F.hspec s) hcorner
    exact ⟨s.1, (D.tile s.1).pts (armP kk fl), triStep_of_start kk fl hk hp' hq' hcrs hsp⟩
  · exfalso
    rw [hnext] at hP0
    simp only [Sum.elim_inr] at hP0
    cases b
    · simp only [h3] at hP0
      have := hP0.1
      unfold crs at this hcr
      nlinarith
    · have h5 : F.e (j0 + 1) = F.e (j0 + 0) := by
        show F.e (j0 + 1) = F.e j0
        rw [hnext, hej0]
      have := e_inj_shift F j0 (by
        have : 2 ≤ Fintype.card (AtV D V ⊕ Bool) := by
          rw [Fintype.card_sum]; simp
        omega) (by
        have := hj0; omega) h5
      omega
end Erdos634.Draft.LaczFormal.RG
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21
namespace Erdos634.Draft.LaczFormal.RG
variable {N M : ℕ} [NeZero M]
theorem poly_vertex_is_tile_vertex (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (m : Fin M) :
    ∃ i k, (D.tile i).pts k = P.v m := by
  classical
  set k1 := m - 1 with hk1
  have hm : k1 + 1 = m := (ConvPoly.fin_facts P.three_le m).2.2.2.2.1
  have hV : P.v m ∈ P.carrier := by
    intro j
    by_cases hj : j = m
    · subst hj; rw [← P.c_self j]; rfl
    · by_cases hj' : j + 1 = m
      · rw [← hj']; exact (P.c_next j).symm ▸ le_rfl
      · exact (P.c_vertex_pos (Ne.symm hj) (Ne.symm hj')).le
  have hcov : P.v m ∈ ⋃ i, (D.tile i).carrier := by rw [D.covers, hreg]; exact hV
  obtain ⟨i0, hi0⟩ := Set.mem_iUnion.mp hcov
  have hN : 0 < N := Fin.pos i0
  obtain ⟨ρ, hρ, hiff⟩ := P.vertex_local_T P.three_le k1
  have hT1 : (P.locTri P.three_le k1).pts 1 = P.v m := by rw [← hm]; rfl
  have hiffD : ∀ y, dist y (P.v m) < ρ → (y ∈ D.region ↔ y ∈ (P.locTri P.three_le k1).carrier) := by
    intro y hy; rw [hreg]; exact hiff y (by rw [hm]; exact hy)
  have hsum := sum_localAngle_tri D hN (P.locTri P.three_le k1) hρ hiffD
  have hT1' : (P.locTri P.three_le k1).localAngle (P.v m) < Real.pi := by
    rw [← hT1, Tri.localAngle_vertex]
    exact Erdos634.RouteOneVertexKill.cornerAngle_lt_pi _ 1
  have hle : (D.tile i0).localAngle (P.v m) ≤ ∑ i', (D.tile i').localAngle (P.v m) :=
    Finset.single_le_sum (f := fun i' => (D.tile i').localAngle (P.v m)) (fun i' _ => (D.tile i').localAngle_nonneg _) (Finset.mem_univ i0)
  rw [hsum] at hle
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i0) (P.v m) with ⟨j, hj, -⟩ | h2 | h1 | h0
  · exact ⟨i0, j, hj.symm⟩
  · exfalso; have := Real.pi_pos; linarith
  · exfalso; linarith
  · exact absurd h0 (Erdos634.MarchFlank.localAngle_ne_zero_of_mem _ hi0)
theorem vertex_on_edge (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {U : Plane}
    (hU : ∃ j k, (D.tile j).pts k = U) (hline : crs (toV2 (P.e i)) (toV2 (U - P.v i)) = 0) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, U = (1 - t) • P.v i + t • P.v (i + 1) := by
  have hUP : U ∈ P.carrier := by
    obtain ⟨j, k, hjk⟩ := hU
    rw [← hreg, ← D.covers]
    exact Set.mem_iUnion.mpr ⟨j, hjk ▸ subset_convexHull ℝ _ ⟨k, rfl⟩⟩
  have h0 : P.c i U = 0 := by
    have : P.c i U = crs (toV2 (P.e i)) (toV2 (U - P.v i)) := rfl
    rw [this]; exact hline
  exact P.edge_param P.three_le hUP h0
theorem step_exists_poly (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) {U : Plane}
    (hU : ∃ j k, (D.tile j).pts k = U) (hline : crs (toV2 (P.e i)) (toV2 (U - P.v i)) = 0) (hUY : U ≠ P.v (i + 1)) :
    ∃ j U', TriStep (D.tile j) (toV2 (P.e i)) U U' := by
  classical
  obtain ⟨t, ht, hUt⟩ := vertex_on_edge D P hreg i hU hline
  rcases ht.1.eq_or_lt with h0 | h0
  · 
    have hUX : U = P.v i := by rw [hUt, ← h0]; simp
    have hk : i - 1 + 1 = i := (ConvPoly.fin_facts P.three_le i).2.2.2.2.1
    have hvert : ∃ j k, (D.tile j).pts k = P.v (i - 1 + 1) := by rw [hk, ← hUX]; exact hU
    obtain ⟨pT, qT, F, hpd, hqd, hcr, h1, h2, h3, h4, h5⟩ := fan_vertex_poly D P hreg (i - 1) hvert
    rw [hk] at hpd
    obtain ⟨j, U', hS⟩ := first_step_corner D F hcr h1 h2 h3 h4 hpd hvert
    rw [hk] at hS
    rw [hUX]
    exact ⟨j, U', hS⟩
  · have ht1 : t < 1 := by
      rcases ht.2.eq_or_lt with h1 | h1
      · exfalso; apply hUY; rw [hUt, h1]; simp
      · exact h1
    have hvert : ∃ j k, (D.tile j).pts k = (1 - t) • P.v i + t • P.v (i + 1) := by rw [← hUt]; exact hU
    obtain ⟨pT, F, hpd, hpe, hqe, hTgt⟩ := fan_open_edge D P hreg i h0 ht1 hvert
    obtain ⟨j, U', hS⟩ := first_step_open D F hpe hqe hpd hvert
    rw [← hUt] at hS
    exact ⟨j, U', hS⟩
theorem side_walk_exists_poly (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) :
    ∃ L, WalkT D (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L := by
  classical
  set d := toV2 (P.e i) with hd
  set X0 := P.v i with hX0
  set Y0 := P.v (i + 1) with hY0
  have hd0 : d ≠ 0 := toV2_ne_zero (P.e_ne_zero P.three_le i)
  have hnd : 0 < nsq d := nsq_pos hd0
  set A : Finset Plane := vtxSet D with hA
  set F : Plane → Finset Plane := fun U => A.filter (fun v => dt d (toV2 (v - X0)) > dt d (toV2 (U - X0))) with hF
  have key : ∀ n : ℕ, ∀ U : Plane, (F U).card = n → (∃ j k, (D.tile j).pts k = U) →
      crs d (toV2 (U - X0)) = 0 → ∃ L, WalkT D d U Y0 L := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro U hcard hvert hline
      by_cases hUY : U = Y0
      · exact ⟨[], hUY ▸ WalkT.nil U⟩
      · have hstep : ∃ j U', TriStep (D.tile j) d U U' := step_exists_poly D P hreg i hvert hline hUY
        obtain ⟨j, U', hS⟩ := hstep
        obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := id hS
        obtain ⟨c, hc, hcw⟩ := hpar.smul
        have hdec : toV2 (U' - X0) = ((toV2 (U' - U)).1 + (toV2 (U - X0)).1, (toV2 (U' - U)).2 + (toV2 (U - X0)).2) := by
          unfold toV2; ext <;> simp
        have hline' : crs d (toV2 (U' - X0)) = 0 := by
          rw [hdec, hcw]
          unfold crs at hline ⊢; simp only at hline ⊢; nlinarith [hline]
        have hdt : dt d (toV2 (U' - X0)) > dt d (toV2 (U - X0)) := by
          rw [hdec, hcw]
          unfold dt nsq at *; simp only; nlinarith [mul_pos hc hnd]
        have hvert' : ∃ j k, (D.tile j).pts k = U' := ⟨j, f, hf⟩
        have hsub : F U' ⊂ F U := by
          refine ⟨?_, ?_⟩
          · intro v hv
            simp only [hF, Finset.mem_filter] at hv ⊢
            exact ⟨hv.1, lt_trans hdt hv.2⟩
          · intro hsub
            have hU'mem : U' ∈ F U := by
              simp only [hF, Finset.mem_filter]
              exact ⟨mem_vtxSet.mpr hvert', hdt⟩
            have := hsub hU'mem
            simp only [hF, Finset.mem_filter] at this
            exact lt_irrefl _ this.2
        have hlt : (F U').card < n := hcard ▸ Finset.card_lt_card hsub
        obtain ⟨L, hL⟩ := ih (F U').card hlt U' rfl hvert' hline'
        exact ⟨(j, U, U') :: L, WalkT.cons hS hL⟩
  have hX0v : ∃ j k, (D.tile j).pts k = X0 := poly_vertex_is_tile_vertex D P hreg i
  exact key _ X0 rfl hX0v (by unfold crs toV2; simp)
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
namespace Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry Erdos634.TilePlacement
def IrrPi (x : ℝ) : Prop := ¬ ∃ r : ℚ, x = (r : ℝ) * Real.pi
end Erdos634.Draft.TheoremPConditional
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
namespace Erdos634.Draft.LaczFormal
theorem angleAt_sum (T : Tri) : T.angleAt 0 + T.angleAt 1 + T.angleAt 2 = Real.pi := by
  show cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) +
       cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) +
       cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi
  exact Erdos634.Geometry.cornerAngle_sum T
def TileAngles {N : ℕ} (D : CongruentDissection N) (x y z : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), D.model.angleAt (σ 0) = x ∧ D.model.angleAt (σ 1) = y ∧
    D.model.angleAt (σ 2) = z
end Erdos634.Draft.LaczFormal
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21
namespace Erdos634.Draft.LaczFormal.RG
variable {N M : ℕ} [NeZero M]
theorem walkT_nil_eq {D : RegionDissection N} {d : V2} {X Y : Plane} (W : WalkT D d X Y []) : X = Y := by
  cases W; rfl
theorem walkT_head {D : RegionDissection N} {d : V2} {X Y : Plane} {e : Fin N × Plane × Plane} {L' : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y (e :: L')) : e.2.1 = X ∧ TriStep (D.tile e.1) d e.2.1 e.2.2 := by
  cases W with
  | cons hS _ => exact ⟨rfl, hS⟩
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
theorem sideOpp_law (M : Tri) (j : Fin 3) : sideOpp M j * Real.sin (angleAt M 0) = sideOpp M 0 * Real.sin (angleAt M j) := by
  fin_cases j
  · rfl
  · have := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp M 0
    have e : (0 + 1 : Fin 3) = 1 := rfl
    rw [e] at this
    show sideOpp M 1 * Real.sin (angleAt M 0) = sideOpp M 0 * Real.sin (angleAt M 1)
    linarith
  · have := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp M 2
    have e : (2 + 1 : Fin 3) = 0 := rfl
    rw [e] at this
    show sideOpp M 2 * Real.sin (angleAt M 0) = sideOpp M 0 * Real.sin (angleAt M 2)
    linarith
theorem dist_eq_sideOpp (M : Tri) (x y z : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    dist (M.pts x) (M.pts y) = sideOpp M z := by
  unfold sideOpp
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all <;> first | rfl | exact dist_comm _ _
theorem fin3_third_exists : ∀ x y : Fin 3, x ≠ y → ∃ z : Fin 3, x ≠ z ∧ y ≠ z := by decide
theorem model_dist_of_angles (M : Tri) (x y x' y' : Fin 3) (hxy : x ≠ y) (hxy' : x' ≠ y')
    (hx : angleAt M x = angleAt M x') (hy : angleAt M y = angleAt M y') :
    dist (M.pts x) (M.pts y) = dist (M.pts x') (M.pts y') := by
  obtain ⟨z, hxz, hyz⟩ := fin3_third_exists x y hxy
  obtain ⟨z', hxz', hyz'⟩ := fin3_third_exists x' y' hxy'
  rw [dist_eq_sideOpp M x y z hxy hxz hyz, dist_eq_sideOpp M x' y' z' hxy' hxz' hyz']
  have hs : angleAt M 0 + angleAt M 1 + angleAt M 2 = Real.pi := Erdos634.Draft.LaczFormal.angleAt_sum M
  have hz : angleAt M z = Real.pi - angleAt M x - angleAt M y := by
    have : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z → angleAt M x + angleAt M y + angleAt M z = Real.pi := by
      intro x y z h1 h2 h3
      fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all <;> linarith
    have := this x y z hxy hxz hyz
    linarith
  have hz' : angleAt M z' = Real.pi - angleAt M x' - angleAt M y' := by
    have : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z → angleAt M x + angleAt M y + angleAt M z = Real.pi := by
      intro x y z h1 h2 h3
      fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all <;> linarith
    have := this x' y' z' hxy' hxz' hyz'
    linarith
  have hzz : angleAt M z = angleAt M z' := by rw [hz, hz', hx, hy]
  have h0 := Erdos634.Draft.LaczFormal.Thm21.sin_angleAt_pos M 0
  have l1 := sideOpp_law M z
  have l2 := sideOpp_law M z'
  rw [hzz] at l1
  apply mul_right_cancel₀ h0.ne'
  rw [l1, l2]
theorem idx_dist_of_angle (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hA : ∀ i v, angleAt D.model (idx i v) = angleAt (D.tile i) v) :
    ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')) := by
  obtain ⟨σ, hσd, hσa⟩ := exists_idx_both D
  intro i k k'
  by_cases hkk : k = k'
  · subst hkk; simp
  · rw [hσd i k k']
    apply model_dist_of_angles D.model (σ i k) (σ i k') (idx i k) (idx i k')
      (fun h => hkk ((σ i).injective h)) (fun h => hkk ((idx i).injective h))
    · rw [hσa i k, hA i k]
    · rw [hσa i k', hA i k']
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
noncomputable def Tri.relabel (M : Tri) (σ : Equiv.Perm (Fin 3)) : Tri where
  pts := fun k => M.pts (σ k)
  indep := M.indep.comp_embedding σ.toEmbedding
noncomputable def relabel (D : CongruentRegionDissection N) (σ : Equiv.Perm (Fin 3)) : CongruentRegionDissection N where
  toRegionDissection := D.toRegionDissection
  model := Tri.relabel D.model σ
  tiles_congruent := by
    intro i
    obtain ⟨f, τ, hf⟩ := D.tiles_congruent i
    exact ⟨f, τ.trans σ.symm, fun k => by
      show f ((D.tile i).pts k) = D.model.pts (σ (σ.symm (τ k)))
      rw [Equiv.apply_symm_apply]; exact hf k⟩
theorem relabel_slen (D : CongruentRegionDissection N) (σ : Equiv.Perm (Fin 3)) (t : Fin 3) :
    slen (relabel D σ) t = slen D (σ t) := by
  unfold slen
  show dist (D.model.pts (σ (t + 1))) (D.model.pts (σ (t + 2))) = dist (D.model.pts (σ t + 1)) (D.model.pts (σ t + 2))
  rcases perm_adj σ t with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, dist_comm]
theorem relabel_angleAt (D : CongruentRegionDissection N) (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    angleAt (relabel D σ).model j = angleAt D.model (σ j) := by
  unfold angleAt cornerAngle
  show EuclideanGeometry.angle (D.model.pts (σ (j + 1))) (D.model.pts (σ j)) (D.model.pts (σ (j + 2))) = _
  rcases perm_adj σ j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, EuclideanGeometry.angle_comm]
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
theorem model_angle_pos' (D : CongruentRegionDissection N) (l : Fin 3) : 0 < D.model.angleAt l :=
  Erdos634.MarchFlank.cornerAngle_pos D.model l
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N M : ℕ} [NeZero M]
theorem poly_c_continuous (P : ConvPoly M) (i : Fin M) : Continuous (fun x : Plane => P.c i x) := by
  unfold ConvPoly.c cross2
  fun_prop
theorem interior_of_c_pos (P : ConvPoly M) {X : Plane} (h : ∀ i, 0 < P.c i X) : X ∈ interior P.carrier := by
  rw [mem_interior]
  refine ⟨{x | ∀ i, 0 < P.c i x}, fun x hx i => (hx i).le, ?_, h⟩
  have : {x : Plane | ∀ i, 0 < P.c i x} = ⋂ i, {x : Plane | 0 < P.c i x} := by ext x; simp
  rw [this]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (poly_c_continuous P i))
theorem point_cases (D : RegionDissection N) (P : ConvPoly M) (hreg : D.region = P.carrier) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) :
    X ∈ interior D.region ∨ (∃ (i : Fin M) (t : ℝ), 0 < t ∧ t < 1 ∧ X = (1 - t) • P.v i + t • P.v (i + 1)) ∨
      (∃ k : Fin M, X = P.v (k + 1)) := by
  classical
  have hXP : X ∈ P.carrier := by
    obtain ⟨j, k, hjk⟩ := hvert
    rw [← hreg, ← D.covers]
    exact Set.mem_iUnion.mpr ⟨j, hjk ▸ subset_convexHull ℝ _ ⟨k, rfl⟩⟩
  by_cases hall : ∀ i, 0 < P.c i X
  · left; rw [hreg]; exact interior_of_c_pos P hall
  · right
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    have h0 : P.c i X = 0 := le_antisymm hi (hXP i)
    have hline : crs (toV2 (P.e i)) (toV2 (X - P.v i)) = 0 := h0
    obtain ⟨t, ht, hXt⟩ := vertex_on_edge D P hreg i hvert hline
    rcases ht.1.eq_or_lt with h0t | h0t
    · right
      refine ⟨i - 1, ?_⟩
      rw [(ConvPoly.fin_facts P.three_le i).2.2.2.2.1, hXt, ← h0t]; simp
    · rcases ht.2.eq_or_lt with h1t | h1t
      · right
        refine ⟨i, ?_⟩
        rw [hXt, h1t]; simp
      · left; exact ⟨i, t, h0t, h1t, hXt⟩
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N M : ℕ} [NeZero M]
theorem cnt_zero_of_not_vertex' (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {P : Plane}
    (hP : ¬ ∃ i k, (D.tile i).pts k = P) (l : Fin 3) : cnt D idx P l = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨i, k⟩ _ ⟨h, -⟩
  exact hP ⟨i, k, h⟩
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N M : ℕ} [NeZero M]
theorem walkT_getLast {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) (hL : L ≠ []) :
    ∃ el, L.getLast? = some el ∧ el.2.2 = Y ∧ TriStep (D.tile el.1) d el.2.1 el.2.2 := by
  induction W with
  | nil X => exact absurd rfl hL
  | @cons i X X' Y L hS W ih =>
    by_cases hL' : L = []
    · subst hL'
      have hX : X' = Y := walkT_nil_eq W
      exact ⟨(i, X, X'), by simp, hX, hS⟩
    · obtain ⟨el, h1, h2, h3⟩ := ih hL'
      refine ⟨el, ?_, h2, h3⟩
      cases L with
      | nil => exact absurd rfl hL'
      | cons e2 L2 => simpa [List.getLast?_cons_cons] using h1
theorem edge_data (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier) (i : Fin M) :
    ∃ (L : List (Fin N × Plane × Plane)) (e0 el : Fin N × Plane × Plane),
      WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) L ∧ L.head? = some e0 ∧ L.getLast? = some el ∧
      e0.2.1 = P.v i ∧ el.2.2 = P.v (i + 1) ∧ TriStep (D.tile e0.1) (toV2 (P.e i)) e0.2.1 e0.2.2 ∧
      TriStep (D.tile el.1) (toV2 (P.e i)) el.2.1 el.2.2 := by
  classical
  obtain ⟨L, W⟩ := side_walk_exists_poly D.toRegionDissection P hreg i
  have hne : P.v i ≠ P.v (i + 1) := by
    intro he
    apply P.e_ne_zero P.three_le i
    unfold ConvPoly.e; rw [← he]; simp
  have hL : L ≠ [] := by
    rintro rfl
    exact hne (walkT_nil_eq W)
  obtain ⟨e0, L0, hL0⟩ : ∃ e0 L0, L = e0 :: L0 := by
    cases L with
    | nil => exact absurd rfl hL
    | cons e0 L0 => exact ⟨e0, L0, rfl⟩
  obtain ⟨el, hl1, hl2, hl3⟩ := walkT_getLast W hL
  have hh := walkT_head (hL0 ▸ W)
  exact ⟨L, e0, el, W, by rw [hL0]; rfl, hl1, hh.1, hl2, hh.2, hl3⟩
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N M : ℕ} [NeZero M]
theorem swap02_0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by simp
theorem swap02_1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
theorem swap02_2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by simp
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N M : ℕ} [NeZero M]
noncomputable def Asum (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (X : Plane) : ℝ :=
  ∑ l, (cnt D idx X l : ℝ) * D.model.angleAt l
theorem Asum_pos (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) : 0 < Asum D idx X := by
  obtain ⟨j, k, hk⟩ := hvert
  have hc : 1 ≤ cnt D idx X (idx j k) := by
    unfold cnt
    exact Finset.card_pos.mpr ⟨(j, k), by simp [hk]⟩
  unfold Asum
  refine Finset.sum_pos' (fun l _ => mul_nonneg (Nat.cast_nonneg _) (model_angle_pos' D l).le) ⟨idx j k, Finset.mem_univ _, ?_⟩
  exact mul_pos (by exact_mod_cast hc) (model_angle_pos' D _)
theorem corner_A (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (k : Fin M)
    (hvert : ∃ j k', (D.tile j).pts k' = P.v (k + 1)) : Asum D idx (P.v (k + 1)) = P.angle (k + 1) := by
  classical
  have hpi := Real.pi_pos
  set V := P.v (k + 1) with hVdef
  obtain ⟨pT, qT, F, hpd, hqd, hcr, h1, h2, h3, h4, h5⟩ := fan_vertex_poly D.toRegionDissection P hreg k hvert
  have hqT : qT ≠ 0 := by intro h; rw [h] at hcr; unfold crs at hcr; simp at hcr
  obtain ⟨i0, k0, hk0⟩ := hvert
  have hmem0 : V ∈ (D.tile i0).carrier := hk0 ▸ subset_convexHull ℝ _ ⟨k0, rfl⟩
  have hsumT := corner_tile_sum D.toRegionDissection F hcr h1 h2 h3 h4
  have hwlt := wd_lt_pi_of_crs_pos hcr
  have hwpos := wd_pos (Or.inl hcr : SecOK pT qT)
  have hnostr : ∀ x : AtV D.toRegionDissection V, ∃ k, (D.tile x.1).pts k = V := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso
      have hw : wd (F.p x) (F.q x) = Real.pi := by rw [hq]; exact wd_straight (F.hok x).ne_p
      have hle : wd (F.p x) (F.q x) ≤ ∑ y : AtV D.toRegionDissection V, wd (F.p y) (F.q y) :=
        Finset.single_le_sum (f := fun y => wd (F.p y) (F.q y)) (fun y _ => (wd_pos (F.hok y)).le) (Finset.mem_univ x)
      linarith
  have hStrn : Strn D.toRegionDissection V = ∅ := by
    ext j
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and, not_forall, not_not]
    intro hj
    exact hnostr ⟨j, hj⟩
  have hang := head_angle_sum_gen D idx hidxA F
  have hvirt : ∑ j : Bool, wd (F.pe j) (F.qe j) = Real.pi + (Real.pi - wd pT qT) := by
    rw [Fintype.sum_bool, h1, h2, h3, h4, wd_straight hqT, wd_neg_left hcr]; ring
  rw [hStrn, hvirt] at hang
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] at hang
  have hAsum : Asum D idx V = wd pT qT := by unfold Asum; linarith
  have hθ : P.angle (k + 1) = wd pT qT := by
    obtain ⟨ρ, hρ, hiff⟩ := P.vertex_local_T P.three_le k
    have hN : 0 < N := Fin.pos i0
    have hT1 : (P.locTri P.three_le k).pts 1 = V := rfl
    have hiffD : ∀ y, dist y ((P.locTri P.three_le k).pts 1) < ρ → (y ∈ D.region ↔ y ∈ (P.locTri P.three_le k).carrier) := by
      intro y hy; rw [hreg]; exact hiff y hy
    have hs := sum_localAngle_tri D.toRegionDissection hN (P.locTri P.three_le k) hρ hiffD
    have hwdt := tiles_angle_sum D.toRegionDissection V F.p F.q F.hwd
    have hwdT : wd pT qT = (P.locTri P.three_le k).localAngle V := by
      rw [← hsumT, hwdt]; exact hs
    have hloc : (P.locTri P.three_le k).localAngle V = P.angle (k + 1) := by
      have := Tri.localAngle_vertex (P.locTri P.three_le k) 1
      rw [hT1] at this
      rw [this]
      unfold ConvPoly.angle cornerAngle
      have e1 : k + 1 - 1 = k := by simp
      have e2 : k + 1 + 1 = k + 2 := (ConvPoly.fin_facts P.three_le k).2.2.2.2.2
      rw [e1, e2, EuclideanGeometry.angle_comm (P.v k)]
      rfl
    rw [← hloc, hwdT]
  rw [hAsum, hθ]
theorem vertex_A (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) :
    (X ∈ interior D.region ∧ (Asum D idx X = 2 * Real.pi ∨ Asum D idx X = Real.pi)) ∨
    ((X ∉ interior D.region) ∧ (Asum D idx X = Real.pi ∨ ∃ k : Fin M, X = P.v (k + 1) ∧ Asum D idx X = P.angle (k + 1))) := by
  classical
  have hpi := Real.pi_pos
  have hA := Asum_pos D idx hvert
  by_cases hint : X ∈ interior D.region
  · left
    refine ⟨hint, ?_⟩
    obtain ⟨F⟩ := extFan_interior D.toRegionDissection X hvert hint
    have hang := head_angle_sum D idx hidxA F inferInstance
    have hAe : Asum D idx X + Real.pi * ((Strn D.toRegionDissection X).card : ℝ) = 2 * Real.pi := hang
    rcases Nat.lt_or_ge (Strn D.toRegionDissection X).card 2 with hlt | hge
    · interval_cases hc : (Strn D.toRegionDissection X).card
      · left; simpa using hAe
      · right; simp at hAe; linarith
    · exfalso
      have : (2 : ℝ) ≤ (Strn D.toRegionDissection X).card := by exact_mod_cast hge
      nlinarith
  · right
    refine ⟨hint, ?_⟩
    rcases point_cases D.toRegionDissection P hreg hvert with h | ⟨i, t, ht0, ht1, hXt⟩ | ⟨k, hXk⟩
    · exact absurd h hint
    · left
      subst hXt
      obtain ⟨pT, F, hpd, hpe, hqe, hTgt⟩ := fan_open_edge D.toRegionDissection P hreg i ht0 ht1 hvert
      have hpT : pT ≠ 0 := hpd.ne_left
      have hang := head_angle_sum_gen D idx hidxA F
      have hvirt : ∑ j : Unit, wd (F.pe j) (F.qe j) = Real.pi := by
        rw [Fintype.sum_unique]
        show wd (F.pe ()) (F.qe ()) = Real.pi
        rw [hpe, hqe, wd_ext hpT]
      rw [hvirt] at hang
      have hAe : Asum D idx ((1 - t) • P.v i + t • P.v (i + 1)) +
          Real.pi * ((Strn D.toRegionDissection ((1 - t) • P.v i + t • P.v (i + 1))).card : ℝ) = Real.pi := by
        unfold Asum; linarith
      rcases Nat.eq_zero_or_pos (Strn D.toRegionDissection ((1 - t) • P.v i + t • P.v (i + 1))).card with h0 | h0
      · rw [h0] at hAe; simpa using hAe
      · exfalso
        have : (1 : ℝ) ≤ (Strn D.toRegionDissection ((1 - t) • P.v i + t • P.v (i + 1))).card := by exact_mod_cast h0
        nlinarith
    · right
      refine ⟨k, hXk, ?_⟩
      subst hXk
      exact corner_A D P hreg idx hidxA k hvert
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N M : ℕ} [NeZero M]
theorem type_arith {α β γ : ℝ} (hαβ : α + β = Real.pi / 3) (hγ : γ = 2 * Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (c0 c1 c2 m : ℕ)
    (h : (c0 : ℝ) * α + c1 * β + c2 * γ = m * (Real.pi / 3)) : c0 = c1 ∧ c0 + 2 * c2 = m := by
  have hpi := Real.pi_pos
  have hβ : β = Real.pi / 3 - α := by linarith
  subst hγ
  subst hβ
  have e : ((c0 : ℝ) - c1) * α = ((m : ℝ) - c1 - 2 * c2) * (Real.pi / 3) := by linear_combination h
  by_cases hne : c0 = c1
  · subst hne
    refine ⟨rfl, ?_⟩
    have e2 : ((m : ℝ) - c0 - 2 * c2) * (Real.pi / 3) = 0 := by rw [← e]; ring
    have e3 : (m : ℝ) - c0 - 2 * c2 = 0 := by
      rcases mul_eq_zero.mp e2 with h1 | h1
      · exact h1
      · exfalso; linarith
    have e4 : ((c0 + 2 * c2 : ℕ) : ℝ) = m := by push_cast; linarith
    exact_mod_cast e4
  · exfalso
    apply hα
    have hd : ((c0 : ℝ) - c1) ≠ 0 := by
      intro h0
      apply hne
      have : (c0 : ℝ) = c1 := by linarith
      exact_mod_cast this
    refine ⟨((m : ℚ) - c1 - 2 * c2) / (3 * ((c0 : ℚ) - c1)), ?_⟩
    push_cast
    field_simp
    linarith
theorem vertex_type (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi) (hPang : ∀ i, P.angle i = Real.pi / 3) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) :
    cnt D idx X 0 = cnt D idx X 1 ∧
      ((X ∈ interior D.region ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = 6) ∨ cnt D idx X 0 + 2 * cnt D idx X 2 = 3 ∨
        (X ∉ interior D.region ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = 1 ∧ ∃ k : Fin M, X = P.v (k + 1))) := by
  have hA : Asum D idx X = ((Asum D idx X) / (Real.pi / 3)) * (Real.pi / 3) := by
    have := Real.pi_pos; field_simp
  have hAexp : Asum D idx X = (cnt D idx X 0 : ℝ) * D.model.angleAt 0 + (cnt D idx X 1 : ℝ) * D.model.angleAt 1 + (cnt D idx X 2 : ℝ) * D.model.angleAt 2 := by
    unfold Asum; rw [Fin.sum_univ_three]
  have hpi := Real.pi_pos
  have key : ∀ m : ℕ, Asum D idx X = m * (Real.pi / 3) → cnt D idx X 0 = cnt D idx X 1 ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = m := by
    intro m hm
    exact type_arith hαβ hγ hα _ _ _ m (by rw [← hAexp]; exact hm)
  rcases vertex_A D P hreg idx hidxA hvert with ⟨hi, h2 | h1⟩ | ⟨hni, h1 | ⟨k, hXk, hk⟩⟩
  · have := key 6 (by rw [h2]; push_cast; ring)
    exact ⟨this.1, Or.inl ⟨hi, this.2⟩⟩
  · have := key 3 (by rw [h1]; push_cast; ring)
    exact ⟨this.1, Or.inr (Or.inl this.2)⟩
  · have := key 3 (by rw [h1]; push_cast; ring)
    exact ⟨this.1, Or.inr (Or.inl this.2)⟩
  · have := key 1 (by rw [hk, hPang]; push_cast; ring)
    exact ⟨this.1, Or.inr (Or.inr ⟨hni, this.2, k, hXk⟩)⟩
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
namespace Erdos634.Geometry
theorem Tri.oppLen_pos' (T : Tri) (k : Fin 3) : 0 < T.oppLen k := by
  unfold Tri.oppLen
  have hne : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  exact dist_pos.mpr fun h => hne (T.indep.injective h)
end Erdos634.Geometry
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
noncomputable def convPoly3 (a b c : Plane) (h : 0 < cross2 (b - a) (c - a)) : ConvPoly 3 where
  v := ![a, b, c]
  three_le := le_refl _
  left := by
    intro i j hji hji1
    unfold cross2 at h ⊢
    simp only [PiLp.sub_apply] at h
    fin_cases i <;> fin_cases j <;> simp at hji hji1 ⊢ <;> nlinarith [h]
theorem convPoly3_carrier (a b c : Plane) (h : 0 < cross2 (b - a) (c - a)) : (convPoly3 a b c h).carrier = (triOf a b c h).carrier := by
  ext y
  rw [triOf_carrier]
  unfold ConvPoly.carrier convPoly3
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hh
    exact ⟨by simpa using hh 0, by simpa using hh 1, by simpa using hh 2⟩
  · rintro ⟨h1, h2, h3⟩ i
    fin_cases i
    · simpa using h1
    · simpa using h2
    · simpa using h3
theorem convPoly3_angle (a b c : Plane) (h : 0 < cross2 (b - a) (c - a)) (i : Fin 3) :
    (convPoly3 a b c h).angle i = (triOf a b c h).angleAt i := by
  unfold ConvPoly.angle Tri.angleAt cornerAngle
  have e : i - 1 = i + 2 := by fin_cases i <;> decide
  rw [e, EuclideanGeometry.angle_comm]
  rfl
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
theorem regular_of_irr (T : PolyTiling N 3) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi) (hPang : ∀ i, T.P.angle i = Real.pi / 3) : RegularPQ T.C := by
  classical
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both T.C
  refine ⟨idx, hidxA, fun X => ?_⟩
  have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3 := by
    have := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
    have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
    linarith
  have hγ' : T.C.model.angleAt 2 = 2 * Real.pi / 3 := hγ
  have hα' : ¬ ∃ r : ℚ, T.C.model.angleAt 0 = (r : ℝ) * Real.pi := hα
  by_cases hvert : ∃ j k, (T.C.tile j).pts k = X
  · exact (vertex_type T.C T.P T.region_eq idx hidxA hγ' hαβ hα' hPang hvert).1
  · show cnt T.C idx X 0 = cnt T.C idx X 1
    rw [cnt_zero_of_not_vertex' T.C idx hvert 0, cnt_zero_of_not_vertex' T.C idx hvert 1]
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
theorem exists_convpoly_of_tri' (T : Tri) :
    ∃ P : ConvPoly 3, P.carrier = T.carrier ∧ ∃ τ : Equiv.Perm (Fin 3), (∀ i, P.angle i = T.angleAt (τ i)) ∧ (∀ i, P.v i = T.pts (τ i)) := by
  have hdet : T.det = cross2 (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := rfl
  rcases T.det_pos_or_neg with hpos | hneg
  · have h : 0 < cross2 (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := by rw [← hdet]; exact hpos
    refine ⟨convPoly3 (T.pts 0) (T.pts 1) (T.pts 2) h, ?_, 1, fun i => ?_, fun i => ?_⟩
    · rw [convPoly3_carrier]
      show convexHull ℝ (Set.range ![T.pts 0, T.pts 1, T.pts 2]) = convexHull ℝ (Set.range T.pts)
      have : (![T.pts 0, T.pts 1, T.pts 2] : Fin 3 → Plane) = T.pts := by
        funext k; fin_cases k <;> rfl
      rw [this]
    · rw [convPoly3_angle]
      fin_cases i <;> rfl
    · fin_cases i <;> rfl
  · have h : 0 < cross2 (T.pts 2 - T.pts 0) (T.pts 1 - T.pts 0) := by
      have : cross2 (T.pts 2 - T.pts 0) (T.pts 1 - T.pts 0) = - T.det := by
        rw [hdet]; unfold cross2; ring
      rw [this]; linarith
    refine ⟨convPoly3 (T.pts 0) (T.pts 2) (T.pts 1) h, ?_, Equiv.swap 1 2, fun i => ?_, fun i => ?_⟩
    · rw [convPoly3_carrier]
      show convexHull ℝ (Set.range ![T.pts 0, T.pts 2, T.pts 1]) = convexHull ℝ (Set.range T.pts)
      congr 1
      ext x
      simp only [Set.mem_range]
      constructor
      · rintro ⟨k, rfl⟩
        fin_cases k
        · exact ⟨0, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨1, rfl⟩
      · rintro ⟨k, rfl⟩
        fin_cases k
        · exact ⟨0, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨1, rfl⟩
    · rw [convPoly3_angle]
      fin_cases i
      · show cornerAngle _ _ _ = cornerAngle _ _ _
        simp [triOf, cornerAngle, Tri.angleAt]
        rw [EuclideanGeometry.angle_comm]
        rfl
      · show cornerAngle _ _ _ = cornerAngle _ _ _
        simp [triOf, cornerAngle]
        rw [EuclideanGeometry.angle_comm]
      · show cornerAngle _ _ _ = cornerAngle _ _ _
        simp [triOf, cornerAngle]
        rw [EuclideanGeometry.angle_comm]
    · fin_cases i <;> first | rfl | simp [convPoly3, Equiv.swap_apply_def]
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical Fin.NatCast
open Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
-- (sincomm_irr_family removed: not used)
end Erdos634.Draft.LaczFormal.RG
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem Tri.basis_apply' (T : Tri) (j : Fin 3) : T.basis j = T.pts j := rfl
theorem Tri.coord_vertex (T : Tri) (i j : Fin 3) :
    T.basis.coord i (T.pts j) = if i = j then 1 else 0 := by
  rw [← Tri.basis_apply', AffineBasis.coord_apply]
theorem Tri.coord_lineMap (T : Tri) (i : Fin 3) (X Y : Plane) (t : ℝ) :
    T.basis.coord i (AffineMap.lineMap X Y t)
      = T.basis.coord i X + t * (T.basis.coord i Y - T.basis.coord i X) := by
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module']
  simp only [smul_eq_mul]; ring
theorem Tri.mem_carrier_iff_coord (T : Tri) (X : Plane) :
    X ∈ T.carrier ↔ ∀ i, 0 ≤ T.basis.coord i X := by
  rw [T.carrier_eq_nonneg_coord]; rfl
end TriangleTiling
end

section
namespace TriangleTiling.Equilateral
open Erdos634.Geometry
namespace EquilateralBound
theorem sum_rot {E : Type*} [AddCommMonoid E] (f : Fin 3 → E) (k : Fin 3) :
    ∑ i, f i = f k + f (k + 1) + f (k + 2) := by
  rw [Fin.sum_univ_three]
  rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2) k with rfl | rfl | rfl
  · rfl
  · rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]; abel
  · rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]; abel
theorem comb (T : Tri) (P Z : Plane) :
    P - Z = ∑ i, T.basis.coord i P • (T.pts i - Z) := by
  have h := T.basis.linear_combination_coord_eq_self P
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    T.basis.sum_coord_apply_eq_one P, one_smul]
  conv_lhs => rw [← h]
  rfl
theorem vertex_bound (T : Tri) {X : ℝ} (hX : ∀ i j, i ≠ j → dist (T.pts i) (T.pts j) = X)
    (k : Fin 3) {Q : Plane} (hQ : Q ∈ T.carrier) :
    dist (T.pts k) Q ≤ X ∧ (dist (T.pts k) Q = X → Q = T.pts (k + 1) ∨ Q = T.pts (k + 2)) := by
  have hc := (Tri.mem_carrier_iff_coord T Q).mp hQ
  have hk1 : k + 1 ≠ k := by revert k; decide
  have hk2 : k + 2 ≠ k := by revert k; decide
  have hk12 : k + 1 ≠ k + 2 := by revert k; decide
  have hs := T.basis.sum_coord_apply_eq_one Q
  rw [sum_rot _ k] at hs
  set c := T.basis.coord k Q
  set a := T.basis.coord (k + 1) Q with ha_def
  set b := T.basis.coord (k + 2) Q with hb_def
  set u := T.pts (k + 1) - T.pts k
  set w := T.pts (k + 2) - T.pts k
  have hQk : Q - T.pts k = a • u + b • w := by
    rw [comb T Q (T.pts k), sum_rot _ k, sub_self, smul_zero, zero_add]
  have hu : ‖u‖ = X := by rw [← dist_eq_norm]; exact hX _ _ hk1
  have hw : ‖w‖ = X := by rw [← dist_eq_norm]; exact hX _ _ hk2
  have hXpos : 0 < X := by
    rw [← hX _ _ hk1]; exact dist_pos.mpr (T.indep.injective.ne hk1)
  have ha : 0 ≤ a := hc (k + 1)
  have hb : 0 ≤ b := hc (k + 2)
  have hc0 := hc k
  have hd : dist (T.pts k) Q = ‖a • u + b • w‖ := by rw [dist_comm, dist_eq_norm, hQk]
  have hn : ‖a • u‖ + ‖b • w‖ = (a + b) * X := by
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb, hu, hw]; ring
  have hle : ‖a • u + b • w‖ ≤ (a + b) * X := hn ▸ norm_add_le _ _
  refine ⟨by rw [hd]; nlinarith, fun heq => ?_⟩
  rw [hd] at heq
  have hab : a + b = 1 := by nlinarith
  have hsr : SameRay ℝ (a • u) (b • w) := by
    rw [sameRay_iff_norm_add]; nlinarith
  rcases ha.eq_or_lt with ha0 | ha0
  · right
    have hb1 : b = 1 := by linarith
    rw [← ha0, hb1, zero_smul, zero_add, one_smul] at hQk
    exact sub_left_injective (hQk.trans rfl)
  rcases hb.eq_or_lt with hb0 | hb0
  · left
    have ha1 : a = 1 := by linarith
    rw [← hb0, ha1, zero_smul, add_zero, one_smul] at hQk
    exact sub_left_injective (hQk.trans rfl)
  exfalso
  have hu0 : u ≠ 0 := fun h => by rw [h, norm_zero] at hu; linarith
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
  obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ :=
    hsr.exists_pos (smul_ne_zero ha0.ne' hu0) (smul_ne_zero hb0.ne' hw0)
  set t := r₂ * b / (r₁ * a)
  have hut : u = t • w := by
    rw [smul_smul, smul_smul] at hr
    have hpos : r₁ * a ≠ 0 := by positivity
    calc u = (r₁ * a)⁻¹ • ((r₁ * a) • u) := by rw [smul_smul, inv_mul_cancel₀ hpos, one_smul]
      _ = t • w := by rw [hr, smul_smul]; congr 1; simp only [t]; field_simp
  have hline : T.pts (k + 1) = AffineMap.lineMap (T.pts k) (T.pts (k + 2)) t := by
    rw [AffineMap.lineMap_apply_module]
    have : T.pts (k + 1) = T.pts k + t • w := by rw [← hut]; simp only [u]; abel
    rw [this, smul_sub, sub_smul, one_smul]; abel
  have h1 := Tri.coord_vertex T (k + 1) (k + 1)
  rw [hline, Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex, if_neg hk1, if_neg hk12] at h1
  simp at h1
theorem point_bound (T : Tri) {X : ℝ} (hX : ∀ i j, i ≠ j → dist (T.pts i) (T.pts j) = X)
    {P Q : Plane} (hP : P ∈ T.carrier) (hQ : Q ∈ T.carrier) :
    dist P Q ≤ X ∧ (dist P Q = X → ∃ j, Q = T.pts j) := by
  have hc := (Tri.mem_carrier_iff_coord T P).mp hP
  have hs := T.basis.sum_coord_apply_eq_one P
  have hle : dist P Q ≤ ∑ i, T.basis.coord i P * dist (T.pts i) Q := by
    rw [dist_eq_norm, comb T P Q]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_smul, Real.norm_of_nonneg (hc i), dist_eq_norm]
  have hterm : ∀ i ∈ Finset.univ, T.basis.coord i P * dist (T.pts i) Q ≤ T.basis.coord i P * X :=
    fun i _ => mul_le_mul_of_nonneg_left (vertex_bound T hX i hQ).1 (hc i)
  have hsumX : ∑ i, T.basis.coord i P * X = X := by rw [← Finset.sum_mul, hs, one_mul]
  refine ⟨hle.trans ((Finset.sum_le_sum hterm).trans hsumX.le), fun heq => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, 0 < T.basis.coord i P := by
    by_contra h
    push Not at h
    have : ∑ i, T.basis.coord i P ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  have hdi : dist (T.pts i) Q = X := by
    by_contra hne
    have hlt : dist (T.pts i) Q < X := lt_of_le_of_ne (vertex_bound T hX i hQ).1 hne
    have := Finset.sum_lt_sum hterm ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt hi⟩
    linarith
  rcases (vertex_bound T hX i hQ).2 hdi with h | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩
end EquilateralBound
open EquilateralBound in
theorem equilateralbound (T : Tri) {X : ℝ} (hX : ∀ i j, i ≠ j → dist (T.pts i) (T.pts j) = X)
    {P Q : Plane} (hPQ : segment ℝ P Q ⊆ T.carrier) :
    dist P Q ≤ X ∧ (dist P Q = X → ∃ i j, i ≠ j ∧ P = T.pts i ∧ Q = T.pts j) := by
  have hP := hPQ (left_mem_segment ℝ P Q)
  have hQ := hPQ (right_mem_segment ℝ P Q)
  refine ⟨(point_bound T hX hP hQ).1, fun heq => ?_⟩
  obtain ⟨j, rfl⟩ := (point_bound T hX hP hQ).2 heq
  obtain ⟨i, rfl⟩ := (point_bound T hX hQ hP).2 (by rw [dist_comm]; exact heq)
  refine ⟨i, j, fun hij => ?_, rfl, rfl⟩
  have hXpos : 0 < X := by
    rw [← hX 0 1 (by decide)]; exact dist_pos.mpr (T.indep.injective.ne (by decide))
  rw [hij, dist_self] at heq
  linarith
end TriangleTiling.Equilateral
end

section
namespace TriangleTiling.Equilateral
theorem int_sides {a b c : ℝ} {A' B' C' : ℕ} (hC' : 0 < C') (ha : a * C' = c * A')
    (hb : b * C' = c * B') :
    ∃ A B C : ℕ, 0 < C ∧ Nat.gcd (Nat.gcd A B) C = 1 ∧ a * C = c * A ∧ b * C = c * B := by
  set g := Nat.gcd (Nat.gcd A' B') C'
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hC'
  have hgA : g ∣ A' := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgB : g ∣ B' := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hgC : g ∣ C' := Nat.gcd_dvd_right _ _
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  refine ⟨A' / g, B' / g, C' / g, Nat.div_pos (Nat.le_of_dvd hC' hgC) hg, ?_, ?_, ?_⟩
  · rw [Nat.gcd_div hgA hgB, Nat.gcd_div (Nat.gcd_dvd_left _ _) hgC, Nat.div_self hg]
  · rw [Nat.cast_div hgC hgR, Nat.cast_div hgA hgR, mul_div_assoc', mul_div_assoc', ha]
  · rw [Nat.cast_div hgC hgR, Nat.cast_div hgB hgR, mul_div_assoc', mul_div_assoc', hb]
end TriangleTiling.Equilateral
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry MeasureTheory
noncomputable def heron16 (a b c : ℝ) : ℝ :=
  2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 - a ^ 4 - b ^ 4 - c ^ 4
theorem dist_sq_plane (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
theorem four_detTri_sq (T : Tri) :
    4 * Erdos634.AreaDet.detTri T ^ 2 =
      heron16 (dist (T.pts 1) (T.pts 2)) (dist (T.pts 2) (T.pts 0)) (dist (T.pts 0) (T.pts 1)) := by
  rw [Erdos634.AreaDet.detTri_eq, heron16]
  have e0 := dist_sq_plane (T.pts 1) (T.pts 2)
  have e1 := dist_sq_plane (T.pts 2) (T.pts 0)
  have e2 := dist_sq_plane (T.pts 0) (T.pts 1)
  have q : ∀ x : ℝ, x ^ 4 = (x ^ 2) ^ 2 := fun x => by ring
  simp only [q, e0, e1, e2]
  simp only [PiLp.sub_apply]
  ring
theorem area_heron {N : ℕ} (D : CongruentDissection N) :
    (N : ℝ) ^ 2 * heron16 (dist (D.model.pts 1) (D.model.pts 2))
        (dist (D.model.pts 2) (D.model.pts 0)) (dist (D.model.pts 0) (D.model.pts 1)) =
      heron16 (dist (D.target.pts 1) (D.target.pts 2))
        (dist (D.target.pts 2) (D.target.pts 0)) (dist (D.target.pts 0) (D.target.pts 1)) := by
  have hv := Erdos634.CongruentArea.congruentDissection_volume_target D
  rw [Erdos634.AreaDet.volume_eq_det_mul, Erdos634.AreaDet.volume_eq_det_mul] at hv
  have hM := D.model.volume_pos
  rw [Erdos634.AreaDet.volume_eq_det_mul] at hM
  have hc0 : volume Erdos634.AreaDet.stdCarrier ≠ 0 := by
    intro h; rw [h, mul_zero] at hM; exact lt_irrefl _ hM
  have hct : volume Erdos634.AreaDet.stdCarrier ≠ ⊤ :=
    (Erdos634.AreaDet.isCompact_stdCarrier.measure_lt_top).ne
  rw [← mul_assoc] at hv
  have h2 := (ENNReal.mul_left_inj hc0 hct).1 hv
  have h3 : ENNReal.ofReal |Erdos634.AreaDet.detTri D.target| =
      ENNReal.ofReal ((N : ℝ) * |Erdos634.AreaDet.detTri D.model|) := by
    rw [h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have h4 := (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (by positivity)).1 h3
  rw [← four_detTri_sq, ← four_detTri_sq]
  have : Erdos634.AreaDet.detTri D.target ^ 2 =
      ((N : ℝ) * |Erdos634.AreaDet.detTri D.model|) ^ 2 := by
    rw [← h4, sq_abs]
  rw [this, mul_pow, sq_abs]; ring
end TriangleTiling
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
def TileSides (α β γ a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    D.model.angleAt (σ 0) = α ∧ D.model.angleAt (σ 1) = β ∧ D.model.angleAt (σ 2) = γ ∧
    D.model.oppLen (σ 0) = a ∧ D.model.oppLen (σ 1) = b ∧ D.model.oppLen (σ 2) = c
noncomputable def circumdiam (T : Tri) : ℝ := T.oppLen 0 / Real.sin (T.angleAt 0)
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry
theorem tri_angle_lt_pi (T : Tri) (k : Fin 3) : T.angleAt k < Real.pi := by
  have hs := T.angleAt_sum
  have h0 := T.angleAt_pos' 0
  have h1 := T.angleAt_pos' 1
  have h2 := T.angleAt_pos' 2
  fin_cases k <;> simp <;> linarith
theorem tri_sin_pos (T : Tri) (k : Fin 3) : 0 < Real.sin (T.angleAt k) :=
  Real.sin_pos_of_pos_of_lt_pi (T.angleAt_pos' k) (tri_angle_lt_pi T k)
theorem circumdiam_pos (T : Tri) : 0 < circumdiam T :=
  div_pos (T.oppLen_pos 0) (tri_sin_pos T 0)
theorem lawsin (T : Tri) (k : Fin 3) : T.oppLen k = circumdiam T * Real.sin (T.angleAt k) := by
  have hs0 := (tri_sin_pos T 0).ne'
  unfold circumdiam
  rw [div_mul_eq_mul_div, eq_div_iff hs0]
  have l0 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 0
  have l2 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 2
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · ring
  · change Real.sin (T.angleAt 1) * T.oppLen 0 = Real.sin (T.angleAt 0) * T.oppLen 1 at l0
    linarith
  · change Real.sin (T.angleAt 0) * T.oppLen 2 = Real.sin (T.angleAt 2) * T.oppLen 0 at l2
    linarith
theorem heron_sin (T : Tri) :
    heron16 (T.oppLen 0) (T.oppLen 1) (T.oppLen 2)
      = 4 * (T.oppLen 1 * T.oppLen 2 * Real.sin (T.angleAt 0)) ^ 2 := by
  have lc := EuclideanGeometry.law_cos (T.pts 1) (T.pts 0) (T.pts 2)
  have e0 : T.oppLen 0 = dist (T.pts 1) (T.pts 2) := rfl
  have e1 : T.oppLen 1 = dist (T.pts 2) (T.pts 0) := rfl
  have e2 : T.oppLen 2 = dist (T.pts 0) (T.pts 1) := rfl
  have ea : T.angleAt 0 = EuclideanGeometry.angle (T.pts 1) (T.pts 0) (T.pts 2) := rfl
  rw [dist_comm (T.pts 1) (T.pts 0), dist_comm (T.pts 2) (T.pts 0)] at lc
  rw [e0, e1, e2, ea, dist_comm (T.pts 2) (T.pts 0)]
  have hsc := Real.sin_sq_add_cos_sq (EuclideanGeometry.angle (T.pts 1) (T.pts 0) (T.pts 2))
  unfold heron16
  have hx : dist (T.pts 1) (T.pts 2) ^ 2 = dist (T.pts 0) (T.pts 1) ^ 2 + dist (T.pts 0) (T.pts 2) ^ 2
      - 2 * dist (T.pts 0) (T.pts 1) * dist (T.pts 0) (T.pts 2)
        * Real.cos (EuclideanGeometry.angle (T.pts 1) (T.pts 0) (T.pts 2)) := by nlinarith [lc]
  rw [show dist (T.pts 1) (T.pts 2) ^ 4 = (dist (T.pts 1) (T.pts 2) ^ 2) ^ 2 by ring, hx]
  linear_combination (-4 * dist (T.pts 0) (T.pts 1) ^ 2 * dist (T.pts 0) (T.pts 2) ^ 2) * hsc
theorem area_sines {N : ℕ} (D : CongruentDissection N) :
    (N : ℝ) * (circumdiam D.model ^ 2 * (Real.sin (D.model.angleAt 0) *
        Real.sin (D.model.angleAt 1) * Real.sin (D.model.angleAt 2)))
      = circumdiam D.target ^ 2 * (Real.sin (D.target.angleAt 0) *
        Real.sin (D.target.angleAt 1) * Real.sin (D.target.angleAt 2)) := by
  have h := area_heron D
  change (N : ℝ) ^ 2 * heron16 (D.model.oppLen 0) (D.model.oppLen 1) (D.model.oppLen 2)
    = heron16 (D.target.oppLen 0) (D.target.oppLen 1) (D.target.oppLen 2) at h
  rw [heron_sin, heron_sin] at h
  have key : ∀ T : Tri, T.oppLen 1 * T.oppLen 2 * Real.sin (T.angleAt 0)
      = circumdiam T ^ 2 * (Real.sin (T.angleAt 0) * Real.sin (T.angleAt 1) *
        Real.sin (T.angleAt 2)) := by
    intro T; rw [lawsin T 1, lawsin T 2]; ring
  rw [key, key] at h
  have p1 : 0 < circumdiam D.model ^ 2 * (Real.sin (D.model.angleAt 0) *
      Real.sin (D.model.angleAt 1) * Real.sin (D.model.angleAt 2)) := by
    have := circumdiam_pos D.model
    have := tri_sin_pos D.model 0; have := tri_sin_pos D.model 1; have := tri_sin_pos D.model 2
    positivity
  have p2 : 0 < circumdiam D.target ^ 2 * (Real.sin (D.target.angleAt 0) *
      Real.sin (D.target.angleAt 1) * Real.sin (D.target.angleAt 2)) := by
    have := circumdiam_pos D.target
    have := tri_sin_pos D.target 0; have := tri_sin_pos D.target 1; have := tri_sin_pos D.target 2
    positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set X := circumdiam D.model ^ 2 * (Real.sin (D.model.angleAt 0) *
      Real.sin (D.model.angleAt 1) * Real.sin (D.model.angleAt 2))
  set Y := circumdiam D.target ^ 2 * (Real.sin (D.target.angleAt 0) *
      Real.sin (D.target.angleAt 1) * Real.sin (D.target.angleAt 2))
  have h' : ((N : ℝ) * X) ^ 2 = Y ^ 2 := by linear_combination h / 4
  exact (sq_eq_sq₀ (by positivity) p2.le).mp h'
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry EuclideanGeometry
theorem oppLen_relabel (T : Tri) (ρ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (T.relabel ρ).oppLen k = T.oppLen (ρ k) := by
  unfold Tri.oppLen
  simp only [Tri.relabel_pts]
  have : ∀ ρ : Equiv.Perm (Fin 3), ∀ k, (ρ (k + 1) = ρ k + 1 ∧ ρ (k + 2) = ρ k + 2) ∨
      (ρ (k + 1) = ρ k + 2 ∧ ρ (k + 2) = ρ k + 1) := by decide
  rcases this ρ k with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
  exact dist_comm _ _
theorem angleAt_relabel (T : Tri) (ρ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (T.relabel ρ).angleAt k = T.angleAt (ρ k) := by
  unfold Tri.angleAt cornerAngle
  simp only [Tri.relabel_pts]
  have : ∀ ρ : Equiv.Perm (Fin 3), ∀ k, (ρ (k + 1) = ρ k + 1 ∧ ρ (k + 2) = ρ k + 2) ∨
      (ρ (k + 1) = ρ k + 2 ∧ ρ (k + 2) = ρ k + 1) := by decide
  rcases this ρ k with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
  exact EuclideanGeometry.angle_comm _ _ _
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry EuclideanGeometry Set
theorem sides_ne_of_angles_ne {N : ℕ} (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hT : TileSides D α β γ a b c) (hαβ : α ≠ β) : a ≠ b := by
  obtain ⟨σ, h0, h1, -, l0, l1, -⟩ := hT
  intro hab
  set T := D.model.relabel σ
  have e0 : T.angleAt 0 = α := by rw [angleAt_relabel]; exact h0
  have e1 : T.angleAt 1 = β := by rw [angleAt_relabel]; exact h1
  have d : dist (T.pts 2) (T.pts 0) = dist (T.pts 2) (T.pts 1) := by
    have q1 : T.oppLen 1 = b := by rw [oppLen_relabel]; exact l1
    have q0 : T.oppLen 0 = a := by rw [oppLen_relabel]; exact l0
    have : dist (T.pts 2) (T.pts 0) = b := q1
    rw [this, ← hab, ← q0]; exact dist_comm _ _
  apply hαβ
  rw [← e0, ← e1]
  show ∠ (T.pts 1) (T.pts 0) (T.pts 2) = ∠ (T.pts 2) (T.pts 1) (T.pts 0)
  rw [EuclideanGeometry.angle_comm]
  exact EuclideanGeometry.angle_eq_angle_of_dist_eq d
end TriangleTiling.ThreeAlpha
end

section
open scoped Classical
namespace TriangleTiling.Equilateral
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.TheoremPConditional TriangleTiling.ThreeAlpha
open Erdos634.Draft.LaczFormal.Graph (V2 toV2 TriStep)
variable {N M : ℕ}
theorem sum_eq_countP {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ L : List ℝ, (∀ x ∈ L, x = a ∨ x = b ∨ x = c) →
      L.sum = (L.countP (fun x => decide (x = a)) : ℝ) * a + (L.countP (fun x => decide (x = b)) : ℝ) * b +
        (L.countP (fun x => decide (x = c)) : ℝ) * c
  | [], _ => by simp
  | x :: L, h => by
    have ih := sum_eq_countP hab hac hbc L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases h x List.mem_cons_self with rfl | rfl | rfl <;>
      simp [List.countP_cons, hab, hac, hbc, hab.symm, hac.symm, hbc.symm, ih] <;> ring
theorem equilateral_sides (T : Tri) (hP : ∀ k, T.angleAt k = Real.pi / 3) :
    ∀ j : Fin 3, dist (T.pts j) (T.pts (j + 1)) = dist (T.pts 0) (T.pts 1) := by
  have hs : Real.sin (Real.pi / 3) ≠ 0 := by rw [Real.sin_pi_div_three]; positivity
  have e : ∀ i j, T.oppLen j = T.oppLen i := fun i j => by
    have := T.lawSin i j
    rw [hP i, hP j] at this
    exact mul_left_cancel₀ hs this
  intro j
  fin_cases j
  · rfl
  · exact e 2 0
  · exact e 2 1
end TriangleTiling.Equilateral
end

section
open scoped Classical
namespace TriangleTiling.Equilateral
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.RG
open Erdos634.Draft.LaczFormal.Graph (V2 toV2 TriStep crs dt Par)
namespace Walks
variable {N : ℕ}
theorem fin3_adj {kk f : Fin 3} (h : f ≠ kk) : f = kk + 1 ∨ kk = f + 1 := by
  revert kk f; decide
end Walks
end TriangleTiling.Equilateral
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry EuclideanGeometry Set
variable {N : ℕ} (D : CongruentDissection N)
theorem tileSides_swap {α β γ a b c : ℝ} (h : TileSides D α β γ a b c) :
    TileSides D β α γ b a c := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := h
  refine ⟨(Equiv.swap 0 1).trans σ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simpa
end TriangleTiling.ThreeAlpha
end

section
open scoped Classical
namespace TriangleTiling.Equilateral
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.TheoremPConditional TriangleTiling.ThreeAlpha
open Erdos634.Draft.LaczFormal.Graph (V2 toV2 TriStep crs dt Par)
variable {N : ℕ}
namespace NP120
theorem equi_dist (T : Tri) (heq : ∀ j : Fin 3, dist (T.pts j) (T.pts (j + 1)) = dist (T.pts 0) (T.pts 1))
    {u v : Fin 3} (h : u ≠ v) : dist (T.pts u) (T.pts v) = dist (T.pts 0) (T.pts 1) := by
  rcases Walks.fin3_adj (Ne.symm h) with e | e
  · rw [e]; exact heq u
  · rw [e, dist_comm]; exact heq v
theorem facts (D : CongruentDissection N) (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    {α β a b c : ℝ} (hT : TileSides D α β (2 * Real.pi / 3) a b c) (hα : IrrPi α) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ c ^ 2 = a ^ 2 + b ^ 2 + a * b ∧
      D.target.oppLen 0 ^ 2 = N * a * b := by
  have hπ := Real.pi_pos
  have hsum : α + β + 2 * Real.pi / 3 = Real.pi := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [← h0, ← h1, ← h2, e, D.model.angleAt_sum]
  have hγα : 2 * Real.pi / 3 ≠ α := fun e => hα ⟨2 / 3, by rw [← e]; push_cast; ring⟩
  have hγβ : 2 * Real.pi / 3 ≠ β := fun e => hα ⟨-1 / 3, by push_cast; linarith⟩
  have hαβ : α ≠ β := fun e => hα ⟨1 / 6, by push_cast; linarith⟩
  have hab : a ≠ b := sides_ne_of_angles_ne D hT hαβ
  have hcb : c ≠ b := by
    refine sides_ne_of_angles_ne D (α := 2 * Real.pi / 3) (β := β) (γ := α) (a := c) (b := b) (c := a) ?_ hγβ
    obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
    refine ⟨σ * Equiv.swap 0 2, ?_⟩
    simp only [Equiv.Perm.mul_apply, swap02_0, swap02_1, swap02_2]
    exact ⟨h2, h1, h0, l2, l1, l0⟩
  have hca : c ≠ a := by
    refine sides_ne_of_angles_ne D (α := 2 * Real.pi / 3) (β := α) (γ := β) (a := c) (b := a) (c := b) ?_ hγα
    obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
    refine ⟨σ * Equiv.swap 0 2 * Equiv.swap 1 2, ?_⟩
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    simp [Fin.ext_iff]
    exact ⟨h2, h0, h1, l2, l0, l1⟩
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  have pa : 0 < a := l0 ▸ D.model.oppLen_pos _
  have pb : 0 < b := l1 ▸ D.model.oppLen_pos _
  have pc : 0 < c := l2 ▸ D.model.oppLen_pos _
  have hcos : c ^ 2 = a ^ 2 + b ^ 2 + a * b := by
    have hl := D.model.lawCos_perm σ
    rw [l0, l1, l2, h2, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three] at hl
    linarith
  have harea : D.target.oppLen 0 ^ 2 = N * a * b := by
    have hs3 : 0 < Real.sin (Real.pi / 3) := by rw [Real.sin_pi_div_three]; positivity
    have hsγ : Real.sin (2 * Real.pi / 3) = Real.sin (Real.pi / 3) := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub]
    have h := area_sines D
    have hprod : Real.sin (D.model.angleAt 0) * Real.sin (D.model.angleAt 1) *
        Real.sin (D.model.angleAt 2) = Real.sin α * Real.sin β * Real.sin (2 * Real.pi / 3) := by
      have e := Equiv.prod_comp σ (fun k => Real.sin (D.model.angleAt k))
      simp only [Fin.prod_univ_three] at e
      rw [← e, h0, h1, h2]
    rw [hprod, hP 0, hP 1, hP 2] at h
    have ha' := lawsin D.model (σ 0)
    have hb' := lawsin D.model (σ 1)
    rw [l0, h0] at ha'
    rw [l1, h1] at hb'
    have hX := lawsin D.target 0
    rw [hP 0] at hX
    rw [hsγ] at h
    have : ((N : ℝ) * a * b - D.target.oppLen 0 ^ 2) * Real.sin (Real.pi / 3) = 0 := by
      rw [ha', hb', hX]; linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · linarith
  exact ⟨pa, pb, pc, hab, hca, hcb, hcos, harea⟩
theorem setup (D : CongruentDissection N) (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    {α β a b c : ℝ} (hT : TileSides D α β (2 * Real.pi / 3) a b c) (hα : IrrPi α) (hN0 : 0 < N) :
    ∃ (T : PolyTiling N 3) (idx : Fin N → Equiv.Perm (Fin 3)),
      (∀ i, T.C.toRegionDissection.tile i = D.tile i) ∧ RegularPQ T.C ∧
      (∀ i v, T.C.model.angleAt (idx i v) = (T.C.tile i).angleAt v) ∧
      (∀ i k k', dist ((T.C.tile i).pts k) ((T.C.tile i).pts k') =
        dist (T.C.model.pts (idx i k)) (T.C.model.pts (idx i k'))) ∧
      slen T.C 0 = a ∧ slen T.C 1 = b ∧ slen T.C 2 = c ∧
      T.C.model.angleAt 2 = 2 * Real.pi / 3 ∧ (∀ i, T.P.angle i = Real.pi / 3) ∧
      (∀ i, T.P.side i = D.target.oppLen 0) ∧ c ≤ D.target.oppLen 0 := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  set X := D.target.oppLen 0 with hXdef
  have heq := equilateral_sides D.target hP
  obtain ⟨P, hPc, τ, hPa, hPv⟩ := exists_convpoly_of_tri' D.target
  obtain ⟨T, hTC, hTP⟩ : ∃ T : PolyTiling N 3, T.C = relabel D.toRegion σ ∧ T.P = P :=
    ⟨⟨relabel D.toRegion σ, P, by rw [hPc]; rfl⟩, rfl, rfl⟩
  have hang : ∀ j, Erdos634.TilePlacement.angleAt T.C.model j = D.model.angleAt (σ j) := by
    intro j; rw [hTC, relabel_angleAt]; rfl
  have hslen : ∀ k, slen D.toRegion k = D.model.oppLen k := by
    intro k; fin_cases k <;> rfl
  have hsl : ∀ j, slen T.C j = D.model.oppLen (σ j) := by
    intro j; rw [hTC, relabel_slen, hslen]
  have sa : slen T.C 0 = a := by rw [hsl, l0]
  have sb : slen T.C 1 = b := by rw [hsl, l1]
  have sc : slen T.C 2 = c := by rw [hsl, l2]
  have hPang : ∀ i, T.P.angle i = Real.pi / 3 := fun i => by
    rw [hTP, hPa, hP]
  have hγT : Erdos634.TilePlacement.angleAt T.C.model 2 = 2 * Real.pi / 3 := by rw [hang 2, h2]
  have hαT : ¬ ∃ r : ℚ, Erdos634.TilePlacement.angleAt T.C.model 0 = (r : ℝ) * Real.pi := by rw [hang 0, h0]; exact hα
  have hreg : RegularPQ T.C := regular_of_irr T hγT hαT hPang
  obtain ⟨idx, hA, hcnt⟩ := id hreg
  have hidx := idx_dist_of_angle T.C idx hA
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have htile : ∀ i, T.C.toRegionDissection.tile i = D.tile i := fun i => by rw [hTC]; rfl
  have hX : ∀ u v : Fin 3, u ≠ v → dist (D.target.pts u) (D.target.pts v) = X := by
    intro u v huv
    rw [equi_dist D.target heq huv, hXdef]
    show _ = dist (D.target.pts (0 + 1)) (D.target.pts (0 + 2))
    exact (heq 1).symm
  have hside : ∀ i, T.P.side i = X := by
    intro i
    show dist (T.P.v i) (T.P.v (i + 1)) = X
    rw [hTP, hPv, hPv]
    exact hX _ _ (fun e => by
      have := τ.injective e
      revert this; generalize i = i'; revert i'; decide)
  have hcX : c ≤ X := by
    have i0 : Fin N := ⟨0, hN0⟩
    set k := (idx i0).symm 0
    set k' := (idx i0).symm 1
    have hd : dist ((D.tile i0).pts k) ((D.tile i0).pts k') = c := by
      have := hidx i0 k k'
      simp only [k, k', Equiv.apply_symm_apply] at this
      rw [← sc, ← htile]; exact this
    have hseg : segment ℝ ((D.tile i0).pts k) ((D.tile i0).pts k') ⊆ D.target.carrier :=
      ((convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (Set.mem_range_self k))
        (subset_convexHull ℝ _ (Set.mem_range_self k'))).trans (tile_subset_target D.toDissection i0)
    rw [← hd]
    exact (equilateralbound D.target hX hseg).1
  exact ⟨T, idx, htile, hreg, hA, hidx, sa, sb, sc, hγT, hPang, hside, hcX⟩
theorem dvd_ab (D : CongruentDissection N) (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    {α β a b c : ℝ} (hT : TileSides D α β (2 * Real.pi / 3) a b c) (hα : IrrPi α)
    (hN : N.Prime) {A B C : ℕ} {μ : ℝ} (hμ : 0 < μ) (ha : a = μ * A) (hb : b = μ * B)
    (hc : c = μ * C) : N ∣ A * B := by
  obtain ⟨pa, pb, pc, hab, hca, hcb, hcos, harea⟩ := facts D hP hT hα
  obtain ⟨T, idx, htile, hreg, hA, hidx, sa, sb, sc, hγT, hPang, hside, -⟩ := setup D hP hT hα hN.pos
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  obtain ⟨L, -, -, W, -⟩ := edge_data T.C T.P T.region_eq 0
  have hmem : ∀ x ∈ L.map (fun e => dist e.2.1 e.2.2), x = slen T.C 0 ∨ x = slen T.C 1 ∨ x = slen T.C 2 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact side_len_mem T.C idx hidx (walkT_mem_step W e he)
  set ls := L.map (fun e => dist e.2.1 e.2.2) with hls
  set p := ls.countP (fun x => decide (x = slen T.C 0))
  set q := ls.countP (fun x => decide (x = slen T.C 1))
  set r := ls.countP (fun x => decide (x = slen T.C 2))
  have hsumL : D.target.oppLen 0 = p * a + q * b + r * c := by
    have hq := sum_eq_countP (by rwa [sa, sb]) (by rw [sa, sc]; exact hca.symm)
      (by rw [sb, sc]; exact hcb.symm) ls hmem
    calc D.target.oppLen 0 = T.P.side 0 := (hside 0).symm
      _ = ls.sum := (walkT_dist_sum W).symm
      _ = _ := hq
      _ = p * a + q * b + r * c := by simp only [p, q, r, sa, sb, sc]
  obtain ⟨Xn, hXn⟩ : ∃ Xn : ℕ, Xn = p * A + q * B + r * C := ⟨_, rfl⟩
  have hXnR : D.target.oppLen 0 = μ * Xn := by rw [hsumL, ha, hb, hc, hXn]; push_cast; ring
  have hXn2 : Xn ^ 2 = N * (A * B) := by
    have : ((Xn : ℝ)) ^ 2 = N * (A * B) := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hμ.ne')
      have := harea
      rw [hXnR, ha, hb] at this
      linear_combination this
    exact_mod_cast this
  have hNX : N ∣ Xn := hN.dvd_of_dvd_pow (n := 2) (by rw [hXn2]; exact dvd_mul_right _ _)
  obtain ⟨k, hk⟩ := hNX
  have : N * (A * B) = N * (N * k ^ 2) := by rw [← hXn2, hk]; ring
  exact ⟨k ^ 2, Nat.eq_of_mul_eq_mul_left hN.pos this⟩
def _root_.OMACORE {N : ℕ} (D : CongruentDissection N) : Prop := ∀ {α β a b c : ℝ},
    (∀ k, D.target.angleAt k = Real.pi / 3) → TileSides D α β (2 * Real.pi / 3) a b c → IrrPi α →
      N.Prime → 3 < N → ∀ {A B C : ℕ} {μ : ℝ}, 0 < μ → a = μ * A → b = μ * B → c = μ * C →
        Nat.gcd (Nat.gcd A B) C = 1 → N ∣ A → False
theorem core (D : CongruentDissection N) [hCo : Fact (OMACORE D)] (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    {α β a b c : ℝ} (hT : TileSides D α β (2 * Real.pi / 3) a b c) (hα : IrrPi α)
    (hN : N.Prime) (hN3 : 3 < N) {A B C : ℕ} {μ : ℝ} (hμ : 0 < μ) (ha : a = μ * A) (hb : b = μ * B)
    (hc : c = μ * C) (hgcd : Nat.gcd (Nat.gcd A B) C = 1) (hNA : N ∣ A) : False :=
  hCo.out hP hT hα hN hN3 hμ ha hb hc hgcd hNA
end NP120
def _root_.OMARAT120 {N : ℕ} (D : CongruentDissection N) : Prop := ∀ {α β a b c : ℝ},
    (∀ k, D.target.angleAt k = Real.pi / 3) → TileSides D α β (2 * Real.pi / 3) a b c → IrrPi α →
      ∃ p₁ q₁ p₂ q₂ : ℕ, 0 < p₁ ∧ 0 < p₂ ∧ a / c = (q₂ : ℝ) / p₂ ∧ b / c = (q₁ : ℝ) / p₁
open NP120 in
theorem notprime120 (D : CongruentDissection N) [hRat : Fact (OMARAT120 D)] [hCoF : Fact (OMACORE D)] {α β a b c : ℝ}
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (2 * Real.pi / 3) a b c) (hα : IrrPi α) : ¬ N.Prime := by
  intro hN
  obtain ⟨pa, pb, pc, hab, hca, hcb, hcos, harea⟩ := facts D hP hT hα
  have hβ : IrrPi β := by
    have hsum : α + β + 2 * Real.pi / 3 = Real.pi := by
      obtain ⟨σ, h0, h1, h2, -⟩ := hT
      have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
      simp only [Fin.sum_univ_three] at e
      rw [← h0, ← h1, ← h2, e, D.model.angleAt_sum]
    rintro ⟨r, hr⟩; apply hα
    exact ⟨1 / 3 - r, by push_cast; linarith⟩
  by_cases hN3 : 3 < N
  swap
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcX⟩ := setup D hP hT hα hN.pos
    have hN' : (N : ℝ) ≤ 3 := by exact_mod_cast not_lt.mp hN3
    have hc2 : c ^ 2 ≤ D.target.oppLen 0 ^ 2 := pow_le_pow_left₀ pc.le hcX 2
    have hab' : 0 < (a - b) ^ 2 := by positivity
    nlinarith [mul_pos pa pb]
  obtain ⟨p₁, q₁, p₂, q₂, hp₁, hp₂, ha, hb⟩ := hRat.out hP hT hα
  have hp₁R : (0 : ℝ) < p₁ := by exact_mod_cast hp₁
  have hp₂R : (0 : ℝ) < p₂ := by exact_mod_cast hp₂
  rw [div_eq_div_iff pc.ne' hp₂R.ne'] at ha
  rw [div_eq_div_iff pc.ne' hp₁R.ne'] at hb
  obtain ⟨A, B, C, hC0, hgcd, hA, hB⟩ := int_sides (a := a) (b := b) (c := c)
    (A' := q₂ * p₁) (B' := q₁ * p₂) (C' := p₁ * p₂) (Nat.mul_pos hp₁ hp₂)
    (by push_cast; linear_combination (p₁ : ℝ) * ha) (by push_cast; linear_combination (p₂ : ℝ) * hb)
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC0
  set μ := c / C with hμ
  have hμ0 : 0 < μ := div_pos pc hCR
  have eA : a = μ * A := by rw [hμ]; field_simp; linarith
  have eB : b = μ * B := by rw [hμ]; field_simp; linarith
  have eC : c = μ * C := by rw [hμ]; field_simp
  rcases (Nat.Prime.dvd_mul hN).mp (dvd_ab D hP hT hα hN hμ0 eA eB eC) with hNA | hNB
  · exact core D hP hT hα hN hN3 hμ0 eA eB eC hgcd hNA
  · exact core D hP (TriangleTiling.ThreeAlpha.tileSides_swap D hT) hβ hN hN3 hμ0 eB eA eC
      (by rwa [Nat.gcd_comm B A]) hNB
end TriangleTiling.Equilateral
end


/-! ## Bridge: cut data (Mathlib triangles) to a Bonfioli congruent dissection -/

namespace OMA.E634S

open Erdos634.Geometry

abbrev Tr := Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))

/-- The Bonfioli triangle with the same vertices as a Mathlib triangle. -/
def ofS (s : Tr) : Tri := ⟨s.points, s.independent⟩

theorem carrier_ofS (s : Tr) : (ofS s).carrier = s.closedInterior := by
  simp [Tri.carrier, ofS]

/-- The vertices of a triangle in the plane, as an affine basis. -/
noncomputable def basisOf (s : Tr) : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨s.points, s.independent,
    s.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)⟩

theorem basisOf_coe (s : Tr) : ⇑(basisOf s) = s.points := rfl

theorem interior_carrier_subset (s : Tr) : interior (ofS s).carrier ⊆ s.interior := by
  intro x hx
  have hx' : x ∈ interior (convexHull ℝ (Set.range (basisOf s))) := by
    rw [basisOf_coe]; exact hx
  rw [AffineBasis.interior_convexHull] at hx'
  have hpos : ∀ i, 0 < (basisOf s).coord i x := hx'
  have hsum : ∑ i, (basisOf s).coord i x = 1 := (basisOf s).sum_coord_apply_eq_one x
  have hx_eq : Finset.univ.affineCombination ℝ s.points (fun i => (basisOf s).coord i x) = x := by
    have := (basisOf s).affineCombination_coord_eq_self x
    rwa [basisOf_coe] at this
  rw [← hx_eq, Affine.Simplex.affineCombination_mem_interior_iff hsum]
  intro i
  refine ⟨hpos i, ?_⟩
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  rw [Fin.sum_univ_three] at hsum
  fin_cases i <;> simp <;> linarith

theorem congruent_of_cong {s t : Tr} (h : Congruent s.points t.points) : (ofS s).Congruent (ofS t) := by
  apply Erdos634.SssCongruent.congruent_of_dist
  intro i j
  have := h i j
  simp only [edist_dist] at this
  exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg dist_nonneg).mp this

/-- The congruent dissection built from cut data, with model the tile t. -/
noncomputable def mk {p : ℕ} (T : Tr) (Ts : Fin p → Tr)
    (hc : ∀ i j, Congruent (Ts i).points (Ts j).points)
    (hd : Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior))
    (hu : ⋃ i, (Ts i).closedInterior = T.closedInterior) (t : Fin p) : CongruentDissection p :=
  { target := ofS T
    tile := fun i => ofS (Ts i)
    covers := by simp only [carrier_ofS]; exact hu
    interiors_disjoint := fun i j hij =>
      (hd hij).mono (interior_carrier_subset _) (interior_carrier_subset _)
    model := ofS (Ts t)
    tiles_congruent := fun i => congruent_of_cong (hc i t) }

theorem target_angleAt {p : ℕ} (T : Tr) (Ts : Fin p → Tr)
    (hc : ∀ i j, Congruent (Ts i).points (Ts j).points)
    (hd : Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior))
    (hu : ⋃ i, (Ts i).closedInterior = T.closedInterior) (t : Fin p) (k : Fin 3) :
    (mk T Ts hc hd hu t).target.angleAt k =
      EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) := rfl

theorem model_angleAt {p : ℕ} (T : Tr) (Ts : Fin p → Tr)
    (hc : ∀ i j, Congruent (Ts i).points (Ts j).points)
    (hd : Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior))
    (hu : ⋃ i, (Ts i).closedInterior = T.closedInterior) (t : Fin p) (k : Fin 3) :
    (mk T Ts hc hd hu t).model.angleAt k =
      EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) := rfl

end OMA.E634S


namespace OMA.E634H

theorem comp_vec {f : Fin 3 → ℝ} {σ : Equiv.Perm (Fin 3)} {x y z : ℝ} (h0 : f (σ 0) = x)
    (h1 : f (σ 1) = y) (h2 : f (σ 2) = z) : f ∘ σ = ![x, y, z] := by
  funext k; fin_cases k <;> simp [h0, h1, h2]

theorem vec_comp {f : Fin 3 → ℝ} {σ : Equiv.Perm (Fin 3)} {x y z : ℝ} (h : f ∘ σ = ![x, y, z]) :
    f (σ 0) = x ∧ f (σ 1) = y ∧ f (σ 2) = z :=
  ⟨by simpa using congrFun h 0, by simpa using congrFun h 1, by simpa using congrFun h 2⟩

theorem eq_vec {f : Fin 3 → ℝ} {x y z : ℝ} (h0 : f 0 = x) (h1 : f 1 = y) (h2 : f 2 = z) :
    f = ![x, y, z] := by
  funext k; fin_cases k <;> simp [h0, h1, h2]

theorem vec_eq {f : Fin 3 → ℝ} {x y z : ℝ} (h : f = ![x, y, z]) : f 0 = x ∧ f 1 = y ∧ f 2 = z :=
  ⟨by simp [h], by simp [h], by simp [h]⟩

end OMA.E634H


/-- theorem:notprime120 (an equilateral triangle is not tiled by a prime number of tiles (α, π/3 - α,
2π/3), α not in Q π), given the rationality of the tile and the core step (H1, H2 of the reduction). -/
theorem OMA.solution : OMA.R_erdos_634_R1_H2_R1_H1_R1_H3_R1.H3 := by
  intro p hp h3p T Ts hc hd hu t A B L hA hB hL hEq hR hCore α hα hBσ
  obtain rfl : A = _ := funext hA
  obtain rfl : B = _ := funext hB
  obtain rfl : L = _ := funext hL
  let D := OMA.E634S.mk T Ts hc hd hu t
  have hP : ∀ k : Fin 3, D.target.angleAt k = Real.pi / 3 := hEq
  haveI : Fact (OMARAT120 D) := ⟨by
    intro α' β a b c _ hT hα'
    obtain ⟨σ, h0, h1, h2, o0, o1, o2⟩ := hT
    have hsum := Erdos634.Draft.LaczFormal.angleAt_sum D.model
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [h0, h1, h2] at e
    have hβ : β = Real.pi / 3 - α' := by linarith
    subst hβ
    have hc : 0 < c := o2 ▸ D.model.oppLen_pos' _
    obtain ⟨⟨m, n, hm, hn, e1⟩, ⟨m', n', hm', hn', e2⟩⟩ :=
      hR α' a b c hα' ⟨σ, OMA.E634H.comp_vec h0 h1 h2, OMA.E634H.comp_vec o0 o1 o2⟩
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hmR' : (m' : ℝ) ≠ 0 := by exact_mod_cast hm'.ne'
    refine ⟨m', n', m, n, hm', hm, ?_, ?_⟩
    · rw [div_eq_div_iff hc.ne' hmR]; linarith
    · rw [div_eq_div_iff hc.ne' hmR']; linarith⟩
  haveI : Fact (OMACORE D) := ⟨by
    intro α' β a b c _ hT hα' _ _ A' B' C' μ hμ ha hb hc hg hNA
    obtain ⟨σ, h0, h1, h2, o0, o1, o2⟩ := hT
    exact hCore α' β a b c hα' ⟨σ, OMA.E634H.comp_vec h0 h1 h2, OMA.E634H.comp_vec o0 o1 o2⟩
      A' B' C' μ hμ ha hb hc hg hNA⟩
  obtain ⟨σ, hσ⟩ := hBσ
  obtain ⟨h0, h1, h2⟩ := OMA.E634H.vec_comp hσ
  exact TriangleTiling.Equilateral.notprime120 D hP ⟨σ, h0, h1, h2, rfl, rfl, rfl⟩ hα hp

