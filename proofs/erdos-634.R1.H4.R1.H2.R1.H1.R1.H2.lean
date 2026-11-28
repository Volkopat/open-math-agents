import OMAReductions.R_erdos_634_R1_H4_R1_H2_R1_H1_R1

/-!
# Erdos 634, step R1.H4.R1.H2.R1.H1.R1.H2: Beeson-Zhang Theorem 1.1 given Theorem 3.7

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
end Tri
structure Dissection (N : ℕ) where
  target : Tri
  tile : Fin N → Tri
  covers : (⋃ i, (tile i).carrier) = target.carrier
  interiors_disjoint :
    Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier)
namespace Dissection
variable {N : ℕ}
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
structure CongruentDissection (N : ℕ) extends Dissection N where
  model : Tri
  tiles_congruent : ∀ i, (tile i).Congruent model
namespace CongruentDissection
variable {N : ℕ}
end CongruentDissection
end Erdos634.Geometry
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
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
def Tri.TwoPiThreeData (T : Tri) (α a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = Real.pi / 3 - α ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = 2 * Real.pi / 3 ∧ T.oppLen (σ 2) = c
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
theorem smul_par {u v : V2} {c : ℝ} (hc : 0 < c) (hv : v ≠ 0) (h : u = (c * v.1, c * v.2)) : Par u v := by
  subst h
  refine ⟨?_, ?_⟩
  · unfold crs; ring
  · unfold dt
    have := nsq_pos hv
    unfold nsq at this
    nlinarith [mul_pos hc this]
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
def AtV (D : Dissection N) (V : Plane) : Type := {i : Fin N // V ∈ (D.tile i).carrier}
noncomputable instance (D : Dissection N) (V : Plane) : Fintype (AtV D V) := by
  classical unfold AtV; exact Subtype.fintype _
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
def extP (pT : V2) (p : AtV D V → V2) : Option (AtV D V) → V2
  | none => (-pT.1, -pT.2)
  | some s => p s
def extQ (pT : V2) (q : AtV D V → V2) : Option (AtV D V) → V2
  | none => pT
  | some s => q s
end Erdos634.Draft.LaczFormal.Graph
end

section
namespace Erdos634.Draft.LaczFormal.RegFan
def tT : ℕ → ℕ | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 2 | _ => 2
def tU : ℕ → ℕ | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 2 | 4 => 0 | _ => 1
def tW : ℕ → ℕ | 0 => 2 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 1 | _ => 0
def allFans : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (allFans k).flatMap (fun l => (List.range 6).map (fun x => x :: l))
theorem mem_allFans : ∀ (k : ℕ) (l : List ℕ), l.length = k → (∀ x ∈ l, x < 6) → l ∈ allFans k := by
  intro k
  induction k with
  | zero => intro l hl _; simp [List.length_eq_zero_iff.mp hl, allFans]
  | succ k ih =>
    intro l hl hlt
    match l, hl, hlt with
    | x :: t, hl, hlt =>
      have ht : t ∈ allFans k := ih t (by simpa using hl) (fun y hy => hlt y (List.mem_cons_of_mem _ hy))
      simp only [allFans, List.mem_flatMap, List.mem_map, List.mem_range]
      exact ⟨t, ht, x, hlt x (List.mem_cons_self ..), rfl⟩
def cnt (l : List ℕ) (j : ℕ) : ℕ := (l.filter (fun x => tT x == j)).length
def Lc (l : List ℕ) (i : ℕ) : ℕ := l.getD ((i + l.length - 1) % l.length) 0
def Rc (l : List ℕ) (i : ℕ) : ℕ := l.getD (i % l.length) 0
def gaEdge (l : List ℕ) (i : ℕ) : Bool := (tU (Lc l i) == 0) != (tW (Rc l i) == 0)
def gkEdge (l : List ℕ) (i : ℕ) : Bool :=
  tT (Lc l i) == 2 && tT (Rc l i) == 2 && tW (Lc l i) == 1 && tU (Rc l i) == 1
def incoming (l : List ℕ) : Bool :=
  (tW (l.getD 0 0) == 0 && tU (l.getD (l.length - 1) 0) != 0) ||
  (tU (l.getD (l.length - 1) 0) == 0 && tW (l.getD 0 0) != 0)
theorem impl_of_ok {a b : Bool} (h : (!a || b) = true) (ha : a = true) : b = true := by
  simpa [ha] using h
def piNormalHyp (l : List ℕ) : Bool := cnt l 0 == 1 && cnt l 1 == 1 && cnt l 2 == 1 && incoming l
def piNormalConcl (l : List ℕ) : Bool := (List.range 3).any (fun i => 1 ≤ i && gaEdge l i)
def piNormalOK (l : List ℕ) : Bool := !(piNormalHyp l) || piNormalConcl l
theorem pi_normal_check : (allFans 3).all piNormalOK = true := by decide +kernel
theorem pi_fan_normal (l : List ℕ) (hlen : l.length = 3) (hlt : ∀ x ∈ l, x < 6) (h : piNormalHyp l = true) :
    piNormalConcl l = true :=
  impl_of_ok ((List.all_eq_true.mp pi_normal_check) l (mem_allFans 3 l hlen hlt)) h
def pi003Hyp (l : List ℕ) : Bool := cnt l 0 == 0 && cnt l 1 == 0 && cnt l 2 == 3 && incoming l
def pi003Concl (l : List ℕ) : Bool := (List.range 3).any (fun i => 1 ≤ i && (gaEdge l i || gkEdge l i))
def pi003OK (l : List ℕ) : Bool := !(pi003Hyp l) || pi003Concl l
theorem pi003_check : (allFans 3).all pi003OK = true := by decide +kernel
theorem pi_fan_3gamma (l : List ℕ) (hlen : l.length = 3) (hlt : ∀ x ∈ l, x < 6) (h : pi003Hyp l = true) :
    pi003Concl l = true :=
  impl_of_ok ((List.all_eq_true.mp pi003_check) l (mem_allFans 3 l hlen hlt)) h
def code (t u w : ℕ) : ℕ := ((List.range 6).find? (fun x => tT x == t && tU x == u && tW x == w)).getD 0
end Erdos634.Draft.LaczFormal.RegFan
end

section
open Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
theorem code_spec (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    RegFan.tT (RegFan.code a b c) = a ∧ RegFan.tU (RegFan.code a b c) = b ∧ RegFan.tW (RegFan.code a b c) = c ∧
      RegFan.code a b c < 6 := by
  revert a b c; decide
def codeOf (σ : Equiv.Perm (Fin 3)) (k : Fin 3) (fl : Bool) : ℕ :=
  if fl then RegFan.code (σ k) (σ (k + 2)) (σ (k + 1)) else RegFan.code (σ k) (σ (k + 1)) (σ (k + 2))
theorem codeOf_spec (σ : Equiv.Perm (Fin 3)) (k : Fin 3) (fl : Bool) :
    RegFan.tT (codeOf σ k fl) = σ k ∧
    RegFan.tU (codeOf σ k fl) = (if fl then σ (k + 2) else σ (k + 1)) ∧
    RegFan.tW (codeOf σ k fl) = (if fl then σ (k + 1) else σ (k + 2)) ∧ codeOf σ k fl < 6 := by
  have h1 : σ k ≠ σ (k + 1) := fun h => fin3_ne_one k (σ.injective h).symm
  have h2 : σ k ≠ σ (k + 2) := fun h => fin3_ne_two k (σ.injective h).symm
  have h3 : σ (k + 1) ≠ σ (k + 2) := fun h => fin3_add_ne k (σ.injective h)
  unfold codeOf
  cases fl
  · simp only [Bool.false_eq_true, if_false]
    exact code_spec _ _ _ h1 h2 h3
  · simp only [if_true]
    exact code_spec _ _ _ h2 h1 h3.symm
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
theorem codeOf_spec' (σ : Equiv.Perm (Fin 3)) (kk : Fin 3) (fl : Bool) :
    RegFan.tT (codeOf σ kk fl) = σ kk ∧ RegFan.tU (codeOf σ kk fl) = σ (armP kk fl) ∧
    RegFan.tW (codeOf σ kk fl) = σ (armQ kk fl) ∧ codeOf σ kk fl < 6 := by
  obtain ⟨h1, h2, h3, h4⟩ := codeOf_spec σ kk fl
  refine ⟨h1, ?_, ?_, h4⟩
  · rw [h2]; cases fl <;> simp [armP]
  · rw [h3]; cases fl <;> simp [armQ]
theorem fin3_arm (kk a : Fin 3) (h : a ≠ kk) : a = kk + 1 ∨ a = kk + 2 := by
  revert kk a; decide
theorem arm_unique (T : Tri) (V : Plane) (kk : Fin 3) (hk : T.pts kk = V) (a b : Fin 3) (ha : a ≠ kk) (hb : b ≠ kk)
    (d : V2) (h1 : Par (toV2 (T.pts a - V)) d) (h2 : Par (toV2 (T.pts b - V)) d) : a = b := by
  by_contra hab
  have hD : cross (T.pts (kk + 1) - T.pts kk) (T.pts (kk + 2) - T.pts kk) = T.det := T.det_cyclic kk
  have hdet : T.det ≠ 0 := T.det_ne_zero
  have hpar := h1.trans h2.symm
  have hcrs := hpar.1
  rw [crs_toV2] at hcrs
  subst hk
  rcases fin3_arm kk a ha with rfl | rfl <;> rcases fin3_arm kk b hb with rfl | rfl
  · exact hab rfl
  · exact hdet (hD ▸ hcrs)
  · rw [cross_swap, neg_eq_zero] at hcrs; exact hdet (hD ▸ hcrs)
  · exact hab rfl
theorem cnt3_eq (c1 c2 c3 j : ℕ) :
    RegFan.cnt [c1, c2, c3] j = (if RegFan.tT c1 = j then 1 else 0) + (if RegFan.tT c2 = j then 1 else 0) +
      (if RegFan.tT c3 = j then 1 else 0) := by
  by_cases h1 : RegFan.tT c1 = j <;> by_cases h2 : RegFan.tT c2 = j <;> by_cases h3 : RegFan.tT c3 = j <;>
    simp [RegFan.cnt, List.filter_cons, h1, h2, h3]
theorem perm3_cnt (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (j : Fin 3) :
    (if (a : ℕ) = j then 1 else 0) + (if (b : ℕ) = j then 1 else 0) + (if (c : ℕ) = j then 1 else 0) = 1 := by
  revert a b c j; decide
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
theorem arm_cases (kk : Fin 3) (fl : Bool) (f : Fin 3) (h : f ≠ kk) : f = armP kk fl ∨ f = armQ kk fl := by
  rcases fin3_arm kk f h with h1 | h1 <;> cases fl <;> simp [armP, armQ, h1]
theorem triStep_start {T : Tri} {d : V2} {U U' : Plane} (hS : TriStep T d U U') {p q : V2}
    (kk' : Fin 3) (fl : Bool) (hk' : T.pts kk' = U)
    (hp : p = toV2 (T.pts (armP kk' fl) - U)) (hq : q = toV2 (T.pts (armQ kk' fl) - U)) (hok : SecOK p q) :
    Par p d := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  have hkk : kk = kk' := T.indep.injective (hk.trans hk'.symm)
  subst hkk
  rcases arm_cases kk fl f hfk with h | h
  · rw [hp, ← h, hf]; exact hpar
  · 
    have hg : g = armP kk fl := by
      rcases arm_cases kk fl g hgk with h' | h'
      · exact h'
      · exact absurd (h'.trans h.symm) hgf
    exfalso
    have hqpar : Par q d := by rw [hq, ← h, hf]; exact hpar
    obtain ⟨c, hc, hcq⟩ := hqpar.smul
    have hpl : 0 < crs d p := by rw [hp, ← hg]; exact hleft
    have hcrs : crs p q = -(c * crs d p) := by
      rw [hcq]; unfold crs; ring
    rcases hok with h1 | ⟨h1, _⟩
    · nlinarith [mul_pos hc hpl]
    · nlinarith [mul_pos hc hpl]
theorem triStep_end {T : Tri} {d : V2} {U U' : Plane} (hS : TriStep T d U U') {p q : V2}
    (kk' : Fin 3) (fl : Bool) (hk' : T.pts kk' = U')
    (hp : p = toV2 (T.pts (armP kk' fl) - U')) (hq : q = toV2 (T.pts (armQ kk' fl) - U')) (hok : SecOK p q) :
    Par q (-d.1, -d.2) := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  have hff : f = kk' := T.indep.injective (hf.trans hk'.symm)
  subst hff
  obtain ⟨c, hc, hcw⟩ := hpar.smul
  have hd0 : d ≠ 0 := hpar.ne_right
  have ha1 : toV2 (T.pts kk - T.pts f) = (-(toV2 (U' - U)).1, -(toV2 (U' - U)).2) := by
    rw [← hk, ← hf]; unfold toV2; ext <;> simp
  have ha2 : toV2 (T.pts g - T.pts f) = ((toV2 (T.pts g - U)).1 - (toV2 (U' - U)).1,
      (toV2 (T.pts g - U)).2 - (toV2 (U' - U)).2) := by
    rw [← hf]; unfold toV2; ext <;> simp [← hk]
    all_goals ring
  have hl2 : 0 < crs d (toV2 (T.pts g - T.pts f)) := by
    rw [ha2, hcw]
    unfold crs at hleft ⊢
    simp only at hleft ⊢
    nlinarith [hleft]
  rw [← hf] at hp hq
  rcases arm_cases f fl kk hfk.symm with h1 | h1 <;> rcases arm_cases f fl g hgf with h2 | h2
  · exact absurd (h1.trans h2.symm) hgk.symm
  · 
    exfalso
    have hpq : crs p q = -(c * crs d (toV2 (T.pts g - T.pts f))) := by
      rw [hp, hq, ← h1, ← h2, ha1, hcw]
      unfold crs
      simp only
      ring
    rcases hok with h | ⟨h, _⟩
    · nlinarith [mul_pos hc hl2]
    · nlinarith [mul_pos hc hl2]
  · 
    rw [hq, ← h1, ha1, hcw]
    apply smul_par hc (by intro h; apply hd0; have h1' : -d.1 = 0 := congrArg Prod.fst h; have h2' : -d.2 = 0 := congrArg Prod.snd h; exact Prod.ext (show d.1 = 0 by linarith) (show d.2 = 0 by linarith))
    ext <;> simp
  · exact absurd (h1.trans h2.symm) hgk.symm
theorem plus_ray_int {p q : V2} (hs : SecOK p q) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → inInt p q (zplus p ε) := by
  have hp := nsq_pos hs.ne_p
  have e1 : ∀ ε, crs p (zplus p ε) = ε * nsq p := by
    intro ε; unfold crs zplus nsq; ring
  have e2 : ∀ ε, crs (zplus p ε) q = crs p q + ε * (-(dt p q)) := by
    intro ε; unfold crs dt zplus; ring
  rcases hs with h | ⟨h0, hd⟩
  · obtain ⟨δ, hδ, H⟩ := affine_pos_small (crs p q) (-(dt p q)) h
    refine ⟨δ, hδ, fun ε hε hεδ => ⟨?_, ?_⟩⟩
    · rw [e1]; positivity
    · rw [e2]; exact H ε hε hεδ
  · refine ⟨1, one_pos, fun ε hε _ => ⟨?_, ?_⟩⟩
    · rw [e1]; positivity
    · rw [e2, h0]; nlinarith
theorem start_inj {ι : Type*} (p q : ι → V2) (hok : ∀ s, SecOK (p s) (q s))
    (hdis : ∀ s t, s ≠ t → ∀ z, ¬ (inInt (p s) (q s) z ∧ inInt (p t) (q t) z)) {s t : ι} (hst : s ≠ t) :
    ¬ Par (p t) (p s) := by
  intro hpar
  obtain ⟨c, hc, hcq⟩ := hpar.smul
  obtain ⟨d1, hd1, H1⟩ := plus_ray_int (hok s)
  obtain ⟨d2, hd2, H2⟩ := plus_ray_int (hok t)
  set ε := min d1 d2 / 2 with hε
  have hεpos : 0 < ε := by have := lt_min hd1 hd2; positivity
  have hε1 : ε < d1 := by have := min_le_left d1 d2; linarith [lt_min hd1 hd2]
  have hε2 : ε < d2 := by have := min_le_right d1 d2; linarith [lt_min hd1 hd2]
  have h1 := H1 ε hεpos hε1
  have h2 := H2 ε hεpos hε2
  have hz : zplus (p t) ε = (c * (zplus (p s) ε).1, c * (zplus (p s) ε).2) := by
    rw [hcq]; unfold zplus; ext <;> simp <;> ring
  rw [hz] at h2
  exact hdis s t hst (zplus (p s) ε) ⟨h1, (inInt_smul_iff hc).mp h2⟩
theorem end_inj' {ι : Type*} (p q : ι → V2) (hok : ∀ s, SecOK (p s) (q s))
    (hdis : ∀ s t, s ≠ t → ∀ z, ¬ (inInt (p s) (q s) z ∧ inInt (p t) (q t) z)) {s t : ι} (hst : s ≠ t) :
    ¬ Par (q t) (q s) := by
  intro hpar
  obtain ⟨c, hc, hcq⟩ := hpar.smul
  obtain ⟨d1, hd1, H1⟩ := minus_ray_int (hok s)
  obtain ⟨d2, hd2, H2⟩ := minus_ray_int (hok t)
  set ε := min d1 d2 / 2 with hε
  have hεpos : 0 < ε := by have := lt_min hd1 hd2; positivity
  have hε1 : ε < d1 := by have := min_le_left d1 d2; linarith [lt_min hd1 hd2]
  have hε2 : ε < d2 := by have := min_le_right d1 d2; linarith [lt_min hd1 hd2]
  have h1 := H1 ε hεpos hε1
  have h2 := H2 ε hεpos hε2
  have hz : zminus (q t) ε = (c * (zminus (q s) ε).1, c * (zminus (q s) ε).2) := by
    rw [hcq]; unfold zminus; ext <;> simp <;> ring
  rw [hz] at h2
  exact hdis s t hst (zminus (q s) ε) ⟨h1, (inInt_smul_iff hc).mp h2⟩
theorem par_neg {u v : V2} (h : Par u v) : Par (-u.1, -u.2) (-v.1, -v.2) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · unfold crs at h1 ⊢; simp only; linarith
  · unfold dt at h2 ⊢; simp only; linarith
theorem convex_leftHalf (d : V2) (X0 : Plane) : Convex ℝ {y : Plane | 0 ≤ crs d (toV2 (y - X0))} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  unfold crs toV2 at *
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hx hy ⊢
  have : a = 1 - b := by linarith
  subst this
  nlinarith [mul_nonneg ha hx, mul_nonneg hb hy]
theorem fin3_three (kk f g : Fin 3) (h1 : f ≠ kk) (h2 : g ≠ kk) (h3 : g ≠ f) (j : Fin 3) :
    j = kk ∨ j = f ∨ j = g := by
  revert kk f g j; decide
theorem triStep_left_half {T : Tri} {d : V2} {X0 Y0 : Plane} (hS : TriStep T d X0 Y0) :
    T.carrier ⊆ {y : Plane | 0 ≤ crs d (toV2 (y - X0))} := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  obtain ⟨c, hc, hcw⟩ := hpar.smul
  have hv : ∀ j, T.pts j ∈ {y : Plane | 0 ≤ crs d (toV2 (y - X0))} := by
    intro j
    simp only [Set.mem_setOf_eq]
    rcases fin3_three kk f g hfk hgk hgf j with rfl | rfl | rfl
    · rw [hk]; unfold crs toV2; simp
    · rw [hf, hcw]; unfold crs; simp only; ring_nf; exact le_refl _
    · exact hleft.le
  exact convexHull_min (by rintro _ ⟨j, rfl⟩; exact hv j) (convex_leftHalf d X0)
theorem pT_par_d {T : Tri} {d : V2} {X0 Y0 : Plane} (hS : TriStep T d X0 Y0) {V : Plane}
    (hV : crs d (toV2 (V - X0)) = 0) {pT : V2} (hpT : pT ≠ 0)
    (hloc : LocalCone T V pT (-pT.1, -pT.2)) : Par pT d := by
  obtain ⟨r, hr, hiff⟩ := hloc
  have hd0 : d ≠ 0 := by obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := hS; exact hpar.ne_right
  have key : ∀ z : V2, 0 ≤ crs pT z → 0 ≤ crs d z := by
    intro z hz
    obtain ⟨ε, hε, hdist⟩ := exists_ptOf_small V z hr
    have h1 : ptOf V z ε ∈ T.carrier := by
      rw [hiff _ hdist, toV2_ptOf, inCone_straight_iff]
      unfold crs at hz ⊢; simp only; nlinarith [mul_nonneg hε.le hz]
    have h2 := triStep_left_half hS h1
    simp only [Set.mem_setOf_eq] at h2
    have h3 : toV2 (ptOf V z ε - X0) = ((toV2 (ptOf V z ε - V)).1 + (toV2 (V - X0)).1,
        (toV2 (ptOf V z ε - V)).2 + (toV2 (V - X0)).2) := by
      unfold toV2; ext <;> simp
    rw [h3, toV2_ptOf] at h2
    unfold crs at h2 hV ⊢
    simp only at h2 hV ⊢
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos hε (neg_pos.mpr hcon)]
  have a1 := key pT (by unfold crs; ring_nf; exact le_refl _)
  have a2 := key (-pT.1, -pT.2) (by unfold crs; simp only; ring_nf; exact le_refl _)
  have hcr : crs pT d = 0 := by
    unfold crs at a1 a2 ⊢; simp only at a1 a2; linarith
  have a3 := key (-pT.2, pT.1) (by
    have := nsq_pos hpT
    unfold crs nsq at *; simp only; nlinarith)
  refine ⟨hcr, ?_⟩
  have hnn : 0 ≤ dt pT d := by unfold crs dt at *; simp only at a3 ⊢; nlinarith
  rcases hnn.eq_or_lt with h | h
  · exfalso; exact hpT (eq_zero_of_crs_dt hd0 hcr h.symm)
  · exact h
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
structure ExtFan (D : Dissection N) (V : Plane) (κ : Type) [Fintype κ] where
  Tgt : Set V2
  R : ℝ
  hR : 0 < R
  hT : ∀ y : Plane, dist y V < R → (y ∈ D.target.carrier ↔ toV2 (y - V) ∈ Tgt)
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
theorem inCone_convex {p q x y : V2} (hx : inCone p q x) (hy : inCone p q y) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : inCone p q ((a * x.1 + b * y.1, a * x.2 + b * y.2) : V2) := by
  unfold inCone crs at *
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor <;> simp only <;> nlinarith [mul_nonneg ha hx1, mul_nonneg hb hy1, mul_nonneg ha hx2, mul_nonneg hb hy2]
namespace ExtFan
variable {D : Dissection N} {V : Plane} {κ : Type} [Fintype κ]
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
open MeasureTheory Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement
open scoped ENNReal
namespace Erdos634.Draft.LaczFormal.Thm21
def cross2 (u w : Plane) : ℝ := u 0 * w 1 - u 1 * w 0
end Erdos634.Draft.LaczFormal.Thm21
end

section
open MeasureTheory Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.Thm21
structure ConvPoly (M : ℕ) [NeZero M] where
  v : Fin M → Plane
  three_le : 3 ≤ M
  left : ∀ i j : Fin M, j ≠ i → j ≠ i + 1 → 0 < cross2 (v (i + 1) - v i) (v j - v i)
namespace ConvPoly
variable {M : ℕ} [NeZero M] (P : ConvPoly M)
def carrier : Set Plane := {x | ∀ i : Fin M, 0 ≤ cross2 (P.v (i + 1) - P.v i) (x - P.v i)}
noncomputable def angle (i : Fin M) : ℝ := cornerAngle (P.v (i - 1)) (P.v i) (P.v (i + 1))
end ConvPoly
def Comm (x y : ℝ) : Prop := ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℝ) * x = q * y
section Concl
variable {N M : ℕ} [NeZero M]
end Concl
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
variable {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ]
theorem Tgt_inv (F : ExtFan D V κ) {z : V2} {c : ℝ} (hc : 0 < c) (h : ((c * z.1, c * z.2) : V2) ∈ F.Tgt) : z ∈ F.Tgt := by
  have := F.hTs _ h c⁻¹ (inv_pos.mpr hc)
  have e : ((c⁻¹ * (c * z.1), c⁻¹ * (c * z.2)) : V2) = z := by
    ext <;> simp <;> field_simp
  simpa [e] using this
theorem tile_cone_sub (F : ExtFan D V κ) (s : AtV D V) {z : V2} (hz : inCone (F.p s) (F.q s) z) : z ∈ F.Tgt := by
  obtain ⟨r, hr, hiff⟩ := F.hloc s
  obtain ⟨ε, hε, hd⟩ := exists_ptOf_small V z (lt_min hr F.hR)
  have hd1 : dist (ptOf V z ε) V < r := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : dist (ptOf V z ε) V < F.R := lt_of_lt_of_le hd (min_le_right _ _)
  have h1 : ptOf V z ε ∈ (D.tile s.1).carrier := by
    rw [hiff _ hd1, toV2_ptOf]; exact (inCone_smul_iff hε).mpr hz
  have h2 : ptOf V z ε ∈ D.region := by
    rw [← D.covers]; exact Set.mem_iUnion.mpr ⟨s.1, h1⟩
  have h3 := (F.hT _ hd2).mp h2
  rw [toV2_ptOf] at h3
  exact F.Tgt_inv hε h3
theorem disj_all (F : ExtFan D V κ) {o1 o2 : AtV D V ⊕ κ} (h : o1 ≠ o2) (z : V2) :
    ¬ (inInt (Sum.elim F.p F.pe o1) (Sum.elim F.q F.qe o1) z ∧ inInt (Sum.elim F.p F.pe o2) (Sum.elim F.q F.qe o2) z) := by
  rintro ⟨h1, h2⟩
  rcases o1 with s | j <;> rcases o2 with t | j'
  · exact tiles_disjoint D V F.p F.q F.hloc s t (fun e => h (by rw [e])) z ⟨h1, h2⟩
  · exact F.hextT j' z h2 (F.tile_cone_sub s ⟨h1.1.le, h1.2.le⟩)
  · exact F.hextT j z h1 (F.tile_cone_sub t ⟨h2.1.le, h2.2.le⟩)
  · exact F.hdisjE j j' (fun e => h (by rw [e])) z ⟨h1, h2⟩
theorem ray_left (F : ExtFan D V κ) {d : V2} (a b : AtV D V) (hcrsA : 0 < crs (F.p a) (F.q a))
    (hqa : Par (F.q a) (-d.1, -d.2)) (hqb : Par (F.q b) d) :
    ∃ c : AtV D V, 0 < crs (F.p c) (F.q c) ∧ Par (F.p c) d := by
  classical
  have hd0 : d ≠ 0 := hqb.ne_right
  obtain ⟨δa, hδa, Ha⟩ := minus_ray_int (F.hok a)
  set zA := zminus (F.q a) (δa / 2) with hzA
  have hzAint : inInt (F.p a) (F.q a) zA := Ha _ (by positivity) (by linarith)
  have hzA_left : 0 < crs d zA := by
    obtain ⟨c', hc', hq'⟩ := hqa.smul
    have h := hzAint.2
    rw [hq'] at h
    by_contra hX; push Not at hX
    unfold crs at h hX
    try simp only at h hX
    nlinarith [mul_nonneg hc'.le (neg_nonneg.mpr hX)]
  obtain ⟨n, hn, hen⟩ := F.hsurj (Sum.inl b)
  have hPn := F.hP n
  rw [hen] at hPn
  simp only [Sum.elim_inl] at hPn
  have hsucc : Par (Sum.elim F.p F.pe (F.e (n + 1))) d := hPn.trans hqb
  rcases hnext : F.e (n + 1) with c | j
  · rw [hnext] at hsucc
    simp only [Sum.elim_inl] at hsucc
    refine ⟨c, ?_, hsucc⟩
    by_contra hnot
    push Not at hnot
    have hcs : crs (F.p c) (F.q c) = 0 ∧ dt (F.p c) (F.q c) < 0 := by
      rcases F.hok c with h | h
      · linarith
      · exact h
    obtain ⟨c1, hc1, hp1⟩ := hsucc.smul
    have hpar : Par (F.q c) (-(F.p c).1, -(F.p c).2) := by
      refine ⟨?_, ?_⟩
      · unfold crs at hcs ⊢; simp only; linarith [hcs.1]
      · unfold dt at hcs ⊢; simp only; linarith [hcs.2]
    obtain ⟨l, hl, hq1⟩ := hpar.smul
    have hzC : inInt (F.p c) (F.q c) zA := by
      constructor
      · rw [hp1]; unfold crs at hzA_left ⊢; try simp only at hzA_left ⊢; nlinarith [mul_pos hc1 hzA_left]
      · rw [hq1, hp1]; unfold crs at hzA_left ⊢; try simp only at hzA_left ⊢; nlinarith [mul_pos (mul_pos hl hc1) hzA_left]
    have hac : a ≠ c := by rintro rfl; linarith
    exact tiles_disjoint D V F.p F.q F.hloc a c hac zA ⟨hzAint, hzC⟩
  · exfalso
    rw [hnext] at hsucc
    simp only [Sum.elim_inr] at hsucc
    obtain ⟨c2, hc2, hqb2⟩ := hqb.smul
    have hqbT : F.q b ∈ F.Tgt := F.tile_cone_sub b ⟨(F.hok b).elim (fun h => h.le) (fun h => h.1.ge), by
      unfold crs; nlinarith [mul_comm (F.q b).1 (F.q b).2]⟩
    have hdT : d ∈ F.Tgt := F.Tgt_inv hc2 (by rw [← hqb2]; exact hqbT)
    have hzAT : zA ∈ F.Tgt := F.tile_cone_sub a ⟨hzAint.1.le, hzAint.2.le⟩
    obtain ⟨c3, hc3, hp3⟩ := hsucc.smul
    have hok := F.hokE j
    have key : ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ inInt (F.pe j) (F.qe j) ((1 - μ) * d.1 + μ * zA.1, (1 - μ) * d.2 + μ * zA.2) := by
      rcases hok with hs | ⟨hs0, hsd⟩
      · 
        have hdq : 0 < crs d (F.qe j) := by
          rw [hp3] at hs
          unfold crs at hs ⊢; try simp only at hs ⊢
          by_contra hX; push Not at hX
          nlinarith [mul_nonneg hc3.le (neg_nonneg.mpr hX)]
        obtain ⟨δ, hδ, H⟩ := affine_pos_small (crs d (F.qe j)) (crs zA (F.qe j) - crs d (F.qe j)) hdq
        refine ⟨min (δ / 2) (1 / 2), by positivity, by
          have := min_le_right (δ / 2) (1 / 2 : ℝ); linarith, ⟨?_, ?_⟩⟩
        · rw [hp3]
          unfold crs at hzA_left ⊢; try simp only at hzA_left ⊢
          have hμ : 0 < min (δ / 2) (1 / 2 : ℝ) := by positivity
          nlinarith [mul_pos (mul_pos hc3 hμ) hzA_left]
        · have := H (min (δ / 2) (1 / 2)) (by positivity) (by
            have := min_le_left (δ / 2) (1 / 2 : ℝ); linarith)
          unfold crs at this ⊢; try simp only at this ⊢
          nlinarith [this]
      · 
        have hpar : Par (F.qe j) (-d.1, -d.2) := by
          rw [hp3] at hs0 hsd
          refine ⟨?_, ?_⟩
          · unfold crs at hs0 ⊢; try simp only at hs0 ⊢; nlinarith [hs0, hc3]
          · unfold dt at hsd ⊢; try simp only at hsd ⊢; nlinarith [hsd, hc3]
        obtain ⟨l, hl, hq1⟩ := hpar.smul
        refine ⟨1 / 2, by norm_num, by norm_num, ⟨?_, ?_⟩⟩
        · rw [hp3]
          unfold crs at hzA_left ⊢; try simp only at hzA_left ⊢
          nlinarith [mul_pos hc3 hzA_left]
        · rw [hq1]
          unfold crs at hzA_left ⊢; try simp only at hzA_left ⊢
          nlinarith [mul_pos hl hzA_left]
    obtain ⟨μ, hμ0, hμ1, hμin⟩ := key
    have hmemT : ((1 - μ) * d.1 + μ * zA.1, (1 - μ) * d.2 + μ * zA.2) ∈ F.Tgt :=
      F.hTc d hdT zA hzAT (1 - μ) μ (by linarith) hμ0.le (by ring)
    exact F.hextT j _ hμin hmemT
theorem ray_right (F : ExtFan D V κ) {d : V2} (a b : AtV D V) (hcrsA : 0 < crs (F.p a) (F.q a))
    (hpa : Par (F.p a) (-d.1, -d.2)) (hpb : Par (F.p b) d) :
    ∃ c : AtV D V, 0 < crs (F.p c) (F.q c) ∧ Par (F.q c) d := by
  classical
  have hd0 : d ≠ 0 := hpb.ne_right
  obtain ⟨δa, hδa, Ha⟩ := plus_ray_int (F.hok a)
  set zA := zplus (F.p a) (δa / 2) with hzA
  have hzAint : inInt (F.p a) (F.q a) zA := Ha _ (by positivity) (by linarith)
  have hzA_right : crs d zA < 0 := by
    obtain ⟨c', hc', hp'⟩ := hpa.smul
    have h := hzAint.1
    rw [hp'] at h
    by_contra hX; push Not at hX
    unfold crs at h hX
    try simp only at h hX
    nlinarith [mul_nonneg hc'.le hX]
  obtain ⟨n, hn, hen⟩ := F.hsurj (Sum.inl b)
  have hkpos : 0 < Fintype.card (AtV D V ⊕ κ) := lt_of_le_of_lt (Nat.zero_le _) hn
  have hPn := F.hP (n + (Fintype.card (AtV D V ⊕ κ) - 1))
  have hshift : n + (Fintype.card (AtV D V ⊕ κ) - 1) + 1 = n + Fintype.card (AtV D V ⊕ κ) := by omega
  rw [hshift, F.hper n, hen] at hPn
  simp only [Sum.elim_inl] at hPn
  have hpred : Par (Sum.elim F.q F.qe (F.e (n + (Fintype.card (AtV D V ⊕ κ) - 1)))) d := hPn.symm.trans hpb
  rcases hprev : F.e (n + (Fintype.card (AtV D V ⊕ κ) - 1)) with c | j
  · rw [hprev] at hpred
    simp only [Sum.elim_inl] at hpred
    refine ⟨c, ?_, hpred⟩
    by_contra hnot
    push Not at hnot
    have hcs : crs (F.p c) (F.q c) = 0 ∧ dt (F.p c) (F.q c) < 0 := by
      rcases F.hok c with h | h
      · linarith
      · exact h
    obtain ⟨c1, hc1, hq1⟩ := hpred.smul
    have hpar : Par (F.p c) (-(F.q c).1, -(F.q c).2) := by
      refine ⟨?_, ?_⟩
      · unfold crs at hcs ⊢; try simp only; linarith [hcs.1]
      · unfold dt at hcs ⊢; try simp only; linarith [hcs.2]
    obtain ⟨l, hl, hp1⟩ := hpar.smul
    have hzC : inInt (F.p c) (F.q c) zA := by
      constructor
      · rw [hp1, hq1]; unfold crs at hzA_right ⊢; try simp only at hzA_right ⊢; nlinarith [mul_pos (mul_pos hl hc1) (neg_pos.mpr hzA_right)]
      · rw [hq1]; unfold crs at hzA_right ⊢; try simp only at hzA_right ⊢; nlinarith [mul_pos hc1 (neg_pos.mpr hzA_right)]
    have hac : a ≠ c := by rintro rfl; linarith
    exact tiles_disjoint D V F.p F.q F.hloc a c hac zA ⟨hzAint, hzC⟩
  · exfalso
    rw [hprev] at hpred
    simp only [Sum.elim_inr] at hpred
    obtain ⟨c2, hc2, hpb2⟩ := hpb.smul
    have hpbT : F.p b ∈ F.Tgt := F.tile_cone_sub b ⟨by unfold crs; nlinarith [mul_comm (F.p b).1 (F.p b).2],
      (F.hok b).elim (fun h => h.le) (fun h => h.1.ge)⟩
    have hdT : d ∈ F.Tgt := F.Tgt_inv hc2 (by rw [← hpb2]; exact hpbT)
    have hzAT : zA ∈ F.Tgt := F.tile_cone_sub a ⟨hzAint.1.le, hzAint.2.le⟩
    obtain ⟨c3, hc3, hq3⟩ := hpred.smul
    have hok := F.hokE j
    have key : ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ inInt (F.pe j) (F.qe j) ((1 - μ) * d.1 + μ * zA.1, (1 - μ) * d.2 + μ * zA.2) := by
      rcases hok with hs | ⟨hs0, hsd⟩
      · have hpd : 0 < crs (F.pe j) d := by
          rw [hq3] at hs
          unfold crs at hs ⊢; try simp only at hs ⊢
          by_contra hX; push Not at hX
          nlinarith [mul_nonneg hc3.le (neg_nonneg.mpr hX)]
        obtain ⟨δ, hδ, H⟩ := affine_pos_small (crs (F.pe j) d) (crs (F.pe j) zA - crs (F.pe j) d) hpd
        refine ⟨min (δ / 2) (1 / 2), by positivity, by
          have := min_le_right (δ / 2) (1 / 2 : ℝ); linarith, ⟨?_, ?_⟩⟩
        · have := H (min (δ / 2) (1 / 2)) (by positivity) (by
            have := min_le_left (δ / 2) (1 / 2 : ℝ); linarith)
          unfold crs at this ⊢; try simp only at this ⊢
          nlinarith [this]
        · rw [hq3]
          unfold crs at hzA_right ⊢; try simp only at hzA_right ⊢
          have hμ : 0 < min (δ / 2) (1 / 2 : ℝ) := by positivity
          nlinarith [mul_pos (mul_pos hc3 hμ) (neg_pos.mpr hzA_right)]
      · have hpar : Par (F.pe j) (-d.1, -d.2) := by
          rw [hq3] at hs0 hsd
          refine ⟨?_, ?_⟩
          · unfold crs at hs0 ⊢; try simp only at hs0 ⊢; nlinarith [hs0, hc3]
          · unfold dt at hsd ⊢; try simp only at hsd ⊢; nlinarith [hsd, hc3]
        obtain ⟨l, hl, hp1⟩ := hpar.smul
        refine ⟨1 / 2, by norm_num, by norm_num, ⟨?_, ?_⟩⟩
        · rw [hp1]
          unfold crs at hzA_right ⊢; try simp only at hzA_right ⊢
          nlinarith [mul_pos hl (neg_pos.mpr hzA_right)]
        · rw [hq3]
          unfold crs at hzA_right ⊢; try simp only at hzA_right ⊢
          nlinarith [mul_pos hc3 (neg_pos.mpr hzA_right)]
    obtain ⟨μ, hμ0, hμ1, hμin⟩ := key
    have hmemT : ((1 - μ) * d.1 + μ * zA.1, (1 - μ) * d.2 + μ * zA.2) ∈ F.Tgt :=
      F.hTc d hdT zA hzAT (1 - μ) μ (by linarith) hμ0.le (by ring)
    exact F.hextT j _ hμin hmemT
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
open Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
def neg2 (d : V2) : V2 := (-d.1, -d.2)
theorem triStep_of_end {T : Tri} {d : V2} {U : Plane} (kk : Fin 3) (fl : Bool) (hk : T.pts kk = U) {p q : V2}
    (hp : p = toV2 (T.pts (armP kk fl) - U)) (hq : q = toV2 (T.pts (armQ kk fl) - U))
    (hcrs : 0 < crs p q) (hpar : Par q d) : TriStep T (neg2 d) (T.pts (armQ kk fl)) U := by
  obtain ⟨c, hc, hcq⟩ := hpar.smul
  refine ⟨armQ kk fl, kk, armP kk fl, rfl, hk, (armQ_ne kk fl).symm, (armPQ_ne kk fl), (armP_ne kk fl), ?_, ?_⟩
  · have : toV2 (U - T.pts (armQ kk fl)) = (-q.1, -q.2) := by
      rw [hq]; unfold toV2; ext <;> simp
    rw [this]
    exact par_neg hpar
  · have e1 : toV2 (T.pts (armP kk fl) - T.pts (armQ kk fl)) = (p.1 - q.1, p.2 - q.2) := by
      rw [hp, hq]; unfold toV2; ext <;> simp [← hk]
    rw [e1]
    have h1 : crs p q = c * crs p d := by rw [hcq]; unfold crs; ring
    rw [h1] at hcrs
    have hpd : 0 < crs p d := (mul_pos_iff_of_pos_left hc).mp hcrs
    unfold crs at hpd
    unfold crs neg2
    try simp only at hpd ⊢
    rw [hcq]
    nlinarith [hpd]
theorem step_interior_pt {T : Tri} {d : V2} {A B : Plane} (hS : TriStep T d A B) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    A + σ • (B - A) ∈ T.carrier ∧ (∀ k, T.pts k ≠ A + σ • (B - A)) ∧ crs d (toV2 (A + σ • (B - A) - A)) = 0 := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := hS
  obtain ⟨c, hc, hcw⟩ := hpar.smul
  have hAB : B ≠ A := by
    intro h; apply hfk; apply T.indep.injective; rw [hf, hk]; exact h
  have hAm : A ∈ T.carrier := hk ▸ subset_convexHull ℝ _ ⟨kk, rfl⟩
  have hBm : B ∈ T.carrier := hf ▸ subset_convexHull ℝ _ ⟨f, rfl⟩
  have hY : toV2 (A + σ • (B - A) - A) = (σ * (c * d.1), σ * (c * d.2)) := by
    have : toV2 (A + σ • (B - A) - A) = (σ * (toV2 (B - A)).1, σ * (toV2 (B - A)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hcw]
  refine ⟨T.convex.add_smul_sub_mem hAm hBm ⟨h0.le, h1.le⟩, ?_, ?_⟩
  · intro k hkY
    rcases fin3_three kk f g hfk hgk hgf k with rfl | rfl | rfl
    · rw [hk] at hkY
      have : σ • (B - A) = 0 := by simpa using hkY.symm
      rcases smul_eq_zero.mp this with h | h
      · linarith
      · exact hAB (sub_eq_zero.mp h)
    · rw [hf] at hkY
      have h2 : (σ - 1) • (B - A) = 0 := by
        have : A + σ • (B - A) - B = 0 := by rw [← hkY]; simp
        rw [sub_smul, one_smul]
        calc σ • (B - A) - (B - A) = A + σ • (B - A) - B := by abel
          _ = 0 := this
      rcases smul_eq_zero.mp h2 with h | h
      · linarith
      · exact hAB (sub_eq_zero.mp h)
    · have hline := hY
      have hg : crs d (toV2 (T.pts k - A)) > 0 := hleft
      rw [hkY, hY] at hg
      unfold crs at hg; try simp only at hg; nlinarith
  · rw [hY]; unfold crs; ring
theorem coords_of_toV2 {P X : Plane} {t : ℝ} {d : V2} (h : toV2 (P - X) = (t * d.1, t * d.2)) :
    P 0 = X 0 + t * d.1 ∧ P 1 = X 1 + t * d.2 := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [toV2] at h1 h2
  simp only [PiLp.sub_apply] at h1 h2
  constructor <;> linarith
theorem pt_ext {P Q : Plane} (h0 : P 0 = Q 0) (h1 : P 1 = Q 1) : P = Q := by
  ext i; fin_cases i
  · exact h0
  · exact h1
theorem neg2_neg2 (d : V2) : ((-(neg2 d).1, -(neg2 d).2) : V2) = d := by
  unfold neg2; ext <;> simp
end Erdos634.Draft.LaczFormal.Graph
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
inductive WalkR (D : RegionDissection N) (d : V2) : Plane → Plane → List (Fin N × Plane × Plane) → Prop
  | nil (X : Plane) : WalkR D d X X []
  | cons {i : Fin N} {X X' Y : Plane} {L : List (Fin N × Plane × Plane)} :
      TriStep (D.tile i) (neg2 d) X' X → WalkR D d X' Y L → WalkR D d X Y ((i, X, X') :: L)
theorem walkR_progress {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) : ∃ T : ℝ, 0 ≤ T ∧ toV2 (Y - X) = (T * d.1, T * d.2) ∧ (L ≠ [] → 0 < T) := by
  induction W with
  | nil X => exact ⟨0, le_rfl, by unfold toV2; ext <;> simp, fun h => absurd rfl h⟩
  | @cons i X X' Y L hS W ih =>
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    obtain ⟨T, hT, hTe, -⟩ := ih
    refine ⟨c + T, by positivity, ?_, fun _ => by positivity⟩
    have h1 : toV2 (X' - X) = (c * d.1, c * d.2) := by
      have : toV2 (X' - X) = (-(toV2 (X - X')).1, -(toV2 (X - X')).2) := by
        unfold toV2; ext <;> simp
      rw [this, hcw]; unfold neg2; ext <;> simp
    have : toV2 (Y - X) = ((toV2 (Y - X')).1 + (toV2 (X' - X)).1, (toV2 (Y - X')).2 + (toV2 (X' - X)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hTe, h1]
    ext <;> simp <;> ring
theorem walkT_cover {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) {T : ℝ} (hT : toV2 (Y - X) = (T * d.1, T * d.2)) (hd : d ≠ 0) :
    ∀ s : ℝ, 0 ≤ s → s < T → ∃ e ∈ L, ∃ t0 t1 : ℝ, toV2 (e.2.1 - X) = (t0 * d.1, t0 * d.2) ∧
      toV2 (e.2.2 - X) = (t1 * d.1, t1 * d.2) ∧ t0 ≤ s ∧ s < t1 := by
  induction W generalizing T with
  | nil X =>
    intro s hs hsT
    exfalso
    have h1 : T * d.1 = 0 := by have := congrArg Prod.fst hT; simpa [toV2] using this.symm
    have h2 : T * d.2 = 0 := by have := congrArg Prod.snd hT; simpa [toV2] using this.symm
    have hT0 : T = 0 := by
      by_contra hne
      exact hd (Prod.ext ((mul_eq_zero.mp h1).resolve_left hne) ((mul_eq_zero.mp h2).resolve_left hne))
    linarith
  | @cons i X X' Y L hS W ih =>
    intro s hs hsT
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    by_cases hsc : s < c
    · exact ⟨(i, X, X'), List.mem_cons_self .., 0, c, by unfold toV2; ext <;> simp, hcw, hs, hsc⟩
    · push_neg at hsc
      have hT' : toV2 (Y - X') = ((T - c) * d.1, (T - c) * d.2) := by
        have : toV2 (Y - X') = ((toV2 (Y - X)).1 - (toV2 (X' - X)).1, (toV2 (Y - X)).2 - (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, hT, hcw]; ext <;> simp <;> ring
      obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := ih hT' (s - c) (by linarith) (by linarith)
      refine ⟨e, List.mem_cons_of_mem _ he, t0 + c, t1 + c, ?_, ?_, by linarith, by linarith⟩
      · have : toV2 (e.2.1 - X) = ((toV2 (e.2.1 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.1 - X')).2 + (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, h0, hcw]; ext <;> simp <;> ring
      · have : toV2 (e.2.2 - X) = ((toV2 (e.2.2 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.2 - X')).2 + (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, h1, hcw]; ext <;> simp <;> ring
theorem walkR_cover {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) {T : ℝ} (hT : toV2 (Y - X) = (T * d.1, T * d.2)) (hd : d ≠ 0) :
    ∀ s : ℝ, 0 ≤ s → s < T → ∃ e ∈ L, ∃ t0 t1 : ℝ, toV2 (e.2.1 - X) = (t0 * d.1, t0 * d.2) ∧
      toV2 (e.2.2 - X) = (t1 * d.1, t1 * d.2) ∧ t0 ≤ s ∧ s < t1 := by
  induction W generalizing T with
  | nil X =>
    intro s hs hsT
    exfalso
    have h1 : T * d.1 = 0 := by have := congrArg Prod.fst hT; simpa [toV2] using this.symm
    have h2 : T * d.2 = 0 := by have := congrArg Prod.snd hT; simpa [toV2] using this.symm
    have hT0 : T = 0 := by
      by_contra hne
      exact hd (Prod.ext ((mul_eq_zero.mp h1).resolve_left hne) ((mul_eq_zero.mp h2).resolve_left hne))
    linarith
  | @cons i X X' Y L hS W ih =>
    intro s hs hsT
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    have h1 : toV2 (X' - X) = (c * d.1, c * d.2) := by
      have : toV2 (X' - X) = (-(toV2 (X - X')).1, -(toV2 (X - X')).2) := by
        unfold toV2; ext <;> simp
      rw [this, hcw]; unfold neg2; ext <;> simp
    by_cases hsc : s < c
    · exact ⟨(i, X, X'), List.mem_cons_self .., 0, c, by unfold toV2; ext <;> simp, h1, hs, hsc⟩
    · push_neg at hsc
      have hT' : toV2 (Y - X') = ((T - c) * d.1, (T - c) * d.2) := by
        have : toV2 (Y - X') = ((toV2 (Y - X)).1 - (toV2 (X' - X)).1, (toV2 (Y - X)).2 - (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, hT, h1]; ext <;> simp <;> ring
      obtain ⟨e, he, t0, t1, h0, h1', h2, h3⟩ := ih hT' (s - c) (by linarith) (by linarith)
      refine ⟨e, List.mem_cons_of_mem _ he, t0 + c, t1 + c, ?_, ?_, by linarith, by linarith⟩
      · have : toV2 (e.2.1 - X) = ((toV2 (e.2.1 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.1 - X')).2 + (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, h0, h1]; ext <;> simp <;> ring
      · have : toV2 (e.2.2 - X) = ((toV2 (e.2.2 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.2 - X')).2 + (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, h1', h1]; ext <;> simp <;> ring
theorem walkT_last {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) (hL : L ≠ []) : ∃ i U, (i, U, Y) ∈ L ∧ TriStep (D.tile i) d U Y := by
  induction W with
  | nil X => exact absurd rfl hL
  | @cons i X X' Y L hS W ih =>
    by_cases hL' : L = []
    · subst hL'
      cases W
      exact ⟨i, X, List.mem_cons_self .., hS⟩
    · obtain ⟨j, U, hmem, hSj⟩ := ih hL'
      exact ⟨j, U, List.mem_cons_of_mem _ hmem, hSj⟩
theorem walkR_last {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) (hL : L ≠ []) : ∃ i U, (i, U, Y) ∈ L ∧ TriStep (D.tile i) (neg2 d) Y U := by
  induction W with
  | nil X => exact absurd rfl hL
  | @cons i X X' Y L hS W ih =>
    by_cases hL' : L = []
    · subst hL'
      cases W
      exact ⟨i, X, List.mem_cons_self .., hS⟩
    · obtain ⟨j, U, hmem, hSj⟩ := ih hL'
      exact ⟨j, U, List.mem_cons_of_mem _ hmem, hSj⟩
theorem walkR_mem_step {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) : ∀ e ∈ L, TriStep (D.tile e.1) (neg2 d) e.2.2 e.2.1 := by
  induction W with
  | nil X => intro e he; exact absurd he (by simp)
  | @cons i X X' Y L hS W ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact hS
    · exact ih e h
theorem straight_dir {D : RegionDissection N} {V : Plane} (b : AtV D V) {p q : V2} (hok : SecOK p q)
    (hloc : LocalCone (D.tile b.1) V p q) (hspec : SectorSpec (D.tile b.1) V p q)
    (hnv : ∀ k, (D.tile b.1).pts k ≠ V) {d' : V2} {A B : Plane} (hS : TriStep (D.tile b.1) d' A B)
    (hline : crs d' (toV2 (V - A)) = 0) : Par p d' ∧ q = (-p.1, -p.2) := by
  rcases hspec with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
  · exact absurd hk (hnv k)
  · subst hq
    exact ⟨pT_par_d hS hline hok.ne_p hloc, rfl⟩
theorem ends_coincide (D : RegionDissection N) [HasFansC D] {d : V2} (hd : d ≠ 0) {X Y1 Y2 : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (hL1 : L1 ≠ []) (hL2 : L2 ≠ [])
    (W1 : WalkT D d X Y1 L1) (W2 : WalkR D d X Y2 L2)
    (hno1 : ∀ i U', ¬ TriStep (D.tile i) d Y1 U') (hno2 : ∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y2) : Y1 = Y2 := by
  classical
  obtain ⟨T1, hT1, hT1e, hT1p⟩ := walkT_progress W1
  obtain ⟨T2, hT2, hT2e, hT2p⟩ := walkR_progress W2
  have p1 := hT1p hL1
  have p2 := hT2p hL2
  have c1 := coords_of_toV2 hT1e
  have c2 := coords_of_toV2 hT2e
  have hTeq : T1 = T2 := by
    rcases lt_trichotomy T1 T2 with hlt | heq | hgt
    · 
      exfalso
      obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkR_cover W2 hT2e hd T1 hT1 hlt
      have hSe := walkR_mem_step W2 e he
      obtain ⟨i1, U1, hmem1, hS1⟩ := walkT_last W1 hL1
      obtain ⟨kkL, fL, gL, hkL, hfL, -⟩ := id hS1
      have hvert : ∃ j k, (D.tile j).pts k = Y1 := ⟨i1, fL, hfL⟩
      obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D) Y1 hvert
      have hmemA : Y1 ∈ (D.tile i1).carrier := hfL ▸ subset_convexHull ℝ _ ⟨fL, rfl⟩
      set a : AtV D Y1 := ⟨i1, hmemA⟩ with ha
      obtain ⟨kk', fl', hk', hpa, hqa⟩ := spec_corner_data (F.hspec a) ⟨fL, hfL⟩
      have hqa' : Par (F.q a) (-d.1, -d.2) := triStep_end hS1 kk' fl' hk' hpa hqa (F.hok a)
      have hcrsA : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
      have hlt01 : t0 < t1 := lt_of_le_of_lt h2 h3
      set σ : ℝ := (T1 - t0) / (t1 - t0) with hσ
      have hσ0 : 0 ≤ σ := div_nonneg (by linarith) (by linarith)
      have hσ1 : σ < 1 := by rw [hσ, div_lt_one (by linarith)]; linarith
      have hσm : σ * (t1 - t0) = T1 - t0 := by
        have hne : t1 - t0 ≠ 0 := by linarith
        rw [hσ]; exact div_mul_cancel₀ _ hne
      have hY1 : Y1 = e.2.1 + σ • (e.2.2 - e.2.1) := by
        have d0 := coords_of_toV2 h0
        have d1 := coords_of_toV2 h1
        apply pt_ext
        · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          rw [c1.1, d0.1, d1.1]; linear_combination (-d.1) * hσm
        · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          rw [c1.2, d0.2, d1.2]; linear_combination (-d.2) * hσm
      have hqb : ∃ b : AtV D Y1, Par (F.q b) d := by
        obtain ⟨kkS, fS, gS, hkS, hfS, hfkS, hgkS, hgfS, hparS, hleftS⟩ := id hSe
        rcases hσ0.eq_or_lt with h00 | hpos
        · 
          have hY1e : Y1 = e.2.1 := by rw [hY1, ← h00]; simp
          subst hY1e
          have hmemb : e.2.1 ∈ (D.tile e.1).carrier := by rw [← hfS]; exact subset_convexHull ℝ _ ⟨fS, rfl⟩
          set b : AtV D e.2.1 := ⟨e.1, hmemb⟩
          obtain ⟨kk2, fl2, hk2, hpb, hqb'⟩ := spec_corner_data (F.hspec b) ⟨fS, hfS⟩
          have := triStep_end hSe kk2 fl2 hk2 hpb hqb' (F.hok b)
          exact ⟨b, by rw [neg2_neg2] at this; exact this⟩
        · 
          have hσ1' : 0 < 1 - σ := by linarith
          have hσ2' : 1 - σ < 1 := by linarith
          obtain ⟨hmemb, hnv, hline⟩ := step_interior_pt hSe hσ1' hσ2'
          have hYe : e.2.2 + (1 - σ) • (e.2.1 - e.2.2) = Y1 := by
            rw [hY1]; ext i; simp; ring
          rw [hYe] at hmemb hnv hline
          set b : AtV D Y1 := ⟨e.1, hmemb⟩
          obtain ⟨hpar, hq⟩ := straight_dir b (F.hok b) (F.hloc b) (F.hspec b) hnv hSe hline
          refine ⟨b, ?_⟩
          rw [hq]
          have := par_neg hpar
          rw [neg2_neg2] at this
          exact this
      obtain ⟨b, hb⟩ := hqb
      obtain ⟨c, hcrs, hcp⟩ := F.ray_left a b hcrsA hqa' hb
      have hcorner : ∃ k, (D.tile c.1).pts k = Y1 := by
        rcases F.hspec c with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
        · exact ⟨k, hk⟩
        · exfalso
          rw [hq] at hcrs
          unfold crs at hcrs; simp only at hcrs; nlinarith
      obtain ⟨kk3, fl3, hk3, hp3, hq3⟩ := spec_corner_data (F.hspec c) hcorner
      exact hno1 c.1 _ (triStep_of_start kk3 fl3 hk3 hp3 hq3 hcrs hcp)
    · exact heq
    · 
      exfalso
      obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkT_cover W1 hT1e hd T2 hT2 hgt
      have hSe := walkT_mem_step W1 e he
      obtain ⟨i2, U2, hmem2, hS2⟩ := walkR_last W2 hL2
      obtain ⟨kkR, fR, gR, hkR, hfR, -⟩ := id hS2
      have hvert : ∃ j k, (D.tile j).pts k = Y2 := ⟨i2, kkR, hkR⟩
      obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D) Y2 hvert
      have hmemA : Y2 ∈ (D.tile i2).carrier := hkR ▸ subset_convexHull ℝ _ ⟨kkR, rfl⟩
      set a : AtV D Y2 := ⟨i2, hmemA⟩ with ha
      obtain ⟨kk', fl', hk', hpa, hqa⟩ := spec_corner_data (F.hspec a) ⟨kkR, hkR⟩
      have hpa' : Par (F.p a) (neg2 d) := triStep_start hS2 kk' fl' hk' hpa hqa (F.hok a)
      have hcrsA : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
      have hlt01 : t0 < t1 := lt_of_le_of_lt h2 h3
      set σ : ℝ := (T2 - t0) / (t1 - t0) with hσ
      have hσ0 : 0 ≤ σ := div_nonneg (by linarith) (by linarith)
      have hσ1 : σ < 1 := by rw [hσ, div_lt_one (by linarith)]; linarith
      have hσm : σ * (t1 - t0) = T2 - t0 := by
        have hne : t1 - t0 ≠ 0 := by linarith
        rw [hσ]; exact div_mul_cancel₀ _ hne
      have hY2 : Y2 = e.2.1 + σ • (e.2.2 - e.2.1) := by
        have d0 := coords_of_toV2 h0
        have d1 := coords_of_toV2 h1
        apply pt_ext
        · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          rw [c2.1, d0.1, d1.1]; linear_combination (-d.1) * hσm
        · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          rw [c2.2, d0.2, d1.2]; linear_combination (-d.2) * hσm
      have hpb : ∃ b : AtV D Y2, Par (F.p b) d := by
        obtain ⟨kkS, fS, gS, hkS, hfS, hfkS, hgkS, hgfS, hparS, hleftS⟩ := id hSe
        rcases hσ0.eq_or_lt with h00 | hpos
        · have hY2e : Y2 = e.2.1 := by rw [hY2, ← h00]; simp
          subst hY2e
          have hmemb : e.2.1 ∈ (D.tile e.1).carrier := by rw [← hkS]; exact subset_convexHull ℝ _ ⟨kkS, rfl⟩
          set b : AtV D e.2.1 := ⟨e.1, hmemb⟩
          obtain ⟨kk2, fl2, hk2, hpb, hqb'⟩ := spec_corner_data (F.hspec b) ⟨kkS, hkS⟩
          exact ⟨b, triStep_start hSe kk2 fl2 hk2 hpb hqb' (F.hok b)⟩
        · obtain ⟨hmemb, hnv, hline⟩ := step_interior_pt hSe hpos hσ1
          rw [← hY2] at hmemb hnv hline
          set b : AtV D Y2 := ⟨e.1, hmemb⟩
          obtain ⟨hpar, -⟩ := straight_dir b (F.hok b) (F.hloc b) (F.hspec b) hnv hSe hline
          exact ⟨b, hpar⟩
      obtain ⟨b, hb⟩ := hpb
      obtain ⟨c, hcrs, hcq⟩ := F.ray_right a b hcrsA hpa' hb
      have hcorner : ∃ k, (D.tile c.1).pts k = Y2 := by
        rcases F.hspec c with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
        · exact ⟨k, hk⟩
        · exfalso
          rw [hq] at hcrs
          unfold crs at hcrs; simp only at hcrs; nlinarith
      obtain ⟨kk3, fl3, hk3, hp3, hq3⟩ := spec_corner_data (F.hspec c) hcorner
      exact hno2 c.1 _ (triStep_of_end kk3 fl3 hk3 hp3 hq3 hcrs hcq)
  have hY : Y1 = Y2 := by
    apply pt_ext
    · rw [c1.1, c2.1, hTeq]
    · rw [c1.2, c2.2, hTeq]
  exact hY
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
theorem arm_lens (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (i : Fin N) (kk : Fin 3) (fl : Bool) :
    nsq (toV2 ((D.tile i).pts (armP kk fl) - (D.tile i).pts kk)) = slen D (idx i (armQ kk fl)) ^ 2 ∧
    nsq (toV2 ((D.tile i).pts (armQ kk fl) - (D.tile i).pts kk)) = slen D (idx i (armP kk fl)) ^ 2 := by
  rw [nsq_toV2_sub, nsq_toV2_sub]
  have h1 := side_len_01 D idx hidx i kk
  have h2 := side_len_02 D idx hidx i kk
  cases fl
  · simp only [armP, armQ, Bool.false_eq_true, if_false]
    rw [dist_comm, h1, dist_comm, h2]; exact ⟨rfl, rfl⟩
  · simp only [armP, armQ, if_true]
    rw [dist_comm, h2, dist_comm, h1]; exact ⟨rfl, rfl⟩
theorem slen_pos (D : CongruentRegionDissection N) (t : Fin 3) : 0 < slen D t := by
  unfold slen
  apply dist_pos.mpr
  intro h
  exact fin3_add_ne t (D.model.indep.injective h)
theorem slen_sq_eq_iff (D : CongruentRegionDissection N) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) (t : Fin 3) :
    slen D t ^ 2 = slen D 0 ^ 2 ↔ t = 0 := by
  constructor
  · intro h
    have h' : slen D t = slen D 0 := by
      have := slen_pos D t
      have := slen_pos D 0
      nlinarith [sq_nonneg (slen D t - slen D 0), sq_nonneg (slen D t + slen D 0)]
    fin_cases t
    · rfl
    · exact absurd h'.symm hab
    · exact absurd h'.symm hac
  · rintro rfl; rfl
end Erdos634.Draft.LaczFormal.RG
end

section
open Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
def NotComb (a b c : ℝ) : Prop := ∀ r p q : ℕ, 0 < r → (r : ℝ) * a ≠ p * b + q * c
theorem sum_abc (a b c : ℝ) (ds : List ℝ) (h : ∀ x ∈ ds, x = a ∨ x = b ∨ x = c) :
    ∃ na nb nc : ℕ, ds.sum = na * a + nb * b + nc * c ∧ ((∃ x ∈ ds, x ≠ a) → 1 ≤ nb + nc) := by
  induction ds with
  | nil => exact ⟨0, 0, 0, by simp, by simp⟩
  | cons x ds ih =>
    obtain ⟨na, nb, nc, hs, hn⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases h x (List.mem_cons_self ..) with hx | hx | hx
    · refine ⟨na + 1, nb, nc, ?_, ?_⟩
      · simp only [List.sum_cons]; rw [hs, hx]; push_cast; ring
      · rintro ⟨y, hy, hya⟩
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact absurd hx hya
        · exact hn ⟨y, hy', hya⟩
    · refine ⟨na, nb + 1, nc, ?_, ?_⟩
      · simp only [List.sum_cons]; rw [hs, hx]; push_cast; ring
      · intro _; omega
    · refine ⟨na, nb, nc + 1, ?_, ?_⟩
      · simp only [List.sum_cons]; rw [hs, hx]; push_cast; ring
      · intro _; omega
def RunEnd (a : ℝ) (L : List (Fin N × Plane × Plane)) (H : Plane) : Prop :=
  ∃ L' e L'', L = L' ++ e :: L'' ∧ L' ≠ [] ∧ (∀ x ∈ L', dist x.2.1 x.2.2 = a) ∧ dist e.2.1 e.2.2 ≠ a ∧ H = e.2.1
theorem list_first_not {α : Type*} (P : α → Prop) (L : List α) (hL : ∀ e ∈ L.head?, P e) (hne : L ≠ [])
    (hex : ∃ e ∈ L, ¬ P e) : ∃ L' e L'', L = L' ++ e :: L'' ∧ L' ≠ [] ∧ (∀ x ∈ L', P x) ∧ ¬ P e := by
  induction L with
  | nil => exact absurd rfl hne
  | cons x L ih =>
    have hx : P x := hL x (by simp)
    by_cases hL' : ∃ e ∈ L, ¬ P e
    · by_cases hLne : L = []
      · subst hLne; simp at hL'
      · 
        by_cases hh : ∀ e ∈ L.head?, P e
        · obtain ⟨L', e, L'', hL, hL'ne, hall, hnot⟩ := ih hh hLne hL'
          refine ⟨x :: L', e, L'', ?_, by simp, ?_, hnot⟩
          · rw [hL]; rfl
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact hx
            · exact hall y hy'
        · push_neg at hh
          obtain ⟨e, he, hnot⟩ := hh
          cases L with
          | nil => simp at hLne
          | cons y L2 =>
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
            subst he
            exact ⟨[x], _, L2, rfl, by simp, by simpa using hx, hnot⟩
    · push_neg at hL'
      obtain ⟨e, he, hnot⟩ := hex
      rcases List.mem_cons.mp he with he1 | he'
      · rw [he1] at hnot; exact absurd hx hnot
      · exact absurd (hL' e he') hnot
theorem par_arm_neg {A B : Plane} {d : V2} (h : Par (toV2 (B - A)) (neg2 d)) : Par (toV2 (A - B)) d := by
  have := par_neg h
  rw [neg2_neg2] at this
  have e : toV2 (A - B) = (-(toV2 (B - A)).1, -(toV2 (B - A)).2) := by unfold toV2; ext <;> simp
  rw [e]; exact this
end Erdos634.Draft.LaczFormal.Graph
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
theorem exists_maxwalkT (D : RegionDissection N) {d : V2} (hd : d ≠ 0) {X : Plane} (hX : ∃ j k, (D.tile j).pts k = X) :
    ∃ Y L, WalkT D d X Y L ∧ ∀ i U', ¬ TriStep (D.tile i) d Y U' := by
  classical
  have hnd : 0 < nsq d := nsq_pos hd
  set F : Plane → Finset Plane := fun U => (vtxSet D).filter (fun v => dt d (toV2 (v - X)) > dt d (toV2 (U - X))) with hF
  have key : ∀ n : ℕ, ∀ U : Plane, (F U).card = n → (∃ j k, (D.tile j).pts k = U) →
      ∃ Y L, WalkT D d U Y L ∧ ∀ i U', ¬ TriStep (D.tile i) d Y U' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro U hcard hvert
      by_cases hstep : ∃ i U', TriStep (D.tile i) d U U'
      · obtain ⟨i, U', hS⟩ := hstep
        obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := id hS
        obtain ⟨c, hc, hcw⟩ := hpar.smul
        have hdec : toV2 (U' - X) = ((toV2 (U' - U)).1 + (toV2 (U - X)).1, (toV2 (U' - U)).2 + (toV2 (U - X)).2) := by
          unfold toV2; ext <;> simp
        have hdt : dt d (toV2 (U' - X)) > dt d (toV2 (U - X)) := by
          rw [hdec, hcw]
          unfold dt nsq at *; try simp only; nlinarith [mul_pos hc hnd]
        have hvert' : ∃ j k, (D.tile j).pts k = U' := ⟨i, f, hf⟩
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
        obtain ⟨Y, L, hW, hY⟩ := ih (F U').card hlt U' rfl hvert'
        exact ⟨Y, (i, U, U') :: L, WalkT.cons hS hW, hY⟩
      · push_neg at hstep
        exact ⟨U, [], WalkT.nil U, hstep⟩
  exact key _ X rfl hX
theorem exists_maxwalkR (D : RegionDissection N) {d : V2} (hd : d ≠ 0) {X : Plane} (hX : ∃ j k, (D.tile j).pts k = X) :
    ∃ Y L, WalkR D d X Y L ∧ ∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y := by
  classical
  have hnd : 0 < nsq d := nsq_pos hd
  set F : Plane → Finset Plane := fun U => (vtxSet D).filter (fun v => dt d (toV2 (v - X)) > dt d (toV2 (U - X))) with hF
  have key : ∀ n : ℕ, ∀ U : Plane, (F U).card = n → (∃ j k, (D.tile j).pts k = U) →
      ∃ Y L, WalkR D d U Y L ∧ ∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro U hcard hvert
      by_cases hstep : ∃ i U', TriStep (D.tile i) (neg2 d) U' U
      · obtain ⟨i, U', hS⟩ := hstep
        obtain ⟨kk, f, g, hk, hf, -, -, -, hpar, -⟩ := id hS
        obtain ⟨c, hc, hcw⟩ := hpar.smul
        have hUU' : toV2 (U' - U) = (c * d.1, c * d.2) := by
          have : toV2 (U' - U) = (-(toV2 (U - U')).1, -(toV2 (U - U')).2) := by
            unfold toV2; ext <;> simp
          rw [this, hcw]; unfold neg2; ext <;> simp
        have hdec : toV2 (U' - X) = ((toV2 (U' - U)).1 + (toV2 (U - X)).1, (toV2 (U' - U)).2 + (toV2 (U - X)).2) := by
          unfold toV2; ext <;> simp
        have hdt : dt d (toV2 (U' - X)) > dt d (toV2 (U - X)) := by
          rw [hdec, hUU']
          unfold dt nsq at *; try simp only; nlinarith [mul_pos hc hnd]
        have hvert' : ∃ j k, (D.tile j).pts k = U' := ⟨i, kk, hk⟩
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
        obtain ⟨Y, L, hW, hY⟩ := ih (F U').card hlt U' rfl hvert'
        exact ⟨Y, (i, U, U') :: L, WalkR.cons hS hW, hY⟩
      · push_neg at hstep
        exact ⟨U, [], WalkR.nil U, hstep⟩
  exact key _ X rfl hX
theorem exists_maxseg (D : RegionDissection N) [HasFansC D] {d : V2} (hd : d ≠ 0) {X : Plane} (hX : ∃ j k, (D.tile j).pts k = X)
    (hl : ∃ i U', TriStep (D.tile i) d X U') (hr : ∃ i U', TriStep (D.tile i) (neg2 d) U' X) :
    ∃ Y L1 L2, WalkT D d X Y L1 ∧ WalkR D d X Y L2 ∧ L1 ≠ [] ∧ L2 ≠ [] ∧
      (∀ i U', ¬ TriStep (D.tile i) d Y U') ∧ (∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y) := by
  obtain ⟨Y1, L1, W1, hno1⟩ := exists_maxwalkT D hd hX
  obtain ⟨Y2, L2, W2, hno2⟩ := exists_maxwalkR D hd hX
  have hL1 : L1 ≠ [] := by
    rintro rfl
    cases W1
    obtain ⟨i, U', hS⟩ := hl
    exact hno1 i U' hS
  have hL2 : L2 ≠ [] := by
    rintro rfl
    cases W2
    obtain ⟨i, U', hS⟩ := hr
    exact hno2 i U' hS
  have hY : Y1 = Y2 := ends_coincide D hd hL1 hL2 W1 W2 hno1 hno2
  subst hY
  exact ⟨Y1, L1, L2, W1, W2, hL1, hL2, hno1, hno2⟩
theorem walkR_dist_sum {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) : (L.map fun e => dist e.2.1 e.2.2).sum = dist X Y := by
  induction W with
  | nil X => simp
  | @cons i X X' Y L hS W ih =>
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    obtain ⟨T, hT, hTe, -⟩ := walkR_progress W
    have h1 : toV2 (X' - X) = (c * d.1, c * d.2) := by
      have : toV2 (X' - X) = (-(toV2 (X - X')).1, -(toV2 (X - X')).2) := by
        unfold toV2; ext <;> simp
      rw [this, hcw]; unfold neg2; ext <;> simp
    have hXY : toV2 (Y - X) = ((c + T) * d.1, (c + T) * d.2) := by
      have : toV2 (Y - X) = ((toV2 (Y - X')).1 + (toV2 (X' - X)).1, (toV2 (Y - X')).2 + (toV2 (X' - X)).2) := by
        unfold toV2; ext <;> simp
      rw [this, hTe, h1]; ext <;> simp <;> ring
    have d1 := dist_of_toV2 hc.le h1
    have d2 := dist_of_toV2 hT hTe
    have d3 := dist_of_toV2 (by positivity : 0 ≤ c + T) hXY
    simp only [List.map_cons, List.sum_cons]
    rw [ih, dist_comm X X', d1, dist_comm X' Y, d2, dist_comm X Y, d3]
    ring
theorem arun_end (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} {X Y : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    {e1 e2 : Fin N × Plane × Plane} {L1' L2' : List (Fin N × Plane × Plane)} (h1 : L1 = e1 :: L1') (h2 : L2 = e2 :: L2')
    (hf2 : dist e2.2.1 e2.2.2 ≠ slen D 0) : ∃ e ∈ L1, dist e.2.1 e.2.2 ≠ slen D 0 := by
  by_contra hall
  push_neg at hall
  have hs1 := walkT_dist_sum W1
  have hs2 := walkR_dist_sum W2
  have hsum1 : (L1.map fun e => dist e.2.1 e.2.2).sum = L1.length • slen D 0 := by
    have : (L1.map fun e => dist e.2.1 e.2.2).sum = (L1.map fun e => dist e.2.1 e.2.2).length • slen D 0 := by
      apply List.sum_eq_card_nsmul
      intro x hx
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
      exact hall e' he'
    rw [this, List.length_map]
  have hmemR : ∀ e ∈ L2, dist e.2.1 e.2.2 = slen D 0 ∨ dist e.2.1 e.2.2 = slen D 1 ∨ dist e.2.1 e.2.2 = slen D 2 := by
    intro e he
    have := side_len_mem D idx hidx (walkR_mem_step W2 e he)
    rw [dist_comm] at this
    exact this
  obtain ⟨na, nb, nc, hsum2, hn⟩ := sum_abc (slen D 0) (slen D 1) (slen D 2) (L2.map fun e => dist e.2.1 e.2.2)
    (by
      intro x hx
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
      exact hmemR e' he')
  have hnb : 1 ≤ nb + nc := by
    apply hn
    refine ⟨dist e2.2.1 e2.2.2, ?_, hf2⟩
    apply List.mem_map.mpr
    exact ⟨e2, by rw [h2]; exact List.mem_cons_self .., rfl⟩
  have hEq : (L1.length : ℝ) * slen D 0 = na * slen D 0 + nb * slen D 1 + nc * slen D 2 := by
    have := hs1.trans hs2.symm
    rw [hsum1, hsum2] at this
    simpa [nsmul_eq_mul] using this
  have hb := slen_pos D 1
  have hc := slen_pos D 2
  have ha := slen_pos D 0
  have hpos : (0 : ℝ) < nb * slen D 1 + nc * slen D 2 := by
    by_cases hnb0 : nb = 0
    · have h1 : 1 ≤ nc := by omega
      have h2 : (1 : ℝ) ≤ nc := by exact_mod_cast h1
      subst hnb0
      simp only [Nat.cast_zero, zero_mul, zero_add]
      nlinarith
    · have h2 : (1 : ℝ) ≤ nb := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnb0
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) nc) hc.le]
  have hlt : (na : ℝ) < L1.length := by
    by_contra hge
    push_neg at hge
    nlinarith [mul_le_mul_of_nonneg_right hge ha.le]
  have hlt' : na < L1.length := by exact_mod_cast hlt
  refine hnc (L1.length - na) nb nc (by omega) ?_
  rw [Nat.cast_sub hlt'.le]
  linear_combination hEq
def NoBack (D : RegionDissection N) (d : V2) (X : Plane) : Prop :=
  (∀ i A B (σ : ℝ), TriStep (D.tile i) d A B → 0 < σ → σ ≤ 1 → X ≠ A + σ • (B - A)) ∧
  (∀ i A B (σ : ℝ), TriStep (D.tile i) (neg2 d) A B → 0 < σ → σ ≤ 1 → X ≠ B + σ • (A - B))
def GaEdge (D : RegionDissection N) (a : ℝ) (X H : Plane) : Prop :=
  ∃ (d : V2) (Y : Plane) (L1 L2 : List (Fin N × Plane × Plane)),
    d ≠ 0 ∧ NoBack D d X ∧ WalkT D d X Y L1 ∧ WalkR D d X Y L2 ∧ L1 ≠ [] ∧ L2 ≠ [] ∧
    (∀ i U', ¬ TriStep (D.tile i) d Y U') ∧ (∀ i U', ¬ TriStep (D.tile i) (neg2 d) U' Y) ∧
    ((RunEnd a L1 H ∧ ∀ e ∈ L2.head?, dist e.2.1 e.2.2 ≠ a) ∨
     (RunEnd a L2 H ∧ ∀ e ∈ L1.head?, dist e.2.1 e.2.2 ≠ a))
theorem left_step_unique (D : RegionDissection N) [HasFansC D] {d : V2} {X : Plane} {i i' : Fin N} {U U' : Plane}
    (h1 : TriStep (D.tile i) d X U) (h2 : TriStep (D.tile i') d X U') : i = i' ∧ U = U' := by
  classical
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := id h1
  obtain ⟨kk', f', g', hk', hf', hfk', hgk', hgf', hpar', hleft'⟩ := id h2
  have hvert : ∃ j k, (D.tile j).pts k = X := ⟨i, kk, hk⟩
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D) X hvert
  have hmem : X ∈ (D.tile i).carrier := hk ▸ subset_convexHull ℝ _ ⟨kk, rfl⟩
  have hmem' : X ∈ (D.tile i').carrier := hk' ▸ subset_convexHull ℝ _ ⟨kk', rfl⟩
  set s : AtV D X := ⟨i, hmem⟩
  set s' : AtV D X := ⟨i', hmem'⟩
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec s) ⟨kk, hk⟩
  obtain ⟨kk3, fl3, hk3, hp3, hq3⟩ := spec_corner_data (F.hspec s') ⟨kk', hk'⟩
  have hps : Par (F.p s) d := triStep_start h1 kk2 fl2 hk2 hp2 hq2 (F.hok s)
  have hps' : Par (F.p s') d := triStep_start h2 kk3 fl3 hk3 hp3 hq3 (F.hok s')
  have hdis := tiles_disjoint D X F.p F.q F.hloc
  have hss : s = s' := by
    by_contra hne
    exact start_inj F.p F.q F.hok hdis hne (hps'.trans hps.symm)
  have hii : i = i' := congrArg Subtype.val hss
  subst hii
  refine ⟨rfl, ?_⟩
  have hkk : kk = kk' := (D.tile i).indep.injective (hk.trans hk'.symm)
  subst hkk
  have hff : f = f' := by
    apply arm_unique (D.tile i) X kk hk f f' hfk hfk' d
    · rw [← hf] at hpar; exact hpar
    · rw [← hf'] at hpar'; exact hpar'
  rw [← hf, ← hf', hff]
theorem right_step_unique (D : RegionDissection N) [HasFansC D] {d : V2} {X : Plane} {i i' : Fin N} {U U' : Plane}
    (h1 : TriStep (D.tile i) (neg2 d) U X) (h2 : TriStep (D.tile i') (neg2 d) U' X) : i = i' ∧ U = U' := by
  classical
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := id h1
  obtain ⟨kk', f', g', hk', hf', hfk', hgk', hgf', hpar', hleft'⟩ := id h2
  have hvert : ∃ j k, (D.tile j).pts k = X := ⟨i, f, hf⟩
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D) X hvert
  have hmem : X ∈ (D.tile i).carrier := hf ▸ subset_convexHull ℝ _ ⟨f, rfl⟩
  have hmem' : X ∈ (D.tile i').carrier := hf' ▸ subset_convexHull ℝ _ ⟨f', rfl⟩
  set s : AtV D X := ⟨i, hmem⟩
  set s' : AtV D X := ⟨i', hmem'⟩
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec s) ⟨f, hf⟩
  obtain ⟨kk3, fl3, hk3, hp3, hq3⟩ := spec_corner_data (F.hspec s') ⟨f', hf'⟩
  have hqs : Par (F.q s) (-(neg2 d).1, -(neg2 d).2) := triStep_end h1 kk2 fl2 hk2 hp2 hq2 (F.hok s)
  have hqs' : Par (F.q s') (-(neg2 d).1, -(neg2 d).2) := triStep_end h2 kk3 fl3 hk3 hp3 hq3 (F.hok s')
  have hdis := tiles_disjoint D X F.p F.q F.hloc
  have hss : s = s' := by
    by_contra hne
    exact end_inj' F.p F.q F.hok hdis hne (hqs'.trans hqs.symm)
  have hii : i = i' := congrArg Subtype.val hss
  subst hii
  refine ⟨rfl, ?_⟩
  have hff : f = f' := (D.tile i).indep.injective (hf.trans hf'.symm)
  subst hff
  have hP1 : Par (toV2 (U - X)) d := par_arm_neg hpar
  have hP2 : Par (toV2 (U' - X)) d := par_arm_neg hpar'
  have hkk : kk = kk' := by
    apply arm_unique (D.tile i) X f hf kk kk' hfk.symm hfk'.symm d
    · rw [hk]; exact hP1
    · rw [hk']; exact hP2
  rw [← hk, ← hk', hkk]
theorem ga_edge_of_local (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} (hd : d ≠ 0) {X : Plane}
    (hX : ∃ j k, (D.tile j).pts k = X) (hnb : NoBack D.toRegionDissection d X)
    {i1 : Fin N} {U1 : Plane} (hl : TriStep (D.tile i1) d X U1) (hla : dist X U1 = slen D 0)
    {i2 : Fin N} {U2 : Plane} (hr : TriStep (D.tile i2) (neg2 d) U2 X) (hra : dist U2 X ≠ slen D 0) :
    ∃ H, GaEdge D.toRegionDissection (slen D 0) X H := by
  obtain ⟨Y, L1, L2, W1, W2, hL1, hL2, hno1, hno2⟩ := exists_maxseg D.toRegionDissection hd hX ⟨i1, U1, hl⟩ ⟨i2, U2, hr⟩
  obtain ⟨e1, L1', hL1e, hS1, he1X⟩ : ∃ e1 L1', L1 = e1 :: L1' ∧ TriStep (D.tile e1.1) d e1.2.1 e1.2.2 ∧ e1.2.1 = X := by
    cases W1 with
    | nil => exact absurd rfl hL1
    | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
  obtain ⟨e2, L2', hL2e, hS2, he2X⟩ : ∃ e2 L2', L2 = e2 :: L2' ∧ TriStep (D.tile e2.1) (neg2 d) e2.2.2 e2.2.1 ∧ e2.2.1 = X := by
    cases W2 with
    | nil => exact absurd rfl hL2
    | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
  rw [he1X] at hS1
  rw [he2X] at hS2
  obtain ⟨hi1, hU1⟩ := left_step_unique D.toRegionDissection hS1 hl
  obtain ⟨hi2, hU2⟩ := right_step_unique D.toRegionDissection hS2 hr
  have hd1 : dist e1.2.1 e1.2.2 = slen D 0 := by rw [he1X, hU1]; exact hla
  have hd2 : dist e2.2.1 e2.2.2 ≠ slen D 0 := by
    rw [he2X, hU2, dist_comm]; exact hra
  obtain ⟨e, he, hne⟩ := arun_end D idx hidx hnc W1 W2 hL1e hL2e hd2
  obtain ⟨L', e0, L'', hdec, hL'ne, hall, hnot⟩ := list_first_not (fun x : Fin N × Plane × Plane => dist x.2.1 x.2.2 = slen D 0) L1
    (by rw [hL1e]; intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx; rw [← hx]; exact hd1)
    hL1 ⟨e, he, hne⟩
  refine ⟨e0.2.1, d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, hno1, hno2, Or.inl ⟨⟨L', e0, L'', hdec, hL'ne, hall, hnot, rfl⟩, ?_⟩⟩
  intro x hx
  rw [hL2e] at hx
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
  rw [← hx]; exact hd2
end Erdos634.Draft.LaczFormal.RG
end

section
open Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
theorem abc_core {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hnc : NotComb a b c) (LA LB : List ℝ)
    (hA : ∀ x ∈ LA, x = a) (hB : ∀ x ∈ LB, x = a ∨ x = b ∨ x = c) (hsum : LA.sum = LB.sum)
    (hex : ∃ x ∈ LB, x ≠ a) : False := by
  have hsA : LA.sum = LA.length • a := List.sum_eq_card_nsmul LA a hA
  obtain ⟨na, nb, nc, hsum2, hn⟩ := sum_abc a b c LB hB
  have hnb : 1 ≤ nb + nc := hn hex
  have hEq : (LA.length : ℝ) * a = na * a + nb * b + nc * c := by
    rw [hsA, hsum2] at hsum
    simpa [nsmul_eq_mul] using hsum
  have hpos : (0 : ℝ) < nb * b + nc * c := by
    by_cases hnb0 : nb = 0
    · have h1 : 1 ≤ nc := by omega
      have h2 : (1 : ℝ) ≤ nc := by exact_mod_cast h1
      subst hnb0
      simp only [Nat.cast_zero, zero_mul, zero_add]
      nlinarith
    · have h2 : (1 : ℝ) ≤ nb := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnb0
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) nc) hc.le]
  have hlt : (na : ℝ) < LA.length := by
    by_contra hge
    push_neg at hge
    nlinarith [mul_le_mul_of_nonneg_right hge ha.le]
  have hlt' : na < LA.length := by exact_mod_cast hlt
  refine hnc (LA.length - na) nb nc (by omega) ?_
  rw [Nat.cast_sub hlt'.le]
  linear_combination hEq
theorem par_refl {v : V2} (hv : v ≠ 0) : Par v v := by
  refine ⟨by unfold crs; ring, ?_⟩
  have := nsq_pos hv
  unfold dt; unfold nsq at this; nlinarith
end Erdos634.Draft.LaczFormal.Graph
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
theorem walkT_split {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) {P : List (Fin N × Plane × Plane)} {e : Fin N × Plane × Plane} {Q : List (Fin N × Plane × Plane)}
    (h : L = P ++ e :: Q) : WalkT D d X e.2.1 P ∧ WalkT D d e.2.1 Y (e :: Q) := by
  induction P generalizing X L with
  | nil =>
    simp only [List.nil_append] at h
    subst h
    cases W with
    | cons hS W' => exact ⟨WalkT.nil _, WalkT.cons hS W'⟩
  | cons x P ih =>
    simp only [List.cons_append] at h
    subst h
    cases W with
    | cons hS W' =>
      obtain ⟨h1, h2⟩ := ih W' rfl
      exact ⟨WalkT.cons hS h1, h2⟩
theorem walkR_split {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) {P : List (Fin N × Plane × Plane)} {e : Fin N × Plane × Plane} {Q : List (Fin N × Plane × Plane)}
    (h : L = P ++ e :: Q) : WalkR D d X e.2.1 P ∧ WalkR D d e.2.1 Y (e :: Q) := by
  induction P generalizing X L with
  | nil =>
    simp only [List.nil_append] at h
    subst h
    cases W with
    | cons hS W' => exact ⟨WalkR.nil _, WalkR.cons hS W'⟩
  | cons x P ih =>
    simp only [List.cons_append] at h
    subst h
    cases W with
    | cons hS W' =>
      obtain ⟨h1, h2⟩ := ih W' rfl
      exact ⟨WalkR.cons hS h1, h2⟩
theorem abc_contra (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} {X Y : Plane}
    {P1 : List (Fin N × Plane × Plane)} {P2 : List (Fin N × Plane × Plane)}
    (W1 : WalkT D.toRegionDissection d X Y P1) (W2 : WalkR D.toRegionDissection d X Y P2)
    (hall : ∀ e ∈ P1, dist e.2.1 e.2.2 = slen D 0) {e2 : Fin N × Plane × Plane} {P2' : List (Fin N × Plane × Plane)}
    (h2 : P2 = e2 :: P2') (hf2 : dist e2.2.1 e2.2.2 ≠ slen D 0) : False := by
  refine abc_core (slen_pos D 0) (slen_pos D 1) (slen_pos D 2) hnc (P1.map fun e => dist e.2.1 e.2.2)
    (P2.map fun e => dist e.2.1 e.2.2) ?_ ?_ ?_ ⟨dist e2.2.1 e2.2.2, ?_, hf2⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact hall e he
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    have := side_len_mem D idx hidx (walkR_mem_step W2 e he)
    rw [dist_comm] at this
    exact this
  · rw [walkT_dist_sum W1, walkR_dist_sum W2]
  · exact List.mem_map.mpr ⟨e2, by rw [h2]; exact List.mem_cons_self .., rfl⟩
theorem abc_contra' (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} {X Y : Plane}
    {P1 : List (Fin N × Plane × Plane)} {P2 : List (Fin N × Plane × Plane)}
    (W1 : WalkT D.toRegionDissection d X Y P1) (W2 : WalkR D.toRegionDissection d X Y P2)
    (hall : ∀ e ∈ P2, dist e.2.1 e.2.2 = slen D 0) {e1 : Fin N × Plane × Plane} {P1' : List (Fin N × Plane × Plane)}
    (h1 : P1 = e1 :: P1') (hf1 : dist e1.2.1 e1.2.2 ≠ slen D 0) : False := by
  refine abc_core (slen_pos D 0) (slen_pos D 1) (slen_pos D 2) hnc (P2.map fun e => dist e.2.1 e.2.2)
    (P1.map fun e => dist e.2.1 e.2.2) ?_ ?_ ?_ ⟨dist e1.2.1 e1.2.2, ?_, hf1⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact hall e he
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact side_len_mem D idx hidx (walkT_mem_step W1 e he)
  · rw [walkT_dist_sum W1, walkR_dist_sum W2]
  · exact List.mem_map.mpr ⟨e1, by rw [h1]; exact List.mem_cons_self .., rfl⟩
theorem ga_head_left (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} (hd : d ≠ 0) {X Y H : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    (hRun : RunEnd (slen D 0) L1 H) (hR2 : ∀ e ∈ L2.head?, dist e.2.1 e.2.2 ≠ slen D 0) :
    ∃ (iA : Fin N) (HA : Plane) (iB : Fin N) (HB : Plane) (iS : Fin N) (V V' : Plane) (σ : ℝ),
      TriStep (D.tile iA) d HA H ∧ dist HA H = slen D 0 ∧ TriStep (D.tile iB) d H HB ∧ dist H HB ≠ slen D 0 ∧
      TriStep (D.tile iS) (neg2 d) V' V ∧ 0 < σ ∧ σ < 1 ∧ H = V + σ • (V' - V) ∧ H ≠ X := by
  classical
  obtain ⟨L', e0, L'', hdec, hL'ne, hall, hnot, hH⟩ := hRun
  obtain ⟨hpre, hsuf⟩ := walkT_split W1 hdec
  subst hH
  obtain ⟨iA, HA, hmemA, hSA⟩ := walkT_last hpre hL'ne
  have hdA : dist HA e0.2.1 = slen D 0 := hall (iA, HA, e0.2.1) hmemA
  have hmem0 : e0 ∈ L1 := by rw [hdec]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hSB := walkT_mem_step W1 e0 hmem0
  obtain ⟨tH, htH, htHe, htHp⟩ := walkT_progress hpre
  have htHpos := htHp hL'ne
  obtain ⟨T', hT', hT'e, hT'p⟩ := walkT_progress hsuf
  have hT'pos := hT'p (by simp)
  have hXY : toV2 (Y - X) = ((tH + T') * d.1, (tH + T') * d.2) := by
    have : toV2 (Y - X) = ((toV2 (Y - e0.2.1)).1 + (toV2 (e0.2.1 - X)).1, (toV2 (Y - e0.2.1)).2 + (toV2 (e0.2.1 - X)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hT'e, htHe]; ext <;> simp <;> ring
  obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkR_cover W2 hXY hd tH htH (by linarith)
  have hSe := walkR_mem_step W2 e he
  have hHX : e0.2.1 ≠ X := by
    intro h
    rw [h] at htHe
    have h1' : tH * d.1 = 0 := by have := congrArg Prod.fst htHe; simpa [toV2] using this.symm
    have h2' : tH * d.2 = 0 := by have := congrArg Prod.snd htHe; simpa [toV2] using this.symm
    exact hd (Prod.ext ((mul_eq_zero.mp h1').resolve_left htHpos.ne') ((mul_eq_zero.mp h2').resolve_left htHpos.ne'))
  have hne0 : t0 ≠ tH := by
    intro hteq
    have hc0 := coords_of_toV2 h0
    have hcH := coords_of_toV2 htHe
    have heH : e.2.1 = e0.2.1 := by
      apply pt_ext
      · rw [hc0.1, hcH.1, hteq]
      · rw [hc0.2, hcH.2, hteq]
    obtain ⟨P, Q, hPQ⟩ := List.append_of_mem he
    obtain ⟨hpreR, -⟩ := walkR_split W2 hPQ
    rw [heH] at hpreR
    have hPne : P ≠ [] := by
      rintro rfl
      cases hpreR
      exact hHX rfl
    obtain ⟨p1, P', hP1⟩ := List.exists_cons_of_ne_nil hPne
    have hhead : dist p1.2.1 p1.2.2 ≠ slen D 0 := by
      apply hR2 p1
      rw [hPQ, hP1]; simp
    exact abc_contra D idx hidx hnc hpre hpreR hall hP1 hhead
  have hlt0 : t0 < tH := lt_of_le_of_ne h2 hne0
  have hlt01 : t0 < t1 := lt_trans hlt0 h3
  set σ : ℝ := (tH - t0) / (t1 - t0) with hσ
  have hσ0 : 0 < σ := div_pos (by linarith) (by linarith)
  have hσ1 : σ < 1 := by rw [hσ, div_lt_one (by linarith)]; linarith
  have hσm : σ * (t1 - t0) = tH - t0 := by
    have hne : t1 - t0 ≠ 0 := by linarith
    rw [hσ]; exact div_mul_cancel₀ _ hne
  refine ⟨iA, HA, e0.1, e0.2.2, e.1, e.2.1, e.2.2, σ, hSA, hdA, hSB, hnot, hSe, hσ0, hσ1, ?_, hHX⟩
  have d0 := coords_of_toV2 h0
  have d1 := coords_of_toV2 h1
  have cH := coords_of_toV2 htHe
  apply pt_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [cH.1, d0.1, d1.1]; linear_combination (-d.1) * hσm
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [cH.2, d0.2, d1.2]; linear_combination (-d.2) * hσm
theorem ga_head_right (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} (hd : d ≠ 0) {X Y H : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    (hRun : RunEnd (slen D 0) L2 H) (hL1 : ∀ e ∈ L1.head?, dist e.2.1 e.2.2 ≠ slen D 0) :
    ∃ (iA : Fin N) (HA : Plane) (iB : Fin N) (HB : Plane) (iS : Fin N) (V V' : Plane) (σ : ℝ),
      TriStep (D.tile iA) (neg2 d) H HA ∧ dist HA H = slen D 0 ∧ TriStep (D.tile iB) (neg2 d) HB H ∧ dist H HB ≠ slen D 0 ∧
      TriStep (D.tile iS) d V V' ∧ 0 < σ ∧ σ < 1 ∧ H = V + σ • (V' - V) ∧ H ≠ X := by
  classical
  obtain ⟨L', e0, L'', hdec, hL'ne, hall, hnot, hH⟩ := hRun
  obtain ⟨hpre, hsuf⟩ := walkR_split W2 hdec
  subst hH
  obtain ⟨iA, HA, hmemA, hSA⟩ := walkR_last hpre hL'ne
  have hdA : dist HA e0.2.1 = slen D 0 := hall (iA, HA, e0.2.1) hmemA
  have hmem0 : e0 ∈ L2 := by rw [hdec]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hSB := walkR_mem_step W2 e0 hmem0
  obtain ⟨tH, htH, htHe, htHp⟩ := walkR_progress hpre
  have htHpos := htHp hL'ne
  obtain ⟨T', hT', hT'e, hT'p⟩ := walkR_progress hsuf
  have hT'pos := hT'p (by simp)
  have hXY : toV2 (Y - X) = ((tH + T') * d.1, (tH + T') * d.2) := by
    have : toV2 (Y - X) = ((toV2 (Y - e0.2.1)).1 + (toV2 (e0.2.1 - X)).1, (toV2 (Y - e0.2.1)).2 + (toV2 (e0.2.1 - X)).2) := by
      unfold toV2; ext <;> simp
    rw [this, hT'e, htHe]; ext <;> simp <;> ring
  obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkT_cover W1 hXY hd tH htH (by linarith)
  have hSe := walkT_mem_step W1 e he
  have hHX : e0.2.1 ≠ X := by
    intro h
    rw [h] at htHe
    have h1' : tH * d.1 = 0 := by have := congrArg Prod.fst htHe; simpa [toV2] using this.symm
    have h2' : tH * d.2 = 0 := by have := congrArg Prod.snd htHe; simpa [toV2] using this.symm
    exact hd (Prod.ext ((mul_eq_zero.mp h1').resolve_left htHpos.ne') ((mul_eq_zero.mp h2').resolve_left htHpos.ne'))
  have hne0 : t0 ≠ tH := by
    intro hteq
    have hc0 := coords_of_toV2 h0
    have hcH := coords_of_toV2 htHe
    have heH : e.2.1 = e0.2.1 := by
      apply pt_ext
      · rw [hc0.1, hcH.1, hteq]
      · rw [hc0.2, hcH.2, hteq]
    obtain ⟨P, Q, hPQ⟩ := List.append_of_mem he
    obtain ⟨hpreT, -⟩ := walkT_split W1 hPQ
    rw [heH] at hpreT
    have hPne : P ≠ [] := by
      rintro rfl
      cases hpreT
      exact hHX rfl
    obtain ⟨p1, P', hP1⟩ := List.exists_cons_of_ne_nil hPne
    have hhead : dist p1.2.1 p1.2.2 ≠ slen D 0 := by
      apply hL1 p1
      rw [hPQ, hP1]; simp
    exact abc_contra' D idx hidx hnc hpreT hpre hall hP1 hhead
  have hlt0 : t0 < tH := lt_of_le_of_ne h2 hne0
  have hlt01 : t0 < t1 := lt_trans hlt0 h3
  set σ : ℝ := (tH - t0) / (t1 - t0) with hσ
  have hσ0 : 0 < σ := div_pos (by linarith) (by linarith)
  have hσ1 : σ < 1 := by rw [hσ, div_lt_one (by linarith)]; linarith
  have hσm : σ * (t1 - t0) = tH - t0 := by
    have hne : t1 - t0 ≠ 0 := by linarith
    rw [hσ]; exact div_mul_cancel₀ _ hne
  refine ⟨iA, HA, e0.1, e0.2.2, e.1, e.2.1, e.2.2, σ, hSA, hdA, hSB, hnot, hSe, hσ0, hσ1, ?_, hHX⟩
  have d0 := coords_of_toV2 h0
  have d1 := coords_of_toV2 h1
  have cH := coords_of_toV2 htHe
  apply pt_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [cH.1, d0.1, d1.1]; linear_combination (-d.1) * hσm
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [cH.2, d0.2, d1.2]; linear_combination (-d.2) * hσm
theorem ga_edge_of_local' (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} (hd : d ≠ 0) {X : Plane}
    (hX : ∃ j k, (D.tile j).pts k = X) (hnb : NoBack D.toRegionDissection d X)
    {i1 : Fin N} {U1 : Plane} (hl : TriStep (D.tile i1) d X U1) (hla : dist X U1 ≠ slen D 0)
    {i2 : Fin N} {U2 : Plane} (hr : TriStep (D.tile i2) (neg2 d) U2 X) (hra : dist U2 X = slen D 0) :
    ∃ H, GaEdge D.toRegionDissection (slen D 0) X H := by
  obtain ⟨Y, L1, L2, W1, W2, hL1, hL2, hno1, hno2⟩ := exists_maxseg D.toRegionDissection hd hX ⟨i1, U1, hl⟩ ⟨i2, U2, hr⟩
  obtain ⟨e1, L1', hL1e, hS1, he1X⟩ : ∃ e1 L1', L1 = e1 :: L1' ∧ TriStep (D.tile e1.1) d e1.2.1 e1.2.2 ∧ e1.2.1 = X := by
    cases W1 with
    | nil => exact absurd rfl hL1
    | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
  obtain ⟨e2, L2', hL2e, hS2, he2X⟩ : ∃ e2 L2', L2 = e2 :: L2' ∧ TriStep (D.tile e2.1) (neg2 d) e2.2.2 e2.2.1 ∧ e2.2.1 = X := by
    cases W2 with
    | nil => exact absurd rfl hL2
    | cons hS W' => exact ⟨_, _, rfl, hS, rfl⟩
  rw [he1X] at hS1
  rw [he2X] at hS2
  obtain ⟨hi1, hU1⟩ := left_step_unique D.toRegionDissection hS1 hl
  obtain ⟨hi2, hU2⟩ := right_step_unique D.toRegionDissection hS2 hr
  have hd1 : dist e1.2.1 e1.2.2 ≠ slen D 0 := by rw [he1X, hU1]; exact hla
  have hd2 : dist e2.2.1 e2.2.2 = slen D 0 := by
    rw [he2X, hU2, dist_comm]; exact hra
  have hex : ∃ e ∈ L2, dist e.2.1 e.2.2 ≠ slen D 0 := by
    by_contra hall
    push_neg at hall
    exact abc_contra' D idx hidx hnc W1 W2 hall hL1e hd1
  obtain ⟨L', e0, L'', hdec, hL'ne, hall, hnot⟩ := list_first_not (fun x : Fin N × Plane × Plane => dist x.2.1 x.2.2 = slen D 0) L2
    (by rw [hL2e]; intro x hx; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx; rw [← hx]; exact hd2)
    hL2 hex
  refine ⟨e0.2.1, d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, hno1, hno2, Or.inr ⟨⟨L', e0, L'', hdec, hL'ne, hall, hnot, rfl⟩, ?_⟩⟩
  intro x hx
  rw [hL1e] at hx
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
  rw [← hx]; exact hd1
theorem ga_edge_of_ray (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ)
    (x y : AtV D.toRegionDissection H) (hcx : 0 < crs (F.p x) (F.q x)) (hcy : 0 < crs (F.p y) (F.q y))
    (hxy : Par (F.p y) (F.q x)) (hnb : NoBack D.toRegionDissection (F.q x) H)
    (hxor : (nsq (F.q x) = slen D 0 ^ 2 ∧ nsq (F.p y) ≠ slen D 0 ^ 2) ∨
            (nsq (F.q x) ≠ slen D 0 ^ 2 ∧ nsq (F.p y) = slen D 0 ^ 2)) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  classical
  have hd : F.q x ≠ 0 := (F.hok x).ne_q
  have hcornx : ∃ k, (D.tile x.1).pts k = H := by
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso; rw [hq] at hcx; unfold crs at hcx; try simp only at hcx; nlinarith
  have horny : ∃ k, (D.tile y.1).pts k = H := by
    rcases F.hspec y with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
    · exact ⟨k, hk⟩
    · exfalso; rw [hq] at hcy; unfold crs at hcy; try simp only at hcy; nlinarith
  obtain ⟨kx, flx, hkx, hpx, hqx⟩ := spec_corner_data (F.hspec x) hcornx
  obtain ⟨ky, fly, hky, hpy, hqy⟩ := spec_corner_data (F.hspec y) horny
  have hstepR := triStep_of_end (T := D.tile x.1) (d := F.q x) kx flx hkx hpx hqx hcx (par_refl hd)
  have hstepL := triStep_of_start (T := D.tile y.1) (d := F.q x) ky fly hky hpy hqy hcy hxy
  have hX : ∃ j k, (D.tile j).pts k = H := ⟨y.1, ky, hky⟩
  have hdL : dist H ((D.tile y.1).pts (armP ky fly)) ^ 2 = nsq (F.p y) := by
    rw [hpy, nsq_toV2_sub, dist_comm]
  have hdR : dist ((D.tile x.1).pts (armQ kx flx)) H ^ 2 = nsq (F.q x) := by
    rw [hqx, nsq_toV2_sub]
  rcases hxor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · 
    have hra : dist ((D.tile x.1).pts (armQ kx flx)) H = slen D 0 := by
      have := hdR.trans h1
      exact (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).mp this
    have hla : dist H ((D.tile y.1).pts (armP ky fly)) ≠ slen D 0 := by
      intro h; apply h2; rw [← hdL, h]
    exact ga_edge_of_local' D idx hidx hnc hd hX hnb hstepL hla hstepR hra
  · have hla : dist H ((D.tile y.1).pts (armP ky fly)) = slen D 0 := by
      have := hdL.trans h2
      exact (pow_left_inj₀ dist_nonneg (slen_pos D 0).le two_ne_zero).mp this
    have hra : dist ((D.tile x.1).pts (armQ kx flx)) H ≠ slen D 0 := by
      intro h; apply h1; rw [← hdR, h]
    exact ga_edge_of_local D idx hidx hnc hd hX hnb hstepL hla hstepR hra
end Erdos634.Draft.LaczFormal.RG
end

section
open Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
namespace ExtFan
variable {D : Dissection N} {V : Plane} {κ : Type} [Fintype κ]
end ExtFan
theorem par_neg_arm {A B : Plane} {d : V2} (h : Par (toV2 (B - A)) d) : Par (toV2 (A - B)) (neg2 d) := by
  have := par_neg h
  have e : toV2 (A - B) = (-(toV2 (B - A)).1, -(toV2 (B - A)).2) := by unfold toV2; ext <;> simp
  rw [e]; exact this
theorem sq_ne_of_ne {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ≠ y) : x ^ 2 ≠ y ^ 2 := by
  intro h2
  exact h ((pow_left_inj₀ hx hy two_ne_zero).mp h2)
theorem qarm_eq {T : Tri} {V : Plane} {kk' : Fin 3} (fl' : Bool) (hk' : T.pts kk' = V) {W : Plane} {w : Fin 3}
    (hw : T.pts w = W) (hwk : w ≠ kk') {v : V2} (hq : Par (toV2 (T.pts (armQ kk' fl') - V)) v)
    (hW : Par (toV2 (W - V)) v) : T.pts (armQ kk' fl') = W := by
  have := arm_unique T V kk' hk' (armQ kk' fl') w (armQ_ne kk' fl') hwk v hq (by rw [hw]; exact hW)
  rw [this, hw]
theorem parm_eq {T : Tri} {V : Plane} {kk' : Fin 3} (fl' : Bool) (hk' : T.pts kk' = V) {W : Plane} {w : Fin 3}
    (hw : T.pts w = W) (hwk : w ≠ kk') {v : V2} (hq : Par (toV2 (T.pts (armP kk' fl') - V)) v)
    (hW : Par (toV2 (W - V)) v) : T.pts (armP kk' fl') = W := by
  have := arm_unique T V kk' hk' (armP kk' fl') w (armP_ne kk' fl') hwk v hq (by rw [hw]; exact hW)
  rw [this, hw]
theorem neg2_neg2' (d : V2) : neg2 (neg2 d) = d := by unfold neg2; ext <;> simp
namespace ExtFan
variable {D : Dissection N} {V : Plane} {κ : Type} [Fintype κ]
end ExtFan
end Erdos634.Draft.LaczFormal.Graph
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
namespace ExtFan
variable {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ]
theorem noBack_of_none (F : ExtFan D V κ) {d : V2}
    (hnone : ∀ s : AtV D V, ¬ Par (F.p s) (neg2 d) ∧ ¬ Par (F.q s) (neg2 d)) : NoBack D d V := by
  classical
  constructor
  · intro i A B σ hS h0 h1 hV
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := id hS
    by_cases hσ : σ = 1
    · 
      subst hσ
      have hVB : V = B := by rw [hV]; simp
      have hmem : V ∈ (D.tile i).carrier := by rw [hVB, ← hf]; exact subset_convexHull ℝ _ ⟨f, rfl⟩
      set s : AtV D V := ⟨i, hmem⟩
      obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec s) ⟨f, by rw [hf, hVB]⟩
      have hS' : TriStep (D.tile i) d A V := by rw [hVB]; exact hS
      have := triStep_end hS' kk' fl' hk' hp hq (F.hok s)
      exact (hnone s).2 this
    · have hσ1 : σ < 1 := lt_of_le_of_ne h1 hσ
      obtain ⟨hmemV, hnv, hline⟩ := step_interior_pt hS h0 hσ1
      rw [← hV] at hmemV hnv hline
      set s : AtV D V := ⟨i, hmemV⟩
      obtain ⟨hpar', hq⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnv hS hline
      refine (hnone s).2 ?_
      rw [hq]
      have := par_neg hpar'
      exact this
  · intro i A B σ hS h0 h1 hV
    obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := id hS
    by_cases hσ : σ = 1
    · 
      subst hσ
      have hVA : V = A := by rw [hV]; simp
      have hmem : V ∈ (D.tile i).carrier := by rw [hVA, ← hk]; exact subset_convexHull ℝ _ ⟨kk, rfl⟩
      set s : AtV D V := ⟨i, hmem⟩
      obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec s) ⟨kk, by rw [hk, hVA]⟩
      have hS' : TriStep (D.tile i) (neg2 d) V B := by rw [hVA]; exact hS
      have := triStep_start hS' kk' fl' hk' hp hq (F.hok s)
      exact (hnone s).1 this
    · have hσ1 : σ < 1 := lt_of_le_of_ne h1 hσ
      have hV' : V = A + (1 - σ) • (B - A) := by rw [hV]; ext i; simp; ring
      obtain ⟨hmemV, hnv, hline⟩ := step_interior_pt hS (by linarith : 0 < 1 - σ) (by linarith : 1 - σ < 1)
      rw [← hV'] at hmemV hnv hline
      set s : AtV D V := ⟨i, hmemV⟩
      obtain ⟨hpar', hq⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnv hS hline
      exact (hnone s).1 hpar'
theorem tgt_univ_of_straight (F : ExtFan D V κ) (s t : AtV D V)
    (hs : F.q s = (-(F.p s).1, -(F.p s).2)) {z0 : V2} (hz0 : inInt (F.p t) (F.q t) z0)
    (hz0' : crs (F.p s) z0 < 0) : ∀ z : V2, z ∈ F.Tgt := by
  have hHs : ∀ z : V2, 0 ≤ crs (F.p s) z → z ∈ F.Tgt := by
    intro z hz
    apply F.tile_cone_sub s
    rw [hs]
    exact (inCone_straight_iff _ _).mpr hz
  have hz0T : z0 ∈ F.Tgt := F.tile_cone_sub t ⟨hz0.1.le, hz0.2.le⟩
  intro z
  by_cases hz : 0 ≤ crs (F.p s) z
  · exact hHs z hz
  · push_neg at hz
    set lam : ℝ := crs (F.p s) z / crs (F.p s) z0 with hlam
    have hlam0 : 0 < lam := div_pos_of_neg_of_neg hz hz0'
    set r : V2 := (z.1 - lam * z0.1, z.2 - lam * z0.2) with hr
    have hcr : crs (F.p s) r = 0 := by
      have : crs (F.p s) r = crs (F.p s) z - lam * crs (F.p s) z0 := by
        unfold crs; simp only [hr]; ring
      have h2 : lam * crs (F.p s) z0 = crs (F.p s) z := by rw [hlam]; exact div_mul_cancel₀ _ hz0'.ne
      rw [this, h2]; ring
    have hrT : r ∈ F.Tgt := hHs r (by rw [hcr])
    have hw := F.hTc z0 hz0T r hrT (lam / (lam + 1)) (1 / (lam + 1)) (by positivity) (by positivity) (by field_simp)
    have hz' := F.hTs _ hw (lam + 1) (by positivity)
    have e : ((lam + 1) * (lam / (lam + 1) * z0.1 + 1 / (lam + 1) * r.1),
        (lam + 1) * (lam / (lam + 1) * z0.2 + 1 / (lam + 1) * r.2)) = z := by
      ext <;> simp only [hr] <;> field_simp <;> ring
    rw [e] at hz'
    exact hz'
theorem isEmpty_of_univ (F : ExtFan D V κ) (h : ∀ z : V2, z ∈ F.Tgt) : IsEmpty κ := by
  constructor
  intro j
  obtain ⟨δ, hδ, H⟩ := minus_ray_int (F.hokE j)
  exact F.hextT j _ (H (δ / 2) (by positivity) (by linarith)) (h _)
theorem interior_of_univ (F : ExtFan D V κ) (h : ∀ z : V2, z ∈ F.Tgt) : V ∈ interior D.region := by
  apply interior_maximal (t := Metric.ball V F.R)
  · intro y hy
    exact (F.hT y (by simpa [Metric.mem_ball] using hy)).mpr (h _)
  · exact Metric.isOpen_ball
  · exact Metric.mem_ball_self F.hR
theorem head_cyc (F : ExtFan D V κ) {d : V2} (a b s : AtV D V)
    (hca : 0 < crs (F.p a) (F.q a)) (hqa : Par (F.q a) (neg2 d))
    (hcb : 0 < crs (F.p b) (F.q b)) (hpb : Par (F.p b) d)
    (hps : Par (F.p s) (neg2 d)) (hqs : F.q s = (-(F.p s).1, -(F.p s).2)) :
    IsEmpty κ ∧ V ∈ interior D.region ∧ a ≠ s ∧ b ≠ s ∧ a ≠ b ∧
      ∃ j0 < Fintype.card (AtV D V ⊕ κ), F.e j0 = Sum.inl s ∧ F.e (j0 + 1) = Sum.inl b ∧
        F.e (j0 + (Fintype.card (AtV D V ⊕ κ) - 1)) = Sum.inl a := by
  classical
  obtain ⟨δa, hδa, Ha⟩ := minus_ray_int (F.hok a)
  set zA := zminus (F.q a) (δa / 2) with hzA
  have hzAint : inInt (F.p a) (F.q a) zA := Ha _ (by positivity) (by linarith)
  have hzA_left : 0 < crs d zA := by
    obtain ⟨c', hc', hq'⟩ := hqa.smul
    have h := hzAint.2
    rw [hq'] at h
    by_contra hX; push_neg at hX
    unfold crs at h hX
    unfold neg2 at h
    try simp only at h hX
    nlinarith [mul_nonneg hc'.le (neg_nonneg.mpr hX)]
  have hz0' : crs (F.p s) zA < 0 := by
    obtain ⟨c1, hc1, hp1⟩ := hps.smul
    rw [hp1]
    unfold crs at hzA_left ⊢
    unfold neg2
    try simp only at hzA_left ⊢
    nlinarith [mul_pos hc1 hzA_left]
  have huniv := F.tgt_univ_of_straight s a hqs hzAint hz0'
  have hemp := F.isEmpty_of_univ huniv
  have hint := F.interior_of_univ huniv
  have hdis := tiles_disjoint D V F.p F.q F.hloc
  have hcs : crs (F.p s) (F.q s) = 0 := by rw [hqs]; exact crs_straight _
  have has : a ≠ s := by rintro rfl; linarith
  have hbs : b ≠ s := by rintro rfl; linarith
  have hab : a ≠ b := by
    rintro rfl
    obtain ⟨c1, hc1, hp1⟩ := hpb.smul
    obtain ⟨c2, hc2, hq2⟩ := hqa.smul
    have : crs (F.p a) (F.q a) = 0 := by
      rw [hp1, hq2]; unfold crs neg2; ring
    linarith
  refine ⟨hemp, hint, has, hbs, hab, ?_⟩
  obtain ⟨j0, hj0, hej0⟩ := F.hsurj (Sum.inl s)
  have hP0 := F.hP j0
  rw [hej0] at hP0
  simp only [Sum.elim_inl] at hP0
  rw [hqs] at hP0
  have hsucc : Par (Sum.elim F.p F.pe (F.e (j0 + 1))) d := hP0.trans (by
    have := par_neg hps
    rw [neg2_neg2] at this
    exact this)
  have hnext : F.e (j0 + 1) = Sum.inl b := by
    rcases hn : F.e (j0 + 1) with c | j
    · rw [hn] at hsucc
      simp only [Sum.elim_inl] at hsucc
      by_contra hne
      have hcb' : c ≠ b := by intro h; apply hne; rw [h]
      exact start_inj F.p F.q F.hok hdis (Ne.symm hcb') (hsucc.trans hpb.symm)
    · exact (hemp.false j).elim
  have hkpos : 0 < Fintype.card (AtV D V ⊕ κ) := lt_of_le_of_lt (Nat.zero_le _) hj0
  have hP1 := F.hP (j0 + (Fintype.card (AtV D V ⊕ κ) - 1))
  have hshift : j0 + (Fintype.card (AtV D V ⊕ κ) - 1) + 1 = j0 + Fintype.card (AtV D V ⊕ κ) := by omega
  rw [hshift, F.hper j0, hej0] at hP1
  simp only [Sum.elim_inl] at hP1
  have hpred : Par (Sum.elim F.q F.qe (F.e (j0 + (Fintype.card (AtV D V ⊕ κ) - 1)))) (neg2 d) := hP1.symm.trans hps
  have hprev : F.e (j0 + (Fintype.card (AtV D V ⊕ κ) - 1)) = Sum.inl a := by
    rcases hn : F.e (j0 + (Fintype.card (AtV D V ⊕ κ) - 1)) with c | j
    · rw [hn] at hpred
      simp only [Sum.elim_inl] at hpred
      by_contra hne
      have hca : c ≠ a := by intro h; apply hne; rw [h]
      exact end_inj' F.p F.q F.hok hdis (Ne.symm hca) (hpred.trans hqa.symm)
    · exact (hemp.false j).elim
  exact ⟨j0, hj0, hej0, hnext, hprev⟩
end ExtFan
theorem ga_head_sectors_left (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} (hd : d ≠ 0) {X Y H : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    (hRun : RunEnd (slen D 0) L1 H) (hR2 : ∀ e ∈ L2.head?, dist e.2.1 e.2.2 ≠ slen D 0)
    {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) :
    ∃ a b s : AtV D.toRegionDissection H,
      0 < crs (F.p a) (F.q a) ∧ Par (F.q a) (neg2 d) ∧ 0 < crs (F.p b) (F.q b) ∧ Par (F.p b) d ∧
      Par (F.p s) (neg2 d) ∧ F.q s = (-(F.p s).1, -(F.p s).2) ∧
      nsq (F.q a) = slen D 0 ^ 2 ∧ nsq (F.p b) ≠ slen D 0 ^ 2 ∧ H ≠ X := by
  classical
  obtain ⟨iA, HA, iB, HB, iS, V, V', σ, hSA, hdA, hSB, hdB, hSS, hσ0, hσ1, hHV, hHX⟩ :=
    ga_head_left D idx hidx hnc hd W1 W2 hRun hR2
  have hmemA : H ∈ (D.tile iA).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSA
    rw [← hf]; exact subset_convexHull ℝ _ ⟨f, rfl⟩
  have hmemB : H ∈ (D.tile iB).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSB
    rw [← hk]; exact subset_convexHull ℝ _ ⟨kk, rfl⟩
  obtain ⟨hmemS, hnvS, hlineS⟩ := step_interior_pt hSS (σ := 1 - σ) (by linarith) (by linarith)
  have hHS : V' + (1 - σ) • (V - V') = H := by rw [hHV]; ext i; simp; ring
  rw [hHS] at hmemS hnvS hlineS
  set a : AtV D.toRegionDissection H := ⟨iA, hmemA⟩
  set b : AtV D.toRegionDissection H := ⟨iB, hmemB⟩
  set s : AtV D.toRegionDissection H := ⟨iS, hmemS⟩
  refine ⟨a, b, s, ?_⟩
  obtain ⟨kkA, fA, gA, hkA, hfA, hfkA, hgkA, hgfA, hparA, hleftA⟩ := id hSA
  obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec a) ⟨fA, hfA⟩
  have hqa : Par (F.q a) (neg2 d) := triStep_end hSA kk' fl' hk' hp hq (F.hok a)
  have hca : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
  have hkkA : kk' = fA := (D.tile iA).indep.injective (hk'.trans hfA.symm)
  have hnA : nsq (F.q a) = slen D 0 ^ 2 := by
    have hq' : Par (toV2 ((D.tile iA).pts (armQ kk' fl') - H)) (neg2 d) := hq ▸ hqa
    have hHA : Par (toV2 (HA - H)) (neg2 d) := par_neg_arm hparA
    have := qarm_eq (T := D.tile iA) fl' hk' (W := HA) (w := kkA) hkA (by rw [hkkA]; exact hfkA.symm) hq' hHA
    rw [hq, nsq_toV2_sub, this, hdA]
  obtain ⟨kkB, fB, gB, hkB, hfB, hfkB, hgkB, hgfB, hparB, hleftB⟩ := id hSB
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec b) ⟨kkB, hkB⟩
  have hpb : Par (F.p b) d := triStep_start hSB kk2 fl2 hk2 hp2 hq2 (F.hok b)
  have hcb : 0 < crs (F.p b) (F.q b) := crs_pos_of_corner (F.hok b) (F.hspec b) ⟨kk2, hk2⟩
  have hkkB : kk2 = kkB := (D.tile iB).indep.injective (hk2.trans hkB.symm)
  have hnB : nsq (F.p b) ≠ slen D 0 ^ 2 := by
    have hp' : Par (toV2 ((D.tile iB).pts (armP kk2 fl2) - H)) d := hp2 ▸ hpb
    have := parm_eq (T := D.tile iB) fl2 hk2 (W := HB) (w := fB) hfB (by rw [hkkB]; exact hfkB) hp' hparB
    rw [hp2, nsq_toV2_sub, this, dist_comm]
    exact sq_ne_of_ne dist_nonneg (slen_pos D 0).le hdB
  obtain ⟨hpS, hqS⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnvS hSS hlineS
  exact ⟨hca, hqa, hcb, hpb, hpS, hqS, hnA, hnB, hHX⟩
theorem ga_head_sectors_right (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {d : V2} (hd : d ≠ 0) {X Y H : Plane}
    {L1 L2 : List (Fin N × Plane × Plane)} (W1 : WalkT D.toRegionDissection d X Y L1) (W2 : WalkR D.toRegionDissection d X Y L2)
    (hRun : RunEnd (slen D 0) L2 H) (hL1 : ∀ e ∈ L1.head?, dist e.2.1 e.2.2 ≠ slen D 0)
    {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) :
    ∃ a b s : AtV D.toRegionDissection H,
      0 < crs (F.p a) (F.q a) ∧ Par (F.p a) (neg2 d) ∧ 0 < crs (F.p b) (F.q b) ∧ Par (F.q b) d ∧
      Par (F.p s) d ∧ F.q s = (-(F.p s).1, -(F.p s).2) ∧
      nsq (F.p a) = slen D 0 ^ 2 ∧ nsq (F.q b) ≠ slen D 0 ^ 2 ∧ H ≠ X := by
  classical
  obtain ⟨iA, HA, iB, HB, iS, V, V', σ, hSA, hdA, hSB, hdB, hSS, hσ0, hσ1, hHV, hHX⟩ :=
    ga_head_right D idx hidx hnc hd W1 W2 hRun hL1
  have hmemA : H ∈ (D.tile iA).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSA
    rw [← hk]; exact subset_convexHull ℝ _ ⟨kk, rfl⟩
  have hmemB : H ∈ (D.tile iB).carrier := by
    obtain ⟨kk, f, g, hk, hf, -⟩ := id hSB
    rw [← hf]; exact subset_convexHull ℝ _ ⟨f, rfl⟩
  obtain ⟨hmemS, hnvS, hlineS⟩ := step_interior_pt hSS hσ0 hσ1
  rw [← hHV] at hmemS hnvS hlineS
  set a : AtV D.toRegionDissection H := ⟨iA, hmemA⟩
  set b : AtV D.toRegionDissection H := ⟨iB, hmemB⟩
  set s : AtV D.toRegionDissection H := ⟨iS, hmemS⟩
  refine ⟨a, b, s, ?_⟩
  obtain ⟨kkA, fA, gA, hkA, hfA, hfkA, hgkA, hgfA, hparA, hleftA⟩ := id hSA
  obtain ⟨kk', fl', hk', hp, hq⟩ := spec_corner_data (F.hspec a) ⟨kkA, hkA⟩
  have hpa : Par (F.p a) (neg2 d) := triStep_start hSA kk' fl' hk' hp hq (F.hok a)
  have hca : 0 < crs (F.p a) (F.q a) := crs_pos_of_corner (F.hok a) (F.hspec a) ⟨kk', hk'⟩
  have hkkA : kk' = kkA := (D.tile iA).indep.injective (hk'.trans hkA.symm)
  have hnA : nsq (F.p a) = slen D 0 ^ 2 := by
    have hp' : Par (toV2 ((D.tile iA).pts (armP kk' fl') - H)) (neg2 d) := hp ▸ hpa
    have := parm_eq (T := D.tile iA) fl' hk' (W := HA) (w := fA) hfA (by rw [hkkA]; exact hfkA) hp' hparA
    rw [hp, nsq_toV2_sub, this, hdA]
  obtain ⟨kkB, fB, gB, hkB, hfB, hfkB, hgkB, hgfB, hparB, hleftB⟩ := id hSB
  obtain ⟨kk2, fl2, hk2, hp2, hq2⟩ := spec_corner_data (F.hspec b) ⟨fB, hfB⟩
  have hqb0 : Par (F.q b) (-(neg2 d).1, -(neg2 d).2) := triStep_end hSB kk2 fl2 hk2 hp2 hq2 (F.hok b)
  have hqb : Par (F.q b) d := by rw [neg2_neg2] at hqb0; exact hqb0
  have hcb : 0 < crs (F.p b) (F.q b) := crs_pos_of_corner (F.hok b) (F.hspec b) ⟨kk2, hk2⟩
  have hkkB : kk2 = fB := (D.tile iB).indep.injective (hk2.trans hfB.symm)
  have hnB : nsq (F.q b) ≠ slen D 0 ^ 2 := by
    have hq' : Par (toV2 ((D.tile iB).pts (armQ kk2 fl2) - H)) d := hq2 ▸ hqb
    have hHB : Par (toV2 (HB - H)) d := par_arm_neg hparB
    have := qarm_eq (T := D.tile iB) fl2 hk2 (W := HB) (w := kkB) hkB (by rw [hkkB]; exact Ne.symm hfkB) hq' hHB
    rw [hq2, nsq_toV2_sub, this, dist_comm]
    exact sq_ne_of_ne dist_nonneg (slen_pos D 0).le hdB
  obtain ⟨hpS, hqS⟩ := straight_dir s (F.hok s) (F.hloc s) (F.hspec s) hnvS hSS hlineS
  exact ⟨hca, hpa, hcb, hqb, hpS, hqS, hnA, hnB, hHX⟩
def HeadCfg (D : CongruentRegionDissection N) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) (e : V2)
    (u v s : AtV D.toRegionDissection H) : Prop :=
  0 < crs (F.p u) (F.q u) ∧ Par (F.q u) (neg2 e) ∧ 0 < crs (F.p v) (F.q v) ∧ Par (F.p v) e ∧
  Par (F.p s) (neg2 e) ∧ F.q s = (-(F.p s).1, -(F.p s).2) ∧
  ((nsq (F.q u) = slen D 0 ^ 2 ∧ nsq (F.p v) ≠ slen D 0 ^ 2) ∨ (nsq (F.q u) ≠ slen D 0 ^ 2 ∧ nsq (F.p v) = slen D 0 ^ 2))
theorem HeadCfg.of_left (D : CongruentRegionDissection N) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) {d : V2}
    (a b s : AtV D.toRegionDissection H) (h1 : 0 < crs (F.p a) (F.q a)) (h2 : Par (F.q a) (neg2 d)) (h3 : 0 < crs (F.p b) (F.q b))
    (h4 : Par (F.p b) d) (h5 : Par (F.p s) (neg2 d)) (h6 : F.q s = (-(F.p s).1, -(F.p s).2))
    (h7 : nsq (F.q a) = slen D 0 ^ 2) (h8 : nsq (F.p b) ≠ slen D 0 ^ 2) : HeadCfg D F d a b s :=
  ⟨h1, h2, h3, h4, h5, h6, Or.inl ⟨h7, h8⟩⟩
theorem HeadCfg.of_right (D : CongruentRegionDissection N) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) {d : V2}
    (a b s : AtV D.toRegionDissection H) (h1 : 0 < crs (F.p a) (F.q a)) (h2 : Par (F.p a) (neg2 d)) (h3 : 0 < crs (F.p b) (F.q b))
    (h4 : Par (F.q b) d) (h5 : Par (F.p s) d) (h6 : F.q s = (-(F.p s).1, -(F.p s).2))
    (h7 : nsq (F.p a) = slen D 0 ^ 2) (h8 : nsq (F.q b) ≠ slen D 0 ^ 2) : HeadCfg D F (neg2 d) b a s := by
  refine ⟨h3, ?_, h1, h2, ?_, h6, Or.inr ⟨h8, h7⟩⟩
  · rw [neg2_neg2']; exact h4
  · rw [neg2_neg2']; exact h5
namespace ExtFan
variable {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ]
theorem head_four (F : ExtFan D V κ) {e : V2} {u v s : AtV D V}
    (hca : 0 < crs (F.p u) (F.q u)) (hqa : Par (F.q u) (neg2 e)) (hcb : 0 < crs (F.p v) (F.q v)) (hpb : Par (F.p v) e)
    (hps : Par (F.p s) (neg2 e)) (hqs : F.q s = (-(F.p s).1, -(F.p s).2))
    (hcard : Fintype.card (AtV D V) = 4) :
    IsEmpty κ ∧ V ∈ interior D.region ∧
    ∃ m : AtV D V, u ≠ v ∧ u ≠ s ∧ v ≠ s ∧ m ≠ u ∧ m ≠ v ∧ m ≠ s ∧ (∀ x, x = u ∨ x = v ∨ x = m ∨ x = s) ∧
      Par (F.p m) (F.q v) ∧ Par (F.p u) (F.q m) ∧ Par (F.p v) (F.q s) ∧ Par (F.p s) (F.q u) ∧
      0 < crs (F.p m) (F.q m) := by
  classical
  obtain ⟨hemp, hint, hus, hvs, huv, j0, hj0, hes, hev, heu⟩ := F.head_cyc u v s hca hqa hcb hpb hps hqs
  have hκ : Fintype.card κ = 0 := Fintype.card_eq_zero_iff.mpr hemp
  have hk4 : Fintype.card (AtV D V ⊕ κ) = 4 := by rw [Fintype.card_sum, hκ, hcard]
  rw [hk4] at hj0 heu
  have hper := F.hper
  have hinj := F.hinj
  have hsurj := F.hsurj
  rw [hk4] at hper hinj hsurj
  have hmod := cyc_mod F.e 4 hper
  have hP0 := F.hP j0
  have hP1 := F.hP (j0 + 1)
  have hP2 := F.hP (j0 + 2)
  have hP3 := F.hP (j0 + 3)
  obtain ⟨m, hm⟩ : ∃ m : AtV D V, F.e (j0 + 2) = Sum.inl m := by
    rcases hn : F.e (j0 + 2) with m | j
    · exact ⟨m, rfl⟩
    · exact (hemp.false j).elim
  have heu' : F.e (j0 + 3) = Sum.inl u := by simpa using heu
  have e4 : F.e (j0 + 3 + 1) = Sum.inl s := by
    rw [show j0 + 3 + 1 = j0 + 4 from rfl, hper j0, hes]
  rw [show j0 + 1 + 1 = j0 + 2 from rfl, hm, hev] at hP1
  rw [show j0 + 2 + 1 = j0 + 3 from rfl, heu', hm] at hP2
  rw [e4, heu'] at hP3
  rw [hev, hes] at hP0
  simp only [Sum.elim_inl] at hP0 hP1 hP2 hP3
  have hdist : ∀ i i', i ≤ 3 → i' ≤ 3 → i ≠ i' → F.e (j0 + i) ≠ F.e (j0 + i') := by
    intro i i' h1 h2 hne h
    rw [hmod (j0 + i), hmod (j0 + i')] at h
    have := hinj (Set.mem_Iio.mpr (Nat.mod_lt _ (by norm_num))) (Set.mem_Iio.mpr (Nat.mod_lt _ (by norm_num))) h
    omega
  have hmv : m ≠ v := by
    intro h; apply hdist 2 1 (by norm_num) (by norm_num) (by norm_num); rw [hm, hev, h]
  have hmu : m ≠ u := by
    intro h; apply hdist 2 3 (by norm_num) (by norm_num) (by norm_num); rw [hm, heu', h]
  have hms : m ≠ s := by
    intro h; apply hdist 2 0 (by norm_num) (by norm_num) (by norm_num); rw [hm, add_zero, hes, h]
  have hall : ∀ x : AtV D V, x = u ∨ x = v ∨ x = m ∨ x = s := by
    intro x
    obtain ⟨j, hj, hjx⟩ := hsurj (Sum.inl x)
    have hcases : j = (j0 + 0) % 4 ∨ j = (j0 + 1) % 4 ∨ j = (j0 + 2) % 4 ∨ j = (j0 + 3) % 4 := by omega
    rcases hcases with h | h | h | h
    · right; right; right
      have : F.e (j0 + 0) = Sum.inl x := by rw [hmod (j0 + 0), ← h]; exact hjx
      rw [add_zero, hes] at this; exact (Sum.inl.inj this).symm
    · right; left
      have : F.e (j0 + 1) = Sum.inl x := by rw [hmod (j0 + 1), ← h]; exact hjx
      rw [hev] at this; exact (Sum.inl.inj this).symm
    · right; right; left
      have : F.e (j0 + 2) = Sum.inl x := by rw [hmod (j0 + 2), ← h]; exact hjx
      rw [hm] at this; exact (Sum.inl.inj this).symm
    · left
      have : F.e (j0 + 3) = Sum.inl x := by rw [hmod (j0 + 3), ← h]; exact hjx
      rw [heu'] at this; exact (Sum.inl.inj this).symm
  have hmc : 0 < crs (F.p m) (F.q m) := by
    by_contra hnot
    push_neg at hnot
    have hcs : crs (F.p m) (F.q m) = 0 ∧ dt (F.p m) (F.q m) < 0 := by
      rcases F.hok m with h | h
      · linarith
      · exact h
    have hwm : wd (F.p m) (F.q m) = Real.pi := by
      unfold wd
      rw [Complex.arg_eq_pi_iff]
      exact ⟨hcs.2, hcs.1⟩
    have hws : wd (F.p s) (F.q s) = Real.pi := by
      rw [hqs]; exact wd_straight (F.hok s).ne_p
    have hsum := F.hsum
    have hvirt : ∑ j, wd (F.pe j) (F.qe j) = 0 := by
      haveI := hemp
      simp
    rw [hvirt, add_zero] at hsum
    have h3 : wd (F.p s) (F.q s) + wd (F.p m) (F.q m) + wd (F.p u) (F.q u) ≤ ∑ x, wd (F.p x) (F.q x) := by
      have hsub : ({s, m, u} : Finset (AtV D V)) ⊆ Finset.univ := Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun x => wd (F.p x) (F.q x)) hsub
        (fun x _ _ => (wd_pos (F.hok x)).le)
      rw [Finset.sum_insert (by simp [Ne.symm hms, Ne.symm hus]), Finset.sum_pair hmu] at this
      linarith
    have := wd_pos (F.hok u)
    linarith
  exact ⟨hemp, hint, m, huv, hus, hvs, hmu, hmv, hms, hall, hP1, hP2, hP0, hP3, hmc⟩
theorem crs_pos_of_par {e w w' : V2} (h : Par w w') (hw' : 0 < crs e w') : 0 < crs e w := by
  obtain ⟨c, hc, hcw⟩ := h.smul
  rw [hcw]
  unfold crs at hw' ⊢
  try simp only at hw' ⊢
  nlinarith [mul_pos hc hw']
theorem crs_neg_of_par {e d w : V2} (h : Par w (neg2 d)) (hd : 0 < crs e d) : crs e w < 0 := by
  obtain ⟨c, hc, hcw⟩ := h.smul
  rw [hcw]
  unfold crs at hd ⊢
  unfold neg2
  try simp only at hd ⊢
  nlinarith [mul_pos hc hd]
theorem head_inner_noBack (F : ExtFan D V κ) {e : V2} {u v s m : AtV D V}
    (hca : 0 < crs (F.p u) (F.q u)) (hqa : Par (F.q u) (neg2 e)) (hcb : 0 < crs (F.p v) (F.q v)) (hpb : Par (F.p v) e)
    (hps : Par (F.p s) (neg2 e)) (hqs : F.q s = (-(F.p s).1, -(F.p s).2))
    (hall : ∀ x, x = u ∨ x = v ∨ x = m ∨ x = s)
    (hmv : Par (F.p m) (F.q v)) (hum : Par (F.p u) (F.q m)) :
    NoBack D (F.q v) V ∧ NoBack D (F.p u) V := by
  have hvq : 0 < crs e (F.q v) := by
    obtain ⟨c, hc, hcp⟩ := hpb.smul
    have h := hcb
    rw [hcp] at h
    unfold crs at h ⊢; try simp only at h ⊢
    by_contra hX; push_neg at hX
    nlinarith [mul_nonneg hc.le (neg_nonneg.mpr hX)]
  have hup : 0 < crs e (F.p u) := by
    obtain ⟨c, hc, hcq⟩ := hqa.smul
    have h := hca
    rw [hcq] at h
    unfold crs at h ⊢; unfold neg2 at h; try simp only at h ⊢
    by_contra hX; push_neg at hX
    nlinarith [mul_nonneg hc.le (neg_nonneg.mpr hX)]
  have hmp : 0 < crs e (F.p m) := crs_pos_of_par hmv hvq
  have hmq : 0 < crs e (F.q m) := by
    obtain ⟨c, hc, hcp⟩ := hum.smul
    have h := hup
    rw [hcp] at h
    unfold crs at h ⊢; try simp only at h ⊢
    by_contra hX; push_neg at hX
    nlinarith [mul_nonneg hc.le (neg_nonneg.mpr hX)]
  have hsp : crs e (F.p s) = 0 := by
    obtain ⟨c, hc, hcp⟩ := hps.smul
    rw [hcp]; unfold crs neg2; ring
  have hsq : crs e (F.q s) = 0 := by
    rw [hqs]; unfold crs at hsp ⊢; try simp only at hsp ⊢; nlinarith [hsp]
  have hvp : crs e (F.p v) = 0 := by
    obtain ⟨c, hc, hcp⟩ := hpb.smul
    rw [hcp]; unfold crs; ring
  have huq : crs e (F.q u) = 0 := by
    obtain ⟨c, hc, hcq⟩ := hqa.smul
    rw [hcq]; unfold crs neg2; ring
  have hnn : ∀ x : AtV D V, 0 ≤ crs e (F.p x) ∧ 0 ≤ crs e (F.q x) := by
    intro x
    rcases hall x with rfl | rfl | rfl | rfl
    · exact ⟨hup.le, huq.ge⟩
    · exact ⟨hvp.ge, hvq.le⟩
    · exact ⟨hmp.le, hmq.le⟩
    · exact ⟨hsp.ge, hsq.ge⟩
  constructor
  · apply F.noBack_of_none
    intro x
    obtain ⟨h1, h2⟩ := hnn x
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := crs_neg_of_par h hvq; linarith
    · have := crs_neg_of_par h hvq; linarith
  · apply F.noBack_of_none
    intro x
    obtain ⟨h1, h2⟩ := hnn x
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := crs_neg_of_par h hup; linarith
    · have := crs_neg_of_par h hup; linarith
end ExtFan
end Erdos634.Draft.LaczFormal.RG
end

section
open Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
theorem TriStep.of_par {T : Tri} {d d' : V2} {A B : Plane} (hd : Par d' d) (h : TriStep T d A B) : TriStep T d' A B := by
  obtain ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar, hleft⟩ := h
  obtain ⟨c, hc, hcd⟩ := hd.smul
  refine ⟨kk, f, g, hk, hf, hfk, hgk, hgf, hpar.trans hd.symm, ?_⟩
  rw [hcd]
  unfold crs at hleft ⊢
  try simp only at hleft ⊢
  nlinarith [mul_pos hc hleft]
theorem par_eq_of_nsq {u v : V2} (h : Par u v) (hn : nsq u = nsq v) : u = v := by
  obtain ⟨c, hc, hcu⟩ := h.smul
  have hv := nsq_pos h.ne_right
  have hc1 : c = 1 := by
    have : nsq u = c ^ 2 * nsq v := by rw [hcu]; unfold nsq; simp only; ring
    rw [hn] at this
    have h2 : c ^ 2 = 1 := by nlinarith [this]
    nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 1)]
  rw [hcu, hc1]; ext <;> simp
theorem pt_eq_of_toV2 {P Q H : Plane} (h : toV2 (P - H) = toV2 (Q - H)) : P = Q := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [toV2, PiLp.sub_apply] at h1 h2
  apply pt_ext <;> linarith
theorem perm_third (σ : Equiv.Perm (Fin 3)) (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : σ a = 2) (hb : σ b = 1) : σ c = 0 := by
  have h1 : σ c ≠ σ a := fun h => hac (σ.injective h).symm
  have h2 : σ c ≠ σ b := fun h => hbc (σ.injective h).symm
  rw [ha] at h1; rw [hb] at h2
  revert h1 h2; generalize σ c = t; revert t; decide
theorem beq_zero_iff (n : ℕ) (x : Fin 3) (h : n = (x : ℕ)) : (n == 0) = true ↔ x = 0 := by
  subst h
  simp only [beq_iff_eq]
  constructor
  · intro h0; exact Fin.ext (by simpa using h0)
  · intro h0; rw [h0]; rfl
end Erdos634.Draft.LaczFormal.Graph
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
def GkEdge (D : RegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (Z X : Plane) : Prop :=
  ∃ (i j : Fin N) (k1 k2 k1' k2' : Fin 3), i ≠ j ∧ (D.tile i).pts k1 = Z ∧ (D.tile i).pts k2 = X ∧
    (D.tile j).pts k1' = Z ∧ (D.tile j).pts k2' = X ∧ idx i k1 = 2 ∧ idx i k2 = 1 ∧ idx j k1' = 2 ∧ idx j k2' = 1
theorem NoBack.of_par {D : RegionDissection N} {d d' : V2} {X : Plane} (hd : Par d' d) (h : NoBack D d X) : NoBack D d' X := by
  have hn : Par (neg2 d') (neg2 d) := par_neg hd
  refine ⟨fun i A B σ hS h0 h1 => h.1 i A B σ (TriStep.of_par hd.symm hS) h0 h1, fun i A B σ hS h0 h1 => ?_⟩
  exact h.2 i A B σ (TriStep.of_par hn.symm hS) h0 h1
theorem ExtFan.corner_of_crs {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) (x : AtV D V)
    (hc : 0 < crs (F.p x) (F.q x)) : ∃ k, (D.tile x.1).pts k = V := by
  rcases F.hspec x with ⟨k, hk, -⟩ | ⟨-, m', -, -, hq, -⟩
  · exact ⟨k, hk⟩
  · exfalso; rw [hq] at hc; unfold crs at hc; try simp only at hc; nlinarith
theorem nsq_q_iff (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {H : Plane} {i : Fin N} {kk : Fin 3} (fl : Bool)
    (hk : (D.tile i).pts kk = H) {q : V2} (hq : q = toV2 ((D.tile i).pts (armQ kk fl) - H)) :
    nsq q = slen D 0 ^ 2 ↔ idx i (armP kk fl) = 0 := by
  rw [hq, ← hk, (arm_lens D idx hidx i kk fl).2]
  exact slen_sq_eq_iff D hab hac _
theorem nsq_p_iff (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {H : Plane} {i : Fin N} {kk : Fin 3} (fl : Bool)
    (hk : (D.tile i).pts kk = H) {p : V2} (hp : p = toV2 ((D.tile i).pts (armP kk fl) - H)) :
    nsq p = slen D 0 ^ 2 ↔ idx i (armQ kk fl) = 0 := by
  rw [hp, ← hk, (arm_lens D idx hidx i kk fl).1]
  exact slen_sq_eq_iff D hab hac _
theorem gk_of_ray (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ)
    (x y : AtV D.toRegionDissection H) (hxy : Par (F.p y) (F.q x)) (hne : x ≠ y)
    {kx ky : Fin 3} {flx fly : Bool} (hkx : (D.tile x.1).pts kx = H) (hky : (D.tile y.1).pts ky = H)
    (hpx : F.p x = toV2 ((D.tile x.1).pts (armP kx flx) - H)) (hqx : F.q x = toV2 ((D.tile x.1).pts (armQ kx flx) - H))
    (hpy : F.p y = toV2 ((D.tile y.1).pts (armP ky fly) - H)) (hqy : F.q y = toV2 ((D.tile y.1).pts (armQ ky fly) - H))
    (t2x : idx x.1 kx = 2) (t1x : idx x.1 (armQ kx flx) = 1) (t2y : idx y.1 ky = 2) (t1y : idx y.1 (armP ky fly) = 1) :
    ∃ Z, GkEdge D.toRegionDissection idx H Z := by
  have hxA : idx x.1 (armP kx flx) = 0 :=
    perm_third (idx x.1) kx (armQ kx flx) (armP kx flx) (armQ_ne kx flx).symm (armP_ne kx flx).symm (armPQ_ne kx flx).symm t2x t1x
  have hyA : idx y.1 (armQ ky fly) = 0 :=
    perm_third (idx y.1) ky (armP ky fly) (armQ ky fly) (armP_ne ky fly).symm (armQ_ne ky fly).symm (armPQ_ne ky fly) t2y t1y
  have hnx : nsq (F.q x) = slen D 0 ^ 2 := (nsq_q_iff D idx hidx hab hac flx hkx hqx).mpr hxA
  have hny : nsq (F.p y) = slen D 0 ^ 2 := (nsq_p_iff D idx hidx hab hac fly hky hpy).mpr hyA
  have heq : F.p y = F.q x := par_eq_of_nsq hxy (by rw [hnx, hny])
  have hPP : (D.tile x.1).pts (armQ kx flx) = (D.tile y.1).pts (armP ky fly) := by
    apply pt_eq_of_toV2 (H := H)
    rw [← hqx, ← hpy, heq]
  refine ⟨(D.tile x.1).pts (armQ kx flx), x.1, y.1, kx, armQ kx flx, ky, armP ky fly, fun h => hne (Subtype.ext h), hkx, rfl, hky, hPP.symm,
    t2x, t1x, t2y, t1y⟩
theorem ga_of_codes (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ)
    (x y : AtV D.toRegionDissection H) (hcx : 0 < crs (F.p x) (F.q x)) (hcy : 0 < crs (F.p y) (F.q y))
    (hxy : Par (F.p y) (F.q x)) (hnb : NoBack D.toRegionDissection (F.q x) H)
    {kx ky : Fin 3} {flx fly : Bool} (hkx : (D.tile x.1).pts kx = H) (hky : (D.tile y.1).pts ky = H)
    (hqx : F.q x = toV2 ((D.tile x.1).pts (armQ kx flx) - H)) (hpy : F.p y = toV2 ((D.tile y.1).pts (armP ky fly) - H))
    (hg : ((RegFan.tU (codeOf (idx x.1) kx flx) == 0) != (RegFan.tW (codeOf (idx y.1) ky fly) == 0)) = true) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
  obtain ⟨-, tx2, -, -⟩ := codeOf_spec' (idx x.1) kx flx
  obtain ⟨-, -, ty3, -⟩ := codeOf_spec' (idx y.1) ky fly
  have q1 := nsq_q_iff D idx hidx hab hac flx hkx hqx
  have p1 := nsq_p_iff D idx hidx hab hac fly hky hpy
  refine ga_edge_of_ray D idx hidx hnc F x y hcx hcy hxy hnb ?_
  rcases hb1 : (RegFan.tU (codeOf (idx x.1) kx flx) == 0) <;> rcases hb2 : (RegFan.tW (codeOf (idx y.1) ky fly) == 0) <;>
    simp [hb1, hb2] at hg
  · 
    right
    have c1 : idx y.1 (armQ ky fly) = 0 := (beq_zero_iff _ _ ty3).mp hb2
    have c2 : ¬ idx x.1 (armP kx flx) = 0 := fun h => by
      have := (beq_zero_iff _ _ tx2).mpr h
      rw [hb1] at this; exact Bool.false_ne_true this
    exact ⟨fun h => c2 (q1.mp h), p1.mpr c1⟩
  · left
    have c1 : idx x.1 (armP kx flx) = 0 := (beq_zero_iff _ _ tx2).mp hb1
    have c2 : ¬ idx y.1 (armQ ky fly) = 0 := fun h => by
      have := (beq_zero_iff _ _ ty3).mpr h
      rw [hb2] at this; exact Bool.false_ne_true this
    exact ⟨q1.mpr c1, fun h => c2 (p1.mp h)⟩
theorem gk_of_codes (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ)
    (x y : AtV D.toRegionDissection H) (hxy : Par (F.p y) (F.q x)) (hne : x ≠ y)
    {kx ky : Fin 3} {flx fly : Bool} (hkx : (D.tile x.1).pts kx = H) (hky : (D.tile y.1).pts ky = H)
    (hpx : F.p x = toV2 ((D.tile x.1).pts (armP kx flx) - H)) (hqx : F.q x = toV2 ((D.tile x.1).pts (armQ kx flx) - H))
    (hpy : F.p y = toV2 ((D.tile y.1).pts (armP ky fly) - H)) (hqy : F.q y = toV2 ((D.tile y.1).pts (armQ ky fly) - H))
    (hg : (RegFan.tT (codeOf (idx x.1) kx flx) == 2 && RegFan.tT (codeOf (idx y.1) ky fly) == 2 &&
           RegFan.tW (codeOf (idx x.1) kx flx) == 1 && RegFan.tU (codeOf (idx y.1) ky fly) == 1) = true) :
    ∃ Z, GkEdge D.toRegionDissection idx H Z := by
  obtain ⟨tx1, -, tx3, -⟩ := codeOf_spec' (idx x.1) kx flx
  obtain ⟨ty1, ty2, -, -⟩ := codeOf_spec' (idx y.1) ky fly
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := hg
  have e1 : idx x.1 kx = 2 := by apply Fin.ext; rw [← tx1] at *; simpa using g1
  have e2 : idx y.1 ky = 2 := by apply Fin.ext; simpa [ty1] using g2
  have e3 : idx x.1 (armQ kx flx) = 1 := by apply Fin.ext; simpa [tx3] using g3
  have e4 : idx y.1 (armP ky fly) = 1 := by apply Fin.ext; simpa [ty2] using g4
  exact gk_of_ray D idx hidx hab hac F x y hxy hne hkx hky hpx hqx hpy hqy e1 e3 e2 e4
theorem head_out_edge (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) {e : V2} {u v s : AtV D.toRegionDissection H}
    (hc : HeadCfg D F e u v s) (hcard : Fintype.card (AtV D.toRegionDissection H) = 4)
    (hN : (∀ t₁ t₂ : AtV D.toRegionDissection H, t₁ ≠ s → t₂ ≠ s → t₁ ≠ t₂ → ∀ k₁ k₂, (D.tile t₁.1).pts k₁ = H →
            (D.tile t₂.1).pts k₂ = H → idx t₁.1 k₁ ≠ idx t₂.1 k₂) ∨
          (∀ t : AtV D.toRegionDissection H, t ≠ s → ∀ k, (D.tile t.1).pts k = H → idx t.1 k = 2)) :
    (∃ H', GaEdge D.toRegionDissection (slen D 0) H H') ∨ ∃ Z, GkEdge D.toRegionDissection idx H Z := by
  classical
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc
  obtain ⟨hemp, hint, m, huv, hus, hvs, hmu, hmv, hms, hall, hmv', hum', hvs', hsu', hcm⟩ :=
    F.head_four hc1 hc2 hc3 hc4 hc5 hc6 hcard
  have hnb := F.head_inner_noBack hc1 hc2 hc3 hc4 hc5 hc6 hall hmv' hum'
  have hnb2 : NoBack D.toRegionDissection (F.q m) H := NoBack.of_par hum'.symm hnb.2
  obtain ⟨kv0, hkv0⟩ := F.corner_of_crs v hc3
  obtain ⟨km0, hkm0⟩ := F.corner_of_crs m hcm
  obtain ⟨ku0, hku0⟩ := F.corner_of_crs u hc1
  obtain ⟨kv, flv, hkv, hpv, hqv⟩ := spec_corner_data (F.hspec v) ⟨kv0, hkv0⟩
  obtain ⟨km, flm, hkm, hpm, hqm⟩ := spec_corner_data (F.hspec m) ⟨km0, hkm0⟩
  obtain ⟨ku, flu, hku, hpu, hqu⟩ := spec_corner_data (F.hspec u) ⟨ku0, hku0⟩
  set cv := codeOf (idx v.1) kv flv with hcv
  set cm := codeOf (idx m.1) km flm with hcm'
  set cu := codeOf (idx u.1) ku flu with hcu
  obtain ⟨tv1, tv2, tv3, lv⟩ := codeOf_spec' (idx v.1) kv flv
  obtain ⟨tm1, tm2, tm3, lm⟩ := codeOf_spec' (idx m.1) km flm
  obtain ⟨tu1, tu2, tu3, lu⟩ := codeOf_spec' (idx u.1) ku flu
  rw [← hcv] at tv1 tv2 tv3 lv
  rw [← hcm'] at tm1 tm2 tm3 lm
  rw [← hcu] at tu1 tu2 tu3 lu
  have qu := nsq_q_iff D idx hidx hab hac flu hku hqu
  have pv := nsq_p_iff D idx hidx hab hac flv hkv hpv
  set l : List ℕ := [cv, cm, cu] with hl
  have hlen : l.length = 3 := rfl
  have hlt : ∀ x ∈ l, x < 6 := by
    intro x hx
    simp only [hl, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hinc : RegFan.incoming l = true := by
    show ((RegFan.tW cv == 0 && RegFan.tU cu != 0) || (RegFan.tU cu == 0 && RegFan.tW cv != 0)) = true
    rcases hc7 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have a1 : idx u.1 (armP ku flu) = 0 := (qu).mp h1
      have a2 : ¬ idx v.1 (armQ kv flv) = 0 := fun h => h2 ((pv).mpr h)
      have b1 : (RegFan.tU cu == 0) = true := (beq_zero_iff _ _ tu2).mpr a1
      have b2 : (RegFan.tW cv == 0) = false := by
        by_contra hh
        have hh' : (RegFan.tW cv == 0) = true := by simpa using hh
        exact a2 ((beq_zero_iff _ _ tv3).mp hh')
      simp only [bne, b1, b2]; rfl
    · have a1 : idx v.1 (armQ kv flv) = 0 := (pv).mp h2
      have a2 : ¬ idx u.1 (armP ku flu) = 0 := fun h => h1 ((qu).mpr h)
      have b1 : (RegFan.tW cv == 0) = true := (beq_zero_iff _ _ tv3).mpr a1
      have b2 : (RegFan.tU cu == 0) = false := by
        by_contra hh
        have hh' : (RegFan.tU cu == 0) = true := by simpa using hh
        exact a2 ((beq_zero_iff _ _ tu2).mp hh')
      simp only [bne, b1, b2]; rfl
  have hkvH := hkv
  have ray1ga : RegFan.gaEdge l 1 = true → ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
    intro hg
    have hg' : ((RegFan.tU cv == 0) != (RegFan.tW cm == 0)) = true := by
      simpa [RegFan.gaEdge, RegFan.Lc, RegFan.Rc, hl] using hg
    exact ga_of_codes D idx hidx hnc hab hac F v m hc3 hcm hmv' hnb.1 hkv hkm hqv hpm hg'
  have ray2ga : RegFan.gaEdge l 2 = true → ∃ H', GaEdge D.toRegionDissection (slen D 0) H H' := by
    intro hg
    have hg' : ((RegFan.tU cm == 0) != (RegFan.tW cu == 0)) = true := by
      simpa [RegFan.gaEdge, RegFan.Lc, RegFan.Rc, hl] using hg
    exact ga_of_codes D idx hidx hnc hab hac F m u hcm hc1 hum' hnb2 hkm hku hqm hpu hg'
  have ray1gk : RegFan.gkEdge l 1 = true → ∃ Z, GkEdge D.toRegionDissection idx H Z := by
    intro hg
    have hg' : (RegFan.tT cv == 2 && RegFan.tT cm == 2 && RegFan.tW cv == 1 && RegFan.tU cm == 1) = true := by
      simpa [RegFan.gkEdge, RegFan.Lc, RegFan.Rc, hl] using hg
    exact gk_of_codes D idx hidx hab hac F v m hmv' (Ne.symm hmv) hkv hkm hpv hqv hpm hqm hg'
  have ray2gk : RegFan.gkEdge l 2 = true → ∃ Z, GkEdge D.toRegionDissection idx H Z := by
    intro hg
    have hg' : (RegFan.tT cm == 2 && RegFan.tT cu == 2 && RegFan.tW cm == 1 && RegFan.tU cu == 1) = true := by
      simpa [RegFan.gkEdge, RegFan.Lc, RegFan.Rc, hl] using hg
    exact gk_of_codes D idx hidx hab hac F m u hum' hmu hkm hku hpm hqm hpu hqu hg'
  rcases hN with hN1 | hN2
  · 
    have d12 : idx v.1 kv ≠ idx m.1 km := hN1 v m hvs hms (Ne.symm hmv) kv km hkv hkm
    have d13 : idx v.1 kv ≠ idx u.1 ku := hN1 v u hvs hus (Ne.symm huv) kv ku hkv hku
    have d23 : idx m.1 km ≠ idx u.1 ku := hN1 m u hms hus hmu km ku hkm hku
    have hhyp : RegFan.piNormalHyp l = true := by
      unfold RegFan.piNormalHyp
      have c0 := perm3_cnt (idx v.1 kv) (idx m.1 km) (idx u.1 ku) d12 d13 d23 0
      have c1 := perm3_cnt (idx v.1 kv) (idx m.1 km) (idx u.1 ku) d12 d13 d23 1
      have c2 := perm3_cnt (idx v.1 kv) (idx m.1 km) (idx u.1 ku) d12 d13 d23 2
      have e0 : RegFan.cnt l 0 = 1 := by rw [hl, cnt3_eq, tv1, tm1, tu1]; simpa using c0
      have e1 : RegFan.cnt l 1 = 1 := by rw [hl, cnt3_eq, tv1, tm1, tu1]; simpa using c1
      have e2 : RegFan.cnt l 2 = 1 := by rw [hl, cnt3_eq, tv1, tm1, tu1]; simpa using c2
      simp [e0, e1, e2, hinc]
    have hconcl := RegFan.pi_fan_normal l hlen hlt hhyp
    unfold RegFan.piNormalConcl at hconcl
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hconcl
    obtain ⟨i, hi, hi1, hgi⟩ := hconcl
    left
    interval_cases i
    · exact ray1ga hgi
    · exact ray2ga hgi
  · 
    have g1 : idx v.1 kv = 2 := hN2 v hvs kv hkv
    have g2 : idx m.1 km = 2 := hN2 m hms km hkm
    have g3 : idx u.1 ku = 2 := hN2 u hus ku hku
    have hhyp : RegFan.pi003Hyp l = true := by
      unfold RegFan.pi003Hyp
      have e0 : RegFan.cnt l 0 = 0 := by rw [hl, cnt3_eq, tv1, tm1, tu1, g1, g2, g3]; simp
      have e1 : RegFan.cnt l 1 = 0 := by rw [hl, cnt3_eq, tv1, tm1, tu1, g1, g2, g3]; simp
      have e2 : RegFan.cnt l 2 = 3 := by rw [hl, cnt3_eq, tv1, tm1, tu1, g1, g2, g3]; simp
      simp [e0, e1, e2, hinc]
    have hconcl := RegFan.pi_fan_3gamma l hlen hlt hhyp
    unfold RegFan.pi003Concl at hconcl
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hconcl
    obtain ⟨i, hi, hi1, hgi⟩ := hconcl
    interval_cases i
    · rcases hgi with hga | hgk
      · exact Or.inl (ray1ga hga)
      · exact Or.inr (ray1gk hgk)
    · rcases hgi with hga | hgk
      · exact Or.inl (ray2ga hga)
      · exact Or.inr (ray2gk hgk)
end Erdos634.Draft.LaczFormal.RG
end

section
open Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
theorem pt_on_step {X A B P : Plane} {d : V2} {t0 t1 s : ℝ} (h0 : t0 < s) (h1 : s ≤ t1)
    (hA : toV2 (A - X) = (t0 * d.1, t0 * d.2)) (hB : toV2 (B - X) = (t1 * d.1, t1 * d.2))
    (hP : toV2 (P - X) = (s * d.1, s * d.2)) :
    P = A + ((s - t0) / (t1 - t0)) • (B - A) := by
  have hne : t1 - t0 ≠ 0 := by intro h; linarith
  apply pt_eq_of_toV2 (H := X)
  have a1 := congrArg Prod.fst hA
  have a2 := congrArg Prod.snd hA
  have b1 := congrArg Prod.fst hB
  have b2 := congrArg Prod.snd hB
  simp only [toV2, PiLp.sub_apply] at a1 a2 b1 b2 hP ⊢
  rw [hP]
  ext <;> simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] <;> field_simp <;> nlinarith [a1, a2, b1, b2]
theorem xuniq_core {d d' : V2} (hpar : Par d' d) {X X' H : Plane} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (h1 : toV2 (H - X) = (T * d.1, T * d.2)) (h2 : toV2 (H - X') = (T' * d'.1, T' * d'.2)) :
    X = X' ∨ (0 < T - T' * (Classical.choose hpar.smul) ∧ toV2 (X' - X) = ((T - T' * (Classical.choose hpar.smul)) * d.1, (T - T' * (Classical.choose hpar.smul)) * d.2)) ∨
      (0 < T' - T / (Classical.choose hpar.smul) ∧ toV2 (X - X') = ((T' - T / (Classical.choose hpar.smul)) * d'.1, (T' - T / (Classical.choose hpar.smul)) * d'.2)) := by
  obtain ⟨hc, hcd⟩ := Classical.choose_spec hpar.smul
  set c := Classical.choose hpar.smul
  have hd1 : d'.1 = c * d.1 := by rw [hcd]
  have hd2 : d'.2 = c * d.2 := by rw [hcd]
  have e1 := congrArg Prod.fst h1
  have e2 := congrArg Prod.snd h1
  have f1 := congrArg Prod.fst h2
  have f2 := congrArg Prod.snd h2
  simp only [toV2, PiLp.sub_apply] at e1 e2 f1 f2
  rcases lt_trichotomy (T - T' * c) 0 with hlt | heq | hgt
  · right; right
    have hpos : 0 < T' - T / c := by
      have : T / c < T' := by rw [div_lt_iff₀ hc]; linarith
      linarith
    refine ⟨hpos, ?_⟩
    simp only [toV2, PiLp.sub_apply]
    have hcne : c ≠ 0 := hc.ne'
    ext
    · show X 0 - X' 0 = (T' - T / c) * d'.1
      rw [hd1]; field_simp; nlinarith [e1, f1, hd1]
    · show X 1 - X' 1 = (T' - T / c) * d'.2
      rw [hd2]; field_simp; nlinarith [e2, f2, hd2]
  · left
    have : T = T' * c := by linarith
    apply pt_eq_of_toV2 (H := H)
    simp only [toV2, PiLp.sub_apply]
    rw [hd1] at f1; rw [hd2] at f2
    rw [this] at e1 e2
    ext
    · show X 0 - H 0 = X' 0 - H 0
      nlinarith [e1, f1]
    · show X 1 - H 1 = X' 1 - H 1
      nlinarith [e2, f2]
  · right; left
    refine ⟨hgt, ?_⟩
    simp only [toV2, PiLp.sub_apply]
    ext
    · show X' 0 - X 0 = (T - T' * c) * d.1
      rw [hd1] at f1; nlinarith [e1, f1]
    · show X' 1 - X 1 = (T - T' * c) * d.2
      rw [hd2] at f2; nlinarith [e2, f2]
theorem par_neg2 {u v : V2} (h : Par (neg2 u) (neg2 v)) : Par u v := by
  have := par_neg h
  rwa [neg2_neg2, neg2_neg2] at this
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
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
theorem walkT_cover' {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) {T : ℝ} (hT : toV2 (Y - X) = (T * d.1, T * d.2)) (hd : d ≠ 0) :
    ∀ s : ℝ, 0 < s → s ≤ T → ∃ e ∈ L, ∃ t0 t1 : ℝ, toV2 (e.2.1 - X) = (t0 * d.1, t0 * d.2) ∧
      toV2 (e.2.2 - X) = (t1 * d.1, t1 * d.2) ∧ t0 < s ∧ s ≤ t1 := by
  induction W generalizing T with
  | nil X =>
    intro s hs hsT
    exfalso
    have h1 : T * d.1 = 0 := by have := congrArg Prod.fst hT; simpa [toV2] using this.symm
    have h2 : T * d.2 = 0 := by have := congrArg Prod.snd hT; simpa [toV2] using this.symm
    have hT0 : T = 0 := by
      by_contra hne
      exact hd (Prod.ext ((mul_eq_zero.mp h1).resolve_left hne) ((mul_eq_zero.mp h2).resolve_left hne))
    linarith
  | @cons i X X' Y L hS W ih =>
    intro s hs hsT
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    by_cases hsc : s ≤ c
    · exact ⟨(i, X, X'), List.mem_cons_self .., 0, c, by unfold toV2; ext <;> simp, hcw, hs, hsc⟩
    · push_neg at hsc
      have hT' : toV2 (Y - X') = ((T - c) * d.1, (T - c) * d.2) := by
        have : toV2 (Y - X') = ((toV2 (Y - X)).1 - (toV2 (X' - X)).1, (toV2 (Y - X)).2 - (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, hT, hcw]; ext <;> simp <;> ring
      obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := ih hT' (s - c) (by linarith) (by linarith)
      refine ⟨e, List.mem_cons_of_mem _ he, t0 + c, t1 + c, ?_, ?_, by linarith, by linarith⟩
      · have : toV2 (e.2.1 - X) = ((toV2 (e.2.1 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.1 - X')).2 + (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, h0, hcw]; ext <;> simp <;> ring
      · have : toV2 (e.2.2 - X) = ((toV2 (e.2.2 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.2 - X')).2 + (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, h1, hcw]; ext <;> simp <;> ring
theorem walkR_cover' {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X Y L) {T : ℝ} (hT : toV2 (Y - X) = (T * d.1, T * d.2)) (hd : d ≠ 0) :
    ∀ s : ℝ, 0 < s → s ≤ T → ∃ e ∈ L, ∃ t0 t1 : ℝ, toV2 (e.2.1 - X) = (t0 * d.1, t0 * d.2) ∧
      toV2 (e.2.2 - X) = (t1 * d.1, t1 * d.2) ∧ t0 < s ∧ s ≤ t1 := by
  induction W generalizing T with
  | nil X =>
    intro s hs hsT
    exfalso
    have h1 : T * d.1 = 0 := by have := congrArg Prod.fst hT; simpa [toV2] using this.symm
    have h2 : T * d.2 = 0 := by have := congrArg Prod.snd hT; simpa [toV2] using this.symm
    have hT0 : T = 0 := by
      by_contra hne
      exact hd (Prod.ext ((mul_eq_zero.mp h1).resolve_left hne) ((mul_eq_zero.mp h2).resolve_left hne))
    linarith
  | @cons i X X' Y L hS W ih =>
    intro s hs hsT
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c, hc, hcw⟩ := hpar.smul
    have h1 : toV2 (X' - X) = (c * d.1, c * d.2) := by
      have : toV2 (X' - X) = (-(toV2 (X - X')).1, -(toV2 (X - X')).2) := by
        unfold toV2; ext <;> simp
      rw [this, hcw]; unfold neg2; ext <;> simp
    by_cases hsc : s ≤ c
    · exact ⟨(i, X, X'), List.mem_cons_self .., 0, c, by unfold toV2; ext <;> simp, h1, hs, hsc⟩
    · push_neg at hsc
      have hT' : toV2 (Y - X') = ((T - c) * d.1, (T - c) * d.2) := by
        have : toV2 (Y - X') = ((toV2 (Y - X)).1 - (toV2 (X' - X)).1, (toV2 (Y - X)).2 - (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, hT, h1]; ext <;> simp <;> ring
      obtain ⟨e, he, t0, t1, h0, h1', h2, h3⟩ := ih hT' (s - c) (by linarith) (by linarith)
      refine ⟨e, List.mem_cons_of_mem _ he, t0 + c, t1 + c, ?_, ?_, by linarith, by linarith⟩
      · have : toV2 (e.2.1 - X) = ((toV2 (e.2.1 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.1 - X')).2 + (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, h0, h1]; ext <;> simp <;> ring
      · have : toV2 (e.2.2 - X) = ((toV2 (e.2.2 - X')).1 + (toV2 (X' - X)).1, (toV2 (e.2.2 - X')).2 + (toV2 (X' - X)).2) := by
          unfold toV2; ext <;> simp
        rw [this, h1', h1]; ext <;> simp <;> ring
theorem noBack_walkT {D : RegionDissection N} {d : V2} (hd : d ≠ 0) {X H X' : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X H L) {T s : ℝ} (hT : toV2 (H - X) = (T * d.1, T * d.2)) (hs0 : 0 < s) (hsT : s ≤ T)
    (hX' : toV2 (X' - X) = (s * d.1, s * d.2)) (hnb : NoBack D d X') : False := by
  obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkT_cover' W hT hd s hs0 hsT
  have hS := walkT_mem_step W e he
  have hne : t0 < t1 := lt_of_lt_of_le h2 h3
  have hσ0 : 0 < (s - t0) / (t1 - t0) := div_pos (by linarith) (by linarith)
  have hσ1 : (s - t0) / (t1 - t0) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  exact hnb.1 e.1 e.2.1 e.2.2 _ hS hσ0 hσ1 (pt_on_step h2 h3 h0 h1 hX')
theorem noBack_walkR {D : RegionDissection N} {d : V2} (hd : d ≠ 0) {X H X' : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkR D d X H L) {T s : ℝ} (hT : toV2 (H - X) = (T * d.1, T * d.2)) (hs0 : 0 < s) (hsT : s ≤ T)
    (hX' : toV2 (X' - X) = (s * d.1, s * d.2)) (hnb : NoBack D d X') : False := by
  obtain ⟨e, he, t0, t1, h0, h1, h2, h3⟩ := walkR_cover' W hT hd s hs0 hsT
  have hS := walkR_mem_step W e he
  have hne : t0 < t1 := lt_of_lt_of_le h2 h3
  have hσ0 : 0 < (s - t0) / (t1 - t0) := div_pos (by linarith) (by linarith)
  have hσ1 : (s - t0) / (t1 - t0) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  exact hnb.2 e.1 e.2.2 e.2.1 _ hS hσ0 hσ1 (pt_on_step h2 h3 h0 h1 hX')
theorem xuniq_T {D : RegionDissection N} {d d' : V2} (hd : d ≠ 0) (hpar : Par d' d) {X X' H : Plane}
    {P P' : List (Fin N × Plane × Plane)} (W : WalkT D d X H P) (hP : P ≠ []) (W' : WalkT D d' X' H P') (hP' : P' ≠ [])
    (hnb : NoBack D d X) (hnb' : NoBack D d' X') : X = X' := by
  obtain ⟨T, -, hT, hTp⟩ := walkT_progress W
  obtain ⟨T', -, hT', hTp'⟩ := walkT_progress W'
  rcases xuniq_core hpar (hTp hP) (hTp' hP') hT hT' with h | ⟨hpos, hX'⟩ | ⟨hpos, hX⟩
  · exact h
  · exact (noBack_walkT hd W hT hpos (by
      have := Classical.choose_spec hpar.smul
      have : 0 < T' * Classical.choose hpar.smul := mul_pos (hTp' hP') this.1
      linarith) hX' (NoBack.of_par hpar.symm hnb')).elim
  · exact (noBack_walkT hpar.ne_left W' hT' hpos (by
      have := Classical.choose_spec hpar.smul
      have : 0 < T / Classical.choose hpar.smul := div_pos (hTp hP) this.1
      linarith) hX (NoBack.of_par hpar hnb)).elim
theorem xuniq_R {D : RegionDissection N} {d d' : V2} (hd : d ≠ 0) (hpar : Par d' d) {X X' H : Plane}
    {P P' : List (Fin N × Plane × Plane)} (W : WalkR D d X H P) (hP : P ≠ []) (W' : WalkR D d' X' H P') (hP' : P' ≠ [])
    (hnb : NoBack D d X) (hnb' : NoBack D d' X') : X = X' := by
  obtain ⟨T, -, hT, hTp⟩ := walkR_progress W
  obtain ⟨T', -, hT', hTp'⟩ := walkR_progress W'
  rcases xuniq_core hpar (hTp hP) (hTp' hP') hT hT' with h | ⟨hpos, hX'⟩ | ⟨hpos, hX⟩
  · exact h
  · exact (noBack_walkR hd W hT hpos (by
      have := Classical.choose_spec hpar.smul
      have : 0 < T' * Classical.choose hpar.smul := mul_pos (hTp' hP') this.1
      linarith) hX' (NoBack.of_par hpar.symm hnb')).elim
  · exact (noBack_walkR hpar.ne_left W' hT' hpos (by
      have := Classical.choose_spec hpar.smul
      have : 0 < T / Classical.choose hpar.smul := div_pos (hTp hP) this.1
      linarith) hX (NoBack.of_par hpar hnb)).elim
theorem straight_unique {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) {s1 s2 a : AtV D V}
    (h1 : F.q s1 = (-(F.p s1).1, -(F.p s1).2)) (h2 : F.q s2 = (-(F.p s2).1, -(F.p s2).2))
    (ha : 0 < crs (F.p a) (F.q a)) : s1 = s2 := by
  classical
  by_contra hne
  have has1 : a ≠ s1 := by
    rintro rfl; rw [h1] at ha; unfold crs at ha; simp at ha; linarith
  have has2 : a ≠ s2 := by
    rintro rfl; rw [h2] at ha; unfold crs at ha; simp at ha; linarith
  have w1 : wd (F.p s1) (F.q s1) = Real.pi := by rw [h1]; exact wd_straight (F.hok s1).ne_p
  have w2 : wd (F.p s2) (F.q s2) = Real.pi := by rw [h2]; exact wd_straight (F.hok s2).ne_p
  have hsum := F.hsum
  have hvirt : 0 ≤ ∑ j, wd (F.pe j) (F.qe j) := Finset.sum_nonneg (fun j _ => (wd_pos (F.hokE j)).le)
  have h3 : wd (F.p s1) (F.q s1) + wd (F.p s2) (F.q s2) + wd (F.p a) (F.q a) ≤ ∑ x, wd (F.p x) (F.q x) := by
    have hsub : ({s1, s2, a} : Finset (AtV D V)) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun x => wd (F.p x) (F.q x)) hsub
      (fun x _ _ => (wd_pos (F.hok x)).le)
    rw [Finset.sum_insert (by simp [hne, Ne.symm has1]), Finset.sum_pair (Ne.symm has2)] at this
    linarith
  have := wd_pos (F.hok a)
  linarith
theorem corner_start_unique {D : RegionDissection N} {V : Plane} {κ : Type} [Fintype κ] (F : ExtFan D V κ) {x y : AtV D V}
    (hx : 0 < crs (F.p x) (F.q x)) (hy : 0 < crs (F.p y) (F.q y)) (hpar : Par (F.p x) (F.p y)) : x = y := by
  classical
  by_contra hne
  obtain ⟨δx, hδx, Hx⟩ := plus_ray_int (F.hok x)
  obtain ⟨δy, hδy, Hy⟩ := plus_ray_int (F.hok y)
  obtain ⟨c, hc, hcd⟩ := hpar.smul
  set ε := min δx δy / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hεx : ε < δx := by have := min_le_left δx δy; linarith
  have hεy : ε < δy := by have := min_le_right δx δy; linarith
  have hzx := Hx ε hε0 hεx
  have hzy := Hy ε hε0 hεy
  have hzeq : zplus (F.p x) ε = (c * (zplus (F.p y) ε).1, c * (zplus (F.p y) ε).2) := by
    unfold zplus; rw [hcd]; ext <;> simp <;> ring
  rw [hzeq] at hzx
  have hzy' := (inInt_smul hc hzy)
  exact F.disj_all (o1 := Sum.inl x) (o2 := Sum.inl y) (fun h => hne (Sum.inl.inj h)) _ ⟨by simpa using hzx, by simpa using hzy'⟩
theorem ga_edge_vertex (D : RegionDissection N) (a : ℝ) {X H : Plane} (h : GaEdge D a X H) : ∃ i k, (D.tile i).pts k = H := by
  obtain ⟨d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, -, -, hcase⟩ := h
  rcases hcase with ⟨⟨L', e, L'', hdec, -, -, -, hH⟩, -⟩ | ⟨⟨L', e, L'', hdec, -, -, -, hH⟩, -⟩
  · have hmem : e ∈ L1 := by rw [hdec]; exact List.mem_append_right _ (List.mem_cons_self ..)
    obtain ⟨kk, f, g, hk, -⟩ := walkT_mem_step W1 e hmem
    exact ⟨e.1, kk, hH ▸ hk⟩
  · have hmem : e ∈ L2 := by rw [hdec]; exact List.mem_append_right _ (List.mem_cons_self ..)
    obtain ⟨kk, f, g, hk, hf, -⟩ := walkR_mem_step W2 e hmem
    exact ⟨e.1, f, hH ▸ hf⟩
def LeftF (D : CongruentRegionDissection N) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) (d : V2)
    (a b s : AtV D.toRegionDissection H) : Prop :=
  0 < crs (F.p a) (F.q a) ∧ Par (F.q a) (neg2 d) ∧ 0 < crs (F.p b) (F.q b) ∧ Par (F.p b) d ∧
    Par (F.p s) (neg2 d) ∧ F.q s = (-(F.p s).1, -(F.p s).2) ∧ nsq (F.q a) = slen D 0 ^ 2 ∧ nsq (F.p b) ≠ slen D 0 ^ 2
def RightF (D : CongruentRegionDissection N) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) (d : V2)
    (a b s : AtV D.toRegionDissection H) : Prop :=
  0 < crs (F.p a) (F.q a) ∧ Par (F.p a) (neg2 d) ∧ 0 < crs (F.p b) (F.q b) ∧ Par (F.q b) d ∧
    Par (F.p s) d ∧ F.q s = (-(F.p s).1, -(F.p s).2) ∧ nsq (F.p a) = slen D 0 ^ 2 ∧ nsq (F.q b) ≠ slen D 0 ^ 2
theorem ga_edge_data (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {X H : Plane} (h : GaEdge D.toRegionDissection (slen D 0) X H)
    {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ) :
    ∃ d : V2, d ≠ 0 ∧ NoBack D.toRegionDissection d X ∧
      ((∃ P, WalkT D.toRegionDissection d X H P ∧ P ≠ [] ∧ ∃ a b s, LeftF D F d a b s) ∨
       (∃ P, WalkR D.toRegionDissection d X H P ∧ P ≠ [] ∧ ∃ a b s, RightF D F d a b s)) := by
  obtain ⟨d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, -, -, hcase⟩ := h
  refine ⟨d, hd, hnb, ?_⟩
  rcases hcase with ⟨hRun, hR2⟩ | ⟨hRun, hL1'⟩
  · left
    have hRun0 := hRun
    obtain ⟨L', e, L'', hdec, hL'ne, -, -, hH⟩ := hRun
    obtain ⟨hpre, -⟩ := walkT_split W1 hdec
    refine ⟨L', hH ▸ hpre, hL'ne, ?_⟩
    obtain ⟨a, b, s, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ :=
      ga_head_sectors_left D idx hidx hnc hd W1 W2 hRun0 hR2 F
    exact ⟨a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · right
    have hRun0 := hRun
    obtain ⟨L', e, L'', hdec, hL'ne, -, -, hH⟩ := hRun
    obtain ⟨hpre, -⟩ := walkR_split W2 hdec
    refine ⟨L', hH ▸ hpre, hL'ne, ?_⟩
    obtain ⟨a, b, s, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ :=
      ga_head_sectors_right D idx hidx hnc hd W1 W2 hRun0 hL1' F
    exact ⟨a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
theorem left_right_contra (D : CongruentRegionDissection N) {H : Plane} {κ : Type} [Fintype κ] (F : ExtFan D.toRegionDissection H κ)
    {d d' : V2} {a b s a' b' s' : AtV D.toRegionDissection H} (hl : LeftF D F d a b s) (hr : RightF D F d' a' b' s') : False := by
  obtain ⟨hca, hqa, hcb, hpb, hps, hqs, hna, hnb⟩ := hl
  obtain ⟨hca', hpa', hcb', hqb', hps', hqs', hna', hnb'⟩ := hr
  have hss : s = s' := straight_unique F hqs hqs' hca
  subst hss
  have h1 : Par d' (neg2 d) := hps'.symm.trans hps
  have h2 : Par (neg2 d') d := by
    have := par_neg h1
    rwa [neg2_neg2] at this
  have h3 : Par (F.p a') (F.p b) := hpa'.trans (h2.trans hpb.symm)
  have hab : a' = b := corner_start_unique F hca' hcb h3
  subst hab
  exact hnb hna'
theorem ga_indegree (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) {X X' H : Plane}
    (h1 : GaEdge D.toRegionDissection (slen D 0) X H) (h2 : GaEdge D.toRegionDissection (slen D 0) X' H) : X = X' := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H (ga_edge_vertex _ _ h1)
  obtain ⟨d1, hd1, nb1, c1⟩ := ga_edge_data D idx hidx hnc h1 F
  obtain ⟨d2, hd2, nb2, c2⟩ := ga_edge_data D idx hidx hnc h2 F
  rcases c1 with ⟨P, W, hP, a, b, s, hf⟩ | ⟨P, W, hP, a, b, s, hf⟩ <;>
  rcases c2 with ⟨P', W', hP', a', b', s', hf'⟩ | ⟨P', W', hP', a', b', s', hf'⟩
  · 
    have hss : s = s' := straight_unique F hf.2.2.2.2.2.1 hf'.2.2.2.2.2.1 hf.1
    subst hss
    have hpar : Par d2 d1 := par_neg2 (hf'.2.2.2.2.1.symm.trans hf.2.2.2.2.1)
    exact xuniq_T hd1 hpar W hP W' hP' nb1 nb2
  · exact (left_right_contra D F hf hf').elim
  · exact (left_right_contra D F hf' hf).elim
  · 
    have hss : s = s' := straight_unique F hf.2.2.2.2.2.1 hf'.2.2.2.2.2.1 hf.1
    subst hss
    have hpar : Par d2 d1 := hf'.2.2.2.2.1.symm.trans hf.2.2.2.2.1
    exact xuniq_R hd1 hpar W hP W' hP' nb1 nb2
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
noncomputable def Corn (D : RegionDissection N) (H : Plane) : Finset (Fin N) :=
  Finset.univ.filter (fun i => ∃ k, (D.tile i).pts k = H)
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
theorem card_corn (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (H : Plane) :
    (Corn D.toRegionDissection H).card = ∑ l, cnt D idx H l := by
  classical
  let P : Finset (Fin N × Fin 3) := Finset.univ.filter (fun p => (D.tile p.1).pts p.2 = H)
  have h1 : (Corn D.toRegionDissection H).card = P.card := by
    have himg : P.image Prod.fst = Corn D.toRegionDissection H := by
      ext i
      simp only [Finset.mem_image, P, Corn, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨j, k⟩, hk, rfl⟩; exact ⟨k, hk⟩
      · rintro ⟨k, hk⟩; exact ⟨(i, k), hk, rfl⟩
    rw [← himg, Finset.card_image_of_injOn]
    rintro ⟨i, k⟩ hp ⟨i', k'⟩ hp' he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, P] at hp hp'
    simp only at he
    subst he
    have : k = k' := (D.tile i).indep.injective (hp.trans hp'.symm)
    rw [this]
  have h2 : P.card = ∑ l, cnt D idx H l := by
    have := Finset.card_eq_sum_card_fiberwise (s := P) (t := Finset.univ) (f := fun p : Fin N × Fin 3 => idx p.1 p.2)
      (fun _ _ => Finset.mem_univ _)
    rw [this]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    unfold cnt
    congr 1
    ext p
    simp [P, and_comm]
  rw [h1, h2]
theorem card_atV (D : RegionDissection N) (H : Plane) :
    Fintype.card (AtV D H) = (Corn D H).card + (Strn D H).card := by
  classical
  have h0 : Fintype.card (AtV D H) = (Finset.univ.filter (fun i => H ∈ (D.tile i).carrier)).card := by
    exact Fintype.card_subtype (fun i => H ∈ (D.tile i).carrier)
  rw [h0, ← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun i => H ∈ (D.tile i).carrier))
    (fun i => ∃ k, (D.tile i).pts k = H)]
  congr 2
  · ext i
    simp only [Corn, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro ⟨k, hk⟩; exact ⟨vertex_mem hk, k, hk⟩
  · ext i
    simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
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
theorem head_counts (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) {H : Plane} {κ : Type} [Fintype κ]
    (F : ExtFan D.toRegionDissection H κ) (hemp : IsEmpty κ) {s a : AtV D.toRegionDissection H}
    (hs : F.q s = (-(F.p s).1, -(F.p s).2)) (ha : 0 < crs (F.p a) (F.q a)) :
    (Strn D.toRegionDissection H).card = 1 ∧ ∑ l, (cnt D idx H l : ℝ) * D.model.angleAt l = Real.pi ∧
      Fintype.card (AtV D.toRegionDissection H) = 1 + ∑ l, cnt D idx H l := by
  classical
  have hsmem : s.1 ∈ Strn D.toRegionDissection H := by
    rcases F.hspec s with ⟨k, hk, -⟩ | ⟨hnv, m, -⟩
    · exfalso
      have hc := crs_pos_of_corner (F.hok s) (F.hspec s) ⟨k, hk⟩
      rw [hs] at hc; unfold crs at hc; simp at hc; linarith
    · simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨s.2, hnv⟩
  have hcard1 : (Strn D.toRegionDissection H).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨s.1, ?_⟩
    ext j
    simp only [Finset.mem_singleton]
    constructor
    · intro hj
      simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨hjm, hnv⟩ := hj
      rcases F.hspec ⟨j, hjm⟩ with ⟨k, hk, -⟩ | ⟨-, m, -, -, hq, -⟩
      · exact absurd hk (hnv k)
      · exact congrArg Subtype.val (straight_unique F hq hs ha)
    · rintro rfl; exact hsmem
  have hsum := head_angle_sum D idx hidxA F hemp
  rw [hcard1] at hsum
  refine ⟨hcard1, by push_cast at hsum; linarith, ?_⟩
  rw [card_atV, card_corn D idx H, hcard1]; ring
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
namespace Erdos634.Draft.LaczFormal.Graph
def cx (u : V2) : ℂ := ⟨u.1, u.2⟩
theorem cx_ne_zero {u : V2} (h : u ≠ 0) : cx u ≠ 0 := by
  intro h0
  apply h
  have h1 := congrArg Complex.re h0
  have h2 := congrArg Complex.im h0
  simp [cx] at h1 h2
  exact Prod.ext h1 h2
theorem chain_rot (u v : ℕ → V2) (hu : ∀ j, u j ≠ 0) (hpar : ∀ j, Par (u (j + 1)) (v j)) (m : ℕ) :
    ∃ r : ℝ, 0 < r ∧ cx (u m) = (r : ℂ) * Complex.exp (((∑ j ∈ Finset.range m, wd (u j) (v j) : ℝ) : ℂ) * Complex.I) * cx (u 0) := by
  induction m with
  | zero => exact ⟨1, one_pos, by simp⟩
  | succ m ih =>
    obtain ⟨r, hr, hrm⟩ := ih
    obtain ⟨c, hc, hcv⟩ := (hpar m).smul
    set W : ℂ := ⟨dt (u m) (v m), crs (u m) (v m)⟩ with hW
    have hUm := cx_ne_zero (hu m)
    have hnm : ‖cx (u m)‖ ^ 2 = (u m).1 ^ 2 + (u m).2 ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [cx]; ring
    have hnpos : 0 < ‖cx (u m)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hUm) 2
    obtain ⟨Nm, hNm⟩ : ∃ Nm : ℝ, Nm = ‖cx (u m)‖ ^ 2 := ⟨_, rfl⟩
    rw [← hNm] at hnpos hnm
    have hstep : cx (u (m + 1)) * (Nm : ℂ) = (c : ℂ) * W * cx (u m) := by
      have h1 := congrArg Prod.fst hcv
      have h2 := congrArg Prod.snd hcv
      simp only at h1 h2
      apply Complex.ext
      · simp [Complex.mul_re, Complex.mul_im, cx, hW, dt, crs]
        rw [hnm]; first | ring1 | linear_combination ((u m).1 ^ 2 + (u m).2 ^ 2) * h1
      · simp [Complex.mul_re, Complex.mul_im, cx, hW, dt, crs]
        rw [hnm]; first | ring1 | linear_combination ((u m).1 ^ 2 + (u m).2 ^ 2) * h2
    have hWne : W ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      have h2 := congrArg Complex.im h0
      simp [hW] at h1 h2
      exact hu m (eq_zero_of_crs_dt (hpar m).ne_right h2 h1)
    have hWpos' : 0 < ‖W‖ := norm_pos_iff.mpr hWne
    obtain ⟨nW, hnW⟩ : ∃ x : ℝ, x = ‖W‖ := ⟨_, rfl⟩
    have hWpos : 0 < nW := by rw [hnW]; exact hWpos'
    have hWexp : W = (nW : ℂ) * Complex.exp ((wd (u m) (v m) : ℂ) * Complex.I) := by
      rw [hnW]
      have := Complex.norm_mul_exp_arg_mul_I W
      exact this.symm
    refine ⟨c * nW * r / Nm, by positivity, ?_⟩
    have hNc : (Nm : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have e1 : cx (u (m + 1)) = (c : ℂ) * W * cx (u m) / (Nm : ℂ) := by
      rw [← hstep]; field_simp
    rw [e1, hWexp, hrm, Finset.sum_range_succ]
    push_cast
    rw [add_mul, Complex.exp_add]
    field_simp
theorem opp_sum (u v : ℕ → V2) (hu : ∀ j, u j ≠ 0) (hpar : ∀ j, Par (u (j + 1)) (v j)) (m : ℕ)
    (hopp : ∃ t : ℝ, 0 < t ∧ u m = (-(t * (u 0).1), -(t * (u 0).2)))
    (hpos : 0 < ∑ j ∈ Finset.range m, wd (u j) (v j)) (hlt : ∑ j ∈ Finset.range m, wd (u j) (v j) < 2 * Real.pi) :
    ∑ j ∈ Finset.range m, wd (u j) (v j) = Real.pi := by
  obtain ⟨r, hr, hrm⟩ := chain_rot u v hu hpar m
  obtain ⟨t, ht, hut⟩ := hopp
  set S := ∑ j ∈ Finset.range m, wd (u j) (v j) with hS
  have hU0 := cx_ne_zero (hu 0)
  have h1 : (r : ℂ) * Complex.exp ((S : ℂ) * Complex.I) * cx (u 0) = (-(t : ℂ)) * cx (u 0) := by
    rw [← hrm]
    apply Complex.ext <;> simp [cx, hut]
  have h2 : (r : ℂ) * Complex.exp ((S : ℂ) * Complex.I) = -(t : ℂ) := mul_right_cancel₀ hU0 h1
  have hre := congrArg Complex.re h2
  have him := congrArg Complex.im h2
  rw [Complex.exp_mul_I] at hre him
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin] at hre him
  have hsin : Real.sin S = 0 := by
    have : r * Real.sin S = 0 := by simpa using him
    exact (mul_eq_zero.mp this).resolve_left hr.ne'
  have hcos : Real.cos S = -1 := by
    have h3 := Real.sin_sq_add_cos_sq S
    rw [hsin] at h3
    have hc2 : Real.cos S ^ 2 = 1 := by linarith
    have hneg : Real.cos S ≤ 0 := by
      have : r * Real.cos S = -t := by simpa using hre
      by_contra hpos'
      push_neg at hpos'
      nlinarith [mul_pos hr hpos']
    nlinarith [sq_nonneg (Real.cos S + 1)]
  by_cases hle : S ≤ Real.pi
  · have hm1 : S ∈ Set.Icc 0 Real.pi := ⟨hpos.le, hle⟩
    have hm2 : Real.pi ∈ Set.Icc 0 Real.pi := ⟨Real.pi_pos.le, le_rfl⟩
    exact Real.injOn_cos hm1 hm2 (by rw [hcos, Real.cos_pi])
  · push_neg at hle
    have hc : Real.cos (2 * Real.pi - S) = -1 := by rw [Real.cos_two_pi_sub]; exact hcos
    have hm1 : 2 * Real.pi - S ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
    have hm2 : Real.pi ∈ Set.Icc 0 Real.pi := ⟨Real.pi_pos.le, le_rfl⟩
    have := Real.injOn_cos hm1 hm2 (by rw [hc, Real.cos_pi])
    linarith
end Erdos634.Draft.LaczFormal.Graph
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
open scoped Classical
open Erdos634.Geometry Erdos634.KConj
section TL
variable {D : RegionDissection N} {X : Plane} {κ : Type} [Fintype κ] (F : ExtFan D X κ) (hemp : IsEmpty κ)
include F hemp
noncomputable def tl (n : ℕ) : AtV D X :=
  Sum.elim id (fun j => (hemp.false j).elim) (F.e n)
theorem e_eq (n : ℕ) : F.e n = Sum.inl (tl F hemp n) := by
  unfold tl
  rcases h : F.e n with x | j
  · simp
  · exact (hemp.false j).elim
theorem card_ext : Fintype.card (AtV D X ⊕ κ) = Fintype.card (AtV D X) := by
  haveI := hemp
  rw [Fintype.card_sum, Fintype.card_eq_zero (α := κ), add_zero]
theorem tl_add (n : ℕ) : tl F hemp (n + Fintype.card (AtV D X)) = tl F hemp n := by
  have h := F.hper n
  rw [card_ext F hemp] at h
  have := e_eq F hemp (n + Fintype.card (AtV D X))
  rw [h, e_eq F hemp n] at this
  exact (Sum.inl.inj this).symm
theorem tl_add_mul (r q : ℕ) : tl F hemp (r + Fintype.card (AtV D X) * q) = tl F hemp r := by
  induction q with
  | zero => simp
  | succ q ih =>
    have : r + Fintype.card (AtV D X) * (q + 1) = (r + Fintype.card (AtV D X) * q) + Fintype.card (AtV D X) := by ring
    rw [this, tl_add, ih]
theorem tl_mod (n : ℕ) : tl F hemp n = tl F hemp (n % Fintype.card (AtV D X)) := by
  calc tl F hemp n = tl F hemp (n % Fintype.card (AtV D X) + Fintype.card (AtV D X) * (n / Fintype.card (AtV D X))) := by
        rw [Nat.mod_add_div]
    _ = tl F hemp (n % Fintype.card (AtV D X)) := tl_add_mul F hemp _ _
theorem card_pos_atV : 0 < Fintype.card (AtV D X) := by
  haveI : Nonempty (AtV D X ⊕ κ) := ⟨F.e 0⟩
  have := Fintype.card_pos (α := AtV D X ⊕ κ)
  rwa [card_ext F hemp] at this
theorem tl_inj {a b : ℕ} (ha : a < Fintype.card (AtV D X)) (hb : b < Fintype.card (AtV D X)) (h : tl F hemp a = tl F hemp b) : a = b := by
  have h1 := F.hinj (by simpa [card_ext F hemp] using ha : a ∈ Set.Iio (Fintype.card (AtV D X ⊕ κ)))
    (by simpa [card_ext F hemp] using hb : b ∈ Set.Iio (Fintype.card (AtV D X ⊕ κ)))
    (by rw [e_eq F hemp a, e_eq F hemp b, h])
  exact h1
theorem tl_inj_mod {a b : ℕ} (h : tl F hemp a = tl F hemp b) : a % Fintype.card (AtV D X) = b % Fintype.card (AtV D X) := by
  have hpos := card_pos_atV F hemp
  rw [tl_mod F hemp a, tl_mod F hemp b] at h
  exact tl_inj F hemp (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) h
theorem tl_surj (x : AtV D X) : ∃ j < Fintype.card (AtV D X), tl F hemp j = x := by
  obtain ⟨j, hj, hej⟩ := F.hsurj (Sum.inl x)
  rw [card_ext F hemp] at hj
  refine ⟨j, hj, ?_⟩
  rw [e_eq F hemp j] at hej
  exact Sum.inl.inj hej
theorem tl_adj (n : ℕ) : Par (F.p (tl F hemp (n + 1))) (F.q (tl F hemp n)) := by
  have := F.hP n
  rw [e_eq F hemp (n + 1), e_eq F hemp n] at this
  simpa using this
theorem sum_tl {M : Type*} [AddCommMonoid M] (g : AtV D X → M) (b : ℕ) :
    ∑ s ∈ Finset.range (Fintype.card (AtV D X)), g (tl F hemp (b + s)) = ∑ x : AtV D X, g x := by
  have hpos := card_pos_atV F hemp
  let φ : Fin (Fintype.card (AtV D X)) → AtV D X := fun s => tl F hemp (b + s)
  have hinj : Function.Injective φ := by
    intro s s' h
    have := tl_inj_mod F hemp h
    apply Fin.ext
    have h2 : (b + s) % Fintype.card (AtV D X) = (b + s') % Fintype.card (AtV D X) := this
    have h3 : (s : ℕ) ≡ s' [MOD Fintype.card (AtV D X)] := Nat.ModEq.add_left_cancel' b h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 s.2 s'.2
  have hbij : Function.Bijective φ := by
    refine ⟨hinj, ?_⟩
    exact (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, by simp⟩ |>.2
  rw [Finset.sum_range (fun s => g (tl F hemp (b + s)))]
  exact Fintype.sum_bijective φ hbij _ _ (fun _ => rfl)
theorem tl_shift_surj (c : ℕ) (x : AtV D X) : ∃ s < Fintype.card (AtV D X), tl F hemp (c + s) = x := by
  have hpos := card_pos_atV F hemp
  let φ : Fin (Fintype.card (AtV D X)) → AtV D X := fun s => tl F hemp (c + s)
  have hinj : Function.Injective φ := by
    intro s s' h
    have := tl_inj_mod F hemp h
    apply Fin.ext
    have h2 : (c + s) % Fintype.card (AtV D X) = (c + s') % Fintype.card (AtV D X) := this
    have h3 : (s : ℕ) ≡ s' [MOD Fintype.card (AtV D X)] := Nat.ModEq.add_left_cancel' c h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 s.2 s'.2
  have hbij : Function.Bijective φ := (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, by simp⟩
  obtain ⟨s, hs⟩ := hbij.2 x
  exact ⟨s, s.2, hs⟩
theorem tl_ray (b i : ℕ) (hi : i < Fintype.card (AtV D X)) :
    tl F hemp (b + (i + Fintype.card (AtV D X) - 1) % Fintype.card (AtV D X) + 1) = tl F hemp (b + i) := by
  have hpos := card_pos_atV F hemp
  set m := Fintype.card (AtV D X) with hm
  by_cases h0 : i = 0
  · subst h0
    have hlt : 0 + m - 1 < m := by omega
    have : (0 + m - 1) % m = m - 1 := by rw [Nat.mod_eq_of_lt hlt]; omega
    rw [this]
    have e : b + (m - 1) + 1 = b + m := by omega
    rw [e, tl_add]
    rfl
  · have : (i + m - 1) % m = i - 1 := by
      have e : i + m - 1 = (i - 1) + m := by omega
      rw [e, Nat.add_mod_right]
      have hlt : i - 1 < m := by omega
      exact Nat.mod_eq_of_lt hlt
    rw [this]
    have e : b + (i - 1) + 1 = b + i := by omega
    rw [e]
end TL
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
section Fan
variable {D : RegionDissection N} {H : Plane} {κ : Type} [Fintype κ]
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
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal
theorem angleAt_sum (T : Tri) : T.angleAt 0 + T.angleAt 1 + T.angleAt 2 = Real.pi := by
  show cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) +
       cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) +
       cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi
  exact Erdos634.Geometry.cornerAngle_sum T
end Erdos634.Draft.LaczFormal
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
theorem ga_edge_endpoints (D : RegionDissection N) (a : ℝ) {X H : Plane} (h : GaEdge D a X H) :
    (∃ i k, (D.tile i).pts k = X) ∧ (∃ i k, (D.tile i).pts k = H) := by
  refine ⟨?_, ga_edge_vertex D a h⟩
  obtain ⟨d, Y, L1, L2, hd, hnb, W1, W2, hL1, hL2, -⟩ := h
  cases W1 with
  | nil => exact absurd rfl hL1
  | cons hS _ =>
    obtain ⟨kk, f, g, hk, -⟩ := hS
    exact ⟨_, kk, hk⟩
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
open Erdos634.Geometry Erdos634.KConj
namespace Erdos634.Draft.LaczFormal.Graph
variable {N : ℕ}
theorem list_filter_len {α : Type*} (f : ℕ → α) (p : α → Bool) (m : ℕ) :
    (((List.range m).map f).filter p).length = ∑ s ∈ Finset.range m, if p (f s) = true then 1 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    congr 1
    by_cases h : p (f m) = true <;> simp [h]
section CD
variable (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X : Plane} {κ : Type} [Fintype κ]
  (F : ExtFan D.toDissection X κ) (hcor : ∀ x : AtV D.toDissection X, 0 < crs (F.p x) (F.q x))
include hcor
omit hcor in
theorem par_not_neg {u v : V2} (h1 : Par u v) (h2 : Par u (neg2 v)) : False := by
  have a := h1.2
  have b := h2.2
  unfold dt neg2 at b
  unfold dt at a
  simp only at b
  nlinarith
end CD
end Erdos634.Draft.LaczFormal.Graph
end

section
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
open scoped Classical
open Erdos634.Geometry Erdos634.KConj
theorem cnt_atv (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X : Plane}
    (k : AtV D.toRegionDissection X → Fin 3) (hk : ∀ x, (D.tile x.1).pts (k x) = X) (l : Fin 3) :
    cnt D idx X l = (Finset.univ.filter (fun x : AtV D.toRegionDissection X => idx x.1 (k x) = l)).card := by
  classical
  unfold cnt
  symm
  refine Finset.card_bij (fun x _ => (x.1, k x)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hk x, hx⟩
  · intro x _ y _ h
    exact Subtype.ext (congrArg Prod.fst h)
  · rintro ⟨i, k'⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hmem : X ∈ (D.tile i).carrier := vertex_mem hp.1
    refine ⟨⟨i, hmem⟩, ?_, ?_⟩
    · have : k ⟨i, hmem⟩ = k' := (D.tile i).indep.injective ((hk ⟨i, hmem⟩).trans hp.1.symm)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [this] using hp.2⟩
    · have : k ⟨i, hmem⟩ = k' := (D.tile i).indep.injective ((hk ⟨i, hmem⟩).trans hp.1.symm)
      simp [this]
section CD
variable (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {X : Plane} {κ : Type} [Fintype κ]
  (F : ExtFan D.toRegionDissection X κ) (hcor : ∀ x : AtV D.toRegionDissection X, 0 < crs (F.p x) (F.q x))
include hcor
theorem cd_ex (x : AtV D.toRegionDissection X) :
    ∃ p : Fin 3 × Bool, (D.tile x.1).pts p.1 = X ∧ F.p x = toV2 ((D.tile x.1).pts (armP p.1 p.2) - X) ∧
      F.q x = toV2 ((D.tile x.1).pts (armQ p.1 p.2) - X) := by
  obtain ⟨k, hk⟩ := F.corner_of_crs x (hcor x)
  obtain ⟨kk, fl, h1, h2, h3⟩ := spec_corner_data (F.hspec x) ⟨k, hk⟩
  exact ⟨(kk, fl), h1, h2, h3⟩
noncomputable def cd (x : AtV D.toRegionDissection X) : Fin 3 × Bool := Classical.choose (cd_ex D F hcor x)
theorem cd_spec (x : AtV D.toRegionDissection X) :
    (D.tile x.1).pts (cd D F hcor x).1 = X ∧ F.p x = toV2 ((D.tile x.1).pts (armP (cd D F hcor x).1 (cd D F hcor x).2) - X) ∧
      F.q x = toV2 ((D.tile x.1).pts (armQ (cd D F hcor x).1 (cd D F hcor x).2) - X) :=
  Classical.choose_spec (cd_ex D F hcor x)
noncomputable def cdcode (x : AtV D.toRegionDissection X) : ℕ := codeOf (idx x.1) (cd D F hcor x).1 (cd D F hcor x).2
theorem cdcode_spec (x : AtV D.toRegionDissection X) :
    RegFan.tT (cdcode D idx F hcor x) = (idx x.1 (cd D F hcor x).1 : ℕ) ∧
    RegFan.tU (cdcode D idx F hcor x) = (idx x.1 (armP (cd D F hcor x).1 (cd D F hcor x).2) : ℕ) ∧
    RegFan.tW (cdcode D idx F hcor x) = (idx x.1 (armQ (cd D F hcor x).1 (cd D F hcor x).2) : ℕ) ∧
    cdcode D idx F hcor x < 6 :=
  codeOf_spec' (idx x.1) _ _
noncomputable def lst (hemp : IsEmpty κ) (b : ℕ) : List ℕ :=
  (List.range (Fintype.card (AtV D.toRegionDissection X))).map (fun s => cdcode D idx F hcor (tl F hemp (b + s)))
theorem lst_length (hemp : IsEmpty κ) (b : ℕ) : (lst D idx F hcor hemp b).length = Fintype.card (AtV D.toRegionDissection X) := by
  simp [lst]
theorem lst_getD (hemp : IsEmpty κ) (b s : ℕ) (hs : s < Fintype.card (AtV D.toRegionDissection X)) :
    (lst D idx F hcor hemp b).getD s 0 = cdcode D idx F hcor (tl F hemp (b + s)) := by
  simp [lst, List.getD_eq_getElem?_getD, hs]
theorem lst_lt (hemp : IsEmpty κ) (b : ℕ) : ∀ x ∈ lst D idx F hcor hemp b, x < 6 := by
  intro x hx
  simp only [lst, List.mem_map, List.mem_range] at hx
  obtain ⟨s, -, rfl⟩ := hx
  exact (cdcode_spec D idx F hcor _).2.2.2
theorem lst_cnt (hemp : IsEmpty κ) (b : ℕ) (j : Fin 3) :
    RegFan.cnt (lst D idx F hcor hemp b) (j : ℕ) = cnt D idx X j := by
  classical
  rw [cnt_atv D idx (fun x => (cd D F hcor x).1) (fun x => (cd_spec D F hcor x).1) j]
  unfold RegFan.cnt lst
  rw [list_filter_len, Finset.card_filter]
  have := sum_tl F hemp (fun x : AtV D.toRegionDissection X => if (idx x.1 (cd D F hcor x).1 : Fin 3) = j then 1 else 0) b
  rw [← this]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  have h := (cdcode_spec D idx F hcor (tl F hemp (b + s))).1
  simp only [h, beq_iff_eq]
  congr 1
  simp [Fin.ext_iff]
theorem wd_cd' (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v) (x : AtV D.toRegionDissection X) :
    wd (F.p x) (F.q x) = D.model.angleAt (idx x.1 (cd D F hcor x).1) := by
  obtain ⟨hk, -, -⟩ := cd_spec D F hcor x
  have h1 : wd (F.p x) (F.q x) = (D.tile x.1).angleAt (cd D F hcor x).1 := by
    rw [F.hwd x]
    have e := Tri.localAngle_vertex (D.tile x.1) (cd D F hcor x).1
    rw [hk] at e
    have e2 : (D.tile x.1).angleAt (cd D F hcor x).1 =
        cornerAngle ((D.tile x.1).pts ((cd D F hcor x).1 + 1)) X ((D.tile x.1).pts ((cd D F hcor x).1 + 2)) := by
      unfold Tri.angleAt; rw [hk]
    rw [e2]; exact e
  rw [h1, ← hidxA]
theorem opp_colG_aux (hemp : IsEmpty κ) (b i : ℕ) (hi : i < Fintype.card (AtV D.toRegionDissection X)) (s : AtV D.toRegionDissection X)
    (hs : Par (F.p s) (neg2 (F.q (tl F hemp (b + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X)))))) :
    ∃ m' : ℕ, 0 < m' ∧ m' < Fintype.card (AtV D.toRegionDissection X) ∧
      ∑ t ∈ Finset.range m', wd (F.p (tl F hemp (b + i + t))) (F.q (tl F hemp (b + i + t))) = Real.pi := by
  classical
  set m := Fintype.card (AtV D.toRegionDissection X) with hm
  have hpos : 0 < m := card_pos_atV F hemp
  set ρ := F.q (tl F hemp (b + (i + m - 1) % m)) with hρ
  set c := b + i with hc
  have hadj : Par (F.p (tl F hemp c)) ρ := by
    have h := tl_adj F hemp (b + (i + m - 1) % m)
    rw [tl_ray F hemp b i hi] at h
    exact h
  obtain ⟨m', hm', hsm⟩ := tl_shift_surj F hemp c s
  have hm0 : m' ≠ 0 := by
    rintro rfl
    simp only [add_zero] at hsm
    rw [hsm] at hadj
    exact par_not_neg hadj hs
  set u' : ℕ → V2 := fun t => F.p (tl F hemp (c + t)) with hu'
  set v' : ℕ → V2 := fun t => F.q (tl F hemp (c + t)) with hv'
  have hu0 : ∀ t, u' t ≠ 0 := fun t => (F.hok _).ne_p
  have hpar : ∀ t, Par (u' (t + 1)) (v' t) := fun t => tl_adj F hemp (c + t)
  have hopp : ∃ t : ℝ, 0 < t ∧ u' m' = (-(t * (u' 0).1), -(t * (u' 0).2)) := by
    have hum : Par (u' m') (neg2 ρ) := by simp only [hu']; rw [hsm]; exact hs
    have hu0' : Par (u' 0) ρ := by simpa [hu'] using hadj
    obtain ⟨a, ha, hau⟩ := hum.smul
    obtain ⟨b', hb', hbu⟩ := hu0'.smul
    refine ⟨a / b', div_pos ha hb', ?_⟩
    rw [hau, hbu]
    unfold neg2
    ext <;> simp <;> field_simp
  have htot : ∑ t ∈ Finset.range m, wd (u' t) (v' t) = 2 * Real.pi := by
    have h1 := sum_tl F hemp (fun x : AtV D.toRegionDissection X => wd (F.p x) (F.q x)) c
    have h2 := F.hsum
    have hv : ∑ j, wd (F.pe j) (F.qe j) = 0 := by haveI := hemp; simp
    rw [hv, add_zero] at h2
    simpa [hu', hv'] using h1.trans h2
  have hSpos : 0 < ∑ t ∈ Finset.range m', wd (u' t) (v' t) := by
    apply Finset.sum_pos
    · intro t _; exact wd_pos (F.hok _)
    · exact ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hm0)⟩
  have hSlt : ∑ t ∈ Finset.range m', wd (u' t) (v' t) < 2 * Real.pi := by
    rw [← htot, ← Finset.sum_range_add_sum_Ico (fun t => wd (u' t) (v' t)) (le_of_lt hm')]
    have : 0 < ∑ t ∈ Finset.Ico m' m, wd (u' t) (v' t) := by
      apply Finset.sum_pos
      · intro t _; exact wd_pos (F.hok _)
      · exact ⟨m', Finset.mem_Ico.mpr ⟨le_rfl, hm'⟩⟩
    linarith
  have hπ := opp_sum u' v' hu0 hpar m' hopp hSpos hSlt
  exact ⟨m', Nat.pos_of_ne_zero hm0, hm', by simpa [hu', hv'] using hπ⟩
end CD
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
open scoped Classical Fin.NatCast Fin.CommRing
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N M : ℕ} [NeZero M]
theorem comm_of_two_combs {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) {r p q : ℕ} (hr : 0 < r) (e1 : (r : ℝ) * a = p * b + q * c)
    {r' p' q' : ℕ} (hr' : 0 < r') (e2 : (r' : ℝ) * b = p' * a + q' * c) : Comm a b := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp
      have : (0 : ℝ) < r * a := mul_pos (by exact_mod_cast hr) ha
      have e0 : (r : ℝ) * a = 0 := by rw [e1]; simp
      linarith
    · exact ⟨r, p, hr, hp, by simpa using e1⟩
  rcases Nat.eq_zero_or_pos q' with hq' | hq'
  · subst hq'
    rcases Nat.eq_zero_or_pos p' with hp' | hp'
    · subst hp'
      have : (0 : ℝ) < r' * b := mul_pos (by exact_mod_cast hr') hb
      have e0 : (r' : ℝ) * b = 0 := by rw [e2]; simp
      linarith
    · exact ⟨p', r', hp', hr', by simpa using e2.symm⟩
  refine ⟨q * p' + q' * r, q * r' + q' * p, Nat.add_pos_right _ (Nat.mul_pos hq' hr), Nat.add_pos_left (Nat.mul_pos hq hr') _, ?_⟩
  push_cast
  linear_combination (q' : ℝ) * e1 - (q : ℝ) * e2
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
theorem sum_cnt_vtx (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (l : Fin 3) :
    ∑ v ∈ vtxSet D.toRegionDissection, cnt D idx v l = N := by
  classical
  set s : Finset (Fin N × Fin 3) := Finset.univ.filter (fun p => idx p.1 p.2 = l) with hs
  have hcard : s.card = N := by
    have : s.card = (Finset.univ : Finset (Fin N)).card := by
      refine Finset.card_bij (fun p _ => p.1) (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro p hp q hq hpq
        simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        have h1 : p.1 = q.1 := hpq
        have h2 : idx p.1 p.2 = idx p.1 q.2 := by rw [hp, h1, hq]
        exact Prod.ext h1 ((idx p.1).injective h2)
      · intro i _
        refine ⟨(i, (idx i).symm l), ?_, rfl⟩
        simp [hs]
    rw [this]; simp
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2) (s := s) (t := vtxSet D.toRegionDissection)
    (fun p _ => mem_vtxSet.mpr ⟨p.1, p.2, rfl⟩)
  refine Eq.trans ?_ hcard
  rw [hfib]
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold cnt
  congr 1
  ext p
  simp [hs, and_comm]
end Erdos634.Draft.LaczFormal.RG
end

section
namespace Erdos634.Draft.LaczFormal.RegFan
def centerOK (l : List ℕ) : Bool := !(cnt l 2 == 3) || (List.range 3).any (fun i => gaEdge l i)
theorem center_check : (allFans 3).all centerOK = true := by decide +kernel
theorem center_edge (l : List ℕ) (hlen : l.length = 3) (hlt : ∀ x ∈ l, x < 6) (h : cnt l 2 = 3) :
    (List.range 3).any (fun i => gaEdge l i) = true := by
  have := (List.all_eq_true.mp center_check) l (mem_allFans 3 l hlen hlt)
  simpa [centerOK, h] using this
end Erdos634.Draft.LaczFormal.RegFan
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N M : ℕ} [NeZero M]
theorem gk_two_gamma (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {Z X : Plane}
    (h : GkEdge D.toRegionDissection idx Z X) : 2 ≤ cnt D idx Z 2 := by
  classical
  obtain ⟨i, j, k1, k2, k1', k2', hij, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  unfold cnt
  have : ({(i, k1), (j, k1')} : Finset (Fin N × Fin 3)) ⊆ Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = Z ∧ idx p.1 p.2 = 2) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [*]
  have h3 := Finset.card_le_card this
  rw [Finset.card_pair (fun e => hij (congrArg Prod.fst e))] at h3
  exact h3
theorem bz_head_analysis (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    {X H : Plane} (hE : GaEdge D.toRegionDissection (slen D 0) X H) :
    (∑ l, (cnt D idx H l : ℝ) * D.model.angleAt l = Real.pi) ∧
      (cnt D idx H 0 = 1 → cnt D idx H 1 = 1 → cnt D idx H 2 = 1 → ∃ H', GaEdge D.toRegionDissection (slen D 0) H H') := by
  classical
  obtain ⟨κ, _, ⟨F⟩⟩ := HasFansC.fans (D := D.toRegionDissection) H (ga_edge_vertex _ _ hE)
  obtain ⟨d, hd, nb, hc⟩ := ga_edge_data D idx hidx hnc hE F
  have key : ∀ {e : V2} {u v s : AtV D.toRegionDissection H}, HeadCfg D F e u v s →
      (∑ l, (cnt D idx H l : ℝ) * D.model.angleAt l = Real.pi) ∧
      (cnt D idx H 0 = 1 → cnt D idx H 1 = 1 → cnt D idx H 2 = 1 → ∃ H', GaEdge D.toRegionDissection (slen D 0) H H') := by
    intro e u v s hc
    have hc' := hc
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hc'
    have hcyc := F.head_cyc u v s hc1 hc2 hc3 hc4 hc5 hc6
    have hemp : IsEmpty κ := hcyc.1
    obtain ⟨hS1, hsum, hcard⟩ := head_counts D idx hidxA F hemp hc6 hc1
    refine ⟨hsum, fun h0 h1 h2 => ?_⟩
    have hcard4 : Fintype.card (AtV D.toRegionDissection H) = 4 := by
      rw [hcard, Fin.sum_univ_three]; omega
    have hpair : ∀ (l : Fin 3) (t1 t2 : Fin N) (k1 k2 : Fin 3), t1 ≠ t2 → (D.tile t1).pts k1 = H → (D.tile t2).pts k2 = H →
        idx t1 k1 = l → idx t2 k2 = l → 2 ≤ cnt D idx H l := by
      intro l t1 t2 k1 k2 hne h1 h2 e1 e2
      unfold cnt
      have : ({(t1, k1), (t2, k2)} : Finset (Fin N × Fin 3)) ⊆ Finset.univ.filter (fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2 = H ∧ idx p.1 p.2 = l) := by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl <;> simp [*]
      have h3 := Finset.card_le_card this
      rw [Finset.card_pair (fun e => hne (congrArg Prod.fst e))] at h3
      exact h3
    refine (head_out_edge D idx hidx hnc hab hac F hc hcard4 (Or.inl ?_)).resolve_right ?_
    · intro t1 t2 _ _ hne k1 k2 hk1 hk2 heq
      have hl : cnt D idx H (idx t1.1 k1) ≥ 2 := hpair (idx t1.1 k1) t1.1 t2.1 k1 k2 (fun e => hne (Subtype.ext e)) hk1 hk2 rfl heq.symm
      generalize idx t1.1 k1 = z at hl
      fin_cases z <;> simp_all <;> omega
    · rintro ⟨Z, hZ⟩
      have := gk_two_gamma D idx hZ
      omega
  rcases hc with ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩ | ⟨P, W, hP, a, b, s, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact key (HeadCfg.of_left D F a b s h1 h2 h3 h4 h5 h6 h7 h8)
  · exact key (HeadCfg.of_right D F a b s h1 h2 h3 h4 h5 h6 h7 h8)
theorem bz_center_out (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2)) (hab : slen D 0 ≠ slen D 1) (hac : slen D 0 ≠ slen D 2)
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) {X : Plane} (hvert : ∃ j k, (D.tile j).pts k = X) (hint : X ∈ interior D.region)
    (h0 : cnt D idx X 0 = 0) (h1 : cnt D idx X 1 = 0) (h2 : cnt D idx X 2 = 3) :
    ∃ H', GaEdge D.toRegionDissection (slen D 0) X H' := by
  classical
  have hpi := Real.pi_pos
  obtain ⟨F⟩ := extFan_interior D.toRegionDissection X hvert hint
  have hemp : IsEmpty Empty := inferInstance
  have hang := head_angle_sum D idx hidxA F hemp
  have hStr : (Strn D.toRegionDissection X).card = 0 := by
    by_contra hne
    have h1' : (1 : ℝ) ≤ (Strn D.toRegionDissection X).card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    rw [Fin.sum_univ_three, h0, h1, h2, hγ] at hang
    have : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) * D.model.angleAt 0 + ((0 : ℕ) : ℝ) * D.model.angleAt 1 := by simp
    push_cast at hang
    nlinarith
  have hcor : ∀ x : AtV D.toRegionDissection X, 0 < crs (F.p x) (F.q x) := by
    intro x
    rcases F.hspec x with ⟨k, hk, -⟩ | ⟨hnv, -⟩
    · exact crs_pos_of_corner (F.hok x) (F.hspec x) ⟨k, hk⟩
    · exfalso
      have : x.1 ∈ Strn D.toRegionDissection X := by
        simp only [Strn, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨x.2, hnv⟩
      have := Finset.card_pos.mpr ⟨x.1, this⟩
      omega
  have hcard : Fintype.card (AtV D.toRegionDissection X) = 3 := by
    rw [card_atV, card_corn D idx X, hStr, Fin.sum_univ_three]
    omega
  set l := lst D idx F hcor hemp 0 with hl
  have hlen : l.length = 3 := by rw [hl, lst_length, hcard]
  have hlt := lst_lt D idx F hcor hemp 0
  have hc2 : RegFan.cnt l 2 = 3 := (lst_cnt D idx F hcor hemp 0 2).trans h2
  have hconcl := RegFan.center_edge l hlen hlt hc2
  rw [List.any_eq_true] at hconcl
  obtain ⟨i, hi3, hi⟩ := hconcl
  have hi' : i < Fintype.card (AtV D.toRegionDissection X) := by rw [hcard]; exact List.mem_range.mp hi3
  set x := tl F hemp (0 + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X)) with hx
  set y := tl F hemp (0 + i) with hy
  have hxy : Par (F.p y) (F.q x) := by
    have h := tl_adj F hemp (0 + (i + Fintype.card (AtV D.toRegionDissection X) - 1) % Fintype.card (AtV D.toRegionDissection X))
    rw [tl_ray F hemp 0 i hi'] at h
    exact h
  have hLc : RegFan.Lc l i = cdcode D idx F hcor x := by
    unfold RegFan.Lc; rw [hlen]
    have hlt' : (i + 3 - 1) % 3 < Fintype.card (AtV D.toRegionDissection X) := by rw [hcard]; exact Nat.mod_lt _ (by norm_num)
    rw [hl, lst_getD D idx F hcor hemp 0 _ hlt', hx, hcard]
  have hRc : RegFan.Rc l i = cdcode D idx F hcor y := by
    unfold RegFan.Rc; rw [hlen]
    have hlt' : i % 3 < Fintype.card (AtV D.toRegionDissection X) := by rw [hcard]; exact Nat.mod_lt _ (by norm_num)
    rw [hl, lst_getD D idx F hcor hemp 0 _ hlt']
    have : i % 3 = i := Nat.mod_eq_of_lt (List.mem_range.mp hi3)
    rw [this]
  obtain ⟨hkx, hpx, hqx⟩ := cd_spec D F hcor x
  obtain ⟨hky, hpy, hqy⟩ := cd_spec D F hcor y
  have htyp : ∀ z : AtV D.toRegionDissection X, idx z.1 (cd D F hcor z).1 = 2 := by
    intro z
    obtain ⟨hk, -, -⟩ := cd_spec D F hcor z
    have hge : ∀ l : Fin 3, idx z.1 (cd D F hcor z).1 = l → 1 ≤ cnt D idx X l := by
      intro l hl
      unfold cnt
      exact Finset.card_pos.mpr ⟨(z.1, (cd D F hcor z).1), by simp [hk, hl]⟩
    generalize hz : idx z.1 (cd D F hcor z).1 = w
    fin_cases w
    · have := hge 0 hz; omega
    · have := hge 1 hz; omega
    · rfl
  have hp : ∀ s' : AtV D.toRegionDissection X, ¬ Par (F.p s') (neg2 (F.q x)) := by
    intro s' hs
    obtain ⟨m', hm0, hm', hπ⟩ := opp_colG_aux D F hcor hemp 0 i hi' s' hs
    have hwd : ∀ t, wd (F.p (tl F hemp (0 + i + t))) (F.q (tl F hemp (0 + i + t))) = 2 * Real.pi / 3 := by
      intro t
      rw [wd_cd' D idx F hcor hidxA, htyp, hγ]
    rw [Finset.sum_congr rfl (fun t _ => hwd t), Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hπ
    have hm2 : m' = 1 ∨ m' = 2 := by omega
    rcases hm2 with rfl | rfl <;> (push_cast at hπ; linarith)
  have hnb : NoBack D.toRegionDissection (F.q x) X := by
    apply F.noBack_of_none
    intro s
    refine ⟨hp s, fun h => ?_⟩
    obtain ⟨j0, -, hj0⟩ := tl_surj F hemp s
    have h1 := tl_adj F hemp j0
    rw [hj0] at h1
    exact hp _ (h1.trans h)
  unfold RegFan.gaEdge at hi
  rw [hLc, hRc] at hi
  exact ga_of_codes D idx hidx hnc hab hac F x y (hcor x) (hcor y) hxy hnb hkx hky hqx hpy hi
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
namespace Erdos634.Geometry
theorem Tri.oppLen_pos' (T : Tri) (k : Fin 3) : 0 < T.oppLen k := by
  unfold Tri.oppLen
  have hne : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  exact dist_pos.mpr fun h => hne (T.indep.injective h)
theorem Tri.angleAt_pos'' (T : Tri) (j : Fin 3) : 0 < T.angleAt j :=
  Erdos634.MarchFlank.cornerAngle_pos T j
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
theorem tpt_swap {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    T.TwoPiThreeData (Real.pi / 3 - α) b a c := by
  obtain ⟨σ, h0, ha, h1, hb, h2, hc⟩ := h
  refine ⟨σ * Equiv.swap 0 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]; exact h1
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]; exact hb
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]; rw [h0]; ring
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]; exact ha
  · simp only [Equiv.Perm.mul_apply]
    have : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
    rw [this]; exact h2
  · simp only [Equiv.Perm.mul_apply]
    have : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
    rw [this]; exact hc
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N M : ℕ} [NeZero M]
theorem irr_coeff {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (A B : ℤ)
    (h : (A : ℝ) * α = (B : ℝ) * (Real.pi / 3)) : A = 0 ∧ B = 0 := by
  have hpi := Real.pi_pos
  by_cases hA : A = 0
  · subst hA
    refine ⟨rfl, ?_⟩
    have : (B : ℝ) * (Real.pi / 3) = 0 := by rw [← h]; simp
    rcases mul_eq_zero.mp this with h1 | h1
    · exact_mod_cast h1
    · exfalso; linarith
  · exfalso
    apply hα
    have hA' : (A : ℝ) ≠ 0 := by exact_mod_cast hA
    refine ⟨(B : ℚ) / (3 * (A : ℚ)), ?_⟩
    push_cast
    field_simp
    linarith
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
theorem exists_convpoly_of_tri (T : Tri) :
    ∃ P : ConvPoly 3, P.carrier = T.carrier ∧ ∃ τ : Equiv.Perm (Fin 3), ∀ i, P.angle i = T.angleAt (τ i) := by
  have hdet : T.det = cross2 (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := rfl
  rcases T.det_pos_or_neg with hpos | hneg
  · have h : 0 < cross2 (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := by rw [← hdet]; exact hpos
    refine ⟨convPoly3 (T.pts 0) (T.pts 1) (T.pts 2) h, ?_, 1, fun i => ?_⟩
    · rw [convPoly3_carrier]
      show convexHull ℝ (Set.range ![T.pts 0, T.pts 1, T.pts 2]) = convexHull ℝ (Set.range T.pts)
      have : (![T.pts 0, T.pts 1, T.pts 2] : Fin 3 → Plane) = T.pts := by
        funext k; fin_cases k <;> rfl
      rw [this]
    · rw [convPoly3_angle]
      fin_cases i <;> rfl
  · have h : 0 < cross2 (T.pts 2 - T.pts 0) (T.pts 1 - T.pts 0) := by
      have : cross2 (T.pts 2 - T.pts 0) (T.pts 1 - T.pts 0) = - T.det := by
        rw [hdet]; unfold cross2; ring
      rw [this]; linarith
    refine ⟨convPoly3 (T.pts 0) (T.pts 2) (T.pts 1) h, ?_, Equiv.swap 1 2, fun i => ?_⟩
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
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N M : ℕ} [NeZero M]
theorem vertex_type_gen2 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hcorn : ∀ k : Fin M, cnt D idx (P.v (k + 1)) 2 = 0) {X : Plane}
    (hvert : ∃ j k, (D.tile j).pts k = X) :
    (cnt D idx X 0 = cnt D idx X 1 ∧
      ((X ∈ interior D.region ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = 6) ∨ cnt D idx X 0 + 2 * cnt D idx X 2 = 3 ∨
        (X ∉ interior D.region ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = 1 ∧ ∃ k : Fin M, X = P.v (k + 1)))) ∨
    (cnt D idx X 2 = 0 ∧ ∃ k : Fin M, X = P.v (k + 1)) := by
  have hAexp : Asum D idx X = (cnt D idx X 0 : ℝ) * D.model.angleAt 0 + (cnt D idx X 1 : ℝ) * D.model.angleAt 1 + (cnt D idx X 2 : ℝ) * D.model.angleAt 2 := by
    unfold Asum; rw [Fin.sum_univ_three]
  have hpi := Real.pi_pos
  have key : ∀ m : ℕ, Asum D idx X = m * (Real.pi / 3) → cnt D idx X 0 = cnt D idx X 1 ∧ cnt D idx X 0 + 2 * cnt D idx X 2 = m := by
    intro m hm
    exact type_arith hαβ hγ hα _ _ _ m (by rw [← hAexp]; exact hm)
  rcases vertex_A D P hreg idx hidxA hvert with ⟨hi, h2 | h1⟩ | ⟨hni, h1 | ⟨k, hXk, hk⟩⟩
  · have := key 6 (by rw [h2]; push_cast; ring)
    exact Or.inl ⟨this.1, Or.inl ⟨hi, this.2⟩⟩
  · have := key 3 (by rw [h1]; push_cast; ring)
    exact Or.inl ⟨this.1, Or.inr (Or.inl this.2)⟩
  · have := key 3 (by rw [h1]; push_cast; ring)
    exact Or.inl ⟨this.1, Or.inr (Or.inl this.2)⟩
  · exact Or.inr ⟨by rw [hXk]; exact hcorn k, k, hXk⟩
theorem bz_lemma35_gen2 (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i k k', dist ((D.tile i).pts k) ((D.tile i).pts k') = dist (D.model.pts (idx i k)) (D.model.pts (idx i k')))
    (hidxA : ∀ i v, D.model.angleAt (idx i v) = (D.tile i).angleAt v)
    (hnc : NotComb (slen D 0) (slen D 1) (slen D 2))
    (hγ : D.model.angleAt 2 = 2 * Real.pi / 3) (hαβ : D.model.angleAt 0 + D.model.angleAt 1 = Real.pi / 3)
    (hα : ¬ ∃ r : ℚ, D.model.angleAt 0 = (r : ℝ) * Real.pi)
    (hPlt : ∀ i, P.angle i < Real.pi) (hcorn : ∀ k : Fin M, cnt D idx (P.v (k + 1)) 2 = 0) : False := by
  classical
  have hpi := Real.pi_pos
  have hα0 := model_angle_pos' D 0
  have hβ0 := model_angle_pos' D 1
  have hab : slen D 0 ≠ slen D 1 := by
    intro e
    have := hnc 1 1 0 one_pos
    apply this; rw [e]; simp
  have hac : slen D 0 ≠ slen D 2 := by
    intro e
    have := hnc 1 0 1 one_pos
    apply this; rw [e]; simp
  set V := vtxSet D.toRegionDissection with hVdef
  set E : Finset (Plane × Plane) := (V ×ˢ V).filter (fun e => GaEdge D.toRegionDissection (slen D 0) e.1 e.2) with hE
  let out : Plane → ℕ := fun v => (E.filter (fun e => e.1 = v)).card
  let inn : Plane → ℕ := fun v => (E.filter (fun e => e.2 = v)).card
  have hEmem : ∀ e : Plane × Plane, e ∈ E ↔ GaEdge D.toRegionDissection (slen D 0) e.1 e.2 := by
    intro e
    simp only [hE, Finset.mem_filter, Finset.mem_product]
    constructor
    · exact fun h => h.2
    · intro h
      have := ga_edge_endpoints D.toRegionDissection (slen D 0) h
      exact ⟨⟨mem_vtxSet.mpr this.1, mem_vtxSet.mpr this.2⟩, h⟩
  have hin1 : ∀ v, inn v ≤ 1 := by
    intro v
    simp only [inn]
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    have h1 := (hEmem a).mp ha.1
    have h2 := (hEmem b).mp hb.1
    rw [ha.2] at h1
    rw [hb.2] at h2
    have := ga_indegree D idx hidx hnc h1 h2
    exact Prod.ext this (ha.2.trans hb.2.symm)
  have hbal : ∑ v ∈ V, (out v : ℤ) = ∑ v ∈ V, (inn v : ℤ) := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := E) (t := V)
      (fun e he => ((Finset.mem_product.mp (Finset.mem_filter.mp he).1).1))
    have h2 := Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := E) (t := V)
      (fun e he => ((Finset.mem_product.mp (Finset.mem_filter.mp he).1).2))
    have : ∑ v ∈ V, out v = ∑ v ∈ V, inn v := by
      simp only [out, inn]; rw [← h1, ← h2]
    exact_mod_cast this
  have hs0 : ∑ v ∈ V, (cnt D idx v 0 : ℤ) = N := by exact_mod_cast sum_cnt_vtx D idx 0
  have hs1 : ∑ v ∈ V, (cnt D idx v 1 : ℤ) = N := by exact_mod_cast sum_cnt_vtx D idx 1
  have hs2 : ∑ v ∈ V, (cnt D idx v 2 : ℤ) = N := by exact_mod_cast sum_cnt_vtx D idx 2
  have hin0poly : ∀ k : Fin M, inn (P.v (k + 1)) = 0 := by
    intro k
    by_contra hne
    have hi1 := hin1 (P.v (k + 1))
    have h1 : inn (P.v (k + 1)) = 1 := by omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by simp only [inn] at h1 ⊢; omega : 0 < (E.filter (fun e => e.2 = P.v (k + 1))).card)
    simp only [Finset.mem_filter] at he
    have hge := (hEmem e).mp he.1
    rw [he.2] at hge
    obtain ⟨hsum, -⟩ := bz_head_analysis D idx hidx hidxA hnc hab hac hge
    have hv : ∃ j k', (D.tile j).pts k' = P.v (k + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (k + 1)
    have hcA := corner_A D P hreg idx hidxA k hv
    have hAs : Asum D idx (P.v (k + 1)) = Real.pi := by unfold Asum; exact hsum
    rw [hAs] at hcA
    have := hPlt (k + 1)
    linarith
  have hf : ∀ v ∈ V, 0 ≤ 6 * (out v : ℤ) - 6 * (inn v : ℤ) + (cnt D idx v 0 : ℤ) + (cnt D idx v 1 : ℤ) - 2 * (cnt D idx v 2 : ℤ) := by
    intro v hv
    have hvert : ∃ j k, (D.tile j).pts k = v := mem_vtxSet.mp hv
    rcases vertex_type_gen2 D P hreg idx hidxA hγ hαβ hα hcorn hvert with ⟨hreg', htype⟩ | ⟨hc2, k, hk⟩
    · have F1 : inn v = 1 → cnt D idx v 0 + 2 * cnt D idx v 2 = 3 ∧
          (cnt D idx v 0 = 1 → cnt D idx v 2 = 1 → 1 ≤ out v) := by
        intro h1
        have hne : (E.filter (fun e => e.2 = v)).Nonempty := Finset.card_pos.mp (by simp only [inn] at h1; omega)
        obtain ⟨e, he⟩ := hne
        simp only [Finset.mem_filter] at he
        have hge := (hEmem e).mp he.1
        rw [he.2] at hge
        obtain ⟨hsum, hsimple⟩ := bz_head_analysis D idx hidx hidxA hnc hab hac hge
        have hexp : ∑ l, (cnt D idx v l : ℝ) * D.model.angleAt l = (cnt D idx v 0 : ℝ) * D.model.angleAt 0 + (cnt D idx v 1 : ℝ) * D.model.angleAt 1 + (cnt D idx v 2 : ℝ) * D.model.angleAt 2 := by
          rw [Fin.sum_univ_three]
        have := type_arith hαβ hγ hα (cnt D idx v 0) (cnt D idx v 1) (cnt D idx v 2) 3 (by rw [← hexp, hsum]; push_cast; ring)
        refine ⟨this.2, fun h0 h2 => ?_⟩
        have h1' : cnt D idx v 1 = 1 := by omega
        obtain ⟨H', hH'⟩ := hsimple h0 h1' h2
        have : (v, H') ∈ E.filter (fun e => e.1 = v) := by
          rw [Finset.mem_filter]
          exact ⟨(hEmem (v, H')).mpr hH', rfl⟩
        exact Finset.card_pos.mpr ⟨_, this⟩
      have F2 : cnt D idx v 0 = 0 → cnt D idx v 2 = 3 → 1 ≤ out v := by
        intro h0 h2
        have hint : v ∈ interior D.region := by
          rcases htype with ⟨hi, -⟩ | h | ⟨-, h, -⟩
          · exact hi
          · omega
          · omega
        have h1' : cnt D idx v 1 = 0 := by omega
        obtain ⟨H', hH'⟩ := bz_center_out D idx hidx hidxA hnc hab hac hγ hvert hint h0 h1' h2
        have : (v, H') ∈ E.filter (fun e => e.1 = v) := by
          rw [Finset.mem_filter]
          exact ⟨(hEmem (v, H')).mpr hH', rfl⟩
        exact Finset.card_pos.mpr ⟨_, this⟩
      have hi1 := hin1 v
      rcases Nat.lt_or_ge (inn v) 1 with hlt | hge
      · have hi0 : inn v = 0 := by omega
        rw [hi0]
        by_cases hc3 : cnt D idx v 2 = 3
        · have := F2 (by omega) hc3
          omega
        · omega
      · have hi1' : inn v = 1 := by omega
        obtain ⟨hm3, hsm⟩ := F1 hi1'
        by_cases hc1 : cnt D idx v 2 = 1
        · have := hsm (by omega) hc1
          omega
        · omega
    · have hi0 := hin0poly k
      rw [← hk] at hi0
      rw [hi0, hc2]
      omega
  have hv0 : ∃ j k, (D.tile j).pts k = P.v (0 + 1) := poly_vertex_is_tile_vertex D.toRegionDissection P hreg (0 + 1)
  have hvV : P.v (0 + 1) ∈ V := mem_vtxSet.mpr hv0
  have hcA := corner_A D P hreg idx hidxA 0 hv0
  have hcnt2 : cnt D idx (P.v (0 + 1)) 2 = 0 := hcorn 0
  have hApos := Asum_pos D idx hv0
  have hin0 := hin0poly 0
  have hc01 : 1 ≤ cnt D idx (P.v (0 + 1)) 0 + cnt D idx (P.v (0 + 1)) 1 := by
    by_contra hlt
    have h0 : cnt D idx (P.v (0 + 1)) 0 = 0 := by omega
    have h1 : cnt D idx (P.v (0 + 1)) 1 = 0 := by omega
    have hAexp : Asum D idx (P.v (0 + 1)) = (cnt D idx (P.v (0 + 1)) 0 : ℝ) * D.model.angleAt 0 + (cnt D idx (P.v (0 + 1)) 1 : ℝ) * D.model.angleAt 1 + (cnt D idx (P.v (0 + 1)) 2 : ℝ) * D.model.angleAt 2 := by
      unfold Asum; rw [Fin.sum_univ_three]
    rw [hAexp, h0, h1, hcnt2] at hApos
    simp at hApos
  have hf0 : 1 ≤ 6 * (out (P.v (0 + 1)) : ℤ) - 6 * (inn (P.v (0 + 1)) : ℤ) + (cnt D idx (P.v (0 + 1)) 0 : ℤ) + (cnt D idx (P.v (0 + 1)) 1 : ℤ) - 2 * (cnt D idx (P.v (0 + 1)) 2 : ℤ) := by
    rw [hin0, hcnt2]
    push_cast
    omega
  have hsum0 : ∑ v ∈ V, (6 * (out v : ℤ) - 6 * (inn v : ℤ) + (cnt D idx v 0 : ℤ) + (cnt D idx v 1 : ℤ) - 2 * (cnt D idx v 2 : ℤ)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      hbal, hs0, hs1, hs2]
    ring
  have hle := Finset.single_le_sum (f := fun v => 6 * (out v : ℤ) - 6 * (inn v : ℤ) + (cnt D idx v 0 : ℤ) + (cnt D idx v 1 : ℤ) - 2 * (cnt D idx v 2 : ℤ)) hf hvV
  try simp only at hle
  rw [hsum0] at hle
  omega
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
theorem corner_split_core {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (θ : Fin 3 → ℝ) (c : Fin 3 → Fin 3 → ℕ)
    (ang : Fin 3 → ℝ) (h0 : ang 0 = α) (h1 : ang 1 = Real.pi / 3 - α) (h2 : ang 2 = 2 * Real.pi / 3)
    (hθ : ∀ k, θ k = ∑ l, (c k l : ℝ) * ang l) (hsum : θ 0 + θ 1 + θ 2 = Real.pi) (hpos : ∀ k, 0 < θ k)
    (k0 : Fin 3) (hk0 : 1 ≤ c k0 2) : ∃ ρ : Equiv.Perm (Fin 3), ∀ k, θ k = ang (ρ k) := by
  have hpi := Real.pi_pos
  simp only [Fin.sum_univ_three] at hθ
  have hs' : ∀ t0 t1 t2 : ℕ, (t0 : ℝ) * α + (t1 : ℝ) * (Real.pi / 3 - α) + (t2 : ℝ) * (2 * Real.pi / 3) = Real.pi → t0 = t1 ∧ t1 + 2 * t2 = 3 := by
    intro t0 t1 t2 h
    have := irr_coeff hα ((t0 : ℤ) - t1) (3 - (t1 : ℤ) - 2 * t2) (by push_cast; linear_combination h)
    omega
  have key := hs' (c 0 0 + c 1 0 + c 2 0) (c 0 1 + c 1 1 + c 2 1) (c 0 2 + c 1 2 + c 2 2)
    (by
      have hh := hsum
      rw [hθ 0, hθ 1, hθ 2, h0, h1, h2] at hh
      push_cast
      linear_combination hh)
  have fin3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have hT2 : 1 ≤ c 0 2 + c 1 2 + c 2 2 := by
    rcases fin3 k0 with rfl | rfl | rfl <;> omega
  have hT0 : c 0 0 + c 1 0 + c 2 0 = 1 := by omega
  have hT1 : c 0 1 + c 1 1 + c 2 1 = 1 := by omega
  have hT2' : c 0 2 + c 1 2 + c 2 2 = 1 := by omega
  have hone : ∀ k, c k 0 + c k 1 + c k 2 ≥ 1 := by
    intro k
    by_contra hlt
    have e0 : c k 0 = 0 := by omega
    have e1 : c k 1 = 0 := by omega
    have e2 : c k 2 = 0 := by omega
    have hk := hθ k
    rw [e0, e1, e2] at hk
    simp at hk
    linarith [hpos k]
  have hone0 := hone 0
  have hone1 := hone 1
  have hone2 := hone 2
  have hs0 : c 0 0 + c 0 1 + c 0 2 = 1 := by omega
  have hs1 : c 1 0 + c 1 1 + c 1 2 = 1 := by omega
  have hs2 : c 2 0 + c 2 1 + c 2 2 = 1 := by omega
  let f : Fin 3 → Fin 3 := fun k => if c k 0 = 1 then 0 else if c k 1 = 1 then 1 else 2
  have hrow : ∀ k, c k 0 + c k 1 + c k 2 = 1 := by
    intro k
    match k with
    | 0 => exact hs0
    | 1 => exact hs1
    | 2 => exact hs2
  have hθf : ∀ k, θ k = ang (f k) := by
    intro k
    have hr := hrow k
    rw [hθ k]
    simp only [f]
    by_cases a0 : c k 0 = 1
    · have : c k 1 = 0 := by omega
      have : c k 2 = 0 := by omega
      simp [a0, *]
    · by_cases a1 : c k 1 = 1
      · have : c k 0 = 0 := by omega
        have : c k 2 = 0 := by omega
        simp [a1, *]
      · have : c k 2 = 1 := by omega
        have : c k 0 = 0 := by omega
        have : c k 1 = 0 := by omega
        simp [*]
  have inj : Function.Injective f := by
    intro k k' h
    by_contra hne
    have r0 := hrow 0
    have r1 := hrow 1
    have r2 := hrow 2
    rcases fin3 k with rfl | rfl | rfl <;> rcases fin3 k' with rfl | rfl | rfl <;>
      first | exact hne rfl | (simp only [f] at h; split_ifs at h <;> omega)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp inj), fun k => ?_⟩
  simpa using hθf k
def NotSim {N : ℕ} (D : CongruentDissection N) : Prop :=
  ¬ ∃ ρ : Equiv.Perm (Fin 3), ∀ j, D.target.angleAt j = D.model.angleAt (ρ j)
theorem corner_gamma_zero {N : ℕ} (Dr : CongruentRegionDissection N) [HasFansC Dr.toRegionDissection] (P : ConvPoly 3) (hreg : Dr.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hidxA : ∀ i v, Dr.model.angleAt (idx i v) = (Dr.tile i).angleAt v) {α : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h0 : Dr.model.angleAt 0 = α) (h1 : Dr.model.angleAt 1 = Real.pi / 3 - α)
    (h2 : Dr.model.angleAt 2 = 2 * Real.pi / 3) (hsum : P.angle 0 + P.angle 1 + P.angle 2 = Real.pi) (hpos : ∀ i, 0 < P.angle i)
    (hNS : ¬ ∃ ρ : Equiv.Perm (Fin 3), ∀ k : Fin 3, P.angle (k + 1) = Dr.model.angleAt (ρ k)) :
    ∀ k : Fin 3, cnt Dr idx (P.v (k + 1)) 2 = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨k0, hk0⟩ := hne
  have hcA : ∀ k : Fin 3, P.angle (k + 1) = ∑ l, (cnt Dr idx (P.v (k + 1)) l : ℝ) * Dr.model.angleAt l := by
    intro k
    have hv : ∃ j k', (Dr.tile j).pts k' = P.v (k + 1) := poly_vertex_is_tile_vertex Dr.toRegionDissection P hreg (k + 1)
    exact (corner_A Dr P hreg idx hidxA k hv).symm.trans rfl
  have hsum' : P.angle (0 + 1) + P.angle (1 + 1) + P.angle (2 + 1) = Real.pi := by
    have e1 : (0 : Fin 3) + 1 = 1 := by decide
    have e2 : (1 : Fin 3) + 1 = 2 := by decide
    have e3 : (2 : Fin 3) + 1 = 0 := by decide
    rw [e1, e2, e3]; linarith
  obtain ⟨ρ, hρ⟩ := corner_split_core hα (fun k => P.angle (k + 1)) (fun k l => cnt Dr idx (P.v (k + 1)) l) Dr.model.angleAt h0 h1 h2
    hcA hsum' (fun k => hpos _) k0 (Nat.one_le_iff_ne_zero.mpr hk0)
  exact hNS ⟨ρ, hρ⟩
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
theorem tri_setup (D : CongruentDissection N) {α a b c : ℝ} (h : D.model.TwoPiThreeData α a b c) {R : Prop}
    (k : ∀ (Dr : CongruentRegionDissection N) [HasFansC Dr.toRegionDissection] (P : ConvPoly 3) (hreg : Dr.region = P.carrier)
      (idx : Fin N → Equiv.Perm (Fin 3))
      (hidx : ∀ i k k', dist ((Dr.tile i).pts k) ((Dr.tile i).pts k') = dist (Dr.model.pts (idx i k)) (Dr.model.pts (idx i k')))
      (hidxA : ∀ i v, Dr.model.angleAt (idx i v) = (Dr.tile i).angleAt v),
      slen Dr 0 = a → slen Dr 1 = b → slen Dr 2 = c →
      Dr.model.angleAt 0 = α → Dr.model.angleAt 1 = Real.pi / 3 - α → Dr.model.angleAt 2 = 2 * Real.pi / 3 →
      P.angle 0 + P.angle 1 + P.angle 2 = Real.pi → (∀ i, 0 < P.angle i) → (∀ i, P.angle i < Real.pi) →
      (NotSim D → ¬ ∃ ρ : Equiv.Perm (Fin 3), ∀ k : Fin 3, P.angle (k + 1) = Dr.model.angleAt (ρ k)) → R) : R := by
  obtain ⟨P, hPc, τ, hτ⟩ := exists_convpoly_of_tri D.target
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  set Dr := relabel D.toRegion σ with hDr
  have hreg : Dr.region = P.carrier := by rw [hPc]; rfl
  haveI : HasFansC Dr.toRegionDissection := hasFansC_poly _ P hreg
  obtain ⟨idx, hidx, hidxA⟩ := exists_idx_both Dr
  have hang : ∀ j, Dr.model.angleAt j = D.model.angleAt (σ j) := fun j => relabel_angleAt D.toRegion σ j
  have hsl : ∀ t, slen Dr t = D.model.oppLen (σ t) := fun t => relabel_slen D.toRegion σ t
  have hs : D.target.angleAt 0 + D.target.angleAt 1 + D.target.angleAt 2 = Real.pi := angleAt_sum D.target
  have hp : ∀ j, 0 < D.target.angleAt j := fun j => D.target.angleAt_pos'' j
  have hPsum : P.angle 0 + P.angle 1 + P.angle 2 = Real.pi := by
    simp only [hτ]
    have : ∑ i : Fin 3, D.target.angleAt (τ i) = ∑ i : Fin 3, D.target.angleAt i := Equiv.sum_comp τ (fun i => D.target.angleAt i)
    simp only [Fin.sum_univ_three] at this
    linarith
  refine k Dr P hreg idx hidx hidxA (by rw [hsl]; exact o0) (by rw [hsl]; exact o1) (by rw [hsl]; exact o2)
    (by rw [hang]; exact h0) (by rw [hang]; exact h1) (by rw [hang]; exact h2) hPsum (fun i => by rw [hτ]; exact hp _) (fun i => ?_) ?_
  · rw [hτ]
    have := hp (τ i)
    have e : ∀ j : Fin 3, D.target.angleAt j < Real.pi := by
      intro j
      have fin3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
      rcases fin3 j with rfl | rfl | rfl <;> linarith [hp 0, hp 1, hp 2]
    exact e _
  · intro hNS ⟨ρ, hρ⟩
    apply hNS
    refine ⟨τ.symm.trans ((Equiv.addRight (-1 : Fin 3)).trans (ρ.trans σ)), fun j => ?_⟩
    obtain ⟨m, rfl⟩ := τ.surjective j
    have := hρ (m - 1)
    rw [hτ, hang] at this
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.coe_addRight]
    have e : m - 1 + 1 = m := by simp
    rw [e] at this
    rw [show m + -1 = m - 1 from by simp [sub_eq_add_neg]]
    exact this
theorem bz_lemma35_notsim (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (hNS : NotSim D) : ¬ NotComb a b c := by
  intro hnc
  refine tri_setup D h ?_
  intro Dr _ P hreg idx hidx hidxA e0 e1 e2 hA0 hA1 hA2 hsum hpos hlt hns
  refine bz_lemma35_gen2 Dr P hreg idx hidx hidxA ?_ hA2 (by rw [hA0, hA1]; ring) (by rw [hA0]; exact hα) hlt
    (corner_gamma_zero Dr P hreg idx hidxA hα hA0 hA1 hA2 hsum hpos (hns hNS))
  rw [e0, e1, e2]; exact hnc
theorem bz_ab_comm_notsim (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (hNS : NotSim D) : Comm a b := by
  have h1 := bz_lemma35_notsim D hα h hNS
  have hα' : ¬ ∃ r : ℚ, Real.pi / 3 - α = (r : ℝ) * Real.pi := by
    rintro ⟨r, hr⟩
    apply hα
    refine ⟨1 / 3 - r, ?_⟩
    push_cast
    linarith
  have h2 := bz_lemma35_notsim D hα' (tpt_swap h) hNS
  unfold NotComb at h1 h2
  push Not at h1 h2
  obtain ⟨r, p, q, hr, e1⟩ := h1
  obtain ⟨r', p', q', hr', e2⟩ := h2
  have ha : 0 < a := by
    obtain ⟨σ, -, o0, -⟩ := h
    rw [← o0]; exact D.model.oppLen_pos' _
  have hb : 0 < b := by
    obtain ⟨σ, -, -, -, o1, -⟩ := h
    rw [← o1]; exact D.model.oppLen_pos' _
  exact comm_of_two_combs ha hb hr e1 hr' e2
end Erdos634.Draft.LaczFormal.RG
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal.RG
variable {N : ℕ}
def _root_.OMACut_ALLC : Prop := ∀ {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ},
    (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) → D.model.TwoPiThreeData α a b c → NotSim D → Comm a b →
      ¬ Comm a c → False
theorem bz_allc_false [hcut : Fact OMACut_ALLC] (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c) (hNS : NotSim D)
    (hab : Comm a b) (hac : ¬ Comm a c) : False := hcut.out D hα h hNS hab hac
theorem bz_thm11 [Fact OMACut_ALLC] (D : CongruentDissection N) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : D.model.TwoPiThreeData α a b c) (hNS : NotSim D) : Comm a b ∧ Comm a c := by
  have hab := bz_ab_comm_notsim D hα h hNS
  refine ⟨hab, ?_⟩
  by_contra hac
  exact bz_allc_false D hα h hNS hab hac
end Erdos634.Draft.LaczFormal.RG
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

end OMA.E634H


namespace OMA.E634S

open Erdos634.Geometry

/-- The Mathlib triangle with the vertices of a Bonfioli triangle. -/
def toS (t : Tri) : Tr := ⟨t.pts, t.indep⟩

theorem toS_ci (t : Tri) : (toS t).closedInterior = t.carrier := (carrier_ofS (toS t)).symm

/-- The congruent dissection built from cut data with an arbitrary model triangle M. -/
noncomputable def mkM {p : ℕ} (T M : Tr) (Ts : Fin p → Tr)
    (hc : ∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)),
      ∀ k, f ((Ts i).points k) = M.points (σ k))
    (hd : Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)))
    (hu : ⋃ i, (Ts i).closedInterior = T.closedInterior) : CongruentDissection p :=
  { target := ofS T
    tile := fun i => ofS (Ts i)
    covers := by simp only [carrier_ofS]; exact hu
    interiors_disjoint := fun i j hij => by simpa only [carrier_ofS] using hd hij
    model := ofS M
    tiles_congruent := hc }

theorem toS_hc {N : ℕ} (D : CongruentDissection N) : ∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ
    EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)),
      ∀ k, f ((toS (D.tile i)).points k) = (toS D.model).points (σ k) := D.tiles_congruent

theorem toS_hd {N : ℕ} (D : CongruentDissection N) : Pairwise (fun i j =>
    Disjoint (interior (toS (D.tile i)).closedInterior) (interior (toS (D.tile j)).closedInterior)) :=
  fun i j hij => by simpa only [toS_ci] using D.interiors_disjoint hij

theorem toS_hu {N : ℕ} (D : CongruentDissection N) :
    ⋃ i, (toS (D.tile i)).closedInterior = (toS D.target).closedInterior := by
  simp only [toS_ci]; exact D.covers

end OMA.E634S

theorem OMA.E634S.cutALLC_of (h : ∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * b) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c)) : OMACut_ALLC := by
  intro N D α a b c hα hdata hNS hab hac
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := hdata
  exact hac (h N (OMA.E634S.toS D.target) (OMA.E634S.toS D.model) (fun i => OMA.E634S.toS (D.tile i))
    (OMA.E634S.toS_hc D) (OMA.E634S.toS_hd D) (OMA.E634S.toS_hu D) _ _ _ (fun k => rfl) (fun k => rfl)
    (fun k => rfl) α a b c hα ⟨σ, OMA.E634H.comp_vec h0 h1 h2, OMA.E634H.comp_vec o0 o1 o2⟩ (fun ⟨ρ, hρ⟩ => hNS ⟨ρ, fun j => congrFun hρ j⟩) hab)

/-- Beeson-Zhang Theorem 1.1 (the sides of the tile are commensurable), given Theorem 3.7 (H1). -/
theorem OMA.solution : OMA.R_erdos_634_R1_H4_R1_H2_R1_H1_R1.H2 := by
  intro hALLC p T M Ts hc hd hu A B L hA hB hL α a b c hα hdata hns
  obtain rfl : A = _ := funext hA
  obtain rfl : B = _ := funext hB
  obtain rfl : L = _ := funext hL
  let D := OMA.E634S.mkM T M Ts hc hd hu
  obtain ⟨σ, hσ1, hσ2⟩ := hdata
  obtain ⟨h0, h1, h2⟩ := OMA.E634H.vec_comp hσ1
  obtain ⟨o0, o1, o2⟩ := OMA.E634H.vec_comp hσ2
  have hD : D.model.TwoPiThreeData α a b c := ⟨σ, h0, o0, h1, o1, h2, o2⟩
  have hNS : Erdos634.Draft.LaczFormal.RG.NotSim D := fun ⟨ρ, hρ⟩ => hns ⟨ρ, funext hρ⟩
  haveI : Fact OMACut_ALLC := ⟨OMA.E634S.cutALLC_of hALLC⟩
  exact Erdos634.Draft.LaczFormal.RG.bz_thm11 D hα hD hNS

