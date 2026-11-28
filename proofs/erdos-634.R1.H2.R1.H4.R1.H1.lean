import OMAReductions.R_erdos_634_R1_H2_R1_H4_R1

/-!
# Step H1 of the reduction erdos-634.R1.H2.R1.H4.R1 (Equilateral T, 4 exceptional rational tiles)

Proves that for prime p > 3, an equilateral triangle T cannot be p-tiled by any of the four
exceptional rational tiles:
1. (pi/6, pi/6, 2pi/3)
2. (pi/12, pi/3, 7pi/12)
3. (pi/30, pi/3, 19pi/30)
4. (7pi/30, pi/3, 13pi/30)

Method:
* Reuses basic dissection geometry (`Dissection.side_walk_abc`, `CongruentArea`, `AreaDet`,
  `SssCongruent`) from the Bonfioli / Beeson-Rosu formalization (MIT / Apache-2.0, as in
  `proofs/erdos-634.R1.H2.R1.H2.R1.H3.lean`).
* Combines side-length decomposition (`side_walk_abc`) with area additivity (`|T.det| = p |M.det|`)
  and an elementary biquadratic elimination lemma over Q and Q(sqrt 5).
-/

section
namespace Erdos634.SupportFace
open Finset
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem mem_convexHull_max (f : E →ₗ[ℝ] ℝ) (c : ℝ) (s : Finset E)
    (hle : ∀ v ∈ s, f v ≤ c) {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) (hfx : f x = c) :
    x ∈ convexHull ℝ ((s.filter (fun v => f v = c) : Finset E) : Set E) := by
  classical
  rw [Finset.convexHull_eq] at hx
  obtain ⟨w, hw0, hw1, hcm⟩ := hx
  have hcomb : ∑ v ∈ s, w v • v = x := by
    rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]; rfl
  have hdef : ∑ v ∈ s, w v * (c - f v) = 0 := by
    have hfsum : ∑ v ∈ s, w v * f v = c := by
      have : f (∑ v ∈ s, w v • v) = ∑ v ∈ s, w v * f v := by
        rw [map_sum]; simp [map_smul, smul_eq_mul]
      rw [hcomb] at this; rw [← this, hfx]
    calc ∑ v ∈ s, w v * (c - f v)
        = (∑ v ∈ s, w v) * c - ∑ v ∈ s, w v * f v := by
          rw [Finset.sum_mul]; rw [← Finset.sum_sub_distrib]; ring_nf
          exact Finset.sum_congr rfl (fun v _ => by ring)
      _ = 0 := by rw [hw1, hfsum]; ring
  have hterm : ∀ v ∈ s, w v * (c - f v) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hdef
    intro v hv
    exact mul_nonneg (hw0 v hv) (by linarith [hle v hv])
  have hsupp : ∀ v ∈ s, w v ≠ 0 → f v = c := by
    intro v hv hne
    rcases mul_eq_zero.mp (hterm v hv) with h | h
    · exact absurd h hne
    · linarith
  have hzero : ∀ v ∈ s, v ∉ s.filter (fun v => f v = c) → w v = 0 := by
    intro v hv hnot
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hv, hsupp v hv hne⟩)
  have hsub : s.filter (fun v => f v = c) ⊆ s := Finset.filter_subset _ _
  have hsum1 : ∑ v ∈ s.filter (fun v => f v = c), w v = 1 := by
    rw [Finset.sum_subset hsub hzero]; exact hw1
  rw [Finset.convexHull_eq]
  refine ⟨w, ?_, hsum1, ?_⟩
  · intro v hv; exact hw0 v (Finset.mem_filter.mp hv).1
  · rw [Finset.centerMass_eq_of_sum_1 _ _ hsum1]
    have : ∑ v ∈ s.filter (fun v => f v = c), w v • id v = ∑ v ∈ s, w v • v := by
      refine Finset.sum_subset hsub ?_
      intro v hv hnot; simp [hzero v hv hnot]
    rw [this]; exact hcomb
theorem contact_eq_face (f : E →ₗ[ℝ] ℝ) (c : ℝ) (s : Finset E)
    (hle : ∀ v ∈ s, f v ≤ c) :
    {x ∈ convexHull ℝ (s : Set E) | f x = c}
      = convexHull ℝ ((s.filter (fun v => f v = c) : Finset E) : Set E) := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    exact mem_convexHull_max f c s hle hx hfx
  · intro hx
    have hsub : ((s.filter (fun v => f v = c) : Finset E) : Set E) ⊆ (s : Set E) := by
      intro v hv; exact (Finset.mem_filter.mp hv).1
    refine ⟨convexHull_mono hsub hx, ?_⟩
    have : convexHull ℝ ((s.filter (fun v => f v = c) : Finset E) : Set E) ⊆ {y | f y = c} := by
      refine convexHull_min ?_ ?_
      · intro v hv; exact (Finset.mem_filter.mp hv).2
      · intro a ha b hb ta tb hta htb htab
        simp only [Set.mem_setOf_eq] at *
        rw [map_add, map_smul, map_smul, ha, hb, smul_eq_mul, smul_eq_mul]
        linear_combination c * htab
    exact this hx
end Erdos634.SupportFace
end

section
namespace Erdos634.SegmentDense
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private noncomputable def par (x b : E) (t : ℝ) : E := (1 - t) • x + t • b
private theorem par_mem_segment {x b : E} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    par x b t ∈ segment ℝ x b := by
  rw [segment_eq_image]
  exact ⟨t, ht, rfl⟩
private theorem par_dist {x b : E} (t : ℝ) : ‖par x b t - x‖ = |t| * ‖b - x‖ := by
  have : par x b t - x = t • (b - x) := by
    simp only [par, smul_sub, sub_smul, one_smul]; abel
  rw [this, norm_smul, Real.norm_eq_abs]
private theorem par_injOn {x b : E} (hxb : x ≠ b) : Function.Injective (par x b) := by
  intro s t hst
  have h : (s - t) • (b - x) = 0 := by
    have : par x b s - par x b t = (s - t) • (b - x) := by
      simp only [par, smul_sub, sub_smul, one_smul]; abel
    rw [← this, hst, sub_self]
  rcases smul_eq_zero.mp h with h1 | h2
  · linarith [sub_eq_zero.mp (by linarith [h1] : s - t = 0)]
  · exact absurd (sub_eq_zero.mp h2).symm hxb
theorem subset_closure_diff_finite {a b : E} (hab : a ≠ b) {F : Set E} (hF : F.Finite) :
    segment ℝ a b ⊆ closure (segment ℝ a b \ F) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp, hxp⟩ : ∃ p, p ∈ ({a, b} : Set E) ∧ x ≠ p := by
    by_cases h : x = a
    · exact ⟨b, by simp, by rw [h]; exact hab⟩
    · exact ⟨a, by simp, h⟩
  have hpmem : p ∈ segment ℝ a b := by
    rcases hp with h | h
    · rw [h]; exact left_mem_segment ℝ a b
    · rw [h]; exact right_mem_segment ℝ a b
  have hseg : segment ℝ x p ⊆ segment ℝ a b :=
    (convex_segment a b).segment_subset hx hpmem
  have hnorm : 0 < ‖p - x‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (Ne.symm hxp)
  set δ : ℝ := min 1 (ε / (2 * ‖p - x‖)) with hδdef
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hinf : (Set.Ioo (0:ℝ) δ).Infinite := Set.Ioo_infinite hδ
  have himg : ((par x p) '' Set.Ioo (0:ℝ) δ).Infinite :=
    hinf.image ((par_injOn hxp).injOn)
  obtain ⟨y, hy, hyF⟩ := (himg.diff hF).nonempty
  obtain ⟨t, ht, rfl⟩ := hy
  refine ⟨par x p t, ⟨hseg (par_mem_segment ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) (min_le_left _ _)⟩), hyF⟩, ?_⟩
  rw [dist_comm, dist_eq_norm, par_dist, abs_of_pos ht.1]
  have h1 : t < ε / (2 * ‖p - x‖) := lt_of_lt_of_le ht.2 (min_le_right _ _)
  calc t * ‖p - x‖ < (ε / (2 * ‖p - x‖)) * ‖p - x‖ := by
        exact mul_lt_mul_of_pos_right h1 hnorm
    _ = ε / 2 := by field_simp
    _ < ε := by linarith
end Erdos634.SegmentDense
end

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
theorem volume_ne_top (T : Tri) : volume T.carrier ≠ ⊤ := T.isCompact.measure_lt_top.ne
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
theorem pos (D : Dissection N) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    have hz := D.volume_target
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hz
    exact absurd hz D.target.volume_pos.ne'
  · exact h
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
def HasEdgeChains {N : ℕ} (D : Dissection N) (edgeOf : Fin N → Fin 3 → Set Plane) : Prop :=
  ∀ i : Fin 3, ∃ (part : Finset (Fin N × Fin 3)),
    (⋃ e ∈ part, edgeOf e.1 e.2) = segment ℝ (D.target.pts i) (D.target.pts (i + 1))
def Tri.edge (T : Tri) (i : Fin 3) : Set Plane := segment ℝ (T.pts i) (T.pts (i + 1))
theorem tile_contact_face (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hle : ∀ x ∈ T.carrier, f x ≤ c) :
    {x ∈ T.carrier | f x = c}
      = convexHull ℝ (((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane) :
          Set Plane) := by
  classical
  have hmem : ∀ v ∈ (Finset.univ.image T.pts), f v ≤ c := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact hle _ (subset_convexHull ℝ _ ⟨i, rfl⟩)
  have hcar : T.carrier = convexHull ℝ ((Finset.univ.image T.pts : Finset Plane) : Set Plane) := by
    rw [Tri.carrier]; congr 1
    ext x; constructor
    · rintro ⟨i, rfl⟩; exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact ⟨i, rfl⟩
  rw [hcar]
  exact Erdos634.SupportFace.contact_eq_face f c _ hmem
theorem two_vertices_on_line (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hall : ∀ i, f (T.pts i) = c) : False := by
  have hsub : T.carrier ⊆ {x | f x = c} := by
    rw [Tri.carrier]
    refine convexHull_min ?_ ?_
    · rintro x ⟨i, rfl⟩; exact hall i
    · intro a ha b hb ta tb hta htb htab
      simp only [Set.mem_setOf_eq] at *
      rw [map_add, map_smul, map_smul, ha, hb, smul_eq_mul, smul_eq_mul]
      linear_combination c * htab
  obtain ⟨x, hx⟩ := T.interior_nonempty
  have hxc : f x = c := hsub (interior_subset hx)
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext fun z => by simp [h z])
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  set t : ℝ := ε / (2 * ‖y‖) with ht
  have hynorm : 0 < ‖y‖ := by
    rcases eq_or_ne y 0 with rfl | hy0
    · simp at hy
    · exact norm_pos_iff.mpr hy0
  have htpos : 0 < t := by positivity
  have hdist : dist (x + t • y) x = t * ‖y‖ := by
    rw [dist_eq_norm]
    have hxy : x + t • y - x = t • y := by abel
    rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  have hmemball : x + t • y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, hdist]
    have hhalf : t * ‖y‖ = ε / 2 := by rw [ht]; field_simp
    rw [hhalf]; linarith
  have : f (x + t • y) = c := hsub (interior_subset (hball hmemball))
  rw [map_add, map_smul, hxc, smul_eq_mul] at this
  have : t * f y = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (ne_of_gt htpos)
  · exact hy h
theorem tile_subset_target (D : Dissection N) (j : Fin N) :
    (D.tile j).carrier ⊆ D.target.carrier := by
  rw [← D.covers]; exact Set.subset_iUnion (fun i => (D.tile i).carrier) j
theorem Tri.isClosed_edge (T : Tri) (k : Fin 3) : IsClosed (T.edge k) := by
  have hc : IsCompact (T.edge k) := by
    rw [Tri.edge, segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  exact hc.isClosed
theorem Tri.pair_eq_edge (T : Tri) {p q : Fin 3} (hpq : p ≠ q) :
    ∃ k, segment ℝ (T.pts p) (T.pts q) = T.edge k := by
  simp only [Tri.edge]
  fin_cases p <;> fin_cases q <;> simp_all <;>
    [ exact ⟨0, rfl⟩;
      exact ⟨2, segment_symm ℝ _ _⟩;
      exact ⟨0, segment_symm ℝ _ _⟩;
      exact ⟨1, rfl⟩;
      exact ⟨2, rfl⟩;
      exact ⟨1, segment_symm ℝ _ _⟩ ]
noncomputable def Tri.basis (T : Tri) : AffineBasis (Fin 3) ℝ Plane :=
  AffineBasis.mk T.pts T.indep (by
    have := T.affineSpan_eq_top
    rwa [Tri.carrier, affineSpan_convexHull] at this)
theorem exists_supporting (T : Tri) (i : Fin 3) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ (∀ x ∈ T.carrier, f x ≤ c) ∧
      f (T.pts i) = c ∧ f (T.pts (i + 1)) = c ∧ f (T.pts (i + 2)) < c := by
  classical
  set g : Plane →ᵃ[ℝ] ℝ := T.basis.coord (i + 2) with hg
  have hdecomp : ∀ x, g x = g.linear x + g 0 := by
    intro x; simpa using congrFun (AffineMap.decomp g) x
  have hb : ∀ j, g (T.pts j) = if i + 2 = j then 1 else 0 := by
    intro j; exact AffineBasis.coord_apply T.basis (i + 2) j
  have hne1 : i + 2 ≠ i := by fin_cases i <;> decide
  have hne2 : i + 2 ≠ i + 1 := by fin_cases i <;> decide
  have h0 : g (T.pts i) = 0 := by rw [hb]; simp [hne1]
  have h1 : g (T.pts (i + 1)) = 0 := by rw [hb]; simp [hne2]
  have h2 : g (T.pts (i + 2)) = 1 := by rw [hb]; simp
  have hnonneg : ∀ j, (0:ℝ) ≤ g (T.pts j) := by
    intro j; rw [hb]; split <;> norm_num
  refine ⟨-g.linear, g 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have hlin0 : g.linear = 0 := by
      have := congrArg Neg.neg hzero; simpa using this
    have ha := hdecomp (T.pts i)
    have hc := hdecomp (T.pts (i + 2))
    rw [hlin0] at ha hc
    simp only [LinearMap.zero_apply, zero_add] at ha hc
    rw [h0] at ha; rw [h2] at hc
    linarith
  · intro x hx
    rw [Tri.carrier] at hx
    show x ∈ {y : Plane | (-g.linear) y ≤ g 0}
    refine convexHull_min ?_ ?_ hx
    · rintro y ⟨j, rfl⟩
      simp only [Set.mem_setOf_eq, LinearMap.neg_apply]
      linarith [hdecomp (T.pts j), hnonneg j]
    · intro a ha b hb ta tb hta htb htab
      simp only [Set.mem_setOf_eq, LinearMap.neg_apply] at ha hb ⊢
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have key : -(ta * g.linear a + tb * g.linear b)
               = ta * (-g.linear a) + tb * (-g.linear b) := by ring
      rw [key]
      calc ta * (-g.linear a) + tb * (-g.linear b)
          ≤ ta * g 0 + tb * g 0 :=
            add_le_add (mul_le_mul_of_nonneg_left ha hta) (mul_le_mul_of_nonneg_left hb htb)
        _ = g 0 := by rw [← add_mul, htab, one_mul]
  · simp only [LinearMap.neg_apply]; linarith [hdecomp (T.pts i), h0]
  · simp only [LinearMap.neg_apply]; linarith [hdecomp (T.pts (i + 1)), h1]
  · simp only [LinearMap.neg_apply]; linarith [hdecomp (T.pts (i + 2)), h2]
theorem contact_is_edge (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle : ∀ x ∈ T.carrier, f x ≤ c) {x : Plane} (hx : x ∈ T.carrier) (hfx : f x = c)
    (hxv : ∀ k, x ≠ T.pts k) :
    ∃ k, {y ∈ T.carrier | f y = c} = T.edge k := by
  classical
  set V : Finset (Fin 3) := Finset.univ.filter (fun k => f (T.pts k) = c) with hV
  have himg : (((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane) : Set Plane)
            = T.pts '' (V : Set (Fin 3)) := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hv
      obtain ⟨⟨k, _, hk⟩, hfv⟩ := hv
      refine ⟨k, ?_, hk⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter]
      exact ⟨Finset.mem_univ k, by rw [hk]; exact hfv⟩
    · rintro ⟨k, hkV, rfl⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter] at hkV
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨k, Finset.mem_univ k, rfl⟩, hkV.2⟩
  have hcontact : {y ∈ T.carrier | f y = c} = convexHull ℝ (T.pts '' (V : Set (Fin 3))) := by
    rw [tile_contact_face T f c hle, himg]
  have hxc : x ∈ convexHull ℝ (T.pts '' (V : Set (Fin 3))) := by
    rw [← hcontact]; exact ⟨hx, hfx⟩
  have hcard3 : V.card ≤ 3 := by
    have := Finset.card_le_card (Finset.subset_univ V)
    simpa using this
  interval_cases h : V.card
  · 
    rw [Finset.card_eq_zero] at h
    rw [h] at hxc; simp at hxc
  · 
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
    rw [hk] at hxc
    simp only [Finset.coe_singleton, Set.image_singleton, convexHull_singleton,
      Set.mem_singleton_iff] at hxc
    exact absurd hxc (hxv k)
  · 
    obtain ⟨p, q, hpq, hV2⟩ := Finset.card_eq_two.mp h
    obtain ⟨k, hk⟩ := T.pair_eq_edge hpq
    refine ⟨k, ?_⟩
    rw [hcontact, hV2]
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
    rw [convexHull_pair, hk]
  · 
    exfalso
    have hall : ∀ k, f (T.pts k) = c := by
      intro k
      have hmem : k ∈ V := by
        have : V = Finset.univ := Finset.eq_univ_of_card V (by simpa using h)
        rw [this]; exact Finset.mem_univ k
      simpa [hV, Finset.mem_filter] using hmem
    exact two_vertices_on_line T f c hf hall
theorem target_contact_side (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {i : Fin 3}
    (hle : ∀ x ∈ T.carrier, f x ≤ c) (hi : f (T.pts i) = c) (hi1 : f (T.pts (i + 1)) = c)
    (hi2 : f (T.pts (i + 2)) < c) :
    {x ∈ T.carrier | f x = c} = segment ℝ (T.pts i) (T.pts (i + 1)) := by
  classical
  set V : Finset (Fin 3) := Finset.univ.filter (fun k => f (T.pts k) = c) with hV
  have hexh : ∀ k : Fin 3, k = i ∨ k = i + 1 ∨ k = i + 2 := by
    intro k; fin_cases i <;> fin_cases k <;> decide
  have hVeq : V = {i, i + 1} := by
    apply Finset.Subset.antisymm
    · intro k hk
      rw [hV, Finset.mem_filter] at hk
      rcases hexh k with rfl | rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exact absurd hk.2 (by linarith)
    · intro k hk
      rw [hV, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | hk'
      · exact hi
      · rw [Finset.mem_singleton.mp hk']; exact hi1
  have himg : (((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane) : Set Plane)
            = T.pts '' (V : Set (Fin 3)) := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hv
      obtain ⟨⟨k, _, hk⟩, hfv⟩ := hv
      refine ⟨k, ?_, hk⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter]
      exact ⟨Finset.mem_univ k, by rw [hk]; exact hfv⟩
    · rintro ⟨k, hkV, rfl⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter] at hkV
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨k, Finset.mem_univ k, rfl⟩, hkV.2⟩
  rw [tile_contact_face T f c hle, himg, hVeq]
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
  rw [convexHull_pair]
theorem hasEdgeChains_edge (D : Dissection N) :
    HasEdgeChains D (fun j k => (D.tile j).edge k) := by
  classical
  intro i
  obtain ⟨f, c, hf, hle, hi, hi1, hi2⟩ := exists_supporting D.target i
  set S : Set Plane := segment ℝ (D.target.pts i) (D.target.pts (i + 1)) with hSdef
  have hS : {x ∈ D.target.carrier | f x = c} = S :=
    target_contact_side D.target f c hle hi hi1 hi2
  set part : Finset (Fin N × Fin 3) :=
    Finset.univ.filter (fun e : Fin N × Fin 3 => (D.tile e.1).edge e.2 ⊆ S) with hpart
  refine ⟨part, ?_⟩
  apply Set.Subset.antisymm
  · 
    intro x hx
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hx
    have : (D.tile e.1).edge e.2 ⊆ S := by
      rw [hpart, Finset.mem_filter] at he; exact he.2
    exact this hxe
  · 
    have hFfin : (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2).Finite :=
      Set.finite_range _
    have hUclosed : IsClosed (⋃ e ∈ part, (D.tile e.1).edge e.2) :=
      Set.Finite.isClosed_biUnion (Finset.finite_toSet part)
        (fun e _ => (D.tile e.1).isClosed_edge e.2)
    have hnd : D.target.pts i ≠ D.target.pts (i + 1) := by
      intro h
      have hij : i = i + 1 := D.target.indep.injective h
      fin_cases i <;> exact absurd hij (by decide)
    have hkey : S \ (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2)
              ⊆ ⋃ e ∈ part, (D.tile e.1).edge e.2 := by
      rintro x ⟨hxS, hxF⟩
      have hxt : x ∈ D.target.carrier ∧ f x = c := by rw [← hS] at hxS; exact hxS
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (by rw [D.covers]; exact hxt.1)
      have hlej : ∀ y ∈ (D.tile j).carrier, f y ≤ c :=
        fun y hy => hle y (tile_subset_target D j hy)
      have hxv : ∀ k, x ≠ (D.tile j).pts k := by
        intro k hk; exact hxF ⟨(j, k), hk.symm⟩
      obtain ⟨k, hk⟩ := contact_is_edge (D.tile j) f c hf hlej hxj hxt.2 hxv
      have hsub : (D.tile j).edge k ⊆ S := by
        rw [← hk, ← hS]
        rintro y ⟨hy1, hy2⟩
        exact ⟨tile_subset_target D j hy1, hy2⟩
      refine Set.mem_iUnion₂.mpr ⟨(j, k), ?_, ?_⟩
      · rw [hpart, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsub⟩
      · rw [← hk]; exact ⟨hxj, hxt.2⟩
    calc S ⊆ closure (S \ (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2)) :=
          Erdos634.SegmentDense.subset_closure_diff_finite hnd hFfin
      _ ⊆ closure (⋃ e ∈ part, (D.tile e.1).edge e.2) := closure_mono hkey
      _ = _ := hUclosed.closure_eq
theorem Tri.hausdorff_edge (T : Tri) (k : Fin 3) :
    (MeasureTheory.Measure.hausdorffMeasure 1) (T.edge k) = edist (T.pts k) (T.pts (k + 1)) := by
  rw [Tri.edge]
  exact MeasureTheory.hausdorffMeasure_segment _ _
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
theorem Dissection.volume_ball_eq_sum {N : ℕ} (D : Dissection N) {x : Plane} {r : ℝ}
    (hball : Metric.ball x r ⊆ D.target.carrier) :
    volume (Metric.ball x r) = ∑ i, volume ((D.tile i).carrier ∩ Metric.ball x r) := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => (D.tile i).carrier ∩ Metric.ball x r)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) (D.aedisjoint hij))
    (fun i _ => ((D.tile i).nullMeasurableSet).inter
      Metric.isOpen_ball.measurableSet.nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), ((D.tile i).carrier ∩ Metric.ball x r))
          = Metric.ball x r := by
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [← Set.iUnion_inter, D.covers]
    exact Set.inter_eq_self_of_subset_right hball
  rw [hU] at h
  exact h
theorem local_degree_eq {V : ℝ≥0∞} (hV0 : V ≠ 0) (hVt : V ≠ ⊤) {k m : ℕ}
    (h : (k : ℝ≥0∞) * V + (m : ℝ≥0∞) * (2 * V) = 2 * V) :
    k + 2 * m = 2 := by
  have hcast : ((k + 2 * m : ℕ) : ℝ≥0∞) * V = ((2 : ℕ) : ℝ≥0∞) * V := by
    push_cast
    rw [← h]; ring
  exact_mod_cast (ENNReal.mul_left_inj hV0 hVt).mp hcast
theorem local_degree_two {k m : ℕ} (hk : 1 ≤ k) (h : k + 2 * m = 2) : k = 2 ∧ m = 0 := by
  omega
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
theorem Dissection.local_balance {N : ℕ} (D : Dissection N) {x : Plane} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x r ⊆ D.target.carrier)
    (E I : Finset (Fin N)) (hdisj : Disjoint E I)
    (hE : ∀ i ∈ E, 2 * volume ((D.tile i).carrier ∩ Metric.ball x r) = volume (Metric.ball x r))
    (hI : ∀ i ∈ I, volume ((D.tile i).carrier ∩ Metric.ball x r) = volume (Metric.ball x r))
    (hrest : ∀ i ∈ (Finset.univ : Finset (Fin N)), i ∉ E ∪ I →
      volume ((D.tile i).carrier ∩ Metric.ball x r) = 0)
    (hEne : E.Nonempty) :
    E.card = 2 ∧ I.card = 0 := by
  classical
  set V : ℝ≥0∞ := volume (Metric.ball x r) with hV
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hsum : ∑ i ∈ E ∪ I, volume ((D.tile i).carrier ∩ Metric.ball x r) = V := by
    rw [Finset.sum_subset (Finset.subset_univ (E ∪ I)) hrest]
    exact (D.volume_ball_eq_sum hball).symm
  have hsplit : ∑ i ∈ E ∪ I, volume ((D.tile i).carrier ∩ Metric.ball x r)
      = (∑ i ∈ E, volume ((D.tile i).carrier ∩ Metric.ball x r))
        + ∑ i ∈ I, volume ((D.tile i).carrier ∩ Metric.ball x r) :=
    Finset.sum_union hdisj
  have hEsum : 2 * ∑ i ∈ E, volume ((D.tile i).carrier ∩ Metric.ball x r) = (E.card : ℝ≥0∞) * V := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hE, Finset.sum_const, nsmul_eq_mul]
  have hIsum : ∑ i ∈ I, volume ((D.tile i).carrier ∩ Metric.ball x r) = (I.card : ℝ≥0∞) * V := by
    rw [Finset.sum_congr rfl hI, Finset.sum_const, nsmul_eq_mul]
  rw [hsplit] at hsum
  have hkey : (E.card : ℝ≥0∞) * V + (I.card : ℝ≥0∞) * (2 * V) = 2 * V := by
    have h1 : (I.card : ℝ≥0∞) * (2 * V) = 2 * ((I.card : ℝ≥0∞) * V) := by ring
    rw [h1, ← hEsum, ← hIsum, ← mul_add, hsum]
  have hcount : E.card + 2 * I.card = 2 := local_degree_eq hV0 hVt hkey
  exact local_degree_two (Finset.card_pos.mpr hEne) hcount
def OnEdge {N : ℕ} (D : Dissection N) (x : Plane) (i : Fin N) : Prop :=
  ∃ k, (D.tile i).basis.coord k x = 0 ∧ ∀ j, j ≠ k → 0 < (D.tile i).basis.coord j x
def Inside {N : ℕ} (D : Dissection N) (x : Plane) (i : Fin N) : Prop :=
  ∀ j, 0 < (D.tile i).basis.coord j x
theorem Dissection.local_contribution {N : ℕ} (D : Dissection N) {x : Plane} (i : Fin N)
    (hxv : ∀ k, x ≠ (D.tile i).pts k) :
    ∃ ri > 0, ∀ r', 0 < r' → r' ≤ ri →
      (OnEdge D x i →
        2 * volume ((D.tile i).carrier ∩ Metric.ball x r') = volume (Metric.ball x r'))
    ∧ (Inside D x i →
        volume ((D.tile i).carrier ∩ Metric.ball x r') = volume (Metric.ball x r'))
    ∧ (¬ OnEdge D x i → ¬ Inside D x i →
        volume ((D.tile i).carrier ∩ Metric.ball x r') = 0) := by
  classical
  rcases (D.tile i).classify hxv with hpos | ⟨k, hk0, hkpos⟩ | ⟨k, hkneg⟩
  · 
    obtain ⟨r, hr, h⟩ := (D.tile i).volume_inter_ball_interior hpos
    refine ⟨r, hr, fun r' h1 h2 => ⟨fun hE => ?_, fun _ => h r' h1 h2, fun _ hI => absurd hpos hI⟩⟩
    obtain ⟨m, hm, -⟩ := hE
    exact absurd hm (ne_of_gt (hpos m))
  · 
    have hne : ∀ j : Fin 3, j + 1 ≠ j ∧ j + 2 ≠ j := by decide
    obtain ⟨r, hr, h⟩ := (D.tile i).volume_inter_ball_edge k hk0
      (hkpos _ (hne k).1) (hkpos _ (hne k).2)
    refine ⟨r, hr, fun r' h1 h2 => ⟨fun _ => h r' h1 h2, fun hI => ?_, fun hE _ => ?_⟩⟩
    · exact absurd hk0 (ne_of_gt (hI k))
    · exact absurd ⟨k, hk0, hkpos⟩ hE
  · 
    obtain ⟨r, hr, h⟩ := (D.tile i).volume_inter_ball_exterior hkneg
    refine ⟨r, hr, fun r' h1 h2 => ⟨fun hE => ?_, fun hI => ?_, fun _ _ => h r' h1 h2⟩⟩
    · obtain ⟨m, hm, hrest⟩ := hE
      by_cases hmk : k = m
      · rw [hmk] at hkneg; exact absurd hm (ne_of_lt hkneg)
      · exact absurd (hrest k hmk) (not_lt.mpr hkneg.le)
    · exact absurd (hI k) (not_lt.mpr hkneg.le)
open scoped Classical in
theorem Dissection.two_tiles_at_edge_point {N : ℕ} (D : Dissection N) (hN : 0 < N) {x : Plane}
    (hxv : ∀ i k, x ≠ (D.tile i).pts k)
    {R : ℝ} (hR : 0 < R) (hRt : Metric.ball x R ⊆ D.target.carrier)
    (hEne : (Finset.univ.filter (fun i => OnEdge D x i)).Nonempty) :
    (Finset.univ.filter (fun i => OnEdge D x i)).card = 2
      ∧ (Finset.univ.filter (fun i => Inside D x i)).card = 0 := by
  classical
  choose ri hri hcontrib using fun i => D.local_contribution i (hxv i)
  obtain ⟨r0, hr0, hr0le⟩ := exists_common_radius hN ri hri
  refine D.local_balance (x := x) (r := min R r0) (lt_min hR hr0) ?_ _ _ ?_ ?_ ?_ ?_ hEne
  · exact (Metric.ball_subset_ball (min_le_left _ _)).trans hRt
  · 
    rw [Finset.disjoint_left]
    intro i hiE hiI
    obtain ⟨m, hm, -⟩ := (Finset.mem_filter.mp hiE).2
    exact absurd hm (ne_of_gt ((Finset.mem_filter.mp hiI).2 m))
  · exact fun i hi => (hcontrib i _ (lt_min hR hr0)
      ((min_le_right R r0).trans (hr0le i))).1 (Finset.mem_filter.mp hi).2
  · exact fun i hi => (hcontrib i _ (lt_min hR hr0)
      ((min_le_right R r0).trans (hr0le i))).2.1 (Finset.mem_filter.mp hi).2
  · intro i _ hi
    rw [Finset.mem_union, not_or] at hi
    exact (hcontrib i _ (lt_min hR hr0) ((min_le_right R r0).trans (hr0le i))).2.2
      (fun h => hi.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩))
      (fun h => hi.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩))
noncomputable def Tri.det (T : Tri) : ℝ :=
  (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1 - (T.pts 1 - T.pts 0) 1 * (T.pts 2 - T.pts 0) 0
noncomputable def Tri.leftDir (T : Tri) (k : Fin 3) : Plane :=
  if 0 < T.det then T.pts (k + 1) - T.pts k else T.pts k - T.pts (k + 1)
theorem Tri.leftDir_ne_zero (T : Tri) (k : Fin 3) : T.leftDir k ≠ 0 := by
  have hsucc : ∀ j : Fin 3, j ≠ j + 1 := by decide
  have hne : T.pts k ≠ T.pts (k + 1) := fun h => hsucc k (T.indep.injective h)
  unfold Tri.leftDir
  split
  · exact sub_ne_zero.mpr (Ne.symm hne)
  · exact sub_ne_zero.mpr hne
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
theorem Tri.leftDir_eq_or (T : Tri) (k : Fin 3) :
    T.leftDir k = T.pts (k + 1) - T.pts k ∨ T.leftDir k = -(T.pts (k + 1) - T.pts k) := by
  unfold Tri.leftDir; split
  · exact Or.inl rfl
  · right; abel
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
theorem Tri.interior_left_of_leftDir (T : Tri) (k : Fin 3) {y : Plane}
    (hy : ∀ i, 0 < T.basis.coord i y) :
    0 < cross (T.leftDir k) (y - T.pts k) := by
  have hdet : T.det ≠ 0 := T.det_ne_zero
  have hid := T.coord_mul_det k y
  have hc : 0 < T.basis.coord (k + 2) y := hy _
  unfold Tri.leftDir
  split
  · rename_i hpos
    rw [← hid]; exact mul_pos hc hpos
  · rename_i hnpos
    have hneg : T.det < 0 := lt_of_le_of_ne (not_lt.mp hnpos) hdet
    have hflip : T.pts k - T.pts (k + 1) = -(T.pts (k + 1) - T.pts k) := (neg_sub _ _).symm
    rw [hflip, cross_neg_left, ← hid]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg hc hneg)
def Dir : Type := {v : Plane // ‖v‖ = 1}
def Dir.neg (d : Dir) : Dir := ⟨-d.1, by rw [norm_neg]; exact d.2⟩
noncomputable def Tri.leftUnit (T : Tri) (k : Fin 3) : Dir :=
  ⟨‖T.leftDir k‖⁻¹ • T.leftDir k, by
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (T.leftDir_ne_zero k))⟩
theorem proportional_of_ker_le (f g : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (h : ∀ v, f v = 0 → g v = 0) : ∃ c : ℝ, ∀ w, g w = c * f w := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hf (LinearMap.ext fun w => by simpa using hcon w)
  refine ⟨g v / f v, fun w => ?_⟩
  have hker : f (w - (f w / f v) • v) = 0 := by
    simp [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  have := h _ hker
  simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
  rw [this]
  field_simp
theorem proportional_of_disjoint_pos (L₁ L₂ : Plane →ₗ[ℝ] ℝ) (h₁ : L₁ ≠ 0) (h₂ : L₂ ≠ 0)
    (hdisj : ∀ v, ¬(0 < L₁ v ∧ 0 < L₂ v)) :
    ∃ c : ℝ, c < 0 ∧ ∀ v, L₂ v = c * L₁ v := by
  obtain ⟨u, hu⟩ : ∃ u, 0 < L₁ u := by
    obtain ⟨w, hw⟩ : ∃ w, L₁ w ≠ 0 := by
      by_contra hc; push_neg at hc
      exact h₁ (LinearMap.ext fun w => by simpa using hc w)
    rcases lt_or_gt_of_ne hw with hneg | hpos
    · exact ⟨-w, by simpa using hneg⟩
    · exact ⟨w, hpos⟩
  have hker : ∀ v, L₁ v = 0 → L₂ v = 0 := by
    intro v hv
    by_contra hne
    obtain ⟨v', hv1, hv2⟩ : ∃ v', L₁ v' = 0 ∧ 0 < L₂ v' := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨-v, by simpa using hv, by simpa using hlt⟩
      · exact ⟨v, hv, hgt⟩
    by_cases hpos : 0 ≤ L₂ u
    · refine hdisj (u + v') ⟨?_, ?_⟩
      · rw [map_add, hv1, add_zero]; exact hu
      · rw [map_add]; linarith
    · have hnegu : L₂ u < 0 := not_le.mp hpos
      have hepos : 0 < L₂ v' / (-2 * L₂ u) := div_pos hv2 (by linarith)
      refine hdisj ((L₂ v' / (-2 * L₂ u)) • u + v') ⟨?_, ?_⟩
      · rw [map_add, map_smul, hv1, smul_eq_mul, add_zero]
        exact mul_pos hepos hu
      · rw [map_add, map_smul, smul_eq_mul]
        have hune : L₂ u ≠ 0 := ne_of_lt hnegu
        have hcalc : L₂ v' / (-2 * L₂ u) * L₂ u = -(L₂ v') / 2 := by
          field_simp
        rw [hcalc]; linarith
  obtain ⟨c, hc⟩ := proportional_of_ker_le L₁ L₂ h₁ hker
  have hcne : c ≠ 0 := by
    intro h; subst h
    exact h₂ (LinearMap.ext fun v => by simpa using hc v)
  refine ⟨c, ?_, hc⟩
  rcases lt_or_gt_of_ne hcne with hlt | hgt
  · exact hlt
  · exact absurd ⟨hu, by rw [hc u]; exact mul_pos hgt hu⟩ (hdisj u)
theorem Tri.mem_interior_of_cross_pos (T : Tri) {x : Plane} {m : Fin 3}
    (hm : T.basis.coord m x = 0) (hother : ∀ j, j ≠ m → 0 < T.basis.coord j x)
    {v : Plane} (hv : 0 < cross (T.leftDir (m + 1)) v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → x + ε • v ∈ interior T.carrier := by
  have hidx : (m + 1) + 2 = m := by fin_cases m <;> rfl
  set w : Plane := T.pts ((m + 1) + 1) - T.pts (m + 1) with hw
  have hcoord : ∀ ε : ℝ, T.basis.coord m (x + ε • v) * T.det = ε * cross w v := by
    intro ε
    have h1 := T.coord_mul_det (m + 1) (x + ε • v)
    have h2 := T.coord_mul_det (m + 1) x
    rw [hidx] at h1 h2
    rw [hm, zero_mul] at h2
    have hsplit : x + ε • v - T.pts (m + 1) = (x - T.pts (m + 1)) + ε • v := by abel
    rw [hsplit, cross_add_right, cross_smul_right, ← hw, ← h2, zero_add] at h1
    exact h1
  have hvne : v ≠ 0 := by rintro rfl; simp at hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hmpos : ∀ ε : ℝ, 0 < ε → 0 < T.basis.coord m (x + ε • v) := by
    intro ε hε
    have hdet := T.det_ne_zero
    rcases lt_or_gt_of_ne hdet with hneg | hpos
    · have hlv : T.leftDir (m + 1) = -w := by
        unfold Tri.leftDir; rw [if_neg (not_lt.mpr hneg.le), hw]; abel
      rw [hlv, cross_neg_left] at hv
      have hcw : cross w v < 0 := by linarith
      have := hcoord ε
      nlinarith [mul_pos hε (neg_pos.mpr hcw)]
    · have hlv : T.leftDir (m + 1) = w := by
        unfold Tri.leftDir; rw [if_pos hpos, hw]
      rw [hlv] at hv
      have := hcoord ε
      nlinarith [mul_pos hε hv]
  have hopen : IsOpen {y : Plane | ∀ j, j ≠ m → 0 < T.basis.coord j y} := by
    have heq : {y : Plane | ∀ j, j ≠ m → 0 < T.basis.coord j y}
        = ⋂ j : Fin 3, {y : Plane | j ≠ m → 0 < T.basis.coord j y} := by
      ext y; simp [Set.mem_iInter]
    rw [heq]
    refine isOpen_iInter_of_finite fun j => ?_
    by_cases hj : j = m
    · have : {y : Plane | j ≠ m → 0 < T.basis.coord j y} = Set.univ := by ext y; simp [hj]
      rw [this]; exact isOpen_univ
    · have : {y : Plane | j ≠ m → 0 < T.basis.coord j y} = {y | 0 < T.basis.coord j y} := by
        ext y; simp [hj]
      rw [this]
      exact isOpen_lt continuous_const (AffineMap.continuous_of_finiteDimensional _)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hother
  refine ⟨r / ‖v‖, div_pos hr hvpos, fun ε hε hlt => ?_⟩
  have hin : x + ε • v ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : x + ε • v - x = ε • v := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    calc ε * ‖v‖ < (r / ‖v‖) * ‖v‖ := by
          exact mul_lt_mul_of_pos_right hlt hvpos
      _ = r := div_mul_cancel₀ r (ne_of_gt hvpos)
  have hallpos : ∀ j, 0 < T.basis.coord j (x + ε • v) := by
    intro j
    by_cases hj : j = m
    · rw [hj]; exact hmpos ε hε
    · exact hball hin j hj
  obtain ⟨ρ, hρ, hρsub⟩ := T.ball_subset_of_pos hallpos
  exact mem_interior.mpr ⟨Metric.ball (x + ε • v) ρ, hρsub, Metric.isOpen_ball,
    Metric.mem_ball_self hρ⟩
theorem Dissection.cross_disjoint_of_onEdge {N : ℕ} (D : Dissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) {x : Plane} {m₁ m₂ : Fin 3}
    (hm₁ : (D.tile i₁).basis.coord m₁ x = 0)
    (ho₁ : ∀ j, j ≠ m₁ → 0 < (D.tile i₁).basis.coord j x)
    (hm₂ : (D.tile i₂).basis.coord m₂ x = 0)
    (ho₂ : ∀ j, j ≠ m₂ → 0 < (D.tile i₂).basis.coord j x)
    (v : Plane) :
    ¬(0 < cross ((D.tile i₁).leftDir (m₁ + 1)) v
      ∧ 0 < cross ((D.tile i₂).leftDir (m₂ + 1)) v) := by
  rintro ⟨hv₁, hv₂⟩
  obtain ⟨ε₁, hε₁, h₁⟩ := (D.tile i₁).mem_interior_of_cross_pos hm₁ ho₁ hv₁
  obtain ⟨ε₂, hε₂, h₂⟩ := (D.tile i₂).mem_interior_of_cross_pos hm₂ ho₂ hv₂
  set ε := min ε₁ ε₂ / 2 with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact half_pos (lt_min hε₁ hε₂)
  have hlt₁ : ε < ε₁ := by
    rw [hεdef]; have := min_le_left ε₁ ε₂; linarith
  have hlt₂ : ε < ε₂ := by
    rw [hεdef]; have := min_le_right ε₁ ε₂; linarith
  exact Set.disjoint_left.mp (D.interiors_disjoint hne)
    (h₁ ε hεpos hlt₁) (h₂ ε hεpos hlt₂)
noncomputable def crossL (u : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun := cross u
  map_add' := cross_add_right u
  map_smul' := fun t v => cross_smul_right t u v
@[simp] theorem crossL_apply (u v : Plane) : crossL u v = cross u v := rfl
theorem eq_zero_of_cross_eq_zero {u : Plane} (h : ∀ v, cross u v = 0) : u = 0 := by
  have h0 : u 0 = 0 := by
    have := h (EuclideanSpace.single 1 (1 : ℝ)); simpa [cross] using this
  have h1 : u 1 = 0 := by
    have := h (EuclideanSpace.single 0 (1 : ℝ))
    simp [cross] at this
    linarith
  ext i; fin_cases i
  · simpa using h0
  · simpa using h1
theorem crossL_ne_zero {u : Plane} (hu : u ≠ 0) : crossL u ≠ 0 := by
  intro h
  exact hu (eq_zero_of_cross_eq_zero fun v => by
    have := LinearMap.congr_fun h v; simpa using this)
theorem Dissection.leftDir_antiparallel {N : ℕ} (D : Dissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) {x : Plane} {m₁ m₂ : Fin 3}
    (hm₁ : (D.tile i₁).basis.coord m₁ x = 0)
    (ho₁ : ∀ j, j ≠ m₁ → 0 < (D.tile i₁).basis.coord j x)
    (hm₂ : (D.tile i₂).basis.coord m₂ x = 0)
    (ho₂ : ∀ j, j ≠ m₂ → 0 < (D.tile i₂).basis.coord j x) :
    ∃ c : ℝ, c < 0 ∧ (D.tile i₂).leftDir (m₂ + 1) = c • (D.tile i₁).leftDir (m₁ + 1) := by
  obtain ⟨c, hcneg, hc⟩ := proportional_of_disjoint_pos
    (crossL ((D.tile i₁).leftDir (m₁ + 1))) (crossL ((D.tile i₂).leftDir (m₂ + 1)))
    (crossL_ne_zero ((D.tile i₁).leftDir_ne_zero _))
    (crossL_ne_zero ((D.tile i₂).leftDir_ne_zero _))
    (fun v => by
      simpa using D.cross_disjoint_of_onEdge hne hm₁ ho₁ hm₂ ho₂ v)
  refine ⟨c, hcneg, ?_⟩
  have hzero : ∀ v, cross ((D.tile i₂).leftDir (m₂ + 1) - c • (D.tile i₁).leftDir (m₁ + 1)) v = 0 := by
    intro v
    have h1 : cross ((D.tile i₂).leftDir (m₂ + 1)) v = c * cross ((D.tile i₁).leftDir (m₁ + 1)) v := by
      simpa using hc v
    simp only [cross, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    simp only [cross] at h1
    linarith [h1]
  exact sub_eq_zero.mp (eq_zero_of_cross_eq_zero hzero)
theorem exists_second_of_card_two {α : Type*} {s : Finset α} (h : s.card = 2) (a : α) :
    ∃ b ∈ s, b ≠ a :=
  Finset.exists_mem_ne (by omega) a
theorem Dissection.second_tile_at_edge_point {N : ℕ} (D : Dissection N) (hN : 0 < N) {x : Plane}
    (hxv : ∀ i k, x ≠ (D.tile i).pts k)
    {R : ℝ} (hR : 0 < R) (hRt : Metric.ball x R ⊆ D.target.carrier)
    {i₀ : Fin N} (hi₀ : OnEdge D x i₀) :
    ∃ i₁, i₁ ≠ i₀ ∧ OnEdge D x i₁ := by
  classical
  have hmem : i₀ ∈ Finset.univ.filter (fun i => OnEdge D x i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩
  have hcard := (D.two_tiles_at_edge_point hN hxv hR hRt ⟨i₀, hmem⟩).1
  obtain ⟨i₁, hi₁mem, hne⟩ := exists_second_of_card_two hcard i₀
  exact ⟨i₁, hne, (Finset.mem_filter.mp hi₁mem).2⟩
theorem Tri.edge_subset_carrier (T : Tri) (k : Fin 3) : T.edge k ⊆ T.carrier := by
  refine (convex_convexHull ℝ _).segment_subset ?_ ?_ <;>
    exact subset_convexHull ℝ _ ⟨_, rfl⟩
theorem Tri.coord_eq_zero_of_mem_edge (T : Tri) (k : Fin 3) {x : Plane} (hx : x ∈ T.edge k) :
    T.basis.coord (k + 2) x = 0 := by
  have hne1 : (k + 2) ≠ k := by fin_cases k <;> decide
  have hne2 : (k + 2) ≠ (k + 1) := by fin_cases k <;> decide
  have hconv : Convex ℝ ((T.basis.coord (k + 2)) ⁻¹' {(0 : ℝ)}) :=
    (convex_singleton (0 : ℝ)).affine_preimage _
  have hb : ∀ i : Fin 3, T.pts i = (T.basis : Fin 3 → Plane) i := fun _ => rfl
  refine hconv.segment_subset ?_ ?_ hx
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, hb, AffineBasis.coord_apply]
    simp [hne1]
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, hb, AffineBasis.coord_apply]
    simp [hne2]
theorem Tri.mem_edge_of_coord_zero (T : Tri) {m : Fin 3} {x : Plane}
    (hm : T.basis.coord m x = 0) (ho : ∀ j, j ≠ m → 0 < T.basis.coord j x) :
    x ∈ T.edge (m + 1) := by
  have hsum := T.basis.sum_coord_apply_eq_one x
  have hcomb := T.basis.linear_combination_coord_eq_self x
  have h1 : (m + 1) ≠ m := by fin_cases m <;> decide
  have h2 : (m + 2) ≠ m := by fin_cases m <;> decide
  refine ⟨T.basis.coord (m + 1) x, T.basis.coord (m + 1 + 1) x,
    (ho _ h1).le, ?_, ?_, ?_⟩
  · have : (m + 1 + 1) = m + 2 := by fin_cases m <;> rfl
    rw [this]; exact (ho _ h2).le
  · have hthree : ∀ c : Fin 3 → ℝ, ∑ i, c i = c m + c (m + 1) + c (m + 1 + 1) := by
      intro c; fin_cases m <;> simp [Fin.sum_univ_three] <;> ring
    rw [hthree] at hsum; rw [hm, zero_add] at hsum; exact hsum
  · have hthree : ∀ c : Fin 3 → Plane, ∑ i, c i = c m + c (m + 1) + c (m + 1 + 1) := by
      intro c; fin_cases m <;> simp [Fin.sum_univ_three] <;> abel
    rw [hthree] at hcomb
    have hb : ∀ i, T.basis i = T.pts i := fun _ => rfl
    simpa [hm, zero_smul, hb] using hcomb
theorem unit_smul_of_neg {u v : Plane} {c : ℝ} (hc : c < 0) (hu : u ≠ 0) (hv : v = c • u) :
    ‖v‖⁻¹ • v = -(‖u‖⁻¹ • u) := by
  have hun : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hcne : c ≠ 0 := ne_of_lt hc
  have hune : ‖u‖ ≠ 0 := ne_of_gt hun
  subst hv
  have hnv : ‖c • u‖ = -c * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_neg hc]
  rw [hnv, smul_smul, ← neg_smul]
  congr 1
  field_simp
theorem Dissection.leftUnit_neg {N : ℕ} (D : Dissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) {x : Plane} {m₁ m₂ : Fin 3}
    (hm₁ : (D.tile i₁).basis.coord m₁ x = 0)
    (ho₁ : ∀ j, j ≠ m₁ → 0 < (D.tile i₁).basis.coord j x)
    (hm₂ : (D.tile i₂).basis.coord m₂ x = 0)
    (ho₂ : ∀ j, j ≠ m₂ → 0 < (D.tile i₂).basis.coord j x) :
    (D.tile i₂).leftUnit (m₂ + 1) = Dir.neg ((D.tile i₁).leftUnit (m₁ + 1)) := by
  obtain ⟨c, hcneg, hc⟩ := D.leftDir_antiparallel hne hm₁ ho₁ hm₂ ho₂
  apply Subtype.ext
  simpa [Tri.leftUnit, Dir.neg] using
    unit_smul_of_neg hcneg ((D.tile i₁).leftDir_ne_zero (m₁ + 1)) hc
def Dissection.vertexSet {N : ℕ} (D : Dissection N) : Set Plane :=
  ⋃ i : Fin N, ⋃ k : Fin 3, {(D.tile i).pts k}
theorem Dissection.vertexSet_finite {N : ℕ} (D : Dissection N) : D.vertexSet.Finite :=
  Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _
theorem Dissection.notMem_vertexSet {N : ℕ} (D : Dissection N) {x : Plane}
    (hx : x ∉ D.vertexSet) : ∀ i k, x ≠ (D.tile i).pts k := by
  intro i k h
  exact hx (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨k, by simp [h]⟩⟩)
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
open MeasureTheory Set
theorem cross_sub_right (u a b : Plane) : cross u (a - b) = cross u a - cross u b := by
  simp only [cross, PiLp.sub_apply]; ring
theorem cross_smul_left (t : ℝ) (u v : Plane) : cross (t • u) v = t * cross u v := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring
theorem cross_eq_zero_of_common_ker {n u v : Plane} (hn : n ≠ 0)
    (hu : cross n u = 0) (hv : cross n v = 0) : cross u v = 0 := by
  have hcomp : n 0 ≠ 0 ∨ n 1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hn (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  simp only [cross] at hu hv ⊢
  rcases hcomp with h | h
  · have key : n 0 * (u 0 * v 1 - u 1 * v 0) = 0 := by
      linear_combination u 0 * hv - v 0 * hu
    rcases mul_eq_zero.mp key with h' | h'
    · exact absurd h' h
    · exact h'
  · have key : n 1 * (u 0 * v 1 - u 1 * v 0) = 0 := by
      linear_combination u 1 * hv - v 1 * hu
    rcases mul_eq_zero.mp key with h' | h'
    · exact absurd h' h
    · exact h'
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
theorem plane_decomp (y : Plane) :
    y = EuclideanSpace.single (0 : Fin 2) (y 0) + EuclideanSpace.single (1 : Fin 2) (y 1) := by
  ext i
  fin_cases i <;> simp
theorem single_eq_smul (i : Fin 2) (a : ℝ) :
    EuclideanSpace.single i a = a • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases h : j = i <;> simp [h]
noncomputable def rotVec (f : Plane →ₗ[ℝ] ℝ) : Plane :=
  EuclideanSpace.single (0 : Fin 2) (f (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
    + EuclideanSpace.single (1 : Fin 2) (-(f (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))))
theorem rotVec_spec (f : Plane →ₗ[ℝ] ℝ) (y : Plane) : f y = cross (rotVec f) y := by
  have h0 : EuclideanSpace.single (0 : Fin 2) (y 0)
      = y 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := single_eq_smul 0 (y 0)
  have h1 : EuclideanSpace.single (1 : Fin 2) (y 1)
      = y 1 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := single_eq_smul 1 (y 1)
  have hf : f y = y 0 * f (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
      + y 1 * f (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := by
    conv_lhs => rw [plane_decomp y, h0, h1]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hcross : cross (rotVec f) y
      = f (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) * y 1
        + f (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) * y 0 := by
    simp only [cross, rotVec, PiLp.add_apply]
    simp
  rw [hf, hcross]; ring
theorem rotVec_ne_zero {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) : rotVec f ≠ 0 := by
  intro h
  apply hf
  apply LinearMap.ext
  intro y
  rw [rotVec_spec f y, h]
  simp [cross]
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
theorem Tri.interior_lt_of_le (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle : ∀ y ∈ T.carrier, f y ≤ c) {y : Plane} (hy : y ∈ interior T.carrier) : f y < c := by
  rcases (hle y (interior_subset hy)).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hy
    obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hf (LinearMap.ext fun z => by simpa using hc z)
    obtain ⟨v, hv⟩ : ∃ v, 0 < f v := by
      rcases lt_or_gt_of_ne hw with h' | h'
      · exact ⟨-w, by rw [map_neg]; linarith⟩
      · exact ⟨w, h'⟩
    have hvne : v ≠ 0 := by
      rintro rfl
      rw [map_zero] at hv
      exact absurd hv (lt_irrefl 0)
    obtain ⟨hmem, htpos⟩ := move_in_ball (x := y) hvne hr
    have hin : f (y + (r / (2 * ‖v‖)) • v) ≤ c := hle _ (interior_subset (hball hmem))
    rw [map_add, map_smul, smul_eq_mul, h] at hin
    nlinarith [mul_pos htpos hv]
theorem Tri.onEdge_param (T : Tri) {k : Fin 3} {x : Plane} (hx : x ∈ T.edge k)
    (h1 : x ≠ T.pts k) (h2 : x ≠ T.pts (k + 1)) :
    T.basis.coord (k + 2) x = 0 ∧ ∀ j, j ≠ k + 2 → 0 < T.basis.coord j x := by
  have hz := T.coord_eq_zero_of_mem_edge k hx
  rw [Tri.edge] at hx
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hx
  have hca : T.basis.coord k x = a := by
    rw [← hcomb, Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
    have e1 : T.basis.coord k (T.pts k) = 1 := T.basis.coord_apply_eq k
    have e2 : T.basis.coord k (T.pts (k + 1)) = 0 :=
      T.basis.coord_apply_ne (by fin_cases k <;> decide)
    rw [e1, e2]; ring
  have hcb : T.basis.coord (k + 1) x = b := by
    rw [← hcomb, Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
    have e1 : T.basis.coord (k + 1) (T.pts k) = 0 :=
      T.basis.coord_apply_ne (by fin_cases k <;> decide)
    have e2 : T.basis.coord (k + 1) (T.pts (k + 1)) = 1 := T.basis.coord_apply_eq (k + 1)
    rw [e1, e2]; ring
  have hapos : 0 < a := by
    rcases ha.lt_or_eq with h | h
    · exact h
    · exfalso
      apply h2
      have hb1 : b = 1 := by linarith
      rw [← hcomb, ← h, hb1]
      simp
  have hbpos : 0 < b := by
    rcases hb.lt_or_eq with h | h
    · exact h
    · exfalso
      apply h1
      have ha1 : a = 1 := by linarith
      rw [← hcomb, ← h, ha1]
      simp
  refine ⟨hz, fun j hj => ?_⟩
  have hcases : j = k ∨ j = k + 1 := by
    have hall : ∀ j k : Fin 3, j ≠ k + 2 → j = k ∨ j = k + 1 := by decide
    exact hall j k hj
  rcases hcases with rfl | rfl
  · rw [hca]; exact hapos
  · rw [hcb]; exact hbpos
theorem mem_ne_ends_of_avg {A B p q : Plane} (hpq : p ≠ q)
    (hp : p ∈ segment ℝ A B) (hq : q ∈ segment ℝ A B) :
    ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ∈ segment ℝ A B
      ∧ ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ≠ A ∧ ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ≠ B := by
  have hmem : ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ∈ segment ℝ A B :=
    (convex_segment A B) hp hq (by norm_num) (by norm_num) (by norm_num)
  have hAB : A ≠ B := by
    rintro rfl
    rw [segment_same] at hp hq
    rw [Set.mem_singleton_iff] at hp hq
    exact hpq (hp.trans hq.symm)
  rw [segment_eq_image' ℝ A B] at hp hq
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  have hmid : ((1:ℝ)/2) • (A + s • (B - A)) + ((1:ℝ)/2) • (A + t • (B - A))
      = A + ((s + t)/2) • (B - A) := by module
  refine ⟨hmem, ?_, ?_⟩
  · intro hcon
    rw [hmid] at hcon
    have hkey : ((s + t)/2) • (B - A) = 0 := by
      have h1 := congrArg (fun y => y - A) hcon
      simpa using h1
    rcases smul_eq_zero.mp hkey with h | h
    · have hs0 : s = 0 := by
        have := hs.1; have := ht.1
        have h2 : s + t = 0 := by linarith
        linarith
      have ht0 : t = 0 := by
        have := hs.1
        have h2 : s + t = 0 := by linarith
        linarith
      exact hpq (by rw [hs0, ht0])
    · exact hAB (sub_eq_zero.mp h).symm
  · intro hcon
    rw [hmid] at hcon
    have hB : A + (1:ℝ) • (B - A) = B := by module
    rw [← hB] at hcon
    have h2 : ((s + t)/2) • (B - A) = (1:ℝ) • (B - A) := by
      have h1 := congrArg (fun y => y - A) hcon
      simpa using h1
    have h3 : ((s + t)/2 - 1) • (B - A) = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · have hs1 : s = 1 := by
        have := hs.2; have := ht.2
        have h4 : s + t = 2 := by linarith
        linarith
      have ht1 : t = 1 := by
        have := hs.2
        have h4 : s + t = 2 := by linarith
        linarith
      exact hpq (by rw [hs1, ht1])
    · exact hAB (sub_eq_zero.mp h).symm
theorem Tri.edge_endpoints_on_line (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    {x : Plane} {m : Fin 3}
    (hm : T.basis.coord m x = 0) (ho : ∀ j, j ≠ m → 0 < T.basis.coord j x)
    (hfx : f x = c) (hle1 : f (T.pts (m + 1)) ≤ c) (hle2 : f (T.pts (m + 2)) ≤ c) :
    f (T.pts (m + 1)) = c ∧ f (T.pts (m + 2)) = c := by
  have hxe := T.mem_edge_of_coord_zero hm ho
  have hidx : (m + 1) + 1 = m + 2 := by fin_cases m <;> rfl
  rw [Tri.edge, hidx] at hxe
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hxe
  have hfxc : a * f (T.pts (m + 1)) + b * f (T.pts (m + 2)) = c := by
    rw [← hfx, ← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hca : T.basis.coord (m + 1) x = a := by
    rw [← hcomb, Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
    have e1 : T.basis.coord (m + 1) (T.pts (m + 1)) = 1 := T.basis.coord_apply_eq (m + 1)
    have e2 : T.basis.coord (m + 1) (T.pts (m + 2)) = 0 :=
      T.basis.coord_apply_ne (by fin_cases m <;> decide)
    rw [e1, e2]; ring
  have hcb : T.basis.coord (m + 2) x = b := by
    rw [← hcomb, Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
    have e1 : T.basis.coord (m + 2) (T.pts (m + 1)) = 0 :=
      T.basis.coord_apply_ne (by fin_cases m <;> decide)
    have e2 : T.basis.coord (m + 2) (T.pts (m + 2)) = 1 := T.basis.coord_apply_eq (m + 2)
    rw [e1, e2]; ring
  have hapos : 0 < a := by
    rw [← hca]; exact ho _ (by fin_cases m <;> decide)
  have hbpos : 0 < b := by
    rw [← hcb]; exact ho _ (by fin_cases m <;> decide)
  have habc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  constructor
  · by_contra hne
    have hlt : f (T.pts (m + 1)) < c := lt_of_le_of_ne hle1 hne
    have h1 : a * f (T.pts (m + 1)) < a * c := mul_lt_mul_of_pos_left hlt hapos
    have h2 : b * f (T.pts (m + 2)) ≤ b * c := mul_le_mul_of_nonneg_left hle2 hb
    linarith
  · by_contra hne
    have hlt : f (T.pts (m + 2)) < c := lt_of_le_of_ne hle2 hne
    have h1 : a * f (T.pts (m + 1)) ≤ a * c := mul_le_mul_of_nonneg_left hle1 ha
    have h2 : b * f (T.pts (m + 2)) < b * c := mul_lt_mul_of_pos_left hlt hbpos
    linarith
theorem Tri.edge_inward (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle : ∀ y ∈ T.carrier, f y ≤ c) {x : Plane} {m : Fin 3}
    (hm : T.basis.coord m x = 0) (ho : ∀ j, j ≠ m → 0 < T.basis.coord j x)
    (hfx : f x = c) {v : Plane} (hv : f v < 0) :
    0 < cross (T.leftDir (m + 1)) v := by
  have hmem : ∀ i, T.pts i ∈ T.carrier := fun i => subset_convexHull ℝ _ ⟨i, rfl⟩
  obtain ⟨hP, hQ⟩ := T.edge_endpoints_on_line f c hm ho hfx
    (hle _ (hmem _)) (hle _ (hmem _))
  have hidx : (m + 1) + 1 = m + 2 := by fin_cases m <;> rfl
  have hfdir : f (T.leftDir (m + 1)) = 0 := by
    rcases T.leftDir_eq_or (m + 1) with h | h
    · rw [h, hidx, map_sub, hP, hQ, sub_self]
    · rw [h, hidx, map_neg, map_sub, hP, hQ, sub_self, neg_zero]
  have hker : ∀ w, f w = 0 → crossL (T.leftDir (m + 1)) w = 0 := by
    intro w hw
    have hn := rotVec_ne_zero hf
    have h1 : cross (rotVec f) (T.leftDir (m + 1)) = 0 := by
      rw [← rotVec_spec]; exact hfdir
    have h2 : cross (rotVec f) w = 0 := by rw [← rotVec_spec]; exact hw
    rw [crossL_apply]
    exact cross_eq_zero_of_common_ker hn h1 h2
  obtain ⟨c₀, hc₀⟩ := proportional_of_ker_le f (crossL (T.leftDir (m + 1))) hf hker
  obtain ⟨y₀, hy₀⟩ := T.interior_nonempty
  have hy₀pos := T.interior_coord_pos hy₀
  have hcpos : 0 < cross (T.leftDir (m + 1)) (y₀ - T.pts (m + 1)) :=
    T.interior_left_of_leftDir (m + 1) hy₀pos
  have hylt : f y₀ < c := T.interior_lt_of_le f c hf hle hy₀
  have hval : cross (T.leftDir (m + 1)) (y₀ - T.pts (m + 1)) = c₀ * (f y₀ - c) := by
    have h1 := hc₀ (y₀ - T.pts (m + 1))
    rw [crossL_apply] at h1
    rw [h1, map_sub, hP]
  have hc₀neg : c₀ < 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 : 0 < c₀ * (f y₀ - c) := hval ▸ hcpos
    nlinarith
  have h2 := hc₀ v
  rw [crossL_apply] at h2
  rw [h2]
  exact mul_pos_of_neg_of_neg hc₀neg hv
theorem Dissection.no_second_tile_same_side {N : ℕ} (D : Dissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle₁ : ∀ y ∈ (D.tile i₁).carrier, f y ≤ c) (hle₂ : ∀ y ∈ (D.tile i₂).carrier, f y ≤ c)
    {x : Plane} (hfx : f x = c) {m₁ m₂ : Fin 3}
    (hm₁ : (D.tile i₁).basis.coord m₁ x = 0)
    (ho₁ : ∀ j, j ≠ m₁ → 0 < (D.tile i₁).basis.coord j x)
    (hm₂ : (D.tile i₂).basis.coord m₂ x = 0)
    (ho₂ : ∀ j, j ≠ m₂ → 0 < (D.tile i₂).basis.coord j x) : False := by
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf (LinearMap.ext fun z => by simpa using hc z)
  obtain ⟨v, hv⟩ : ∃ v, f v < 0 := by
    rcases lt_or_gt_of_ne hw with h' | h'
    · exact ⟨w, h'⟩
    · exact ⟨-w, by rw [map_neg]; linarith⟩
  exact D.cross_disjoint_of_onEdge hne hm₁ ho₁ hm₂ ho₂ v
    ⟨(D.tile i₁).edge_inward f c hf hle₁ hm₁ ho₁ hfx hv,
     (D.tile i₂).edge_inward f c hf hle₂ hm₂ ho₂ hfx hv⟩
theorem Dissection.two_edge_data_clash {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) {j₁ j₂ : Fin N} {k₁ k₂ : Fin 3}
    (hne : (j₁, k₁) ≠ (j₂, k₂))
    (hle₁ : ∀ y ∈ (D.tile j₁).carrier, f y ≤ c) (hle₂ : ∀ y ∈ (D.tile j₂).carrier, f y ≤ c)
    {x : Plane} (hfx : f x = c)
    (hz₁ : (D.tile j₁).basis.coord (k₁ + 2) x = 0)
    (hp₁ : ∀ j, j ≠ k₁ + 2 → 0 < (D.tile j₁).basis.coord j x)
    (hz₂ : (D.tile j₂).basis.coord (k₂ + 2) x = 0)
    (hp₂ : ∀ j, j ≠ k₂ + 2 → 0 < (D.tile j₂).basis.coord j x) : False := by
  by_cases hsame : j₁ = j₂
  · subst hsame
    have hk : k₁ ≠ k₂ := fun h => hne (by rw [h])
    have hk2 : k₁ + 2 ≠ k₂ + 2 := fun h => hk (add_right_cancel h)
    exact absurd hz₁ (ne_of_gt (hp₂ _ hk2))
  · exact D.no_second_tile_same_side hsame f c hf hle₁ hle₂ hfx hz₁ hp₁ hz₂ hp₂
theorem Dissection.sameside_edges_subsingleton {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    {e₁ e₂ : Fin N × Fin 3} (hne : e₁ ≠ e₂)
    (hle₁ : ∀ y ∈ (D.tile e₁.1).carrier, f y ≤ c)
    (hle₂ : ∀ y ∈ (D.tile e₂.1).carrier, f y ≤ c)
    (hE₁ : ∀ y ∈ (D.tile e₁.1).edge e₁.2, f y = c)
    (hE₂ : ∀ y ∈ (D.tile e₂.1).edge e₂.2, f y = c) :
    ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  obtain ⟨hm1, hn1A, hn1B⟩ := mem_ne_ends_of_avg hpq hp.1 hq.1
  obtain ⟨hm2, hn2A, hn2B⟩ := mem_ne_ends_of_avg hpq hp.2 hq.2
  obtain ⟨hz₁, hp₁⟩ := (D.tile e₁.1).onEdge_param hm1 hn1A hn1B
  obtain ⟨hz₂, hp₂⟩ := (D.tile e₂.1).onEdge_param hm2 hn2A hn2B
  have hne' : (e₁.1, e₁.2) ≠ (e₂.1, e₂.2) := by simpa using hne
  exact D.two_edge_data_clash f c hf hne' hle₁ hle₂ (hE₁ _ hm1) hz₁ hp₁ hz₂ hp₂
theorem sum_hausdorff_of_partition {ι : Type*} (part : Finset ι)
    (E : ι → Set Plane) (S : Set Plane) (F : Set Plane) (hF : F.Finite)
    (hmeas : ∀ e ∈ part, MeasurableSet (E e))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ → (E e₁ ∩ E e₂).Subsingleton)
    (hsub : ∀ e ∈ part, E e ⊆ S)
    (hcov : S \ F ⊆ ⋃ e ∈ part, E e) :
    ∑ e ∈ part, (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) (E e)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) S := by
  classical
  haveI : MeasureTheory.NullSingletonClass
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) :=
    MeasureTheory.Measure.nullSingletonClass_hausdorff Plane (by norm_num)
  set μ := (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) with hμ
  have hadd := MeasureTheory.measure_biUnion_finset₀ (μ := μ) (s := part) (f := E)
    (fun e₁ h₁ e₂ h₂ hne => ((hdisj e₁ h₁ e₂ h₂ hne).finite.measure_zero μ))
    (fun e he => (hmeas e he).nullMeasurableSet)
  have hle1 : μ (⋃ e ∈ part, E e) ≤ μ S := measure_mono (Set.iUnion₂_subset hsub)
  have hFnull : μ F = 0 := hF.measure_zero μ
  have hle2 : μ S ≤ μ (⋃ e ∈ part, E e) := by
    calc μ S ≤ μ ((⋃ e ∈ part, E e) ∪ F) := by
          refine measure_mono fun x hx => ?_
          by_cases hxF : x ∈ F
          · exact Or.inr hxF
          · exact Or.inl (hcov ⟨hx, hxF⟩)
      _ ≤ μ (⋃ e ∈ part, E e) + μ F := measure_union_le _ _
      _ = μ (⋃ e ∈ part, E e) := by rw [hFnull, add_zero]
  rw [← hadd]
  exact le_antisymm hle1 hle2
theorem Dissection.side_partition {N : ℕ} (D : Dissection N) (i : Fin 3) :
    ∃ part : Finset (Fin N × Fin 3),
      ((⋃ e ∈ part, (D.tile e.1).edge e.2)
          = segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
      ∧ (∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
          ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
      ∧ ∑ e ∈ part, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
          = edist (D.target.pts i) (D.target.pts (i + 1)) := by
  classical
  obtain ⟨f, c, hf, hle, hi, hi1, hi2⟩ := exists_supporting D.target i
  obtain ⟨part, hpart⟩ := hasEdgeChains_edge D i
  have hS : {x ∈ D.target.carrier | f x = c}
      = segment ℝ (D.target.pts i) (D.target.pts (i + 1)) :=
    target_contact_side D.target f c hle hi hi1 hi2
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2
      ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
    intro e he y hy
    rw [← hpart]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  have hlineE : ∀ e ∈ part, ∀ y ∈ (D.tile e.1).edge e.2, f y = c := by
    intro e he y hy
    have h1 : y ∈ {x ∈ D.target.carrier | f x = c} := by
      rw [hS]; exact hsub e he hy
    exact h1.2
  have hleT : ∀ e : Fin N × Fin 3, ∀ y ∈ (D.tile e.1).carrier, f y ≤ c :=
    fun e y hy => hle y (tile_subset_target D e.1 hy)
  have hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton :=
    fun e₁ h₁ e₂ h₂ hne => D.sameside_edges_subsingleton f c hf hne
      (hleT e₁) (hleT e₂) (hlineE e₁ h₁) (hlineE e₂ h₂)
  refine ⟨part, hpart, hdisj, ?_⟩
  have hsum := sum_hausdorff_of_partition part (fun e => (D.tile e.1).edge e.2)
    (segment ℝ (D.target.pts i) (D.target.pts (i + 1))) ∅ Set.finite_empty
    (fun e _ => ((D.tile e.1).isClosed_edge e.2).measurableSet)
    hdisj hsub
    (by
      intro x hx
      rw [← hpart] at hx
      exact hx.1)
  calc ∑ e ∈ part, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = ∑ e ∈ part,
          (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
            ((D.tile e.1).edge e.2) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        exact ((D.tile e.1).hausdorff_edge e.2).symm
    _ = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
          (segment ℝ (D.target.pts i) (D.target.pts (i + 1))) := hsum
    _ = edist (D.target.pts i) (D.target.pts (i + 1)) :=
        MeasureTheory.hausdorffMeasure_segment _ _
theorem Dissection.side_walk {N : ℕ} (D : Dissection N) (i : Fin 3) :
    ∃ part : Finset (Fin N × Fin 3),
      ((⋃ e ∈ part, (D.tile e.1).edge e.2)
          = segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
      ∧ (∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
          ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
      ∧ ∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
          = dist (D.target.pts i) (D.target.pts (i + 1)) := by
  obtain ⟨part, hcov, hdisj, hsum⟩ := D.side_partition i
  refine ⟨part, hcov, hdisj, ?_⟩
  have h1 : ENNReal.ofReal
        (∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist (D.target.pts i) (D.target.pts (i + 1))) := by
    calc ENNReal.ofReal
          (∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
        = ∑ e ∈ part,
            ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) :=
          ENNReal.ofReal_sum_of_nonneg (fun e _ => dist_nonneg)
      _ = ∑ e ∈ part, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) :=
          Finset.sum_congr rfl fun e _ => (edist_dist _ _).symm
      _ = edist (D.target.pts i) (D.target.pts (i + 1)) := hsum
      _ = ENNReal.ofReal (dist (D.target.pts i) (D.target.pts (i + 1))) := edist_dist _ _
  exact (ENNReal.ofReal_eq_ofReal_iff
    (Finset.sum_nonneg fun e _ => dist_nonneg) dist_nonneg).mp h1
theorem sum_three_values {ι : Type*} (s : Finset ι) (len : ι → ℝ) (a b c : ℝ)
    (h : ∀ e ∈ s, len e = a ∨ len e = b ∨ len e = c) :
    ∃ P Q R : ℕ, ((P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c = ∑ e ∈ s, len e)
      ∧ P + Q + R = s.card := by
  classical
  refine ⟨(s.filter fun e => len e = a).card,
          (s.filter fun e => ¬ len e = a ∧ len e = b).card,
          (s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card, ?_, ?_⟩
  · have hsplit1 := Finset.sum_filter_add_sum_filter_not s (fun e => len e = a) len
    have hsplit2 := Finset.sum_filter_add_sum_filter_not
      (s.filter fun e => ¬ len e = a) (fun e => len e = b) len
    rw [Finset.filter_filter, Finset.filter_filter] at hsplit2
    have hA : ∑ e ∈ s.filter (fun e => len e = a), len e
        = ((s.filter fun e => len e = a).card : ℝ) * a := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
        Finset.sum_const, nsmul_eq_mul]
    have hB : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ len e = b), len e
        = ((s.filter fun e => ¬ len e = a ∧ len e = b).card : ℝ) * b := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2.2),
        Finset.sum_const, nsmul_eq_mul]
    have hC : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ ¬ len e = b), len e
        = ((s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card : ℝ) * c := by
      rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
      have hmem := Finset.mem_filter.mp he
      rcases h e hmem.1 with h' | h' | h'
      · exact absurd h' hmem.2.1
      · exact absurd h' hmem.2.2
      · exact h'
    rw [hA] at hsplit1
    rw [hB, hC] at hsplit2
    linarith [hsplit1, hsplit2]
  · have h1 := Finset.card_filter_add_card_filter_not
      (s := s) (p := fun e => len e = a)
    have h2 := Finset.card_filter_add_card_filter_not
      (s := s.filter fun e => ¬ len e = a) (p := fun e => len e = b)
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    omega
theorem Dissection.side_walk_abc {N : ℕ} (D : Dissection N) (i : Fin 3) (a b c : ℝ)
    (habc : ∀ (j : Fin N) (k : Fin 3),
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = a
      ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = b
      ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = c) :
    ∃ P Q R : ℕ, (P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c
      = dist (D.target.pts i) (D.target.pts (i + 1)) ∧ P + Q + R ≤ 3 * N := by
  classical
  obtain ⟨part, -, -, hsum⟩ := D.side_walk i
  obtain ⟨P, Q, R, hPQR, hcard⟩ := sum_three_values part
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) a b c
    (fun e _ => habc e.1 e.2)
  refine ⟨P, Q, R, by rw [hPQR, hsum], ?_⟩
  have hle : part.card ≤ Fintype.card (Fin N × Fin 3) := Finset.card_le_univ part
  simp only [Fintype.card_prod, Fintype.card_fin] at hle
  omega
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
def Tri.Congruent (T U : Tri) : Prop :=
  ∃ (f : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3)), ∀ k, f (T.pts k) = U.pts (σ k)
theorem Tri.Congruent.symm {T U : Tri} (h : T.Congruent U) : U.Congruent T := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨f.symm, σ.symm, fun k => ?_⟩
  have hk := hf (σ.symm k)
  rw [Equiv.apply_symm_apply] at hk
  rw [← hk, IsometryEquiv.symm_apply_apply]
theorem Tri.Congruent.dist_eq {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts (σ i)) (U.pts (σ j)) := by
  obtain ⟨f, σ, hf⟩ := h
  exact ⟨σ, fun i j => by rw [← hf i, ← hf j, f.dist_eq]⟩
theorem Tri.det_pos_or_neg (T : Tri) : 0 < T.det ∨ T.det < 0 :=
  (lt_or_gt_of_ne T.det_ne_zero).symm
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
end Erdos634.AreaDet
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
namespace Erdos634.Geometry
noncomputable def Tri.angleAt (T : Tri) (k : Fin 3) : ℝ :=
  cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
noncomputable def Tri.oppLen (T : Tri) (k : Fin 3) : ℝ :=
  dist (T.pts (k + 1)) (T.pts (k + 2))
theorem Tri.oppLen_pos (T : Tri) (k : Fin 3) : 0 < T.oppLen k := by
  unfold Tri.oppLen
  apply dist_pos.mpr
  intro h
  have := T.indep.injective h
  revert this; fin_cases k <;> decide
end Erdos634.Geometry
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


namespace OMA.E634EqRat

open Erdos634.Geometry

private lemma abs_det_eq_k (T : Tri) (k : Fin 3) :
    |T.det| = T.oppLen (k + 1) * T.oppLen (k + 2) * Real.sin (T.angleAt k) := by
  have hang : T.angleAt k =
      InnerProductGeometry.angle (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k) := rfl
  have hk1 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have hk2 : k + 1 + 2 = k := by fin_cases k <;> rfl
  have hk3 : k + 2 + 1 = k := by fin_cases k <;> rfl
  have hk4 : k + 2 + 2 = k + 1 := by fin_cases k <;> rfl
  have h1 : T.oppLen (k + 1) = ‖T.pts (k + 2) - T.pts k‖ := by
    unfold Tri.oppLen; rw [hk1, hk2, dist_eq_norm]
  have h2 : T.oppLen (k + 2) = ‖T.pts (k + 1) - T.pts k‖ := by
    unfold Tri.oppLen; rw [hk3, hk4, dist_comm, dist_eq_norm]
  have hsin := InnerProductGeometry.sin_angle_mul_norm_mul_norm
    (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k)
  have hdet : T.det = cross (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k) := (T.det_cyclic k).symm
  have hid : inner ℝ (T.pts (k + 1) - T.pts k) (T.pts (k + 1) - T.pts k)
        * inner ℝ (T.pts (k + 2) - T.pts k) (T.pts (k + 2) - T.pts k)
      - inner ℝ (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k)
        * inner ℝ (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k) = T.det ^ 2 := by
    rw [hdet]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, cross]
    ring
  rw [← Real.sqrt_sq_eq_abs, ← hid, ← hsin, hang, h1, h2]
  ring

private lemma lawSin (T : Tri) (i j : Fin 3) :
    Real.sin (T.angleAt i) * T.oppLen j = Real.sin (T.angleAt j) * T.oppLen i := by
  have hprod : ∀ k : Fin 3,
      T.oppLen k * |T.det| = (T.oppLen 0 * T.oppLen 1 * T.oppLen 2) * Real.sin (T.angleAt k) := by
    intro k
    rw [abs_det_eq_k T k]
    fin_cases k <;> simp [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
      show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
      show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] <;> ring
  have hP : 0 < T.oppLen 0 * T.oppLen 1 * T.oppLen 2 :=
    mul_pos (mul_pos (T.oppLen_pos 0) (T.oppLen_pos 1)) (T.oppLen_pos 2)
  have hi := hprod i
  have hj := hprod j
  have h1 : (T.oppLen 0 * T.oppLen 1 * T.oppLen 2) *
      (Real.sin (T.angleAt i) * T.oppLen j - Real.sin (T.angleAt j) * T.oppLen i) = 0 := by
    calc _ = ((T.oppLen 0 * T.oppLen 1 * T.oppLen 2) * Real.sin (T.angleAt i)) * T.oppLen j -
             ((T.oppLen 0 * T.oppLen 1 * T.oppLen 2) * Real.sin (T.angleAt j)) * T.oppLen i := by ring
      _ = (T.oppLen i * |T.det|) * T.oppLen j - (T.oppLen j * |T.det|) * T.oppLen i := by rw [← hi, ← hj]
      _ = 0 := by ring
  linarith [(mul_eq_zero.mp h1).resolve_left hP.ne']

private lemma abs_det_target {N : ℕ} (D : CongruentDissection N) :
    |D.target.det| = (N : ℝ) * |D.model.det| := by
  have hdt : ∀ T : Tri, Erdos634.AreaDet.detTri T = T.det := fun T => by
    rw [Erdos634.AreaDet.detTri_eq]; unfold Tri.det; ring
  have hv := Erdos634.CongruentArea.congruentDissection_volume_target D
  rw [Erdos634.AreaDet.volume_eq_det_mul, Erdos634.AreaDet.volume_eq_det_mul, hdt, hdt] at hv
  set S := MeasureTheory.volume Erdos634.AreaDet.stdCarrier
  have hB : ENNReal.ofReal |D.model.det| ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact abs_pos.mpr D.model.det_ne_zero
  have hS0 : S ≠ 0 := by
    have hp := D.model.volume_pos
    rw [Erdos634.AreaDet.volume_eq_det_mul, hdt] at hp
    change 0 < ENNReal.ofReal |D.model.det| * S at hp
    intro h; rw [h, mul_zero] at hp; exact lt_irrefl _ hp
  have hST : S ≠ ⊤ := by
    have hf := D.model.volume_ne_top
    rw [Erdos634.AreaDet.volume_eq_det_mul, hdt] at hf
    change ENNReal.ofReal |D.model.det| * S ≠ ⊤ at hf
    intro h; apply hf; rw [h]; exact ENNReal.mul_top hB
  have hpos : 0 < S.toReal := ENNReal.toReal_pos hS0 hST
  have hr := congrArg ENNReal.toReal hv
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_natCast] at hr
  have : (|D.target.det| - (N : ℝ) * |D.model.det|) * S.toReal = 0 := by linear_combination hr
  have := (mul_eq_zero.mp this).resolve_right hpos.ne'
  linarith

private lemma fin3_others (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (σ (k + 1) = σ k + 1 ∧ σ (k + 2) = σ k + 2) ∨
    (σ (k + 1) = σ k + 2 ∧ σ (k + 2) = σ k + 1) := by
  have h1 : σ (k + 1) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
  have h2 : σ (k + 2) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
  have h3 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne (by fin_cases k <;> decide)
  generalize σ k = x at h1 h2
  generalize σ (k + 1) = y at h1 h3
  generalize σ (k + 2) = z at h2 h3
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all

/-- Common geometric reduction: equilateral target T tiled by p tiles with angles (θ0, θ1, θ2). -/
private lemma eq_tile_master {p : ℕ} (D : CongruentDissection p)
    (hEq : ∀ k, D.target.angleAt k = Real.pi / 3)
    {θ0 θ1 θ2 : ℝ} (σ : Equiv.Perm (Fin 3))
    (h0 : D.model.angleAt (σ 0) = θ0) (h1 : D.model.angleAt (σ 1) = θ1)
    (h2 : D.model.angleAt (σ 2) = θ2)
    (hs2 : 0 < Real.sin θ2) :
    ∃ (Y : ℝ) (P Q R : ℕ), 0 < Y ∧
      Y = (P : ℝ) * Real.sin θ0 + (Q : ℝ) * Real.sin θ1 + (R : ℝ) * Real.sin θ2 ∧
      Y ^ 2 * (Real.sqrt 3 / 2) = (p : ℝ) * (Real.sin θ0 * Real.sin θ1 * Real.sin θ2) := by
  set X : ℝ := D.target.oppLen 0
  have hX_pos : 0 < X := D.target.oppLen_pos 0
  have hs60 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have hs60_pos : 0 < Real.sin (Real.pi / 3) := by rw [hs60]; positivity
  have hX1 : D.target.oppLen 1 = X := by
    have hl := lawSin D.target 0 1
    rw [hEq 0, hEq 1] at hl
    exact mul_left_cancel₀ hs60_pos.ne' hl
  have hX2 : D.target.oppLen 2 = X := by
    have hl := lawSin D.target 0 2
    rw [hEq 0, hEq 2] at hl
    exact mul_left_cancel₀ hs60_pos.ne' hl
  set a : ℝ := D.model.oppLen (σ 0)
  set b : ℝ := D.model.oppLen (σ 1)
  set c : ℝ := D.model.oppLen (σ 2)
  set R0 : ℝ := c / Real.sin θ2
  have hR0_pos : 0 < R0 := div_pos (D.model.oppLen_pos (σ 2)) hs2
  have hc_eq : c = R0 * Real.sin θ2 := by dsimp [R0]; field_simp [hs2.ne']
  have ha_eq : a = R0 * Real.sin θ0 := by
    have hl := lawSin D.model (σ 0) (σ 2)
    rw [h0, h2] at hl
    change Real.sin θ0 * c = Real.sin θ2 * a at hl
    rw [hc_eq] at hl
    have : Real.sin θ2 * (a - R0 * Real.sin θ0) = 0 := by linarith
    linarith [(mul_eq_zero.mp this).resolve_left hs2.ne']
  have hb_eq : b = R0 * Real.sin θ1 := by
    have hl := lawSin D.model (σ 1) (σ 2)
    rw [h1, h2] at hl
    change Real.sin θ1 * c = Real.sin θ2 * b at hl
    rw [hc_eq] at hl
    have : Real.sin θ2 * (b - R0 * Real.sin θ1) = 0 := by linarith
    linarith [(mul_eq_zero.mp this).resolve_left hs2.ne']
  have hmodel_opp : ∀ j : Fin 3, D.model.oppLen j = a ∨ D.model.oppLen j = b ∨ D.model.oppLen j = c := by
    intro j; obtain ⟨u, hu⟩ := σ.surjective j; rw [← hu]
    fin_cases u
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have habc : ∀ (i : Fin p) (u : Fin 3),
      dist ((D.tile i).pts u) ((D.tile i).pts (u + 1)) = a ∨
      dist ((D.tile i).pts u) ((D.tile i).pts (u + 1)) = b ∨
      dist ((D.tile i).pts u) ((D.tile i).pts (u + 1)) = c := by
    intro i u
    obtain ⟨τ, hdist⟩ := (D.tiles_congruent i).dist_eq
    have hne : τ u ≠ τ (u + 1) := τ.injective.ne (by fin_cases u <;> decide)
    have hpair : ∃ r : Fin 3, dist (D.model.pts (τ u)) (D.model.pts (τ (u + 1))) = D.model.oppLen r := by
      generalize τ u = x at hne
      generalize τ (u + 1) = y at hne
      fin_cases x <;> fin_cases y <;> simp_all
      · exact ⟨2, rfl⟩
      · exact ⟨1, dist_comm _ _⟩
      · exact ⟨2, dist_comm _ _⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, dist_comm _ _⟩
    obtain ⟨r, hr⟩ := hpair
    rw [hdist u (u + 1), hr]
    exact hmodel_opp r
  obtain ⟨P, Q, R, hPQR, _⟩ := D.toDissection.side_walk_abc 1 a b c habc
  have hX_side : dist (D.target.pts 1) (D.target.pts (1 + 1)) = X := rfl
  rw [hX_side] at hPQR
  set Y : ℝ := X / R0
  have hY_pos : 0 < Y := div_pos hX_pos hR0_pos
  have hY_comb : Y = (P : ℝ) * Real.sin θ0 + (Q : ℝ) * Real.sin θ1 + (R : ℝ) * Real.sin θ2 := by
    dsimp [Y]
    rw [← hPQR, ha_eq, hb_eq, hc_eq]
    field_simp [hR0_pos.ne']
  have hMdet : |D.model.det| = R0 ^ 2 * (Real.sin θ0 * Real.sin θ1 * Real.sin θ2) := by
    have hd := abs_det_eq_k D.model (σ 1)
    rw [h1] at hd
    have h12 : D.model.oppLen (σ 1 + 1) * D.model.oppLen (σ 1 + 2) = a * c := by
      rcases fin3_others σ 1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [show (1 : Fin 3) + 1 = 2 from rfl] at e1
        rw [show (1 : Fin 3) + 2 = 0 from rfl] at e2
        rw [← e1, ← e2]; show c * a = a * c; ring
      · rw [show (1 : Fin 3) + 1 = 2 from rfl] at e1
        rw [show (1 : Fin 3) + 2 = 0 from rfl] at e2
        rw [← e1, ← e2]
    rw [h12, ha_eq, hc_eq] at hd
    linarith
  have hTdet : |D.target.det| = X ^ 2 * (Real.sqrt 3 / 2) := by
    have hd := abs_det_eq_k D.target 0
    rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hX1, hX2, hEq 0, hs60] at hd
    linarith
  have harea := abs_det_target D
  rw [hTdet, hMdet] at harea
  have hY_area : Y ^ 2 * (Real.sqrt 3 / 2) = (p : ℝ) * (Real.sin θ0 * Real.sin θ1 * Real.sin θ2) := by
    have hX_eq : X = Y * R0 := by dsimp [Y]; field_simp [hR0_pos.ne']
    rw [hX_eq] at harea
    have h1 : R0 ^ 2 * (Y ^ 2 * (Real.sqrt 3 / 2) - (p : ℝ) * (Real.sin θ0 * Real.sin θ1 * Real.sin θ2)) = 0 := by
      linarith
    linarith [(mul_eq_zero.mp h1).resolve_left (sq_pos_of_pos hR0_pos).ne']
  exact ⟨Y, P, Q, R, hY_pos, hY_comb, hY_area⟩

/-- Elementary irrationality: if prime p divides n but p^2 does not, then n is not a rational square. -/
private lemma rat_sq_ne_of_prime_dvd {n p : ℕ} (hp : p.Prime) (hd : p ∣ n) (hnd : ¬ p * p ∣ n)
    (q : ℚ) : q ^ 2 ≠ (n : ℚ) := by
  intro hq
  have hden0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  have hnum : (q.num : ℚ) ^ 2 = (n : ℚ) * (q.den : ℚ) ^ 2 := by
    have hqdef : (q.num : ℚ) = q * (q.den : ℚ) := by
      have h1 := Rat.num_div_den q
      rw [← div_eq_iff hden0]
      exact h1
    calc (q.num : ℚ) ^ 2 = q ^ 2 * (q.den : ℚ) ^ 2 := by rw [hqdef]; ring
      _ = (n : ℚ) * (q.den : ℚ) ^ 2 := by rw [hq]
  have hz : q.num ^ 2 = (n : ℤ) * (q.den : ℤ) ^ 2 := by exact_mod_cast hnum
  have hnat : q.num.natAbs ^ 2 = n * q.den ^ 2 := by
    have h1 : ((q.num.natAbs ^ 2 : ℕ) : ℤ) = ((n * q.den ^ 2 : ℕ) : ℤ) := by
      simp only [Nat.cast_mul, Nat.cast_pow, Int.natCast_natAbs, sq_abs]
      exact hz
    exact_mod_cast h1
  have hp_a2 : p ∣ q.num.natAbs ^ 2 := dvd_trans hd ⟨q.den ^ 2, hnat⟩
  have hp_a : p ∣ q.num.natAbs := hp.dvd_of_dvd_pow hp_a2
  obtain ⟨k, hk⟩ := hp_a
  obtain ⟨m, hm⟩ := hd
  have hpm : ¬ p ∣ m := fun h => hnd (by obtain ⟨r, rfl⟩ := h; exact ⟨r, by rw [hm]; ring⟩)
  have hmb : p ∣ m * q.den ^ 2 := by
    refine ⟨k ^ 2, ?_⟩
    apply mul_left_cancel₀ hp.ne_zero
    calc p * (m * q.den ^ 2) = n * q.den ^ 2 := by rw [hm]; ring
      _ = q.num.natAbs ^ 2 := hnat.symm
      _ = p * (p * k ^ 2) := by rw [hk]; ring
  have hp_b2 : p ∣ q.den ^ 2 := (hp.dvd_mul.mp hmb).resolve_left hpm
  have hp_b : p ∣ q.den := hp.dvd_of_dvd_pow hp_b2
  have hg := Nat.dvd_gcd ⟨k, hk⟩ hp_b
  rw [q.reduced] at hg
  exact absurd (Nat.le_of_dvd Nat.zero_lt_one hg) (by have := hp.two_le; omega)

private lemma real_rat_sq_ne {n p : ℕ} (hp : p.Prime) (hd : p ∣ n) (hnd : ¬ p * p ∣ n)
    (q : ℚ) : (q : ℝ) ^ 2 ≠ (n : ℝ) := fun h =>
  rat_sq_ne_of_prime_dvd hp hd hnd q (by exact_mod_cast h)

/-- Elementary biquadratic elimination over a subfield F of ℝ. -/
private lemma quad_sq_mem_F (F : Set ℝ)
    (hadd : ∀ x ∈ F, ∀ y ∈ F, x + y ∈ F)
    (hsub : ∀ x ∈ F, ∀ y ∈ F, x - y ∈ F)
    (hmul : ∀ x ∈ F, ∀ y ∈ F, x * y ∈ F)
    (hdiv : ∀ x ∈ F, ∀ y ∈ F, x / y ∈ F)
    (hneg : ∀ x ∈ F, -x ∈ F)
    (hnat : ∀ n : ℕ, (n : ℝ) ∈ F)
    {u v t d r1 r2 a1 a2 : ℝ}
    (hu : u ∈ F) (hv : v ∈ F) (ht : t ∈ F) (hd : d ∈ F)
    (ha1 : a1 ∈ F) (ha2 : a2 ∈ F)
    (hr1 : r1 ^ 2 = a1) (hr2 : r2 ^ 2 = a2)
    (hn1 : r1 ∉ F) (hn2 : r2 ∉ F) (hn12 : r1 * r2 ∉ F)
    (hsq : (u + v * r1 + t * r2) ^ 2 = d) :
    (v = 0 ∧ t = 0) ∨ (u = 0 ∧ t = 0) ∨ (u = 0 ∧ v = 0) := by
  have h2 : (2 : ℝ) ∈ F := by simpa using hnat 2
  have h4 : (4 : ℝ) ∈ F := by simpa using hnat 4
  have h8 : (8 : ℝ) ∈ F := by simpa using hnat 8
  have hu2 : u ^ 2 ∈ F := by rw [sq]; exact hmul _ hu _ hu
  have hv2 : v ^ 2 ∈ F := by rw [sq]; exact hmul _ hv _ hv
  have ht2 : t ^ 2 ∈ F := by rw [sq]; exact hmul _ ht _ ht
  set E : ℝ := d - u ^ 2 - v ^ 2 * a1 - t ^ 2 * a2
  have hE : E ∈ F :=
    hsub _ (hsub _ (hsub _ hd _ hu2) _ (hmul _ hv2 _ ha1)) _ (hmul _ ht2 _ ha2)
  have hlin : 2 * u * v * r1 + 2 * u * t * r2 = E - 2 * v * t * (r1 * r2) := by
    have : (u + v * r1 + t * r2) ^ 2 =
        u ^ 2 + v ^ 2 * r1 ^ 2 + t ^ 2 * r2 ^ 2 +
        2 * u * v * r1 + 2 * u * t * r2 + 2 * v * t * (r1 * r2) := by ring
    rw [hr1, hr2] at this
    dsimp [E]; linarith
  have hsq2 : (8 * u ^ 2 + 4 * E) * v * t * (r1 * r2) =
      E ^ 2 + 4 * v ^ 2 * t ^ 2 * a1 * a2 - 4 * u ^ 2 * (v ^ 2 * a1 + t ^ 2 * a2) := by
    have h := congrArg (fun x : ℝ => x ^ 2) hlin
    have hL : (2 * u * v * r1 + 2 * u * t * r2) ^ 2 =
        4 * u ^ 2 * (v ^ 2 * r1 ^ 2 + t ^ 2 * r2 ^ 2) + 8 * u ^ 2 * v * t * (r1 * r2) := by ring
    have hR : (E - 2 * v * t * (r1 * r2)) ^ 2 =
        E ^ 2 + 4 * v ^ 2 * t ^ 2 * (r1 ^ 2 * r2 ^ 2) - 4 * E * v * t * (r1 * r2) := by ring
    rw [hL, hR, hr1, hr2] at h
    linarith
  have hRHS_F : E ^ 2 + 4 * v ^ 2 * t ^ 2 * a1 * a2 - 4 * u ^ 2 * (v ^ 2 * a1 + t ^ 2 * a2) ∈ F := by
    have hE2 : E ^ 2 ∈ F := by rw [sq]; exact hmul _ hE _ hE
    exact hsub _ (hadd _ hE2 _ (hmul _ (hmul _ (hmul _ (hmul _ h4 _ hv2) _ ht2) _ ha1) _ ha2))
      _ (hmul _ (hmul _ h4 _ hu2) _ (hadd _ (hmul _ hv2 _ ha1) _ (hmul _ ht2 _ ha2)))
  have hcoeff_F : (8 * u ^ 2 + 4 * E) * v * t ∈ F :=
    hmul _ (hmul _ (hadd _ (hmul _ h8 _ hu2) _ (hmul _ h4 _ hE)) _ hv) _ ht
  have hcoeff0 : (8 * u ^ 2 + 4 * E) * v * t = 0 := by
    by_contra hne
    apply hn12
    have : r1 * r2 = (E ^ 2 + 4 * v ^ 2 * t ^ 2 * a1 * a2 - 4 * u ^ 2 * (v ^ 2 * a1 + t ^ 2 * a2)) /
        ((8 * u ^ 2 + 4 * E) * v * t) := by
      rw [eq_div_iff hne]; linarith
    rw [this]
    exact hdiv _ hRHS_F _ hcoeff_F
  have hvt0 : v = 0 ∨ t = 0 := by
    rcases mul_eq_zero.mp hcoeff0 with h1 | ht0
    · rcases mul_eq_zero.mp h1 with hE2 | hv0
      · have hEeq : E = -2 * u ^ 2 := by linarith
        rw [hcoeff0, zero_mul, hEeq] at hsq2
        have hfac : 4 * (u ^ 2 - v ^ 2 * a1) * (u ^ 2 - t ^ 2 * a2) = 0 := by linarith
        rcases mul_eq_zero.mp hfac with h4u | ht2
        · rcases mul_eq_zero.mp h4u with h40 | hv2
          · norm_num at h40
          · left
            by_contra hvne
            have hsq1 : r1 ^ 2 = (u / v) ^ 2 := by rw [hr1, div_pow, eq_div_iff (pow_ne_zero 2 hvne)]; linarith
            rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq1 with hpos | hneg'
            · exact hn1 (hpos ▸ hdiv _ hu _ hv)
            · exact hn1 (hneg' ▸ hneg _ (hdiv _ hu _ hv))
        · right
          by_contra htne
          have hsq2' : r2 ^ 2 = (u / t) ^ 2 := by rw [hr2, div_pow, eq_div_iff (pow_ne_zero 2 htne)]; linarith
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2' with hpos | hneg'
          · exact hn2 (hpos ▸ hdiv _ hu _ ht)
          · exact hn2 (hneg' ▸ hneg _ (hdiv _ hu _ ht))
      · exact Or.inl hv0
    · exact Or.inr ht0
  rcases hvt0 with rfl | rfl
  · simp only [mul_zero, zero_mul, zero_add, sub_zero] at hlin
    have hut0 : 2 * u * t = 0 := by
      by_contra hne
      apply hn2
      have : r2 = E / (2 * u * t) := by rw [eq_div_iff hne]; linarith
      rw [this]
      exact hdiv _ hE _ (hmul _ (hmul _ h2 _ hu) _ ht)
    rcases mul_eq_zero.mp hut0 with h2u | ht0
    · rcases mul_eq_zero.mp h2u with h20 | hu0
      · norm_num at h20
      · exact Or.inr (Or.inr ⟨hu0, rfl⟩)
    · exact Or.inl ⟨rfl, ht0⟩
  · simp only [mul_zero, zero_mul, add_zero, sub_zero] at hlin
    have huv0 : 2 * u * v = 0 := by
      by_contra hne
      apply hn1
      have : r1 = E / (2 * u * v) := by rw [eq_div_iff hne]; linarith
      rw [this]
      exact hdiv _ hE _ (hmul _ (hmul _ h2 _ hu) _ hv)
    rcases mul_eq_zero.mp huv0 with h2u | hv0
    · rcases mul_eq_zero.mp h2u with h20 | hu0
      · norm_num at h20
      · exact Or.inr (Or.inl ⟨hu0, rfl⟩)
    · exact Or.inl ⟨hv0, rfl⟩

/-- The subfield Q(sqrt 5) inside R. -/
private def Q5 : Set ℝ := {x : ℝ | ∃ a b : ℚ, x = (a : ℝ) + (b : ℝ) * Real.sqrt 5}

private lemma q5_eq_zero {a b : ℚ} (h : (a : ℝ) + (b : ℝ) * Real.sqrt 5 = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb; simp at h; exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have hsq : ((-a / b : ℚ) : ℝ) ^ 2 = (5 : ℝ) := by
      have h1 : Real.sqrt 5 = -(a : ℝ) / (b : ℝ) := by
        rw [eq_div_iff hbR]; linarith
      push_cast
      rw [← h1, Real.sq_sqrt (by norm_num)]
    exact real_rat_sq_ne (n := 5) (p := 5) (by decide) (dvd_refl 5) (by decide) (-a / b) hsq

private lemma q5_eq_iff {a1 b1 a2 b2 : ℚ}
    (h : (a1 : ℝ) + (b1 : ℝ) * Real.sqrt 5 = (a2 : ℝ) + (b2 : ℝ) * Real.sqrt 5) :
    a1 = a2 ∧ b1 = b2 := by
  have h0 : ((a1 - a2 : ℚ) : ℝ) + ((b1 - b2 : ℚ) : ℝ) * Real.sqrt 5 = 0 := by push_cast; linarith
  obtain ⟨ha, hb⟩ := q5_eq_zero h0
  exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp hb⟩

private lemma q5_add : ∀ x ∈ Q5, ∀ y ∈ Q5, x + y ∈ Q5 := by
  rintro _ ⟨a1, b1, rfl⟩ _ ⟨a2, b2, rfl⟩
  exact ⟨a1 + a2, b1 + b2, by push_cast; ring⟩

private lemma q5_sub : ∀ x ∈ Q5, ∀ y ∈ Q5, x - y ∈ Q5 := by
  rintro _ ⟨a1, b1, rfl⟩ _ ⟨a2, b2, rfl⟩
  exact ⟨a1 - a2, b1 - b2, by push_cast; ring⟩

private lemma q5_neg : ∀ x ∈ Q5, -x ∈ Q5 := by
  rintro _ ⟨a, b, rfl⟩
  exact ⟨-a, -b, by push_cast; ring⟩

private lemma q5_mul : ∀ x ∈ Q5, ∀ y ∈ Q5, x * y ∈ Q5 := by
  rintro _ ⟨a1, b1, rfl⟩ _ ⟨a2, b2, rfl⟩
  refine ⟨a1 * a2 + 5 * b1 * b2, a1 * b2 + b1 * a2, ?_⟩
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  push_cast
  linear_combination (b1 : ℝ) * (b2 : ℝ) * h5

private lemma q5_div : ∀ x ∈ Q5, ∀ y ∈ Q5, x / y ∈ Q5 := by
  rintro _ ⟨a1, b1, rfl⟩ y ⟨a2, b2, rfl⟩
  by_cases hy : (a2 : ℝ) + (b2 : ℝ) * Real.sqrt 5 = 0
  · rw [hy, div_zero]; exact ⟨0, 0, by simp⟩
  · have hnorm_ne : (a2 : ℝ) ^ 2 - 5 * (b2 : ℝ) ^ 2 ≠ 0 := by
      intro h0
      by_cases hb : b2 = 0
      · subst hb; simp at h0; exact hy (by simp [h0])
      · have hbR : (b2 : ℝ) ≠ 0 := by exact_mod_cast hb
        have hsq : ((a2 / b2 : ℚ) : ℝ) ^ 2 = (5 : ℝ) := by
          push_cast; rw [div_pow, div_eq_iff (pow_ne_zero 2 hbR)]; linarith
        exact real_rat_sq_ne (n := 5) (p := 5) (by decide) (dvd_refl 5) (by decide) (a2 / b2) hsq
    set D : ℚ := a2 ^ 2 - 5 * b2 ^ 2
    have hDR : (D : ℝ) ≠ 0 := by simpa [D] using hnorm_ne
    refine ⟨(a1 * a2 - 5 * b1 * b2) / D, (b1 * a2 - a1 * b2) / D, ?_⟩
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    rw [div_eq_iff hy]
    push_cast [D]
    field_simp [hnorm_ne]
    linear_combination -((b1 : ℝ) * (a2 : ℝ) - (a1 : ℝ) * (b2 : ℝ)) * (b2 : ℝ) * h5

private lemma q5_nat (n : ℕ) : (n : ℝ) ∈ Q5 := ⟨n, 0, by simp⟩

private lemma sqrt3_not_Q5 : Real.sqrt 3 ∉ Q5 := by
  rintro ⟨a, b, hab⟩
  have hsq : (a : ℝ) ^ 2 + 5 * (b : ℝ) ^ 2 + (2 * (a : ℝ) * (b : ℝ)) * Real.sqrt 5 = (3 : ℝ) + 0 * Real.sqrt 5 := by
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h := congrArg (fun x : ℝ => x ^ 2) hab
    rw [h3] at h
    linear_combination -h - (b : ℝ) ^ 2 * h5
  have hsq' : ((a ^ 2 + 5 * b ^ 2 : ℚ) : ℝ) + ((2 * a * b : ℚ) : ℝ) * Real.sqrt 5 =
      ((3 : ℚ) : ℝ) + ((0 : ℚ) : ℝ) * Real.sqrt 5 := by push_cast; linarith
  obtain ⟨h1, h2⟩ := q5_eq_iff hsq'
  have hab0 : a = 0 ∨ b = 0 := by
    have : a * b = 0 := by linarith
    exact mul_eq_zero.mp this
  rcases hab0 with rfl | rfl
  · have hb2 : (5 * b) ^ 2 = (15 : ℚ) := by linarith
    exact rat_sq_ne_of_prime_dvd (n := 15) (p := 3) (by decide) (by decide) (by decide) (5 * b) hb2
  · have ha2 : a ^ 2 = (3 : ℚ) := by linarith
    exact rat_sq_ne_of_prime_dvd (n := 3) (p := 3) (by decide) (by decide) (by decide) a ha2

private lemma not_Q5_of_norm_not_sq {r : ℝ} {d e : ℚ}
    (hr : r ^ 2 = (d : ℝ) + (e : ℝ) * Real.sqrt 5)
    {N p : ℕ} (hN : d ^ 2 - 5 * e ^ 2 = (N : ℚ))
    (hp : p.Prime) (hd : p ∣ N) (hnd : ¬ p * p ∣ N) : r ∉ Q5 := by
  rintro ⟨a, b, hab⟩
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsq := congrArg (fun x : ℝ => x ^ 2) hab
  rw [hr] at hsq
  have hcomp : ((a ^ 2 + 5 * b ^ 2 : ℚ) : ℝ) + ((2 * a * b : ℚ) : ℝ) * Real.sqrt 5 =
      (d : ℝ) + (e : ℝ) * Real.sqrt 5 := by
    push_cast
    linear_combination -hsq - (b : ℝ) ^ 2 * h5
  obtain ⟨hd_eq, he_eq⟩ := q5_eq_iff hcomp
  have hnorm_sq : (a ^ 2 - 5 * b ^ 2) ^ 2 = (N : ℚ) := by
    rw [← hN, ← hd_eq, ← he_eq]; ring
  exact rat_sq_ne_of_prime_dvd hp hd hnd (a ^ 2 - 5 * b ^ 2) hnorm_sq

/-- Exact trig values for pi/5 and 2*pi/5. -/
private lemma trig_pi_div_five :
    Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 ∧
    Real.sin (Real.pi / 5) = Real.sqrt (10 - 2 * Real.sqrt 5) / 4 ∧
    Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 ∧
    Real.sin (2 * Real.pi / 5) = Real.sqrt (10 + 2 * Real.sqrt 5) / 4 := by
  have hpi := Real.pi_pos
  set c := Real.cos (Real.pi / 5)
  have h32 : Real.cos (3 * (Real.pi / 5)) = -Real.cos (2 * (Real.pi / 5)) := by
    rw [show 3 * (Real.pi / 5) = Real.pi - 2 * (Real.pi / 5) by ring, Real.cos_pi_sub]
  rw [Real.cos_three_mul, Real.cos_two_mul] at h32
  have hfac : (c + 1) * (4 * c ^ 2 - 2 * c - 1) = 0 := by dsimp [c]; linarith
  have hc_gt : (1 : ℝ) / 2 < c := by
    have hlt : Real.cos (Real.pi / 3) < Real.cos (Real.pi / 5) :=
      Real.strictAntiOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    rw [Real.cos_pi_div_three] at hlt
    exact hlt
  have hquad : 4 * c ^ 2 - 2 * c - 1 = 0 := (mul_eq_zero.mp hfac).resolve_left (by linarith)
  have hsq5 : (4 * c - 1) ^ 2 = 5 := by linarith
  have hc_eq : c = (1 + Real.sqrt 5) / 4 := by
    have h4c : 4 * c - 1 = Real.sqrt 5 := by
      have := congrArg Real.sqrt hsq5
      rwa [Real.sqrt_sq (by linarith)] at this
    linarith
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs1_pos : 0 ≤ Real.sin (Real.pi / 5) :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).le
  have hs1_sq : Real.sin (Real.pi / 5) ^ 2 = (10 - 2 * Real.sqrt 5) / 16 := by
    have hsc := Real.sin_sq_add_cos_sq (Real.pi / 5)
    change Real.sin (Real.pi / 5) ^ 2 + c ^ 2 = 1 at hsc
    rw [hc_eq] at hsc
    linear_combination hsc - (1 / 16 : ℝ) * hs5
  have hs1_eq : Real.sin (Real.pi / 5) = Real.sqrt (10 - 2 * Real.sqrt 5) / 4 := by
    have h := congrArg Real.sqrt hs1_sq
    rw [Real.sqrt_sq hs1_pos, Real.sqrt_div (by nlinarith [Real.sqrt_nonneg 5])] at h
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h16] at h
  have hc2_eq : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
    rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring, Real.cos_two_mul]
    change 2 * c ^ 2 - 1 = _
    rw [hc_eq]
    linear_combination (1 / 8 : ℝ) * hs5
  have hs2_pos : 0 ≤ Real.sin (2 * Real.pi / 5) :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).le
  have hs2_sq : Real.sin (2 * Real.pi / 5) ^ 2 = (10 + 2 * Real.sqrt 5) / 16 := by
    have hsc := Real.sin_sq_add_cos_sq (2 * Real.pi / 5)
    rw [hc2_eq] at hsc
    linear_combination hsc - (1 / 16 : ℝ) * hs5
  have hs2_eq : Real.sin (2 * Real.pi / 5) = Real.sqrt (10 + 2 * Real.sqrt 5) / 4 := by
    have h := congrArg Real.sqrt hs2_sq
    rw [Real.sqrt_sq hs2_pos, Real.sqrt_div (by positivity)] at h
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h16] at h
  exact ⟨hc_eq, hs1_eq, hc2_eq, hs2_eq⟩

private lemma tile3_or_tile4_contra {p : ℕ} (hp : 0 < p) {P Q R : ℕ} {ε : ℚ}
    (hε : ε = -1 ∨ ε = 1) {Y : ℝ} (hY_pos : 0 < Y)
    (hY_comb : 8 * Y = ((R : ℤ) - (P : ℤ) : ℝ) * (-(ε : ℝ) + Real.sqrt 5) +
        (4 * (Q : ℤ) : ℝ) * Real.sqrt 3 +
        ((P : ℤ) + (R : ℤ) : ℝ) * (Real.sqrt 3 * Real.sqrt (10 + 2 * (ε : ℝ) * Real.sqrt 5)))
    (hY_sq : (8 * Y) ^ 2 = (8 * (p : ℝ)) * (3 + (ε : ℝ) * Real.sqrt 5)) : False := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h10_nn : 0 ≤ 10 + 2 * (ε : ℝ) * Real.sqrt 5 := by
    rcases hε with rfl | rfl
    · have : Real.sqrt 5 < 3 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num
      push_cast; linarith
    · push_cast; positivity
  set w0 : ℝ := Real.sqrt (10 + 2 * (ε : ℝ) * Real.sqrt 5)
  have hw0_sq : w0 ^ 2 = 10 + 2 * (ε : ℝ) * Real.sqrt 5 := Real.sq_sqrt h10_nn
  set r1 : ℝ := Real.sqrt 3
  set r2 : ℝ := Real.sqrt 3 * w0
  have hr1_sq : r1 ^ 2 = 3 := h3
  have hr2_sq : r2 ^ 2 = (30 : ℚ) + ((6 * ε : ℚ) : ℝ) * Real.sqrt 5 := by
    dsimp [r2]; rw [mul_pow, h3, hw0_sq]; push_cast; ring
  have hr12_sq : (r1 * r2) ^ 2 = (90 : ℚ) + ((18 * ε : ℚ) : ℝ) * Real.sqrt 5 := by
    dsimp [r1, r2]
    have : (Real.sqrt 3 * (Real.sqrt 3 * w0)) ^ 2 = (Real.sqrt 3 ^ 2) ^ 2 * w0 ^ 2 := by ring
    rw [this, h3, hw0_sq]; push_cast; ring
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hn2 : r2 ∉ Q5 :=
    not_Q5_of_norm_not_sq hr2_sq (N := 720) (p := 5)
      (by linear_combination -180 * hε2) (by decide) (by decide) (by decide)
  have hn12 : r1 * r2 ∉ Q5 :=
    not_Q5_of_norm_not_sq hr12_sq (N := 6480) (p := 5)
      (by linear_combination -1620 * hε2) (by decide) (by decide) (by decide)
  set u : ℝ := ((R : ℤ) - (P : ℤ) : ℝ) * (-(ε : ℝ) + Real.sqrt 5)
  set v : ℝ := (4 * (Q : ℤ) : ℝ)
  set t : ℝ := ((P : ℤ) + (R : ℤ) : ℝ)
  have hu : u ∈ Q5 := ⟨-((R : ℤ) - (P : ℤ)) * ε, (R : ℤ) - (P : ℤ), by dsimp [u]; push_cast; ring⟩
  have hv : v ∈ Q5 := ⟨4 * (Q : ℤ), 0, by dsimp [v]; push_cast; ring⟩
  have ht : t ∈ Q5 := ⟨(P : ℤ) + (R : ℤ), 0, by dsimp [t]; push_cast; ring⟩
  have hd : (8 * (p : ℝ)) * (3 + (ε : ℝ) * Real.sqrt 5) ∈ Q5 :=
    ⟨24 * p, 8 * p * ε, by push_cast; ring⟩
  have ha1 : (3 : ℝ) ∈ Q5 := q5_nat 3
  have ha2 : ((30 : ℚ) : ℝ) + ((6 * ε : ℚ) : ℝ) * Real.sqrt 5 ∈ Q5 := ⟨30, 6 * ε, rfl⟩
  have hsq : (u + v * r1 + t * r2) ^ 2 = (8 * (p : ℝ)) * (3 + (ε : ℝ) * Real.sqrt 5) := by
    rw [← hY_comb]; exact hY_sq
  rcases quad_sq_mem_F Q5 q5_add q5_sub q5_mul q5_div q5_neg q5_nat hu hv ht hd ha1 ha2
      hr1_sq hr2_sq sqrt3_not_Q5 hn2 hn12 hsq with ⟨hv0, ht0⟩ | ⟨hu0, ht0⟩ | ⟨hu0, hv0⟩
  · -- v = 0 and t = 0: P + R = 0 in N -> P = 0, R = 0 -> u = 0 -> Y = 0!
    have hPR : P + R = 0 := by
      have : ((P + R : ℕ) : ℝ) = 0 := by push_cast; exact ht0
      exact_mod_cast this
    have hQ0 : Q = 0 := by
      have : (4 : ℝ) * (Q : ℝ) = 0 := by simpa [v] using hv0
      have hQr : (Q : ℝ) = 0 := by linarith
      exact_mod_cast hQr
    have hP0 : P = 0 := by omega
    have hR0 : R = 0 := by omega
    rw [hv0, ht0] at hY_comb
    dsimp [u] at hY_comb
    rw [hP0, hR0] at hY_comb
    simp at hY_comb
    linarith
  · -- u = 0 and t = 0: P + R = 0, so 8Y = 4Q * sqrt 3 -> 48 Q^2 = 8 p (3 + ε sqrt 5)!
    rw [hu0, ht0, zero_mul, zero_add, add_zero] at hsq
    have hQeq : ((3 * (4 * (Q : ℤ)) ^ 2 : ℚ) : ℝ) + ((0 : ℚ) : ℝ) * Real.sqrt 5 =
        ((24 * (p : ℚ) : ℚ) : ℝ) + ((8 * (p : ℚ) * ε : ℚ) : ℝ) * Real.sqrt 5 := by
      have h1 : (v * r1) ^ 2 = 3 * v ^ 2 := by rw [mul_pow, hr1_sq]; ring
      rw [h1] at hsq
      dsimp [v] at hsq
      push_cast at hsq ⊢; linarith
    obtain ⟨_, hcoeff5⟩ := q5_eq_iff hQeq
    have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
    have hε_ne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    have : 8 * (p : ℚ) * ε ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hp_ne) hε_ne
    exact this hcoeff5.symm
  · -- u = 0 and v = 0: so (t * r2)^2 = 8 p (3 + ε sqrt 5) -> t^2 * (30 + 6ε√5) = 24p + 8pε√5!
    rw [hu0, hv0, zero_mul, add_zero, zero_add] at hsq
    have hteq : ((30 * ((P : ℤ) + (R : ℤ)) ^ 2 : ℚ) : ℝ) +
        ((6 * ε * ((P : ℤ) + (R : ℤ)) ^ 2 : ℚ) : ℝ) * Real.sqrt 5 =
        ((24 * (p : ℚ) : ℚ) : ℝ) + ((8 * (p : ℚ) * ε : ℚ) : ℝ) * Real.sqrt 5 := by
      rw [mul_pow, hr2_sq] at hsq
      dsimp [t] at hsq
      push_cast at hsq ⊢
      linarith
    obtain ⟨h1, h2⟩ := q5_eq_iff hteq
    have h2' : 6 * (((P : ℤ) + (R : ℤ) : ℚ) ^ 2) = 8 * (p : ℚ) := by
      rcases hε with rfl | rfl <;> linarith
    have hp0 : (p : ℚ) = 0 := by linarith
    exact (by exact_mod_cast hp.ne' : (p : ℚ) ≠ 0) hp0

end OMA.E634EqRat

set_option maxHeartbeats 800000 in
theorem OMA.solution : OMA.R_erdos_634_R1_H2_R1_H4_R1.H1 := by
  intro p hp hp3 T Ts hc hd hu t A B hA hB _hns hEq hsh
  let D := OMA.E634S.mk T Ts hc hd hu t
  have hAD : ∀ k, D.target.angleAt k = Real.pi / 3 := fun k =>
    (OMA.E634S.target_angleAt T Ts hc hd hu t k).trans ((hA k).symm.trans (hEq k))
  have hBD : ∀ k, D.model.angleAt k = B k := fun k =>
    (OMA.E634S.model_angleAt T Ts hc hd hu t k).trans (hB k).symm
  obtain ⟨σ, hcase⟩ := hsh
  rcases hcase with hT1 | hT2 | hT3 | hT4
  · -- Tile 1: (pi/6, pi/6, 2pi/3).
    have hb0 : D.model.angleAt (σ 0) = Real.pi / 6 := (hBD _).trans (by simpa using congrFun hT1 0)
    have hb1 : D.model.angleAt (σ 1) = Real.pi / 6 := (hBD _).trans (by simpa using congrFun hT1 1)
    have hb2 : D.model.angleAt (σ 2) = 2 * Real.pi / 3 := (hBD _).trans (by simpa using congrFun hT1 2)
    have hs2 : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
    obtain ⟨Y, P, Q, R, hY_pos, hY_comb, hY_area⟩ :=
      OMA.E634EqRat.eq_tile_master D hAD σ hb0 hb1 hb2 (by rw [hs2]; positivity)
    rw [Real.sin_pi_div_six, hs2] at hY_comb hY_area
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hY_sq : (2 * Y) ^ 2 = (p : ℝ) := by
      have : Real.sqrt 3 * ((2 * Y) ^ 2 - (p : ℝ)) = 0 := by linarith
      linarith [(mul_eq_zero.mp this).resolve_left (by positivity)]
    have h2Y : 2 * Y = ((P + Q : ℕ) : ℝ) + (R : ℝ) * Real.sqrt 3 := by push_cast; linarith
    rw [h2Y] at hY_sq
    have hexp : (((P + Q : ℕ) ^ 2 + 3 * R ^ 2 : ℕ) : ℝ) + (2 * ((P + Q : ℕ) : ℝ) * (R : ℝ)) * Real.sqrt 3 = (p : ℝ) := by
      push_cast at hY_sq ⊢
      linear_combination hY_sq - (R : ℝ) ^ 2 * hsq3
    have hcross0 : (P + Q) * R = 0 := by
      by_contra hne
      have hneR : (2 * ((P + Q : ℕ) : ℝ) * (R : ℝ)) ≠ 0 := by
        have hne' : (((P + Q) * R : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hne
        intro h0; apply hne'; push_cast at h0 ⊢; linarith
      set q : ℚ := ((p : ℤ) - ((P + Q : ℕ) ^ 2 + 3 * R ^ 2 : ℤ)) / (2 * ((P + Q : ℕ) : ℤ) * (R : ℤ))
      have hq : (q : ℝ) = Real.sqrt 3 := by
        dsimp [q]; push_cast at hneR hexp ⊢
        rw [div_eq_iff hneR]; linarith
      exact OMA.E634EqRat.real_rat_sq_ne (n := 3) (p := 3) (by decide) (dvd_refl 3) (by decide) q
        (by rw [hq, hsq3]; norm_num)
    rcases mul_eq_zero.mp hcross0 with hPQ0 | hR0
    · rw [hPQ0] at hexp
      have hp3R : p = 3 * R ^ 2 := by
        have h1 : ((3 * R ^ 2 : ℕ) : ℝ) = (p : ℝ) := by
          push_cast at hexp ⊢; linarith
        exact_mod_cast h1.symm
      have h3p : 3 ∣ p := ⟨R ^ 2, hp3R⟩
      rcases hp.eq_one_or_self_of_dvd 3 h3p with h1 | h3 <;> omega
    · rw [hR0] at hexp
      have hpPQ : p = (P + Q) ^ 2 := by
        have h1 : (((P + Q) ^ 2 : ℕ) : ℝ) = (p : ℝ) := by
          push_cast at hexp ⊢; linarith
        exact_mod_cast h1.symm
      have hdvd : (P + Q) ∣ p := ⟨P + Q, by rw [hpPQ, sq]⟩
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hself
      · rw [h1] at hpPQ; norm_num at hpPQ; omega
      · rw [hself] at hpPQ; nlinarith
  · -- Tile 2: (pi/12, pi/3, 7pi/12).
    have hb0 : D.model.angleAt (σ 0) = Real.pi / 12 := (hBD _).trans (by simpa using congrFun hT2 0)
    have hb1 : D.model.angleAt (σ 1) = Real.pi / 3 := (hBD _).trans (by simpa using congrFun hT2 1)
    have hb2 : D.model.angleAt (σ 2) = 7 * Real.pi / 12 := (hBD _).trans (by simpa using congrFun hT2 2)
    have hs0 : Real.sin (Real.pi / 12) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
      rw [show Real.pi / 12 = Real.pi / 3 - Real.pi / 4 by ring, Real.sin_sub,
        Real.sin_pi_div_three, Real.cos_pi_div_three, Real.sin_pi_div_four, Real.cos_pi_div_four]
      have h6 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
        rw [← Real.sqrt_mul (by norm_num)]; norm_num
      linarith
    have hs2 : Real.sin (7 * Real.pi / 12) = (Real.sqrt 6 + Real.sqrt 2) / 4 := by
      rw [show 7 * Real.pi / 12 = Real.pi / 3 + Real.pi / 4 by ring, Real.sin_add,
        Real.sin_pi_div_three, Real.cos_pi_div_three, Real.sin_pi_div_four, Real.cos_pi_div_four]
      have h6 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
        rw [← Real.sqrt_mul (by norm_num)]; norm_num
      linarith
    obtain ⟨Y, P, Q, R, hY_pos, hY_comb, hY_area⟩ :=
      OMA.E634EqRat.eq_tile_master D hAD σ hb0 hb1 hb2 (by rw [hs2]; positivity)
    rw [hs0, Real.sin_pi_div_three, hs2] at hY_comb hY_area
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have h26 : Real.sqrt 2 * Real.sqrt 6 = 2 * Real.sqrt 3 := by
      rw [← Real.sqrt_mul (by norm_num), show (2 : ℝ) * 6 = 2 ^ 2 * 3 by norm_num,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    have h23 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    have hZ_comb : 2 * Real.sqrt 2 * Y = ((R : ℤ) - (P : ℤ) : ℝ) +
        ((P : ℤ) + (R : ℤ) : ℝ) * Real.sqrt 3 + (Q : ℝ) * Real.sqrt 6 := by
      have h1 := congrArg (fun x : ℝ => 2 * Real.sqrt 2 * x) hY_comb
      push_cast
      linear_combination h1 + ((P : ℝ) + (R : ℝ)) / 2 * h26 + ((R : ℝ) - (P : ℝ)) / 2 * h2 + (Q : ℝ) * h23
    have hZ_sq : (2 * Real.sqrt 2 * Y) ^ 2 = 2 * (p : ℝ) := by
      have hprod : ((Real.sqrt 6 - Real.sqrt 2) / 4) * ((Real.sqrt 6 + Real.sqrt 2) / 4) = 1 / 4 := by
        linear_combination (1 / 16 : ℝ) * h6 - (1 / 16 : ℝ) * h2
      have hY2 : Y ^ 2 = (p : ℝ) / 4 := by
        have : Real.sqrt 3 * (Y ^ 2 - (p : ℝ) / 4) = 0 := by
          linear_combination 2 * hY_area + (p : ℝ) * Real.sqrt 3 * hprod
        linarith [(mul_eq_zero.mp this).resolve_left (by positivity)]
      calc (2 * Real.sqrt 2 * Y) ^ 2 = 4 * Real.sqrt 2 ^ 2 * Y ^ 2 := by ring
        _ = 4 * 2 * ((p : ℝ) / 4) := by rw [h2, hY2]
        _ = 2 * (p : ℝ) := by ring
    let Qset : Set ℝ := Set.range (fun q : ℚ => (q : ℝ))
    have hQadd : ∀ x ∈ Qset, ∀ y ∈ Qset, x + y ∈ Qset := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a + b, by push_cast; rfl⟩
    have hQsub : ∀ x ∈ Qset, ∀ y ∈ Qset, x - y ∈ Qset := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a - b, by push_cast; rfl⟩
    have hQmul : ∀ x ∈ Qset, ∀ y ∈ Qset, x * y ∈ Qset := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, by push_cast; rfl⟩
    have hQdiv : ∀ x ∈ Qset, ∀ y ∈ Qset, x / y ∈ Qset := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a / b, by push_cast; rfl⟩
    have hQneg : ∀ x ∈ Qset, -x ∈ Qset := by
      rintro _ ⟨a, rfl⟩; exact ⟨-a, by push_cast; rfl⟩
    have hQnat : ∀ n : ℕ, (n : ℝ) ∈ Qset := fun n => ⟨n, by simp⟩
    have hn3 : Real.sqrt 3 ∉ Qset := by
      rintro ⟨q, hq⟩; dsimp at hq
      exact OMA.E634EqRat.real_rat_sq_ne (n := 3) (p := 3) (by decide) (dvd_refl 3) (by decide) q (by rw [hq, h3]; norm_num)
    have hn6 : Real.sqrt 6 ∉ Qset := by
      rintro ⟨q, hq⟩; dsimp at hq
      exact OMA.E634EqRat.real_rat_sq_ne (n := 6) (p := 2) (by decide) (by decide) (by decide) q (by rw [hq, h6]; norm_num)
    have hn18 : Real.sqrt 3 * Real.sqrt 6 ∉ Qset := by
      rintro ⟨q, hq⟩; dsimp at hq
      have hsq18 : (q : ℝ) ^ 2 = (18 : ℝ) := by rw [hq, mul_pow, h3, h6]; norm_num
      exact OMA.E634EqRat.real_rat_sq_ne (n := 18) (p := 2) (by decide) (by decide) (by decide) q hsq18
    rw [hZ_comb] at hZ_sq
    rcases OMA.E634EqRat.quad_sq_mem_F Qset hQadd hQsub hQmul hQdiv hQneg hQnat
        ⟨(R : ℤ) - (P : ℤ), by push_cast; rfl⟩ ⟨(P : ℤ) + (R : ℤ), by push_cast; rfl⟩
        ⟨Q, by simp⟩ ⟨2 * p, by push_cast; rfl⟩ ⟨3, by simp⟩ ⟨6, by simp⟩
        h3 h6 hn3 hn6 hn18 hZ_sq with ⟨hv0, ht0⟩ | ⟨hu0, ht0⟩ | ⟨hu0, hv0⟩
    · have hPR : P + R = 0 := by
        have : ((P + R : ℕ) : ℝ) = 0 := by push_cast; exact hv0
        exact_mod_cast this
      have hQ0 : Q = 0 := by exact_mod_cast ht0
      have hP0 : P = 0 := by omega
      have hR0 : R = 0 := by omega
      rw [hP0, hQ0, hR0] at hZ_comb; simp at hZ_comb
      have : 0 < 2 * Real.sqrt 2 * Y := by positivity
      linarith
    · rw [hu0, ht0, zero_mul, zero_add, add_zero, mul_pow, h3] at hZ_sq
      have h2p : 2 * p = 3 * (P + R) ^ 2 := by
        have : ((2 * p : ℕ) : ℝ) = ((3 * (P + R) ^ 2 : ℕ) : ℝ) := by
          push_cast at hZ_sq ⊢; linarith
        exact_mod_cast this
      have h3p : 3 ∣ 2 * p := ⟨(P + R) ^ 2, h2p⟩
      have h3p' : 3 ∣ p := ((Nat.prime_three).dvd_mul.mp h3p).resolve_left (by decide)
      rcases hp.eq_one_or_self_of_dvd 3 h3p' with h1 | h3' <;> omega
    · rw [hu0, hv0, zero_mul, add_zero, zero_add, mul_pow, h6] at hZ_sq
      have hp3Q : p = 3 * Q ^ 2 := by
        have : (p : ℝ) = ((3 * Q ^ 2 : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
      have h3p : 3 ∣ p := ⟨Q ^ 2, hp3Q⟩
      rcases hp.eq_one_or_self_of_dvd 3 h3p with h1 | h3' <;> omega
  · -- Tile 3: (pi/30, pi/3, 19pi/30).
    have hb0 : D.model.angleAt (σ 0) = Real.pi / 30 := (hBD _).trans (by simpa using congrFun hT3 0)
    have hb1 : D.model.angleAt (σ 1) = Real.pi / 3 := (hBD _).trans (by simpa using congrFun hT3 1)
    have hb2 : D.model.angleAt (σ 2) = 19 * Real.pi / 30 := (hBD _).trans (by simpa using congrFun hT3 2)
    obtain ⟨hc5, hs5, -, -⟩ := OMA.E634EqRat.trig_pi_div_five
    have hs0 : Real.sin (Real.pi / 30) = (Real.sqrt 3 * Real.sqrt (10 - 2 * Real.sqrt 5) - (1 + Real.sqrt 5)) / 8 := by
      rw [show Real.pi / 30 = Real.pi / 5 - Real.pi / 6 by ring, Real.sin_sub,
        hs5, hc5, Real.cos_pi_div_six, Real.sin_pi_div_six]; ring
    have hs2 : Real.sin (19 * Real.pi / 30) = (Real.sqrt 3 * Real.sqrt (10 - 2 * Real.sqrt 5) + (1 + Real.sqrt 5)) / 8 := by
      rw [show 19 * Real.pi / 30 = Real.pi - (Real.pi / 5 + Real.pi / 6) by ring, Real.sin_pi_sub,
        Real.sin_add, hs5, hc5, Real.cos_pi_div_six, Real.sin_pi_div_six]; ring
    have hs2_pos : 0 < Real.sin (19 * Real.pi / 30) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    obtain ⟨Y, P, Q, R, hY_pos, hY_comb, hY_area⟩ :=
      OMA.E634EqRat.eq_tile_master D hAD σ hb0 hb1 hb2 hs2_pos
    rw [hs0, Real.sin_pi_div_three, hs2] at hY_comb hY_area
    have hsq5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h10_nn : 0 ≤ 10 - 2 * Real.sqrt 5 := by
      have : Real.sqrt 5 < 3 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
      linarith
    have hsq10 : Real.sqrt (10 - 2 * Real.sqrt 5) ^ 2 = 10 - 2 * Real.sqrt 5 := Real.sq_sqrt h10_nn
    have hprod : Real.sin (Real.pi / 30) * Real.sin (19 * Real.pi / 30) = (3 - Real.sqrt 5) / 8 := by
      rw [hs0, hs2]
      have h1 : (Real.sqrt 3 * Real.sqrt (10 - 2 * Real.sqrt 5)) ^ 2 = 3 * (10 - 2 * Real.sqrt 5) := by
        rw [mul_pow, hsq3, hsq10]
      linear_combination (1 / 64 : ℝ) * h1 - (1 / 64 : ℝ) * hsq5
    have hY_sq : (8 * Y) ^ 2 = (8 * (p : ℝ)) * (3 + ((-1 : ℚ) : ℝ) * Real.sqrt 5) := by
      rw [hs0, hs2] at hprod
      have h1 : Real.sqrt 3 * ((8 * Y) ^ 2 - 8 * (p : ℝ) * (3 - Real.sqrt 5)) = 0 := by
        linear_combination 128 * hY_area + 64 * (p : ℝ) * Real.sqrt 3 * hprod
      have h2 := (mul_eq_zero.mp h1).resolve_left (by positivity)
      push_cast; linarith
    have hY_comb' : 8 * Y = ((R : ℤ) - (P : ℤ) : ℝ) * (-((-1 : ℚ) : ℝ) + Real.sqrt 5) +
        (4 * (Q : ℤ) : ℝ) * Real.sqrt 3 +
        ((P : ℤ) + (R : ℤ) : ℝ) * (Real.sqrt 3 * Real.sqrt (10 + 2 * ((-1 : ℚ) : ℝ) * Real.sqrt 5)) := by
      push_cast
      rw [show (10 : ℝ) + 2 * (-1 : ℝ) * Real.sqrt 5 = 10 - 2 * Real.sqrt 5 by ring]
      linarith
    exact OMA.E634EqRat.tile3_or_tile4_contra hp.pos (Or.inl rfl) hY_pos hY_comb' hY_sq
  · -- Tile 4: (7pi/30, pi/3, 13pi/30).
    have hb0 : D.model.angleAt (σ 0) = 7 * Real.pi / 30 := (hBD _).trans (by simpa using congrFun hT4 0)
    have hb1 : D.model.angleAt (σ 1) = Real.pi / 3 := (hBD _).trans (by simpa using congrFun hT4 1)
    have hb2 : D.model.angleAt (σ 2) = 13 * Real.pi / 30 := (hBD _).trans (by simpa using congrFun hT4 2)
    obtain ⟨-, -, hc25, hs25⟩ := OMA.E634EqRat.trig_pi_div_five
    have hs0 : Real.sin (7 * Real.pi / 30) = (Real.sqrt 3 * Real.sqrt (10 + 2 * Real.sqrt 5) - (Real.sqrt 5 - 1)) / 8 := by
      rw [show 7 * Real.pi / 30 = 2 * Real.pi / 5 - Real.pi / 6 by ring, Real.sin_sub,
        hs25, hc25, Real.cos_pi_div_six, Real.sin_pi_div_six]; ring
    have hs2 : Real.sin (13 * Real.pi / 30) = (Real.sqrt 3 * Real.sqrt (10 + 2 * Real.sqrt 5) + (Real.sqrt 5 - 1)) / 8 := by
      rw [show 13 * Real.pi / 30 = Real.pi - (2 * Real.pi / 5 + Real.pi / 6) by ring, Real.sin_pi_sub,
        Real.sin_add, hs25, hc25, Real.cos_pi_div_six, Real.sin_pi_div_six]; ring
    have hs2_pos : 0 < Real.sin (13 * Real.pi / 30) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    obtain ⟨Y, P, Q, R, hY_pos, hY_comb, hY_area⟩ :=
      OMA.E634EqRat.eq_tile_master D hAD σ hb0 hb1 hb2 hs2_pos
    rw [hs0, Real.sin_pi_div_three, hs2] at hY_comb hY_area
    have hsq5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hsq10 : Real.sqrt (10 + 2 * Real.sqrt 5) ^ 2 = 10 + 2 * Real.sqrt 5 :=
      Real.sq_sqrt (by positivity)
    have hprod : Real.sin (7 * Real.pi / 30) * Real.sin (13 * Real.pi / 30) = (3 + Real.sqrt 5) / 8 := by
      rw [hs0, hs2]
      have h1 : (Real.sqrt 3 * Real.sqrt (10 + 2 * Real.sqrt 5)) ^ 2 = 3 * (10 + 2 * Real.sqrt 5) := by
        rw [mul_pow, hsq3, hsq10]
      linear_combination (1 / 64 : ℝ) * h1 - (1 / 64 : ℝ) * hsq5
    have hY_sq : (8 * Y) ^ 2 = (8 * (p : ℝ)) * (3 + ((1 : ℚ) : ℝ) * Real.sqrt 5) := by
      rw [hs0, hs2] at hprod
      have h1 : Real.sqrt 3 * ((8 * Y) ^ 2 - 8 * (p : ℝ) * (3 + Real.sqrt 5)) = 0 := by
        linear_combination 128 * hY_area + 64 * (p : ℝ) * Real.sqrt 3 * hprod
      have h2 := (mul_eq_zero.mp h1).resolve_left (by positivity)
      push_cast; linarith
    have hY_comb' : 8 * Y = ((R : ℤ) - (P : ℤ) : ℝ) * (-((1 : ℚ) : ℝ) + Real.sqrt 5) +
        (4 * (Q : ℤ) : ℝ) * Real.sqrt 3 +
        ((P : ℤ) + (R : ℤ) : ℝ) * (Real.sqrt 3 * Real.sqrt (10 + 2 * ((1 : ℚ) : ℝ) * Real.sqrt 5)) := by
      push_cast
      rw [show (10 : ℝ) + 2 * (1 : ℝ) * Real.sqrt 5 = 10 + 2 * Real.sqrt 5 by ring]
      linarith
    exact OMA.E634EqRat.tile3_or_tile4_contra hp.pos (Or.inr rfl) hY_pos hY_comb' hY_sq
