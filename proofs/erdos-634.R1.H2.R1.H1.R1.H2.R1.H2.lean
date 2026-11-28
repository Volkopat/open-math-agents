import OMAReductions.R_erdos_634_R1_H2_R1_H1_R1_H2_R1

/-!
# Erdos 634, step R1.H2.R1.H1.R1.H2.R1.H2: theorem:notprime60 given the rationality of the tile

Flattened from the Lean port of Beeson-Rosu / Bonfioli (formalizations of the triangle tiling
papers), restricted to the declarations this step uses.
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
theorem Dir.neg_involutive : Function.Involutive Dir.neg := by
  intro d; apply Subtype.ext; simp [Dir.neg]
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
noncomputable def Dissection.dirSet {N : ℕ} (D : Dissection N) (d : Dir) : Set Plane :=
  (⋃ i : Fin N, ⋃ k : Fin 3, ⋃ (_ : (D.tile i).leftUnit k = d), (D.tile i).edge k)
    ∩ interior D.target.carrier
theorem Dissection.mem_dirSet {N : ℕ} (D : Dissection N) (d : Dir) {x : Plane}
    (hx : x ∈ D.dirSet d) :
    ∃ i k, (D.tile i).leftUnit k = d ∧ x ∈ (D.tile i).edge k := by
  obtain ⟨hu, -⟩ := hx
  simp only [Set.mem_iUnion] at hu
  obtain ⟨i, k, hik, hmem⟩ := hu
  exact ⟨i, k, hik, hmem⟩
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
theorem Tri.onEdge_data (T : Tri) {k : Fin 3} {x : Plane} (hx : x ∈ T.edge k)
    (hxv : ∀ m, x ≠ T.pts m) :
    T.basis.coord (k + 2) x = 0 ∧ ∀ j, j ≠ k + 2 → 0 < T.basis.coord j x := by
  refine ⟨T.coord_eq_zero_of_mem_edge k hx, fun j hj => ?_⟩
  have hnn : 0 ≤ T.basis.coord j x := by
    have := T.edge_subset_carrier k hx
    rw [T.carrier_eq_nonneg_coord] at this; exact this j
  refine lt_of_le_of_ne hnn (Ne.symm fun hzero => ?_)
  obtain ⟨m, hm⟩ := T.eq_vertex_of_two_coords_zero hj hzero (T.coord_eq_zero_of_mem_edge k hx)
  exact hxv m hm
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
theorem Dissection.dirSet_sub {N : ℕ} (D : Dissection N) (hN : 0 < N) (d : Dir) :
    D.dirSet d \ D.vertexSet ⊆ D.dirSet (Dir.neg d) \ D.vertexSet := by
  rintro x ⟨hxd, hxv⟩
  refine ⟨?_, hxv⟩
  have hxint : x ∈ interior D.target.carrier := hxd.2
  obtain ⟨i₀, k₀, hk₀, hmem⟩ := D.mem_dirSet d hxd
  have hnv := D.notMem_vertexSet hxv
  obtain ⟨hz₀, hp₀⟩ := (D.tile i₀).onEdge_data hmem (hnv i₀)
  obtain ⟨R, hR, hRt⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
  have hRt' : Metric.ball x R ⊆ D.target.carrier := hRt.trans interior_subset
  obtain ⟨i₁, hne, hi₁⟩ := D.second_tile_at_edge_point hN hnv hR hRt' ⟨k₀ + 2, hz₀, hp₀⟩
  obtain ⟨m₁, hz₁, hp₁⟩ := hi₁
  have hkey := D.leftUnit_neg (Ne.symm hne) hz₀ hp₀ hz₁ hp₁
  have hshift : (k₀ + 2 + 1 : Fin 3) = k₀ := by fin_cases k₀ <;> rfl
  rw [hshift, hk₀] at hkey
  refine ⟨?_, hxint⟩
  exact Set.mem_iUnion.mpr ⟨i₁, Set.mem_iUnion.mpr ⟨m₁ + 1, Set.mem_iUnion.mpr
    ⟨hkey, (D.tile i₁).mem_edge_of_coord_zero hz₁ hp₁⟩⟩⟩
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
def Tri.Congruent (T U : Tri) : Prop :=
  ∃ (f : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3)), ∀ k, f (T.pts k) = U.pts (σ k)
theorem Tri.Congruent.dist_eq {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts (σ i)) (U.pts (σ j)) := by
  obtain ⟨f, σ, hf⟩ := h
  exact ⟨σ, fun i j => by rw [← hf i, ← hf j, f.dist_eq]⟩
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
end Erdos634.AreaDet
end

section
namespace Erdos634.Geometry
open MeasureTheory Set
theorem cross_sub_right (u a b : Plane) : cross u (a - b) = cross u a - cross u b := by
  simp only [cross, PiLp.sub_apply]; ring
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
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
open EuclideanGeometry
theorem angle_of_sss {p q r p' q' r' : Plane}
    (hpq : dist p q = dist p' q') (hqr : dist q r = dist q' r') (hpr : dist p r = dist p' r')
    (hp : p ≠ q) (hr : r ≠ q) :
    EuclideanGeometry.angle (V := Plane) p q r = EuclideanGeometry.angle (V := Plane) p' q' r' := by
  have hd1 : (0:ℝ) < dist p q := dist_pos.mpr hp
  have hd2 : (0:ℝ) < dist r q := dist_pos.mpr hr
  have law1 := EuclideanGeometry.law_cos (V := Plane) p q r
  have law2 := EuclideanGeometry.law_cos (V := Plane) p' q' r'
  have hqr'' : dist r q = dist r' q' := by rw [dist_comm r q, dist_comm r' q']; exact hqr
  have hcos : Real.cos (EuclideanGeometry.angle (V := Plane) p q r)
      = Real.cos (EuclideanGeometry.angle (V := Plane) p' q' r') := by
    rw [← hpq, ← hqr'', ← hpr] at law2
    have h2d : (0:ℝ) < 2 * dist p q * dist r q := by positivity
    have hmul : 2 * dist p q * dist r q * Real.cos (EuclideanGeometry.angle (V := Plane) p q r)
        = 2 * dist p q * dist r q * Real.cos (EuclideanGeometry.angle (V := Plane) p' q' r') := by
      nlinarith [law1, law2]
    exact mul_left_cancel₀ (ne_of_gt h2d) hmul
  have hmem1 : EuclideanGeometry.angle (V := Plane) p q r ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hmem2 : EuclideanGeometry.angle (V := Plane) p' q' r' ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  exact Real.injOn_cos hmem1 hmem2 hcos
theorem fin3_cases (a k : Fin 3) (h : a ≠ k) : a = k + 1 ∨ a = k + 2 := by
  fin_cases a <;> fin_cases k <;> simp_all <;> decide
end Erdos634.Geometry
end

section
namespace Erdos634.BaseSelection
open Erdos634.Geometry
theorem coord_zero_mem_segment (T : Tri) (k : Fin 3) (x : Plane)
    (h0 : T.basis.coord k x = 0) (hnn : ∀ j, 0 ≤ T.basis.coord j x) :
    x ∈ segment ℝ (T.pts (k+1)) (T.pts (k+2)) := by
  have hx : x = (T.basis.coord 0 x) • T.pts 0 + (T.basis.coord 1 x) • T.pts 1
        + (T.basis.coord 2 x) • T.pts 2 := by
    have h := T.basis.affineCombination_coord_eq_self (k := ℝ) x
    rw [Finset.affineCombination_eq_linear_combination] at h
    · rw [Fin.sum_univ_three] at h; exact h.symm
    · exact T.basis.sum_coord_apply_eq_one x
  have hsum : T.basis.coord 0 x + T.basis.coord 1 x + T.basis.coord 2 x = 1 := by
    have := T.basis.sum_coord_apply_eq_one (k := ℝ) x
    rwa [Fin.sum_univ_three] at this
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · refine ⟨T.basis.coord 1 x, T.basis.coord 2 x, hnn 1, hnn 2, by linarith [h0, hsum], ?_⟩
    simp only [show ((0:Fin 3)+1) = 1 from rfl, show ((0:Fin 3)+2) = 2 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module
  · refine ⟨T.basis.coord 2 x, T.basis.coord 0 x, hnn 2, hnn 0, by linarith [h0, hsum], ?_⟩
    simp only [show ((1:Fin 3)+1) = 2 from rfl, show ((1:Fin 3)+2) = 0 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module
  · refine ⟨T.basis.coord 0 x, T.basis.coord 1 x, hnn 0, hnn 1, by linarith [h0, hsum], ?_⟩
    simp only [show ((2:Fin 3)+1) = 0 from rfl, show ((2:Fin 3)+2) = 1 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module
end Erdos634.BaseSelection
end

section
open scoped Classical
namespace Erdos634.Geometry
open MeasureTheory Set
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
noncomputable def Tri.flux (T : Tri) (f : Dir → E) : E :=
  ∑ k : Fin 3, dist (T.pts k) (T.pts (k + 1)) • f (T.leftUnit k)
theorem Dir.neg_ne_self (d : Dir) : Dir.neg d ≠ d := by
  intro h
  have h1 : -d.1 = d.1 := congrArg Subtype.val h
  have h2 : (2:ℝ) • d.1 = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h1]
    exact neg_add_cancel _
  have h3 : d.1 = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  have h4 := d.2
  rw [h3, norm_zero] at h4
  norm_num at h4
namespace Dissection
noncomputable def eLen (D : Dissection N) (e : Fin N × Fin 3) : ℝ :=
  dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
noncomputable def eDir (D : Dissection N) (e : Fin N × Fin 3) : Dir := (D.tile e.1).leftUnit e.2
def eSet (D : Dissection N) (e : Fin N × Fin 3) : Set Plane := (D.tile e.1).edge e.2
noncomputable def sideEdges (D : Dissection N) (j : Fin 3) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e => D.eSet e ⊆ D.target.edge j
noncomputable def intEdges (D : Dissection N) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e => ∀ j, ¬ D.eSet e ⊆ D.target.edge j
theorem flux_sum_eq (D : Dissection N) (f : Dir → E) :
    ∑ i, (D.tile i).flux f = ∑ e : Fin N × Fin 3, D.eLen e • f (D.eDir e) := by
  rw [Fintype.sum_prod_type]
  rfl
end Dissection
theorem Tri.notMem_interior_of_mem_edge (T : Tri) {j : Fin 3} {x : Plane}
    (hx : x ∈ T.edge j) : x ∉ interior T.carrier := by
  intro hint
  have h0 := T.coord_eq_zero_of_mem_edge j hx
  have hpos := T.interior_coord_pos hint (j + 2)
  rw [h0] at hpos
  exact lt_irrefl _ hpos
theorem Tri.coord_zero_mem_segment' (T : Tri) (k : Fin 3) (x : Plane)
    (h0 : T.basis.coord k x = 0) (hnn : ∀ j, 0 ≤ T.basis.coord j x) :
    x ∈ segment ℝ (T.pts (k+1)) (T.pts (k+2)) := by
  have hx : x = (T.basis.coord 0 x) • T.pts 0 + (T.basis.coord 1 x) • T.pts 1
        + (T.basis.coord 2 x) • T.pts 2 := by
    have h := T.basis.affineCombination_coord_eq_self (k := ℝ) x
    rw [Finset.affineCombination_eq_linear_combination] at h
    · rw [Fin.sum_univ_three] at h; exact h.symm
    · exact T.basis.sum_coord_apply_eq_one x
  have hsum : T.basis.coord 0 x + T.basis.coord 1 x + T.basis.coord 2 x = 1 := by
    have := T.basis.sum_coord_apply_eq_one (k := ℝ) x
    rwa [Fin.sum_univ_three] at this
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · refine ⟨T.basis.coord 1 x, T.basis.coord 2 x, hnn 1, hnn 2, by linarith [h0, hsum], ?_⟩
    simp only [show ((0:Fin 3)+1) = 1 from rfl, show ((0:Fin 3)+2) = 2 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module
  · refine ⟨T.basis.coord 2 x, T.basis.coord 0 x, hnn 2, hnn 0, by linarith [h0, hsum], ?_⟩
    simp only [show ((1:Fin 3)+1) = 2 from rfl, show ((1:Fin 3)+2) = 0 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module
  · refine ⟨T.basis.coord 0 x, T.basis.coord 1 x, hnn 0, hnn 1, by linarith [h0, hsum], ?_⟩
    simp only [show ((2:Fin 3)+1) = 0 from rfl, show ((2:Fin 3)+2) = 1 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module
theorem Tri.mem_edge_of_coord_zero_nonneg (T : Tri) {m : Fin 3} {x : Plane}
    (h0 : T.basis.coord m x = 0) (hnn : ∀ j, 0 ≤ T.basis.coord j x) :
    x ∈ T.edge (m + 1) := by
  have h := T.coord_zero_mem_segment' m x h0 hnn
  have hidx : m + 1 + 1 = m + 2 := by fin_cases m <;> rfl
  rw [Tri.edge, hidx]
  exact h
theorem Dissection.edge_interior_or_side (D : Dissection N) (e : Fin N × Fin 3) {x : Plane}
    (hx : x ∈ D.eSet e) (hx1 : x ≠ (D.tile e.1).pts e.2) (hx2 : x ≠ (D.tile e.1).pts (e.2 + 1)) :
    x ∈ interior D.target.carrier ∨ ∃ j, D.eSet e ⊆ D.target.edge j := by
  by_cases hint : x ∈ interior D.target.carrier
  · exact Or.inl hint
  right
  have hnnT : ∀ y ∈ (D.tile e.1).carrier, ∀ i, 0 ≤ D.target.basis.coord i y := by
    intro y hy i
    have := tile_subset_target D e.1 hy
    rw [D.target.carrier_eq_nonneg_coord] at this
    exact this i
  have haT : (D.tile e.1).pts e.2 ∈ (D.tile e.1).carrier := subset_convexHull ℝ _ ⟨e.2, rfl⟩
  have hbT : (D.tile e.1).pts (e.2 + 1) ∈ (D.tile e.1).carrier :=
    subset_convexHull ℝ _ ⟨e.2 + 1, rfl⟩
  have hxT : x ∈ (D.tile e.1).carrier := (D.tile e.1).edge_subset_carrier e.2 hx
  obtain ⟨m, hm⟩ : ∃ m, D.target.basis.coord m x = 0 := by
    by_contra hcon
    push Not at hcon
    apply hint
    have hpos : ∀ i, 0 < D.target.basis.coord i x := fun i =>
      lt_of_le_of_ne (hnnT x hxT i) (Ne.symm (hcon i))
    obtain ⟨r, hr, hsub⟩ := D.target.ball_subset_of_pos hpos
    exact mem_interior.mpr ⟨Metric.ball x r, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
  have hx' : x ∈ segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := hx
  obtain ⟨s, t, hs, ht, hst, hxst⟩ := hx'
  have hspos : 0 < s := by
    rcases hs.lt_or_eq with h | h
    · exact h
    · exfalso; apply hx2
      have ht1 : t = 1 := by linarith
      rw [← hxst, ← h, ht1, zero_smul, one_smul, zero_add]
  have htpos : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · exfalso; apply hx1
      have hs1 : s = 1 := by linarith
      rw [← hxst, ← h, hs1, zero_smul, one_smul, add_zero]
  have hcomb : D.target.basis.coord m x
      = s * D.target.basis.coord m ((D.tile e.1).pts e.2)
        + t * D.target.basis.coord m ((D.tile e.1).pts (e.2 + 1)) := by
    rw [← hxst, Convex.combo_affine_apply hst, smul_eq_mul, smul_eq_mul]
  have hga := hnnT _ haT m
  have hgb := hnnT _ hbT m
  have h1 : 0 ≤ s * D.target.basis.coord m ((D.tile e.1).pts e.2) := mul_nonneg hs hga
  have h2 : 0 ≤ t * D.target.basis.coord m ((D.tile e.1).pts (e.2 + 1)) := mul_nonneg ht hgb
  have h3 : s * D.target.basis.coord m ((D.tile e.1).pts e.2) = 0 := by linarith
  have h4 : t * D.target.basis.coord m ((D.tile e.1).pts (e.2 + 1)) = 0 := by linarith
  have hza := (mul_eq_zero.mp h3).resolve_left hspos.ne'
  have hzb := (mul_eq_zero.mp h4).resolve_left htpos.ne'
  have haE := D.target.mem_edge_of_coord_zero_nonneg hza (hnnT _ haT)
  have hbE := D.target.mem_edge_of_coord_zero_nonneg hzb (hnnT _ hbT)
  exact ⟨m + 1, (convex_segment _ _).segment_subset haE hbE⟩
theorem Dissection.mem_interior_of_mem_intEdges (D : Dissection N) {e : Fin N × Fin 3}
    (he : e ∈ D.intEdges) {x : Plane} (hx : x ∈ D.eSet e)
    (hx1 : x ≠ (D.tile e.1).pts e.2) (hx2 : x ≠ (D.tile e.1).pts (e.2 + 1)) :
    x ∈ interior D.target.carrier := by
  rcases D.edge_interior_or_side e hx hx1 hx2 with h | ⟨j, hj⟩
  · exact h
  · unfold Dissection.intEdges at he
    exact absurd hj ((Finset.mem_filter.mp he).2 j)
theorem Dissection.mem_intEdges_of_interior (D : Dissection N) {e : Fin N × Fin 3} {x : Plane}
    (hx : x ∈ D.eSet e) (hxi : x ∈ interior D.target.carrier) : e ∈ D.intEdges := by
  unfold Dissection.intEdges
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, fun j hj => D.target.notMem_interior_of_mem_edge (hj hx) hxi⟩
theorem Tri.edge_inter_edge_subsingleton (T : Tri) {j j' : Fin 3} (h : j ≠ j') :
    (T.edge j ∩ T.edge j').Subsingleton := by
  have h2 : j + 2 ≠ j' + 2 := fun h' => h (add_right_cancel h')
  have key : ∀ y ∈ T.edge j ∩ T.edge j', ∃ m, y = T.pts m ∧ m ≠ j + 2 ∧ m ≠ j' + 2 := by
    rintro y ⟨hy, hy'⟩
    have hz := T.coord_eq_zero_of_mem_edge j hy
    have hz' := T.coord_eq_zero_of_mem_edge j' hy'
    obtain ⟨m, rfl⟩ := T.eq_vertex_of_two_coords_zero h2 hz hz'
    have e1 : T.basis.coord m (T.pts m) = 1 := T.basis.coord_apply_eq m
    refine ⟨m, rfl, ?_, ?_⟩
    · intro hm; rw [← hm, e1] at hz; exact one_ne_zero hz
    · intro hm; rw [← hm, e1] at hz'; exact one_ne_zero hz'
  intro y hy z hz
  obtain ⟨m, rfl, hm1, hm2⟩ := key y hy
  obtain ⟨m', rfl, hm1', hm2'⟩ := key z hz
  have hall : ∀ a b c d : Fin 3, a ≠ b → c ≠ a → c ≠ b → d ≠ a → d ≠ b → c = d := by decide
  rw [hall _ _ _ _ h2 hm1 hm2 hm1' hm2']
theorem Dissection.sideEdges_disjoint (D : Dissection N) {j j' : Fin 3} (h : j ≠ j') :
    Disjoint (D.sideEdges j) (D.sideEdges j') := by
  rw [Finset.disjoint_left]
  intro e he he'
  unfold Dissection.sideEdges at he he'
  have hj := (Finset.mem_filter.mp he).2
  have hj' := (Finset.mem_filter.mp he').2
  have ha : (D.tile e.1).pts e.2 ∈ D.eSet e := left_mem_segment ℝ _ _
  have hb : (D.tile e.1).pts (e.2 + 1) ∈ D.eSet e := right_mem_segment ℝ _ _
  have hsucc : ∀ i : Fin 3, i ≠ i + 1 := by decide
  have hne : (D.tile e.1).pts e.2 ≠ (D.tile e.1).pts (e.2 + 1) := fun hh =>
    hsucc e.2 ((D.tile e.1).indep.injective hh)
  exact hne (D.target.edge_inter_edge_subsingleton h ⟨hj ha, hj' ha⟩ ⟨hj hb, hj' hb⟩)
omit [Module ℝ E] in
theorem Dissection.sum_split (D : Dissection N) (g : Fin N × Fin 3 → E) :
    ∑ e, g e = ∑ e ∈ D.intEdges, g e + ∑ j : Fin 3, ∑ e ∈ D.sideEdges j, g e := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 3))) D.sideEdges :=
    fun j _ j' _ hjj' => D.sideEdges_disjoint hjj'
  rw [← Finset.sum_biUnion hdisj]
  have hunion : D.intEdges ∪ (Finset.univ : Finset (Fin 3)).biUnion D.sideEdges
      = Finset.univ := by
    ext e
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true,
      Dissection.intEdges, Dissection.sideEdges, Finset.mem_filter]
    by_cases h : ∀ j, ¬ D.eSet e ⊆ D.target.edge j
    · exact Or.inl h
    · push Not at h; exact Or.inr h
  have hdis2 : Disjoint D.intEdges ((Finset.univ : Finset (Fin 3)).biUnion D.sideEdges) := by
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Dissection.sideEdges,
      Finset.mem_filter] at he'
    simp only [Dissection.intEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨j, hj⟩ := he'
    exact he j hj
  rw [← Finset.sum_union hdis2, hunion]
theorem Dissection.sameDir_subsingleton (D : Dissection N) {e₁ e₂ : Fin N × Fin 3}
    (hne : e₁ ≠ e₂) (hdir : D.eDir e₁ = D.eDir e₂) :
    (D.eSet e₁ ∩ D.eSet e₂).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  obtain ⟨hm1, hn1A, hn1B⟩ := mem_ne_ends_of_avg hpq hp.1 hq.1
  obtain ⟨hm2, hn2A, hn2B⟩ := mem_ne_ends_of_avg hpq hp.2 hq.2
  obtain ⟨hz₁, hp₁⟩ := (D.tile e₁.1).onEdge_param (k := e₁.2) hm1 hn1A hn1B
  obtain ⟨hz₂, hp₂⟩ := (D.tile e₂.1).onEdge_param (k := e₂.2) hm2 hn2A hn2B
  have hshift : ∀ k : Fin 3, k + 2 + 1 = k := by decide
  by_cases hsame : e₁.1 = e₂.1
  · have hk : e₁.2 ≠ e₂.2 := fun h => hne (Prod.ext hsame h)
    have hk2 : e₁.2 + 2 ≠ e₂.2 + 2 := fun h => hk (add_right_cancel h)
    rw [hsame] at hz₁
    exact absurd hz₁ (ne_of_gt (hp₂ _ hk2))
  · have hkey := D.leftUnit_neg hsame hz₁ hp₁ hz₂ hp₂
    simp only [hshift] at hkey
    exact Dir.neg_ne_self _ (hkey.symm.trans hdir.symm)
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
noncomputable def toC : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
theorem toC_apply (v : Plane) : toC v = (v 0 : ℂ) + (v 1 : ℂ) * Complex.I :=
  Complex.orthonormalBasisOneI_repr_symm_apply v
theorem toC_re (v : Plane) : (toC v).re = v 0 := by simp [toC_apply]
theorem toC_im (v : Plane) : (toC v).im = v 1 := by simp [toC_apply]
theorem toC_ne_zero {v : Plane} (hv : v ≠ 0) : toC v ≠ 0 := by
  intro h
  apply hv
  exact toC.injective (h.trans (map_zero toC).symm)
theorem toC_div_im (u v : Plane) :
    (toC v / toC u).im = cross u v / Complex.normSq (toC u) := by
  rw [Complex.div_im, toC_re, toC_re, toC_im, toC_im]
  unfold cross
  ring
theorem arg_turn {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) (hc : 0 < cross u v) :
    ((Complex.arg (toC v) : ℝ) : Real.Angle)
      = (Complex.arg (toC u) : Real.Angle)
        + ((InnerProductGeometry.angle u v : ℝ) : Real.Angle) := by
  have hu' := toC_ne_zero hu
  have hv' := toC_ne_zero hv
  have him : 0 ≤ (toC v / toC u).im := by
    rw [toC_div_im]
    exact div_nonneg hc.le (Complex.normSq_nonneg _)
  have h1 : InnerProductGeometry.angle (toC u) (toC v) = InnerProductGeometry.angle u v :=
    toC.toLinearIsometry.angle_map u v
  have hang : InnerProductGeometry.angle u v = Complex.arg (toC v / toC u) := by
    rw [← h1, InnerProductGeometry.angle_comm, Complex.angle_eq_abs_arg hv' hu',
      abs_of_nonneg (Complex.arg_nonneg_iff.mpr him)]
  rw [hang, Complex.arg_div_coe_angle hv' hu']
  abel
noncomputable def Dir.angle (d : Dir) : Real.Angle := (Complex.arg (toC d.1) : Real.Angle)
theorem Dir.ne_zero (d : Dir) : d.1 ≠ 0 := by
  intro h
  have h2 := d.2
  rw [h, norm_zero] at h2
  norm_num at h2
theorem Dir.angle_neg (d : Dir) :
    (Dir.neg d).angle = d.angle + ((Real.pi : ℝ) : Real.Angle) := by
  unfold Dir.angle
  have h : toC (Dir.neg d).1 = - toC d.1 := map_neg toC d.1
  rw [h, Complex.arg_neg_coe_angle (toC_ne_zero d.ne_zero)]
theorem Tri.leftUnit_angle (T : Tri) (k : Fin 3) :
    (T.leftUnit k).angle = (Complex.arg (toC (T.leftDir k)) : Real.Angle) := by
  unfold Dir.angle
  show ((Complex.arg (toC (‖T.leftDir k‖⁻¹ • T.leftDir k)) : ℝ) : Real.Angle) = _
  rw [map_smul, Complex.real_smul,
    Complex.arg_real_mul _ (inv_pos.mpr (norm_pos_iff.mpr (T.leftDir_ne_zero k)))]
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
theorem Tri.pi_sub_angleAt (T : Tri) (k : Fin 3) :
    Real.pi - T.angleAt (k + 1)
      = InnerProductGeometry.angle (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts (k + 1)) := by
  have h1 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have h2 : k + 1 + 2 = k := by fin_cases k <;> rfl
  unfold Tri.angleAt cornerAngle EuclideanGeometry.angle
  rw [h1, h2]
  simp only [vsub_eq_sub]
  rw [InnerProductGeometry.angle_comm,
    show T.pts k - T.pts (k + 1) = -(T.pts (k + 1) - T.pts k) by abel,
    InnerProductGeometry.angle_neg_left]
  ring
theorem Tri.cross_consecutive (T : Tri) (k : Fin 3) :
    cross (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts (k + 1)) = T.det := by
  have h := T.det_cyclic k
  have e : T.pts (k + 2) - T.pts (k + 1) = (T.pts (k + 2) - T.pts k) - (T.pts (k + 1) - T.pts k) := by
    abel
  rw [e, cross_sub_right, h, cross_self, sub_zero]
theorem Tri.leftUnit_turn_of_pos (T : Tri) (hT : 0 < T.det) (k : Fin 3) :
    (T.leftUnit (k + 1)).angle
      = (T.leftUnit k).angle + ((Real.pi - T.angleAt (k + 1) : ℝ) : Real.Angle) := by
  have h1 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have hk : T.leftDir k = T.pts (k + 1) - T.pts k := by unfold Tri.leftDir; rw [if_pos hT]
  have hk1 : T.leftDir (k + 1) = T.pts (k + 2) - T.pts (k + 1) := by
    unfold Tri.leftDir; rw [if_pos hT, h1]
  rw [Tri.leftUnit_angle, Tri.leftUnit_angle, T.pi_sub_angleAt k, hk, hk1]
  refine arg_turn ?_ ?_ ?_
  · rw [← hk]; exact T.leftDir_ne_zero k
  · rw [← hk1]; exact T.leftDir_ne_zero (k + 1)
  · rw [T.cross_consecutive k]; exact hT
theorem Tri.leftUnit_turn_of_neg (T : Tri) (hT : T.det < 0) (k : Fin 3) :
    (T.leftUnit k).angle
      = (T.leftUnit (k + 1)).angle + ((Real.pi - T.angleAt (k + 1) : ℝ) : Real.Angle) := by
  have h1 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have hn : ¬ 0 < T.det := not_lt.mpr hT.le
  have hk : T.leftDir k = -(T.pts (k + 1) - T.pts k) := by
    unfold Tri.leftDir; rw [if_neg hn]; abel
  have hk1 : T.leftDir (k + 1) = -(T.pts (k + 2) - T.pts (k + 1)) := by
    unfold Tri.leftDir; rw [if_neg hn, h1]; abel
  have hang : InnerProductGeometry.angle (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts (k + 1))
      = InnerProductGeometry.angle (-(T.pts (k + 2) - T.pts (k + 1))) (-(T.pts (k + 1) - T.pts k)) := by
    rw [InnerProductGeometry.angle_neg_neg, InnerProductGeometry.angle_comm]
  rw [Tri.leftUnit_angle, Tri.leftUnit_angle, T.pi_sub_angleAt k, hk, hk1, hang]
  refine arg_turn ?_ ?_ ?_
  · rw [← hk1]; exact T.leftDir_ne_zero (k + 1)
  · rw [← hk]; exact T.leftDir_ne_zero k
  · have hc := T.cross_consecutive k
    simp only [cross, PiLp.neg_apply] at hc ⊢
    linarith
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
structure GridChar (R : Type*) [CommRing R] where
  L : AddSubgroup Real.Angle
  pi_mem : ((Real.pi : ℝ) : Real.Angle) ∈ L
  ψ : AddChar L R
  ψ_pi : ψ ⟨((Real.pi : ℝ) : Real.Angle), pi_mem⟩ = -1
  anchor : Real.Angle
namespace GridChar
variable {R : Type*} [CommRing R] (G : GridChar R)
noncomputable def chi (θ : Real.Angle) : R := if h : θ ∈ G.L then G.ψ ⟨θ, h⟩ else 0
theorem chi_of_mem {θ : Real.Angle} (h : θ ∈ G.L) : G.chi θ = G.ψ ⟨θ, h⟩ := dif_pos h
theorem chi_add {l l' : Real.Angle} (hl : l ∈ G.L) (hl' : l' ∈ G.L) :
    G.chi (l + l') = G.chi l * G.chi l' := by
  rw [G.chi_of_mem (G.L.add_mem hl hl'), G.chi_of_mem hl, G.chi_of_mem hl']
  exact AddChar.map_add_eq_mul G.ψ ⟨l, hl⟩ ⟨l', hl'⟩
theorem chi_zero : G.chi 0 = 1 := by
  rw [G.chi_of_mem G.L.zero_mem]
  exact AddChar.map_zero_eq_one G.ψ
theorem chi_pi : G.chi ((Real.pi : ℝ) : Real.Angle) = -1 := by
  rw [G.chi_of_mem G.pi_mem]
  exact G.ψ_pi
noncomputable def rep (θ : Real.Angle) : Real.Angle :=
  if θ - G.anchor ∈ G.L then G.anchor else (QuotientAddGroup.mk θ : Real.Angle ⧸ G.L).out
theorem sub_rep_mem (θ : Real.Angle) : θ - G.rep θ ∈ G.L := by
  unfold rep
  split_ifs with h
  · exact h
  · obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_mul G.L θ
    rw [hl, show θ - (θ + (l : Real.Angle)) = -(l : Real.Angle) by abel]
    exact G.L.neg_mem l.2
theorem rep_add (θ : Real.Angle) {l : Real.Angle} (hl : l ∈ G.L) : G.rep (θ + l) = G.rep θ := by
  unfold rep
  have hiff : (θ + l - G.anchor ∈ G.L) ↔ (θ - G.anchor ∈ G.L) := by
    rw [show θ + l - G.anchor = (θ - G.anchor) + l by abel]
    exact G.L.add_mem_cancel_right hl
  have hmk : (QuotientAddGroup.mk (θ + l) : Real.Angle ⧸ G.L) = QuotientAddGroup.mk θ :=
    QuotientAddGroup.mk_add_of_mem θ hl
  by_cases h : θ - G.anchor ∈ G.L
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, hmk]
noncomputable def val (θ : Real.Angle) : R := G.chi (θ - G.rep θ)
theorem val_add (θ : Real.Angle) {l : Real.Angle} (hl : l ∈ G.L) :
    G.val (θ + l) = G.chi l * G.val θ := by
  unfold val
  rw [G.rep_add θ hl, show θ + l - G.rep θ = (θ - G.rep θ) + l by abel,
    G.chi_add (G.sub_rep_mem θ) hl, mul_comm]
theorem val_anchor : G.val G.anchor = 1 := by
  have h : G.rep G.anchor = G.anchor := by
    unfold rep
    rw [if_pos (by rw [sub_self]; exact G.L.zero_mem)]
  unfold val
  rw [h, sub_self, G.chi_zero]
noncomputable def weight (d : Dir) : R := G.val d.angle
theorem weight_odd (d : Dir) : G.weight (Dir.neg d) = - G.weight d := by
  unfold weight
  rw [Dir.angle_neg, G.val_add _ G.pi_mem, G.chi_pi, neg_one_mul]
theorem val_sq (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (θ : Real.Angle) :
    G.val θ * G.val θ = 1 :=
  hsq _ (G.sub_rep_mem θ)
end GridChar
def signChar {A : Type*} [AddCommGroup A] (χ : A →+ ZMod 2) : AddChar A ℝ where
  toFun x := if χ x = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro a b
    simp only [map_add]
    have hcase : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    rcases hcase (χ a) with h1 | h1 <;> rcases hcase (χ b) with h2 | h2 <;>
      simp [h1, h2, h11, h10]
theorem signChar_apply {A : Type*} [AddCommGroup A] (χ : A →+ ZMod 2) (x : A) :
    signChar χ x = if χ x = 0 then 1 else -1 := rfl
noncomputable def rangePre {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle) (x : φ.range) : A :=
  Classical.choose (AddMonoidHom.mem_range.mp x.2)
theorem rangePre_spec {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle) (x : φ.range) :
    φ (rangePre φ x) = x :=
  Classical.choose_spec (AddMonoidHom.mem_range.mp x.2)
noncomputable def rangeChar {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) : φ.range →+ ZMod 2 where
  toFun x := χ (rangePre φ x)
  map_zero' := by
    have h := rangePre_spec φ 0
    exact hker _ (by rw [h]; rfl)
  map_add' := by
    intro x y
    have hx := rangePre_spec φ x
    have hy := rangePre_spec φ y
    have hxy := rangePre_spec φ (x + y)
    have h0 : φ (rangePre φ (x + y) - rangePre φ x - rangePre φ y) = 0 := by
      rw [map_sub, map_sub, hxy, hx, hy, AddSubgroup.coe_add]
      abel
    have h1 := hker _ h0
    rw [map_sub, map_sub] at h1
    linear_combination h1
theorem rangeChar_apply {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) (a : A) :
    rangeChar φ χ hker ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩ = χ a := by
  show χ (rangePre φ ⟨φ a, _⟩) = χ a
  have hs := rangePre_spec φ ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  have h0 : φ (rangePre φ ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩ - a) = 0 := by
    rw [map_sub, hs]; exact sub_self _
  have h1 := hker _ h0
  rw [map_sub] at h1
  linear_combination h1
noncomputable def GridChar.ofHom {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) (a₀ : A)
    (hπ : φ a₀ = ((Real.pi : ℝ) : Real.Angle)) (hχ : χ a₀ = 1) (anchor : Real.Angle) :
    GridChar ℝ where
  L := φ.range
  pi_mem := AddMonoidHom.mem_range.mpr ⟨a₀, hπ⟩
  ψ := signChar (rangeChar φ χ hker)
  ψ_pi := by
    have h := rangeChar_apply φ χ hker a₀
    have e : (⟨((Real.pi : ℝ) : Real.Angle), AddMonoidHom.mem_range.mpr ⟨a₀, hπ⟩⟩ : φ.range)
        = ⟨φ a₀, AddMonoidHom.mem_range.mpr ⟨a₀, rfl⟩⟩ := Subtype.ext hπ.symm
    rw [e, signChar_apply, h, hχ]
    simp
  anchor := anchor
theorem GridChar.ofHom_chi {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) (a₀ : A)
    (hπ : φ a₀ = ((Real.pi : ℝ) : Real.Angle)) (hχ : χ a₀ = 1) (anchor : Real.Angle) (a : A) :
    (GridChar.ofHom φ χ hker a₀ hπ hχ anchor).chi (φ a) = if χ a = 0 then 1 else -1 := by
  rw [GridChar.chi_of_mem _ (AddMonoidHom.mem_range.mpr ⟨a, rfl⟩)]
  show signChar (rangeChar φ χ hker) ⟨φ a, _⟩ = _
  rw [signChar_apply, rangeChar_apply]
theorem GridChar.ofHom_sq {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) (a₀ : A)
    (hπ : φ a₀ = ((Real.pi : ℝ) : Real.Angle)) (hχ : χ a₀ = 1) (anchor : Real.Angle) :
    ∀ l ∈ (GridChar.ofHom φ χ hker a₀ hπ hχ anchor).L,
      (GridChar.ofHom φ χ hker a₀ hπ hχ anchor).chi l
        * (GridChar.ofHom φ χ hker a₀ hπ hχ anchor).chi l = 1 := by
  intro l hl
  obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hl
  rw [GridChar.ofHom_chi]
  split_ifs <;> norm_num
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
open MeasureTheory Set
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
noncomputable def Dissection.overlap (D : Dissection N) (e e' : Fin N × Fin 3) : ℝ :=
  ((Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e ∩ D.eSet e')).toReal
theorem Dissection.overlap_comm (D : Dissection N) (e e' : Fin N × Fin 3) :
    D.overlap e e' = D.overlap e' e := by
  unfold Dissection.overlap
  rw [Set.inter_comm]
theorem Dissection.opposite_cover (D : Dissection N) {e : Fin N × Fin 3} (he : e ∈ D.intEdges) :
    ∑ e' ∈ D.intEdges.filter (fun e' => D.eDir e' = Dir.neg (D.eDir e)),
        (Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e' ∩ D.eSet e)
      = (Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e) := by
  refine sum_hausdorff_of_partition _ (fun e' => D.eSet e' ∩ D.eSet e) (D.eSet e) D.vertexSet
    D.vertexSet_finite ?_ ?_ ?_ ?_
  · intro e' _
    exact (((D.tile e'.1).isClosed_edge e'.2).inter
      ((D.tile e.1).isClosed_edge e.2)).measurableSet
  · intro e₁ h₁ e₂ h₂ hne
    have hd₁ := (Finset.mem_filter.mp h₁).2
    have hd₂ := (Finset.mem_filter.mp h₂).2
    exact (D.sameDir_subsingleton hne (hd₁.trans hd₂.symm)).anti
      (fun y hy => ⟨hy.1.1, hy.2.1⟩)
  · intro e' _
    exact Set.inter_subset_right
  · rintro x ⟨hx, hxv⟩
    have hnv := D.notMem_vertexSet hxv
    have hxint : x ∈ interior D.target.carrier :=
      D.mem_interior_of_mem_intEdges he hx (hnv _ _) (hnv _ _)
    have hxd : x ∈ D.dirSet (D.eDir e) := by
      unfold Dissection.dirSet
      exact ⟨Set.mem_iUnion.mpr ⟨e.1, Set.mem_iUnion.mpr ⟨e.2, Set.mem_iUnion.mpr ⟨rfl, hx⟩⟩⟩,
        hxint⟩
    have hxd' := (D.dirSet_sub D.pos (D.eDir e) ⟨hxd, hxv⟩).1
    obtain ⟨i, k, hik, hxik⟩ := D.mem_dirSet _ hxd'
    refine Set.mem_iUnion₂.mpr ⟨(i, k), ?_, hxik, hx⟩
    rw [Finset.mem_filter]
    exact ⟨D.mem_intEdges_of_interior (e := (i, k)) hxik hxint, hik⟩
theorem Dissection.opposite_cover_real (D : Dissection N) {e : Fin N × Fin 3}
    (he : e ∈ D.intEdges) :
    ∑ e' ∈ D.intEdges, (if D.eDir e' = Dir.neg (D.eDir e) then D.overlap e' e else 0)
      = D.eLen e := by
  rw [← Finset.sum_filter]
  have hfin : ∀ e' ∈ D.intEdges.filter (fun e' => D.eDir e' = Dir.neg (D.eDir e)),
      (Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e' ∩ D.eSet e) ≠ ⊤ := by
    intro e' _
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    rw [show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge]
    exact edist_ne_top _ _
  unfold Dissection.overlap
  rw [← ENNReal.toReal_sum hfin, D.opposite_cover he,
    show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]
  rfl
theorem Dissection.interior_flux_zero (D : Dissection N) (f : Dir → E)
    (hodd : ∀ d, f (Dir.neg d) = - f d) :
    ∑ e ∈ D.intEdges, D.eLen e • f (D.eDir e) = 0 := by
  set I := D.intEdges with hI
  let A : Fin N × Fin 3 → Fin N × Fin 3 → ℝ := fun e e' =>
    if D.eDir e' = Dir.neg (D.eDir e) then D.overlap e' e else 0
  set X := ∑ e ∈ I, D.eLen e • f (D.eDir e) with hX
  have h1 : X = ∑ e ∈ I, ∑ e' ∈ I, A e e' • f (D.eDir e) := by
    refine Finset.sum_congr rfl fun e he => ?_
    rw [← Finset.sum_smul]
    congr 1
    exact (D.opposite_cover_real he).symm
  have hterm : ∀ e e', A e e' • f (D.eDir e) = -(A e' e • f (D.eDir e')) := by
    intro e e'
    by_cases h : D.eDir e' = Dir.neg (D.eDir e)
    · have h' : D.eDir e = Dir.neg (D.eDir e') := by rw [h, Dir.neg_involutive (D.eDir e)]
      have hA : A e e' = D.overlap e' e := if_pos h
      have hA' : A e' e = D.overlap e e' := if_pos h'
      rw [hA, hA', h', hodd, D.overlap_comm e' e, smul_neg]
    · have h' : ¬ D.eDir e = Dir.neg (D.eDir e') := fun h'' =>
        h (by rw [h'', Dir.neg_involutive (D.eDir e')])
      have hA : A e e' = 0 := if_neg h
      have hA' : A e' e = 0 := if_neg h'
      rw [hA, hA', zero_smul, zero_smul, neg_zero]
  have h2 : X = -X := by
    calc X = ∑ e ∈ I, ∑ e' ∈ I, A e e' • f (D.eDir e) := h1
      _ = ∑ e' ∈ I, ∑ e ∈ I, A e e' • f (D.eDir e) := Finset.sum_comm
      _ = ∑ e' ∈ I, ∑ e ∈ I, -(A e' e • f (D.eDir e')) :=
          Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun e _ => hterm e e'
      _ = -∑ e' ∈ I, ∑ e ∈ I, A e' e • f (D.eDir e') := by
          simp only [Finset.sum_neg_distrib]
      _ = -X := by rw [h1]
  have h3 : (2:ℝ) • X = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h2]
    exact neg_add_cancel X
  calc X = (2:ℝ)⁻¹ • ((2:ℝ) • X) := by
        rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
    _ = 0 := by rw [h3, smul_zero]
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
open MeasureTheory Set
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
theorem unit_smul_of_pos {u v : Plane} {c : ℝ} (hc : 0 < c) (hu : u ≠ 0) (hv : v = c • u) :
    ‖v‖⁻¹ • v = ‖u‖⁻¹ • u := by
  have hun : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hcne : c ≠ 0 := ne_of_gt hc
  have hune : ‖u‖ ≠ 0 := ne_of_gt hun
  subst hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
  congr 1
  field_simp
theorem Dissection.eDir_of_side (D : Dissection N) {e : Fin N × Fin 3} {j : Fin 3}
    (h : D.eSet e ⊆ D.target.edge j) : D.eDir e = D.target.leftUnit j := by
  have hsucc : ∀ i : Fin 3, i ≠ i + 1 := by decide
  have hshift : ∀ i : Fin 3, i + 2 + 1 = i := by decide
  have hab : (D.tile e.1).pts e.2 ≠ (D.tile e.1).pts (e.2 + 1) := fun hh =>
    hsucc e.2 ((D.tile e.1).indep.injective hh)
  have ha : (D.tile e.1).pts e.2 ∈ (D.tile e.1).edge e.2 := left_mem_segment ℝ _ _
  have hb : (D.tile e.1).pts (e.2 + 1) ∈ (D.tile e.1).edge e.2 := right_mem_segment ℝ _ _
  obtain ⟨hxT, hxa, hxb⟩ := mem_ne_ends_of_avg hab ha hb
  obtain ⟨hzT, hpT⟩ := (D.tile e.1).onEdge_param (k := e.2) hxT hxa hxb
  have haS : (D.tile e.1).pts e.2 ∈ D.target.edge j := h ha
  have hbS : (D.tile e.1).pts (e.2 + 1) ∈ D.target.edge j := h hb
  obtain ⟨hxS, hxA, hxB⟩ := mem_ne_ends_of_avg hab haS hbS
  obtain ⟨hzS, hpS⟩ := D.target.onEdge_param (k := j) hxS hxA hxB
  obtain ⟨g, c, hg, hle, hj, hj1, hj2⟩ := exists_supporting D.target j
  have hgx : g (((1:ℝ)/2) • (D.tile e.1).pts e.2 + ((1:ℝ)/2) • (D.tile e.1).pts (e.2 + 1))
      = c := by
    have hS := target_contact_side D.target g c hle hj hj1 hj2
    have hmem : ((1:ℝ)/2) • (D.tile e.1).pts e.2 + ((1:ℝ)/2) • (D.tile e.1).pts (e.2 + 1)
        ∈ {y ∈ D.target.carrier | g y = c} := by
      rw [hS]; exact hxS
    exact hmem.2
  have hleT : ∀ y ∈ (D.tile e.1).carrier, g y ≤ c := fun y hy =>
    hle y (tile_subset_target D e.1 hy)
  have hinT : ∀ v, g v < 0 → 0 < cross ((D.tile e.1).leftDir e.2) v := by
    intro v hv
    have := (D.tile e.1).edge_inward g c hg hleT hzT hpT hgx hv
    rwa [hshift] at this
  have hinS : ∀ v, g v < 0 → 0 < cross (D.target.leftDir j) v := by
    intro v hv
    have := D.target.edge_inward g c hg hle hzS hpS hgx hv
    rwa [hshift] at this
  have hnegcross : ∀ w v : Plane, cross w (-v) = - cross w v := by
    intro w v; simp only [cross, PiLp.neg_apply]; ring
  have hdisjT : ∀ v, ¬ (0 < crossL ((D.tile e.1).leftDir e.2) v ∧ 0 < g v) := by
    rintro v ⟨h1, h2⟩
    have h3 := hinT (-v) (by rw [map_neg]; linarith)
    rw [crossL_apply] at h1
    rw [hnegcross] at h3
    linarith
  have hdisjS : ∀ v, ¬ (0 < crossL (D.target.leftDir j) v ∧ 0 < g v) := by
    rintro v ⟨h1, h2⟩
    have h3 := hinS (-v) (by rw [map_neg]; linarith)
    rw [crossL_apply] at h1
    rw [hnegcross] at h3
    linarith
  obtain ⟨c₁, hc₁, hgT⟩ := proportional_of_disjoint_pos (crossL ((D.tile e.1).leftDir e.2)) g
    (crossL_ne_zero ((D.tile e.1).leftDir_ne_zero e.2)) hg hdisjT
  obtain ⟨c₂, hc₂, hgS⟩ := proportional_of_disjoint_pos (crossL (D.target.leftDir j)) g
    (crossL_ne_zero (D.target.leftDir_ne_zero j)) hg hdisjS
  have hc₂ne : c₂ ≠ 0 := ne_of_lt hc₂
  have hprop : D.target.leftDir j = (c₁ / c₂) • (D.tile e.1).leftDir e.2 := by
    have hzero : ∀ v, cross (D.target.leftDir j - (c₁ / c₂) • (D.tile e.1).leftDir e.2) v = 0 := by
      intro v
      have e1 := hgT v
      have e2 := hgS v
      rw [crossL_apply] at e1 e2
      have hrel : cross (D.target.leftDir j) v = (c₁ / c₂) * cross ((D.tile e.1).leftDir e.2) v := by
        rw [div_mul_eq_mul_div, eq_div_iff hc₂ne]
        linear_combination e1 - e2
      simp only [cross, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hrel ⊢
      linear_combination hrel
    exact sub_eq_zero.mp (eq_zero_of_cross_eq_zero hzero)
  have hpos : 0 < c₁ / c₂ := div_pos_of_neg_of_neg hc₁ hc₂
  have hunit := unit_smul_of_pos hpos ((D.tile e.1).leftDir_ne_zero e.2) hprop
  apply Subtype.ext
  show ‖(D.tile e.1).leftDir e.2‖⁻¹ • (D.tile e.1).leftDir e.2
    = ‖D.target.leftDir j‖⁻¹ • D.target.leftDir j
  exact hunit.symm
theorem Dissection.side_len_sum (D : Dissection N) (j : Fin 3) :
    ∑ e ∈ D.sideEdges j, D.eLen e = dist (D.target.pts j) (D.target.pts (j + 1)) := by
  obtain ⟨g, c, hg, hle, hj, hj1, hj2⟩ := exists_supporting D.target j
  have hS : {x ∈ D.target.carrier | g x = c} = D.target.edge j :=
    target_contact_side D.target g c hle hj hj1 hj2
  have hmemS : ∀ e ∈ D.sideEdges j, D.eSet e ⊆ D.target.edge j := fun e he => by
    unfold Dissection.sideEdges at he
    exact (Finset.mem_filter.mp he).2
  have hon : ∀ e ∈ D.sideEdges j, ∀ y ∈ (D.tile e.1).edge e.2, g y = c := by
    intro e he y hy
    have hy' : y ∈ {x ∈ D.target.carrier | g x = c} := by rw [hS]; exact hmemS e he hy
    exact hy'.2
  have hleT : ∀ e : Fin N × Fin 3, ∀ y ∈ (D.tile e.1).carrier, g y ≤ c :=
    fun e y hy => hle y (tile_subset_target D e.1 hy)
  have hcov : D.target.edge j \ ∅ ⊆ ⋃ e ∈ D.sideEdges j, D.eSet e := by
    rintro y ⟨hy, -⟩
    obtain ⟨part, hpart⟩ := hasEdgeChains_edge D j
    have hy' := (Set.ext_iff.mp hpart y).mpr hy
    obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy'
    refine Set.mem_iUnion₂.mpr ⟨e, ?_, hye⟩
    unfold Dissection.sideEdges
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun z hz => ?_⟩
    exact (Set.ext_iff.mp hpart z).mp (Set.mem_iUnion₂.mpr ⟨e, he, hz⟩)
  have hsum := sum_hausdorff_of_partition (D.sideEdges j) D.eSet (D.target.edge j) ∅
    Set.finite_empty
    (fun e _ => ((D.tile e.1).isClosed_edge e.2).measurableSet)
    (fun e₁ h₁ e₂ h₂ hne => D.sameside_edges_subsingleton g c hg hne (hleT e₁) (hleT e₂)
      (hon e₁ h₁) (hon e₂ h₂))
    hmemS hcov
  have hfin : ∀ e ∈ D.sideEdges j,
      (Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e) ≠ ⊤ := by
    intro e _
    rw [show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge]
    exact edist_ne_top _ _
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum hfin, Tri.hausdorff_edge, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg] at hreal
  rw [← hreal]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]
  rfl
theorem Dissection.side_flux (D : Dissection N) (f : Dir → E) :
    ∑ j : Fin 3, ∑ e ∈ D.sideEdges j, D.eLen e • f (D.eDir e) = D.target.flux f := by
  unfold Tri.flux
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∑ e ∈ D.sideEdges j, D.eLen e • f (D.eDir e)
      = ∑ e ∈ D.sideEdges j, D.eLen e • f (D.target.leftUnit j) := by
    refine Finset.sum_congr rfl fun e he => ?_
    unfold Dissection.sideEdges at he
    rw [D.eDir_of_side (Finset.mem_filter.mp he).2]
  rw [h1, ← Finset.sum_smul, D.side_len_sum j]
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
theorem Dissection.flux_cancel (D : Dissection N) (f : Dir → E)
    (hodd : ∀ d, f (Dir.neg d) = - f d) :
    ∑ i, (D.tile i).flux f = D.target.flux f := by
  rw [D.flux_sum_eq, D.sum_split, D.interior_flux_zero f hodd, zero_add, D.side_flux]
theorem CongruentDissection.flux_cancel (D : CongruentDissection N) (f : Dir → E)
    (hodd : ∀ d, f (Dir.neg d) = - f d) :
    ∑ i, (D.tile i).flux f = D.target.flux f :=
  D.toDissection.flux_cancel f hodd
end Erdos634.Geometry
end

section
namespace Erdos634.InvariantCore
open Finset
theorem integrality_parity (N : ℕ) (sgn : Fin N → ℤ) (hs : ∀ i, sgn i = 1 ∨ sgn i = -1) :
    (2 : ℤ) ∣ (∑ i, sgn i) - (N : ℤ) := by
  have hsum : ∑ i : Fin N, (sgn i - 1) = (∑ i, sgn i) - (N : ℤ) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [← hsum]
  refine Finset.dvd_sum ?_
  intro i _
  rcases hs i with h | h <;> rw [h] <;> decide
end Erdos634.InvariantCore
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ}
theorem Tri.pi_sub_angleAt_mem (G : GridChar ℝ) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3) :
    ((Real.pi - T.angleAt k : ℝ) : Real.Angle) ∈ G.L := by
  rw [Real.Angle.coe_sub]
  exact G.L.sub_mem G.pi_mem (h k)
theorem Tri.flux_grid_of_pos (G : GridChar ℝ) (T : Tri) (hT : 0 < T.det)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    T.flux G.weight = G.weight (T.leftUnit 0) *
      (T.oppLen 2 + G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * T.oppLen 0
        + G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle)
          * G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * T.oppLen 1) := by
  have t1 := T.leftUnit_turn_of_pos hT 0
  have t2 := T.leftUnit_turn_of_pos hT 1
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t1 t2
  have w1 : G.weight (T.leftUnit 1)
      = G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * G.weight (T.leftUnit 0) := by
    unfold GridChar.weight
    rw [t1, G.val_add _ (T.pi_sub_angleAt_mem G h 1)]
  have w2 : G.weight (T.leftUnit 2)
      = G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * G.weight (T.leftUnit 1) := by
    unfold GridChar.weight
    rw [t2, G.val_add _ (T.pi_sub_angleAt_mem G h 2)]
  unfold Tri.flux Tri.oppLen
  rw [Fin.sum_univ_three]
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 2 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl, smul_eq_mul]
  rw [w2, w1]
  ring
theorem Tri.flux_grid_of_neg (G : GridChar ℝ) (T : Tri) (hT : T.det < 0)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    T.flux G.weight = G.weight (T.leftUnit 2) *
      (T.oppLen 1 + G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * T.oppLen 0
        + G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle)
          * G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * T.oppLen 2) := by
  have t0 := T.leftUnit_turn_of_neg hT 0
  have t1 := T.leftUnit_turn_of_neg hT 1
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t0 t1
  have w1 : G.weight (T.leftUnit 1)
      = G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * G.weight (T.leftUnit 2) := by
    unfold GridChar.weight
    rw [t1, G.val_add _ (T.pi_sub_angleAt_mem G h 2)]
  have w0 : G.weight (T.leftUnit 0)
      = G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * G.weight (T.leftUnit 1) := by
    unfold GridChar.weight
    rw [t0, G.val_add _ (T.pi_sub_angleAt_mem G h 1)]
  unfold Tri.flux Tri.oppLen
  rw [Fin.sum_univ_three]
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 2 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl, smul_eq_mul]
  rw [w0, w1]
  ring
noncomputable def GridChar.tileValue (G : GridChar ℝ) (T : Tri) : ℝ :=
  ∑ k : Fin 3, G.chi ((Real.pi - T.angleAt k : ℝ) : Real.Angle) * T.oppLen k
theorem Tri.chi_prod (G : GridChar ℝ) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle)
      * G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle)
      * G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) = 1 := by
  have m0 := T.pi_sub_angleAt_mem G h 0
  have m1 := T.pi_sub_angleAt_mem G h 1
  have m2 := T.pi_sub_angleAt_mem G h 2
  rw [← G.chi_add m0 m1, ← G.chi_add (G.L.add_mem m0 m1) m2, ← Real.Angle.coe_add,
    ← Real.Angle.coe_add]
  have hs : (Real.pi - T.angleAt 0) + (Real.pi - T.angleAt 1) + (Real.pi - T.angleAt 2)
      = 2 * Real.pi := by linarith [T.angleAt_sum]
  rw [hs, Real.Angle.coe_two_pi, G.chi_zero]
theorem Tri.flux_grid_pm (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    T.flux G.weight = G.tileValue T ∨ T.flux G.weight = - G.tileValue T := by
  have hc0 := hsq _ (T.pi_sub_angleAt_mem G h 0)
  have hc1 := hsq _ (T.pi_sub_angleAt_mem G h 1)
  have hc2 := hsq _ (T.pi_sub_angleAt_mem G h 2)
  have hprod := T.chi_prod G h
  have hK : G.tileValue T
      = G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle) * T.oppLen 0
        + G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * T.oppLen 1
        + G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * T.oppLen 2 := by
    unfold GridChar.tileValue
    rw [Fin.sum_univ_three]
  set c0 := G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle) with hc0def
  set c1 := G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) with hc1def
  set c2 := G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) with hc2def
  rcases T.det_pos_or_neg with hT | hT
  · rw [T.flux_grid_of_pos G hT h, hK]
    set w := G.weight (T.leftUnit 0) with hwdef
    have hw : w * w = 1 := G.val_sq hsq _
    have e1 : c0 * c2 = c1 := by linear_combination c1 * hprod - (c0 * c2) * hc1
    have key : w * (T.oppLen 2 + c1 * T.oppLen 0 + c1 * c2 * T.oppLen 1)
        = (w * c2) * (c0 * T.oppLen 0 + c1 * T.oppLen 1 + c2 * T.oppLen 2) := by
      linear_combination (-(w * T.oppLen 0)) * e1 - (w * T.oppLen 2) * hc2
    have hs : (w * c2) * (w * c2) = 1 := by linear_combination c2 * c2 * hw + hc2
    rw [key]
    rcases mul_self_eq_one_iff.mp hs with h1 | h1
    · left; rw [h1, one_mul]
    · right; rw [h1, neg_one_mul]
  · rw [T.flux_grid_of_neg G hT h, hK]
    set w := G.weight (T.leftUnit 2) with hwdef
    have hw : w * w = 1 := G.val_sq hsq _
    have e2 : c0 * c1 = c2 := by linear_combination c2 * hprod - (c0 * c1) * hc2
    have key : w * (T.oppLen 1 + c2 * T.oppLen 0 + c2 * c1 * T.oppLen 2)
        = (w * c1) * (c0 * T.oppLen 0 + c1 * T.oppLen 1 + c2 * T.oppLen 2) := by
      linear_combination (-(w * T.oppLen 0)) * e2 - (w * T.oppLen 1) * hc1
    have hs : (w * c1) * (w * c1) = 1 := by linear_combination c1 * c1 * hw + hc1
    rw [key]
    rcases mul_self_eq_one_iff.mp hs with h1 | h1
    · left; rw [h1, one_mul]
    · right; rw [h1, neg_one_mul]
theorem Tri.Congruent.exists_perm {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k, T.angleAt k = U.angleAt (σ k) ∧ T.oppLen k = U.oppLen (σ k) := by
  obtain ⟨σ, hd⟩ := h.dist_eq
  refine ⟨σ, fun k => ?_⟩
  have hne1 : k + 1 ≠ k := by fin_cases k <;> decide
  have hne2 : k + 2 ≠ k := by fin_cases k <;> decide
  have hne12 : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  have hT1 : T.pts (k + 1) ≠ T.pts k := fun hh => hne1 (T.indep.injective hh)
  have hT2 : T.pts (k + 2) ≠ T.pts k := fun hh => hne2 (T.indep.injective hh)
  have hs1 : σ (k + 1) ≠ σ k := fun hh => hne1 (σ.injective hh)
  have hs2 : σ (k + 2) ≠ σ k := fun hh => hne2 (σ.injective hh)
  have hs12 : σ (k + 1) ≠ σ (k + 2) := fun hh => hne12 (σ.injective hh)
  have hang : T.angleAt k = cornerAngle (U.pts (σ (k + 1))) (U.pts (σ k)) (U.pts (σ (k + 2))) := by
    unfold Tri.angleAt cornerAngle
    exact angle_of_sss (hd (k + 1) k) (hd k (k + 2)) (hd (k + 1) (k + 2)) hT1 hT2
  have hopp : T.oppLen k = dist (U.pts (σ (k + 1))) (U.pts (σ (k + 2))) := hd (k + 1) (k + 2)
  have hsum : σ k + 1 ≠ σ k + 2 := by
    intro hh
    have := add_left_cancel hh
    exact absurd this (by decide)
  rcases fin3_cases _ _ hs1 with ha | ha
  · rcases fin3_cases _ _ hs2 with hb | hb
    · exact absurd (ha.trans hb.symm) hs12
    · refine ⟨?_, ?_⟩
      · rw [hang, ha, hb]; rfl
      · rw [hopp, ha, hb]; rfl
  · rcases fin3_cases _ _ hs2 with hb | hb
    · refine ⟨?_, ?_⟩
      · rw [hang, ha, hb]
        unfold Tri.angleAt cornerAngle
        exact EuclideanGeometry.angle_comm _ _ _
      · rw [hopp, ha, hb, dist_comm]; rfl
    · exact absurd (ha.trans hb.symm) hs12
theorem GridChar.tileValue_congr (G : GridChar ℝ) {T U : Tri} (h : T.Congruent U) :
    G.tileValue T = G.tileValue U := by
  obtain ⟨σ, hσ⟩ := h.exists_perm
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ
    (fun j => G.chi ((Real.pi - U.angleAt j : ℝ) : Real.Angle) * U.oppLen j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(hσ k).1, (hσ k).2]
theorem CongruentDissection.target_flux_signs (D : CongruentDissection N) (G : GridChar ℝ)
    (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1)
    (h : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    ∃ S : ℤ, (2 : ℤ) ∣ S - N ∧ |S| ≤ N ∧
      D.target.flux G.weight = (S : ℝ) * G.tileValue D.model := by
  set K := G.tileValue D.model with hKdef
  have htile : ∀ i, (D.tile i).flux G.weight = K ∨ (D.tile i).flux G.weight = -K := by
    intro i
    obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
    have hi : ∀ k, (((D.tile i).angleAt k : ℝ) : Real.Angle) ∈ G.L := fun k => by
      rw [(hσ k).1]; exact h _
    rw [hKdef, ← G.tileValue_congr (D.tiles_congruent i)]
    exact (D.tile i).flux_grid_pm G hsq hi
  let ε : Fin N → ℤ := fun i => if (D.tile i).flux G.weight = K then 1 else -1
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    by_cases hi : (D.tile i).flux G.weight = K
    · left; exact if_pos hi
    · right; exact if_neg hi
  have hεval : ∀ i, (D.tile i).flux G.weight = (ε i : ℝ) * K := by
    intro i
    by_cases hi : (D.tile i).flux G.weight = K
    · rw [show ε i = 1 from if_pos hi]; push_cast; rw [one_mul, hi]
    · rw [show ε i = -1 from if_neg hi]; push_cast
      rcases htile i with h1 | h1
      · exact absurd h1 hi
      · rw [h1, neg_one_mul]
  refine ⟨∑ i, ε i, InvariantCore.integrality_parity N ε hε, ?_, ?_⟩
  · calc |∑ i, ε i| ≤ ∑ i, |ε i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _i : Fin N, (1 : ℤ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rcases hε i with h1 | h1 <;> rw [h1] <;> rfl
      _ = N := by simp
  · rw [← D.flux_cancel G.weight G.weight_odd]
    rw [Finset.sum_congr rfl fun i _ => hεval i, ← Finset.sum_mul]
    push_cast
    rfl
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ}
namespace GridChar
variable (G : GridChar ℝ)
theorem chi_pi_sub (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) {θ : ℝ}
    (h : ((θ : ℝ) : Real.Angle) ∈ G.L) :
    G.chi ((Real.pi - θ : ℝ) : Real.Angle) = - G.chi ((θ : ℝ) : Real.Angle) := by
  have hneg : ((-θ : ℝ) : Real.Angle) ∈ G.L := by
    rw [Real.Angle.coe_neg]; exact G.L.neg_mem h
  have e : ((Real.pi - θ : ℝ) : Real.Angle)
      = ((Real.pi : ℝ) : Real.Angle) + ((-θ : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add, sub_eq_add_neg]
  have h0 : G.chi ((θ : ℝ) : Real.Angle) * G.chi ((-θ : ℝ) : Real.Angle) = 1 := by
    rw [← G.chi_add h hneg, ← Real.Angle.coe_add, add_neg_cancel, Real.Angle.coe_zero, G.chi_zero]
  have hs := hsq _ h
  have hsym : G.chi ((-θ : ℝ) : Real.Angle) = G.chi ((θ : ℝ) : Real.Angle) := by
    linear_combination (G.chi ((θ : ℝ) : Real.Angle)) * h0
      - (G.chi ((-θ : ℝ) : Real.Angle)) * hs
  rw [e, G.chi_add G.pi_mem hneg, G.chi_pi, hsym]
  ring
noncomputable def paperK (T : Tri) : ℝ :=
  - ∑ k : Fin 3, G.chi ((T.angleAt k : ℝ) : Real.Angle) * T.oppLen k
theorem tileValue_eq_paperK (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) : G.tileValue T = G.paperK T := by
  unfold tileValue paperK
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [G.chi_pi_sub hsq (h k)]
  ring
noncomputable def edgeSign (T : Tri) (k : Fin 3) : ℝ :=
  G.chi ((Real.pi - T.angleAt (k + 2) : ℝ) : Real.Angle) * G.weight (T.leftUnit k)
theorem edgeSign_eq_paper (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3) :
    G.edgeSign T k = - G.chi ((T.angleAt (k + 2) : ℝ) : Real.Angle) * G.weight (T.leftUnit k) := by
  unfold edgeSign
  rw [G.chi_pi_sub hsq (h (k + 2))]
end GridChar
theorem Tri.weight_succ_of_pos (G : GridChar ℝ) (T : Tri) (hT : 0 < T.det)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3) :
    G.weight (T.leftUnit (k + 1))
      = G.chi ((Real.pi - T.angleAt (k + 1) : ℝ) : Real.Angle) * G.weight (T.leftUnit k) := by
  unfold GridChar.weight
  rw [T.leftUnit_turn_of_pos hT k, G.val_add _ (T.pi_sub_angleAt_mem G h (k + 1))]
theorem Tri.weight_succ_of_neg (G : GridChar ℝ) (T : Tri) (hT : T.det < 0)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3) :
    G.weight (T.leftUnit k)
      = G.chi ((Real.pi - T.angleAt (k + 1) : ℝ) : Real.Angle) * G.weight (T.leftUnit (k + 1)) := by
  unfold GridChar.weight
  rw [T.leftUnit_turn_of_neg hT k, G.val_add _ (T.pi_sub_angleAt_mem G h (k + 1))]
theorem Tri.flux_eq_edgeSign (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3) :
    T.flux G.weight = G.edgeSign T k * G.tileValue T := by
  have hc0 := hsq _ (T.pi_sub_angleAt_mem G h 0)
  have hc1 := hsq _ (T.pi_sub_angleAt_mem G h 1)
  have hc2 := hsq _ (T.pi_sub_angleAt_mem G h 2)
  have hprod := T.chi_prod G h
  have hK : G.tileValue T
      = G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle) * T.oppLen 0
        + G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * T.oppLen 1
        + G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * T.oppLen 2 := by
    unfold GridChar.tileValue
    rw [Fin.sum_univ_three]
  unfold GridChar.edgeSign
  set c0 := G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle) with hc0def
  set c1 := G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) with hc1def
  set c2 := G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) with hc2def
  have e02 : c0 * c2 = c1 := by linear_combination c1 * hprod - (c0 * c2) * hc1
  have e01 : c0 * c1 = c2 := by linear_combination c2 * hprod - (c0 * c1) * hc2
  rcases T.det_pos_or_neg with hT | hT
  · have hF := T.flux_grid_of_pos G hT h
    have w1 := T.weight_succ_of_pos G hT h 0
    have w2 := T.weight_succ_of_pos G hT h 1
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at w1 w2
    rw [← hc1def] at w1
    rw [← hc2def] at w2
    rw [← hc1def, ← hc2def] at hF
    set w0 := G.weight (T.leftUnit 0)
    have key : T.flux G.weight = (c2 * w0) * G.tileValue T := by
      rw [hF, hK]
      linear_combination (-(w0 * T.oppLen 0)) * e02 - (w0 * T.oppLen 2) * hc2
    rw [key]
    fin_cases k
    · show (c2 * w0) * _ = (G.chi ((Real.pi - T.angleAt ((0 : Fin 3) + 2) : ℝ) : Real.Angle)
        * w0) * _
      rfl
    · show (c2 * w0) * _ = (G.chi ((Real.pi - T.angleAt ((1 : Fin 3) + 2) : ℝ) : Real.Angle)
        * G.weight (T.leftUnit 1)) * _
      rw [show (1 : Fin 3) + 2 = 0 from rfl, ← hc0def, w1]
      congr 1
      linear_combination (-w0) * e01
    · show (c2 * w0) * _ = (G.chi ((Real.pi - T.angleAt ((2 : Fin 3) + 2) : ℝ) : Real.Angle)
        * G.weight (T.leftUnit 2)) * _
      rw [show (2 : Fin 3) + 2 = 1 from rfl, ← hc1def, w2, w1]
      congr 1
      linear_combination (-(c2 * w0)) * hc1
  · have hF := T.flux_grid_of_neg G hT h
    have w0 := T.weight_succ_of_neg G hT h 0
    have w1 := T.weight_succ_of_neg G hT h 1
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at w0 w1
    rw [← hc1def] at w0
    rw [← hc2def] at w1
    rw [← hc1def, ← hc2def] at hF
    set w2 := G.weight (T.leftUnit 2)
    have key : T.flux G.weight = (c1 * w2) * G.tileValue T := by
      rw [hF, hK]
      linear_combination (-(w2 * T.oppLen 0)) * e01 - (w2 * T.oppLen 1) * hc1
    rw [key]
    fin_cases k
    · show (c1 * w2) * _ = (G.chi ((Real.pi - T.angleAt ((0 : Fin 3) + 2) : ℝ) : Real.Angle)
        * G.weight (T.leftUnit 0)) * _
      rw [show (0 : Fin 3) + 2 = 2 from rfl, ← hc2def, w0, w1]
      congr 1
      linear_combination (-(c1 * w2)) * hc2
    · show (c1 * w2) * _ = (G.chi ((Real.pi - T.angleAt ((1 : Fin 3) + 2) : ℝ) : Real.Angle)
        * G.weight (T.leftUnit 1)) * _
      rw [show (1 : Fin 3) + 2 = 0 from rfl, ← hc0def, w1]
      congr 1
      linear_combination (-w2) * e02
    · show (c1 * w2) * _ = (G.chi ((Real.pi - T.angleAt ((2 : Fin 3) + 2) : ℝ) : Real.Angle)
        * w2) * _
      rfl
theorem Tri.flux_eq_of_anchor (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3)
    (hanc : G.anchor = (T.leftUnit k).angle) :
    T.flux G.weight = - G.chi ((T.angleAt (k + 2) : ℝ) : Real.Angle) * G.paperK T := by
  rw [T.flux_eq_edgeSign G hsq h k, G.edgeSign_eq_paper hsq T h k, G.tileValue_eq_paperK hsq T h]
  have hw : G.weight (T.leftUnit k) = 1 := by
    unfold GridChar.weight; rw [← hanc]; exact G.val_anchor
  rw [hw, mul_one]
theorem CongruentDissection.triangle_boundary_anchor (D : CongruentDissection N)
    (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1)
    (hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L)
    (htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3)
    (hanc : G.anchor = (D.target.leftUnit k).angle) :
    ∃ S : ℤ, (2 : ℤ) ∣ S - N ∧ |S| ≤ N ∧
      (S : ℝ) * G.paperK D.model
        = - G.chi ((D.target.angleAt (k + 2) : ℝ) : Real.Angle) * G.paperK D.target := by
  obtain ⟨S, hS2, hSN, hSf⟩ := D.target_flux_signs G hsq hmodel
  refine ⟨S, hS2, hSN, ?_⟩
  rw [← G.tileValue_eq_paperK hsq _ hmodel, ← hSf]
  exact D.target.flux_eq_of_anchor G hsq htarget k hanc
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
open Set
variable {N : ℕ}
def Dissection.Adj (D : Dissection N) (i j : Fin N) : Prop :=
  i ≠ j ∧ ∃ (k l : Fin 3) (p q : Plane), p ≠ q ∧ p ∈ (D.tile i).edge k ∧ q ∈ (D.tile i).edge k ∧
    p ∈ (D.tile j).edge l ∧ q ∈ (D.tile j).edge l
def Dissection.ProperColouring (D : Dissection N) (ε : Fin N → ℤ) : Prop :=
  (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ i j, D.Adj i j → ε i = - ε j
theorem Dissection.Adj.leftUnit_neg {D : Dissection N} {i j : Fin N} (h : D.Adj i j) :
    ∃ k l : Fin 3, (D.tile j).leftUnit l = Dir.neg ((D.tile i).leftUnit k) := by
  obtain ⟨hne, k, l, p, q, hpq, h1, h2, h3, h4⟩ := h
  obtain ⟨-, hn1A, hn1B⟩ := mem_ne_ends_of_avg hpq h1 h2
  obtain ⟨-, hn2A, hn2B⟩ := mem_ne_ends_of_avg hpq h3 h4
  have hm1 : ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ∈ (D.tile i).edge k :=
    (mem_ne_ends_of_avg hpq h1 h2).1
  have hm2 : ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ∈ (D.tile j).edge l :=
    (mem_ne_ends_of_avg hpq h3 h4).1
  obtain ⟨hz₁, hp₁⟩ := (D.tile i).onEdge_param hm1 hn1A hn1B
  obtain ⟨hz₂, hp₂⟩ := (D.tile j).onEdge_param hm2 hn2A hn2B
  have hshift : ∀ k : Fin 3, k + 2 + 1 = k := by decide
  have hkey := D.leftUnit_neg hne hz₁ hp₁ hz₂ hp₂
  simp only [hshift] at hkey
  exact ⟨k, l, hkey⟩
theorem Tri.weight_const (G : GridChar ℝ) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L)
    (hext : ∀ k, G.chi ((Real.pi - T.angleAt k : ℝ) : Real.Angle) = 1) (k : Fin 3) :
    G.weight (T.leftUnit k) = G.weight (T.leftUnit 0) := by
  rcases T.det_pos_or_neg with hT | hT
  · have w1 := T.weight_succ_of_pos G hT h 0
    have w2 := T.weight_succ_of_pos G hT h 1
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at w1 w2
    rw [hext 1, one_mul] at w1
    rw [hext 2, one_mul] at w2
    fin_cases k
    · rfl
    · exact w1
    · exact w2.trans w1
  · have w0 := T.weight_succ_of_neg G hT h 0
    have w1 := T.weight_succ_of_neg G hT h 1
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at w0 w1
    rw [hext 1, one_mul] at w0
    rw [hext 2, one_mul] at w1
    fin_cases k
    · rfl
    · exact w0.symm
    · exact w1.symm.trans w0.symm
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
open Set
variable {N : ℕ}
theorem Tri.edge_of_not_interior (T : Tri) {x : Plane} (hx : x ∈ T.carrier)
    (hn : x ∉ interior T.carrier) : ∃ k : Fin 3, x ∈ T.edge k := by
  have hnn : ∀ j, 0 ≤ T.basis.coord j x := by
    have h : x ∈ T.carrier := hx
    rw [T.carrier_eq_nonneg_coord] at h
    exact h
  by_cases hpos : ∀ j, 0 < T.basis.coord j x
  · exfalso
    obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
    exact hn (mem_interior.mpr ⟨Metric.ball x r, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩)
  · push_neg at hpos
    obtain ⟨k, hk⟩ := hpos
    have h0 : T.basis.coord k x = 0 := le_antisymm hk (hnn k)
    refine ⟨k + 1, ?_⟩
    rw [Tri.edge, show k + 1 + 1 = k + 2 from by omega]
    exact Erdos634.BaseSelection.coord_zero_mem_segment T k x h0 hnn
theorem Tri.closure_interior_eq (T : Tri) : closure (interior T.carrier) = T.carrier := by
  rw [T.convex.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty]
  exact T.isCompact.isClosed.closure_eq
theorem Dissection.not_mem_interior_of_inter (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) :
    x ∉ interior (D.tile i).carrier := by
  intro hint
  have hcl : x ∈ closure (interior (D.tile j).carrier) := by
    rw [(D.tile j).closure_interior_eq]; exact hxj
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hcl _ isOpen_interior hint
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hy1 hy2
theorem Dissection.mem_edges_of_inter (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) :
    (∃ k, x ∈ (D.tile i).edge k) ∧ ∃ l, x ∈ (D.tile j).edge l :=
  ⟨(D.tile i).edge_of_not_interior hxi (D.not_mem_interior_of_inter hij hxi hxj),
   (D.tile j).edge_of_not_interior hxj (D.not_mem_interior_of_inter hij.symm hxj hxi)⟩
theorem Dissection.inter_finite_of_not_adj (D : Dissection N) {i j : Fin N} (hij : i ≠ j)
    (hna : ¬ D.Adj i j) : ((D.tile i).carrier ∩ (D.tile j).carrier).Finite := by
  by_contra hinf
  have hinf' : ((D.tile i).carrier ∩ (D.tile j).carrier).Infinite := hinf
  obtain ⟨s, hs, hcard⟩ := hinf'.exists_subset_card_eq 10
  let f : Plane → Fin 3 × Fin 3 := fun x =>
    if h : x ∈ (D.tile i).carrier ∩ (D.tile j).carrier then
      ((D.mem_edges_of_inter hij h.1 h.2).1.choose, (D.mem_edges_of_inter hij h.1 h.2).2.choose)
    else (0, 0)
  have hmaps : ∀ x ∈ s, f x ∈ (Finset.univ : Finset (Fin 3 × Fin 3)) := fun x _ => Finset.mem_univ _
  have hlt : (Finset.univ : Finset (Fin 3 × Fin 3)).card < s.card := by
    rw [hcard]; simp
  obtain ⟨p, hp, q, hq, hpq, hfe⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  have hpm : p ∈ (D.tile i).carrier ∩ (D.tile j).carrier := hs hp
  have hqm : q ∈ (D.tile i).carrier ∩ (D.tile j).carrier := hs hq
  simp only [f, dif_pos hpm, dif_pos hqm, Prod.mk.injEq] at hfe
  obtain ⟨hk, hl⟩ := hfe
  apply hna
  refine ⟨hij, (D.mem_edges_of_inter hij hpm.1 hpm.2).1.choose, (D.mem_edges_of_inter hij hpm.1 hpm.2).2.choose,
    p, q, hpq, (D.mem_edges_of_inter hij hpm.1 hpm.2).1.choose_spec, ?_,
    (D.mem_edges_of_inter hij hpm.1 hpm.2).2.choose_spec, ?_⟩
  · rw [hk]; exact (D.mem_edges_of_inter hij hqm.1 hqm.2).1.choose_spec
  · rw [hl]; exact (D.mem_edges_of_inter hij hqm.1 hqm.2).2.choose_spec
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
open MeasureTheory Set
private theorem line_ne_top (x f : Plane) : affineSpan ℝ ({x, f} : Set Plane) ≠ ⊤ := by
  intro h
  have hc : Collinear ℝ ({x, f} : Set Plane) := collinear_pair ℝ x f
  have hd : vectorSpan ℝ ({x, f} : Set Plane) = ⊤ := by
    rw [← direction_affineSpan, h, AffineSubspace.direction_top]
  have h1 : Module.rank ℝ (vectorSpan ℝ ({x, f} : Set Plane)) ≤ 1 := hc
  rw [hd, rank_top] at h1
  have h2 : Module.rank ℝ Plane = 2 := by
    rw [← Module.finrank_eq_rank]; simp
  rw [h2] at h1
  norm_num at h1
private theorem mem_line_of_seg {u v w : Plane} (hw : w ∈ segment ℝ u v) (hne : w ≠ u) :
    v ∈ affineSpan ℝ ({u, w} : Set Plane) := by
  obtain ⟨a, b, ha, hb, hab, hw⟩ := hw
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hne
    have : a = 1 := by linarith
    rw [← hw, this]; simp
  have ha' : a = 1 - b := by linarith
  have e : w -ᵥ u = b • (v - u) := by
    rw [← hw, vsub_eq_sub, ha', sub_smul, one_smul, smul_sub]; abel
  have : v = AffineMap.lineMap u w b⁻¹ := by
    rw [AffineMap.lineMap_apply, e, smul_smul, inv_mul_cancel₀ hb0, one_smul]
    simp [vadd_eq_add]
  rw [this]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
theorem no_split {R UA UB : Set Plane} (hR : Convex ℝ R) (hint : (interior R).Nonempty)
    (hA : IsClosed UA) (hB : IsClosed UB) (hU : UA ∪ UB = R) (hF : (UA ∩ UB).Finite) :
    UA ⊆ UB ∨ UB ⊆ UA := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hAB, hBA⟩ := hcon
  obtain ⟨x, hxA, hxB⟩ := Set.not_subset.mp hAB
  obtain ⟨y, hyB, hyA⟩ := Set.not_subset.mp hBA
  set F := UA ∩ UB with hFdef
  set bad : Set Plane := ⋃ f ∈ F, ((affineSpan ℝ ({x, f} : Set Plane) : Set Plane) ∪
    (affineSpan ℝ ({y, f} : Set Plane) : Set Plane)) with hbad
  have hbad0 : volume bad = 0 := by
    refine (measure_biUnion_null_iff hF.countable).2 fun f _ => ?_
    exact measure_union_null (Measure.addHaar_affineSubspace _ _ (line_ne_top _ _))
      (Measure.addHaar_affineSubspace _ _ (line_ne_top _ _))
  obtain ⟨z, hzint, hzbad⟩ : ∃ z ∈ interior R, z ∉ bad := by
    by_contra h
    push Not at h
    have := measure_mono_null h hbad0
    exact (isOpen_interior.measure_pos volume hint).ne' this
  have hxR : x ∈ R := hU ▸ Or.inl hxA
  have hyR : y ∈ R := hU ▸ Or.inr hyB
  have hzR : z ∈ R := interior_subset hzint
  have hxF : x ∉ F := fun h => hxB h.2
  have hyF : y ∉ F := fun h => hyA h.1
  set S : Set Plane := segment ℝ x z ∪ segment ℝ z y with hS
  have hSR : S ⊆ R := union_subset (hR.segment_subset hxR hzR) (hR.segment_subset hzR hyR)
  have hSF : S ∩ F = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro w ⟨hw, hwF⟩
    rcases hw with hw | hw
    · have hwx : w ≠ x := fun h => hxF (h ▸ hwF)
      exact hzbad (Set.mem_biUnion hwF (Or.inl (mem_line_of_seg hw hwx)))
    · have hwy : w ≠ y := fun h => hyF (h ▸ hwF)
      exact hzbad (Set.mem_biUnion hwF (Or.inr (mem_line_of_seg (segment_symm ℝ z y ▸ hw) hwy)))
  have hpre : IsPreconnected S :=
    ((convex_segment x z).isPreconnected).union z (right_mem_segment ℝ x z) (left_mem_segment ℝ z y)
      (convex_segment z y).isPreconnected
  have hsub : S ⊆ UA ∪ UB := hU ▸ hSR
  have hxS : x ∈ S := Or.inl (left_mem_segment ℝ x z)
  have hyS : y ∈ S := Or.inr (right_mem_segment ℝ z y)
  have := (isPreconnected_closed_iff.mp hpre) UA UB hA hB hsub ⟨x, hxS, hxA⟩ ⟨y, hyS, hyB⟩
  obtain ⟨w, hwS, hwA, hwB⟩ := this
  have : w ∈ S ∩ F := ⟨hwS, hwA, hwB⟩
  rw [hSF] at this
  exact this
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
variable {N : ℕ}
def Dissection.AdjConnected (D : Dissection N) : Prop :=
  ∀ i j : Fin N, Relation.ReflTransGen (fun a b => D.Adj a b) i j
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
open MeasureTheory Set
variable {N : ℕ}
theorem Dissection.adjConnected (D : Dissection N) : D.AdjConnected := by
  intro i j
  by_contra hij
  set A : Set (Fin N) := {a | Relation.ReflTransGen (fun a b => D.Adj a b) i a} with hA
  set UA : Set Plane := ⋃ a ∈ A, (D.tile a).carrier with hUA
  set UB : Set Plane := ⋃ b ∈ Aᶜ, (D.tile b).carrier with hUB
  have hiA : i ∈ A := Relation.ReflTransGen.refl
  have hjA : j ∈ Aᶜ := hij
  have hU : UA ∪ UB = D.target.carrier := by
    rw [← D.covers]
    ext x
    simp only [hUA, hUB, mem_union, mem_iUnion, exists_prop]
    constructor
    · rintro (⟨a, _, h⟩ | ⟨a, _, h⟩) <;> exact ⟨a, h⟩
    · rintro ⟨a, h⟩
      by_cases ha : a ∈ A
      · exact Or.inl ⟨a, ha, h⟩
      · exact Or.inr ⟨a, ha, h⟩
  have hclA : IsClosed UA :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun a _ => (D.tile a).isCompact.isClosed
  have hclB : IsClosed UB :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun a _ => (D.tile a).isCompact.isClosed
  have hF : (UA ∩ UB).Finite := by
    have hfin : (⋃ a ∈ A, ⋃ b ∈ Aᶜ, ((D.tile a).carrier ∩ (D.tile b).carrier)).Finite := by
      refine Set.Finite.biUnion (Set.toFinite _) fun a ha => Set.Finite.biUnion (Set.toFinite _) fun b hb => ?_
      have hab : a ≠ b := fun h => hb (h ▸ ha)
      refine D.inter_finite_of_not_adj hab fun hadj => hb ?_
      exact Relation.ReflTransGen.tail ha hadj
    refine hfin.subset ?_
    rintro x ⟨hxA, hxB⟩
    simp only [hUA, hUB, mem_iUnion, exists_prop] at hxA hxB
    obtain ⟨a, ha, hxa⟩ := hxA
    obtain ⟨b, hb, hxb⟩ := hxB
    simp only [mem_iUnion, exists_prop]
    exact ⟨a, ha, b, hb, hxa, hxb⟩
  have hnull : ∀ k : Fin N, (D.tile k).carrier ⊆ UA ∩ UB → False := by
    intro k hk
    have h0 : volume (UA ∩ UB) = 0 := hF.measure_zero volume
    have := measure_mono_null hk h0
    exact (D.tile k).volume_pos.ne' this
  rcases no_split D.target.convex D.target.interior_nonempty hclA hclB hU hF with h | h
  · refine hnull i fun x hx => ?_
    have hxA : x ∈ UA := mem_biUnion hiA hx
    exact ⟨hxA, h hxA⟩
  · refine hnull j fun x hx => ?_
    have hxB : x ∈ UB := mem_biUnion hjA hx
    exact ⟨h hxB, hxB⟩
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
def rank2Par (b : ZMod 2) : ℤ × ℤ →+ ZMod 2 where
  toFun p := (p.1 : ZMod 2) + b * (p.2 : ZMod 2)
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring
end Erdos634.Geometry
end

section
namespace Erdos634.TilePlacement
open Erdos634.Geometry Finset
noncomputable def sideOpp (T : Tri) (j : Fin 3) : ℝ := dist (T.pts (j + 1)) (T.pts (j + 2))
noncomputable def angleAt (T : Tri) (j : Fin 3) : ℝ :=
  cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))
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
theorem Tri.oppLen_pos (T : Tri) (k : Fin 3) : 0 < T.oppLen k := by
  unfold Tri.oppLen
  have hne : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  exact dist_pos.mpr fun h => hne (T.indep.injective h)
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
open MeasureTheory
variable {N : ℕ}
theorem dist_sq_coord' (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
theorem Tri.four_detTri_sq (T : Tri) :
    4 * Erdos634.AreaDet.detTri T ^ 2
      = 4 * T.oppLen 2 ^ 2 * T.oppLen 1 ^ 2 - (T.oppLen 2 ^ 2 + T.oppLen 1 ^ 2 - T.oppLen 0 ^ 2) ^ 2 := by
  rw [Erdos634.AreaDet.detTri_eq]
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  rw [dist_sq_coord' (T.pts 0) (T.pts 1), dist_sq_coord' (T.pts 2) (T.pts 0),
    dist_sq_coord' (T.pts 1) (T.pts 2)]
  simp only [PiLp.sub_apply]
  ring
theorem CongruentDissection.abs_detTri_target (D : CongruentDissection N) :
    |Erdos634.AreaDet.detTri D.target| = N * |Erdos634.AreaDet.detTri D.model| := by
  have h := Erdos634.CongruentArea.congruentDissection_volume_target D
  have hm := D.model.volume_pos
  have hmt := D.model.volume_ne_top
  rw [Erdos634.AreaDet.volume_eq_det_mul, Erdos634.AreaDet.volume_eq_det_mul] at h
  rw [Erdos634.AreaDet.volume_eq_det_mul] at hm hmt
  set V := volume Erdos634.AreaDet.stdCarrier with hVdef
  have hV0 : V ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hm; exact lt_irrefl _ hm
  have hd0 : ENNReal.ofReal |Erdos634.AreaDet.detTri D.model| ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hm; exact lt_irrefl _ hm
  have hVt : V ≠ ⊤ := by
    intro ht; apply hmt; rw [ht, ENNReal.mul_top hd0]
  rw [← mul_assoc, ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)] at h
  have h2 := (ENNReal.mul_left_inj hV0 hVt).mp h
  exact (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (by positivity)).mp h2
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
noncomputable def rankMap (n : ℕ) (θ : ℝ) : ℤ × ℤ →+ Real.Angle where
  toFun p := p.1 • ((Real.pi / n : ℝ) : Real.Angle) + p.2 • ((θ : ℝ) : Real.Angle)
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, add_zsmul]
    abel
theorem rankMap_apply (n : ℕ) (θ : ℝ) (j k : ℤ) :
    rankMap n θ (j, k) = (((j : ℝ) * (Real.pi / n) + (k : ℝ) * θ : ℝ) : Real.Angle) := by
  show j • ((Real.pi / n : ℝ) : Real.Angle) + k • ((θ : ℝ) : Real.Angle) = _
  rw [Real.Angle.coe_add, ← Real.Angle.coe_zsmul, ← Real.Angle.coe_zsmul, zsmul_eq_mul,
    zsmul_eq_mul]
theorem rankn_ker (n : ℕ) (hn : 0 < n) (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi)
    (b : ZMod 2) (p : ℤ × ℤ) (hp : rankMap n θ p = 0) : rank2Par b p = 0 := by
  obtain ⟨j, k⟩ := p
  rw [rankMap_apply, Real.Angle.coe_eq_zero_iff] at hp
  obtain ⟨m, hm⟩ := hp
  rw [zsmul_eq_mul] at hm
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have e : (j : ℝ) * (Real.pi / n) * n = j * Real.pi := by field_simp
  by_cases hk : k = 0
  · have hk0 : (k : ℝ) = 0 := by exact_mod_cast hk
    have h2 : ((j : ℝ) - 2 * m * n) * Real.pi = 0 := by
      linear_combination (-(n : ℝ)) * hm - e - (θ * n) * hk0
    have h3 : (j : ℝ) - 2 * m * n = 0 := (mul_eq_zero.mp h2).resolve_right Real.pi_ne_zero
    have hj : j = 2 * (m * n) := by
      have h4 : (j : ℝ) = ((2 * (m * n) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast h4
    show (j : ZMod 2) + b * (k : ZMod 2) = 0
    rw [hj, hk]
    push_cast
    have h20 : (2 : ZMod 2) = 0 := by decide
    rw [h20]
    ring
  · exfalso
    apply hθ
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have h1 : (k : ℝ) * n * θ = (2 * m * n - j) * Real.pi := by
      linear_combination (-(n : ℝ)) * hm - e
    refine ⟨((2 * m * n - j : ℤ) : ℚ) / ((n * k : ℤ) : ℚ), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hn' hk')]
    linear_combination h1
noncomputable def GridChar.rankn (n : ℕ) (hn : 0 < n) (hodd : (n : ZMod 2) = 1) (θ : ℝ)
    (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2) (anchor : Real.Angle) : GridChar ℝ :=
  GridChar.ofHom (rankMap n θ) (rank2Par b) (rankn_ker n hn θ hθ b) ((n : ℤ), 0)
    (by
      rw [rankMap_apply]
      congr 1
      have hn' : (n : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring)
    (by
      show (((n : ℤ)) : ZMod 2) + b * ((0 : ℤ) : ZMod 2) = 1
      push_cast
      rw [hodd]
      ring)
    anchor
theorem GridChar.rankn_mem (n : ℕ) (hn : 0 < n) (hodd : (n : ZMod 2) = 1) (θ : ℝ)
    (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2) (anchor : Real.Angle) (j k : ℤ) :
    (((j : ℝ) * (Real.pi / n) + (k : ℝ) * θ : ℝ) : Real.Angle)
      ∈ (GridChar.rankn n hn hodd θ hθ b anchor).L := by
  rw [← rankMap_apply]
  exact AddMonoidHom.mem_range.mpr ⟨(j, k), rfl⟩
theorem GridChar.rankn_chi (n : ℕ) (hn : 0 < n) (hodd : (n : ZMod 2) = 1) (θ : ℝ)
    (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2) (anchor : Real.Angle) (j k : ℤ) :
    (GridChar.rankn n hn hodd θ hθ b anchor).chi
        (((j : ℝ) * (Real.pi / n) + (k : ℝ) * θ : ℝ) : Real.Angle)
      = if (j : ZMod 2) + b * (k : ZMod 2) = 0 then 1 else -1 := by
  rw [← rankMap_apply]
  exact GridChar.ofHom_chi _ _ _ _ _ _ _ (j, k)
theorem GridChar.rankn_sq (n : ℕ) (hn : 0 < n) (hodd : (n : ZMod 2) = 1) (θ : ℝ)
    (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2) (anchor : Real.Angle) :
    ∀ l ∈ (GridChar.rankn n hn hodd θ hθ b anchor).L,
      (GridChar.rankn n hn hodd θ hθ b anchor).chi l
        * (GridChar.rankn n hn hodd θ hθ b anchor).chi l = 1 :=
  GridChar.ofHom_sq _ _ _ _ _ _ _
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
theorem Tri.four_detTri_sq_sym (T : Tri) :
    4 * Erdos634.AreaDet.detTri T ^ 2
      = (∑ k, T.oppLen k ^ 2) ^ 2 - 2 * ∑ k, T.oppLen k ^ 4 := by
  rw [T.four_detTri_sq, Fin.sum_univ_three, Fin.sum_univ_three]
  ring
noncomputable def wAt (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) : GridChar ℝ :=
  GridChar.rankn 3 (by norm_num) (by decide) α hα b anc
theorem wAt_sq (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2) (anc : Real.Angle) :
    ∀ l ∈ (wAt α hα b anc).L, (wAt α hα b anc).chi l * (wAt α hα b anc).chi l = 1 :=
  GridChar.rankn_sq _ _ _ _ _ _ _
theorem wAt_form (α : ℝ) (j k : ℤ) :
    ((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α) = ((j : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + (k : ℝ) * α) := by
  push_cast; ring
theorem wAt_mem (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2) (anc : Real.Angle)
    (j k : ℤ) : (((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle) ∈ (wAt α hα b anc).L := by
  rw [wAt_form]
  exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
theorem wAt_chi (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2) (anc : Real.Angle)
    (j k : ℤ) :
    (wAt α hα b anc).chi (((j : ℝ) * (Real.pi / 3) + (k : ℝ) * α : ℝ) : Real.Angle)
      = if (j : ZMod 2) + b * (k : ZMod 2) = 0 then 1 else -1 := by
  rw [wAt_form]
  exact GridChar.rankn_chi _ _ _ _ _ _ _ _ _
theorem wAt_tileValue (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) (T : Tri) : (wAt α hα b anc).tileValue T = (wAt α hα b 0).tileValue T := rfl
def Tri.SixtyData (T : Tri) (α a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = 2 * Real.pi / 3 - α ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = Real.pi / 3 ∧ T.oppLen (σ 2) = c
theorem Tri.sixty_angles_mem {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.SixtyData α a b c) (b' : ZMod 2) (anc : Real.Angle) :
    ∀ j, ((T.angleAt j : ℝ) : Real.Angle) ∈ (wAt α hα b' anc).L := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  intro j
  obtain ⟨k, rfl⟩ := σ.surjective j
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · rw [h0, show ((α : ℝ) : Real.Angle)
        = ((((0 : ℤ) : ℝ) * (Real.pi / 3) + ((1 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
          congr 1; push_cast; ring]
    exact wAt_mem _ _ _ _ _ _
  · rw [h1, show 2 * Real.pi / 3 - α = ((2 : ℤ) : ℝ) * (Real.pi / 3) + ((-1 : ℤ) : ℝ) * α by
      push_cast; ring]
    exact wAt_mem _ _ _ _ _ _
  · rw [h2, show Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α by push_cast; ring]
    exact wAt_mem _ _ _ _ _ _
theorem sixty_tileValue (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.SixtyData α a b c) (b' : ZMod 2) :
    (wAt α hα b' 0).tileValue T
      = (if ((3 : ℤ) : ZMod 2) + b' * ((-1 : ℤ) : ZMod 2) = 0 then 1 else -1) * a
        + (if ((1 : ℤ) : ZMod 2) + b' * ((1 : ℤ) : ZMod 2) = 0 then 1 else -1) * b
        + (if ((2 : ℤ) : ZMod 2) + b' * ((0 : ℤ) : ZMod 2) = 0 then 1 else -1) * c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ (fun j => (wAt α hα b' 0).chi
      ((Real.pi - T.angleAt j : ℝ) : Real.Angle) * T.oppLen j), Fin.sum_univ_three]
  rw [h0, o0, h1, o1, h2, o2,
    show Real.pi - α = ((3 : ℤ) : ℝ) * (Real.pi / 3) + ((-1 : ℤ) : ℝ) * α by push_cast; ring,
    show Real.pi - (2 * Real.pi / 3 - α) = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((1 : ℤ) : ℝ) * α by
      push_cast; ring,
    show Real.pi - Real.pi / 3 = ((2 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring,
    wAt_chi, wAt_chi, wAt_chi]
theorem sixty_tileValue_two (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.SixtyData α a b c) : (wAt α hα 1 0).tileValue T = a + b + c := by
  rw [sixty_tileValue T hα h 1, if_pos (by decide), if_pos (by decide), if_pos (by decide)]
  ring
theorem Row5.equilateral_boundary (D : CongruentDissection N) {α : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b' : ZMod 2)
    (hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle)
      ∈ (wAt α hα b' (D.target.leftUnit 0).angle).L)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3) :
    D.target.oppLen 1 = D.target.oppLen 0 ∧ D.target.oppLen 2 = D.target.oppLen 0 ∧
    ∃ S : ℤ, (2 : ℤ) ∣ S - N ∧ |S| ≤ N ∧
      (S : ℝ) * (wAt α hα b' 0).tileValue D.model = 3 * D.target.oppLen 0 := by
  set anc := (D.target.leftUnit 0).angle with hancdef
  have e3 : Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α := by push_cast; ring
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (wAt α hα b' anc).L := by
    intro k; rw [hP k, e3]; exact wAt_mem _ _ _ _ _ _
  have hchi : (wAt α hα b' anc).chi ((Real.pi / 3 : ℝ) : Real.Angle) = -1 := by
    rw [e3, wAt_chi, if_neg]
    have h1 : ((1 : ℤ) : ZMod 2) = 1 := by decide
    have h0 : ((0 : ℤ) : ZMod 2) = 0 := by decide
    rw [h1, h0, mul_zero, add_zero]
    decide
  have hsin : 0 < Real.sin (Real.pi / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have l01 := D.target.lawSin 0 1
  have l02 := D.target.lawSin 0 2
  rw [hP 0, hP 1] at l01
  rw [hP 0, hP 2] at l02
  have e1 : D.target.oppLen 1 = D.target.oppLen 0 := mul_left_cancel₀ hsin.ne' l01
  have e2 : D.target.oppLen 2 = D.target.oppLen 0 := mul_left_cancel₀ hsin.ne' l02
  refine ⟨e1, e2, ?_⟩
  have hPK : (wAt α hα b' anc).paperK D.target = 3 * D.target.oppLen 0 := by
    unfold GridChar.paperK
    rw [Fin.sum_univ_three, hP 0, hP 1, hP 2, hchi, e1, e2]
    ring
  obtain ⟨S, hS2, hSN, hSe⟩ := D.triangle_boundary_anchor (wAt α hα b' anc) (wAt_sq _ _ _ _)
    hmodel htarget 0 rfl
  rw [show (0 : Fin 3) + 2 = 2 from rfl, hP 2, hchi, hPK,
    ← GridChar.tileValue_eq_paperK _ (wAt_sq _ _ _ _) _ hmodel, wAt_tileValue] at hSe
  exact ⟨S, hS2, hSN, by linear_combination hSe⟩
theorem Row5.area (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3)) {a b c κ : ℝ}
    (ha : D.model.oppLen (σ 0) = a) (hb : D.model.oppLen (σ 1) = b) (hc : D.model.oppLen (σ 2) = c)
    (hκ : κ ^ 2 = 1) (hcos : c ^ 2 = a ^ 2 + b ^ 2 + κ * a * b)
    (hP1 : D.target.oppLen 1 = D.target.oppLen 0) (hP2 : D.target.oppLen 2 = D.target.oppLen 0) :
    D.target.oppLen 0 ^ 2 = N * a * b := by
  have hA := D.abs_detTri_target
  have hT := D.target.four_detTri_sq_sym
  have hM := D.model.four_detTri_sq_sym
  rw [Fin.sum_univ_three, Fin.sum_univ_three, hP1, hP2] at hT
  rw [D.model.sum_perm 2 σ, D.model.sum_perm 4 σ, ha, hb, hc] at hM
  have hsq : Erdos634.AreaDet.detTri D.target ^ 2
      = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hA
    simp only [mul_pow, sq_abs] at h
    exact h
  have ha0 : 0 < a := ha ▸ D.model.oppLen_pos (σ 0)
  have hb0 : 0 < b := hb ▸ D.model.oppLen_pos (σ 1)
  have hS0 : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  set S := D.target.oppLen 0
  have h4 : (S ^ 2) ^ 2 = ((N : ℝ) * a * b) ^ 2 := by
    have eT : 4 * Erdos634.AreaDet.detTri D.target ^ 2 = 3 * S ^ 4 := by rw [hT]; ring
    have eM : 4 * Erdos634.AreaDet.detTri D.model ^ 2 = 3 * a ^ 2 * b ^ 2 := by
      rw [hM]
      linear_combination (-(a ^ 2 * b ^ 2)) * hκ - (c ^ 2 - a ^ 2 - b ^ 2 + κ * a * b) * hcos
    linear_combination (-1 / 3 : ℝ) * eT + ((N : ℝ) ^ 2 / 3) * eM + (4 / 3 : ℝ) * hsq
  have hN0 : (0 : ℝ) ≤ N * a * b := mul_nonneg (mul_nonneg (Nat.cast_nonneg N) ha0.le) hb0.le
  exact (pow_left_inj₀ (sq_nonneg S) hN0 two_ne_zero).mp h4
end Erdos634.Geometry
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
end Erdos634.Draft.LaczFormal
end

section
namespace TriangleTiling.Equilateral
theorem notprime60_case {N a b c M t : ℕ} (hN : N.Prime) (hN5 : 5 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (hgcd : Nat.gcd (Nat.gcd a b) c = 1) (hcos : c ^ 2 + a * b = a ^ 2 + b ^ 2) (hab : a ≠ b)
    (ht0 : 0 < t) (ht : 6 * N = (a + b + c) * t) (hE2 : t * (a + b) = t * c + 2 * M ^ 2)
    (hE3 : t ^ 2 * (a * b) = 4 * M ^ 2 * N) (htri : a < b + c) (hNa : N ∣ a) : False := by
  obtain ⟨a', rfl⟩ := hNa
  have hN0 := hN.pos
  have ha' : 0 < a' := Nat.pos_of_mul_pos_left ha
  have h2a : 2 * (N * a') * t < (N * a' + b + c) * t :=
    Nat.mul_lt_mul_of_pos_right (by omega) ht0
  rw [← ht] at h2a
  have hat : a' * t < 3 := by
    have : N * (2 * (a' * t)) < N * 6 := by linarith
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  have ha3 : a' < 3 := lt_of_le_of_lt (Nat.le_mul_of_pos_right a' ht0) hat
  have ht3 : t < 3 := lt_of_le_of_lt (Nat.le_mul_of_pos_left t ha') hat
  interval_cases a' <;> interval_cases t <;> norm_num at hat
  · 
    have hb' : b = 4 * M ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left hN0; linarith
    generalize M ^ 2 = m at hb' hE2
    have h3 : 3 ∣ N := by omega
    rcases hN.eq_one_or_self_of_dvd 3 h3 with h | h <;> omega
  · 
    have hb' : b = M ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 4 * N); linarith
    have hc : c = N := by
      generalize M ^ 2 = m at hb' hE2
      omega
    rw [hc] at hcos
    have : N * b = b * b := by nlinarith
    have := Nat.eq_of_mul_eq_mul_right hb this
    exact hab (by omega)
  · 
    have hb' : b = 2 * M ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 * N); linarith
    have h2a : 2 ∣ N * 2 := Dvd.intro_left N rfl
    have h2b : 2 ∣ b := ⟨M ^ 2, hb'⟩
    have h2c : 2 ∣ c := by
      apply Nat.prime_two.dvd_of_dvd_pow (n := 2)
      have h1 : 2 ∣ c ^ 2 + N * 2 * b := by
        rw [hcos]
        exact dvd_add (dvd_pow h2a two_ne_zero) (dvd_pow h2b two_ne_zero)
      exact (Nat.dvd_add_left (dvd_mul_of_dvd_left h2a b)).mp h1
    have := Nat.dvd_gcd (Nat.dvd_gcd h2a h2b) h2c
    rw [hgcd] at this
    omega
theorem notprime60_core {N a b c M : ℕ} (hN : N.Prime) (hN5 : 5 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hgcd : Nat.gcd (Nat.gcd a b) c = 1) (hcos : c ^ 2 + a * b = a ^ 2 + b ^ 2)
    (hab : a ≠ b) (hMN : M ^ 2 < N) (hsq : (M * (a + b + c)) ^ 2 = 9 * N * a * b) : False := by
  have hs0 : 0 < a + b + c := by omega
  have hkey : 6 * N * c + (a + b + c) * M ^ 2 = 3 * N * (a + b + c) := by
    have hsq' : ((M : ℤ) * (a + b + c)) ^ 2 = 9 * N * a * b := by exact_mod_cast hsq
    have hcos' : (c : ℤ) ^ 2 + a * b = a ^ 2 + b ^ 2 := by exact_mod_cast hcos
    have h : ((a + b + c : ℕ) : ℤ) * (6 * N * c + (a + b + c) * M ^ 2) =
        ((a + b + c : ℕ) : ℤ) * (3 * N * (a + b + c)) := by
      push_cast; linear_combination hsq' + 3 * (N : ℤ) * hcos'
    have h' := mul_left_cancel₀ (by exact_mod_cast hs0.ne' : ((a + b + c : ℕ) : ℤ) ≠ 0) h
    exact_mod_cast h'
  have hcop : Nat.Coprime (a + b + c) c := by
    apply Nat.coprime_of_dvd
    intro p hp hps hpc
    have hpab : p ∣ a + b := (Nat.dvd_add_left hpc).mp hps
    have hfa : p ∣ a → False := by
      intro hpa
      have hpb := (Nat.dvd_add_right hpa).mp hpab
      have := Nat.dvd_gcd (Nat.dvd_gcd hpa hpb) hpc
      rw [hgcd] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hfb : p ∣ b → False := fun hpb => hfa ((Nat.dvd_add_left hpb).mp hpab)
    have hs3 : (a + b) ^ 2 = c ^ 2 + 3 * (a * b) := by nlinarith
    have h3ab : p ∣ 3 * (a * b) :=
      (Nat.dvd_add_right (dvd_pow hpc two_ne_zero)).mp (by rw [← hs3]; exact dvd_pow hpab two_ne_zero)
    rcases (Nat.Prime.dvd_mul hp).mp h3ab with h3 | h3
    · have hp3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      subst hp3
      have h9a : 3 * 3 ∣ (a + b) ^ 2 := by rw [pow_two]; exact Nat.mul_dvd_mul hpab hpab
      have h9c : 3 * 3 ∣ c ^ 2 := by rw [pow_two]; exact Nat.mul_dvd_mul hpc hpc
      rw [hs3] at h9a
      have h9 : 3 * 3 ∣ 3 * (a * b) := (Nat.dvd_add_right h9c).mp h9a
      have h3' := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h9
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3' with h | h
      · exact hfa h
      · exact hfb h
    · rcases (Nat.Prime.dvd_mul hp).mp h3 with h | h
      · exact hfa h
      · exact hfb h
  have hd : (a + b + c) ∣ 6 * N * c :=
    (Nat.dvd_add_left (Dvd.intro _ rfl : (a + b + c) ∣ (a + b + c) * M ^ 2)).mp
      (hkey ▸ Dvd.intro_left _ rfl)
  obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_right hd
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; have := hN.pos; omega
    · exact h
  have htZ : (6 * N : ℤ) = (a + b + c) * t := by exact_mod_cast ht
  have hkeyZ : (6 * N * c + (a + b + c) * M ^ 2 : ℤ) = 3 * N * (a + b + c) := by
    exact_mod_cast hkey
  have hsqZ : ((M : ℤ) * (a + b + c)) ^ 2 = 9 * N * a * b := by exact_mod_cast hsq
  have hE1 : t * c + M ^ 2 = 3 * N := by
    have h : ((a + b + c : ℕ) : ℤ) * (t * c + M ^ 2) = ((a + b + c : ℕ) : ℤ) * (3 * N) := by
      push_cast; linear_combination hkeyZ - (c : ℤ) * htZ
    exact_mod_cast mul_left_cancel₀ (by exact_mod_cast hs0.ne' : ((a + b + c : ℕ) : ℤ) ≠ 0) h
  have hE1Z : (t * c + M ^ 2 : ℤ) = 3 * N := by exact_mod_cast hE1
  have hE2 : t * (a + b) = t * c + 2 * M ^ 2 := by
    have h : (t * (a + b) : ℤ) = t * c + 2 * M ^ 2 := by
      linear_combination -htZ - 2 * hE1Z
    exact_mod_cast h
  have hE3 : t ^ 2 * (a * b) = 4 * M ^ 2 * N := by
    have h : ((9 * N : ℕ) : ℤ) * (t ^ 2 * (a * b)) = ((9 * N : ℕ) : ℤ) * (4 * M ^ 2 * N) := by
      push_cast
      linear_combination (-(t : ℤ) ^ 2) * hsqZ +
        -(M : ℤ) ^ 2 * ((a + b + c) * t + 6 * N) * htZ
    exact_mod_cast mul_left_cancel₀ (by have := hN.pos; positivity) h
  have hcab : c < a + b := by
    by_contra h; push Not at h
    have h1 := Nat.mul_le_mul h h
    have h2 := Nat.mul_pos ha hb
    ring_nf at h1 hcos
    linarith
  have ht2M : t ≤ 2 * M ^ 2 := by
    have h1 := Nat.mul_le_mul_left t (hcab : c + 1 ≤ a + b)
    ring_nf at h1 hE2 ⊢
    linarith
  have htN : t < 2 * N := by linarith
  rcases Nat.coprime_or_dvd_of_prime hN t with hcopt | hNt
  · 
    have hNab : N ∣ a * b := by
      have h1 : N ∣ t ^ 2 * (a * b) := hE3 ▸ Dvd.intro_left _ rfl
      exact (Nat.Coprime.pow_right 2 hcopt).dvd_of_dvd_mul_left h1
    have hatri : a < b + c := by
      by_contra h; push Not at h
      have h1 := Nat.mul_le_mul_left a h
      have h2 := Nat.mul_le_mul_left c h
      have h3 := Nat.mul_pos hb hc
      ring_nf at h1 h2 h3 hcos
      nlinarith
    have hbtri : b < a + c := by
      by_contra h; push Not at h
      have h1 := Nat.mul_le_mul_left b h
      have h2 := Nat.mul_le_mul_left c h
      have h3 := Nat.mul_pos ha hc
      ring_nf at h1 h2 h3 hcos
      nlinarith
    rcases (Nat.Prime.dvd_mul hN).mp hNab with hNa | hNb
    · exact notprime60_case hN hN5 ha hb hgcd hcos hab ht0 ht hE2 hE3 hatri hNa
    · refine notprime60_case (a := b) (b := a) hN hN5 hb ha (by rwa [Nat.gcd_comm b a]) (by linarith)
        (Ne.symm hab) ht0 (by rw [ht]; ring) (by linarith) (by rw [← hE3]; ring) hbtri hNb
  · 
    obtain ⟨k, rfl⟩ := hNt
    have hk : k = 1 := by
      have hk0 : 0 < k := Nat.pos_of_mul_pos_left ht0
      have : N * k < N * 2 := by linarith
      have := Nat.lt_of_mul_lt_mul_left this
      omega
    subst hk
    have h1 : N * (a + b) < N * (c + 2) := by ring_nf at hE2 ⊢; linarith
    have h2 := Nat.lt_of_mul_lt_mul_left h1
    have h3 : a + b = c + 1 := by omega
    rw [h3] at hE2
    have h4 : N = 2 * M ^ 2 := by linarith
    have h5 : 2 ∣ N := ⟨M ^ 2, h4⟩
    rcases hN.eq_one_or_self_of_dvd 2 h5 with h | h <;> omega
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
namespace TriangleTiling.Equilateral
theorem sixty_alg {u v M N x : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v)
    (hcos : 1 = u ^ 2 + v ^ 2 - u * v) (hN : 0 < N) (hx : 0 < x)
    (hcol : M * (u + v + 1) = 3 * x) (harea : x ^ 2 = N * (u * v)) :
    M ^ 2 < N ∧ 0 < 3 * N - M ^ 2 ∧
      u + v = (3 * N + M ^ 2) / (3 * N - M ^ 2) ∧
      u * v = 4 * M ^ 2 * N / (3 * N - M ^ 2) ^ 2 ∧
      ((u = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) +
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)) ∧
        v = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) -
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2))) ∨
       (u = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) -
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)) ∧
        v = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) +
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)))) := by
  set s := u + v with hs
  have hs1 : 1 < s := by nlinarith [mul_pos hu hv]
  have hp : u * v = (s ^ 2 - 1) / 3 := by rw [hs]; linarith
  have hMs : M ^ 2 * (s + 1) = 3 * N * (s - 1) := by
    have h1 : M ^ 2 * (s + 1) ^ 2 = 9 * (N * (u * v)) := by
      rw [← harea, show M ^ 2 * (s + 1) ^ 2 = (M * (u + v + 1)) ^ 2 by rw [hs]; ring, hcol]; ring
    rw [hp] at h1
    have h2 : (s + 1) * (M ^ 2 * (s + 1) - 3 * N * (s - 1)) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · linarith
  have hD : 0 < 3 * N - M ^ 2 := by nlinarith [sq_nonneg M]
  have hsf : s = (3 * N + M ^ 2) / (3 * N - M ^ 2) := by
    rw [eq_div_iff hD.ne']; linarith
  have hdiff : (u - v) ^ 2 = (9 * N - M ^ 2) * (N - M ^ 2) / (3 * N - M ^ 2) ^ 2 := by
    have : (u - v) ^ 2 = s ^ 2 - 4 * (u * v) := by rw [hs]; ring
    rw [this, hp, hsf]; field_simp; ring
  have hpos : 0 < (u - v) ^ 2 := by
    have : u - v ≠ 0 := sub_ne_zero.mpr huv
    positivity
  have hDpos : 0 < (9 * N - M ^ 2) * (N - M ^ 2) := by
    rw [hdiff] at hpos
    exact (div_pos_iff_of_pos_right (by positivity)).mp hpos
  have hMN : M ^ 2 < N := by
    have h9 : 0 < 9 * N - M ^ 2 := by linarith
    have := (pos_iff_pos_of_mul_pos hDpos).mp h9
    linarith
  have hab : u * v = 4 * M ^ 2 * N / (3 * N - M ^ 2) ^ 2 := by
    rw [hp, hsf]; field_simp; ring
  refine ⟨hMN, hD, hsf, hab, ?_⟩
  set R := Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2))
  have hR : (u - v) ^ 2 = (R / (3 * N - M ^ 2)) ^ 2 := by
    rw [hdiff, div_pow, Real.sq_sqrt hDpos.le]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hR with h | h
  · left; constructor <;> linarith
  · right; constructor <;> linarith
end TriangleTiling.Equilateral
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem fin3_ne_add_one : ∀ k : Fin 3, k ≠ k + 1 := by decide
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem eq_endpoint_of_mem_segment {x y u v : Plane} (hu : u ∈ segment ℝ x y)
    (hv : v ∈ segment ℝ x y) (hx : x ∈ segment ℝ u v) : x = u ∨ x = v := by
  by_cases hxy : x = y
  · subst hxy
    rw [segment_same] at hu
    exact Or.inl hu.symm
  have hL := AffineMap.lineMap_injective ℝ hxy
  rw [segment_eq_image_lineMap] at hu hv
  obtain ⟨s, hs, rfl⟩ := hu
  obtain ⟨t, ht, rfl⟩ := hv
  rw [← image_segment, segment_eq_Icc'] at hx
  obtain ⟨r, hr, hrx⟩ := hx
  have hr0 : r = 0 := hL (hrx.trans (AffineMap.lineMap_apply_zero x y).symm)
  subst hr0
  rcases le_total s t with h | h
  · left
    have h0 : s = 0 := le_antisymm (by have := hr.1; rwa [min_eq_left h] at this) hs.1
    rw [h0, AffineMap.lineMap_apply_zero]
  · right
    have h0 : t = 0 := le_antisymm (by have := hr.1; rwa [min_eq_right h] at this) ht.1
    rw [h0, AffineMap.lineMap_apply_zero]
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry Polynomial
variable {N : ℕ} (D : CongruentDissection N)
theorem side_edge_at_end {part : Finset (Fin N × Fin 3)} {P Q V : Plane}
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ P Q) (hV : V = P ∨ V = Q) :
    ∃ e ∈ part, ((D.tile e.1).pts e.2 = V ∨ (D.tile e.1).pts (e.2 + 1) = V) := by
  have hVs : V ∈ segment ℝ P Q := by
    rcases hV with h | h
    · rw [h]; exact left_mem_segment _ _ _
    · rw [h]; exact right_mem_segment _ _ _
  rw [← hcov] at hVs
  obtain ⟨e, he, hVe⟩ := Set.mem_iUnion₂.mp hVs
  have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ P Q := by
    rw [← hcov]; intro z hz; exact Set.mem_iUnion₂.mpr ⟨e, he, hz⟩
  have hu := hsub (left_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
  have hv := hsub (right_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
  refine ⟨e, he, ?_⟩
  rcases hV with h | h
  · rw [← h] at hu hv
    rcases eq_endpoint_of_mem_segment hu hv hVe with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'.symm
  · rw [segment_symm] at hu hv
    rw [← h] at hu hv
    rcases eq_endpoint_of_mem_segment hu hv hVe with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'.symm
end TriangleTiling
end

section
namespace TriangleTiling.Equilateral
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
def AtAOnAB (i : Fin N) : Prop :=
  ∃ l l' : Fin 3, l ≠ l' ∧ (D.tile i).pts l = D.target.pts 0 ∧
    (D.tile i).pts l' ∈ segment ℝ (D.target.pts 0) (D.target.pts 1)
theorem edge_of_AtAOnAB {i : Fin N} (hi : AtAOnAB D i) :
    ∃ e : Fin 3, (D.tile i).edge e ⊆ D.target.edge 0 := by
  obtain ⟨l, l', hll', hl, hl'⟩ := hi
  have hAB : D.target.edge 0 = segment ℝ (D.target.pts 0) (D.target.pts 1) := rfl
  have hA : D.target.pts 0 ∈ segment ℝ (D.target.pts 0) (D.target.pts 1) :=
    left_mem_segment ℝ _ _
  have hcases : ∀ l l' : Fin 3, l ≠ l' → l' = l + 1 ∨ l = l' + 1 := by decide
  rcases hcases l l' hll' with e | e
  · refine ⟨l, ?_⟩
    rw [hAB, Tri.edge, ← e, hl]
    exact (convex_segment _ _).segment_subset hA hl'
  · refine ⟨l', ?_⟩
    rw [hAB, Tri.edge, ← e, hl]
    exact (convex_segment _ _).segment_subset hl' hA
theorem exists_atA_onAB : ∃ i, AtAOnAB D i := by
  obtain ⟨part, hcov, -, -⟩ := D.toDissection.side_walk 0
  have hcov' : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1) := hcov
  obtain ⟨e, he, hV⟩ := TriangleTiling.side_edge_at_end D hcov' (V := D.target.pts 0) (Or.inl rfl)
  have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) := by
    rw [← hcov']; intro y hy; exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  refine ⟨e.1, ?_⟩
  rcases hV with h' | h'
  · exact ⟨e.2, e.2 + 1, fin3_ne_add_one e.2, h', hsub (right_mem_segment ℝ _ _)⟩
  · exact ⟨e.2 + 1, e.2, (fin3_ne_add_one e.2).symm, h', hsub (left_mem_segment ℝ _ _)⟩
variable {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
theorem tile_sixty (h : D.model.SixtyData α a b c) (i : Fin N) : (D.tile i).SixtyData α a b c := by
  obtain ⟨σ, h0, h0', h1, h1', h2, h2'⟩ := h
  obtain ⟨τ, hτ⟩ := (D.tiles_congruent i).exists_perm
  refine ⟨σ.trans τ.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Equiv.trans_apply, (hτ _).1, (hτ _).2, Equiv.apply_symm_apply] <;> assumption
include hα in
theorem sixty_hext (T : Tri) (h : T.SixtyData α a b c) (anc : Real.Angle) (k : Fin 3) :
    (wAt α hα 1 anc).chi ((Real.pi - T.angleAt k : ℝ) : Real.Angle) = 1 := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  obtain ⟨x, rfl⟩ := σ.surjective k
  rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2) x with rfl | rfl | rfl
  · rw [h0, show Real.pi - α = ((3 : ℤ) : ℝ) * (Real.pi / 3) + ((-1 : ℤ) : ℝ) * α by push_cast; ring,
      wAt_chi, if_pos (by decide)]
  · rw [h1, show Real.pi - (2 * Real.pi / 3 - α) = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((1 : ℤ) : ℝ) * α by
      push_cast; ring, wAt_chi, if_pos (by decide)]
  · rw [h2, show Real.pi - Real.pi / 3 = ((2 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring, wAt_chi, if_pos (by decide)]
inductive Chain (D : Dissection N) (i₀ : Fin N) : Fin N → ℕ → Prop
  | nil : Chain D i₀ i₀ 0
  | cons {j k : Fin N} {n : ℕ} : Chain D i₀ j n → D.Adj j k → Chain D i₀ k (n + 1)
noncomputable def pathColour (D : Dissection N) (i₀ j : Fin N) : ℤ :=
  haveI := Classical.propDecidable
  if ∃ n, Chain D i₀ j n ∧ Even n then 1 else -1
theorem exists_chain (D : Dissection N) (i₀ j : Fin N) : ∃ n, Chain D i₀ j n := by
  induction D.adjConnected i₀ j with
  | refl => exact ⟨0, .nil⟩
  | tail _ hab ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .cons hn hab⟩
theorem colour_chain {D : Dissection N} {ε : Fin N → ℤ} (hε : D.ProperColouring ε) {i₀ j : Fin N}
    {n : ℕ} (hc : Chain D i₀ j n) : ε j = ε i₀ * (-1) ^ n := by
  induction hc with
  | nil => ring
  | cons _ hadj ih =>
    rw [pow_succ, ← mul_assoc, ← ih]
    have := hε.2 _ _ hadj
    omega
noncomputable def tpar (i : Fin N) : ℝ := (wAt α hα 1 0).weight ((D.tile i).leftUnit 0)
include hα in
theorem tpar_sq (i : Fin N) : tpar D hα i * tpar D hα i = 1 := (wAt α hα 1 0).val_sq (wAt_sq α hα 1 0) _
include hα in
theorem tpar_edge (h : D.model.SixtyData α a b c) (i : Fin N) (k : Fin 3) :
    (wAt α hα 1 0).weight ((D.tile i).leftUnit k) = tpar D hα i :=
  (D.tile i).weight_const _ ((D.tile i).sixty_angles_mem hα (tile_sixty D h i) 1 0)
    (sixty_hext hα (D.tile i) (tile_sixty D h i) 0) k
include hα in
theorem tpar_adj (h : D.model.SixtyData α a b c) {i j : Fin N} (hij : D.toDissection.Adj i j) :
    tpar D hα j = - tpar D hα i := by
  obtain ⟨k, l, hkl⟩ := hij.leftUnit_neg
  rw [← tpar_edge D hα h j l, ← tpar_edge D hα h i k, hkl, (wAt α hα 1 0).weight_odd]
include hα in
theorem tpar_chain (h : D.model.SixtyData α a b c) {i₀ j : Fin N} {n : ℕ}
    (hc : Chain D.toDissection i₀ j n) : tpar D hα j = (-1) ^ n * tpar D hα i₀ := by
  induction hc with
  | nil => ring
  | cons _ hadj ih => rw [tpar_adj D hα h hadj, ih]; ring
include hα in
theorem pathColour_of_chain (h : D.model.SixtyData α a b c) {i₀ j : Fin N} {n : ℕ}
    (hc : Chain D.toDissection i₀ j n) : pathColour D.toDissection i₀ j = (-1) ^ n := by
  unfold pathColour
  split_ifs with hE
  · obtain ⟨m, hm, hev⟩ := hE
    have h0 : tpar D hα i₀ ≠ 0 := fun e => by simpa [e] using tpar_sq D hα i₀
    have hmn : ((-1 : ℝ)) ^ m = (-1) ^ n :=
      mul_right_cancel₀ h0 ((tpar_chain D hα h hm).symm.trans (tpar_chain D hα h hc))
    rcases Nat.even_or_odd n with hn | hn
    · exact hn.neg_one_pow.symm
    · rw [hev.neg_one_pow, hn.neg_one_pow] at hmn; norm_num at hmn
  · rcases Nat.even_or_odd n with hn | hn
    · exact absurd ⟨n, hc, hn⟩ hE
    · exact hn.neg_one_pow.symm
include hα in
theorem pathColour_proper (h : D.model.SixtyData α a b c) (i₀ : Fin N) :
    D.toDissection.ProperColouring (pathColour D.toDissection i₀) ∧
      pathColour D.toDissection i₀ i₀ = 1 := by
  refine ⟨⟨fun j => ?_, fun i j hij => ?_⟩, by rw [pathColour_of_chain D hα h .nil]; rfl⟩
  · unfold pathColour; split_ifs <;> simp
  · obtain ⟨n, hn⟩ := exists_chain D.toDissection i₀ i
    rw [pathColour_of_chain D hα h hn, pathColour_of_chain D hα h (.cons hn hij), pow_succ]
    ring
include hα in
theorem coloring_equation (h : D.model.SixtyData α a b c)
    (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtAOnAB D i₀)
    (h1 : ε i₀ = 1) :
    ((∑ i, ε i : ℤ) : ℝ) * (a + b + c) = 3 * D.target.oppLen 0 := by
  set G := wAt α hα 1 0
  have hsq := wAt_sq α hα 1 0
  have hεj : ∀ j, (ε j : ℝ) = tpar D hα j * tpar D hα i₀ := by
    intro j
    obtain ⟨n, hn⟩ := exists_chain D.toDissection i₀ j
    have e1 : (ε j : ℝ) = (-1) ^ n := by
      have := colour_chain hε hn
      rw [h1, one_mul] at this
      exact_mod_cast this
    rw [e1, tpar_chain D hα h hn, mul_assoc, tpar_sq, mul_one]
  have hflux : ∀ i, (D.tile i).flux G.weight = tpar D hα i * (a + b + c) := by
    intro i
    have hTi := tile_sixty D h i
    rw [(D.tile i).flux_eq_edgeSign G hsq ((D.tile i).sixty_angles_mem hα hTi 1 0) 0]
    unfold GridChar.edgeSign
    rw [sixty_hext hα (D.tile i) hTi 0, one_mul, sixty_tileValue_two (D.tile i) hα hTi]
    rfl
  have e3 : Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α := by push_cast; ring
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ G.L := by
    intro k; rw [hP k, e3]; exact wAt_mem _ _ _ _ _ _
  have hchi2 : G.chi ((Real.pi - Real.pi / 3 : ℝ) : Real.Angle) = 1 := by
    rw [show Real.pi - Real.pi / 3 = ((2 : ℤ) : ℝ) * (Real.pi / 3) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring, wAt_chi, if_pos (by decide)]
  obtain ⟨e1, e2, -⟩ := Row5.equilateral_boundary D hα 1
    (fun k => D.model.sixty_angles_mem hα h 1 _ k) hP
  set w := G.weight (D.target.leftUnit 0)
  have hT : D.target.flux G.weight = w * (3 * D.target.oppLen 0) := by
    rw [Tri.flux_eq_edgeSign G hsq D.target htarget 0]
    unfold GridChar.edgeSign GridChar.tileValue
    rw [Fin.sum_univ_three, hP, hP, hP, hP, hchi2, e1, e2]
    ring
  obtain ⟨e, he⟩ := edge_of_AtAOnAB D hi₀
  have hdir : (D.tile i₀).leftUnit e = D.target.leftUnit 0 :=
    D.toDissection.eDir_of_side (e := (i₀, e)) he
  have hw : w = tpar D hα i₀ := by rw [← tpar_edge D hα h i₀ e, hdir]
  have hsum : ((∑ i, ε i : ℤ) : ℝ) * (a + b + c) = tpar D hα i₀ * ∑ i, (D.tile i).flux G.weight := by
    push_cast
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hflux j, hεj j]; ring
  rw [hsum, D.flux_cancel G.weight G.weight_odd, hT, hw]
  linear_combination (3 * D.target.oppLen 0) * tpar_sq D hα i₀
end TriangleTiling.Equilateral
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
def TileSides (α β γ a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    D.model.angleAt (σ 0) = α ∧ D.model.angleAt (σ 1) = β ∧ D.model.angleAt (σ 2) = γ ∧
    D.model.oppLen (σ 0) = a ∧ D.model.oppLen (σ 1) = b ∧ D.model.oppLen (σ 2) = c
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
namespace TriangleTiling.Equilateral
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional TriangleTiling.ThreeAlpha
variable {N : ℕ} (D : CongruentDissection N)
theorem sixty_setup {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hβ : IrrPi β) :
    β = 2 * Real.pi / 3 - α ∧ IrrPi α ∧ D.model.SixtyData α a b c ∧
      c ^ 2 = a ^ 2 + b ^ 2 - a * b ∧ D.target.oppLen 0 ^ 2 = N * a * b ∧
      D.target.oppLen 1 = D.target.oppLen 0 ∧ D.target.oppLen 2 = D.target.oppLen 0 ∧
      0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧
      a * Real.sin (Real.pi / 3) = c * Real.sin α ∧ b * Real.sin (Real.pi / 3) = c * Real.sin β := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  have hsum : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) = Real.pi := by
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [e, D.model.angleAt_sum]
  have hβα : β = 2 * Real.pi / 3 - α := by rw [h0, h1, h2] at hsum; linarith
  have hα : IrrPi α := by
    rintro ⟨r, hr⟩; apply hβ; exact ⟨2 / 3 - r, by rw [hβα, hr]; push_cast; ring⟩
  have hS : D.model.SixtyData α a b c := ⟨σ, h0, l0, hβα ▸ h1, l1, h2, l2⟩
  have hcos := D.model.lawCos_perm σ
  rw [l0, l1, l2, h2, Real.cos_pi_div_three] at hcos
  have hcos' : c ^ 2 = a ^ 2 + b ^ 2 - a * b := by linarith
  obtain ⟨e1, e2, -⟩ := Row5.equilateral_boundary D hα 1
    (fun k => D.model.sixty_angles_mem hα hS 1 _ k) hP
  have harea := Row5.area D σ l0 l1 l2 (κ := -1) (by norm_num) (by linarith) e1 e2
  have pa : 0 < a := l0 ▸ D.model.oppLen_pos _
  have pb : 0 < b := l1 ▸ D.model.oppLen_pos _
  have pc : 0 < c := l2 ▸ D.model.oppLen_pos _
  have hαβ : α ≠ β := by
    intro e; apply hβ; exact ⟨1 / 3, by rw [hβα] at e ⊢; push_cast; linarith⟩
  have hab := sides_ne_of_angles_ne D ⟨σ, h0, h1, h2, l0, l1, l2⟩ hαβ
  have s0 := D.model.lawSin (σ 0) (σ 2)
  have s1 := D.model.lawSin (σ 1) (σ 2)
  rw [h0, h2, l0, l2] at s0
  rw [h1, h2, l1, l2] at s1
  refine ⟨hβα, hα, hS, hcos', by rw [harea]; try ring, e1, e2, pa, pb, pc, hab, by linarith, by linarith⟩
theorem sixty_main {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hβ : IrrPi β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtAOnAB D i₀)
    (h1 : ε i₀ = 1) :
    let M : ℝ := ((∑ i, ε i : ℤ) : ℝ)
    M ^ 2 < N ∧ 0 < 3 * N - M ^ 2 ∧
      a / c + b / c = (3 * N + M ^ 2) / (3 * N - M ^ 2) ∧
      a / c * (b / c) = 4 * M ^ 2 * N / (3 * N - M ^ 2) ^ 2 ∧
      ((a / c = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) +
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)) ∧
        b / c = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) -
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2))) ∨
       (a / c = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) -
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)) ∧
        b / c = (1 / 2) * ((3 * N + M ^ 2) / (3 * N - M ^ 2) +
          Real.sqrt ((9 * N - M ^ 2) * (N - M ^ 2)) / (3 * N - M ^ 2)))) := by
  intro M
  obtain ⟨-, hα, hS, hcos, harea, -, -, pa, pb, pc, hab, -, -⟩ := sixty_setup D hP hT hβ
  have hcol := coloring_equation D hα hS hP hε hi₀ h1
  have hX := D.target.oppLen_pos 0
  have hN : (0 : ℝ) < N := by
    have : (0 : ℝ) < N * a * b := by rw [← harea]; positivity
    by_contra h; push Not at h
    nlinarith [mul_pos pa pb]
  exact sixty_alg (x := D.target.oppLen 0 / c) (div_pos pa pc) (div_pos pb pc)
    (fun e => hab (by field_simp at e; exact e)) (by field_simp; linarith) hN (div_pos hX pc)
    (by field_simp; linarith) (by field_simp; rw [harea]; try ring)
theorem exists_colouring {α a b c : ℝ} (hα : IrrPi α) (hS : D.model.SixtyData α a b c) (i₀ : Fin N) :
    ∃ ε : Fin N → ℤ, D.toDissection.ProperColouring ε ∧ ε i₀ = 1 :=
  ⟨_, pathColour_proper D hα hS i₀⟩
theorem irr_beta_of_alpha {α β a b c : ℝ} (hT : TileSides D α β (Real.pi / 3) a b c) (hα : IrrPi α) :
    IrrPi β := by
  obtain ⟨σ, h0, h1', h2, -⟩ := hT
  have hsum : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) = Real.pi := by
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [e, D.model.angleAt_sum]
  rintro ⟨r, hr⟩; apply hα
  exact ⟨2 / 3 - r, by rw [h0, h1', h2] at hsum; push_cast; linarith⟩
theorem M_pos {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hβ : IrrPi β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtAOnAB D i₀)
    (h1 : ε i₀ = 1) : 0 < ∑ i, ε i := by
  obtain ⟨-, hα, hS, -, -, -, -, pa, pb, pc, -⟩ := sixty_setup D hP hT hβ
  have hcol := coloring_equation D hα hS hP hε hi₀ h1
  have hX := D.target.oppLen_pos 0
  have : (0 : ℝ) < ((∑ i, ε i : ℤ) : ℝ) := by
    have : 0 < ((∑ i, ε i : ℤ) : ℝ) * (a + b + c) := by rw [hcol]; positivity
    exact pos_of_mul_pos_left this (by positivity)
  exact_mod_cast this
def _root_.OMARAT60 {N : ℕ} (D : CongruentDissection N) : Prop := ∀ {α β a b c : ℝ},
    (∀ k, D.target.angleAt k = Real.pi / 3) → TileSides D α β (Real.pi / 3) a b c → IrrPi α →
      ∃ p₁ q₁ p₂ q₂ : ℕ, 0 < p₁ ∧ 0 < p₂ ∧ a / c = (q₂ : ℝ) / p₂ ∧ b / c = (q₁ : ℝ) / p₁
theorem sixty_rational [hR : Fact (OMARAT60 D)] {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hα : IrrPi α) :
    ∃ p₁ q₁ p₂ q₂ : ℕ, 0 < p₁ ∧ 0 < p₂ ∧ a / c = (q₂ : ℝ) / p₂ ∧ b / c = (q₁ : ℝ) / p₁ := hR.out hP hT hα
theorem square60 [Fact (OMARAT60 D)] {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hα : IrrPi α)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtAOnAB D i₀)
    (h1 : ε i₀ = 1) :
    let M : ℤ := ∑ i, ε i
    0 < M ∧ (M : ℝ) < Real.sqrt N ∧ IsSquare ((9 * N - M ^ 2) * (N - M ^ 2)) := by
  intro M
  have hβ := irr_beta_of_alpha D hT hα
  obtain ⟨hMN, hT3, -, -, hform⟩ := sixty_main D hP hT hβ hε hi₀ h1
  have hM0 := M_pos D hP hT hβ hε hi₀ h1
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  obtain ⟨p₁, q₁, p₂, q₂, hp₁, hp₂, ha, hb⟩ := sixty_rational D hP hT hα
  set D₀ : ℤ := (9 * N - M ^ 2) * (N - M ^ 2)
  have hD₀ : ((D₀ : ℤ) : ℝ) = (9 * N - (M : ℝ) ^ 2) * (N - (M : ℝ) ^ 2) := by
    simp only [D₀]; push_cast; ring
  have hsq : IsSquare D₀ := by
    have hD0 : 0 ≤ D₀ := by
      have : (0 : ℝ) ≤ ((D₀ : ℤ) : ℝ) := by rw [hD₀]; nlinarith
      exact_mod_cast this
    by_contra hns
    have hirr := (irrational_sqrt_intCast_iff_of_nonneg hD0).mpr hns
    rw [hD₀] at hirr
    apply hirr
    rcases hform with ⟨u1, u2⟩ | ⟨u1, u2⟩
    · refine ⟨(3 * N - M ^ 2) * ((q₂ : ℚ) / p₂ - (q₁ : ℚ) / p₁), ?_⟩
      push_cast
      rw [← ha, ← hb, u1, u2]; field_simp; ring
    · refine ⟨-((3 * N - M ^ 2) * ((q₂ : ℚ) / p₂ - (q₁ : ℚ) / p₁)), ?_⟩
      push_cast
      rw [← ha, ← hb, u1, u2]; field_simp; ring
  exact ⟨hM0, by rw [Real.lt_sqrt hMr.le]; exact hMN, hsq⟩
theorem notprime60 [Fact (OMARAT60 D)] {α β a b c : ℝ} (hP : ∀ k, D.target.angleAt k = Real.pi / 3)
    (hT : TileSides D α β (Real.pi / 3) a b c) (hα : IrrPi α) : ¬ N.Prime := by
  intro hNp
  have hβ := irr_beta_of_alpha D hT hα
  obtain ⟨-, -, hS, hcos, harea, -, -, pa, pb, pc, hab, -⟩ := sixty_setup D hP hT hβ
  obtain ⟨i₀, hi₀⟩ := exists_atA_onAB D
  obtain ⟨ε, hε, h1⟩ := exists_colouring D hα hS i₀
  obtain ⟨hM0, -, hsq⟩ := square60 D hP hT hα hε hi₀ h1
  obtain ⟨hMN, -⟩ := sixty_main D hP hT hβ hε hi₀ h1
  have hcol := coloring_equation D hα hS hP hε hi₀ h1
  set M : ℤ := ∑ i, ε i with hMdef
  by_cases hN5 : 5 ≤ N
  swap
  · 
    set D₀ : ℤ := (9 * N - M ^ 2) * (N - M ^ 2) with hD₀
    have hN4 : N ≠ 4 := by rintro rfl; exact absurd hNp (by decide)
    have hN5' : (N : ℤ) < 5 := by exact_mod_cast not_le.mp hN5
    have hN2 := hNp.two_le
    have hMN' : M ^ 2 < N := by exact_mod_cast hMN
    have hM1 : M = 1 := by nlinarith
    obtain ⟨r, hr⟩ := hsq
    simp only [D₀, hM1] at hr
    have h' : ((r.natAbs : ℤ) * r.natAbs) = r * r := Int.natAbs_mul_self' r
    have hN23 : N = 2 ∨ N = 3 := by omega
    rcases hN23 with e | e <;> rw [e] at hr <;> norm_num at hr
    · have h17 : r.natAbs * r.natAbs = 17 := by
        have : ((r.natAbs * r.natAbs : ℕ) : ℤ) = 17 := by rw [Nat.cast_mul]; linarith
        exact_mod_cast this
      have hle : r.natAbs ≤ 17 := by nlinarith
      interval_cases h : r.natAbs <;> omega
    · have h52 : r.natAbs * r.natAbs = 52 := by
        have : ((r.natAbs * r.natAbs : ℕ) : ℤ) = 52 := by rw [Nat.cast_mul]; linarith
        exact_mod_cast this
      have hle : r.natAbs ≤ 52 := by nlinarith
      interval_cases h : r.natAbs <;> omega
  obtain ⟨p₁, q₁, p₂, q₂, hp₁, hp₂, ha, hb⟩ := sixty_rational D hP hT hα
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
  have hA0 : 0 < A := by
    have : (0 : ℝ) < μ * A := eA ▸ pa
    exact_mod_cast pos_of_mul_pos_right this hμ0.le
  have hB0 : 0 < B := by
    have : (0 : ℝ) < μ * B := eB ▸ pb
    exact_mod_cast pos_of_mul_pos_right this hμ0.le
  have hμ2 : μ ^ 2 ≠ 0 := by positivity
  have hMn : ((M.toNat : ℕ) : ℝ) = (M : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hM0.le
  have hsqR : ((M.toNat : ℝ) * (A + B + C)) ^ 2 = 9 * N * A * B := by
    apply mul_left_cancel₀ hμ2
    rw [hMn]
    calc μ ^ 2 * ((M : ℝ) * (A + B + C)) ^ 2 = ((M : ℝ) * (a + b + c)) ^ 2 := by
          rw [eA, eB, eC]; ring
      _ = 9 * D.target.oppLen 0 ^ 2 := by rw [hcol]; ring
      _ = μ ^ 2 * (9 * N * A * B) := by rw [harea, eA, eB]; ring
  have hcosR : (C : ℝ) ^ 2 + A * B = A ^ 2 + B ^ 2 := by
    apply mul_left_cancel₀ hμ2
    have : (μ * C) ^ 2 = (μ * A) ^ 2 + (μ * B) ^ 2 - μ * A * (μ * B) := by
      rw [← eA, ← eB, ← eC]; exact hcos
    linear_combination this
  have hMNn : M.toNat ^ 2 < N := by
    have : ((M.toNat : ℕ) : ℝ) ^ 2 < N := by rw [hMn]; exact hMN
    exact_mod_cast this
  refine notprime60_core hNp hN5 hA0 hB0 hC0 hgcd (by exact_mod_cast hcosR) ?_ hMNn
    (by exact_mod_cast hsqR)
  intro e; apply hab; rw [eA, eB, e]
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


/-- theorem:notprime60 (an equilateral triangle is not tiled by a prime number of tiles (α, 2π/3 - α,
π/3), α not in Q π), given that the tile is rational (H1 of the reduction). -/
theorem OMA.solution : OMA.R_erdos_634_R1_H2_R1_H1_R1_H2_R1.H2 := by
  intro p hp h3p T Ts hc hd hu t A B L hA hB hL hEq hR α hα hBσ
  obtain rfl : A = _ := funext hA
  obtain rfl : B = _ := funext hB
  obtain rfl : L = _ := funext hL
  let D := OMA.E634S.mk T Ts hc hd hu t
  have hP : ∀ k : Fin 3, D.target.angleAt k = Real.pi / 3 := hEq
  haveI : Fact (OMARAT60 D) := ⟨by
    intro α' β a b c _ hT hα'
    obtain ⟨σ, h0, h1, h2, o0, o1, o2⟩ := hT
    have hsum := Erdos634.Draft.LaczFormal.angleAt_sum D.model
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [h0, h1, h2] at e
    have hβ : β = 2 * Real.pi / 3 - α' := by linarith
    subst hβ
    have ha : 0 < a := o0 ▸ D.model.oppLen_pos' _
    have hb : 0 < b := o1 ▸ D.model.oppLen_pos' _
    have hc : 0 < c := o2 ▸ D.model.oppLen_pos' _
    obtain ⟨⟨m, n, hm, hn, e1⟩, ⟨m', n', hm', hn', e2⟩⟩ :=
      hR α' a b c hα' ⟨σ, OMA.E634H.comp_vec h0 h1 h2, OMA.E634H.comp_vec o0 o1 o2⟩ ha hb
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hmR' : (m' : ℝ) ≠ 0 := by exact_mod_cast hm'.ne'
    refine ⟨m', n', m, n, hm', hm, ?_, ?_⟩
    · rw [div_eq_div_iff hc.ne' hmR]; linarith
    · rw [div_eq_div_iff hc.ne' hmR']; linarith⟩
  obtain ⟨σ, hσ⟩ := hBσ
  obtain ⟨h0, h1, h2⟩ := OMA.E634H.vec_comp hσ
  exact TriangleTiling.Equilateral.notprime60 D hP ⟨σ, h0, h1, h2, rfl, rfl, rfl⟩ hα hp

