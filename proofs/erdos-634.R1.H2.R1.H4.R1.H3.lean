import OMAReductions.R_erdos_634_R1_H2_R1_H4_R1

/-!
# Erdos 634, step R1.H2.R1.H4.R1.H3: the tile (θ, pi - 3θ, 2θ)

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
theorem angle_indep {α : ℝ} (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (A B : ℤ)
    (h : (A : ℝ) * α + (B : ℝ) * Real.pi = 0) : A = 0 ∧ B = 0 := by
  have hA : A = 0 := by
    by_contra hA0
    apply hirr
    have hAR : (A : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hA0
    refine ⟨((-B : ℤ) : ℚ) / ((A : ℤ) : ℚ), ?_⟩
    push_cast
    field_simp
    linarith
  refine ⟨hA, ?_⟩
  have h' : (B : ℝ) * Real.pi = 0 := by
    rw [hA] at h
    push_cast at h
    linarith
  rcases mul_eq_zero.mp h' with hb | hpi
  · exact_mod_cast hb
  · exact absurd hpi Real.pi_ne_zero
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
theorem Tri.localAngle_interior (T : Tri) {p : Plane} (hp : p ∈ interior T.carrier) :
    T.localAngle p = 2 * Real.pi := by
  classical
  have hpos := T.interior_coord_pos hp
  have hv : ¬ ∃ j, p = T.pts j := by
    rintro ⟨j, rfl⟩
    have hne : ∀ m : Fin 3, m + 1 ≠ m := by decide
    have h0 : T.basis.coord (j + 1) (T.pts j) = 0 := T.basis.coord_apply_ne (hne j)
    exact absurd h0 (ne_of_gt (hpos (j + 1)))
  rw [Tri.localAngle, dif_neg hv, if_pos hpos]
theorem Tri.localAngle_frontier (T : Tri) {p : Plane} (hp : p ∈ frontier T.carrier)
    (hv : p ∉ Set.range T.pts) : T.localAngle p = Real.pi := by
  classical
  have hv' : ∀ k, p ≠ T.pts k := fun k h => hv ⟨k, h.symm⟩
  have hcar : p ∈ T.carrier := by
    have h1 : p ∈ closure T.carrier := frontier_subset_closure hp
    rwa [T.isCompact.isClosed.closure_eq] at h1
  have hnint : p ∉ interior T.carrier := fun h => hp.2 h
  rcases T.classify hv' with hpos | ⟨k, hk0, hkpos⟩ | ⟨k, hkneg⟩
  · exact absurd ((T.mem_interior_iff_coord_pos p).mpr hpos) hnint
  · have hIn : ¬ ∀ j, 0 < T.basis.coord j p := fun hI => absurd hk0 (ne_of_gt (hI k))
    rw [Tri.localAngle, dif_neg (not_exists.mpr hv'), if_neg hIn,
      if_pos ⟨k, hk0, hkpos⟩]
  · rw [T.carrier_eq_nonneg_coord] at hcar
    exact absurd (hcar k) (not_le.mpr hkneg)
theorem Tri.localAngle_vertex (T : Tri) (k : Fin 3) :
    T.localAngle (T.pts k)
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
  classical
  have hv : ∃ j, T.pts k = T.pts j := ⟨k, rfl⟩
  rw [Tri.localAngle, dif_pos hv]
  have hk : hv.choose = k := T.indep.injective hv.choose_spec.symm
  rw [hk]
theorem Dissection.volume_inter_ball_eq_sum {N : ℕ} (D : Dissection N) (x : Plane) (r : ℝ) :
    volume (D.target.carrier ∩ Metric.ball x r)
      = ∑ i, volume ((D.tile i).carrier ∩ Metric.ball x r) := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => (D.tile i).carrier ∩ Metric.ball x r)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) (D.aedisjoint hij))
    (fun i _ => ((D.tile i).nullMeasurableSet).inter
      Metric.isOpen_ball.measurableSet.nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), ((D.tile i).carrier ∩ Metric.ball x r))
          = D.target.carrier ∩ Metric.ball x r := by
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [← Set.iUnion_inter, D.covers]
  rw [hU] at h
  exact h
theorem Dissection.sum_localAngle_eq {N : ℕ} (D : Dissection N) (p : Plane) :
    ∑ i, (D.tile i).localAngle p = D.target.localAngle p := by
  classical
  obtain ⟨rT, hrT, hT⟩ := D.target.volume_inter_ball_localAngle p
  choose ri hri hcontrib using fun i => (D.tile i).volume_inter_ball_localAngle p
  obtain ⟨r0, hr0, hr0le⟩ := exists_common_radius D.pos ri hri
  set r : ℝ := min rT r0 with hrdef
  have hrpos : 0 < r := lt_min hrT hr0
  have hsum := D.volume_inter_ball_eq_sum p r
  rw [hT r hrpos (min_le_left _ _)] at hsum
  have htiles : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      volume ((D.tile i).carrier ∩ Metric.ball p r)
        = ENNReal.ofReal ((D.tile i).localAngle p / 2 * r ^ 2) := fun i _ =>
    hcontrib i r hrpos ((min_le_right _ _).trans (hr0le i))
  rw [Finset.sum_congr rfl htiles,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      have := (D.tile i).localAngle_nonneg p
      positivity)] at hsum
  have hreal := (ENNReal.ofReal_eq_ofReal_iff
    (by have := D.target.localAngle_nonneg p; positivity)
    (Finset.sum_nonneg fun i _ => by
      have := (D.tile i).localAngle_nonneg p
      positivity)).mp hsum
  have hfact : ∑ i, (D.tile i).localAngle p / 2 * r ^ 2
      = (∑ i, (D.tile i).localAngle p) * (r ^ 2 / 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfact] at hreal
  have hr2 : (0:ℝ) < r ^ 2 / 2 := by positivity
  have hkey : (∑ i, (D.tile i).localAngle p) * (r ^ 2 / 2)
      = D.target.localAngle p * (r ^ 2 / 2) := by
    rw [← hreal]; ring
  exact mul_right_cancel₀ hr2.ne' hkey
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
theorem Tri.Congruent.trans {T U V : Tri} (h₁ : T.Congruent U) (h₂ : U.Congruent V) :
    T.Congruent V := by
  obtain ⟨f, σ, hf⟩ := h₁
  obtain ⟨g, τ, hg⟩ := h₂
  exact ⟨f.trans g, σ.trans τ, fun k => by simp [hf k, hg (σ k)]⟩
theorem Tri.Congruent.dist_eq {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts (σ i)) (U.pts (σ j)) := by
  obtain ⟨f, σ, hf⟩ := h
  exact ⟨σ, fun i j => by rw [← hf i, ← hf j, f.dist_eq]⟩
noncomputable def Tri.relabel (T : Tri) (τ : Equiv.Perm (Fin 3)) : Tri where
  pts := T.pts ∘ τ
  indep := T.indep.comp_embedding τ.toEmbedding
theorem Tri.relabel_pts (T : Tri) (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (T.relabel τ).pts k = T.pts (τ k) := rfl
theorem Tri.congruent_relabel (T : Tri) (τ : Equiv.Perm (Fin 3)) : T.Congruent (T.relabel τ) := by
  refine ⟨IsometryEquiv.refl Plane, τ.symm, fun k => ?_⟩
  show T.pts k = (T.relabel τ).pts (τ.symm k)
  simp [Tri.relabel_pts]
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
theorem congruent_corner_angles {T U : Tri} (h : T.Congruent U) (j : Fin 3) :
    ∃ k : Fin 3, cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2))
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
  obtain ⟨σ, hd⟩ := h.dist_eq
  set k := σ.symm j with hk
  have hσk : σ k = j := by rw [hk]; simp
  refine ⟨k, ?_⟩
  have h1 : σ (k + 1) ≠ j := by
    intro hh; have := σ.injective (hh.trans hσk.symm)
    simp at this
  have h2 : σ (k + 2) ≠ j := by
    intro hh; have := σ.injective (hh.trans hσk.symm)
    simp at this
  have hne12 : σ (k + 1) ≠ σ (k + 2) := by
    intro hh; have := σ.injective hh; simp at this
  have hUne1 : U.pts (j + 1) ≠ U.pts j := by
    intro hh
    have := U.indep.injective hh
    have hne : j + 1 ≠ j := by fin_cases j <;> decide
    exact hne this
  have hUne2 : U.pts (j + 2) ≠ U.pts j := by
    intro hh
    have := U.indep.injective hh
    have hne : j + 2 ≠ j := by fin_cases j <;> decide
    exact hne this
  rcases fin3_cases (σ (k+1)) j h1 with hc1 | hc1
  · 
    have hc2 : σ (k + 2) = j + 2 := by
      rcases fin3_cases (σ (k+2)) j h2 with hx | hx
      · exfalso; exact hne12 (by rw [hc1, hx])
      · exact hx
    have ptj : U.pts j = U.pts (σ k) := by rw [hσk]
    have pt1 : U.pts (j + 1) = U.pts (σ (k + 1)) := by rw [hc1]
    have pt2 : U.pts (j + 2) = U.pts (σ (k + 2)) := by rw [hc2]
    refine angle_of_sss ?_ ?_ ?_ hUne1 hUne2
    · rw [pt1, ptj]; exact (hd (k+1) k).symm
    · rw [ptj, pt2]; exact (hd k (k+2)).symm
    · rw [pt1, pt2]; exact (hd (k+1) (k+2)).symm
  · 
    have hc2 : σ (k + 2) = j + 1 := by
      rcases fin3_cases (σ (k+2)) j h2 with hx | hx
      · exact hx
      · exfalso; exact hne12 (by rw [hc1, hx])
    have hcomm : cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2))
        = cornerAngle (U.pts (j + 2)) (U.pts j) (U.pts (j + 1)) :=
      EuclideanGeometry.angle_comm (V := Plane) _ _ _
    rw [hcomm]
    have ptj : U.pts j = U.pts (σ k) := by rw [hσk]
    have pt1 : U.pts (j + 2) = U.pts (σ (k + 1)) := by rw [hc1]
    have pt2 : U.pts (j + 1) = U.pts (σ (k + 2)) := by rw [hc2]
    refine angle_of_sss ?_ ?_ ?_ hUne2 hUne1
    · rw [pt1, ptj]; exact (hd (k+1) k).symm
    · rw [ptj, pt2]; exact (hd k (k+2)).symm
    · rw [pt1, pt2]; exact (hd (k+1) (k+2)).symm
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
open MeasureTheory Set
theorem Tri.carrier_subset_halfplane (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (h : ∀ i, f (T.pts i) ≤ c) : ∀ y ∈ T.carrier, f y ≤ c := by
  intro y hy
  rw [Tri.carrier] at hy
  have hsub : convexHull ℝ (Set.range T.pts) ⊆ {z | f z ≤ c} := by
    refine convexHull_min ?_ ?_
    · rintro z ⟨i, rfl⟩
      exact h i
    · intro p hp q hq a b ha hb hab
      simp only [Set.mem_setOf_eq] at hp hq ⊢
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have habc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
      have h1 : a * f p ≤ a * c := mul_le_mul_of_nonneg_left hp ha
      have h2 : b * f q ≤ b * c := mul_le_mul_of_nonneg_left hq hb
      linarith
  exact hsub hy
theorem Dissection.carrier_point_not_interior {N : ℕ} (D : Dissection N)
    {j : Fin N} {x : Plane} (hx : x ∈ (D.tile j).carrier) :
    ∀ i, i ≠ j → x ∉ interior (D.tile i).carrier := by
  intro i hij hi
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hi
  obtain ⟨y₀, hy₀⟩ := (D.tile j).interior_nonempty
  by_cases hyx : y₀ ∈ Metric.ball x r
  · exact Set.disjoint_left.mp (D.interiors_disjoint hij) (hball hyx) hy₀
  · have hd : r ≤ ‖y₀ - x‖ := by
      rw [Metric.mem_ball, dist_eq_norm] at hyx
      push_neg at hyx
      exact hyx
    have hdpos : 0 < ‖y₀ - x‖ := lt_of_lt_of_le hr hd
    set t := r / (2 * ‖y₀ - x‖) with htdef
    have htpos : 0 < t := by positivity
    have htlt : t < 1 := by
      rw [htdef]
      rw [div_lt_one (by positivity)]
      linarith
    set z := x + t • (y₀ - x) with hzdef
    have hz₁ : z ∈ openSegment ℝ x y₀ := by
      rw [openSegment_eq_image' ℝ x y₀]
      exact ⟨t, ⟨htpos, htlt⟩, rfl⟩
    have hz₂ : z ∈ interior (D.tile j).carrier := by
      have hseg : openSegment ℝ y₀ x ⊆ interior (D.tile j).carrier :=
        (D.tile j).convex.openSegment_interior_closure_subset_interior hy₀
          (subset_closure hx)
      rw [openSegment_symm ℝ x y₀] at hz₁
      exact hseg hz₁
    have hz₃ : z ∈ interior (D.tile i).carrier := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : z - x = t • (y₀ - x) := by rw [hzdef]; abel
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      have h2 : t * ‖y₀ - x‖ = r / 2 := by
        rw [htdef]; field_simp
      rw [h2]; linarith
    exact Set.disjoint_left.mp (D.interiors_disjoint hij) hz₃ hz₂
theorem Dissection.edge_point_not_interior {N : ℕ} (D : Dissection N)
    {j : Fin N} {k : Fin 3} {x : Plane} (hx : x ∈ (D.tile j).edge k) :
    ∀ i, x ∉ interior (D.tile i).carrier := by
  intro i hi
  by_cases hij : i = j
  · subst hij
    have hz := (D.tile i).coord_eq_zero_of_mem_edge k hx
    exact absurd hz (ne_of_gt ((D.tile i).interior_coord_pos hi (k + 2)))
  · exact D.carrier_point_not_interior ((D.tile j).edge_subset_carrier k hx) i hij hi
theorem openSegment_two_sided {u₁ u₂ x : Plane} (hx : x ∈ openSegment ℝ u₁ u₂) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, |ε| < ε₀ → x + ε • (u₂ - u₁) ∈ openSegment ℝ u₁ u₂ := by
  rw [openSegment_eq_image' ℝ u₁ u₂] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨min t (1 - t), lt_min ht.1 (by linarith [ht.2]), fun ε hε => ?_⟩
  rw [openSegment_eq_image' ℝ u₁ u₂]
  refine ⟨t + ε, ⟨?_, ?_⟩, ?_⟩
  · have h1 : |ε| < t := lt_of_lt_of_le hε (min_le_left _ _)
    have h2 := abs_lt.mp h1
    linarith [h2.1]
  · have h1 : |ε| < 1 - t := lt_of_lt_of_le hε (min_le_right _ _)
    have h2 := abs_lt.mp h1
    linarith [h2.2]
  · show u₁ + (t + ε) • (u₂ - u₁) = u₁ + t • (u₂ - u₁) + ε • (u₂ - u₁)
    rw [add_smul]
    abel
theorem Tri.edge_on_line (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    {x : Plane} {m : Fin 3}
    (hm : T.basis.coord m x = 0) (ho : ∀ j, j ≠ m → 0 < T.basis.coord j x)
    (hfx : f x = c) {w : Plane} (hw0 : w ≠ 0) (hfw : f w = 0)
    (hcross : cross (T.leftDir (m + 1)) w = 0) :
    f (T.pts (m + 1)) = c ∧ f (T.pts (m + 2)) = c ∧ f (T.pts m) ≠ c := by
  obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero (T.leftDir_ne_zero (m + 1)) hcross
  have hτne : τ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hτ
    exact hw0 hτ
  have hfdir : f (T.leftDir (m + 1)) = 0 := by
    have h1 : f w = τ * f (T.leftDir (m + 1)) := by rw [hτ, map_smul, smul_eq_mul]
    rw [hfw] at h1
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd h hτne
    · exact h
  have hidx : (m + 1) + 1 = m + 2 := by fin_cases m <;> rfl
  have hPQ : f (T.pts (m + 2)) = f (T.pts (m + 1)) := by
    rcases T.leftDir_eq_or (m + 1) with h | h
    · have h2 := hfdir
      rw [h, hidx, map_sub] at h2
      linarith
    · have h2 := hfdir
      rw [h, hidx, map_neg, map_sub] at h2
      linarith
  have hxe := T.mem_edge_of_coord_zero hm ho
  rw [Tri.edge, hidx] at hxe
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hxe
  have hfP : f (T.pts (m + 1)) = c := by
    have h1 : a * f (T.pts (m + 1)) + b * f (T.pts (m + 2)) = c := by
      rw [← hfx, ← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [hPQ] at h1
    have h2 : (a + b) * f (T.pts (m + 1)) = c := by rw [add_mul]; linarith
    rw [hab, one_mul] at h2
    exact h2
  have hfQ : f (T.pts (m + 2)) = c := by rw [hPQ, hfP]
  refine ⟨hfP, hfQ, fun hfm => ?_⟩
  have hall : ∀ i, f (T.pts i) = c := by
    intro i
    have h3 : ∀ i m : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    rcases h3 i m with rfl | rfl | rfl
    · exact hfm
    · exact hfP
    · exact hfQ
  exact two_vertices_on_line T f c hf hall
open Classical in
noncomputable def Dissection.lineChain {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e =>
    f ((D.tile e.1).pts e.2) = c ∧ f ((D.tile e.1).pts (e.2 + 1)) = c
      ∧ ∀ i, f ((D.tile e.1).pts i) ≤ c
theorem Dissection.mem_lineChain {N : ℕ} {D : Dissection N} {f : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    {e : Fin N × Fin 3} :
    e ∈ D.lineChain f c ↔
      f ((D.tile e.1).pts e.2) = c ∧ f ((D.tile e.1).pts (e.2 + 1)) = c
        ∧ ∀ i, f ((D.tile e.1).pts i) ≤ c := by
  classical
  simp [Dissection.lineChain]
theorem Dissection.lineChain_edge_subset {N : ℕ} (D : Dissection N)
    {f : Plane →ₗ[ℝ] ℝ} {c : ℝ} {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) :
    ∀ y ∈ (D.tile e.1).edge e.2, f y = c := by
  obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
  intro y hy
  rw [Tri.edge] at hy
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hy
  rw [← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h1, h2,
    ← add_mul, hab, one_mul]
theorem Dissection.wall_cover {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) {u₁ u₂ : Plane} (hu : u₁ ≠ u₂)
    (hS : segment ℝ u₁ u₂ ⊆ {y | f y = c})
    (hint : openSegment ℝ u₁ u₂ ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u₁ u₂, ∀ i, y ∉ interior (D.tile i).carrier)
    {x : Plane} (hx : x ∈ openSegment ℝ u₁ u₂) (hxv : x ∉ D.vertexSet) :
    ∃ e ∈ D.lineChain f c, x ∈ (D.tile e.1).edge e.2 := by
  classical
  have hnv := D.notMem_vertexSet hxv
  have hxint : x ∈ interior D.target.carrier := hint hx
  have hxtar : x ∈ D.target.carrier := interior_subset hxint
  have hfx : f x = c := hS (openSegment_subset_segment ℝ u₁ u₂ hx)
  have hw0 : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hfw : f (u₂ - u₁) = 0 := by
    have h1 : f u₁ = c := hS (left_mem_segment ℝ u₁ u₂)
    have h2 : f u₂ = c := hS (right_mem_segment ℝ u₁ u₂)
    rw [map_sub, h1, h2, sub_self]
  obtain ⟨j₀, hj₀⟩ : ∃ j, x ∈ (D.tile j).carrier := by
    have h1 := hxtar
    rw [← D.covers] at h1
    exact Set.mem_iUnion.mp h1
  rcases (D.tile j₀).classify (hnv j₀) with hpos | ⟨m₀, hm₀, ho₀⟩ | ⟨m₀, hneg⟩
  · obtain ⟨r, hr, hsub'⟩ := (D.tile j₀).ball_subset_of_pos hpos
    exact absurd (mem_interior.mpr ⟨Metric.ball x r, hsub', Metric.isOpen_ball,
      Metric.mem_ball_self hr⟩) (hwall x hx j₀)
  · 
    have hcr : cross ((D.tile j₀).leftDir (m₀ + 1)) (u₂ - u₁) = 0 := by
      by_contra hc
      obtain ⟨ε₀, hε₀, hmove⟩ := openSegment_two_sided hx
      rcases lt_or_gt_of_ne hc with hneg' | hpos'
      · have hpos'' : 0 < cross ((D.tile j₀).leftDir (m₀ + 1)) (-(u₂ - u₁)) := by
          rw [← neg_one_smul ℝ (u₂ - u₁), cross_smul_right]
          linarith
        obtain ⟨ε₁, hε₁, hpush⟩ := (D.tile j₀).mem_interior_of_cross_pos hm₀ ho₀ hpos''
        set ε := min ε₀ ε₁ / 2 with hεdef
        have hεpos : 0 < ε := by
          rw [hεdef]; have := lt_min hε₀ hε₁; linarith
        have hlt₁ : ε < ε₁ := by
          rw [hεdef]
          have h2 := min_le_right ε₀ ε₁
          have := lt_min hε₀ hε₁
          linarith
        have hlt₀ : ε < ε₀ := by
          rw [hεdef]
          have h2 := min_le_left ε₀ ε₁
          have := lt_min hε₀ hε₁
          linarith
        have h1 : x + ε • -(u₂ - u₁) ∈ interior (D.tile j₀).carrier := hpush ε hεpos hlt₁
        have h2 : x + ε • -(u₂ - u₁) ∈ openSegment ℝ u₁ u₂ := by
          have h3 : x + ε • -(u₂ - u₁) = x + (-ε) • (u₂ - u₁) := by
            rw [smul_neg, neg_smul]
          rw [h3]
          apply hmove
          rw [abs_neg, abs_of_pos hεpos]
          exact hlt₀
        exact absurd h1 (hwall _ h2 j₀)
      · obtain ⟨ε₁, hε₁, hpush⟩ := (D.tile j₀).mem_interior_of_cross_pos hm₀ ho₀ hpos'
        set ε := min ε₀ ε₁ / 2 with hεdef
        have hεpos : 0 < ε := by
          rw [hεdef]; have := lt_min hε₀ hε₁; linarith
        have hlt₁ : ε < ε₁ := by
          rw [hεdef]
          have h2 := min_le_right ε₀ ε₁
          have := lt_min hε₀ hε₁
          linarith
        have hlt₀ : ε < ε₀ := by
          rw [hεdef]
          have h2 := min_le_left ε₀ ε₁
          have := lt_min hε₀ hε₁
          linarith
        have h1 : x + ε • (u₂ - u₁) ∈ interior (D.tile j₀).carrier := hpush ε hεpos hlt₁
        have h2 : x + ε • (u₂ - u₁) ∈ openSegment ℝ u₁ u₂ := by
          apply hmove
          rw [abs_of_pos hεpos]
          exact hlt₀
        exact absurd h1 (hwall _ h2 j₀)
    obtain ⟨hfP, hfQ, hfm⟩ := (D.tile j₀).edge_on_line f c hf hm₀ ho₀ hfx hw0 hfw hcr
    have hxe : x ∈ (D.tile j₀).edge (m₀ + 1) := (D.tile j₀).mem_edge_of_coord_zero hm₀ ho₀
    have hidx : ∀ m : Fin 3, (m + 1) + 1 = m + 2 := by decide
    have h3 : ∀ i m : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    rcases lt_or_gt_of_ne hfm with hlt | hgt
    · refine ⟨(j₀, m₀ + 1), ?_, hxe⟩
      rw [Dissection.mem_lineChain]
      refine ⟨hfP, by rw [hidx m₀]; exact hfQ, ?_⟩
      intro i
      rcases h3 i m₀ with rfl | rfl | rfl
      · exact hlt.le
      · exact hfP.le
      · exact hfQ.le
    · 
      have hN := D.pos
      obtain ⟨R, hR, hRt'⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
      have hRt : Metric.ball x R ⊆ D.target.carrier := hRt'.trans interior_subset
      obtain ⟨j₁, hne, hOn⟩ := D.second_tile_at_edge_point hN hnv hR hRt ⟨m₀, hm₀, ho₀⟩
      obtain ⟨m₁, hm₁, ho₁⟩ := hOn
      obtain ⟨c₀, hc₀neg, hc₀⟩ := D.leftDir_antiparallel (Ne.symm hne) hm₀ ho₀ hm₁ ho₁
      have hcr₁ : cross ((D.tile j₁).leftDir (m₁ + 1)) (u₂ - u₁) = 0 := by
        rw [hc₀, cross_smul_left, hcr, mul_zero]
      obtain ⟨hfP₁, hfQ₁, hfm₁⟩ := (D.tile j₁).edge_on_line f c hf hm₁ ho₁ hfx hw0 hfw hcr₁
      have hxe₁ : x ∈ (D.tile j₁).edge (m₁ + 1) := (D.tile j₁).mem_edge_of_coord_zero hm₁ ho₁
      rcases lt_or_gt_of_ne hfm₁ with hlt₁ | hgt₁
      · refine ⟨(j₁, m₁ + 1), ?_, hxe₁⟩
        rw [Dissection.mem_lineChain]
        refine ⟨hfP₁, by rw [hidx m₁]; exact hfQ₁, ?_⟩
        intro i
        rcases h3 i m₁ with rfl | rfl | rfl
        · exact hlt₁.le
        · exact hfP₁.le
        · exact hfQ₁.le
      · 
        exfalso
        have hle₀ : ∀ y ∈ (D.tile j₀).carrier, (-f) y ≤ -c := by
          apply (D.tile j₀).carrier_subset_halfplane
          intro i
          simp only [LinearMap.neg_apply]
          rcases h3 i m₀ with rfl | rfl | rfl
          · linarith
          · linarith [hfP.le, hfP.ge]
          · linarith [hfQ.le, hfQ.ge]
        have hle₁ : ∀ y ∈ (D.tile j₁).carrier, (-f) y ≤ -c := by
          apply (D.tile j₁).carrier_subset_halfplane
          intro i
          simp only [LinearMap.neg_apply]
          rcases h3 i m₁ with rfl | rfl | rfl
          · linarith
          · linarith [hfP₁.le, hfP₁.ge]
          · linarith [hfQ₁.le, hfQ₁.ge]
        have hfx' : (-f) x = -c := by
          simp only [LinearMap.neg_apply, hfx]
        have hf' : (-f : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf (neg_eq_zero.mp h)
        exact D.no_second_tile_same_side (Ne.symm hne) (-f) (-c) hf' hle₀ hle₁ hfx'
          hm₀ ho₀ hm₁ ho₁
  · rw [(D.tile j₀).carrier_eq_nonneg_coord] at hj₀
    exact absurd (hj₀ m₀) (not_le.mpr hneg)
theorem Dissection.wall_partition {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) {u₁ u₂ : Plane} (hu : u₁ ≠ u₂)
    (hS : segment ℝ u₁ u₂ ⊆ {y | f y = c})
    (hint : openSegment ℝ u₁ u₂ ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u₁ u₂, ∀ i, y ∉ interior (D.tile i).carrier) :
    ∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) (segment ℝ u₁ u₂) := by
  classical
  have hclseg : IsClosed (segment ℝ u₁ u₂) := by
    rw [segment_eq_image ℝ u₁ u₂]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  apply sum_hausdorff_of_partition (D.lineChain f c)
    (fun e => (D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂) (segment ℝ u₁ u₂)
    (D.vertexSet ∪ {u₁, u₂})
    (D.vertexSet_finite.union ((Set.finite_singleton u₂).insert u₁))
  · exact fun e _ => (((D.tile e.1).isClosed_edge e.2).inter hclseg).measurableSet
  · intro e₁ h₁ e₂ h₂ hne
    have hsub : ((D.tile e₁.1).edge e₁.2 ∩ segment ℝ u₁ u₂)
        ∩ ((D.tile e₂.1).edge e₂.2 ∩ segment ℝ u₁ u₂)
        ⊆ (D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2 :=
      fun y hy => ⟨hy.1.1, hy.2.1⟩
    refine Set.Subsingleton.anti ?_ hsub
    obtain ⟨hP₁, hQ₁, hle₁⟩ := Dissection.mem_lineChain.mp h₁
    obtain ⟨hP₂, hQ₂, hle₂⟩ := Dissection.mem_lineChain.mp h₂
    exact D.sameside_edges_subsingleton f c hf hne
      ((D.tile e₁.1).carrier_subset_halfplane f c hle₁)
      ((D.tile e₂.1).carrier_subset_halfplane f c hle₂)
      (D.lineChain_edge_subset h₁) (D.lineChain_edge_subset h₂)
  · exact fun e _ => Set.inter_subset_right
  · intro y hy
    obtain ⟨hyS, hyF⟩ := hy
    rw [Set.mem_union, not_or] at hyF
    obtain ⟨hyv, hyends⟩ := hyF
    have hy1 : u₁ ≠ y := fun h => hyends (by rw [← h]; exact Set.mem_insert _ _)
    have hy2 : u₂ ≠ y := fun h => hyends (by rw [← h]; simp)
    have hyopen : y ∈ openSegment ℝ u₁ u₂ :=
      mem_openSegment_of_ne_left_right hy1 hy2 hyS
    obtain ⟨e, he, hye⟩ := D.wall_cover f c hf hu hS hint hwall hyopen hyv
    exact Set.mem_iUnion₂.mpr ⟨e, he, hye, hyS⟩
theorem Tri.edge_line (T : Tri) (k : Fin 3) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ ∀ y ∈ T.edge k, f y = c := by
  have hne : T.pts (k + 1) - T.pts k ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h1 : k + 1 = k := T.indep.injective h
    have h2 : ∀ m : Fin 3, m + 1 ≠ m := by decide
    exact h2 k h1
  refine ⟨crossL (T.pts (k + 1) - T.pts k),
    cross (T.pts (k + 1) - T.pts k) (T.pts k), crossL_ne_zero hne, ?_⟩
  intro y hy
  rw [Tri.edge] at hy
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hy
  have hPP' : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 1))
      = cross (T.pts (k + 1) - T.pts k) (T.pts k) := by
    have h1 : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 1) - T.pts k) = 0 := cross_self _
    rw [cross_sub_right] at h1
    linarith
  rw [crossL_apply, ← hcomb, cross_add_right, cross_smul_right, cross_smul_right, hPP',
    ← add_mul, hab, one_mul]
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
def permTri (U : Tri) (σ : Equiv.Perm (Fin 3)) : Tri where
  pts := U.pts ∘ σ
  indep := U.indep.comp_embedding σ.toEmbedding
theorem congruent_permTri (U : Tri) (σ : Equiv.Perm (Fin 3)) : (permTri U σ).Congruent U :=
  ⟨IsometryEquiv.refl Plane, σ, fun k => rfl⟩
theorem congruent_of_dist_perm {T U : Tri} (σ : Equiv.Perm (Fin 3))
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts (σ i)) (U.pts (σ j))) : T.Congruent U :=
  (congruent_of_dist (U := permTri U σ) hd).trans (congruent_permTri U σ)
end Erdos634.SssCongruent
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
end Erdos634.MarchFlank
end

section
open scoped Classical
namespace Erdos634.Geometry
open Real
variable {N : ℕ}
theorem Row2.fin3_rot : ∀ a b c : Fin 3, b ≠ a → c ≠ a → b ≠ c →
    (b = a + 1 ∧ c = a + 2) ∨ (b = a + 2 ∧ c = a + 1) := by decide
theorem Row2.perm_succ (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (σ (k + 1) = σ k + 1 ∧ σ (k + 2) = σ k + 2) ∨ (σ (k + 1) = σ k + 2 ∧ σ (k + 2) = σ k + 1) := by
  have h1 : k + 1 ≠ k := by
    have : ∀ a : Fin 3, a + 1 ≠ a := by decide
    exact this k
  have h2 : k + 2 ≠ k := by
    have : ∀ a : Fin 3, a + 2 ≠ a := by decide
    exact this k
  have h12 : k + 1 ≠ k + 2 := by
    have : ∀ a : Fin 3, a + 1 ≠ a + 2 := by decide
    exact this k
  exact Row2.fin3_rot _ _ _ (fun h => h1 (σ.injective h)) (fun h => h2 (σ.injective h))
    (fun h => h12 (σ.injective h))
theorem Row2.angleAt_comp (T U : Tri) (σ : Equiv.Perm (Fin 3)) (hU : ∀ k, U.pts k = T.pts (σ k))
    (k : Fin 3) : U.angleAt k = T.angleAt (σ k) ∧ U.oppLen k = T.oppLen (σ k) := by
  unfold Tri.angleAt Tri.oppLen
  simp only [hU]
  rcases Row2.perm_succ σ k with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact ⟨rfl, rfl⟩
  · rw [h1, h2]; exact ⟨EuclideanGeometry.angle_comm _ _ _, dist_comm _ _⟩
end Erdos634.Geometry
end

section
theorem gamma2alpha_param (a b c : ℕ) (hb : 0 < b)
    (hc : c ^ 2 = a ^ 2 + a * b) (hcop : Nat.gcd (Nat.gcd a b) c = 1) :
    ∃ k m : ℕ, Nat.Coprime k m ∧ k < m ∧ a = k ^ 2 ∧ b = m ^ 2 - k ^ 2 ∧ c = k * m := by
  have hcab : c ^ 2 = a * (a + b) := by rw [hc]; ring
  set g := Nat.gcd a b with hg
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have hg2c2 : g ^ 2 ∣ c ^ 2 := by
    rw [hcab, pow_two]; exact mul_dvd_mul hga (Nat.dvd_add hga hgb)
  have hgc : g ∣ c := (Nat.pow_dvd_pow_iff (by norm_num)).mp hg2c2
  have hg1 : g = 1 := by rw [← Nat.gcd_eq_left hgc]; exact hcop
  have hcopab : Nat.Coprime a b := hg1
  have hcopab' : Nat.Coprime a (a + b) := by
    rw [add_comm]; exact (Nat.coprime_add_self_right).mpr hcopab
  have hsq : a * (a + b) = c ^ 2 := hcab.symm
  have hua : IsUnit (gcd a (a + b)) := by
    rw [Nat.isUnit_iff]; exact hcopab'
  have hub : IsUnit (gcd (a + b) a) := by
    rw [Nat.isUnit_iff]; exact hcopab'.symm
  obtain ⟨k, hk⟩ := exists_eq_pow_of_mul_eq_pow hua hsq
  obtain ⟨m, hm⟩ := exists_eq_pow_of_mul_eq_pow hub (by rw [mul_comm]; exact hsq)
  have hkn : a = k ^ 2 := hk
  have hmn : a + b = m ^ 2 := hm
  have hlt : k ^ 2 < m ^ 2 := by omega
  have hkm : k < m := by
    by_contra h; push_neg at h; have := Nat.pow_le_pow_left h 2; omega
  have hcopkm : Nat.Coprime k m := by
    have h2 : Nat.Coprime (k ^ 2) (m ^ 2) := by rw [← hkn, ← hmn]; exact hcopab'
    exact Nat.Coprime.coprime_dvd_right (dvd_pow_self m two_ne_zero)
      (Nat.Coprime.coprime_dvd_left (dvd_pow_self k two_ne_zero) h2)
  have hceq : c = k * m := by
    have : c ^ 2 = (k * m) ^ 2 := by rw [hcab, hmn, hkn]; ring
    exact Nat.pow_left_injective (by norm_num) this
  exact ⟨k, m, hcopkm, hkm, hkn, by omega, hceq⟩
end

section
namespace TriangleTiling
open EuclideanGeometry
section Geometry
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]
theorem dist_lt_dist_add_dist_of_not_collinear {A B C : P}
    (h : ¬ Collinear ℝ ({A, B, C} : Set P)) : dist A C < dist A B + dist B C := by
  rcases (dist_triangle A B C).lt_or_eq with h' | h'
  · exact h'
  · exact absurd (dist_add_dist_eq_iff.mp h'.symm).collinear h
theorem twoalphatiles {A B C : P} {a b c : ℝ} (hABC : AffineIndependent ℝ ![A, B, C])
    (ha : dist B C = a) (hb : dist C A = b) (hc : dist A B = c) :
    ∠ A C B = 2 * ∠ B A C ↔ c ^ 2 = a ^ 2 + a * b := by
  have hcol := affineIndependent_iff_not_collinear_set.mp hABC
  have t1 := dist_lt_dist_add_dist_of_not_collinear hcol
  have t2 := dist_lt_dist_add_dist_of_not_collinear (A := B) (B := A) (C := C)
    (by rwa [Set.insert_comm])
  have t3 := dist_lt_dist_add_dist_of_not_collinear (A := A) (B := C) (C := B)
    (by rwa [Set.pair_comm])
  rw [dist_comm A C, hb, hc, ha] at t1
  rw [dist_comm B A, hc, ha, dist_comm A C, hb] at t2
  rw [hc, dist_comm A C, hb, dist_comm C B, ha] at t3
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  set x := Real.cos (∠ B A C) with hx
  set y := Real.cos (∠ A C B) with hy
  have hα : 2 * b * c * x = b ^ 2 + c ^ 2 - a ^ 2 := by
    have := law_cos B A C
    rw [ha, dist_comm B A, hc, hb, ← hx] at this
    linear_combination this
  have hγ : 2 * a * b * y = a ^ 2 + b ^ 2 - c ^ 2 := by
    have := law_cos A C B
    rw [hc, dist_comm A C, hb, ha, ← hy] at this
    linear_combination this
  have key : (a + b) * (c ^ 2 - a ^ 2 - a * b) * ((b - a) ^ 2 - c ^ 2)
      = 2 * a * b ^ 2 * c ^ 2 * (y - (2 * x ^ 2 - 1)) := by
    linear_combination (-(b * c ^ 2)) * hγ + (a * ((b ^ 2 + c ^ 2 - a ^ 2) + 2 * b * c * x)) * hα
  have hneg : (b - a) ^ 2 - c ^ 2 < 0 := by nlinarith
  constructor
  · intro h
    have hy2 : y - (2 * x ^ 2 - 1) = 0 := by
      rw [hy, h, Real.cos_two_mul]; ring
    rw [hy2, mul_zero] at key
    have hab : a + b ≠ 0 := by positivity
    rcases mul_eq_zero.mp key with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hab
      · linarith
    · linarith
  · intro h
    have hy2 : y - (2 * x ^ 2 - 1) = 0 := by
      have : 2 * a * b ^ 2 * c ^ 2 * (y - (2 * x ^ 2 - 1)) = 0 := by
        rw [← key]; simp [show c ^ 2 - a ^ 2 - a * b = 0 by linarith]
      rcases mul_eq_zero.mp this with h1 | h1
      · exfalso; have : 0 < 2 * a * b ^ 2 * c ^ 2 := by positivity
        linarith
      · exact h1
    have hx0 : 0 < x := by
      have : 0 < 2 * b * c * x := by rw [hα]; nlinarith
      have : 0 < 2 * b * c := by positivity
      exact pos_of_mul_pos_right ‹0 < 2 * b * c * x› this.le
    have hαle : ∠ B A C ≤ Real.pi / 2 := by
      by_contra hcon
      push Not at hcon
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hcon.le
        (by linarith [angle_le_pi B A C, Real.pi_pos])
      linarith
    apply Real.injOn_cos ⟨angle_nonneg A C B, angle_le_pi A C B⟩
      ⟨by linarith [angle_nonneg B A C], by linarith⟩
    rw [Real.cos_two_mul, ← hx, ← hy]
    linarith
end Geometry
theorem luthar (a b c : ℕ) :
    (Nat.gcd (Nat.gcd a b) c = 1 ∧ c ^ 2 = a ^ 2 + a * b ∧
      a < b + c ∧ b < a + c ∧ c < a + b) ↔
    ∃ k m : ℕ, Nat.Coprime k m ∧ k < m ∧ m < 2 * k ∧
      a = k ^ 2 ∧ b = m ^ 2 - k ^ 2 ∧ c = k * m := by
  constructor
  · rintro ⟨hcop, hc, h1, h2, h3⟩
    have hb : 0 < b := by omega
    obtain ⟨k, m, hkm_cop, hkm, rfl, rfl, rfl⟩ := gamma2alpha_param a b c hb hc hcop
    refine ⟨k, m, hkm_cop, hkm, ?_, rfl, rfl, rfl⟩
    have hle : k ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hkm.le 2
    zify [hle] at h2
    have : (m : ℤ) < 2 * k := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_nonneg (sub_nonneg.mpr hcon) (by positivity : (0 : ℤ) ≤ m + k)]
    exact_mod_cast this
  · rintro ⟨k, m, hkm_cop, hkm, hm2k, rfl, rfl, rfl⟩
    have hle : k ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hkm.le 2
    have hkmZ : (k : ℤ) < m := by exact_mod_cast hkm
    have hm2kZ : (m : ℤ) < 2 * k := by exact_mod_cast hm2k
    have hk0 : (0 : ℤ) ≤ k := by positivity
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · 
      set d := Nat.gcd (Nat.gcd (k ^ 2) (m ^ 2 - k ^ 2)) (k * m)
      have hda : d ∣ k ^ 2 := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
      have hdb : d ∣ m ^ 2 - k ^ 2 := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
      have hdm : d ∣ m ^ 2 := by
        have := Nat.dvd_add hdb hda
        rwa [Nat.sub_add_cancel hle] at this
      have := Nat.dvd_gcd hda hdm
      rw [(Nat.Coprime.pow 2 2 hkm_cop).gcd_eq_one] at this
      exact Nat.dvd_one.mp this
    · zify [hle]; ring
    · 
      zify [hle]
      nlinarith [mul_pos (sub_pos.mpr hkmZ) (by omega : (0 : ℤ) < m + 2 * k)]
    · 
      zify [hle]
      nlinarith [mul_pos (sub_pos.mpr hm2kZ) (by omega : (0 : ℤ) < k + m)]
    · 
      zify [hle]
      nlinarith [mul_pos (by omega : (0 : ℤ) < m) (sub_pos.mpr hkmZ)]
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry MeasureTheory
theorem strict_triangle_ineqs {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {A B C : P} (h : AffineIndependent ℝ ![A, B, C]) :
    dist B C < dist C A + dist A B ∧ dist C A < dist A B + dist B C ∧
      dist A B < dist B C + dist C A := by
  have hcol := affineIndependent_iff_not_collinear_set.mp h
  have t1 := dist_lt_dist_add_dist_of_not_collinear hcol
  have t2 := dist_lt_dist_add_dist_of_not_collinear (A := B) (B := A) (C := C)
    (by rwa [Set.insert_comm])
  have t3 := dist_lt_dist_add_dist_of_not_collinear (A := A) (B := C) (C := B)
    (by rwa [Set.pair_comm])
  rw [dist_comm A C] at t1
  rw [dist_comm B A, dist_comm A C] at t2
  rw [dist_comm A C, dist_comm C B] at t3
  exact ⟨by linarith, t1, by linarith⟩
theorem tri_indep (T : Tri) : AffineIndependent ℝ ![T.pts 0, T.pts 1, T.pts 2] := by
  convert T.indep using 1
  ext i; fin_cases i <;> rfl
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
theorem areaequation_core {N : ℕ} (D : CongruentDissection N) {a b c X Y : ℝ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hX : dist (D.target.pts 0) (D.target.pts 1) = X)
    (hY : dist (D.target.pts 2) (D.target.pts 0) = Y)
    (hγ : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) =
      2 * ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)) :
    dist (D.target.pts 1) (D.target.pts 2) = X ∧ a * Y = c * X ∧ X ^ 2 = N * a * b := by
  set M := D.model.pts with hM
  set T := D.target.pts with hT
  set X' := dist (T 1) (T 2) with hX'
  set k := Real.cos (∠ (M 1) (M 0) (M 2)) with hk
  have hcab : c ^ 2 = a ^ 2 + a * b := (twoalphatiles (tri_indep D.model) ha hb hc).mp hγ
  obtain ⟨m1, m2, m3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at m1 m2 m3
  obtain ⟨t1, t2, t3⟩ := strict_triangle_ineqs (tri_indep D.target)
  rw [hX, hY] at t1 t2 t3
  rw [← hX'] at t1 t2 t3
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hY0 : 0 < Y := by linarith
  have hα : 2 * b * c * k = b ^ 2 + c ^ 2 - a ^ 2 := by
    have := law_cos (M 1) (M 0) (M 2)
    rw [ha, dist_comm (M 1) (M 0), hc, hb, ← hk] at this
    linear_combination this
  have eA : X' ^ 2 = X ^ 2 + Y ^ 2 - 2 * X * Y * k := by
    have := law_cos (T 1) (T 0) (T 2)
    rw [hA, ← hk, dist_comm (T 1) (T 0), hX, hY] at this
    linear_combination this
  have eC : X ^ 2 = X' ^ 2 + Y ^ 2 - 2 * X' * Y * k := by
    have := law_cos (T 1) (T 2) (T 0)
    rw [hC, ← hk, dist_comm (T 1) (T 0), hX, dist_comm (T 0) (T 2), hY] at this
    linear_combination this
  have p1 : (0 : ℝ) < a - b + c := by linarith
  have p2 : (0 : ℝ) < a + b - c := by linarith
  have p3 : (0 : ℝ) < b + c - a := by linarith
  have p4 : (0 : ℝ) < a + b + c := by linarith
  have e1 : 2 * b * c * (1 - k) = (a - b + c) * (a + b - c) := by linear_combination -hα
  have e2 : 2 * b * c * (1 + k) = (b + c - a) * (a + b + c) := by linear_combination hα
  have hbc : 0 < 2 * b * c := by positivity
  have hk1 : k < 1 := by nlinarith [mul_pos p1 p2]
  have hk1' : -1 < k := by nlinarith [mul_pos p3 p4]
  have hXX : X' = X := by
    have h0 : (X' - X) * (X' + X - Y * k) = 0 := by linear_combination (eA - eC) / 2
    have h1 : X' + X - Y * k ≠ 0 := by nlinarith
    have := (mul_eq_zero.mp h0).resolve_right h1
    linarith
  have hYk : Y = 2 * X * k := by
    rw [hXX] at eA
    have : Y * (Y - 2 * X * k) = 0 := by linear_combination -eA
    have := (mul_eq_zero.mp this).resolve_left hY0.ne'
    linarith
  have hak : 2 * a * k = c := by
    have h1 : b * (2 * c * k - (a + b)) = 0 := by linear_combination hα + hcab
    have h2 := (mul_eq_zero.mp h1).resolve_left hb0.ne'
    have h3 : c * (2 * a * k - c) = 0 := by linear_combination a * h2 - hcab
    have := (mul_eq_zero.mp h3).resolve_left hc0.ne'
    linarith
  refine ⟨hXX, by rw [hYk, ← hak]; ring, ?_⟩
  have hH := area_heron D
  rw [ha, hb, hc, ← hX', hXX, hY, hX] at hH
  have hH1 : heron16 a b c = 4 * b ^ 2 * c ^ 2 * (1 - k ^ 2) := by
    unfold heron16; linear_combination (2 * b * c * k + (b ^ 2 + c ^ 2 - a ^ 2)) * hα
  have hH2 : heron16 X Y X = 16 * X ^ 4 * k ^ 2 * (1 - k ^ 2) := by
    unfold heron16; rw [hYk]; ring
  rw [hH1, hH2] at hH
  have hpos : 0 < 1 - k ^ 2 := by
    have := mul_pos (sub_pos.mpr hk1) (show (0 : ℝ) < 1 + k by linarith)
    linarith [show (1 - k) * (1 + k) = 1 - k ^ 2 by ring]
  have h4 : (N : ℝ) ^ 2 * b ^ 2 * c ^ 2 = 4 * X ^ 4 * k ^ 2 := by
    have : (1 - k ^ 2) * (4 * ((N : ℝ) ^ 2 * b ^ 2 * c ^ 2 - 4 * X ^ 4 * k ^ 2)) = 0 := by
      linear_combination hH
    have := (mul_eq_zero.mp this).resolve_left hpos.ne'
    linarith
  have h5 : c ^ 2 * (((N : ℝ) * a * b) ^ 2 - (X ^ 2) ^ 2) = 0 := by
    linear_combination a ^ 2 * h4 + (X ^ 4 * (2 * a * k + c)) * hak
  have h6 := (mul_eq_zero.mp h5).resolve_left (by positivity)
  have h7 : (X ^ 2 - N * a * b) * (X ^ 2 + N * a * b) = 0 := by linear_combination -h6
  have h8 : 0 < X ^ 2 + N * a * b := by
    have : 0 < X := by linarith
    positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp h7).resolve_right h8.ne')
end TriangleTiling
end

section
namespace TriangleTiling
open Set
variable {ι : Type*}
theorem exists_bound_left (s : Finset ι) (lo hi : ι → ℝ) (x : ℝ) {m₀ : ℝ} (hm₀ : m₀ < x)
    (h : ∀ k ∈ s, lo k < x → hi k < x) :
    ∃ m, m < x ∧ m₀ ≤ m ∧ ∀ k ∈ s, lo k < x → hi k ≤ m := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨m₀, hm₀, le_rfl, fun k hk => absurd hk (Finset.notMem_empty k)⟩
  | insert j s hj ih =>
    obtain ⟨m, hmx, hm0, hm⟩ := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    by_cases hjx : lo j < x
    · have hj' := h j (Finset.mem_insert_self j s) hjx
      refine ⟨max m (hi j), max_lt hmx hj', le_trans hm0 (le_max_left _ _), ?_⟩
      intro k hk hkx
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact le_max_right _ _
      · exact le_trans (hm k hk hkx) (le_max_left _ _)
    · refine ⟨m, hmx, hm0, ?_⟩
      intro k hk hkx
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact absurd hkx hjx
      · exact hm k hk hkx
theorem exists_bound_right (s : Finset ι) (lo hi : ι → ℝ) (x : ℝ) {m₀ : ℝ} (hm₀ : x < m₀)
    (h : ∀ k ∈ s, x < hi k → x < lo k) :
    ∃ m, x < m ∧ m ≤ m₀ ∧ ∀ k ∈ s, x < hi k → m ≤ lo k := by
  obtain ⟨m, hmx, hm0, hm⟩ := exists_bound_left s (fun k => -hi k) (fun k => -lo k) (-x)
    (m₀ := -m₀) (by linarith) (fun k hk hkx => by have := h k hk (by linarith); linarith)
  exact ⟨-m, by linarith, by linarith, fun k hk hkx => by have := hm k hk (by linarith); linarith⟩
theorem exists_interval_left (s : Finset ι) (lo hi : ι → ℝ) (x : ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {E : Set ℝ} (hE : E.Finite)
    (hcov : ∀ y ∈ Ioo (x - δ₀) x, y ∉ E → ∃ k ∈ s, y ∈ Icc (lo k) (hi k)) :
    ∃ k ∈ s, lo k < x ∧ x ≤ hi k := by
  by_contra hno
  push Not at hno
  obtain ⟨m, hmx, hm0, hm⟩ := exists_bound_left s lo hi x (m₀ := x - δ₀) (by linarith) hno
  obtain ⟨y, hy, hyE⟩ := ((Set.Ioo_infinite hmx).diff hE).nonempty
  obtain ⟨k, hk, hyk⟩ := hcov y ⟨by linarith [hy.1], hy.2⟩ hyE
  have := hm k hk (lt_of_le_of_lt hyk.1 hy.2)
  linarith [hy.1, hyk.2]
theorem exists_interval_right (s : Finset ι) (lo hi : ι → ℝ) (x : ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {E : Set ℝ} (hE : E.Finite)
    (hcov : ∀ y ∈ Ioo x (x + δ₀), y ∉ E → ∃ k ∈ s, y ∈ Icc (lo k) (hi k)) :
    ∃ k ∈ s, lo k ≤ x ∧ x < hi k := by
  by_contra hno
  push Not at hno
  obtain ⟨m, hmx, hm0, hm⟩ := exists_bound_right s lo hi x (m₀ := x + δ₀) (by linarith)
    (fun k hk hkx => by by_contra h; push Not at h; exact absurd (hno k hk h) (not_le.mpr hkx))
  obtain ⟨y, hy, hyE⟩ := ((Set.Ioo_infinite hmx).diff hE).nonempty
  obtain ⟨k, hk, hyk⟩ := hcov y ⟨hy.1, by linarith [hy.2]⟩ hyE
  have := hm k hk (lt_of_lt_of_le hy.1 hyk.2)
  linarith [hy.2, hyk.1]
end TriangleTiling
end

section
namespace TriangleTiling
open Set
variable {ι : Type*} (s : Finset ι) (l r : ι → ℝ)
structure IntervalChain : Prop where
  lt : ∀ k ∈ s, l k < r k
  sub : ∀ k ∈ s, 0 ≤ l k ∧ r k ≤ 1
  cover : ∀ x, 0 ≤ x → x ≤ 1 → ∃ k ∈ s, l k ≤ x ∧ x ≤ r k
  disj : ∀ k ∈ s, ∀ j ∈ s, k ≠ j → (Icc (l k) (r k) ∩ Icc (l j) (r j)).Subsingleton
variable {s l r}
theorem IntervalChain.exists_left_eq_right (h : IntervalChain s l r) {k : ι} (hk : k ∈ s)
    (hr1 : r k ≠ 1) : ∃ j ∈ s, l j = r k := by
  classical
  have hrk : r k < 1 := lt_of_le_of_ne (h.sub k hk).2 hr1
  by_contra hno
  push Not at hno
  have hstep : ∃ j ∈ s, l j ≤ r k ∧ r k < r j := by
    set T : Finset ℝ := insert 1 ((s.filter fun j => r k < l j).image l) with hT
    have hTne : T.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
    set m := T.min' hTne
    have hmT : ∀ x ∈ T, r k < x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hrk
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        exact (Finset.mem_filter.mp hj).2
    have hm : r k < m := hmT m (Finset.min'_mem T hTne)
    have hm1 : m ≤ 1 := Finset.min'_le T 1 (Finset.mem_insert_self _ _)
    have h0 : 0 ≤ r k := (h.sub k hk).1.trans (h.lt k hk).le
    obtain ⟨j, hj, hlj, hrj⟩ := h.cover ((r k + m) / 2) (by linarith) (by linarith)
    refine ⟨j, hj, ?_, by linarith⟩
    by_contra hlt
    push Not at hlt
    have : m ≤ l j := Finset.min'_le T (l j)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hlt⟩, rfl⟩))
    linarith
  obtain ⟨j, hj, hlj, hrj⟩ := hstep
  have hjk : k ≠ j := by rintro rfl; linarith
  have hlj' : l j < r k := lt_of_le_of_ne hlj (hno j hj)
  set M := max (l k) (l j)
  have hM : M < r k := max_lt (h.lt k hk) hlj'
  have hx : r k ∈ Icc (l k) (r k) ∩ Icc (l j) (r j) :=
    ⟨⟨(h.lt k hk).le, le_rfl⟩, ⟨hlj, hrj.le⟩⟩
  have hy : (M + r k) / 2 ∈ Icc (l k) (r k) ∩ Icc (l j) (r j) := by
    refine ⟨⟨?_, by linarith⟩, ⟨?_, by linarith⟩⟩
    · have := le_max_left (l k) (l j); linarith
    · have := le_max_right (l k) (l j); linarith
  have := h.disj k hk j hj hjk hx hy
  linarith
theorem IntervalChain.right_eq_one_unique (h : IntervalChain s l r) {k j : ι} (hk : k ∈ s)
    (hj : j ∈ s) (hrk : r k = 1) (hrj : r j = 1) : k = j := by
  by_contra hkj
  set M := max (l k) (l j)
  have hM : M < 1 := max_lt (hrk ▸ h.lt k hk) (hrj ▸ h.lt j hj)
  have hx : (1 : ℝ) ∈ Icc (l k) (r k) ∩ Icc (l j) (r j) :=
    ⟨⟨by rw [← hrk]; exact (h.lt k hk).le, hrk.ge⟩, ⟨by rw [← hrj]; exact (h.lt j hj).le, hrj.ge⟩⟩
  have hy : (M + 1) / 2 ∈ Icc (l k) (r k) ∩ Icc (l j) (r j) := by
    refine ⟨⟨?_, by linarith⟩, ⟨?_, by linarith⟩⟩
    · have := le_max_left (l k) (l j); linarith
    · have := le_max_right (l k) (l j); linarith
  have := h.disj k hk j hj hkj hx hy
  linarith
theorem IntervalChain.left_eq_zero_unique (h : IntervalChain s l r) {k j : ι} (hk : k ∈ s)
    (hj : j ∈ s) (hlk : l k = 0) (hlj : l j = 0) : k = j := by
  by_contra hkj
  set m := min (r k) (r j)
  have hm : 0 < m := lt_min (hlk ▸ h.lt k hk) (hlj ▸ h.lt j hj)
  have hx : (0 : ℝ) ∈ Icc (l k) (r k) ∩ Icc (l j) (r j) :=
    ⟨⟨hlk.le, by rw [← hlk]; exact (h.lt k hk).le⟩, ⟨hlj.le, by rw [← hlj]; exact (h.lt j hj).le⟩⟩
  have hy : m / 2 ∈ Icc (l k) (r k) ∩ Icc (l j) (r j) := by
    refine ⟨⟨by linarith, ?_⟩, ⟨by linarith, ?_⟩⟩
    · have := min_le_left (r k) (r j); linarith
    · have := min_le_right (r k) (r j); linarith
  have := h.disj k hk j hj hkj hx hy
  linarith
theorem IntervalChain.card_interior_endpoints [DecidableEq ℝ] (h : IntervalChain s l r) :
    ((s.image l ∪ s.image r).filter fun x => x ≠ 0 ∧ x ≠ 1).card + 1 ≤ s.card := by
  classical
  obtain ⟨k0, hk0, hl0, -⟩ := h.cover 0 le_rfl zero_le_one
  have hl0' : l k0 = 0 := le_antisymm hl0 (h.sub k0 hk0).1
  have h0 : (0 : ℝ) ∈ s.image l := Finset.mem_image.mpr ⟨k0, hk0, hl0'⟩
  have hsub : ((s.image l ∪ s.image r).filter fun x => x ≠ 0 ∧ x ≠ 1) ⊆ (s.image l).erase 0 := by
    intro x hx
    obtain ⟨hx, hx0, hx1⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_erase.mpr ⟨hx0, ?_⟩
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hx
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, hjk⟩ := h.exists_left_eq_right hk hx1
      exact Finset.mem_image.mpr ⟨j, hj, hjk⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem h0] at h1
  have h2 : (s.image l).card ≤ s.card := Finset.card_image_le
  have h3 : 0 < (s.image l).card := Finset.card_pos.mpr ⟨0, h0⟩
  omega
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry MeasureTheory Set
theorem eq_lineMap_of_level {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) {c : ℝ} {P Q y : Plane}
    (hPQ : P ≠ Q) (hP : f P = c) (hQ : f Q = c) (hy : f y = c) :
    ∃ t : ℝ, y = AffineMap.lineMap P Q t := by
  have hn := rotVec_ne_zero hf
  have hu : cross (rotVec f) (Q - P) = 0 := by rw [← rotVec_spec, map_sub, hP, hQ, sub_self]
  have hv : cross (rotVec f) (y - P) = 0 := by rw [← rotVec_spec, map_sub, hP, hy, sub_self]
  have hcr := cross_eq_zero_of_common_ker hn hu hv
  obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero (sub_ne_zero.mpr hPQ.symm) hcr
  refine ⟨τ, ?_⟩
  rw [AffineMap.lineMap_apply_module', ← hτ]
  abel
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
open Classical in
noncomputable def lineParam (Q W y : Plane) : ℝ :=
  if h : ∃ t : ℝ, y = AffineMap.lineMap Q W t then h.choose else 0
theorem lineMap_lineParam {Q W y : Plane} (h : ∃ t : ℝ, y = AffineMap.lineMap Q W t) :
    AffineMap.lineMap Q W (lineParam Q W y) = y := by
  classical
  rw [lineParam, dif_pos h]
  exact h.choose_spec.symm
theorem lineParam_lineMap {Q W : Plane} (hQW : Q ≠ W) (t : ℝ) :
    lineParam Q W (AffineMap.lineMap Q W t) = t :=
  AffineMap.lineMap_injective ℝ hQW (lineMap_lineParam ⟨t, rfl⟩)
noncomputable def edgeLo (Q W : Plane) (T : Tri) (k : Fin 3) : ℝ :=
  min (lineParam Q W (T.pts k)) (lineParam Q W (T.pts (k + 1)))
noncomputable def edgeHi (Q W : Plane) (T : Tri) (k : Fin 3) : ℝ :=
  max (lineParam Q W (T.pts k)) (lineParam Q W (T.pts (k + 1)))
section Line
variable {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} {Q W : Plane}
theorem eq_lineMap_lineParam (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    {y : Plane} (hy : g y = c) : AffineMap.lineMap Q W (lineParam Q W y) = y :=
  lineMap_lineParam (eq_lineMap_of_level hg hQW hQ hW hy)
theorem level_lineMap (hQ : g Q = c) (hW : g W = c) (t : ℝ) :
    g (AffineMap.lineMap Q W t) = c := by
  rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul, hQ, hW, smul_eq_mul,
    smul_eq_mul]
  ring
theorem edge_eq_image (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c) (T : Tri)
    (k : Fin 3) (h1 : g (T.pts k) = c) (h2 : g (T.pts (k + 1)) = c) :
    T.edge k = AffineMap.lineMap Q W '' Icc (edgeLo Q W T k) (edgeHi Q W T k) := by
  rw [edgeLo, edgeHi, ← segment_eq_Icc', image_segment, eq_lineMap_lineParam hg hQW hQ hW h1,
    eq_lineMap_lineParam hg hQW hQ hW h2]
  rfl
theorem lineMap_mem_edge_iff (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    (T : Tri) (k : Fin 3) (h1 : g (T.pts k) = c) (h2 : g (T.pts (k + 1)) = c) (t : ℝ) :
    AffineMap.lineMap Q W t ∈ T.edge k ↔ t ∈ Icc (edgeLo Q W T k) (edgeHi Q W T k) := by
  rw [edge_eq_image hg hQW hQ hW T k h1 h2]
  exact (AffineMap.lineMap_injective ℝ hQW).mem_set_image
theorem edgeLo_lt_edgeHi (T : Tri) (k : Fin 3)
    (h1 : ∃ t : ℝ, T.pts k = AffineMap.lineMap Q W t)
    (h2 : ∃ t : ℝ, T.pts (k + 1) = AffineMap.lineMap Q W t) :
    edgeLo Q W T k < edgeHi Q W T k := by
  rw [edgeLo, edgeHi]
  have hne : lineParam Q W (T.pts k) ≠ lineParam Q W (T.pts (k + 1)) := by
    intro h
    have hk : T.pts k = T.pts (k + 1) := by
      rw [← lineMap_lineParam h1, ← lineMap_lineParam h2, h]
    have := T.indep.injective hk
    have hne : ∀ m : Fin 3, m ≠ m + 1 := by decide
    exact hne k this
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]; exact h
  · rw [min_eq_right h.le, max_eq_left h.le]; exact h
theorem lineMap_mem_openSegment_iff (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    (T : Tri) (k : Fin 3) (h1 : g (T.pts k) = c) (h2 : g (T.pts (k + 1)) = c) (t : ℝ) :
    AffineMap.lineMap Q W t ∈ openSegment ℝ (T.pts k) (T.pts (k + 1)) ↔
      t ∈ Ioo (edgeLo Q W T k) (edgeHi Q W T k) := by
  have hlt := edgeLo_lt_edgeHi T k (eq_lineMap_of_level hg hQW hQ hW h1)
    (eq_lineMap_of_level hg hQW hQ hW h2)
  have hab : lineParam Q W (T.pts k) ≠ lineParam Q W (T.pts (k + 1)) := by
    intro h
    rw [edgeLo, edgeHi, h, min_self, max_self] at hlt
    exact lt_irrefl _ hlt
  have e1 := (eq_lineMap_lineParam hg hQW hQ hW h1).symm
  have e2 := (eq_lineMap_lineParam hg hQW hQ hW h2).symm
  rw [e1, e2, ← image_openSegment, openSegment_eq_Ioo' hab,
    (AffineMap.lineMap_injective ℝ hQW).mem_set_image]
  rfl
end Line
section Chain
variable {N : ℕ} (D : Dissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} {Q W : Plane}
theorem lineChain_ends {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    g ((D.tile e.1).pts e.2) = c ∧ g ((D.tile e.1).pts (e.2 + 1)) = c :=
  ⟨(Dissection.mem_lineChain.mp he).1, (Dissection.mem_lineChain.mp he).2.1⟩
theorem lineChain_le {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    ∀ y ∈ (D.tile e.1).carrier, g y ≤ c :=
  (D.tile e.1).carrier_subset_halfplane g c (Dissection.mem_lineChain.mp he).2.2
theorem chain_mem_edge_iff (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) (t : ℝ) :
    AffineMap.lineMap Q W t ∈ (D.tile e.1).edge e.2 ↔
      t ∈ Icc (edgeLo Q W (D.tile e.1) e.2) (edgeHi Q W (D.tile e.1) e.2) :=
  lineMap_mem_edge_iff hg hQW hQ hW _ _ (lineChain_ends D he).1 (lineChain_ends D he).2 t
theorem chain_lo_lt_hi (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    edgeLo Q W (D.tile e.1) e.2 < edgeHi Q W (D.tile e.1) e.2 :=
  edgeLo_lt_edgeHi _ _ (eq_lineMap_of_level hg hQW hQ hW (lineChain_ends D he).1)
    (eq_lineMap_of_level hg hQW hQ hW (lineChain_ends D he).2)
theorem lineChain_eq_of_two (hg : g ≠ 0) {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain g c)
    (he' : e' ∈ D.lineChain g c) {y z : Plane} (hyz : y ≠ z)
    (hy : y ∈ (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2)
    (hz : z ∈ (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2) : e = e' := by
  by_contra hne
  exact hyz (D.sameside_edges_subsingleton g c hg hne (lineChain_le D he) (lineChain_le D he')
    (D.lineChain_edge_subset he) (D.lineChain_edge_subset he') hy hz)
theorem lineChain_eq_of_overlap (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain g c) (he' : e' ∈ D.lineChain g c)
    (h : max (edgeLo Q W (D.tile e.1) e.2) (edgeLo Q W (D.tile e'.1) e'.2)
      < min (edgeHi Q W (D.tile e.1) e.2) (edgeHi Q W (D.tile e'.1) e'.2)) : e = e' := by
  set a := max (edgeLo Q W (D.tile e.1) e.2) (edgeLo Q W (D.tile e'.1) e'.2)
  set b := min (edgeHi Q W (D.tile e.1) e.2) (edgeHi Q W (D.tile e'.1) e'.2)
  have hmem : ∀ t, a ≤ t → t ≤ b → AffineMap.lineMap Q W t ∈
      (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2 := by
    intro t h1 h2
    refine ⟨(chain_mem_edge_iff D hg hQW hQ hW he t).mpr ⟨?_, ?_⟩,
      (chain_mem_edge_iff D hg hQW hQ hW he' t).mpr ⟨?_, ?_⟩⟩
    · exact le_trans (le_max_left _ _) h1
    · exact le_trans h2 (min_le_left _ _)
    · exact le_trans (le_max_right _ _) h1
    · exact le_trans h2 (min_le_right _ _)
  refine lineChain_eq_of_two D hg he he' ?_ (hmem a le_rfl h.le) (hmem b h.le le_rfl)
  intro hab
  exact h.ne (AffineMap.lineMap_injective ℝ hQW hab)
theorem vertex_params_finite (hQW : Q ≠ W) :
    {t : ℝ | AffineMap.lineMap Q W t ∈ D.vertexSet}.Finite :=
  D.vertexSet_finite.preimage (AffineMap.lineMap_injective ℝ hQW).injOn
theorem wall_cover_param (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c) {a b : ℝ}
    (hab : a < b)
    (hint : openSegment ℝ (AffineMap.lineMap Q W a) (AffineMap.lineMap Q W b)
      ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ (AffineMap.lineMap Q W a) (AffineMap.lineMap Q W b),
      ∀ i, y ∉ interior (D.tile i).carrier)
    {t : ℝ} (ht : t ∈ Ioo a b) (hv : AffineMap.lineMap Q W t ∉ D.vertexSet) :
    ∃ e ∈ D.lineChain g c, t ∈ Icc (edgeLo Q W (D.tile e.1) e.2) (edgeHi Q W (D.tile e.1) e.2) := by
  have hne : AffineMap.lineMap Q W a ≠ (AffineMap.lineMap Q W b : Plane) :=
    fun h => hab.ne (AffineMap.lineMap_injective ℝ hQW h)
  have hS : segment ℝ (AffineMap.lineMap Q W a) (AffineMap.lineMap Q W b) ⊆ {y | g y = c} := by
    rw [← image_segment]
    rintro _ ⟨s, -, rfl⟩
    exact level_lineMap hQ hW s
  have htmem : AffineMap.lineMap Q W t ∈
      openSegment ℝ (AffineMap.lineMap Q W a) (AffineMap.lineMap Q W b) := by
    rw [← image_openSegment, openSegment_eq_Ioo hab]
    exact ⟨t, ht, rfl⟩
  obtain ⟨e, he, hte⟩ := D.wall_cover g c hg hne hS hint hwall htmem hv
  exact ⟨e, he, (chain_mem_edge_iff D hg hQW hQ hW he t).mp hte⟩
end Chain
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem localAngle_mem {N : ℕ} (D : CongruentDissection N) (v : Plane) (i : Fin N) :
    (D.tile i).localAngle v = cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) ∨
    (D.tile i).localAngle v = cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) ∨
    (D.tile i).localAngle v = cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) ∨
    (D.tile i).localAngle v = Real.pi ∨ (D.tile i).localAngle v = 2 * Real.pi ∨
    (D.tile i).localAngle v = 0 := by
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with ⟨j, -, hval⟩ | h | h | h
  · obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
    rw [hval, hk]
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
theorem sum_eq_counts {ι : Type*} [Fintype ι] [DecidableEq ℝ] (f : ι → ℝ) (v : Fin 5 → ℝ)
    (hv0 : ∀ j, v j ≠ 0) (hinj : Function.Injective v)
    (hf : ∀ i, (∃ j, f i = v j) ∨ f i = 0) :
    ∑ i, f i = ∑ j, ((Finset.univ.filter fun i => f i = v j).card : ℝ) * v j := by
  have hpt : ∀ i, f i = ∑ j, if f i = v j then v j else 0 := by
    intro i
    rcases hf i with ⟨j, hj⟩ | h0
    · rw [Finset.sum_eq_single j]
      · simp [hj]
      · intro k _ hkj
        rw [if_neg]
        rw [hj]; exact fun h => hkj (hinj h).symm
      · simp
    · rw [h0, Finset.sum_eq_zero]
      intro k _
      rw [if_neg (fun h => hv0 k h.symm)]
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
theorem twobeta_arith {α : ℝ} (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (x y z u w : ℕ) (s t : ℤ) (hst : (t = 1 ∧ s ≤ 0) ∨ (t = 0 ∧ s = 1))
    (h : (x : ℝ) * α + y * (Real.pi - 3 * α) + z * (2 * α) + u * Real.pi + w * (2 * Real.pi)
      = s * α + t * Real.pi) :
    y ≤ 1 ∧ z ≤ 1 := by
  have key : (((x : ℤ) - 3 * y + 2 * z - s : ℤ) : ℝ) * α
      + (((y : ℤ) + u + 2 * w - t : ℤ) : ℝ) * Real.pi = 0 := by
    push_cast; linear_combination h
  obtain ⟨h1, h2⟩ := angle_indep hirr _ _ key
  omega
theorem twobeta {N : ℕ} (D : CongruentDissection N)
    (hγ : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) =
      2 * ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hirr : ¬ ∃ r : ℚ, ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    {P : Plane} (hP : P ∈ frontier D.target.carrier) :
    (Finset.univ.filter fun i =>
        (D.tile i).localAngle P = ∠ (D.model.pts 2) (D.model.pts 1) (D.model.pts 0)).card ≤ 1 ∧
    (Finset.univ.filter fun i =>
        (D.tile i).localAngle P = ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1)).card ≤ 1 := by
  classical
  set α := ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) with hαdef
  set β := ∠ (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) with hβdef
  set γ := ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) with hγdef
  have hsum3 : α + β + γ = Real.pi := cornerAngle_sum D.model
  have hβ : β = Real.pi - 3 * α := by linarith
  have hne : ∀ p q : ℤ, p ≠ 0 → (p : ℝ) * α ≠ q * Real.pi := by
    intro p q hp h
    exact hp (angle_indep hirr p (-q) (by push_cast; linarith)).1
  have hpi := Real.pi_pos
  let v : Fin 5 → ℝ := ![α, β, γ, Real.pi, 2 * Real.pi]
  have hv0 : ∀ j, v j ≠ 0 := by
    intro j; fin_cases j
    · exact fun h => hne 1 0 one_ne_zero (by simp [v] at h ⊢; linarith)
    · exact fun h => hne 3 1 (by norm_num) (by simp [v] at h; push_cast; linarith)
    · exact fun h => hne 1 0 one_ne_zero (by simp [v] at h; push_cast; linarith)
    · simp [v, hpi.ne']
    · simp [v, hpi.ne']
  have hinj : Function.Injective v := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;> simp [v] at hjk ⊢
    all_goals first
      | exact hne 4 1 (by norm_num) (by push_cast; linarith)
      | exact hne 1 0 one_ne_zero (by push_cast; linarith)
      | exact hne 1 1 one_ne_zero (by push_cast; linarith)
      | exact hne 1 2 one_ne_zero (by push_cast; linarith)
      | exact hne 5 1 (by norm_num) (by push_cast; linarith)
      | exact hne 3 (-1) (by norm_num) (by push_cast; linarith)
      | exact hne 2 1 (by norm_num) (by push_cast; linarith)
  have hf : ∀ i, (∃ j, (D.tile i).localAngle P = v j) ∨ (D.tile i).localAngle P = 0 := by
    intro i
    rcases localAngle_mem D P i with h | h | h | h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inl ⟨2, h⟩
    · exact Or.inl ⟨3, h⟩
    · exact Or.inl ⟨4, h⟩
    · exact Or.inr h
  have hcount := sum_eq_counts (fun i => (D.tile i).localAngle P) v hv0 hinj hf
  rw [D.toDissection.sum_localAngle_eq P, Fin.sum_univ_five] at hcount
  set c := fun j => (Finset.univ.filter fun i => (D.tile i).localAngle P = v j).card with hc
  have htarget : ∃ s t : ℤ, ((t = 1 ∧ s ≤ 0) ∨ (t = 0 ∧ s = 1)) ∧
      D.target.localAngle P = s * α + t * Real.pi := by
    by_cases hv : P ∈ Set.range D.target.pts
    · obtain ⟨k, rfl⟩ := hv
      rw [Tri.localAngle_vertex]
      have hT := cornerAngle_sum D.target
      have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = α := hA
      have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = α := by
        rw [cornerAngle, angle_comm]; exact hC
      fin_cases k
      · refine ⟨1, 0, Or.inr ⟨rfl, rfl⟩, ?_⟩
        show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = _
        push_cast; linarith
      · refine ⟨-2, 1, Or.inl ⟨rfl, by norm_num⟩, ?_⟩
        show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
        push_cast; linarith
      · refine ⟨1, 0, Or.inr ⟨rfl, rfl⟩, ?_⟩
        show cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = _
        push_cast; linarith
    · exact ⟨0, 1, Or.inl ⟨rfl, le_rfl⟩, by
        rw [D.target.localAngle_frontier hP hv]; push_cast; ring⟩
  obtain ⟨s, t, hst, ht⟩ := htarget
  rw [ht] at hcount
  have hcount' : (s : ℝ) * α + t * Real.pi = (c 0 : ℝ) * α + (c 1 : ℝ) * β + (c 2 : ℝ) * γ
      + (c 3 : ℝ) * Real.pi + (c 4 : ℝ) * (2 * Real.pi) := hcount
  exact twobeta_arith hirr (c 0) (c 1) (c 2) (c 3) (c 4) s t hst (by
    rw [← hβ, ← (show γ = 2 * α from hγ)]
    linarith)
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
section Defs
variable {N : ℕ} (D : CongruentDissection N)
noncomputable def tileα : ℝ := ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)
noncomputable def tileβ : ℝ := ∠ (D.model.pts 2) (D.model.pts 1) (D.model.pts 0)
noncomputable def tileγ : ℝ := ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1)
noncomputable def angleCount (P : Plane) (θ : ℝ) : ℕ :=
  (Finset.univ.filter fun i => (D.tile i).localAngle P = θ).card
open Classical in
noncomputable def tilingVertices : Finset Plane :=
  Finset.univ.image fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2
noncomputable def vertexType (P : Plane) : ℕ × ℕ × ℕ :=
  (angleCount D P (tileα D), angleCount D P (tileβ D), angleCount D P (tileγ D))
open Classical in
noncomputable def typeCount (t : ℕ × ℕ × ℕ) : ℕ :=
  ((tilingVertices D).filter fun P => P ∉ Set.range D.target.pts ∧ vertexType D P = t).card
end Defs
theorem card_eq_counts {ι : Type*} [Fintype ι] [DecidableEq ℝ] (f : ι → ℝ) (v : Fin 5 → ℝ)
    (hv0 : ∀ j, v j ≠ 0) (hinj : Function.Injective v)
    (hf : ∀ i, (∃ j, f i = v j) ∨ f i = 0) :
    Fintype.card ι = ∑ j, (Finset.univ.filter fun i => f i = v j).card
      + (Finset.univ.filter fun i => f i = 0).card := by
  have hpt : ∀ i, (1 : ℕ) = (∑ j, if f i = v j then 1 else 0) + if f i = 0 then 1 else 0 := by
    intro i
    rcases hf i with ⟨j, hj⟩ | h0
    · rw [Finset.sum_eq_single j, if_pos hj, if_neg (by rw [hj]; exact hv0 j)]
      · intro k _ hkj; rw [if_neg]; rw [hj]; exact fun h => hkj (hinj h).symm
      · simp
    · rw [Finset.sum_eq_zero, if_pos h0]
      intro k _; rw [if_neg (fun h => hv0 k (h.symm.trans h0))]
  rw [← Finset.card_univ, Finset.card_eq_sum_ones, Finset.sum_congr rfl (fun i _ => hpt i),
    Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_filter]
  · rw [Finset.card_filter]
theorem angle_values {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) :
    tileβ D = Real.pi - 3 * tileα D ∧
    (∀ j, ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j ≠ 0) ∧
    Function.Injective ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] := by
  set α := tileα D
  set β := tileβ D
  set γ := tileγ D
  have hsum3 : α + β + γ = Real.pi := cornerAngle_sum D.model
  have hβ : β = Real.pi - 3 * α := by linarith
  have hne : ∀ p q : ℤ, p ≠ 0 → (p : ℝ) * α ≠ q * Real.pi := by
    intro p q hp h
    exact hp (angle_indep hirr p (-q) (by push_cast; linarith)).1
  have hpi := Real.pi_pos
  refine ⟨hβ, ?_, ?_⟩
  · intro j; fin_cases j
    · exact fun h => hne 1 0 one_ne_zero (by simp at h ⊢; linarith)
    · exact fun h => hne 3 1 (by norm_num) (by simp at h; push_cast; linarith)
    · exact fun h => hne 1 0 one_ne_zero (by simp at h; push_cast; linarith)
    · simp [hpi.ne']
    · simp [hpi.ne']
  · intro j k hjk
    fin_cases j <;> fin_cases k <;> simp at hjk ⊢
    all_goals first
      | exact hne 4 1 (by norm_num) (by push_cast; linarith)
      | exact hne 1 0 one_ne_zero (by push_cast; linarith)
      | exact hne 1 1 one_ne_zero (by push_cast; linarith)
      | exact hne 1 2 one_ne_zero (by push_cast; linarith)
      | exact hne 5 1 (by norm_num) (by push_cast; linarith)
      | exact hne 3 (-1) (by norm_num) (by push_cast; linarith)
      | exact hne 2 1 (by norm_num) (by push_cast; linarith)
theorem counts_arith {α β γ : ℝ} (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hβ : β = Real.pi - 3 * α) (hγ : γ = 2 * α) (n₀ n₁ n₂ n₃ n₄ : ℕ) (s t : ℤ)
    (h : (n₀ : ℝ) * α + n₁ * β + n₂ * γ + n₃ * Real.pi + n₄ * (2 * Real.pi) = s * α + t * Real.pi) :
    (n₀ : ℤ) - 3 * n₁ + 2 * n₂ = s ∧ (n₁ : ℤ) + n₃ + 2 * n₄ = t := by
  subst hβ hγ
  have key : (((n₀ : ℤ) - 3 * n₁ + 2 * n₂ - s : ℤ) : ℝ) * α
      + (((n₁ : ℤ) + n₃ + 2 * n₄ - t : ℤ) : ℝ) * Real.pi = 0 := by
    push_cast; linear_combination h
  obtain ⟨h1, h2⟩ := angle_indep hirr _ _ key
  omega
theorem vertex_relations {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) (P : Plane) (s t : ℤ)
    (hP : D.target.localAngle P = s * tileα D + t * Real.pi) :
    ((angleCount D P (tileα D) : ℤ) - 3 * angleCount D P (tileβ D)
        + 2 * angleCount D P (tileγ D) = s) ∧
    ((angleCount D P (tileβ D) : ℤ) + angleCount D P Real.pi
        + 2 * angleCount D P (2 * Real.pi) = t) := by
  obtain ⟨hβ, hv0, hinj⟩ := angle_values D hγ hirr
  have hf : ∀ i, (∃ j, (D.tile i).localAngle P =
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j) ∨ (D.tile i).localAngle P = 0 := by
    intro i
    rcases localAngle_mem D P i with h | h | h | h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inl ⟨2, h⟩
    · exact Or.inl ⟨3, h⟩
    · exact Or.inl ⟨4, h⟩
    · exact Or.inr h
  have hcount := sum_eq_counts (fun i => (D.tile i).localAngle P) _ hv0 hinj hf
  rw [D.toDissection.sum_localAngle_eq P, Fin.sum_univ_five, hP] at hcount
  have hcount' : (angleCount D P (tileα D) : ℝ) * tileα D
      + (angleCount D P (tileβ D) : ℝ) * tileβ D + (angleCount D P (tileγ D) : ℝ) * tileγ D
      + (angleCount D P Real.pi : ℝ) * Real.pi
      + (angleCount D P (2 * Real.pi) : ℝ) * (2 * Real.pi) = s * tileα D + t * Real.pi :=
    hcount.symm
  exact counts_arith hirr hβ hγ _ _ _ _ _ s t hcount'
theorem target_corner_angle {N : ℕ} (D : CongruentDissection N)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D) (k : Fin 3) :
    ∃ s t : ℤ, ((s = 1 ∧ t = 0) ∨ (s = -2 ∧ t = 1)) ∧
      D.target.localAngle (D.target.pts k) = s * tileα D + t * Real.pi := by
  rw [Tri.localAngle_vertex]
  have hT := cornerAngle_sum D.target
  have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
  have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileα D := by
    rw [cornerAngle, angle_comm]; exact hC
  fin_cases k
  · refine ⟨1, 0, Or.inl ⟨rfl, rfl⟩, ?_⟩
    show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = _
    push_cast; linarith
  · refine ⟨-2, 1, Or.inr ⟨rfl, rfl⟩, ?_⟩
    show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
    push_cast; linarith
  · refine ⟨1, 0, Or.inl ⟨rfl, rfl⟩, ?_⟩
    show cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = _
    push_cast; linarith
def AnglesSep {N : ℕ} (D : CongruentDissection N) : Prop :=
  (∀ j, ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j ≠ 0) ∧
    Function.Injective ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi]
theorem anglesSep_of_two_alpha {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) : AnglesSep D :=
  ⟨(angle_values D hγ hirr).2.1, (angle_values D hγ hirr).2.2⟩
theorem corner_perm {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3,
      cornerAngle (U.pts (σ k + 1)) (U.pts (σ k)) (U.pts (σ k + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨σ, fun k => ?_⟩
  have hmap : cornerAngle (U.pts (σ (k + 1))) (U.pts (σ k)) (U.pts (σ (k + 2)))
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
    rw [← hf (k + 1), ← hf k, ← hf (k + 2)]
    rw [Erdos634.Geometry.cornerAngle, Erdos634.Geometry.cornerAngle]
    rw [show (f : Plane → Plane) = f.toRealAffineIsometryEquiv from
      (IsometryEquiv.coeFn_toRealAffineIsometryEquiv f).symm]
    exact f.toRealAffineIsometryEquiv.toAffineIsometry.angle_map _ _ _
  have hidx : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z →
      (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by decide
  have hne : ∀ x : Fin 3, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x + 1 ≠ x + 2 := by decide
  obtain ⟨h1, h2, h12⟩ := hne k
  rcases hidx (σ k) (σ (k + 1)) (σ (k + 2))
      (fun he => h1 (σ.injective he)) (fun he => h2 (σ.injective he))
      (fun he => h12 (σ.injective he)) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [← ha, ← hb]; exact hmap
  · rw [← ha, ← hb]
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]
    exact hmap
theorem tile_angle_count_sep {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D)
    (i : Fin N) :
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileα D).card = 1 ∧
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileβ D).card = 1 ∧
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileγ D).card = 1 := by
  classical
  obtain ⟨σ, hperm⟩ := corner_perm (D.tiles_congruent i).symm
  set M := D.model
  have hm : ∀ k : Fin 3, cornerAngle (M.pts (k + 1)) (M.pts k) (M.pts (k + 2)) =
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] (k.castLE (by norm_num)) := by
    intro k; fin_cases k <;> rfl
  have hdist : ∀ k l : Fin 3, cornerAngle (M.pts (k + 1)) (M.pts k) (M.pts (k + 2))
      = cornerAngle (M.pts (l + 1)) (M.pts l) (M.pts (l + 2)) → k = l := by
    intro k l h
    rw [hm, hm] at h
    exact Fin.castLE_injective _ (hsep.2 h)
  have hcount : ∀ k : Fin 3, (Finset.univ.filter fun j : Fin 3 =>
      cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        = cornerAngle (M.pts (k + 1)) (M.pts k) (M.pts (k + 2))).card = 1 := by
    intro k
    refine Finset.card_eq_one.mpr ⟨σ k, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      have h' := hperm (σ.symm j)
      rw [Equiv.apply_symm_apply] at h'
      have := hdist _ _ (h'.symm.trans hj)
      rw [← this, Equiv.apply_symm_apply]
    · intro hj; subst hj; exact hperm k
  exact ⟨hcount 0, hcount 1, hcount 2⟩
theorem tile_angle_count {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) (i : Fin N) :
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileα D).card = 1 ∧
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileβ D).card = 1 ∧
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileγ D).card = 1 := by
  obtain ⟨hβ, hv0, hinj⟩ := angle_values D hγ hirr
  set g := fun k : Fin 3 =>
    cornerAngle ((D.tile i).pts (k + 1)) ((D.tile i).pts k) ((D.tile i).pts (k + 2)) with hg
  have hgv : ∀ k, ∃ j, g k = ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j := by
    intro k
    obtain ⟨k', hk'⟩ := congruent_corner_angles (D.tiles_congruent i).symm k
    refine ⟨k'.castLE (by norm_num), ?_⟩
    rw [hg]; simp only; rw [hk']
    fin_cases k' <;> rfl
  have hf : ∀ k, (∃ j, g k = ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j) ∨ g k = 0 :=
    fun k => Or.inl (hgv k)
  have hsum := sum_eq_counts g _ hv0 hinj hf
  have hcard := card_eq_counts g _ hv0 hinj hf
  have h0 : (Finset.univ.filter fun k => g k = 0).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _ hk
    obtain ⟨j, hj⟩ := hgv k
    exact hv0 j (hj ▸ hk)
  have hπ : ∑ k, g k = Real.pi := by
    rw [Fin.sum_univ_three]; exact cornerAngle_sum (D.tile i)
  rw [hπ, Fin.sum_univ_five] at hsum
  rw [Fin.sum_univ_five, h0, Fintype.card_fin] at hcard
  have hsum' : ((Finset.univ.filter fun k => g k = tileα D).card : ℝ) * tileα D
      + ((Finset.univ.filter fun k => g k = tileβ D).card : ℝ) * tileβ D
      + ((Finset.univ.filter fun k => g k = tileγ D).card : ℝ) * tileγ D
      + ((Finset.univ.filter fun k => g k = Real.pi).card : ℝ) * Real.pi
      + ((Finset.univ.filter fun k => g k = 2 * Real.pi).card : ℝ) * (2 * Real.pi)
      = Real.pi := hsum.symm
  have hcard' : 3 = (Finset.univ.filter fun k => g k = tileα D).card
      + (Finset.univ.filter fun k => g k = tileβ D).card
      + (Finset.univ.filter fun k => g k = tileγ D).card
      + (Finset.univ.filter fun k => g k = Real.pi).card
      + (Finset.univ.filter fun k => g k = 2 * Real.pi).card + 0 := hcard
  show (Finset.univ.filter fun k => g k = tileα D).card = 1 ∧
    (Finset.univ.filter fun k => g k = tileβ D).card = 1 ∧
    (Finset.univ.filter fun k => g k = tileγ D).card = 1
  clear hsum hcard
  generalize (Finset.univ.filter fun k => g k = tileα D).card = A at hsum' hcard' ⊢
  generalize (Finset.univ.filter fun k => g k = tileβ D).card = B at hsum' hcard' ⊢
  generalize (Finset.univ.filter fun k => g k = tileγ D).card = C at hsum' hcard' ⊢
  generalize (Finset.univ.filter fun k => g k = Real.pi).card = E at hsum' hcard'
  generalize (Finset.univ.filter fun k => g k = 2 * Real.pi).card = F at hsum' hcard'
  have hr := counts_arith hirr hβ hγ A B C E F 0 1 (by rw [hsum']; norm_num)
  obtain ⟨hr1, hr2⟩ := hr
  have hB : B ≤ 1 := by omega
  interval_cases B <;> omega
theorem filter_localAngle_eq [DecidableEq Plane] (T : Tri) (W : Finset Plane)
    (hW : ∀ k, T.pts k ∈ W) (θ : ℝ) (h0 : θ ≠ 0) (hπ : θ ≠ Real.pi) (h2π : θ ≠ 2 * Real.pi) :
    W.filter (fun v => T.localAngle v = θ) =
      (Finset.univ.filter fun k : Fin 3 =>
        cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) = θ).image T.pts := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩
    rcases Erdos634.PinPlumbing.localAngle_cases T v with ⟨j, hv, hval⟩ | h' | h' | h'
    · exact ⟨j, hval ▸ h, hv.symm⟩
    · exact absurd (h ▸ h') h2π
    · exact absurd (h ▸ h') hπ
    · exact absurd (h ▸ h') h0
  · rintro ⟨k, hk, rfl⟩
    exact ⟨hW k, by rw [Tri.localAngle_vertex]; exact hk⟩
theorem sum_angleCount [DecidableEq Plane] {N : ℕ} (D : CongruentDissection N)
    (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (W : Finset Plane) (hW : ∀ i k, (D.tile i).pts k ∈ W) (θ : ℝ)
    (hθ : θ = tileα D ∨ θ = tileγ D) :
    ∑ v ∈ W, angleCount D v θ = N := by
  obtain ⟨-, hv0, hinj⟩ := angle_values D hγ hirr
  have hθ0 : θ ≠ 0 ∧ θ ≠ Real.pi ∧ θ ≠ 2 * Real.pi := by
    rcases hθ with rfl | rfl
    · exact ⟨hv0 0, fun h => hinj.ne (show (0 : Fin 5) ≠ 3 by decide) h,
        fun h => hinj.ne (show (0 : Fin 5) ≠ 4 by decide) h⟩
    · exact ⟨hv0 2, fun h => hinj.ne (show (2 : Fin 5) ≠ 3 by decide) h,
        fun h => hinj.ne (show (2 : Fin 5) ≠ 4 by decide) h⟩
  simp only [angleCount, Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ i : Fin N, (∑ v ∈ W, if (D.tile i).localAngle v = θ then 1 else 0) = 1 := by
    intro i
    rw [← Finset.card_filter, filter_localAngle_eq (D.tile i) W (hW i) θ hθ0.1 hθ0.2.1 hθ0.2.2,
      Finset.card_image_of_injective _ (D.tile i).indep.injective]
    rcases hθ with rfl | rfl
    · exact (tile_angle_count D hγ hirr i).1
    · exact (tile_angle_count D hγ hirr i).2.2
  rw [Finset.sum_congr rfl fun i _ => this i]
  simp
theorem starsandcenters {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D) :
    typeCount D (0, 2, 3) = typeCount D (3, 1, 0) + typeCount D (4, 2, 1)
      + 2 * typeCount D (6, 2, 0) + 1 := by
  classical
  set TV := tilingVertices D
  set Cn : Finset Plane := Finset.univ.image D.target.pts
  set W := TV ∪ Cn with hWdef
  have hTV : ∀ i k, (D.tile i).pts k ∈ TV := fun i k =>
    Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, rfl⟩
  have hW : ∀ i k, (D.tile i).pts k ∈ W := fun i k => Finset.mem_union_left _ (hTV i k)
  have hzero : ∑ v ∈ W, ((angleCount D v (tileα D) : ℤ) - angleCount D v (tileγ D)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 := sum_angleCount D hγ hirr W hW (tileα D) (Or.inl rfl)
    have h2 := sum_angleCount D hγ hirr W hW (tileγ D) (Or.inr rfl)
    have e1 : ∑ v ∈ W, (angleCount D v (tileα D) : ℤ) = N := by exact_mod_cast h1
    have e2 : ∑ v ∈ W, (angleCount D v (tileγ D) : ℤ) = N := by exact_mod_cast h2
    rw [e1, e2, sub_self]
  rw [← Finset.sum_filter_add_sum_filter_not W (fun v => v ∈ Set.range D.target.pts)] at hzero
  have hcorners : W.filter (fun v => v ∈ Set.range D.target.pts) = Cn := by
    ext v
    simp only [Finset.mem_filter, hWdef, Finset.mem_union, Cn, Finset.mem_image,
      Finset.mem_univ, true_and, Set.mem_range]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨Or.inr h, h⟩
  have hcornerw : ∀ v ∈ Cn,
      (angleCount D v (tileα D) : ℤ) - angleCount D v (tileγ D) = 1 := by
    intro v hv
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨s, t, hst, hk⟩ := target_corner_angle D hA hC k
    have := vertex_relations D hγ hirr _ s t hk
    omega
  rw [hcorners, Finset.sum_congr rfl hcornerw, Finset.sum_const,
    Finset.card_image_of_injective _ D.target.indep.injective] at hzero
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one] at hzero
  set R := W.filter (fun v => ¬ v ∈ Set.range D.target.pts) with hR
  let wt : Plane → ℤ := fun v =>
    (if vertexType D v = (3, 1, 0) then 1 else 0) + (if vertexType D v = (4, 2, 1) then 1 else 0)
    + (if vertexType D v = (6, 2, 0) then 2 else 0) - (if vertexType D v = (0, 2, 3) then 1 else 0)
  have hrest : ∀ v ∈ R,
      (angleCount D v (tileα D) : ℤ) - angleCount D v (tileγ D) = 3 * wt v := by
    intro v hv
    obtain ⟨hvW, hvc⟩ := Finset.mem_filter.mp hv
    have hvTV : v ∈ TV := by
      rcases Finset.mem_union.mp hvW with h | h
      · exact h
      · exact absurd (by obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h; exact ⟨k, rfl⟩) hvc
    obtain ⟨⟨i, k⟩, -, rfl⟩ := Finset.mem_image.mp hvTV
    have hcar : (D.tile i).pts k ∈ D.target.carrier := by
      rw [← D.covers]
      exact Set.mem_iUnion.mpr ⟨i, subset_convexHull ℝ _ ⟨k, rfl⟩⟩
    have hrel : ∃ t : ℤ, (t = 1 ∨ t = 2) ∧
        D.target.localAngle ((D.tile i).pts k) = (0 : ℤ) * tileα D + t * Real.pi := by
      by_cases hint : (D.tile i).pts k ∈ interior D.target.carrier
      · exact ⟨2, Or.inr rfl, by rw [D.target.localAngle_interior hint]; push_cast; ring⟩
      · have hfr : (D.tile i).pts k ∈ frontier D.target.carrier :=
          ⟨subset_closure hcar, hint⟩
        exact ⟨1, Or.inl rfl, by rw [D.target.localAngle_frontier hfr hvc]; push_cast; ring⟩
    obtain ⟨t, ht, hloc⟩ := hrel
    have hr := vertex_relations D hγ hirr _ 0 t hloc
    simp only [wt, vertexType, Prod.mk.injEq]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl hrest, ← Finset.mul_sum] at hzero
  have hcount : ∀ (t : ℕ × ℕ × ℕ) (c : ℤ),
      ∑ v ∈ R, (if vertexType D v = t then c else 0) = c * typeCount D t := by
    intro t c
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    unfold typeCount
    congr 1
    ext v
    simp only [Finset.mem_filter, hR, hWdef, Finset.mem_union, Cn, Finset.mem_image,
      Finset.mem_univ, true_and, Set.mem_range]
    constructor
    · rintro ⟨⟨h | ⟨k, rfl⟩, hc⟩, ht⟩
      · exact ⟨h, hc, ht⟩
      · exact absurd ⟨k, rfl⟩ hc
    · rintro ⟨h, hc, ht⟩; exact ⟨⟨Or.inl h, hc⟩, ht⟩
  have hwt : ∑ v ∈ R, wt v = typeCount D (3, 1, 0) + typeCount D (4, 2, 1)
      + 2 * typeCount D (6, 2, 0) - typeCount D (0, 2, 3) := by
    simp only [wt, Finset.sum_sub_distrib, Finset.sum_add_distrib, hcount]
    ring
  rw [hwt] at hzero
  omega
end TriangleTiling
end

section
namespace TriangleTiling
open Set
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
theorem segment_chain_endpoints [DecidableEq E] {ι : Type*} (A B : E) (hAB : A ≠ B)
    (s : Finset ι) (u v : ι → E) (huv : ∀ k ∈ s, u k ≠ v k)
    (hcov : (⋃ k ∈ s, segment ℝ (u k) (v k)) = segment ℝ A B)
    (hdisj : ∀ k ∈ s, ∀ j ∈ s, k ≠ j →
      (segment ℝ (u k) (v k) ∩ segment ℝ (u j) (v j)).Subsingleton) :
    ((s.image u ∪ s.image v).filter fun x => x ≠ A ∧ x ≠ B).card + 1 ≤ s.card ∧
    (∀ k ∈ s, ∀ j ∈ s, (u k = B ∨ v k = B) → (u j = B ∨ v j = B) → k = j) ∧
    (∀ k ∈ s, ∀ j ∈ s, (u k = A ∨ v k = A) → (u j = A ∨ v j = A) → k = j) := by
  classical
  set L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap A B with hLdef
  have hL : Function.Injective L := AffineMap.lineMap_injective ℝ hAB
  have hL0 : L 0 = A := AffineMap.lineMap_apply_zero A B
  have hL1 : L 1 = B := AffineMap.lineMap_apply_one A B
  have hseg : segment ℝ A B = L '' Icc 0 1 := by
    rw [segment_eq_image_lineMap]
  have hmem : ∀ k ∈ s, u k ∈ segment ℝ A B ∧ v k ∈ segment ℝ A B := by
    intro k hk
    rw [← hcov]
    exact ⟨mem_biUnion hk (left_mem_segment ℝ _ _), mem_biUnion hk (right_mem_segment ℝ _ _)⟩
  have hpar : ∀ x ∈ segment ℝ A B, ∃ t ∈ Icc (0 : ℝ) 1, L t = x := by
    intro x hx; rw [hseg] at hx; exact hx
  let tu : ι → ℝ := fun k =>
    if h : ∃ t ∈ Icc (0 : ℝ) 1, L t = u k then h.choose else 0
  let tv : ι → ℝ := fun k =>
    if h : ∃ t ∈ Icc (0 : ℝ) 1, L t = v k then h.choose else 0
  have htu : ∀ k ∈ s, tu k ∈ Icc (0 : ℝ) 1 ∧ L (tu k) = u k := by
    intro k hk
    have h := hpar _ (hmem k hk).1
    simp only [tu, dif_pos h]
    exact h.choose_spec
  have htv : ∀ k ∈ s, tv k ∈ Icc (0 : ℝ) 1 ∧ L (tv k) = v k := by
    intro k hk
    have h := hpar _ (hmem k hk).2
    simp only [tv, dif_pos h]
    exact h.choose_spec
  let l : ι → ℝ := fun k => min (tu k) (tv k)
  let r : ι → ℝ := fun k => max (tu k) (tv k)
  have hsegk : ∀ k ∈ s, segment ℝ (u k) (v k) = L '' Icc (l k) (r k) := by
    intro k hk
    rw [← (htu k hk).2, ← (htv k hk).2, ← image_segment, segment_eq_Icc']
  have hchain : IntervalChain s l r := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk
      have hne : tu k ≠ tv k := fun h => huv k hk (by rw [← (htu k hk).2, ← (htv k hk).2, h])
      exact min_lt_max.mpr hne
    · intro k hk
      exact ⟨le_min (htu k hk).1.1 (htv k hk).1.1, max_le (htu k hk).1.2 (htv k hk).1.2⟩
    · intro x hx0 hx1
      have hLx : L x ∈ segment ℝ A B := by rw [hseg]; exact ⟨x, ⟨hx0, hx1⟩, rfl⟩
      rw [← hcov] at hLx
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hLx
      rw [hsegk k hk] at hxk
      obtain ⟨y, hy, hyx⟩ := hxk
      exact ⟨k, hk, (hL hyx) ▸ hy.1, (hL hyx) ▸ hy.2⟩
    · intro k hk j hj hkj x hx y hy
      have h := hdisj k hk j hj hkj
      have hx' : L x ∈ segment ℝ (u k) (v k) ∩ segment ℝ (u j) (v j) := by
        rw [hsegk k hk, hsegk j hj]
        exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
      have hy' : L y ∈ segment ℝ (u k) (v k) ∩ segment ℝ (u j) (v j) := by
        rw [hsegk k hk, hsegk j hj]
        exact ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
      exact hL (h hx' hy')
  have hends : ∀ k ∈ s, ∀ t, (t = tu k ∨ t = tv k) → (t = l k ∨ t = r k) := by
    intro k _ t ht
    rcases le_total (tu k) (tv k) with h | h
    · rcases ht with rfl | rfl
      · exact Or.inl (min_eq_left h).symm
      · exact Or.inr (max_eq_right h).symm
    · rcases ht with rfl | rfl
      · exact Or.inr (max_eq_left h).symm
      · exact Or.inl (min_eq_right h).symm
  refine ⟨?_, ?_, ?_⟩
  · 
    have hsub : ((s.image u ∪ s.image v).filter fun x => x ≠ A ∧ x ≠ B) ⊆
        ((s.image l ∪ s.image r).filter fun x => x ≠ 0 ∧ x ≠ 1).image L := by
      intro x hx
      obtain ⟨hx, hxA, hxB⟩ := Finset.mem_filter.mp hx
      have : ∃ k ∈ s, ∃ t, (t = tu k ∨ t = tv k) ∧ L t = x := by
        rcases Finset.mem_union.mp hx with hx | hx
        · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
          exact ⟨k, hk, tu k, Or.inl rfl, (htu k hk).2⟩
        · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
          exact ⟨k, hk, tv k, Or.inr rfl, (htv k hk).2⟩
      obtain ⟨k, hk, t, ht, rfl⟩ := this
      refine Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩, rfl⟩
      · rcases hends k hk t ht with h | h
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, hk, h.symm⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hk, h.symm⟩)
      · rintro rfl; exact hxA hL0
      · rintro rfl; exact hxB hL1
    have := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := (s.image l ∪ s.image r).filter fun x => x ≠ 0 ∧ x ≠ 1)
      (f := L)
    have h3 := hchain.card_interior_endpoints
    omega
  · intro k hk j hj hkB hjB
    have hr : ∀ i ∈ s, (u i = B ∨ v i = B) → r i = 1 := by
      intro i hi hiB
      have ht1 : tu i = 1 ∨ tv i = 1 := by
        rcases hiB with h | h
        · exact Or.inl (hL ((htu i hi).2.trans (h.trans hL1.symm)))
        · exact Or.inr (hL ((htv i hi).2.trans (h.trans hL1.symm)))
      apply le_antisymm (hchain.sub i hi).2
      rcases ht1 with h | h
      · rw [← h]; exact le_max_left _ _
      · rw [← h]; exact le_max_right _ _
    exact hchain.right_eq_one_unique hk hj (hr k hk hkB) (hr j hj hjB)
  · intro k hk j hj hkA hjA
    have hl : ∀ i ∈ s, (u i = A ∨ v i = A) → l i = 0 := by
      intro i hi hiA
      have ht0 : tu i = 0 ∨ tv i = 0 := by
        rcases hiA with h | h
        · exact Or.inl (hL ((htu i hi).2.trans (h.trans hL0.symm)))
        · exact Or.inr (hL ((htv i hi).2.trans (h.trans hL0.symm)))
      apply le_antisymm _ (hchain.sub i hi).1
      rcases ht0 with h | h
      · rw [← h]; exact min_le_left _ _
      · rw [← h]; exact min_le_right _ _
    exact hchain.left_eq_zero_unique hk hj (hl k hk hkA) (hl j hj hjA)
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem tri_side_subset_frontier (T : Tri) (i : Fin 3) :
    segment ℝ (T.pts i) (T.pts (i + 1)) ⊆ frontier T.carrier := by
  intro x hx
  have hcar : x ∈ T.carrier := T.convex.segment_subset
    (subset_convexHull ℝ _ ⟨i, rfl⟩) (subset_convexHull ℝ _ ⟨i + 1, rfl⟩) hx
  refine ⟨subset_closure hcar, fun hint => ?_⟩
  have hpos := (T.mem_interior_iff_coord_pos x).mp hint (i + 2)
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, -, rfl⟩ := hx
  rw [AffineMap.apply_lineMap] at hpos
  have h1 : T.basis.coord (i + 2) (T.pts i) = 0 := by
    have : T.pts i = T.basis i := rfl
    rw [this, AffineBasis.coord_apply_ne]; fin_cases i <;> decide
  have h2 : T.basis.coord (i + 2) (T.pts (i + 1)) = 0 := by
    have : T.pts (i + 1) = T.basis (i + 1) := rfl
    rw [this, AffineBasis.coord_apply_ne]; fin_cases i <;> decide
  rw [h1, h2, AffineMap.lineMap_same_apply] at hpos
  exact lt_irrefl _ hpos
theorem fin3_ne_add_one : ∀ k : Fin 3, k ≠ k + 1 := by decide
theorem tri_two_edges_on_segment (T : Tri) {A B : Plane} {k k' : Fin 3} (hkk : k ≠ k')
    (hk : T.edge k ⊆ segment ℝ A B) (hk' : T.edge k' ⊆ segment ℝ A B) : False := by
  have hend : ∀ m : Fin 3, T.pts m ∈ T.edge m ∧ T.pts (m + 1) ∈ T.edge m :=
    fun m => ⟨left_mem_segment _ _ _, right_mem_segment _ _ _⟩
  have hall : ∀ j, T.pts j ∈ segment ℝ A B := by
    intro j
    fin_cases k <;> fin_cases k' <;> fin_cases j <;> simp at hkk <;>
      first
      | exact hk (hend _).1 | exact hk (hend _).2
      | exact hk' (hend _).1 | exact hk' (hend _).2
  have hline : ∀ j, T.pts j ∈ line[ℝ, A, B] :=
    fun j => (mem_segment_iff_wbtw.mp (hall j)).mem_affineSpan
  have hcol := collinear_insert_insert_insert_of_mem_affineSpan_pair (hline 0) (hline 1) (hline 2)
  have : Collinear ℝ {T.pts 0, T.pts 1, T.pts 2} :=
    hcol.subset (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  exact (affineIndependent_iff_not_collinear_set.mp (tri_indep T)) this
theorem side_pigeonhole {N : ℕ} (D : CongruentDissection N) (θ : ℝ) (i : Fin 3)
    (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
    (hcorner : ∀ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts e.2) = θ ∨
      (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 1)) = θ)
    (hAθ : ∀ e ∈ part, ((D.tile e.1).pts e.2 = D.target.pts i ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts i) →
        (D.tile e.1).localAngle (D.target.pts i) ≠ θ)
    (hBθ : ∀ e ∈ part, ((D.tile e.1).pts e.2 = D.target.pts (i + 1) ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts (i + 1)) →
        (D.tile e.1).localAngle (D.target.pts (i + 1)) ≠ θ)
    (htwo : ∀ P ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)),
      (Finset.univ.filter fun i => (D.tile i).localAngle P = θ).card ≤ 1) : False := by
  classical
  set A := D.target.pts i
  set B := D.target.pts (i + 1)
  set u : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts e.2 with hu
  set v : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts (e.2 + 1) with hv
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ A B := by
    intro e he y hy
    rw [← hcov]
    exact Set.mem_biUnion he hy
  let φ : Fin N × Fin 3 → Plane := fun e =>
    if (D.tile e.1).localAngle (u e) = θ then u e else v e
  have hφθ : ∀ e ∈ part, (D.tile e.1).localAngle (φ e) = θ := by
    intro e he
    simp only [φ]
    split_ifs with h
    · exact h
    · exact (hcorner e he).resolve_left h
  have hφuv : ∀ e, φ e = u e ∨ φ e = v e := by
    intro e; simp only [φ]; split_ifs <;> simp
  set Eint := (part.image u ∪ part.image v).filter fun x => x ≠ A ∧ x ≠ B
  have hφE : ∀ e ∈ part, φ e ∈ Eint := by
    intro e he
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
    · rcases hφuv e with h | h <;> rw [h]
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
    · intro h
      refine hAθ e he ?_ (h ▸ hφθ e he)
      rcases hφuv e with h' | h'
      · exact Or.inl (h'.symm.trans h)
      · exact Or.inr (h'.symm.trans h)
    · intro h
      refine hBθ e he ?_ (h ▸ hφθ e he)
      rcases hφuv e with h' | h'
      · exact Or.inl (h'.symm.trans h)
      · exact Or.inr (h'.symm.trans h)
  have hinj : Set.InjOn φ part := by
    intro e he e' he' heq
    by_contra hne
    by_cases h1 : e.1 = e'.1
    · have h2 : e.2 ≠ e'.2 := fun h2 => hne (Prod.ext h1 h2)
      exact tri_two_edges_on_segment (D.tile e.1) h2 (hsub e he) (h1 ▸ hsub e' he')
    · have hP : φ e ∈ segment ℝ A B := by
        apply hsub e he
        rcases hφuv e with h | h <;> rw [h]
        · exact left_mem_segment _ _ _
        · exact right_mem_segment _ _ _
      have hcard := htwo (φ e) hP
      have : 1 < (Finset.univ.filter fun i => (D.tile i).localAngle (φ e) = θ).card :=
        Finset.one_lt_card.mpr ⟨e.1, by simp [hφθ e he], e'.1,
          by simp [heq, hφθ e' he'], h1⟩
      omega
  have hle := Finset.card_le_card_of_injOn φ hφE hinj
  have hAB : A ≠ B := D.target.indep.injective.ne (fin3_ne_add_one i)
  have huv : ∀ e ∈ part, u e ≠ v e :=
    fun e _ => (D.tile e.1).indep.injective.ne (fin3_ne_add_one e.2)
  have hchain : Eint.card + 1 ≤ part.card :=
    (segment_chain_endpoints A B hAB part u v huv hcov hdisj).1
  omega
theorem side_has_edge {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) (θ : ℝ)
    (hθ : θ = tileβ D ∨ θ = tileγ D) (i : Fin 3) (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
    (hAθ : ∀ e ∈ part, ((D.tile e.1).pts e.2 = D.target.pts i ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts i) →
        (D.tile e.1).localAngle (D.target.pts i) ≠ θ)
    (hBθ : ∀ e ∈ part, ((D.tile e.1).pts e.2 = D.target.pts (i + 1) ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts (i + 1)) →
        (D.tile e.1).localAngle (D.target.pts (i + 1)) ≠ θ)
    (htwo : ∀ P ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)),
      (Finset.univ.filter fun i => (D.tile i).localAngle P = θ).card ≤ 1) :
    ∃ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = θ := by
  classical
  by_contra hno
  push Not at hno
  set A := D.target.pts i
  set B := D.target.pts (i + 1)
  set u : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts e.2 with hu
  set v : Fin N × Fin 3 → Plane := fun e => (D.tile e.1).pts (e.2 + 1) with hv
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ A B := by
    intro e he y hy
    rw [← hcov]
    exact Set.mem_biUnion he hy
  have hcorner : ∀ e ∈ part, (D.tile e.1).localAngle (u e) = θ ∨
      (D.tile e.1).localAngle (v e) = θ := by
    intro e he
    have hcnt := tile_angle_count D hγ hirr e.1
    have hcard : (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile e.1).pts (k + 1))
        ((D.tile e.1).pts k) ((D.tile e.1).pts (k + 2)) = θ).card = 1 := by
      rcases hθ with rfl | rfl
      · exact hcnt.2.1
      · exact hcnt.2.2
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
    have hkθ : cornerAngle ((D.tile e.1).pts (k + 1)) ((D.tile e.1).pts k)
        ((D.tile e.1).pts (k + 2)) = θ := by
      have : k ∈ Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile e.1).pts (k + 1))
          ((D.tile e.1).pts k) ((D.tile e.1).pts (k + 2)) = θ := by rw [hk]; simp
      exact (Finset.mem_filter.mp this).2
    have hloc : (D.tile e.1).localAngle ((D.tile e.1).pts k) = θ := by
      rw [Tri.localAngle_vertex]; exact hkθ
    have hk2 : k ≠ e.2 + 2 := fun h => hno e he (h ▸ hloc)
    have : k = e.2 ∨ k = e.2 + 1 := by
      obtain ⟨_, j⟩ := e
      fin_cases j <;> fin_cases k <;> simp at hk2 ⊢
    rcases this with rfl | rfl
    · exact Or.inl hloc
    · exact Or.inr hloc
  exact side_pigeonhole D θ i part hcov hdisj hcorner hAθ hBθ htwo
theorem qandrnotzero {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
    (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
    (hB : ∀ e ∈ part, ((D.tile e.1).pts e.2 = D.target.pts 1 ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts 1) →
        (D.tile e.1).localAngle (D.target.pts 1) = tileα D) :
    (∃ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileβ D) ∧
    (∃ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileγ D) := by
  obtain ⟨-, hv0, hinj⟩ := angle_values D hγ hirr
  have hTsum := cornerAngle_sum D.target
  have hlocA : D.target.localAngle (D.target.pts 0) = (1 : ℤ) * tileα D + (0 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = _
    have : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
    rw [this]; push_cast; ring
  have hlocB : D.target.localAngle (D.target.pts 1) = (-2 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
    have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
    have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileα D := by
      rw [cornerAngle, angle_comm]; exact hC
    push_cast; linarith
  have rA := vertex_relations D hγ hirr _ 1 0 hlocA
  have rB := vertex_relations D hγ hirr _ (-2) 1 hlocB
  have none : ∀ (P : Plane) (θ : ℝ), angleCount D P θ = 0 → ∀ i, (D.tile i).localAngle P ≠ θ := by
    intro P θ h i hi
    have : i ∈ Finset.univ.filter fun i => (D.tile i).localAngle P = θ := by simp [hi]
    rw [angleCount, Finset.card_eq_zero] at h
    rw [h] at this
    simp at this
  have hβA : angleCount D (D.target.pts 0) (tileβ D) = 0 := by omega
  have hγA : angleCount D (D.target.pts 0) (tileγ D) = 0 := by omega
  have hγB : angleCount D (D.target.pts 1) (tileγ D) = 0 := by
    have : angleCount D (D.target.pts 1) (tileβ D) ≤ 1 := by omega
    interval_cases h : angleCount D (D.target.pts 1) (tileβ D) <;> omega
  have hfr : ∀ P ∈ segment ℝ (D.target.pts 0) (D.target.pts 1), P ∈ frontier D.target.carrier :=
    fun P hP => tri_side_subset_frontier D.target 0 hP
  have htb := fun P hP => twobeta D hγ hirr hA hC (hfr P hP)
  refine ⟨side_has_edge D hγ hirr _ (Or.inl rfl) 0 part hcov hdisj
      (fun e _ _ => none _ _ hβA e.1) ?_ (fun P hP => (htb P hP).1),
    side_has_edge D hγ hirr _ (Or.inr rfl) 0 part hcov hdisj (fun e _ _ => none _ _ hγA e.1)
      (fun e _ _ => none _ _ hγB e.1) (fun P hP => (htb P hP).2)⟩
  intro e he hend h
  have h' : (D.tile e.1).localAngle (D.target.pts 1) = tileβ D := h
  rw [hB e he hend] at h'
  exact hinj.ne (show (0 : Fin 5) ≠ 1 by decide) h'
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem edge_len_mem {N : ℕ} (D : CongruentDissection N) (j : Fin N) (k : Fin 3) :
    dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = dist (D.model.pts 1) (D.model.pts 2) ∨
    dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = dist (D.model.pts 2) (D.model.pts 0) ∨
    dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = dist (D.model.pts 0) (D.model.pts 1) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent j).dist_eq
  rw [hσ]
  have hne : σ k ≠ σ (k + 1) := σ.injective.ne (by fin_cases k <;> decide)
  generalize σ k = u at hne
  generalize σ (k + 1) = v at hne
  fin_cases u <;> fin_cases v <;>
    first
    | exact absurd rfl hne
    | (left; rfl) | (left; exact dist_comm _ _)
    | (right; left; rfl) | (right; left; exact dist_comm _ _)
    | (right; right; rfl) | (right; right; exact dist_comm _ _)
theorem notprimehelper {N : ℕ} (D : CongruentDissection N) {a b c : ℕ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1)
    (hγ : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) =
      2 * ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2))
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) =
      ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)) :
    (∃ s : ℕ, N * b = s ^ 2) ∧ (Squarefree N → ∃ ℓ : ℕ, b = N * ℓ ^ 2) := by
  obtain ⟨-, hYX, hX2⟩ := areaequation_core D ha hb hc rfl rfl hγ hA hC
  set X := dist (D.target.pts 0) (D.target.pts 1)
  have habc : ∀ (j : Fin N) (k : Fin 3),
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (a : ℝ) ∨
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (b : ℝ) ∨
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = (c : ℝ) := by
    intro j k; rw [← ha, ← hb, ← hc]; exact edge_len_mem D j k
  obtain ⟨P, Q, R, hPQR, -⟩ := D.toDissection.side_walk_abc 2 a b c habc
  have h20 : (2 : Fin 3) + 1 = 0 := rfl
  rw [h20] at hPQR
  set Yn : ℕ := P * a + Q * b + R * c with hYn
  have hY : dist (D.target.pts 2) (D.target.pts 0) = (Yn : ℝ) := by
    rw [← hPQR, hYn]; push_cast; ring
  rw [hY] at hYX
  have hcab : c ^ 2 = a ^ 2 + a * b := by
    have := (twoalphatiles (tri_indep D.model) ha hb hc).mp hγ
    exact_mod_cast this
  obtain ⟨m1, m2, m3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at m1 m2 m3
  have m1' : a < b + c := by exact_mod_cast m1
  have m2' : b < c + a := by exact_mod_cast m2
  have m3' : c < a + b := by exact_mod_cast m3
  obtain ⟨k, m, -, hkm, -, hak, -, hck⟩ :=
    (luthar a b c).mp ⟨hcop, hcab, m1', by omega, m3'⟩
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hak; omega
    · exact h
  have hm0 : 0 < m := by omega
  have ha0 : (0 : ℝ) < a := by have : 0 < a := by rw [hak]; positivity
                               exact_mod_cast this
  have hreal : (a : ℝ) * (Yn : ℝ) ^ 2 = N * b * (c : ℝ) ^ 2 := by
    have h1 : (a : ℝ) * ((a : ℝ) * (Yn : ℝ) ^ 2 - N * b * (c : ℝ) ^ 2) = 0 := by
      linear_combination (a * Yn + c * X) * hYX + c ^ 2 * hX2
    have := (mul_eq_zero.mp h1).resolve_left ha0.ne'
    linarith
  have hnat : k ^ 2 * Yn ^ 2 = k ^ 2 * (N * b * m ^ 2) := by
    have : a * Yn ^ 2 = N * b * c ^ 2 := by exact_mod_cast hreal
    rw [hak, hck] at this
    rw [this]; ring
  have h1 : Yn ^ 2 = N * b * m ^ 2 := Nat.eq_of_mul_eq_mul_left (by positivity) hnat
  have hmY : m ∣ Yn := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨N * b, by rw [h1]; ring⟩
  obtain ⟨t, ht⟩ := hmY
  have hNb : N * b = t ^ 2 := by
    rw [ht] at h1
    have : m ^ 2 * (N * b) = m ^ 2 * t ^ 2 :=
      calc m ^ 2 * (N * b) = N * b * m ^ 2 := by ring
        _ = (m * t) ^ 2 := h1.symm
        _ = m ^ 2 * t ^ 2 := by ring
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) this)
  refine ⟨⟨t, hNb⟩, fun hsq => ?_⟩
  have hN0 : 0 < N := Nat.pos_of_ne_zero (fun h => by subst h; exact not_squarefree_zero hsq)
  obtain ⟨u, hu⟩ := (hsq.dvd_pow_iff_dvd two_ne_zero).mp ⟨b, hNb.symm⟩
  refine ⟨u, Nat.eq_of_mul_eq_mul_left hN0 ?_⟩
  rw [hNb, hu]; ring
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem fin3_add_two_add_one : ∀ k : Fin 3, k + 2 + 1 = k := by decide
theorem fin3_add_two_add_two : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide
theorem congruent_corner_opp {T U : Tri} (h : T.Congruent U) (k : Fin 3) :
    ∃ j : Fin 3, cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) =
        cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2)) ∧
      dist (T.pts (k + 1)) (T.pts (k + 2)) = dist (U.pts (j + 1)) (U.pts (j + 2)) := by
  obtain ⟨σ, hσ⟩ := h.dist_eq
  refine ⟨σ k, ?_, ?_⟩
  · have hang : cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) =
        cornerAngle (U.pts (σ (k + 1))) (U.pts (σ k)) (U.pts (σ (k + 2))) :=
      angle_of_sss (hσ _ _) (hσ _ _) (hσ _ _)
        (T.indep.injective.ne (by fin_cases k <;> decide))
        (T.indep.injective.ne (by fin_cases k <;> decide))
    rw [hang]
    have h1 : σ (k + 1) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
    have h2 : σ (k + 2) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
    have h12 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne (by fin_cases k <;> decide)
    generalize σ k = j0 at h1 h2 h12 ⊢
    generalize σ (k + 1) = j1 at h1 h2 h12 ⊢
    generalize σ (k + 2) = j2 at h1 h2 h12 ⊢
    fin_cases j0 <;> fin_cases j1 <;> fin_cases j2 <;> simp at h1 h2 h12 ⊢ <;>
      first | rfl | exact angle_comm _ _ _
  · rw [hσ]
    have h1 : σ (k + 1) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
    have h2 : σ (k + 2) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
    have h12 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne (by fin_cases k <;> decide)
    generalize σ k = j0 at h1 h2 h12 ⊢
    generalize σ (k + 1) = j1 at h1 h2 h12 ⊢
    generalize σ (k + 2) = j2 at h1 h2 h12 ⊢
    fin_cases j0 <;> fin_cases j1 <;> fin_cases j2 <;> simp at h1 h2 h12 ⊢ <;>
      first | rfl | exact dist_comm _ _
theorem opp_side_sep {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D) (i : Fin N)
    (k : Fin 3) :
    ((D.tile i).localAngle ((D.tile i).pts k) = tileα D →
      dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) =
        dist (D.model.pts 1) (D.model.pts 2)) ∧
    ((D.tile i).localAngle ((D.tile i).pts k) = tileβ D →
      dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) =
        dist (D.model.pts 2) (D.model.pts 0)) ∧
    ((D.tile i).localAngle ((D.tile i).pts k) = tileγ D →
      dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) =
        dist (D.model.pts 0) (D.model.pts 1)) := by
  obtain ⟨-, hinj⟩ := hsep
  obtain ⟨j, hang, hd⟩ := congruent_corner_opp (D.tiles_congruent i) k
  rw [Tri.localAngle_vertex, hang, hd]
  have e0 : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = tileα D := rfl
  have e1 : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = tileβ D := rfl
  have e2 : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = tileγ D := rfl
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  fin_cases j
  · refine ⟨fun _ => rfl, fun h => absurd (e0.symm.trans h) (ne 0 1 (by decide)),
      fun h => absurd (e0.symm.trans h) (ne 0 2 (by decide))⟩
  · refine ⟨fun h => absurd (e1.symm.trans h) (ne 1 0 (by decide)), fun _ => rfl,
      fun h => absurd (e1.symm.trans h) (ne 1 2 (by decide))⟩
  · refine ⟨fun h => absurd (e2.symm.trans h) (ne 2 0 (by decide)),
      fun h => absurd (e2.symm.trans h) (ne 2 1 (by decide)), fun _ => rfl⟩
theorem localAngle_at_own_vertex_mem' {N : ℕ} (D : CongruentDissection N) (i : Fin N)
    (k : Fin 3) :
    (D.tile i).localAngle ((D.tile i).pts k) = tileα D ∨
    (D.tile i).localAngle ((D.tile i).pts k) = tileβ D ∨
    (D.tile i).localAngle ((D.tile i).pts k) = tileγ D := by
  rw [Tri.localAngle_vertex]
  obtain ⟨j, hj, -⟩ := congruent_corner_opp (D.tiles_congruent i) k
  rw [hj]
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
theorem side_walk_counts_sep {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D)
    (part : Finset (Fin N × Fin 3))
    (L : ℝ) (hsum : ∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = L) :
    L = ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileα D).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      + ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileβ D).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
      + ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileγ D).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1) := by
  classical
  obtain ⟨hv0, hinj⟩ := hsep
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  have hαβ : tileα D ≠ tileβ D := ne 0 1 (by decide)
  have hαγ : tileα D ≠ tileγ D := ne 0 2 (by decide)
  have hβγ : tileβ D ≠ tileγ D := ne 1 2 (by decide)
  have hpt : ∀ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      (if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileα D
        then dist (D.model.pts 1) (D.model.pts 2) else 0)
      + (if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileβ D
        then dist (D.model.pts 2) (D.model.pts 0) else 0)
      + (if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileγ D
        then dist (D.model.pts 0) (D.model.pts 1) else 0) := by
    intro e _
    have hsides := opp_side_sep D ⟨hv0, hinj⟩ e.1 (e.2 + 2)
    have e3 : e.2 + 2 + 1 = e.2 := fin3_add_two_add_one e.2
    have e4 : e.2 + 2 + 2 = e.2 + 1 := fin3_add_two_add_two e.2
    rw [e3, e4] at hsides
    have hmem := localAngle_at_own_vertex_mem' D e.1 (e.2 + 2)
    rcases hmem with h | h | h
    · rw [if_pos h, if_neg (h ▸ hαβ), if_neg (h ▸ hαγ), hsides.1 h]; ring
    · rw [if_neg (h ▸ hαβ.symm), if_pos h, if_neg (h ▸ hβγ), hsides.2.1 h]; ring
    · rw [if_neg (h ▸ hαγ.symm), if_neg (h ▸ hβγ.symm), if_pos h, hsides.2.2 h]; ring
  rw [← hsum, Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
theorem side_walk_counts {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi) (part : Finset (Fin N × Fin 3))
    (L : ℝ) (hsum : ∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = L) :
    L = ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileα D).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      + ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileβ D).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
      + ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileγ D).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1) :=
  side_walk_counts_sep D (anglesSep_of_two_alpha D hγ hirr) part L hsum
theorem corner_eq_of_two (T : Tri) (kB a₁ a₂ : Fin 3) (h₁ : a₁ ≠ kB) (h₂ : a₂ ≠ kB)
    (h₁₂ : a₁ ≠ a₂) :
    cornerAngle (T.pts (kB + 1)) (T.pts kB) (T.pts (kB + 2)) = ∠ (T.pts a₁) (T.pts kB) (T.pts a₂) := by
  fin_cases kB <;> fin_cases a₁ <;> fin_cases a₂ <;> simp at h₁ h₂ h₁₂ ⊢ <;>
    first | rfl | exact angle_comm _ _ _
theorem edge_endpoint (T : Tri) (j : Fin 3) {B : Plane}
    (h : T.pts j = B ∨ T.pts (j + 1) = B) :
    ∃ kB a : Fin 3, T.pts kB = B ∧ a ≠ kB ∧ T.pts a ∈ T.edge j := by
  rcases h with h | h
  · exact ⟨j, j + 1, h, (fin3_ne_add_one j).symm, right_mem_segment _ _ _⟩
  · exact ⟨j + 1, j, h, fin3_ne_add_one j, left_mem_segment _ _ _⟩
theorem beta_at_apex {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
    (part₀ part₁ : Finset (Fin N × Fin 3))
    (hcov₀ : (⋃ e ∈ part₀, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1))
    (hcov₁ : (⋃ e ∈ part₁, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 1) (D.target.pts 2)) :
    (∀ e ∈ part₀, ((D.tile e.1).pts e.2 = D.target.pts 1 ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts 1) →
        (D.tile e.1).localAngle (D.target.pts 1) ≠ tileβ D) ∨
    (∀ e ∈ part₁, ((D.tile e.1).pts e.2 = D.target.pts 1 ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts 1) →
        (D.tile e.1).localAngle (D.target.pts 1) ≠ tileβ D) := by
  classical
  obtain ⟨hβ, -, -⟩ := angle_values D hγ hirr
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨e₁, he₁, hend₁, hβ₁⟩, ⟨e₂, he₂, hend₂, hβ₂⟩⟩ := hcon
  set B := D.target.pts 1
  have hTsum := cornerAngle_sum D.target
  have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
  have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileα D := by
    rw [cornerAngle, angle_comm]; exact hC
  have hBang : ∠ (D.target.pts 0) B (D.target.pts 2) = Real.pi - 2 * tileα D := by
    have : cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) =
        Real.pi - 2 * tileα D := by linarith
    rw [cornerAngle, angle_comm] at this; exact this
  have hlocB : D.target.localAngle B = (-2 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
    push_cast; linarith
  have rB := vertex_relations D hγ hirr _ (-2) 1 hlocB
  have hcnt : angleCount D B (tileβ D) ≤ 1 := by omega
  have hsame : e₁.1 = e₂.1 := by
    have := Finset.card_le_one.mp hcnt e₁.1 (by simp [hβ₁]) e₂.1 (by simp [hβ₂])
    exact this
  set t := D.tile e₁.1
  obtain ⟨kB, a₁, hkB, ha₁, hP⟩ := edge_endpoint t e₁.2 hend₁
  obtain ⟨kB', a₂, hkB', ha₂, hQ⟩ := edge_endpoint (D.tile e₂.1) e₂.2 hend₂
  rw [← hsame] at hkB' hQ
  have hkk : kB' = kB := t.indep.injective (hkB'.trans hkB.symm)
  rw [hkk] at ha₂
  have hPseg : t.pts a₁ ∈ segment ℝ (D.target.pts 0) B := by
    rw [← hcov₀]; exact Set.mem_biUnion he₁ hP
  have hQseg : t.pts a₂ ∈ segment ℝ B (D.target.pts 2) := by
    rw [← hcov₁]; exact Set.mem_biUnion he₂ (hsame ▸ hQ)
  have hPB : t.pts a₁ ≠ B := fun h => ha₁ (t.indep.injective (h.trans hkB.symm))
  have hQB : t.pts a₂ ≠ B := fun h => ha₂ (t.indep.injective (h.trans hkB.symm))
  have hang : ∠ (t.pts a₁) B (t.pts a₂) = Real.pi - 2 * tileα D := by
    rw [(mem_segment_iff_wbtw.mp hPseg).symm.angle_eq_left _ hPB,
      (mem_segment_iff_wbtw.mp hQseg).angle_eq_right _ hQB, hBang]
  by_cases h12 : a₁ = a₂
  · 
    subst h12
    rw [angle_self_of_ne hPB] at hang
    exact hirr ⟨1 / 2, by push_cast; linarith⟩
  · 
    have hcorner := corner_eq_of_two t kB a₁ a₂ ha₁ ha₂ h12
    rw [hkB, hang] at hcorner
    have : t.localAngle B = Real.pi - 2 * tileα D := by
      rw [← hkB, Tri.localAngle_vertex, hkB]; exact hcorner
    rw [this, hβ] at hβ₁
    exact hirr ⟨0, by push_cast; linarith⟩
theorem notsquarefree_arith (N k m ℓ p q r : ℕ) (hk : 0 < k) (hkm : k < m)
    (hcop : Nat.Coprime k m) (hb : N * ℓ ^ 2 = m ^ 2 - k ^ 2)
    (hX : N * k * ℓ = p * k ^ 2 + q * (m ^ 2 - k ^ 2) + r * (k * m)) (hq : 1 ≤ q) (hr : 1 ≤ r) :
    False := by
  set b := m ^ 2 - k ^ 2 with hbdef
  have hk2m2 : k ^ 2 < m ^ 2 := Nat.pow_lt_pow_left hkm two_ne_zero
  have hbm : b + k ^ 2 = m ^ 2 := by omega
  have hb0 : 0 < b := by omega
  have hℓ : 0 < ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · rw [h] at hb; simp at hb; omega
    · exact h
  have hkq : k ∣ q := by
    have h1 : k ∣ q * b := by
      have h2 : k ∣ N * k * ℓ := ⟨N * ℓ, by ring⟩
      rw [hX, show p * k ^ 2 + q * b + r * (k * m) = (p * k ^ 2 + r * (k * m)) + q * b by ring]
        at h2
      exact (Nat.dvd_add_right ⟨p * k + r * m, by ring⟩).mp h2
    have h3 : k ∣ q * m ^ 2 := by
      rw [← hbm, mul_add]
      exact Nat.dvd_add h1 ⟨q * k, by ring⟩
    exact (Nat.Coprime.pow_right 2 hcop).dvd_of_dvd_mul_right h3
  have hqk : k ≤ q := Nat.le_of_dvd (by omega) hkq
  have hkb : k * b = ℓ * (p * k ^ 2) + ℓ * q * b + ℓ * r * (k * m) := by
    have : ℓ * (N * k * ℓ) = k * b := by rw [← hb]; ring
    rw [← this, hX]; ring
  have hge : k * b ≤ ℓ * q * b :=
    Nat.mul_le_mul_right b (le_trans hqk (Nat.le_mul_of_pos_left q hℓ))
  have hpos : 0 < ℓ * r * (k * m) :=
    Nat.mul_pos (Nat.mul_pos hℓ (by omega)) (Nat.mul_pos hk (by omega))
  omega
theorem notsquarefree_int {N : ℕ} (D : CongruentDissection N) {a b c : ℕ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1) (hγ : tileγ D = 2 * tileα D)
    (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D) :
    ¬ Squarefree N := by
  classical
  intro hsq
  obtain ⟨-, hv0, hinj⟩ := angle_values D hγ hirr
  obtain ⟨ℓ, hbℓ⟩ := (notprimehelper D ha hb hc hcop hγ hA hC).2 hsq
  obtain ⟨hBC, -, hX2⟩ := areaequation_core D ha hb hc rfl rfl hγ hA hC
  set X := dist (D.target.pts 0) (D.target.pts 1) with hXdef
  have hcab : c ^ 2 = a ^ 2 + a * b := by
    have := (twoalphatiles (tri_indep D.model) ha hb hc).mp hγ
    exact_mod_cast this
  obtain ⟨m1, m2, m3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at m1 m2 m3
  have m1' : a < b + c := by exact_mod_cast m1
  have m2' : b < c + a := by exact_mod_cast m2
  have m3' : c < a + b := by exact_mod_cast m3
  obtain ⟨k, m, hkm_cop, hkm, -, hak, hbk, hck⟩ :=
    (luthar a b c).mp ⟨hcop, hcab, m1', by omega, m3'⟩
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hak; simp at hak; omega
    · exact h
  have hX : X = (N * k * ℓ : ℕ) := by
    have hX0 : 0 ≤ X := dist_nonneg
    have hsq' : X ^ 2 = ((N * k * ℓ : ℕ) : ℝ) ^ 2 := by
      rw [hX2]
      have : (a : ℝ) * b = (k : ℝ) ^ 2 * (N * ℓ ^ 2) := by
        rw [hak, hbℓ]; push_cast; ring
      push_cast
      linear_combination (N : ℝ) * this
    exact (sq_eq_sq₀ hX0 (by positivity)).mp hsq'
  have hTsum := cornerAngle_sum D.target
  have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
  have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileα D := by
    rw [cornerAngle, angle_comm]; exact hC
  have hloc0 : D.target.localAngle (D.target.pts 0) = (1 : ℤ) * tileα D + (0 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = _
    push_cast; linarith
  have hloc1 : D.target.localAngle (D.target.pts 1) = (-2 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
    push_cast; linarith
  have hloc2 : D.target.localAngle (D.target.pts 2) = (1 : ℤ) * tileα D + (0 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = _
    push_cast; linarith
  have r0 := vertex_relations D hγ hirr _ 1 0 hloc0
  have r1 := vertex_relations D hγ hirr _ (-2) 1 hloc1
  have r2 := vertex_relations D hγ hirr _ 1 0 hloc2
  have none : ∀ (P : Plane) (θ : ℝ), angleCount D P θ = 0 →
      ∀ i, (D.tile i).localAngle P ≠ θ := by
    intro P θ h i hi
    have : i ∈ Finset.univ.filter fun i => (D.tile i).localAngle P = θ := by simp [hi]
    rw [angleCount, Finset.card_eq_zero] at h
    rw [h] at this
    simp at this
  have hβ0 : angleCount D (D.target.pts 0) (tileβ D) = 0 := by omega
  have hγ0 : angleCount D (D.target.pts 0) (tileγ D) = 0 := by omega
  have hβ2 : angleCount D (D.target.pts 2) (tileβ D) = 0 := by omega
  have hγ2 : angleCount D (D.target.pts 2) (tileγ D) = 0 := by omega
  have hγ1 : angleCount D (D.target.pts 1) (tileγ D) = 0 := by
    have : angleCount D (D.target.pts 1) (tileβ D) ≤ 1 := by omega
    interval_cases h : angleCount D (D.target.pts 1) (tileβ D) <;> omega
  obtain ⟨part₀, hcov₀, hdisj₀, hsum₀⟩ := D.toDissection.side_walk 0
  obtain ⟨part₁, hcov₁, hdisj₁, hsum₁⟩ := D.toDissection.side_walk 1
  have h01 : (0 : Fin 3) + 1 = 1 := rfl
  have h12 : (1 : Fin 3) + 1 = 2 := rfl
  rw [h01] at hcov₀ hsum₀
  rw [h12] at hcov₁ hsum₁
  have finish : ∀ (part : Finset (Fin N × Fin 3)),
      (∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = X) →
      (∃ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileβ D) →
      (∃ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileγ D) → False := by
    intro part hsum ⟨eq, hq, hqβ⟩ ⟨er, hr, hrγ⟩
    have hw := side_walk_counts D hγ hirr part X hsum
    rw [ha, hb, hc, hX] at hw
    set p := (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
      = tileα D).card
    set q := (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
      = tileβ D).card
    set r := (part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
      = tileγ D).card
    have hq1 : 1 ≤ q := Finset.card_pos.mpr ⟨eq, Finset.mem_filter.mpr ⟨hq, hqβ⟩⟩
    have hr1 : 1 ≤ r := Finset.card_pos.mpr ⟨er, Finset.mem_filter.mpr ⟨hr, hrγ⟩⟩
    have hwn : N * k * ℓ = p * a + q * b + r * c := by exact_mod_cast hw
    rw [hak, hbk, hck] at hwn
    rw [hbk] at hbℓ
    exact notsquarefree_arith N k m ℓ p q r hk0 hkm hkm_cop hbℓ.symm
      hwn hq1 hr1
  have htb := fun P (hP : P ∈ frontier D.target.carrier) => twobeta D hγ hirr hA hC hP
  rcases beta_at_apex D hγ hirr hA hC part₀ part₁ hcov₀ hcov₁ with hB | hB
  · 
    have hfr : ∀ P ∈ segment ℝ (D.target.pts 0) (D.target.pts 1),
        P ∈ frontier D.target.carrier := fun P hP => tri_side_subset_frontier D.target 0 hP
    refine finish part₀ hsum₀ ?_ ?_
    · exact side_has_edge D hγ hirr _ (Or.inl rfl) 0 part₀ hcov₀ hdisj₀
        (fun e _ _ => none _ _ hβ0 e.1) hB (fun P hP => (htb P (hfr P hP)).1)
    · exact side_has_edge D hγ hirr _ (Or.inr rfl) 0 part₀ hcov₀ hdisj₀
        (fun e _ _ => none _ _ hγ0 e.1) (fun e _ _ => none _ _ hγ1 e.1)
        (fun P hP => (htb P (hfr P hP)).2)
  · 
    have hfr : ∀ P ∈ segment ℝ (D.target.pts 1) (D.target.pts 2),
        P ∈ frontier D.target.carrier := fun P hP => tri_side_subset_frontier D.target 1 hP
    refine finish part₁ (hsum₁.trans hBC) ?_ ?_
    · exact side_has_edge D hγ hirr _ (Or.inl rfl) 1 part₁ hcov₁ hdisj₁ hB
        (fun e _ _ => none _ _ hβ2 e.1) (fun P hP => (htb P (hfr P hP)).1)
    · exact side_has_edge D hγ hirr _ (Or.inr rfl) 1 part₁ hcov₁ hdisj₁
        (fun e _ _ => none _ _ hγ1 e.1) (fun e _ _ => none _ _ hγ2 e.1)
        (fun P hP => (htb P (hfr P hP)).2)
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry MeasureTheory Set
theorem tri_closure_interior (T : Tri) : closure (interior T.carrier) = T.carrier := by
  rw [T.convex.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty,
    T.isCompact.isClosed.closure_eq]
end TriangleTiling
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
theorem Tri.localAngle_openSegment (T : Tri) (m : Fin 3) {x : Plane}
    (hx : x ∈ openSegment ℝ (T.pts m) (T.pts (m + 1))) : T.localAngle x = Real.pi := by
  classical
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  have hm : T.basis.coord m (AffineMap.lineMap (T.pts m) (T.pts (m + 1)) t) = 1 - t := by
    rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m ≠ m + 1 by fin_cases m <;> decide]; ring
  have hm1 : T.basis.coord (m + 1) (AffineMap.lineMap (T.pts m) (T.pts (m + 1)) t) = t := by
    rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m + 1 ≠ m by fin_cases m <;> decide]
  have hm2 : T.basis.coord (m + 2) (AffineMap.lineMap (T.pts m) (T.pts (m + 1)) t) = 0 := by
    rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m + 2 ≠ m by fin_cases m <;> decide, show m + 2 ≠ m + 1 by fin_cases m <;> decide]
  set x := AffineMap.lineMap (T.pts m) (T.pts (m + 1)) t
  have hv : ¬ ∃ j, x = T.pts j := by
    rintro ⟨j, hj⟩
    have h1 := Tri.coord_vertex T m j
    have h2 := Tri.coord_vertex T (m + 1) j
    rw [← hj, hm] at h1
    rw [← hj, hm1] at h2
    split_ifs at h1 h2 <;> linarith
  have h2 : ¬ ∀ j, 0 < T.basis.coord j x := fun h => by have := h (m + 2); rw [hm2] at this; linarith
  have h3 : ∃ k, T.basis.coord k x = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j x := by
    refine ⟨m + 2, hm2, fun j hj => ?_⟩
    have : j = m ∨ j = m + 1 := by fin_cases m <;> fin_cases j <;> simp at hj ⊢
    rcases this with rfl | rfl
    · rw [hm]; linarith
    · rw [hm1]; exact ht0
  rw [Tri.localAngle, dif_neg hv, if_neg h2, if_pos h3]
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
section Counts
variable {N : ℕ} (D : CongruentDissection N)
theorem angleCount_pos {P : Plane} {θ : ℝ} {i : Fin N} (hi : (D.tile i).localAngle P = θ) :
    1 ≤ angleCount D P θ :=
  Finset.card_pos.mpr ⟨i, by simp [hi]⟩
theorem ne_of_angleCount_zero {P : Plane} {θ : ℝ} (h : angleCount D P θ = 0) (i : Fin N) :
    (D.tile i).localAngle P ≠ θ := fun hi => by
  have := angleCount_pos D hi; omega
variable (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hγ hirr
variable (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
include hA hC
theorem counts_at_corners :
    angleCount D (D.target.pts 0) (tileβ D) = 0 ∧ angleCount D (D.target.pts 0) (tileγ D) = 0 ∧
    angleCount D (D.target.pts 2) (tileβ D) = 0 ∧ angleCount D (D.target.pts 2) (tileγ D) = 0 ∧
    angleCount D (D.target.pts 1) (tileβ D) ≤ 1 ∧ angleCount D (D.target.pts 1) (tileγ D) = 0 ∧
    angleCount D (D.target.pts 0) (tileα D) = 1 ∧ angleCount D (D.target.pts 1) (tileα D) ≤ 1 := by
  have hTsum := cornerAngle_sum D.target
  have eA : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D := hA
  have eC : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileα D := by
    rw [cornerAngle, angle_comm]; exact hC
  have h0 : D.target.localAngle (D.target.pts 0) = (1 : ℤ) * tileα D + (0 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = _
    push_cast; linarith
  have h1 : D.target.localAngle (D.target.pts 1) = (-2 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
    push_cast; linarith
  have h2 : D.target.localAngle (D.target.pts 2) = (1 : ℤ) * tileα D + (0 : ℤ) * Real.pi := by
    rw [Tri.localAngle_vertex]
    show cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = _
    push_cast; linarith
  have r0 := vertex_relations D hγ hirr _ 1 0 h0
  have r1 := vertex_relations D hγ hirr _ (-2) 1 h1
  have r2 := vertex_relations D hγ hirr _ 1 0 h2
  have hb1 : angleCount D (D.target.pts 1) (tileβ D) ≤ 1 := by omega
  refine ⟨by omega, by omega, by omega, by omega, hb1, ?_, by omega, ?_⟩
  · interval_cases h : angleCount D (D.target.pts 1) (tileβ D) <;> omega
  · interval_cases h : angleCount D (D.target.pts 1) (tileβ D) <;> omega
end Counts
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry MeasureTheory
open Classical in
theorem wall_sum {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    {U V : Plane} (hUV : U ≠ V) (hS : segment ℝ U V ⊆ {y | f y = c})
    (hint : openSegment ℝ U V ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ U V, ∀ i, y ∉ interior (D.tile i).carrier)
    (hdich : ∀ e ∈ D.lineChain f c, (D.tile e.1).edge e.2 ⊆ segment ℝ U V ∨
      ((D.tile e.1).edge e.2 ∩ segment ℝ U V).Subsingleton) :
    ∑ e ∈ (D.lineChain f c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ U V),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist U V := by
  classical
  haveI : NullSingletonClass (Measure.hausdorffMeasure (1 : ℝ) : Measure Plane) :=
    Measure.nullSingletonClass_hausdorff _ one_pos
  have hp := D.wall_partition f c hf hUV hS hint hwall
  rw [← Finset.sum_filter_add_sum_filter_not (D.lineChain f c)
    (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ U V)] at hp
  have h0 : ∑ e ∈ (D.lineChain f c).filter
      (fun e => ¬ (D.tile e.1).edge e.2 ⊆ segment ℝ U V),
      (Measure.hausdorffMeasure 1 : Measure Plane) ((D.tile e.1).edge e.2 ∩ segment ℝ U V)
      = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    obtain ⟨he, hns⟩ := Finset.mem_filter.mp he
    exact ((hdich e he).resolve_left hns).measure_zero _
  have h1 : ∀ e ∈ (D.lineChain f c).filter
      (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ U V),
      (Measure.hausdorffMeasure 1 : Measure Plane) ((D.tile e.1).edge e.2 ∩ segment ℝ U V)
      = edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
    intro e he
    rw [Set.inter_eq_left.mpr (Finset.mem_filter.mp he).2, Tri.hausdorff_edge]
  rw [h0, add_zero, Finset.sum_congr rfl h1, hausdorffMeasure_segment] at hp
  have := congrArg ENNReal.toReal hp
  rw [ENNReal.toReal_sum (fun e _ => edist_ne_top _ _)] at this
  simpa [← dist_edist] using this
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem Tri.coord_openSegment (T : Tri) (m : Fin 3) {x : Plane}
    (hx : x ∈ openSegment ℝ (T.pts m) (T.pts (m + 1))) :
    0 < T.basis.coord m x ∧ 0 < T.basis.coord (m + 1) x ∧ T.basis.coord (m + 2) x = 0 := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m ≠ m + 1 by fin_cases m <;> decide]; linarith
  · rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m + 1 ≠ m by fin_cases m <;> decide]; exact ht0
  · rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m + 2 ≠ m by fin_cases m <;> decide, show m + 2 ≠ m + 1 by fin_cases m <;> decide]
theorem fin3_cases3 : ∀ j k : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by decide
theorem level_eq_coord (T : Tri) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (k : Fin 3)
    (h1 : g (T.pts (k + 1)) = c) (h2 : g (T.pts (k + 2)) = c) (Y : Plane) :
    g Y - c = T.basis.coord k Y * (g (T.pts k) - c) := by
  have hY := T.basis.linear_combination_coord_eq_self Y
  have hs := T.basis.sum_coord_apply_eq_one Y
  have hgY : g Y = ∑ i, T.basis.coord i Y * g (T.pts i) := by
    conv_lhs => rw [← hY]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]; rfl
  have hc : c = ∑ i, T.basis.coord i Y * c := by rw [← Finset.sum_mul, hs, one_mul]
  have e3 : ∀ i : Fin 3, i = k ∨ i = k + 1 ∨ i = k + 2 := fun i => fin3_cases3 i k
  rw [hgY]
  conv_lhs => rw [hc]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k]
  · ring
  · intro i _ hik
    rcases e3 i with h | h | h
    · exact absurd h hik
    · rw [h, h1]; ring
    · rw [h, h2]; ring
  · simp
theorem exists_small_pos {a b : ℝ} (ha : 0 < a) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → 0 < a + ε * b := by
  by_cases hb : 0 ≤ b
  · exact ⟨1, one_pos, fun ε hε _ => by nlinarith⟩
  · push Not at hb
    refine ⟨a / (-b), div_pos ha (by linarith), fun ε hε hlt => ?_⟩
    rw [lt_div_iff₀ (by linarith)] at hlt
    nlinarith
theorem edge_level_oriented (T : Tri) (m : Fin 3) :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ (∀ y ∈ T.edge m, g y = c) ∧ c < g (T.pts (m + 2)) := by
  obtain ⟨f, c, hf, hline⟩ := T.edge_line m
  have h1 : f (T.pts m) = c := hline _ (left_mem_segment _ _ _)
  have h2 : f (T.pts (m + 1)) = c := hline _ (right_mem_segment _ _ _)
  have hne : f (T.pts (m + 2)) ≠ c := by
    intro h3
    apply hf
    have hall : ∀ Y, f Y = c := by
      intro Y
      have := level_eq_coord T f c (m + 2) (by rw [fin3_add_two_add_one]; exact h1)
        (by rw [fin3_add_two_add_two]; exact h2) Y
      rw [h3, sub_self, mul_zero] at this; linarith
    have hc : c = 0 := by rw [← hall 0, map_zero]
    ext Y; simp [hall Y, hc]
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨-f, -c, neg_ne_zero.mpr hf, fun y hy => by simp [hline y hy], ?_⟩
    simp only [LinearMap.neg_apply]; linarith
  · exact ⟨f, c, hf, hline, h⟩
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry
theorem Tri.localAngle_le_two_pi (T : Tri) (p : Plane) : T.localAngle p ≤ 2 * Real.pi := by
  classical
  rw [Tri.localAngle]
  split
  · exact le_trans (EuclideanGeometry.angle_le_pi _ _ _) (by linarith [Real.pi_pos])
  · split
    · exact le_rfl
    · split <;> linarith [Real.pi_pos]
theorem Tri.localAngle_le_pi (T : Tri) {p : Plane} (hp : p ∉ interior T.carrier) :
    T.localAngle p ≤ Real.pi := by
  classical
  rw [Tri.localAngle]
  split
  · exact EuclideanGeometry.angle_le_pi _ _ _
  · split
    · rename_i h; exact absurd ((Tri.mem_interior_iff_coord_pos T p).mpr h) hp
    · split <;> linarith [Real.pi_pos]
theorem Tri.vertex_not_mem_openSegment (T : Tri) (k m : Fin 3) :
    T.pts k ∉ openSegment ℝ (T.pts m) (T.pts (m + 1)) := by
  intro h
  obtain ⟨h0, h1, h2⟩ := Tri.coord_openSegment T m h
  rw [Tri.coord_vertex] at h0 h1 h2
  rcases fin3_cases3 k m with rfl | rfl | rfl
  · have : ¬ (k + 1 = k) := by fin_cases k <;> decide
    simp [this] at h1
  · have : ¬ (m = m + 1) := by fin_cases m <;> decide
    simp [this] at h0
  · have : ¬ (m = m + 2) := by fin_cases m <;> decide
    simp [this] at h0
theorem Tri.openSegment_edge_unique (T : Tri) {m m' : Fin 3} {p : Plane}
    (h : p ∈ openSegment ℝ (T.pts m) (T.pts (m + 1)))
    (h' : p ∈ openSegment ℝ (T.pts m') (T.pts (m' + 1))) : m = m' := by
  obtain ⟨a0, a1, a2⟩ := Tri.coord_openSegment T m h
  obtain ⟨b0, b1, b2⟩ := Tri.coord_openSegment T m' h'
  rcases fin3_cases3 m' m with rfl | rfl | rfl
  · rfl
  · rw [show m + 1 + 1 = m + 2 by fin_cases m <;> rfl, a2] at b1
    exact absurd b1 (lt_irrefl 0)
  · rw [show m + 2 + 2 = m + 1 by fin_cases m <;> rfl] at b2
    linarith
section Dissection
variable {N : ℕ} (D : Dissection N)
theorem mem_interior_of_sum_gt {p : Plane} (hp : Real.pi < ∑ i, (D.tile i).localAngle p) :
    p ∈ interior D.target.carrier := by
  by_contra h
  rw [D.sum_localAngle_eq] at hp
  linarith [Tri.localAngle_le_pi D.target h]
theorem sum_ge_two {i j : Fin N} (hij : i ≠ j) (p : Plane) :
    (D.tile i).localAngle p + (D.tile j).localAngle p ≤ ∑ k, (D.tile k).localAngle p := by
  calc _ = ∑ k ∈ {i, j}, (D.tile k).localAngle p := (Finset.sum_pair hij).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun k _ _ => (D.tile k).localAngle_nonneg p
theorem sum_ge_three {i j k : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : Plane) :
    (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p
      ≤ ∑ l, (D.tile l).localAngle p := by
  have h : ({i, j, k} : Finset (Fin N)).sum (fun l => (D.tile l).localAngle p)
      = (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p := by
    rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_pair hjk, add_assoc]
  rw [← h]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun l _ _ => (D.tile l).localAngle_nonneg p
theorem interior_of_two_openSegment {i j : Fin N} (hij : i ≠ j) {m m' : Fin 3} {p : Plane}
    (hi : p ∈ openSegment ℝ ((D.tile i).pts m) ((D.tile i).pts (m + 1)))
    (hj : p ∈ openSegment ℝ ((D.tile j).pts m') ((D.tile j).pts (m' + 1))) :
    p ∈ interior D.target.carrier := by
  apply mem_interior_of_sum_gt D
  have := sum_ge_two D hij p
  rw [Tri.localAngle_openSegment _ m hi, Tri.localAngle_openSegment _ m' hj] at this
  linarith [Real.pi_pos]
theorem interior_of_vertex_openSegment {i j : Fin N} {k m : Fin 3} {p : Plane}
    (hi : (D.tile i).pts k = p)
    (hj : p ∈ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1))) :
    p ∈ interior D.target.carrier := by
  have hij : i ≠ j := by
    rintro rfl
    exact Tri.vertex_not_mem_openSegment _ k m (hi ▸ hj)
  apply mem_interior_of_sum_gt D
  have := sum_ge_two D hij p
  rw [← hi, Tri.localAngle_vertex, hi, Tri.localAngle_openSegment _ m hj] at this
  have hc := Erdos634.MarchFlank.cornerAngle_pos (D.tile i) k
  rw [hi] at hc
  linarith
theorem openSegment_tile_unique {i j j' : Fin N} {k m m' : Fin 3} {p : Plane}
    (hi : (D.tile i).pts k = p)
    (hj : p ∈ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)))
    (hj' : p ∈ openSegment ℝ ((D.tile j').pts m') ((D.tile j').pts (m' + 1))) : j = j' := by
  by_contra hjj
  have hij : i ≠ j := by
    rintro rfl
    exact Tri.vertex_not_mem_openSegment _ k m (hi ▸ hj)
  have hij' : i ≠ j' := by
    rintro rfl
    exact Tri.vertex_not_mem_openSegment _ k m' (hi ▸ hj')
  have hsum := sum_ge_three D hij hij' hjj p
  rw [← hi, Tri.localAngle_vertex, hi, Tri.localAngle_openSegment _ m hj,
    Tri.localAngle_openSegment _ m' hj', D.sum_localAngle_eq] at hsum
  have hc := Erdos634.MarchFlank.cornerAngle_pos (D.tile i) k
  rw [hi] at hc
  linarith [Tri.localAngle_le_two_pi D.target p]
end Dissection
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
section Parity
variable {α : Type*} [DecidableEq α]
theorem even_card_of_pairing (R : α → α → Prop) (hsymm : ∀ x y, R x y → R y x)
    (hirr : ∀ x, ¬ R x x) (huniq : ∀ x y z, R x y → R x z → y = z) :
    ∀ n (A : Finset α), A.card = n → (∀ x ∈ A, ∃ y ∈ A, R x y) → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hA hpair
  rcases A.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · rw [← hA, Finset.card_empty]; exact ⟨0, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hpair x hx
  have hne : y ≠ x := fun h => hirr x (h ▸ hxy)
  set A' := (A.erase x).erase y with hA'def
  have hcard : A'.card + 2 = n := by
    rw [hA'def, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne, hy⟩),
      Finset.card_erase_of_mem hx, ← hA]
    have : 2 ≤ A.card := by
      have h2 : ({x, y} : Finset α) ⊆ A := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · rw [Finset.mem_singleton.mp hz]; exact hy
      have := Finset.card_le_card h2
      rwa [Finset.card_pair hne.symm] at this
    omega
  have hpair' : ∀ z ∈ A', ∃ w ∈ A', R z w := by
    intro z hz
    have hzy : z ≠ y := (Finset.mem_erase.mp hz).1
    have hzx : z ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
    have hzA : z ∈ A := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
    obtain ⟨w, hw, hzw⟩ := hpair z hzA
    refine ⟨w, ?_, hzw⟩
    have hwx : w ≠ x := by
      rintro rfl
      exact hzy (huniq w y z hxy (hsymm z w hzw)).symm
    have hwy : w ≠ y := by
      rintro rfl
      exact hzx (huniq w x z (hsymm x w hxy) (hsymm z w hzw)).symm
    exact Finset.mem_erase.mpr ⟨hwy, Finset.mem_erase.mpr ⟨hwx, hw⟩⟩
  have := ih A'.card (by omega) A' rfl hpair'
  rw [← hcard]
  exact this.add ⟨1, rfl⟩
theorem card_filter_mod_two (S : Finset α) (R : α → α → Prop) [DecidableRel R]
    (Θ : α → Prop) [DecidablePred Θ]
    (hsymm : ∀ x ∈ S, ∀ y ∈ S, R x y → R y x) (hirr : ∀ x, ¬ R x x)
    (huniq : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, R x y → R x z → y = z)
    (hnomix : ∀ x ∈ S, ∀ y ∈ S, R x y → Θ x → Θ y)
    (L : Finset α) (hL : ∀ x, x ∈ L ↔ x ∈ S ∧ Θ x ∧ ∀ y ∈ S, ¬ R x y) :
    (S.filter Θ).card % 2 = L.card % 2 := by
  have hLeq : L = S.filter fun x => Θ x ∧ ∀ y ∈ S, ¬ R x y := by
    ext x; rw [hL, Finset.mem_filter]
  subst hLeq
  set P := S.filter fun x => Θ x ∧ ∃ y ∈ S, R x y
  have hsplit : (S.filter Θ).card
      = (S.filter fun x => Θ x ∧ ∀ y ∈ S, ¬ R x y).card + P.card := by
    rw [← Finset.card_filter_add_card_filter_not (s := S.filter Θ) (fun x => ∀ y ∈ S, ¬ R x y),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    ext x
    simp only [P, Finset.mem_filter, not_forall, not_not, exists_prop]
  let R' : α → α → Prop := fun x y => x ∈ S ∧ y ∈ S ∧ R x y
  have hP : Even P.card := by
    refine even_card_of_pairing R' (fun x y h => ⟨h.2.1, h.1, hsymm x h.1 y h.2.1 h.2.2⟩)
      (fun x h => hirr x h.2.2)
      (fun x y z h1 h2 => huniq x h1.1 y h1.2.1 z h2.2.1 h1.2.2 h2.2.2) _ P rfl ?_
    intro x hx
    obtain ⟨hxS, hxΘ, y, hyS, hxy⟩ := Finset.mem_filter.mp hx
    refine ⟨y, Finset.mem_filter.mpr ⟨hyS, hnomix x hxS y hyS hxy hxΘ, x, hxS,
      hsymm x hxS y hyS hxy⟩, hxS, hyS, hxy⟩
  rw [hsplit, Nat.add_mod, Nat.even_iff.mp hP, add_zero, Nat.mod_mod]
end Parity
section EdgesAt
variable {N : ℕ} (D : Dissection N)
open Classical in
noncomputable def edgesAt (Q : Plane) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e => (D.tile e.1).pts e.2 = Q ∨ (D.tile e.1).pts (e.2 + 1) = Q
open Classical in
noncomputable def farEnd (Q : Plane) (e : Fin N × Fin 3) : Plane :=
  if (D.tile e.1).pts e.2 = Q then (D.tile e.1).pts (e.2 + 1) else (D.tile e.1).pts e.2
def SameRayAt (Q : Plane) (e e' : Fin N × Fin 3) : Prop :=
  ∃ t : ℝ, 0 < t ∧ farEnd D Q e' = AffineMap.lineMap Q (farEnd D Q e) t
theorem mem_edgesAt {Q : Plane} {e : Fin N × Fin 3} :
    e ∈ edgesAt D Q ↔ (D.tile e.1).pts e.2 = Q ∨ (D.tile e.1).pts (e.2 + 1) = Q := by
  classical
  simp [edgesAt]
theorem tri_pts_succ_ne (T : Tri) (k : Fin 3) : T.pts k ≠ T.pts (k + 1) := by
  intro h
  have := T.indep.injective h
  have hne : ∀ m : Fin 3, m ≠ m + 1 := by decide
  exact hne k this
theorem edgesAt_ends {Q : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q) :
    ((D.tile e.1).pts e.2 = Q ∧ (D.tile e.1).pts (e.2 + 1) = farEnd D Q e) ∨
    ((D.tile e.1).pts e.2 = farEnd D Q e ∧ (D.tile e.1).pts (e.2 + 1) = Q) := by
  classical
  rcases (mem_edgesAt D).mp he with h | h
  · left; exact ⟨h, by rw [farEnd, if_pos h]⟩
  · right
    have h' : (D.tile e.1).pts e.2 ≠ Q := fun h0 =>
      tri_pts_succ_ne (D.tile e.1) e.2 (h0.trans h.symm)
    exact ⟨by rw [farEnd, if_neg h'], h⟩
theorem farEnd_ne {Q : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q) : farEnd D Q e ≠ Q := by
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h2, ← h1]; exact (tri_pts_succ_ne _ _).symm
  · rw [← h1, ← h2]; exact tri_pts_succ_ne _ _
theorem edgesAt_edge {Q : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q) :
    (D.tile e.1).edge e.2 = segment ℝ Q (farEnd D Q e) := by
  rw [Tri.edge]
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, segment_symm]
theorem level_far {Q : Plane} {e : Fin N × Fin 3} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (he : e ∈ edgesAt D Q) (hQ : g Q = c) (hF : g (farEnd D Q e) = c) :
    g ((D.tile e.1).pts e.2) = c ∧ g ((D.tile e.1).pts (e.2 + 1)) = c := by
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact ⟨hQ, hF⟩
  · rw [h1, h2]; exact ⟨hF, hQ⟩
theorem not_mem_both_chains {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {e : Fin N × Fin 3}
    (h1 : e ∈ D.lineChain g c) (h2 : e ∈ D.lineChain (-g) (-c)) : False := by
  obtain ⟨a1, a2, a3⟩ := Dissection.mem_lineChain.mp h1
  obtain ⟨-, -, b3⟩ := Dissection.mem_lineChain.mp h2
  have h3 : g ((D.tile e.1).pts (e.2 + 2)) = c := by
    have := b3 (e.2 + 2)
    simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
    exact le_antisymm (a3 _) this
  obtain ⟨t, ht⟩ := eq_lineMap_of_level hg (tri_pts_succ_ne (D.tile e.1) e.2) a1 a2 h3
  have hc := congrArg ((D.tile e.1).basis.coord (e.2 + 2)) ht
  rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex, Tri.coord_vertex] at hc
  have n1 : ∀ k : Fin 3, ¬ (k + 2 = k) := by decide
  have n2 : ∀ k : Fin 3, ¬ (k + 2 = k + 1) := by decide
  simp [n1 e.2, n2 e.2] at hc
theorem edgesAt_chain {Q : Plane} {e : Fin N × Fin 3} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (he : e ∈ edgesAt D Q) (hQ : g Q = c) (hF : g (farEnd D Q e) = c) :
    e ∈ D.lineChain g c ∨ e ∈ D.lineChain (-g) (-c) := by
  obtain ⟨a1, a2⟩ := level_far D he hQ hF
  rcases le_total (g ((D.tile e.1).pts (e.2 + 2))) c with h | h
  · left
    refine Dissection.mem_lineChain.mpr ⟨a1, a2, fun i => ?_⟩
    rcases fin3_cases3 i e.2 with rfl | rfl | rfl
    · exact a1.le
    · exact a2.le
    · exact h
  · right
    refine Dissection.mem_lineChain.mpr ⟨by simp [a1], by simp [a2], fun i => ?_⟩
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    rcases fin3_cases3 i e.2 with rfl | rfl | rfl
    · exact a1.ge
    · exact a2.ge
    · exact h
theorem ray_level {Q F : Plane} (hQF : F ≠ Q) :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g Q = c ∧ g F = c := by
  refine ⟨crossL (F - Q), cross (F - Q) Q, crossL_ne_zero (sub_ne_zero.mpr hQF), rfl, ?_⟩
  rw [crossL_apply]
  have h := cross_sub_right (F - Q) F Q
  rw [cross_self] at h
  linarith
theorem mem_edge_of_ray {Q F : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q) {t : ℝ}
    (hF : farEnd D Q e = AffineMap.lineMap Q F t) {s : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) :
    AffineMap.lineMap Q F s ∈ (D.tile e.1).edge e.2 := by
  rw [edgesAt_edge D he, hF]
  have h0 : AffineMap.lineMap Q F (0 : ℝ) = Q := AffineMap.lineMap_apply_zero Q F
  have : segment ℝ Q (AffineMap.lineMap Q F t) = AffineMap.lineMap Q F '' segment ℝ 0 t := by
    rw [image_segment, h0]
  rw [this, segment_eq_Icc (hs0.trans hst)]
  exact ⟨s, ⟨hs0, hst⟩, rfl⟩
theorem lineMap_lineMap_eq {Q F : Plane} (t s : ℝ) :
    AffineMap.lineMap Q (AffineMap.lineMap Q F t) s = AffineMap.lineMap Q F (s * t) := by
  simp only [AffineMap.lineMap_apply_module', smul_smul, add_sub_cancel_right]
theorem sameRayAt_symm {Q : Plane} {e e' : Fin N × Fin 3} (h : SameRayAt D Q e e') : SameRayAt D Q e' e := by
  obtain ⟨t, ht, hF⟩ := h
  refine ⟨t⁻¹, inv_pos.mpr ht, ?_⟩
  rw [hF, lineMap_lineMap_eq, inv_mul_cancel₀ ht.ne', AffineMap.lineMap_apply_one]
theorem sameRayAt_unique {Q : Plane} {e e' e'' : Fin N × Fin 3} (he : e ∈ edgesAt D Q)
    (he' : e' ∈ edgesAt D Q) (he'' : e'' ∈ edgesAt D Q) (h1 : e' ≠ e) (h2 : e'' ≠ e)
    (h3 : e' ≠ e'') (r1 : SameRayAt D Q e e') (r2 : SameRayAt D Q e e'') : False := by
  obtain ⟨t', ht', hF'⟩ := r1
  obtain ⟨t'', ht'', hF''⟩ := r2
  set F := farEnd D Q e
  obtain ⟨g, c, hg, hgQ, hgF⟩ := ray_level (farEnd_ne D he)
  set s := min 1 (min t' t'') with hsdef
  have hs : 0 < s := lt_min one_pos (lt_min ht' ht'')
  have hy : ∀ x ∈ edgesAt D Q, ∀ t : ℝ, s ≤ t → farEnd D Q x = AffineMap.lineMap Q F t →
      Q ∈ (D.tile x.1).edge x.2 ∧ AffineMap.lineMap Q F s ∈ (D.tile x.1).edge x.2 := by
    intro x hx t hst ht
    refine ⟨?_, mem_edge_of_ray D hx ht hs.le hst⟩
    rw [edgesAt_edge D hx]; exact left_mem_segment ℝ _ _
  have y0 := hy e he 1 (min_le_left _ _) (AffineMap.lineMap_apply_one Q F).symm
  have y1 := hy e' he' t' ((min_le_right _ _).trans (min_le_left _ _)) hF'
  have y2 := hy e'' he'' t'' ((min_le_right _ _).trans (min_le_right _ _)) hF''
  have hyQ : AffineMap.lineMap Q F s ≠ Q := by
    intro h
    have : AffineMap.lineMap Q F s = (AffineMap.lineMap Q F (0 : ℝ) : Plane) := by
      rw [h, AffineMap.lineMap_apply_zero]
    exact hs.ne' (AffineMap.lineMap_injective ℝ (farEnd_ne D he).symm this)
  have hlev : ∀ x ∈ edgesAt D Q, (∃ t : ℝ, farEnd D Q x = AffineMap.lineMap Q F t) →
      x ∈ D.lineChain g c ∨ x ∈ D.lineChain (-g) (-c) := by
    rintro x hx ⟨t, ht⟩
    exact edgesAt_chain D hx hgQ (by rw [ht]; exact level_lineMap hgQ hgF t)
  have c0 := hlev e he ⟨1, (AffineMap.lineMap_apply_one Q F).symm⟩
  have c1 := hlev e' he' ⟨t', hF'⟩
  have c2 := hlev e'' he'' ⟨t'', hF''⟩
  have key : ∀ {g' : Plane →ₗ[ℝ] ℝ} {c' : ℝ}, g' ≠ 0 → ∀ x y : Fin N × Fin 3,
      (Q ∈ (D.tile x.1).edge x.2 ∧ AffineMap.lineMap Q F s ∈ (D.tile x.1).edge x.2) →
      (Q ∈ (D.tile y.1).edge y.2 ∧ AffineMap.lineMap Q F s ∈ (D.tile y.1).edge y.2) →
      x ≠ y → x ∈ D.lineChain g' c' → y ∈ D.lineChain g' c' → False := by
    intro g' c' hg' x y hx hy' hxy hxc hyc
    exact hxy (lineChain_eq_of_two D hg' hxc hyc hyQ.symm ⟨hx.1, hy'.1⟩ ⟨hx.2, hy'.2⟩)
  have hng : -g ≠ 0 := neg_ne_zero.mpr hg
  rcases c0 with c0 | c0 <;> rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2
  · exact key hg e e' y0 y1 h1.symm c0 c1
  · exact key hg e e' y0 y1 h1.symm c0 c1
  · exact key hg e e'' y0 y2 h2.symm c0 c2
  · exact key hng e' e'' y1 y2 h3 c1 c2
  · exact key hg e' e'' y1 y2 h3 c1 c2
  · exact key hng e e'' y0 y2 h2.symm c0 c2
  · exact key hng e e' y0 y1 h1.symm c0 c1
  · exact key hng e e' y0 y1 h1.symm c0 c1
theorem lonely_openSegment {Q : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q)
    {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) (hgQ : g Q = c) (hgF : g (farEnd D Q e) = c)
    (hec : e ∈ D.lineChain g c)
    (hlonely : ∀ e' ∈ edgesAt D Q, e' ≠ e → ¬ SameRayAt D Q e e')
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (hint : AffineMap.lineMap Q (farEnd D Q e) τ ∈ interior D.target.carrier) :
    ∃ e₂ ∈ D.lineChain (-g) (-c),
      Q ∈ openSegment ℝ ((D.tile e₂.1).pts e₂.2) ((D.tile e₂.1).pts (e₂.2 + 1)) := by
  set F := farEnd D Q e
  have hQF : Q ≠ F := (farEnd_ne D he).symm
  have hng : -g ≠ 0 := neg_ne_zero.mpr hg
  have hnQ : (-g) Q = -c := by simp [hgQ]
  have hnF : (-g) F = -c := by simp [hgF]
  have hL0 : AffineMap.lineMap Q F (0 : ℝ) = Q := AffineMap.lineMap_apply_zero Q F
  have hQt : Q ∈ D.target.carrier := by
    rw [← D.covers]
    refine Set.mem_iUnion.mpr ⟨e.1, ?_⟩
    have : Q ∈ (D.tile e.1).edge e.2 := by rw [edgesAt_edge D he]; exact left_mem_segment ℝ _ _
    exact (D.tile e.1).edge_subset_carrier e.2 this
  have hseg : openSegment ℝ (AffineMap.lineMap Q F (0 : ℝ)) (AffineMap.lineMap Q F τ)
      ⊆ interior D.target.carrier := by
    rw [hL0]
    exact D.target.convex.openSegment_closure_interior_subset_interior (subset_closure hQt) hint
  have hwall : ∀ y ∈ openSegment ℝ (AffineMap.lineMap Q F (0 : ℝ)) (AffineMap.lineMap Q F τ),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    rw [← image_openSegment, openSegment_eq_Ioo hτ.1] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact D.edge_point_not_interior (mem_edge_of_ray D he (t := 1)
      (AffineMap.lineMap_apply_one Q F).symm hs.1.le (hs.2.le.trans hτ.2.le))
  obtain ⟨e₂, he₂, hlo, hhi⟩ := exists_interval_right (D.lineChain (-g) (-c))
    (fun x => edgeLo Q F (D.tile x.1) x.2) (fun x => edgeHi Q F (D.tile x.1) x.2) 0
    hτ.1 (vertex_params_finite D hQF) (fun y hy hyv => by
      rw [zero_add] at hy
      exact wall_cover_param D hng hQF hnQ hnF hτ.1 hseg hwall hy hyv)
  obtain ⟨n1, n2⟩ := lineChain_ends D he₂
  have n1' : g ((D.tile e₂.1).pts e₂.2) = c := by simpa using n1
  have n2' : g ((D.tile e₂.1).pts (e₂.2 + 1)) = c := by simpa using n2
  rcases hlo.lt_or_eq with hlo | hlo
  · refine ⟨e₂, he₂, ?_⟩
    rw [← hL0]
    exact (lineMap_mem_openSegment_iff hg hQF hgQ hgF _ _ n1' n2' 0).mpr ⟨hlo, hhi⟩
  · exfalso
    have hne : e₂ ≠ e := fun h => not_mem_both_chains D hg hec (h ▸ he₂)
    have e1 := eq_lineMap_lineParam hg hQF hgQ hgF n1'
    have e2 := eq_lineMap_lineParam hg hQF hgQ hgF n2'
    simp only [edgeLo, edgeHi] at hlo hhi
    rcases min_choice (lineParam Q F ((D.tile e₂.1).pts e₂.2))
      (lineParam Q F ((D.tile e₂.1).pts (e₂.2 + 1))) with hm | hm
    · rw [hm] at hlo
      have hQ2 : (D.tile e₂.1).pts e₂.2 = Q := by rw [← e1, hlo, hL0]
      have hmem : e₂ ∈ edgesAt D Q := (mem_edgesAt D).mpr (Or.inl hQ2)
      refine hlonely e₂ hmem hne ⟨lineParam Q F ((D.tile e₂.1).pts (e₂.2 + 1)), ?_, ?_⟩
      · rcases max_choice (lineParam Q F ((D.tile e₂.1).pts e₂.2))
          (lineParam Q F ((D.tile e₂.1).pts (e₂.2 + 1))) with h' | h'
        · rw [h', hlo] at hhi; exact absurd hhi (lt_irrefl _)
        · rw [h'] at hhi; exact hhi
      · rw [farEnd, if_pos hQ2, e2]
    · rw [hm] at hlo
      have hQ2 : (D.tile e₂.1).pts (e₂.2 + 1) = Q := by rw [← e2, hlo, hL0]
      have hmem : e₂ ∈ edgesAt D Q := (mem_edgesAt D).mpr (Or.inr hQ2)
      have hQ1 : (D.tile e₂.1).pts e₂.2 ≠ Q := fun h0 =>
        tri_pts_succ_ne (D.tile e₂.1) e₂.2 (h0.trans hQ2.symm)
      refine hlonely e₂ hmem hne ⟨lineParam Q F ((D.tile e₂.1).pts e₂.2), ?_, ?_⟩
      · rcases max_choice (lineParam Q F ((D.tile e₂.1).pts e₂.2))
          (lineParam Q F ((D.tile e₂.1).pts (e₂.2 + 1))) with h' | h'
        · rw [h'] at hhi; exact hhi
        · rw [h', hlo] at hhi; exact absurd hhi (lt_irrefl _)
      · rw [farEnd, if_neg hQ1, e1]
end EdgesAt
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
def edgeType (φ : ℝ) (e : Fin N × Fin 3) : Prop :=
  (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = φ
theorem sum_two_edges (k0 : Fin 3) (f : Fin 3 → Prop) [DecidablePred f] :
    (∑ k : Fin 3, if (k = k0 ∨ k = k0 + 2) ∧ f k then (1 : ℕ) else 0)
      = (if f k0 then 1 else 0) + (if f (k0 + 2) then 1 else 0) := by
  rw [Fin.sum_univ_three]
  fin_cases k0 <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd,
    Fin.reduceEq, or_true, or_false, true_and, false_and, if_false, add_zero, zero_add,
    or_self] <;> split_ifs <;> simp
theorem card_three (k0 : Fin 3) (p : Fin 3 → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card
      = (if p k0 then 1 else 0) + (if p (k0 + 1) then 1 else 0) + (if p (k0 + 2) then 1 else 0) := by
  rw [Finset.card_filter, Fin.sum_univ_three]
  fin_cases k0 <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    Fin.reduceAdd] <;> split_ifs <;> simp
variable (hsep : AnglesSep D)
include hsep
theorem localAngle_ne_of_not_vertex {i : Fin N} {Q : Plane} (hQ : ∀ k, (D.tile i).pts k ≠ Q)
    {φ : ℝ} (hφ : φ = tileα D ∨ φ = tileβ D ∨ φ = tileγ D) : (D.tile i).localAngle Q ≠ φ := by
  have ⟨hv0, hinj⟩ := hsep
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) Q with ⟨j, hj, -⟩ | h | h | h
  · exact absurd hj.symm (hQ j)
  · rw [h]
    rcases hφ with rfl | rfl | rfl
    · exact (ne 4 0 (by decide))
    · exact (ne 4 1 (by decide))
    · exact (ne 4 2 (by decide))
  · rw [h]
    rcases hφ with rfl | rfl | rfl
    · exact (ne 3 0 (by decide))
    · exact (ne 3 1 (by decide))
    · exact (ne 3 2 (by decide))
  · rw [h]
    rcases hφ with rfl | rfl | rfl
    · exact (hv0 0).symm
    · exact (hv0 1).symm
    · exact (hv0 2).symm
open Classical in
theorem tile_marked_count (i : Fin N) (Q : Plane) {φ : ℝ}
    (hφ : φ = tileα D ∨ φ = tileβ D ∨ φ = tileγ D) :
    (∑ k : Fin 3, if ((D.tile i).pts k = Q ∨ (D.tile i).pts (k + 1) = Q) ∧
        edgeType D φ (i, k) then 1 else 0)
      + (if (D.tile i).localAngle Q = φ then 1 else 0)
      = (if (D.tile i).localAngle Q = tileα D then 1 else 0)
        + (if (D.tile i).localAngle Q = tileβ D then 1 else 0)
        + (if (D.tile i).localAngle Q = tileγ D then 1 else 0) := by
  have ⟨hv0, hinj⟩ := hsep
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  have hαβ : tileα D ≠ tileβ D := ne 0 1 (by decide)
  have hαγ : tileα D ≠ tileγ D := ne 0 2 (by decide)
  have hβγ : tileβ D ≠ tileγ D := ne 1 2 (by decide)
  by_cases hv : ∃ k0, (D.tile i).pts k0 = Q
  · obtain ⟨k0, hk0⟩ := hv
    have hinj' := (D.tile i).indep.injective
    have hcond : ∀ k : Fin 3, ((D.tile i).pts k = Q ∨ (D.tile i).pts (k + 1) = Q) ↔
        (k = k0 ∨ k = k0 + 2) := by
      intro k
      rw [← hk0]
      constructor
      · rintro (h | h)
        · exact Or.inl (hinj' h)
        · right
          have := hinj' h
          rw [← this]
          fin_cases k <;> rfl
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · right
          congr 1
          fin_cases k0 <;> rfl
    simp only [hcond]
    rw [sum_two_edges k0 (fun k => edgeType D φ (i, k))]
    have hloc : ∀ k, (D.tile i).localAngle ((D.tile i).pts k)
        = cornerAngle ((D.tile i).pts (k + 1)) ((D.tile i).pts k) ((D.tile i).pts (k + 2)) :=
      Tri.localAngle_vertex _
    obtain ⟨cα, cβ, cγ⟩ := tile_angle_count_sep D hsep i
    have hone : (if (D.tile i).localAngle ((D.tile i).pts k0) = φ then 1 else 0)
        + (if (D.tile i).localAngle ((D.tile i).pts (k0 + 1)) = φ then 1 else 0)
        + (if (D.tile i).localAngle ((D.tile i).pts (k0 + 2)) = φ then 1 else 0) = 1 := by
      have hc : (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
          ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = φ).card = 1 := by
        rcases hφ with rfl | rfl | rfl
        · exact cα
        · exact cβ
        · exact cγ
      simp only [← hloc] at hc
      have h3 := card_three k0 (fun k => (D.tile i).localAngle ((D.tile i).pts k) = φ)
      rw [hc] at h3
      exact h3.symm
    have hk2 : k0 + 2 + 2 = k0 + 1 := by fin_cases k0 <;> rfl
    have e1 : edgeType D φ (i, k0) ↔ (D.tile i).localAngle ((D.tile i).pts (k0 + 2)) = φ :=
      Iff.rfl
    have e2 : edgeType D φ (i, k0 + 2) ↔ (D.tile i).localAngle ((D.tile i).pts (k0 + 1)) = φ := by
      show (D.tile i).localAngle ((D.tile i).pts (k0 + 2 + 2)) = φ ↔ _
      rw [hk2]
    simp only [e1, e2]
    rw [← hk0]
    set θ := (D.tile i).localAngle ((D.tile i).pts k0)
    rcases localAngle_at_own_vertex_mem' D i k0 with h | h | h
    · have n1 : ¬ θ = tileβ D := fun h' => hαβ (h.symm.trans h')
      have n2 : ¬ θ = tileγ D := fun h' => hαγ (h.symm.trans h')
      rw [if_pos h, if_neg n1, if_neg n2]
      omega
    · have n1 : ¬ θ = tileα D := fun h' => hαβ (h'.symm.trans h)
      have n2 : ¬ θ = tileγ D := fun h' => hβγ (h.symm.trans h')
      rw [if_neg n1, if_pos h, if_neg n2]
      omega
    · have n1 : ¬ θ = tileα D := fun h' => hαγ (h'.symm.trans h)
      have n2 : ¬ θ = tileβ D := fun h' => hβγ (h'.symm.trans h)
      rw [if_neg n1, if_neg n2, if_pos h]
      omega
  · push Not at hv
    have h0 : ∀ k : Fin 3, ¬ (((D.tile i).pts k = Q ∨ (D.tile i).pts (k + 1) = Q) ∧
        edgeType D φ (i, k)) := fun k h => by
      rcases h.1 with h' | h'
      · exact hv k h'
      · exact hv (k + 1) h'
    simp only [h0, if_false, Finset.sum_const_zero, zero_add]
    rw [if_neg (localAngle_ne_of_not_vertex D hsep hv hφ),
      if_neg (localAngle_ne_of_not_vertex D hsep hv (Or.inl rfl)),
      if_neg (localAngle_ne_of_not_vertex D hsep hv (Or.inr (Or.inl rfl))),
      if_neg (localAngle_ne_of_not_vertex D hsep hv (Or.inr (Or.inr rfl)))]
open Classical in
theorem card_marked (Q : Plane) {φ : ℝ} (hφ : φ = tileα D ∨ φ = tileβ D ∨ φ = tileγ D) :
    ((edgesAt D.toDissection Q).filter (edgeType D φ)).card + angleCount D Q φ
      = angleCount D Q (tileα D) + angleCount D Q (tileβ D) + angleCount D Q (tileγ D) := by
  have hfilt : (edgesAt D.toDissection Q).filter (edgeType D φ) = Finset.univ.filter fun e =>
      ((D.tile e.1).pts e.2 = Q ∨ (D.tile e.1).pts (e.2 + 1) = Q) ∧ edgeType D φ e := by
    rw [edgesAt, Finset.filter_filter]
  rw [hfilt, Finset.card_filter, Fintype.sum_prod_type]
  simp only [angleCount, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => tile_marked_count D hsep i Q hφ
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
variable {N : ℕ} (D : Dissection N) (isθ : Fin N × Fin 3 → Prop)
structure LinkData (Q R : Plane) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) : Prop where
  ne : Q ≠ R
  hg : g ≠ 0
  hQ : g Q = c
  hR : g R = c
  cov : ∀ y ∈ openSegment ℝ Q R, ∃ e ∈ D.lineChain g c, y ∈ (D.tile e.1).edge e.2
  inner : ∀ e ∈ D.lineChain g c, ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q R).Nonempty →
    (D.tile e.1).edge e.2 ⊆ segment ℝ Q R ∧ isθ e
  start : ∀ e ∈ D.lineChain g c, isθ e → Q ∈ (D.tile e.1).edge e.2 →
    ∀ y ∈ (D.tile e.1).edge e.2, Q ∉ openSegment ℝ y R
  past : ∃ e ∈ D.lineChain g c, ¬ isθ e ∧ R ∈ (D.tile e.1).edge e.2 ∧
    ∃ y ∈ (D.tile e.1).edge e.2, R ∈ openSegment ℝ Q y
  across : ∃ e ∈ D.lineChain (-g) (-c),
    R ∈ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
def IsLink (Q R : Plane) : Prop := ∃ g c, LinkData D isθ Q R g c
theorem openSegment_param {Q R y : Plane} :
    y ∈ openSegment ℝ Q R ↔ ∃ t ∈ Ioo (0 : ℝ) 1, AffineMap.lineMap Q R t = y := by
  rw [openSegment_eq_image_lineMap]
  rfl
theorem segment_param {Q R y : Plane} :
    y ∈ segment ℝ Q R ↔ ∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap Q R t = y := by
  rw [segment_eq_image_lineMap]
  rfl
theorem lineMap_mem_openSegment_params {Q R : Plane} (hQR : Q ≠ R) {a b t : ℝ} :
    AffineMap.lineMap Q R t ∈
        openSegment ℝ (AffineMap.lineMap Q R a) (AffineMap.lineMap Q R b) ↔
      t ∈ openSegment ℝ a b := by
  rw [← image_openSegment]
  exact (AffineMap.lineMap_injective ℝ hQR).mem_set_image
theorem third_off_line (T : Tri) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) (k : Fin 3)
    (h1 : g (T.pts k) = c) (h2 : g (T.pts (k + 1)) = c) : g (T.pts (k + 2)) ≠ c := by
  intro h3
  obtain ⟨t, ht⟩ := eq_lineMap_of_level hg (tri_pts_succ_ne T k) h1 h2 h3
  have hc := congrArg (T.basis.coord (k + 2)) ht
  rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex, Tri.coord_vertex] at hc
  have n1 : ∀ k : Fin 3, ¬ (k + 2 = k) := by decide
  have n2 : ∀ k : Fin 3, ¬ (k + 2 = k + 1) := by decide
  simp [n1 k, n2 k] at hc
theorem chain_transfer {g₁ g₂ : Plane →ₗ[ℝ] ℝ} {c₁ c₂ : ℝ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {ε : Fin N × Fin 3} (h₁ : ε ∈ D.lineChain (-g₁) (-c₁)) (h₂ : ε ∈ D.lineChain (-g₂) (-c₂)) :
    (∀ y, g₂ y = c₂ → g₁ y = c₁) ∧ (∀ e ∈ D.lineChain g₂ c₂, e ∈ D.lineChain g₁ c₁) := by
  obtain ⟨j, m⟩ := ε
  set S := D.tile j
  have i1 : ∀ m : Fin 3, m + 2 + 1 = m := by decide
  have i2 : ∀ m : Fin 3, m + 2 + 2 = m + 1 := by decide
  have lev : ∀ {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}, g ≠ 0 → (j, m) ∈ D.lineChain (-g) (-c) →
      g (S.pts (m + 2 + 1)) = c ∧ g (S.pts (m + 2 + 2)) = c ∧ 0 < g (S.pts (m + 2)) - c := by
    intro g c hg hε
    obtain ⟨a1, a2, a3⟩ := Dissection.mem_lineChain.mp hε
    simp only [LinearMap.neg_apply, neg_inj] at a1 a2
    have b3 := a3 (m + 2)
    simp only [LinearMap.neg_apply, neg_le_neg_iff] at b3
    refine ⟨by rw [i1]; exact a1, by rw [i2]; exact a2, ?_⟩
    have := third_off_line S hg m a1 a2
    exact sub_pos.mpr (lt_of_le_of_ne b3 (Ne.symm this))
  obtain ⟨p1, p2, d1⟩ := lev hg₁ h₁
  obtain ⟨q1, q2, d2⟩ := lev hg₂ h₂
  have key1 := level_eq_coord S g₁ c₁ (m + 2) p1 p2
  have key2 := level_eq_coord S g₂ c₂ (m + 2) q1 q2
  have hon : ∀ y, g₂ y = c₂ → g₁ y = c₁ := by
    intro y hy
    have h2y := key2 y
    rw [hy, sub_self] at h2y
    have hc : S.basis.coord (m + 2) y = 0 := by
      rcases mul_eq_zero.mp h2y.symm with h | h
      · exact h
      · linarith
    have h1y := key1 y
    rw [hc, zero_mul] at h1y
    linarith
  refine ⟨hon, fun e he => ?_⟩
  obtain ⟨e1, e2, e3⟩ := Dissection.mem_lineChain.mp he
  refine Dissection.mem_lineChain.mpr ⟨hon _ e1, hon _ e2, fun i => ?_⟩
  have h2y := key2 ((D.tile e.1).pts i)
  have h1y := key1 ((D.tile e.1).pts i)
  have hle := e3 i
  have hc : S.basis.coord (m + 2) ((D.tile e.1).pts i) ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith
  nlinarith
namespace LinkData
variable {D isθ} {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
theorem mem_edge_iff (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c)
    (t : ℝ) : AffineMap.lineMap Q R t ∈ (D.tile e.1).edge e.2 ↔
      t ∈ Icc (edgeLo Q R (D.tile e.1) e.2) (edgeHi Q R (D.tile e.1) e.2) :=
  chain_mem_edge_iff D h.hg h.ne h.hQ h.hR he t
theorem params_of_inner (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) (hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ Q R) :
    0 ≤ edgeLo Q R (D.tile e.1) e.2 ∧ edgeHi Q R (D.tile e.1) e.2 ≤ 1 := by
  have hlt := chain_lo_lt_hi D h.hg h.ne h.hQ h.hR he
  have key : ∀ t ∈ Icc (edgeLo Q R (D.tile e.1) e.2) (edgeHi Q R (D.tile e.1) e.2),
      t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := segment_param.mp (hsub ((h.mem_edge_iff he t).mpr ht))
    rwa [← AffineMap.lineMap_injective ℝ h.ne hst]
  exact ⟨(key _ ⟨le_rfl, hlt.le⟩).1, (key _ ⟨hlt.le, le_rfl⟩).2⟩
theorem arrive (h : LinkData D isθ Q R g c) :
    ∃ e ∈ D.lineChain g c, isθ e ∧ 0 ≤ edgeLo Q R (D.tile e.1) e.2 ∧
      edgeLo Q R (D.tile e.1) e.2 < 1 ∧ edgeHi Q R (D.tile e.1) e.2 = 1 := by
  obtain ⟨e, he, hlo, hhi⟩ := exists_interval_left (D.lineChain g c)
    (fun x => edgeLo Q R (D.tile x.1) x.2) (fun x => edgeHi Q R (D.tile x.1) x.2) 1
    one_pos Set.finite_empty (fun y hy _ => by
      rw [sub_self] at hy
      obtain ⟨e, he, hye⟩ := h.cov _ (openSegment_param.mpr ⟨y, hy, rfl⟩)
      exact ⟨e, he, (h.mem_edge_iff he y).mp hye⟩)
  set m := max (edgeLo Q R (D.tile e.1) e.2) 0
  have hm1 : m < 1 := max_lt hlo one_pos
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q R).Nonempty := by
    refine ⟨AffineMap.lineMap Q R ((m + 1) / 2), (h.mem_edge_iff he _).mpr ⟨?_, ?_⟩,
      openSegment_param.mpr ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith [le_max_left (edgeLo Q R (D.tile e.1) e.2) 0]
    · linarith
    · linarith [le_max_right (edgeLo Q R (D.tile e.1) e.2) 0]
    · linarith
  obtain ⟨hsub, hθ⟩ := h.inner e he hmeet
  obtain ⟨h0, h1⟩ := h.params_of_inner he hsub
  exact ⟨e, he, hθ, h0, hlo, le_antisymm h1 hhi⟩
theorem end_of_param (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) :
    ∃ k : Fin 3, (D.tile e.1).pts k = AffineMap.lineMap Q R (edgeHi Q R (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  rcases max_choice (lineParam Q R ((D.tile e.1).pts e.2))
    (lineParam Q R ((D.tile e.1).pts (e.2 + 1))) with hm | hm
  · exact ⟨e.2, by rw [edgeHi, hm, eq_lineMap_lineParam h.hg h.ne h.hQ h.hR n1]⟩
  · exact ⟨e.2 + 1, by rw [edgeHi, hm, eq_lineMap_lineParam h.hg h.ne h.hQ h.hR n2]⟩
theorem end_vertex (h : LinkData D isθ Q R g c) : ∃ i k, (D.tile i).pts k = R := by
  obtain ⟨e, he, -, -, -, hhi⟩ := h.arrive
  obtain ⟨k, hk⟩ := h.end_of_param he
  exact ⟨e.1, k, by rw [hk, hhi, AffineMap.lineMap_apply_one]⟩
theorem end_interior (h : LinkData D isθ Q R g c) : R ∈ interior D.target.carrier := by
  obtain ⟨i, k, hk⟩ := h.end_vertex
  obtain ⟨e, -, he⟩ := h.across
  exact interior_of_vertex_openSegment D hk he
theorem leave (h : LinkData D isθ Q R g c) :
    ∃ e ∈ D.lineChain g c, ¬ isθ e ∧ edgeLo Q R (D.tile e.1) e.2 = 1 ∧
      1 < edgeHi Q R (D.tile e.1) e.2 := by
  obtain ⟨e, he, hθ, hRe, y, hy, hRy⟩ := h.past
  have hR1 : (1 : ℝ) ∈ Icc (edgeLo Q R (D.tile e.1) e.2) (edgeHi Q R (D.tile e.1) e.2) := by
    rw [← h.mem_edge_iff he, AffineMap.lineMap_apply_one]; exact hRe
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  obtain ⟨s, hs⟩ : ∃ s, AffineMap.lineMap Q R s = y := by
    have hgy : g y = c := D.lineChain_edge_subset he y hy
    exact ⟨_, eq_lineMap_lineParam h.hg h.ne h.hQ h.hR hgy⟩
  have hs1 : 1 < s := by
    have hseg : openSegment ℝ Q y = AffineMap.lineMap Q R '' openSegment ℝ 0 s := by
      rw [image_openSegment, AffineMap.lineMap_apply_zero, hs]
    rw [hseg] at hRy
    obtain ⟨t, ht, hteq⟩ := hRy
    have ht1 : t = 1 :=
      AffineMap.lineMap_injective ℝ h.ne (hteq.trans (AffineMap.lineMap_apply_one Q R).symm)
    rw [ht1] at ht
    rcases lt_trichotomy 0 s with h0 | h0 | h0
    · rw [openSegment_eq_Ioo h0] at ht; exact ht.2
    · rw [← h0, openSegment_same] at ht; norm_num at ht
    · rw [openSegment_symm, openSegment_eq_Ioo h0] at ht; linarith [ht.1, ht.2]
  have hsI : s ∈ Icc (edgeLo Q R (D.tile e.1) e.2) (edgeHi Q R (D.tile e.1) e.2) := by
    rw [← h.mem_edge_iff he, hs]; exact hy
  refine ⟨e, he, hθ, ?_, lt_of_lt_of_le hs1 hsI.2⟩
  by_contra hne
  have hlo : edgeLo Q R (D.tile e.1) e.2 < 1 := lt_of_le_of_ne hR1.1 hne
  set m := max (edgeLo Q R (D.tile e.1) e.2) 0
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q R).Nonempty := by
    refine ⟨AffineMap.lineMap Q R ((m + 1) / 2), (h.mem_edge_iff he _).mpr ⟨?_, ?_⟩,
      openSegment_param.mpr ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith [le_max_left (edgeLo Q R (D.tile e.1) e.2) 0, max_lt hlo one_pos]
    · linarith [max_lt hlo one_pos, hR1.2]
    · linarith [le_max_right (edgeLo Q R (D.tile e.1) e.2) 0]
    · linarith [max_lt hlo one_pos]
  exact hθ (h.inner e he hmeet).2
section Two
variable {Q₁ Q₂ : Plane} {g₁ g₂ : Plane →ₗ[ℝ] ℝ} {c₁ c₂ : ℝ}
theorem same_side (h1 : LinkData D isθ Q₁ R g₁ c₁) (h2 : LinkData D isθ Q₂ R g₂ c₂) :
    (∀ y, g₂ y = c₂ → g₁ y = c₁) ∧ (∀ e ∈ D.lineChain g₂ c₂, e ∈ D.lineChain g₁ c₁) := by
  obtain ⟨i, k, hik⟩ := h1.end_vertex
  obtain ⟨ε₁, hε₁, hR₁⟩ := h1.across
  obtain ⟨ε₂, hε₂, hR₂⟩ := h2.across
  have hj : ε₁.1 = ε₂.1 := openSegment_tile_unique D hik hR₁ hR₂
  obtain ⟨j, m⟩ := ε₁
  obtain ⟨j', m'⟩ := ε₂
  simp only at hj
  subst hj
  have hm : m = m' := Tri.openSegment_edge_unique (D.tile j) hR₁ hR₂
  subst hm
  exact chain_transfer D h1.hg h2.hg hε₁ hε₂
theorem not_between (h1 : LinkData D isθ Q₁ R g₁ c₁) (h2 : LinkData D isθ Q₂ R g₂ c₂)
    (hQ : Q₂ ∈ openSegment ℝ Q₁ R) : False := by
  obtain ⟨t2, ht2, hQ2⟩ := openSegment_param.mp hQ
  obtain ⟨e, he, hlo, hhi⟩ := exists_interval_left (D.lineChain g₁ c₁)
    (fun x => edgeLo Q₁ R (D.tile x.1) x.2) (fun x => edgeHi Q₁ R (D.tile x.1) x.2) t2
    ht2.1 Set.finite_empty (fun y hy _ => by
      rw [sub_self] at hy
      obtain ⟨e, he, hye⟩ := h1.cov _ (openSegment_param.mpr ⟨y, ⟨hy.1, hy.2.trans ht2.2⟩, rfl⟩)
      exact ⟨e, he, (h1.mem_edge_iff he y).mp hye⟩)
  set m := max (edgeLo Q₁ R (D.tile e.1) e.2) 0
  have hm : m < t2 := max_lt hlo ht2.1
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q₁ R).Nonempty := by
    refine ⟨AffineMap.lineMap Q₁ R ((m + t2) / 2), (h1.mem_edge_iff he _).mpr ⟨?_, ?_⟩,
      openSegment_param.mpr ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith [le_max_left (edgeLo Q₁ R (D.tile e.1) e.2) 0]
    · linarith
    · linarith [le_max_right (edgeLo Q₁ R (D.tile e.1) e.2) 0]
    · linarith [ht2.2]
  obtain ⟨-, hθ⟩ := h1.inner e he hmeet
  have he2 : e ∈ D.lineChain g₂ c₂ := (same_side h2 h1).2 e he
  refine h2.start e he2 hθ ?_ (AffineMap.lineMap Q₁ R (edgeLo Q₁ R (D.tile e.1) e.2))
    ((h1.mem_edge_iff he _).mpr ⟨le_rfl, (hlo.trans_le hhi).le⟩) ?_
  · rw [← hQ2]; exact (h1.mem_edge_iff he _).mpr ⟨hlo.le, hhi⟩
  · rw [← hQ2]
    have := (lineMap_mem_openSegment_params h1.ne (a := edgeLo Q₁ R (D.tile e.1) e.2) (b := 1)
      (t := t2)).mpr (by rw [openSegment_eq_Ioo (hlo.trans ht2.2)]; exact ⟨hlo, ht2.2⟩)
    rwa [AffineMap.lineMap_apply_one] at this
theorem not_opposite (h1 : LinkData D isθ Q₁ R g₁ c₁) (h2 : LinkData D isθ Q₂ R g₂ c₂)
    {t2 : ℝ} (ht2 : 1 < t2) (hQ2 : AffineMap.lineMap Q₁ R t2 = Q₂) : False := by
  obtain ⟨e, he, hθ, hlo, hhi⟩ := h1.leave
  have he2 : e ∈ D.lineChain g₂ c₂ := (same_side h2 h1).2 e he
  set s := (1 + min (edgeHi Q₁ R (D.tile e.1) e.2) t2) / 2
  have hs1 : 1 < s := by
    have := lt_min hhi ht2
    simp only [s]; linarith
  have hs2 : s < min (edgeHi Q₁ R (D.tile e.1) e.2) t2 := by
    have := lt_min hhi ht2
    simp only [s]; linarith
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q₂ R).Nonempty := by
    refine ⟨AffineMap.lineMap Q₁ R s, (h1.mem_edge_iff he _).mpr
      ⟨by rw [hlo]; exact hs1.le, (hs2.trans_le (min_le_left _ _)).le⟩, ?_⟩
    rw [← hQ2, openSegment_symm]
    have := (lineMap_mem_openSegment_params h1.ne (a := 1) (b := t2) (t := s)).mpr
      (by rw [openSegment_eq_Ioo ht2]; exact ⟨hs1, hs2.trans_le (min_le_right _ _)⟩)
    rwa [AffineMap.lineMap_apply_one] at this
  exact hθ (h2.inner e he2 hmeet).2
end Two
end LinkData
theorem link_unique {Q₁ Q₂ R : Plane} (h1 : IsLink D isθ Q₁ R) (h2 : IsLink D isθ Q₂ R) :
    Q₁ = Q₂ := by
  obtain ⟨g₁, c₁, h1⟩ := h1
  obtain ⟨g₂, c₂, h2⟩ := h2
  have hon := (h1.same_side h2).1 Q₂ h2.hQ
  obtain ⟨t2, ht2⟩ := eq_lineMap_of_level h1.hg h1.ne h1.hQ h1.hR hon
  rcases lt_trichotomy t2 0 with h0 | h0 | h0
  · exfalso
    refine h2.not_between h1 ?_
    rw [ht2]
    have := (lineMap_mem_openSegment_params h1.ne (a := t2) (b := 1) (t := 0)).mpr
      (by rw [openSegment_eq_Ioo (h0.trans one_pos)]; exact ⟨h0, one_pos⟩)
    rwa [AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero] at this
  · rw [ht2, h0, AffineMap.lineMap_apply_zero]
  · rcases lt_trichotomy t2 1 with h1' | h1' | h1'
    · exact (h1.not_between h2 (openSegment_param.mpr ⟨t2, ⟨h0, h1'⟩, ht2.symm⟩)).elim
    · exact absurd (by rw [ht2, h1', AffineMap.lineMap_apply_one]) h2.ne
    · exact (h1.not_opposite h2 h1' ht2.symm).elim
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
theorem Tri.lineMap_mem_interior (T : Tri) (m : Fin 3) {Q Z : Plane}
    (hQ : Q ∈ openSegment ℝ (T.pts m) (T.pts (m + 1))) (hZ : 0 < T.basis.coord (m + 2) Z) :
    ∃ τ₀ > (0 : ℝ), ∀ τ, 0 < τ → τ < τ₀ → AffineMap.lineMap Q Z τ ∈ interior T.carrier := by
  obtain ⟨h0, h1, h2⟩ := Tri.coord_openSegment T m hQ
  obtain ⟨ε0, hε0, hε⟩ := exists_small_pos (b := T.basis.coord m Z - T.basis.coord m Q) h0
  obtain ⟨ε1, hε1, hε'⟩ :=
    exists_small_pos (b := T.basis.coord (m + 1) Z - T.basis.coord (m + 1) Q) h1
  refine ⟨min ε0 ε1, lt_min hε0 hε1, fun τ hτ hτ' => ?_⟩
  rw [Tri.mem_interior_iff_coord_pos]
  intro j
  rw [Tri.coord_lineMap]
  rcases fin3_cases3 j m with rfl | rfl | rfl
  · exact hε τ hτ (lt_of_lt_of_le hτ' (min_le_left _ _))
  · exact hε' τ hτ (lt_of_lt_of_le hτ' (min_le_right _ _))
  · rw [h2, sub_zero, zero_add]; exact mul_pos hτ hZ
theorem tile_side_of_openSegment {N : ℕ} (D : Dissection N) {j : Fin N} {m : Fin 3} {Q : Plane}
    (hQ : Q ∈ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)))
    {i : Fin N} (hij : i ≠ j) (hQi : Q ∈ (D.tile i).carrier) :
    ∀ z ∈ (D.tile i).carrier, (D.tile j).basis.coord (m + 2) z ≤ 0 := by
  intro z hz
  by_contra hpos
  push Not at hpos
  obtain ⟨τ0, hτ0, hint⟩ := Tri.lineMap_mem_interior (D.tile j) m hQ hpos
  set τ := min τ0 1 / 2
  have hτ : 0 < τ := by have := lt_min hτ0 one_pos; simp only [τ]; linarith
  have hττ : τ < τ0 := by have := min_le_left τ0 1; simp only [τ]; linarith
  have hτ1 : τ ≤ 1 := by have := min_le_right τ0 1; simp only [τ]; linarith
  have hyS := hint τ hτ hττ
  have hyT : AffineMap.lineMap Q z τ ∈ (D.tile i).carrier := by
    refine (D.tile i).convex.segment_subset hQi hz ?_
    rw [segment_eq_image_lineMap]
    exact ⟨τ, ⟨hτ.le, hτ1⟩, rfl⟩
  have hcl : AffineMap.lineMap Q z τ ∈ closure (interior (D.tile i).carrier) := by
    rw [tri_closure_interior]; exact hyT
  obtain ⟨w, hwS, hwT⟩ := mem_closure_iff.mp hcl _ isOpen_interior hyS
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hwT hwS
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
variable {N : ℕ} (D : Dissection N) (isθ : Fin N × Fin 3 → Prop)
theorem edgesAt_params {Q F : Plane} (hQF : Q ≠ F) {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q)
    {t : ℝ} (ht : 0 < t) (hfar : farEnd D Q e = AffineMap.lineMap Q F t) :
    edgeLo Q F (D.tile e.1) e.2 = 0 ∧ edgeHi Q F (D.tile e.1) e.2 = t := by
  have h0 : lineParam Q F Q = 0 := by
    have := lineParam_lineMap hQF 0
    rwa [AffineMap.lineMap_apply_zero] at this
  have ht' : lineParam Q F (farEnd D Q e) = t := by rw [hfar, lineParam_lineMap hQF]
  rw [edgeLo, edgeHi]
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, h0, ht', min_eq_left ht.le, max_eq_right ht.le]; exact ⟨rfl, rfl⟩
  · rw [h1, h2, h0, ht', min_eq_right ht.le, max_eq_left ht.le]; exact ⟨rfl, rfl⟩
theorem tile_ne_of_chains {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {e₁ e₂ : Fin N × Fin 3}
    (h1 : e₁ ∈ D.lineChain g c) (h2 : e₂ ∈ D.lineChain (-g) (-c)) : e₁.1 ≠ e₂.1 := by
  intro h
  obtain ⟨a1, a2, a3⟩ := Dissection.mem_lineChain.mp h1
  obtain ⟨-, -, b3⟩ := Dissection.mem_lineChain.mp h2
  apply third_off_line (D.tile e₁.1) hg e₁.2 a1 a2
  have := b3 (e₁.2 + 2)
  rw [← h] at this
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
  exact le_antisymm (a3 _) this
theorem pair_line {Q : Plane} {e₁ e₂ : Fin N × Fin 3} (he₁ : e₁ ∈ edgesAt D Q)
    (he₂ : e₂ ∈ edgesAt D Q) (hne : e₂ ≠ e₁) (hray : SameRayAt D Q e₁ e₂) :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (t₂ : ℝ), g ≠ 0 ∧ g Q = c ∧ g (farEnd D Q e₁) = c ∧
      e₁ ∈ D.lineChain g c ∧ e₂ ∈ D.lineChain (-g) (-c) ∧ 0 < t₂ ∧
      farEnd D Q e₂ = AffineMap.lineMap Q (farEnd D Q e₁) t₂ := by
  obtain ⟨t₂, ht₂, hF₂⟩ := hray
  set F := farEnd D Q e₁
  have hQF : Q ≠ F := (farEnd_ne D he₁).symm
  obtain ⟨g₀, c₀, hg₀, hQ₀, hF₀⟩ := ray_level (farEnd_ne D he₁)
  obtain ⟨g, c, hg, hQ, hF, h1⟩ : ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g Q = c ∧ g F = c ∧
      e₁ ∈ D.lineChain g c := by
    rcases edgesAt_chain D he₁ hQ₀ hF₀ with h | h
    · exact ⟨g₀, c₀, hg₀, hQ₀, hF₀, h⟩
    · exact ⟨-g₀, -c₀, neg_ne_zero.mpr hg₀, by simp [hQ₀], by simp only [LinearMap.neg_apply, F, hF₀], h⟩
  refine ⟨g, c, t₂, hg, hQ, hF, h1, ?_, ht₂, hF₂⟩
  have hF2 : g (farEnd D Q e₂) = c := by rw [hF₂]; exact level_lineMap hQ hF t₂
  rcases edgesAt_chain D he₂ hQ hF2 with h2 | h2
  · exfalso
    have hs : 0 < min 1 t₂ := lt_min one_pos ht₂
    have hm1 := mem_edge_of_ray D he₁ (t := 1) (AffineMap.lineMap_apply_one Q F).symm hs.le
      (min_le_left _ _)
    have hm2 := mem_edge_of_ray D he₂ hF₂ hs.le (min_le_right _ _)
    have hQ1 : Q ∈ (D.tile e₁.1).edge e₁.2 := by
      rw [edgesAt_edge D he₁]; exact left_mem_segment ℝ _ _
    have hQ2 : Q ∈ (D.tile e₂.1).edge e₂.2 := by
      rw [edgesAt_edge D he₂]; exact left_mem_segment ℝ _ _
    have hneq : Q ≠ AffineMap.lineMap Q F (min 1 t₂) := by
      intro h
      have : AffineMap.lineMap Q F (0 : ℝ) = AffineMap.lineMap Q F (min 1 t₂) := by
        rw [AffineMap.lineMap_apply_zero]; exact h
      exact hs.ne (AffineMap.lineMap_injective ℝ hQF this)
    exact hne (lineChain_eq_of_two D hg h1 h2 hneq ⟨hQ1, hQ2⟩ ⟨hm1, hm2⟩).symm
  · exact h2
theorem param_dich {lo hi T : ℝ} (h : ∀ x ∈ Ioo 0 T, x ∈ Icc lo hi → 0 ≤ lo ∧ hi ≤ T) :
    Icc lo hi ⊆ Icc 0 T ∨ (Icc lo hi ∩ Icc 0 T).Subsingleton := by
  by_cases hx : ∃ x ∈ Ioo 0 T, x ∈ Icc lo hi
  · obtain ⟨x, hx, hxI⟩ := hx
    obtain ⟨h0, hT⟩ := h x hx hxI
    left
    exact fun y hy => ⟨h0.trans hy.1, hy.2.trans hT⟩
  · right
    push Not at hx
    intro a ha b hb
    by_contra hab
    apply hx ((a + b) / 2)
    · rcases lt_or_gt_of_ne hab with h' | h'
      · constructor <;> linarith [ha.2.1, hb.2.2]
      · constructor <;> linarith [ha.2.2, hb.2.1]
    · constructor <;> linarith [ha.1.1, hb.1.1, ha.1.2, hb.1.2]
theorem exists_pts_eq_hi {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {Q F : Plane} (hQF : Q ≠ F)
    (hQ : g Q = c) (hF : g F = c) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    ∃ k : Fin 3, (D.tile e.1).pts k = AffineMap.lineMap Q F (edgeHi Q F (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  rcases max_choice (lineParam Q F ((D.tile e.1).pts e.2))
    (lineParam Q F ((D.tile e.1).pts (e.2 + 1))) with hm | hm
  · exact ⟨e.2, by rw [edgeHi, hm, eq_lineMap_lineParam hg hQF hQ hF n1]⟩
  · exact ⟨e.2 + 1, by rw [edgeHi, hm, eq_lineMap_lineParam hg hQF hQ hF n2]⟩
theorem dich_of_param {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {Q F : Plane} (hQF : Q ≠ F)
    (hQ : g Q = c) (hF : g F = c) {T : ℝ} (hT : 0 < T)
    (hin : ∀ e ∈ D.lineChain g c, ∀ x ∈ Ioo 0 T,
      x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) →
        0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ T) :
    ∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ Q (AffineMap.lineMap Q F T) ∨
      ((D.tile e.1).edge e.2 ∩ segment ℝ Q (AffineMap.lineMap Q F T)).Subsingleton := by
  have hseg : AffineMap.lineMap Q F '' Icc 0 T = segment ℝ Q (AffineMap.lineMap Q F T) := by
    rw [← segment_eq_Icc hT.le, image_segment, AffineMap.lineMap_apply_zero]
  intro e he
  have himg : (D.tile e.1).edge e.2 =
      AffineMap.lineMap Q F '' Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) :=
    edge_eq_image hg hQF hQ hF _ _ (lineChain_ends D he).1 (lineChain_ends D he).2
  rw [himg, ← hseg]
  rcases param_dich (hin e he) with h | h
  · left; exact Set.image_mono h
  · right
    rw [← Set.image_inter (AffineMap.lineMap_injective ℝ hQF)]
    exact h.image _
structure TermSeg (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (Q R : Plane) : Prop where
  ne : Q ≠ R
  hg : g ≠ 0
  hQ : g Q = c
  hR : g R = c
  int : openSegment ℝ Q R ⊆ interior D.target.carrier
  wall : ∀ y ∈ openSegment ℝ Q R, ∀ i, y ∉ interior (D.tile i).carrier
  dich₁ : ∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ Q R ∨
    ((D.tile e.1).edge e.2 ∩ segment ℝ Q R).Subsingleton
  dich₂ : ∀ e ∈ D.lineChain (-g) (-c), (D.tile e.1).edge e.2 ⊆ segment ℝ Q R ∨
    ((D.tile e.1).edge e.2 ∩ segment ℝ Q R).Subsingleton
open Classical in
noncomputable def sideEdges (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (Q R : Plane) : Finset (Fin N × Fin 3) :=
  (D.lineChain g c).filter fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ Q R
theorem segment_level {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} {Q R : Plane} (hQ : g Q = c) (hR : g R = c) :
    segment ℝ Q R ⊆ {y | g y = c} := by
  rintro _ ⟨s, t, -, -, hst, rfl⟩
  simp only [Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul, hQ, hR]
  rw [← add_mul, hst, one_mul]
theorem TermSeg.sums {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} {Q R : Plane} (h : TermSeg D g c Q R) :
    ∑ e ∈ sideEdges D g c Q R, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = dist Q R ∧
    ∑ e ∈ sideEdges D (-g) (-c) Q R, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = dist Q R := by
  classical
  have hnQ : (-g) Q = -c := by simp [h.hQ]
  have hnR : (-g) R = -c := by simp [h.hR]
  refine ⟨?_, ?_⟩
  · unfold sideEdges
    convert wall_sum D g c h.hg h.ne (segment_level h.hQ h.hR) h.int h.wall h.dich₁
  · unfold sideEdges
    convert wall_sum D (-g) (-c) (neg_ne_zero.mpr h.hg) h.ne (segment_level hnQ hnR) h.int h.wall
      h.dich₂
def WallRel : Prop :=
  ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (Q R : Plane), TermSeg D g c Q R ∧
    (∀ e ∈ sideEdges D g c Q R, isθ e) ∧ ∃ e ∈ sideEdges D (-g) (-c) Q R, ¬ isθ e
theorem relation_of_wallRel (h : WallRel D isθ) :
    ∃ s₁ s₂ : Finset (Fin N × Fin 3), (∀ e ∈ s₁, isθ e) ∧ (∃ e ∈ s₂, ¬ isθ e) ∧
      ∑ e ∈ s₁, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        = ∑ e ∈ s₂, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
  obtain ⟨g, c, Q, R, ht, h1, h2⟩ := h
  exact ⟨_, _, h1, h2, ht.sums.1.trans ht.sums.2.symm⟩
set_option maxHeartbeats 4000000 in
open Classical in
theorem extend_link_wall {Q : Plane} {e₁ e₂ : Fin N × Fin 3} (he₁ : e₁ ∈ edgesAt D Q)
    (he₂ : e₂ ∈ edgesAt D Q) (hne : e₂ ≠ e₁) (hray : SameRayAt D Q e₁ e₂)
    (hθ₁ : isθ e₁) (hθ₂ : ¬ isθ e₂)
    (hback : ∀ e : Fin N × Fin 3, Q ∈ (D.tile e.1).edge e.2 →
      ∀ y ∈ (D.tile e.1).edge e.2, Q ∉ openSegment ℝ y (farEnd D Q e₁)) :
    (∃ R, IsLink D isθ Q R) ∨ WallRel D isθ := by
  obtain ⟨g, c, t₂, hg, hQ, hF, h1, h2, ht₂, hF₂⟩ := pair_line D he₁ he₂ hne hray
  set F := farEnd D Q e₁ with hFdef
  have hQF : Q ≠ F := (farEnd_ne D he₁).symm
  have hng : -g ≠ 0 := neg_ne_zero.mpr hg
  have hnQ : (-g) Q = -c := by simp [hQ]
  have hnF : (-g) F = -c := by simp only [LinearMap.neg_apply, hF]
  have hQ0 : AffineMap.lineMap Q F (0 : ℝ) = Q := AffineMap.lineMap_apply_zero Q F
  have mem₁ : ∀ e ∈ D.lineChain g c, ∀ t, AffineMap.lineMap Q F t ∈ (D.tile e.1).edge e.2 ↔
      t ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) :=
    fun e he t => chain_mem_edge_iff D hg hQF hQ hF he t
  have mem₂ : ∀ e ∈ D.lineChain (-g) (-c), ∀ t,
      AffineMap.lineMap Q F t ∈ (D.tile e.1).edge e.2 ↔
        t ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) :=
    fun e he t => chain_mem_edge_iff D hng hQF hnQ hnF he t
  have lt₁ : ∀ e ∈ D.lineChain g c, edgeLo Q F (D.tile e.1) e.2 < edgeHi Q F (D.tile e.1) e.2 :=
    fun e he => chain_lo_lt_hi D hg hQF hQ hF he
  have ov₁ : ∀ e ∈ D.lineChain g c, ∀ e' ∈ D.lineChain g c,
      max (edgeLo Q F (D.tile e.1) e.2) (edgeLo Q F (D.tile e'.1) e'.2)
        < min (edgeHi Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e'.1) e'.2) → e = e' :=
    fun e he e' he' h => lineChain_eq_of_overlap D hg hQF hQ hF he he' h
  have ov₂ : ∀ e ∈ D.lineChain (-g) (-c), ∀ e' ∈ D.lineChain (-g) (-c),
      max (edgeLo Q F (D.tile e.1) e.2) (edgeLo Q F (D.tile e'.1) e'.2)
        < min (edgeHi Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e'.1) e'.2) → e = e' :=
    fun e he e' he' h => lineChain_eq_of_overlap D hng hQF hnQ hnF he he' h
  obtain ⟨p₁lo, p₁hi⟩ := edgesAt_params D hQF he₁ one_pos (AffineMap.lineMap_apply_one Q F).symm
  obtain ⟨p₂lo, p₂hi⟩ := edgesAt_params D hQF he₂ ht₂ hF₂
  have back : ∀ e : Fin N × Fin 3, (∀ t, AffineMap.lineMap Q F t ∈ (D.tile e.1).edge e.2 ↔
      t ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2)) →
      edgeLo Q F (D.tile e.1) e.2 < 0 → edgeHi Q F (D.tile e.1) e.2 < 0 := by
    intro e hmem hlo
    by_contra hhi
    push Not at hhi
    have hQe : Q ∈ (D.tile e.1).edge e.2 := by
      have := (hmem 0).mpr ⟨hlo.le, hhi⟩
      rwa [hQ0] at this
    refine hback e hQe _ ((hmem _).mpr ⟨le_rfl, (hlo.trans_le hhi).le⟩) ?_
    have := (lineMap_mem_openSegment_params hQF (a := edgeLo Q F (D.tile e.1) e.2) (b := 1)
      (t := 0)).mpr (by rw [openSegment_eq_Ioo (hlo.trans one_pos)]; exact ⟨hlo, one_pos⟩)
    rwa [hQ0, AffineMap.lineMap_apply_one] at this
  let Good : ℝ → Prop := fun t => 0 < t ∧ ∀ x ∈ Icc (0 : ℝ) t, ∃ e ∈ D.lineChain g c, isθ e ∧
    0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ t ∧
    x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2)
  have good1 : Good 1 :=
    ⟨one_pos, fun x hx => ⟨e₁, h1, hθ₁, p₁lo.ge, p₁hi.le, by rw [p₁lo, p₁hi]; exact hx⟩⟩
  set Cand := ((D.lineChain g c).image fun e => edgeHi Q F (D.tile e.1) e.2).filter Good
  have h1C : (1 : ℝ) ∈ Cand := Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨e₁, h1, p₁hi⟩, good1⟩
  set T := Cand.max' ⟨1, h1C⟩ with hTdef
  have hTgood : Good T := (Finset.mem_filter.mp (Finset.max'_mem Cand ⟨1, h1C⟩)).2
  have hTpos : 0 < T := hTgood.1
  have hmax : ∀ t, Good t → t ∈ (D.lineChain g c).image (fun e => edgeHi Q F (D.tile e.1) e.2) →
      t ≤ T := fun t ht hti => Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hti, ht⟩)
  have inner₁ : ∀ e ∈ D.lineChain g c, ∀ x ∈ Ioo 0 T,
      x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) →
        isθ e ∧ 0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ T := by
    intro e he x hx hxe
    set S := (D.lineChain g c).filter fun e => isθ e ∧ 0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧
      edgeHi Q F (D.tile e.1) e.2 ≤ T
    have hcovS : ∀ y ∈ Icc 0 T, ∃ e' ∈ S,
        y ∈ Icc (edgeLo Q F (D.tile e'.1) e'.2) (edgeHi Q F (D.tile e'.1) e'.2) := by
      intro y hy
      obtain ⟨e', he', hθ', hlo', hhi', hye'⟩ := hTgood.2 y hy
      exact ⟨e', Finset.mem_filter.mpr ⟨he', hθ', hlo', hhi'⟩, hye'⟩
    suffices hS : e ∈ S from (Finset.mem_filter.mp hS).2
    rcases hxe.2.lt_or_eq with hxhi | hxhi
    · obtain ⟨e', he', hlo', hhi'⟩ := exists_interval_right S
        (fun e => edgeLo Q F (D.tile e.1) e.2) (fun e => edgeHi Q F (D.tile e.1) e.2) x
        (δ₀ := T - x) (by linarith [hx.2]) Set.finite_empty
        (fun y hy _ => hcovS y ⟨by linarith [hx.1, hy.1], by linarith [hy.2]⟩)
      have : e = e' := ov₁ e he e' (Finset.mem_filter.mp he').1
        (lt_of_le_of_lt (max_le hxe.1 hlo') (lt_min hxhi hhi'))
      rw [this]; exact he'
    · obtain ⟨e', he', hlo', hhi'⟩ := exists_interval_left S
        (fun e => edgeLo Q F (D.tile e.1) e.2) (fun e => edgeHi Q F (D.tile e.1) e.2) x
        (δ₀ := x) hx.1 Set.finite_empty
        (fun y hy _ => hcovS y ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩)
      have : e = e' := ov₁ e he e' (Finset.mem_filter.mp he').1
        (lt_of_lt_of_le (max_lt (by rw [hxhi]; exact lt₁ e he) hlo') (le_min hxhi.le hhi'))
      rw [this]; exact he'
  set R := AffineMap.lineMap Q F T with hRdef
  have hOS : openSegment ℝ Q R = AffineMap.lineMap Q F '' Ioo 0 T := by
    rw [← openSegment_eq_Ioo hTpos, image_openSegment, hQ0]
  have hSeg : segment ℝ Q R = AffineMap.lineMap Q F '' Icc 0 T := by
    rw [← segment_eq_Icc hTpos.le, image_segment, hQ0]
  have hQR : Q ≠ R := by
    intro h
    have : AffineMap.lineMap Q F (0 : ℝ) = AffineMap.lineMap Q F T := by rw [hQ0]; exact h
    exact hTpos.ne (AffineMap.lineMap_injective ℝ hQF this)
  have hRc : g R = c := level_lineMap hQ hF T
  obtain ⟨eR, heR, -, -, heRhi, heRT⟩ := hTgood.2 T ⟨hTpos.le, le_rfl⟩
  have hRhi : edgeHi Q F (D.tile eR.1) eR.2 = T := le_antisymm heRhi heRT.2
  obtain ⟨kR, hkR⟩ := exists_pts_eq_hi D hg hQF hQ hF heR
  rw [hRhi] at hkR
  have hRt : R ∈ D.target.carrier := by
    rw [← D.covers]
    exact Set.mem_iUnion.mpr ⟨eR.1, (D.tile eR.1).edge_subset_carrier eR.2 ((mem₁ eR heR T).mpr heRT)⟩
  have hT12 : e₁.1 ≠ e₂.1 := tile_ne_of_chains D hg h1 h2
  have near : ∀ τ : ℝ, 0 < τ → τ < 1 → τ < t₂ →
      AffineMap.lineMap Q F τ ∈ interior D.target.carrier := by
    intro τ h0 h1' h2'
    obtain ⟨a1, a2⟩ := lineChain_ends D h1
    obtain ⟨b1, b2⟩ := lineChain_ends D h2
    have ha := (lineMap_mem_openSegment_iff hg hQF hQ hF _ _ a1 a2 τ).mpr
      (by rw [p₁lo, p₁hi]; exact ⟨h0, h1'⟩)
    have hb := (lineMap_mem_openSegment_iff hng hQF hnQ hnF _ _ b1 b2 τ).mpr
      (by rw [p₂lo, p₂hi]; exact ⟨h0, h2'⟩)
    exact interior_of_two_openSegment D hT12 ha hb
  have hint : openSegment ℝ Q R ⊆ interior D.target.carrier := by
    rw [hOS]
    rintro _ ⟨x, hx, rfl⟩
    set τ := min (min x 1) t₂ / 2
    have hm : 0 < min (min x 1) t₂ := lt_min (lt_min hx.1 one_pos) ht₂
    have hτ0 : 0 < τ := by simp only [τ]; linarith
    have hτx : τ < x := by
      have := min_le_left (min x 1) t₂; have := min_le_left x 1; simp only [τ]; linarith
    have hτ1 : τ < 1 := by
      have := min_le_left (min x 1) t₂; have := min_le_right x 1; simp only [τ]; linarith
    have hτ2 : τ < t₂ := by
      have := min_le_right (min x 1) t₂; simp only [τ]; linarith
    have hxin : AffineMap.lineMap Q F x ∈ openSegment ℝ (AffineMap.lineMap Q F τ) R :=
      (lineMap_mem_openSegment_params hQF).mpr
        (by rw [openSegment_eq_Ioo (hτx.trans hx.2)]; exact ⟨hτx, hx.2⟩)
    exact D.target.convex.openSegment_interior_closure_subset_interior (near τ hτ0 hτ1 hτ2)
      (subset_closure hRt) hxin
  have hwall : ∀ y ∈ openSegment ℝ Q R, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    rw [hOS] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨e, he, -, -, -, hxe⟩ := hTgood.2 x ⟨hx.1.le, hx.2.le⟩
    exact D.edge_point_not_interior ((mem₁ e he x).mpr hxe)
  have hint0 : openSegment ℝ (AffineMap.lineMap Q F (0 : ℝ)) (AffineMap.lineMap Q F T)
      ⊆ interior D.target.carrier := by rw [hQ0]; exact hint
  have hwall0 : ∀ y ∈ openSegment ℝ (AffineMap.lineMap Q F (0 : ℝ)) (AffineMap.lineMap Q F T),
      ∀ i, y ∉ interior (D.tile i).carrier := by rw [hQ0]; exact hwall
  obtain ⟨ε, hε, hεlo, hεhi⟩ := exists_interval_left (D.lineChain (-g) (-c))
    (fun e => edgeLo Q F (D.tile e.1) e.2) (fun e => edgeHi Q F (D.tile e.1) e.2) T
    hTpos (vertex_params_finite D hQF) (fun y hy hyv => by
      rw [sub_self] at hy
      exact wall_cover_param D hng hQF hnQ hnF hTpos hint0 hwall0 hy hyv)
  rcases hεhi.lt_or_eq with hεhi | hεhi
  · 
    left
    refine ⟨R, g, c, ⟨hQR, hg, hQ, hRc, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro y hy
      rw [hOS] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨e, he, -, -, -, hxe⟩ := hTgood.2 x ⟨hx.1.le, hx.2.le⟩
      exact ⟨e, he, (mem₁ e he x).mpr hxe⟩
    · intro e he hmeet
      obtain ⟨y, hye, hyo⟩ := hmeet
      rw [hOS] at hyo
      obtain ⟨x, hx, rfl⟩ := hyo
      obtain ⟨hθ, hlo, hhi⟩ := inner₁ e he x hx ((mem₁ e he x).mp hye)
      refine ⟨?_, hθ⟩
      rw [edge_eq_image hg hQF hQ hF _ _ (lineChain_ends D he).1 (lineChain_ends D he).2, hSeg]
      exact Set.image_mono fun z hz => ⟨hlo.trans hz.1, hz.2.trans hhi⟩
    · intro e he _ hQe y hy hQy
      have hgy : g y = c := D.lineChain_edge_subset he y hy
      obtain ⟨s, rfl⟩ : ∃ s, AffineMap.lineMap Q F s = y :=
        ⟨_, eq_lineMap_lineParam hg hQF hQ hF hgy⟩
      have hs : s < 0 := by
        have hQy' : AffineMap.lineMap Q F (0 : ℝ) ∈
            openSegment ℝ (AffineMap.lineMap Q F s) (AffineMap.lineMap Q F T) := by
          rw [hQ0]; exact hQy
        have h0 := (lineMap_mem_openSegment_params hQF (a := s) (b := T) (t := 0)).mp hQy'
        rcases lt_trichotomy s T with h | h | h
        · rw [openSegment_eq_Ioo h] at h0; exact h0.1
        · rw [h, openSegment_same] at h0; exact absurd (Set.mem_singleton_iff.mp h0) hTpos.ne
        · rw [openSegment_symm, openSegment_eq_Ioo h] at h0; linarith [h0.1]
      refine hback e hQe _ hy ?_
      have := (lineMap_mem_openSegment_params hQF (a := s) (b := 1) (t := 0)).mpr
        (by rw [openSegment_eq_Ioo (hs.trans one_pos)]; exact ⟨hs, one_pos⟩)
      rwa [hQ0, AffineMap.lineMap_apply_one] at this
    · 
      have hRint : R ∈ interior D.target.carrier := by
        obtain ⟨b1, b2⟩ := lineChain_ends D hε
        have hRε := (lineMap_mem_openSegment_iff hng hQF hnQ hnF _ _ b1 b2 T).mpr ⟨hεlo, hεhi⟩
        exact interior_of_vertex_openSegment D hkR hRε
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior R hRint
      have hdQF : 0 < dist Q F := dist_pos.mpr hQF
      set δ₁ := min (edgeHi Q F (D.tile ε.1) ε.2 - T) (r / dist Q F) / 2 with hδ₁def
      have hδ₁ : 0 < δ₁ := by
        have : 0 < min (edgeHi Q F (D.tile ε.1) ε.2 - T) (r / dist Q F) :=
          lt_min (by linarith) (div_pos hr hdQF)
        simp only [δ₁]; linarith
      have hδ₁ε : T + δ₁ < edgeHi Q F (D.tile ε.1) ε.2 := by
        have := min_le_left (edgeHi Q F (D.tile ε.1) ε.2 - T) (r / dist Q F)
        simp only [δ₁]; linarith
      have hδ₁r : δ₁ * dist Q F < r := by
        have h := min_le_right (edgeHi Q F (D.tile ε.1) ε.2 - T) (r / dist Q F)
        have : δ₁ < r / dist Q F := by simp only [δ₁]; linarith [div_pos hr hdQF]
        calc δ₁ * dist Q F < r / dist Q F * dist Q F := mul_lt_mul_of_pos_right this hdQF
          _ = r := div_mul_cancel₀ r hdQF.ne'
      have hint' : openSegment ℝ (AffineMap.lineMap Q F T) (AffineMap.lineMap Q F (T + δ₁))
          ⊆ interior D.target.carrier := by
        rw [← image_openSegment, openSegment_eq_Ioo (by linarith)]
        rintro _ ⟨s, hs, rfl⟩
        apply hball
        rw [Metric.mem_ball, hRdef, dist_lineMap_lineMap, Real.dist_eq, abs_of_pos (by linarith [hs.1])]
        calc (s - T) * dist Q F < δ₁ * dist Q F :=
              mul_lt_mul_of_pos_right (by linarith [hs.2]) hdQF
          _ < r := hδ₁r
      have hwall' : ∀ y ∈ openSegment ℝ (AffineMap.lineMap Q F T)
          (AffineMap.lineMap Q F (T + δ₁)), ∀ i, y ∉ interior (D.tile i).carrier := by
        rw [← image_openSegment, openSegment_eq_Ioo (by linarith)]
        rintro _ ⟨s, hs, rfl⟩
        exact D.edge_point_not_interior ((mem₂ ε hε s).mpr
          ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      obtain ⟨e', he', hlo', hhi'⟩ := exists_interval_right (D.lineChain g c)
        (fun e => edgeLo Q F (D.tile e.1) e.2) (fun e => edgeHi Q F (D.tile e.1) e.2) T
        hδ₁ (vertex_params_finite D hQF)
        (fun y hy hyv => wall_cover_param D hg hQF hQ hF (by linarith) hint' hwall' hy hyv)
      have hθ' : ¬ isθ e' := by
        intro hθ'
        rcases hlo'.lt_or_eq with hlt | heq
        · set m := max (edgeLo Q F (D.tile e'.1) e'.2) 0
          have hm : m < T := max_lt hlt hTpos
          have := (inner₁ e' he' ((m + T) / 2)
            ⟨by linarith [le_max_right (edgeLo Q F (D.tile e'.1) e'.2) 0], by linarith⟩
            ⟨by linarith [le_max_left (edgeLo Q F (D.tile e'.1) e'.2) 0], by linarith⟩).2.2
          linarith
        · have hgood : Good (edgeHi Q F (D.tile e'.1) e'.2) := by
            refine ⟨hTpos.trans hhi', fun x hx => ?_⟩
            rcases le_or_gt x T with hxT | hxT
            · obtain ⟨e, he, hθ, h0, hT', hxe⟩ := hTgood.2 x ⟨hx.1, hxT⟩
              exact ⟨e, he, hθ, h0, hT'.trans hhi'.le, hxe⟩
            · exact ⟨e', he', hθ', by rw [heq]; exact hTpos.le, le_rfl,
                ⟨by rw [heq]; exact hxT.le, hx.2⟩⟩
          have := hmax _ hgood (Finset.mem_image.mpr ⟨e', he', rfl⟩)
          linarith
      refine ⟨e', he', hθ', (mem₁ e' he' T).mpr ⟨hlo', hhi'.le⟩,
        AffineMap.lineMap Q F (edgeHi Q F (D.tile e'.1) e'.2),
        (mem₁ e' he' _).mpr ⟨(hlo'.trans hhi'.le), le_rfl⟩, ?_⟩
      have := (lineMap_mem_openSegment_params hQF (a := 0)
        (b := edgeHi Q F (D.tile e'.1) e'.2) (t := T)).mpr
        (by rw [openSegment_eq_Ioo (hTpos.trans hhi')]; exact ⟨hTpos, hhi'⟩)
      rwa [hQ0] at this
    · obtain ⟨b1, b2⟩ := lineChain_ends D hε
      exact ⟨ε, hε, (lineMap_mem_openSegment_iff hng hQF hnQ hnF _ _ b1 b2 T).mpr ⟨hεlo, hεhi⟩⟩
  · 
    right
    have inner₂ : ∀ e ∈ D.lineChain (-g) (-c), ∀ x ∈ Ioo 0 T,
        x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) →
          0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ T := by
      intro e he x hx hxe
      constructor
      · by_contra hlo
        push Not at hlo
        have := back e (mem₂ e he) hlo
        linarith [hxe.2, hx.1]
      · by_contra hhi
        push Not at hhi
        have := ov₂ e he ε hε (lt_of_lt_of_le
          (max_lt (lt_of_le_of_lt hxe.1 hx.2) hεlo) (le_min hhi.le hεhi.le))
        rw [this] at hhi
        linarith
    have hin₁ : ∀ e ∈ D.lineChain g c, ∀ x ∈ Ioo 0 T,
        x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) →
          0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ T :=
      fun e he x hx hxe => (inner₁ e he x hx hxe).2
    have d₁ := dich_of_param D hg hQF hQ hF hTpos hin₁
    have d₂ := dich_of_param D hng hQF hnQ hnF hTpos inner₂
    refine ⟨g, c, Q, R, ⟨hQR, hg, hQ, hRc, hint, hwall, d₁, d₂⟩, ?_, ⟨e₂, ?_, hθ₂⟩⟩
    · intro e he
      obtain ⟨he, hsub⟩ := Finset.mem_filter.mp he
      rw [edge_eq_image hg hQF hQ hF _ _ (lineChain_ends D he).1 (lineChain_ends D he).2,
        hSeg, Set.image_subset_image_iff (AffineMap.lineMap_injective ℝ hQF)] at hsub
      have hlt := lt₁ e he
      have hlo := (hsub ⟨le_rfl, hlt.le⟩).1
      have hhi := (hsub ⟨hlt.le, le_rfl⟩).2
      exact (inner₁ e he ((edgeLo Q F (D.tile e.1) e.2 + edgeHi Q F (D.tile e.1) e.2) / 2)
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩).1
    · refine Finset.mem_filter.mpr ⟨h2, ?_⟩
      have := (inner₂ e₂ h2 (min t₂ T / 2)
        ⟨by positivity, by linarith [min_le_right t₂ T]⟩
        (by rw [p₂lo, p₂hi]; exact ⟨by positivity, by linarith [min_le_left t₂ T]⟩)).2
      rw [p₂hi] at this
      rw [edge_eq_image hng hQF hnQ hnF _ _ (lineChain_ends D h2).1 (lineChain_ends D h2).2,
        hSeg, p₂lo, p₂hi]
      exact Set.image_mono fun z hz => ⟨hz.1, hz.2.trans this⟩
open Classical in
theorem extend_link {Q : Plane} {e₁ e₂ : Fin N × Fin 3} (he₁ : e₁ ∈ edgesAt D Q)
    (he₂ : e₂ ∈ edgesAt D Q) (hne : e₂ ≠ e₁) (hray : SameRayAt D Q e₁ e₂)
    (hθ₁ : isθ e₁) (hθ₂ : ¬ isθ e₂)
    (hback : ∀ e : Fin N × Fin 3, Q ∈ (D.tile e.1).edge e.2 →
      ∀ y ∈ (D.tile e.1).edge e.2, Q ∉ openSegment ℝ y (farEnd D Q e₁)) :
    (∃ R, IsLink D isθ Q R) ∨
    ∃ s₁ s₂ : Finset (Fin N × Fin 3), (∀ e ∈ s₁, isθ e) ∧ (∃ e ∈ s₂, ¬ isθ e) ∧
      ∑ e ∈ s₁, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        = ∑ e ∈ s₂, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) :=
  (extend_link_wall D isθ he₁ he₂ hne hray hθ₁ hθ₂ hback).imp id (relation_of_wallRel D isθ)
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
variable {N : ℕ} {D : Dissection N} {isθ : Fin N × Fin 3 → Prop}
theorem exists_pts_eq_lo (D : Dissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0)
    {Q F : Plane} (hQF : Q ≠ F) (hQ : g Q = c) (hF : g F = c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) :
    ∃ k : Fin 3, (D.tile e.1).pts k = AffineMap.lineMap Q F (edgeLo Q F (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  rcases min_choice (lineParam Q F ((D.tile e.1).pts e.2))
    (lineParam Q F ((D.tile e.1).pts (e.2 + 1))) with hm | hm
  · exact ⟨e.2, by rw [edgeLo, hm, eq_lineMap_lineParam hg hQF hQ hF n1]⟩
  · exact ⟨e.2 + 1, by rw [edgeLo, hm, eq_lineMap_lineParam hg hQF hQ hF n2]⟩
theorem lineMap_params {Q R : Plane} (a b t : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap Q R a) (AffineMap.lineMap Q R b) t
      = AffineMap.lineMap Q R (a + t * (b - a)) := by
  simp only [AffineMap.lineMap_apply_module']
  rw [show (b • (R - Q) + Q) - (a • (R - Q) + Q) = (b - a) • (R - Q) by
    rw [sub_smul]; abel]
  rw [smul_smul, add_smul]
  abel
theorem chain_iff {g₁ g₂ : Plane →ₗ[ℝ] ℝ} {c₁ c₂ : ℝ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {ε : Fin N × Fin 3} (h₁ : ε ∈ D.lineChain (-g₁) (-c₁)) (h₂ : ε ∈ D.lineChain (-g₂) (-c₂))
    (e : Fin N × Fin 3) : e ∈ D.lineChain g₁ c₁ ↔ e ∈ D.lineChain g₂ c₂ :=
  ⟨(chain_transfer D hg₂ hg₁ h₂ h₁).2 e, (chain_transfer D hg₁ hg₂ h₁ h₂).2 e⟩
theorem chain_coord {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c)) :
    0 < g ((D.tile ε.1).pts (ε.2 + 2)) - c ∧ ∀ z, g z - c =
      (D.tile ε.1).basis.coord (ε.2 + 2) z * (g ((D.tile ε.1).pts (ε.2 + 2)) - c) := by
  obtain ⟨a1, a2, a3⟩ := Dissection.mem_lineChain.mp hε
  simp only [LinearMap.neg_apply, neg_inj] at a1 a2
  have b3 := a3 (ε.2 + 2)
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at b3
  have i1 : ∀ m : Fin 3, m + 2 + 1 = m := by decide
  have i2 : ∀ m : Fin 3, m + 2 + 2 = m + 1 := by decide
  refine ⟨sub_pos.mpr (lt_of_le_of_ne b3 (Ne.symm (third_off_line _ hg ε.2 a1 a2))), fun z => ?_⟩
  exact level_eq_coord _ g c (ε.2 + 2) (by rw [i1]; exact a1) (by rw [i2]; exact a2) z
theorem end_param_at (D : Dissection N) {Q W : Plane} (hQW : Q ≠ W) {q : ℝ} {e : Fin N × Fin 3}
    (he : e ∈ edgesAt D (AffineMap.lineMap Q W q)) :
    edgeLo Q W (D.tile e.1) e.2 = q ∨ edgeHi Q W (D.tile e.1) e.2 = q := by
  have hq : lineParam Q W (AffineMap.lineMap Q W q) = q := lineParam_lineMap hQW q
  rcases (mem_edgesAt D).mp he with h1 | h1
  · rcases le_total (lineParam Q W ((D.tile e.1).pts e.2))
      (lineParam Q W ((D.tile e.1).pts (e.2 + 1))) with h2 | h2
    · left; rw [edgeLo, min_eq_left h2, h1, hq]
    · right; rw [edgeHi, max_eq_left h2, h1, hq]
  · rcases le_total (lineParam Q W ((D.tile e.1).pts e.2))
      (lineParam Q W ((D.tile e.1).pts (e.2 + 1))) with h2 | h2
    · right; rw [edgeHi, max_eq_right h2, h1, hq]
    · left; rw [edgeLo, min_eq_right h2, h1, hq]
theorem edgesAt_of_hi (D : Dissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {Q W : Plane}
    (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) {q : ℝ} (hhi : edgeHi Q W (D.tile e.1) e.2 = q) :
    e ∈ edgesAt D (AffineMap.lineMap Q W q) ∧
      farEnd D (AffineMap.lineMap Q W q) e = AffineMap.lineMap Q W (edgeLo Q W (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  have e1 := eq_lineMap_lineParam hg hQW hQ hW n1
  have e2 := eq_lineMap_lineParam hg hQW hQ hW n2
  rw [edgeHi] at hhi
  rw [edgeLo]
  rcases le_total (lineParam Q W ((D.tile e.1).pts e.2))
      (lineParam Q W ((D.tile e.1).pts (e.2 + 1))) with hle | hle
  · rw [max_eq_right hle] at hhi
    rw [min_eq_left hle]
    have hR : (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap Q W q := by rw [← e2, hhi]
    have hne : (D.tile e.1).pts e.2 ≠ AffineMap.lineMap Q W q := fun h0 =>
      tri_pts_succ_ne (D.tile e.1) e.2 (h0.trans hR.symm)
    exact ⟨(mem_edgesAt D).mpr (Or.inr hR), by rw [farEnd, if_neg hne, e1]⟩
  · rw [max_eq_left hle] at hhi
    rw [min_eq_right hle]
    have hR : (D.tile e.1).pts e.2 = AffineMap.lineMap Q W q := by rw [← e1, hhi]
    exact ⟨(mem_edgesAt D).mpr (Or.inl hR), by rw [farEnd, if_pos hR, e2]⟩
theorem edgesAt_of_lo (D : Dissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {Q W : Plane}
    (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) {q : ℝ} (hlo : edgeLo Q W (D.tile e.1) e.2 = q) :
    e ∈ edgesAt D (AffineMap.lineMap Q W q) ∧
      farEnd D (AffineMap.lineMap Q W q) e = AffineMap.lineMap Q W (edgeHi Q W (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  have e1 := eq_lineMap_lineParam hg hQW hQ hW n1
  have e2 := eq_lineMap_lineParam hg hQW hQ hW n2
  rw [edgeLo] at hlo
  rw [edgeHi]
  rcases le_total (lineParam Q W ((D.tile e.1).pts e.2))
      (lineParam Q W ((D.tile e.1).pts (e.2 + 1))) with hle | hle
  · rw [min_eq_left hle] at hlo
    rw [max_eq_right hle]
    have hR : (D.tile e.1).pts e.2 = AffineMap.lineMap Q W q := by rw [← e1, hlo]
    exact ⟨(mem_edgesAt D).mpr (Or.inl hR), by rw [farEnd, if_pos hR, e2]⟩
  · rw [min_eq_right hle] at hlo
    rw [max_eq_left hle]
    have hR : (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap Q W q := by rw [← e2, hlo]
    have hne : (D.tile e.1).pts e.2 ≠ AffineMap.lineMap Q W q := fun h0 =>
      tri_pts_succ_ne (D.tile e.1) e.2 (h0.trans hR.symm)
    exact ⟨(mem_edgesAt D).mpr (Or.inr hR), by rw [farEnd, if_neg hne, e1]⟩
theorem lonely_relint (D : Dissection N) {Q : Plane} (hQ : Q ∈ interior D.target.carrier) {e : Fin N × Fin 3}
    (he : e ∈ edgesAt D Q) (hlonely : ∀ e' ∈ edgesAt D Q, e' ≠ e → ¬ SameRayAt D Q e e') :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g Q = c ∧ g (farEnd D Q e) = c ∧
      e ∈ D.lineChain g c ∧ ∃ e₂ ∈ D.lineChain (-g) (-c),
        Q ∈ openSegment ℝ ((D.tile e₂.1).pts e₂.2) ((D.tile e₂.1).pts (e₂.2 + 1)) := by
  set F := farEnd D Q e
  have hQF : Q ≠ F := (farEnd_ne D he).symm
  obtain ⟨g₀, c₀, hg₀, hQ₀, hF₀⟩ := ray_level (farEnd_ne D he)
  obtain ⟨g, c, hg, hgQ, hgF, hec⟩ : ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g Q = c ∧
      g F = c ∧ e ∈ D.lineChain g c := by
    rcases edgesAt_chain D he hQ₀ hF₀ with h' | h'
    · exact ⟨g₀, c₀, hg₀, hQ₀, hF₀, h'⟩
    · exact ⟨-g₀, -c₀, neg_ne_zero.mpr hg₀, by simp [hQ₀],
        by simp only [LinearMap.neg_apply, F, hF₀], h'⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior Q hQ
  have hdQF : 0 < dist Q F := dist_pos.mpr hQF
  set τ := min (1 / 2) (r / (2 * dist Q F))
  have hτ0 : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hint : AffineMap.lineMap Q F τ ∈ interior D.target.carrier := by
    apply hball
    rw [Metric.mem_ball, dist_lineMap_left, Real.norm_eq_abs, abs_of_pos hτ0]
    have : τ ≤ r / (2 * dist Q F) := min_le_right _ _
    calc τ * dist Q F ≤ r / (2 * dist Q F) * dist Q F :=
          mul_le_mul_of_nonneg_right this hdQF.le
      _ = r / 2 := by field_simp
      _ < r := by linarith
  exact ⟨g, c, hg, hgQ, hgF, hec, lonely_openSegment D he hg hgQ hgF hec hlonely ⟨hτ0, hτ1⟩ hint⟩
namespace LinkData
variable {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
theorem start_vertex (h : LinkData D isθ Q R g c) : ∃ i k, (D.tile i).pts k = Q := by
  obtain ⟨e, he, hlo, hhi⟩ := exists_interval_right (D.lineChain g c)
    (fun x => edgeLo Q R (D.tile x.1) x.2) (fun x => edgeHi Q R (D.tile x.1) x.2) 0
    one_pos Set.finite_empty (fun y hy _ => by
      rw [zero_add] at hy
      obtain ⟨e, he, hye⟩ := h.cov _ (openSegment_param.mpr ⟨y, hy, rfl⟩)
      exact ⟨e, he, (h.mem_edge_iff he y).mp hye⟩)
  have hm : 0 < min (edgeHi Q R (D.tile e.1) e.2) 1 := lt_min hhi one_pos
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q R).Nonempty := by
    refine ⟨AffineMap.lineMap Q R (min (edgeHi Q R (D.tile e.1) e.2) 1 / 2),
      (h.mem_edge_iff he _).mpr ⟨?_, ?_⟩, openSegment_param.mpr ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith
    · linarith [min_le_left (edgeHi Q R (D.tile e.1) e.2) 1]
    · linarith
    · linarith [min_le_right (edgeHi Q R (D.tile e.1) e.2) 1]
  obtain ⟨hsub, -⟩ := h.inner e he hmeet
  have h0 := (h.params_of_inner he hsub).1
  obtain ⟨k, hk⟩ := exists_pts_eq_lo D h.hg h.ne h.hQ h.hR he
  exact ⟨e.1, k, by rw [hk, le_antisymm hlo h0, AffineMap.lineMap_apply_zero]⟩
theorem tiles_side (h : LinkData D isθ Q R g c) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c))
    (hRε : R ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
    {i : Fin N} (hi : i ≠ ε.1) (hRi : R ∈ (D.tile i).carrier) :
    ∀ z ∈ (D.tile i).carrier, g z ≤ c := by
  intro z hz
  have h1 := tile_side_of_openSegment D hRε hi hRi z hz
  obtain ⟨hpos, hcoord⟩ := chain_coord h.hg hε
  have := hcoord z
  nlinarith
theorem end_param (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3} (he : e ∈ edgesAt D R) :
    edgeLo Q R (D.tile e.1) e.2 = 1 ∨ edgeHi Q R (D.tile e.1) e.2 = 1 := by
  rw [← AffineMap.lineMap_apply_one (k := ℝ) Q R] at he
  exact end_param_at D h.ne he
end LinkData
theorem edgesAt_params' {Q W R : Plane} (hQW : Q ≠ W) {e : Fin N × Fin 3}
    (he : e ∈ edgesAt D R) {r p : ℝ} (hR : R = AffineMap.lineMap Q W r)
    (hfar : farEnd D R e = AffineMap.lineMap Q W p) :
    edgeLo Q W (D.tile e.1) e.2 = min r p ∧ edgeHi Q W (D.tile e.1) e.2 = max r p := by
  have hr : lineParam Q W R = r := by rw [hR, lineParam_lineMap hQW]
  have hp : lineParam Q W (farEnd D R e) = p := by rw [hfar, lineParam_lineMap hQW]
  rw [edgeLo, edgeHi]
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, hr, hp]; exact ⟨rfl, rfl⟩
  · rw [h1, h2, hr, hp, min_comm, max_comm]; exact ⟨rfl, rfl⟩
namespace LinkData
variable {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
theorem eps_params (h : LinkData D isθ Q R g c) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c))
    (hRε : R ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1))) :
    edgeLo Q R (D.tile ε.1) ε.2 < 1 ∧ 1 < edgeHi Q R (D.tile ε.1) ε.2 := by
  have hng : -g ≠ 0 := neg_ne_zero.mpr h.hg
  have hnQ : (-g) Q = -c := by simp [h.hQ]
  have hnR : (-g) R = -c := by simp [h.hR]
  obtain ⟨b1, b2⟩ := lineChain_ends D hε
  have h1 : AffineMap.lineMap Q R (1 : ℝ) ∈
      openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) := by
    rw [AffineMap.lineMap_apply_one]; exact hRε
  exact (lineMap_mem_openSegment_iff hng h.ne hnQ hnR _ _ b1 b2 1).mp h1
theorem not_side2 (h : LinkData D isθ Q R g c) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c))
    (hRε : R ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
    {z : Fin N × Fin 3} (hz : z ∈ edgesAt D R) : z ∉ D.lineChain (-g) (-c) := by
  intro hz2
  have hng : -g ≠ 0 := neg_ne_zero.mpr h.hg
  have hnQ : (-g) Q = -c := by simp [h.hQ]
  have hnR : (-g) R = -c := by simp [h.hR]
  obtain ⟨hε1, hε2⟩ := h.eps_params hε hRε
  have hlt := chain_lo_lt_hi D hng h.ne hnQ hnR hz2
  rcases h.end_param hz with h1 | h1
  · have := lineChain_eq_of_overlap D hng h.ne hnQ hnR hz2 hε
      (lt_of_le_of_lt (max_le h1.le hε1.le) (lt_min (h1 ▸ hlt) hε2))
    rw [this] at h1
    linarith
  · have := lineChain_eq_of_overlap D hng h.ne hnQ hnR hz2 hε
      (lt_of_lt_of_le (max_lt (h1 ▸ hlt) hε1) (le_min h1.ge hε2.le))
    rw [this] at h1
    linarith
theorem far_le (h : LinkData D isθ Q R g c) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c))
    (hRε : R ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
    {x : Fin N × Fin 3} (hx : x ∈ edgesAt D R) : g (farEnd D R x) ≤ c := by
  have hRx : R ∈ (D.tile x.1).carrier := by
    have : R ∈ (D.tile x.1).edge x.2 := by rw [edgesAt_edge D hx]; exact left_mem_segment ℝ _ _
    exact (D.tile x.1).edge_subset_carrier x.2 this
  have hFx : farEnd D R x ∈ (D.tile x.1).carrier := by
    have : farEnd D R x ∈ (D.tile x.1).edge x.2 := by
      rw [edgesAt_edge D hx]; exact right_mem_segment ℝ _ _
    exact (D.tile x.1).edge_subset_carrier x.2 this
  have hne : x.1 ≠ ε.1 := by
    intro hxε
    rcases (mem_edgesAt D).mp hx with h1 | h1
    · have h2 : (D.tile ε.1).pts x.2 = R := by rw [← hxε]; exact h1
      exact Tri.vertex_not_mem_openSegment (D.tile ε.1) x.2 ε.2 (by rw [h2]; exact hRε)
    · have h2 : (D.tile ε.1).pts (x.2 + 1) = R := by rw [← hxε]; exact h1
      exact Tri.vertex_not_mem_openSegment (D.tile ε.1) (x.2 + 1) ε.2 (by rw [h2]; exact hRε)
  exact h.tiles_side hε hRε hne hRx _ hFx
theorem far_lt_of_partner (h : LinkData D isθ Q R g c) {x y : Fin N × Fin 3}
    (hx : x ∈ edgesAt D R) (hy : y ∈ edgesAt D R) (hxy : x ≠ y) (hray : SameRayAt D R x y) :
    g (farEnd D R x) < c := by
  obtain ⟨ε, hε, hRε⟩ := h.across
  rcases (h.far_le hε hRε hx).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨t, ht, hFy⟩ := hray
    set F := farEnd D R x
    have hgy : g (farEnd D R y) = c := by rw [hFy]; exact level_lineMap h.hR heq t
    have cx := edgesAt_chain D hx h.hR heq
    have cy := edgesAt_chain D hy h.hR hgy
    have nx := h.not_side2 hε hRε hx
    have ny := h.not_side2 hε hRε hy
    have cx' : x ∈ D.lineChain g c := cx.resolve_right nx
    have cy' : y ∈ D.lineChain g c := cy.resolve_right ny
    have hRF : R ≠ F := (farEnd_ne D hx).symm
    have hs : 0 < min 1 t := lt_min one_pos ht
    have hm1 := mem_edge_of_ray D hx (t := 1) (AffineMap.lineMap_apply_one R F).symm hs.le
      (min_le_left _ _)
    have hm2 := mem_edge_of_ray D hy hFy hs.le (min_le_right _ _)
    have hR1 : R ∈ (D.tile x.1).edge x.2 := by rw [edgesAt_edge D hx]; exact left_mem_segment ℝ _ _
    have hR2 : R ∈ (D.tile y.1).edge y.2 := by rw [edgesAt_edge D hy]; exact left_mem_segment ℝ _ _
    have hneq : R ≠ AffineMap.lineMap R F (min 1 t) := by
      intro h'
      have : AffineMap.lineMap R F (0 : ℝ) = AffineMap.lineMap R F (min 1 t) := by
        rw [AffineMap.lineMap_apply_zero]; exact h'
      exact hs.ne (AffineMap.lineMap_injective ℝ hRF this)
    exact hxy (lineChain_eq_of_two D h.hg cx' cy' hneq ⟨hR1, hR2⟩ ⟨hm1, hm2⟩)
theorem back_of_partner (h : LinkData D isθ Q R g c) {x y : Fin N × Fin 3}
    (hx : x ∈ edgesAt D R) (hy : y ∈ edgesAt D R) (hxy : x ≠ y) (hray : SameRayAt D R x y) :
    ∀ e : Fin N × Fin 3, R ∈ (D.tile e.1).edge e.2 →
      ∀ z ∈ (D.tile e.1).edge e.2, R ∉ openSegment ℝ z (farEnd D R x) := by
  intro e hRe z hz hRz
  obtain ⟨ε, hε, hRε⟩ := h.across
  have hlt := h.far_lt_of_partner hx hy hxy hray
  have hgz : c < g z := by
    obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hRz
    have hR := h.hR
    rw [← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hR
    have key : a * (g z - c) = b * (c - g (farEnd D R x)) := by
      linear_combination hR - c * hab
    have := mul_pos hb (sub_pos.mpr hlt)
    by_contra hc
    push Not at hc
    nlinarith
  obtain ⟨hκ, hcoord⟩ := chain_coord h.hg hε
  have hcz : 0 < (D.tile ε.1).basis.coord (ε.2 + 2) z := by
    have := hcoord z
    by_contra hc
    push Not at hc
    nlinarith
  obtain ⟨τ0, hτ0, hint⟩ := Tri.lineMap_mem_interior (D.tile ε.1) ε.2 hRε hcz
  set τ := min τ0 1 / 2
  have hτ : 0 < τ := by have := lt_min hτ0 one_pos; simp only [τ]; linarith
  have hττ : τ < τ0 := by have := min_le_left τ0 1; simp only [τ]; linarith
  have hτ1 : τ ≤ 1 := by have := min_le_right τ0 1; simp only [τ]; linarith
  have hmem : AffineMap.lineMap R z τ ∈ (D.tile e.1).edge e.2 := by
    rw [Tri.edge] at hRe hz ⊢
    refine (convex_segment (𝕜 := ℝ) _ _).segment_subset hRe hz ?_
    rw [segment_eq_image_lineMap]
    exact ⟨τ, ⟨hτ.le, hτ1⟩, rfl⟩
  exact D.edge_point_not_interior hmem _ (hint τ hτ hττ)
theorem arrive_at (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c)
    (hhi : edgeHi Q R (D.tile e.1) e.2 = 1) :
    e ∈ edgesAt D R ∧ farEnd D R e = AffineMap.lineMap Q R (edgeLo Q R (D.tile e.1) e.2) := by
  have := edgesAt_of_hi D h.hg h.ne h.hQ h.hR he hhi
  rwa [AffineMap.lineMap_apply_one] at this
theorem lonely_marked (h : LinkData D isθ Q R g c) :
    ∃ e₀ ∈ edgesAt D R, isθ e₀ ∧
      (∀ e' ∈ edgesAt D R, ¬ (e₀ ≠ e' ∧ SameRayAt D R e₀ e')) ∧
      ∀ e ∈ edgesAt D R, isθ e → (∀ e' ∈ edgesAt D R, ¬ (e ≠ e' ∧ SameRayAt D R e e')) →
        e = e₀ := by
  obtain ⟨e₀, he₀, hθ₀, -, hlo₀, hhi₀⟩ := h.arrive
  obtain ⟨he₀R, hfar₀⟩ := h.arrive_at he₀ hhi₀
  obtain ⟨ε, hε, hRε⟩ := h.across
  obtain ⟨hε1, hε2⟩ := h.eps_params hε hRε
  obtain ⟨eo, heo, hθo, hloo, hhio⟩ := h.leave
  have hR1 : R = AffineMap.lineMap Q R (1 : ℝ) := (AffineMap.lineMap_apply_one Q R).symm
  refine ⟨e₀, he₀R, hθ₀, ?_, ?_⟩
  · 
    rintro e' he' ⟨hne, t, ht, hFt⟩
    set lo₀ := edgeLo Q R (D.tile e₀.1) e₀.2
    have hfar' : farEnd D R e' = AffineMap.lineMap Q R (1 + t * (lo₀ - 1)) := by
      rw [hFt, hfar₀]
      calc AffineMap.lineMap R (AffineMap.lineMap Q R lo₀) t
          = AffineMap.lineMap (AffineMap.lineMap Q R (1 : ℝ)) (AffineMap.lineMap Q R lo₀) t := by
            rw [AffineMap.lineMap_apply_one]
        _ = _ := lineMap_params 1 lo₀ t
    obtain ⟨plo, phi⟩ := edgesAt_params' h.ne he' hR1 hfar'
    have hp : 1 + t * (lo₀ - 1) < 1 := by nlinarith
    rw [min_eq_right hp.le] at plo
    rw [max_eq_left hp.le] at phi
    have hg' : g (farEnd D R e') = c := by rw [hfar']; exact level_lineMap h.hQ h.hR _
    rcases edgesAt_chain D he' h.hR hg' with c1 | c2
    · apply hne
      refine (lineChain_eq_of_overlap D h.hg h.ne h.hQ h.hR c1 he₀ ?_).symm
      rw [plo, phi, hhi₀, min_self]
      exact max_lt hp hlo₀
    · exact h.not_side2 hε hRε he' c2
  · 
    intro e he hθ hlonely
    obtain ⟨g', c', hg', -, -, hec, e₂, he₂, hRe₂⟩ := lonely_relint D h.end_interior he
      (fun e' he' hne hray => hlonely e' he' ⟨hne.symm, hray⟩)
    obtain ⟨i, k, hik⟩ := h.end_vertex
    have hj : e₂.1 = ε.1 := openSegment_tile_unique D hik hRe₂ hRε
    have hm : e₂.2 = ε.2 := by
      have := hRe₂
      rw [hj] at this
      exact Tri.openSegment_edge_unique (D.tile ε.1) this hRε
    have heq : e₂ = ε := Prod.ext hj hm
    rw [heq] at he₂
    have he1 : e ∈ D.lineChain g c := (chain_iff hg' h.hg he₂ hε e).mp hec
    have hlt := chain_lo_lt_hi D h.hg h.ne h.hQ h.hR he1
    rcases h.end_param he with h1 | h1
    · exfalso
      have := lineChain_eq_of_overlap D h.hg h.ne h.hQ h.hR he1 heo
        (lt_of_le_of_lt (max_le h1.le hloo.le) (lt_min (h1 ▸ hlt) hhio))
      rw [this] at hθ
      exact hθo hθ
    · exact lineChain_eq_of_overlap D h.hg h.ne h.hQ h.hR he1 he₀
        (lt_of_lt_of_le (max_lt (h1 ▸ hlt) hlo₀) (le_min h1.ge hhi₀.ge))
end LinkData
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
variable {N : ℕ} (D : Dissection N) (isθ : Fin N × Fin 3 → Prop)
def HasRelation : Prop :=
  ∃ s₁ s₂ : Finset (Fin N × Fin 3), (∀ e ∈ s₁, isθ e) ∧ (∃ e ∈ s₂, ¬ isθ e) ∧
    ∑ e ∈ s₁, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = ∑ e ∈ s₂, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
def Partners (V : Plane) (x y : Fin N × Fin 3) : Prop := x ≠ y ∧ SameRayAt D V x y
open Classical in
theorem mixed_of_parity {V : Plane} {e₀ : Fin N × Fin 3} (he₀ : e₀ ∈ edgesAt D V)
    (hθ₀ : isθ e₀) (hl₀ : ∀ e' ∈ edgesAt D V, ¬ Partners D V e₀ e')
    (huniq : ∀ e ∈ edgesAt D V, isθ e → (∀ e' ∈ edgesAt D V, ¬ Partners D V e e') → e = e₀)
    (heven : Even ((edgesAt D V).filter isθ).card) :
    ∃ x ∈ edgesAt D V, ∃ y ∈ edgesAt D V, Partners D V x y ∧ isθ x ∧ ¬ isθ y := by
  by_contra hno
  push Not at hno
  have hpar := card_filter_mod_two (edgesAt D V) (Partners D V) isθ
    (fun x _ y _ h => ⟨h.1.symm, sameRayAt_symm D h.2⟩) (fun x h => h.1 rfl)
    (fun x hx y hy z hz hxy hxz => by
      by_contra hyz
      exact sameRayAt_unique D hx hy hz hxy.1.symm hxz.1.symm hyz hxy.2 hxz.2)
    (fun x hx y hy hxy hθ => by
      exact hno x hx y hy hxy hθ) {e₀} (fun x => by
        rw [Finset.mem_singleton]
        constructor
        · rintro rfl
          exact ⟨he₀, hθ₀, hl₀⟩
        · rintro ⟨hx, hθ, hl⟩
          exact huniq x hx hθ hl)
  rw [Finset.card_singleton, Nat.even_iff.mp heven] at hpar
  exact absurd hpar (by norm_num)
open Classical in
theorem out_of_in_wall {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (h : LinkData D isθ Q R g c)
    (heven : Even ((edgesAt D R).filter isθ).card) (hnw : ¬ WallRel D isθ) :
    ∃ R', IsLink D isθ R R' := by
  obtain ⟨e₀, he₀, hθ₀, hl₀, huniq⟩ := h.lonely_marked
  obtain ⟨x, hx, y, hy, hxy, hθx, hθy⟩ := mixed_of_parity D isθ he₀ hθ₀
    (fun e' he' h' => hl₀ e' he' h') (fun e he hθ hl => huniq e he hθ (fun e' he' h' => hl e' he' h'))
    heven
  rcases extend_link_wall D isθ hx hy hxy.1.symm hxy.2 hθx hθy
    (h.back_of_partner hx hy hxy.1 hxy.2) with hlink | hw
  · exact hlink
  · exact absurd hw hnw
theorem hasRelation_of_wallRel (h : WallRel D isθ) : HasRelation D isθ :=
  relation_of_wallRel D isθ h
open Classical in
theorem out_of_in {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (h : LinkData D isθ Q R g c)
    (heven : Even ((edgesAt D R).filter isθ).card) (hnorel : ¬ HasRelation D isθ) :
    ∃ R', IsLink D isθ R R' :=
  out_of_in_wall D isθ h heven fun hw => hnorel (hasRelation_of_wallRel D isθ hw)
open Classical in
theorem sum_out_eq_sum_in (V : Finset Plane) :
    ∑ v ∈ V, (V.filter fun w => IsLink D isθ v w).card
      = ∑ w ∈ V, (V.filter fun v => IsLink D isθ v w).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm
open Classical in
theorem in_le_one (V : Finset Plane) (w : Plane) :
    (V.filter fun v => IsLink D isθ v w).card ≤ 1 :=
  Finset.card_le_one.mpr fun _ ha _ hb =>
    link_unique D isθ (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
open Classical in
noncomputable def vertexFinset : Finset Plane :=
  Finset.univ.image fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2
theorem link_mem_vertexFinset {u w : Plane} (h : IsLink D isθ u w) :
    u ∈ vertexFinset D ∧ w ∈ vertexFinset D := by
  classical
  obtain ⟨g, c, h⟩ := h
  obtain ⟨i, k, hik⟩ := h.start_vertex
  obtain ⟨i', k', hik'⟩ := h.end_vertex
  exact ⟨Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, hik⟩,
    Finset.mem_image.mpr ⟨(i', k'), Finset.mem_univ _, hik'⟩⟩
open Classical in
theorem relation_of_start
    (heven : ∀ Q R g c, LinkData D isθ Q R g c → Even ((edgesAt D R).filter isθ).card)
    (hstart : ∃ Q₀ ∈ frontier D.target.carrier, ∃ R, IsLink D isθ Q₀ R) :
    HasRelation D isθ := by
  by_contra hnorel
  obtain ⟨Q₀, hQ₀fr, R₀, hlink₀⟩ := hstart
  set V := vertexFinset D
  have hge : ∀ v ∈ V, (V.filter fun u => IsLink D isθ u v).card ≤
      (V.filter fun w => IsLink D isθ v w).card := by
    intro v _
    rcases Nat.eq_zero_or_pos (V.filter fun u => IsLink D isθ u v).card with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      obtain ⟨-, g, c, hl⟩ := Finset.mem_filter.mp hu
      obtain ⟨R', hR'⟩ := out_of_in D isθ hl (heven _ _ _ _ hl) hnorel
      have : 1 ≤ (V.filter fun w => IsLink D isθ v w).card :=
        Finset.card_pos.mpr ⟨R', Finset.mem_filter.mpr ⟨(link_mem_vertexFinset D isθ hR').2, hR'⟩⟩
      linarith [in_le_one D isθ V v]
  have hin0 : (V.filter fun u => IsLink D isθ u Q₀).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro u - ⟨g, c, hl⟩
    exact hQ₀fr.2 hl.end_interior
  have hout : 0 < (V.filter fun w => IsLink D isθ Q₀ w).card :=
    Finset.card_pos.mpr ⟨R₀, Finset.mem_filter.mpr ⟨(link_mem_vertexFinset D isθ hlink₀).2,
      hlink₀⟩⟩
  have hlt := Finset.sum_lt_sum hge
    ⟨Q₀, (link_mem_vertexFinset D isθ hlink₀).1, by rw [hin0]; exact hout⟩
  rw [sum_out_eq_sum_in] at hlt
  exact lt_irrefl _ hlt
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry MeasureTheory Set
variable {N : ℕ} (D : Dissection N)
theorem volume_inter_eq_sum {U : Set Plane} (hU : MeasurableSet U) :
    volume (D.target.carrier ∩ U) = ∑ i, volume ((D.tile i).carrier ∩ U) := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => (D.tile i).carrier ∩ U)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) (D.aedisjoint hij))
    (fun i _ => ((D.tile i).nullMeasurableSet).inter hU.nullMeasurableSet)
  have hUn : (⋃ i ∈ (Finset.univ : Finset (Fin N)), ((D.tile i).carrier ∩ U))
      = D.target.carrier ∩ U := by
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [← Set.iUnion_inter, D.covers]
  rw [hUn] at h
  exact h
theorem volume_level_zero {g : Plane →ₗ[ℝ] ℝ} (hg : g ≠ 0) (c : ℝ) :
    volume {y : Plane | g y = c} = 0 := by
  obtain ⟨Q, hQ⟩ : ∃ Q : Plane, g Q = c := by
    obtain ⟨v, hv⟩ : ∃ v, g v ≠ 0 := by
      by_contra h
      push Not at h
      exact hg (LinearMap.ext h)
    exact ⟨(c / g v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hv]⟩
  let s : AffineSubspace ℝ Plane := AffineSubspace.mk' Q (LinearMap.ker g)
  have hsub : {y : Plane | g y = c} ⊆ s := by
    intro y hy
    show y ∈ AffineSubspace.mk' Q (LinearMap.ker g)
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub, hQ]
    exact sub_eq_zero.mpr hy
  have hs : s ≠ ⊤ := by
    intro htop
    apply hg
    ext v
    have hv : Q + v ∈ s := by rw [htop]; exact AffineSubspace.mem_top ℝ Plane _
    have : Q + v ∈ AffineSubspace.mk' Q (LinearMap.ker g) := hv
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, add_sub_cancel_left] at this
    simpa using this
  exact measure_mono_null hsub (Measure.addHaar_affineSubspace volume s hs)
theorem continuous_functional (g : Plane →ₗ[ℝ] ℝ) : Continuous g :=
  LinearMap.continuous_of_finiteDimensional g
theorem volume_ball_inter_half {g : Plane →ₗ[ℝ] ℝ} (hg : g ≠ 0) {Q : Plane} {c : ℝ}
    (hQ : g Q = c) (r : ℝ) :
    volume (Metric.ball Q r) = 2 * volume (Metric.ball Q r ∩ {y | g y ≤ c}) := by
  have hcont := continuous_functional g
  have hH : MeasurableSet {y : Plane | g y ≤ c} :=
    (isClosed_le hcont continuous_const).measurableSet
  have hH' : MeasurableSet {y : Plane | c ≤ g y} :=
    (isClosed_le continuous_const hcont).measurableSet
  set A := Metric.ball Q r ∩ {y | g y ≤ c}
  set A' := Metric.ball Q r ∩ {y | c ≤ g y}
  have hrefl : volume A' = volume A := by
    have hmp := Measure.measurePreserving_sub_left (volume : Measure Plane) (Q + Q)
    have hpre : (fun y => Q + Q - y) ⁻¹' A = A' := by
      ext y
      simp only [A, A', Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, Set.mem_setOf_eq,
        map_sub, map_add, hQ]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, by linarith⟩
        rwa [dist_eq_norm, show Q + Q - y - Q = Q - y by abel, ← dist_eq_norm, dist_comm] at h1
      · rintro ⟨h1, h2⟩
        refine ⟨?_, by linarith⟩
        rwa [dist_eq_norm, show Q + Q - y - Q = Q - y by abel, ← dist_eq_norm, dist_comm]
    rw [← hpre]
    exact hmp.measure_preimage (Metric.isOpen_ball.measurableSet.inter hH).nullMeasurableSet
  have hunion : A ∪ A' = Metric.ball Q r := by
    ext y
    simp only [A, A', Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases le_total (g y) c with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have hinter : volume (A ∩ A') = 0 := by
    refine measure_mono_null ?_ (volume_level_zero hg c)
    rintro y ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    exact le_antisymm h1 h2
  have hA'm : NullMeasurableSet A' volume :=
    ((Metric.isOpen_ball (x := Q) (ε := r)).measurableSet.inter hH').nullMeasurableSet
  have := measure_union_add_inter₀ (μ := volume) A hA'm
  rw [hunion, hinter, add_zero, hrefl] at this
  rw [this, two_mul]
open Classical in
theorem half_angle_sum {Q : Plane} (hQ : Q ∈ interior D.target.carrier)
    {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) (hgQ : g Q = c)
    (hside : ∀ i, Q ∈ (D.tile i).carrier → (∀ y ∈ (D.tile i).carrier, g y ≤ c) ∨
      (∀ y ∈ (D.tile i).carrier, c ≤ g y)) :
    ∑ i ∈ Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c),
      (D.tile i).localAngle Q = Real.pi := by
  obtain ⟨rT, hrT, hT⟩ := D.target.volume_inter_ball_localAngle Q
  choose ri hri hcontrib using fun i => (D.tile i).volume_inter_ball_localAngle Q
  have hfar : ∀ i, ∃ s > (0 : ℝ), Q ∉ (D.tile i).carrier →
      Metric.ball Q s ∩ (D.tile i).carrier = ∅ := by
    intro i
    by_cases hQi : Q ∈ (D.tile i).carrier
    · exact ⟨1, one_pos, fun h => absurd hQi h⟩
    · obtain ⟨s, hs, hsub⟩ :=
        Metric.isOpen_iff.mp (D.tile i).isCompact.isClosed.isOpen_compl Q hQi
      exact ⟨s, hs, fun _ => Set.eq_empty_iff_forall_notMem.mpr fun y hy => hsub hy.1 hy.2⟩
  choose si hsi hsfar using hfar
  obtain ⟨r0, hr0, hr0le⟩ := exists_common_radius D.pos (fun i => min (ri i) (si i))
    (fun i => lt_min (hri i) (hsi i))
  obtain ⟨rI, hrI, hball⟩ := Metric.isOpen_iff.mp isOpen_interior Q hQ
  set r := min r0 (min rT rI)
  have hr : 0 < r := lt_min hr0 (lt_min hrT hrI)
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hrT' : r ≤ rT := (min_le_right _ _).trans (min_le_left _ _)
  have hrI' : r ≤ rI := (min_le_right _ _).trans (min_le_right _ _)
  set B := Metric.ball Q r
  have hBt : B ⊆ D.target.carrier := fun y hy =>
    interior_subset (hball (Metric.ball_subset_ball hrI' hy))
  have hB : volume B = ENNReal.ofReal (2 * Real.pi / 2 * r ^ 2) := by
    have := hT r hr hrT'
    rwa [Tri.localAngle_interior _ hQ, Set.inter_eq_right.mpr hBt] at this
  set H := {y : Plane | g y ≤ c}
  have hHm : MeasurableSet H :=
    (isClosed_le (continuous_functional g) continuous_const).measurableSet
  have hhalf := volume_ball_inter_half hg hgQ r
  have hper : ∀ i, volume ((D.tile i).carrier ∩ (B ∩ H)) = ENNReal.ofReal
      (if ∀ y ∈ (D.tile i).carrier, g y ≤ c then (D.tile i).localAngle Q / 2 * r ^ 2 else 0) := by
    intro i
    have hri' : r ≤ ri i := hrr0.trans ((hr0le i).trans (min_le_left _ _))
    have hsi' : r ≤ si i := hrr0.trans ((hr0le i).trans (min_le_right _ _))
    split_ifs with hsub
    · have heq : (D.tile i).carrier ∩ (B ∩ H) = (D.tile i).carrier ∩ B := by
        ext y
        simp only [Set.mem_inter_iff]
        exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hsub y h.1⟩⟩
      rw [heq]
      exact hcontrib i r hr hri'
    · rw [ENNReal.ofReal_zero]
      by_cases hQi : Q ∈ (D.tile i).carrier
      · rcases hside i hQi with h | h
        · exact absurd h hsub
        · refine measure_mono_null ?_ (volume_level_zero hg c)
          rintro y ⟨hy, -, hyH⟩
          exact le_antisymm hyH (h y hy)
      · have hempty := hsfar i hQi
        refine measure_mono_null ?_ measure_empty
        rintro y ⟨hy, hyB, -⟩
        rw [← hempty]
        exact ⟨Metric.ball_subset_ball hsi' hyB, hy⟩
  have hsum := volume_inter_eq_sum D ((Metric.isOpen_ball (x := Q) (ε := r)).measurableSet.inter hHm)
  rw [Set.inter_eq_right.mpr (fun y hy => hBt hy.1), Finset.sum_congr rfl (fun i _ => hper i),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      split_ifs
      · have := (D.tile i).localAngle_nonneg Q; positivity
      · exact le_rfl)] at hsum
  rw [hsum, hB] at hhalf
  have hnn : 0 ≤ ∑ i, (if ∀ y ∈ (D.tile i).carrier, g y ≤ c then
      (D.tile i).localAngle Q / 2 * r ^ 2 else 0) :=
    Finset.sum_nonneg fun i _ => by
      split_ifs
      · have := (D.tile i).localAngle_nonneg Q; positivity
      · exact le_rfl
  have h2 : ∀ x : ℝ, (2 : ENNReal) * ENNReal.ofReal x = ENNReal.ofReal (2 * x) := by
    intro x; rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
  rw [h2] at hhalf
  have hreal := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).mp hhalf
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_mul, ← Finset.sum_div] at hreal
  have hr2 : 0 < r ^ 2 := by positivity
  have : (∑ i ∈ Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c),
      (D.tile i).localAngle Q) * r ^ 2 = Real.pi * r ^ 2 := by linarith
  exact mul_right_cancel₀ hr2.ne' this
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
variable {N : ℕ} (D : Dissection N)
theorem no_straddle {Q : Plane} {x e : Fin N × Fin 3} (hx : x ∈ edgesAt D Q)
    (he : e ∈ edgesAt D Q) {t : ℝ} (ht : t < 0)
    (hfar : farEnd D Q e = AffineMap.lineMap Q (farEnd D Q x) t)
    {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) (hgQ : g Q = c) (hgF : g (farEnd D Q x) = c)
    (i : Fin N) (hQi : Q ∈ (D.tile i).carrier) :
    (∀ y ∈ (D.tile i).carrier, g y ≤ c) ∨ (∀ y ∈ (D.tile i).carrier, c ≤ g y) := by
  set F := farEnd D Q x
  have hQF : Q ≠ F := (farEnd_ne D hx).symm
  have hcont := continuous_functional g
  by_contra hno
  push Not at hno
  obtain ⟨⟨z₂, hz₂, hgz₂⟩, ⟨z₁, hz₁, hgz₁⟩⟩ := hno
  have hcl := tri_closure_interior (D.tile i)
  have side_pt : ∀ z ∈ (D.tile i).carrier, ∀ (p : ℝ → Prop), IsOpen {y : Plane | p (g y)} →
      p (g z) → ∃ w ∈ interior (D.tile i).carrier, p (g w) := by
    intro z hz p hp hpz
    rw [← hcl] at hz
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hz _ hp hpz
    exact ⟨w, hw2, hw1⟩
  obtain ⟨w₁, hw₁, hg₁⟩ := side_pt z₁ hz₁ (fun s => s < c)
    (isOpen_lt hcont continuous_const) hgz₁
  obtain ⟨w₂, hw₂, hg₂⟩ := side_pt z₂ hz₂ (fun s => c < s)
    (isOpen_lt continuous_const hcont) hgz₂
  set s := (c - g w₁) / (g w₂ - g w₁)
  have hden : 0 < g w₂ - g w₁ := by linarith
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hden.le
  have hs1 : s ≤ 1 := (div_le_one hden).mpr (by linarith)
  set w := AffineMap.lineMap w₁ w₂ s
  have hgw : g w = c := by
    simp only [w, AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul, s]
    field_simp
    ring
  have hw : w ∈ interior (D.tile i).carrier := by
    refine (D.tile i).convex.interior.segment_subset hw₁ hw₂ ?_
    rw [segment_eq_image_lineMap]
    exact ⟨s, ⟨hs0, hs1⟩, rfl⟩
  obtain ⟨r, hr⟩ := eq_lineMap_of_level hg hQF hgQ hgF hgw
  have hQint : Q ∉ interior (D.tile i).carrier := by
    have : Q ∈ (D.tile x.1).edge x.2 := by rw [edgesAt_edge D hx]; exact left_mem_segment ℝ _ _
    exact D.edge_point_not_interior this i
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [AffineMap.lineMap_apply_zero] at hr
    exact hQint (hr ▸ hw)
  have hseg : openSegment ℝ Q w ⊆ interior (D.tile i).carrier :=
    (D.tile i).convex.openSegment_closure_interior_subset_interior (subset_closure hQi) hw
  have hL0 : AffineMap.lineMap Q F (0 : ℝ) = Q := AffineMap.lineMap_apply_zero Q F
  have hOS : openSegment ℝ Q w = AffineMap.lineMap Q F '' openSegment ℝ (0 : ℝ) r := by
    rw [image_openSegment, hL0, hr]
  have hex : (D.tile x.1).edge x.2 = AffineMap.lineMap Q F '' segment ℝ (0 : ℝ) 1 := by
    rw [edgesAt_edge D hx, image_segment, hL0, AffineMap.lineMap_apply_one]
  have hee : (D.tile e.1).edge e.2 = AffineMap.lineMap Q F '' segment ℝ (0 : ℝ) t := by
    rw [edgesAt_edge D he, image_segment, hL0, hfar]
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · set u := max r t / 2
    have hm : max r t < 0 := max_lt hneg ht
    have hu : u ∈ openSegment ℝ (0 : ℝ) r := by
      rw [openSegment_symm, openSegment_eq_Ioo hneg]
      constructor <;> simp only [u] <;> linarith [le_max_left r t]
    have hue : u ∈ segment ℝ (0 : ℝ) t := by
      rw [segment_symm, segment_eq_Icc ht.le]
      constructor <;> simp only [u] <;> linarith [le_max_right r t]
    have hP : AffineMap.lineMap Q F u ∈ interior (D.tile i).carrier := hseg (hOS ▸ ⟨u, hu, rfl⟩)
    have hPe : AffineMap.lineMap Q F u ∈ (D.tile e.1).edge e.2 := hee ▸ ⟨u, hue, rfl⟩
    exact D.edge_point_not_interior hPe i hP
  · set u := min r 1 / 2
    have hm : 0 < min r 1 := lt_min hpos one_pos
    have hu : u ∈ openSegment ℝ (0 : ℝ) r := by
      rw [openSegment_eq_Ioo hpos]
      constructor <;> simp only [u] <;> linarith [min_le_left r 1]
    have hux : u ∈ segment ℝ (0 : ℝ) 1 := by
      rw [segment_eq_Icc zero_le_one]
      constructor <;> simp only [u] <;> linarith [min_le_right r 1]
    have hP : AffineMap.lineMap Q F u ∈ interior (D.tile i).carrier := hseg (hOS ▸ ⟨u, hu, rfl⟩)
    have hPx : AffineMap.lineMap Q F u ∈ (D.tile x.1).edge x.2 := hex ▸ ⟨u, hux, rfl⟩
    exact D.edge_point_not_interior hPx i hP
open Classical in
theorem straight_angle_sum {Q : Plane} (hQ : Q ∈ interior D.target.carrier)
    {x e : Fin N × Fin 3} (hx : x ∈ edgesAt D Q) (he : e ∈ edgesAt D Q) {t : ℝ} (ht : t < 0)
    (hfar : farEnd D Q e = AffineMap.lineMap Q (farEnd D Q x) t) :
    ∃ S : Finset (Fin N), ∑ i ∈ S, (D.tile i).localAngle Q = Real.pi := by
  obtain ⟨g, c, hg, hgQ, hgF⟩ := ray_level (farEnd_ne D hx)
  exact ⟨_, half_angle_sum D hQ hg hgQ
    (fun i hQi => no_straddle D hx he ht hfar hg hgQ hgF i hQi)⟩
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
variable {N : ℕ} (D : CongruentDissection N)
theorem localAngle_interior' {P : Plane} (hP : P ∈ interior D.target.carrier) :
    D.target.localAngle P = (0 : ℤ) * tileα D + (2 : ℤ) * Real.pi := by
  rw [Tri.localAngle_interior _ hP]; push_cast; ring
theorem vertex_counts_pos {P : Plane} {i : Fin N} {k : Fin 3} (hk : (D.tile i).pts k = P) :
    1 ≤ angleCount D P (tileα D) + angleCount D P (tileβ D) + angleCount D P (tileγ D) := by
  rcases localAngle_at_own_vertex_mem' D i k with h | h | h <;> rw [hk] at h
  · have := angleCount_pos D h; omega
  · have := angleCount_pos D h; omega
  · have := angleCount_pos D h; omega
theorem mem_tilingVertices {P : Plane} : P ∈ tilingVertices D ↔ ∃ i k, (D.tile i).pts k = P := by
  classical
  simp [tilingVertices]
variable (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hγ hirr
open Classical in
theorem c_count_even {P : Plane} {t : ℤ}
    (hP : D.target.localAngle P = (0 : ℤ) * tileα D + t * Real.pi) :
    Even ((edgesAt D.toDissection P).filter (edgeType D (tileγ D))).card := by
  have hcm := card_marked D (anglesSep_of_two_alpha D hγ hirr) P (φ := tileγ D) (Or.inr (Or.inr rfl))
  obtain ⟨h1, -⟩ := vertex_relations D hγ hirr P 0 t hP
  refine ⟨2 * angleCount D P (tileβ D) - angleCount D P (tileγ D), ?_⟩
  omega
open Classical in
theorem link_end_a {isθ : Fin N × Fin 3 → Prop} {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (h : LinkData D.toDissection isθ Q R g c) :
    vertexType D R = (3, 1, 0) ∨
      Even ((edgesAt D.toDissection R).filter (edgeType D (tileα D))).card := by
  have hcm := card_marked D (anglesSep_of_two_alpha D hγ hirr) R (φ := tileα D) (Or.inl rfl)
  obtain ⟨h1, h2⟩ := vertex_relations D hγ hirr R 0 2 (localAngle_interior' D h.end_interior)
  obtain ⟨ε, -, hRε⟩ := h.across
  have hπ := angleCount_pos D (Tri.localAngle_openSegment _ ε.2 hRε)
  obtain ⟨i, k, hik⟩ := h.end_vertex
  have hpos := vertex_counts_pos D hik
  by_cases hγ0 : angleCount D R (tileγ D) = 0
  · left
    simp only [vertexType, Prod.mk.injEq]
    omega
  · right
    exact ⟨angleCount D R (tileβ D), by omega⟩
theorem center_facts {Q : Plane} (hv : Q ∈ tilingVertices D)
    (hnc : Q ∉ Set.range D.target.pts) (ht : vertexType D Q = (0, 2, 3)) :
    Q ∈ interior D.target.carrier ∧ angleCount D Q Real.pi = 0 ∧
      angleCount D Q (2 * Real.pi) = 0 := by
  obtain ⟨i, k, hik⟩ := (mem_tilingVertices D).mp hv
  simp only [vertexType, Prod.mk.injEq] at ht
  obtain ⟨hα, hβ, hγ'⟩ := ht
  have hQt : Q ∈ D.target.carrier := by
    rw [← D.covers]
    exact Set.mem_iUnion.mpr ⟨i, hik ▸ subset_convexHull ℝ _ ⟨k, rfl⟩⟩
  by_cases hint : Q ∈ interior D.target.carrier
  · obtain ⟨-, h2⟩ := vertex_relations D hγ hirr Q 0 2 (localAngle_interior' D hint)
    exact ⟨hint, by omega, by omega⟩
  · exfalso
    have hfr : Q ∈ frontier D.target.carrier := by
      rw [frontier, D.target.isCompact.isClosed.closure_eq]; exact ⟨hQt, hint⟩
    have hloc : D.target.localAngle Q = (0 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
      rw [D.target.localAngle_frontier hfr hnc]; push_cast; ring
    obtain ⟨-, h2⟩ := vertex_relations D hγ hirr Q 0 1 hloc
    omega
theorem center_no_half {Q : Plane} (hv : Q ∈ tilingVertices D)
    (hnc : Q ∉ Set.range D.target.pts) (ht : vertexType D Q = (0, 2, 3))
    (S : Finset (Fin N)) : ∑ i ∈ S, (D.tile i).localAngle Q ≠ Real.pi := by
  classical
  obtain ⟨-, hπ, h2π⟩ := center_facts D hγ hirr hv hnc ht
  simp only [vertexType, Prod.mk.injEq] at ht
  obtain ⟨hα0, -, -⟩ := ht
  obtain ⟨hβ, hv0, hinj⟩ := angle_values D hγ hirr
  have hβγ : tileβ D ≠ tileγ D := by
    have ne : ∀ x y : Fin 5, x ≠ y →
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
          ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
    exact ne 1 2 (by decide)
  have hval : ∀ i, (D.tile i).localAngle Q = tileβ D ∨ (D.tile i).localAngle Q = tileγ D ∨
      (D.tile i).localAngle Q = 0 := by
    intro i
    rcases localAngle_mem D Q i with h | h | h | h | h | h
    · exfalso
      have := angleCount_pos D (show (D.tile i).localAngle Q = tileα D from h)
      omega
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exfalso; have := angleCount_pos D h; omega
    · exfalso; have := angleCount_pos D h; omega
    · exact Or.inr (Or.inr h)
  have hpt : ∀ i ∈ S, (D.tile i).localAngle Q =
      (if (D.tile i).localAngle Q = tileβ D then tileβ D else 0)
        + (if (D.tile i).localAngle Q = tileγ D then tileγ D else 0) := by
    intro i _
    rcases hval i with h | h | h
    · rw [if_pos h, if_neg (h ▸ hβγ), add_zero, h]
    · rw [if_neg (h ▸ hβγ.symm), if_pos h, zero_add, h]
    · rw [if_neg (by rw [h]; exact (hv0 1).symm), if_neg (by rw [h]; exact (hv0 2).symm), h,
        add_zero]
  intro hsum
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at hsum
  set kβ := (S.filter fun i => (D.tile i).localAngle Q = tileβ D).card
  set kγ := (S.filter fun i => (D.tile i).localAngle Q = tileγ D).card
  rw [hβ, hγ] at hsum
  have key : (((2 * kγ - 3 * kβ : ℤ)) : ℝ) * tileα D + (((kβ - 1 : ℤ)) : ℝ) * Real.pi = 0 := by
    push_cast; linarith
  obtain ⟨h1, h2⟩ := angle_indep hirr _ _ key
  omega
theorem center_out {Q : Plane} (hv : Q ∈ tilingVertices D)
    (hnc : Q ∉ Set.range D.target.pts) (ht : vertexType D Q = (0, 2, 3))
    (hnorel : ¬ HasRelation D.toDissection (edgeType D (tileα D))) :
    ∃ R, IsLink D.toDissection (edgeType D (tileα D)) Q R := by
  classical
  obtain ⟨hQint, hπ0, -⟩ := center_facts D hγ hirr hv hnc ht
  have hnrel : ∀ j : Fin N, ∀ m : Fin 3,
      Q ∉ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)) := by
    intro j m hQ
    have := angleCount_pos D (Tri.localAngle_openSegment _ m hQ)
    omega
  have hnolone : ∀ e ∈ edgesAt D.toDissection Q, ∃ e' ∈ edgesAt D.toDissection Q,
      Partners D.toDissection Q e e' := by
    intro e he
    by_contra hno
    push Not at hno
    obtain ⟨-, -, -, -, -, -, e₂, -, hQe₂⟩ := lonely_relint D.toDissection hQint he
      (fun e' he' hne hray => hno e' he' ⟨hne.symm, hray⟩)
    exact hnrel _ _ hQe₂
  have hcm := card_marked D (anglesSep_of_two_alpha D hγ hirr) Q (φ := tileα D) (Or.inl rfl)
  simp only [vertexType, Prod.mk.injEq] at ht
  obtain ⟨hα0, hβ2, hγ3⟩ := ht
  obtain ⟨x, hx, y, hy, hxy, hθx, hθy⟩ : ∃ x ∈ edgesAt D.toDissection Q,
      ∃ y ∈ edgesAt D.toDissection Q, Partners D.toDissection Q x y ∧
        edgeType D (tileα D) x ∧ ¬ edgeType D (tileα D) y := by
    by_contra hno
    push Not at hno
    have hpar := card_filter_mod_two (edgesAt D.toDissection Q) (Partners D.toDissection Q)
      (edgeType D (tileα D)) (fun x _ y _ h => ⟨h.1.symm, sameRayAt_symm _ h.2⟩)
      (fun x h => h.1 rfl)
      (fun x hx y hy z hz hxy hxz => by
        by_contra hyz
        exact sameRayAt_unique _ hx hy hz hxy.1.symm hxz.1.symm hyz hxy.2 hxz.2)
      (fun x hx y hy hxy hθ => hno x hx y hy hxy hθ) ∅ (fun x => by
        simp only [Finset.notMem_empty, false_iff, not_and, not_forall, not_not]
        intro hx _
        obtain ⟨e', he', h'⟩ := hnolone x hx
        exact ⟨e', he', h'⟩)
    rw [Finset.card_empty] at hpar
    omega
  have hback : ∀ e : Fin N × Fin 3, Q ∈ (D.tile e.1).edge e.2 →
      ∀ z ∈ (D.tile e.1).edge e.2, Q ∉ openSegment ℝ z (farEnd D.toDissection Q x) := by
    intro e hQe z hz hQz
    set F := farEnd D.toDissection Q x
    have hQF : Q ≠ F := (farEnd_ne _ hx).symm
    have he : e ∈ edgesAt D.toDissection Q := by
      rw [Tri.edge, ← insert_endpoints_openSegment] at hQe
      rcases hQe with h | h | h
      · exact (mem_edgesAt _).mpr (Or.inl h.symm)
      · exact (mem_edgesAt _).mpr (Or.inr h.symm)
      · exact absurd h (hnrel e.1 e.2)
    obtain ⟨g, c, hg, hgQ, hgF⟩ := ray_level (farEnd_ne _ hx)
    have hgz : g z = c := by
      obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hQz
      have h1 := hgQ
      rw [← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hgF] at h1
      have : a * (g z - c) = 0 := by linear_combination h1 - c * hab
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    obtain ⟨tz, htz⟩ := eq_lineMap_of_level hg hQF hgQ hgF hgz
    have htz0 : tz < 0 := by
      have h0 : AffineMap.lineMap Q F (0 : ℝ) ∈
          openSegment ℝ (AffineMap.lineMap Q F tz) (AffineMap.lineMap Q F (1 : ℝ)) := by
        rw [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, ← htz]; exact hQz
      rw [← image_openSegment, (AffineMap.lineMap_injective ℝ hQF).mem_set_image] at h0
      rcases lt_trichotomy tz 1 with h | h | h
      · rw [openSegment_eq_Ioo h] at h0; exact h0.1
      · rw [h, openSegment_same] at h0; norm_num at h0
      · rw [openSegment_symm, openSegment_eq_Ioo h] at h0; linarith [h0.1]
    have hzQ : z ≠ Q := by
      intro h
      have : AffineMap.lineMap Q F tz = AffineMap.lineMap Q F (0 : ℝ) := by
        rw [← htz, h, AffineMap.lineMap_apply_zero]
      exact htz0.ne (AffineMap.lineMap_injective ℝ hQF this)
    rw [edgesAt_edge _ he, segment_eq_image_lineMap] at hz
    obtain ⟨s, hs, hzs⟩ := hz
    have hs0 : 0 < s := by
      rcases hs.1.lt_or_eq with h | h
      · exact h
      · rw [← h, AffineMap.lineMap_apply_zero] at hzs; exact absurd hzs.symm hzQ
    have hgfe : g (farEnd D.toDissection Q e) = c := by
      have := congrArg g hzs
      rw [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, smul_eq_mul, hgQ, hgz]
        at this
      have h' : s * (g (farEnd D.toDissection Q e) - c) = 0 := by linarith
      rcases mul_eq_zero.mp h' with h | h
      · linarith
      · linarith
    obtain ⟨te, hte⟩ := eq_lineMap_of_level hg hQF hgQ hgF hgfe
    have hte0 : te < 0 := by
      rw [hte, lineMap_lineMap_eq, htz] at hzs
      have := AffineMap.lineMap_injective ℝ hQF hzs
      nlinarith
    obtain ⟨S, hS⟩ := straight_angle_sum D.toDissection hQint hx he hte0 hte
    exact center_no_half D hγ hirr hv hnc (by simp [vertexType, hα0, hβ2, hγ3]) S hS
  rcases extend_link D.toDissection (edgeType D (tileα D)) hx hy hxy.1.symm hxy.2 hθx hθy
    hback with h | h
  · exact h
  · exact absurd h hnorel
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
variable {N : ℕ} (D : Dissection N)
theorem side_level :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g (D.target.pts 0) = c ∧ g (D.target.pts 1) = c ∧
      c < g (D.target.pts 2) ∧ ∀ y ∈ D.target.carrier, c ≤ g y := by
  obtain ⟨g, c, hg, hline, h2⟩ := edge_level_oriented D.target 0
  have h0 : g (D.target.pts 0) = c := hline _ (left_mem_segment _ _ _)
  have h1 : g (D.target.pts 1) = c := hline _ (right_mem_segment _ _ _)
  refine ⟨g, c, hg, h0, h1, h2, fun y hy => ?_⟩
  have := D.target.carrier_subset_halfplane (-g) (-c) (fun i => by
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    rcases fin3_cases3 i 0 with rfl | rfl | rfl
    · exact h0.ge
    · exact h1.ge
    · exact h2.le) y hy
  simpa using this
theorem side_chain {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hside : ∀ y ∈ D.target.carrier, c ≤ g y)
    {e : Fin N × Fin 3} (h1 : g ((D.tile e.1).pts e.2) = c)
    (h2 : g ((D.tile e.1).pts (e.2 + 1)) = c) : e ∈ D.lineChain (-g) (-c) := by
  refine Dissection.mem_lineChain.mpr ⟨by simp [h1], by simp [h2], fun i => ?_⟩
  have hmem : (D.tile e.1).pts i ∈ D.target.carrier := by
    rw [← D.covers]
    exact Set.mem_iUnion.mpr ⟨e.1, subset_convexHull ℝ _ ⟨i, rfl⟩⟩
  simpa using hside _ hmem
set_option maxHeartbeats 4000000 in
open Classical in
theorem side_start (isθ : Fin N × Fin 3 → Prop) (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts 0) (D.target.pts 1))
    {ec en : Fin N × Fin 3} (hec : ec ∈ part) (hen : en ∈ part)
    (hθc : isθ ec) (hθn : ¬ isθ en)
    (hgood : ∀ Q ∈ openSegment ℝ (D.target.pts 0) (D.target.pts 1),
      (∃ i k, (D.tile i).pts k = Q) →
        (∀ j : Fin N, ∀ m : Fin 3, Q ∉ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)))
          ∧ Even ((edgesAt D Q).filter isθ).card)
    (hnorel : ¬ HasRelation D isθ) :
    ∃ Q₀ ∈ frontier D.target.carrier, ∃ R, IsLink D isθ Q₀ R := by
  obtain ⟨g, c, hg, hT0, hT1, hT2, hside⟩ := side_level D
  set T0 := D.target.pts 0
  set T1 := D.target.pts 1
  have hT01 : T0 ≠ T1 := tri_pts_succ_ne D.target 0
  have hng : -g ≠ 0 := neg_ne_zero.mpr hg
  have hnT0 : (-g) T0 = -c := by simp [hT0]
  have hnT1 : (-g) T1 = -c := by simp [hT1]
  have hL0 : AffineMap.lineMap T0 T1 (0 : ℝ) = T0 := AffineMap.lineMap_apply_zero T0 T1
  have hsegI : segment ℝ T0 T1 = AffineMap.lineMap T0 T1 '' Icc (0 : ℝ) 1 := by
    rw [← segment_eq_Icc zero_le_one, image_segment, hL0, AffineMap.lineMap_apply_one]
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ T0 T1 := fun e he => by
    rw [← hcov]; exact Set.subset_biUnion_of_mem (u := fun e => (D.tile e.1).edge e.2) he
  have hline : ∀ y ∈ segment ℝ T0 T1, g y = c := by
    intro y hy
    rw [hsegI] at hy
    obtain ⟨t, -, rfl⟩ := hy
    exact level_lineMap hT0 hT1 t
  have hchain : ∀ e ∈ part, e ∈ D.lineChain (-g) (-c) := fun e he =>
    side_chain D hside (hline _ (hsub e he (left_mem_segment _ _ _)))
      (hline _ (hsub e he (right_mem_segment _ _ _)))
  have mem : ∀ e ∈ D.lineChain (-g) (-c), ∀ t,
      AffineMap.lineMap T0 T1 t ∈ (D.tile e.1).edge e.2 ↔
        t ∈ Icc (edgeLo T0 T1 (D.tile e.1) e.2) (edgeHi T0 T1 (D.tile e.1) e.2) :=
    fun e he t => chain_mem_edge_iff D hng hT01 hnT0 hnT1 he t
  have hlt : ∀ e ∈ D.lineChain (-g) (-c),
      edgeLo T0 T1 (D.tile e.1) e.2 < edgeHi T0 T1 (D.tile e.1) e.2 :=
    fun e he => chain_lo_lt_hi D hng hT01 hnT0 hnT1 he
  have ov : ∀ e ∈ D.lineChain (-g) (-c), ∀ e' ∈ D.lineChain (-g) (-c),
      max (edgeLo T0 T1 (D.tile e.1) e.2) (edgeLo T0 T1 (D.tile e'.1) e'.2)
        < min (edgeHi T0 T1 (D.tile e.1) e.2) (edgeHi T0 T1 (D.tile e'.1) e'.2) → e = e' :=
    fun e he e' he' h => lineChain_eq_of_overlap D hng hT01 hnT0 hnT1 he he' h
  have hI : ∀ e ∈ part, 0 ≤ edgeLo T0 T1 (D.tile e.1) e.2 ∧ edgeHi T0 T1 (D.tile e.1) e.2 ≤ 1 := by
    intro e he
    have key : ∀ t, t ∈ Icc (edgeLo T0 T1 (D.tile e.1) e.2) (edgeHi T0 T1 (D.tile e.1) e.2) →
        t ∈ Icc (0 : ℝ) 1 := by
      intro t ht
      have := hsub e he ((mem e (hchain e he) t).mpr ht)
      rw [hsegI] at this
      obtain ⟨s, hs, hst⟩ := this
      rwa [← AffineMap.lineMap_injective ℝ hT01 hst]
    have h := hlt e (hchain e he)
    exact ⟨(key _ ⟨le_rfl, h.le⟩).1, (key _ ⟨h.le, le_rfl⟩).2⟩
  set U := ⋃ e ∈ part.filter (isθ), (D.tile e.1).edge e.2
  set V := ⋃ e ∈ part.filter (fun e => ¬ isθ e), (D.tile e.1).edge e.2
  have hclosed : ∀ e : Fin N × Fin 3, IsClosed ((D.tile e.1).edge e.2) := fun e => by
    rw [Tri.edge, segment_eq_image_lineMap]
    exact (isCompact_Icc.image (AffineMap.lineMap_continuous)).isClosed
  have hU : IsClosed U := isClosed_biUnion_finset fun e _ => hclosed e
  have hV : IsClosed V := isClosed_biUnion_finset fun e _ => hclosed e
  have hUV : segment ℝ T0 T1 ⊆ U ∪ V := by
    rw [← hcov]
    intro y hy
    obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy
    by_cases hθ : isθ e
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hθ⟩, hye⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hθ⟩, hye⟩)
  have hpt : ∀ e ∈ part, (D.tile e.1).pts e.2 ∈ segment ℝ T0 T1 ∩ (D.tile e.1).edge e.2 :=
    fun e he => ⟨hsub e he (left_mem_segment _ _ _), left_mem_segment _ _ _⟩
  obtain ⟨Q₀, hQ₀s, hQ₀U, hQ₀V⟩ := isPreconnected_closed_iff.mp
    (convex_segment T0 T1).isPreconnected U V hU hV hUV
    ⟨_, (hpt ec hec).1, Set.mem_iUnion₂.mpr ⟨ec, Finset.mem_filter.mpr ⟨hec, hθc⟩, (hpt ec hec).2⟩⟩
    ⟨_, (hpt en hen).1, Set.mem_iUnion₂.mpr ⟨en, Finset.mem_filter.mpr ⟨hen, hθn⟩, (hpt en hen).2⟩⟩
  obtain ⟨x, hx, hQx⟩ := Set.mem_iUnion₂.mp hQ₀U
  obtain ⟨y, hy, hQy⟩ := Set.mem_iUnion₂.mp hQ₀V
  obtain ⟨hxp, hθx⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyp, hθy⟩ := Finset.mem_filter.mp hy
  have hxc := hchain x hxp
  have hyc := hchain y hyp
  have hxy : x ≠ y := fun h => hθy (h ▸ hθx)
  rw [hsegI] at hQ₀s
  obtain ⟨q, -, rfl⟩ := hQ₀s
  have hqx := (mem x hxc q).mp hQx
  have hqy := (mem y hyc q).mp hQy
  have hno := fun h => hxy (ov x hxc y hyc h)
  have hlx := hlt x hxc
  have hly := hlt y hyc
  have hsplit : (edgeHi T0 T1 (D.tile x.1) x.2 = q ∧ edgeLo T0 T1 (D.tile y.1) y.2 = q) ∨
      (edgeLo T0 T1 (D.tile x.1) x.2 = q ∧ edgeHi T0 T1 (D.tile y.1) y.2 = q) := by
    by_contra hc
    apply hno
    rcases le_total (edgeLo T0 T1 (D.tile x.1) x.2) (edgeLo T0 T1 (D.tile y.1) y.2) with h1 | h1 <;>
    rcases le_total (edgeHi T0 T1 (D.tile x.1) x.2) (edgeHi T0 T1 (D.tile y.1) y.2) with h2 | h2
    · rw [max_eq_right h1, min_eq_left h2]
      by_contra h; push Not at h
      exact hc (Or.inl ⟨by linarith [hqx.2, hqy.1], by linarith [hqx.2, hqy.1]⟩)
    · rw [max_eq_right h1, min_eq_right h2]; linarith
    · rw [max_eq_left h1, min_eq_left h2]; linarith
    · rw [max_eq_left h1, min_eq_right h2]
      by_contra h; push Not at h
      exact hc (Or.inr ⟨by linarith [hqx.1, hqy.2], by linarith [hqx.1, hqy.2]⟩)
  obtain ⟨hx0, hx1⟩ := hI x hxp
  obtain ⟨hy0, hy1⟩ := hI y hyp
  have hq0 : 0 < q := by rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hq1 : q < 1 := by rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  set Q₀ := AffineMap.lineMap T0 T1 q
  have hQ₀open : Q₀ ∈ openSegment ℝ T0 T1 := by
    rw [openSegment_eq_image_lineMap]; exact ⟨q, ⟨hq0, hq1⟩, rfl⟩
  have hgQ₀ : g Q₀ = c := level_lineMap hT0 hT1 q
  have hQ₀fr : Q₀ ∈ frontier D.target.carrier :=
    tri_side_subset_frontier D.target 0 (openSegment_subset_segment _ _ _ hQ₀open)
  have hQ₀nc : Q₀ ∉ Set.range D.target.pts := by
    rintro ⟨m, hm⟩
    exact Tri.vertex_not_mem_openSegment D.target m 0 (hm ▸ hQ₀open)
  refine ⟨Q₀, hQ₀fr, ?_⟩
  have hxe : x ∈ edgesAt D Q₀ := by
    rcases hsplit with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact (edgesAt_of_hi D hng hT01 hnT0 hnT1 hxc h1).1
    · exact (edgesAt_of_lo D hng hT01 hnT0 hnT1 hxc h1).1
  have hye : y ∈ edgesAt D Q₀ := by
    rcases hsplit with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact (edgesAt_of_lo D hng hT01 hnT0 hnT1 hyc h2).1
    · exact (edgesAt_of_hi D hng hT01 hnT0 hnT1 hyc h2).1
  have honline : ∀ e ∈ edgesAt D Q₀, g (farEnd D Q₀ e) = c →
      e = x ∨ e = y := by
    intro e he hgF
    obtain ⟨n1, n2⟩ := level_far D he hgQ₀ hgF
    have hec' := side_chain D hside n1 n2
    have hle := hlt e hec'
    rcases end_param_at D hT01 he with hl | hh
    · have he1 : q < edgeHi T0 T1 (D.tile e.1) e.2 := by rw [← hl]; exact hle
      rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; apply ov e hec' y hyc; rw [hl, h2, max_self]
        exact lt_min he1 (by rw [← h2]; exact hly)
      · left; apply ov e hec' x hxc; rw [hl, h1, max_self]
        exact lt_min he1 (by rw [← h1]; exact hlx)
    · have he1 : edgeLo T0 T1 (D.tile e.1) e.2 < q := by rw [← hh]; exact hle
      rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; apply ov e hec' x hxc; rw [hh, h1, min_self]
        exact max_lt he1 (by rw [← h1]; exact hlx)
      · right; apply ov e hec' y hyc; rw [hh, h2, min_self]
        exact max_lt he1 (by rw [← h2]; exact hly)
  have hcoord : ∀ z, g z - c = D.target.basis.coord (0 + 2) z * (g (D.target.pts (0 + 2)) - c) :=
    level_eq_coord D.target g c (0 + 2) (by rw [show (0 : Fin 3) + 2 + 1 = 0 from rfl]; exact hT0)
      (by rw [show (0 : Fin 3) + 2 + 2 = 0 + 1 from rfl]; exact hT1)
  have hinto : ∀ e ∈ edgesAt D Q₀, c < g (farEnd D Q₀ e) →
      ∃ τ ∈ Ioo (0 : ℝ) 1, AffineMap.lineMap Q₀ (farEnd D Q₀ e) τ ∈
        interior D.target.carrier := by
    intro e he hF
    have hpos : 0 < D.target.basis.coord (0 + 2) (farEnd D Q₀ e) := by
      have := hcoord (farEnd D Q₀ e)
      have h2 : 0 < g (D.target.pts (0 + 2)) - c := by
        rw [show (0 : Fin 3) + 2 = 2 from rfl]; linarith
      by_contra hc; push Not at hc; nlinarith
    obtain ⟨τ0, hτ0, hint⟩ := Tri.lineMap_mem_interior D.target 0 hQ₀open hpos
    refine ⟨min τ0 1 / 2, ⟨by have := lt_min hτ0 one_pos; linarith,
      by have := min_le_right τ0 1; linarith⟩, hint _ (by have := lt_min hτ0 one_pos; linarith)
      (by have := min_le_left τ0 1; linarith)⟩
  obtain ⟨hnrel, heven⟩ := hgood Q₀ hQ₀open (by
    rcases (mem_edgesAt _).mp hxe with h | h
    · exact ⟨_, _, h⟩
    · exact ⟨_, _, h⟩)
  have hlone_line : ∀ e ∈ edgesAt D Q₀,
      (∀ e' ∈ edgesAt D Q₀, ¬ Partners D Q₀ e e') →
        g (farEnd D Q₀ e) = c := by
    intro e he hl
    have hFt : farEnd D Q₀ e ∈ D.target.carrier := by
      rw [← D.covers]
      refine Set.mem_iUnion.mpr ⟨e.1, (D.tile e.1).edge_subset_carrier e.2 ?_⟩
      rw [edgesAt_edge _ he]; exact right_mem_segment _ _ _
    rcases (hside _ hFt).lt_or_eq with hlt' | heq
    · exfalso
      obtain ⟨τ, hτ, hint⟩ := hinto e he hlt'
      obtain ⟨g₀, c₀, hg₀, hQ₀', hF₀⟩ := ray_level (farEnd_ne _ he)
      obtain ⟨g', c', hg', hQ', hF', hec'⟩ : ∃ (g' : Plane →ₗ[ℝ] ℝ) (c' : ℝ), g' ≠ 0 ∧
          g' Q₀ = c' ∧ g' (farEnd D Q₀ e) = c' ∧ e ∈ D.lineChain g' c' := by
        rcases edgesAt_chain _ he hQ₀' hF₀ with h' | h'
        · exact ⟨g₀, c₀, hg₀, hQ₀', hF₀, h'⟩
        · exact ⟨-g₀, -c₀, neg_ne_zero.mpr hg₀, by simp [hQ₀'], by simp [hF₀], h'⟩
      obtain ⟨e₂, -, hQe₂⟩ := lonely_openSegment _ he hg' hQ' hF' hec'
        (fun e' he' hne hray => hl e' he' ⟨hne.symm, hray⟩) hτ hint
      exact hnrel _ _ hQe₂
    · exact heq.symm
  have hgx : g (farEnd D Q₀ x) = c := by
    rcases hsplit with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [(edgesAt_of_hi D hng hT01 hnT0 hnT1 hxc h1).2]
      exact level_lineMap hT0 hT1 _
    · rw [(edgesAt_of_lo D hng hT01 hnT0 hnT1 hxc h1).2]
      exact level_lineMap hT0 hT1 _
  have hnxy : ¬ SameRayAt D Q₀ x y := by
    rintro ⟨t, ht, hFt⟩
    rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have fx := (edgesAt_of_hi D hng hT01 hnT0 hnT1 hxc h1).2
      have fy := (edgesAt_of_lo D hng hT01 hnT0 hnT1 hyc h2).2
      rw [fx, fy, lineMap_params] at hFt
      have := AffineMap.lineMap_injective ℝ hT01 hFt
      nlinarith
    · have fx := (edgesAt_of_lo D hng hT01 hnT0 hnT1 hxc h1).2
      have fy := (edgesAt_of_hi D hng hT01 hnT0 hnT1 hyc h2).2
      rw [fx, fy, lineMap_params] at hFt
      have := AffineMap.lineMap_injective ℝ hT01 hFt
      nlinarith
  have hlone_xy : ∀ u ∈ ({x, y} : Finset (Fin N × Fin 3)),
      ∀ e' ∈ edgesAt D Q₀, ¬ Partners D Q₀ u e' := by
    intro u hu e' he' ⟨hne, hray⟩
    have hgu : g (farEnd D Q₀ u) = c := by
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hgx
      · rw [Finset.mem_singleton.mp hu]
        obtain ⟨n1, n2⟩ := lineChain_ends D hyc
        rcases (mem_edgesAt _).mp hye with h | h
        · rw [farEnd, if_pos h]; simpa using n2
        · have hne' : (D.tile y.1).pts y.2 ≠ Q₀ := fun h0 =>
            tri_pts_succ_ne (D.tile y.1) y.2 (h0.trans h.symm)
          rw [farEnd, if_neg hne']; simpa using n1
    obtain ⟨t, ht, hFt⟩ := hray
    have hge : g (farEnd D Q₀ e') = c := by
      rw [hFt]; exact level_lineMap hgQ₀ hgu t
    have hray' : SameRayAt D Q₀ u e' := ⟨t, ht, hFt⟩
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rcases honline e' he' hge with h | h
      · exact hne h.symm
      · exact hnxy (h ▸ hray')
    · rw [Finset.mem_singleton.mp hu] at hne hray'
      rcases honline e' he' hge with h | h
      · exact hnxy (sameRayAt_symm _ (h ▸ hray'))
      · exact hne h.symm
  have hxlone : ∀ e' ∈ edgesAt D Q₀, ¬ Partners D Q₀ x e' :=
    hlone_xy x (by simp)
  have huniq : ∀ e ∈ edgesAt D Q₀, isθ e →
      (∀ e' ∈ edgesAt D Q₀, ¬ Partners D Q₀ e e') → e = x := by
    intro e he hθ hl
    rcases honline e he (hlone_line e he hl) with h | h
    · exact h
    · exact absurd (h ▸ hθ) hθy
  obtain ⟨x', hx', y', hy', hxy', hθx', hθy'⟩ := mixed_of_parity D
    (isθ) hxe hθx hxlone huniq heven
  have hgx' : c < g (farEnd D Q₀ x') := by
    have hFt : farEnd D Q₀ x' ∈ D.target.carrier := by
      rw [← D.covers]
      refine Set.mem_iUnion.mpr ⟨x'.1, (D.tile x'.1).edge_subset_carrier x'.2 ?_⟩
      rw [edgesAt_edge _ hx']; exact right_mem_segment _ _ _
    rcases (hside _ hFt).lt_or_eq with h | h
    · exact h
    · exfalso
      rcases honline x' hx' h.symm with rfl | rfl
      · exact hlone_xy _ (by simp) y' hy' hxy'
      · exact hlone_xy _ (by simp) y' hy' hxy'
  have hback : ∀ e : Fin N × Fin 3, Q₀ ∈ (D.tile e.1).edge e.2 →
      ∀ z ∈ (D.tile e.1).edge e.2, Q₀ ∉ openSegment ℝ z (farEnd D Q₀ x') := by
    intro e _ z hz hQz
    have hzt : z ∈ D.target.carrier := by
      rw [← D.covers]
      exact Set.mem_iUnion.mpr ⟨e.1, (D.tile e.1).edge_subset_carrier e.2 hz⟩
    obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hQz
    have h1 := hgQ₀
    rw [← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    have h3 := mul_le_mul_of_nonneg_left (hside z hzt) ha.le
    have h4 := mul_lt_mul_of_pos_left hgx' hb
    have h5 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    linarith
  rcases extend_link D (isθ) hx' hy' hxy'.1.symm hxy'.2 hθx' hθy'
    hback with h | h
  · exact h
  · exact absurd h hnorel
section Specific
variable {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
  (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hγ hirr
open Classical in
theorem boundary_start (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts 0) (D.target.pts 1))
    {ec en : Fin N × Fin 3} (hec : ec ∈ part) (hen : en ∈ part)
    (hθc : edgeType D (tileγ D) ec) (hθn : ¬ edgeType D (tileγ D) en)
    (hnorel : ¬ HasRelation D.toDissection (edgeType D (tileγ D))) :
    ∃ Q₀ ∈ frontier D.target.carrier, ∃ R, IsLink D.toDissection (edgeType D (tileγ D)) Q₀ R := by
  refine side_start D.toDissection (edgeType D (tileγ D)) part hcov hec hen hθc hθn ?_ hnorel
  intro Q hQ ⟨i, k, hik⟩
  have hQfr : Q ∈ frontier D.target.carrier :=
    tri_side_subset_frontier D.target 0 (openSegment_subset_segment _ _ _ hQ)
  have hQnc : Q ∉ Set.range D.target.pts := by
    rintro ⟨m, hm⟩
    exact Tri.vertex_not_mem_openSegment D.target m 0 (hm ▸ hQ)
  have hloc : D.target.localAngle Q = (0 : ℤ) * tileα D + (1 : ℤ) * Real.pi := by
    rw [D.target.localAngle_frontier hQfr hQnc]; push_cast; ring
  have hrel := vertex_relations D hγ hirr Q 0 1 hloc
  have hpos := vertex_counts_pos D hik
  refine ⟨fun j m hQ' => ?_, c_count_even D hγ hirr hloc⟩
  have := angleCount_pos D (Tri.localAngle_openSegment _ m hQ')
  omega
end Specific
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
theorem model_sides_pos :
    0 < dist (D.model.pts 1) (D.model.pts 2) ∧ 0 < dist (D.model.pts 2) (D.model.pts 0) ∧
      0 < dist (D.model.pts 0) (D.model.pts 1) := by
  have hne : ∀ i j : Fin 3, i ≠ j → D.model.pts i ≠ D.model.pts j :=
    fun i j h e => h (D.model.indep.injective e)
  exact ⟨dist_pos.mpr (hne 1 2 (by decide)), dist_pos.mpr (hne 2 0 (by decide)),
    dist_pos.mpr (hne 0 1 (by decide))⟩
variable (hsep : AnglesSep D)
include hsep
open Classical in
theorem relation_counts {φ : ℝ} (h : HasRelation D.toDissection (edgeType D φ)) :
    ∃ (s₁ s₂ : Finset (Fin N × Fin 3)), (∀ e ∈ s₁, edgeType D φ e) ∧
      (∃ e ∈ s₂, ¬ edgeType D φ e) ∧
      ((s₁.filter (edgeType D (tileα D))).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
        + ((s₁.filter (edgeType D (tileβ D))).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
        + ((s₁.filter (edgeType D (tileγ D))).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
      = ((s₂.filter (edgeType D (tileα D))).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
        + ((s₂.filter (edgeType D (tileβ D))).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
        + ((s₂.filter (edgeType D (tileγ D))).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1) := by
  obtain ⟨s₁, s₂, h1, h2, hsum⟩ := h
  refine ⟨s₁, s₂, h1, h2, ?_⟩
  have w1 := side_walk_counts_sep D hsep s₁ _ rfl
  have w2 := side_walk_counts_sep D hsep s₂ _ rfl
  unfold edgeType
  rw [← w1, ← w2]
  exact hsum
theorem types_ne : tileα D ≠ tileβ D ∧ tileα D ≠ tileγ D ∧ tileβ D ≠ tileγ D := by
  have hinj := hsep.2
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  exact ⟨ne 0 1 (by decide), ne 0 2 (by decide), ne 1 2 (by decide)⟩
open Classical in
theorem c_relation_of_edges (h : HasRelation D.toDissection (edgeType D (tileγ D))) :
    ∃ J p q : ℕ, 0 < J ∧
    (J : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
      = p * dist (D.model.pts 1) (D.model.pts 2) + q * dist (D.model.pts 2) (D.model.pts 0) := by
  obtain ⟨hαβ, hαγ, hβγ⟩ := types_ne D hsep
  obtain ⟨ha, hb, hc⟩ := model_sides_pos D
  obtain ⟨s₁, s₂, h1, ⟨e, he, hne⟩, hrel⟩ :=
    relation_counts D hsep h
  have f1 : s₁.filter (edgeType D (tileα D)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx h' => hαγ (h'.symm.trans (h1 x hx))
  have f2 : s₁.filter (edgeType D (tileβ D)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx h' => hβγ (h'.symm.trans (h1 x hx))
  have f3 : s₁.filter (edgeType D (tileγ D)) = s₁ := Finset.filter_true_of_mem h1
  rw [f1, f2, f3, Finset.card_empty, Nat.cast_zero, zero_mul, zero_mul, zero_add, zero_add] at hrel
  set pα := (s₂.filter (edgeType D (tileα D))).card
  set pβ := (s₂.filter (edgeType D (tileβ D))).card
  set pγ := (s₂.filter (edgeType D (tileγ D))).card
  have hpos : 1 ≤ pα + pβ := by
    rcases localAngle_at_own_vertex_mem' D e.1 (e.2 + 2) with h | h | h
    · have : 1 ≤ pα := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩; omega
    · have : 1 ≤ pβ := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩; omega
    · exact absurd h hne
  have hlt : pγ < s₁.card := by
    by_contra hle
    push Not at hle
    have h3 : (s₁.card : ℝ) ≤ pγ := by exact_mod_cast hle
    have h4 : (1 : ℝ) ≤ pα + pβ := by exact_mod_cast hpos
    have h5 : (0 : ℝ) < pα * dist (D.model.pts 1) (D.model.pts 2)
        + pβ * dist (D.model.pts 2) (D.model.pts 0) := by
      rcases Nat.eq_zero_or_pos pα with h0 | h0
      · have : (1 : ℝ) ≤ pβ := by rw [h0] at hpos; exact_mod_cast (by omega : 1 ≤ pβ)
        rw [h0, Nat.cast_zero, zero_mul, zero_add]; nlinarith
      · have : (1 : ℝ) ≤ pα := by exact_mod_cast h0
        have : (0 : ℝ) ≤ pβ := Nat.cast_nonneg _
        nlinarith
    nlinarith
  refine ⟨s₁.card - pγ, pα, pβ, by omega, ?_⟩
  rw [Nat.cast_sub hlt.le]
  linarith
open Classical in
theorem a_relation_of_edges (h : HasRelation D.toDissection (edgeType D (tileα D))) :
    ∃ J p q : ℕ, 0 < J ∧
    (J : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      = p * dist (D.model.pts 2) (D.model.pts 0) + q * dist (D.model.pts 0) (D.model.pts 1) := by
  obtain ⟨hαβ, hαγ, hβγ⟩ := types_ne D hsep
  obtain ⟨ha, hb, hc⟩ := model_sides_pos D
  obtain ⟨s₁, s₂, h1, ⟨e, he, hne⟩, hrel⟩ :=
    relation_counts D hsep h
  have f1 : s₁.filter (edgeType D (tileα D)) = s₁ := Finset.filter_true_of_mem h1
  have f2 : s₁.filter (edgeType D (tileβ D)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx h' => hαβ ((h1 x hx).symm.trans h')
  have f3 : s₁.filter (edgeType D (tileγ D)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx h' => hαγ ((h1 x hx).symm.trans h')
  rw [f1, f2, f3, Finset.card_empty, Nat.cast_zero, zero_mul, zero_mul, add_zero, add_zero] at hrel
  set pα := (s₂.filter (edgeType D (tileα D))).card
  set pβ := (s₂.filter (edgeType D (tileβ D))).card
  set pγ := (s₂.filter (edgeType D (tileγ D))).card
  have hpos : 1 ≤ pβ + pγ := by
    rcases localAngle_at_own_vertex_mem' D e.1 (e.2 + 2) with h | h | h
    · exact absurd h hne
    · have : 1 ≤ pβ := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩; omega
    · have : 1 ≤ pγ := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩; omega
  have hlt : pα < s₁.card := by
    by_contra hle
    push Not at hle
    have h3 : (s₁.card : ℝ) ≤ pα := by exact_mod_cast hle
    have h5 : (0 : ℝ) < pβ * dist (D.model.pts 2) (D.model.pts 0)
        + pγ * dist (D.model.pts 0) (D.model.pts 1) := by
      rcases Nat.eq_zero_or_pos pβ with h0 | h0
      · have : (1 : ℝ) ≤ pγ := by rw [h0] at hpos; exact_mod_cast (by omega : 1 ≤ pγ)
        rw [h0, Nat.cast_zero, zero_mul, zero_add]; nlinarith
      · have : (1 : ℝ) ≤ pβ := by exact_mod_cast h0
        have : (0 : ℝ) ≤ pγ := Nat.cast_nonneg _
        nlinarith
    nlinarith
  refine ⟨s₁.card - pα, pβ, pγ, by omega, ?_⟩
  rw [Nat.cast_sub hlt.le]
  linarith
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
noncomputable def swapAC {N : ℕ} (D : CongruentDissection N) : CongruentDissection N where
  target := ⟨![D.target.pts 2, D.target.pts 1, D.target.pts 0], by
    have h := tri_indep D.target
    have : ![D.target.pts 2, D.target.pts 1, D.target.pts 0] =
        ![D.target.pts 0, D.target.pts 1, D.target.pts 2] ∘ (Equiv.swap (0 : Fin 3) 2) := by
      ext i; fin_cases i <;> rfl
    rw [this]
    exact h.comp_embedding (Equiv.swap (0 : Fin 3) 2).toEmbedding⟩
  tile := D.tile
  covers := by
    rw [D.covers]
    show convexHull ℝ (Set.range D.target.pts) =
      convexHull ℝ (Set.range ![D.target.pts 2, D.target.pts 1, D.target.pts 0])
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
  interiors_disjoint := D.interiors_disjoint
  model := D.model
  tiles_congruent := D.tiles_congruent
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set EuclideanGeometry
variable {N : ℕ} (D : CongruentDissection N)
theorem swapAC_carrier : (swapAC D).target.carrier = D.target.carrier := by
  show convexHull ℝ (Set.range ![D.target.pts 2, D.target.pts 1, D.target.pts 0]) =
    convexHull ℝ (Set.range D.target.pts)
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
theorem corner_not_interior (m : Fin 3) : D.target.pts m ∉ interior D.target.carrier := by
  intro h
  have := (Tri.mem_interior_iff_coord_pos D.target _).mp h (m + 1)
  rw [Tri.coord_vertex] at this
  have hne : ¬ (m + 1 = m) := by fin_cases m <;> decide
  simp [hne] at this
theorem isLink_of_swapAC {isθ : Fin N × Fin 3 → Prop} {Q R : Plane}
    (h : IsLink (swapAC D).toDissection isθ Q R) : IsLink D.toDissection isθ Q R := by
  obtain ⟨g, c, h⟩ := h
  exact ⟨g, c, ⟨h.ne, h.hg, h.hQ, h.hR, h.cov, h.inner, h.start, h.past, h.across⟩⟩
theorem link_mem_vertices {isθ : Fin N × Fin 3 → Prop} {u w : Plane}
    (h : IsLink D.toDissection isθ u w) : u ∈ tilingVertices D ∧ w ∈ tilingVertices D := by
  obtain ⟨g, c, h⟩ := h
  obtain ⟨i, k, hik⟩ := h.start_vertex
  obtain ⟨i', k', hik'⟩ := h.end_vertex
  exact ⟨(mem_tilingVertices D).mpr ⟨i, k, hik⟩, (mem_tilingVertices D).mpr ⟨i', k', hik'⟩⟩
theorem rational_of_relations {a b c : ℝ} (ha : 0 < a) (hcab : c ^ 2 = a ^ 2 + a * b)
    (hRc : ∃ J p q : ℕ, 0 < J ∧ (J : ℝ) * c = p * a + q * b)
    (hRa : ∃ J p q : ℕ, 0 < J ∧ (J : ℝ) * a = p * b + q * c) :
    ∃ r s : ℚ, b = r * a ∧ c = s * a := by
  obtain ⟨j', p', q', hj', hc'⟩ := hRc
  obtain ⟨j, p, q, hj, ha'⟩ := hRa
  have hj'R : (0 : ℝ) < j' := by exact_mod_cast hj'
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have key : ((j : ℝ) * j' - q * p') * a = ((j' : ℝ) * p + q * q') * b := by
    have e1 : (j' : ℝ) * (j * a) = j' * p * b + q * (j' * c) := by rw [ha']; ring
    rw [hc'] at e1
    linear_combination e1
  by_cases hden : (j' : ℕ) * p + q * q' = 0
  · 
    have hp : p = 0 := by
      rcases Nat.eq_zero_of_add_eq_zero hden with ⟨h1, -⟩
      rcases Nat.mul_eq_zero.mp h1 with h | h
      · omega
      · exact h
    have hdenR : ((j' : ℝ) * p + q * q') = 0 := by exact_mod_cast hden
    rw [hdenR, zero_mul] at key
    have hq : q ≠ 0 := by
      rintro rfl
      rw [hp] at ha'
      simp at ha'
      rcases ha' with h | h
      · omega
      · exact ha.ne' h
    have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    rw [hp, Nat.cast_zero, zero_mul, zero_add] at ha'
    have hcs : c = ((j : ℚ) / q : ℚ) * a := by
      push_cast; field_simp; linarith
    refine ⟨((j : ℚ) / q) ^ 2 - 1, (j : ℚ) / q, ?_, hcs⟩
    have : a * b = a * ((((j : ℚ) / q) ^ 2 - 1 : ℚ) * a) := by
      rw [show a * b = c ^ 2 - a ^ 2 by linarith, hcs]; push_cast; ring
    exact mul_left_cancel₀ ha.ne' this
  · have hdenR : ((j' : ℝ) * p + q * q') ≠ 0 := by exact_mod_cast hden
    have hb : b = ((((j : ℚ) * j' - q * p') / (j' * p + q * q') : ℚ)) * a := by
      push_cast
      field_simp
      linarith
    refine ⟨((j : ℚ) * j' - q * p') / (j' * p + q * q'),
      (p' + q' * (((j : ℚ) * j' - q * p') / (j' * p + q * q'))) / j', hb, ?_⟩
    have hc2 : c = (p' * a + q' * b) / j' := by field_simp; linarith
    rw [hc2, hb]
    push_cast
    field_simp
variable (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
  (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
include hγ hirr
include hA hC in
open Classical in
theorem gamma_c_start (hnorel : ¬ HasRelation D.toDissection (edgeType D (tileγ D))) :
    ∃ Q₀ ∈ frontier D.target.carrier, ∃ R, IsLink D.toDissection (edgeType D (tileγ D)) Q₀ R := by
  obtain ⟨-, -, hinj⟩ := angle_values D hγ hirr
  have hβγ : tileβ D ≠ tileγ D := by
    have ne : ∀ x y : Fin 5, x ≠ y →
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
          ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
    exact ne 1 2 (by decide)
  obtain ⟨part₀, hcov₀, hdisj₀, -⟩ := D.toDissection.side_walk 0
  obtain ⟨part₁, hcov₁, hdisj₁, -⟩ := D.toDissection.side_walk 1
  have h01 : (0 : Fin 3) + 1 = 1 := rfl
  have h12 : (1 : Fin 3) + 1 = 2 := rfl
  rw [h01] at hcov₀
  rw [h12] at hcov₁
  obtain ⟨-, -, -, -, -, cγB, -, -⟩ := counts_at_corners D hγ hirr hA hC
  have hα : ∀ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts 1 →
      (D.tile i).localAngle (D.target.pts 1) ≠ tileβ D →
        (D.tile i).localAngle (D.target.pts 1) = tileα D := by
    intro i j hj hβ
    rcases localAngle_at_own_vertex_mem' D i j with h | h | h <;> rw [hj] at h
    · exact h
    · exact absurd h hβ
    · exact absurd h (ne_of_angleCount_zero D cγB i)
  have hvert : ∀ e : Fin N × Fin 3, ((D.tile e.1).pts e.2 = D.target.pts 1 ∨
      (D.tile e.1).pts (e.2 + 1) = D.target.pts 1) →
        ∃ j : Fin 3, (D.tile e.1).pts j = D.target.pts 1 := by
    intro e h
    rcases h with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  rcases beta_at_apex D hγ hirr hA hC part₀ part₁ hcov₀ hcov₁ with hB | hB
  · obtain ⟨⟨eb, heb, hθb⟩, ⟨ec, hec, hθc⟩⟩ := qandrnotzero D hγ hirr hA hC part₀ hcov₀ hdisj₀
      (fun e he hend => by
        obtain ⟨j, hj⟩ := hvert e hend
        exact hα e.1 j hj (hB e he hend))
    exact boundary_start D hγ hirr part₀ hcov₀ hec heb hθc
      (fun h => hβγ (hθb.symm.trans h)) hnorel
  · 
    have hcov' : (⋃ e ∈ part₁, ((swapAC D).tile e.1).edge e.2) =
        segment ℝ ((swapAC D).target.pts 0) ((swapAC D).target.pts 1) :=
      hcov₁.trans (segment_symm ℝ _ _)
    obtain ⟨⟨eb, heb, hθb⟩, ⟨ec, hec, hθc⟩⟩ := qandrnotzero (swapAC D) hγ hirr hC hA part₁ hcov'
      hdisj₁ (fun e he hend => by
        obtain ⟨j, hj⟩ := hvert e hend
        exact hα e.1 j hj (hB e he hend))
    obtain ⟨Q₀, hQ₀, R, hR⟩ := boundary_start (swapAC D) hγ hirr part₁ hcov' hec heb hθc
      (fun h => hβγ (hθb.symm.trans h)) hnorel
    exact ⟨Q₀, by rwa [swapAC_carrier] at hQ₀, R, isLink_of_swapAC D hR⟩
include hA hC in
open Classical in
theorem crelation4_edges : HasRelation D.toDissection (edgeType D (tileγ D)) := by
  by_contra hnorel
  exact hnorel (relation_of_start D.toDissection _
    (fun _ _ _ _ hl => c_count_even D hγ hirr (localAngle_interior' D hl.end_interior))
    (gamma_c_start D hγ hirr hA hC hnorel))
include hA hC in
open Classical in
theorem arelation_edges : HasRelation D.toDissection (edgeType D (tileα D)) := by
  by_contra hnorel
  set θ := edgeType D (tileα D)
  set V := tilingVertices D
  let star : Plane → Prop := fun v => v ∉ Set.range D.target.pts ∧ vertexType D v = (3, 1, 0)
  let center : Plane → Prop := fun v => v ∉ Set.range D.target.pts ∧ vertexType D v = (0, 2, 3)
  have key : ∀ v ∈ V, (V.filter fun u => IsLink D.toDissection θ u v).card
      + (if center v then 1 else 0) ≤
      (V.filter fun w => IsLink D.toDissection θ v w).card + (if star v then 1 else 0) := by
    intro v hv
    have hle1 := in_le_one D.toDissection θ V v
    by_cases hc : center v
    · have hns : ¬ star v := fun hs => by
        have := hs.2.symm.trans hc.2
        simp at this
      rw [if_pos hc, if_neg hns]
      have hin0 : (V.filter fun u => IsLink D.toDissection θ u v).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro u - ⟨g, c, hl⟩
        obtain ⟨-, hπ, -⟩ := center_facts D hγ hirr hv hc.1 hc.2
        obtain ⟨ε, -, hRε⟩ := hl.across
        have := angleCount_pos D (Tri.localAngle_openSegment _ ε.2 hRε)
        omega
      obtain ⟨R, hR⟩ := center_out D hγ hirr hv hc.1 hc.2 hnorel
      have : 1 ≤ (V.filter fun w => IsLink D.toDissection θ v w).card :=
        Finset.card_pos.mpr ⟨R, Finset.mem_filter.mpr ⟨(link_mem_vertices D hR).2, hR⟩⟩
      omega
    · rw [if_neg hc]
      by_cases hs : star v
      · rw [if_pos hs]; omega
      · rw [if_neg hs]
        rcases Nat.eq_zero_or_pos (V.filter fun u => IsLink D.toDissection θ u v).card
          with h0 | hpos
        · omega
        · obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
          obtain ⟨-, g, c, hl⟩ := Finset.mem_filter.mp hu
          rcases link_end_a D hγ hirr hl with ht | heven
          · exfalso
            refine hs ⟨?_, ht⟩
            rintro ⟨m, hm⟩
            exact corner_not_interior D m (hm ▸ hl.end_interior)
          · obtain ⟨R', hR'⟩ := out_of_in D.toDissection θ hl heven hnorel
            have : 1 ≤ (V.filter fun w => IsLink D.toDissection θ v w).card :=
              Finset.card_pos.mpr ⟨R', Finset.mem_filter.mpr
                ⟨(link_mem_vertices D hR').2, hR'⟩⟩
            omega
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.card_filter,
    ← Finset.card_filter, sum_out_eq_sum_in] at hsum
  have hsc := starsandcenters D hγ hirr hA hC
  change _ + typeCount D (0, 2, 3) ≤ _ + typeCount D (3, 1, 0) at hsum
  omega
include hA hC in
theorem crelation4 : ∃ J p q : ℕ, 0 < J ∧
    (J : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
      = p * dist (D.model.pts 1) (D.model.pts 2) + q * dist (D.model.pts 2) (D.model.pts 0) :=
  c_relation_of_edges D (anglesSep_of_two_alpha D hγ hirr) (crelation4_edges D hγ hirr hA hC)
include hA hC in
theorem arelation : ∃ J p q : ℕ, 0 < J ∧
    (J : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      = p * dist (D.model.pts 2) (D.model.pts 0) + q * dist (D.model.pts 0) (D.model.pts 1) :=
  a_relation_of_edges D (anglesSep_of_two_alpha D hγ hirr) (arelation_edges D hγ hirr hA hC)
include hA hC in
theorem rationaltile : ∃ r s : ℚ,
    dist (D.model.pts 2) (D.model.pts 0) = r * dist (D.model.pts 1) (D.model.pts 2) ∧
    dist (D.model.pts 0) (D.model.pts 1) = s * dist (D.model.pts 1) (D.model.pts 2) := by
  obtain ⟨ha, -, -⟩ := model_sides_pos D
  have hcab := (twoalphatiles (tri_indep D.model) rfl rfl rfl).mp hγ
  exact rational_of_relations ha hcab (crelation4 D hγ hirr hA hC) (arelation D hγ hirr hA hC)
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set EuclideanGeometry
open scoped Pointwise
noncomputable def Tri.scale (T : Tri) (κ : ℝ) (hκ : κ ≠ 0) : Tri where
  pts k := κ • T.pts k
  indep := by
    have h := T.indep.map' (LinearEquiv.smulOfNeZero ℝ Plane κ hκ).toLinearMap.toAffineMap
      (LinearEquiv.smulOfNeZero ℝ Plane κ hκ).injective
    exact h
theorem Tri.scale_carrier (T : Tri) (κ : ℝ) (hκ : κ ≠ 0) :
    (Tri.scale T κ hκ).carrier = κ • T.carrier := by
  show convexHull ℝ (Set.range fun k => κ • T.pts k) = κ • convexHull ℝ (Set.range T.pts)
  rw [← convexHull_smul, ← Set.range_smul]
theorem dist_smul_smul (κ : ℝ) (x y : Plane) : dist (κ • x) (κ • y) = |κ| * dist x y := by
  rw [dist_smul₀, Real.norm_eq_abs]
theorem angle_smul_smul' {κ : ℝ} (hκ : κ ≠ 0) (x y z : Plane) :
    ∠ (κ • x) (κ • y) (κ • z) = ∠ x y z := by
  simp only [EuclideanGeometry.angle, vsub_eq_sub, ← smul_sub]
  exact InnerProductGeometry.angle_smul_smul hκ _ _
noncomputable def CongruentDissection.scale {N : ℕ} (D : CongruentDissection N) (κ : ℝ)
    (hκ : κ ≠ 0) : CongruentDissection N where
  target := Tri.scale D.target κ hκ
  tile i := Tri.scale (D.tile i) κ hκ
  covers := by
    simp only [Tri.scale_carrier]
    rw [← Set.smul_set_iUnion, D.covers]
  interiors_disjoint := by
    intro i j hij
    simp only [Tri.scale_carrier, interior_smul₀ hκ]
    rw [← Set.image_smul, ← Set.image_smul]
    exact (Set.disjoint_image_iff (smul_right_injective Plane hκ)).mpr (D.interiors_disjoint hij)
  model := Tri.scale D.model κ hκ
  tiles_congruent := by
    intro i
    obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).dist_eq
    refine Erdos634.SssCongruent.congruent_of_dist_perm σ fun a b => ?_
    show dist (κ • (D.tile i).pts a) (κ • (D.tile i).pts b) =
      dist (κ • D.model.pts (σ a)) (κ • D.model.pts (σ b))
    rw [dist_smul_smul, dist_smul_smul, hσ]
namespace CongruentDissection
variable {N : ℕ} (D : CongruentDissection N) {κ : ℝ} (hκ : κ ≠ 0)
theorem scale_model_pts (k : Fin 3) :
    (CongruentDissection.scale D κ hκ).model.pts k = κ • D.model.pts k := rfl
end CongruentDissection
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
variable {N : ℕ} (D : CongruentDissection N) {κ : ℝ} (hκ : κ ≠ 0)
theorem tileα_scale : tileα (CongruentDissection.scale D κ hκ) = tileα D :=
  angle_smul_smul' hκ _ _ _
theorem tileγ_scale : tileγ (CongruentDissection.scale D κ hκ) = tileγ D :=
  angle_smul_smul' hκ _ _ _
theorem scale_hyps (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D) :
    let D' := CongruentDissection.scale D κ hκ
    tileγ D' = 2 * tileα D' ∧ (¬ ∃ r : ℚ, tileα D' = (r : ℝ) * Real.pi) ∧
      ∠ (D'.target.pts 1) (D'.target.pts 0) (D'.target.pts 2) = tileα D' ∧
      ∠ (D'.target.pts 1) (D'.target.pts 2) (D'.target.pts 0) = tileα D' := by
  intro D'
  refine ⟨by rw [tileγ_scale, tileα_scale]; exact hγ, by rw [tileα_scale]; exact hirr, ?_, ?_⟩
  · exact (angle_smul_smul' hκ _ _ _).trans (hA.trans (tileα_scale D hκ).symm)
  · exact (angle_smul_smul' hκ _ _ _).trans (hC.trans (tileα_scale D hκ).symm)
theorem int_scale_of_rational (r s : ℚ)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = r * dist (D.model.pts 1) (D.model.pts 2))
    (hc : dist (D.model.pts 0) (D.model.pts 1) = s * dist (D.model.pts 1) (D.model.pts 2)) : ∃ (κ : ℝ) (hκ : κ ≠ 0) (a b c : ℕ),
    dist ((CongruentDissection.scale D κ hκ).model.pts 1)
      ((CongruentDissection.scale D κ hκ).model.pts 2) = a ∧
    dist ((CongruentDissection.scale D κ hκ).model.pts 2)
      ((CongruentDissection.scale D κ hκ).model.pts 0) = b ∧
    dist ((CongruentDissection.scale D κ hκ).model.pts 0)
      ((CongruentDissection.scale D κ hκ).model.pts 1) = c ∧
    Nat.gcd (Nat.gcd a b) c = 1 := by
  obtain ⟨ha0, hb0, hc0⟩ := model_sides_pos D
  set a0 := dist (D.model.pts 1) (D.model.pts 2)
  set b0 := dist (D.model.pts 2) (D.model.pts 0)
  set c0 := dist (D.model.pts 0) (D.model.pts 1)
  have hr : (0 : ℝ) < r := by
    rw [hb] at hb0; exact pos_of_mul_pos_left hb0 ha0.le
  have hs : (0 : ℝ) < s := by
    rw [hc] at hc0; exact pos_of_mul_pos_left hc0 ha0.le
  have hrn : 0 < r.num := Rat.num_pos.mpr (by exact_mod_cast hr)
  have hsn : 0 < s.num := Rat.num_pos.mpr (by exact_mod_cast hs)
  set A := r.den * s.den
  set B := r.num.toNat * s.den
  set C := s.num.toNat * r.den
  have hA0 : 0 < A := Nat.mul_pos r.den_pos s.den_pos
  have hrA : (r : ℝ) * A = B := by
    have : (r.num.toNat : ℝ) = r.num := by exact_mod_cast Int.toNat_of_nonneg hrn.le
    simp only [A, B, Nat.cast_mul, this]
    rw [Rat.cast_def]
    field_simp
  have hsA : (s : ℝ) * A = C := by
    have : (s.num.toNat : ℝ) = s.num := by exact_mod_cast Int.toNat_of_nonneg hsn.le
    simp only [A, C, Nat.cast_mul, this]
    rw [Rat.cast_def]
    field_simp
  set g := Nat.gcd (Nat.gcd A B) C
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.gcd_pos_of_pos_left _ hA0)
  have hgA : g ∣ A := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgB : g ∣ B := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hgC : g ∣ C := Nat.gcd_dvd_right _ _
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  set κ : ℝ := A / (g * a0)
  have hκpos : 0 < κ := by
    have : (0 : ℝ) < A := by exact_mod_cast hA0
    positivity
  refine ⟨κ, hκpos.ne', A / g, B / g, C / g, ?_, ?_, ?_, ?_⟩
  · rw [CongruentDissection.scale_model_pts, CongruentDissection.scale_model_pts, dist_smul_smul,
      abs_of_pos hκpos, Nat.cast_div hgA hgR.ne']
    change κ * a0 = _
    simp only [κ]
    field_simp
  · rw [CongruentDissection.scale_model_pts, CongruentDissection.scale_model_pts, dist_smul_smul,
      abs_of_pos hκpos, Nat.cast_div hgB hgR.ne', ← hrA]
    change κ * b0 = _
    rw [hb]
    simp only [κ]
    field_simp
  · rw [CongruentDissection.scale_model_pts, CongruentDissection.scale_model_pts, dist_smul_smul,
      abs_of_pos hκpos, Nat.cast_div hgC hgR.ne', ← hsA]
    change κ * c0 = _
    rw [hc]
    simp only [κ]
    field_simp
  · rw [Nat.gcd_div hgA hgB, Nat.gcd_div (Nat.gcd_dvd_left _ _) hgC, Nat.div_self hg]
variable (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
  (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
include hγ hirr hA hC
theorem exists_int_scale : ∃ (κ : ℝ) (hκ : κ ≠ 0) (a b c : ℕ),
    dist ((CongruentDissection.scale D κ hκ).model.pts 1)
      ((CongruentDissection.scale D κ hκ).model.pts 2) = a ∧
    dist ((CongruentDissection.scale D κ hκ).model.pts 2)
      ((CongruentDissection.scale D κ hκ).model.pts 0) = b ∧
    dist ((CongruentDissection.scale D κ hκ).model.pts 0)
      ((CongruentDissection.scale D κ hκ).model.pts 1) = c ∧
    Nat.gcd (Nat.gcd a b) c = 1 := by
  obtain ⟨r, s, hb, hc⟩ := rationaltile D hγ hirr hA hC
  exact int_scale_of_rational D r s hb hc
theorem notsquarefree : ¬ Squarefree N := by
  obtain ⟨κ, hκ, a, b, c, ha, hb, hc, hcop⟩ := exists_int_scale D hγ hirr hA hC
  obtain ⟨hγ', hirr', hA', hC'⟩ := scale_hyps D hκ hγ hirr hA hC
  exact notsquarefree_int _ ha hb hc hcop hγ' hirr' hA' hC'
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry Set
variable {N : ℕ} (D : CongruentDissection N)
noncomputable def relabelTarget (σ : Equiv.Perm (Fin 3)) : CongruentDissection N where
  target := ⟨D.target.pts ∘ σ, D.target.indep.comp_embedding σ.toEmbedding⟩
  tile := D.tile
  covers := by
    rw [D.covers]
    show convexHull ℝ (Set.range D.target.pts) = convexHull ℝ (Set.range (D.target.pts ∘ σ))
    rw [Set.range_comp, σ.range_eq_univ, Set.image_univ]
  interiors_disjoint := D.interiors_disjoint
  model := D.model
  tiles_congruent := D.tiles_congruent
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
variable {N : ℕ}
noncomputable def relabelModel (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) :
    CongruentDissection N where
  toDissection := D.toDissection
  model := D.model.relabel τ
  tiles_congruent := fun i => (D.tiles_congruent i).trans (D.model.congruent_relabel τ)
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
variable {N : ℕ} (D : CongruentDissection N)
theorem model_angleAt_0 : D.model.angleAt 0 = tileα D := rfl
theorem model_angleAt_2 : D.model.angleAt 2 = tileγ D := rfl
theorem target_angleAt_0 :
    D.target.angleAt 0 = ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) := rfl
theorem target_angleAt_2 :
    D.target.angleAt 2 = ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) :=
  angle_comm _ _ _
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
variable {N : ℕ} (D : CongruentDissection N)
theorem relabel_angleAt (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabelModel D τ).model.angleAt k = D.model.angleAt (τ k) :=
  (Row2.angleAt_comp D.model (relabelModel D τ).model τ (fun _ => rfl) k).1
end TriangleTiling
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
variable {α β a b c : ℝ}
theorem others (x y z : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by
  revert x y z; decide
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
section Normalize
theorem relabel_angleAt (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabelTarget D σ).target.angleAt k = D.target.angleAt (σ k) := by
  have d1 : σ k ≠ σ (k + 1) := σ.injective.ne (fin3_ne_add_one k)
  have d2 : σ k ≠ σ (k + 2) := σ.injective.ne ((by decide : ∀ x : Fin 3, x ≠ x + 2) k)
  have d12 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne ((by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k)
  show cornerAngle (D.target.pts (σ (k + 1))) (D.target.pts (σ k)) (D.target.pts (σ (k + 2))) = _
  unfold Tri.angleAt cornerAngle
  rcases others _ _ _ d1 d2 d12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
  exact EuclideanGeometry.angle_comm _ _ _
end Normalize
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.Prime
open Erdos634.Geometry EuclideanGeometry
variable {N : ℕ}
theorem exists_perm_02 : ∀ i j : Fin 3, i ≠ j → ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 2 = j := by
  decide
end TriangleTiling.Prime
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


open EuclideanGeometry in
/-- The tile (θ, pi - 3θ, 2θ) with θ not in Q pi on an isosceles T with base angles θ
(theorem:notsquarefree: the number of tiles is not squarefree). -/
theorem OMA.solution : OMA.R_erdos_634_R1_H2_R1_H4_R1.H3 := by
  intro p hp hp3 T Ts hc hd hu t A B hA hB i j hij he hθi hρ
  obtain ⟨ρ, hρ⟩ := hρ
  let D := OMA.E634S.mk T Ts hc hd hu t
  have hAD : ∀ m, D.target.angleAt m = A m := fun m =>
    (OMA.E634S.target_angleAt T Ts hc hd hu t m).trans (hA m).symm
  have hBD : ∀ m, D.model.angleAt m = B m := fun m =>
    (OMA.E634S.model_angleAt T Ts hc hd hu t m).trans (hB m).symm
  obtain ⟨σ, hσ0, hσ2⟩ := TriangleTiling.Prime.exists_perm_02 i j hij
  let D₁ := TriangleTiling.relabelTarget D σ
  have ht : ∀ m, D₁.target.angleAt m = A (σ m) := fun m => by
    rw [TriangleTiling.ThreeAlpha.relabel_angleAt]; exact hAD (σ m)
  have hm : ∀ m, D₁.model.angleAt m = B m := hBD
  have hA1 : ∠ (D₁.target.pts 1) (D₁.target.pts 0) (D₁.target.pts 2) = A i := by
    rw [← TriangleTiling.target_angleAt_0 (D := D₁), ht, hσ0]
  have hC1 : ∠ (D₁.target.pts 1) (D₁.target.pts 2) (D₁.target.pts 0) = A i := by
    rw [← TriangleTiling.target_angleAt_2 (D := D₁), ht, hσ2, he]
  obtain ⟨r0, -, r2⟩ := OMA.E634H.vec_comp hρ
  let D' := TriangleTiling.relabelModel D₁ ρ
  have hm' : ∀ m, D'.model.angleAt m = B (ρ m) := fun m => by
    rw [TriangleTiling.relabel_angleAt]; exact hm (ρ m)
  have e0 : TriangleTiling.tileα D' = A i := by
    rw [← TriangleTiling.model_angleAt_0 (D := D'), hm', r0]
  have e2 : TriangleTiling.tileγ D' = 2 * A i := by
    rw [← TriangleTiling.model_angleAt_2 (D := D'), hm', r2]
  refine TriangleTiling.notsquarefree D' (by rw [e2, e0]) (by rw [e0]; exact hθi) (by rw [e0]; exact hA1)
    (by rw [e0]; exact hC1) ?_
  exact Irreducible.squarefree hp

