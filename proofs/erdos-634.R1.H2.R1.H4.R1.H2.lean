import OMAReductions.R_erdos_634_R1_H2_R1_H4_R1

/-!
# Erdos 634, step R1.H2.R1.H4.R1.H2: classification of isosceles tilings with an irrational tile

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
theorem Tri.det_pos_or_neg (T : Tri) : 0 < T.det ∨ T.det < 0 :=
  (lt_or_gt_of_ne T.det_ne_zero).symm
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
namespace Erdos634.PinPlumbing
open Erdos634.Geometry
theorem pin_angle_sum {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts) :
    ∑ i, (D.tile i).localAngle p = Real.pi := by
  rw [D.sum_localAngle_eq p, D.target.localAngle_frontier hp hv]
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
theorem pin_angle_sum_interior {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ interior D.target.carrier) :
    ∑ i, (D.tile i).localAngle p = 2 * Real.pi := by
  rw [D.sum_localAngle_eq p, D.target.localAngle_interior hp]
end Erdos634.PinPlumbing
end

section
namespace Erdos634.BaseSelection
open Erdos634.Geometry
theorem tile_subset_target {N : ℕ} (D : Dissection N) (i : Fin N) :
    (D.tile i).carrier ⊆ D.target.carrier := by
  rw [← D.covers]
  exact Set.subset_iUnion (fun j => (D.tile j).carrier) i
theorem tile_interior_subset {N : ℕ} (D : Dissection N) (i : Fin N) :
    interior (D.tile i).carrier ⊆ interior D.target.carrier :=
  interior_mono (tile_subset_target D i)
end Erdos634.BaseSelection
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
namespace Erdos634.VertexFigureReal
open Erdos634.Geometry Finset
theorem sum_by_value {N : ℕ} (S : Finset ℝ) (f : Fin N → ℝ) (h : ∀ i, f i ∈ S) :
    ∑ i, f i = ∑ v ∈ S, (({i | f i = v} : Finset (Fin N)).card : ℝ) * v := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun i _ => h i) f]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const,
    nsmul_eq_mul]
theorem corner_angle_sum {N : ℕ} (D : Dissection N) (k : Fin 3) :
    ∑ i, (D.tile i).localAngle (D.target.pts k)
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) := by
  rw [D.sum_localAngle_eq (D.target.pts k), D.target.localAngle_vertex k]
end Erdos634.VertexFigureReal
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
namespace Erdos634.Geometry.Dissection
variable {N : ℕ}
theorem target_vertex_not_interior (T : Erdos634.Geometry.Tri) (k : Fin 3) :
    T.pts k ∉ interior T.carrier := by
  rw [T.mem_interior_iff_coord_pos]
  push_neg
  refine ⟨k + 1, ?_⟩
  have hne : (k + 1 : Fin 3) ≠ k := by
    have h : ∀ x : Fin 3, x + 1 ≠ x := by decide
    exact h k
  have hz : T.basis.coord (k + 1) (T.pts k) = 0 := by
    have h := T.basis.coord_apply (k + 1) k
    simp only [if_neg hne] at h
    exact h
  rw [hz]
theorem target_vertex_not_interior_tile (D : Dissection N) (k : Fin 3) (i : Fin N) :
    D.target.pts k ∉ interior (D.tile i).carrier := by
  intro h
  exact target_vertex_not_interior D.target k (Erdos634.BaseSelection.tile_interior_subset D i h)
theorem localAngle_ne_two_pi_of_not_mem_interior {T : Erdos634.Geometry.Tri} {p : Plane}
    (hp : p ∉ interior T.carrier) : T.localAngle p ≠ 2 * Real.pi := by
  classical
  intro h2
  rw [Erdos634.Geometry.Tri.localAngle] at h2
  split at h2
  · rename_i hv
    have hle := EuclideanGeometry.angle_le_pi ((T.pts (hv.choose + 1)))
      (T.pts hv.choose) (T.pts (hv.choose + 2))
    have hpi := Real.pi_pos
    rw [Erdos634.Geometry.cornerAngle] at h2
    rw [h2] at hle; linarith
  · split at h2
    · rename_i hall
      exact hp (T.mem_interior_iff_coord_pos p |>.mpr hall)
    · split at h2 <;> [skip; skip] <;>
        first
          | (exfalso; have := Real.pi_pos; linarith)
          | (exfalso; have := Real.pi_pos; linarith)
end Erdos634.Geometry.Dissection
end

section
namespace Erdos634.PlacementCompleteness
open Erdos634.Geometry Erdos634.Geometry.Dissection Set MeasureTheory
def unfilled {N : ℕ} (D : Dissection N) (S : Finset (Fin N)) : Set Plane :=
  D.target.carrier \ ⋃ i ∈ S, (D.tile i).carrier
end Erdos634.PlacementCompleteness
namespace Erdos634.PlacementCompleteness
open Erdos634.Geometry Erdos634.Geometry.Dissection Set MeasureTheory
end Erdos634.PlacementCompleteness
end

section
namespace Erdos634.RouteOne
open Erdos634.Geometry
theorem Tri.carrier_eq_closure_interior (T : Tri) :
    T.carrier = closure (interior T.carrier) := by
  have hconv : Convex ℝ T.carrier := by
    rw [Erdos634.Geometry.Tri.carrier]; exact convex_convexHull ℝ _
  have hne : (interior T.carrier).Nonempty := Erdos634.Geometry.Tri.interior_nonempty T
  have hclosed : IsClosed T.carrier := (Erdos634.Geometry.Tri.isCompact T).isClosed
  rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne, hclosed.closure_eq]
theorem Dissection.not_mem_interior_of_mem {N : ℕ} (D : Dissection N) {i j : Fin N}
    (hij : i ≠ j) {x : Plane} (hx : x ∈ (D.tile i).carrier) :
    x ∉ interior (D.tile j).carrier := by
  intro hxj
  have hx' : x ∈ closure (interior (D.tile i).carrier) := by
    rw [← Tri.carrier_eq_closure_interior]; exact hx
  obtain ⟨y, hyi, hyj⟩ :=
    mem_closure_iff.mp hx' (interior (D.tile j).carrier) isOpen_interior hxj
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hyj hyi
end Erdos634.RouteOne
end

section
open Erdos634.Geometry
namespace Erdos634.Geometry
theorem Tri.Congruent.cornerAngle_perm {T U : Tri} (h : T.Congruent U) :
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
theorem Tri.Congruent.corner_count_eq_one {T U : Tri} (h : T.Congruent U)
    (hdist : ∀ k l : Fin 3,
      cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
        = cornerAngle (T.pts (l + 1)) (T.pts l) (T.pts (l + 2)) → k = l)
    (k : Fin 3) :
    ({j | cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))} : Finset (Fin 3)).card = 1 := by
  classical
  obtain ⟨σ, hperm⟩ := h.cornerAngle_perm
  refine Finset.card_eq_one.mpr ⟨σ k, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hj
    have hm := hperm (σ.symm j)
    rw [Equiv.apply_symm_apply] at hm
    have : cornerAngle (T.pts (σ.symm j + 1)) (T.pts (σ.symm j)) (T.pts (σ.symm j + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by rw [← hm]; exact hj
    have hk := hdist _ _ this
    rw [← hk, Equiv.apply_symm_apply]
  · intro hj; subst hj; exact hperm k
theorem congruentDissection_corner_total {N : ℕ} (D : CongruentDissection N)
    (hdist : ∀ k l : Fin 3,
      cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))
        = cornerAngle (D.model.pts (l + 1)) (D.model.pts l) (D.model.pts (l + 2)) → k = l)
    (k : Fin 3) :
    ∑ i : Fin N, ({j | cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j)
          ((D.tile i).pts (j + 2))
        = cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))}
        : Finset (Fin 3)).card = N := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => ((D.tiles_congruent i).symm).corner_count_eq_one hdist k)]
  simp
open Classical in
noncomputable def cornerPts {N : ℕ} (D : Dissection N) : Finset Plane :=
  Finset.univ.biUnion (fun i : Fin N => Finset.univ.image (fun j : Fin 3 => (D.tile i).pts j))
theorem mem_cornerPts {N : ℕ} (D : Dissection N) (i : Fin N) (j : Fin 3) :
    (D.tile i).pts j ∈ cornerPts D := by
  classical
  refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
theorem tile_corner_card {N : ℕ} (D : Dissection N) (i : Fin N) (θ : ℝ)
    (h0 : θ ≠ 0) (hpi : θ ≠ Real.pi) (h2pi : θ ≠ 2 * Real.pi) :
    ({j | cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = θ}
        : Finset (Fin 3)).card
      = ({v ∈ cornerPts D | (D.tile i).localAngle v = θ} : Finset Plane).card := by
  classical
  have himg : ({v ∈ cornerPts D | (D.tile i).localAngle v = θ} : Finset Plane)
      = ({j | cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = θ}
          : Finset (Fin 3)).image (D.tile i).pts := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hang⟩
      rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with
        ⟨j, hj, hval⟩ | h | h | h
      · exact ⟨j, by rw [← hval]; exact hang, hj.symm⟩
      · exact absurd (h ▸ hang) (Ne.symm h2pi)
      · exact absurd (h ▸ hang) (Ne.symm hpi)
      · exact absurd (h ▸ hang) (Ne.symm h0)
    · rintro ⟨j, hj, rfl⟩
      exact ⟨mem_cornerPts D i j, by rw [Erdos634.Geometry.Tri.localAngle_vertex]; exact hj⟩
  rw [himg, Finset.card_image_of_injective _ (D.tile i).indep.injective]
theorem corner_double_count {N : ℕ} (D : Dissection N) (θ : ℝ)
    (h0 : θ ≠ 0) (hpi : θ ≠ Real.pi) (h2pi : θ ≠ 2 * Real.pi) :
    ∑ i : Fin N,
        ({j | cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = θ}
          : Finset (Fin 3)).card
      = ∑ v ∈ cornerPts D, ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)).card := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => tile_corner_card D i θ h0 hpi h2pi)]
  simp only [Finset.card_filter]
  exact Finset.sum_comm
theorem congruentDissection_corner_balance {N : ℕ} (D : CongruentDissection N)
    (hdist : ∀ k l : Fin 3,
      cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))
        = cornerAngle (D.model.pts (l + 1)) (D.model.pts l) (D.model.pts (l + 2)) → k = l)
    (k : Fin 3)
    (h0 : cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) ≠ 0)
    (hpi : cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) ≠ Real.pi)
    (h2pi : cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))
      ≠ 2 * Real.pi) :
    ∑ v ∈ cornerPts D.toDissection,
        ({i | (D.tile i).localAngle v
          = cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))}
          : Finset (Fin N)).card = N := by
  classical
  rw [← corner_double_count D.toDissection _ h0 hpi h2pi]
  exact congruentDissection_corner_total D hdist k
theorem congruentDissection_localAngle_mem_all {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (v : Plane) (i : Fin N) :
    (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ) := by
  classical
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with
    ⟨j, -, hval⟩ | h2pi | hpi | h0
  · obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
    rw [hval, hk]
    have hall : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2 := by decide
    have hk3 := hall k
    rcases hk3 with rfl | rfl | rfl
    · rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hα]; simp
    · rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, hβ]; simp
    · rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hγ]; simp
  · rw [h2pi]; simp
  · rw [hpi]; simp
  · rw [h0]; simp
theorem congruentDissection_localAngle_mem_at_corner {N : ℕ} (D : CongruentDissection N)
    (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {v : Plane} (j : Fin N) (m : Fin 3) (hvj : (D.tile j).pts m = v) (i : Fin N) :
    (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) := by
  classical
  have hmemj : v ∈ (D.tile j).carrier := by
    rw [← hvj, Erdos634.Geometry.Tri.carrier]; exact subset_convexHull ℝ _ ⟨m, rfl⟩
  have hnotint : v ∉ interior (D.tile i).carrier := by
    by_cases hij : i = j
    · subst hij; rw [← hvj]; exact _root_.Erdos634.Geometry.Dissection.target_vertex_not_interior _ m
    · exact fun hint =>
        Erdos634.RouteOne.Dissection.not_mem_interior_of_mem D.toDissection (Ne.symm hij) hmemj hint
  have h2pi := _root_.Erdos634.Geometry.Dissection.localAngle_ne_two_pi_of_not_mem_interior hnotint
  have hmem := congruentDissection_localAngle_mem_all D α β γ hmα hmβ hmγ v i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
  rcases hmem with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact absurd h h2pi
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
theorem vertex_of_localAngle_corner (T : Tri) {v : Plane} {θ : ℝ} (h : T.localAngle v = θ)
    (h0 : θ ≠ 0) (hpi : θ ≠ Real.pi) (h2pi : θ ≠ 2 * Real.pi) :
    ∃ m : Fin 3, T.pts m = v := by
  classical
  rcases Erdos634.PinPlumbing.localAngle_cases T v with ⟨m, hm, -⟩ | hb | hb | hb
  · exact ⟨m, hm.symm⟩
  · exact absurd (h.symm.trans hb) h2pi
  · exact absurd (h.symm.trans hb) hpi
  · exact absurd (h.symm.trans hb) h0
theorem localAngle_at_own_vertex_mem {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (j : Fin N) (m : Fin 3) :
    (D.tile j).localAngle ((D.tile j).pts m) = α ∨
    (D.tile j).localAngle ((D.tile j).pts m) = β ∨
    (D.tile j).localAngle ((D.tile j).pts m) = γ := by
  rw [Erdos634.Geometry.Tri.localAngle_vertex]
  obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent j).symm m
  rw [hk]
  have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases hall k with rfl | rfl | rfl
  · left
    rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl]
    exact hmα
  · right; left
    rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]
    exact hmβ
  · right; right
    rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
    exact hmγ
theorem cornerPts_trichotomy {N : ℕ} (D : Dissection N) {v : Plane} (hv : v ∈ cornerPts D) :
    v ∈ Set.range D.target.pts ∨
    (v ∈ frontier D.target.carrier ∧ v ∉ Set.range D.target.pts) ∨
    v ∈ interior D.target.carrier := by
  classical
  have hvt : v ∈ D.target.carrier := by
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hi
    refine tile_subset_target D i ?_
    rw [← hm, Erdos634.Geometry.Tri.carrier]; exact subset_convexHull ℝ _ ⟨m, rfl⟩
  by_cases hint : v ∈ interior D.target.carrier
  · exact Or.inr (Or.inr hint)
  · have hfr : v ∈ frontier D.target.carrier := by
      rw [(D.target.isCompact.isClosed).frontier_eq]
      exact ⟨hvt, hint⟩
    by_cases hcorner : v ∈ Set.range D.target.pts
    · exact Or.inl hcorner
    · exact Or.inr (Or.inl ⟨hfr, hcorner⟩)
end Erdos634.Geometry
end

section
namespace Erdos634.CertNode
open Erdos634.Geometry Erdos634.CertCoord Erdos634.PlacementCompleteness
noncomputable def sr (Dn : ℝ) : ℝ := Real.sqrt Dn
noncomputable def rp (Dn x y : ℝ) : Plane := mkPt x (y * sr Dn)
@[simp] theorem rp_zero (Dn x y : ℝ) : rp Dn x y 0 = x := by simp [rp]
@[simp] theorem rp_one (Dn x y : ℝ) : rp Dn x y 1 = y * sr Dn := by simp [rp]
theorem pts_injective (T : Tri) : Function.Injective T.pts := T.indep.injective
end Erdos634.CertNode
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
namespace Erdos634.Geometry.Row3.RP
open Real Erdos634.Geometry Erdos634.Geometry.Row3
theorem oppLen_pos (T : Tri) (k : Fin 3) : 0 < T.oppLen k := by
  unfold Tri.oppLen
  apply dist_pos.mpr
  intro h
  have := T.indep.injective h
  revert this; fin_cases k <;> decide
end Erdos634.Geometry.Row3.RP
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
noncomputable def rank2Map (θ : ℝ) : ℤ × ℤ →+ Real.Angle where
  toFun p := p.1 • ((Real.pi : ℝ) : Real.Angle) + p.2 • ((θ : ℝ) : Real.Angle)
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, add_zsmul]
    abel
theorem rank2Map_apply (θ : ℝ) (j k : ℤ) :
    rank2Map θ (j, k) = (((j : ℝ) * Real.pi + (k : ℝ) * θ : ℝ) : Real.Angle) := by
  show j • ((Real.pi : ℝ) : Real.Angle) + k • ((θ : ℝ) : Real.Angle) = _
  rw [Real.Angle.coe_add, ← Real.Angle.coe_zsmul, ← Real.Angle.coe_zsmul, zsmul_eq_mul,
    zsmul_eq_mul]
def rank2Par (b : ZMod 2) : ℤ × ℤ →+ ZMod 2 where
  toFun p := (p.1 : ZMod 2) + b * (p.2 : ZMod 2)
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring
theorem rank2_ker (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2) (p : ℤ × ℤ)
    (hp : rank2Map θ p = 0) : rank2Par b p = 0 := by
  obtain ⟨j, k⟩ := p
  rw [rank2Map_apply, Real.Angle.coe_eq_zero_iff] at hp
  obtain ⟨m, hm⟩ := hp
  rw [zsmul_eq_mul] at hm
  by_cases hk : k = 0
  · subst hk
    have h2 : ((j : ℝ) - 2 * m) * Real.pi = 0 := by
      push_cast at hm
      linear_combination (-1 : ℝ) * hm
    have h3 : (j : ℝ) - 2 * m = 0 := (mul_eq_zero.mp h2).resolve_right Real.pi_ne_zero
    have hj : j = 2 * m := by exact_mod_cast (sub_eq_zero.mp h3)
    show (j : ZMod 2) + b * ((0 : ℤ) : ZMod 2) = 0
    rw [hj]
    push_cast
    have h20 : (2 : ZMod 2) = 0 := by decide
    rw [h20]
    ring
  · exfalso
    apply hθ
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have h1 : (k : ℝ) * θ = (2 * m - j) * Real.pi := by
      linear_combination (-1 : ℝ) * hm
    refine ⟨((2 * m - j : ℤ) : ℚ) / (k : ℚ), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hk']
    linear_combination h1
noncomputable def GridChar.rank2 (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anchor : Real.Angle) : GridChar ℝ :=
  GridChar.ofHom (rank2Map θ) (rank2Par b) (rank2_ker θ hθ b) (1, 0)
    (by rw [rank2Map_apply]; push_cast; rw [one_mul, zero_mul, add_zero])
    (by show ((1 : ℤ) : ZMod 2) + b * ((0 : ℤ) : ZMod 2) = 1; push_cast; ring)
    anchor
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
theorem theta_irr_of_alpha {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    ¬ ∃ r : ℚ, α / 2 + Real.pi / 2 = (r : ℝ) * Real.pi := by
  rintro ⟨r, hr⟩
  apply hα
  refine ⟨2 * r - 1, ?_⟩
  push_cast
  linear_combination 2 * hr
noncomputable def chiPlus (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : GridChar ℝ :=
  GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) 0 0
def Tri.ThreeAlphaData (T : Tri) (α β a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = β ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = 2 * α + β ∧ T.oppLen (σ 2) = c
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
def Tri.TwoAlphaData (T : Tri) (α a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = Real.pi - 3 * α ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = 2 * α ∧ T.oppLen (σ 2) = c
end Erdos634.Geometry
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
namespace Erdos634.Geometry.CaseA.LemmaV
open Erdos634.Geometry
theorem angle_pos (T : Tri) (k : Fin 3) : 0 < T.angleAt k := Erdos634.MarchFlank.cornerAngle_pos T k
theorem angle_lt_pi (T : Tri) (k : Fin 3) : T.angleAt k < Real.pi :=
  Erdos634.RouteOneVertexKill.cornerAngle_lt_pi T k
end Erdos634.Geometry.CaseA.LemmaV
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
theorem Tri.range_pts_eq' (T : Tri) (j : Fin 3) :
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
theorem Tri.strict_triangle' (T : Tri) (j : Fin 3) :
    dist (T.pts (j + 1)) (T.pts (j + 2))
      < dist (T.pts (j + 1)) (T.pts j) + dist (T.pts j) (T.pts (j + 2)) := by
  rcases lt_or_eq_of_le (dist_triangle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) with h | h
  · exact h
  · exfalso
    have hw : Wbtw ℝ (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) :=
      dist_add_dist_eq_iff.mp h.symm
    have hcol : Collinear ℝ (Set.range T.pts) := by
      rw [T.range_pts_eq' j]; exact hw.collinear
    exact (affineIndependent_iff_not_collinear.mp T.indep) hcol
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
namespace Erdos634.Geometry.A1Field
open Erdos634.Geometry Complex
open Erdos634.Geometry.CaseA.LemmaV (angle_pos angle_lt_pi)
variable {N : ℕ}
theorem sin_angle_pos (T : Tri) (k : Fin 3) : 0 < Real.sin (T.angleAt k) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos T k) (angle_lt_pi T k)
end Erdos634.Geometry.A1Field
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
noncomputable def fAlpha (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : GridChar ℝ :=
  GridChar.rankn 3 (by norm_num) (by decide) α hα 0 0
noncomputable def fBeta (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : GridChar ℝ :=
  GridChar.rankn 3 (by norm_num) (by decide) α hα 1 0
def Tri.TwoPiThreeData (T : Tri) (α a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = Real.pi / 3 - α ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = 2 * Real.pi / 3 ∧ T.oppLen (σ 2) = c
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
def Tri.SixtyData (T : Tri) (α a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = 2 * Real.pi / 3 - α ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = Real.pi / 3 ∧ T.oppLen (σ 2) = c
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
def Tri.GridTriData (T : Tri) (α : ℝ) (j0 k0 j1 k1 j2 k2 : ℤ) (s0 s1 s2 : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = (j0 : ℝ) * (Real.pi / 3) + (k0 : ℝ) * α ∧ T.oppLen (σ 0) = s0 ∧
    T.angleAt (σ 1) = (j1 : ℝ) * (Real.pi / 3) + (k1 : ℝ) * α ∧ T.oppLen (σ 1) = s1 ∧
    T.angleAt (σ 2) = (j2 : ℝ) * (Real.pi / 3) + (k2 : ℝ) * α ∧ T.oppLen (σ 2) = s2
theorem Tri.gridTriData_angles_mem {T : Tri} {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {j0 k0 j1 k1 j2 k2 : ℤ} {s0 s1 s2 : ℝ} (h : T.GridTriData α j0 k0 j1 k1 j2 k2 s0 s1 s2)
    (b' : ZMod 2) :
    ∀ i, ((T.angleAt i : ℝ) : Real.Angle)
      ∈ (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).L := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  intro i
  obtain ⟨m, rfl⟩ := σ.surjective i
  have hm : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hm with rfl | rfl | rfl
  · rw [h0, show ((j0 : ℝ) * (Real.pi / 3) + (k0 : ℝ) * α : ℝ)
        = (((j0 : ℝ)) * (Real.pi / ((3 : ℕ) : ℝ)) + ((k0 : ℝ)) * α : ℝ) by push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
  · rw [h1, show ((j1 : ℝ) * (Real.pi / 3) + (k1 : ℝ) * α : ℝ)
        = (((j1 : ℝ)) * (Real.pi / ((3 : ℕ) : ℝ)) + ((k1 : ℝ)) * α : ℝ) by push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
  · rw [h2, show ((j2 : ℝ) * (Real.pi / 3) + (k2 : ℝ) * α : ℝ)
        = (((j2 : ℝ)) * (Real.pi / ((3 : ℕ) : ℝ)) + ((k2 : ℝ)) * α : ℝ) by push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
theorem Tri.gridTriData_tileValue (T : Tri) {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {j0 k0 j1 k1 j2 k2 : ℤ} {s0 s1 s2 : ℝ}
    (h : T.GridTriData α j0 k0 j1 k1 j2 k2 s0 s1 s2) (b' : ZMod 2) :
    (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).tileValue T
      = (if ((3 - j0 : ℤ) : ZMod 2) + b' * ((-k0 : ℤ) : ZMod 2) = 0 then 1 else -1) * s0
        + (if ((3 - j1 : ℤ) : ZMod 2) + b' * ((-k1 : ℤ) : ZMod 2) = 0 then 1 else -1) * s1
        + (if ((3 - j2 : ℤ) : ZMod 2) + b' * ((-k2 : ℤ) : ZMod 2) = 0 then 1 else -1) * s2 := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ (fun i => (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).chi
    ((Real.pi - T.angleAt i : ℝ) : Real.Angle) * T.oppLen i), Fin.sum_univ_three]
  rw [h0, o0, h1, o1, h2, o2,
    show Real.pi - ((j0 : ℝ) * (Real.pi / 3) + (k0 : ℝ) * α)
        = ((3 - j0 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-k0 : ℤ) : ℝ) * α by push_cast; ring,
    show Real.pi - ((j1 : ℝ) * (Real.pi / 3) + (k1 : ℝ) * α)
        = ((3 - j1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-k1 : ℤ) : ℝ) * α by push_cast; ring,
    show Real.pi - ((j2 : ℝ) * (Real.pi / 3) + (k2 : ℝ) * α)
        = ((3 - j2 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-k2 : ℤ) : ℝ) * α by push_cast; ring,
    GridChar.rankn_chi, GridChar.rankn_chi, GridChar.rankn_chi]
theorem Tri.gridTriData_flux_pm (T : Tri) {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    {j0 k0 j1 k1 j2 k2 : ℤ} {s0 s1 s2 : ℝ}
    (h : T.GridTriData α j0 k0 j1 k1 j2 k2 s0 s1 s2) (b' : ZMod 2) :
    T.flux (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).weight
        = (if ((3 - j0 : ℤ) : ZMod 2) + b' * ((-k0 : ℤ) : ZMod 2) = 0 then 1 else -1) * s0
          + (if ((3 - j1 : ℤ) : ZMod 2) + b' * ((-k1 : ℤ) : ZMod 2) = 0 then 1 else -1) * s1
          + (if ((3 - j2 : ℤ) : ZMod 2) + b' * ((-k2 : ℤ) : ZMod 2) = 0 then 1 else -1) * s2
      ∨ T.flux (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0).weight
        = -((if ((3 - j0 : ℤ) : ZMod 2) + b' * ((-k0 : ℤ) : ZMod 2) = 0 then 1 else -1) * s0
          + (if ((3 - j1 : ℤ) : ZMod 2) + b' * ((-k1 : ℤ) : ZMod 2) = 0 then 1 else -1) * s1
          + (if ((3 - j2 : ℤ) : ZMod 2) + b' * ((-k2 : ℤ) : ZMod 2) = 0 then 1 else -1) * s2) := by
  rcases T.flux_grid_pm (GridChar.rankn 3 (by norm_num) (by decide) α hα b' 0)
      (GridChar.rankn_sq _ _ _ _ _ _ _) (T.gridTriData_angles_mem hα h b') with h1 | h1
  · left; rw [h1, T.gridTriData_tileValue hα h b']
  · right; rw [h1, T.gridTriData_tileValue hα h b']
end Erdos634.Geometry
end

section
namespace Erdos634.NonIntegrality
theorem k_not_dvd (a k c : ℤ) (ha : 0 < a) (hk : 0 < k) (hc : 0 < c)
    (hcop : IsCoprime a k) (heq : c ^ 2 = a ^ 2 + a * k ^ 2 + (k ^ 2) ^ 2) :
    ¬ (k ∣ (a + k ^ 2 - c)) := by
  intro hdvd
  have hca : a < c := by nlinarith
  have hcab : c < a + k ^ 2 := by nlinarith
  have hdvd' : k ∣ (c - a) := by
    have : c - a = k ^ 2 - (a + k ^ 2 - c) := by ring
    rw [this]
    exact dvd_sub (Dvd.intro k (by ring)) hdvd
  obtain ⟨t, ht⟩ := hdvd'
  have ht0 : 0 < t := by nlinarith
  have htk : t < k := by nlinarith
  have hkey : a * (2 * t - k) = k * (k - t) * (k + t) := by
    have hc' : c = a + k * t := by linarith [ht]
    have hexp : k * (a * (2 * t - k) - (k - t) * (k + t) * k) = 0 := by
      rw [hc'] at heq; nlinarith [heq]
    have hk0 : k ≠ 0 := ne_of_gt hk
    have := mul_eq_zero.mp hexp
    rcases this with h | h
    · exact absurd h hk0
    · linarith [h]
  have hdvd2 : k ∣ a * (2 * t - k) := ⟨(k - t) * (k + t), by linarith [hkey]⟩
  have hdvd3 : k ∣ (2 * t - k) := (hcop.symm.dvd_of_dvd_mul_left hdvd2)
  have hdvd4 : k ∣ 2 * t := by
    have : 2 * t = (2 * t - k) + k := by ring
    rw [this]; exact dvd_add hdvd3 dvd_rfl
  obtain ⟨u, hu⟩ := hdvd4
  have hu1 : u = 1 := by nlinarith
  have h2t : 2 * t = k := by rw [hu, hu1]; ring
  rw [h2t] at hkey
  have hzero : (0:ℤ) = k * (k - t) * (k + t) := by linarith [hkey]
  have hpos : 0 < k * (k - t) * (k + t) := by
    apply mul_pos (mul_pos hk (by linarith)) (by linarith)
  linarith [hzero, hpos]
end Erdos634.NonIntegrality
end

section
open scoped Classical
namespace Erdos634.Geometry
theorem Row9.iso_closed_forms (a b c : ℝ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (c - a - b) * (c + a - b) = b * (a + 2 * b - 2 * c) ∧
      (c + a + b) * (c + b - a) = b * (a + 2 * b + 2 * c) := by
  constructor <;> nlinarith [hc]
theorem Row9.k_sq_eq_b (a b k : ℤ) (N : ℕ) (hN : N.Prime) (ha2b : 3 ≤ a + 2 * b)
    (hcop : IsCoprime b (a + 2 * b)) (harea : (b : ℤ) * (N : ℤ) = k ^ 2 * (a + 2 * b)) :
    k ^ 2 = b ∧ (N : ℤ) = a + 2 * b := by
  have hdvd : (a + 2 * b) ∣ b * N := ⟨k ^ 2, by rw [harea]; ring⟩
  have hdvd2 : (a + 2 * b) ∣ (N : ℤ) := hcop.symm.dvd_of_dvd_mul_left hdvd
  set e : ℕ := (a + 2 * b).toNat with he
  have he' : (e : ℤ) = a + 2 * b := Int.toNat_of_nonneg (by linarith)
  have hdvdN : e ∣ N := by
    have : (e : ℤ) ∣ (N : ℤ) := by rw [he']; exact hdvd2
    exact_mod_cast this
  have he3 : 3 ≤ e := by
    have : (3 : ℤ) ≤ (e : ℤ) := by rw [he']; exact ha2b
    exact_mod_cast this
  rcases (hN.eq_one_or_self_of_dvd e hdvdN) with h | h
  · omega
  · have hNe : (N : ℤ) = a + 2 * b := by rw [← he', h]
    refine ⟨?_, hNe⟩
    have hNpos : (N : ℤ) ≠ 0 := by
      have : 0 < N := hN.pos
      omega
    have hcancel : b * (N : ℤ) = k ^ 2 * (N : ℤ) := by rw [harea, hNe]
    exact (mul_right_cancel₀ hNpos hcancel).symm
theorem Row9.iso_arith_core (a b c k M : ℤ) (N : ℕ) (ha : 0 < a) (hb : 0 < b) (hc0 : 0 < c)
    (hk : 0 < k) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hac : IsCoprime a c) (hN : N.Prime)
    (ha2b : 3 ≤ a + 2 * b) (hcopN : IsCoprime b (a + 2 * b)) (habN : b * (N : ℤ) = k ^ 2 * (a + 2 * b))
    (hM : k * M = c - a - b) : False := by
  obtain ⟨hkb, -⟩ := Row9.k_sq_eq_b a b k N hN ha2b hcopN habN
  have hcop_ak : IsCoprime a k := by
    have hcop_ab : IsCoprime a b := by
      rw [Int.isCoprime_iff_gcd_eq_one] at hac ⊢
      set d : ℤ := (Int.gcd a b : ℤ) with hd
      have hda : d ∣ a := Int.gcd_dvd_left a b
      have hdb : d ∣ b := Int.gcd_dvd_right a b
      have hdc2 : d ∣ c ^ 2 := by
        have heq : c ^ 2 = a * a + a * b + b * b := by rw [hc]; ring
        rw [heq]
        exact dvd_add (dvd_add (hda.mul_right a) (hda.mul_right b)) (hdb.mul_right b)
      have hcop_dc : IsCoprime d c :=
        (Int.isCoprime_iff_gcd_eq_one.mpr hac).of_isCoprime_of_dvd_left hda
      have hunit : IsUnit d := (hcop_dc.pow_right (n := 2)).isUnit_of_dvd hdc2
      have hdpos : 0 ≤ d := by rw [hd]; positivity
      rcases Int.isUnit_iff.mp hunit with h | h
      · rw [hd] at h; exact_mod_cast h
      · rw [hd] at h; omega
    have hcop_a_k2 : IsCoprime a (k ^ 2) := by rw [hkb]; exact hcop_ab
    exact hcop_a_k2.of_isCoprime_of_dvd_right (dvd_pow_self k two_ne_zero)
  have hkM : k ∣ (c - a - b) := ⟨M, hM.symm⟩
  exact NonIntegrality.k_not_dvd a k c ha hk hc0 hcop_ak (by
    rw [hkb]; linarith [hc]) (by
    have : a + k ^ 2 - c = -(c - a - b) - (b - k ^ 2) := by ring
    rw [this, hkb, sub_self, sub_zero]
    exact hkM.neg_right)
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
def Tri.BaseAlphaData (T : Tri) (α a b c μ : ℝ) : Prop :=
  0 < μ ∧ T.GridTriData α 0 1 0 1 3 (-2) (μ * c) (μ * c) (μ * (a + 2 * b))
theorem Row9.lemmaCF_alpha (T : Tri) {α a b c μ : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.BaseAlphaData α a b c μ) :
    T.flux (fAlpha α hα).weight = μ * (a + 2 * b - 2 * c)
      ∨ T.flux (fAlpha α hα).weight = -(μ * (a + 2 * b - 2 * c)) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fAlpha
  rcases T.gridTriData_flux_pm hα hgrid 0 with h1 | h1
  · left
    rw [h1, if_neg (by decide), if_pos (by decide)]
    ring
  · right
    rw [h1, if_neg (by decide), if_pos (by decide)]
    ring
theorem Row9.lemmaCF_beta (T : Tri) {α a b c μ : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.BaseAlphaData α a b c μ) :
    T.flux (fBeta α hα).weight = μ * (a + 2 * b + 2 * c)
      ∨ T.flux (fBeta α hα).weight = -(μ * (a + 2 * b + 2 * c)) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fBeta
  rcases T.gridTriData_flux_pm hα hgrid 1 with h1 | h1
  · left
    rw [h1, if_pos (by decide), if_pos (by decide)]
    ring
  · right
    rw [h1, if_pos (by decide), if_pos (by decide)]
    ring
end Erdos634.Geometry
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
open scoped Classical
namespace Erdos634.Geometry
noncomputable def fAlphaAt (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (θ₀ : Real.Angle) :
    GridChar ℝ :=
  GridChar.rankn 3 (by norm_num) (by decide) α hα 0 θ₀
noncomputable def fBetaAt (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (θ₀ : Real.Angle) :
    GridChar ℝ :=
  GridChar.rankn 3 (by norm_num) (by decide) α hα 1 θ₀
theorem fAlphaAt_zero (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    fAlphaAt α hα 0 = fAlpha α hα := rfl
theorem fBetaAt_zero (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    fBetaAt α hα 0 = fBeta α hα := rfl
theorem Tri.data_angles_mem_at {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) (b' : ZMod 2) (θ₀ : Real.Angle) :
    ∀ j, ((T.angleAt j : ℝ) : Real.Angle)
      ∈ (GridChar.rankn 3 (by norm_num) (by decide) α hα b' θ₀).L := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  intro j
  obtain ⟨k, rfl⟩ := σ.surjective j
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · rw [h0, show ((α : ℝ) : Real.Angle)
        = ((((0 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((1 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
          congr 1; push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
  · rw [h1, show ((Real.pi / 3 - α : ℝ) : Real.Angle)
        = ((((1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-1 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
          congr 1; push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
  · rw [h2, show ((2 * Real.pi / 3 : ℝ) : Real.Angle)
        = ((((2 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((0 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
          congr 1; push_cast; ring]
    exact GridChar.rankn_mem _ _ _ _ _ _ _ _ _
theorem data_tileValue_at (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) (b' : ZMod 2) (θ₀ : Real.Angle) :
    (GridChar.rankn 3 (by norm_num) (by decide) α hα b' θ₀).tileValue T
      = (if ((3 : ℤ) : ZMod 2) + b' * ((-1 : ℤ) : ZMod 2) = 0 then 1 else -1) * a
        + (if ((2 : ℤ) : ZMod 2) + b' * ((1 : ℤ) : ZMod 2) = 0 then 1 else -1) * b
        + (if ((1 : ℤ) : ZMod 2) + b' * ((0 : ℤ) : ZMod 2) = 0 then 1 else -1) * c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ (fun j => (GridChar.rankn 3 (by norm_num) (by decide) α hα b' θ₀).chi
    ((Real.pi - T.angleAt j : ℝ) : Real.Angle) * T.oppLen j), Fin.sum_univ_three]
  rw [h0, o0, h1, o1, h2, o2,
    show Real.pi - α = ((3 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((-1 : ℤ) : ℝ) * α by
      push_cast; ring,
    show Real.pi - (Real.pi / 3 - α) = ((2 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((1 : ℤ) : ℝ) * α by
      push_cast; ring,
    show Real.pi - 2 * Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / ((3 : ℕ) : ℝ)) + ((0 : ℤ) : ℝ) * α by
      push_cast; ring,
    GridChar.rankn_chi, GridChar.rankn_chi, GridChar.rankn_chi]
theorem data_tileValue_alpha_at (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) (θ₀ : Real.Angle) :
    (fAlphaAt α hα θ₀).tileValue T = -(c + a - b) := by
  unfold fAlphaAt
  rw [data_tileValue_at T hα h 0 θ₀, if_neg (by decide), if_pos (by decide), if_neg (by decide)]
  ring
theorem data_tileValue_beta_at (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) (θ₀ : Real.Angle) :
    (fBetaAt α hα θ₀).tileValue T = -(c + b - a) := by
  unfold fBetaAt
  rw [data_tileValue_at T hα h 1 θ₀, if_pos (by decide), if_neg (by decide), if_neg (by decide)]
  ring
theorem Tri.oppLen_lt_sum (T : Tri) (j : Fin 3) :
    T.oppLen j < T.oppLen (j + 1) + T.oppLen (j + 2) := by
  have h0 := T.strict_triangle' 0
  have h1 := T.strict_triangle' 1
  have h2 := T.strict_triangle' 2
  have c01 := dist_comm (T.pts 0) (T.pts 1)
  have c02 := dist_comm (T.pts 0) (T.pts 2)
  have c12 := dist_comm (T.pts 1) (T.pts 2)
  unfold Tri.oppLen
  fin_cases j <;> simp at h0 h1 h2 ⊢ <;> linarith
theorem Tri.TwoPiThreeData.tri_ineq {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    a < b + c ∧ b < a + c ∧ c < a + b := by
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := h
  have H : ∀ j, T.oppLen j < T.oppLen (j + 1) + T.oppLen (j + 2) := T.oppLen_lt_sum
  have i01 : σ 0 ≠ σ 1 := fun e => absurd (σ.injective e) (by decide)
  have i02 : σ 0 ≠ σ 2 := fun e => absurd (σ.injective e) (by decide)
  have i12 : σ 1 ≠ σ 2 := fun e => absurd (σ.injective e) (by decide)
  subst o0 o1 o2
  generalize σ 0 = x at *
  generalize σ 1 = y at *
  generalize σ 2 = z at *
  have H0 := H 0; have H1 := H 1; have H2 := H 2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at H0 H1 H2
  refine ⟨?_, ?_, ?_⟩ <;>
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp at i01 i02 i12 ⊢ <;> linarith
theorem Tri.TwoPiThreeData.pos_caMb {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    0 < c + a - b := by linarith [h.tri_ineq.2.1]
theorem Tri.TwoPiThreeData.pos_cbMa {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    0 < c + b - a := by linarith [h.tri_ineq.1]
theorem Paper.cor_int_at {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (θ₀ : Real.Angle) :
    0 < c + a - b ∧ 0 < c + b - a ∧
    ∃ Mα Mβ : ℤ,
      (Mα : ℝ) = D.target.flux (fAlphaAt α hα θ₀).weight / (c + a - b) ∧
      (Mβ : ℝ) = D.target.flux (fBetaAt α hα θ₀).weight / (c + b - a) ∧
      (2 : ℤ) ∣ Mα - N ∧ (2 : ℤ) ∣ Mβ - N ∧ (2 : ℤ) ∣ Mα - Mβ := by
  have hA := h.pos_caMb
  have hB := h.pos_cbMa
  obtain ⟨S, hS2, -, hSf⟩ := D.target_flux_signs (fAlphaAt α hα θ₀)
    (GridChar.rankn_sq _ _ _ _ _ _ _) (D.model.data_angles_mem_at hα h 0 θ₀)
  obtain ⟨S', hS2', -, hSf'⟩ := D.target_flux_signs (fBetaAt α hα θ₀)
    (GridChar.rankn_sq _ _ _ _ _ _ _) (D.model.data_angles_mem_at hα h 1 θ₀)
  have p1 : (2 : ℤ) ∣ -S - N := by
    rw [show -S - (N : ℤ) = -(S - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hS2) (dvd_mul_right 2 _)
  have p2 : (2 : ℤ) ∣ -S' - N := by
    rw [show -S' - (N : ℤ) = -(S' - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hS2') (dvd_mul_right 2 _)
  refine ⟨hA, hB, -S, -S', ?_, ?_, p1, p2, ?_⟩
  · rw [hSf, data_tileValue_alpha_at D.model hα h θ₀, eq_div_iff hA.ne']; push_cast; ring
  · rw [hSf', data_tileValue_beta_at D.model hα h θ₀, eq_div_iff hB.ne']; push_cast; ring
  · rw [show -S - -S' = (-S - N) - (-S' - N) by ring]; exact dvd_sub p1 p2
end Erdos634.Geometry
namespace Erdos634.Draft.FluxPaperWitness
open Erdos634.Geometry
end Erdos634.Draft.FluxPaperWitness
end

section
namespace Erdos634.Draft.LemmaCShapes
def TA (θ : Fin 3 → ℝ) (x y z : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), θ (σ 0) = x ∧ θ (σ 1) = y ∧ θ (σ 2) = z
theorem ta_of_idx (θ : Fin 3 → ℝ) (x y z : ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hx : θ i = x) (hy : θ j = y) (hz : θ l = z) : TA θ x y z := by
  have key : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → Function.Bijective ![i, j, l] := by decide
  refine ⟨Equiv.ofBijective _ (key i j l hij hil hjl), ?_, ?_, ?_⟩
  · simpa using hx
  · simpa using hy
  · simpa using hz
theorem fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
set_option maxHeartbeats 4000000 in
theorem shapes_threeTwo (θ : Fin 3 → ℝ) (u v w : ℝ) (P Q R : Fin 3 → ℕ)
    (hu : u = 2 * w + v) (hrel : 3 * w + 2 * v = Real.pi)
    (hθ : ∀ k, θ k = (P k : ℝ) * u + (Q k : ℝ) * v + (R k : ℝ) * w)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 2) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) :
    TA θ v v (3 * w) ∨
    TA θ (w + v) (w + v) w ∨
    TA θ (2 * w) v (w + v) ∨
    TA θ (2 * w) w (2 * v) ∨
    TA θ w w (w + 2 * v) ∨
    TA θ w v u := by
  have h0 := hθ 0; have h1 := hθ 1; have h2 := hθ 2
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have hPk : P 0 = 0 ∧ P 1 = 0 ∧ P 2 = 0 := by omega
  obtain ⟨hP0, hP1, hP2⟩ := hPk
  rcases (by omega : Q 0 = 0 ∨ Q 0 = 1 ∨ Q 0 = 2) with e0 | e0 | e0
  · 
    rcases (by omega : R 0 = 1 ∨ R 0 = 2 ∨ R 0 = 3) with e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 2 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
    · 
      obtain e2 : Q 1 = 1 := by omega
      obtain e3 : R 1 = 0 := by omega
      obtain e4 : Q 2 = 1 := by omega
      obtain e5 : R 2 = 0 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1 ∨ R 0 = 2) with e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2 ∨ R 1 = 3) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 3 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1) with e1 | e1
    · 
      obtain e2 : Q 1 = 0 := by omega
      rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 2 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
    · 
      obtain e2 : Q 1 = 0 := by omega
      obtain e3 : R 1 = 1 := by omega
      obtain e4 : Q 2 = 0 := by omega
      obtain e5 : R 2 = 1 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
set_option maxHeartbeats 4000000 in
theorem shapes_twoAlpha (θ : Fin 3 → ℝ) (u v w : ℝ) (P Q R : Fin 3 → ℕ)
    (hu : u = 2 * w) (hv : v = Real.pi - 3 * w)
    (hθ : ∀ k, θ k = (P k : ℝ) * u + (Q k : ℝ) * v + (R k : ℝ) * w)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 1) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) :
    TA θ w w (v + w) ∨
    TA θ w v u := by
  have h0 := hθ 0; have h1 := hθ 1; have h2 := hθ 2
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have hPk : P 0 = 0 ∧ P 1 = 0 ∧ P 2 = 0 := by omega
  obtain ⟨hP0, hP1, hP2⟩ := hPk
  rcases (by omega : Q 0 = 0 ∨ Q 0 = 1) with e0 | e0
  · 
    rcases (by omega : R 0 = 1 ∨ R 0 = 2) with e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1) with e1 | e1
    · 
      obtain e2 : Q 1 = 0 := by omega
      rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 2 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
    · 
      obtain e2 : Q 1 = 0 := by omega
      obtain e3 : R 1 = 1 := by omega
      obtain e4 : Q 2 = 0 := by omega
      obtain e5 : R 2 = 1 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
set_option maxHeartbeats 4000000 in
theorem shapes_right (θ : Fin 3 → ℝ) (u v w : ℝ) (P Q R : Fin 3 → ℕ)
    (hu : u = Real.pi / 2) (hw : w = Real.pi / 2 - v)
    (hθ : ∀ k, θ k = (P k : ℝ) * u + (Q k : ℝ) * v + (R k : ℝ) * w)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 2) (hR : R 0 + R 1 + R 2 = 2)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) :
    TA θ v v (2 * w) ∨
    TA θ (2 * v) w w ∨
    TA θ u v w := by
  have h0 := hθ 0; have h1 := hθ 1; have h2 := hθ 2
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have hPk : P 0 = 0 ∧ P 1 = 0 ∧ P 2 = 0 := by omega
  obtain ⟨hP0, hP1, hP2⟩ := hPk
  rcases (by omega : Q 0 = 0 ∨ Q 0 = 1 ∨ Q 0 = 2) with e0 | e0 | e0
  · 
    rcases (by omega : R 0 = 1 ∨ R 0 = 2) with e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 2 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
    · 
      obtain e2 : Q 1 = 1 := by omega
      obtain e3 : R 1 = 0 := by omega
      obtain e4 : Q 2 = 1 := by omega
      obtain e5 : R 2 = 0 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1) with e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
  · 
    obtain e1 : R 0 = 0 := by omega
    obtain e2 : Q 1 = 0 := by omega
    obtain e3 : R 1 = 1 := by omega
    obtain e4 : Q 2 = 0 := by omega
    obtain e5 : R 2 = 1 := by omega
    rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
    push_cast at h0 h1 h2
    exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
set_option maxHeartbeats 4000000 in
theorem shapes_twoPiThree (θ : Fin 3 → ℝ) (u v w : ℝ) (P Q R : Fin 3 → ℕ)
    (hu : u = 2 * Real.pi / 3) (hv : v = Real.pi / 3 - w)
    (hθ : ∀ k, θ k = (P k : ℝ) * u + (Q k : ℝ) * v + (R k : ℝ) * w)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 3) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) :
    (∀ k, θ k = Real.pi / 3) ∨
    TA θ w w (w + 3 * v) ∨
    TA θ v v (v + 3 * w) ∨
    TA θ w (w + v) (w + 2 * v) ∨
    TA θ v (w + v) (2 * w + v) ∨
    TA θ (2 * w) (2 * v) (w + v) ∨
    TA θ w (2 * w) (3 * v) ∨
    TA θ v (2 * v) (3 * w) ∨
    TA θ w (2 * v) (2 * w + v) ∨
    TA θ v (2 * w) (w + 2 * v) ∨
    TA θ w v u := by
  have h0 := hθ 0; have h1 := hθ 1; have h2 := hθ 2
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have hPk : P 0 = 0 ∧ P 1 = 0 ∧ P 2 = 0 := by omega
  obtain ⟨hP0, hP1, hP2⟩ := hPk
  rcases (by omega : Q 0 = 0 ∨ Q 0 = 1 ∨ Q 0 = 2 ∨ Q 0 = 3) with e0 | e0 | e0 | e0
  · 
    rcases (by omega : R 0 = 1 ∨ R 0 = 2 ∨ R 0 = 3) with e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2 ∨ Q 1 = 3) with e2 | e2 | e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 3 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 3 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2 ∨ Q 1 = 3) with e2 | e2 | e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 3 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
    · 
      rcases (by omega : Q 1 = 1 ∨ Q 1 = 2) with e2 | e2
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 2 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1 ∨ R 0 = 2 ∨ R 0 = 3) with e1 | e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2 ∨ R 1 = 3) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2 ∨ R 1 = 3) with e3 | e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 3 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 3 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (fun k => by rcases fin3 k with rfl | rfl | rfl <;> linarith)
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 2 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
    · 
      obtain e2 : Q 1 = 1 := by omega
      obtain e3 : R 1 = 0 := by omega
      obtain e4 : Q 2 = 1 := by omega
      obtain e5 : R 2 = 0 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1 ∨ R 0 = 2) with e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2 ∨ R 1 = 3) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 3 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1) with e1 | e1
    · 
      obtain e2 : Q 1 = 0 := by omega
      rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 2 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
    · 
      obtain e2 : Q 1 = 0 := by omega
      obtain e3 : R 1 = 1 := by omega
      obtain e4 : Q 2 = 0 := by omega
      obtain e5 : R 2 = 1 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
end Erdos634.Draft.LemmaCShapes
end

section
open scoped BigOperators
namespace Erdos634.Draft.LemmaCArith
lemma rat_prop (x : Fin 3 → ℝ) (hsum : x 0 + x 1 + x 2 = Real.pi)
    (hirr : ∃ i, ¬ ∃ r : ℚ, x i = (r : ℝ) * Real.pi)
    (g e : Fin 3 → ℤ)
    (hg : (g 0 : ℝ) * x 0 + g 1 * x 1 + g 2 * x 2 = 0)
    (he : (e 0 : ℝ) * x 0 + e 1 * x 1 + e 2 * x 2 = 0) (hne : e ≠ 0) :
    ∀ i j, g i * e j = g j * e i := by
  by_contra hcon
  have hw : ¬ (g 1 * e 2 - g 2 * e 1 = 0 ∧ g 2 * e 0 - g 0 * e 2 = 0 ∧
      g 0 * e 1 - g 1 * e 0 = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hcon
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  obtain ⟨i0, hi0⟩ := hirr
  set w0 : ℤ := g 1 * e 2 - g 2 * e 1 with hw0
  set w1 : ℤ := g 2 * e 0 - g 0 * e 2 with hw1
  set w2 : ℤ := g 0 * e 1 - g 1 * e 0 with hw2
  have h01 : x 0 * (w1 : ℝ) = x 1 * w0 := by
    simp only [hw0, hw1]; push_cast
    linear_combination (g 2 : ℝ) * he - (e 2 : ℝ) * hg
  have h02 : x 0 * (w2 : ℝ) = x 2 * w0 := by
    simp only [hw0, hw2]; push_cast
    linear_combination (-(g 1 : ℝ)) * he + (e 1 : ℝ) * hg
  have h12 : x 1 * (w2 : ℝ) = x 2 * w1 := by
    simp only [hw1, hw2]; push_cast
    linear_combination (g 0 : ℝ) * he - (e 0 : ℝ) * hg
  have hS : ((w0 + w1 + w2 : ℤ) : ℝ) ≠ 0 := by
    intro hS0
    push_cast at hS0
    have a0 : (w0 : ℝ) * Real.pi = 0 := by
      have : x 0 * ((w0 : ℝ) + w1 + w2) = (w0 : ℝ) * Real.pi := by
        rw [← hsum]; linear_combination h01 + h02
      rw [← this, hS0]; ring
    have a1 : (w1 : ℝ) * Real.pi = 0 := by
      have : x 1 * ((w0 : ℝ) + w1 + w2) = (w1 : ℝ) * Real.pi := by
        rw [← hsum]; linear_combination (-1 : ℝ) * h01 + h12
      rw [← this, hS0]; ring
    have a2 : (w2 : ℝ) * Real.pi = 0 := by
      have : x 2 * ((w0 : ℝ) + w1 + w2) = (w2 : ℝ) * Real.pi := by
        rw [← hsum]; linear_combination (-1 : ℝ) * h02 - h12
      rw [← this, hS0]; ring
    have hpi := Real.pi_pos.ne'
    have b0 : (w0 : ℝ) = 0 := by
      rcases mul_eq_zero.mp a0 with h | h
      · exact h
      · exact absurd h hpi
    have b1 : (w1 : ℝ) = 0 := by
      rcases mul_eq_zero.mp a1 with h | h
      · exact h
      · exact absurd h hpi
    have b2 : (w2 : ℝ) = 0 := by
      rcases mul_eq_zero.mp a2 with h | h
      · exact h
      · exact absurd h hpi
    exact hw ⟨by exact_mod_cast b0, by exact_mod_cast b1, by exact_mod_cast b2⟩
  apply hi0
  have hSq : ((w0 + w1 + w2 : ℤ) : ℚ) ≠ 0 := by
    intro h; apply hS; have := congrArg (fun q : ℚ => (q : ℝ)) h; simpa using this
  have hx0 : x 0 * ((w0 : ℝ) + w1 + w2) = (w0 : ℝ) * Real.pi := by
    rw [← hsum]; linear_combination h01 + h02
  have hx1 : x 1 * ((w0 : ℝ) + w1 + w2) = (w1 : ℝ) * Real.pi := by
    rw [← hsum]; linear_combination (-1 : ℝ) * h01 + h12
  have hx2 : x 2 * ((w0 : ℝ) + w1 + w2) = (w2 : ℝ) * Real.pi := by
    rw [← hsum]; linear_combination (-1 : ℝ) * h02 - h12
  push_cast at hS
  fin_cases i0
  · refine ⟨(w0 : ℚ) / ((w0 : ℚ) + w1 + w2), ?_⟩
    push_cast; field_simp; linarith
  · refine ⟨(w1 : ℚ) / ((w0 : ℚ) + w1 + w2), ?_⟩
    push_cast; field_simp; linarith
  · refine ⟨(w2 : ℚ) / ((w0 : ℚ) + w1 + w2), ?_⟩
    push_cast; field_simp; linarith
theorem lemmaC_arith (x : Fin 3 → ℝ) (hpos : ∀ i, 0 < x i)
    (hsum : x 0 + x 1 + x 2 = Real.pi)
    (hirr : ∃ i, ¬ ∃ r : ℚ, x i = (r : ℝ) * Real.pi)
    (c : Fin 3 → ℕ) (hc3 : 3 ≤ c 0 + c 1 + c 2)
    (hc : (c 0 : ℝ) * x 0 + c 1 * x 1 + c 2 * x 2 = Real.pi)
    (hne : ¬ (c 0 = 1 ∧ c 1 = 1 ∧ c 2 = 1))
    {ι : Type*} (s : Finset ι) (f : ι → Fin 3 → ℕ) (k : ι → ℕ)
    (hk : ∀ v ∈ s, k v = 1 ∨ k v = 2)
    (hf : ∀ v ∈ s, (f v 0 : ℝ) * x 0 + f v 1 * x 1 + f v 2 * x 2 = (k v : ℝ) * Real.pi)
    (N : ℕ) (hN : ∀ j, ∑ v ∈ s, f v j + c j = N) :
    ∃ d : Fin 3 → ℤ, (∀ j, (c j : ℤ) = 1 + d j) ∧ (∀ j, -1 ≤ d j ∧ d j ≤ 2) ∧
      (∃ j, d j = -1) ∧ (∃ j, 0 < d j) ∧ 0 ≤ d 0 + d 1 + d 2 ∧
      (d 0 : ℝ) * x 0 + d 1 * x 1 + d 2 * x 2 = 0 := by
  classical
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  set e : Fin 3 → ℤ := fun j => (c j : ℤ) - 1 with he_def
  have hex : (e 0 : ℝ) * x 0 + e 1 * x 1 + e 2 * x 2 = 0 := by
    simp only [he_def]; push_cast; linarith
  have hene : e ≠ 0 := by
    intro h
    apply hne
    have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
    simp only [he_def, Pi.zero_apply] at h0 h1 h2
    omega
  set g : ι → Fin 3 → ℤ := fun v j => (f v j : ℤ) - k v with hg_def
  have hgx : ∀ v ∈ s, (g v 0 : ℝ) * x 0 + g v 1 * x 1 + g v 2 * x 2 = 0 := by
    intro v hv
    simp only [hg_def]; push_cast
    have := hf v hv
    linear_combination this - (k v : ℝ) * hsum
  have hp : ∀ v ∈ s, ∀ i j, g v i * e j = g v j * e i := fun v hv =>
    rat_prop x hsum hirr (g v) e (hgx v hv) hex hene
  obtain ⟨n, hnpos, hndvd, α, hnα⟩ : ∃ n : ℤ, 0 < n ∧ (∀ j, n ∣ e j) ∧
      ∃ α : Fin 3 → ℤ, n = α 0 * e 0 + α 1 * e 1 + α 2 * e 2 := by
    set m : ℤ := (Int.gcd (e 0) (e 1) : ℤ) with hm
    have hm0 : m ∣ e 0 := Int.gcd_dvd_left ..
    have hm1 : m ∣ e 1 := Int.gcd_dvd_right ..
    have hmB : m = e 0 * Int.gcdA (e 0) (e 1) + e 1 * Int.gcdB (e 0) (e 1) :=
      Int.gcd_eq_gcd_ab _ _
    set n : ℤ := (Int.gcd m (e 2) : ℤ) with hn
    have hnm : n ∣ m := Int.gcd_dvd_left ..
    have hn2 : n ∣ e 2 := Int.gcd_dvd_right ..
    have hnB : n = m * Int.gcdA m (e 2) + e 2 * Int.gcdB m (e 2) := Int.gcd_eq_gcd_ab _ _
    have hdv : ∀ j, n ∣ e j := by
      intro j; fin_cases j
      · exact hnm.trans hm0
      · exact hnm.trans hm1
      · exact hn2
    refine ⟨n, ?_, hdv, ![Int.gcdA (e 0) (e 1) * Int.gcdA m (e 2),
      Int.gcdB (e 0) (e 1) * Int.gcdA m (e 2), Int.gcdB m (e 2)], ?_⟩
    · have hn0 : n ≠ 0 := by
        intro h0
        apply hene
        funext j
        have := hdv j
        rw [h0, zero_dvd_iff] at this
        simpa using this
      exact lt_of_le_of_ne (Int.natCast_nonneg _) (Ne.symm hn0)
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [hnB, hmB]; ring
  have hn0 : n ≠ 0 := hnpos.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  set d : Fin 3 → ℤ := fun j => e j / n with hd_def
  have hed : ∀ j, e j = n * d j := fun j => (Int.mul_ediv_cancel' (hndvd j)).symm
  have hdx : (d 0 : ℝ) * x 0 + d 1 * x 1 + d 2 * x 2 = 0 := by
    have h : (n : ℝ) * ((d 0 : ℝ) * x 0 + d 1 * x 1 + d 2 * x 2) = 0 := by
      have := hex
      rw [hed 0, hed 1, hed 2] at this
      push_cast at this; linarith
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hnR
    · exact h
  have hdne : ∃ j, d j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hene; funext j; rw [hed j, hcon j]; simp
  set t : ι → ℤ := fun v => α 0 * g v 0 + α 1 * g v 1 + α 2 * g v 2 with ht_def
  have hgt : ∀ v ∈ s, ∀ j, g v j = t v * d j := by
    intro v hv j
    have hp' := hp v hv
    have key : n * g v j = n * (t v * d j) := by
      have h1 : n * g v j = t v * e j := by
        rw [hnα]; simp only [ht_def]
        linear_combination α 0 * hp' j 0 + α 1 * hp' j 1 + α 2 * hp' j 2
      rw [h1, hed j]; ring
    exact mul_left_cancel₀ hn0 key
  have hfv : ∀ v ∈ s, ∀ j, (f v j : ℤ) = k v + t v * d j := by
    intro v hv j
    have := hgt v hv j
    simp only [hg_def] at this
    linarith
  have hcj : ∀ j, (c j : ℤ) = 1 + n * d j := by
    intro j; have := hed j; simp only [he_def] at this; linarith
  set T : ℤ := ∑ v ∈ s, t v with hT
  set K : ℤ := ∑ v ∈ s, (k v : ℤ) with hK
  have hcount : ∀ j, K + T * d j = (N : ℤ) - c j := by
    intro j
    have h1 : ∑ v ∈ s, (f v j : ℤ) = (N : ℤ) - c j := by
      have := hN j
      have h2 : ((∑ v ∈ s, f v j : ℕ) : ℤ) + c j = N := by exact_mod_cast this
      push_cast at h2; linarith
    rw [← h1, Finset.sum_congr rfl (fun v hv => hfv v hv j), Finset.sum_add_distrib, ← Finset.sum_mul]
  have hTn : ∀ j, (T + n) * d j = (N : ℤ) - 1 - K := by
    intro j; have := hcount j; have := hcj j; linarith
  have hNK : (N : ℤ) - 1 - K = 0 := by
    have h : ((N : ℝ) - 1 - K) * Real.pi = 0 := by
      have e0 := hTn 0; have e1 := hTn 1; have e2 := hTn 2
      have r0 : (((T + n) * d 0 : ℤ) : ℝ) = (((N : ℤ) - 1 - K : ℤ) : ℝ) := by rw [e0]
      have r1 : (((T + n) * d 1 : ℤ) : ℝ) = (((N : ℤ) - 1 - K : ℤ) : ℝ) := by rw [e1]
      have r2 : (((T + n) * d 2 : ℤ) : ℝ) = (((N : ℤ) - 1 - K : ℤ) : ℝ) := by rw [e2]
      push_cast at r0 r1 r2
      have : ((N : ℝ) - 1 - K) * (x 0 + x 1 + x 2)
          = ((T : ℝ) + n) * ((d 0 : ℝ) * x 0 + d 1 * x 1 + d 2 * x 2) := by
        linear_combination (-x 0) * r0 + (-x 1) * r1 + (-x 2) * r2
      rw [hsum, hdx] at this; linarith
    rcases mul_eq_zero.mp h with h | h
    · exact_mod_cast (by linarith : ((N : ℝ) - 1 - K) = 0)
    · exact absurd h hpi
  have hTn0 : T + n = 0 := by
    obtain ⟨j, hj⟩ := hdne
    have := hTn j
    rw [hNK] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hj
  have hTneg : T = -n := by linarith
  obtain ⟨v0, hv0, htv0⟩ : ∃ v ∈ s, t v < 0 := by
    by_contra h
    push Not at h
    have : 0 ≤ T := Finset.sum_nonneg h
    linarith
  have hk2 : (k v0 : ℤ) ≤ 2 := by have := hk v0 hv0; omega
  have hdle : ∀ j, d j ≤ 2 := by
    intro j
    by_contra hj
    push Not at hj
    have h1 := hfv v0 hv0 j
    have h2 : (0 : ℤ) ≤ (f v0 j : ℤ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -1 - t v0) (by linarith : (0 : ℤ) ≤ d j)]
  have hneg : ∃ j, d j < 0 := by
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := hdne
    have hjpos : 0 < d j := lt_of_le_of_ne (h j) (Ne.symm hj)
    have t0 : 0 ≤ (d 0 : ℝ) * x 0 := mul_nonneg (by exact_mod_cast h 0) (hpos 0).le
    have t1 : 0 ≤ (d 1 : ℝ) * x 1 := mul_nonneg (by exact_mod_cast h 1) (hpos 1).le
    have t2 : 0 ≤ (d 2 : ℝ) * x 2 := mul_nonneg (by exact_mod_cast h 2) (hpos 2).le
    have hjr : 0 < (d j : ℝ) * x j := mul_pos (by exact_mod_cast hjpos) (hpos j)
    fin_cases j <;> simp at hjr <;> linarith
  have hposx : ∃ j, 0 < d j := by
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := hdne
    have hjneg : d j < 0 := lt_of_le_of_ne (h j) hj
    have t0 : (d 0 : ℝ) * x 0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h 0) (hpos 0).le
    have t1 : (d 1 : ℝ) * x 1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h 1) (hpos 1).le
    have t2 : (d 2 : ℝ) * x 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h 2) (hpos 2).le
    have hjr : (d j : ℝ) * x j < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast hjneg) (hpos j)
    fin_cases j <;> simp at hjr <;> linarith
  obtain ⟨j0, hj0⟩ := hneg
  have hc0 : (0 : ℤ) ≤ (c j0 : ℤ) := Nat.cast_nonneg _
  have hn1 : n = 1 := by
    have := hcj j0
    nlinarith [mul_nonneg hnpos.le (by linarith : (0 : ℤ) ≤ -1 - d j0)]
  subst hn1
  have hcj1 : ∀ j, (c j : ℤ) = 1 + d j := fun j => by have := hcj j; linarith
  have hge : ∀ j, -1 ≤ d j := fun j => by
    have := hcj1 j; have : (0 : ℤ) ≤ (c j : ℤ) := Nat.cast_nonneg _; linarith
  refine ⟨d, hcj1, fun j => ⟨hge j, hdle j⟩, ⟨j0, by have := hge j0; omega⟩, hposx, ?_, hdx⟩
  have h0 := hcj1 0; have h1 := hcj1 1; have h2 := hcj1 2
  omega
def sixVectors : Finset (ℤ × ℤ × ℤ) :=
  {(-1, 1, 0), (-1, 0, 2), (-1, 1, 1), (-1, 1, 2), (-1, 2, 2), (-1, -1, 2)}
theorem enum_six (a b c : ℤ) (ha : -1 ≤ a ∧ a ≤ 2) (hb : -1 ≤ b ∧ b ≤ 2) (hc : -1 ≤ c ∧ c ≤ 2)
    (hm : a = -1 ∨ b = -1 ∨ c = -1) (hp : 0 < a ∨ 0 < b ∨ 0 < c) (hs : 0 ≤ a + b + c) :
    ∃ i j l : Fin 3, i ≠ j ∧ j ≠ l ∧ i ≠ l ∧
      (![a, b, c] i, ![a, b, c] j, ![a, b, c] l) ∈ sixVectors := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  interval_cases a <;> interval_cases b <;> interval_cases c <;> first
    | (exfalso; omega)
    | decide
end Erdos634.Draft.LemmaCArith
end

section
open scoped Classical
open Erdos634.Geometry
namespace Erdos634.Draft.LemmaCFigures
theorem vertex_figure_sum {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi)
    {v : Plane} (hv : v ∈ cornerPts D.toDissection) (hnc : v ∉ Set.range D.target.pts) :
    ∃ k : ℕ, (k = 1 ∨ k = 2) ∧
      (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card : ℝ) * α
      + (({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card : ℝ) * β
      + (({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card : ℝ) * γ
      = (k : ℝ) * Real.pi := by
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hj
  have hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem_at_corner D α β γ hmα hmβ hmγ j m hm i
  have hpi := Real.pi_pos
  have hsumv := VertexFigureReal.sum_by_value ({α, β, γ, Real.pi, 0} : Finset ℝ)
    (fun i => (D.tile i).localAngle v) hvals
  rw [show ({α, β, γ, Real.pi, 0} : Finset ℝ)
      = insert α (insert β (insert γ (insert Real.pi {0}))) from rfl] at hsumv
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hαβ, hαγ, hαπ.ne, hα0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hβγ, hβπ.ne, hβ0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hγπ.ne, hγ0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hpi.ne'),
      Finset.sum_singleton] at hsumv
  beta_reduce at hsumv
  set cα := (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card : ℝ) with hcα
  set cβ := (({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card : ℝ) with hcβ
  set cγ := (({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card : ℝ) with hcγ
  set cπ := ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card with hcπ
  have hown : cα ≠ 0 ∨ cβ ≠ 0 ∨ cγ ≠ 0 := by
    have h := localAngle_at_own_vertex_mem D α β γ hmα hmβ hmγ j m
    rw [hm] at h
    have hne : ∀ c : Finset (Fin N), j ∈ c → (c.card : ℝ) ≠ 0 := fun c hc => by
      have := Finset.card_pos.mpr ⟨j, hc⟩; positivity
    rcases h with h | h | h
    · exact Or.inl (hne _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    · exact Or.inr (Or.inl (hne _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
    · exact Or.inr (Or.inr (hne _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
  have hc0 : 0 ≤ cα := Nat.cast_nonneg _
  have hc1 : 0 ≤ cβ := Nat.cast_nonneg _
  have hc2 : 0 ≤ cγ := Nat.cast_nonneg _
  have hcp : 0 ≤ (cπ : ℝ) := Nat.cast_nonneg _
  have hFpos : 0 < cα * α + cβ * β + cγ * γ := by
    have p0 := mul_nonneg hc0 hα0.le
    have p1 := mul_nonneg hc1 hβ0.le
    have p2 := mul_nonneg hc2 hγ0.le
    rcases hown with h | h | h
    · have := mul_pos (lt_of_le_of_ne hc0 (Ne.symm h)) hα0; linarith
    · have := mul_pos (lt_of_le_of_ne hc1 (Ne.symm h)) hβ0; linarith
    · have := mul_pos (lt_of_le_of_ne hc2 (Ne.symm h)) hγ0; linarith
  rcases Erdos634.Geometry.cornerPts_trichotomy D.toDissection hv with h | ⟨hfr, -⟩ | hint
  · exact absurd h hnc
  · have htot := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hfr hnc
    rw [hsumv] at htot
    have : (cπ : ℝ) < 1 := by nlinarith
    have hz : cπ = 0 := by exact_mod_cast (by exact_mod_cast this : cπ < 1) |> Nat.lt_one_iff.mp
    refine ⟨1, Or.inl rfl, ?_⟩
    rw [hz] at htot; push_cast at htot ⊢; linarith
  · have htot := Erdos634.PinPlumbing.pin_angle_sum_interior D.toDissection hint
    rw [hsumv] at htot
    have : (cπ : ℝ) < 2 := by nlinarith
    have hle : cπ ≤ 1 := by
      have : cπ < 2 := by exact_mod_cast this
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hz | hz
    · refine ⟨2, Or.inr rfl, ?_⟩
      rw [hz] at htot; push_cast at htot ⊢; linarith
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [hz] at htot; push_cast at htot ⊢; linarith
theorem count_sum {N : ℕ} (la : Fin N → ℝ) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi)
    (hvals : ∀ i, la i ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ)) :
    ∑ i, la i = (({i | la i = α} : Finset (Fin N)).card : ℝ) * α
      + (({i | la i = β} : Finset (Fin N)).card : ℝ) * β
      + (({i | la i = γ} : Finset (Fin N)).card : ℝ) * γ
      + (({i | la i = Real.pi} : Finset (Fin N)).card : ℝ) * Real.pi := by
  have hpi := Real.pi_pos
  have hsumv := VertexFigureReal.sum_by_value ({α, β, γ, Real.pi, 0} : Finset ℝ) la hvals
  rw [show ({α, β, γ, Real.pi, 0} : Finset ℝ)
      = insert α (insert β (insert γ (insert Real.pi {0}))) from rfl] at hsumv
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hαβ, hαγ, hαπ.ne, hα0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hβγ, hβπ.ne, hβ0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hγπ.ne, hγ0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hpi.ne'),
      Finset.sum_singleton] at hsumv
  rw [hsumv]; ring
theorem corner_figure {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi) (k : Fin 3) :
    D.target.pts k ∈ cornerPts D.toDissection ∧
    (({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card : ℝ) * α
      + (({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card : ℝ) * β
      + (({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card : ℝ) * γ
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) ∧
    1 ≤ ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card := by
  have hpi := Real.pi_pos
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts k) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) := by
    intro i
    have hmem := congruentDissection_localAngle_mem_all D α β γ hmα hmβ hmγ (D.target.pts k) i
    have h2 := Erdos634.Geometry.Dissection.localAngle_ne_two_pi_of_not_mem_interior
      (D.toDissection.target_vertex_not_interior_tile k i)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    rcases hmem with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact absurd h h2
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hcs := count_sum (fun i => (D.tile i).localAngle (D.target.pts k)) α β γ hαβ hαγ hβγ
    hα0 hβ0 hγ0 hαπ hβπ hγπ hvals
  have hθ := Erdos634.VertexFigureReal.corner_angle_sum D.toDissection k
  have hθlt := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target k
  have hθpos := Erdos634.MarchFlank.cornerAngle_pos D.target k
  beta_reduce at hcs
  set cα := (({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card : ℝ)
  set cβ := (({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card : ℝ)
  set cγ := (({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card : ℝ)
  set cπ := (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card : ℝ)
  have hc0 : 0 ≤ cα := Nat.cast_nonneg _
  have hc1 : 0 ≤ cβ := Nat.cast_nonneg _
  have hc2 : 0 ≤ cγ := Nat.cast_nonneg _
  have hcp : 0 ≤ cπ := Nat.cast_nonneg _
  have hcπ0 : cπ = 0 := by
    by_contra hne
    have : 1 ≤ cπ := by
      have : (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card) ≠ 0 := by
        intro h; apply hne; simp [cπ, h]
      exact Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr this)
    nlinarith [mul_nonneg hc0 hα0.le, mul_nonneg hc1 hβ0.le, mul_nonneg hc2 hγ0.le]
  rw [hcπ0] at hcs
  have hF : cα * α + cβ * β + cγ * γ = cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) := by linarith
  have hFpos : 0 < cα * α + cβ * β + cγ * γ := by rw [hF]; exact hθpos
  have hsum1 : 1 ≤ ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card := by
    by_contra hlt
    have h0 : ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 0 := by omega
    have h1 : ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 0 := by omega
    have h2 : ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 := by omega
    have e0 : cα = 0 := by simp [cα, h0]
    have e1 : cβ = 0 := by simp [cβ, h1]
    have e2 : cγ = 0 := by simp [cγ, h2]
    rw [e0, e1, e2] at hFpos; simp at hFpos
  refine ⟨?_, hF, hsum1⟩
  have : ∃ i, (D.tile i).localAngle (D.target.pts k) = α ∨ (D.tile i).localAngle (D.target.pts k) = β
      ∨ (D.tile i).localAngle (D.target.pts k) = γ := by
    by_contra hno
    push Not at hno
    have hz : ∀ (θ : ℝ), (∀ i, (D.tile i).localAngle (D.target.pts k) ≠ θ) →
        ({i | (D.tile i).localAngle (D.target.pts k) = θ} : Finset (Fin N)).card = 0 := by
      intro θ h; simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff, h]
    have := hz α (fun i => (hno i).1)
    have := hz β (fun i => (hno i).2.1)
    have := hz γ (fun i => (hno i).2.2)
    omega
  obtain ⟨i, hi⟩ := this
  have hne : ∀ θ, (D.tile i).localAngle (D.target.pts k) = θ → 0 < θ → θ < Real.pi →
      D.target.pts k ∈ cornerPts D.toDissection := by
    intro θ h h0 hpi'
    obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile i) h h0.ne' hpi'.ne (by linarith)
    rw [← hm]; exact mem_cornerPts D.toDissection i m
  rcases hi with h | h | h
  · exact hne α h hα0 hαπ
  · exact hne β h hβ0 hβπ
  · exact hne γ h hγ0 hγπ
end Erdos634.Draft.LemmaCFigures
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.Draft.LemmaCFigures
namespace Erdos634.Draft.LemmaCAssemble
noncomputable def cnt {N : ℕ} (D : CongruentDissection N) (θ : ℝ) (v : Plane) : ℕ :=
  ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)).card
noncomputable def cfig {N : ℕ} (D : CongruentDissection N) (x : Fin 3 → ℝ) (j : Fin 3) : ℕ :=
  ∑ k : Fin 3, cnt D (x j) (D.target.pts k)
theorem lemmaC_geometric {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi)
    (hirr : ∃ i, ¬ ∃ r : ℚ, ![α, β, γ] i = (r : ℝ) * Real.pi)
    (hne : ¬ (cfig D ![α, β, γ] 0 = 1 ∧ cfig D ![α, β, γ] 1 = 1 ∧ cfig D ![α, β, γ] 2 = 1)) :
    ∃ d : Fin 3 → ℤ, (∀ j, (cfig D ![α, β, γ] j : ℤ) = 1 + d j) ∧ (∀ j, -1 ≤ d j ∧ d j ≤ 2) ∧
      (∃ j, d j = -1) ∧ (∃ j, 0 < d j) ∧ 0 ≤ d 0 + d 1 + d 2 ∧
      (d 0 : ℝ) * α + d 1 * β + d 2 * γ = 0 := by
  have hpi := Real.pi_pos
  set x : Fin 3 → ℝ := ![α, β, γ] with hx
  have hsum : x 0 + x 1 + x 2 = Real.pi := by
    have := Erdos634.Geometry.cornerAngle_sum D.model
    simp only [hx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linarith
  have hpos : ∀ i, 0 < x i := by intro i; fin_cases i <;> simp [hx, hα0, hβ0, hγ0]
  set s : Finset Plane := (cornerPts D.toDissection).filter (fun v => v ∉ Set.range D.target.pts)
    with hs
  have hF1 : ∀ v ∈ s, ∃ k : ℕ, (k = 1 ∨ k = 2) ∧
      (cnt D α v : ℝ) * α + (cnt D β v : ℝ) * β + (cnt D γ v : ℝ) * γ = (k : ℝ) * Real.pi := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
    exact vertex_figure_sum D α β γ hmα hmβ hmγ hαβ hαγ hβγ hα0 hβ0 hγ0 hαπ hβπ hγπ hv1 hv2
  choose! k hk hf using hF1
  have hcorner := fun kk => corner_figure D α β γ hmα hmβ hmγ hαβ hαγ hβγ hα0 hβ0 hγ0 hαπ hβπ hγπ kk
  have hxk : ∀ kk : Fin 3, cornerAngle (D.model.pts (kk + 1)) (D.model.pts kk)
      (D.model.pts (kk + 2)) = x kk := by
    intro kk; fin_cases kk
    · simpa [hx] using hmα
    · simpa [hx] using hmβ
    · simpa [hx] using hmγ
  have hxinj : ∀ a b : Fin 3, x a = x b → a = b := by
    intro a b h
    have hd : ∀ u v : ℝ, u = v → v = u → u ≠ v → False := fun u v h _ hn => hn h
    fin_cases a <;> fin_cases b <;> simp [hx] at h ⊢ <;> simp_all [eq_comm]
  have htotal : ∀ j : Fin 3, ∑ v ∈ cornerPts D.toDissection, cnt D (x j) v = N := by
    intro j
    have := congruentDissection_corner_balance D
      (fun a b h => hxinj a b (by rw [← hxk a, ← hxk b]; exact h)) j
      (by rw [hxk j]; exact (hpos j).ne')
      (by rw [hxk j]; fin_cases j <;> simp [hx] <;> linarith)
      (by rw [hxk j]; fin_cases j <;> simp [hx] <;> linarith)
    rw [hxk j] at this
    exact this
  have hcorn_mem : ∀ kk, D.target.pts kk ∈ cornerPts D.toDissection := fun kk => (hcorner kk).1
  have himg : (cornerPts D.toDissection).filter (fun v => v ∈ Set.range D.target.pts)
      = Finset.univ.image D.target.pts := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
    constructor
    · rintro ⟨_, kk, hkk⟩; exact ⟨kk, hkk⟩
    · rintro ⟨kk, rfl⟩; exact ⟨hcorn_mem kk, kk, rfl⟩
  have hsplit : ∀ j, ∑ v ∈ s, cnt D (x j) v + cfig D x j = N := by
    intro j
    have h1 := Finset.sum_filter_add_sum_filter_not (cornerPts D.toDissection)
      (fun v => v ∈ Set.range D.target.pts) (fun v => cnt D (x j) v)
    rw [himg, Finset.sum_image (fun a _ b _ hab => Erdos634.CertNode.pts_injective D.target hab),
      htotal j] at h1
    have h2 : cfig D x j = ∑ kk : Fin 3, cnt D (x j) (D.target.pts kk) := rfl
    have h3 : s = (cornerPts D.toDissection).filter (fun v => ¬ v ∈ Set.range D.target.pts) := rfl
    rw [h3]; omega
  have e0 := (hcorner 0).2
  have e1 := (hcorner 1).2
  have e2 := (hcorner 2).2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at e0 e1 e2
  have hT := Erdos634.Geometry.cornerAngle_sum D.target
  have hc3 : 3 ≤ cfig D x 0 + cfig D x 1 + cfig D x 2 := by
    obtain ⟨-, a0⟩ := e0
    obtain ⟨-, a1⟩ := e1
    obtain ⟨-, a2⟩ := e2
    simp only [cfig, cnt, Fin.sum_univ_three, hx, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    omega
  have hc : (cfig D x 0 : ℝ) * x 0 + cfig D x 1 * x 1 + cfig D x 2 * x 2 = Real.pi := by
    obtain ⟨b0, -⟩ := e0
    obtain ⟨b1, -⟩ := e1
    obtain ⟨b2, -⟩ := e2
    simp only [cfig, cnt, Fin.sum_univ_three, hx, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast
    linarith
  have hf' : ∀ v ∈ s, (cnt D (x 0) v : ℝ) * x 0 + (cnt D (x 1) v : ℝ) * x 1
      + (cnt D (x 2) v : ℝ) * x 2 = (k v : ℝ) * Real.pi := by
    intro v hv
    have := (hf v hv)
    simpa [hx] using this
  obtain ⟨d, hd1, hd2, hd3, hd4, hd5, hd6⟩ := Erdos634.Draft.LemmaCArith.lemmaC_arith x hpos hsum
    hirr (fun j => cfig D x j) hc3 hc hne s (fun v j => cnt D (x j) v) k (fun v hv => hk v hv)
    hf' N hsplit
  refine ⟨d, hd1, hd2, hd3, hd4, hd5, ?_⟩
  simpa [hx] using hd6
end Erdos634.Draft.LemmaCAssemble
end

section
open scoped Classical
namespace Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry Erdos634.TilePlacement
def IrrPi (x : ℝ) : Prop := ¬ ∃ r : ℚ, x = (r : ℝ) * Real.pi
def TgtAngles {N : ℕ} (D : CongruentDissection N) (x y z : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), D.target.angleAt (σ 0) = x ∧ D.target.angleAt (σ 1) = y ∧
    D.target.angleAt (σ 2) = z
def SimilarTM {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ (μ : ℝ) (τ : Equiv.Perm (Fin 3)), ∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧
    D.target.oppLen k = μ * D.model.oppLen (τ k)
def RightCase {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ Irrational (α / Real.pi) ∧
    (∃ p q : Fin 3, p ≠ q ∧ D.model.angleAt p = α ∧ D.model.angleAt q = Real.pi / 2) ∧
    ∃ γ : ℝ, (γ = α ∨ γ = Real.pi / 2 - α) ∧
      ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = γ ∧ D.target.angleAt j = γ
def TwoAlphaCase {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α a b c : ℝ, IrrPi α ∧ D.model.TwoAlphaData α a b c ∧
    ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = α ∧ D.target.angleAt j = α
def SixtyTile {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α a b c : ℝ, IrrPi α ∧ D.model.SixtyData α a b c
def Equilateral {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∀ k, D.target.angleAt k = Real.pi / 3
def IsoTP {N : ℕ} (D : CongruentDissection N) (α : ℝ) : Prop :=
  TgtAngles D α α (α + 3 * (Real.pi / 3 - α)) ∨
    TgtAngles D (Real.pi / 3 - α) (Real.pi / 3 - α) ((Real.pi / 3 - α) + 3 * α)
def F1Shape {N : ℕ} (D : CongruentDissection N) (α : ℝ) : Prop :=
  TgtAngles D α (α + (Real.pi / 3 - α)) (α + 2 * (Real.pi / 3 - α)) ∨
    TgtAngles D (Real.pi / 3 - α) (α + (Real.pi / 3 - α)) (2 * α + (Real.pi / 3 - α))
def F2to4Shape {N : ℕ} (D : CongruentDissection N) (α : ℝ) : Prop :=
  TgtAngles D (2 * α) (2 * (Real.pi / 3 - α)) (α + (Real.pi / 3 - α)) ∨
  TgtAngles D α (2 * α) (3 * (Real.pi / 3 - α)) ∨
  TgtAngles D (Real.pi / 3 - α) (2 * (Real.pi / 3 - α)) (3 * α) ∨
  TgtAngles D α (2 * (Real.pi / 3 - α)) (2 * α + (Real.pi / 3 - α)) ∨
  TgtAngles D (Real.pi / 3 - α) (2 * α) (α + 2 * (Real.pi / 3 - α))
def TwoPiThreeCase {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α a b c : ℝ, IrrPi α ∧ D.model.TwoPiThreeData α a b c ∧
    (Equilateral D ∨ IsoTP D α ∨ F1Shape D α ∨ F2to4Shape D α)
def ThreeTwoCase {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α β a b c : ℝ, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ D.model.ThreeAlphaData α β a b c ∧
    (TgtAngles D β β (3 * α) ∨ TgtAngles D (α + β) (α + β) α ∨
     TgtAngles D (2 * α) β (α + β) ∨ TgtAngles D (2 * α) α (2 * β) ∨
     TgtAngles D α α (α + 2 * β))
end Erdos634.Draft.TheoremPConditional
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCAssemble
namespace Erdos634.Draft.LemmaCSimilar
theorem sides_of_angles (T M : Tri) (τ : Equiv.Perm (Fin 3))
    (h : ∀ k, T.angleAt k = M.angleAt (τ k)) :
    ∃ μ : ℝ, ∀ k, T.oppLen k = μ * M.oppLen (τ k) := by
  have hs : 0 < Real.sin (T.angleAt 0) := Erdos634.Geometry.A1Field.sin_angle_pos T 0
  have hm : 0 < M.oppLen (τ 0) := Erdos634.Geometry.Row3.RP.oppLen_pos M _
  refine ⟨T.oppLen 0 / M.oppLen (τ 0), fun k => ?_⟩
  have h1 := T.lawSin 0 k
  have h2 := M.lawSin (τ 0) (τ k)
  rw [← h 0, ← h k] at h2
  field_simp
  have : Real.sin (T.angleAt 0) * (T.oppLen k * M.oppLen (τ 0))
      = Real.sin (T.angleAt 0) * (T.oppLen 0 * M.oppLen (τ k)) := by
    linear_combination M.oppLen (τ 0) * h1 - T.oppLen 0 * h2
  exact mul_left_cancel₀ hs.ne' this
theorem perm_of_figures (T M : Tri) (α β γ : ℝ)
    (hM0 : M.angleAt 0 = α) (hM1 : M.angleAt 1 = β) (hM2 : M.angleAt 2 = γ)
    (a b c : Fin 3 → ℕ)
    (hF : ∀ k, (a k : ℝ) * α + (b k : ℝ) * β + (c k : ℝ) * γ = T.angleAt k)
    (hpos : ∀ k, 1 ≤ a k + b k + c k)
    (h0 : a 0 + a 1 + a 2 = 1) (h1 : b 0 + b 1 + b 2 = 1) (h2 : c 0 + c 1 + c 2 = 1) :
    ∃ τ : Equiv.Perm (Fin 3), ∀ k, T.angleAt k = M.angleAt (τ k) := by
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  let J : Fin 3 → Fin 3 := fun k => if a k = 1 then 0 else if b k = 1 then 1 else 2
  have hc : ∀ k : Fin 3, (a k = 1 ∧ b k = 0 ∧ c k = 0) ∨ (a k = 0 ∧ b k = 1 ∧ c k = 0)
      ∨ (a k = 0 ∧ b k = 0 ∧ c k = 1) := by
    have : ∀ k : Fin 3, 1 ≤ a k + b k + c k := hpos
    intro k
    rcases fin3 k with rfl | rfl | rfl <;> omega
  have hJinj : Function.Injective J := by
    intro k l hkl
    by_contra hne
    have hk := hc k; have hl := hc l
    have hkl' : k ≠ l := hne
    rcases fin3 k with rfl | rfl | rfl <;> rcases fin3 l with rfl | rfl | rfl <;>
      first | exact absurd rfl hkl' | (simp only [J] at hkl; split_ifs at hkl <;> simp_all <;> omega)
  have hθ : ∀ k, T.angleAt k = M.angleAt (J k) := by
    intro k
    have hk := hF k
    rcases hc k with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · simp only [J, e0, if_true]; rw [← hk, e0, e1, e2, hM0]; simp
    · simp only [J, e0, e1]; simp; rw [← hk, e0, e1, e2, hM1]; simp
    · simp only [J, e0, e1]; simp; rw [← hk, e0, e1, e2, hM2]; simp
  exact ⟨Equiv.ofBijective J (Finite.injective_iff_bijective.mp hJinj), hθ⟩
theorem cfig_ne_of_notSimilar {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi)
    (hns : ¬ SimilarTM D) :
    ¬ (cfig D ![α, β, γ] 0 = 1 ∧ cfig D ![α, β, γ] 1 = 1 ∧ cfig D ![α, β, γ] 2 = 1) := by
  rintro ⟨h0, h1, h2⟩
  apply hns
  have hcorner := fun kk => Erdos634.Draft.LemmaCFigures.corner_figure D α β γ hmα hmβ hmγ hαβ hαγ
    hβγ hα0 hβ0 hγ0 hαπ hβπ hγπ kk
  obtain ⟨τ, hτ⟩ := perm_of_figures D.target D.model α β γ hmα hmβ hmγ
    (fun k => cnt D α (D.target.pts k)) (fun k => cnt D β (D.target.pts k))
    (fun k => cnt D γ (D.target.pts k))
    (fun k => (hcorner k).2.1) (fun k => (hcorner k).2.2)
    (by simpa [cfig, Fin.sum_univ_three] using h0)
    (by simpa [cfig, Fin.sum_univ_three] using h1)
    (by simpa [cfig, Fin.sum_univ_three] using h2)
  obtain ⟨μ, hμ⟩ := sides_of_angles D.target D.model τ hτ
  exact ⟨μ, τ, fun k => ⟨hτ k, hμ k⟩⟩
end Erdos634.Draft.LemmaCSimilar
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCFigures
namespace Erdos634.Draft.LemmaCIso
theorem corner_fig2 {N : ℕ} (D : CongruentDissection N) (a b : ℝ)
    (hmod : ∀ k : Fin 3, cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) = a
      ∨ cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) = b)
    (hab : a ≠ b) (ha0 : 0 < a) (hb0 : 0 < b) (haπ : a < Real.pi) (hbπ : b < Real.pi) (k : Fin 3) :
    D.target.pts k ∈ cornerPts D.toDissection ∧
    (({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card : ℝ) * a
      + (({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card : ℝ) * b
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) ∧
    1 ≤ ({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card := by
  have hpi := Real.pi_pos
  set x0 := cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) with hx0
  set x1 := cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) with hx1
  set x2 := cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) with hx2
  have hxab : ∀ y, (y = x0 ∨ y = x1 ∨ y = x2) → y = a ∨ y = b := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact hmod 0
    · exact hmod 1
    · exact hmod 2
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts k) ∈ ({a, b, Real.pi, 0} : Finset ℝ) := by
    intro i
    have hmem := congruentDissection_localAngle_mem_all D x0 x1 x2 rfl rfl rfl (D.target.pts k) i
    have h2 := Erdos634.Geometry.Dissection.localAngle_ne_two_pi_of_not_mem_interior
      (D.toDissection.target_vertex_not_interior_tile k i)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    rcases hmem with h | h | h | h | h | h
    · rcases hxab _ (Or.inl rfl) with e | e <;> [exact Or.inl (h.trans e); exact Or.inr (Or.inl (h.trans e))]
    · rcases hxab _ (Or.inr (Or.inl rfl)) with e | e <;> [exact Or.inl (h.trans e); exact Or.inr (Or.inl (h.trans e))]
    · rcases hxab _ (Or.inr (Or.inr rfl)) with e | e <;> [exact Or.inl (h.trans e); exact Or.inr (Or.inl (h.trans e))]
    · exact Or.inr (Or.inr (Or.inl h))
    · exact absurd h h2
    · exact Or.inr (Or.inr (Or.inr h))
  have hsumv := VertexFigureReal.sum_by_value ({a, b, Real.pi, 0} : Finset ℝ)
    (fun i => (D.tile i).localAngle (D.target.pts k)) hvals
  rw [show ({a, b, Real.pi, 0} : Finset ℝ) = insert a (insert b (insert Real.pi {0})) from rfl] at hsumv
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hab, haπ.ne, ha0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hbπ.ne, hb0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hpi.ne'),
      Finset.sum_singleton] at hsumv
  beta_reduce at hsumv
  have hθ := Erdos634.VertexFigureReal.corner_angle_sum D.toDissection k
  have hθlt := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target k
  have hθpos := Erdos634.MarchFlank.cornerAngle_pos D.target k
  set cα := (({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card : ℝ) with hca
  set cβ := (({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card : ℝ) with hcb
  set cπ := (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card : ℝ) with hcp
  have hc0 : 0 ≤ cα := Nat.cast_nonneg _
  have hc1 : 0 ≤ cβ := Nat.cast_nonneg _
  have hcπ0 : cπ = 0 := by
    by_contra hne
    have : 1 ≤ cπ := by
      have : (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card) ≠ 0 := by
        intro h; apply hne; simp [cπ, h]
      exact Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr this)
    nlinarith [mul_nonneg hc0 ha0.le, mul_nonneg hc1 hb0.le]
  rw [hcπ0] at hsumv
  have hF : cα * a + cβ * b = cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) := by linarith
  have hFpos : 0 < cα * a + cβ * b := by rw [hF]; exact hθpos
  have hsum1 : 1 ≤ ({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card := by
    by_contra hlt
    have h0 : ({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card = 0 := by omega
    have h1 : ({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card = 0 := by omega
    have e0 : cα = 0 := by simp [cα, h0]
    have e1 : cβ = 0 := by simp [cβ, h1]
    rw [e0, e1] at hFpos; simp at hFpos
  refine ⟨?_, hF, hsum1⟩
  have : ∃ i, (D.tile i).localAngle (D.target.pts k) = a ∨ (D.tile i).localAngle (D.target.pts k) = b := by
    by_contra hno
    push Not at hno
    have hz : ∀ (θ : ℝ), (∀ i, (D.tile i).localAngle (D.target.pts k) ≠ θ) →
        ({i | (D.tile i).localAngle (D.target.pts k) = θ} : Finset (Fin N)).card = 0 := by
      intro θ h; simp [h]
    have := hz a (fun i => (hno i).1)
    have := hz b (fun i => (hno i).2)
    omega
  obtain ⟨i, hi⟩ := this
  have hne : ∀ θ, (D.tile i).localAngle (D.target.pts k) = θ → 0 < θ → θ < Real.pi →
      D.target.pts k ∈ cornerPts D.toDissection := by
    intro θ h h0 hpi'
    obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile i) h h0.ne' hpi'.ne (by linarith)
    rw [← hm]; exact mem_cornerPts D.toDissection i m
  rcases hi with h | h
  · exact hne a h ha0 haπ
  · exact hne b h hb0 hbπ
theorem iso_arith (a b : ℝ) (hb : 2 * a + b = Real.pi) (hirr : IrrPi a) (m n : ℤ)
    (h : (m : ℝ) * a + (n : ℝ) * b = 0) : m = 0 ∧ n = 0 := by
  have hpi := Real.pi_pos
  have h2 : ((m : ℝ) - 2 * n) * a + (n : ℝ) * Real.pi = 0 := by
    have : b = Real.pi - 2 * a := by linarith
    rw [this] at h; linarith
  by_cases hm : (m : ℝ) - 2 * n = 0
  · rw [hm] at h2
    have hn : (n : ℝ) = 0 := by
      rcases mul_eq_zero.mp (by linarith : (n : ℝ) * Real.pi = 0) with h | h
      · exact h
      · exact absurd h hpi.ne'
    have hn' : n = 0 := by exact_mod_cast hn
    refine ⟨?_, hn'⟩
    have : (m : ℝ) = 0 := by rw [hn] at hm; linarith
    exact_mod_cast this
  · exfalso
    apply hirr
    refine ⟨(-(n : ℚ)) / ((m : ℚ) - 2 * n), ?_⟩
    push_cast
    have hm' : ((m : ℝ) - 2 * n) ≠ 0 := hm
    rw [div_mul_eq_mul_div, eq_div_iff hm']
    linarith
theorem swap_match (f g : Fin 3 → ℝ) (a b : ℝ) (i j : Fin 3)
    (hf : f i = b ∧ ∀ k, k ≠ i → f k = a) (hg : g j = b ∧ ∀ k, k ≠ j → g k = a) :
    ∀ k, f k = g (Equiv.swap i j k) := by
  intro k
  by_cases hki : k = i
  · subst hki; rw [Equiv.swap_apply_left, hf.1, hg.1]
  · by_cases hkj : k = j
    · subst hkj
      rw [Equiv.swap_apply_right, hf.2 _ hki]
      have : k ≠ i := hki
      exact (hg.2 i (fun h => hki h.symm)).symm
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, hf.2 _ hki, hg.2 _ hkj]
theorem iso_similar {N : ℕ} (D : CongruentDissection N) (p q r : Fin 3)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (heq : D.model.angleAt p = D.model.angleAt q)
    (hirr : ∃ i, IrrPi (D.model.angleAt i)) : SimilarTM D := by
  have hpi := Real.pi_pos
  have key : ∀ p q r k : Fin 3, p ≠ q → p ≠ r → q ≠ r → k = p ∨ k = q ∨ k = r := by decide
  have hall : ∀ k, k = p ∨ k = q ∨ k = r := fun k => key p q r k hpq hpr hqr
  have huniv : (Finset.univ : Finset (Fin 3)) = {p, q, r} := by
    ext k; simp [hall k]
  have hsumA : D.model.angleAt 0 + D.model.angleAt 1 + D.model.angleAt 2 = Real.pi :=
    Erdos634.Geometry.cornerAngle_sum D.model
  have hpqr : D.model.angleAt p + D.model.angleAt q + D.model.angleAt r = Real.pi := by
    have h := Fin.sum_univ_three (fun k => D.model.angleAt k)
    rw [huniv, Finset.sum_insert (by simp [hpq, hpr]), Finset.sum_insert (by simp [hqr]),
      Finset.sum_singleton] at h
    linarith
  set a := D.model.angleAt p with ha
  set b := D.model.angleAt r with hb
  have h2ab : 2 * a + b = Real.pi := by rw [← heq] at hpqr; linarith
  have hirra : IrrPi a := by
    obtain ⟨i, hi⟩ := hirr
    rcases hall i with rfl | rfl | rfl
    · exact hi
    · rw [← heq] at hi; exact hi
    · rintro ⟨s, hs⟩
      apply hi
      refine ⟨1 - 2 * s, ?_⟩
      push_cast
      have : b = Real.pi - 2 * a := by linarith
      rw [show D.model.angleAt i = b from rfl, this, hs]; ring
  have hposA : ∀ k, 0 < D.model.angleAt k := fun k => Erdos634.MarchFlank.cornerAngle_pos D.model k
  have hltA : ∀ k, D.model.angleAt k < Real.pi := fun k => Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.model k
  have ha0 := hposA p
  have hb0 := hposA r
  have haπ := hltA p
  have hbπ := hltA r
  have hab : a ≠ b := by
    intro h
    apply hirra
    refine ⟨1 / 3, ?_⟩
    push_cast
    linarith
  have hmod : ∀ k : Fin 3, cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) = a
      ∨ cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) = b := by
    intro k
    rcases hall k with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl heq.symm
    · exact Or.inr rfl
  have hcor := fun k => corner_fig2 D a b hmod hab ha0 hb0 haπ hbπ k
  have e0 := (hcor 0).2
  have e1 := (hcor 1).2
  have e2 := (hcor 2).2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at e0 e1 e2
  have hT := Erdos634.Geometry.cornerAngle_sum D.target
  set A : Fin 3 → ℕ := fun k => ({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card
    with hA
  set B : Fin 3 → ℕ := fun k => ({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card
    with hB
  have hreal : ((A 0 + A 1 + A 2 : ℕ) : ℝ) * a + ((B 0 + B 1 + B 2 : ℕ) : ℝ) * b = Real.pi := by
    push_cast
    have := e0.1; have := e1.1; have := e2.1
    simp only [hA, hB]
    linarith [e0.1, e1.1, e2.1]
  have hz := iso_arith a b h2ab hirra ((A 0 + A 1 + A 2 : ℕ) - 2 : ℤ) ((B 0 + B 1 + B 2 : ℕ) - 1 : ℤ)
    (by push_cast; nlinarith [hreal])
  have hA2 : A 0 + A 1 + A 2 = 2 := by have := hz.1; omega
  have hB1 : B 0 + B 1 + B 2 = 1 := by have := hz.2; omega
  have hp0 : 1 ≤ A 0 + B 0 := e0.2
  have hp1 : 1 ≤ A 1 + B 1 := e1.2
  have hp2 : 1 ≤ A 2 + B 2 := e2.2
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have hpick : ∃ i, B i = 1 ∧ ∀ k, k ≠ i → B k = 0 := by
    have : (B 0 = 1 ∧ B 1 = 0 ∧ B 2 = 0) ∨ (B 0 = 0 ∧ B 1 = 1 ∧ B 2 = 0)
        ∨ (B 0 = 0 ∧ B 1 = 0 ∧ B 2 = 1) := by omega
    rcases this with h | h | h
    · refine ⟨0, h.1, fun k hk => ?_⟩
      rcases fin3 k with rfl | rfl | rfl
      · exact absurd rfl hk
      · exact h.2.1
      · exact h.2.2
    · refine ⟨1, h.2.1, fun k hk => ?_⟩
      rcases fin3 k with rfl | rfl | rfl
      · exact h.1
      · exact absurd rfl hk
      · exact h.2.2
    · refine ⟨2, h.2.2, fun k hk => ?_⟩
      rcases fin3 k with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact absurd rfl hk
  obtain ⟨i, hi1, hi0⟩ := hpick
  have hAk : ∀ k, A k + B k = 1 := by
    intro k; rcases fin3 k with rfl | rfl | rfl <;> omega
  have hθ : ∀ k, (A k : ℝ) * a + (B k : ℝ) * b = D.target.angleAt k := by
    intro k; rcases fin3 k with rfl | rfl | rfl
    · exact e0.1
    · exact e1.1
    · exact e2.1
  have hf : D.target.angleAt i = b ∧ ∀ k, k ≠ i → D.target.angleAt k = a := by
    refine ⟨?_, fun k hk => ?_⟩
    · rw [← hθ i]; have := hAk i; have : A i = 0 := by omega
      rw [this, hi1]; simp
    · rw [← hθ k]; have := hAk k; have h0 := hi0 k hk
      have : A k = 1 := by omega
      rw [this, h0]; simp
  have hg : D.model.angleAt r = b ∧ ∀ k, k ≠ r → D.model.angleAt k = a := by
    refine ⟨rfl, fun k hk => ?_⟩
    rcases hall k with rfl | rfl | rfl
    · rfl
    · exact heq.symm
    · exact absurd rfl hk
  have hτ := swap_match (fun k => D.target.angleAt k) (fun k => D.model.angleAt k) a b i r hf hg
  obtain ⟨μ, hμ⟩ := Erdos634.Draft.LemmaCSimilar.sides_of_angles D.target D.model (Equiv.swap i r) hτ
  exact ⟨μ, Equiv.swap i r, fun k => ⟨hτ k, hμ k⟩⟩
end Erdos634.Draft.LemmaCIso
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCAssemble Erdos634.Draft.LemmaCShapes
namespace Erdos634.Draft.LemmaCFinal
theorem key3 : ∀ p q r k : Fin 3, p ≠ q → p ≠ r → q ≠ r → k = p ∨ k = q ∨ k = r := by decide
theorem sum3 {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : f i + f j + f l = f 0 + f 1 + f 2 := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {i, j, l} := by
    ext k; simp [key3 i j l k hij hil hjl]
  have h := Fin.sum_univ_three f
  rw [huniv, Finset.sum_insert (by simp [hij, hil]), Finset.sum_insert (by simp [hjl]),
    Finset.sum_singleton] at h
  rw [← h, add_assoc]
theorem irr_transfer (y w : ℝ) (a b : ℚ) (h : y = a * w + b * Real.pi) (hy : IrrPi y) :
    IrrPi w := by
  rintro ⟨q, hq⟩
  exact hy ⟨a * q + b, by rw [h, hq]; push_cast; ring⟩
noncomputable def permOf (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Equiv.Perm (Fin 3) :=
  Equiv.ofBijective ![a, b, c]
    ((by decide : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → Function.Bijective ![i, j, l])
      a b c hab hac hbc)
theorem permOf_0 (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    permOf a b c hab hac hbc 0 = a := rfl
theorem permOf_1 (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    permOf a b c hab hac hbc 1 = b := rfl
theorem permOf_2 (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    permOf a b c hab hac hbc 2 = c := rfl
theorem sim_of_TA {N : ℕ} (D : CongruentDissection N) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : TA (fun k => D.target.angleAt k) (D.model.angleAt a) (D.model.angleAt b)
      (D.model.angleAt c)) : SimilarTM D := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  let τ : Equiv.Perm (Fin 3) := σ.symm.trans (permOf a b c hab hac hbc)
  have hτ : ∀ k, D.target.angleAt k = D.model.angleAt (τ k) := by
    intro k
    obtain ⟨m, rfl⟩ := σ.surjective k
    have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
    rcases fin3 m with rfl | rfl | rfl
    · simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply, permOf_0]; exact h0
    · simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply, permOf_1]; exact h1
    · simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply, permOf_2]; exact h2
  obtain ⟨μ, hμ⟩ := Erdos634.Draft.LemmaCSimilar.sides_of_angles D.target D.model τ hτ
  exact ⟨μ, τ, fun k => ⟨hτ k, hμ k⟩⟩
theorem caseSixty {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m))
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i - D.model.angleAt j + 2 * D.model.angleAt l = 0) : SixtyTile D := by
  have hl : D.model.angleAt l = Real.pi / 3 := by linarith
  have hj : D.model.angleAt j = 2 * Real.pi / 3 - D.model.angleAt i := by linarith
  have hIrr : IrrPi (D.model.angleAt i) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact hm
    · exact irr_transfer _ _ (-1) (2 / 3) (by rw [hj]; push_cast; ring) hm
    · exact irr_transfer _ _ 0 (1 / 3) (by rw [hl]; push_cast; ring) hm
  refine ⟨D.model.angleAt i, D.model.oppLen i, D.model.oppLen j, D.model.oppLen l, hIrr,
    permOf i j l hij hil hjl, ?_, rfl, ?_, rfl, ?_, rfl⟩
  · rw [permOf_0]
  · rw [permOf_1, hj]
  · rw [permOf_2, hl]
theorem caseThreeTwo {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m)) (hns : ¬ SimilarTM D)
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i + D.model.angleAt j + 2 * D.model.angleAt l = 0)
    (P Q R : Fin 3 → ℕ)
    (hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 2) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) : ThreeTwoCase D := by
  have hu : D.model.angleAt i = 2 * D.model.angleAt l + D.model.angleAt j := by linarith
  have hr2 : 3 * D.model.angleAt l + 2 * D.model.angleAt j = Real.pi := by linarith
  have hj : D.model.angleAt j = Real.pi / 2 - 3 / 2 * D.model.angleAt l := by linarith
  have hIrr : IrrPi (D.model.angleAt l) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact irr_transfer _ _ (1 / 2) (1 / 2) (by rw [hu, hj]; push_cast; ring) hm
    · exact irr_transfer _ _ (-3 / 2) (1 / 2) (by rw [hj]; push_cast; ring) hm
    · exact hm
  have hdata : D.model.ThreeAlphaData (D.model.angleAt l) (D.model.angleAt j)
      (D.model.oppLen l) (D.model.oppLen j) (D.model.oppLen i) :=
    ⟨permOf l j i hjl.symm hil.symm hij.symm, by rw [permOf_0], rfl, by rw [permOf_1], rfl,
      by rw [permOf_2, hu], rfl⟩
  refine ⟨_, _, _, _, _, hIrr, hr2, hdata, ?_⟩
  rcases shapes_threeTwo (fun k => D.target.angleAt k) _ _ _ P Q R hu hr2 hθ hP hQ hR hpos with
    h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact absurd (sim_of_TA D l j i hjl.symm hil.symm hij.symm h) hns
theorem caseTwoAlpha {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m)) (hns : ¬ SimilarTM D)
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i + 0 * D.model.angleAt j + 2 * D.model.angleAt l = 0)
    (P Q R : Fin 3 → ℕ)
    (hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 1) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) : TwoAlphaCase D := by
  have hu : D.model.angleAt i = 2 * D.model.angleAt l := by linarith
  have hv : D.model.angleAt j = Real.pi - 3 * D.model.angleAt l := by linarith
  have hIrr : IrrPi (D.model.angleAt l) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact irr_transfer _ _ 2 0 (by rw [hu]; push_cast; ring) hm
    · exact irr_transfer _ _ (-3) 1 (by rw [hv]; push_cast; ring) hm
    · exact hm
  have hdata : D.model.TwoAlphaData (D.model.angleAt l) (D.model.oppLen l) (D.model.oppLen j)
      (D.model.oppLen i) :=
    ⟨permOf l j i hjl.symm hil.symm hij.symm, by rw [permOf_0], rfl, by rw [permOf_1, hv], rfl,
      by rw [permOf_2, hu], rfl⟩
  refine ⟨_, _, _, _, hIrr, hdata, ?_⟩
  rcases shapes_twoAlpha (fun k => D.target.angleAt k) _ _ _ P Q R hu hv hθ hP hQ hR hpos with h | h
  · obtain ⟨σ, h0, h1, -⟩ := h
    exact ⟨σ 0, σ 1, fun e => absurd (σ.injective e) (by decide), h0, h1⟩
  · exact absurd (sim_of_TA D l j i hjl.symm hil.symm hij.symm h) hns
theorem caseRight {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m)) (hns : ¬ SimilarTM D)
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = 0)
    (P Q R : Fin 3 → ℕ)
    (hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 2) (hR : R 0 + R 1 + R 2 = 2)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) : RightCase D := by
  have hu : D.model.angleAt i = Real.pi / 2 := by linarith
  have hw : D.model.angleAt l = Real.pi / 2 - D.model.angleAt j := by linarith
  have hlpos : 0 < D.model.angleAt l := Erdos634.MarchFlank.cornerAngle_pos D.model l
  have hjpos : 0 < D.model.angleAt j := Erdos634.MarchFlank.cornerAngle_pos D.model j
  have hIrr : IrrPi (D.model.angleAt j) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact absurd ⟨1 / 2, by rw [hu]; push_cast; ring⟩ hm
    · exact hm
    · exact irr_transfer _ _ (-1) (1 / 2) (by rw [hw]; push_cast; ring) hm
  have hirrat : Irrational (D.model.angleAt j / Real.pi) := by
    rintro ⟨q, hq⟩
    apply hIrr
    refine ⟨q, ?_⟩
    have := Real.pi_pos.ne'
    field_simp at hq ⊢
    linarith
  refine ⟨D.model.angleAt j, hjpos, by linarith, hirrat, ⟨j, i, hij.symm, rfl, hu⟩, ?_⟩
  rcases shapes_right (fun k => D.target.angleAt k) _ _ _ P Q R hu hw hθ hP hQ hR hpos with
    h | h | h
  · obtain ⟨σ, h0, h1, -⟩ := h
    exact ⟨D.model.angleAt j, Or.inl rfl, σ 0, σ 1,
      fun e => absurd (σ.injective e) (by decide), h0, h1⟩
  · obtain ⟨σ, -, h1, h2⟩ := h
    exact ⟨D.model.angleAt l, Or.inr hw, σ 1, σ 2,
      fun e => absurd (σ.injective e) (by decide), h1, h2⟩
  · exact absurd (sim_of_TA D i j l hij hil hjl h) hns
theorem caseTwoPiThree {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m)) (hns : ¬ SimilarTM D)
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i + 2 * D.model.angleAt j + 2 * D.model.angleAt l = 0)
    (P Q R : Fin 3 → ℕ)
    (hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 3) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) : TwoPiThreeCase D := by
  have hu : D.model.angleAt i = 2 * Real.pi / 3 := by linarith
  have hv : D.model.angleAt j = Real.pi / 3 - D.model.angleAt l := by linarith
  have hIrr : IrrPi (D.model.angleAt l) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact absurd ⟨2 / 3, by rw [hu]; push_cast; ring⟩ hm
    · exact irr_transfer _ _ (-1) (1 / 3) (by rw [hv]; push_cast; ring) hm
    · exact hm
  have hdata : D.model.TwoPiThreeData (D.model.angleAt l) (D.model.oppLen l) (D.model.oppLen j)
      (D.model.oppLen i) :=
    ⟨permOf l j i hjl.symm hil.symm hij.symm, by rw [permOf_0], rfl, by rw [permOf_1, hv], rfl,
      by rw [permOf_2, hu], rfl⟩
  have hθ' : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i
      + (Q k : ℝ) * (Real.pi / 3 - D.model.angleAt l) + (R k : ℝ) * D.model.angleAt l := by
    intro k; rw [hθ k, hv]
  refine ⟨_, _, _, _, hIrr, hdata, ?_⟩
  rcases shapes_twoPiThree (fun k => D.target.angleAt k) _ _ _ P Q R hu rfl hθ' hP hQ hR hpos with
    h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  · have h' : TA (fun k => D.target.angleAt k) (D.model.angleAt l) (D.model.angleAt j)
        (D.model.angleAt i) := by rw [hv]; exact h
    exact absurd (sim_of_TA D l j i hjl.symm hil.symm hij.symm h') hns
theorem lemmaC_general {N : ℕ} (D : CongruentDissection N)
    (hirr : ∃ k, IrrPi (D.model.angleAt k)) (hns : ¬ SimilarTM D) :
    RightCase D ∨ TwoAlphaCase D ∨ SixtyTile D ∨ TwoPiThreeCase D ∨ ThreeTwoCase D := by
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  by_cases iso : ∃ p q : Fin 3, p ≠ q ∧ D.model.angleAt p = D.model.angleAt q
  · obtain ⟨p, q, hpq, he⟩ := iso
    have h3 : ∀ p q : Fin 3, p ≠ q → ∃ r, p ≠ r ∧ q ≠ r := by decide
    obtain ⟨r, hpr, hqr⟩ := h3 p q hpq
    exact absurd (Erdos634.Draft.LemmaCIso.iso_similar D p q r hpq hpr hqr he hirr) hns
  push Not at iso
  set α := D.model.angleAt 0 with hα
  set β := D.model.angleAt 1 with hβ
  set γ := D.model.angleAt 2 with hγ
  have hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α := rfl
  have hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β := rfl
  have hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ := rfl
  have hαβ : α ≠ β := iso 0 1 (by decide)
  have hαγ : α ≠ γ := iso 0 2 (by decide)
  have hβγ : β ≠ γ := iso 1 2 (by decide)
  have hpos : ∀ m, 0 < D.model.angleAt m := fun m => Erdos634.MarchFlank.cornerAngle_pos D.model m
  have hlt : ∀ m, D.model.angleAt m < Real.pi := fun m =>
    Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.model m
  have hxm : ∀ m, (![α, β, γ] : Fin 3 → ℝ) m = D.model.angleAt m := by
    intro m; rcases fin3 m with rfl | rfl | rfl <;> rfl
  have hirr' : ∃ i, ¬ ∃ r : ℚ, (![α, β, γ] : Fin 3 → ℝ) i = (r : ℝ) * Real.pi := by
    obtain ⟨k, hk⟩ := hirr
    exact ⟨k, by rw [hxm]; exact hk⟩
  have hne := Erdos634.Draft.LemmaCSimilar.cfig_ne_of_notSimilar D α β γ hmα hmβ hmγ hαβ hαγ hβγ
    (hpos 0) (hpos 1) (hpos 2) (hlt 0) (hlt 1) (hlt 2) hns
  obtain ⟨d, hd1, hd2, hd3, hd4, hd5, hd6⟩ := lemmaC_geometric D α β γ hmα hmβ hmγ hαβ hαγ hβγ
    (hpos 0) (hpos 1) (hpos 2) (hlt 0) (hlt 1) (hlt 2) hirr' hne
  have hm : d 0 = -1 ∨ d 1 = -1 ∨ d 2 = -1 := by
    obtain ⟨j, hj⟩ := hd3; rcases fin3 j with rfl | rfl | rfl <;> simp_all
  have hp : 0 < d 0 ∨ 0 < d 1 ∨ 0 < d 2 := by
    obtain ⟨j, hj⟩ := hd4; rcases fin3 j with rfl | rfl | rfl <;> simp_all
  obtain ⟨i, j, l, hij, hjl, hil, hmem⟩ := Erdos634.Draft.LemmaCArith.enum_six (d 0) (d 1) (d 2)
    (hd2 0) (hd2 1) (hd2 2) hm hp hd5
  have hdi : ∀ m, (![d 0, d 1, d 2] : Fin 3 → ℤ) m = d m := by
    intro m; rcases fin3 m with rfl | rfl | rfl <;> rfl
  simp only [hdi, Erdos634.Draft.LemmaCArith.sixVectors, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hmem
  have hsumπ : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi := by
    rw [sum3 (fun m => D.model.angleAt m) i j l hij hil hjl]
    exact Erdos634.Geometry.cornerAngle_sum D.model
  have hrel : (d i : ℝ) * D.model.angleAt i + (d j : ℝ) * D.model.angleAt j
      + (d l : ℝ) * D.model.angleAt l = 0 := by
    rw [sum3 (fun m => (d m : ℝ) * D.model.angleAt m) i j l hij hil hjl]
    exact hd6
  have hcorner := fun kk => Erdos634.Draft.LemmaCFigures.corner_figure D α β γ hmα hmβ hmγ hαβ hαγ
    hβγ (hpos 0) (hpos 1) (hpos 2) (hlt 0) (hlt 1) (hlt 2) kk
  set P : Fin 3 → ℕ := fun k => cnt D (D.model.angleAt i) (D.target.pts k) with hP
  set Q : Fin 3 → ℕ := fun k => cnt D (D.model.angleAt j) (D.target.pts k) with hQ
  set R : Fin 3 → ℕ := fun k => cnt D (D.model.angleAt l) (D.target.pts k) with hR
  have hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l := by
    intro k
    have h := (hcorner k).2.1
    have h2 := sum3 (fun m => ((cnt D (D.model.angleAt m) (D.target.pts k) : ℕ) : ℝ) *
      D.model.angleAt m) i j l hij hil hjl
    try simp only [Fin.sum_univ_three] at h2
    have hk : D.target.angleAt k = cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) := rfl
    rw [hk, ← h]
    simp only [hP, hQ, hR]
    simp only [cnt] at h2 ⊢
    linarith [h2]
  have hposk : ∀ k, 1 ≤ P k + Q k + R k := by
    intro k
    have h : 1 ≤ cnt D (D.model.angleAt 0) (D.target.pts k)
        + cnt D (D.model.angleAt 1) (D.target.pts k) + cnt D (D.model.angleAt 2) (D.target.pts k) :=
      (hcorner k).2.2
    have h2 := sum3 (fun m => cnt D (D.model.angleAt m) (D.target.pts k)) i j l hij hil hjl
    simp only [hP, hQ, hR] at h2 ⊢
    omega
  have htot : ∀ m, cnt D (D.model.angleAt m) (D.target.pts 0) + cnt D (D.model.angleAt m) (D.target.pts 1)
      + cnt D (D.model.angleAt m) (D.target.pts 2) = cfig D ![α, β, γ] m := by
    intro m
    simp only [cfig, Fin.sum_univ_three, hxm]
  have hPt : ∀ e : ℤ, d i = e → P 0 + P 1 + P 2 = (1 + e).toNat := by
    intro e he; have := hd1 i; have := htot i; simp only [hP]; omega
  have hQt : ∀ e : ℤ, d j = e → Q 0 + Q 1 + Q 2 = (1 + e).toNat := by
    intro e he; have := hd1 j; have := htot j; simp only [hQ]; omega
  have hRt : ∀ e : ℤ, d l = e → R 0 + R 1 + R 2 = (1 + e).toNat := by
    intro e he; have := hd1 l; have := htot l; simp only [hR]; omega
  have hc : ∀ (a b c : ℤ), d i = a → d j = b → d l = c →
      (a : ℝ) * D.model.angleAt i + (b : ℝ) * D.model.angleAt j + (c : ℝ) * D.model.angleAt l = 0 := by
    intro a b c ha hb hc'
    have := hrel; rw [ha, hb, hc'] at this; exact this
  rcases hmem with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · exfalso
    have := hc _ _ _ e1 e2 e3
    push_cast at this
    exact iso i j hij (by linarith)
  · refine Or.inr (Or.inl (caseTwoAlpha D i j l hij hil hjl hirr hns hsumπ ?_ P Q R hθ ?_ ?_ ?_ hposk))
    · have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
    · rw [hPt _ e1]; rfl
    · rw [hQt _ e2]; rfl
    · rw [hRt _ e3]; rfl
  · refine Or.inl (caseRight D i j l hij hil hjl hirr hns hsumπ ?_ P Q R hθ ?_ ?_ ?_ hposk)
    · have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
    · rw [hPt _ e1]; rfl
    · rw [hQt _ e2]; rfl
    · rw [hRt _ e3]; rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (caseThreeTwo D i j l hij hil hjl hirr hns hsumπ ?_ P Q R hθ ?_ ?_ ?_ hposk))))
    · have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
    · rw [hPt _ e1]; rfl
    · rw [hQt _ e2]; rfl
    · rw [hRt _ e3]; rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inl (caseTwoPiThree D i j l hij hil hjl hirr hns hsumπ ?_ P Q R hθ ?_ ?_ ?_ hposk))))
    · have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
    · rw [hPt _ e1]; rfl
    · rw [hQt _ e2]; rfl
    · rw [hRt _ e3]; rfl
  · refine Or.inr (Or.inr (Or.inl (caseSixty D i j l hij hil hjl hirr hsumπ ?_)))
    have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
end Erdos634.Draft.LemmaCFinal
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCFinal
namespace Erdos634.Draft.LaczFormal
def TileAngles {N : ℕ} (D : CongruentDissection N) (x y z : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), D.model.angleAt (σ 0) = x ∧ D.model.angleAt (σ 1) = y ∧
    D.model.angleAt (σ 2) = z
theorem TileAngles.swap {N : ℕ} {D : CongruentDissection N} {x y z : ℝ}
    (h : TileAngles D x y z) : TileAngles D y x z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  refine ⟨(Equiv.swap (0 : Fin 3) 1).trans σ, ?_, ?_, ?_⟩
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]; exact h1
  · simp only [Equiv.trans_apply, Equiv.swap_apply_right]; exact h0
  · simp only [Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; exact h2
end Erdos634.Draft.LaczFormal
end

section
open scoped Classical
namespace Erdos634.Draft.LemmaPProof
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.VertexFigureReal Erdos634.RouteOneVertexKill
lemma irrPi_ne_pi_third {α : ℝ} (hα : IrrPi α) : α ≠ Real.pi / 3 := fun h =>
  hα ⟨1/3, by rw [h]; ring⟩
lemma irrPi_ne_two_thirds_minus {α : ℝ} (hα : IrrPi α) : α ≠ 2 * Real.pi / 3 - α := fun h =>
  hα ⟨1/3, by linarith⟩
lemma irrPi_ne_zero {α : ℝ} (hα : IrrPi α) : α ≠ 0 := fun h =>
  hα ⟨0, by rw [h]; ring⟩
lemma pi_third_ne_two_thirds_minus {α : ℝ} (hα : IrrPi α) : Real.pi / 3 ≠ 2 * Real.pi / 3 - α :=
  fun h => hα ⟨1/3, by linarith⟩
lemma pi_third_ne_zero : Real.pi / 3 ≠ 0 :=
  div_ne_zero Real.pi_ne_zero (by norm_num)
lemma two_thirds_minus_ne_zero {α : ℝ} (hα : IrrPi α) : 2 * Real.pi / 3 - α ≠ 0 := fun h =>
  hα ⟨2/3, by linarith⟩
lemma sixtyData_cornerAngle_mem {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hd : D.model.SixtyData α a b c) (i : Fin N) (j : Fin 3) :
    cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
      ∈ ({α, 2 * Real.pi / 3 - α, Real.pi / 3} : Finset ℝ) := by
  classical
  obtain ⟨σ, hσ0, -, hσ1, -, hσ2, -⟩ := hd
  obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
  rw [hk]; obtain ⟨m, rfl⟩ := σ.surjective k
  fin_cases m <;> simp only [Finset.mem_insert, Finset.mem_singleton]
  · exact Or.inl hσ0
  · exact Or.inr (Or.inl hσ1)
  · exact Or.inr (Or.inr hσ2)
lemma localAngle_at_vertex_mem {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hd : D.model.SixtyData α a b c) (k : Fin 3) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, 2 * Real.pi / 3 - α, Real.pi / 3, 0} : Finset ℝ) := by
  classical
  have hcas := corner_angle_sum D.toDissection k
  have hlt := cornerAngle_lt_pi D.target k
  have hnneg : ∀ m : Fin N, 0 ≤ (D.tile m).localAngle (D.target.pts k) :=
    fun m => (D.tile m).localAngle_nonneg _
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) (D.target.pts k) with
    ⟨j, _, hval⟩ | h2pi | hpi | h0
  · rw [hval]
    have hcm := sixtyData_cornerAngle_mem D hd i j
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcm ⊢; tauto
  · exfalso
    have hge2 : 2 * Real.pi ≤ ∑ i, (D.tile i).localAngle (D.target.pts k) :=
      h2pi.symm.le.trans (Finset.single_le_sum (fun m _ => hnneg m) (Finset.mem_univ i))
    linarith [hge2.trans_eq hcas, hlt, Real.pi_pos]
  · exfalso
    have hge1 : Real.pi ≤ ∑ i, (D.tile i).localAngle (D.target.pts k) :=
      hpi.symm.le.trans (Finset.single_le_sum (fun m _ => hnneg m) (Finset.mem_univ i))
    linarith [hge1.trans_eq hcas, hlt, Real.pi_pos]
  · simp [h0]
noncomputable def multOf {N : ℕ} (D : CongruentDissection N) (v : ℝ) (k : Fin 3) : ℕ :=
  ({i : Fin N | (D.tile i).localAngle (D.target.pts k) = v} : Finset (Fin N)).card
lemma per_vertex_eq {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hα : IrrPi α) (hd : D.model.SixtyData α a b c) (k : Fin 3) :
    D.target.angleAt k = (multOf D α k : ℝ) * α +
      (multOf D (2 * Real.pi / 3 - α) k : ℝ) * (2 * Real.pi / 3 - α) +
      (multOf D (Real.pi / 3) k : ℝ) * (Real.pi / 3) := by
  classical
  have hcas := corner_angle_sum D.toDissection k
  rw [show cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = D.target.angleAt k from rfl] at hcas
  have hmem : ∀ i, (D.tile i).localAngle (D.target.pts k) ∈
      ({α, 2 * Real.pi / 3 - α, Real.pi / 3, 0} : Finset ℝ) :=
    fun i => localAngle_at_vertex_mem D hd k i
  rw [sum_by_value _ _ hmem] at hcas
  rw [← hcas]
  have hα23 : α ∉ ({2 * Real.pi / 3 - α, Real.pi / 3, 0} : Finset ℝ) := by
    simp [irrPi_ne_two_thirds_minus hα, irrPi_ne_pi_third hα, irrPi_ne_zero hα]
  have h23_rest : 2 * Real.pi / 3 - α ∉ ({Real.pi / 3, 0} : Finset ℝ) := by
    intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h1 | h2
    · exact pi_third_ne_two_thirds_minus hα h1.symm
    · exact two_thirds_minus_ne_zero hα h2
  have h13_0 : Real.pi / 3 ∉ ({0} : Finset ℝ) := by simp [pi_third_ne_zero]
  simp only [show ({α, 2 * Real.pi / 3 - α, Real.pi / 3, 0} : Finset ℝ) =
      insert α (insert (2 * Real.pi / 3 - α) (insert (Real.pi / 3) {0})) from rfl,
    Finset.sum_insert hα23, Finset.sum_insert h23_rest, Finset.sum_insert h13_0,
    Finset.sum_singleton, mul_zero, add_zero, multOf]
  ring
lemma target_angle_sum {N : ℕ} (D : CongruentDissection N) :
    D.target.angleAt 0 + D.target.angleAt 1 + D.target.angleAt 2 = Real.pi := by
  show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) +
       cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) +
       cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = Real.pi
  exact Erdos634.Geometry.cornerAngle_sum D.target
theorem lemmaP_general {N : ℕ} (D : CongruentDissection N) (α a b c : ℝ) (hα : IrrPi α)
    (hd : D.model.SixtyData α a b c) (hB : ¬ SimilarTM D) : Equilateral D := by
  unfold Equilateral; intro k; classical
  have hpv0 := per_vertex_eq D hα hd 0
  have hpv1 := per_vertex_eq D hα hd 1
  have hpv2 := per_vertex_eq D hα hd 2
  have hpi := target_angle_sum D
  let SA : ℤ := (multOf D α 0 : ℤ) + multOf D α 1 + multOf D α 2
  let S23 : ℤ := (multOf D (2 * Real.pi / 3 - α) 0 : ℤ) +
    multOf D (2 * Real.pi / 3 - α) 1 + multOf D (2 * Real.pi / 3 - α) 2
  let S13 : ℤ := (multOf D (Real.pi / 3) 0 : ℤ) +
    multOf D (Real.pi / 3) 1 + multOf D (Real.pi / 3) 2
  have hglobal : (SA : ℝ) * α + (S23 : ℝ) * (2 * Real.pi / 3 - α) +
      (S13 : ℝ) * (Real.pi / 3) = Real.pi := by
    simp only [SA, S23, S13]; push_cast; linarith
  obtain ⟨hA, hB'⟩ := Erdos634.Geometry.angle_indep hα
    (3 * (SA - S23)) (2 * S23 + S13 - 3)
    (by simp only [SA, S23, S13]; push_cast; linarith)
  have heqA : SA = S23 := by omega
  have hsum3 : 2 * S23 + S13 = 3 := by omega
  have hs23_nn : 0 ≤ S23 := by
    simp only [S23]; positivity
  have hs23_le1 : S23 ≤ 1 := by omega
  have hS23_cases : S23 = 0 ∨ S23 = 1 := by omega
  rcases hS23_cases with hs0 | hs1
  · 
    have hSA0 : SA = 0 := by omega
    have hS130 : S13 = 3 := by omega
    have hSA_exp : (multOf D α 0 : ℤ) + multOf D α 1 + multOf D α 2 = 0 := by
      have h : SA = 0 := hSA0; simp only [SA] at h; exact h
    have hS23_exp : (multOf D (2 * Real.pi / 3 - α) 0 : ℤ) +
        multOf D (2 * Real.pi / 3 - α) 1 + multOf D (2 * Real.pi / 3 - α) 2 = 0 := by
      have h : S23 = 0 := hs0; simp only [S23] at h; exact h
    have hmα : ∀ j : Fin 3, multOf D α j = 0 := by
      have hsum : multOf D α 0 + multOf D α 1 + multOf D α 2 = 0 := by exact_mod_cast hSA_exp
      have e0 : multOf D α 0 = 0 := by omega
      have e1 : multOf D α 1 = 0 := by omega
      have e2 : multOf D α 2 = 0 := by omega
      intro j; fin_cases j; exact e0; exact e1; exact e2
    have hm23 : ∀ j : Fin 3, multOf D (2 * Real.pi / 3 - α) j = 0 := by
      have hsum : multOf D (2 * Real.pi / 3 - α) 0 + multOf D (2 * Real.pi / 3 - α) 1 +
          multOf D (2 * Real.pi / 3 - α) 2 = 0 := by exact_mod_cast hS23_exp
      have e0 : multOf D (2 * Real.pi / 3 - α) 0 = 0 := by omega
      have e1 : multOf D (2 * Real.pi / 3 - α) 1 = 0 := by omega
      have e2 : multOf D (2 * Real.pi / 3 - α) 2 = 0 := by omega
      intro j; fin_cases j; exact e0; exact e1; exact e2
    have ha : ∀ j : Fin 3, D.target.angleAt j = (multOf D (Real.pi / 3) j : ℝ) * (Real.pi / 3) := by
      intro j
      have hpv := per_vertex_eq D hα hd j
      have hαj : multOf D α j = 0 := hmα j
      have h23j : multOf D (2 * Real.pi / 3 - α) j = 0 := hm23 j
      rw [hpv, hαj, h23j]; push_cast; ring
    have hn13_each : ∀ j : Fin 3, multOf D (Real.pi / 3) j = 1 := by
      have hpos : ∀ j : Fin 3, 1 ≤ multOf D (Real.pi / 3) j := by
        intro j; by_contra hlt; push_neg at hlt
        have hj0 : multOf D (Real.pi / 3) j = 0 := Nat.lt_one_iff.mp hlt
        have hay := ha j; rw [hj0] at hay; push_cast at hay
        linarith [Tri.angleAt_pos' D.target j]
      have htot' : multOf D (Real.pi / 3) 0 + multOf D (Real.pi / 3) 1 +
          multOf D (Real.pi / 3) 2 = 3 := by
        have h : S13 = 3 := hS130; simp only [S13] at h; exact_mod_cast h
      have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
      have e0 : multOf D (Real.pi / 3) 0 = 1 := by omega
      have e1 : multOf D (Real.pi / 3) 1 = 1 := by omega
      have e2 : multOf D (Real.pi / 3) 2 = 1 := by omega
      intro j; fin_cases j
      · exact e0
      · exact e1
      · exact e2
    have hk := ha k; rw [hn13_each k] at hk; push_cast at hk; linarith
  · 
    exfalso; apply hB
    have hSA1 : SA = 1 := heqA.trans hs1
    have hS131 : S13 = 1 := by omega
    have hα_n : multOf D α 0 + multOf D α 1 + multOf D α 2 = 1 := by
      have h : SA = 1 := hSA1; simp only [SA] at h; exact_mod_cast h
    have h23_n : multOf D (2*Real.pi/3-α) 0 + multOf D (2*Real.pi/3-α) 1 +
        multOf D (2*Real.pi/3-α) 2 = 1 := by
      have h : S23 = 1 := hs1; simp only [S23] at h; exact_mod_cast h
    have h13_n : multOf D (Real.pi/3) 0 + multOf D (Real.pi/3) 1 +
        multOf D (Real.pi/3) 2 = 1 := by
      have h : S13 = 1 := hS131; simp only [S13] at h; exact_mod_cast h
    have hT_pos : ∀ j : Fin 3, 0 < multOf D α j + multOf D (2*Real.pi/3-α) j + multOf D (Real.pi/3) j := by
      intro j; by_contra hc; push_neg at hc
      have h0 : multOf D α j = 0 := by omega
      have h1 : multOf D (2*Real.pi/3-α) j = 0 := by omega
      have h2 : multOf D (Real.pi/3) j = 0 := by omega
      have := per_vertex_eq D hα hd j; rw [h0, h1, h2] at this; push_cast at this
      linarith [Tri.angleAt_pos' D.target j]
    have hTe0 : multOf D α 0 + multOf D (2*Real.pi/3-α) 0 + multOf D (Real.pi/3) 0 = 1 := by
      have p0 := hT_pos 0; have p1 := hT_pos 1; have p2 := hT_pos 2; omega
    have hTe1 : multOf D α 1 + multOf D (2*Real.pi/3-α) 1 + multOf D (Real.pi/3) 1 = 1 := by
      have p0 := hT_pos 0; have p1 := hT_pos 1; have p2 := hT_pos 2; omega
    have hTe2 : multOf D α 2 + multOf D (2*Real.pi/3-α) 2 + multOf D (Real.pi/3) 2 = 1 := by
      have p0 := hT_pos 0; have p1 := hT_pos 1; have p2 := hT_pos 2; omega
    have hpv_val : ∀ j : Fin 3,
        (multOf D α j = 1 → D.target.angleAt j = α) ∧
        (multOf D (2*Real.pi/3-α) j = 1 → D.target.angleAt j = 2*Real.pi/3-α) ∧
        (multOf D (Real.pi/3) j = 1 → D.target.angleAt j = Real.pi/3) := by
      intro j
      have hTj : multOf D α j + multOf D (2*Real.pi/3-α) j + multOf D (Real.pi/3) j = 1 := by
        fin_cases j; exact hTe0; exact hTe1; exact hTe2
      have hpv := per_vertex_eq D hα hd j
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have h1 : multOf D (2*Real.pi/3-α) j = 0 := by omega
        have h2 : multOf D (Real.pi/3) j = 0 := by omega
        rw [hpv, h, h1, h2]; push_cast; ring
      · have h0 : multOf D α j = 0 := by omega
        have h2 : multOf D (Real.pi/3) j = 0 := by omega
        rw [hpv, h0, h, h2]; push_cast; ring
      · have h0 : multOf D α j = 0 := by omega
        have h1 : multOf D (2*Real.pi/3-α) j = 0 := by omega
        rw [hpv, h0, h1, h]; push_cast; ring
    obtain ⟨σ, hσα, hσα_len, hσ23, hσ23_len, hσ13, hσ13_len⟩ := hd
    have oppLen_ratio : ∀ (τ : Equiv.Perm (Fin 3)) (k : Fin 3),
        (∀ j : Fin 3, D.target.angleAt j = D.model.angleAt (τ j)) →
        D.target.oppLen k * D.model.oppLen (τ 0) = D.target.oppLen 0 * D.model.oppLen (τ k) := by
      intro τ k hangle
      have hls_t : Real.sin (D.model.angleAt (τ 0)) * D.target.oppLen k =
          Real.sin (D.model.angleAt (τ k)) * D.target.oppLen 0 := by
        have := Tri.lawSin D.target 0 k; rw [hangle 0, hangle k] at this; exact this
      have hls_m : Real.sin (D.model.angleAt (τ 0)) * D.model.oppLen (τ k) =
          Real.sin (D.model.angleAt (τ k)) * D.model.oppLen (τ 0) :=
        Tri.lawSin D.model (τ 0) (τ k)
      have hsin0 : 0 < Real.sin (D.model.angleAt (τ 0)) :=
        Real.sin_pos_of_pos_of_lt_pi (Tri.angleAt_pos' D.model (τ 0)) (cornerAngle_lt_pi D.model (τ 0))
      have step : Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen k * D.model.oppLen (τ 0)) =
          Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen 0 * D.model.oppLen (τ k)) :=
        calc Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen k * D.model.oppLen (τ 0))
            = Real.sin (D.model.angleAt (τ 0)) * D.target.oppLen k * D.model.oppLen (τ 0) := by ring
          _ = Real.sin (D.model.angleAt (τ k)) * D.target.oppLen 0 * D.model.oppLen (τ 0) := by rw [hls_t]
          _ = D.target.oppLen 0 * (Real.sin (D.model.angleAt (τ k)) * D.model.oppLen (τ 0)) := by ring
          _ = D.target.oppLen 0 * (Real.sin (D.model.angleAt (τ 0)) * D.model.oppLen (τ k)) := by rw [hls_m]
          _ = Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen 0 * D.model.oppLen (τ k)) := by ring
      exact mul_left_cancel₀ (ne_of_gt hsin0) step
    have hα_case : (multOf D α 0 = 1 ∧ multOf D α 1 = 0 ∧ multOf D α 2 = 0) ∨
        (multOf D α 0 = 0 ∧ multOf D α 1 = 1 ∧ multOf D α 2 = 0) ∨
        (multOf D α 0 = 0 ∧ multOf D α 1 = 0 ∧ multOf D α 2 = 1) := by omega
    have build_similar : ∀ (τ : Equiv.Perm (Fin 3)),
        (∀ j : Fin 3, D.target.angleAt j = D.model.angleAt (τ j)) → SimilarTM D := by
      intro τ hangle
      exact ⟨D.target.oppLen 0 / D.model.oppLen (τ 0), τ, fun k => ⟨hangle k, by
        rcases Nat.eq_zero_or_pos k.val with hk | hk
        · have : k = 0 := by ext; exact hk
          subst this; simp [div_mul_cancel₀, ne_of_gt (Tri.oppLen_pos D.model (τ 0))]
        · have hrat := oppLen_ratio τ k hangle
          have hpos := Tri.oppLen_pos D.model (τ 0)
          field_simp [ne_of_gt hpos]; linarith [hrat]⟩⟩
    rcases hα_case with ⟨hα0, hα10, hα20⟩ | ⟨hα00, hα1, hα20⟩ | ⟨hα00, hα10, hα2⟩
    · 
      have h23_02 : multOf D (2*Real.pi/3-α) 0 = 0 := by have := hTe0; omega
      have h13_02 : multOf D (Real.pi/3) 0 = 0 := by have := hTe0; omega
      have h23_case : (multOf D (2*Real.pi/3-α) 1 = 1 ∧ multOf D (2*Real.pi/3-α) 2 = 0) ∨
          (multOf D (2*Real.pi/3-α) 1 = 0 ∧ multOf D (2*Real.pi/3-α) 2 = 1) := by omega
      rcases h23_case with ⟨h231, h232⟩ | ⟨h231, h232⟩
      · 
        have h13_2 : multOf D (Real.pi/3) 2 = 1 := by have := hTe2; omega
        have hta0 := (hpv_val 0).1 hα0
        have hta1 := (hpv_val 1).2.1 h231
        have hta2 := (hpv_val 2).2.2 h13_2
        exact build_similar σ (fun k => by
          fin_cases k
          · simp [hta0, hσα]
          · simp [hta1, hσ23]
          · simp [hta2, hσ13])
      · 
        have h13_1 : multOf D (Real.pi/3) 1 = 1 := by have := hTe1; omega
        have hta0 := (hpv_val 0).1 hα0
        have hta1 := (hpv_val 1).2.2 h13_1
        have hta2 := (hpv_val 2).2.1 h232
        exact build_similar ((Equiv.swap (1:Fin 3) 2).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 0); rw [hta0, hσα]
          · change D.target.angleAt 1 = D.model.angleAt (σ 2); rw [hta1, hσ13]
          · change D.target.angleAt 2 = D.model.angleAt (σ 1); rw [hta2, hσ23])
    · 
      have h23_12 : multOf D (2*Real.pi/3-α) 1 = 0 := by have := hTe1; omega
      have h13_12 : multOf D (Real.pi/3) 1 = 0 := by have := hTe1; omega
      have h23_case : (multOf D (2*Real.pi/3-α) 0 = 1 ∧ multOf D (2*Real.pi/3-α) 2 = 0) ∨
          (multOf D (2*Real.pi/3-α) 0 = 0 ∧ multOf D (2*Real.pi/3-α) 2 = 1) := by omega
      rcases h23_case with ⟨h230, h232⟩ | ⟨h230, h232⟩
      · 
        have h13_2 : multOf D (Real.pi/3) 2 = 1 := by have := hTe2; omega
        have hta0 := (hpv_val 0).2.1 h230
        have hta1 := (hpv_val 1).1 hα1
        have hta2 := (hpv_val 2).2.2 h13_2
        exact build_similar ((Equiv.swap (0:Fin 3) 1).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 1); rw [hta0, hσ23]
          · change D.target.angleAt 1 = D.model.angleAt (σ 0); rw [hta1, hσα]
          · change D.target.angleAt 2 = D.model.angleAt (σ 2); rw [hta2, hσ13])
      · 
        have h13_0 : multOf D (Real.pi/3) 0 = 1 := by have := hTe0; omega
        have hta0 := (hpv_val 0).2.2 h13_0
        have hta1 := (hpv_val 1).1 hα1
        have hta2 := (hpv_val 2).2.1 h232
        exact build_similar (((Equiv.swap (0:Fin 3) 2).trans (Equiv.swap 0 1)).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 2); rw [hta0, hσ13]
          · change D.target.angleAt 1 = D.model.angleAt (σ 0); rw [hta1, hσα]
          · change D.target.angleAt 2 = D.model.angleAt (σ 1); rw [hta2, hσ23])
    · 
      have h23_22 : multOf D (2*Real.pi/3-α) 2 = 0 := by have := hTe2; omega
      have h13_22 : multOf D (Real.pi/3) 2 = 0 := by have := hTe2; omega
      have h23_case : (multOf D (2*Real.pi/3-α) 0 = 1 ∧ multOf D (2*Real.pi/3-α) 1 = 0) ∨
          (multOf D (2*Real.pi/3-α) 0 = 0 ∧ multOf D (2*Real.pi/3-α) 1 = 1) := by omega
      rcases h23_case with ⟨h230, h231⟩ | ⟨h230, h231⟩
      · 
        have h13_1 : multOf D (Real.pi/3) 1 = 1 := by have := hTe1; omega
        have hta0 := (hpv_val 0).2.1 h230
        have hta1 := (hpv_val 1).2.2 h13_1
        have hta2 := (hpv_val 2).1 hα2
        exact build_similar (((Equiv.swap (0:Fin 3) 1).trans (Equiv.swap 0 2)).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 1); rw [hta0, hσ23]
          · change D.target.angleAt 1 = D.model.angleAt (σ 2); rw [hta1, hσ13]
          · change D.target.angleAt 2 = D.model.angleAt (σ 0); rw [hta2, hσα])
      · 
        have h13_0 : multOf D (Real.pi/3) 0 = 1 := by have := hTe0; omega
        have hta0 := (hpv_val 0).2.2 h13_0
        have hta1 := (hpv_val 1).2.1 h231
        have hta2 := (hpv_val 2).1 hα2
        exact build_similar ((Equiv.swap (0:Fin 3) 2).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 2); rw [hta0, hσ13]
          · change D.target.angleAt 1 = D.model.angleAt (σ 1); rw [hta1, hσ23]
          · change D.target.angleAt 2 = D.model.angleAt (σ 0); rw [hta2, hσα])
end Erdos634.Draft.LemmaPProof
end

section
open scoped Classical
namespace Erdos634.Draft.ThmIso
open Erdos634.Geometry Erdos634.AreaDet
private lemma twoPiThree_c_sq {α a b c : ℝ} (T : Tri) (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hlc := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hlc
  linarith
theorem model_four_det_sq {α a b c : ℝ} (T : Tri) (h : T.TwoPiThreeData α a b c) :
    4 * Erdos634.AreaDet.detTri T ^ 2 = 3 * a ^ 2 * b ^ 2 := by
  have hc2 := twoPiThree_c_sq T h
  obtain ⟨σ, -, ha, -, hb, -, hc⟩ := h
  have hM := T.four_detTri_sq_sym
  rw [T.sum_perm 2 σ, T.sum_perm 4 σ, ha, hb, hc] at hM
  linear_combination hM + (a ^ 2 - a * b + b ^ 2 - c ^ 2) * hc2
theorem target_four_det_sq {α a b c μ : ℝ} (T : Tri) (h : T.BaseAlphaData α a b c μ)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    4 * Erdos634.AreaDet.detTri T ^ 2 = 3 * μ ^ 4 * a ^ 2 * (a + 2 * b) ^ 2 := by
  obtain ⟨-, hgrid⟩ := h
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := hgrid
  have hM := T.four_detTri_sq_sym
  rw [T.sum_perm 2 σ, T.sum_perm 4 σ, o0, o1, o2] at hM
  linear_combination hM + 4 * μ ^ 4 * (a + 2 * b) ^ 2 * hc2
theorem base_alpha_area_identity {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.BaseAlphaData α a b c μ)
    (ha : 0 < a) (hb : 0 < b) (hμ : 0 < μ) :
    (N : ℝ) * b = μ ^ 2 * (a + 2 * b) := by
  have hc2 := twoPiThree_c_sq D.model hm
  have hdet := D.abs_detTri_target
  have hdet_sq : Erdos634.AreaDet.detTri D.target ^ 2
      = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hdet
    simp only [mul_pow, sq_abs] at h
    exact h
  have hmod_det := model_four_det_sq D.model hm
  have htgt_det := target_four_det_sq D.target ht hc2
  have key : 3 * μ ^ 4 * a ^ 2 * (a + 2 * b) ^ 2 = 3 * (N : ℝ) ^ 2 * a ^ 2 * b ^ 2 := by
    linear_combination -htgt_det + (N : ℝ) ^ 2 * hmod_det + 4 * hdet_sq
  have hμ4_eq : μ ^ 4 * (a + 2 * b) ^ 2 = (N : ℝ) ^ 2 * b ^ 2 :=
    mul_left_cancel₀ (by positivity : (3 : ℝ) * a ^ 2 ≠ 0) (by linear_combination key)
  have h_sq_eq : (μ ^ 2 * (a + 2 * b)) ^ 2 = ((N : ℝ) * b) ^ 2 := by
    have : (μ ^ 2 * (a + 2 * b)) ^ 2 = μ ^ 4 * (a + 2 * b) ^ 2 := by ring
    rw [this, hμ4_eq]; ring
  have hLpos : (0 : ℝ) ≤ μ ^ 2 * (a + 2 * b) := by positivity
  have hRpos : (0 : ℝ) ≤ (N : ℝ) * b := mul_nonneg (Nat.cast_nonneg N) hb.le
  exact ((pow_left_inj₀ hLpos hRpos two_ne_zero).mp h_sq_eq).symm
end Erdos634.Draft.ThmIso
end

section
open scoped Classical
namespace Erdos634.Geometry
open Erdos634.Draft.TheoremPConditional
open A1Field (sin_angle_pos)
theorem cos_alpha_of_TwoPiThree (T : Tri) {α a b c : ℝ}
    (h : T.TwoPiThreeData α a b c) :
    Real.cos α = (a + 2 * b) / (2 * c) ∧ 0 < c ∧ 0 < a ∧ 0 < b := by
  obtain ⟨σ, hα0, ha, hα1, hb, hγ, hc⟩ := h
  have ha0 : 0 < a := ha ▸ T.oppLen_pos (σ 0)
  have hb0 : 0 < b := hb ▸ T.oppLen_pos (σ 1)
  have hc0 : 0 < c := hc ▸ T.oppLen_pos (σ 2)
  have hlc : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
    have hl := T.lawCos_perm σ
    rw [ha, hb, hc, hγ,
        show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three] at hl
    linarith
  have hsum1 : T.oppLen (σ 0 + 1) + T.oppLen (σ 0 + 2) = b + c := by
    have s1 := T.sum_rot 1 (σ 0)
    have s2 := T.sum_perm 1 σ
    simp only [pow_one] at s1 s2
    rw [ha, hb, hc] at s2
    rw [ha] at s1
    linarith
  have hsum2 : T.oppLen (σ 0 + 1) ^ 2 + T.oppLen (σ 0 + 2) ^ 2 = b ^ 2 + c ^ 2 := by
    have s1 := T.sum_rot 2 (σ 0)
    have s2 := T.sum_perm 2 σ
    rw [ha, hb, hc] at s2
    rw [ha] at s1
    linarith
  have hprod : T.oppLen (σ 0 + 1) * T.oppLen (σ 0 + 2) = b * c := by
    nlinarith [sq_nonneg (T.oppLen (σ 0 + 1) - T.oppLen (σ 0 + 2)),
               T.oppLen_pos (σ 0 + 1), T.oppLen_pos (σ 0 + 2)]
  have hla : a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * Real.cos α := by
    have hl := T.lawCos (σ 0)
    rw [ha, hα0] at hl
    linear_combination hl + hsum2 - 2 * Real.cos α * hprod
  have h_rhs : b ^ 2 + c ^ 2 - a ^ 2 = b * (a + 2 * b) := by linear_combination hlc
  have h1 : 2 * b * c * Real.cos α = b * (a + 2 * b) := by linarith [hla, h_rhs]
  refine ⟨?_, hc0, ha0, hb0⟩
  rw [eq_div_iff (by positivity : (2 : ℝ) * c ≠ 0)]
  exact mul_left_cancel₀ hb0.ne'
    (show b * (Real.cos α * (2 * c)) = b * (a + 2 * b) by linear_combination h1)
theorem base_alpha_of_isoTP {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : TgtAngles D α α (α + 3 * (Real.pi / 3 - α))) :
    ∃ μ > 0, D.target.BaseAlphaData α a b c μ := by
  obtain ⟨cos_eq, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨σ, htα0, htα1, htα2⟩ := ht
  have hsin_α_pos : 0 < Real.sin α := by
    have := sin_angle_pos D.target (σ 0)
    rwa [htα0] at this
  have hls01 := D.target.lawSin (σ 0) (σ 1)
  rw [htα0, htα1] at hls01
  have hoppL01 : D.target.oppLen (σ 1) = D.target.oppLen (σ 0) :=
    mul_left_cancel₀ hsin_α_pos.ne' hls01
  have hangle2 : D.target.angleAt (σ 2) = Real.pi - 2 * α := by rw [htα2]; ring
  have hsin2 : Real.sin (D.target.angleAt (σ 2)) = 2 * Real.sin α * Real.cos α := by
    rw [hangle2, Real.sin_pi_sub, Real.sin_two_mul]
  have hls02 := D.target.lawSin (σ 0) (σ 2)
  rw [htα0, hsin2] at hls02
  have hoppL2 : D.target.oppLen (σ 2) = 2 * Real.cos α * D.target.oppLen (σ 0) :=
    mul_left_cancel₀ hsin_α_pos.ne' (by linear_combination hls02)
  have hoppL0_pos : 0 < D.target.oppLen (σ 0) := D.target.oppLen_pos (σ 0)
  have hμ_pos : 0 < D.target.oppLen (σ 0) / c := div_pos hoppL0_pos hc0
  have hside0 : D.target.oppLen (σ 0) = D.target.oppLen (σ 0) / c * c :=
    (div_mul_cancel₀ (D.target.oppLen (σ 0)) hc0.ne').symm
  have hside1 : D.target.oppLen (σ 1) = D.target.oppLen (σ 0) / c * c := by
    rw [hoppL01]; exact hside0
  have hside2 : D.target.oppLen (σ 2) = D.target.oppLen (σ 0) / c * (a + 2 * b) := by
    rw [hoppL2, cos_eq]
    field_simp [hc0.ne']
  refine ⟨D.target.oppLen (σ 0) / c, hμ_pos, ?_⟩
  constructor
  · exact hμ_pos
  · 
    exact ⟨σ,
      by rw [htα0]; push_cast; ring,
      hside0,
      by rw [htα1]; push_cast; ring,
      hside1,
      by rw [htα2]; push_cast; ring,
      hside2⟩
end Erdos634.Geometry
end

section
namespace Erdos634.Rationality
variable {R : Type*} [CommRing R]
theorem prod_eq (a b c P : R) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (P * (c - a - b)) * (P * (c + a + b)) = -(P ^ 2 * (a * b)) := by
  have h : (c - a - b) * (c + a + b) = c ^ 2 - (a + b) ^ 2 := by ring
  calc (P * (c - a - b)) * (P * (c + a + b))
      = P ^ 2 * ((c - a - b) * (c + a + b)) := by ring
    _ = P ^ 2 * (c ^ 2 - (a + b) ^ 2) := by rw [h]
    _ = -(P ^ 2 * (a * b)) := by rw [hc]; ring
theorem sum_eq (a b c P : R) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    P ^ 2 * (b * (a + 2 * b)) + (P * (c - a - b)) * (P * (c + a + b)) = 2 * (P ^ 2 * b ^ 2) := by
  rw [prod_eq a b c P hc]; ring
theorem ratio_ab (a b c P : R) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    a * (P ^ 2 * (b * (a + 2 * b)) + (P * (c - a - b)) * (P * (c + a + b)))
      = b * (-(2 : R) * ((P * (c - a - b)) * (P * (c + a + b)))) := by
  rw [sum_eq a b c P hc, prod_eq a b c P hc]; ring
theorem ratio_c (a b c P : R) :
    c * ((P * (c + a + b)) - (P * (c - a - b))) = (a + b) * ((P * (c - a - b)) + (P * (c + a + b))) := by
  ring
theorem tile_rational (a b c P : ℝ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hb : b ≠ 0) (hP : P ≠ 0) (hab : a + b ≠ 0)
    (nN nA nB : ℤ)
    (hN : (nN : ℝ) = P ^ 2 * (b * (a + 2 * b)))
    (hA : (nA : ℝ) = P * (c - a - b))
    (hB : (nB : ℝ) = P * (c + a + b)) :
    ∃ q r : ℚ, a = (q : ℝ) * b ∧ c = (r : ℝ) * b := by
  have hsum : P ^ 2 * (b * (a + 2 * b)) + (P * (c - a - b)) * (P * (c + a + b))
      = 2 * (P ^ 2 * b ^ 2) := sum_eq a b c P hc
  have hD1R : ((nN + nA * nB : ℤ) : ℝ) = 2 * (P ^ 2 * b ^ 2) := by
    push_cast [hN, hA, hB]; linarith [hsum]
  have hD1 : (nN + nA * nB : ℤ) ≠ 0 := by
    intro h
    rw [h] at hD1R
    have hpos : (0 : ℝ) < 2 * (P ^ 2 * b ^ 2) := by positivity
    push_cast at hD1R; linarith
  have hD2R : ((nB - nA : ℤ) : ℝ) = 2 * P * (a + b) := by push_cast [hA, hB]; ring
  have hD2 : (nB - nA : ℤ) ≠ 0 := by
    intro h
    rw [h] at hD2R
    push_cast at hD2R
    exact (mul_ne_zero (mul_ne_zero (two_ne_zero (α := ℝ)) hP) hab) hD2R.symm
  have hD1' : ((nN + nA * nB : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hD1
  have hD2' : ((nB - nA : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hD2
  set q : ℚ := (-2 * nA * nB : ℤ) / (nN + nA * nB : ℤ) with hq
  have hqR : (q : ℝ) = ((-2 * nA * nB : ℤ) : ℝ) / ((nN + nA * nB : ℤ) : ℝ) := by
    rw [hq]; push_cast; ring
  have ha : a = (q : ℝ) * b := by
    have hkey : a * ((nN : ℝ) + nA * nB) = b * (-2 * ((nA : ℝ) * nB)) := by
      rw [hN, hA, hB]; linear_combination ratio_ab a b c P hc
    rw [hqR]
    field_simp
    push_cast at hkey ⊢
    linarith [hkey]
  refine ⟨q, ((nA + nB : ℤ) : ℚ) / ((nB - nA : ℤ) : ℚ) * (q + 1), ha, ?_⟩
  have hkeyc : c * ((nB : ℝ) - nA) = (a + b) * ((nA : ℝ) + nB) := by
    rw [hA, hB]; linear_combination ratio_c a b c P
  have habq : a + b = ((q : ℝ) + 1) * b := by rw [ha]; ring
  rw [habq] at hkeyc
  have hd : ((nB : ℝ) - nA) ≠ 0 := by
    have h := hD2'; push_cast at h; exact h
  have hr : (((((nA + nB : ℤ) : ℚ) / ((nB - nA : ℤ) : ℚ)) * (q + 1) : ℚ) : ℝ)
      = (((nA : ℝ) + nB) * ((q : ℝ) + 1)) / ((nB : ℝ) - nA) := by
    push_cast; field_simp
  rw [hr, div_mul_eq_mul_div, eq_div_iff hd]
  linear_combination hkeyc
end Erdos634.Rationality
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
section Defs
variable {N : ℕ} (D : CongruentDissection N)
noncomputable def tileα : ℝ := ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)
noncomputable def tileγ : ℝ := ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1)
end Defs
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem fin3_ne_add_one : ∀ k : Fin 3, k ≠ k + 1 := by decide
end TriangleTiling
end

section
namespace TriangleTiling.Laczkovich
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles TileAngles.swap)
variable {N : ℕ} (D : CongruentDissection N)
def RightRow : Prop :=
  ∃ α β : ℝ, TileAngles D α β (Real.pi / 2) ∧ TgtAngles D α α (2 * β)
def EquiRow : Prop :=
  TileAngles D (Real.pi / 6) (Real.pi / 6) (2 * Real.pi / 3) ∧ Equilateral D
theorem fin3_third : ∀ p q : Fin 3, p ≠ q → ∃ r, r ≠ p ∧ r ≠ q := by decide
theorem angleAt_sum3 (T : Tri) {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    T.angleAt p + T.angleAt q + T.angleAt r = Real.pi := by
  rw [Erdos634.Draft.LemmaCFinal.sum3 T.angleAt p q r hpq hpr hqr]
  exact T.angleAt_sum
theorem triple_of (T : Tri) {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ σ : Equiv.Perm (Fin 3), T.angleAt (σ 0) = T.angleAt p ∧ T.angleAt (σ 1) = T.angleAt q ∧
      T.angleAt (σ 2) = T.angleAt r := by
  refine ⟨Erdos634.Draft.LemmaCFinal.permOf p q r hpq hpr hqr, ?_, ?_, ?_⟩
  · rw [Erdos634.Draft.LemmaCFinal.permOf_0]
  · rw [Erdos634.Draft.LemmaCFinal.permOf_1]
  · rw [Erdos634.Draft.LemmaCFinal.permOf_2]
theorem tgt_of_two {i j : Fin 3} (hij : i ≠ j) {x : ℝ} (hi : D.target.angleAt i = x)
    (hj : D.target.angleAt j = x) : TgtAngles D x x (Real.pi - 2 * x) := by
  obtain ⟨r, hri, hrj⟩ := fin3_third i j hij
  have hs := angleAt_sum3 D.target hij hri.symm hrj.symm
  obtain ⟨σ, h0, h1, h2⟩ := triple_of D.target hij hri.symm hrj.symm
  exact ⟨σ, h0.trans hi, h1.trans hj, by rw [h2]; linarith⟩
theorem rightRow_of {k l : Fin 3} (hlk : l ≠ k) (hk : D.model.angleAt k = Real.pi / 2)
    {j₁ j₂ : Fin 3} (hj : j₁ ≠ j₂) (h1 : D.target.angleAt j₁ = D.model.angleAt l)
    (h2 : D.target.angleAt j₂ = D.model.angleAt l) : RightRow D := by
  obtain ⟨m, hml, hmk⟩ := fin3_third l k hlk
  have hs := angleAt_sum3 D.model hml.symm hlk hmk
  obtain ⟨σ, h0, h1', h2'⟩ := triple_of D.model hml.symm hlk hmk
  refine ⟨D.model.angleAt l, D.model.angleAt m, ⟨σ, h0, h1', h2'.trans hk⟩, ?_⟩
  obtain ⟨τ, t0, t1, t2⟩ := tgt_of_two D hj h1 h2
  exact ⟨τ, t0, t1, by rw [t2]; linarith⟩
theorem tileAngles_of_eq {x y z x' y' z' : ℝ} (h : TileAngles D x y z) (hx : x = x') (hy : y = y')
    (hz : z = z') : TileAngles D x' y' z' := by
  subst hx hy hz; exact h
theorem tgtAngles_of_eq {x y z x' y' z' : ℝ} (h : TgtAngles D x y z) (hx : x = x') (hy : y = y')
    (hz : z = z') : TgtAngles D x' y' z' := by
  subst hx hy hz; exact h
theorem table_incommensurable (hirr : ∃ k, IrrPi (D.model.angleAt k)) :
    SimilarTM D ∨ RightRow D ∨
    (Equilateral D ∧ ∃ α, IrrPi α ∧ TileAngles D α (2 * Real.pi / 3 - α) (Real.pi / 3)) ∨
    (∃ α, IrrPi α ∧ TileAngles D α (Real.pi - 3 * α) (2 * α) ∧
      TgtAngles D α α (Real.pi - 2 * α)) ∨
    (∃ α β, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
      (TgtAngles D β β (3 * α) ∨ TgtAngles D (α + β) (α + β) α ∨
        TgtAngles D (2 * α) β (α + β) ∨ TgtAngles D (2 * α) α (2 * β) ∨
        TgtAngles D α α (α + 2 * β))) ∨
    (∃ α, IrrPi α ∧ TileAngles D α (Real.pi / 3 - α) (2 * Real.pi / 3) ∧
      (Equilateral D ∨ IsoTP D α ∨ F1Shape D α ∨ F2to4Shape D α)) := by
  by_cases hs : SimilarTM D
  · exact Or.inl hs
  right
  rcases Erdos634.Draft.LemmaCFinal.lemmaC_general D hirr hs with h | h | h | h | h
  · 
    obtain ⟨α, -, -, -, ⟨p, q, hpq, hp, hq⟩, γ, hγ, i, j, hij, hi, hj⟩ := h
    left
    obtain ⟨r, hrp, hrq⟩ := fin3_third p q hpq
    have hs3 := angleAt_sum3 D.model hpq hrp.symm hrq.symm
    rcases hγ with rfl | rfl
    · exact rightRow_of D hpq hq hij (hi.trans hp.symm) (hj.trans hp.symm)
    · have hr : D.model.angleAt r = Real.pi / 2 - α := by linarith
      exact rightRow_of D hrq hq hij (hi.trans hr.symm) (hj.trans hr.symm)
  · 
    obtain ⟨α, a, b, c, hα, ⟨σ, h0, -, h1, -, h2, -⟩, i, j, hij, hi, hj⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨α, hα, ⟨σ, h0, h1, h2⟩, tgt_of_two D hij hi hj⟩))
  · 
    obtain ⟨α, a, b, c, hα, hd⟩ := h
    have heq := Erdos634.Draft.LemmaPProof.lemmaP_general D α a b c hα hd hs
    obtain ⟨σ, h0, -, h1, -, h2, -⟩ := hd
    exact Or.inr (Or.inl ⟨heq, α, hα, ⟨σ, h0, h1, h2⟩⟩)
  · 
    obtain ⟨α, a, b, c, hα, ⟨σ, h0, -, h1, -, h2, -⟩, hshape⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨α, hα, ⟨σ, h0, h1, h2⟩, hshape⟩)))
  · 
    obtain ⟨α, β, a, b, c, hα, hrel, ⟨σ, h0, -, h1, -, h2, -⟩, hshape⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨α, β, hα, hrel, ⟨σ, h0, h1, h2⟩, hshape⟩)))
end TriangleTiling.Laczkovich
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
open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open TriangleTiling.Laczkovich
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
open scoped Classical
namespace Erdos634.Draft.ThmIsoFull
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
private lemma twoPiThreeData_swap {T : Tri} {α a b c : ℝ}
    (h : T.TwoPiThreeData α a b c) :
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
private lemma irrPi_beta {α : ℝ} (h : IrrPi α) : IrrPi (Real.pi / 3 - α) :=
  fun ⟨r, hr⟩ => h ⟨1 / 3 - r, by push_cast at hr ⊢; linarith⟩
private lemma rat_den_eq (q r : ℚ) (heq : r ^ 2 = q ^ 2 + q + 1) : q.den = r.den := by
  have hqd_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
  have hrd_ne : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.pos.ne'
  have hint : (r.num : ℤ) ^ 2 * (q.den : ℤ) ^ 2 =
      ((q.num : ℤ) ^ 2 + q.num * q.den + (q.den : ℤ) ^ 2) * (r.den : ℤ) ^ 2 := by
    have hq : (q : ℚ) = q.num / q.den := q.num_div_den.symm
    have hr : (r : ℚ) = r.num / r.den := r.num_div_den.symm
    have key := heq
    rw [hq, hr] at key
    have h : (r.num : ℚ) ^ 2 * q.den ^ 2 =
        (q.num ^ 2 + q.num * q.den + q.den ^ 2) * r.den ^ 2 := by
      field_simp [hqd_ne, hrd_ne] at key ⊢
      linarith
    exact_mod_cast h
  have hrd_dvd : r.den ∣ q.den := by
    have hdvd : (r.den : ℤ) ^ 2 ∣ (r.num : ℤ) ^ 2 * (q.den : ℤ) ^ 2 :=
      ⟨(q.num : ℤ)^2 + q.num * q.den + (q.den : ℤ)^2, by linear_combination hint⟩
    have hrcop2 : IsCoprime ((r.den : ℤ) ^ 2) ((r.num : ℤ) ^ 2) :=
      (Rat.isCoprime_num_den r).symm.pow_left.pow_right
    have h2 : (r.den : ℤ) ^ 2 ∣ (q.den : ℤ) ^ 2 :=
      hrcop2.dvd_of_dvd_mul_left hdvd
    exact (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp (by exact_mod_cast h2)
  have hqd_dvd : q.den ∣ r.den := by
    have hdvd2 : (q.den : ℤ) ^ 2 ∣
        ((q.num : ℤ) ^ 2 + q.num * q.den + (q.den : ℤ) ^ 2) * (r.den : ℤ) ^ 2 :=
      ⟨(r.num : ℤ) ^ 2, by linear_combination -hint⟩
    have hcop : IsCoprime (q.den : ℤ) ((q.num : ℤ) ^ 2 + q.num * q.den + (q.den : ℤ) ^ 2) := by
      have h : IsCoprime (q.den : ℤ) ((q.num : ℤ) ^ 2) :=
        (Rat.isCoprime_num_den q).symm.pow_right
      have h2 : IsCoprime (q.den : ℤ) ((q.num : ℤ) ^ 2 + (q.den : ℤ) * (q.num + q.den)) :=
        h.add_mul_left_right _
      rwa [show (q.num : ℤ) ^ 2 + (q.den : ℤ) * (q.num + q.den) =
               q.num ^ 2 + q.num * q.den + q.den ^ 2 from by ring] at h2
    have h2 : (q.den : ℤ) ^ 2 ∣ (r.den : ℤ) ^ 2 :=
      hcop.pow_left.dvd_of_dvd_mul_left hdvd2
    exact (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp (by exact_mod_cast h2)
  exact (Nat.dvd_antisymm hrd_dvd hqd_dvd).symm
set_option maxHeartbeats 800000 in
private lemma thmIso_arith_bridge
    (N : ℕ) (hN_prime : N.Prime) (hN3 : 3 < N)
    (a b c μ : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hμ : 0 < μ)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (harea : (N : ℝ) * b = μ ^ 2 * (a + 2 * b))
    (nA nB : ℤ)
    (hA : (nA : ℝ) = (μ / b) * (c - a - b))
    (hB : (nB : ℝ) = (μ / b) * (c + a + b)) :
    False := by
  have hP_ne : μ / b ≠ 0 := (div_pos hμ hb).ne'
  obtain ⟨q, r, haq, hcr⟩ :=
    Erdos634.Rationality.tile_rational a b c (μ/b) hc2 hb.ne' hP_ne (by positivity) N nA nB
      (by push_cast; field_simp [hb.ne']; linarith [harea])
      (by push_cast; linarith [hA])
      (by push_cast; linarith [hB])
  have hrq_sq : r ^ 2 = q ^ 2 + q + 1 := by
    have hb2 : (b : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hb.ne'
    have key : ((r : ℝ) ^ 2 - ((q : ℝ) ^ 2 + q + 1)) * b ^ 2 = 0 := by
      push_cast [haq, hcr] at hc2 ⊢; nlinarith
    have := (mul_eq_zero.mp key).resolve_right hb2
    exact_mod_cast sub_eq_zero.mp this
  have hden_eq : q.den = r.den := rat_den_eq q r hrq_sq
  set a₀ : ℤ := q.num
  set b₀ : ℤ := (q.den : ℤ)
  set c₀ : ℤ := r.num
  have hb0_pos : 0 < b₀ := by simp only [b₀]; exact_mod_cast q.pos
  have ha0_pos : 0 < a₀ := by
    have hq_pos : 0 < (q : ℚ) := by
      have : 0 < (q : ℝ) := by
        have hqb : (q : ℝ) * b = a := haq.symm
        exact (mul_pos_iff.mp (show 0 < q * b by rw [hqb]; exact ha)).resolve_right
          (fun ⟨_, hh⟩ => absurd hh (not_lt.mpr hb.le)) |>.1
      exact_mod_cast this
    exact_mod_cast Rat.num_pos.mpr hq_pos
  have hc0_pos : 0 < c₀ := by
    have hr_pos : 0 < (r : ℚ) := by
      have : 0 < (r : ℝ) := by
        have hrb : (r : ℝ) * b = c := hcr.symm
        exact (mul_pos_iff.mp (show 0 < r * b by rw [hrb]; exact hc)).resolve_right
          (fun ⟨_, hh⟩ => absurd hh (not_lt.mpr hb.le)) |>.1
      exact_mod_cast this
    exact_mod_cast Rat.num_pos.mpr hr_pos
  have hc0_sq : c₀ ^ 2 = a₀ ^ 2 + a₀ * b₀ + b₀ ^ 2 := by
    have hqd_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
    have h_rat : (r.num : ℚ) ^ 2 =
        (q.num : ℚ) ^ 2 + (q.num : ℚ) * q.den + (q.den : ℚ) ^ 2 := by
      have h := hrq_sq
      rw [show (q : ℚ) = q.num / q.den from q.num_div_den.symm,
          show (r : ℚ) = r.num / r.den from r.num_div_den.symm, ← hden_eq] at h
      field_simp [hqd_ne] at h
      linarith
    exact_mod_cast h_rat
  have hcop_ab : IsCoprime a₀ b₀ := Rat.isCoprime_num_den q
  have hcop_b_a2b : IsCoprime b₀ (a₀ + 2 * b₀) := hcop_ab.symm.add_mul_right_right 2
  have hcop_ac : IsCoprime a₀ c₀ := by
    rw [← IsCoprime.pow_right_iff (by norm_num : 0 < 2)]
    rw [show c₀ ^ 2 = b₀ ^ 2 + a₀ * (a₀ + b₀) from by linarith [hc0_sq]]
    exact hcop_ab.pow_right.add_mul_left_right (a₀ + b₀)
  have hb0_r : (b₀ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb0_pos.ne'
  have hqnd : (q : ℝ) * q.den = q.num := by
    have : (q : ℚ) * q.den = q.num := by
      nth_rw 1 [q.num_div_den.symm]; field_simp [Nat.cast_ne_zero.mpr q.pos.ne']
    exact_mod_cast this
  have hrnd : (r : ℝ) * q.den = r.num := by
    have h : (r : ℝ) * r.den = r.num := by
      have : (r : ℚ) * r.den = r.num := by
        nth_rw 1 [r.num_div_den.symm]; field_simp [Nat.cast_ne_zero.mpr r.pos.ne']
      exact_mod_cast this
    have hd : (q.den : ℝ) = r.den := by exact_mod_cast hden_eq
    rw [← hd] at h; exact h
  have hcab_real : μ * ((c₀ - a₀ - b₀ : ℤ) : ℝ) = ((nA * b₀ : ℤ) : ℝ) := by
    push_cast
    have hAb : (nA : ℝ) * b = μ * (c - a - b) := by rw [hA]; field_simp [hb.ne']
    have h1 : μ * ((r.num : ℝ) - q.num - q.den) * b = μ * (c - a - b) * q.den := by
      rw [hcr, haq, ← hrnd, ← hqnd]; ring
    apply mul_right_cancel₀ hb.ne'
    linear_combination h1 - (q.den : ℝ) * hAb
  have hcab2_real : μ * ((c₀ + a₀ + b₀ : ℤ) : ℝ) = ((nB * b₀ : ℤ) : ℝ) := by
    push_cast
    have hBb : (nB : ℝ) * b = μ * (c + a + b) := by rw [hB]; field_simp [hb.ne']
    have h1 : μ * ((r.num : ℝ) + q.num + q.den) * b = μ * (c + a + b) * q.den := by
      rw [hcr, haq, ← hrnd, ← hqnd]; ring
    apply mul_right_cancel₀ hb.ne'
    linear_combination h1 - (q.den : ℝ) * hBb
  have ha_eq : (a : ℝ) = a₀ / b₀ * b := by
    simp only [a₀, b₀]; push_cast
    rw [← show (q : ℝ) = q.num / q.den from by exact_mod_cast q.num_div_den.symm]
    exact haq
  have hd_ne : (c₀ - a₀ - b₀ : ℤ) ≠ 0 := by
    intro h0
    have hcab0_zero := hcab_real
    rw [show ((c₀ - a₀ - b₀ : ℤ) : ℝ) = 0 from by exact_mod_cast h0, mul_zero] at hcab0_zero
    have hnA : nA = 0 := by
      have : (nA * b₀ : ℤ) = 0 := by exact_mod_cast hcab0_zero.symm
      exact (mul_eq_zero.mp this).resolve_right hb0_pos.ne'
    have hcab0 : c = a + b := by
      have hnA_r : (nA : ℝ) = 0 := by exact_mod_cast hnA
      have hmcab : (μ / b) * (c - a - b) = 0 := by linarith [hA, hnA_r]
      rcases mul_eq_zero.mp hmcab with h | h
      · exact absurd h hP_ne
      · linarith
    have hc2' := hc2; rw [hcab0] at hc2'
    nlinarith [hc2', mul_pos ha hb]
  let qμ : ℚ := (nA * b₀ : ℤ) / ((c₀ - a₀ - b₀ : ℤ) : ℚ)
  have hqmu_eq : μ = qμ := by
    have hd_r : ((c₀ - a₀ - b₀ : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hd_ne
    rw [show (qμ : ℝ) = ((nA * b₀ : ℤ) : ℝ) / ((c₀ - a₀ - b₀ : ℤ) : ℝ) from by simp [qμ]]
    rw [eq_comm, div_eq_iff hd_r]
    linarith [hcab_real]
  have h2mu2 : 2 * μ ^ 2 = (N : ℝ) + nA * nB := by
    have hprod : μ ^ 2 * ((c₀ - a₀ - b₀ : ℤ) : ℝ) * ((c₀ + a₀ + b₀ : ℤ) : ℝ) =
        (nA : ℝ) * nB * (b₀ : ℝ) ^ 2 := by
      have h1 : μ * ((c₀ - a₀ - b₀ : ℤ) : ℝ) = (nA : ℝ) * b₀ := by
        have := hcab_real; push_cast at this ⊢; linarith
      have h2 : μ * ((c₀ + a₀ + b₀ : ℤ) : ℝ) = (nB : ℝ) * b₀ := by
        have := hcab2_real; push_cast at this ⊢; linarith
      calc μ ^ 2 * ((c₀ - a₀ - b₀ : ℤ) : ℝ) * ((c₀ + a₀ + b₀ : ℤ) : ℝ)
          = μ * ((c₀ - a₀ - b₀ : ℤ) : ℝ) * (μ * ((c₀ + a₀ + b₀ : ℤ) : ℝ)) := by ring
        _ = (nA : ℝ) * b₀ * ((nB : ℝ) * b₀) := by rw [h1, h2]
        _ = nA * nB * b₀ ^ 2 := by ring
    have hident : ((c₀ - a₀ - b₀ : ℤ) : ℝ) * ((c₀ + a₀ + b₀ : ℤ) : ℝ) =
        -(a₀ : ℝ) * b₀ := by
      have hc0_sq_r : ((c₀ : ℤ) : ℝ) ^ 2 = (a₀ : ℝ) ^ 2 + (a₀ : ℝ) * b₀ + (b₀ : ℝ) ^ 2 :=
        by exact_mod_cast hc0_sq
      push_cast; nlinarith [hc0_sq_r]
    have hprod_fac : μ ^ 2 * (-(a₀ : ℝ) * b₀) = (nA : ℝ) * nB * b₀ ^ 2 :=
      calc μ ^ 2 * (-(a₀ : ℝ) * b₀)
          = μ ^ 2 * (((c₀-a₀-b₀:ℤ):ℝ) * ((c₀+a₀+b₀:ℤ):ℝ)) := by rw [hident]
        _ = μ ^ 2 * ((c₀-a₀-b₀:ℤ):ℝ) * ((c₀+a₀+b₀:ℤ):ℝ) := by ring
        _ = (nA : ℝ) * nB * b₀ ^ 2 := hprod
    have harea_sc : μ ^ 2 * ((a₀ : ℝ) + 2 * b₀) = (N : ℝ) * b₀ := by
      apply mul_right_cancel₀ hb.ne'
      calc μ ^ 2 * ((a₀ : ℝ) + 2 * b₀) * b
          = μ ^ 2 * (a₀ / b₀ * b + 2 * b) * b₀ := by field_simp [hb0_r]
        _ = μ ^ 2 * (a + 2 * b) * b₀ := by rw [ha_eq]
        _ = N * b * b₀ := by rw [harea]
        _ = N * b₀ * b := by ring
    have h2b : 2 * μ ^ 2 * b₀ ^ 2 = ((N : ℝ) + nA * nB) * b₀ ^ 2 := by
      have key : μ ^ 2 * ((a₀ : ℝ) + 2 * b₀) * b₀ = (N : ℝ) * b₀ ^ 2 := by
        rw [show μ ^ 2 * ((a₀ : ℝ) + 2 * b₀) * b₀ =
              (μ ^ 2 * ((a₀ : ℝ) + 2 * b₀)) * b₀ from by ring, harea_sc]; ring
      have h1 : μ ^ 2 * (a₀ : ℝ) * b₀ + 2 * μ ^ 2 * b₀ ^ 2 = (N : ℝ) * b₀ ^ 2 := by
        linarith [show μ^2*((a₀:ℝ)+2*b₀)*b₀ = μ^2*(a₀:ℝ)*b₀ + 2*μ^2*b₀^2 from by ring, key]
      have h2 : μ ^ 2 * (a₀ : ℝ) * b₀ = -((nA : ℝ) * nB * b₀ ^ 2) := by
        linarith [show μ^2*(-(a₀:ℝ)*b₀) = -(μ^2*(a₀:ℝ)*b₀) from by ring, hprod_fac]
      linarith [h1, h2]
    exact mul_right_cancel₀ (pow_ne_zero 2 hb0_r) (by linarith [h2b])
  have hden1 : qμ.den = 1 := by
    have h2q2 : 2 * qμ ^ 2 = ((N : ℤ) + nA * nB : ℤ) := by
      have : (2 * qμ ^ 2 : ℝ) = (((N : ℤ) + nA * nB : ℤ) : ℝ) := by
        push_cast; rw [← hqmu_eq]; linarith [h2mu2]
      exact_mod_cast this
    have hd_ne' : (qμ.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr qμ.pos.ne'
    have hint_int : 2 * (qμ.num : ℤ) ^ 2 = (qμ.den : ℤ) ^ 2 * ((N : ℤ) + nA * nB) := by
      have h2q2' := h2q2
      rw [show (qμ : ℚ) = (qμ.num : ℚ) / qμ.den from qμ.num_div_den.symm] at h2q2'
      field_simp [hd_ne'] at h2q2'
      exact_mod_cast h2q2'
    have hdvd : (qμ.den : ℤ) ^ 2 ∣ 2 * qμ.num ^ 2 := by
      rw [hint_int]; exact dvd_mul_right _ _
    have hcop_pow : IsCoprime ((qμ.den : ℤ) ^ 2) ((qμ.num : ℤ) ^ 2) :=
      (Rat.isCoprime_num_den qμ).symm.pow_left.pow_right
    have hdvd2 : (qμ.den : ℤ) ^ 2 ∣ 2 :=
      hcop_pow.dvd_of_dvd_mul_left (by rwa [mul_comm] at hdvd)
    have hd_le : (qμ.den : ℤ) ^ 2 ≤ 2 := Int.le_of_dvd (by norm_num) hdvd2
    have hd_le1 : qμ.den ≤ 1 := by
      have hd_int : (0 : ℤ) < qμ.den := by exact_mod_cast qμ.pos
      have : (qμ.den : ℤ) ≤ 1 := by nlinarith [sq_nonneg ((qμ.den : ℤ) - 1), hd_le]
      exact_mod_cast this
    exact Nat.le_antisymm hd_le1 qμ.pos
  obtain ⟨k, hk⟩ : ∃ k : ℤ, μ = k :=
    ⟨qμ.num, by
      rw [hqmu_eq]
      have hqnum_eq : (qμ.num : ℚ) = qμ := by
        nth_rw 2 [← qμ.num_div_den]; rw [hden1, Nat.cast_one, div_one]
      exact_mod_cast hqnum_eq.symm⟩
  have hk_pos : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by rw [← hk]; exact hμ)
  have harea_int : b₀ * (N : ℤ) = k ^ 2 * (a₀ + 2 * b₀) := by
    have h_r : (b₀ : ℝ) * N = k ^ 2 * (a₀ + 2 * b₀) := by
      rw [hk] at harea
      apply mul_right_cancel₀ hb.ne'
      calc (b₀ : ℝ) * N * b
          = N * b * b₀ := by ring
        _ = k ^ 2 * (a + 2 * b) * b₀ := by rw [harea]
        _ = k ^ 2 * (a₀ / b₀ * b + 2 * b) * b₀ := by rw [ha_eq]
        _ = k ^ 2 * (a₀ + 2 * b₀) * b := by field_simp [hb0_r]
    exact_mod_cast h_r
  have ha2b_ge3 : 3 ≤ a₀ + 2 * b₀ := by linarith [ha0_pos, hb0_pos]
  obtain ⟨hksq, _⟩ := Row9.k_sq_eq_b a₀ b₀ k N hN_prime ha2b_ge3 hcop_b_a2b
    (by linarith [harea_int])
  have hkM : k * nA = c₀ - a₀ - b₀ := by
    have h_int : k * (c₀ - a₀ - b₀) = nA * k ^ 2 := by
      have h_real : (k : ℝ) * ((c₀ - a₀ - b₀ : ℤ) : ℝ) = ((nA * b₀ : ℤ) : ℝ) := by
        rw [← hk]; exact hcab_real
      have this_int := by exact_mod_cast h_real
      linear_combination this_int - nA * hksq
    exact Int.eq_of_mul_eq_mul_left hk_pos.ne' (by linear_combination -h_int)
  exact Row9.iso_arith_core a₀ b₀ c₀ k nA N
    ha0_pos hb0_pos hc0_pos hk_pos hc0_sq hcop_ac hN_prime ha2b_ge3 hcop_b_a2b
    (by linarith [harea_int]) hkM
private lemma twoPiThree_c_sq' {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha', -, hb', hγ, hc'⟩ := h
  have hlc := T.lawCos_perm σ
  rw [ha', hb', hc', hγ, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hlc
  linarith
set_option maxHeartbeats 800000 in
theorem thmIsoAll : ∀ (N : ℕ) (D : CongruentDissection N), N.Prime → 3 < N →
    ∀ α a b c : ℝ, IrrPi α → D.model.TwoPiThreeData α a b c → IsoTP D α → False := by
  intro N D hN_prime hN3 α a b c hα hm hisoTP
  obtain ⟨_, hc, ha, hb⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := twoPiThree_c_sq' hm
  obtain ⟨hiso_α, hiso_β⟩ := Row9.iso_closed_forms a b c hc2
  obtain ⟨hcamb_pos, hcbma_pos, Mα, Mβ, hMα_raw, hMβ_raw, -, -, -⟩ :=
    Paper.cor_int_at D hα hm 0
  erw [fAlphaAt_zero] at hMα_raw; erw [fBetaAt_zero] at hMβ_raw
  have hA_eq : ∀ μ : ℝ, 0 < μ →
      D.target.flux (fAlpha α hα).weight = μ*(a+2*b-2*c) →
      (Mα : ℝ) = (μ/b)*(c-a-b) := fun μ _ sgn => by
    rw [hMα_raw, sgn]; field_simp [hcamb_pos.ne', hb.ne']; nlinarith [hiso_α]
  have hA_neg : ∀ μ : ℝ, 0 < μ →
      D.target.flux (fAlpha α hα).weight = -(μ*(a+2*b-2*c)) →
      ((-Mα : ℤ) : ℝ) = (μ/b)*(c-a-b) := fun μ _ sgn => by
    push_cast
    have hgoal : -(Mα : ℝ) = μ*(a+2*b-2*c) / (c+a-b) := by rw [hMα_raw, sgn]; ring
    rw [hgoal]; field_simp [hcamb_pos.ne', hb.ne']; nlinarith [hiso_α]
  have hB_eq : ∀ μ : ℝ, 0 < μ →
      D.target.flux (fBeta α hα).weight = μ*(a+2*b+2*c) →
      (Mβ : ℝ) = (μ/b)*(c+a+b) := fun μ _ sgn => by
    rw [hMβ_raw, sgn]; field_simp [hcbma_pos.ne', hb.ne']; nlinarith [hiso_β]
  have hB_neg : ∀ μ : ℝ, 0 < μ →
      D.target.flux (fBeta α hα).weight = -(μ*(a+2*b+2*c)) →
      ((-Mβ : ℤ) : ℝ) = (μ/b)*(c+a+b) := fun μ _ sgn => by
    push_cast
    have hgoal : -(Mβ : ℝ) = μ*(a+2*b+2*c) / (c+b-a) := by rw [hMβ_raw, sgn]; ring
    rw [hgoal]; field_simp [hcbma_pos.ne', hb.ne']; nlinarith [hiso_β]
  rcases hisoTP with htgt | htgt
  · obtain ⟨μ, hμ, hbase⟩ := base_alpha_of_isoTP D hm htgt
    have harea := Erdos634.Draft.ThmIso.base_alpha_area_identity D hm hbase ha hb hμ
    obtain hcf_α | hcf_α := Row9.lemmaCF_alpha D.target hα hbase <;>
    obtain hcf_β | hcf_β := Row9.lemmaCF_beta D.target hα hbase
    · exact thmIso_arith_bridge N hN_prime hN3 a b c μ ha hb hc hμ hc2 harea Mα Mβ
        (hA_eq μ hμ hcf_α) (hB_eq μ hμ hcf_β)
    · exact thmIso_arith_bridge N hN_prime hN3 a b c μ ha hb hc hμ hc2 harea Mα (-Mβ)
        (hA_eq μ hμ hcf_α) (hB_neg μ hμ hcf_β)
    · exact thmIso_arith_bridge N hN_prime hN3 a b c μ ha hb hc hμ hc2 harea (-Mα) Mβ
        (hA_neg μ hμ hcf_α) (hB_eq μ hμ hcf_β)
    · exact thmIso_arith_bridge N hN_prime hN3 a b c μ ha hb hc hμ hc2 harea (-Mα) (-Mβ)
        (hA_neg μ hμ hcf_α) (hB_neg μ hμ hcf_β)
  · have hm' := twoPiThreeData_swap hm
    have hα' := irrPi_beta hα
    have htgt' : TgtAngles D (Real.pi/3-α) (Real.pi/3-α)
        ((Real.pi/3-α) + 3*(Real.pi/3-(Real.pi/3-α))) := by convert htgt using 2; ring
    obtain ⟨μ, hμ, hbase⟩ := base_alpha_of_isoTP D hm' htgt'
    have hc2' : c ^ 2 = b ^ 2 + b * a + a ^ 2 := by linarith [hc2, mul_comm a b]
    have harea := Erdos634.Draft.ThmIso.base_alpha_area_identity D hm' hbase hb ha hμ
    obtain ⟨hiso_α', hiso_β'⟩ := Row9.iso_closed_forms b a c hc2'
    obtain ⟨hcamb_pos', hcbma_pos', Mα', Mβ', hMα_raw', hMβ_raw', -, -, -⟩ :=
      Paper.cor_int_at D hα' hm' 0
    erw [fAlphaAt_zero] at hMα_raw'; erw [fBetaAt_zero] at hMβ_raw'
    have hA_eq' : ∀ μ : ℝ, 0 < μ →
        D.target.flux (fAlpha (Real.pi/3-α) hα').weight = μ*(b+2*a-2*c) →
        (Mα' : ℝ) = (μ/a)*(c-b-a) := fun μ _ sgn => by
      rw [hMα_raw', sgn]; field_simp [hcamb_pos'.ne', ha.ne']; nlinarith [hiso_α']
    have hA_neg' : ∀ μ : ℝ, 0 < μ →
        D.target.flux (fAlpha (Real.pi/3-α) hα').weight = -(μ*(b+2*a-2*c)) →
        ((-Mα' : ℤ) : ℝ) = (μ/a)*(c-b-a) := fun μ _ sgn => by
      push_cast
      have hgoal : -(Mα' : ℝ) = μ*(b+2*a-2*c) / (c+b-a) := by rw [hMα_raw', sgn]; ring
      rw [hgoal]; field_simp [hcamb_pos'.ne', ha.ne']; nlinarith [hiso_α']
    have hB_eq' : ∀ μ : ℝ, 0 < μ →
        D.target.flux (fBeta (Real.pi/3-α) hα').weight = μ*(b+2*a+2*c) →
        (Mβ' : ℝ) = (μ/a)*(c+b+a) := fun μ _ sgn => by
      rw [hMβ_raw', sgn]; field_simp [hcbma_pos'.ne', ha.ne']; nlinarith [hiso_β']
    have hB_neg' : ∀ μ : ℝ, 0 < μ →
        D.target.flux (fBeta (Real.pi/3-α) hα').weight = -(μ*(b+2*a+2*c)) →
        ((-Mβ' : ℤ) : ℝ) = (μ/a)*(c+b+a) := fun μ _ sgn => by
      push_cast
      have hgoal : -(Mβ' : ℝ) = μ*(b+2*a+2*c) / (c+a-b) := by rw [hMβ_raw', sgn]; ring
      rw [hgoal]; field_simp [hcbma_pos'.ne', ha.ne']; nlinarith [hiso_β']
    obtain hcf_α | hcf_α := Row9.lemmaCF_alpha D.target hα' hbase <;>
    obtain hcf_β | hcf_β := Row9.lemmaCF_beta D.target hα' hbase
    · exact thmIso_arith_bridge N hN_prime hN3 b a c μ hb ha hc hμ hc2' harea Mα' Mβ'
        (hA_eq' μ hμ hcf_α) (hB_eq' μ hμ hcf_β)
    · exact thmIso_arith_bridge N hN_prime hN3 b a c μ hb ha hc hμ hc2' harea Mα' (-Mβ')
        (hA_eq' μ hμ hcf_α) (hB_neg' μ hμ hcf_β)
    · exact thmIso_arith_bridge N hN_prime hN3 b a c μ hb ha hc hμ hc2' harea (-Mα') Mβ'
        (hA_neg' μ hμ hcf_α) (hB_eq' μ hμ hcf_β)
    · exact thmIso_arith_bridge N hN_prime hN3 b a c μ hb ha hc hμ hc2' harea (-Mα') (-Mβ')
        (hA_neg' μ hμ hcf_α) (hB_neg' μ hμ hcf_β)
end Erdos634.Draft.ThmIsoFull
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open TriangleTiling.Laczkovich
variable {N : ℕ} (D : CongruentDissection N)
theorem relabel_angleAt (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabelModel D τ).model.angleAt k = D.model.angleAt (τ k) :=
  (Row2.angleAt_comp D.model (relabelModel D τ).model τ (fun _ => rfl) k).1
theorem tgt_iso {θ : ℝ} (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = θ)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = θ) :
    TgtAngles D θ θ (Real.pi - 2 * θ) :=
  tgt_of_two D (i := 0) (j := 2) (by decide) hA (by rw [target_angleAt_2]; exact hC)
end TriangleTiling
end

section
namespace TriangleTiling.Laczkovich
open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles TileAngles.swap)
variable {N : ℕ} (D : CongruentDissection N)
theorem two_equal_of_iso {x y z : ℝ} (h : TgtAngles D x y z)
    (hiso : D.target.angleAt 0 = D.target.angleAt 2) : x = y ∨ x = z ∨ y = z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  have hi : σ (σ.symm 0) = 0 := σ.apply_symm_apply 0
  have hj : σ (σ.symm 2) = 2 := σ.apply_symm_apply 2
  have hne : σ.symm 0 ≠ σ.symm 2 := fun h => absurd (σ.symm.injective h) (by decide)
  have : ∀ i j : Fin 3, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 0) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by decide
  rcases this _ _ hne with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
    rw [a] at hi <;> rw [b] at hj
  · left; rw [← h0, ← h1, hi, hj, hiso]
  · right; left; rw [← h0, ← h2, hi, hj, hiso]
  · left; rw [← h0, ← h1, hi, hj, hiso]
  · right; right; rw [← h1, ← h2, hi, hj, hiso]
  · right; left; rw [← h0, ← h2, hi, hj, hiso]
  · right; right; rw [← h1, ← h2, hi, hj, hiso]
theorem base_of_double {x z : ℝ} (h : TgtAngles D x x z)
    (hiso : D.target.angleAt 0 = D.target.angleAt 2) : D.target.angleAt 0 = x := by
  obtain ⟨σ, s0, s1, -⟩ := h
  have hσ : σ 0 ≠ σ 1 := fun h => absurd (σ.injective h) (by decide)
  have : ∀ i j : Fin 3, i ≠ j → (i = 0 ∨ i = 2) ∨ (j = 0 ∨ j = 2) := by decide
  rcases this (σ 0) (σ 1) hσ with (h | h) | (h | h)
  · rw [← s0, h]
  · rw [← s0, h, hiso]
  · rw [← s1, h]
  · rw [← s1, h, hiso]
end TriangleTiling.Laczkovich
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
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
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
open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
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


namespace TriangleTiling.Laczkovich
open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles TileAngles.swap)
variable {N : ℕ} (D : CongruentDissection N)
/-- The irrational half of laczkovich_isosceles (the classification of tilings of an isosceles
triangle whose tile has an angle not in Q pi). -/
theorem omaIsoIrr {θ : ℝ} (hirr : ∃ k, IrrPi (D.model.angleAt k))
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = θ)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = θ)
    (hne : θ ≠ Real.pi / 3) :
    SimilarTM D ∨ TileAngles D θ (Real.pi / 2 - θ) (Real.pi / 2) ∨
    (IrrPi θ ∧ TileAngles D θ (Real.pi - 3 * θ) (2 * θ)) ∨
    (IrrPi θ ∧ TileAngles D θ (Real.pi / 3 - θ) (2 * Real.pi / 3)) ∨
    (∃ α β, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
      (θ = α ∨ θ = β ∨ θ = α + β)) := by
  have ht0 : D.target.angleAt 0 = θ := hA
  have ht2 : D.target.angleAt 2 = θ := by rw [target_angleAt_2, hC]
  have hiso : D.target.angleAt 0 = D.target.angleAt 2 := ht0.trans ht2.symm
  have hpi := Real.pi_pos
  have noeq : Equilateral D → False := fun h => hne (ht0 ▸ h 0)
  
  have of_right : RightRow D → TileAngles D θ (Real.pi / 2 - θ) (Real.pi / 2) := by
    rintro ⟨α, β, hT, hG⟩
    have hαθ : θ = α := ht0 ▸ base_of_double D hG hiso
    obtain ⟨ρ, r0, r1, r2⟩ := hT
    have hs := D.model.angleAt_sum
    have hsum : α + β + Real.pi / 2 = Real.pi := by
      have := angleAt_sum3 D.model (p := ρ 0) (q := ρ 1) (r := ρ 2)
        (fun h => absurd (ρ.injective h) (by decide)) (fun h => absurd (ρ.injective h) (by decide))
        (fun h => absurd (ρ.injective h) (by decide))
      rw [r0, r1, r2] at this; exact this
    exact ⟨ρ, r0.trans hαθ.symm, by rw [r1, hαθ]; linarith, r2⟩
  rcases table_incommensurable D hirr with h | h | ⟨h, -⟩ | ⟨α, hα, hT, hG⟩ |
      ⟨α, β, hα, hrel, hT, hG⟩ | ⟨α, hα, hT, hG⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl (of_right h))
  · exact (noeq h).elim
  · 
    have hθ : θ = α := ht0 ▸ base_of_double D hG hiso
    subst hθ
    exact Or.inr (Or.inr (Or.inl ⟨hα, hT⟩))
  · 
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨α, β, hα, hrel, hT, ?_⟩)))
    rcases hG with h | h | h | h | h
    · exact Or.inr (Or.inl (ht0 ▸ base_of_double D h hiso))
    · exact Or.inr (Or.inr (ht0 ▸ base_of_double D h hiso))
    · exfalso
      rcases two_equal_of_iso D h hiso with e | e | e
      · exact hα ⟨1 / 7, by push_cast; linarith⟩
      · exact hα ⟨1 / 5, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
    · exfalso
      rcases two_equal_of_iso D h hiso with e | e | e
      · exact hα ⟨0, by push_cast; linarith⟩
      · exact hα ⟨1 / 5, by push_cast; linarith⟩
      · exact hα ⟨1 / 4, by push_cast; linarith⟩
    · exact Or.inl (ht0 ▸ base_of_double D h hiso)
  · 
    rcases hG with h | h | h | h
    · exact (noeq h).elim
    · rcases h with h | h
      · have hθ : θ = α := ht0 ▸ base_of_double D h hiso
        subst hθ
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hα, hT⟩)))
      · have hθ : θ = Real.pi / 3 - α := ht0 ▸ base_of_double D h hiso
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨fun ⟨q, hq⟩ => hα ⟨1 / 3 - q, ?_⟩, ?_⟩)))
        · push_cast; linarith
        · exact tileAngles_of_eq D hT.swap hθ.symm (by linarith) rfl
    · exfalso
      rcases h with h | h <;> rcases two_equal_of_iso D h hiso with e | e | e
      · exact hα ⟨1 / 3, by push_cast; linarith⟩
      · exact hα ⟨1 / 3, by push_cast; linarith⟩
      · exact hα ⟨1 / 3, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
    · exfalso
      rcases h with h | h | h | h | h <;> rcases two_equal_of_iso D h hiso with e | e | e
      · exact hα ⟨1 / 6, by push_cast; linarith⟩
      · exact hα ⟨1 / 6, by push_cast; linarith⟩
      · exact hα ⟨1 / 6, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
      · exact hα ⟨1 / 4, by push_cast; linarith⟩
      · exact hα ⟨1 / 5, by push_cast; linarith⟩
      · exact hα ⟨1 / 3, by push_cast; linarith⟩
      · exact hα ⟨1 / 12, by push_cast; linarith⟩
      · exact hα ⟨2 / 15, by push_cast; linarith⟩
      · exact hα ⟨2 / 9, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
      · exact hα ⟨1 / 9, by push_cast; linarith⟩
      · exact hα ⟨1 / 9, by push_cast; linarith⟩
      · exact hα ⟨0, by push_cast; linarith⟩
      · exact hα ⟨2 / 9, by push_cast; linarith⟩
end TriangleTiling.Laczkovich

open EuclideanGeometry in
/-- Laczkovich's classification for an isosceles T (repeated angle not pi/3) and a tile with an angle
not in Q pi, with the RightRow and similar cases and the (θ, pi/3 - θ, 2pi/3) tile (Bonfioli,
thmIsoAll) excluded. -/
theorem OMA.solution : OMA.R_erdos_634_R1_H2_R1_H4_R1.H2 := by
  intro p hp hp3 T Ts hc hd hu t A B hA hB hs hrr hiso hirr
  obtain ⟨i, j, hij, he, hθ⟩ := hiso
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
  have hk : ∃ k, Erdos634.Draft.TheoremPConditional.IrrPi (D₁.model.angleAt k) := by
    by_contra h
    apply hirr
    intro k
    by_contra hq
    exact h ⟨k, fun ⟨q, e⟩ => hq ⟨q, by rw [← hm k]; exact e⟩⟩
  rcases TriangleTiling.Laczkovich.omaIsoIrr D₁ hk hA1 hC1 hθ with
    ⟨μ, τ, hsim⟩ | ⟨ρ, r0, r1, r2⟩ | ⟨hθi, ρ, r0, r1, r2⟩ | ⟨hθi, ρ, r0, r1, r2⟩ |
      ⟨α, β, hα, hrel, ⟨ρ, r0, r1, r2⟩, hθ'⟩
  · exfalso
    apply hs
    refine ⟨σ.symm.trans τ, funext fun k => ?_⟩
    have e := (hsim (σ.symm k)).1
    rw [ht, hm, Equiv.apply_symm_apply] at e
    show A k = B ((σ.symm.trans τ) k)
    rw [Equiv.trans_apply]
    exact e
  · exfalso
    apply hrr
    exact ⟨ρ 2, ρ 0, fun h => absurd (ρ.injective h) (by decide), (hm _).symm.trans r2, i, j, hij,
      r0.symm.trans (hm _), he.symm.trans (r0.symm.trans (hm _))⟩
  · exact Or.inl ⟨i, j, hij, he, hθi, ρ, OMA.E634H.comp_vec ((hm _).symm.trans r0)
      ((hm _).symm.trans r1) ((hm _).symm.trans r2)⟩
  · exfalso
    have hdata : D₁.model.TwoPiThreeData (A i) (D₁.model.oppLen (ρ 0)) (D₁.model.oppLen (ρ 1))
        (D₁.model.oppLen (ρ 2)) := ⟨ρ, r0, rfl, r1, rfl, r2, rfl⟩
    have hisoTP : Erdos634.Draft.TheoremPConditional.IsoTP D₁ (A i) :=
      Or.inl (TriangleTiling.Laczkovich.tgtAngles_of_eq D₁ (TriangleTiling.tgt_iso D₁ hA1 hC1) rfl rfl
        (by ring))
    exact Erdos634.Draft.ThmIsoFull.thmIsoAll p D₁ hp hp3 (A i) _ _ _ hθi hdata hisoTP
  · exact Or.inr ⟨α, β, hα, hrel, ⟨ρ, OMA.E634H.comp_vec ((hm _).symm.trans r0)
      ((hm _).symm.trans r1) ((hm _).symm.trans r2)⟩, i, j, hij, he, hθ'⟩


