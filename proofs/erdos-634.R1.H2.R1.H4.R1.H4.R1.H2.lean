import OMAReductions.R_erdos_634_R1_H2_R1_H4_R1_H4_R1

/-!
# Erdos 634, step R1.H2.R1.H4.R1.H4.R1.H2: the tile (α, β, 2α + β) on an isosceles triangle, given rationaltile and isobetaone

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
theorem vertex_multiplicities {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (x y z : ℕ) (s t : ℤ)
    (hsum : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = (s : ℝ) * α + (t : ℝ) * β) :
    (x : ℤ) + 2 * z = s ∧ (y : ℤ) + z = t := by
  have hβ : β = (Real.pi - 3 * α) / 2 := by linarith
  have hkey : ((2 * ((x : ℤ) + 2 * z - s) - 3 * ((y : ℤ) + z - t) : ℤ) : ℝ) * α
      + (((y : ℤ) + z - t : ℤ) : ℝ) * Real.pi = 0 := by
    rw [hβ] at hsum
    push_cast
    linear_combination 2 * hsum
  obtain ⟨hA, hB⟩ := angle_indep hirr
    (2 * ((x : ℤ) + 2 * z - s) - 3 * ((y : ℤ) + z - t)) ((y : ℤ) + z - t) hkey
  omega
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
def Tri.Reflected (T model : Tri) : Prop := (0 < T.det) ↔ (model.det < 0)
noncomputable def Tri.relabel (T : Tri) (τ : Equiv.Perm (Fin 3)) : Tri where
  pts := T.pts ∘ τ
  indep := T.indep.comp_embedding τ.toEmbedding
theorem Tri.relabel_pts (T : Tri) (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (T.relabel τ).pts k = T.pts (τ k) := rfl
theorem Tri.congruent_relabel (T : Tri) (τ : Equiv.Perm (Fin 3)) : T.Congruent (T.relabel τ) := by
  refine ⟨IsometryEquiv.refl Plane, τ.symm, fun k => ?_⟩
  show T.pts k = (T.relabel τ).pts (τ.symm k)
  simp [Tri.relabel_pts]
theorem Tri.Congruent.relabel {T U : Tri} (h : T.Congruent U) (τ : Equiv.Perm (Fin 3)) :
    T.Congruent (U.relabel τ) :=
  h.trans (U.congruent_relabel τ)
structure CongruentDissection (N : ℕ) extends Dissection N where
  model : Tri
  tiles_congruent : ∀ i, (tile i).Congruent model
namespace CongruentDissection
variable {N : ℕ}
noncomputable def relabelModel (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) :
    CongruentDissection N where
  toDissection := D.toDissection
  model := D.model.relabel τ
  tiles_congruent := fun i => (D.tiles_congruent i).relabel τ
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
namespace Erdos634.BaseSelection
open Erdos634.Geometry
theorem tile_subset_target {N : ℕ} (D : Dissection N) (i : Fin N) :
    (D.tile i).carrier ⊆ D.target.carrier := by
  rw [← D.covers]
  exact Set.subset_iUnion (fun j => (D.tile j).carrier) i
theorem tile_interior_subset {N : ℕ} (D : Dissection N) (i : Fin N) :
    interior (D.tile i).carrier ⊆ interior D.target.carrier :=
  interior_mono (tile_subset_target D i)
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
theorem corner_multiplicities {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ)) :
    (({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card : ℝ) * α
      + (({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card : ℝ) * β
      + (({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card : ℝ) * γ
      + (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card : ℝ)
        * Real.pi
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) := by
  classical
  have hsum := Erdos634.VertexFigureReal.corner_angle_sum D k
  rw [Erdos634.VertexFigureReal.sum_by_value ({α, β, γ, Real.pi, 0} : Finset ℝ) _ hvals] at hsum
  rw [Finset.sum_insert (by simp [hαβ, hαγ, hαπ, hα0]),
      Finset.sum_insert (by simp [hβγ, hβπ, hβ0]),
      Finset.sum_insert (by simp [hγπ, hγ0]),
      Finset.sum_insert (by simp [hπ0]), Finset.sum_singleton] at hsum
  push_cast at hsum ⊢
  linarith [hsum]
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
theorem GridChar.rank2_mem (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anchor : Real.Angle) (j k : ℤ) :
    (((j : ℝ) * Real.pi + (k : ℝ) * θ : ℝ) : Real.Angle) ∈ (GridChar.rank2 θ hθ b anchor).L := by
  rw [← rank2Map_apply]
  exact AddMonoidHom.mem_range.mpr ⟨(j, k), rfl⟩
theorem GridChar.rank2_chi (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anchor : Real.Angle) (j k : ℤ) :
    (GridChar.rank2 θ hθ b anchor).chi (((j : ℝ) * Real.pi + (k : ℝ) * θ : ℝ) : Real.Angle)
      = if (j : ZMod 2) + b * (k : ZMod 2) = 0 then 1 else -1 := by
  rw [← rank2Map_apply]
  exact GridChar.ofHom_chi _ _ _ _ _ _ _ (j, k)
theorem GridChar.rank2_sq (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anchor : Real.Angle) :
    ∀ l ∈ (GridChar.rank2 θ hθ b anchor).L,
      (GridChar.rank2 θ hθ b anchor).chi l * (GridChar.rank2 θ hθ b anchor).chi l = 1 :=
  GridChar.ofHom_sq _ _ _ _ _ _ _
end Erdos634.Geometry
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
noncomputable def chiMinus (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : GridChar ℝ :=
  GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) 1 0
def Tri.ThreeAlphaData (T : Tri) (α β a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = β ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = 2 * α + β ∧ T.oppLen (σ 2) = c
theorem Tri.threeAlpha_angles_mem {T : Tri} {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : T.ThreeAlphaData α β a b c) (b' : ZMod 2) :
    ∀ j, ((T.angleAt j : ℝ) : Real.Angle)
      ∈ (GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) b' 0).L := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  intro j
  obtain ⟨k, rfl⟩ := σ.surjective j
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · rw [h0, show ((α : ℝ) : Real.Angle)
        = ((((-1 : ℤ) : ℝ) * Real.pi + ((2 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) by
      congr 1; push_cast; ring]
    exact GridChar.rank2_mem _ _ _ _ _ _
  · rw [h1, show β = ((2 : ℤ) : ℝ) * Real.pi + ((-3 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith]
    exact GridChar.rank2_mem _ _ _ _ _ _
  · rw [h2, show 2 * α + β = ((0 : ℤ) : ℝ) * Real.pi + ((1 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith]
    exact GridChar.rank2_mem _ _ _ _ _ _
theorem threeAlpha_tileValue (T : Tri) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : T.ThreeAlphaData α β a b c) (b' : ZMod 2) :
    (GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) b' 0).tileValue T
      = (if ((2 : ℤ) : ZMod 2) + b' * ((-2 : ℤ) : ZMod 2) = 0 then 1 else -1) * a
        + (if ((-1 : ℤ) : ZMod 2) + b' * ((3 : ℤ) : ZMod 2) = 0 then 1 else -1) * b
        + (if ((1 : ℤ) : ZMod 2) + b' * ((-1 : ℤ) : ZMod 2) = 0 then 1 else -1) * c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ (fun j =>
    (GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) b' 0).chi
      ((Real.pi - T.angleAt j : ℝ) : Real.Angle) * T.oppLen j), Fin.sum_univ_three]
  rw [h0, o0, h1, o1, h2, o2,
    show Real.pi - α = ((2 : ℤ) : ℝ) * Real.pi + ((-2 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; ring,
    show Real.pi - β = ((-1 : ℤ) : ℝ) * Real.pi + ((3 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith,
    show Real.pi - (2 * α + β) = ((1 : ℤ) : ℝ) * Real.pi + ((-1 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith,
    GridChar.rank2_chi, GridChar.rank2_chi, GridChar.rank2_chi]
theorem threeAlpha_tileValue_minus (T : Tri) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : T.ThreeAlphaData α β a b c) : (chiMinus α hα).tileValue T = a + b + c := by
  unfold chiMinus
  rw [threeAlpha_tileValue T hα hrel h 1, if_pos (by decide), if_pos (by decide),
    if_pos (by decide)]
  ring
end Erdos634.Geometry
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
theorem tile_angle_dichotomy_at_vertex (D : Dissection N) (k : Fin 3) {i : Fin N}
    (hi : D.target.pts k ∈ (D.tile i).carrier) :
    (∃ j : Fin 3, D.target.pts k = (D.tile i).pts j ∧
        (D.tile i).localAngle (D.target.pts k)
          = cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))) ∨
    (D.tile i).localAngle (D.target.pts k) = Real.pi := by
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) (D.target.pts k) with
    hvertex | h2pi | hpi | h0
  · exact Or.inl hvertex
  · exact absurd h2pi (localAngle_ne_two_pi_of_not_mem_interior (D.target_vertex_not_interior_tile k i))
  · exact Or.inr hpi
  · exact absurd h0 (Erdos634.MarchFlank.localAngle_ne_zero_of_mem _ hi)
open Erdos634.TilePlacement in
theorem congruentDissection_localAngle_mem (D : CongruentDissection N) (α β γ : ℝ)
    (hα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts k) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) := by
  classical
  by_cases hi : D.target.pts k ∈ (D.tile i).carrier
  · rcases D.toDissection.tile_angle_dichotomy_at_vertex k hi with ⟨j, hjp, hjeq⟩ | hpi
    · obtain ⟨m, hm⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
      rw [hjeq, hm]
      have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hcases with rfl | rfl | rfl
      · left; rw [← hα]; congr 1
      · right; left; rw [← hβ]; congr 1
      · right; right; left; rw [← hγ]; congr 1
    · simp [hpi]
  · 
    have h0 : (D.tile i).localAngle (D.target.pts k) = 0 := by
      classical
      rw [Erdos634.Geometry.Tri.localAngle]
      split
      · rename_i hv
        have hvmem : (D.target.pts k) ∈ Set.range (D.tile i).pts := ⟨hv.choose, hv.choose_spec.symm⟩
        exact absurd (subset_convexHull ℝ _ hvmem) hi
      · split
        · rename_i hall
          have hint : D.target.pts k ∈ interior (D.tile i).carrier :=
            (D.tile i).mem_interior_iff_coord_pos _ |>.mpr hall
          exact absurd (interior_subset hint) hi
        · split
          · rename_i hedge
            obtain ⟨kk, hkk1, hkk2⟩ := hedge
            have hmem : D.target.pts k ∈ (D.tile i).carrier := by
              rw [(D.tile i).carrier_eq_nonneg_coord]
              intro j
              rcases eq_or_ne j kk with rfl | hne
              · exact hkk1.ge
              · exact (hkk2 j hne).le
            exact absurd hmem hi
          · rfl
    simp [h0]
end Erdos634.Geometry.Dissection
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
theorem law_sines (T : Tri) (j : Fin 3) :
    Real.sin (T.angleAt (j + 1)) * T.oppLen j = Real.sin (T.angleAt j) * T.oppLen (j + 1) :=
  Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T j
end Erdos634.Geometry.CaseA.LemmaV
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ}
namespace GridChar
variable (G : GridChar ℝ)
noncomputable def edgeSign (T : Tri) (k : Fin 3) : ℝ :=
  G.chi ((Real.pi - T.angleAt (k + 2) : ℝ) : Real.Angle) * G.weight (T.leftUnit k)
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
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ}
theorem Tri.angleAt_pos' (T : Tri) (j : Fin 3) : 0 < T.angleAt j :=
  Erdos634.MarchFlank.cornerAngle_pos T j
theorem Tri.oppLen_pos (T : Tri) (k : Fin 3) : 0 < T.oppLen k := by
  unfold Tri.oppLen
  have hne : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  exact dist_pos.mpr fun h => hne (T.indep.injective h)
noncomputable def chiAt (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) : GridChar ℝ :=
  GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) b anc
theorem chiAt_sq (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) :
    ∀ l ∈ (chiAt α hα b anc).L, (chiAt α hα b anc).chi l * (chiAt α hα b anc).chi l = 1 :=
  GridChar.rank2_sq _ _ _ _
theorem chiAt_mem (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) (j k : ℤ) :
    (((j : ℝ) * Real.pi + (k : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle)
      ∈ (chiAt α hα b anc).L :=
  GridChar.rank2_mem _ _ _ _ _ _
theorem chiAt_chi (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anc : Real.Angle) (j k : ℤ) :
    (chiAt α hα b anc).chi (((j : ℝ) * Real.pi + (k : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle)
      = if (j : ZMod 2) + b * (k : ZMod 2) = 0 then 1 else -1 :=
  GridChar.rank2_chi _ _ _ _ _ _
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry.A1Field
open Erdos634.Geometry Complex
open Erdos634.Geometry.CaseA.LemmaV (law_sines angle_pos angle_lt_pi)
variable {N : ℕ}
noncomputable def circD (T : Tri) : ℝ := T.oppLen 0 / Real.sin (T.angleAt 0)
theorem sin_angle_pos (T : Tri) (k : Fin 3) : 0 < Real.sin (T.angleAt k) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos T k) (angle_lt_pi T k)
theorem circD_pos (T : Tri) : 0 < circD T := by
  have h12 : T.pts 1 ≠ T.pts 2 := fun h => absurd (T.indep.injective h) (by decide)
  exact div_pos (dist_pos.mpr h12) (sin_angle_pos T 0)
theorem oppLen_eq (T : Tri) (k : Fin 3) : T.oppLen k = circD T * Real.sin (T.angleAt k) := by
  have hs := (sin_angle_pos T 0).ne'
  have h0 : Real.sin (T.angleAt 1) * T.oppLen 0 = Real.sin (T.angleAt 0) * T.oppLen 1 :=
    law_sines T 0
  have h2 := law_sines T 2
  have e : (2 : Fin 3) + 1 = 0 := rfl
  rw [e] at h2
  unfold circD
  fin_cases k
  · show T.oppLen 0 = T.oppLen 0 / Real.sin (T.angleAt 0) * Real.sin (T.angleAt 0)
    field_simp
  · show T.oppLen 1 = T.oppLen 0 / Real.sin (T.angleAt 0) * Real.sin (T.angleAt 1)
    field_simp; linarith
  · show T.oppLen 2 = T.oppLen 0 / Real.sin (T.angleAt 0) * Real.sin (T.angleAt 2)
    field_simp; linarith
end Erdos634.Geometry.A1Field
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
theorem CongruentDissection.flux_colouring (D : CongruentDissection N) (G : GridChar ℝ)
    (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1)
    (hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L)
    (hext : ∀ k, G.chi ((Real.pi - D.model.angleAt k : ℝ) : Real.Angle) = 1) :
    ∃ ε : Fin N → ℤ, D.toDissection.ProperColouring ε ∧
      (∀ i, (D.tile i).flux G.weight = (ε i : ℝ) * G.tileValue D.model) ∧
      D.target.flux G.weight = ((∑ i, ε i : ℤ) : ℝ) * G.tileValue D.model := by
  have hang : ∀ i k, ∃ m, (D.tile i).angleAt k = D.model.angleAt m := by
    intro i k
    obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
    exact ⟨σ k, (hσ k).1⟩
  have hi : ∀ i k, (((D.tile i).angleAt k : ℝ) : Real.Angle) ∈ G.L := by
    intro i k
    obtain ⟨m, hm⟩ := hang i k
    rw [hm]; exact hmodel m
  have hie : ∀ i k, G.chi ((Real.pi - (D.tile i).angleAt k : ℝ) : Real.Angle) = 1 := by
    intro i k
    obtain ⟨m, hm⟩ := hang i k
    rw [hm]; exact hext m
  have hw : ∀ i, G.weight ((D.tile i).leftUnit 0) = 1 ∨ G.weight ((D.tile i).leftUnit 0) = -1 := by
    intro i
    have := G.val_sq hsq ((D.tile i).leftUnit 0).angle
    exact mul_self_eq_one_iff.mp this
  let ε : Fin N → ℤ := fun i => if G.weight ((D.tile i).leftUnit 0) = 1 then 1 else -1
  have hε : ∀ i, ((ε i : ℤ) : ℝ) = G.weight ((D.tile i).leftUnit 0) := by
    intro i
    by_cases h1 : G.weight ((D.tile i).leftUnit 0) = 1
    · show (((if G.weight ((D.tile i).leftUnit 0) = 1 then 1 else -1 : ℤ)) : ℝ) = _
      rw [if_pos h1, h1]; norm_num
    · rcases hw i with h2 | h2
      · exact absurd h2 h1
      · show (((if G.weight ((D.tile i).leftUnit 0) = 1 then 1 else -1 : ℤ)) : ℝ) = _
        rw [if_neg h1, h2]; norm_num
  have hε1 : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    by_cases h1 : G.weight ((D.tile i).leftUnit 0) = 1
    · left; exact if_pos h1
    · right; exact if_neg h1
  have hflux : ∀ i, (D.tile i).flux G.weight = (ε i : ℝ) * G.tileValue D.model := by
    intro i
    rw [(D.tile i).flux_eq_edgeSign G hsq (hi i) 0, G.tileValue_congr (D.tiles_congruent i), hε]
    unfold GridChar.edgeSign
    rw [hie i (0 + 2), one_mul]
  refine ⟨ε, ⟨hε1, ?_⟩, hflux, ?_⟩
  · intro i j hadj
    obtain ⟨k, l, hkl⟩ := hadj.leftUnit_neg
    have hjl : G.weight ((D.tile j).leftUnit l) = G.weight ((D.tile j).leftUnit 0) :=
      (D.tile j).weight_const G (hi j) (hie j) l
    have hik : G.weight ((D.tile i).leftUnit k) = G.weight ((D.tile i).leftUnit 0) :=
      (D.tile i).weight_const G (hi i) (hie i) k
    have h : G.weight ((D.tile j).leftUnit 0) = - G.weight ((D.tile i).leftUnit 0) := by
      rw [← hjl, ← hik, hkl, G.weight_odd]
    have hr : ((ε j : ℤ) : ℝ) = - ((ε i : ℤ) : ℝ) := by rw [hε, hε, h]
    have : ε j = - ε i := by exact_mod_cast hr
    omega
  · rw [← D.flux_cancel G.weight G.weight_odd, Finset.sum_congr rfl fun i _ => hflux i,
      ← Finset.sum_mul]
    push_cast
    rfl
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
theorem Dissection.colouring_unique {D : Dissection N} (hc : D.AdjConnected) {ε ε' : Fin N → ℤ}
    (h : D.ProperColouring ε) (h' : D.ProperColouring ε') :
    ε' = ε ∨ ε' = fun i => - ε i := by
  have key : ∀ i j, ε' i * ε i = ε' j * ε j := by
    intro i j
    induction hc i j with
    | refl => rfl
    | @tail b c _ hstep ih =>
      have e1 := h.2 b c hstep
      have e2 := h'.2 b c hstep
      rw [ih, e1, e2]; ring
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; left; funext i; exact i.elim0
  · let i0 : Fin N := ⟨0, hN⟩
    have hp : ∀ i, ε' i * ε i = ε' i0 * ε i0 := fun i => key i i0
    rcases h.1 i0 with a | a <;> rcases h'.1 i0 with b | b
    · left; funext i; have := hp i; rw [a, b] at this
      rcases h.1 i with c | c <;> rcases h'.1 i with d | d <;> simp_all
    · right; funext i; have := hp i; rw [a, b] at this
      rcases h.1 i with c | c <;> rcases h'.1 i with d | d <;> simp_all
    · right; funext i; have := hp i; rw [a, b] at this
      rcases h.1 i with c | c <;> rcases h'.1 i with d | d <;> simp_all
    · left; funext i; have := hp i; rw [a, b] at this
      rcases h.1 i with c | c <;> rcases h'.1 i with d | d <;> simp_all
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
theorem Dissection.colouring_unique' (D : Dissection N) {ε ε' : Fin N → ℤ}
    (h : D.ProperColouring ε) (h' : D.ProperColouring ε') :
    ε' = ε ∨ ε' = fun i => - ε i :=
  Dissection.colouring_unique D.adjConnected h h'
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.BeesonColoring
open Erdos634.Geometry
variable {N : ℕ}
theorem model_abc_pos {T : Tri} {α β a b c : ℝ} (h : T.ThreeAlphaData α β a b c) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < α ∧ 0 < β := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  exact ⟨o0 ▸ T.oppLen_pos (σ 0), o1 ▸ T.oppLen_pos (σ 1), o2 ▸ T.oppLen_pos (σ 2),
    h0 ▸ T.angleAt_pos' (σ 0), h1 ▸ T.angleAt_pos' (σ 1)⟩
end Erdos634.BeesonColoring
end

section
open scoped Classical
namespace Erdos634.BeesonColoring
open Erdos634.Geometry
variable {N : ℕ}
theorem model_hext (T : Tri) {α β a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.ThreeAlphaData α β a b c) (hrel : 3 * α + 2 * β = Real.pi) :
    ∀ k, (chiAt α hα 1 0).chi ((Real.pi - T.angleAt k : ℝ) : Real.Angle) = 1 := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  intro k
  obtain ⟨m, rfl⟩ := σ.surjective k
  have hk : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hk with rfl | rfl | rfl
  · rw [h0, show Real.pi - α = ((2 : ℤ) : ℝ) * Real.pi + ((-2 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; ring, chiAt_chi, if_pos (by decide)]
  · rw [h1, show Real.pi - β = ((-1 : ℤ) : ℝ) * Real.pi + ((3 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith, chiAt_chi, if_pos (by decide)]
  · rw [h2, show Real.pi - (2 * α + β) = ((1 : ℤ) : ℝ) * Real.pi + ((-1 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith, chiAt_chi, if_pos (by decide)]
end Erdos634.BeesonColoring
end

section
open scoped Classical
namespace Erdos634.BeesonColoring
open Erdos634.Geometry
def Triple3 (x y z a b c : ℝ) : Prop :=
  (x = a ∧ y = b ∧ z = c) ∨ (x = a ∧ y = c ∧ z = b) ∨ (x = b ∧ y = a ∧ z = c) ∨
  (x = b ∧ y = c ∧ z = a) ∨ (x = c ∧ y = a ∧ z = b) ∨ (x = c ∧ y = b ∧ z = a)
def FiveShapes (x y z α β : ℝ) : Prop :=
  Triple3 x y z α (α + 2 * β) α ∨ Triple3 x y z β (3 * α) β ∨
  Triple3 x y z (α + β) α (α + β) ∨ Triple3 x y z (2 * α) β (α + β) ∨
  Triple3 x y z (2 * α) α (2 * β)
theorem three_shapes_arith {α β θ0 θ1 θ2 : ℝ} (a0 a1 a2 b0 b1 b2 : ℕ)
    (h0 : θ0 = a0 * α + b0 * β) (h1 : θ1 = a1 * α + b1 * β) (h2 : θ2 = a2 * α + b2 * β)
    (hP : a0 + a1 + a2 = 3) (hQ : b0 + b1 + b2 = 2)
    (n0 : 1 ≤ a0 + b0) (n1 : 1 ≤ a1 + b1) (n2 : 1 ≤ a2 + b2) :
    Triple3 θ0 θ1 θ2 α β (2 * α + β) ∨ FiveShapes θ0 θ1 θ2 α β := by
  have ha2 : a2 = 3 - a0 - a1 := by omega
  have hb2 : b2 = 2 - b0 - b1 := by omega
  have a0le : a0 ≤ 3 := by omega
  have a1le : a1 ≤ 3 := by omega
  have b0le : b0 ≤ 2 := by omega
  have b1le : b1 ≤ 2 := by omega
  subst ha2 hb2 h0 h1 h2
  interval_cases a0 <;> interval_cases a1 <;> interval_cases b0 <;> interval_cases b1 <;>
    first | (exfalso; omega) | simp [Triple3, FiveShapes]
theorem one_each_arith {α β γ θ0 θ1 θ2 : ℝ} (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℕ)
    (h0 : θ0 = a0 * α + b0 * β + c0 * γ) (h1 : θ1 = a1 * α + b1 * β + c1 * γ)
    (h2 : θ2 = a2 * α + b2 * β + c2 * γ)
    (hP : a0 + a1 + a2 = 1) (hQ : b0 + b1 + b2 = 1) (hR : c0 + c1 + c2 = 1)
    (n0 : 1 ≤ a0 + b0 + c0) (n1 : 1 ≤ a1 + b1 + c1) (n2 : 1 ≤ a2 + b2 + c2) :
    Triple3 θ0 θ1 θ2 α β γ := by
  have : a0 ≤ 1 := by omega
  have : a1 ≤ 1 := by omega
  have : b0 ≤ 1 := by omega
  have : b1 ≤ 1 := by omega
  have : c0 ≤ 1 := by omega
  have : c1 ≤ 1 := by omega
  have ha2 : a2 = 1 - a0 - a1 := by omega
  have hb2 : b2 = 1 - b0 - b1 := by omega
  have hc2 : c2 = 1 - c0 - c1 := by omega
  subst ha2 hb2 hc2 h0 h1 h2
  interval_cases a0 <;> interval_cases a1 <;> interval_cases b0 <;> interval_cases b1 <;>
    interval_cases c0 <;> interval_cases c1 <;>
    first | (exfalso; omega) | simp [Triple3]
noncomputable def vcount {N : ℕ} (D : CongruentDissection N) (k : Fin 3) (x : ℝ) : ℕ :=
  ({i | (D.tile i).localAngle (D.target.pts k) = x} : Finset (Fin N)).card
theorem localAngle_mem_3a {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (h : D.model.ThreeAlphaData α β a b c) (k : Fin 3) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts k) ∈ ({α, β, 2 * α + β, Real.pi, 0} : Finset ℝ) := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  have key : ∀ (σ : Equiv.Perm (Fin 3)) (i : Fin 3),
      (σ (i + 1) = σ i + 1 ∧ σ (i + 2) = σ i + 2) ∨ (σ (i + 1) = σ i + 2 ∧ σ (i + 2) = σ i + 1) := by
    decide
  have rel : ∀ i : Fin 3, cornerAngle ((D.model.relabel σ).pts (i + 1)) ((D.model.relabel σ).pts i)
      ((D.model.relabel σ).pts (i + 2)) = D.model.angleAt (σ i) := by
    intro i
    show cornerAngle (D.model.pts (σ (i + 1))) (D.model.pts (σ i)) (D.model.pts (σ (i + 2))) = _
    rcases key σ i with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; rfl
    · rw [e1, e2]; unfold Tri.angleAt
      exact EuclideanGeometry.angle_comm _ _ _
  exact Erdos634.Geometry.Dissection.congruentDissection_localAngle_mem (D.relabelModel σ) α β (2 * α + β)
    ((rel 0).trans h0) ((rel 1).trans h1) ((rel 2).trans h2) k i
theorem corner_fig {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) (k : Fin 3) :
    vcount D k Real.pi = 0 ∧
    (vcount D k α : ℝ) * α + (vcount D k β : ℝ) * β + (vcount D k (2 * α + β) : ℝ) * (2 * α + β)
      = D.target.angleAt k := by
  obtain ⟨ha, hb, -, hαpos, hβpos⟩ := model_abc_pos h
  have hαβ : α ≠ β := fun e => hirr ⟨1 / 5, by push_cast; linarith⟩
  have hαπ : α ≠ Real.pi := by intro e; linarith
  have hβπ : β ≠ Real.pi := by intro e; linarith
  have hπ0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hm := Erdos634.TilePlacement.corner_multiplicities D.toDissection α β (2 * α + β) hαβ
    (by intro e; linarith) hαπ hαpos.ne' (by intro e; linarith) hβπ hβpos.ne'
    (by intro e; linarith) (by intro e; linarith) hπ0 k (fun i => localAngle_mem_3a D h k i)
  have hpos := D.target.angleAt_pos' k
  have hsum := D.target.angleAt_sum
  have hlt : D.target.angleAt k < Real.pi := by
    have := D.target.angleAt_pos' 0
    have := D.target.angleAt_pos' 1
    have := D.target.angleAt_pos' 2
    fin_cases k <;> simp <;> linarith
  have hpi : vcount D k Real.pi = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ (vcount D k Real.pi : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have hp : (vcount D k Real.pi : ℝ) * Real.pi ≥ Real.pi := by nlinarith [Real.pi_pos]
    have := mul_nonneg (Nat.cast_nonneg (vcount D k α) : (0:ℝ) ≤ _) hαpos.le
    have := mul_nonneg (Nat.cast_nonneg (vcount D k β) : (0:ℝ) ≤ _) hβpos.le
    have := mul_nonneg (Nat.cast_nonneg (vcount D k (2 * α + β)) : (0:ℝ) ≤ _) (by linarith : (0:ℝ) ≤ 2 * α + β)
    unfold vcount at *
    change _ = D.target.angleAt k at hm
    linarith
  refine ⟨hpi, ?_⟩
  unfold vcount at hpi ⊢
  have := hm
  rw [hpi] at this
  change _ = D.target.angleAt k at this
  simpa using this
theorem corner_totals {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    (∑ k, vcount D k α) + 2 * (∑ k, vcount D k (2 * α + β)) = 3 ∧
    (∑ k, vcount D k β) + (∑ k, vcount D k (2 * α + β)) = 2 := by
  have e0 := corner_fig D hirr hrel h 0
  have e1 := corner_fig D hirr hrel h 1
  have e2 := corner_fig D hirr hrel h 2
  have hsum := D.target.angleAt_sum
  have hx : ((∑ k, vcount D k α : ℕ) : ℝ) * α + ((∑ k, vcount D k β : ℕ) : ℝ) * β
      + ((∑ k, vcount D k (2 * α + β) : ℕ) : ℝ) * (2 * α + β)
      = ((3 : ℤ) : ℝ) * α + ((2 : ℤ) : ℝ) * β := by
    simp only [Fin.sum_univ_three]
    push_cast
    linarith [e0.2, e1.2, e2.2]
  obtain ⟨u, v⟩ := vertex_multiplicities hrel hirr _ _ _ 3 2 hx
  constructor <;> omega
theorem lemma6 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β) ∨
    ((∀ k, vcount D k (2 * α + β) = 0) ∧ (∑ k, vcount D k α) = 3 ∧ (∑ k, vcount D k β) = 2 ∧
      (∑ k, (vcount D k α + vcount D k β)) = 5) := by
  obtain ⟨hP, hQ⟩ := corner_totals D hirr hrel h
  by_cases hJ : (∑ k, vcount D k (2 * α + β)) = 0
  · right
    have hz : ∀ k, vcount D k (2 * α + β) = 0 := fun k => by
      have := Finset.sum_eq_zero_iff.mp hJ k (Finset.mem_univ k)
      exact this
    refine ⟨hz, by omega, by omega, ?_⟩
    rw [Finset.sum_add_distrib]; omega
  · left
    have hJ1 : (∑ k, vcount D k (2 * α + β)) = 1 := by omega
    have e0 := corner_fig D hirr hrel h 0
    have e1 := corner_fig D hirr hrel h 1
    have e2 := corner_fig D hirr hrel h 2
    obtain ⟨ha, hb, -, hαpos, hβpos⟩ := model_abc_pos h
    have npos : ∀ k : Fin 3, 1 ≤ vcount D k α + vcount D k β + vcount D k (2 * α + β) := by
      intro k
      by_contra hn
      have h0 : vcount D k α = 0 := by omega
      have h1 : vcount D k β = 0 := by omega
      have h2 : vcount D k (2 * α + β) = 0 := by omega
      have := (corner_fig D hirr hrel h k).2
      rw [h0, h1, h2] at this
      have := D.target.angleAt_pos' k
      simp_all
    simp only [Fin.sum_univ_three] at hP hQ hJ1
    exact one_each_arith _ _ _ _ _ _ _ _ _ e0.2.symm e1.2.symm e2.2.symm (by omega) (by omega) hJ1
      (npos 0) (npos 1) (npos 2)
theorem lemma11 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    FiveShapes (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β ∧
    (∑ k, vcount D k α) = 3 ∧ (∑ k, vcount D k β) = 2 ∧ (∀ k, vcount D k (2 * α + β) = 0) ∧
    (∀ k, 1 ≤ vcount D k α + vcount D k β) := by
  rcases lemma6 D hirr hrel h with hs | ⟨hz, hP, hQ, -⟩
  · exact absurd hs hns
  · have e0 := corner_fig D hirr hrel h 0
    have e1 := corner_fig D hirr hrel h 1
    have e2 := corner_fig D hirr hrel h 2
    have npos : ∀ k : Fin 3, 1 ≤ vcount D k α + vcount D k β := by
      intro k
      by_contra hn
      have h0 : vcount D k α = 0 := by omega
      have h1 : vcount D k β = 0 := by omega
      have := (corner_fig D hirr hrel h k).2
      rw [h0, h1, hz k] at this
      have := D.target.angleAt_pos' k
      simp_all
    simp only [Fin.sum_univ_three] at hP hQ
    have f0 := e0.2; have f1 := e1.2; have f2 := e2.2
    rw [hz 0] at f0; rw [hz 1] at f1; rw [hz 2] at f2
    have := three_shapes_arith _ _ _ _ _ _ (by simpa using f0.symm) (by simpa using f1.symm)
      (by simpa using f2.symm) hP hQ (npos 0) (npos 1) (npos 2)
    refine ⟨?_, by simpa [Fin.sum_univ_three] using hP, by simpa [Fin.sum_univ_three] using hQ, hz, npos⟩
    rcases this with h6 | h5
    · exact absurd h6 hns
    · exact h5
end Erdos634.BeesonColoring
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
namespace Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry Erdos634.TilePlacement
def IrrPi (x : ℝ) : Prop := ¬ ∃ r : ℚ, x = (r : ℝ) * Real.pi
def TgtAngles {N : ℕ} (D : CongruentDissection N) (x y z : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), D.target.angleAt (σ 0) = x ∧ D.target.angleAt (σ 1) = y ∧
    D.target.angleAt (σ 2) = z
def SimilarTM {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ (μ : ℝ) (τ : Equiv.Perm (Fin 3)), ∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧
    D.target.oppLen k = μ * D.model.oppLen (τ k)
end Erdos634.Draft.TheoremPConditional
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
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
end Erdos634.Draft.LemmaCFinal
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCFinal
namespace Erdos634.Draft.LaczFormal
def TileAngles {N : ℕ} (D : CongruentDissection N) (x y z : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), D.model.angleAt (σ 0) = x ∧ D.model.angleAt (σ 1) = y ∧
    D.model.angleAt (σ 2) = z
end Erdos634.Draft.LaczFormal
end

section
open scoped BigOperators Classical
namespace Erdos634.Draft.LaczFormal
def excl_6 : List (ℕ × ℕ × ℕ) := [(1, 1, 4), (1, 4, 1), (4, 1, 1), (1, 2, 3), (1, 3, 2), (2, 1, 3), (2, 3, 1), (3, 1, 2), (3, 2, 1)]
def excl_8 : List (ℕ × ℕ × ℕ) := [(1, 2, 5), (1, 5, 2), (2, 1, 5), (2, 5, 1), (5, 1, 2), (5, 2, 1)]
def excl_10 : List (ℕ × ℕ × ℕ) := [(1, 2, 7), (1, 7, 2), (2, 1, 7), (2, 7, 1), (7, 1, 2), (7, 2, 1), (1, 3, 6), (1, 6, 3), (3, 1, 6), (3, 6, 1), (6, 1, 3), (6, 3, 1)]
end Erdos634.Draft.LaczFormal
end

section
open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry.CaseA.LemmaV (angle_pos angle_lt_pi)
namespace Erdos634.Draft.LaczFormal
variable {N : ℕ}
theorem similar_of_same_angles (D : CongruentDissection N) {x y z : ℝ} (hM : TileAngles D x y z)
    (hT : TgtAngles D x y z) : SimilarTM D := by
  obtain ⟨σ, m0, m1, m2⟩ := hM
  obtain ⟨τ, t0, t1, t2⟩ := hT
  have hm : ∀ k, D.model.angleAt (σ k) = (![x, y, z] : Fin 3 → ℝ) k := by
    intro k; fin_cases k <;> simp [m0, m1, m2]
  have ht : ∀ k, D.target.angleAt (τ k) = (![x, y, z] : Fin 3 → ℝ) k := by
    intro k; fin_cases k <;> simp [t0, t1, t2]
  have hang : ∀ j, D.target.angleAt j = D.model.angleAt ((τ.symm.trans σ) j) := by
    intro j
    simp only [Equiv.trans_apply]
    rw [hm, ← ht, Equiv.apply_symm_apply]
  set μ := A1Field.circD D.target / A1Field.circD D.model
  have hcm := (A1Field.circD_pos D.model).ne'
  refine ⟨μ, τ.symm.trans σ, fun j => ⟨hang j, ?_⟩⟩
  rw [A1Field.oppLen_eq D.target j, A1Field.oppLen_eq D.model ((τ.symm.trans σ) j), hang j]
  simp only [μ]; field_simp
end Erdos634.Draft.LaczFormal
end

section
namespace Erdos634.MirrorGauge
open Erdos634.Geometry
noncomputable def mirrorPt (p : Plane) : Plane := WithLp.toLp 2 ![p 0, - p 1]
@[simp] theorem mirrorPt_zero (p : Plane) : mirrorPt p 0 = p 0 := rfl
@[simp] theorem mirrorPt_one (p : Plane) : mirrorPt p 1 = - p 1 := rfl
@[simp] theorem mirrorPt_involutive (p : Plane) : mirrorPt (mirrorPt p) = p := by
  ext i; fin_cases i <;> simp
theorem mirrorPt_injective : Function.Injective mirrorPt := fun p q h => by
  have := congrArg mirrorPt h; simpa using this
noncomputable def mirrorL : Plane →ₗ[ℝ] Plane where
  toFun := mirrorPt
  map_add' := by intro x y; ext i; fin_cases i <;> simp; ring
  map_smul' := by intro c x; ext i; fin_cases i <;> simp
@[simp] theorem mirrorL_apply (p : Plane) : mirrorL p = mirrorPt p := rfl
theorem mirrorPt_dist (p q : Plane) : dist (mirrorPt p) (mirrorPt q) = dist p q := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  fin_cases i
  · simp
  · show dist (mirrorPt p 1) (mirrorPt q 1) ^ 2 = dist (p 1) (q 1) ^ 2
    rw [mirrorPt_one, mirrorPt_one, dist_neg_neg]
noncomputable def mirrorIso : Plane ≃ᵢ Plane where
  toFun := mirrorPt
  invFun := mirrorPt
  left_inv := mirrorPt_involutive
  right_inv := mirrorPt_involutive
  isometry_toFun := Isometry.of_dist_eq mirrorPt_dist
@[simp] theorem mirrorIso_apply (p : Plane) : mirrorIso p = mirrorPt p := rfl
noncomputable def mirrorHomeo : Homeomorph Plane Plane := mirrorIso.toHomeomorph
@[simp] theorem mirrorHomeo_apply (p : Plane) : mirrorHomeo p = mirrorPt p := rfl
noncomputable def Tri.mirror (T : Tri) : Tri where
  pts := mirrorPt ∘ T.pts
  indep := T.indep.map' mirrorL.toAffineMap mirrorPt_injective
@[simp] theorem Tri.mirror_pts (T : Tri) (k : Fin 3) : (Tri.mirror T).pts k = mirrorPt (T.pts k) :=
  rfl
theorem Tri.det_mirror (T : Tri) : (Tri.mirror T).det = - T.det := by
  simp only [Erdos634.Geometry.Tri.det, Tri.mirror_pts]
  have h0 : ∀ u v : Plane, (mirrorPt u - mirrorPt v) 0 = (u - v) 0 := by
    intro u v; simp
  have h1 : ∀ u v : Plane, (mirrorPt u - mirrorPt v) 1 = - ((u - v) 1) := by
    intro u v; simp; ring
  rw [h0, h0, h1, h1]; ring
theorem Tri.carrier_mirror (T : Tri) :
    (Tri.mirror T).carrier = mirrorPt '' T.carrier := by
  have hcomp : ⇑(mirrorL.toAffineMap) = mirrorPt := rfl
  rw [Erdos634.Geometry.Tri.carrier, Erdos634.Geometry.Tri.carrier, ← hcomp,
    AffineMap.image_convexHull]
  congr 1
  rw [Tri.mirror, ← Set.range_comp]
  rfl
theorem Tri.congruent_self_mirror (T : Tri) : T.Congruent (Tri.mirror T) :=
  ⟨mirrorIso, Equiv.refl _, fun _ => rfl⟩
noncomputable def Dissection.mirror {N : ℕ} (D : Dissection N) : Dissection N where
  target := Tri.mirror D.target
  tile := fun i => Tri.mirror (D.tile i)
  covers := by
    have : (⋃ i, mirrorPt '' (D.tile i).carrier) = mirrorPt '' (⋃ i, (D.tile i).carrier) := by
      rw [Set.image_iUnion]
    simp only [Tri.carrier_mirror]
    rw [this, D.covers]
  interiors_disjoint := by
    intro i j hij
    have hd : Disjoint (interior (D.tile i).carrier) (interior (D.tile j).carrier) :=
      D.interiors_disjoint hij
    simp only [Tri.carrier_mirror]
    have hi : ∀ k, interior (mirrorPt '' (D.tile k).carrier)
        = mirrorPt '' interior (D.tile k).carrier := by
      intro k
      have := mirrorHomeo.image_interior (D.tile k).carrier
      have hc : ⇑mirrorHomeo = mirrorPt := rfl
      rw [hc] at this
      exact this.symm
    rw [hi, hi]
    exact (Set.disjoint_image_iff mirrorPt_injective).mpr hd
@[simp] theorem Dissection.mirror_tile {N : ℕ} (D : Dissection N) (i : Fin N) :
    (Dissection.mirror D).tile i = Tri.mirror (D.tile i) := rfl
noncomputable def CongruentDissection.mirror {N : ℕ} (D : CongruentDissection N) :
    CongruentDissection N where
  toDissection := Dissection.mirror D.toDissection
  model := D.model
  tiles_congruent := fun i =>
    (Tri.congruent_self_mirror (D.tile i)).symm.trans (D.tiles_congruent i)
@[simp] theorem CongruentDissection.mirror_tile {N : ℕ} (D : CongruentDissection N) (i : Fin N) :
    (CongruentDissection.mirror D).tile i = Tri.mirror (D.tile i) := rfl
@[simp] theorem CongruentDissection.mirror_model {N : ℕ} (D : CongruentDissection N) :
    (CongruentDissection.mirror D).model = D.model := rfl
def wordMirror (n : ℕ) (w : ℕ → Bool) : ℕ → Bool := fun j => ! w (n - j)
@[simp] theorem first_mirror (n : ℕ) (w : ℕ → Bool) : wordMirror n w 0 = ! w n := by
  simp [wordMirror]
@[simp] theorem last_mirror (n : ℕ) (w : ℕ → Bool) : wordMirror n w n = ! w 0 := by
  simp [wordMirror]
end Erdos634.MirrorGauge
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
end Defs
def AnglesSep {N : ℕ} (D : CongruentDissection N) : Prop :=
  (∀ j, ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j ≠ 0) ∧
    Function.Injective ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi]
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
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry MeasureTheory
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
open Erdos634.Geometry EuclideanGeometry
section Counts
variable {N : ℕ} (D : CongruentDissection N)
theorem angleCount_pos {P : Plane} {θ : ℝ} {i : Fin N} (hi : (D.tile i).localAngle P = θ) :
    1 ≤ angleCount D P θ :=
  Finset.card_pos.mpr ⟨i, by simp [hi]⟩
theorem ne_of_angleCount_zero {P : Plane} {θ : ℝ} (h : angleCount D P θ = 0) (i : Fin N) :
    (D.tile i).localAngle P ≠ θ := fun hi => by
  have := angleCount_pos D hi; omega
end Counts
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
def edgeType (φ : ℝ) (e : Fin N × Fin 3) : Prop :=
  (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = φ
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
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry Set
theorem side_has_edge_sep {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D) (θ : ℝ)
    (hθ : θ = tileα D ∨ θ = tileβ D ∨ θ = tileγ D) (i : Fin 3) (part : Finset (Fin N × Fin 3))
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
  have hcorner : ∀ e ∈ part, (D.tile e.1).localAngle ((D.tile e.1).pts e.2) = θ ∨
      (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 1)) = θ := by
    intro e he
    have hcnt := tile_angle_count_sep D hsep e.1
    have hcard : (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile e.1).pts (k + 1))
        ((D.tile e.1).pts k) ((D.tile e.1).pts (k + 2)) = θ).card = 1 := by
      rcases hθ with rfl | rfl | rfl
      · exact hcnt.1
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
end TriangleTiling
end

section
namespace TriangleTiling.Laczkovich
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
variable {N : ℕ} (D : CongruentDissection N)
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
theorem tgtAngles_of_eq {x y z x' y' z' : ℝ} (h : TgtAngles D x y z) (hx : x = x') (hy : y = y')
    (hz : z = z') : TgtAngles D x' y' z' := by
  subst hx hy hz; exact h
end TriangleTiling.Laczkovich
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
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
def TileSides (α β γ a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    D.model.angleAt (σ 0) = α ∧ D.model.angleAt (σ 1) = β ∧ D.model.angleAt (σ 2) = γ ∧
    D.model.oppLen (σ 0) = a ∧ D.model.oppLen (σ 1) = b ∧ D.model.oppLen (σ 2) = c
def TileAt (k : Fin 3) (i : Fin N) : Prop :=
  ∃ l : Fin 3, (D.tile i).pts l = D.target.pts k
noncomputable def tilesAt (k : Fin 3) : ℕ :=
  open Classical in ({i | TileAt D k i} : Finset (Fin N)).card
noncomputable def anglesAt (k : Fin 3) (x : ℝ) : ℕ :=
  open Classical in
  ({i | ∃ l, (D.tile i).pts l = D.target.pts k ∧ (D.tile i).angleAt l = x} : Finset (Fin N)).card
def AtBOnAB (i : Fin N) : Prop :=
  ∃ l l' : Fin 3, l ≠ l' ∧ (D.tile i).pts l = D.target.pts 1 ∧
    (D.tile i).pts l' ∈ segment ℝ (D.target.pts 0) (D.target.pts 1)
noncomputable def baseDir : Real.Angle := (D.target.leftUnit 0).angle
noncomputable def Phi1 (δ : ℝ) (θ₀ θ : Real.Angle) : ℝ :=
  open Classical in
  if ∃ n : ℤ, θ = θ₀ + ((n * δ : ℝ) : Real.Angle) then 1
  else if ∃ n : ℤ, θ = θ₀ + ((n * δ + Real.pi : ℝ) : Real.Angle) then -1
  else 0
noncomputable def Phi2 (δ : ℝ) (θ₀ θ : Real.Angle) : ℝ :=
  open Classical in
  if h : ∃ n : ℤ, θ = θ₀ + ((n * δ : ℝ) : Real.Angle) then (h.choose.negOnePow : ℤ)
  else if h : ∃ n : ℤ, θ = θ₀ + ((n * δ + Real.pi : ℝ) : Real.Angle) then
    -((h.choose.negOnePow : ℤ) : ℝ)
  else 0
noncomputable def PhiR (Φ : Real.Angle → ℝ) (R : Tri) : ℝ := R.flux fun d => Φ d.angle
noncomputable def circumdiam (T : Tri) : ℝ := T.oppLen 0 / Real.sin (T.angleAt 0)
noncomputable def Lam : ℝ := circumdiam D.target / circumdiam D.model
def RationalTile (a b c : ℝ) : Prop :=
  (∃ q : ℚ, a / c = q) ∧ (∃ q : ℚ, b / c = q) ∧ (∃ q : ℚ, a / b = q)
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry Erdos634.BeesonColoring
variable {N : ℕ} (D : CongruentDissection N)
theorem localAngle_pts (T : Tri) (l : Fin 3) : T.localAngle (T.pts l) = T.angleAt l :=
  T.localAngle_vertex l
theorem vertex_of_localAngle (T : Tri) {p : Plane} {x : ℝ} (h : T.localAngle p = x)
    (h0 : x ≠ 0) (hπ : x ≠ Real.pi) (h2π : x ≠ 2 * Real.pi) : ∃ l, T.pts l = p := by
  classical
  unfold Tri.localAngle at h
  split_ifs at h with h1
  · exact ⟨h1.choose, h1.choose_spec.symm⟩
  · exact absurd h.symm h2π
  · exact absurd h.symm hπ
  · exact absurd h.symm h0
theorem localAngle_iff (T : Tri) (p : Plane) {x : ℝ} (h0 : x ≠ 0) (hπ : x ≠ Real.pi)
    (h2π : x ≠ 2 * Real.pi) : T.localAngle p = x ↔ ∃ l, T.pts l = p ∧ T.angleAt l = x := by
  constructor
  · intro h
    obtain ⟨l, rfl⟩ := vertex_of_localAngle T h h0 hπ h2π
    exact ⟨l, rfl, (localAngle_pts T l).symm.trans h⟩
  · rintro ⟨l, rfl, hl⟩
    exact (localAngle_pts T l).trans hl
variable {α β a b c : ℝ}
theorem tile_threeAlpha (h : D.model.ThreeAlphaData α β a b c) (i : Fin N) :
    (D.tile i).ThreeAlphaData α β a b c := by
  obtain ⟨σ, h0, h0', h1, h1', h2, h2'⟩ := h
  obtain ⟨τ, hτ⟩ := (D.tiles_congruent i).exists_perm
  refine ⟨σ.trans τ.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Equiv.trans_apply, (hτ _).1, (hτ _).2, Equiv.apply_symm_apply] <;> assumption
theorem tile_angle_mem (h : D.model.ThreeAlphaData α β a b c) (i : Fin N) (l : Fin 3) :
    (D.tile i).angleAt l = α ∨ (D.tile i).angleAt l = β ∨ (D.tile i).angleAt l = 2 * α + β := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := tile_threeAlpha D h i
  obtain ⟨m, rfl⟩ := σ.surjective l
  have hm : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hm with rfl | rfl | rfl
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h2)
theorem angles_pos (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c) :
    0 < α ∧ 0 < β ∧ α < Real.pi / 3 ∧ β < Real.pi / 2 := by
  obtain ⟨-, -, -, hα, hβ⟩ := model_abc_pos h
  refine ⟨hα, hβ, by linarith, by linarith⟩
theorem vcount_eq_anglesAt (k : Fin 3) {x : ℝ} (hx0 : x ≠ 0) (hxπ : x ≠ Real.pi)
    (hx2π : x ≠ 2 * Real.pi) : vcount D k x = anglesAt D k x := by
  unfold vcount anglesAt
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact localAngle_iff _ _ hx0 hxπ hx2π
theorem perm3 (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ τ : Equiv.Perm (Fin 3), τ 0 = i ∧ τ 1 = j ∧ τ 2 = k := by
  revert i j k; decide
section Counts
variable (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel h
omit hirr in
theorem anglesAt_eq_vcount_α (k : Fin 3) : anglesAt D k α = vcount D k α := by
  obtain ⟨hα, -, hα3, -⟩ := angles_pos D hrel h
  have := Real.pi_pos
  exact (vcount_eq_anglesAt D k hα.ne' (by linarith) (by linarith)).symm
omit hirr in
theorem anglesAt_eq_vcount_β (k : Fin 3) : anglesAt D k β = vcount D k β := by
  obtain ⟨-, hβ, -, hβ2⟩ := angles_pos D hrel h
  have := Real.pi_pos
  exact (vcount_eq_anglesAt D k hβ.ne' (by linarith) (by linarith)).symm
theorem tilesAt_eq (k : Fin 3) (hz : vcount D k (2 * α + β) = 0) :
    tilesAt D k = vcount D k α + vcount D k β := by
  classical
  obtain ⟨hα, hβ, hα3, hβ2⟩ := angles_pos D hrel h
  have hπ := Real.pi_pos
  have hαβ : α ≠ β := fun e => hirr ⟨1 / 5, by push_cast; linarith⟩
  rw [anglesAt_eq_vcount_α D hrel h k |>.symm, anglesAt_eq_vcount_β D hrel h k |>.symm]
  unfold tilesAt anglesAt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    simp only [TileAt]
    constructor
    · rintro ⟨l, hl⟩
      rcases tile_angle_mem D h i l with e | e | e
      · exact Or.inl ⟨l, hl, e⟩
      · exact Or.inr ⟨l, hl, e⟩
      · exfalso
        have hγ0 : 2 * α + β ≠ 0 := by linarith
        have hγπ : 2 * α + β ≠ Real.pi := by linarith
        have hγ2π : 2 * α + β ≠ 2 * Real.pi := by linarith
        have hmem : i ∈ ({i | (D.tile i).localAngle (D.target.pts k) = 2 * α + β} :
            Finset (Fin N)) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (localAngle_iff _ _ hγ0 hγπ hγ2π).mpr ⟨l, hl, e⟩
        unfold vcount at hz
        rw [Finset.card_eq_zero] at hz
        rw [hz] at hmem
        exact Finset.notMem_empty _ hmem
    · rintro (⟨l, hl, -⟩ | ⟨l, hl, -⟩) <;> exact ⟨l, hl⟩
  · rw [Finset.disjoint_filter]
    rintro i - ⟨l, hl, e⟩ ⟨l', hl', e'⟩
    have : l = l' := (D.tile i).indep.injective (hl.trans hl'.symm)
    subst this
    exact hαβ (e.symm.trans e')
end Counts
theorem proper_neg {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) :
    D.toDissection.ProperColouring (fun i => - ε i) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rcases hε.1 i with e | e <;> simp [e]
  · have := hε.2 i j hij; simp only; omega
theorem edge_of_AtBOnAB {i : Fin N} (hi : AtBOnAB D i) :
    ∃ e : Fin 3, (D.tile i).edge e ⊆ D.target.edge 0 := by
  obtain ⟨l, l', hll', hl, hl'⟩ := hi
  have hAB : D.target.edge 0 = segment ℝ (D.target.pts 0) (D.target.pts 1) := rfl
  have hB : D.target.pts 1 ∈ segment ℝ (D.target.pts 0) (D.target.pts 1) :=
    right_mem_segment ℝ _ _
  have hcases : ∀ l l' : Fin 3, l ≠ l' → l' = l + 1 ∨ l = l' + 1 := by decide
  rcases hcases l l' hll' with e | e
  · refine ⟨l, ?_⟩
    rw [hAB, Tri.edge, ← e, hl]
    exact (convex_segment _ _).segment_subset hB hl'
  · refine ⟨l', ?_⟩
    rw [hAB, Tri.edge, ← e, hl]
    exact (convex_segment _ _).segment_subset hl' hB
section Colouring
variable (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel
omit D in
theorem indep {p q p' q' : ℕ} (e : (p : ℝ) * α + q * β = p' * α + q' * β) : p = p' ∧ q = q' := by
  have key : (((p : ℝ) - p') - 3 * ((q : ℝ) - q') / 2) * α = -(((q : ℝ) - q') / 2) * Real.pi := by
    linear_combination e - ((q : ℝ) - q') / 2 * hrel
  by_cases hc : ((p : ℝ) - p') - 3 * ((q : ℝ) - q') / 2 = 0
  · have hq : ((q : ℝ) - q') * Real.pi = 0 := by
      rw [hc, zero_mul] at key; linarith
    have hq' : (q : ℝ) = q' := by
      rcases mul_eq_zero.mp hq with e | e
      · linarith
      · exact absurd e Real.pi_ne_zero
    have hp' : (p : ℝ) = p' := by rw [hq'] at hc; linarith
    exact ⟨by exact_mod_cast hp', by exact_mod_cast hq'⟩
  · exfalso
    apply hirr
    refine ⟨-(((q : ℚ) - q') / 2) / (((p : ℚ) - p') - 3 * ((q : ℚ) - q') / 2), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hc]
    linear_combination key
omit D in
theorem chi_ext (p q : ℕ) :
    (chiAt α hirr 1 0).chi (((Real.pi - ((p : ℝ) * α + q * β)) : ℝ) : Real.Angle)
      = if Even (p + q) then -1 else 1 := by
  have hrep : Real.pi - ((p : ℝ) * α + q * β)
      = ((1 - 2 * q + p : ℤ) : ℝ) * Real.pi + ((3 * q - 2 * p : ℤ) : ℝ) * (α / 2 + Real.pi / 2) := by
    push_cast
    linear_combination (-(q : ℝ) / 2) * hrel
  rw [hrep, chiAt_chi]
  have key : ((1 - 2 * q + p : ℤ) : ZMod 2) + 1 * ((3 * q - 2 * p : ℤ) : ZMod 2)
      = (((1 - 2 * q + p) + (3 * q - 2 * p) : ℤ) : ZMod 2) := by push_cast; ring
  rw [key]
  split_ifs with h1 h2 h2
  · exfalso
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h1
    obtain ⟨r, hr⟩ := h2
    omega
  · rfl
  · rfl
  · exfalso
    apply h1
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [Nat.not_even_iff_odd] at h2
    obtain ⟨r, hr⟩ := h2
    exact ⟨(q : ℤ) - r, by omega⟩
omit D in
theorem mem_L (p q : ℕ) :
    ((((p : ℝ) * α + q * β) : ℝ) : Real.Angle) ∈ (chiAt α hirr 1 0).L := by
  have hrep : (p : ℝ) * α + q * β
      = ((2 * q - p : ℤ) : ℝ) * Real.pi + ((2 * p - 3 * q : ℤ) : ℝ) * (α / 2 + Real.pi / 2) := by
    push_cast
    linear_combination (q : ℝ) / 2 * hrel
  rw [hrep]
  exact chiAt_mem _ _ _ _ _ _
include h
theorem corner_eq (hz : ∀ k, vcount D k (2 * α + β) = 0) (k : Fin 3) :
    D.target.angleAt k = (vcount D k α : ℝ) * α + (vcount D k β : ℝ) * β := by
  have := (corner_fig D hirr hrel h k).2
  rw [hz k] at this
  push_cast at this
  linarith
theorem sign_at_B {ε : Fin N → ℤ}
    (hflux : ∀ i, (D.tile i).flux (chiAt α hirr 1 0).weight
      = (ε i : ℝ) * (chiAt α hirr 1 0).tileValue D.model)
    {i : Fin N} (hi : AtBOnAB D i) :
    (ε i : ℝ) = (chiAt α hirr 1 0).weight (D.target.leftUnit 0) := by
  obtain ⟨e, he⟩ := edge_of_AtBOnAB D hi
  have hT := tile_threeAlpha D h i
  have hdir : (D.tile i).leftUnit e = D.target.leftUnit 0 :=
    D.toDissection.eDir_of_side (e := (i, e)) he
  have hf := Tri.flux_eq_edgeSign (chiAt α hirr 1 0) (chiAt_sq _ _ _ _) (D.tile i)
    ((D.tile i).threeAlpha_angles_mem hirr hrel hT 1) e
  have hext := model_hext (D.tile i) hirr hT hrel (e + 2)
  have hK : (chiAt α hirr 1 0).tileValue D.model = a + b + c :=
    threeAlpha_tileValue_minus D.model hirr hrel h
  have hKi : (chiAt α hirr 1 0).tileValue (D.tile i) = a + b + c :=
    threeAlpha_tileValue_minus (D.tile i) hirr hrel hT
  unfold GridChar.edgeSign at hf
  rw [hext, hdir, one_mul, hKi, hflux i, hK] at hf
  obtain ⟨ha, hb, hc, -, -⟩ := model_abc_pos h
  have hpos : 0 < a + b + c := by linarith
  exact mul_right_cancel₀ hpos.ne' hf
theorem target_flux (hz : ∀ k, vcount D k (2 * α + β) = 0) :
    D.target.flux (chiAt α hirr 1 0).weight
      = (chiAt α hirr 1 0).chi ((Real.pi - D.target.angleAt 2 : ℝ) : Real.Angle)
        * (chiAt α hirr 1 0).weight (D.target.leftUnit 0)
        * ∑ k : Fin 3, (chiAt α hirr 1 0).chi ((Real.pi - D.target.angleAt k : ℝ) : Real.Angle)
            * D.target.oppLen k := by
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (chiAt α hirr 1 0).L := by
    intro k
    rw [corner_eq D hirr hrel h hz k]
    exact mem_L hirr hrel _ _
  rw [Tri.flux_eq_edgeSign (chiAt α hirr 1 0) (chiAt_sq _ _ _ _) D.target htarget 0]
  rfl
theorem signedtiles_irr (i₀ : Fin N) :
    ∃ ε : Fin N → ℤ, D.toDissection.ProperColouring ε ∧ ε i₀ = 1 := by
  obtain ⟨ε, hε, -, -⟩ := D.flux_colouring (chiAt α hirr 1 0) (chiAt_sq _ _ _ _)
    (D.model.threeAlpha_angles_mem hirr hrel h 1) (model_hext D.model hirr h hrel)
  rcases hε.1 i₀ with e | e
  · exact ⟨ε, hε, e⟩
  · exact ⟨fun i => - ε i, proper_neg D hε, by simp [e]⟩
theorem flux_identity
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β
      (2 * α + β)) :
    ∃ ε₀ : Fin N → ℤ, D.toDissection.ProperColouring ε₀ ∧
      (∀ i, AtBOnAB D i → (ε₀ i : ℝ) = (chiAt α hirr 1 0).weight (D.target.leftUnit 0)) ∧
      ((∑ i, ε₀ i : ℤ) : ℝ) * (a + b + c)
        = (if Even (tilesAt D 2) then -1 else 1)
          * (chiAt α hirr 1 0).weight (D.target.leftUnit 0)
          * ∑ k : Fin 3, (if Even (tilesAt D k) then -1 else 1) * D.target.oppLen k := by
  rcases lemma6 D hirr hrel h with hs | ⟨hz, -, -, -⟩
  · exact absurd hs hns
  obtain ⟨ε₀, hε₀, hflux, hS⟩ := D.flux_colouring (chiAt α hirr 1 0) (chiAt_sq _ _ _ _)
    (D.model.threeAlpha_angles_mem hirr hrel h 1) (model_hext D.model hirr h hrel)
  have hK : (chiAt α hirr 1 0).tileValue D.model = a + b + c :=
    threeAlpha_tileValue_minus D.model hirr hrel h
  have hchi : ∀ k, (chiAt α hirr 1 0).chi ((Real.pi - D.target.angleAt k : ℝ) : Real.Angle)
      = if Even (tilesAt D k) then -1 else 1 := by
    intro k
    rw [corner_eq D hirr hrel h hz k, chi_ext hirr hrel, tilesAt_eq D hirr hrel h k (hz k)]
  refine ⟨ε₀, hε₀, fun i hi => sign_at_B D hirr hrel h hflux hi, ?_⟩
  rw [← hK, ← hS, target_flux D hirr hrel h hz, hchi]
  simp only [hchi]
theorem coloring_irr
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β
      (2 * α + β)) :
    (∃ σ : Equiv.Perm (Fin 3), tilesAt D (σ 0) = tilesAt D (σ 2)) ∧
      (tilesAt D 0 = tilesAt D 2 → ∀ (ε : Fin N → ℤ) (i₀ : Fin N),
        D.toDissection.ProperColouring ε → AtBOnAB D i₀ → ε i₀ = 1 →
        ((D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∨
            (D.target.angleAt 0 = β ∧ D.target.angleAt 2 = β) →
          ((∑ i, ε i : ℤ) : ℝ) * (a + b + c)
            = D.target.oppLen 0 + D.target.oppLen 1 + D.target.oppLen 2) ∧
        (¬ ((D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∨
            (D.target.angleAt 0 = β ∧ D.target.angleAt 2 = β)) →
          ((∑ i, ε i : ℤ) : ℝ) * (a + b + c)
            = D.target.oppLen 0 - D.target.oppLen 1 + D.target.oppLen 2)) := by
  rcases lemma6 D hirr hrel h with hs | ⟨hz, hP, hQ, -⟩
  · exact absurd hs hns
  obtain ⟨-, -, -, -, hpos⟩ := lemma11 D hirr hrel h hns
  have hn : ∀ k, tilesAt D k = vcount D k α + vcount D k β :=
    fun k => tilesAt_eq D hirr hrel h k (hz k)
  rw [Fin.sum_univ_three] at hP hQ
  have p0 := hpos 0
  have p1 := hpos 1
  have p2 := hpos 2
  have n0 := hn 0
  have n1 := hn 1
  have n2 := hn 2
  refine ⟨?_, ?_⟩
  · have : tilesAt D 0 = tilesAt D 2 ∨ tilesAt D 0 = tilesAt D 1 ∨ tilesAt D 1 = tilesAt D 2 := by
      omega
    rcases this with e | e | e
    · exact ⟨1, e⟩
    · obtain ⟨τ, t0, -, t2⟩ := perm3 0 2 1 (by decide) (by decide) (by decide)
      exact ⟨τ, by rw [t0, t2, e]⟩
    · obtain ⟨τ, t0, -, t2⟩ := perm3 1 0 2 (by decide) (by decide) (by decide)
      exact ⟨τ, by rw [t0, t2, e]⟩
  intro h02 ε i₀ hε hi₀ hεi₀
  obtain ⟨ε₀, hε₀, hB, hid⟩ := flux_identity D hirr hrel h hns
  set w := (chiAt α hirr 1 0).weight (D.target.leftUnit 0) with hwdef
  have hw := hB i₀ hi₀
  have hM : ((∑ i, ε i : ℤ) : ℝ) = w * ((∑ i, ε₀ i : ℤ) : ℝ) := by
    rcases Dissection.colouring_unique' D.toDissection hε₀ hε with e | e
    · subst e
      rw [← hw, hεi₀]
      simp
    · subst e
      have : (ε₀ i₀ : ℝ) = -1 := by
        have : ε₀ i₀ = -1 := by simp only at hεi₀; omega
        exact_mod_cast this
      rw [← hw, this, Finset.sum_neg_distrib]
      push_cast
      ring
  have hw2 : w * w = 1 := (chiAt α hirr 1 0).val_sq (chiAt_sq _ _ _ _) _
  have key : ((∑ i, ε i : ℤ) : ℝ) * (a + b + c)
      = (if Even (tilesAt D 2) then -1 else 1)
          * ∑ k : Fin 3, (if Even (tilesAt D k) then -1 else 1) * D.target.oppLen k := by
    rw [hM, mul_assoc, hid]
    linear_combination ((if Even (tilesAt D 2) then (-1 : ℝ) else 1)
      * ∑ k : Fin 3, (if Even (tilesAt D k) then (-1 : ℝ) else 1) * D.target.oppLen k) * hw2
  rw [Fin.sum_univ_three] at key
  have hiff : ((D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∨
      (D.target.angleAt 0 = β ∧ D.target.angleAt 2 = β)) ↔ tilesAt D 0 = 1 := by
    have c0 := corner_eq D hirr hrel h hz 0
    have c1 := corner_eq D hirr hrel h hz 1
    have c2 := corner_eq D hirr hrel h hz 2
    constructor
    · rintro (⟨e0, -⟩ | ⟨e0, -⟩)
      · have := indep hirr hrel (p := vcount D 0 α) (q := vcount D 0 β) (p' := 1) (q' := 0)
          (by rw [← c0, e0]; push_cast; ring)
        omega
      · have := indep hirr hrel (p := vcount D 0 α) (q := vcount D 0 β) (p' := 0) (q' := 1)
          (by rw [← c0, e0]; push_cast; ring)
        omega
    · intro h1
      have hcase : (vcount D 0 α = 1 ∧ vcount D 0 β = 0 ∨ vcount D 0 α = 0 ∧ vcount D 0 β = 1) ∧
          (vcount D 2 α = 1 ∧ vcount D 2 β = 0 ∨ vcount D 2 α = 0 ∧ vcount D 2 β = 1) := by
        omega
      rcases hcase with ⟨⟨a0, b0⟩ | ⟨a0, b0⟩, ⟨a2, b2⟩ | ⟨a2, b2⟩⟩
      · left
        rw [c0, c2, a0, b0, a2, b2]; push_cast; constructor <;> ring
      · exfalso; apply hns
        have a1 : vcount D 1 α = 2 := by omega
        have b1 : vcount D 1 β = 1 := by omega
        right; left
        rw [c0, c1, c2, a0, b0, a1, b1, a2, b2]; push_cast
        exact ⟨by ring, by ring, by ring⟩
      · exfalso; apply hns
        have a1 : vcount D 1 α = 2 := by omega
        have b1 : vcount D 1 β = 1 := by omega
        right; right; right; left
        rw [c0, c1, c2, a0, b0, a1, b1, a2, b2]; push_cast
        exact ⟨by ring, by ring, by ring⟩
      · right
        rw [c0, c2, a0, b0, a2, b2]; push_cast; constructor <;> ring
  have e1 : ¬ Even 1 := by decide
  have e2 : Even 2 := by decide
  have e3 : ¬ Even 3 := by decide
  refine ⟨fun hp => ?_, fun hnp => ?_⟩
  · have h0 : tilesAt D 0 = 1 := hiff.mp hp
    have h2 : tilesAt D 2 = 1 := by omega
    have h1 : tilesAt D 1 = 3 := by omega
    rw [h0, h1, h2, if_neg e1, if_neg e3] at key
    linarith
  · have h0 : tilesAt D 0 = 2 := by
      have := mt hiff.mpr hnp
      omega
    have h2 : tilesAt D 2 = 2 := by omega
    have h1 : tilesAt D 1 = 1 := by omega
    rw [h0, h1, h2, if_pos e2, if_neg e1] at key
    linarith
end Colouring
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles similar_of_same_angles)
open Erdos634.BeesonColoring TriangleTiling.Laczkovich
variable {N : ℕ} (D : CongruentDissection N)
theorem tgtAngles_of_triple3 {x y z : ℝ}
    (h : Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) x y z) :
    TgtAngles D x y z := by
  rcases h with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩
  · obtain ⟨τ, t0, t1, t2⟩ := perm3 0 1 2 (by decide) (by decide) (by decide)
    exact ⟨τ, by rw [t0, h0], by rw [t1, h1], by rw [t2, h2]⟩
  · obtain ⟨τ, t0, t1, t2⟩ := perm3 0 2 1 (by decide) (by decide) (by decide)
    exact ⟨τ, by rw [t0, h0], by rw [t1, h2], by rw [t2, h1]⟩
  · obtain ⟨τ, t0, t1, t2⟩ := perm3 1 0 2 (by decide) (by decide) (by decide)
    exact ⟨τ, by rw [t0, h1], by rw [t1, h0], by rw [t2, h2]⟩
  · obtain ⟨τ, t0, t1, t2⟩ := perm3 2 0 1 (by decide) (by decide) (by decide)
    exact ⟨τ, by rw [t0, h2], by rw [t1, h0], by rw [t2, h1]⟩
  · obtain ⟨τ, t0, t1, t2⟩ := perm3 1 2 0 (by decide) (by decide) (by decide)
    exact ⟨τ, by rw [t0, h1], by rw [t1, h2], by rw [t2, h0]⟩
  · obtain ⟨τ, t0, t1, t2⟩ := perm3 2 1 0 (by decide) (by decide) (by decide)
    exact ⟨τ, by rw [t0, h2], by rw [t1, h1], by rw [t2, h0]⟩
theorem tile_facts {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hT : TileAngles D α β γ) :
    0 < α ∧ 0 < β ∧ γ = 2 * α + β := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  have hs := D.model.angleAt_sum
  have hsum : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) = Real.pi := by
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [e, hs]
  refine ⟨h0 ▸ Tri.angleAt_pos' _ _, h1 ▸ Tri.angleAt_pos' _ _, ?_⟩
  rw [h0, h1, h2] at hsum
  linarith
theorem threeAlphaData_of {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileAngles D α β γ) :
    ∃ a b c : ℝ, D.model.ThreeAlphaData α β a b c := by
  have hγ := (tile_facts D hrel hT).2.2
  obtain ⟨σ, h0, h1, h2⟩ := hT
  exact ⟨_, _, _, σ, h0, rfl, h1, rfl, hγ ▸ h2, rfl⟩
theorem threeAlphaData_of_sides {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) : D.model.ThreeAlphaData α β a b c := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  have hγ := (tile_facts D hrel ⟨σ, h0, h1, h2⟩).2.2
  exact ⟨σ, h0, l0, h1, l1, hγ ▸ h2, l2⟩
theorem not_triple3 {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hT : TileAngles D α β γ)
    (hns : ¬ SimilarTM D) :
    ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β) := by
  have hγ := (tile_facts D hrel hT).2.2
  intro h3
  exact hns (similar_of_same_angles D hT (hγ ▸ tgtAngles_of_triple3 D h3))
theorem angles {α β γ : ℝ} [hI : Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)]
    (hrel : 3 * α + 2 * β = Real.pi) (hT : TileAngles D α β γ) (hns : ¬ SimilarTM D) :
    IrrPi α ∧ IrrPi β ∧
      ∀ x y z : ℚ, (y : ℝ) * α + z * β = x * Real.pi → ∃ t : ℚ, y = 3 * t ∧ z = 2 * t ∧ x = t := by
  have hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi := hI.out
  refine ⟨hα, ?_, ?_⟩
  · rintro ⟨r, hr⟩
    exact hα ⟨(1 - 2 * r) / 3, by push_cast; linear_combination (1 / 3 : ℝ) * hrel - (2 / 3 : ℝ) * hr⟩
  · intro x y z h
    by_cases hy : (y : ℝ) - 3 * z / 2 = 0
    · have hy' : y = 3 * (z / 2) := by
        have : (y : ℝ) = 3 * ((z : ℝ) / 2) := by linarith
        exact_mod_cast this
      refine ⟨z / 2, hy', by ring, ?_⟩
      have e : ((x : ℝ) - z / 2) * Real.pi = 0 := by
        linear_combination -h + ((z : ℝ) / 2) * hrel + α * hy
      rcases mul_eq_zero.mp e with e | e
      · have : (x : ℝ) = (z : ℝ) / 2 := by linarith
        exact_mod_cast this
      · exact absurd e Real.pi_ne_zero
    · exfalso
      have e : ((y : ℝ) - 3 * z / 2) * α = ((x : ℝ) - z / 2) * Real.pi := by
        linear_combination h - ((z : ℝ) / 2) * hrel
      exact hα ⟨(x - z / 2) / (y - 3 * z / 2), by
        push_cast; rw [div_mul_eq_mul_div, eq_div_iff hy]; linear_combination e⟩

theorem signedtiles {α β γ : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi) (hT : TileAngles D α β γ)
    (hns : ¬ SimilarTM D) {i₀ : Fin N} (hi₀ : TileAt D 1 i₀) :
    ∃ ε : Fin N → ℤ, D.toDissection.ProperColouring ε ∧ ε i₀ = 1 := by
  obtain ⟨a, b, c, h⟩ := threeAlphaData_of D hrel hT
  exact signedtiles_irr D (angles D hrel hT hns).1 hrel h i₀
theorem coloring {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) :
    (∃ σ : Equiv.Perm (Fin 3), tilesAt D (σ 0) = tilesAt D (σ 2)) ∧
      (tilesAt D 0 = tilesAt D 2 → ∀ (ε : Fin N → ℤ) (i₀ : Fin N),
        D.toDissection.ProperColouring ε → AtBOnAB D i₀ → ε i₀ = 1 →
        let M : ℤ := ∑ i, ε i
        let X := D.target.oppLen 0
        let Y := D.target.oppLen 1
        let Z := D.target.oppLen 2
        ((D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∨
            (D.target.angleAt 0 = β ∧ D.target.angleAt 2 = β) →
          (M : ℝ) * (a + b + c) = X + Y + Z) ∧
        (¬ ((D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∨
            (D.target.angleAt 0 = β ∧ D.target.angleAt 2 = β)) →
          (M : ℝ) * (a + b + c) = X - Y + Z)) := by
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  exact coloring_irr D (angles D hrel hT' hns).1 hrel (threeAlphaData_of_sides D hrel hT)
    (not_triple3 D hrel hT' hns)
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry
section Eval
variable {δ : ℝ} (hδ : ¬ ∃ q : ℚ, δ = (q : ℝ) * Real.pi)
include hδ
theorem coset_eq {θ₀ : Real.Angle} {n m e f : ℤ}
    (h : θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle) = θ₀ + ((m * δ + f * Real.pi : ℝ) : Real.Angle)) :
    n = m ∧ Even (e - f) := by
  have h' := add_left_cancel h
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h'
  obtain ⟨k, hk⟩ := h'
  have hπ := Real.pi_pos
  by_cases hnm : n = m
  · subst hnm
    refine ⟨rfl, k, ?_⟩
    have : ((e - f : ℤ) : ℝ) = ((k + k : ℤ) : ℝ) := by
      push_cast
      have : ((e : ℝ) - f) * Real.pi = (k + k) * Real.pi := by linarith
      exact mul_right_cancel₀ hπ.ne' this
    exact_mod_cast this
  · exfalso
    apply hδ
    have hd : ((n : ℝ) - m) ≠ 0 := fun e0 => hnm (by exact_mod_cast sub_eq_zero.mp e0)
    refine ⟨(2 * k - (e - f)) / (n - m), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hd]
    linear_combination hk
omit hδ in
theorem coe_add_two_pi_mul' (x : ℝ) (t : ℤ) :
    ((x + (t + t : ℤ) * Real.pi : ℝ) : Real.Angle) = (x : Real.Angle) := by
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub]
  exact ⟨t, by push_cast; ring⟩
theorem phi1_eval (θ₀ : Real.Angle) (n e : ℤ) :
    Phi1 δ θ₀ (θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)) = ((e.negOnePow : ℤ) : ℝ) := by
  unfold Phi1
  rcases Int.even_or_odd e with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hang : θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle) = θ₀ + ((n * δ : ℝ) : Real.Angle) := by
      subst ht; rw [coe_add_two_pi_mul' (n * δ) t]
    rw [if_pos ⟨n, hang⟩, Int.negOnePow_even _ ⟨t, ht⟩]
    simp
  · have hodd : ¬ ∃ m : ℤ, θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
        = θ₀ + ((m * δ : ℝ) : Real.Angle) := by
      rintro ⟨m, hm⟩
      have := coset_eq hδ (m := m) (f := 0) (by rw [hm]; simp)
      rw [sub_zero] at this
      exact (Int.not_even_iff_odd.mpr ⟨t, ht⟩) this.2
    have hang : θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
        = θ₀ + ((n * δ + Real.pi : ℝ) : Real.Angle) := by
      subst ht
      have : (n : ℝ) * δ + ((2 * t + 1 : ℤ) : ℝ) * Real.pi
          = (n * δ + Real.pi) + ((t + t : ℤ) : ℝ) * Real.pi := by push_cast; ring
      rw [this, coe_add_two_pi_mul' _ t]
    rw [if_neg hodd, if_pos ⟨n, hang⟩, Int.negOnePow_odd _ ⟨t, ht⟩]
    simp
theorem phi2_eval (θ₀ : Real.Angle) (n e : ℤ) :
    Phi2 δ θ₀ (θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)) = (((n + e).negOnePow : ℤ) : ℝ) := by
  unfold Phi2
  rcases Int.even_or_odd e with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hex : ∃ m : ℤ, θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
        = θ₀ + ((m * δ : ℝ) : Real.Angle) := ⟨n, by subst ht; rw [coe_add_two_pi_mul' (n * δ) t]⟩
    rw [dif_pos hex]
    set m := hex.choose with hmdef
    have hc : θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle) = θ₀ + ((m * δ : ℝ) : Real.Angle) :=
      hex.choose_spec
    have hm := (coset_eq hδ (m := m) (f := 0) (by rw [hc]; simp)).1
    rw [← hm, Int.negOnePow_add, Int.negOnePow_even e ⟨t, ht⟩, mul_one]
  · have hodd : ¬ ∃ m : ℤ, θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
        = θ₀ + ((m * δ : ℝ) : Real.Angle) := by
      rintro ⟨m, hm⟩
      have := coset_eq hδ (m := m) (f := 0) (by rw [hm]; simp)
      rw [sub_zero] at this
      exact (Int.not_even_iff_odd.mpr ⟨t, ht⟩) this.2
    have hex : ∃ m : ℤ, θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
        = θ₀ + ((m * δ + Real.pi : ℝ) : Real.Angle) := ⟨n, by
      subst ht
      have : (n : ℝ) * δ + ((2 * t + 1 : ℤ) : ℝ) * Real.pi
          = (n * δ + Real.pi) + ((t + t : ℤ) : ℝ) * Real.pi := by push_cast; ring
      rw [this, coe_add_two_pi_mul' _ t]⟩
    rw [dif_neg hodd, dif_pos hex]
    set m := hex.choose with hmdef
    have hc : θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)
        = θ₀ + ((m * δ + Real.pi : ℝ) : Real.Angle) := hex.choose_spec
    have hm := (coset_eq hδ (m := m) (f := 1) (by rw [hc]; simp)).1
    rw [← hm, Int.negOnePow_add, Int.negOnePow_odd e ⟨t, ht⟩]
    push_cast
    ring
omit hδ in
theorem phi_off {θ₀ θ : Real.Angle}
    (h : ¬ ∃ n e : ℤ, θ = θ₀ + ((n * δ + e * Real.pi : ℝ) : Real.Angle)) :
    Phi1 δ θ₀ θ = 0 ∧ Phi2 δ θ₀ θ = 0 := by
  have h1 : ¬ ∃ m : ℤ, θ = θ₀ + ((m * δ : ℝ) : Real.Angle) := by
    rintro ⟨m, hm⟩; exact h ⟨m, 0, by rw [hm]; simp⟩
  have h2 : ¬ ∃ m : ℤ, θ = θ₀ + ((m * δ + Real.pi : ℝ) : Real.Angle) := by
    rintro ⟨m, hm⟩; exact h ⟨m, 1, by rw [hm]; simp⟩
  unfold Phi1 Phi2
  rw [if_neg h1, if_neg h2, dif_neg h1, dif_neg h2]
  exact ⟨rfl, rfl⟩
end Eval
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry Erdos634.BeesonColoring
variable {α β a b c : ℝ}
theorem delta_irr' (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi) : ¬ ∃ q : ℚ, α + β = (q : ℝ) * Real.pi := by
  rintro ⟨q, hq⟩
  exact hirr ⟨1 - 2 * q, by push_cast; linarith⟩
section Tiling
variable {N : ℕ} (D : CongruentDissection N) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
  (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel h
omit hirr h in
theorem ext_coords (p q : ℤ) :
    Real.pi - (p * α + q * β) = (2 * p - 3 * q : ℤ) * (α + β) + (1 - p + q : ℤ) * Real.pi := by
  push_cast
  linear_combination ((q : ℝ) - p) * hrel
omit h in
theorem Phisigns_row (hccw : 0 < D.target.det) (p₁ q₁ p₂ q₂ : ℤ)
    (h₁ : D.target.angleAt 1 = p₁ * α + q₁ * β) (h₂ : D.target.angleAt 2 = p₂ * α + q₂ * β)
    {u₁ u₂ v₁ v₂ : ℤ} (hu₁ : ((1 - p₁ + q₁).negOnePow : ℤ) = u₁)
    (hu₂ : (((1 - p₁ + q₁) + (1 - p₂ + q₂)).negOnePow : ℤ) = u₂)
    (hv₁ : (((2 * p₁ - 3 * q₁) + (1 - p₁ + q₁)).negOnePow : ℤ) = v₁)
    (hv₂ : (((2 * p₁ - 3 * q₁) + (2 * p₂ - 3 * q₂) + ((1 - p₁ + q₁) + (1 - p₂ + q₂))).negOnePow
      : ℤ) = v₂) :
    Phi1 (α + β) (baseDir D) (D.target.leftUnit 1).angle = u₁ ∧
      Phi1 (α + β) (baseDir D) (D.target.leftUnit 2).angle = u₂ ∧
      Phi2 (α + β) (baseDir D) (D.target.leftUnit 1).angle = v₁ ∧
      Phi2 (α + β) (baseDir D) (D.target.leftUnit 2).angle = v₂ := by
  have hδ := delta_irr' hirr hrel
  have t0 := D.target.leftUnit_turn_of_pos hccw 0
  have t1 := D.target.leftUnit_turn_of_pos hccw 1
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl] at t0 t1
  rw [h₁, ext_coords hrel] at t0
  rw [h₂, ext_coords hrel] at t1
  have eBC : (D.target.leftUnit 1).angle = baseDir D + ((((2 * p₁ - 3 * q₁ : ℤ) : ℝ) * (α + β)
      + ((1 - p₁ + q₁ : ℤ) : ℝ) * Real.pi : ℝ) : Real.Angle) := t0
  have eCA : (D.target.leftUnit 2).angle = baseDir D + (((((2 * p₁ - 3 * q₁) + (2 * p₂ - 3 * q₂) : ℤ)
      : ℝ) * (α + β) + (((1 - p₁ + q₁) + (1 - p₂ + q₂) : ℤ) : ℝ) * Real.pi : ℝ) : Real.Angle) := by
    rw [t1, eBC, add_assoc, ← Real.Angle.coe_add]; push_cast; ring_nf
  rw [eBC, eCA, phi1_eval hδ, phi1_eval hδ, phi2_eval hδ, phi2_eval hδ, hu₁, hu₂, hv₁, hv₂]
  exact ⟨rfl, rfl, rfl, rfl⟩
end Tiling
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
variable {N : ℕ} (D : CongruentDissection N)
theorem Phisigns {α β γ : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi) (hT : TileAngles D α β γ)
    (hns : ¬ SimilarTM D) (hccw : 0 < D.target.det) :
    let Φ₁ := Phi1 (α + β) (baseDir D)
    let Φ₂ := Phi2 (α + β) (baseDir D)
    let AB := (D.target.leftUnit 0).angle
    let BC := (D.target.leftUnit 1).angle
    let CA := (D.target.leftUnit 2).angle
    let shape := fun x y z : ℝ =>
      D.target.angleAt 0 = x ∧ D.target.angleAt 1 = y ∧ D.target.angleAt 2 = z
    (Φ₁ AB = 1 ∧ Φ₂ AB = 1) ∧
    (shape (2 * α) β (α + β) → Φ₁ BC = 1 ∧ Φ₁ CA = -1 ∧ Φ₂ BC = -1 ∧ Φ₂ CA = -1) ∧
    (shape β (3 * α) β → Φ₁ BC = 1 ∧ Φ₁ CA = 1 ∧ Φ₂ BC = 1 ∧ Φ₂ CA = -1) ∧
    (shape (α + β) α (α + β) → Φ₁ BC = 1 ∧ Φ₁ CA = -1 ∧ Φ₂ BC = 1 ∧ Φ₂ CA = 1) ∧
    (shape α (α + 2 * β) α → Φ₁ BC = 1 ∧ Φ₁ CA = 1 ∧ Φ₂ BC = 1 ∧ Φ₂ CA = 1) ∧
    (shape (2 * α) α (2 * β) → Φ₁ BC = 1 ∧ Φ₁ CA = -1 ∧ Φ₂ BC = 1 ∧ Φ₂ CA = -1) := by
  intro Φ₁ Φ₂ AB BC CA shape
  have hirr := (angles D hrel hT hns).1
  have hδ := delta_irr' hirr hrel
  have hAB : AB = baseDir D + ((((0 : ℤ) : ℝ) * (α + β) + ((0 : ℤ) : ℝ) * Real.pi : ℝ) : Real.Angle) := by
    simp [AB, baseDir]
  have row := Phisigns_row D hirr hrel hccw
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show Phi1 (α + β) (baseDir D) AB = 1
    rw [hAB, phi1_eval hδ]; simp
  · show Phi2 (α + β) (baseDir D) AB = 1
    rw [hAB, phi2_eval hδ]; simp
  · rintro ⟨-, e1, e2⟩
    have := row 0 1 1 1 (u₁ := 1) (u₂ := -1) (v₁ := -1) (v₂ := -1)
      (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring)
      (by decide) (by decide) (by decide) (by decide)
    push_cast at this
    exact this
  · rintro ⟨-, e1, e2⟩
    have := row 3 0 0 1 (u₁ := 1) (u₂ := 1) (v₁ := 1) (v₂ := -1)
      (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring)
      (by decide) (by decide) (by decide) (by decide)
    push_cast at this
    exact this
  · rintro ⟨-, e1, e2⟩
    have := row 1 0 1 1 (u₁ := 1) (u₂ := -1) (v₁ := 1) (v₂ := 1)
      (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring)
      (by decide) (by decide) (by decide) (by decide)
    push_cast at this
    exact this
  · rintro ⟨-, e1, e2⟩
    have := row 1 2 1 0 (u₁ := 1) (u₂ := 1) (v₁ := 1) (v₂ := 1)
      (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring)
      (by decide) (by decide) (by decide) (by decide)
    push_cast at this
    exact this
  · rintro ⟨-, e1, e2⟩
    have := row 1 0 0 2 (u₁ := 1) (u₂ := -1) (v₁ := 1) (v₂ := -1)
      (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring)
      (by decide) (by decide) (by decide) (by decide)
    push_cast at this
    exact this
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open EuclideanGeometry Real
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]
theorem sines {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hrel : 3 * α + 2 * β = π) :
    let δ := α + β
    let s := 2 * cos δ
    sin α / sin δ = s ∧ sin β / sin δ = 1 - s ^ 2 ∧ sin (2 * α + β) / sin δ = 1 ∧
      sin (α + β) / sin δ = 1 ∧ sin (2 * α) / sin δ = s * (2 - s ^ 2) ∧
      sin (α + 2 * β) / sin δ = s * (2 - s ^ 2) ∧
      sin (3 * α) / sin δ = s * (1 - s ^ 2) * (3 - s ^ 2) ∧
      sin (2 * β) / sin δ = s * (1 - s ^ 2) * (3 - s ^ 2) := by
  intro δ s
  have hsc := sin_sq_add_cos_sq δ
  have hπ := pi_pos
  have hsδ : 0 < sin δ := sin_pos_of_pos_of_lt_pi (by simp only [δ]; linarith)
    (by simp only [δ]; linarith)
  have hne := hsδ.ne'
  have Sα : sin α = 2 * sin δ * cos δ := by
    rw [show α = π - 2 * δ by simp only [δ]; linarith, sin_pi_sub, sin_two_mul]
  have Cα : cos α = 1 - 2 * cos δ ^ 2 := by
    rw [show α = π - 2 * δ by simp only [δ]; linarith, cos_pi_sub, cos_two_mul]; ring
  have Sβ : sin β = -(3 * sin δ - 4 * sin δ ^ 3) := by
    rw [show β = 3 * δ - π by simp only [δ]; linarith, sin_sub_pi, sin_three_mul]
  have Sγ : sin (2 * α + β) = sin δ := by
    rw [show 2 * α + β = π - δ by simp only [δ]; linarith, sin_pi_sub]
  have S2α : sin (2 * α) = 2 * sin α * cos α := sin_two_mul α
  have Sα2β : sin (α + 2 * β) = sin (2 * α) := by
    rw [show α + 2 * β = π - 2 * α by linarith, sin_pi_sub]
  have S3α : sin (3 * α) = 3 * sin α - 4 * sin α ^ 3 := sin_three_mul α
  have S2β : sin (2 * β) = sin (3 * α) := by
    rw [show 2 * β = π - 3 * α by linarith, sin_pi_sub]
  simp only [s]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [div_eq_iff hne]
  · rw [Sα]; ring
  · rw [Sβ]; linear_combination 4 * sin δ * hsc
  · rw [Sγ]; ring
  · ring
  · rw [S2α, Sα, Cα]; ring
  · rw [Sα2β, S2α, Sα, Cα]; ring
  · rw [S3α, Sα]; linear_combination (-32 * sin δ * cos δ ^ 3) * hsc
  · rw [S2β, S3α, Sα]; linear_combination (-32 * sin δ * cos δ ^ 3) * hsc
theorem gsquare_arith (a b c m k : ℕ) (hb0 : 0 < b) (hc0 : 0 < c)
    (hgcd : Nat.gcd (Nat.gcd a b) c = 1) (hrel' : a ^ 2 + b * c = c ^ 2)
    (hmk : Nat.Coprime m k) (hk : 0 < k) (hratio : a * k = m * c) :
    a = m * k ∧ b = k ^ 2 - m ^ 2 ∧ c = k ^ 2 ∧ k = Nat.gcd a c ∧ m = a / k ∧ m < k := by
  obtain ⟨t, rfl⟩ : k ∣ c :=
    (Nat.Coprime.symm hmk).dvd_of_dvd_mul_left ⟨a, by rw [← hratio, mul_comm]⟩
  have hat : a = m * t := by
    apply Nat.eq_of_mul_eq_mul_left hk
    rw [mul_comm k a, hratio]
    ring
  subst hat
  have ht : 0 < t := Nat.pos_of_mul_pos_left hc0
  have h1 : m ^ 2 * t + b * k = k ^ 2 * t := by
    apply Nat.eq_of_mul_eq_mul_left ht
    linear_combination hrel'
  have hkt : k ∣ t := by
    have : k ∣ m ^ 2 * t := by
      have h2 : k ∣ m ^ 2 * t + b * k := by rw [h1]; exact ⟨k * t, by ring⟩
      exact (Nat.dvd_add_left (Dvd.intro_left b rfl)).mp h2
    exact (Nat.Coprime.pow_right 2 hmk.symm).dvd_of_dvd_mul_left this
  obtain ⟨u, rfl⟩ := hkt
  have h2 : m ^ 2 * u + b = k ^ 2 * u := by
    apply Nat.eq_of_mul_eq_mul_left hk
    linear_combination h1
  have hu : u = 1 := by
    have hub : u ∣ b := by
      have : u ∣ m ^ 2 * u + b := by rw [h2]; exact Dvd.intro_left _ rfl
      exact (Nat.dvd_add_right (Dvd.intro_left _ rfl)).mp this
    have : u ∣ Nat.gcd (Nat.gcd (m * (k * u)) b) (k * (k * u)) :=
      Nat.dvd_gcd (Nat.dvd_gcd ⟨m * k, by ring⟩ hub) ⟨k * k, by ring⟩
    rw [hgcd] at this
    exact Nat.dvd_one.mp this
  subst hu
  simp only [mul_one] at h2 ⊢
  have hmk' : m < k := by
    have : m ^ 2 < k ^ 2 := by linarith
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp this
  refine ⟨trivial, by rw [← h2, Nat.add_sub_cancel_left], by ring, ?_, ?_, hmk'⟩
  · rw [Nat.gcd_mul_right, Nat.Coprime.gcd_eq_one hmk, one_mul]
  · rw [Nat.mul_div_cancel _ hk]
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
theorem model_facts {N : ℕ} (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hT : TileSides D α β γ a b c) :
    0 < α ∧ 0 < β ∧ γ = 2 * α + β ∧ 0 < Real.sin (α + β) ∧ 0 < c ∧
      a = 2 * Real.cos (α + β) * c ∧ b = (1 - (2 * Real.cos (α + β)) ^ 2) * c ∧
      0 < 2 * Real.cos (α + β) ∧ 2 * Real.cos (α + β) < 1 ∧
      circumdiam D.model = c / Real.sin (α + β) ∧
      Real.sin (D.model.angleAt 0) * Real.sin (D.model.angleAt 1) * Real.sin (D.model.angleAt 2)
        = Real.sin α * Real.sin β * Real.sin (2 * α + β) := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  have hα : 0 < α := h0 ▸ D.model.angleAt_pos' _
  have hβ : 0 < β := h1 ▸ D.model.angleAt_pos' _
  have hsum : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) = Real.pi := by
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [e, D.model.angleAt_sum]
  have hγ : γ = 2 * α + β := by rw [h0, h1, h2] at hsum; linarith
  have hπ := Real.pi_pos
  have hS : 0 < Real.sin (α + β) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hSγ : Real.sin γ = Real.sin (α + β) := by
    rw [hγ, show 2 * α + β = Real.pi - (α + β) by linarith, Real.sin_pi_sub]
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨r1, r2, -, -, -, -, -, -⟩ := r
  rw [div_eq_iff hS.ne'] at r1 r2
  have hd := circumdiam_pos D.model
  have la := lawsin D.model (σ 0)
  have lb := lawsin D.model (σ 1)
  have lc := lawsin D.model (σ 2)
  rw [l0, h0] at la
  rw [l1, h1] at lb
  rw [l2, h2, hSγ] at lc
  have hc : 0 < c := by rw [lc]; positivity
  have hdc : circumdiam D.model = c / Real.sin (α + β) := by rw [lc]; field_simp
  have hcos : 0 < Real.cos (α + β) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcos2 : Real.cos (α + β) < 1 / 2 := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  refine ⟨hα, hβ, hγ, hS, hc, ?_, ?_, by linarith, by linarith, hdc, ?_⟩
  · rw [la, r1, lc]; ring
  · rw [lb, r2, lc]; ring
  · have e := Equiv.prod_comp σ (fun k => Real.sin (D.model.angleAt k))
    simp only [Fin.prod_univ_three] at e
    rw [← e, h0, h1, h2, hγ]
theorem shapeareas {N : ℕ} (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hT : TileSides D α β γ a b c) :
    let s := a / c
    let Λ := Lam D
    let shape := fun x y z : ℝ =>
      D.target.angleAt 0 = x ∧ D.target.angleAt 1 = y ∧ D.target.angleAt 2 = z
    (shape (2 * α) β (α + β) → N / Λ ^ 2 = 2 - s ^ 2) ∧
    (shape β (3 * α) β → N / Λ ^ 2 = (1 - s ^ 2) ^ 2 * (3 - s ^ 2)) ∧
    (shape (α + β) α (α + β) → N / Λ ^ 2 = 1 / (1 - s ^ 2)) ∧
    (shape α (α + 2 * β) α → N / Λ ^ 2 = s ^ 2 * (2 - s ^ 2) / (1 - s ^ 2)) ∧
    (shape (2 * α) α (2 * β) → N / Λ ^ 2 = s ^ 2 * (2 - s ^ 2) * (3 - s ^ 2)) := by
  intro s Λ shape
  obtain ⟨hα, hβ, hγ, hS, hc, ha, hb, hs0, hs1, hdm, hPm⟩ := model_facts D hrel hT
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := r
  rw [div_eq_iff hS.ne'] at r1 r2 r3 r4 r5 r6 r7 r8
  set S := Real.sin (α + β)
  set t := 2 * Real.cos (α + β)
  have hst : s = t := by simp only [s]; rw [ha]; field_simp
  have hA := area_sines D
  have hdt := circumdiam_pos D.target
  have hdm' := circumdiam_pos D.model
  have hΛ : Λ = circumdiam D.target / circumdiam D.model := rfl
  have hNΛ : (N : ℝ) / Λ ^ 2 = (Real.sin (D.target.angleAt 0) * Real.sin (D.target.angleAt 1) *
      Real.sin (D.target.angleAt 2)) / (Real.sin α * Real.sin β * Real.sin (2 * α + β)) := by
    rw [← hPm, hΛ, div_pow, div_div_eq_mul_div, eq_div_iff (by
      have := tri_sin_pos D.model 0; have := tri_sin_pos D.model 1; have := tri_sin_pos D.model 2
      positivity), div_mul_eq_mul_div, div_eq_iff (by positivity)]
    linarith [hA]
  have ht1 : 1 - t ^ 2 ≠ 0 := by nlinarith
  have hPm' : Real.sin α * Real.sin β * Real.sin (2 * α + β) = t * (1 - t ^ 2) * S ^ 3 := by
    rw [r1, r2, r3]; ring
  rw [hst]
  refine ⟨fun ⟨e0, e1, e2⟩ => ?_, fun ⟨e0, e1, e2⟩ => ?_, fun ⟨e0, e1, e2⟩ => ?_,
    fun ⟨e0, e1, e2⟩ => ?_, fun ⟨e0, e1, e2⟩ => ?_⟩ <;>
    rw [hNΛ, hPm', e0, e1, e2]
  · rw [r5, r2]; first | (field_simp; ring) | field_simp
  · rw [r2, r7]; first | (field_simp; ring) | field_simp
  · rw [r1]; first | (field_simp; ring) | field_simp
  · rw [r1, r6]; first | (field_simp; ring) | field_simp
  · rw [r5, r1, r8]; first | (field_simp; ring) | field_simp
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
variable {N : ℕ} (D : CongruentDissection N)
theorem PhiR_target (Φ : Real.Angle → ℝ) (T : Tri) :
    PhiR Φ T = T.oppLen 2 * Φ (T.leftUnit 0).angle + T.oppLen 0 * Φ (T.leftUnit 1).angle
      + T.oppLen 1 * Φ (T.leftUnit 2).angle := by
  unfold PhiR Tri.flux Tri.oppLen
  simp only [Fin.sum_univ_three, smul_eq_mul]
  rfl
theorem target_side {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (k : Fin 3) :
    D.target.oppLen k = Lam D * c * (Real.sin (D.target.angleAt k) / Real.sin (α + β)) := by
  obtain ⟨-, -, -, hS, hc, -, -, -, -, hdm, -⟩ := model_facts D hrel hT
  have hd := circumdiam_pos D.model
  rw [lawsin D.target k, Lam, hdm]
  field_simp
theorem M1M2 {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) (hccw : 0 < D.target.det)
    {M₁ M₂ : ℤ} (h₁ : PhiR (Phi1 (α + β) (baseDir D)) D.target = M₁ * (a + b + c))
    (h₂ : PhiR (Phi2 (α + β) (baseDir D)) D.target = M₂ * (a - b - c)) :
    let s := a / c
    let Λ := Lam D
    let shape := fun x y z : ℝ =>
      D.target.angleAt 0 = x ∧ D.target.angleAt 1 = y ∧ D.target.angleAt 2 = z
    (shape (2 * α) β (α + β) → (M₁ : ℝ) = Λ * s ∧ (M₂ : ℝ) = Λ * s) ∧
    (shape β (3 * α) β →
      (M₁ : ℝ) = Λ * (1 - s) * (1 + s) ^ 2 ∧ (M₂ : ℝ) = -Λ * (1 - s) ^ 2 * (1 + s)) ∧
    (shape (α + β) α (α + β) → (M₁ : ℝ) = Λ / (1 + s) ∧ (M₂ : ℝ) = -Λ / (1 - s)) ∧
    (shape α (α + 2 * β) α →
      (M₁ : ℝ) = Λ * s * (2 + s) / (1 + s) ∧ (M₂ : ℝ) = -Λ * s * (2 - s) / (1 - s)) ∧
    (shape (2 * α) α (2 * β) →
      (M₁ : ℝ) = Λ * s * (1 - s) * (2 + s) ∧ (M₂ : ℝ) = -Λ * s * (2 - s) * (1 + s)) ∧
    ((shape (2 * α) β (α + β) ∨ shape β (3 * α) β ∨ shape (α + β) α (α + β) ∨
        shape α (α + 2 * β) α ∨ shape (2 * α) α (2 * β)) → M₁ ≠ 0 ∧ M₂ ≠ 0) ∧
    (shape (2 * α) β (α + β) → Λ = M₁ / s) := by
  intro s Λ shape
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  obtain ⟨hα, hβ, hγ, hS, hc, ha, hb, ht0, ht1, -, -⟩ := model_facts D hrel hT
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨r1, r2, -, -, r5, r6, r7, r8⟩ := r
  rw [div_eq_iff hS.ne'] at r1 r2 r5 r6 r7 r8
  have sg := Phisigns D hrel hT' hns hccw
  dsimp only at sg
  obtain ⟨⟨p1, p2⟩, g1, g2, g3, g4, g5⟩ := sg
  set t := 2 * Real.cos (α + β)
  have hst : s = t := by simp only [s]; rw [ha]; field_simp
  have habc : a + b + c ≠ 0 := ne_of_gt (by
    rw [ha, hb]
    have : 0 < 2 + t - t ^ 2 := by nlinarith
    nlinarith [mul_pos hc this])
  have habc' : a - b - c ≠ 0 := ne_of_lt (by
    rw [ha, hb]
    have : 0 < 2 - t - t ^ 2 := by nlinarith
    nlinarith [mul_pos hc this])
  have hΛ : 0 < Λ := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have eM1 : (M₁ : ℝ) = PhiR (Phi1 (α + β) (baseDir D)) D.target / (a + b + c) := by
    rw [h₁]; field_simp
  have eM2 : (M₂ : ℝ) = PhiR (Phi2 (α + β) (baseDir D)) D.target / (a - b - c) := by
    rw [h₂]; field_simp
  rw [PhiR_target] at eM1 eM2
  simp only [target_side D hrel hT] at eM1 eM2
  rw [p1] at eM1
  rw [p2] at eM2
  have h1t : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have h1t' : 1 - t ≠ 0 := ne_of_gt (by linarith)
  have row1 : shape (2 * α) β (α + β) → (M₁ : ℝ) = Λ * s ∧ (M₂ : ℝ) = Λ * s := by
    rintro ⟨e0, e1, e2⟩
    obtain ⟨b1, c1, b2, c2⟩ := g1 ⟨e0, e1, e2⟩
    rw [b1, c1, e0, e1, e2, r5, r2] at eM1
    rw [b2, c2, e0, e1, e2, r5, r2] at eM2
    rw [hst, eM1, eM2]
    have hS' := hS.ne'
    constructor <;> field_simp <;> rw [ha, hb] <;> ring
  have row2 : shape β (3 * α) β →
      (M₁ : ℝ) = Λ * (1 - s) * (1 + s) ^ 2 ∧ (M₂ : ℝ) = -Λ * (1 - s) ^ 2 * (1 + s) := by
    rintro ⟨e0, e1, e2⟩
    obtain ⟨b1, c1, b2, c2⟩ := g2 ⟨e0, e1, e2⟩
    rw [b1, c1, e0, e1, e2, r2, r7] at eM1
    rw [b2, c2, e0, e1, e2, r2, r7] at eM2
    rw [hst, eM1, eM2]
    have hS' := hS.ne'
    constructor <;> field_simp <;> rw [ha, hb] <;> ring
  have row3 : shape (α + β) α (α + β) → (M₁ : ℝ) = Λ / (1 + s) ∧ (M₂ : ℝ) = -Λ / (1 - s) := by
    rintro ⟨e0, e1, e2⟩
    obtain ⟨b1, c1, b2, c2⟩ := g3 ⟨e0, e1, e2⟩
    rw [b1, c1, e0, e1, e2, r1] at eM1
    rw [b2, c2, e0, e1, e2, r1] at eM2
    rw [hst, eM1, eM2]
    have hS' := hS.ne'
    constructor <;> field_simp <;> rw [ha, hb] <;> ring
  have row4 : shape α (α + 2 * β) α →
      (M₁ : ℝ) = Λ * s * (2 + s) / (1 + s) ∧ (M₂ : ℝ) = -Λ * s * (2 - s) / (1 - s) := by
    rintro ⟨e0, e1, e2⟩
    obtain ⟨b1, c1, b2, c2⟩ := g4 ⟨e0, e1, e2⟩
    rw [b1, c1, e0, e1, e2, r1, r6] at eM1
    rw [b2, c2, e0, e1, e2, r1, r6] at eM2
    rw [hst, eM1, eM2]
    have hS' := hS.ne'
    constructor <;> field_simp <;> rw [ha, hb] <;> ring
  have row5 : shape (2 * α) α (2 * β) →
      (M₁ : ℝ) = Λ * s * (1 - s) * (2 + s) ∧ (M₂ : ℝ) = -Λ * s * (2 - s) * (1 + s) := by
    rintro ⟨e0, e1, e2⟩
    obtain ⟨b1, c1, b2, c2⟩ := g5 ⟨e0, e1, e2⟩
    rw [b1, c1, e0, e1, e2, r5, r1, r8] at eM1
    rw [b2, c2, e0, e1, e2, r5, r1, r8] at eM2
    rw [hst, eM1, eM2]
    have hS' := hS.ne'
    constructor <;> field_simp <;> rw [ha, hb] <;> ring
  refine ⟨row1, row2, row3, row4, row5, ?_, fun h => ?_⟩
  · rw [hst] at row1 row2 row3 row4 row5
    have hp : 0 < Λ * t := mul_pos hΛ ht0
    have ne : ∀ (x : ℝ) (m : ℤ), (m : ℝ) = x → x ≠ 0 → m ≠ 0 := fun x m hm hx h0 =>
      hx (by rw [← hm, h0, Int.cast_zero])
    rintro (h | h | h | h | h)
    · obtain ⟨e1, e2⟩ := row1 h
      exact ⟨ne _ _ e1 hp.ne', ne _ _ e2 hp.ne'⟩
    · obtain ⟨e1, e2⟩ := row2 h
      exact ⟨ne _ _ e1 (by positivity), ne _ _ e2 (by
        have : 0 < Λ * (1 - t) ^ 2 * (1 + t) := by positivity
        linarith)⟩
    · obtain ⟨e1, e2⟩ := row3 h
      exact ⟨ne _ _ e1 (by positivity), ne _ _ e2 (by
        have : 0 < Λ / (1 - t) := div_pos hΛ (by linarith)
        rw [neg_div]; linarith)⟩
    · obtain ⟨e1, e2⟩ := row4 h
      exact ⟨ne _ _ e1 (by positivity), ne _ _ e2 (by
        have : 0 < Λ * t * (2 - t) / (1 - t) := div_pos (by
          have : 0 < 2 - t := by linarith
          positivity) (by linarith)
        rw [show -Λ * t * (2 - t) / (1 - t) = -(Λ * t * (2 - t) / (1 - t)) by ring]; linarith)⟩
    · obtain ⟨e1, e2⟩ := row5 h
      exact ⟨ne _ _ e1 (by
        have : 0 < 1 - t := by linarith
        positivity), ne _ _ e2 (by
        have : 0 < Λ * t * (2 - t) * (1 + t) := by
          have : 0 < 2 - t := by linarith
          positivity
        linarith)⟩
  · rw [(row1 h).1, hst]; field_simp
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry Erdos634.BeesonColoring
variable {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
  (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel
omit D in
theorem int_indep {x y : ℤ} (e : (x : ℝ) * α + y * β = 0) : x = 0 ∧ y = 0 := by
  have key : ((x : ℝ) - 3 * y / 2) * α = -((y : ℝ) / 2) * Real.pi := by
    linear_combination e - (y : ℝ) / 2 * hrel
  by_cases hc : (x : ℝ) - 3 * y / 2 = 0
  · have hy : (y : ℝ) * Real.pi = 0 := by rw [hc, zero_mul] at key; linarith
    have hy' : (y : ℝ) = 0 := by
      rcases mul_eq_zero.mp hy with e | e
      · exact e
      · exact absurd e Real.pi_ne_zero
    have hx' : (x : ℝ) = 0 := by rw [hy'] at hc; linarith
    exact ⟨by exact_mod_cast hx', by exact_mod_cast hy'⟩
  · exfalso
    apply hirr
    refine ⟨-((y : ℚ) / 2) / ((x : ℚ) - 3 * y / 2), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hc]
    linear_combination key
include h
theorem model_angles : ∃ σ : Equiv.Perm (Fin 3), D.model.angleAt (σ 0) = α ∧
    D.model.angleAt (σ 1) = β ∧ D.model.angleAt (σ 2) = 2 * α + β := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  exact ⟨σ, h0, h1, h2⟩
theorem values_sep :
    (∀ j, ![α, β, 2 * α + β, Real.pi, 2 * Real.pi] j ≠ 0) ∧
      Function.Injective ![α, β, 2 * α + β, Real.pi, 2 * Real.pi] := by
  obtain ⟨hα, hβ, hα3, hβ2⟩ := angles_pos D hrel h
  have hπ := Real.pi_pos
  have hαβ : α ≠ β := fun e => hirr ⟨1 / 5, by push_cast; linarith⟩
  refine ⟨fun j => ?_, fun i j hij => ?_⟩
  · fin_cases j <;> simp <;> linarith
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first | exact hαβ hij | exact hαβ hij.symm | linarith
theorem anglesSep : AnglesSep D := by
  obtain ⟨σ, h0, h1, h2⟩ := model_angles D hirr hrel h
  obtain ⟨hv0, hinj⟩ := values_sep D hirr hrel h
  have hm : ∀ k : Fin 3, D.model.angleAt k = α ∨ D.model.angleAt k = β ∨
      D.model.angleAt k = 2 * α + β := by
    intro k
    obtain ⟨m, rfl⟩ := σ.surjective k
    fin_cases m
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)
  have e0 : tileα D = D.model.angleAt 0 := rfl
  have e1 : tileβ D = D.model.angleAt 1 := rfl
  have e2 : tileγ D = D.model.angleAt 2 := rfl
  have hd : ∀ i j : Fin 3, i ≠ j → D.model.angleAt i ≠ D.model.angleAt j := by
    intro i j hij e
    obtain ⟨m, rfl⟩ := σ.surjective i
    obtain ⟨m', rfl⟩ := σ.surjective j
    have hmm : m ≠ m' := fun h => hij (by rw [h])
    have v : ∀ m : Fin 3, D.model.angleAt (σ m) = ![α, β, 2 * α + β, Real.pi, 2 * Real.pi]
        (Fin.castLE (by norm_num) m) := by
      intro m; fin_cases m <;> simp [h0, h1, h2]
    rw [v, v] at e
    exact hmm (Fin.castLE_injective _ (hinj e))
  have hp : ∀ k, 0 < D.model.angleAt k := fun k => D.model.angleAt_pos' k
  have hl : ∀ k, D.model.angleAt k < Real.pi := fun k => tri_angle_lt_pi D.model k
  have hπ := Real.pi_pos
  refine ⟨fun j => ?_, fun i j hij => ?_⟩
  · fin_cases j <;> simp [e0, e1, e2]
    · exact (hp 0).ne'
    · exact (hp 1).ne'
    · exact (hp 2).ne'
  · fin_cases i <;> fin_cases j <;> simp [e0, e1, e2] at hij ⊢ <;>
      first
      | exact hd _ _ (by decide) hij
      | (have := hl 0; linarith) | (have := hl 1; linarith) | (have := hl 2; linarith)
      | linarith
theorem localAngle_cases (P : Plane) (i : Fin N) :
    (∃ j, (D.tile i).localAngle P = ![α, β, 2 * α + β, Real.pi, 2 * Real.pi] j) ∨
      (D.tile i).localAngle P = 0 := by
  obtain ⟨σ, h0, h1, h2⟩ := model_angles D hirr hrel h
  have hm : ∀ k : Fin 3, ∃ j : Fin 5, D.model.angleAt k = ![α, β, 2 * α + β, Real.pi, 2 * Real.pi] j := by
    intro k
    obtain ⟨m, rfl⟩ := σ.surjective k
    fin_cases m
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
  rcases localAngle_mem D P i with e | e | e | e | e | e
  · obtain ⟨j, hj⟩ := hm 0; exact Or.inl ⟨j, e.trans hj⟩
  · obtain ⟨j, hj⟩ := hm 1; exact Or.inl ⟨j, e.trans hj⟩
  · obtain ⟨j, hj⟩ := hm 2; exact Or.inl ⟨j, e.trans hj⟩
  · exact Or.inl ⟨3, e⟩
  · exact Or.inl ⟨4, e⟩
  · exact Or.inr e
theorem counts_sum (P : Plane) :
    (angleCount D P α : ℝ) * α + angleCount D P β * β + angleCount D P (2 * α + β) * (2 * α + β)
      + angleCount D P Real.pi * Real.pi + angleCount D P (2 * Real.pi) * (2 * Real.pi)
      = D.target.localAngle P := by
  classical
  obtain ⟨hv0, hinj⟩ := values_sep D hirr hrel h
  have hc := sum_eq_counts (fun i => (D.tile i).localAngle P) _ hv0 hinj
    (localAngle_cases D hirr hrel h P)
  rw [D.toDissection.sum_localAngle_eq P, Fin.sum_univ_five] at hc
  rw [hc]
  simp only [angleCount]
  rfl
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry Erdos634.BeesonColoring
variable {N : ℕ} (D : CongruentDissection N)
variable {α β a b c : ℝ}
theorem others (x y z : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by
  revert x y z; decide
section Relation
variable (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel h
theorem counts_lin (P : Plane) (t : ℕ) (ht : D.target.localAngle P = t * Real.pi) :
    ((angleCount D P α : ℤ) + 2 * angleCount D P (2 * α + β)
        = 3 * (t - (angleCount D P Real.pi + 2 * angleCount D P (2 * Real.pi)))) ∧
      ((angleCount D P β : ℤ) + angleCount D P (2 * α + β)
        = 2 * (t - (angleCount D P Real.pi + 2 * angleCount D P (2 * Real.pi)))) := by
  have hs := counts_sum D hirr hrel h P
  rw [ht] at hs
  set nα := angleCount D P α
  set nβ := angleCount D P β
  set nγ := angleCount D P (2 * α + β)
  set nπ := angleCount D P Real.pi
  set n2 := angleCount D P (2 * Real.pi)
  have key := int_indep hirr hrel (x := nα + 2 * nγ - 3 * (t - (nπ + 2 * n2)))
    (y := nβ + nγ - 2 * (t - (nπ + 2 * n2)))
    (by push_cast; linear_combination hs + ((nπ : ℝ) + 2 * n2 - t) * hrel)
  omega
theorem side_counts {P : Plane} (hP : P ∈ frontier D.target.carrier)
    (hnc : P ∉ Set.range D.target.pts) :
    ((angleCount D P α : ℤ) + 2 * angleCount D P (2 * α + β)
        = 3 * (1 - (angleCount D P Real.pi + 2 * angleCount D P (2 * Real.pi)))) ∧
      ((angleCount D P β : ℤ) + angleCount D P (2 * α + β)
        = 2 * (1 - (angleCount D P Real.pi + 2 * angleCount D P (2 * Real.pi)))) :=
  counts_lin D hirr hrel h P 1 (by rw [Tri.localAngle_frontier _ hP hnc]; push_cast; ring)
end Relation
section TQ
variable (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel h
theorem tile_vals (x : ℝ) : (x = tileα D ∨ x = tileβ D ∨ x = tileγ D) ↔
    (x = α ∨ x = β ∨ x = 2 * α + β) := by
  obtain ⟨σ, h0, h1, h2⟩ := model_angles D hirr hrel h
  have e0 : tileα D = D.model.angleAt 0 := rfl
  have e1 : tileβ D = D.model.angleAt 1 := rfl
  have e2 : tileγ D = D.model.angleAt 2 := rfl
  rw [e0, e1, e2]
  have hk : ∀ y, (y = D.model.angleAt 0 ∨ y = D.model.angleAt 1 ∨ y = D.model.angleAt 2) ↔
      ∃ k, y = D.model.angleAt k := by
    intro y; constructor
    · rintro (h | h | h) <;> exact ⟨_, h⟩
    · rintro ⟨k, rfl⟩; fin_cases k <;> simp
  have hk' : ∀ y, (y = α ∨ y = β ∨ y = 2 * α + β) ↔ ∃ m, y = D.model.angleAt (σ m) := by
    intro y; rw [← h2, ← h0, ← h1]; constructor
    · rintro (h | h | h) <;> exact ⟨_, h⟩
    · rintro ⟨m, rfl⟩; fin_cases m <;> simp
  rw [hk, hk']
  constructor
  · rintro ⟨k, rfl⟩; obtain ⟨m, rfl⟩ := σ.surjective k; exact ⟨m, rfl⟩
  · rintro ⟨m, rfl⟩; exact ⟨_, rfl⟩
end TQ
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open Erdos634.BeesonColoring
variable {N : ℕ} (D : CongruentDissection N)
section Normalize
open Erdos634.MirrorGauge in
theorem mirror_angleAt (T : Tri) (k : Fin 3) : (Erdos634.MirrorGauge.Tri.mirror T).angleAt k = T.angleAt k := by
  have hn : ∀ v : Plane, ‖mirrorL v‖ = ‖v‖ := by
    intro v
    have := mirrorPt_dist v 0
    have h0 : mirrorPt 0 = 0 := by ext i; fin_cases i <;> simp
    rw [h0, dist_zero_right, dist_zero_right] at this
    exact this
  let f : Plane →ₗᵢ[ℝ] Plane := ⟨mirrorL, hn⟩
  unfold Tri.angleAt cornerAngle
  exact f.toAffineIsometry.angle_map _ _ _
open Erdos634.MirrorGauge in
theorem mirror_oppLen (T : Tri) (k : Fin 3) : (Erdos634.MirrorGauge.Tri.mirror T).oppLen k = T.oppLen k :=
  mirrorPt_dist _ _
theorem relabel_angleAt (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabelTarget D σ).target.angleAt k = D.target.angleAt (σ k) := by
  have d1 : σ k ≠ σ (k + 1) := σ.injective.ne (fin3_ne_add_one k)
  have d2 : σ k ≠ σ (k + 2) := σ.injective.ne ((by decide : ∀ x : Fin 3, x ≠ x + 2) k)
  have d12 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne ((by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k)
  show cornerAngle (D.target.pts (σ (k + 1))) (D.target.pts (σ k)) (D.target.pts (σ (k + 2))) = _
  unfold Tri.angleAt cornerAngle
  rcases others _ _ _ d1 d2 d12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
  exact EuclideanGeometry.angle_comm _ _ _
theorem relabel_oppLen (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabelTarget D σ).target.oppLen k = D.target.oppLen (σ k) := by
  have d1 : σ k ≠ σ (k + 1) := σ.injective.ne (fin3_ne_add_one k)
  have d2 : σ k ≠ σ (k + 2) := σ.injective.ne ((by decide : ∀ x : Fin 3, x ≠ x + 2) k)
  have d12 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne ((by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k)
  show dist (D.target.pts (σ (k + 1))) (D.target.pts (σ (k + 2))) = _
  unfold Tri.oppLen
  rcases others _ _ _ d1 d2 d12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
  exact dist_comm _ _
theorem similar_of_relabel (σ : Equiv.Perm (Fin 3)) (h : SimilarTM (relabelTarget D σ)) :
    SimilarTM D := by
  obtain ⟨μ, τ, hτ⟩ := h
  refine ⟨μ, σ.symm.trans τ, fun k => ?_⟩
  obtain ⟨k', rfl⟩ := σ.surjective k
  have := hτ k'
  rw [relabel_angleAt, relabel_oppLen] at this
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  exact this
theorem similar_of_mirror (h : SimilarTM (Erdos634.MirrorGauge.CongruentDissection.mirror D)) :
    SimilarTM D := by
  obtain ⟨μ, τ, hτ⟩ := h
  refine ⟨μ, τ, fun k => ?_⟩
  have := hτ k
  change (Erdos634.MirrorGauge.Tri.mirror D.target).angleAt k = _ ∧
    (Erdos634.MirrorGauge.Tri.mirror D.target).oppLen k = _ at this
  rw [mirror_angleAt, mirror_oppLen] at this
  exact this
theorem normalize {x y z : ℝ} (hxyz : TgtAngles D x y z) (hns : ¬ SimilarTM D) :
    ∃ D' : CongruentDissection N, D'.model = D.model ∧ ¬ SimilarTM D' ∧ 0 < D'.target.det ∧
      D'.target.angleAt 0 = x ∧ D'.target.angleAt 1 = y ∧ D'.target.angleAt 2 = z := by
  obtain ⟨σ, h0, h1, h2⟩ := hxyz
  set D₁ := relabelTarget D σ
  have hns₁ : ¬ SimilarTM D₁ := fun h => hns (similar_of_relabel D σ h)
  have a0 : D₁.target.angleAt 0 = x := by rw [relabel_angleAt]; exact h0
  have a1 : D₁.target.angleAt 1 = y := by rw [relabel_angleAt]; exact h1
  have a2 : D₁.target.angleAt 2 = z := by rw [relabel_angleAt]; exact h2
  rcases D₁.target.det_pos_or_neg with hd | hd
  · exact ⟨D₁, rfl, hns₁, hd, a0, a1, a2⟩
  · set D₂ := Erdos634.MirrorGauge.CongruentDissection.mirror D₁
    refine ⟨D₂, rfl, fun h => hns₁ (similar_of_mirror D₁ h), ?_, ?_, ?_, ?_⟩
    · change 0 < (Erdos634.MirrorGauge.Tri.mirror D₁.target).det
      rw [Erdos634.MirrorGauge.Tri.det_mirror]; linarith
    · change (Erdos634.MirrorGauge.Tri.mirror D₁.target).angleAt 0 = x
      rw [mirror_angleAt]; exact a0
    · change (Erdos634.MirrorGauge.Tri.mirror D₁.target).angleAt 1 = y
      rw [mirror_angleAt]; exact a1
    · change (Erdos634.MirrorGauge.Tri.mirror D₁.target).angleAt 2 = z
      rw [mirror_angleAt]; exact a2
theorem tileSides_of_model {D' : CongruentDissection N} (hm : D'.model = D.model)
    {α β γ a b c : ℝ} (hT : TileSides D α β γ a b c) : TileSides D' α β γ a b c := by
  unfold TileSides; rw [hm]; exact hT
end Normalize
def _root_.OMACut_RT : Prop := ∀ {N : ℕ} (D : CongruentDissection N) {α β γ a b c : ℝ},
    Erdos634.Draft.TheoremPConditional.IrrPi α → 3 * α + 2 * β = Real.pi → TileSides D α β γ a b c →
      ¬ SimilarTM D → RationalTile a b c
theorem rationaltile [hcut : Fact OMACut_RT] {α β γ a b c : ℝ}
    [hI : Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) : RationalTile a b c :=
  hcut.out D hI.out hrel hT hns
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open Erdos634.BeesonColoring
variable {N : ℕ} (D : CongruentDissection N)
theorem angles_of_similar {α β γ a b c : ℝ} (hT : TileSides D α β γ a b c) (hs : SimilarTM D)
    (k : Fin 3) : D.target.angleAt k = α ∨ D.target.angleAt k = β ∨ D.target.angleAt k = γ := by
  obtain ⟨μ, τ, hτ⟩ := hs
  obtain ⟨σ, h0, h1, h2, -⟩ := hT
  rw [(hτ k).1]
  obtain ⟨m, hm⟩ := σ.surjective (τ k)
  rw [← hm]
  fin_cases m
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h2)
theorem not_similar_of_alpha_beta {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) {k : Fin 3} (hk : D.target.angleAt k = α + β) :
    ¬ SimilarTM D := by
  intro hs
  obtain ⟨hα, hβ, hγ, -⟩ := model_facts D hrel hT
  rcases angles_of_similar D hT hs k with e | e | e <;> rw [hk] at e <;> linarith
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
theorem zmod8_c : ∀ m k : ZMod 8, ¬ (4 * m = 0 ∧ 4 * k = 0) → 4 * (m + k) = 0 →
    4 ∣ (3 * k ^ 2 - m ^ 2).val → False := by decide
theorem notprime4_arith {N M m k : ℤ} (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k)
    (heq : N * (m + k) ^ 2 = M ^ 2 * (3 * k ^ 2 - m ^ 2)) : (m + k) ∣ M := by
  set d := m + k
  set Y := 3 * k ^ 2 - m ^ 2
  have hd0 : d ≠ 0 := by simp only [d]; omega
  have hdk : IsCoprime d k := by
    have : d = m + k * 1 := by simp only [d]; ring
    rw [this]; exact (IsCoprime.add_mul_left_left_iff).mpr hcop
  have hcomm : ∀ t : ℤ, t ∣ d → t ∣ Y → t ∣ 2 := by
    intro t htd htY
    have h2k : t ∣ 2 * k ^ 2 := by
      have : 2 * k ^ 2 = Y - d * (2 * k - d) := by simp only [Y, d]; ring
      rw [this]; exact dvd_sub htY (dvd_mul_of_dvd_left htd _)
    have htk : IsCoprime t (k ^ 2) := (hdk.of_isCoprime_of_dvd_left htd).pow_right
    exact htk.dvd_of_dvd_mul_right h2k
  by_cases hM : M = 0
  · rw [hM]; exact dvd_zero _
  obtain ⟨g, M', d', hg, hgcd, hMg, hdg⟩ := Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left d hM)
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have heq' : N * d' ^ 2 = M' ^ 2 * Y := by
    rw [hMg, hdg] at heq
    have : ((g : ℤ) ^ 2) * (N * d' ^ 2) = ((g : ℤ) ^ 2) * (M' ^ 2 * Y) := by linear_combination heq
    exact mul_left_cancel₀ (pow_ne_zero 2 hg0) this
  have hcop' : IsCoprime (d' ^ 2) (M' ^ 2) := ((Int.isCoprime_iff_gcd_eq_one.mpr hgcd).symm).pow
  have hd'Y : d' ^ 2 ∣ Y := hcop'.dvd_of_dvd_mul_left ⟨N, by rw [← heq']; ring⟩
  have hd'd : d' ∣ d := ⟨g, by rw [hdg]⟩
  have hd'2 : d' ∣ 2 := hcomm d' hd'd (dvd_trans (dvd_pow_self d' two_ne_zero) hd'Y)
  have hd'1 : d' = 1 ∨ d' = -1 := by
    have hle : d'.natAbs ∣ 2 := by
      have := Int.natAbs_dvd_natAbs.mpr hd'2; simpa using this
    have h2 : d'.natAbs = 1 ∨ d'.natAbs = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hle with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases h2 with h | h
    · exact Int.natAbs_eq_iff.mp h |>.imp (by simp) (by simp)
    · exfalso
      have h4 : (4 : ℤ) ∣ Y := by
        have : (4 : ℤ) = d' ^ 2 := by
          rcases Int.natAbs_eq_iff.mp h with e | e <;> rw [e] <;> norm_num
        rw [this]; exact hd'Y
      have h2d : (2 : ℤ) ∣ d := by
        have : (2 : ℤ) ∣ d' := by
          rcases Int.natAbs_eq_iff.mp h with e | e <;> rw [e] <;> norm_num
        exact dvd_trans this hd'd
      have hne : ¬ (4 * (m : ZMod 8) = 0 ∧ 4 * (k : ZMod 8) = 0) := by
        rintro ⟨h1, h2⟩
        have h1' : ((4 * m : ℤ) : ZMod 8) = 0 := by push_cast; exact h1
        have h2' : ((4 * k : ℤ) : ZMod 8) = 0 := by push_cast; exact h2
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1' h2'
        have hm2 : (2 : ℤ) ∣ m := by obtain ⟨t, ht⟩ := h1'; push_cast at ht; exact ⟨t, by linarith⟩
        have hk2 : (2 : ℤ) ∣ k := by obtain ⟨t, ht⟩ := h2'; push_cast at ht; exact ⟨t, by linarith⟩
        have := hcop.isUnit_of_dvd' hm2 hk2
        rw [Int.isUnit_iff] at this; omega
      have hd8 : 4 * ((m : ZMod 8) + k) = 0 := by
        obtain ⟨t, ht⟩ := h2d
        have : ((d : ℤ) : ZMod 8) = ((2 * t : ℤ) : ZMod 8) := by rw [ht]
        simp only [d] at this
        push_cast at this
        rw [this]
        have : (8 : ZMod 8) = 0 := by decide
        linear_combination (t : ZMod 8) * this
      apply zmod8_c _ _ hne hd8
      obtain ⟨t, ht⟩ := h4
      have : ((3 * (k : ZMod 8) ^ 2 - (m : ZMod 8) ^ 2)) = 4 * (t : ZMod 8) := by
        have := congrArg (fun x : ℤ => (x : ZMod 8)) ht
        simp only [Y] at this; push_cast at this; exact this
      rw [this]
      have : ∀ x : ZMod 8, 4 ∣ (4 * x).val := by decide
      exact this _
  rcases hd'1 with h | h
  · rw [hdg, h, one_mul] at *; exact ⟨M', by rw [hMg]; ring⟩
  · exact ⟨-M', by rw [hMg, hdg, h]; ring⟩
theorem notprime3_arith {N : ℕ} {M m k p q r : ℤ} (hN : N.Prime) (hM : 0 < M) (hm : 0 < m)
    (hmk : m < k) (hcop : IsCoprime m k) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 1 ≤ r)
    (h1 : ((N : ℤ) + M ^ 2) * m = ((N : ℤ) - M ^ 2) * k)
    (h2 : M * (k + m) * m = p * (m * k) + q * (k ^ 2 - m ^ 2) + r * k ^ 2) : False := by
  have hk : 0 < k := by linarith
  have hkd : k ∣ ((N : ℤ) + M ^ 2) := by
    have : k ∣ ((N : ℤ) + M ^ 2) * m := ⟨(N : ℤ) - M ^ 2, by rw [h1]; ring⟩
    exact hcop.symm.dvd_of_dvd_mul_right this
  obtain ⟨u, hu⟩ := hkd
  have hu' : (N : ℤ) - M ^ 2 = m * u := by
    have : k * ((N : ℤ) - M ^ 2) = k * (m * u) := by linear_combination (-1) * h1 + m * hu
    exact mul_left_cancel₀ hk.ne' this
  have hN2 : (2 : ℤ) ≤ N := by exact_mod_cast hN.two_le
  have hu0 : 0 < u := by
    have : (0 : ℤ) < k * u := by rw [← hu]; positivity
    exact pos_of_mul_pos_right this hk.le
  have hNM : (M : ℤ) ^ 2 < N := by have : 0 < m * u := mul_pos hm hu0; linarith
  have hcopN : IsCoprime (N : ℤ) (M ^ 2) := by
    have hnd : ¬ N ∣ M.natAbs ^ 2 := by
      intro hd
      have hdM : N ∣ M.natAbs := hN.dvd_of_dvd_pow hd
      have h0 : 0 < M.natAbs := Int.natAbs_pos.mpr hM.ne'
      have := Nat.le_of_dvd h0 hdM
      have hsq : (M.natAbs : ℤ) ^ 2 = M ^ 2 := Int.natAbs_sq M
      have : (N : ℤ) ≤ M.natAbs := by exact_mod_cast this
      nlinarith
    have := (Nat.Prime.coprime_iff_not_dvd hN).mpr hnd
    have := Nat.isCoprime_iff_coprime.mpr this
    push_cast at this
    rwa [sq_abs] at this
  obtain ⟨x, y, hxy⟩ := hcopN
  have hu2 : u ∣ 2 := by
    have e : (2 : ℤ) = x * (u * (k + m)) + y * (u * (k - m)) := by
      have hs : u * (k + m) = 2 * N := by linear_combination -hu - hu'
      have hd : u * (k - m) = 2 * M ^ 2 := by linear_combination -hu + hu'
      rw [hs, hd]; linear_combination -2 * hxy
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
      (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  have hu12 : u ≤ 2 := Int.le_of_dvd (by norm_num) hu2
  have hkm : M ^ 2 ≤ k - m := by
    have hd : u * (k - m) = 2 * M ^ 2 := by linear_combination -hu + hu'
    nlinarith
  have hqM : k ∣ M + q := by
    have : k ∣ (M + q) * m ^ 2 := ⟨p * m + q * k + r * k - M * m, by linear_combination h2⟩
    exact hcop.symm.pow_right.dvd_of_dvd_mul_right this
  obtain ⟨t, ht⟩ := hqM
  have ht1 : 1 ≤ t := by
    by_contra h0; push Not at h0
    have : k * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le (by omega)
    linarith
  have hqk : k - M ≤ q := by nlinarith
  have hkm2 : 0 < k ^ 2 - m ^ 2 := by nlinarith
  have hkey : (k - M) * (k ^ 2 - m ^ 2) - M * m * (k + m) = k * (k + m) * (k - m - M) := by ring
  have hpos : 0 ≤ k * (k + m) * (k - m - M) := by
    apply mul_nonneg (by positivity)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hqk hkm2.le, mul_nonneg hp (mul_pos hm hk).le]
theorem notprime5_arith {N : ℕ} {j m k : ℤ} (hN : N.Prime) (hj : 0 < j) (hm : 0 < m)
    (hmk : m < k) (hcop : IsCoprime m k)
    (h : (N : ℤ) * (k - m) = j ^ 2 * (m + k) * (2 * k ^ 2 - m ^ 2)) : False := by
  have hc1 : IsCoprime m (k - m) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨u + v, v, by linear_combination huv⟩
  obtain ⟨u, v, huv⟩ := hc1.pow_left (m := 2)
  have hc2 : IsCoprime (2 * k ^ 2 - m ^ 2) (k - m) :=
    ⟨u, v - 2 * u * (k + m), by linear_combination huv⟩
  have hd : (2 * k ^ 2 - m ^ 2) ∣ (N : ℤ) :=
    hc2.dvd_of_dvd_mul_right ⟨j ^ 2 * (m + k), by rw [h]; ring⟩
  have hd1 : 1 < 2 * k ^ 2 - m ^ 2 := by nlinarith
  have hj2 : 1 ≤ j ^ 2 := by nlinarith
  have hdN : 2 * k ^ 2 - m ^ 2 < (N : ℤ) := by
    have hkm : 0 < k - m := by linarith
    have : (2 * k ^ 2 - m ^ 2) * (k - m) < (N : ℤ) * (k - m) := by
      have e1 : k - m < j ^ 2 * (m + k) := by nlinarith
      rw [h, mul_comm (2 * k ^ 2 - m ^ 2)]
      exact mul_lt_mul_of_pos_right e1 (by linarith)
    exact lt_of_mul_lt_mul_right this hkm.le
  have hd' : (2 * k ^ 2 - m ^ 2).natAbs ∣ N := by
    have := Int.natAbs_dvd_natAbs.mpr hd
    simpa using this
  rcases hN.eq_one_or_self_of_dvd _ hd' with e | e <;> omega
section Corners
open Erdos634.Geometry Erdos634.BeesonColoring
variable {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
  (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
  (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β
      (2 * α + β))
include hirr hrel h hns
theorem corner_counts (k : Fin 3) {p q : ℕ} (hk : D.target.angleAt k = p * α + q * β) :
    vcount D k α = p ∧ vcount D k β = q ∧ tilesAt D k = p + q := by
  rcases lemma6 D hirr hrel h with hs | ⟨hz, -, -, -⟩
  · exact absurd hs hns
  have hc := corner_eq D hirr hrel h hz k
  rw [hk] at hc
  obtain ⟨e1, e2⟩ := indep hirr hrel hc.symm
  exact ⟨e1, e2, by rw [tilesAt_eq D hirr hrel h k (hz k), e1, e2]⟩
omit hirr hrel h hns in
open Classical in
theorem atB_onAB (h1 : tilesAt D 1 = 1) {i₀ : Fin N} (hi₀ : TileAt D 1 i₀) : AtBOnAB D i₀ := by
  obtain ⟨part, hcov, -, -⟩ := D.toDissection.side_walk 0
  have hcov' : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1) := hcov
  obtain ⟨e, he, hV⟩ := side_edge_at_end D hcov' (V := D.target.pts 1) (Or.inr rfl)
  have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) := by
    rw [← hcov']; intro y hy; exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  have heq : e.1 = i₀ := by
    have hmem : ∀ i, TileAt D 1 i → i ∈ ({i | TileAt D 1 i} : Finset (Fin N)) := fun i hi => by
      simp [hi]
    have h1' : ({i | TileAt D 1 i} : Finset (Fin N)).card = 1 := h1
    have he1 : TileAt D 1 e.1 := by
      rcases hV with h' | h'
      · exact ⟨_, h'⟩
      · exact ⟨_, h'⟩
    exact Finset.card_le_one.mp h1'.le _ (hmem _ he1) _ (hmem _ hi₀)
  subst heq
  rcases hV with h' | h'
  · exact ⟨e.2, e.2 + 1, fin3_ne_add_one e.2, h', hsub (right_mem_segment ℝ _ _)⟩
  · exact ⟨e.2 + 1, e.2, (fin3_ne_add_one e.2).symm, h', hsub (left_mem_segment ℝ _ _)⟩
omit hirr hrel h hns in
theorem exists_atB_onAB : ∃ i, AtBOnAB D i := by
  obtain ⟨part, hcov, -, -⟩ := D.toDissection.side_walk 0
  have hcov' : (⋃ e ∈ part, (D.tile e.1).edge e.2) =
      segment ℝ (D.target.pts 0) (D.target.pts 1) := hcov
  obtain ⟨e, he, hV⟩ := side_edge_at_end D hcov' (V := D.target.pts 1) (Or.inr rfl)
  have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) := by
    rw [← hcov']; intro y hy; exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  refine ⟨e.1, ?_⟩
  rcases hV with h' | h'
  · exact ⟨e.2, e.2 + 1, fin3_ne_add_one e.2, h', hsub (right_mem_segment ℝ _ _)⟩
  · exact ⟨e.2 + 1, e.2, (fin3_ne_add_one e.2).symm, h', hsub (left_mem_segment ℝ _ _)⟩
open Classical in
theorem side_decomp (j : Fin 3) :
    ∃ p q r : ℕ, 1 ≤ r ∧ dist (D.target.pts j) (D.target.pts (j + 1)) = p * a + q * b + r * c := by
  rcases lemma6 D hirr hrel h with hs | ⟨hz, -, -, -⟩
  · exact absurd hs hns
  have hsep := anglesSep D hirr hrel h
  obtain ⟨hα, hβ, hα3, hβ2⟩ := angles_pos D hrel h
  have hπ := Real.pi_pos
  obtain ⟨part, hcov, hdisj, hsum⟩ := D.toDissection.side_walk j
  have hlen : ∀ e : Fin N × Fin 3, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = (if edgeType D α e then a else 0) + (if edgeType D β e then b else 0) +
        (if edgeType D (2 * α + β) e then c else 0) := by
    intro e
    obtain ⟨ρ, h0, l0, h1, l1, h2, l2⟩ := tile_threeAlpha D h e.1
    have hd : dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = (D.tile e.1).oppLen (e.2 + 2) := by
      unfold Tri.oppLen
      rw [(by decide : ∀ x : Fin 3, x + 2 + 1 = x) e.2,
        (by decide : ∀ x : Fin 3, x + 2 + 2 = x + 1) e.2]
    have ht : ∀ x, edgeType D x e ↔ (D.tile e.1).angleAt (e.2 + 2) = x := by
      intro x; unfold edgeType; rw [localAngle_pts]
    simp only [ht]
    rw [hd]
    obtain ⟨u, hu⟩ := ρ.surjective (e.2 + 2)
    rw [← hu]
    have hαβ : α ≠ β := fun e => hirr ⟨1 / 5, by push_cast; linarith⟩
    fin_cases u
    · simp [h0, l0, hαβ, show α ≠ 2 * α + β by intro e; linarith]
    · simp [h1, l1, hαβ.symm, show β ≠ 2 * α + β by intro e; linarith]
    · simp [h2, l2, show 2 * α + β ≠ α by intro e; linarith, show 2 * α + β ≠ β by intro e; linarith]
  refine ⟨(part.filter (edgeType D α)).card, (part.filter (edgeType D β)).card,
    (part.filter (edgeType D (2 * α + β))).card, ?_, ?_⟩
  · 
    have htwo : ∀ i : Fin 3, ∀ P ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1)),
        (Finset.univ.filter fun jj => (D.tile jj).localAngle P = 2 * α + β).card ≤ 1 := by
      intro i P hP
      change angleCount D P (2 * α + β) ≤ 1
      by_cases hPc : P ∈ Set.range D.target.pts
      · obtain ⟨m, rfl⟩ := hPc
        rw [show angleCount D (D.target.pts m) (2 * α + β) = 0 from hz m]; omega
      · obtain ⟨e1, -⟩ := side_counts D hirr hrel h (tri_side_subset_frontier D.target i hP) hPc
        omega
    have hγv : 2 * α + β = tileα D ∨ 2 * α + β = tileβ D ∨ 2 * α + β = tileγ D :=
      (tile_vals D hirr hrel h _).2 (Or.inr (Or.inr rfl))
    obtain ⟨ec, hec, hθc⟩ := side_has_edge_sep D hsep _ hγv j part hcov hdisj
      (fun e _ _ => ne_of_angleCount_zero D (hz j) e.1)
      (fun e _ _ => ne_of_angleCount_zero D (hz (j + 1)) e.1) (htwo j)
    exact Finset.card_pos.mpr ⟨ec, Finset.mem_filter.mpr ⟨hec, hθc⟩⟩
  · rw [← hsum, Finset.sum_congr rfl fun e _ => hlen e, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_ite]
    simp only [Finset.sum_const, add_zero, nsmul_eq_mul, mul_zero]
end Corners
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open Erdos634.BeesonColoring
variable {N : ℕ} (D : CongruentDissection N)
theorem isobeta_core {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    ((∑ i, ε i : ℤ) : ℝ) = Lam D * (1 - a / c) * (1 + a / c) ^ 2 ∧
      (N : ℝ) = Lam D ^ 2 * ((1 - (a / c) ^ 2) ^ 2 * (3 - (a / c) ^ 2)) ∧ 0 < a / c ∧ a / c < 1 ∧
      0 < Lam D := by
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hns3 := not_triple3 D hrel hT' hns
  obtain ⟨-, -, t0⟩ := corner_counts D hirr hrel h hns3 0 (p := 0) (q := 1)
    (by rw [hshape.1]; push_cast; ring)
  obtain ⟨-, -, t2⟩ := corner_counts D hirr hrel h hns3 2 (p := 0) (q := 1)
    (by rw [hshape.2.2]; push_cast; ring)
  obtain ⟨hα, hβ, hγ, hS, hc, ha, hb', ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hcol := (coloring D hrel hT hns).2 (by rw [t0, t2]) ε i₀ hε hi₀ hb
  have hM := hcol.1 (Or.inr ⟨hshape.1, hshape.2.2⟩)
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨-, r2, -, -, -, -, r7, -⟩ := r
  rw [div_eq_iff hS.ne'] at r2 r7
  have s0 := target_side D hrel hT 0
  have s1 := target_side D hrel hT 1
  have s2 := target_side D hrel hT 2
  rw [hshape.1, r2] at s0
  rw [hshape.2.1, r7] at s1
  rw [hshape.2.2, r2] at s2
  set t := 2 * Real.cos (α + β)
  have hst : a / c = t := by rw [ha]; field_simp
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have ar := (shapeareas D hrel hT).2.1 hshape
  rw [hst] at ar
  rw [hst]
  have hS' := hS.ne'
  have s0' : D.target.oppLen 0 = Lam D * c * (1 - t ^ 2) := by rw [s0]; field_simp
  have s1' : D.target.oppLen 1 = Lam D * c * (t * (1 - t ^ 2) * (3 - t ^ 2)) := by
    rw [s1]; field_simp
  have s2' : D.target.oppLen 2 = Lam D * c * (1 - t ^ 2) := by rw [s2]; field_simp
  refine ⟨?_, by rw [← ar]; field_simp, ht0, ht1, hΛ⟩
  have key : ((∑ i, ε i : ℤ) : ℝ) * (c * ((2 - t) * (1 + t))) =
      Lam D * (1 - t) * (1 + t) ^ 2 * (c * ((2 - t) * (1 + t))) := by
    rw [s0', s1', s2', ha, hb'] at hM
    linear_combination hM
  have h2 : (0 : ℝ) < (2 - t) * (1 + t) := by
    have : 0 < 2 - t := by linarith
    positivity
  exact mul_right_cancel₀ (by positivity) key

theorem tilingequation3 {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β)
    {a' b' c' : ℕ} (hint : a = a' ∧ b = b' ∧ c = c') (hprim : Nat.gcd (Nat.gcd a' b') c' = 1)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    let s := a / c
    let M : ℤ := ∑ i, ε i
    0 < (N : ℝ) / 3 ∧ (N : ℝ) / 3 < (M : ℝ) ^ 2 ∧ (M : ℝ) ^ 2 < 2 * N ∧
      (N : ℝ) / (M : ℝ) ^ 2 = (3 - s ^ 2) / (1 + s) ^ 2 ∧
      s = (Real.sqrt (3 * (M : ℝ) ^ 2 + 2 * N) * M - N) / ((M : ℝ) ^ 2 + N) := by
  intro s M
  obtain ⟨eM, eN, ht0, ht1, hΛ⟩ := isobeta_core D hrel hT hns hshape hε hi₀ hb
  set t := a / c
  have hMpos : (0 : ℝ) < M := by
    rw [eM]
    have : 0 < 1 - t := by linarith
    positivity
  have hM0 : (M : ℝ) ≠ 0 := hMpos.ne'
  have hf : (N : ℝ) = (M : ℝ) ^ 2 * ((3 - t ^ 2) / (1 + t) ^ 2) := by
    rw [eN, eM]
    have : (1 : ℝ) + t ≠ 0 := by positivity
    field_simp; ring
  have hNM : (N : ℝ) / (M : ℝ) ^ 2 = (3 - t ^ 2) / (1 + t) ^ 2 := by
    rw [hf]; field_simp
  have hlo : 1 / 2 < (3 - t ^ 2) / (1 + t) ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hhi : (3 - t ^ 2) / (1 + t) ^ 2 < 3 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, hNM, ?_⟩
  · rw [hf]; have : 0 < (3 - t ^ 2) / (1 + t) ^ 2 := by linarith
    positivity
  · rw [hf]; nlinarith
  · rw [hf]; nlinarith
  · 
    have hquad : ((M : ℝ) ^ 2 + N) * t ^ 2 + 2 * N * t + N - 3 * (M : ℝ) ^ 2 = 0 := by
      have h1 : (N : ℝ) * (1 + t) ^ 2 = (M : ℝ) ^ 2 * (3 - t ^ 2) := by
        rw [hf]; have : (1 : ℝ) + t ≠ 0 := by positivity
        field_simp
      linear_combination h1
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hR := Real.sq_sqrt (show (0 : ℝ) ≤ 3 * (M : ℝ) ^ 2 + 2 * N by positivity)
    have hRnn := Real.sqrt_nonneg (3 * (M : ℝ) ^ 2 + 2 * N)
    have hsq : (((M : ℝ) ^ 2 + N) * t + N) ^ 2 =
        (Real.sqrt (3 * (M : ℝ) ^ 2 + 2 * N) * M) ^ 2 := by
      rw [mul_pow, hR]
      linear_combination ((M : ℝ) ^ 2 + N) * hquad
    have heq := (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq
    rw [eq_div_iff (by positivity)]
    linarith
theorem notprime4 {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β)
    {a' b' c' : ℕ} (hint : a = a' ∧ b = b' ∧ c = c') (hprim : Nat.gcd (Nat.gcd a' b') c' = 1)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) {m k : ℕ} (hmk : Nat.Coprime m k) (hk : 0 < k) (hratio : a / c = m / k) :
    let M : ℤ := ∑ i, ε i
    ((m : ℤ) + k ∣ M) ∧ ∃ j : ℤ, 0 < j ∧ M = j * (m + k) ∧ (N : ℤ) = j ^ 2 * (3 * k ^ 2 - m ^ 2) ∧
      (N : ℤ) = j ^ 2 * (3 * c' - (a' : ℤ) ^ 2 / c') ∧ (Squarefree N → j = 1) := by
  intro M
  obtain ⟨eM, eN, ht0, ht1, hΛ⟩ := isobeta_core D hrel hT hns hshape hε hi₀ hb
  have te := tilingequation3 D hrel hT hns hshape hint hprim hε hi₀ hb
  dsimp only at te
  obtain ⟨-, -, -, hNM, -⟩ := te
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) < m := by
    have := ht0
    rw [hratio] at this
    exact (div_pos_iff_of_pos_right hkR).mp this
  have hmk' : (m : ℝ) < k := by
    have : (m : ℝ) / k < 1 := by rw [← hratio]; exact ht1
    rwa [div_lt_one hkR] at this
  have hMpos : (0 : ℝ) < M := by
    rw [eM]
    have : 0 < 1 - a / c := by linarith
    positivity
  have heqR : ((N : ℤ) : ℝ) * (((m : ℤ) + k : ℤ) : ℝ) ^ 2 =
      (((M : ℤ) ^ 2 * (3 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2) : ℤ) : ℝ) := by
    push_cast
    rw [hratio] at hNM
    rw [div_eq_div_iff (by positivity) (by positivity)] at hNM
    field_simp at hNM
    linear_combination hNM
  have heqZ : (N : ℤ) * ((m : ℤ) + k) ^ 2 = M ^ 2 * (3 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2) := by
    exact_mod_cast heqR
  have hcop : IsCoprime (m : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.mpr hmk
  have hdvd := notprime4_arith (N := (N : ℤ)) (by exact_mod_cast hm0) (by exact_mod_cast hmk') hcop
    heqZ
  refine ⟨hdvd, ?_⟩
  obtain ⟨j, hj⟩ := hdvd
  have hd0 : (0 : ℤ) < m + k := by
    have : (0 : ℤ) < m := by exact_mod_cast hm0
    omega
  have hj0 : 0 < j := by
    have : (0 : ℤ) < M := by exact_mod_cast hMpos
    rw [hj] at this
    exact pos_of_mul_pos_right this hd0.le
  have hNj : (N : ℤ) = j ^ 2 * (3 * k ^ 2 - m ^ 2) := by
    rw [hj] at heqZ
    have : ((m : ℤ) + k) ^ 2 * N = ((m : ℤ) + k) ^ 2 * (j ^ 2 * (3 * k ^ 2 - m ^ 2)) := by
      linear_combination heqZ
    exact mul_left_cancel₀ (pow_ne_zero 2 hd0.ne') this
  obtain ⟨-, -, -, -, hc, ha, hb', -, -, -, -⟩ := model_facts D hrel hT
  obtain ⟨ea, eb, ec⟩ := hint
  have hc0 : 0 < c' := by
    have : (0 : ℝ) < c' := by rw [← ec]; exact hc
    exact_mod_cast this
  have hb0 : 0 < b' := by
    have : (0 : ℝ) < b' := by
      rw [← eb, hb']
      obtain ⟨-, -, -, -, -, -, -, ht0', ht1', -, -⟩ := model_facts D hrel hT
      have : 0 < 1 - (2 * Real.cos (α + β)) ^ 2 := by nlinarith
      positivity
    exact_mod_cast this
  have hrel' : a' ^ 2 + b' * c' = c' ^ 2 := by
    have : ((a' ^ 2 + b' * c' : ℕ) : ℝ) = ((c' ^ 2 : ℕ) : ℝ) := by
      push_cast; rw [← ea, ← eb, ← ec, ha, hb']; ring
    exact_mod_cast this
  have hratio' : a' * k = m * c' := by
    have : ((a' * k : ℕ) : ℝ) = ((m * c' : ℕ) : ℝ) := by
      push_cast; rw [← ea, ← ec]
      rw [div_eq_div_iff hc.ne' hkR.ne'] at hratio; linarith
    exact_mod_cast this
  obtain ⟨hae, -, hce, -, -, -⟩ := gsquare_arith a' b' c' m k hb0 hc0 hprim hrel' hmk hk hratio'
  refine ⟨j, hj0, by rw [hj]; ring, hNj, ?_, fun hsf => ?_⟩
  · rw [hNj, hae, hce]
    push_cast
    have : ((m : ℤ) * k) ^ 2 / (k : ℤ) ^ 2 = (m : ℤ) ^ 2 := by
      rw [mul_pow, Int.mul_ediv_cancel _ (pow_ne_zero 2 (by exact_mod_cast hk.ne'))]
    rw [this]
  · have hjN : j.natAbs * j.natAbs ∣ N := by
      have : (j.natAbs : ℤ) * j.natAbs ∣ (N : ℤ) := by
        rw [hNj]; exact ⟨3 * k ^ 2 - m ^ 2, by rw [← sq, Int.natAbs_sq]⟩
      exact_mod_cast this
    have := hsf _ hjN
    rw [Nat.isUnit_iff] at this
    omega
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open Erdos634.BeesonColoring
variable {N : ℕ} (D : CongruentDissection N)
theorem isoab_core {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    ((∑ i, ε i : ℤ) : ℝ) = Lam D / (1 + a / c) ∧ (N : ℝ) = Lam D ^ 2 / (1 - (a / c) ^ 2) ∧
      D.target.oppLen 1 = Lam D * c * (a / c) ∧ D.target.oppLen 2 = Lam D * c ∧
      D.target.oppLen 0 = Lam D * c ∧ 0 < a / c ∧ a / c < 1 ∧ 0 < Lam D := by
  have hns := not_similar_of_alpha_beta D hrel hT hshape.1
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hns3 := not_triple3 D hrel hT' hns
  obtain ⟨-, -, t0⟩ := corner_counts D hirr hrel h hns3 0 (p := 1) (q := 1)
    (by rw [hshape.1]; push_cast; ring)
  obtain ⟨-, -, t2⟩ := corner_counts D hirr hrel h hns3 2 (p := 1) (q := 1)
    (by rw [hshape.2.2]; push_cast; ring)
  obtain ⟨hα, hβ, hγ, hS, hc, ha, hb', ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hcol := (coloring D hrel hT hns).2 (by rw [t0, t2]) ε i₀ hε hi₀ hb
  have hnp : ¬ ((D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∨
      (D.target.angleAt 0 = β ∧ D.target.angleAt 2 = β)) := by
    rw [hshape.1]; rintro (⟨e, -⟩ | ⟨e, -⟩) <;> linarith
  have hM := hcol.2 hnp
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨r1, -, -, -, -, -, -, -⟩ := r
  rw [div_eq_iff hS.ne'] at r1
  have s0 := target_side D hrel hT 0
  have s1 := target_side D hrel hT 1
  have s2 := target_side D hrel hT 2
  rw [hshape.1] at s0
  rw [hshape.2.1, r1] at s1
  rw [hshape.2.2] at s2
  set t := 2 * Real.cos (α + β)
  have hst : a / c = t := by rw [ha]; field_simp
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have ar := (shapeareas D hrel hT).2.2.1 hshape
  rw [hst] at ar
  rw [hst]
  have hS' := hS.ne'
  have s0' : D.target.oppLen 0 = Lam D * c := by rw [s0]; field_simp
  have s1' : D.target.oppLen 1 = Lam D * c * t := by rw [s1]; field_simp
  have s2' : D.target.oppLen 2 = Lam D * c := by rw [s2]; field_simp
  have h1t : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  have eN : (N : ℝ) = Lam D ^ 2 / (1 - t ^ 2) := by
    rw [div_eq_iff (by positivity)] at ar
    rw [ar]; field_simp
  refine ⟨?_, eN, s1', s2', s0', ht0, ht1, hΛ⟩
  have key : ((∑ i, ε i : ℤ) : ℝ) * (c * ((2 - t) * (1 + t))) =
      Lam D / (1 + t) * (c * ((2 - t) * (1 + t))) := by
    rw [s0', s1', s2', ha, hb'] at hM
    have h1 : (1 : ℝ) + t ≠ 0 := by positivity
    have : Lam D / (1 + t) * (c * ((2 - t) * (1 + t))) = Lam D * c * (2 - t) := by
      field_simp
    rw [this]
    linear_combination hM
  have h2 : (0 : ℝ) < (2 - t) * (1 + t) := by
    have : 0 < 2 - t := by linarith
    positivity
  exact mul_right_cancel₀ (by positivity) key
theorem isosceles1 {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    let s := a / c
    let M : ℤ := ∑ i, ε i
    (N : ℝ) / (M : ℝ) ^ 2 = (1 + s) / (1 - s) ∧ s = (N - (M : ℝ) ^ 2) / (N + (M : ℝ) ^ 2) ∧
      Lam D = M * (1 + s) := by
  intro s M
  obtain ⟨eM, eN, -, -, -, ht0, ht1, hΛ⟩ := isoab_core D hrel hT hshape hε hi₀ hb
  simp only [s]
  set t := a / c
  have h1p : (0 : ℝ) < 1 + t := by positivity
  have h1m : (0 : ℝ) < 1 - t := by linarith
  rw [show (1 : ℝ) - t ^ 2 = (1 - t) * (1 + t) by ring] at eN
  refine ⟨?_, ?_, ?_⟩
  · rw [eN, eM]; field_simp
  · rw [eN, eM, eq_div_iff (by positivity)]; field_simp; ring
  · rw [eM, div_mul_cancel₀ _ h1p.ne']
theorem notprime3 [Fact OMACut_RT] {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hshape : TgtAngles D (α + β) α (α + β)) : ¬ N.Prime := by
  intro hN
  obtain ⟨σ, h0, h1, h2⟩ := hshape
  set D₁ := relabelTarget D σ
  have hT₁ : TileSides D₁ α β γ a b c := hT
  have e0 : D₁.target.angleAt 0 = α + β := by rw [relabel_angleAt]; exact h0
  have e1 : D₁.target.angleAt 1 = α := by rw [relabel_angleAt]; exact h1
  have e2 : D₁.target.angleAt 2 = α + β := by rw [relabel_angleAt]; exact h2
  have hns₁ := not_similar_of_alpha_beta D₁ hrel hT₁ e0
  have hT' : TileAngles D₁ α β γ := by
    obtain ⟨τ, g0, g1, g2, -⟩ := hT₁
    exact ⟨τ, g0, g1, g2⟩
  have hirr := (angles D₁ hrel hT' hns₁).1
  have h := threeAlphaData_of_sides D₁ hrel hT₁
  have hns3 := not_triple3 D₁ hrel hT' hns₁
  obtain ⟨-, -, t1⟩ := corner_counts D₁ hirr hrel h hns3 1 (p := 1) (q := 0)
    (by rw [e1]; push_cast; ring)
  obtain ⟨i₀, hi₀⟩ : ∃ i, TileAt D₁ 1 i := by
    classical
    have : 0 < ({i | TileAt D₁ 1 i} : Finset (Fin N)).card := by
      have : tilesAt D₁ 1 = 1 := t1
      unfold tilesAt at this; omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp this
    exact ⟨i, by simpa using hi⟩
  obtain ⟨ε, hε, hεi⟩ := signedtiles D₁ hrel hT' hns₁ hi₀
  have hAB := atB_onAB D₁ t1 hi₀
  have te := isosceles1 D₁ hrel hT₁ ⟨e0, e1, e2⟩ hε hAB hεi
  dsimp only at te
  obtain ⟨-, hs, hΛ⟩ := te
  obtain ⟨eM, -, eY, -, -, ht0, ht1, hΛ0⟩ := isoab_core D₁ hrel hT₁ ⟨e0, e1, e2⟩ hε hAB hεi
  set M : ℤ := ∑ i, ε i
  have hMpos : (0 : ℝ) < M := by rw [eM]; positivity
  obtain ⟨⟨q, hq⟩, -, -⟩ := rationaltile D₁ hrel hT₁ hns₁
  have hq0 : 0 < q := by have : (0 : ℝ) < q := by rw [← hq]; exact ht0
                         exact_mod_cast this
  have hq1 : q < 1 := by have : (q : ℝ) < 1 := by rw [← hq]; exact ht1
                         exact_mod_cast this
  set m : ℤ := q.num
  set k : ℤ := (q.den : ℤ)
  have hm : 0 < m := Rat.num_pos.mpr hq0
  have hk : 0 < k := by simp only [k]; exact_mod_cast q.den_pos
  have hmk : m < k := Rat.num_lt_denom_iff.mpr hq1
  have hcop : IsCoprime m k := by rw [Int.isCoprime_iff_gcd_eq_one]; exact q.reduced
  have hqmk : (q : ℝ) = m / k := by rw [Rat.cast_def]; simp [m, k]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (((N : ℤ) + M ^ 2) * m : ℤ) = ((N : ℤ) - M ^ 2) * k := by
    have : ((((N : ℤ) + M ^ 2) * m : ℤ) : ℝ) = ((((N : ℤ) - M ^ 2) * k : ℤ) : ℝ) := by
      push_cast
      rw [hq, hqmk] at hs
      have hd : (N : ℝ) + (M : ℝ) ^ 2 ≠ 0 := by positivity
      rw [eq_div_iff hd, div_mul_eq_mul_div, div_eq_iff hkR.ne'] at hs
      linarith
    exact_mod_cast this
  obtain ⟨p', q', r', hr, hY⟩ := side_decomp D₁ hirr hrel h hns3 2
  have hYo : dist (D₁.target.pts 2) (D₁.target.pts (2 + 1)) = D₁.target.oppLen 1 := rfl
  rw [hYo, eY] at hY
  obtain ⟨-, -, -, -, hc, ha, hb', -, -, -, -⟩ := model_facts D₁ hrel hT₁
  have hst : a / c = 2 * Real.cos (α + β) := by rw [ha]; field_simp
  set t := 2 * Real.cos (α + β)
  have htq : t = m / k := by rw [← hst, hq, hqmk]
  have eA : a = (m / k) * c := by rw [ha, htq]
  have eB : b = (1 - (m / k) ^ 2) * c := by rw [hb', htq]
  have eL : Lam D₁ = M * (1 + m / k) := by rw [hΛ, hst, htq]
  rw [eL, hst, htq, eA, eB] at hY
  have h2 : M * (k + m) * m = (p' : ℤ) * (m * k) + q' * (k ^ 2 - m ^ 2) + r' * k ^ 2 := by
    have : ((M * (k + m) * m : ℤ) : ℝ) =
        (((p' : ℤ) * (m * k) + q' * (k ^ 2 - m ^ 2) + r' * k ^ 2 : ℤ) : ℝ) := by
      push_cast
      have hk0 : (k : ℝ) ≠ 0 := hkR.ne'
      field_simp at hY
      linear_combination hY
    exact_mod_cast this
  exact notprime3_arith hN (by exact_mod_cast hMpos) hm hmk hcop (by positivity) (by positivity)
    (by exact_mod_cast hr) h1 h2
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open Erdos634.BeesonColoring
variable {N : ℕ} (D : CongruentDissection N)
theorem isoalpha_core {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α + 2 * β ∧ D.target.angleAt 2 = α)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    ((∑ i, ε i : ℤ) : ℝ) * (1 + a / c) = Lam D * (a / c) * (2 + a / c) ∧
      (N : ℝ) * (1 - (a / c) ^ 2) = Lam D ^ 2 * (a / c) ^ 2 * (2 - (a / c) ^ 2) ∧
      D.target.oppLen 0 = Lam D * c * (a / c) ∧ 0 < a / c ∧ a / c < 1 ∧ 0 < Lam D := by
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hns3 := not_triple3 D hrel hT' hns
  obtain ⟨-, -, t0⟩ := corner_counts D hirr hrel h hns3 0 (p := 1) (q := 0)
    (by rw [hshape.1]; push_cast; ring)
  obtain ⟨-, -, t2⟩ := corner_counts D hirr hrel h hns3 2 (p := 1) (q := 0)
    (by rw [hshape.2.2]; push_cast; ring)
  obtain ⟨hα, hβ, hγ, hS, hc, ha, hb', ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hcol := (coloring D hrel hT hns).2 (by rw [t0, t2]) ε i₀ hε hi₀ hb
  have hM := hcol.1 (Or.inl ⟨hshape.1, hshape.2.2⟩)
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨r1, -, -, -, -, r6, -, -⟩ := r
  rw [div_eq_iff hS.ne'] at r1 r6
  have s0 := target_side D hrel hT 0
  have s1 := target_side D hrel hT 1
  have s2 := target_side D hrel hT 2
  rw [hshape.1, r1] at s0
  rw [hshape.2.1, r6] at s1
  rw [hshape.2.2, r1] at s2
  set t := 2 * Real.cos (α + β)
  have hst : a / c = t := by rw [ha]; field_simp
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have ar := (shapeareas D hrel hT).2.2.2.1 hshape
  rw [hst] at ar
  rw [hst]
  have hS' := hS.ne'
  have s0' : D.target.oppLen 0 = Lam D * c * t := by rw [s0]; field_simp
  have s1' : D.target.oppLen 1 = Lam D * c * (t * (2 - t ^ 2)) := by rw [s1]; field_simp
  have s2' : D.target.oppLen 2 = Lam D * c * t := by rw [s2]; field_simp
  have h1t : 1 - t ^ 2 ≠ 0 := by nlinarith
  refine ⟨?_, ?_, s0', ht0, ht1, hΛ⟩
  · have key : ((∑ i, ε i : ℤ) : ℝ) * (1 + t) * (c * (2 - t)) =
        Lam D * t * (2 + t) * (c * (2 - t)) := by
      rw [s0', s1', s2', ha, hb'] at hM
      linear_combination hM
    have : (0 : ℝ) < 2 - t := by linarith
    exact mul_right_cancel₀ (by positivity) key
  · rw [div_eq_iff (by positivity)] at ar
    rw [ar]; field_simp
theorem isoalpha_int {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α + 2 * β ∧ D.target.angleAt 2 = α)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) {m k : ℤ} (hk : 0 < k) (hcop : IsCoprime m k) (hratio : a / c = m / k) :
    0 < m ∧ m < k ∧ (2 * k + m ∣ ∑ i, ε i) ∧
      (N : ℤ) * (k - m) * (2 * k + m) ^ 2 = (∑ i, ε i) ^ 2 * (m + k) * (2 * k ^ 2 - m ^ 2) := by
  obtain ⟨eM, eN, eX, ht0, ht1, hΛ⟩ := isoalpha_core D hrel hT hns hshape hε hi₀ hb
  set M : ℤ := ∑ i, ε i
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : 0 < m := by
    have : (0 : ℝ) < m / k := by rw [← hratio]; exact ht0
    exact_mod_cast (div_pos_iff_of_pos_right hkR).mp this
  have hmk : m < k := by
    have : (m : ℝ) / k < 1 := by rw [← hratio]; exact ht1
    rw [div_lt_one hkR] at this
    exact_mod_cast this
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [hratio] at eM eN eX
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hns3 := not_triple3 D hrel hT' hns
  obtain ⟨p', q', r', -, hX⟩ := side_decomp D hirr hrel h hns3 1
  have hXo : dist (D.target.pts 1) (D.target.pts (1 + 1)) = D.target.oppLen 0 := rfl
  rw [hXo, eX] at hX
  obtain ⟨-, -, -, -, hc, ha, hb', -, -, -, -⟩ := model_facts D hrel hT
  have hst : a / c = 2 * Real.cos (α + β) := by rw [ha]; field_simp
  have eA : a = (m / k) * c := by rw [← hratio, div_mul_cancel₀ _ hc.ne']
  have eB : b = (1 - (m / k) ^ 2) * c := by rw [hb', ← hst, hratio]
  rw [eA, eB] at hX
  have hk0 : (k : ℝ) ≠ 0 := hkR.ne'
  have h2 : M * (k + m) * k ^ 2 =
      ((p' : ℤ) * (m * k) + q' * (k ^ 2 - m ^ 2) + r' * k ^ 2) * (2 * k + m) := by
    have : ((M * (k + m) * k ^ 2 : ℤ) : ℝ) =
        ((((p' : ℤ) * (m * k) + q' * (k ^ 2 - m ^ 2) + r' * k ^ 2) * (2 * k + m) : ℤ) : ℝ) := by
      push_cast
      have hL : Lam D * c * (m / k) = c * (p' * (m / k) + q' * (1 - (m / k) ^ 2) + r') := by
        rw [hX]; ring
      have hL' : Lam D * (m / k) = p' * (m / k) + q' * (1 - (m / k) ^ 2) + r' := by
        have := mul_left_cancel₀ hc.ne' (by linear_combination hL :
          c * (Lam D * (m / k)) = c * (p' * (m / k) + q' * (1 - (m / k) ^ 2) + r'))
        exact this
      have e1 : (M : ℝ) * (k + m) = Lam D * (m / k) * (2 * k + m) := by
        field_simp at eM ⊢; linear_combination eM
      rw [hL'] at e1
      field_simp at e1
      linear_combination e1
    exact_mod_cast this
  have hcA : IsCoprime (2 * k + m) (k + m) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨v - u, 2 * u - v, by linear_combination huv⟩
  have hcB : IsCoprime (2 * k + m) k := by
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨u, v - 2 * u, by linear_combination huv⟩
  have hdvd : 2 * k + m ∣ M :=
    (hcA.mul_right (hcB.pow_right (n := 2))).dvd_of_dvd_mul_right
      ⟨(p' : ℤ) * (m * k) + q' * (k ^ 2 - m ^ 2) + r' * k ^ 2, by rw [mul_assoc] at h2; rw [h2]; ring⟩
  refine ⟨hm, hmk, hdvd, ?_⟩
  have : (((N : ℤ) * (k - m) * (2 * k + m) ^ 2 : ℤ) : ℝ) =
      ((M ^ 2 * (m + k) * (2 * k ^ 2 - m ^ 2) : ℤ) : ℝ) := by
    push_cast
    have hmk' : (1 : ℝ) + m / k ≠ 0 := by positivity
    have e3 : (N : ℝ) * (1 - m / k) * (2 + m / k) ^ 2 = (M : ℝ) ^ 2 * (1 + m / k) * (2 - (m / k) ^ 2) := by
      have e4 : (1 + m / k) * ((N : ℝ) * (1 - m / k) * (2 + m / k) ^ 2 -
          (M : ℝ) ^ 2 * (1 + m / k) * (2 - (m / k) ^ 2)) = 0 := by
        linear_combination (2 + m / k) ^ 2 * eN -
          (2 - (m / k) ^ 2) * ((M : ℝ) * (1 + m / k) + Lam D * (m / k) * (2 + m / k)) * eM
      rcases mul_eq_zero.mp e4 with e | e
      · exact absurd e hmk'
      · linarith
    field_simp at e3
    linear_combination e3
  exact_mod_cast this
theorem notprime5 [Fact OMACut_RT] {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)] (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : TgtAngles D α (α + 2 * β) α) : ¬ N.Prime := by
  intro hN
  obtain ⟨σ, h0, h1, h2⟩ := hshape
  set D₁ := relabelTarget D σ
  have hT₁ : TileSides D₁ α β γ a b c := hT
  have e0 : D₁.target.angleAt 0 = α := by rw [relabel_angleAt]; exact h0
  have e1 : D₁.target.angleAt 1 = α + 2 * β := by rw [relabel_angleAt]; exact h1
  have e2 : D₁.target.angleAt 2 = α := by rw [relabel_angleAt]; exact h2
  have hns₁ : ¬ SimilarTM D₁ := fun hs => hns (similar_of_relabel D σ hs)
  have hT' : TileAngles D₁ α β γ := by
    obtain ⟨τ, g0, g1, g2, -⟩ := hT₁
    exact ⟨τ, g0, g1, g2⟩
  obtain ⟨i₀, hAB⟩ := exists_atB_onAB D₁
  have hi₀ : TileAt D₁ 1 i₀ := by
    obtain ⟨l, -, -, hl, -⟩ := hAB
    exact ⟨l, hl⟩
  obtain ⟨ε, hε, hεi⟩ := signedtiles D₁ hrel hT' hns₁ hi₀
  obtain ⟨-, -, -, ht0, ht1, -⟩ := isoalpha_core D₁ hrel hT₁ hns₁ ⟨e0, e1, e2⟩ hε hAB hεi
  obtain ⟨⟨q, hq⟩, -, -⟩ := rationaltile D₁ hrel hT₁ hns₁
  have hq0 : 0 < q := by
    have : (0 : ℝ) < q := by rw [← hq]; exact ht0
    exact_mod_cast this
  set m : ℤ := q.num
  set k : ℤ := (q.den : ℤ)
  have hk : 0 < k := by simp only [k]; exact_mod_cast q.den_pos
  have hcop : IsCoprime m k := by rw [Int.isCoprime_iff_gcd_eq_one]; exact q.reduced
  have hqmk : (q : ℝ) = m / k := by rw [Rat.cast_def]; simp [m, k]
  obtain ⟨hm, hmk, hdvd, heq⟩ :=
    isoalpha_int D₁ hrel hT₁ hns₁ ⟨e0, e1, e2⟩ hε hAB hεi hk hcop (by rw [hq, hqmk])
  set M : ℤ := ∑ i, ε i
  obtain ⟨j, hj⟩ := hdvd
  have hd : (0 : ℤ) < 2 * k + m := by omega
  have hMpos : 0 < M := by
    obtain ⟨eM, -, -, ht0', -, hΛ⟩ := isoalpha_core D₁ hrel hT₁ hns₁ ⟨e0, e1, e2⟩ hε hAB hεi
    have : (0 : ℝ) < M := by
      have h' : (0 : ℝ) < (M : ℝ) * (1 + a / c) := by rw [eM]; positivity
      exact pos_of_mul_pos_left h' (by positivity)
    exact_mod_cast this
  have hj0 : 0 < j := by
    rw [hj] at hMpos
    exact pos_of_mul_pos_right hMpos hd.le
  have hNj : (N : ℤ) * (k - m) = j ^ 2 * (m + k) * (2 * k ^ 2 - m ^ 2) := by
    rw [hj] at heq
    have : (2 * k + m) ^ 2 * ((N : ℤ) * (k - m)) =
        (2 * k + m) ^ 2 * (j ^ 2 * (m + k) * (2 * k ^ 2 - m ^ 2)) := by
      linear_combination heq
    exact mul_left_cancel₀ (pow_ne_zero 2 hd.ne') this
  exact notprime5_arith hN hj0 hm hmk hcop hNj
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.Prime
open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open TriangleTiling.Laczkovich
variable {N : ℕ}
theorem tgt_swap12 {D : CongruentDissection N} {x y z : ℝ} (h : TgtAngles D x y z) :
    TgtAngles D x z y := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  refine ⟨(Equiv.swap (1 : Fin 3) 2).trans σ, ?_, ?_, ?_⟩
  · simp only [Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; exact h0
  · simpa using h2
  · simpa using h1
end TriangleTiling.Prime
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry EuclideanGeometry Set
open scoped Pointwise
noncomputable def scaleTri (T : Tri) (κ : ℝ) (hκ : κ ≠ 0) : Tri where
  pts := fun k => κ • T.pts k
  indep := by
    have := T.indep.map' (LinearEquiv.smulOfNeZero ℝ Plane κ hκ).toLinearMap.toAffineMap
      (LinearEquiv.smulOfNeZero ℝ Plane κ hκ).injective
    convert this using 1 <;> first | rfl | (funext k; rfl)
theorem scale_carrier (T : Tri) {κ : ℝ} (hκ : κ ≠ 0) :
    (scaleTri T κ hκ).carrier = κ • T.carrier := by
  unfold Tri.carrier scaleTri
  rw [← convexHull_smul, Set.smul_set_range]
theorem scale_congruent {T U : Tri} (h : T.Congruent U) {κ : ℝ} (hκ : 0 < κ) :
    (scaleTri T κ hκ.ne').Congruent (scaleTri U κ hκ.ne') := by
  obtain ⟨f, σ, hf⟩ := h
  have h0 := hκ.ne'
  let e : Plane ≃ Plane :=
    { toFun := fun x => κ • f (κ⁻¹ • x)
      invFun := fun x => κ • f.symm (κ⁻¹ • x)
      left_inv := fun x => by simp [h0]
      right_inv := fun x => by simp [h0] }
  have hiso : Isometry e := Isometry.of_dist_eq fun x y => by
    show dist (κ • f (κ⁻¹ • x)) (κ • f (κ⁻¹ • y)) = dist x y
    rw [dist_smul₀, f.dist_eq, dist_smul₀, ← mul_assoc, norm_inv, mul_inv_cancel₀ (by simpa using h0),
      one_mul]
  refine ⟨⟨e, hiso⟩, σ, fun k => ?_⟩
  show κ • f (κ⁻¹ • (κ • T.pts k)) = κ • U.pts (σ k)
  rw [inv_smul_smul₀ h0, hf]
theorem scale_angleAt (T : Tri) {κ : ℝ} (hκ : κ ≠ 0) (k : Fin 3) :
    (scaleTri T κ hκ).angleAt k = T.angleAt k := by
  unfold Tri.angleAt cornerAngle scaleTri EuclideanGeometry.angle
  simp only [vsub_eq_sub, ← smul_sub]
  exact InnerProductGeometry.angle_smul_smul hκ _ _
theorem scale_oppLen (T : Tri) {κ : ℝ} (hκ : 0 < κ) (k : Fin 3) :
    (scaleTri T κ hκ.ne').oppLen k = κ * T.oppLen k := by
  unfold Tri.oppLen scaleTri
  simp only
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hκ]
variable {N : ℕ}
noncomputable def scaleDissection (D : CongruentDissection N) {κ : ℝ} (hκ : 0 < κ) :
    CongruentDissection N where
  target := scaleTri D.target κ hκ.ne'
  tile i := scaleTri (D.tile i) κ hκ.ne'
  covers := by
    simp only [scale_carrier]
    rw [← Set.smul_set_iUnion, D.covers]
  interiors_disjoint := by
    intro i j hij
    simp only [scale_carrier, interior_smul₀ hκ.ne']
    rw [← Set.image_smul, ← Set.image_smul]
    exact (Set.disjoint_image_iff (smul_right_injective Plane hκ.ne')).mpr (D.interiors_disjoint hij)
  model := scaleTri D.model κ hκ.ne'
  tiles_congruent i := scale_congruent (D.tiles_congruent i) hκ
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry EuclideanGeometry Set
variable {N : ℕ} (D : CongruentDissection N)
theorem tileSides_angles {α β γ a b c : ℝ} (hT : TileSides D α β γ a b c) :
    0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = Real.pi := by
  obtain ⟨σ, h0, h1, h2, -, -, -⟩ := hT
  have hsum : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2) = Real.pi := by
    have e := Equiv.sum_comp σ (fun k => D.model.angleAt k)
    simp only [Fin.sum_univ_three] at e
    rw [e, D.model.angleAt_sum]
  exact ⟨h0 ▸ D.model.angleAt_pos' _, h1 ▸ D.model.angleAt_pos' _, h2 ▸ D.model.angleAt_pos' _,
    by rw [← h0, ← h1, ← h2]; exact hsum⟩
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.Prime
open Erdos634.Geometry EuclideanGeometry Real Set Metric
variable {N : ℕ}
namespace RunSetting
end RunSetting
def _root_.OMACut_ISO1 : Prop := ∀ {N : ℕ} {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ},
    ThreeAlpha.TileSides D α β γ a b c → 3 * α + 2 * β = π → (¬ ∃ r : ℚ, α = r * π) → 0 < m → m < k →
      IsCoprime m k → a = m * k → b = k ^ 2 - m ^ 2 → c = k ^ 2 →
        (D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β) →
          (N : ℝ) ≠ 3 * k ^ 2 - m ^ 2
theorem isobetaone [hcut : Fact OMACut_ISO1] {D : CongruentDissection N} {α β γ a b c : ℝ} {m k : ℤ}
    (hT : ThreeAlpha.TileSides D α β γ a b c) (hrel : 3 * α + 2 * β = π)
    (hirr : ¬ ∃ r : ℚ, α = r * π) (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k)
    (ha : a = m * k) (hb : b = k ^ 2 - m ^ 2) (hc : c = k ^ 2)
    (hshape : D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β) :
    (N : ℝ) ≠ 3 * k ^ 2 - m ^ 2 := hcut.out hT hrel hirr hm hmk hcop ha hb hc hshape
end TriangleTiling.Prime
end

section
namespace TriangleTiling.Prime
open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open TriangleTiling.ThreeAlpha
variable {N : ℕ}
theorem tile_params [Fact OMACut_RT] (D : CongruentDissection N) {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)]
    (hrel : 3 * α + 2 * β = Real.pi) (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ m k : ℕ, Nat.Coprime m k ∧ 0 < m ∧ m < k ∧
      a = τ * (m * k) ∧ b = τ * (k ^ 2 - m ^ 2) ∧ c = τ * k ^ 2 := by
  obtain ⟨⟨q, hq⟩, -, -⟩ := TriangleTiling.ThreeAlpha.rationaltile D hrel hT hns
  obtain ⟨-, -, -, -, hc, ha, hb, ht0, ht1, -, -⟩ := model_facts D hrel hT
  set t := 2 * Real.cos (α + β)
  have hqt : (q : ℝ) = t := by rw [← hq, ha]; field_simp
  have hq0 : (0 : ℚ) < q := by exact_mod_cast (hqt ▸ ht0)
  have hn0 : 0 < q.num := Rat.num_pos.mpr hq0
  set m := q.num.toNat
  set k := q.den
  have hmn : (m : ℤ) = q.num := Int.toNat_of_nonneg hn0.le
  have hk0 : (0 : ℝ) < k := by exact_mod_cast q.den_pos
  have htmk : t = m / k := by
    rw [← hqt, Rat.cast_def]
    congr 1
    rw [← hmn]; push_cast; rfl
  have hm0 : 0 < m := by omega
  have hmk : m < k := by
    have : (m : ℝ) / k < 1 := htmk ▸ ht1
    rw [div_lt_one hk0] at this
    exact_mod_cast this
  have hcop : Nat.Coprime m k := by
    have h := q.reduced
    have : q.num.natAbs = m := by omega
    rwa [this] at h
  refine ⟨c / k ^ 2, by positivity, m, k, hcop, hm0, hmk, ?_, ?_, ?_⟩
  · rw [ha, htmk]; field_simp
  · rw [hb, htmk]; field_simp
  · field_simp
theorem tileSides_scale (D : CongruentDissection N) {κ : ℝ} (hκ : 0 < κ) {α β γ a b c : ℝ}
    (hT : TileSides D α β γ a b c) :
    TileSides (scaleDissection D hκ) α β γ (κ * a) (κ * b) (κ * c) := by
  obtain ⟨σ, h0, h1, h2, l0, l1, l2⟩ := hT
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [scaleDissection, scale_angleAt, scale_oppLen _ hκ, *]
theorem scale_target_angleAt (D : CongruentDissection N) {κ : ℝ} (hκ : 0 < κ) (j : Fin 3) :
    (scaleDissection D hκ).target.angleAt j = D.target.angleAt j :=
  scale_angleAt D.target hκ.ne' j
theorem similar_of_scale (D : CongruentDissection N) {κ : ℝ} (hκ : 0 < κ)
    (h : SimilarTM (scaleDissection D hκ)) : SimilarTM D := by
  obtain ⟨μ, τ, hτ⟩ := h
  refine ⟨μ, τ, fun j => ?_⟩
  obtain ⟨e1, e2⟩ := hτ j
  change (scaleTri D.target κ hκ.ne').angleAt j = (scaleTri D.model κ hκ.ne').angleAt (τ j) at e1
  change (scaleTri D.target κ hκ.ne').oppLen j = μ * (scaleTri D.model κ hκ.ne').oppLen (τ j) at e2
  rw [scale_angleAt, scale_angleAt] at e1
  rw [scale_oppLen _ hκ, scale_oppLen _ hκ] at e2
  refine ⟨e1, ?_⟩
  have : κ * (D.target.oppLen j - μ * D.model.oppLen (τ j)) = 0 := by linear_combination e2
  linarith [(mul_eq_zero.mp this).resolve_left hκ.ne']
theorem tileSides_unscale (D : CongruentDissection N) {τ : ℝ} (hτ : 0 < τ) {α β γ a b c : ℝ}
    {m k : ℕ} (hT : TileSides D α β γ a b c) (ha : a = τ * (m * k))
    (hb : b = τ * (k ^ 2 - m ^ 2)) (hc : c = τ * k ^ 2) :
    TileSides (scaleDissection D (inv_pos.mpr hτ)) α β γ (m * k) (k ^ 2 - m ^ 2) (k ^ 2) := by
  have h := tileSides_scale D (inv_pos.mpr hτ) hT
  rw [ha, hb, hc, inv_mul_cancel_left₀ hτ.ne', inv_mul_cancel_left₀ hτ.ne',
    inv_mul_cancel_left₀ hτ.ne'] at h
  exact h
theorem gcd_params {m k : ℕ} (hmk : Nat.Coprime m k) (hlt : m < k) :
    Nat.gcd (Nat.gcd (m * k) (k ^ 2 - m ^ 2)) (k ^ 2) = 1 := by
  have hle : m ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hlt.le 2
  show Nat.Coprime _ _
  apply Nat.Coprime.pow_right
  apply Nat.coprime_of_dvd
  intro p hp hpd hpk
  have h2 : p ∣ k ^ 2 - m ^ 2 := hpd.trans (Nat.gcd_dvd_right _ _)
  have h3 : p ∣ k ^ 2 := dvd_pow hpk two_ne_zero
  have h4 : p ∣ m ^ 2 := by
    have := Nat.dvd_sub h3 h2
    rwa [Nat.sub_sub_self hle] at this
  have h5 := Nat.dvd_gcd (hp.dvd_of_dvd_pow h4) hpk
  rw [Nat.Coprime.gcd_eq_one hmk] at h5
  exact hp.not_dvd_one h5
theorem isoscelesbeta [Fact OMACut_ISO1] [Fact OMACut_RT] (D : CongruentDissection N) {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)]
    (hT : TileSides D α β γ a b c) (hrel : 3 * α + 2 * β = Real.pi) (hirr : IrrPi α)
    (hshape : TgtAngles D β (3 * α) β) :
    ¬ N.Prime ∧ ¬ Squarefree N ∧ ∃ j m k : ℕ, 1 < j ∧ Nat.Coprime m k ∧ 0 < m ∧ m < k ∧
      (N : ℤ) = j ^ 2 * (3 * k ^ 2 - m ^ 2) ∧
      ∃ τ : ℝ, 0 < τ ∧ a = τ * (m * k) ∧ b = τ * (k ^ 2 - m ^ 2) ∧ c = τ * k ^ 2 := by
  have hns : ¬ SimilarTM D := by
    intro hs
    obtain ⟨hα, -, -, hsum⟩ := TriangleTiling.ThreeAlpha.tileSides_angles D hT
    obtain ⟨σ, -, h1, -⟩ := hshape
    rcases angles_of_similar D hT hs (σ 1) with e | e | e <;> rw [h1] at e
    · linarith
    · exact hirr ⟨1 / 9, by push_cast; linarith⟩
    · exact hirr ⟨1 / 5, by push_cast; linarith⟩
  obtain ⟨D', hm, hns', -, e0, e1, e2⟩ := normalize D hshape hns
  have hT' := tileSides_of_model D hm hT
  obtain ⟨τ, hτ, m, k, hmk, hm0, hlt, ha, hb, hc⟩ := tile_params D' hrel hT' hns'
  set D'' := scaleDissection D' (inv_pos.mpr hτ)
  have hT'' : TileSides D'' α β γ (m * k) (k ^ 2 - m ^ 2) (k ^ 2) :=
    tileSides_unscale D' hτ hT' ha hb hc
  have hns'' : ¬ SimilarTM D'' := fun h => hns' (similar_of_scale D' _ h)
  have hs := scale_target_angleAt D' (inv_pos.mpr hτ)
  have hshape'' : D''.target.angleAt 0 = β ∧ D''.target.angleAt 1 = 3 * α ∧
      D''.target.angleAt 2 = β := ⟨by rw [hs]; exact e0, by rw [hs]; exact e1, by rw [hs]; exact e2⟩
  have hTA : TileAngles D'' α β γ := by
    obtain ⟨σ, g0, g1, g2, -⟩ := hT''; exact ⟨σ, g0, g1, g2⟩
  have hle : m ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left hlt.le 2
  have hbN : ((k ^ 2 - m ^ 2 : ℕ) : ℝ) = (k : ℝ) ^ 2 - (m : ℝ) ^ 2 := by
    rw [Nat.cast_sub hle]; push_cast; ring
  have hTn : TileSides D'' α β γ ((m * k : ℕ) : ℝ) ((k ^ 2 - m ^ 2 : ℕ) : ℝ) ((k ^ 2 : ℕ) : ℝ) := by
    rw [hbN]; push_cast; exact hT''
  obtain ⟨i₀, hAB⟩ := exists_atB_onAB D''
  have hi₀ : TileAt D'' 1 i₀ := by
    obtain ⟨l, -, -, hl, -⟩ := hAB
    exact ⟨l, hl⟩
  obtain ⟨ε, hε, hεi⟩ := signedtiles D'' hrel hTA hns'' hi₀
  have hk0 : 0 < k := by omega
  have te := notprime4 D'' hrel hTn hns'' hshape'' ⟨rfl, rfl, rfl⟩ (gcd_params hmk hlt) hε hAB
    hεi hmk hk0 (by push_cast; field_simp)
  dsimp only at te
  obtain ⟨-, j, hj0, -, hNj, -, hsq⟩ := te
  have hj1 : j ≠ 1 := by
    rintro rfl
    rw [one_pow, one_mul] at hNj
    refine isobetaone hT'' hrel hirr (m := m) (k := k) (by exact_mod_cast hm0)
      (by exact_mod_cast hlt) (Nat.isCoprime_iff_coprime.mpr hmk) (by push_cast; ring)
      (by push_cast; ring) (by push_cast; ring) hshape'' ?_
    have : ((N : ℤ) : ℝ) = ((3 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2 : ℤ) : ℝ) := by rw [hNj]
    push_cast at this ⊢
    exact this
  have hsq' : ¬ Squarefree N := fun h => hj1 (hsq h)
  have hjn : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0.le
  refine ⟨fun hp => hsq' (Irreducible.squarefree hp), hsq', j.toNat, m, k, by omega, hmk, hm0,
    hlt, by rw [hjn]; exact hNj, τ, hτ, ha, hb, hc⟩
theorem isobetaprime [Fact OMACut_ISO1] [Fact OMACut_RT] (D : CongruentDissection N) {α β γ a b c : ℝ} [Fact (Erdos634.Draft.TheoremPConditional.IrrPi α)]
    (hrel : 3 * α + 2 * β = Real.pi) (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : TgtAngles D β (3 * α) β) : ¬ N.Prime := by
  have hTA : TileAngles D α β γ := by obtain ⟨σ, g0, g1, g2, -⟩ := hT; exact ⟨σ, g0, g1, g2⟩
  exact (isoscelesbeta D hT hrel (TriangleTiling.ThreeAlpha.angles D hrel hTA hns).1 hshape).1
end TriangleTiling.Prime
end

section
namespace TriangleTiling.Prime
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Real
open Erdos634.Draft.LaczFormal (TileAngles)
theorem similar_of_angles {N : ℕ} (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3))
    (h : ∀ k, D.model.angleAt (σ k) = D.target.angleAt k) : SimilarTM D := by
  have hdm := ThreeAlpha.circumdiam_pos D.model
  refine ⟨ThreeAlpha.circumdiam D.target / ThreeAlpha.circumdiam D.model, σ, fun k => ⟨(h k).symm, ?_⟩⟩
  rw [ThreeAlpha.lawsin D.target k, ThreeAlpha.lawsin D.model (σ k), h k]
  field_simp
end TriangleTiling.Prime
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

theorem OMA.E634S.cutRT_ofF (h : ∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α β γ a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 2 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, γ] ∧ L ∘ σ = ![a, b, c]) → (¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ q : ℚ, a / c = q) ∧ (∃ q : ℚ, b / c = q) ∧ (∃ q : ℚ, a / b = q)) ∧ ∀ m k : ℤ, 0 < m → m < k → IsCoprime m k → a = m * k → b = k ^ 2 - m ^ 2 → c = k ^ 2 → A = ![β, 3 * α, β] → (p : ℝ) ≠ 3 * k ^ 2 - m ^ 2) : OMACut_RT := by
  intro N D α β γ a b c hα hrel hT hns
  obtain ⟨σ, h0, h1, h2, o0, o1, o2⟩ := hT
  exact (h N (OMA.E634S.toS D.target) (OMA.E634S.toS D.model) (fun i => OMA.E634S.toS (D.tile i))
    (OMA.E634S.toS_hc D) (OMA.E634S.toS_hd D) (OMA.E634S.toS_hu D) _ _ _ (fun k => rfl) (fun k => rfl)
    (fun k => rfl) α β γ a b c hα hrel
    ⟨σ, OMA.E634H.comp_vec h0 h1 h2, OMA.E634H.comp_vec o0 o1 o2⟩).1
    (fun ⟨ρ, hρ⟩ => hns (TriangleTiling.Prime.similar_of_angles D ρ (fun k => (congrFun hρ k).symm)))

theorem OMA.E634S.cutISO1_ofF (h : ∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α β γ a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 2 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, γ] ∧ L ∘ σ = ![a, b, c]) → (¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ q : ℚ, a / c = q) ∧ (∃ q : ℚ, b / c = q) ∧ (∃ q : ℚ, a / b = q)) ∧ ∀ m k : ℤ, 0 < m → m < k → IsCoprime m k → a = m * k → b = k ^ 2 - m ^ 2 → c = k ^ 2 → A = ![β, 3 * α, β] → (p : ℝ) ≠ 3 * k ^ 2 - m ^ 2) : OMACut_ISO1 := by
  intro N D α β γ a b c m k hT hrel hirr hm hmk hcop ha hb hc hshape
  obtain ⟨σ, h0, h1, h2, o0, o1, o2⟩ := hT
  exact (h N (OMA.E634S.toS D.target) (OMA.E634S.toS D.model) (fun i => OMA.E634S.toS (D.tile i))
    (OMA.E634S.toS_hc D) (OMA.E634S.toS_hd D) (OMA.E634S.toS_hu D) _ _ _ (fun k => rfl) (fun k => rfl)
    (fun k => rfl) α β γ a b c hirr hrel ⟨σ, OMA.E634H.comp_vec h0 h1 h2, OMA.E634H.comp_vec o0 o1 o2⟩).2
    m k hm hmk hcop ha hb hc (OMA.E634H.eq_vec hshape.1 hshape.2.1 hshape.2.2)

open EuclideanGeometry in
/-- The tile (α, β, 2α + β) on an isosceles T with repeated angle α, β or α + β
(theorem:notprime5, notprime3, isoscelesbeta via isobetaprime), given theorem:rationaltile and the
j = 1 case of theorem:isoscelesbeta (H1 of the reduction). -/
theorem OMA.solution : OMA.R_erdos_634_R1_H2_R1_H4_R1_H4_R1.H2 := by
  intro hF p hp hp3 T Ts hc hd hu t A B hA hB hs α β hα hrel hσB i j hij he hθ
  haveI : Fact (Erdos634.Draft.TheoremPConditional.IrrPi α) := ⟨hα⟩
  haveI : Fact OMACut_RT := ⟨OMA.E634S.cutRT_ofF hF⟩
  haveI : Fact OMACut_ISO1 := ⟨OMA.E634S.cutISO1_ofF hF⟩
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
  have hns₁ : ¬ Erdos634.Draft.TheoremPConditional.SimilarTM D₁ := by
    rintro ⟨μ, τ, h⟩
    apply hs
    refine ⟨σ.symm.trans τ, funext fun k => ?_⟩
    have e := (h (σ.symm k)).1
    rw [ht, hm, Equiv.apply_symm_apply] at e
    show A k = B ((σ.symm.trans τ) k)
    rw [Equiv.trans_apply]
    exact e
  obtain ⟨ρ, hρ⟩ := hσB
  obtain ⟨g0, g1, g2⟩ := OMA.E634H.vec_comp hρ
  have hT' : TriangleTiling.ThreeAlpha.TileSides D₁ α β (2 * α + β) (D₁.model.oppLen (ρ 0))
      (D₁.model.oppLen (ρ 1)) (D₁.model.oppLen (ρ 2)) :=
    ⟨ρ, (hm _).trans g0, (hm _).trans g1, (hm _).trans g2, rfl, rfl, rfl⟩
  have htgt := TriangleTiling.tgt_iso D₁ hA1 hC1
  rcases hθ with hθ | hθ | hθ
  · exact TriangleTiling.ThreeAlpha.notprime5 D₁ hrel hT' hns₁
      (TriangleTiling.Laczkovich.tgtAngles_of_eq D₁ (TriangleTiling.Prime.tgt_swap12 htgt) hθ
        (by linarith) hθ) hp
  · exact TriangleTiling.Prime.isobetaprime D₁ hrel hT' hns₁
      (TriangleTiling.Prime.tgt_swap12
        (TriangleTiling.Laczkovich.tgtAngles_of_eq D₁ htgt hθ hθ (by linarith))) hp
  · exact TriangleTiling.ThreeAlpha.notprime3 D₁ hrel hT'
      (TriangleTiling.Laczkovich.tgtAngles_of_eq D₁ (TriangleTiling.Prime.tgt_swap12 htgt) hθ
        (by linarith) hθ) hp

