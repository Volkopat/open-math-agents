/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1

-- Step PoincareConjecture.poincare_conjecture.R1.H3.R1.H2.R1.H2.R1.H2

/-!
# Local charts from smooth projection fields

Paired triangular facets give interior to the frozen projected star. The quantitative inverse
theorem then gives a chart for the varying projection in the prescribed neighborhood.
-/

open Set Filter Geometry
open scoped Topology

namespace FleetCharts

/-- A face containing a point in the intrinsic interior of another face contains all its
vertices. -/
theorem face_subset_of_intrinsicInterior_mem_convexHull {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : SimplicialComplex ℝ E}
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) {a : E}
    (ha : a ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hat : a ∈ convexHull ℝ (t : Set E)) : s ⊆ t := by
  classical
  intro v hvs
  by_contra hvt
  obtain ⟨u, hsu, hi, hu⟩ :=
    exists_subset_affineIndependent_affineSpan_eq_top
      (s := (s : Set E)) (K.indep hs)
  let b : AffineBasis u ℝ E :=
    ⟨Subtype.val, hi, by simpa only [Subtype.range_coe] using hu⟩
  let i : u := ⟨v, hsu hvs⟩
  let f := b.coord i
  have hfv : f v = 1 := b.coord_apply_eq i
  have hf_zero {w : E} (hws : w ∈ s) (hwv : w ≠ v) : f w = 0 :=
    b.coord_apply_ne (i := i) (j := ⟨w, hsu hws⟩) (fun h => hwv (congrArg Subtype.val h).symm)
  have hf_nonneg : convexHull ℝ (s : Set E) ⊆ f ⁻¹' Ici 0 := by
    refine convexHull_min (fun w hw => ?_) ((convex_Ici (0 : ℝ)).affine_preimage f)
    change 0 ≤ f w
    by_cases hwv : w = v
    · rw [hwv, hfv]
      exact zero_le_one
    · exact (hf_zero hw hwv).ge
  have hf_face : convexHull ℝ ((s : Set E) ∩ t) ⊆ f ⁻¹' {0} := by
    refine convexHull_min (fun w hw => ?_) ((convex_singleton (0 : ℝ)).affine_preimage f)
    exact hf_zero hw.1 (fun h => hvt (h ▸ hw.2))
  have hfa : f (a : E) = 0 := hf_face (K.inter_subset_convexHull hs ht
    ⟨intrinsicInterior_subset ha, hat⟩)
  obtain ⟨a', ha', hcoe⟩ := mem_intrinsicInterior.mp ha
  let A := affineSpan ℝ (convexHull ℝ (s : Set E))
  have : Nonempty A := ⟨a'⟩
  let v' : A := ⟨v, subset_affineSpan _ _ (subset_convexHull ℝ (s : Set E) hvs)⟩
  let q : ℝ → A := AffineMap.lineMap a' v'
  have hq : Continuous q := AffineMap.lineMap_continuous
  have hnear : ∀ᶠ r : ℝ in 𝓝[<] (0 : ℝ), (q r : E) ∈ convexHull ℝ (s : Set E) := by
    have htop : (Subtype.val ⁻¹' convexHull ℝ (s : Set E) : Set A) ∈ 𝓝 (q 0) := by
      simpa only [q, AffineMap.lineMap_apply_zero] using mem_interior_iff_mem_nhds.mp ha'
    exact hq.continuousWithinAt.eventually_mem htop
  have hneg : ∀ᶠ r : ℝ in 𝓝[<] (0 : ℝ), r < 0 := self_mem_nhdsWithin
  obtain ⟨r, hr, hrneg⟩ := (hnear.and hneg).exists
  have hnonneg : 0 ≤ f (q r : E) := hf_nonneg hr
  have hline : (q r : E) = AffineMap.lineMap (a : E) v r := by
    change A.subtype (AffineMap.lineMap a' v' r) = _
    rw [AffineMap.apply_lineMap]
    change AffineMap.lineMap (a' : E) v r = _
    rw [hcoe]
  rw [hline, AffineMap.apply_lineMap, hfa, hfv] at hnonneg
  exact hrneg.not_ge (by simpa [AffineMap.lineMap_apply_ring] using hnonneg)

/-- The closed star of a face is a neighborhood in the carrier at each point of the
intrinsic interior of the face. -/
theorem closedStar_mem_nhds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] (K : SimplicialComplex ℝ E) (hfinite : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces) {a : K.space}
    (ha : (a : E) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    {y : K.space | (y : E) ∈ ⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E)} ∈ 𝓝 a := by
  let F := {t : Finset E | t ∈ K.faces ∧ ¬ s ⊆ t}
  let B := ⋃ t ∈ F, convexHull ℝ (t : Set E)
  have hF : F.Finite := hfinite.subset fun _ ht => ht.1
  have hB : IsClosed B := hF.isClosed_biUnion fun t _ => t.finite_toSet.isClosed_convexHull ℝ
  have haB : (a : E) ∉ B := by
    intro haB
    obtain ⟨t, ht, hat⟩ := mem_iUnion₂.mp haB
    exact ht.2 (face_subset_of_intrinsicInterior_mem_convexHull hs ht.1 ha hat)
  have hn : (Subtype.val ⁻¹' Bᶜ : Set K.space) ∈ 𝓝 a :=
    (hB.isOpen_compl.preimage continuous_subtype_val).mem_nhds haB
  refine mem_of_superset hn fun y hy => ?_
  change (y : E) ∉ B at hy
  obtain ⟨t, ht, hyt⟩ := SimplicialComplex.mem_space_iff.mp y.property
  have hst : s ⊆ t := by
    by_contra hst
    exact hy (mem_iUnion₂.mpr ⟨t, ⟨ht, hst⟩, hyt⟩)
  exact mem_iUnion₂.mpr ⟨t, ⟨ht, by rwa [Finset.union_eq_right.mpr hst]⟩, hyt⟩

end FleetCharts

open Set Filter Geometry Metric
open scoped NNReal Topology

namespace Fleet.ChartImage

abbrev Target := EuclideanSpace ℝ (Fin 3)

/-- A closed set fills an open convex region if its boundary there lies on finitely many
lines and the region meets its interior. The lines need not be disjoint. -/
theorem subset_of_frontier_covered_by_lines {D U : Set Target} (hD : IsClosed D)
    (hU : IsOpen U) (hcU : Convex ℝ U) (hinside : (U ∩ interior D).Nonempty)
    {B : Set (Set Target)} (hf : B.Finite)
    (hdim : ∀ b ∈ B, Module.finrank ℝ (vectorSpan ℝ b) ≤ 1)
    (hfrontier : ∀ z ∈ U ∩ frontier D, ∃ b ∈ B, z ∈ affineSpan ℝ b) : U ⊆ D := by
  intro x hx
  by_contra hxD
  let A (b : Set Target) : AffineSubspace ℝ Target := affineSpan ℝ (insert x b)
  have hAproper (b : Set Target) (hb : b ∈ B) : A b ≠ ⊤ := by
    have hle := (finrank_vectorSpan_insert_le_set ℝ b x).trans
      (Nat.add_le_add_right (hdim b hb) 1)
    intro ht
    rw [← direction_affineSpan, show affineSpan ℝ (insert x b) = ⊤ from ht,
      AffineSubspace.direction_top, finrank_top, finrank_euclideanSpace_fin] at hle
    omega
  have hAclosed (b : Set Target) : IsClosed (A b : Set Target) :=
    (A b).closed_of_finiteDimensional
  have hAdense (b : Set Target) (hb : b ∈ B) : Dense (A b : Set Target)ᶜ := by
    rw [← interior_eq_empty_iff_dense_compl, ← Set.not_nonempty_iff_eq_empty]
    intro hn
    apply hAproper b hb
    apply top_unique
    rw [← isOpen_interior.affineSpan_eq_top hn, affineSpan_le]
    exact interior_subset
  let O := (fun b : Set Target => (A b : Set Target)ᶜ) '' B
  have hdense : Dense (⋂₀ O) := (hf.image _).dense_sInter
    (by rintro _ ⟨b, hb, rfl⟩; exact (hAclosed b).isOpen_compl)
    (by rintro _ ⟨b, hb, rfl⟩; exact hAdense b hb)
  obtain ⟨y, ⟨hyU, hyD⟩, hyO⟩ := hdense.inter_open_nonempty _ (hU.inter isOpen_interior) hinside
  obtain ⟨z, hzD, hxyz, hv⟩ := hD.exists_wbtw_isVisible (interior_subset hyD) x
  have hxz : x ≠ z := ne_of_mem_of_not_mem hzD hxD |>.symm
  have hzfront : z ∈ frontier D := ⟨subset_closure hzD, fun h => hxz (hv.eq_of_mem_interior h)⟩
  obtain ⟨b, hb, hz⟩ := hfrontier z ⟨hcU.mem_of_wbtw hxyz hx hyU, hzfront⟩
  have hy : y ∈ A b := AffineSubspace.right_mem_of_wbtw hxyz
    (subset_affineSpan ℝ _ (mem_insert x b))
    (affineSpan_mono ℝ (subset_insert x b) hz) hxz
  exact (mem_sInter.mp hyO _ (mem_image_of_mem _ hb)) hy

/-- An affine map injective on the convex hull preserves affine independence there. -/
theorem affineIndependent_comp_of_injOn_convexHull {E V ι : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]
    {p : ι → E} (hp : AffineIndependent ℝ p) (f : E →ᵃ[ℝ] V)
    (hf : InjOn f (convexHull ℝ (range p))) : AffineIndependent ℝ (f ∘ p) := by
  by_contra h
  obtain ⟨I, z, hz, hz'⟩ := Convex.radon_partition h
  change z ∈ convexHull ℝ ((fun i => f (p i)) '' I) at hz
  change z ∈ convexHull ℝ ((fun i => f (p i)) '' Iᶜ) at hz'
  rw [← Set.image_image f p I, ← f.image_convexHull] at hz
  rw [← Set.image_image f p Iᶜ, ← f.image_convexHull] at hz'
  obtain ⟨x, hx, hxz⟩ := hz
  obtain ⟨y, hy, hyz⟩ := hz'
  have hxy := hf (convexHull_mono (image_subset_range p I) hx)
    (convexHull_mono (image_subset_range p Iᶜ) hy) (hxz.trans hyz.symm)
  subst y
  exact (Set.disjoint_left.mp (hp.affineSpan_disjoint_of_disjoint disjoint_compl_right))
    (convexHull_subset_affineSpan _ hx) (convexHull_subset_affineSpan _ hy)

section Facet

variable {V ι κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private theorem isOpen_positive_coords [Finite ι] (b : AffineBasis ι ℝ V) (i : ι) :
    IsOpen {x : V | ∀ j : {j : ι // j ≠ i}, 0 < b.coord j x} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (continuous_barycentric_coord b j)

omit [FiniteDimensional ℝ V] in
/-- Barycentric coordinate zero is equivalent to membership in the opposite facet, within
the closed simplex. -/
theorem mem_convexHull_opposite_iff [Fintype ι] (b : AffineBasis ι ℝ V) {x : V}
    (hx : x ∈ convexHull ℝ (range b)) (i : ι) :
    x ∈ convexHull ℝ (b '' ({i}ᶜ : Set ι)) ↔ b.coord i x = 0 := by
  classical
  constructor
  · intro h
    have h' := mem_image_of_mem (b.coord i) h
    rw [(b.coord i).image_convexHull] at h'
    have hnull : (b.coord i) '' (b '' ({i}ᶜ : Set ι)) ⊆ ({0} : Set ℝ) := by
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact b.coord_apply_ne (fun h => hj (Set.mem_singleton_iff.mpr h.symm))
    simpa using convexHull_mono hnull h'
  · intro hz
    rw [b.convexHull_eq_nonneg_coord] at hx
    let p := Finset.univ.erase i
    have hsum : ∑ j ∈ p, b.coord j x = 1 := by
      simp only [p, Finset.sum_erase_eq_sub (Finset.mem_univ i), b.sum_coord_apply_eq_one, hz,
        sub_zero]
    have hvec : ∑ j ∈ p, b.coord j x • b j = x := by
      simp only [p, Finset.sum_erase_eq_sub (Finset.mem_univ i),
        b.linear_combination_coord_eq_self, hz, zero_smul, sub_zero]
    rw [← hvec]
    exact (convex_convexHull ℝ _).sum_mem (fun j _ => hx j) hsum fun j hj =>
      subset_convexHull _ _ (mem_image_of_mem _ (by simpa [p] using hj))

/-- At a point with positive coordinates along a shared facet, two full-dimensional
simplices with disjoint interiors together contain a neighborhood. -/
theorem mem_interior_union_of_adjacent_simplices [Fintype ι] [Fintype κ]
    (b : AffineBasis ι ℝ V) (c : AffineBasis κ ℝ V) (i₀ : ι) (j₀ : κ)
    (hshare : ∀ j ≠ j₀, ∃ i ≠ i₀, b i = c j)
    (hdis : Disjoint (interior (convexHull ℝ (range b))) (interior (convexHull ℝ (range c))))
    {x : V} (hx : x ∈ convexHull ℝ (range c))
    (hxb : ∀ i ≠ i₀, 0 < b.coord i x) (hxc : ∀ j ≠ j₀, 0 < c.coord j x) :
    x ∈ interior (convexHull ℝ (range b) ∪ convexHull ℝ (range c)) := by
  let k := b.coord i₀ (c j₀)
  have heq : b.coord i₀ = k • c.coord j₀ := by
    apply AffineMap.ext_on c.tot
    rintro _ ⟨j, rfl⟩
    change b.coord i₀ (c j) = k • c.coord j₀ (c j)
    by_cases hj : j = j₀
    · subst j
      simp [k]
    · obtain ⟨i, hi, hij⟩ := hshare j hj
      rw [c.coord_apply_ne (Ne.symm hj), smul_zero, ← hij, b.coord_apply_ne hi.symm]
  have hscale (y : V) : b.coord i₀ y = k * c.coord j₀ y := by
    simpa only [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul] using DFunLike.congr_fun heq y
  let U := {y : V | ∀ i : {i : ι // i ≠ i₀}, 0 < b.coord i y}
  let W := {y : V | ∀ j : {j : κ // j ≠ j₀}, 0 < c.coord j y}
  have hU : IsOpen U := isOpen_positive_coords b i₀
  have hW : IsOpen W := isOpen_positive_coords c j₀
  have hxU : x ∈ U := fun i => hxb i i.property
  have hxW : x ∈ W := fun j => hxc j j.property
  have hk : k < 0 := by
    by_contra! hk
    have hk' : 0 < k := lt_of_le_of_ne hk fun hn => by
      simpa [← hn] using hscale (b i₀)
    have hcconv := convex_convexHull ℝ (range c)
    have hcl := hcconv.closure_interior_eq_closure_of_nonempty_interior
      ⟨_, c.centroid_mem_interior_convexHull⟩
    have hxcl : x ∈ closure (interior (convexHull ℝ (range c))) := hcl.symm ▸ subset_closure hx
    obtain ⟨y, hyU, hyc⟩ := mem_closure_iff_nhds.mp hxcl _ (hU.mem_nhds hxU)
    refine (Set.disjoint_left.mp hdis) (a := y) ?_ hyc
    rw [b.interior_convexHull]
    intro i
    by_cases hi : i = i₀
    · subst i
      rw [hscale]
      rw [c.interior_convexHull] at hyc
      exact mul_pos hk' (hyc j₀)
    · exact hyU ⟨i, hi⟩
  apply mem_interior_iff_mem_nhds.2
  apply Filter.mem_of_superset ((hU.inter hW).mem_nhds ⟨hxU, hxW⟩)
  rintro y ⟨hyU, hyW⟩
  by_cases hi₀ : 0 ≤ b.coord i₀ y
  · apply Or.inl
    rw [b.convexHull_eq_nonneg_coord]
    intro i
    by_cases hi : i = i₀
    · simpa [hi] using hi₀
    · exact (hyU ⟨i, hi⟩).le
  · apply Or.inr
    rw [c.convexHull_eq_nonneg_coord]
    intro j
    by_cases hj : j = j₀
    · subst j
      exact le_of_lt (pos_of_mul_neg_right (hscale y ▸ lt_of_not_ge hi₀) hk.le)
    · exact (hyW ⟨j, hj⟩).le

end Facet

/-- A finite pure three-dimensional complex with paired triangular facets fills a neighborhood
of every point whose closed star projects injectively. -/
theorem mem_interior_affine_image_closedStar {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [DecidableEq E] (K : SimplicialComplex ℝ E) (hfinite : K.faces.Finite)
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 4)
    (htriangle : ∀ t ∈ K.faces, t.card = 3 →
      ({p : E | {p} ∈ K.faces ∧ Disjoint t {p} ∧ t ∪ {p} ∈ K.faces} : Set E).ncard = 2)
    {s : Finset E} (hs : s ∈ K.faces) {a : E}
    (ha : a ∈ convexHull ℝ (s : Set E))
    (hminimal : ∀ t ∈ K.faces, a ∈ convexHull ℝ (t : Set E) → s ⊆ t)
    (f : E →ᵃ[ℝ] Target)
    (hf : InjOn f (⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E))) :
    f a ∈ interior (f '' (⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E))) := by
  classical
  let F : Set (Finset E) := {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces}
  let T : Set (Finset E) := {t | t ∈ K.faces ∧ s ⊆ t ∧ t.card = 4}
  let H (t : Finset E) := convexHull ℝ (f '' (t : Set E))
  let D := ⋃ t ∈ T, H t
  have hTstar {t : Finset E} (ht : t ∈ T) : t ∈ F :=
    ⟨ht.1, by simpa [Finset.union_eq_right.mpr ht.2.1] using ht.1⟩
  have hsubstar {t u : Finset E} (ht : t ∈ T) (hu : u ⊆ t) (hne : u.Nonempty) : u ∈ F :=
    ⟨K.down_closed ht.1 hu hne, K.down_closed ht.1 (Finset.union_subset ht.2.1 hu)
      (hne.mono Finset.subset_union_right)⟩
  have hH (t : Finset E) : H t = f '' convexHull ℝ (t : Set E) :=
    (f.image_convexHull _).symm
  have hHD {t : Finset E} (ht : t ∈ T) : H t ⊆ D := subset_iUnion₂ (s := fun t _ => H t) t ht
  have hD : f '' (⋃ t ∈ F, convexHull ℝ (t : Set E)) = D := by
    rw [image_iUnion]
    simp only [image_iUnion, ← hH]
    refine subset_antisymm ?_ (iUnion₂_subset fun t ht => ?_)
    · refine iUnion₂_subset fun u hu => ?_
      obtain ⟨t, ht, hst, h4⟩ := hpure (s ∪ u) hu.2
      exact (convexHull_mono (image_mono (Finset.coe_subset.mpr
        (Finset.subset_union_right.trans hst)))).trans
          (hHD ⟨ht, Finset.subset_union_left.trans hst, h4⟩)
    · exact subset_iUnion₂ (s := fun t _ => H t) t (hTstar ht)
  change f a ∈ interior (f '' (⋃ t ∈ F, convexHull ℝ (t : Set E)))
  rw [hD]
  have hclosed (A : Set (Finset E)) (hA : A ⊆ K.faces) : IsClosed (⋃ t ∈ A, H t) :=
    (hfinite.subset hA).isClosed_biUnion fun t _ =>
      ((t.finite_toSet.image f).isCompact_convexHull ℝ).isClosed
  let O : Set (Finset E) := {t ∈ F | ¬ s ⊆ t}
  let C := (⋃ t ∈ O, H t)ᶜ
  have hC : IsOpen C := (hclosed O fun t ht => ht.1.1).isOpen_compl
  have hsF : s ∈ F := ⟨hs, by simpa using hs⟩
  have haS : a ∈ ⋃ t ∈ F, convexHull ℝ (t : Set E) := mem_iUnion₂.mpr ⟨s, hsF, ha⟩
  have haC : f a ∈ C := by
    rintro h
    obtain ⟨t, ht, hta⟩ := mem_iUnion₂.mp h
    rw [hH] at hta
    obtain ⟨x, hx, hxa⟩ := hta
    have he : x = a := hf (mem_iUnion₂.mpr ⟨t, ht.1, hx⟩) haS hxa
    exact ht.2 (hminimal t ht.1.1 (he ▸ hx))
  obtain ⟨r, hr, hrC⟩ := Metric.isOpen_iff.mp hC (f a) haC
  let U := ball (f a) r
  have haU : f a ∈ U := mem_ball_self hr
  have hCoeRange (t : Finset E) : range ((↑) : t → E) = (t : Set E) := by
    ext x
    simp
  have hRange (t : Finset E) : range (fun x : t => f x) = f '' (t : Set E) := by
    change range (f ∘ ((↑) : t → E)) = _
    rw [Set.range_comp, hCoeRange]
  let b (t : Finset E) (ht : t ∈ T) : AffineBasis t ℝ Target := by
    have hind : AffineIndependent ℝ (fun x : t => f x) := by
      apply affineIndependent_comp_of_injOn_convexHull (K.indep ht.1) f
      rw [hCoeRange t]
      exact hf.mono (fun _ hx => mem_iUnion₂.mpr ⟨t, hTstar ht, hx⟩)
    exact ⟨_, hind, hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.2 (by simpa using ht.2.2)⟩
  have hb (t : Finset E) (ht : t ∈ T) : range (b t ht) = f '' (t : Set E) := hRange t
  have hinside : (U ∩ interior D).Nonempty := by
    obtain ⟨t, ht, hst, hcard⟩ := hpure s hs
    have htT : t ∈ T := ⟨ht, hst, hcard⟩
    have hta : f a ∈ H t := by rw [hH]; exact mem_image_of_mem _ (convexHull_mono hst ha)
    have hne : (interior (H t)).Nonempty := by
      change (interior (convexHull ℝ (f '' (t : Set E)))).Nonempty
      rw [← hb t htT]
      exact ⟨_, (b t htT).centroid_mem_interior_convexHull⟩
    have hcl : f a ∈ closure (interior (H t)) := by
      have hConv : Convex ℝ (H t) := convex_convexHull ℝ _
      rw [hConv.closure_interior_eq_closure_of_nonempty_interior hne]
      exact subset_closure hta
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff_nhds.mp hcl U (isOpen_ball.mem_nhds haU)
    exact ⟨z, hzU, interior_mono (hHD htT) hz⟩
  let B : Set (Finset E) := {u ∈ K.faces | u.card = 2}
  have hBF : B ⊆ K.faces := fun _ hu => hu.1
  have hcap {u v : Finset E} (hu : u ∈ F) (hv : v ∈ F) : H u ∩ H v ⊆ H (u ∩ v) := by
    rw [hH, hH, hH]
    rintro _ ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
    have he : y = x := hf (mem_iUnion₂.mpr ⟨v, hv, hy⟩) (mem_iUnion₂.mpr ⟨u, hu, hx⟩) hyx
    refine mem_image_of_mem _ ?_
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hu.1 hv.1]
    exact ⟨hx, he ▸ hy⟩
  have hOpp (t : Finset E) (ht : t ∈ T) (i : t) :
      b t ht '' ({i}ᶜ : Set t) = f '' (t.erase (i : E) : Set E) := by
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, Finset.mem_erase.mpr ⟨fun h => hj (Subtype.ext h), j.property⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨hvi, hvt⟩ := Finset.mem_erase.mp hv
      exact ⟨⟨v, hvt⟩, fun h => hvi (congrArg Subtype.val h), rfl⟩
  have hErase (t : Finset E) (ht : t ∈ T) (i : t) : t.erase (i : E) ∈ F :=
    hsubstar ht (Finset.erase_subset _ _) (Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem i.property, ht.2.2]; decide))
  have hCoord (t : Finset E) (ht : t ∈ T) {z : Target} (hz : z ∈ H t) (i : t) :
      z ∈ H (t.erase (i : E)) ↔ (b t ht).coord i z = 0 := by
    change z ∈ convexHull ℝ (f '' (t.erase (i : E) : Set E)) ↔ _
    rw [← hOpp t ht i]
    exact mem_convexHull_opposite_iff (b t ht) (by rwa [hb t ht]) i
  refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (isOpen_ball.mem_nhds haU) ?_)
  apply subset_of_frontier_covered_by_lines (hclosed T fun t ht => ht.1) isOpen_ball
    (convex_ball _ _) hinside ((hfinite.subset hBF).image
      (fun u : Finset E => f '' (u : Set E)))
  · rintro _ ⟨u, hu, rfl⟩
    change Module.finrank ℝ (vectorSpan ℝ (f '' (u : Set E))) ≤ 1
    rw [← hRange u]
    exact finrank_vectorSpan_range_le ℝ (fun x : u => f x) (by simpa using hu.2)
  intro z hz
  by_cases hsmall : ∃ u ∈ B, z ∈ H u
  · obtain ⟨u, hu, hzu⟩ := hsmall
    exact ⟨_, mem_image_of_mem _ hu, convexHull_subset_affineSpan _ hzu⟩
  exfalso
  have hzD := (hclosed T fun t ht => ht.1).frontier_subset hz.2
  obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hzD
  have hnot : ¬ ∀ i, 0 < (b t ht).coord i z := by
    intro h
    apply hz.2.2
    apply interior_mono (hHD ht)
    rw [show H t = convexHull ℝ (range (b t ht)) by rw [hb t ht], (b t ht).interior_convexHull]
    exact h
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hnonneg {t : Finset E} (ht : t ∈ T) (hzt : z ∈ H t) (k : t) :
      0 ≤ (b t ht).coord k z := by
    rw [show H t = convexHull ℝ (range (b t ht)) by rw [hb t ht],
      (b t ht).convexHull_eq_nonneg_coord] at hzt
    exact hzt k
  let u := t.erase (i : E)
  have hzu : z ∈ H u := (hCoord t ht hzt i).2 (le_antisymm (le_of_not_gt hi) (hnonneg ht hzt i))
  have huF : u ∈ F := hErase t ht i
  have hu3 : u.card = 3 := by rw [Finset.card_erase_of_mem i.property, ht.2.2]
  have hti : u ∪ {(i : E)} = t := by rw [Finset.union_singleton, Finset.insert_erase i.property]
  have hsu : s ⊆ u := by
    by_contra hs'
    exact (hrC hz.1) (mem_iUnion₂.mpr ⟨u, ⟨huF, hs'⟩, hzu⟩)
  let L : Set E := {p | {p} ∈ K.faces ∧ Disjoint u {p} ∧ u ∪ {p} ∈ K.faces}
  have hLn : L.ncard = 2 := htriangle u huF.1 hu3
  obtain ⟨p, q, hpq, hL⟩ := Set.ncard_eq_two.mp hLn
  have hother : ∃ j ∈ L, j ≠ (i : E) := by
    rw [hL]
    by_cases hpi : p = (i : E)
    · exact ⟨q, by simp, fun hqi => hpq (hpi.trans hqi.symm)⟩
    · exact ⟨p, by simp, hpi⟩
  obtain ⟨j, hj, hji⟩ := hother
  have hju := Finset.disjoint_singleton_right.mp hj.2.1
  let v := u ∪ {j}
  have hv : v ∈ T := ⟨hj.2.2, hsu.trans Finset.subset_union_left, by
    change (u ∪ {j}).card = 4
    rw [Finset.union_singleton, Finset.card_insert_of_notMem hju, hu3]⟩
  have hjv : j ∈ v := Finset.mem_union_right _ (Finset.mem_singleton_self _)
  let j₀ : v := ⟨j, hjv⟩
  have hve : v.erase j = u := by
    change (u ∪ {j}).erase j = u
    rw [Finset.union_singleton, Finset.erase_insert hju]
  have hzv : z ∈ H v := convexHull_mono (image_mono (Finset.coe_subset.mpr
    (Finset.subset_union_left : u ⊆ v))) hzu
  have huv : t ∩ v = u := by
    rw [← hti]
    ext x
    simp only [v, Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hx | hxi, hx' | hxj⟩
      · exact hx
      · exact hx
      · exact hx'
      · exact (hji (hxj.symm.trans hxi)).elim
    · intro hx
      exact ⟨Or.inl hx, Or.inl hx⟩
  have hpositive {t : Finset E} (ht : t ∈ T) (hzt : z ∈ H t) (i : t)
      (hzfacet : z ∈ H (t.erase (i : E))) (k : t) (hki : k ≠ i) : 0 < (b t ht).coord k z := by
    have hki' : (k : E) ≠ i := fun h => hki (Subtype.ext h)
    by_contra! hnot
    have hzero := le_antisymm hnot (hnonneg ht hzt k)
    have hzk := (hCoord t ht hzt k).2 hzero
    have he := hcap (hErase t ht k) (hErase t ht i) ⟨hzk, hzfacet⟩
    rw [Finset.erase_inter, Finset.inter_eq_right.mpr (Finset.erase_subset _ _)] at he
    have hkface : (k : E) ∈ t.erase (i : E) := Finset.mem_erase.2 ⟨hki', k.property⟩
    have hcard : ((t.erase (i : E)).erase (k : E)).card = 2 := by
      rw [Finset.card_erase_of_mem hkface, Finset.card_erase_of_mem i.property, ht.2.2]
    have hne : ((t.erase (i : E)).erase (k : E)).Nonempty := Finset.card_pos.mp (by simp [hcard])
    exact hsmall ⟨_, ⟨K.down_closed (hErase t ht i).1 (Finset.erase_subset _ _) hne, hcard⟩, he⟩
  have hshare (k : v) (hkj : k ≠ j₀) : ∃ l : t, l ≠ i ∧ b t ht l = b v hv k := by
    have hkU : (k : E) ∈ u := by
      rw [← hve]
      exact Finset.mem_erase.2 ⟨fun h => hkj (Subtype.ext h), k.property⟩
    have hku := Finset.mem_erase.mp hkU
    exact ⟨⟨k, hku.2⟩, fun h => hku.1 (congrArg Subtype.val h), rfl⟩
  have hdis : Disjoint (interior (convexHull ℝ (range (b t ht))))
      (interior (convexHull ℝ (range (b v hv)))) := by
    apply Set.disjoint_left.2
    intro y hyt hyv
    have hy : y ∈ H u := by
      rw [← huv]
      apply hcap (hTstar ht) (hTstar hv)
      simp only [hb] at hyt hyv
      exact ⟨interior_subset hyt, interior_subset hyv⟩
    have hy0 := (hCoord t ht (interior_subset (by simpa only [hb] using hyt)) i).1 hy
    rw [(b t ht).interior_convexHull] at hyt
    exact (hyt i).ne' hy0
  have hzfacet : z ∈ H (v.erase (j₀ : E)) := hve.symm ▸ hzu
  have hzint := mem_interior_union_of_adjacent_simplices (b t ht) (b v hv) i j₀ hshare hdis
    (by rwa [hb v hv]) (hpositive ht hzt i hzu) (hpositive hv hzv j₀ hzfacet)
  simp only [hb] at hzint
  exact hz.2.2 (interior_mono (Set.union_subset (hHD ht) (hHD hv)) hzint)

/-- The frozen projection centered at the active face maps its closed star onto a
neighborhood of zero. -/
theorem zero_mem_interior_frozenProjection_closedStar {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [DecidableEq E] (K : SimplicialComplex ℝ E) (hfinite : K.faces.Finite)
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 4)
    (htriangle : ∀ t ∈ K.faces, t.card = 3 →
      ({p : E | {p} ∈ K.faces ∧ Disjoint t {p} ∧ t ∪ {p} ∈ K.faces} : Set E).ncard = 2)
    {s : Finset E} (hs : s ∈ K.faces) {a : E}
    (ha : a ∈ convexHull ℝ (s : Set E))
    (hminimal : ∀ t ∈ K.faces, a ∈ convexHull ℝ (t : Set E) → s ⊆ t)
    (Q : E →L[ℝ] Target) (L : ℝ≥0)
    (hL : let S := ⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
        convexHull ℝ (t : Set E)
      ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L * ‖Q x - Q y‖) :
    (0 : Target) ∈ interior ((fun x : E => Q (x - a)) ''
      (⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
        convexHull ℝ (t : Set E))) := by
  let f : E →ᵃ[ℝ] Target := Q.toLinearMap.toAffineMap - AffineMap.const ℝ E (Q a)
  have hf : (f : E → Target) = fun x => Q (x - a) := by
    funext x
    change Q x - Q a = Q (x - a)
    rw [map_sub]
  have hinj : InjOn f (⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E)) := by
    intro x hx y hy hxy
    have hQxy : Q x = Q y := by
      simpa only [sub_add_cancel] using
        congrArg (fun z : Target => z + Q a) (show Q x - Q a = Q y - Q a from hxy)
    have h := hL x hx y hy
    have hnorm : ‖x - y‖ = 0 := le_antisymm (by simpa [hQxy] using h) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  simpa only [hf, sub_self, map_zero] using
    mem_interior_affine_image_closedStar K hfinite hpure htriangle hs ha hminimal f hinj

end Fleet.ChartImage

open Set Filter
open scoped ContDiff NNReal Topology

namespace Fleet.Charts

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The varying projection has the fixed projection as its strict derivative at the center. -/
theorem hasStrictFDerivAt_varyingProjection {Q : E → E →L[ℝ] V} {a : E}
    (hQ : ContDiffAt ℝ ∞ Q a) :
    HasStrictFDerivAt (fun y => Q y (y - a)) (Q a) a := by
  have hzero : (fderiv ℝ Q a).flip (a - a) = 0 := by
    ext x
    simp
  simpa only [ContinuousLinearMap.comp_id, hzero, add_zero] using
    (hQ.hasStrictFDerivAt (by simp)).clm_apply
      (hasStrictFDerivAt_sub_const (𝕜 := ℝ) (x := a) a)

/-- On a neighborhood of the center, the projection error has an arbitrarily small Lipschitz
constant, which can be chosen small relative to the inverse Lipschitz constant of fixed coordinates. -/
theorem exists_approximatesLinearOn_varyingProjection {Q : E → E →L[ℝ] V} {a : E}
    (hQ : ContDiffAt ℝ ∞ Q a) (L : ℝ≥0) :
    ∃ (c : ℝ≥0) (U : Set E), c < (L + 1)⁻¹ ∧ c * L < 1 ∧ IsOpen U ∧ a ∈ U ∧
      ApproximatesLinearOn (fun y => Q y (y - a)) (Q a) U c := by
  have hden : 0 < L + 1 := zero_lt_one.trans_le (le_add_of_nonneg_left zero_le)
  have hpos : 0 < (L + 1)⁻¹ := inv_pos.mpr hden
  let c : ℝ≥0 := (L + 1)⁻¹ / 2
  have hc : 0 < c := half_pos hpos
  have hlt : c < (L + 1)⁻¹ := half_lt_self hpos
  have hinv : (L + 1)⁻¹ * L < 1 := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_lt_one hden).mpr (lt_add_of_pos_right L zero_lt_one)
  have hmul : c * L < 1 := (mul_le_mul_of_nonneg_right hlt.le (show 0 ≤ L from zero_le)).trans_lt hinv
  obtain ⟨U, hU, happrox⟩ :=
    (hasStrictFDerivAt_varyingProjection hQ).approximates_deriv_on_nhds (Or.inr hc)
  obtain ⟨U₀, hsub, hopen, ha⟩ := _root_.mem_nhds_iff.mp hU
  exact ⟨c, U₀, hlt, hmul, hopen, ha, happrox.mono_set hsub⟩

/-- Given a fixed projection chart, the varying projection gives a chart in any prescribed
neighborhood. The lower Lipschitz bound is only required on the set containing the fixed chart. -/
theorem exists_varyingProjection_chart [CompleteSpace V] [Nontrivial V]
    {X : Type*} [TopologicalSpace X] {v : X → E} (hv : Continuous v) {a : X}
    {Q : E → E →L[ℝ] V} (hQ : ContDiffAt ℝ ∞ Q (v a))
    {S : Set E} (L : ℝ≥0)
    (hL : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L * ‖Q (v a) x - Q (v a) y‖)
    (d : OpenPartialHomeomorph X V) (ha : a ∈ d.source)
    (hS : ∀ x ∈ d.source, v x ∈ S)
    (hd : ∀ x ∈ d.source, d x = Q (v a) (v x - v a))
    {W : Set X} (hW : W ∈ 𝓝 a) :
    ∃ e : OpenPartialHomeomorph X V, a ∈ e.source ∧ e.source ⊆ W ∧
      ∀ x ∈ e.source, e x = Q (v x) (v x - v a) := by
  obtain ⟨c, U, _, hcL, hU, haU, happrox⟩ := exists_approximatesLinearOn_varyingProjection hQ L
  obtain ⟨W₀, hW₀W, hW₀, haW₀⟩ := _root_.mem_nhds_iff.mp hW
  let d₀ := d.restrOpen (W₀ ∩ v ⁻¹' U) (hW₀.inter (hU.preimage hv))
  have ha₀ : a ∈ d₀.source := ⟨ha, haW₀, haU⟩
  let f := fun z : V => Q (v (d₀.symm z)) (v (d₀.symm z) - v a)
  let idV := ContinuousLinearEquiv.refl ℝ V
  have hcoord (z : V) (hz : z ∈ d₀.target) : Q (v a) (v (d₀.symm z) - v a) = z := by
    have hs : d₀.symm z ∈ d₀.source := d₀.map_target hz
    exact (hd _ hs.1).symm.trans (d₀.right_inv hz)
  have happ : ApproximatesLinearOn f (idV : V →L[ℝ] V) d₀.target (c * L) := by
    intro x hx y hy
    have hx₀ : d₀.symm x ∈ d₀.source := d₀.map_target hx
    have hy₀ : d₀.symm y ∈ d₀.source := d₀.map_target hy
    have hlin : Q (v a) (v (d₀.symm x) - v (d₀.symm y)) = x - y := by
      rw [← sub_sub_sub_cancel_right (v (d₀.symm x)) (v (d₀.symm y)) (v a),
        map_sub, hcoord x hx, hcoord y hy]
    have hlower := hL _ (hS _ hx₀.1) _ (hS _ hy₀.1)
    rw [← map_sub, hlin] at hlower
    have hres := happrox _ hx₀.2.2 _ hy₀.2.2
    rw [hlin] at hres
    change ‖f x - f y - (x - y)‖ ≤ (c : ℝ) * (L : ℝ) * ‖x - y‖
    rw [mul_assoc]
    exact hres.trans (mul_le_mul_of_nonneg_left hlower c.coe_nonneg)
  have hid : ‖(idV.symm : V →L[ℝ] V)‖₊ = 1 := ContinuousLinearMap.nnnorm_id
  have hcId : Subsingleton V ∨ c * L < ‖(idV.symm : V →L[ℝ] V)‖₊⁻¹ := by
    exact Or.inr (by rwa [hid, inv_one])
  let p := happ.toOpenPartialHomeomorph f d₀.target hcId d₀.open_target
  refine ⟨d₀.trans' p rfl, ha₀, fun x hx => hW₀W hx.2.1, ?_⟩
  · intro x hx
    change f (d₀ x) = Q (v x) (v x - v a)
    simp only [f, d₀.left_inv hx]

end Fleet.Charts

open Set Filter Metric
open scoped NNReal Topology

namespace Fleet.Charts

private theorem fixedProjectionChart {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {f : X → Y} (hf : Continuous f) {a : X} {S : Set X} (hS : S ∈ 𝓝 a)
    (himage : f '' S ∈ 𝓝 (f a)) (L : ℝ≥0)
    (hL : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ L * dist (f x) (f y)) :
    ∃ e : OpenPartialHomeomorph X Y, a ∈ e.source ∧ e.source ⊆ S ∧ EqOn e f e.source := by
  classical
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨R, hR, hRS⟩ := Metric.mem_nhds_iff.mp himage
  have hpos : 0 < (L : ℝ) + 1 := by positivity
  let δ := min R (r / ((L : ℝ) + 1))
  have hδ : 0 < δ := lt_min hR (div_pos hr hpos)
  have hδr : ((L : ℝ) + 1) * δ ≤ r := by
    calc
      _ ≤ ((L : ℝ) + 1) * (r / ((L : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hpos.le
      _ = r := by field_simp [hpos.ne']
  let T := ball a r ∩ f ⁻¹' ball (f a) δ
  have hT : T ⊆ S := fun _ hx => hrS hx.1
  have haT : a ∈ T := ⟨mem_ball_self hr, mem_ball_self hδ⟩
  have hopen : IsOpen T := isOpen_ball.inter (isOpen_ball.preimage hf)
  have htarget : f '' T = ball (f a) δ := by
    refine subset_antisymm (fun z ⟨y, hy, h⟩ => h ▸ hy.2) ?_
    intro z hz
    have hzR : z ∈ ball (f a) R := (mem_ball.mp hz).trans_le (min_le_left _ _)
    obtain ⟨y, hy, rfl⟩ := hRS hzR
    refine ⟨y, ⟨?_, hz⟩, rfl⟩
    calc
      dist y a ≤ (L : ℝ) * dist (f y) (f a) := hL y hy a (mem_of_mem_nhds hS)
      _ ≤ ((L : ℝ) + 1) * dist (f y) (f a) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg
      _ < ((L : ℝ) + 1) * δ := mul_lt_mul_of_pos_left (mem_ball.mp hz) hpos
      _ ≤ r := hδr
  have hi : InjOn f T := by
    intro x hx y hy hxy
    have h := hL x (hT hx) y (hT hy)
    simpa [hxy] using h
  let : Nonempty X := ⟨a⟩
  let p := hi.toPartialEquiv f T
  have hpinv : LipschitzOnWith L p.symm p.target := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := hL _ (hT (p.map_target hx)) _ (hT (p.map_target hy))
    change dist (p.symm x) (p.symm y) ≤ L * dist (p (p.symm x)) (p (p.symm y)) at h
    simpa only [p.right_inv hx, p.right_inv hy] using h
  exact ⟨{ toPartialEquiv := p
           open_source := hopen
           open_target := by change IsOpen (f '' T); rw [htarget]; exact isOpen_ball
           continuousOn_toFun := hf.continuousOn
           continuousOn_invFun := hpinv.continuousOn }, haT, hT, fun _ _ => rfl⟩

theorem exists_fixedProjection_chart {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {A S : Set E} (hSA : S ⊆ A)
    (a : A) (q : E →L[ℝ] V) (L : ℝ≥0)
    (hL : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ L * ‖q x - q y‖)
    (hn : (Subtype.val ⁻¹' S : Set A) ∈ 𝓝 a)
    (hi : (0 : V) ∈ interior ((fun x : E => q (x - (a : E))) '' S)) :
    ∃ d : OpenPartialHomeomorph A V, a ∈ d.source ∧
      (∀ x ∈ d.source, (x : E) ∈ S) ∧
      ∀ x ∈ d.source, d x = q ((x : E) - (a : E)) := by
  let g := fun x : E => q (x - (a : E))
  let f := fun x : A => g x
  have hf : Continuous f := q.continuous.comp (continuous_subtype_val.sub continuous_const)
  have hEq : f '' (Subtype.val ⁻¹' S : Set A) = g '' S := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hSA hy⟩, hy, rfl⟩
  have hImage : f '' (Subtype.val ⁻¹' S : Set A) ∈ 𝓝 (f a) := by
    rw [hEq]
    have ha : f a = 0 := by simp [f, g]
    rw [ha]
    exact mem_interior_iff_mem_nhds.mp hi
  have hdist (x : A) (hx : x ∈ (Subtype.val ⁻¹' S : Set A))
      (y : A) (hy : y ∈ (Subtype.val ⁻¹' S : Set A)) :
      dist x y ≤ L * dist (f x) (f y) := by
    change dist (x : E) (y : E) ≤ L * dist (g x) (g y)
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : g x - g y = q x - q y := by
      simp only [g, map_sub]
      abel
    rw [hsub]
    exact hL x hx y hy
  exact fixedProjectionChart hf hn hImage L hdist

end Fleet.Charts

open Set Filter Geometry
open scoped NNReal Topology

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1.H2 := by
  classical
  intro m K
  dsimp only
  intro hfinite hpure htriangle s hs a ha Q J _W hQ _hJ hbound hW
  let E := EuclideanSpace ℝ (Fin m)
  let : DecidableEq E := Classical.decEq E
  let S : Set E :=
    ⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces}, convexHull ℝ (t : Set E)
  obtain ⟨L, hL⟩ := hbound
  have hSA : S ⊆ K.space := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact K.convexHull_subset_space ht.1 hxt
  have hn : (Subtype.val ⁻¹' S : Set K.space) ∈ 𝓝 a :=
    FleetCharts.closedStar_mem_nhds K hfinite hs ha
  have hi : (0 : EuclideanSpace ℝ (Fin 3)) ∈
      interior ((fun x : E => Q a (x - (a : E))) '' S) := by
    exact Fleet.ChartImage.zero_mem_interior_frozenProjection_closedStar K hfinite hpure htriangle hs
      (intrinsicInterior_subset ha)
      (fun t ht hat => FleetCharts.face_subset_of_intrinsicInterior_mem_convexHull hs ht ha hat)
      (Q a) L hL
  obtain ⟨d, had, hSd, hd⟩ :=
    Fleet.Charts.exists_fixedProjection_chart hSA a (Q a) L hL hn hi
  exact Fleet.Charts.exists_varyingProjection_chart continuous_subtype_val hQ L hL
    d had hSd hd hW
