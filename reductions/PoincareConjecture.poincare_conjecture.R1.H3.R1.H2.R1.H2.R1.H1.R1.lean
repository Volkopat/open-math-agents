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

-- Reduction PoincareConjecture.poincare_conjecture.R1.H3.R1.H2.R1.H2.R1.H1.R1

/-! A point in the carrier of a simplicial complex lies in the relative interior of
a unique face. -/

open Geometry Set
open scoped BigOperators

namespace Fleet.FaceCarrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem mem_intrinsicInterior_convexHull_iff_pos {s : Finset E}
    (hs : s.Nonempty) (hind : AffineIndependent ℝ ((↑) : s → E))
    {w : E → ℝ} (hw : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i • i) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ↔
      ∀ i ∈ s, 0 < w i := by
  classical
  obtain ⟨p, hp⟩ := hs
  let S := affineSpan ℝ (s : Set E)
  let p' : S := ⟨p, subset_affineSpan ℝ (s : Set E) hp⟩
  let : Nonempty (s : Set E) := ⟨⟨p, hp⟩⟩
  let : Nonempty S := ⟨p'⟩
  let e : S.direction ≃ᵃⁱ[ℝ] S := AffineIsometryEquiv.vaddConst ℝ p'
  let f : S.direction →ᵃ[ℝ] E := S.subtype.comp e.toAffineEquiv.toAffineMap
  let v : s → S.direction := fun i => e.symm ⟨i, subset_affineSpan ℝ (s : Set E) i.property⟩
  have hv (i : s) : f (v i) = (i : E) := by
    change (↑(e (e.symm ⟨i, subset_affineSpan ℝ (s : Set E) i.property⟩)) : E) = i
    rw [e.apply_symm_apply]
  have hv' : f ∘ v = ((↑) : s → E) := funext hv
  have hfi : Function.Injective f := S.subtype_injective.comp e.injective
  have hfv : f '' range v = (s : Set E) := by
    rw [← Set.range_comp, hv']
    exact Subtype.range_coe_subtype
  have hpre : range v = e.toAffineEquiv ⁻¹' (((↑) : S → E) ⁻¹' (s : Set E)) := by
    ext z
    change z ∈ range v ↔ f z ∈ (s : Set E)
    constructor
    · rintro ⟨i, rfl⟩
      rw [hv]
      exact i.property
    · intro hz
      exact ⟨⟨f z, hz⟩, hfi (hv ⟨f z, hz⟩)⟩
  let b : AffineBasis s ℝ S.direction := ⟨v, by
    apply AffineIndependent.of_comp f
    rwa [hv'], by
    rw [hpre, ← AffineSubspace.comap_span, affineSpan_coe_preimage_eq_top,
      AffineSubspace.comap_top]⟩
  have hfconv : f ⁻¹' convexHull ℝ (s : Set E) = convexHull ℝ (range b) := by
    change _ = convexHull ℝ (range v)
    calc
      _ = f ⁻¹' (f '' convexHull ℝ (range v)) := by rw [f.image_convexHull, hfv]
      _ = _ := Set.preimage_image_eq _ hfi
  let z := Finset.univ.affineCombination ℝ b (fun i : s => w i)
  have hsum : (∑ i : s, w i) = 1 := (Finset.sum_coe_sort s w).trans hw
  have hfz : f z = ∑ i ∈ s, w i • i := by
    dsimp only [z]
    rw [Finset.map_affineCombination _ _ _ hsum f,
      Finset.affineCombination_eq_linear_combination _ _ _ hsum]
    change (∑ i : s, w i • f (v i)) = _
    simp only [hv]
    exact Finset.sum_coe_sort s (fun i => w i • i)
  rw [← hfz, intrinsicInterior, affineSpan_convexHull]
  change e z ∈ Subtype.val ⁻¹'
    (Subtype.val '' interior (((↑) : S → E) ⁻¹' convexHull ℝ (s : Set E))) ↔ _
  rw [Set.preimage_image_eq _ Subtype.val_injective]
  change z ∈ e.toHomeomorph ⁻¹'
    interior (((↑) : S → E) ⁻¹' convexHull ℝ (s : Set E)) ↔ _
  rw [e.toHomeomorph.preimage_interior]
  change z ∈ interior (f ⁻¹' convexHull ℝ (s : Set E)) ↔ _
  rw [hfconv, b.interior_convexHull]
  change (∀ i : s, 0 < b.coord i z) ↔ _
  have hcoord (i : s) : b.coord i z = w i :=
    b.coord_apply_combination_of_mem (Finset.mem_univ i) hsum
  simp only [hcoord, Subtype.forall]

/-- Membership in the geometric carrier is equivalent to membership in a face's intrinsic
interior. -/
theorem mem_space_iff_exists_carrierFace {K : SimplicialComplex ℝ E} {x : E} :
    x ∈ K.space ↔
      ∃ s ∈ K.faces, x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  classical
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.1 hx
    obtain ⟨w, hw₀, hw₁, hwx⟩ := Finset.mem_convexHull'.1 hxt
    let s := t.filter fun i => 0 < w i
    have hst : s ⊆ t := Finset.filter_subset _ _
    have hz (i : E) (hi : i ∈ t) (his : i ∉ s) : w i = 0 :=
      le_antisymm (le_of_not_gt fun hh => his (Finset.mem_filter.mpr ⟨hi, hh⟩)) (hw₀ i hi)
    have hws : ∑ i ∈ s, w i = 1 := (Finset.sum_subset hst hz).trans hw₁
    have hxs : ∑ i ∈ s, w i • i = x :=
      (Finset.sum_subset hst fun i hi his => by rw [hz i hi his, zero_smul]).trans hwx
    have hsne : s.Nonempty := by
      by_contra h
      simp [Finset.not_nonempty_iff_eq_empty.mp h] at hws
    have hs := K.down_closed ht hst hsne
    refine ⟨s, hs, ?_⟩
    rw [← hxs]
    exact (mem_intrinsicInterior_convexHull_iff_pos hsne (K.indep hs) hws).2
      (fun i hi => (Finset.mem_filter.1 hi).2)
  · rintro ⟨s, hs, hx⟩
    exact K.convexHull_subset_space hs (intrinsicInterior_subset hx)

/-- Every point of the carrier belongs to the intrinsic interior of some simplex. -/
theorem exists_carrierFace (K : SimplicialComplex ℝ E) (a : K.space) :
    ∃ s ∈ K.faces, (a : E) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) :=
  mem_space_iff_exists_carrierFace.1 a.property

/-- Any simplex containing a point includes the face carrying that point. -/
theorem carrierFace_subset {K : SimplicialComplex ℝ E} {s t : Finset E} {x : E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hxt : x ∈ convexHull ℝ (t : Set E)) : s ⊆ t := by
  classical
  have hx' : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    exact ⟨intrinsicInterior_subset hx, hxt⟩
  obtain ⟨w, _, hw, hwx⟩ := Finset.mem_convexHull'.1 hx'
  let v : E → ℝ := ((s ∩ t : Finset E) : Set E).indicator w
  have hsub : s ∩ t ⊆ s := Finset.inter_subset_left
  have hv : ∑ i ∈ s, v i = 1 := (Finset.sum_indicator_subset w hsub).trans hw
  have hvx : ∑ i ∈ s, v i • i = x :=
    (Finset.sum_indicator_subset_of_eq_zero w (fun i r => r • i) hsub
      (fun i => zero_smul ℝ i)).trans hwx
  have hvpos := (mem_intrinsicInterior_convexHull_iff_pos
    (K.nonempty_of_mem_faces hs) (K.indep hs) hv).1 (hvx.symm ▸ hx)
  intro i hi
  by_contra hni
  exact (ne_of_gt (hvpos i hi)) (by simp [v, hni])

/-- The intrinsic interiors of distinct faces do not meet. -/
theorem existsUnique_carrierFace (K : SimplicialComplex ℝ E) (a : K.space) :
    ∃! s, s ∈ K.faces ∧ (a : E) ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  obtain ⟨s, hs, ha⟩ := exists_carrierFace K a
  refine ⟨s, ⟨hs, ha⟩, fun t ⟨ht, hat⟩ => ?_⟩
  exact Finset.Subset.antisymm (carrierFace_subset ht hs hat (intrinsicInterior_subset ha))
    (carrierFace_subset hs ht ha (intrinsicInterior_subset hat))

end Fleet.FaceCarrier

open Set Geometry
open scoped NNReal

namespace Fleet.StarLinear

variable {E V : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]

/-- Arbitrary values on an affinely independent set extend to an ambient affine map. -/
theorem exists_affineMap_eqOn {S : Set E} (hS : AffineIndependent ℝ ((↑) : S → E))
    (f : E → V) : ∃ A : E →ᵃ[ℝ] V, EqOn f A S := by
  obtain ⟨T, hST, hT, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hS
  let b : AffineBasis T ℝ E :=
    ⟨Subtype.val, hT, by simpa only [Subtype.range_coe] using hspan⟩
  obtain ⟨i⟩ := b.nonempty
  let L := (b.basisOf i).constr ℝ (fun j => f (b j) - f (b i))
  let A : E →ᵃ[ℝ] V :=
    AffineMap.mk' (fun x => L (x - b i) + f (b i)) L (b i) (by simp)
  refine ⟨A, fun x hx => ?_⟩
  let j : T := ⟨x, hST hx⟩
  change f (b j) = L (b j - b i) + f (b i)
  by_cases hji : j = i
  · simp [hji]
  · have hL : L (b j - b i) = f (b j) - f (b i) := by
      simpa [L] using (b.basisOf i).constr_basis ℝ (fun j => f (b j) - f (b i)) ⟨j, hji⟩
    rw [hL, sub_add_cancel]

variable (K : SimplicialComplex ℝ E)

theorem star_subset_star [DecidableEq E] {s s' : Finset E} (h : s ⊆ s') :
    ({t : Finset E | t ∈ K.faces ∧ s' ∪ t ∈ K.faces}) ⊆ ({t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces}) := by
  intro t ht
  refine ⟨ht.1, K.down_closed ht.2 (Finset.union_subset_union h Subset.rfl) ?_⟩
  exact (K.nonempty_of_mem_faces ht.1).mono Finset.subset_union_right

theorem carrier_mono {F G : Set (Finset E)} (h : F ⊆ G) : (⋃ t ∈ F, convexHull ℝ (t : Set E)) ⊆ (⋃ t ∈ G, convexHull ℝ (t : Set E)) :=
  fun _ hx => by
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨t, h ht, hxt⟩

/-- A map affine on each face of a family agrees there with a single affine map. -/
theorem exists_affineMap_eqOn_carrier
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) {F : Set (Finset E)}
    (hF : F ⊆ K.faces) {f : E → V}
    (hf : ∀ t ∈ F, ∃ B : E →ᵃ[ℝ] V, EqOn f B (convexHull ℝ (t : Set E))) :
    ∃ A : E →ᵃ[ℝ] V, EqOn f A ((⋃ t ∈ F, convexHull ℝ (t : Set E))) := by
  obtain ⟨A, hA⟩ := exists_affineMap_eqOn hK f
  refine ⟨A, fun x hx => ?_⟩
  obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
  obtain ⟨B, hB⟩ := hf t ht
  have hAB : EqOn B A (t : Set E) := by
    intro y hy
    exact (hB (subset_convexHull ℝ _ hy)).symm.trans (hA (K.down_closed (hF ht)
      (Finset.singleton_subset_iff.mpr hy) (Finset.singleton_nonempty _)))
  exact (hB hxt).trans (AffineMap.eqOn_affineSpan hAB (convexHull_subset_affineSpan _ hxt))

private theorem sum_extend_by_zero {ι M : Type*} [AddCommMonoid M] [DecidableEq ι]
    {s t : Finset ι} (hst : s ⊆ t) (w : ι → M) :
    (∑ z ∈ t, if z ∈ s then w z else 0) = ∑ z ∈ s, w z := by
  calc
    _ = ∑ z ∈ s, if z ∈ s then w z else 0 :=
      (Finset.sum_subset hst fun z _ hz => if_neg hz).symm
    _ = _ := Finset.sum_congr rfl fun z hz => if_pos hz

/-- Every nonzero secant between two simplices rescales to a secant between disjoint subfaces. -/
private theorem secant_rescale {s t : Finset E} {x y : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) (hy : y ∈ convexHull ℝ (t : Set E))
    (hxy : x ≠ y) :
    ∃ (a b : Finset E) (x' y' : E) (r : ℝ), a ⊆ s ∧ b ⊆ t ∧ Disjoint a b ∧
      x' ∈ convexHull ℝ (a : Set E) ∧ y' ∈ convexHull ℝ (b : Set E) ∧
      0 < r ∧ x - y = r • (x' - y') := by
  classical
  obtain ⟨u, hu₀, hu₁, hux⟩ := Finset.mem_convexHull'.mp hx
  obtain ⟨v, hv₀, hv₁, hvy⟩ := Finset.mem_convexHull'.mp hy
  let u' (z : E) := if z ∈ s then u z else 0
  let v' (z : E) := if z ∈ t then v z else 0
  let w (z : E) := u' z - v' z
  let a := (s ∪ t).filter (fun z => 0 < w z)
  let b := (s ∪ t).filter (fun z => w z < 0)
  have hu' (z : E) : 0 ≤ u' z := by
    by_cases hz : z ∈ s <;> simp [u', hz, hu₀]
  have hv' (z : E) : 0 ≤ v' z := by
    by_cases hz : z ∈ t <;> simp [v', hz, hv₀]
  have ha : a ⊆ s := by
    intro z hz
    have hp := (Finset.mem_filter.mp hz).2
    by_contra h
    have hu : u' z = 0 := if_neg h
    exact (not_lt_of_ge (sub_nonpos.mpr ((le_of_eq hu).trans (hv' z)))) hp
  have hb : b ⊆ t := by
    intro z hz
    have hn := (Finset.mem_filter.mp hz).2
    by_contra h
    have hv : v' z = 0 := if_neg h
    exact (not_lt_of_ge (sub_nonneg.mpr ((le_of_eq hv).trans (hu' z)))) hn
  have hab : Disjoint a b := Finset.disjoint_left.mpr fun z ha' hb' =>
    (not_lt_of_ge (le_of_lt (Finset.mem_filter.mp ha').2)) (Finset.mem_filter.mp hb').2
  have hsplit (z : E) :
      (if 0 < w z then w z else 0) - (if w z < 0 then -w z else 0) = w z := by
    by_cases hp : 0 < w z
    · simp [hp, not_lt_of_ge hp.le]
    by_cases hn : w z < 0
    · simp [hp, hn]
    have he : w z = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
    simp [he]
  have hmass : (∑ z ∈ a, w z) = ∑ z ∈ b, -w z := by
    apply sub_eq_zero.mp
    simp only [a, b, Finset.sum_filter, ← Finset.sum_sub_distrib, hsplit]
    change (∑ z ∈ s ∪ t, (u' z - v' z)) = 0
    rw [Finset.sum_sub_distrib, sum_extend_by_zero Finset.subset_union_left,
      sum_extend_by_zero Finset.subset_union_right, hu₁, hv₁, sub_self]
  have hvec : (∑ z ∈ a, w z • z) - (∑ z ∈ b, (-w z) • z) = x - y := by
    have hvsplit (z : E) :
        (if 0 < w z then w z • z else 0) - (if w z < 0 then (-w z) • z else 0) =
          w z • z := by
      simpa only [sub_smul, ite_smul, zero_smul] using congrArg (fun c : ℝ => c • z) (hsplit z)
    simp only [a, b, Finset.sum_filter, ← Finset.sum_sub_distrib]
    simp_rw [hvsplit, w, sub_smul]
    rw [Finset.sum_sub_distrib]
    simp only [u', v', ite_smul, zero_smul]
    rw [sum_extend_by_zero Finset.subset_union_left, sum_extend_by_zero Finset.subset_union_right,
      hux, hvy]
  let r := ∑ z ∈ a, w z
  have hr : 0 < r := by
    by_contra hn
    have h := le_of_not_gt hn
    have ha₀ : a = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun hne =>
      (not_lt_of_ge h) (Finset.sum_pos (fun z hz => (Finset.mem_filter.mp hz).2) hne)
    have hb₀ : b = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun hne => by
      have hp := Finset.sum_pos (fun z hz => neg_pos.mpr (Finset.mem_filter.mp hz).2) hne
      rw [← hmass, ha₀, Finset.sum_empty] at hp
      exact (lt_irrefl 0) hp
    apply hxy (sub_eq_zero.mp _)
    simpa [ha₀, hb₀] using hvec.symm
  let x' := r⁻¹ • ∑ z ∈ a, w z • z
  let y' := r⁻¹ • ∑ z ∈ b, (-w z) • z
  refine ⟨a, b, x', y', r, ha, hb, hab, ?_, ?_, hr, ?_⟩
  · refine Finset.mem_convexHull'.mpr ⟨fun z => r⁻¹ * w z, fun z hz => ?_, ?_, ?_⟩
    · exact mul_nonneg (inv_nonneg.mpr hr.le) (le_of_lt (Finset.mem_filter.mp hz).2)
    · rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hr.ne'
    · simp only [x', mul_smul, Finset.smul_sum]
  · refine Finset.mem_convexHull'.mpr ⟨fun z => r⁻¹ * (-w z), fun z hz => ?_, ?_, ?_⟩
    · exact mul_nonneg (inv_nonneg.mpr hr.le) (le_of_lt (neg_pos.mpr (Finset.mem_filter.mp hz).2))
    · rw [← Finset.mul_sum, ← hmass]
      exact inv_mul_cancel₀ hr.ne'
    · simp only [y', mul_smul, Finset.smul_sum]
  · dsimp only [x', y']
    rw [← smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, hvec]

section Normed

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- An affine map whose image contains a nonempty open set has a split surjective linear part. -/
theorem exists_rightInverse_linear_of_nonempty_interior
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] {A : X →ᵃ[ℝ] Y} {S : Set X}
    (hA : (interior (A '' S)).Nonempty) : A.linear.toContinuousLinearMap.HasRightInverse := by
  have htop : (⊤ : AffineSubspace ℝ X).map A = ⊤ := by
    have hspan : affineSpan ℝ (interior (A '' S)) ≤ (⊤ : AffineSubspace ℝ X).map A := by
      apply affineSpan_le.mpr
      intro y hy
      obtain ⟨x, -, rfl⟩ := interior_subset hy
      exact AffineSubspace.mem_map_of_mem A (AffineSubspace.mem_top ℝ X x)
    rw [isOpen_interior.affineSpan_eq_top hA] at hspan
    exact top_unique hspan
  have hsurj : Function.Surjective A := by
    intro y
    have hy : y ∈ (⊤ : AffineSubspace ℝ X).map A := htop.symm ▸ AffineSubspace.mem_top ℝ Y y
    obtain ⟨x, -, hx⟩ := AffineSubspace.mem_map.mp hy
    exact ⟨x, hx⟩
  exact ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional
    (A.linear_surjective_iff.mpr hsurj)

/-- A right inverse identifies the codimension of the kernel with the target dimension. -/
theorem finrank_ker_add_finrank_of_rightInverse [FiniteDimensional ℝ X]
    (Q : X →L[ℝ] Y) {J : Y →L[ℝ] X} (hJ : Function.RightInverse J Q) :
    Module.finrank ℝ Q.ker + Module.finrank ℝ Y = Module.finrank ℝ X := by
  have hrange : LinearMap.range Q.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr hJ.surjective
  have h := Q.toLinearMap.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, add_comm] at h
  exact h

/-- A linear map injective on the carrier of a finite, downward-closed family of faces satisfies
a uniform lower Lipschitz bound on that carrier. -/
theorem norm_sub_le_mul_of_injOn_carrier (K : SimplicialComplex ℝ X) {F : Set (Finset X)}
    (hF : F ⊆ K.faces) (hFfin : F.Finite)
    (hdown : ∀ ⦃s t : Finset X⦄, s ∈ F → t ⊆ s → t.Nonempty → t ∈ F)
    (Q : X →L[ℝ] Y) (hQ : InjOn Q ((⋃ t ∈ F, convexHull ℝ (t : Set X)))) :
    ∃ L : ℝ≥0, ∀ x ∈ (⋃ t ∈ F, convexHull ℝ (t : Set X)), ∀ y ∈ (⋃ t ∈ F, convexHull ℝ (t : Set X)), ‖x - y‖ ≤ L * ‖Q x - Q y‖ := by
  classical
  let pairs : Set (Finset X × Finset X) := {p ∈ F ×ˢ F | Disjoint p.1 p.2}
  let faceHull (s : Finset X) := convexHull ℝ (s : Set X)
  let diff (p : X × X) := p.1 - p.2
  let D := ⋃ p ∈ pairs, diff '' (faceHull p.1 ×ˢ faceHull p.2)
  have hD : IsCompact D :=
    ((hFfin.prod hFfin).subset (sep_subset ..)).isCompact_biUnion fun p _ =>
      (((Finset.finite_toSet p.1).isCompact_convexHull ℝ).prod
        ((Finset.finite_toSet p.2).isCompact_convexHull ℝ)).image
          (continuous_fst.sub continuous_snd)
  have hDpos : ∀ d ∈ D, 0 < ‖Q d‖ := by
    intro d hd
    obtain ⟨⟨s, t⟩, ⟨⟨hs, ht⟩, hst⟩, ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩⟩ := mem_iUnion₂.mp hd
    apply norm_pos_iff.mpr
    intro hzero
    have hQxy : Q x = Q y := sub_eq_zero.mp (by simpa only [diff, map_sub] using hzero)
    have hxy : x = y :=
      hQ (mem_iUnion₂.mpr ⟨s, hs, hx⟩) (mem_iUnion₂.mpr ⟨t, ht, hy⟩) hQxy
    subst y
    change Disjoint s t at hst
    have h := K.inter_subset_convexHull (hF hs) (hF ht) ⟨hx, hy⟩
    simp [← Finset.coe_inter, Finset.disjoint_iff_inter_eq_empty.mp hst] at h
  obtain ⟨ε, hε, hεD⟩ := hD.exists_forall_le' Q.continuous.norm.continuousOn hDpos
  obtain ⟨M, hM, hMD⟩ := hD.isBounded.exists_pos_norm_le
  let L : ℝ≥0 := ⟨M / ε, (div_pos hM hε).le⟩
  refine ⟨L, fun x hx y hy => ?_⟩
  by_cases hxy : x = y
  · simp [hxy]
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
  obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp hy
  obtain ⟨a, b, x', y', r, ha, hb, hab, hx', hy', hr, hsec⟩ := secant_rescale hxs hyt hxy
  have haF : a ∈ F := hdown hs ha (by simpa using convexHull_nonempty_iff.mp ⟨x', hx'⟩)
  have hbF : b ∈ F := hdown ht hb (by simpa using convexHull_nonempty_iff.mp ⟨y', hy'⟩)
  have hd : x' - y' ∈ D := mem_iUnion₂.mpr
    ⟨(a, b), ⟨⟨haF, hbF⟩, hab⟩, ⟨(x', y'), ⟨hx', hy'⟩, rfl⟩⟩
  have hsecbound : ‖x' - y'‖ ≤ (L : ℝ) * ‖Q (x' - y')‖ :=
    (hMD _ hd).trans <| by
      dsimp [L]
      calc
        M = M / ε * ε := (div_mul_cancel₀ M hε.ne').symm
        _ ≤ M / ε * ‖Q (x' - y')‖ := mul_le_mul_of_nonneg_left (hεD _ hd) (div_pos hM hε).le
  rw [← map_sub, hsec, map_smul, norm_smul, norm_smul, Real.norm_of_nonneg hr.le]
  simpa only [mul_left_comm (L : ℝ) r] using mul_le_mul_of_nonneg_left hsecbound hr.le

/-- The fixed projection and its right inverse supplied by an embedded vertex star. -/
theorem exists_star_projection (K : SimplicialComplex ℝ X) [DecidableEq X]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (hK : AffineIndependent ℝ ((↑) : K.vertices → X)) (hfin : K.faces.Finite)
    {p : X} {f : X → Y}
    (haff : ∀ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), ∃ B : X →ᵃ[ℝ] Y, EqOn f B (convexHull ℝ (t : Set X)))
    (hinj : InjOn f ((⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X))))
    (hint : (interior (f '' (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)))).Nonempty) :
    ∃ (Q : X →L[ℝ] Y) (J : Y →L[ℝ] X) (L : ℝ≥0), Function.RightInverse J Q ∧
      ∀ x ∈ (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)), ∀ y ∈ (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)), ‖x - y‖ ≤ L * ‖Q x - Q y‖ := by
  have hsub : ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}) ⊆ K.faces := fun _ ht => ht.1
  obtain ⟨A, hA⟩ := exists_affineMap_eqOn_carrier K hK hsub haff
  let Q := A.linear.toContinuousLinearMap
  have hintA : (interior (A '' (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)))).Nonempty := hA.image_eq ▸ hint
  obtain ⟨J, hJ⟩ := exists_rightInverse_linear_of_nonempty_interior hintA
  have hQ : InjOn Q ((⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X))) := by
    intro x hx y hy hxy
    apply hinj hx hy
    rw [hA hx, hA hy, ← sub_eq_zero, ← vsub_eq_sub, ← A.linearMap_vsub]
    change Q (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hdown ⦃s t : Finset X⦄ (hs : s ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces})) (hst : t ⊆ s) (ht : t.Nonempty) :
      t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}) :=
    ⟨K.down_closed hs.1 hst ht, K.down_closed hs.2 (Finset.union_subset_union_right hst)
      (ht.mono Finset.subset_union_right)⟩
  obtain ⟨L, hL⟩ := norm_sub_le_mul_of_injOn_carrier K hsub (hfin.subset hsub) hdown Q hQ
  exact ⟨Q, J, L, hJ, hL⟩

/-- The fixed projection for a face comes from the star of any vertex of the face. -/
theorem exists_face_projection (K : SimplicialComplex ℝ X) [DecidableEq X]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (hK : AffineIndependent ℝ ((↑) : K.vertices → X)) (hfin : K.faces.Finite)
    (hvertex : ∀ p : X, {p} ∈ K.faces → ∃ f : X → Y,
      (∀ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), ∃ B : X →ᵃ[ℝ] Y, EqOn f B (convexHull ℝ (t : Set X))) ∧
        InjOn f ((⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X))) ∧ (interior (f '' (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)))).Nonempty)
    {s : Finset X} (hs : s ∈ K.faces) :
    ∃ (Q : X →L[ℝ] Y) (J : Y →L[ℝ] X) (L : ℝ≥0), Function.RightInverse J Q ∧
      ∀ x ∈ (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ s ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)), ∀ y ∈ (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ s ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)), ‖x - y‖ ≤ L * ‖Q x - Q y‖ := by
  obtain ⟨p, hp⟩ := K.nonempty_of_mem_faces hs
  have hps : {p} ⊆ s := Finset.singleton_subset_iff.mpr hp
  have hpK := K.down_closed hs hps (Finset.singleton_nonempty p)
  obtain ⟨f, haff, hinj, hint⟩ := hvertex p hpK
  obtain ⟨Q, J, L, hJ, hL⟩ := exists_star_projection K hK hfin haff hinj hint
  have hsub := carrier_mono (star_subset_star K hps)
  exact ⟨Q, J, L, hJ, fun x hx y hy => hL x (hsub hx) y (hsub hy)⟩

/-- Any fixed projection injective on a closed star satisfies a uniform lower Lipschitz bound. -/
theorem norm_sub_le_mul_of_injOn_star (K : SimplicialComplex ℝ X) [DecidableEq X]
    (hfin : K.faces.Finite) {s : Finset X} (Q : X →L[ℝ] Y)
    (hQ : InjOn Q ((⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ s ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)))) :
    ∃ L : ℝ≥0, ∀ x ∈ (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ s ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)), ∀ y ∈ (⋃ t ∈ ({t : Finset X | t ∈ K.faces ∧ s ∪ t ∈ K.faces}), convexHull ℝ (t : Set X)),
      ‖x - y‖ ≤ L * ‖Q x - Q y‖ := by
  have hsub : ({t : Finset X | t ∈ K.faces ∧ s ∪ t ∈ K.faces}) ⊆ K.faces := fun _ ht => ht.1
  apply norm_sub_le_mul_of_injOn_carrier K hsub (hfin.subset hsub) _ Q hQ
  intro t u ht htu hu
  exact ⟨K.down_closed ht.1 htu hu, K.down_closed ht.2 (Finset.union_subset_union_right htu)
    (hu.mono Finset.subset_union_right)⟩

end Normed

end Fleet.StarLinear

open Set Filter Function Geometry Metric
open scoped ContDiff NNReal Topology

namespace Fleet.Planes

theorem exists_normalized_field {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
    {P : E → Submodule ℝ E} {a : E} {U : Set E} {R : E → E →L[ℝ] V}
    (hU : IsOpen U) (ha : a ∈ U) (hR : ContDiffOn ℝ ∞ R U) (hsurj : Surjective (R a))
    (hker : ∀ y ∈ U, (R y).ker = P y)
    (hleaf : ∀ y ∈ U, ∀ᶠ z in 𝓝 y, z - y ∈ P y → P z = P y) :
    ∃ (U' : Set E) (J : V →L[ℝ] E) (Q : E → E →L[ℝ] V),
      IsOpen U' ∧ a ∈ U' ∧ ContDiffOn ℝ ∞ Q U' ∧ Q a = R a ∧
      ∀ y ∈ U', RightInverse J (Q y) ∧ (Q y).ker = P y ∧
        ∀ᶠ z in 𝓝 y, z - y ∈ P y → Q z = Q y := by
  obtain ⟨J, hJ⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hsurj
  let B := fun y => (R y).comp J
  have hB : ContDiffOn ℝ ∞ B U := hR.clm_comp contDiffOn_const
  have hBa : B a = 1 := by
    ext v
    exact hJ v
  let U' := U ∩ B ⁻¹' {b | IsUnit b}
  have hU' : IsOpen U' := hB.continuousOn.isOpen_inter_preimage hU Units.isOpen
  have ha' : a ∈ U' := ⟨ha, by change IsUnit (B a); rw [hBa]; exact isUnit_one⟩
  have hB' (y) (hy : y ∈ U') : (B y).IsInvertible := by
    have h : IsUnit (B y) := hy.2
    obtain ⟨u, hu⟩ := h
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ V u, hu⟩
  let Q := fun y => (B y).inverse.comp (R y)
  have hQ : ContDiffOn ℝ ∞ Q U' := by
    intro y hy
    have hny := hU.mem_nhds hy.1
    exact (((hB' y hy).contDiffAt_map_inverse.comp y (hB.contDiffAt hny)).clm_comp
      (hR.contDiffAt hny)).contDiffWithinAt
  have hbase : Q a = R a := by
    change (B a).inverse.comp (R a) = R a
    rw [hBa]
    simp [ContinuousLinearMap.one_def]
  have hright (y) (hy : y ∈ U') : RightInverse J (Q y) := fun v =>
    (hB' y hy).inverse_apply_self v
  have hQker (y) (hy : y ∈ U') : (Q y).ker = P y := by
    rw [← hker y hy.1]
    ext x
    change (B y).inverse (R y x) = 0 ↔ R y x = 0
    constructor
    · intro hx
      simpa only [(hB' y hy).self_apply_inverse, map_zero] using congrArg (B y) hx
    · intro hx
      rw [hx, map_zero]
  refine ⟨U', J, Q, hU', ha', hQ, hbase, fun y hy => ⟨hright y hy, hQker y hy, ?_⟩⟩
  filter_upwards [hU'.mem_nhds hy, hleaf y hy.1] with z hz hP
  intro hzy
  have hPzy := hP hzy
  ext v
  have hv : v - J (Q y v) ∈ (Q y).ker := by
    change Q y (v - J (Q y v)) = 0
    rw [map_sub, hright y hy, sub_self]
  have hvz : v - J (Q y v) ∈ (Q z).ker := by
    rwa [hQker z hz, hPzy, ← hQker y hy]
  change Q z (v - J (Q y v)) = 0 at hvz
  rw [map_sub, hright z hz] at hvz
  exact sub_eq_zero.mp hvz

theorem injOn_closedStar_of_local {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {a : E} {s : Finset E} {r : ℝ} {q : E →L[ℝ] V}
    (ha : a ∈ convexHull ℝ (s : Set E)) (hr : 0 < r)
    (hinj : InjOn q (K.space ∩ ball a r)) :
    InjOn q (⋃ t ∈ {t : Finset E | t ∈ K.faces ∧ s ∪ t ∈ K.faces}, convexHull ℝ (t : Set E)) := by
  intro x hx y hy hxy
  simp only [mem_iUnion, mem_ofPred_eq] at hx hy
  obtain ⟨t, ⟨_, ht⟩, hx⟩ := hx
  obtain ⟨u, ⟨_, hu⟩, hy⟩ := hy
  have hnear (z : E) : ∀ᶠ c : ℝ in 𝓝 0, AffineMap.lineMap a z c ∈ ball a r := by
    have hcont : Continuous (fun c : ℝ => AffineMap.lineMap a z c) := by
      simp only [AffineMap.lineMap_apply_module']
      fun_prop
    have ht : Tendsto (fun c : ℝ => AffineMap.lineMap a z c) (𝓝 0)
        (𝓝 (AffineMap.lineMap a z (0 : ℝ))) := hcont.continuousAt
    rw [AffineMap.lineMap_apply_zero] at ht
    exact ht.eventually (show ∀ᶠ w in 𝓝 a, w ∈ ball a r from isOpen_ball.mem_nhds (mem_ball_self hr))
  have hboth := (hnear x).and (hnear y)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hboth
  let c := min (ε / 2) (1 / 2)
  have hc : 0 < c := lt_min (half_pos hε) (by norm_num)
  have hcε : c ∈ ball (0 : ℝ) ε := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hc]
    exact (min_le_left _ _).trans_lt (half_lt_self hε)
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc.le, (min_le_right _ _).trans (by norm_num)⟩
  have hmem (w : Finset E) (hw : s ∪ w ∈ K.faces) (z : E) (hz : z ∈ convexHull ℝ (w : Set E)) :
      AffineMap.lineMap a z c ∈ K.space := by
    apply K.convexHull_subset_space hw
    apply (convex_convexHull ℝ _).lineMap_mem _ _ hcI
    · exact convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left) ha
    · exact convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_right) hz
  have heq : AffineMap.lineMap a x c = AffineMap.lineMap a y c := by
    apply hinj ⟨hmem t ht x hx, (hεsub hcε).1⟩ ⟨hmem u hu y hy, (hεsub hcε).2⟩
    simp only [AffineMap.lineMap_apply_module', map_add, map_smul, map_sub, hxy]
  rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module', add_right_cancel_iff] at heq
  have hdiff : x - a = y - a := (smul_right_injective E hc.ne') heq
  calc
    x = (x - a) + a := (sub_add_cancel x a).symm
    _ = (y - a) + a := congrArg (· + a) hdiff
    _ = y := sub_add_cancel y a

theorem codim_and_secants_of_projection {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S : Set E} (q : E →L[ℝ] V) (hsurj : Surjective q) (hinj : InjOn q S) :
    Module.finrank ℝ q.ker + Module.finrank ℝ V = Module.finrank ℝ E ∧
      ∀ x ∈ S, ∀ y ∈ S, x - y ∈ q.ker → x = y := by
  constructor
  · have htop : LinearMap.range q.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have h := q.toLinearMap.finrank_range_add_finrank_ker
    rw [htop, finrank_top, add_comm] at h
    exact h
  · intro x hx y hy hxy
    apply hinj hx hy
    change q (x - y) = 0 at hxy
    rwa [map_sub, sub_eq_zero] at hxy

end Fleet.Planes

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∀ (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let S (s : Finset E) := ⋃ t ∈ {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E)
    let G (s : Finset E) := {P : Submodule ℝ E //
      Module.finrank ℝ P + 3 = m ∧ ∀ x ∈ S s, ∀ y ∈ S s, x - y ∈ P → x = y}
    let topo (s : Finset E) : TopologicalSpace (G s) :=
      TopologicalSpace.induced (fun P : G s => P.val.starProjection) inferInstance
    let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
    AffineIndependent ℝ ((↑) : K.vertices → E) → K.faces.Finite →
    (∀ s ∈ K.faces, s.card ≤ 4) →
    (∀ s ∈ K.faces, s.card = 2 →
      IsConnected (⋃ t ∈ link s, convexHull ℝ (t : Set E))) →
    (∀ s ∈ K.faces, s.card = 3 → ({p : E | {p} ∈ link s} : Set E).ncard = 2) →
    ∀ s ∈ K.faces, 2 ≤ s.card → @ContractibleSpace (G s) (topo s)

def H2 : Prop :=
  ∀ (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let S (s : Finset E) := ⋃ t ∈ {t | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
      convexHull ℝ (t : Set E)
    let G (s : Finset E) := {P : Submodule ℝ E //
      Module.finrank ℝ P + 3 = m ∧ ∀ x ∈ S s, ∀ y ∈ S s, x - y ∈ P → x = y}
    let topo (s : Finset E) : TopologicalSpace (G s) :=
      TopologicalSpace.induced (fun P : G s => P.val.starProjection) inferInstance
    let V := EuclideanSpace ℝ (Fin 3)
    K.faces.Finite → (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) →
    (∀ s ∈ K.faces, s.card = 1 → Nonempty (G s)) →
    (∀ s ∈ K.faces, 2 ≤ s.card → @ContractibleSpace (G s) (topo s)) →
    ∃ P : E → Submodule ℝ E,
      ∀ a : K.space, ∃ (U : Set E) (R : E → E →L[ℝ] V) (r : ℝ),
        IsOpen U ∧ (a : E) ∈ U ∧ ContDiffOn ℝ ∞ R U ∧ Function.Surjective (R a) ∧
        0 < r ∧ InjOn (R a) (K.space ∩ ball (a : E) r) ∧
        (∀ y ∈ U, (R y).ker = P y) ∧
        (∀ y ∈ U, ∀ᶠ z in 𝓝 y, z - y ∈ P y → P z = P y)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1.H1 := by
  classical
  intro hcontract hglue m K
  dsimp only
  intro hind hfinite hpure hedges htriangles hvertices
  let : DecidableEq (EuclideanSpace ℝ (Fin m)) := Classical.decEq _
  have hsmall (s : Finset (EuclideanSpace ℝ (Fin m))) (hs : s ∈ K.faces) : s.card ≤ 4 := by
    obtain ⟨t, _, hst, hcard⟩ := hpure s hs
    exact hcard ▸ Finset.card_le_card hst
  have hfield := hglue m K hfinite hpure (by
    intro s hs _
    obtain ⟨Q, J, L, hJ, hL⟩ := Fleet.StarLinear.exists_face_projection
      (Y := EuclideanSpace ℝ (Fin 3)) K hind hfinite (by
        intro p hp
        obtain ⟨f, haff, hinj, hint⟩ := hvertices p hp
        refine ⟨f, ?_, hinj, hint⟩
        intro t ht
        obtain ⟨A, hA⟩ := haff t ht
        exact ⟨A.toAffineMap, hA⟩) hs
    have hi : InjOn Q (⋃ t ∈ {t : Finset (EuclideanSpace ℝ (Fin m)) | t ∈ K.faces ∧ s ∪ t ∈ K.faces},
        convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin m)))) := by
      intro x hx y hy hxy
      have h := hL x hx y hy
      exact sub_eq_zero.mp (norm_eq_zero.mp
        (le_antisymm (by simpa [hxy] using h) (norm_nonneg _)))
    have h := Fleet.Planes.codim_and_secants_of_projection Q hJ.surjective hi
    exact ⟨⟨Q.ker, by simpa only [finrank_euclideanSpace_fin] using h.1, h.2⟩⟩)
    (hcontract m K hind hfinite hsmall hedges htriangles)
  obtain ⟨P, hP⟩ := hfield
  refine ⟨P, ?_⟩
  intro a
  obtain ⟨s, hs, hsa⟩ := Fleet.FaceCarrier.exists_carrierFace K a
  obtain ⟨U, R, r, hU, ha, hR, hsurj, hr, hlocal, hker, hleaf⟩ := hP a
  obtain ⟨U', J, Q, hU', ha', hQ, hbase, hprops⟩ :=
    Fleet.Planes.exists_normalized_field hU ha hR hsurj hker hleaf
  have hstar := Fleet.Planes.injOn_closedStar_of_local (intrinsicInterior_subset hsa) hr hlocal
  have hb := Fleet.StarLinear.norm_sub_le_mul_of_injOn_star K hfinite (s := s) (R a) hstar
  refine ⟨s, U', J, Q, hs, hsa, hU', ha', hQ, ?_, hprops⟩
  rwa [hbase]

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1_H2_R1_H1_R1
