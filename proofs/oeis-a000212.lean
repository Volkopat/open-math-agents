import OMAStatements.S_oeis_a000212

namespace OMA.OeisA000212

open OMA.S_oeis_a000212

lemma fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

/-!
## 1. Standard triangle and affine invariance
-/

def stdVerts : Fin 3 → ℝ × ℝ
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (0, 1)

def stdTri : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}

lemma stdTri_open : IsOpen stdTri := by
  have h1 : IsOpen {p : ℝ × ℝ | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have h2 : IsOpen {p : ℝ × ℝ | 0 < p.2} := isOpen_lt continuous_const continuous_snd
  have h3 : IsOpen {p : ℝ × ℝ | p.1 + p.2 < 1} :=
    isOpen_lt (continuous_fst.add continuous_snd) continuous_const
  exact h1.inter (h2.inter h3)

lemma stdTri_convex : Convex ℝ stdTri := by
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨hp1, hp2, hp3⟩
  rcases hq with ⟨hq1, hq2, hq3⟩
  refine ⟨?_, ?_, ?_⟩
  · change 0 < a * p.1 + b * q.1
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp only [zero_mul, zero_add]
      have hb1 : b = 1 := by linarith
      rw [hb1, one_mul]; exact hq1
    · nlinarith
  · change 0 < a * p.2 + b * q.2
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp only [zero_mul, zero_add]
      have hb1 : b = 1 := by linarith
      rw [hb1, one_mul]; exact hq2
    · nlinarith
  · change (a * p.1 + b * q.1) + (a * p.2 + b * q.2) < 1
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      rw [hb1]; linarith
    · nlinarith

lemma convexHull_stdVerts :
    convexHull ℝ (Set.range stdVerts) = {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ ?_
    · rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [stdVerts]
    · intro p hp q hq a b ha hb hab
      rcases hp with ⟨hp1, hp2, hp3⟩
      rcases hq with ⟨hq1, hq2, hq3⟩
      refine ⟨?_, ?_, ?_⟩
      · change 0 ≤ a * p.1 + b * q.1; nlinarith
      · change 0 ≤ a * p.2 + b * q.2; nlinarith
      · change (a * p.1 + b * q.1) + (a * p.2 + b * q.2) ≤ 1; nlinarith
  · rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    have h0 : ((0 : ℝ), (0 : ℝ)) ∈ convexHull ℝ (Set.range stdVerts) :=
      subset_convexHull ℝ _ ⟨0, rfl⟩
    have h1 : ((1 : ℝ), (0 : ℝ)) ∈ convexHull ℝ (Set.range stdVerts) :=
      subset_convexHull ℝ _ ⟨1, rfl⟩
    have h2 : ((0 : ℝ), (1 : ℝ)) ∈ convexHull ℝ (Set.range stdVerts) :=
      subset_convexHull ℝ _ ⟨2, rfl⟩
    rcases eq_or_lt_of_le (add_nonneg hx hy) with hs0 | hspos
    · have hx0 : x = 0 := by linarith
      have hy0 : y = 0 := by linarith
      subst hx0; subst hy0; exact h0
    · set s := x + y
      have hq : (x / s, y / s) ∈ convexHull ℝ (Set.range stdVerts) := by
        have hcomb := (convex_convexHull ℝ (Set.range stdVerts)) h1 h2
          (div_nonneg hx hspos.le) (div_nonneg hy hspos.le)
          (by field_simp [hspos.ne']; ring)
        convert hcomb using 1
        ext <;> simp
      have hp := (convex_convexHull ℝ (Set.range stdVerts)) h0 hq
        (by linarith : 0 ≤ 1 - s) hspos.le (by ring)
      convert hp using 1
      ext
      · change x = (1 - s) * 0 + s * (x / s); field_simp [hspos.ne']; ring
      · change y = (1 - s) * 0 + s * (y / s); field_simp [hspos.ne']; ring

lemma triangleInterior_stdVerts : triangleInterior stdVerts = stdTri := by
  unfold triangleInterior
  rw [convexHull_stdVerts]
  apply Set.Subset.antisymm
  · intro p hp
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hp
    obtain ⟨ε, hε, hball⟩ := hp
    have hq1 : (p.1 - ε / 2, p.2) ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      have h1 : |p.1 - ε / 2 - p.1| = ε / 2 := by
        rw [show p.1 - ε / 2 - p.1 = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]
      have h2 : |p.2 - p.2| = 0 := by simp
      rw [h1, h2, max_eq_left (by linarith)]
      linarith
    have hq2 : (p.1, p.2 - ε / 2) ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      have h1 : |p.1 - p.1| = 0 := by simp
      have h2 : |p.2 - ε / 2 - p.2| = ε / 2 := by
        rw [show p.2 - ε / 2 - p.2 = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]
      rw [h1, h2, max_eq_right (by linarith)]
      linarith
    have hq3 : (p.1 + ε / 2, p.2 + ε / 2) ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      have h1 : |p.1 + ε / 2 - p.1| = ε / 2 := by
        rw [show p.1 + ε / 2 - p.1 = ε / 2 by ring, abs_of_pos (by linarith)]
      have h2 : |p.2 + ε / 2 - p.2| = ε / 2 := by
        rw [show p.2 + ε / 2 - p.2 = ε / 2 by ring, abs_of_pos (by linarith)]
      rw [h1, h2, max_self]
      linarith
    have m1 := hball hq1
    have m2 := hball hq2
    have m3 := hball hq3
    simp only [Set.mem_setOf_eq] at m1 m2 m3
    exact ⟨by linarith, by linarith, by linarith⟩
  · refine stdTri_open.subset_interior_iff.mpr ?_
    rintro p ⟨h1, h2, h3⟩
    exact ⟨h1.le, h2.le, h3.le⟩

lemma det_ne_zero_of_affineIndependent {v : Fin 3 → ℝ × ℝ}
    (hv : AffineIndependent ℝ v) :
    (v 1 - v 0).1 * (v 2 - v 0).2 - (v 1 - v 0).2 * (v 2 - v 0).1 ≠ 0 := by
  set w₁ := v 1 - v 0
  set w₂ := v 2 - v 0
  intro hdet
  have hw1 : w₁ ≠ 0 := by
    intro h0
    have heq : v 1 = v 0 := sub_eq_zero.mp h0
    have := hv.injective heq
    exact absurd this (by decide)
  have hex : ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a • w₁ + b • w₂ = 0 := by
    by_cases h1 : w₁.1 ≠ 0
    · refine ⟨w₂.1, -w₁.1, Or.inr (neg_ne_zero.mpr h1), ?_⟩
      ext
      · change w₂.1 * w₁.1 + -w₁.1 * w₂.1 = 0; ring
      · change w₂.1 * w₁.2 + -w₁.1 * w₂.2 = 0; linarith
    · push_neg at h1
      have h2 : w₁.2 ≠ 0 := by
        intro h2
        apply hw1; ext <;> assumption
      refine ⟨w₂.2, -w₁.2, Or.inr (neg_ne_zero.mpr h2), ?_⟩
      ext
      · change w₂.2 * w₁.1 + -w₁.2 * w₂.1 = 0; linarith
      · change w₂.2 * w₁.2 + -w₁.2 * w₂.2 = 0; ring
  obtain ⟨a, b, hab, hcomb⟩ := hex
  let w : Fin 3 → ℝ := ![-(a + b), a, b]
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin 3)), w i = 0 := by
    rw [Fin.sum_univ_three]
    simp [w]
  have hwv : (Finset.univ : Finset (Fin 3)).weightedVSub v w = 0 := by
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hsum (v 0)]
    rw [Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]
    simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      vsub_self, smul_zero, zero_add]
    exact hcomb
  have hzero := hv Finset.univ w hsum hwv
  have ha0 : a = 0 := by simpa [w] using hzero 1 (Finset.mem_univ _)
  have hb0 : b = 0 := by simpa [w] using hzero 2 (Finset.mem_univ _)
  rcases hab with ha | hb
  · exact ha ha0
  · exact hb hb0

noncomputable def stdAffineEquiv {v : Fin 3 → ℝ × ℝ} (hv : AffineIndependent ℝ v) :
    (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ) := by
  let w₁ := v 1 - v 0
  let w₂ := v 2 - v 0
  let det := w₁.1 * w₂.2 - w₁.2 * w₂.1
  have hdet : det ≠ 0 := det_ne_zero_of_affineIndependent hv
  let lin : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun p => (p.1 * w₁.1 + p.2 * w₂.1, p.1 * w₁.2 + p.2 * w₂.2)
      invFun := fun q => ((q.1 * w₂.2 - q.2 * w₂.1) / det, (-q.1 * w₁.2 + q.2 * w₁.1) / det)
      map_add' := fun p q => by ext <;> simp <;> ring
      map_smul' := fun r p => by ext <;> simp <;> ring
      left_inv := fun p => by
        ext
        · change ((p.1 * w₁.1 + p.2 * w₂.1) * w₂.2 - (p.1 * w₁.2 + p.2 * w₂.2) * w₂.1) / det = p.1
          rw [div_eq_iff hdet]; dsimp only [det]; ring
        · change (-(p.1 * w₁.1 + p.2 * w₂.1) * w₁.2 + (p.1 * w₁.2 + p.2 * w₂.2) * w₁.1) / det = p.2
          rw [div_eq_iff hdet]; dsimp only [det]; ring
      right_inv := fun q => by
        ext
        · change ((q.1 * w₂.2 - q.2 * w₂.1) / det) * w₁.1 +
              ((-q.1 * w₁.2 + q.2 * w₁.1) / det) * w₂.1 = q.1
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdet]
          dsimp only [det]; ring
        · change ((q.1 * w₂.2 - q.2 * w₂.1) / det) * w₁.2 +
              ((-q.1 * w₁.2 + q.2 * w₁.1) / det) * w₂.2 = q.2
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdet]
          dsimp only [det]; ring }
  exact lin.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (ℝ × ℝ) (v 0))

lemma stdAffineEquiv_stdVerts {v : Fin 3 → ℝ × ℝ} (hv : AffineIndependent ℝ v) (i : Fin 3) :
    stdAffineEquiv hv (stdVerts i) = v i := by
  fin_cases i <;> ext <;> simp [stdAffineEquiv, stdVerts]

noncomputable def stdHomeomorph {v : Fin 3 → ℝ × ℝ} (hv : AffineIndependent ℝ v) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  { toEquiv := (stdAffineEquiv hv).toEquiv
    continuous_toFun := by
      change Continuous (fun p : ℝ × ℝ =>
        ((v 0).1 + (p.1 * (v 1 - v 0).1 + p.2 * (v 2 - v 0).1),
         (v 0).2 + (p.1 * (v 1 - v 0).2 + p.2 * (v 2 - v 0).2)))
      fun_prop
    continuous_invFun := by
      let w₁ := v 1 - v 0
      let w₂ := v 2 - v 0
      let det := w₁.1 * w₂.2 - w₁.2 * w₂.1
      change Continuous (fun q : ℝ × ℝ =>
        (((-v 0 + q).1 * w₂.2 - (-v 0 + q).2 * w₂.1) / det,
         (-(-v 0 + q).1 * w₁.2 + (-v 0 + q).2 * w₁.1) / det))
      fun_prop }

lemma affineEquiv_apply_comb (e : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ)) (a b : ℝ × ℝ) {u v : ℝ} (huv : u + v = 1) :
    e (u • a + v • b) = u • e a + v • e b := by
  have hu : u = 1 - v := by linarith
  have h1 : u • a + v • b = AffineMap.lineMap a b v := by
    rw [AffineMap.lineMap_apply_module, hu]
  have h2 : u • e a + v • e b = AffineMap.lineMap (e a) (e b) v := by
    rw [AffineMap.lineMap_apply_module, hu]
  rw [h1, h2]
  exact e.toAffineMap.apply_lineMap a b v

lemma affineEquiv_image_openSegment (e : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ)) (a b : ℝ × ℝ) :
    e '' openSegment ℝ a b = openSegment ℝ (e a) (e b) := by
  ext y
  constructor
  · rintro ⟨x, ⟨u, v, hu, hv, huv, rfl⟩, rfl⟩
    exact ⟨u, v, hu, hv, huv, (affineEquiv_apply_comb e a b huv).symm⟩
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    exact ⟨u • a + v • b, ⟨u, v, hu, hv, huv, rfl⟩, affineEquiv_apply_comb e a b huv⟩

lemma affineEquiv_image_segment (e : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ)) (a b : ℝ × ℝ) :
    e '' segment ℝ a b = segment ℝ (e a) (e b) := by
  ext y
  constructor
  · rintro ⟨x, ⟨u, v, hu, hv, huv, rfl⟩, rfl⟩
    exact ⟨u, v, hu, hv, huv, (affineEquiv_apply_comb e a b huv).symm⟩
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    exact ⟨u • a + v • b, ⟨u, v, hu, hv, huv, rfl⟩, affineEquiv_apply_comb e a b huv⟩

noncomputable def mapCevian {v : Fin 3 → ℝ × ℝ} (hv : AffineIndependent ℝ v)
    (c : Cevian stdVerts) : Cevian v where
  vertex := c.vertex
  endpoint := stdAffineEquiv hv c.endpoint
  endpoint_mem := by
    rw [← stdAffineEquiv_stdVerts hv (c.vertex + 1), ← stdAffineEquiv_stdVerts hv (c.vertex + 2),
      ← affineEquiv_image_openSegment]
    exact ⟨c.endpoint, c.endpoint_mem, rfl⟩

noncomputable def unmapCevian {v : Fin 3 → ℝ × ℝ} (hv : AffineIndependent ℝ v)
    (c : Cevian v) : Cevian stdVerts where
  vertex := c.vertex
  endpoint := (stdAffineEquiv hv).symm c.endpoint
  endpoint_mem := by
    have h1 : stdVerts (c.vertex + 1) = (stdAffineEquiv hv).symm (v (c.vertex + 1)) := by
      rw [← stdAffineEquiv_stdVerts hv (c.vertex + 1), AffineEquiv.symm_apply_apply]
    have h2 : stdVerts (c.vertex + 2) = (stdAffineEquiv hv).symm (v (c.vertex + 2)) := by
      rw [← stdAffineEquiv_stdVerts hv (c.vertex + 2), AffineEquiv.symm_apply_apply]
    rw [h1, h2, ← affineEquiv_image_openSegment]
    exact ⟨c.endpoint, c.endpoint_mem, rfl⟩

noncomputable def cevianEquiv {v : Fin 3 → ℝ × ℝ} (hv : AffineIndependent ℝ v) :
    Cevian stdVerts ≃ Cevian v where
  toFun := mapCevian hv
  invFun := unmapCevian hv
  left_inv c := by cases c; simp [mapCevian, unmapCevian]
  right_inv c := by cases c; simp [mapCevian, unmapCevian]

lemma mapCevian_points {v : Fin 3 → ℝ × ℝ} (hv : AffineIndependent ℝ v) (c : Cevian stdVerts) :
    (mapCevian hv c).points = stdAffineEquiv hv '' c.points := by
  unfold Cevian.points mapCevian
  simp only
  rw [← stdAffineEquiv_stdVerts hv c.vertex, affineEquiv_image_segment]

lemma triangleInterior_image {v : Fin 3 → ℝ × ℝ} (hv : AffineIndependent ℝ v) :
    triangleInterior v = stdAffineEquiv hv '' stdTri := by
  rw [← triangleInterior_stdVerts]
  unfold triangleInterior
  have hrange : Set.range v = (stdAffineEquiv hv).toAffineMap '' Set.range stdVerts := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨stdVerts i, ⟨i, rfl⟩, stdAffineEquiv_stdVerts hv i⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (stdAffineEquiv_stdVerts hv i).symm⟩
  rw [hrange, ← AffineMap.image_convexHull (stdAffineEquiv hv).toAffineMap]
  exact ((stdHomeomorph hv).image_interior _).symm

def homeomorph_connectedComponents {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := Quotient.lift (fun x => ConnectedComponents.mk (h x))
    (fun x₁ x₂ hxy => by
      have hconn : IsPreconnected (h '' connectedComponent x₁) :=
        isConnected_connectedComponent.isPreconnected.image h h.continuous.continuousOn
      have hmem : h x₂ ∈ connectedComponent (h x₁) :=
        hconn.subset_connectedComponent (Set.mem_image_of_mem h mem_connectedComponent)
          (Set.mem_image_of_mem h (hxy ▸ mem_connectedComponent))
      exact Quotient.sound (connectedComponent_eq hmem))
  invFun := Quotient.lift (fun y => ConnectedComponents.mk (h.symm y))
    (fun y₁ y₂ hy => by
      have hconn : IsPreconnected (h.symm '' connectedComponent y₁) :=
        isConnected_connectedComponent.isPreconnected.image h.symm h.symm.continuous.continuousOn
      have hmem : h.symm y₂ ∈ connectedComponent (h.symm y₁) :=
        hconn.subset_connectedComponent (Set.mem_image_of_mem h.symm mem_connectedComponent)
          (Set.mem_image_of_mem h.symm (hy ▸ mem_connectedComponent))
      exact Quotient.sound (connectedComponent_eq hmem))
  left_inv c := Quotient.inductionOn c fun x => by
    change ConnectedComponents.mk (h.symm (h x)) = ConnectedComponents.mk x
    simp
  right_inv c := Quotient.inductionOn c fun y => by
    change ConnectedComponents.mk (h (h.symm y)) = ConnectedComponents.mk y
    simp

lemma regionCount_mapCevian {v : Fin 3 → ℝ × ℝ} (hv : AffineIndependent ℝ v) {n : ℕ}
    (c : Fin n → Cevian stdVerts) :
    regionCount (fun i => mapCevian hv (c i)) = regionCount c := by
  unfold regionCount
  have hset : triangleInterior v \ ⋃ i, (mapCevian hv (c i)).points =
      stdHomeomorph hv '' (triangleInterior stdVerts \ ⋃ i, (c i).points) := by
    rw [triangleInterior_image hv, triangleInterior_stdVerts]
    have hfun : (stdHomeomorph hv : ℝ × ℝ → ℝ × ℝ) = stdAffineEquiv hv := rfl
    rw [hfun, Set.image_diff (stdAffineEquiv hv).injective, Set.image_iUnion]
    congr 1
    ext p
    simp only [Set.mem_iUnion, mapCevian_points]
  have hhomeo : ↥(triangleInterior stdVerts \ ⋃ i, (c i).points) ≃ₜ
      ↥(triangleInterior v \ ⋃ i, (mapCevian hv (c i)).points) := by
    let e1 := (stdHomeomorph hv).image (triangleInterior stdVerts \ ⋃ i, (c i).points)
    exact e1.trans (Homeomorph.setCongr hset.symm)
  exact ENat.card_congr (homeomorph_connectedComponents hhomeo.symm)

lemma crossingCount_mapCevian {v : Fin 3 → ℝ × ℝ} (hv : AffineIndependent ℝ v) {n : ℕ}
    (c : Fin n → Cevian stdVerts) :
    crossingCount (fun i => mapCevian hv (c i)) = crossingCount c := by
  unfold crossingCount
  have hset :
      {p ∈ triangleInterior v |
        ∃ i j : Fin n, i ≠ j ∧ p ∈ (mapCevian hv (c i)).points ∧ p ∈ (mapCevian hv (c j)).points} =
      stdAffineEquiv hv '' {p ∈ triangleInterior stdVerts |
        ∃ i j : Fin n, i ≠ j ∧ p ∈ (c i).points ∧ p ∈ (c j).points} := by
    ext q
    rw [triangleInterior_image hv, triangleInterior_stdVerts]
    simp only [Set.mem_setOf_eq, Set.mem_image, mapCevian_points]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, i, j, hij, ⟨p1, hp1, h1⟩, ⟨p2, hp2, h2⟩⟩
      have heq1 : p1 = p := (stdAffineEquiv hv).injective h1
      have heq2 : p2 = p := (stdAffineEquiv hv).injective h2
      exact ⟨p, ⟨hp, i, j, hij, heq1 ▸ hp1, heq2 ▸ hp2⟩, rfl⟩
    · rintro ⟨p, ⟨hp, i, j, hij, hp1, hp2⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, i, j, hij, ⟨p, hp1, rfl⟩, ⟨p, hp2, rfl⟩⟩
  rw [hset]
  exact (stdAffineEquiv hv).injective.encard_image _

/-!
## 2. Coordinates, line equations, and pairwise intersections on the standard triangle
-/

def param (c : Cevian stdVerts) : ℝ :=
  match c.vertex with
  | 0 => c.endpoint.2
  | 1 => c.endpoint.2
  | 2 => c.endpoint.1

lemma param_spec (c : Cevian stdVerts) :
    0 < param c ∧ param c < 1 ∧
      c.endpoint = match c.vertex with
        | 0 => (1 - param c, param c)
        | 1 => (0, param c)
        | 2 => (param c, 0) := by
  obtain ⟨u, v, hu, hv, huv, hpt⟩ := c.endpoint_mem
  have hv_cases : c.vertex = 0 ∨ c.vertex = 1 ∨ c.vertex = 2 := fin3_cases c.vertex
  rcases hv_cases with h | h | h
  · rw [h] at hpt
    have hpt' : ((u : ℝ), (v : ℝ)) = c.endpoint := by
      simpa [stdVerts] using hpt
    have h1 : c.endpoint.1 = u := congrArg Prod.fst hpt'.symm
    have h2 : c.endpoint.2 = v := congrArg Prod.snd hpt'.symm
    have hp : param c = v := by simp [param, h, h2]
    rw [h, hp]
    refine ⟨hv, by linarith, ?_⟩
    ext
    · simp [h1]; linarith
    · simp [h2]
  · rw [h] at hpt
    have hpt' : ((0 : ℝ), (u : ℝ)) = c.endpoint := by
      simpa [stdVerts] using hpt
    have h1 : c.endpoint.1 = 0 := congrArg Prod.fst hpt'.symm
    have h2 : c.endpoint.2 = u := congrArg Prod.snd hpt'.symm
    have hp : param c = u := by simp [param, h, h2]
    rw [h, hp]
    refine ⟨hu, by linarith, ?_⟩
    ext
    · simp [h1]
    · simp [h2]
  · rw [h] at hpt
    have hpt' : ((v : ℝ), (0 : ℝ)) = c.endpoint := by
      simpa [stdVerts] using hpt
    have h1 : c.endpoint.1 = v := congrArg Prod.fst hpt'.symm
    have h2 : c.endpoint.2 = 0 := congrArg Prod.snd hpt'.symm
    have hp : param c = v := by simp [param, h, h1]
    rw [h, hp]
    refine ⟨hv, by linarith, ?_⟩
    ext
    · simp [h1]
    · simp [h2]

lemma cevian_ext {c₁ c₂ : Cevian stdVerts}
    (hv : c₁.vertex = c₂.vertex) (hp : param c₁ = param c₂) : c₁ = c₂ := by
  have h1 := (param_spec c₁).2.2
  have h2 := (param_spec c₂).2.2
  have hend : c₁.endpoint = c₂.endpoint := by
    rw [h1, h2, hv, hp]
  cases c₁; cases c₂
  simp only at hv hend
  subst hv; subst hend; rfl

def mkStdCevian (v : Fin 3) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : Cevian stdVerts where
  vertex := v
  endpoint := match v with
    | 0 => (1 - t, t)
    | 1 => (0, t)
    | 2 => (t, 0)
  endpoint_mem := by
    fin_cases v
    · refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
      ext <;> simp [stdVerts]
    · refine ⟨t, 1 - t, ht0, by linarith, by ring, ?_⟩
      ext <;> simp [stdVerts]
    · refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
      ext <;> simp [stdVerts]

lemma mkStdCevian_param (v : Fin 3) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    param (mkStdCevian v t ht0 ht1) = t := by
  fin_cases v <;> rfl

def cevianFunc (c : Cevian stdVerts) (p : ℝ × ℝ) : ℝ :=
  match c.vertex with
  | 0 => param c * p.1 - (1 - param c) * p.2
  | 1 => param c * (1 - p.1) - p.2
  | 2 => param c * (1 - p.2) - p.1

lemma cevianFunc_affine (c : Cevian stdVerts) (p q : ℝ × ℝ) (s : ℝ) :
    cevianFunc c ((1 - s) • p + s • q) = (1 - s) * cevianFunc c p + s * cevianFunc c q := by
  unfold cevianFunc
  cases c.vertex using Fin.cases with
  | zero => simp; ring
  | succ i =>
    cases i using Fin.cases with
    | zero => simp; ring
    | succ j =>
      cases j using Fin.cases with
      | zero => simp; ring
      | succ k => exact Fin.elim0 k

lemma cevianFunc_continuous (c : Cevian stdVerts) : Continuous (cevianFunc c) := by
  unfold cevianFunc
  cases c.vertex using Fin.cases with
  | zero => fun_prop
  | succ i =>
    cases i using Fin.cases with
    | zero => fun_prop
    | succ j =>
      cases j using Fin.cases with
      | zero => fun_prop
      | succ k => exact Fin.elim0 k

lemma cevianFunc_dir (c : Cevian stdVerts) :
    ∃ v : ℝ × ℝ, ∀ p (ε : ℝ), cevianFunc c (p + ε • v) = cevianFunc c p + ε := by
  unfold cevianFunc
  cases c.vertex using Fin.cases with
  | zero => refine ⟨(1, -1), fun p ε => ?_⟩; simp; ring
  | succ i =>
    cases i using Fin.cases with
    | zero => refine ⟨(0, -1), fun p ε => ?_⟩; simp; ring
    | succ j =>
      cases j using Fin.cases with
      | zero => refine ⟨(-1, 0), fun p ε => ?_⟩; simp; ring
      | succ k => exact Fin.elim0 k

def cevianRay (c : Cevian stdVerts) (s : ℝ) : ℝ × ℝ :=
  (1 - s) • stdVerts c.vertex + s • c.endpoint

def rayParam (c : Cevian stdVerts) (p : ℝ × ℝ) : ℝ :=
  match c.vertex with
  | 0 => p.1 + p.2
  | 1 => 1 - p.1
  | 2 => 1 - p.2

lemma cevianRay_mem_stdTri (c : Cevian stdVerts) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    cevianRay c s ∈ stdTri ∧ cevianFunc c (cevianRay c s) = 0 := by
  obtain ⟨ht0, ht1, hend⟩ := param_spec c
  have hv : c.vertex = 0 ∨ c.vertex = 1 ∨ c.vertex = 2 := fin3_cases c.vertex
  rcases hv with h | h | h
  · rw [cevianRay, cevianFunc, hend, h]
    simp only [stdVerts, Prod.smul_mk, smul_eq_mul, mul_zero, Prod.mk_add_mk, zero_add]
    refine ⟨⟨by nlinarith, by nlinarith, by nlinarith⟩, by ring⟩
  · rw [cevianRay, cevianFunc, hend, h]
    simp only [stdVerts, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add]
    refine ⟨⟨by linarith, by nlinarith, by nlinarith⟩, by ring⟩
  · rw [cevianRay, cevianFunc, hend, h]
    simp only [stdVerts, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add]
    refine ⟨⟨by nlinarith, by linarith, by nlinarith⟩, by ring⟩

lemma rayParam_cevianRay (c : Cevian stdVerts) (s : ℝ) :
    rayParam c (cevianRay c s) = s := by
  obtain ⟨_, _, hend⟩ := param_spec c
  have hv : c.vertex = 0 ∨ c.vertex = 1 ∨ c.vertex = 2 := fin3_cases c.vertex
  rcases hv with h | h | h
  · rw [rayParam, cevianRay, hend, h]; simp [stdVerts]; ring
  · rw [rayParam, cevianRay, hend, h]; simp [stdVerts]
  · rw [rayParam, cevianRay, hend, h]; simp [stdVerts]

lemma cevianRay_injective (c : Cevian stdVerts) : Function.Injective (cevianRay c) := by
  intro s₁ s₂ h
  have := congrArg (rayParam c) h
  simpa [rayParam_cevianRay] using this

lemma cevianRay_rayParam {c : Cevian stdVerts} {p : ℝ × ℝ}
    (hp : p ∈ stdTri) (h0 : cevianFunc c p = 0) :
    0 < rayParam c p ∧ rayParam c p < 1 ∧ cevianRay c (rayParam c p) = p := by
  obtain ⟨_, _, hend⟩ := param_spec c
  rcases hp with ⟨hp1, hp2, hp3⟩
  have hv : c.vertex = 0 ∨ c.vertex = 1 ∨ c.vertex = 2 := fin3_cases c.vertex
  rcases hv with h | h | h
  · rw [cevianFunc, h] at h0
    rw [rayParam, cevianRay, hend, h]
    refine ⟨by linarith, by linarith, ?_⟩
    ext <;> simp [stdVerts] <;> linarith
  · rw [cevianFunc, h] at h0
    rw [rayParam, cevianRay, hend, h]
    refine ⟨by linarith, by linarith, ?_⟩
    ext <;> simp [stdVerts] <;> linarith
  · rw [cevianFunc, h] at h0
    rw [rayParam, cevianRay, hend, h]
    refine ⟨by linarith, by linarith, ?_⟩
    ext <;> simp [stdVerts] <;> linarith

lemma mem_points_iff_func_zero {c : Cevian stdVerts} {p : ℝ × ℝ} (hp : p ∈ stdTri) :
    p ∈ c.points ↔ cevianFunc c p = 0 := by
  constructor
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    have hu' : u = 1 - v := by linarith
    rw [hu']
    have h1 : (1 - v) • stdVerts c.vertex + v • c.endpoint = cevianRay c v := rfl
    rw [h1]
    obtain ⟨_, _, hend⟩ := param_spec c
    have hvc : c.vertex = 0 ∨ c.vertex = 1 ∨ c.vertex = 2 := fin3_cases c.vertex
    rcases hvc with h | h | h <;> (rw [cevianFunc, cevianRay, hend, h]; simp [stdVerts]; ring)
  · intro h0
    obtain ⟨hs0, hs1, hray⟩ := cevianRay_rayParam hp h0
    refine ⟨1 - rayParam c p, rayParam c p, by linarith, hs0.le, by ring, hray⟩

lemma same_vertex_disjoint {c₁ c₂ : Cevian stdVerts}
    (hv : c₁.vertex = c₂.vertex) (hne : c₁ ≠ c₂) {p : ℝ × ℝ} (hp : p ∈ stdTri) :
    ¬ (p ∈ c₁.points ∧ p ∈ c₂.points) := by
  rintro ⟨h1, h2⟩
  rw [mem_points_iff_func_zero hp] at h1 h2
  have hne_p : param c₁ ≠ param c₂ := fun heq => hne (cevian_ext hv heq)
  rcases hp with ⟨hp1, hp2, hp3⟩
  have hvc : c₁.vertex = 0 ∨ c₁.vertex = 1 ∨ c₁.vertex = 2 := fin3_cases c₁.vertex
  rcases hvc with h | h | h
  · have h' : c₂.vertex = 0 := hv.symm.trans h
    rw [cevianFunc, h] at h1; rw [cevianFunc, h'] at h2
    have : (param c₁ - param c₂) * (p.1 + p.2) = 0 := by linarith
    rcases mul_eq_zero.mp this with ha | hb
    · exact hne_p (sub_eq_zero.mp ha)
    · linarith
  · have h' : c₂.vertex = 1 := hv.symm.trans h
    rw [cevianFunc, h] at h1; rw [cevianFunc, h'] at h2
    have : (param c₁ - param c₂) * (1 - p.1) = 0 := by linarith
    rcases mul_eq_zero.mp this with ha | hb
    · exact hne_p (sub_eq_zero.mp ha)
    · linarith
  · have h' : c₂.vertex = 2 := hv.symm.trans h
    rw [cevianFunc, h] at h1; rw [cevianFunc, h'] at h2
    have : (param c₁ - param c₂) * (1 - p.2) = 0 := by linarith
    rcases mul_eq_zero.mp this with ha | hb
    · exact hne_p (sub_eq_zero.mp ha)
    · linarith

lemma diff_vertex_unique_inter_01 {c₁ c₂ : Cevian stdVerts}
    (h1 : c₁.vertex = 0) (h2 : c₂.vertex = 1) :
    ∃! p : ℝ × ℝ, p ∈ stdTri ∧ p ∈ c₁.points ∧ p ∈ c₂.points := by
  set a := param c₁
  set b := param c₂
  obtain ⟨ha0, ha1, _⟩ := param_spec c₁
  obtain ⟨hb0, hb1, _⟩ := param_spec c₂
  set D := a + (1 - a) * b
  have hD : 0 < D := by nlinarith
  refine ⟨((1 - a) * b / D, a * b / D), ?_, ?_⟩
  · have htri : ((1 - a) * b / D, a * b / D) ∈ stdTri := by
      refine ⟨div_pos (by nlinarith) hD, div_pos (by nlinarith) hD, ?_⟩
      rw [← add_div, div_lt_one hD]
      dsimp only [D]; nlinarith
    refine ⟨htri, (mem_points_iff_func_zero htri).mpr ?_, (mem_points_iff_func_zero htri).mpr ?_⟩
    · rw [cevianFunc, h1]; field_simp [hD.ne']; dsimp only [a, b, D]; ring
    · rw [cevianFunc, h2]; field_simp [hD.ne']; dsimp only [a, b, D]; ring
  · rintro ⟨x, y⟩ ⟨htri, hx1, hx2⟩
    rw [mem_points_iff_func_zero htri, cevianFunc, h1] at hx1
    rw [mem_points_iff_func_zero htri, cevianFunc, h2] at hx2
    ext
    · change x = (1 - a) * b / D
      rw [eq_div_iff hD.ne']
      dsimp only [a, b, D] at hx1 hx2 ⊢; nlinarith
    · change y = a * b / D
      rw [eq_div_iff hD.ne']
      dsimp only [a, b, D] at hx1 hx2 ⊢; nlinarith

lemma diff_vertex_unique_inter_02 {c₁ c₂ : Cevian stdVerts}
    (h1 : c₁.vertex = 0) (h2 : c₂.vertex = 2) :
    ∃! p : ℝ × ℝ, p ∈ stdTri ∧ p ∈ c₁.points ∧ p ∈ c₂.points := by
  set a := param c₁
  set b := param c₂
  obtain ⟨ha0, ha1, _⟩ := param_spec c₁
  obtain ⟨hb0, hb1, _⟩ := param_spec c₂
  set D := (1 - a) + a * b
  have hD : 0 < D := by nlinarith
  refine ⟨((1 - a) * b / D, a * b / D), ?_, ?_⟩
  · have htri : ((1 - a) * b / D, a * b / D) ∈ stdTri := by
      refine ⟨div_pos (by nlinarith) hD, div_pos (by nlinarith) hD, ?_⟩
      rw [← add_div, div_lt_one hD]
      dsimp only [D]; nlinarith
    refine ⟨htri, (mem_points_iff_func_zero htri).mpr ?_, (mem_points_iff_func_zero htri).mpr ?_⟩
    · rw [cevianFunc, h1]; field_simp [hD.ne']; dsimp only [a, b, D]; ring
    · rw [cevianFunc, h2]; field_simp [hD.ne']; dsimp only [a, b, D]; ring
  · rintro ⟨x, y⟩ ⟨htri, hx1, hx2⟩
    rw [mem_points_iff_func_zero htri, cevianFunc, h1] at hx1
    rw [mem_points_iff_func_zero htri, cevianFunc, h2] at hx2
    ext
    · change x = (1 - a) * b / D
      rw [eq_div_iff hD.ne']
      dsimp only [a, b, D] at hx1 hx2 ⊢; nlinarith
    · change y = a * b / D
      rw [eq_div_iff hD.ne']
      dsimp only [a, b, D] at hx1 hx2 ⊢; nlinarith

lemma diff_vertex_unique_inter_12 {c₁ c₂ : Cevian stdVerts}
    (h1 : c₁.vertex = 1) (h2 : c₂.vertex = 2) :
    ∃! p : ℝ × ℝ, p ∈ stdTri ∧ p ∈ c₁.points ∧ p ∈ c₂.points := by
  set a := param c₁
  set b := param c₂
  obtain ⟨ha0, ha1, _⟩ := param_spec c₁
  obtain ⟨hb0, hb1, _⟩ := param_spec c₂
  set D := 1 - a * b
  have hD : 0 < D := by nlinarith
  refine ⟨(b * (1 - a) / D, a * (1 - b) / D), ?_, ?_⟩
  · have htri : (b * (1 - a) / D, a * (1 - b) / D) ∈ stdTri := by
      refine ⟨div_pos (by nlinarith) hD, div_pos (by nlinarith) hD, ?_⟩
      rw [← add_div, div_lt_one hD]
      dsimp only [D]; nlinarith
    refine ⟨htri, (mem_points_iff_func_zero htri).mpr ?_, (mem_points_iff_func_zero htri).mpr ?_⟩
    · rw [cevianFunc, h1]; field_simp [hD.ne']; dsimp only [a, b, D]; ring
    · rw [cevianFunc, h2]; field_simp [hD.ne']; dsimp only [a, b, D]; ring
  · rintro ⟨x, y⟩ ⟨htri, hx1, hx2⟩
    rw [mem_points_iff_func_zero htri, cevianFunc, h1] at hx1
    rw [mem_points_iff_func_zero htri, cevianFunc, h2] at hx2
    ext
    · change x = b * (1 - a) / D
      rw [eq_div_iff hD.ne']
      dsimp only [a, b, D] at hx1 hx2 ⊢; nlinarith
    · change y = a * (1 - b) / D
      rw [eq_div_iff hD.ne']
      dsimp only [a, b, D] at hx1 hx2 ⊢; nlinarith

lemma diff_vertex_unique_inter {c₁ c₂ : Cevian stdVerts} (hv : c₁.vertex ≠ c₂.vertex) :
    ∃! p : ℝ × ℝ, p ∈ stdTri ∧ p ∈ c₁.points ∧ p ∈ c₂.points := by
  have h1 : c₁.vertex = 0 ∨ c₁.vertex = 1 ∨ c₁.vertex = 2 := fin3_cases c₁.vertex
  have h2 : c₂.vertex = 0 ∨ c₂.vertex = 1 ∨ c₂.vertex = 2 := fin3_cases c₂.vertex
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2
  · exact (hv (h1.trans h2.symm)).elim
  · exact diff_vertex_unique_inter_01 h1 h2
  · exact diff_vertex_unique_inter_02 h1 h2
  · obtain ⟨p, ⟨ht, hp2, hp1⟩, huniq⟩ := diff_vertex_unique_inter_01 h2 h1
    exact ⟨p, ⟨ht, hp1, hp2⟩, fun q ⟨hq, hq1, hq2⟩ => huniq q ⟨hq, hq2, hq1⟩⟩
  · exact (hv (h1.trans h2.symm)).elim
  · exact diff_vertex_unique_inter_12 h1 h2
  · obtain ⟨p, ⟨ht, hp2, hp1⟩, huniq⟩ := diff_vertex_unique_inter_02 h2 h1
    exact ⟨p, ⟨ht, hp1, hp2⟩, fun q ⟨hq, hq1, hq2⟩ => huniq q ⟨hq, hq2, hq1⟩⟩
  · obtain ⟨p, ⟨ht, hp2, hp1⟩, huniq⟩ := diff_vertex_unique_inter_12 h2 h1
    exact ⟨p, ⟨ht, hp1, hp2⟩, fun q ⟨hq, hq1, hq2⟩ => huniq q ⟨hq, hq2, hq1⟩⟩
  · exact (hv (h1.trans h2.symm)).elim

noncomputable def interPt (c₁ c₂ : Cevian stdVerts) : ℝ × ℝ :=
  if h : c₁.vertex ≠ c₂.vertex then (diff_vertex_unique_inter h).choose else (0, 0)

lemma interPt_spec {c₁ c₂ : Cevian stdVerts} (h : c₁.vertex ≠ c₂.vertex) :
    interPt c₁ c₂ ∈ stdTri ∧ interPt c₁ c₂ ∈ c₁.points ∧ interPt c₁ c₂ ∈ c₂.points := by
  rw [interPt, dif_pos h]
  exact (diff_vertex_unique_inter h).choose_spec.1

lemma interPt_eq_of_mem {c₁ c₂ : Cevian stdVerts} {p : ℝ × ℝ}
    (h : c₁.vertex ≠ c₂.vertex) (hp : p ∈ stdTri) (h1 : p ∈ c₁.points) (h2 : p ∈ c₂.points) :
    p = interPt c₁ c₂ := by
  rw [interPt, dif_pos h]
  exact (diff_vertex_unique_inter h).choose_spec.2 p ⟨hp, h1, h2⟩

lemma interPt_comm {c₁ c₂ : Cevian stdVerts} (h : c₁.vertex ≠ c₂.vertex) :
    interPt c₁ c₂ = interPt c₂ c₁ := by
  obtain ⟨ht, h1, h2⟩ := interPt_spec h
  exact interPt_eq_of_mem h.symm ht h2 h1

lemma cevianFunc_ray_sign_change {c d : Cevian stdVerts} (hne : c ≠ d)
    {s₁ t s₂ : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hs₁ : s₁ < t) (hs₂ : t < s₂)
    (hzero : cevianFunc d (cevianRay c t) = 0) :
    (decide (0 < cevianFunc d (cevianRay c s₁))) ≠
      (decide (0 < cevianFunc d (cevianRay c s₂))) := by
  set a := cevianFunc d c.endpoint - cevianFunc d (stdVerts c.vertex)
  have hlin : ∀ s : ℝ, cevianFunc d (cevianRay c s) = a * (s - t) := by
    intro s
    have h1 := cevianFunc_affine d (stdVerts c.vertex) c.endpoint s
    have h2 := cevianFunc_affine d (stdVerts c.vertex) c.endpoint t
    change cevianFunc d (cevianRay c s) = _ at h1
    change cevianFunc d (cevianRay c t) = _ at h2
    dsimp only [a]; linarith
  have ha : a ≠ 0 := by
    intro ha0
    have ht_mem := cevianRay_mem_stdTri c ht0 ht1
    have hmid_mem := cevianRay_mem_stdTri c (show 0 < t / 2 by linarith) (show t / 2 < 1 by linarith)
    have hdt : cevianRay c t ∈ d.points := (mem_points_iff_func_zero ht_mem.1).mpr hzero
    have hdm : cevianRay c (t / 2) ∈ d.points :=
      (mem_points_iff_func_zero hmid_mem.1).mpr (by rw [hlin, ha0, zero_mul])
    have hct : cevianRay c t ∈ c.points := (mem_points_iff_func_zero ht_mem.1).mpr ht_mem.2
    have hcm : cevianRay c (t / 2) ∈ c.points := (mem_points_iff_func_zero hmid_mem.1).mpr hmid_mem.2
    by_cases hv : c.vertex = d.vertex
    · exact same_vertex_disjoint hv hne ht_mem.1 ⟨hct, hdt⟩
    · have heq1 := interPt_eq_of_mem hv ht_mem.1 hct hdt
      have heq2 := interPt_eq_of_mem hv hmid_mem.1 hcm hdm
      have hinj := cevianRay_injective c (heq1.trans heq2.symm)
      linarith
  rw [hlin s₁, hlin s₂]
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have h1 : 0 < a * (s₁ - t) := by nlinarith
    have h2 : ¬ (0 < a * (s₂ - t)) := by nlinarith
    simp [h1, h2]
  · have h1 : ¬ (0 < a * (s₁ - t)) := by nlinarith
    have h2 : 0 < a * (s₂ - t) := by nlinarith
    simp [h1, h2]

/-!
## 3. Hyperplane arrangement regions via sign vectors
-/

def openCompl (S : Finset (Cevian stdVerts)) : Set (ℝ × ℝ) :=
  stdTri \ ⋃ c ∈ S, c.points

noncomputable def signVec (S : Finset (Cevian stdVerts)) (p : ℝ × ℝ) : S → Bool :=
  fun c => decide (0 < cevianFunc c.1 p)

noncomputable def realized (S : Finset (Cevian stdVerts)) : Finset (S → Bool) := by
  classical
  exact Finset.univ.filter (fun σ => ∃ p ∈ openCompl S, signVec S p = σ)

lemma mem_openCompl_iff {S : Finset (Cevian stdVerts)} {p : ℝ × ℝ} :
    p ∈ openCompl S ↔ p ∈ stdTri ∧ ∀ c ∈ S, cevianFunc c p ≠ 0 := by
  simp only [openCompl, Set.mem_diff, Set.mem_iUnion, not_exists]
  constructor
  · rintro ⟨hp, hno⟩
    exact ⟨hp, fun c hc h0 => hno c hc ((mem_points_iff_func_zero hp).mpr h0)⟩
  · rintro ⟨hp, hno⟩
    exact ⟨hp, fun c hc hmem => hno c hc ((mem_points_iff_func_zero hp).mp hmem)⟩

lemma signVec_fiber_open (S : Finset (Cevian stdVerts)) (σ : S → Bool) :
    IsOpen {p : ℝ × ℝ | p ∈ openCompl S ∧ signVec S p = σ} := by
  have heq : {p : ℝ × ℝ | p ∈ openCompl S ∧ signVec S p = σ} =
      stdTri ∩ ⋂ c : S, if σ c then {p | 0 < cevianFunc c.1 p} else {p | cevianFunc c.1 p < 0} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, mem_openCompl_iff]
    constructor
    · rintro ⟨⟨hp, hnz⟩, hsig⟩
      refine ⟨hp, fun c => ?_⟩
      have hsc : decide (0 < cevianFunc c.1 p) = σ c := congrFun hsig c
      cases hval : σ c
      · simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq]
        rw [hval, decide_eq_false_iff_not] at hsc
        exact lt_of_le_of_ne (not_lt.mp hsc) (hnz c.1 c.2)
      · simp only [↓reduceIte, Set.mem_setOf_eq]
        rw [hval, decide_eq_true_eq] at hsc
        exact hsc
    · rintro ⟨hp, hall⟩
      refine ⟨⟨hp, fun c hc => ?_⟩, funext fun c => ?_⟩
      · have h := hall ⟨c, hc⟩
        cases hval : σ ⟨c, hc⟩ <;> simp only [hval, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq] at h
        · exact ne_of_lt h
        · exact ne_of_gt h
      · have h := hall c
        cases hval : σ c <;> simp only [hval, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq] at h
        · simp [signVec, not_lt.mpr h.le]
        · simp [signVec, h]
  rw [heq]
  refine stdTri_open.inter (isOpen_iInter_of_finite fun c => ?_)
  cases σ c
  · exact isOpen_lt (cevianFunc_continuous c.1) continuous_const
  · exact isOpen_lt continuous_const (cevianFunc_continuous c.1)

lemma signVec_fiber_convex (S : Finset (Cevian stdVerts)) (σ : S → Bool) :
    Convex ℝ {p : ℝ × ℝ | p ∈ openCompl S ∧ signVec S p = σ} := by
  intro p ⟨hp, hsp⟩ q ⟨hq, hsq⟩ a b ha hb hab
  have hp_tri := (mem_openCompl_iff.mp hp).1
  have hq_tri := (mem_openCompl_iff.mp hq).1
  have htri : a • p + b • q ∈ stdTri := stdTri_convex hp_tri hq_tri ha hb hab
  have ha' : a = 1 - b := by linarith
  have hlin : ∀ c : S, cevianFunc c.1 (a • p + b • q) = a * cevianFunc c.1 p + b * cevianFunc c.1 q := by
    intro c
    rw [ha', cevianFunc_affine]
  have hsign : ∀ c : S,
      (σ c = true → 0 < cevianFunc c.1 (a • p + b • q)) ∧
      (σ c = false → cevianFunc c.1 (a • p + b • q) < 0) := by
    intro c
    have hp_c := congrFun hsp c
    have hq_c := congrFun hsq c
    dsimp only [signVec] at hp_c hq_c
    have hp_nz := (mem_openCompl_iff.mp hp).2 c.1 c.2
    have hq_nz := (mem_openCompl_iff.mp hq).2 c.1 c.2
    rw [hlin c]
    constructor
    · intro ht
      rw [ht, decide_eq_true_eq] at hp_c hq_c
      rcases eq_or_lt_of_le ha with rfl | ha_pos
      · have hb1 : b = 1 := by linarith
        rw [hb1]; linarith
      · nlinarith
    · intro hf
      rw [hf, decide_eq_false_iff_not] at hp_c hq_c
      have hp_lt : cevianFunc c.1 p < 0 := lt_of_le_of_ne (not_lt.mp hp_c) hp_nz
      have hq_lt : cevianFunc c.1 q < 0 := lt_of_le_of_ne (not_lt.mp hq_c) hq_nz
      rcases eq_or_lt_of_le ha with rfl | ha_pos
      · have hb1 : b = 1 := by linarith
        rw [hb1]; linarith
      · nlinarith
  refine ⟨mem_openCompl_iff.mpr ⟨htri, fun c hc => ?_⟩, funext fun c => ?_⟩
  · cases hval : σ ⟨c, hc⟩
    · exact ne_of_lt ((hsign ⟨c, hc⟩).2 hval)
    · exact ne_of_gt ((hsign ⟨c, hc⟩).1 hval)
  · cases hval : σ c
    · simp [signVec, not_lt.mpr ((hsign c).2 hval).le]
    · simp [signVec, (hsign c).1 hval]

lemma card_connectedComponents_eq (S : Finset (Cevian stdVerts)) :
    ENat.card (ConnectedComponents ↥(openCompl S)) = ((realized S).card : ℕ∞) := by
  classical
  have hclopen : ∀ σ : S → Bool,
      IsClopen {x : ↥(openCompl S) | signVec S x.1 = σ} := by
    intro σ
    refine ⟨?_, ?_⟩
    · rw [← isOpen_compl_iff]
      have hcompl : ({x : ↥(openCompl S) | signVec S x.1 = σ})ᶜ =
          ⋃ τ : {τ : S → Bool // τ ≠ σ}, {x : ↥(openCompl S) | signVec S x.1 = τ.1} := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · intro hne; exact ⟨⟨signVec S x.1, hne⟩, rfl⟩
        · rintro ⟨⟨τ, hne⟩, h⟩; exact h ▸ hne
      rw [hcompl]
      refine isOpen_iUnion fun τ => ?_
      have hsub : {x : ↥(openCompl S) | signVec S x.1 = τ.1} =
          Subtype.val ⁻¹' {p : ℝ × ℝ | p ∈ openCompl S ∧ signVec S p = τ.1} := by
        ext x; simp [x.2]
      rw [hsub]
      exact (signVec_fiber_open S τ.1).preimage continuous_subtype_val
    · have hsub : {x : ↥(openCompl S) | signVec S x.1 = σ} =
          Subtype.val ⁻¹' {p : ℝ × ℝ | p ∈ openCompl S ∧ signVec S p = σ} := by
        ext x; simp [x.2]
      rw [hsub]
      exact (signVec_fiber_open S σ).preimage continuous_subtype_val
  have hwd : ∀ x y : ↥(openCompl S),
      connectedComponent x = connectedComponent y → signVec S x.1 = signVec S y.1 := by
    intro x y hxy
    have hmem : y ∈ connectedComponent x := hxy ▸ mem_connectedComponent
    have hsub : connectedComponent x ⊆ {z : ↥(openCompl S) | signVec S z.1 = signVec S x.1} :=
      (hclopen (signVec S x.1)).connectedComponent_subset (by simp)
    exact (hsub hmem).symm
  let toFun : ConnectedComponents ↥(openCompl S) → ↥(realized S) :=
    Quotient.lift
      (fun x : ↥(openCompl S) =>
        (⟨signVec S x.1, by
          simp only [realized, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨x.1, x.2, rfl⟩⟩ : ↥(realized S)))
      (fun x y hxy => Subtype.ext (hwd x y hxy))
  have hbij : Function.Bijective toFun := by
    constructor
    · intro a b hab
      refine Quotient.inductionOn₂ a b (fun x y h => ?_) hab
      have hsig : signVec S x.1 = signVec S y.1 := congrArg Subtype.val h
      apply Quotient.sound
      change connectedComponent x = connectedComponent y
      let F : Set (ℝ × ℝ) := {p | p ∈ openCompl S ∧ signVec S p = signVec S x.1}
      have hFsub : F ⊆ openCompl S := fun p hp => hp.1
      have hFconn : IsPreconnected F := (signVec_fiber_convex S (signVec S x.1)).isPreconnected
      let F' : Set ↥(openCompl S) := Subtype.val ⁻¹' F
      have hF'conn : IsPreconnected F' := by
        rw [Topology.IsInducing.subtypeVal.isPreconnected_image.symm]
        have himg : Subtype.val '' F' = F := by
          ext p
          simp only [F', Set.mem_image, Set.mem_preimage, Subtype.exists]
          constructor
          · rintro ⟨q, _, hq, rfl⟩; exact hq
          · intro hp; exact ⟨p, hFsub hp, hp, rfl⟩
        rw [himg]; exact hFconn
      have hxF : x ∈ F' := ⟨x.2, rfl⟩
      have hyF : y ∈ F' := ⟨y.2, hsig.symm⟩
      exact connectedComponent_eq (hF'conn.subset_connectedComponent hxF hyF)
    · rintro ⟨σ, hσ⟩
      simp only [realized, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      obtain ⟨p, hp, hsig⟩ := hσ
      refine ⟨ConnectedComponents.mk ⟨p, hp⟩, Subtype.ext hsig⟩
  rw [ENat.card_congr (Equiv.ofBijective toFun hbij)]
  simp [ENat.card_eq_coe_fintype_card]

/-!
## 4. Zaslavsky insertion step
-/

noncomputable def interPts (S : Finset (Cevian stdVerts)) (c : Cevian stdVerts) : Finset (ℝ × ℝ) := by
  classical
  exact (S.filter (fun d => d.vertex ≠ c.vertex)).image (interPt c)

lemma mem_interPts_iff {S : Finset (Cevian stdVerts)} {c : Cevian stdVerts} (hc : c ∉ S) {p : ℝ × ℝ} :
    p ∈ interPts S c ↔ p ∈ stdTri ∧ p ∈ c.points ∧ ∃ d ∈ S, p ∈ d.points := by
  classical
  simp only [interPts, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨d, ⟨hdS, hdv⟩, rfl⟩
    obtain ⟨ht, hcp, hdp⟩ := interPt_spec hdv.symm
    exact ⟨ht, hcp, d, hdS, hdp⟩
  · rintro ⟨ht, hcp, d, hdS, hdp⟩
    have hne : c ≠ d := fun heq => hc (heq ▸ hdS)
    have hdv : d.vertex ≠ c.vertex := fun heq =>
      same_vertex_disjoint heq.symm hne ht ⟨hcp, hdp⟩
    exact ⟨d, ⟨hdS, hdv⟩, (interPt_eq_of_mem hdv.symm ht hcp hdp).symm⟩

noncomputable def interParams (S : Finset (Cevian stdVerts)) (c : Cevian stdVerts) : Finset ℝ := by
  classical
  exact (interPts S c).image (rayParam c)

lemma interParams_card {S : Finset (Cevian stdVerts)} {c : Cevian stdVerts} (hc : c ∉ S) :
    (interParams S c).card = (interPts S c).card := by
  classical
  unfold interParams
  refine Finset.card_image_of_injOn ?_
  intro p hp q hq heq
  have hp' := (mem_interPts_iff hc).mp hp
  have hq' := (mem_interPts_iff hc).mp hq
  have h1 := (cevianRay_rayParam hp'.1 ((mem_points_iff_func_zero hp'.1).mp hp'.2.1)).2.2
  have h2 := (cevianRay_rayParam hq'.1 ((mem_points_iff_func_zero hq'.1).mp hq'.2.1)).2.2
  rw [← h1, ← h2, heq]

lemma interParams_mem_Ioo {S : Finset (Cevian stdVerts)} {c : Cevian stdVerts} (hc : c ∉ S)
    {t : ℝ} (ht : t ∈ interParams S c) : 0 < t ∧ t < 1 := by
  classical
  rw [interParams, Finset.mem_image] at ht
  obtain ⟨p, hp, rfl⟩ := ht
  have hp' := (mem_interPts_iff hc).mp hp
  have h := cevianRay_rayParam hp'.1 ((mem_points_iff_func_zero hp'.1).mp hp'.2.1)
  exact ⟨h.1, h.2.1⟩

lemma ray_mem_openCompl_iff {S : Finset (Cevian stdVerts)} {c : Cevian stdVerts} (hc : c ∉ S)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    cevianRay c s ∈ openCompl S ↔ s ∉ interParams S c := by
  classical
  have hray := cevianRay_mem_stdTri c hs0 hs1
  have hcp : cevianRay c s ∈ c.points := (mem_points_iff_func_zero hray.1).mpr hray.2
  rw [mem_openCompl_iff]
  constructor
  · intro ⟨_, hnz⟩ hmem
    rw [interParams, Finset.mem_image] at hmem
    obtain ⟨p, hp, heq⟩ := hmem
    have hp' := (mem_interPts_iff hc).mp hp
    have hpr : cevianRay c (rayParam c p) = p :=
      (cevianRay_rayParam hp'.1 ((mem_points_iff_func_zero hp'.1).mp hp'.2.1)).2.2
    rw [heq] at hpr
    obtain ⟨d, hdS, hdp⟩ := hp'.2.2
    rw [← hpr] at hdp
    exact hnz d hdS ((mem_points_iff_func_zero hray.1).mp hdp)
  · intro hnot
    refine ⟨hray.1, fun d hdS h0 => hnot ?_⟩
    have hdp : cevianRay c s ∈ d.points := (mem_points_iff_func_zero hray.1).mpr h0
    have hp : cevianRay c s ∈ interPts S c :=
      (mem_interPts_iff hc).mpr ⟨hray.1, hcp, d, hdS, hdp⟩
    rw [interParams, Finset.mem_image]
    exact ⟨cevianRay c s, hp, rayParam_cevianRay c s⟩

lemma rank_surj_Ioo_aux : ∀ (n : ℕ) (T : Finset ℝ) (lo hi : ℝ),
    lo < hi → T.card = n → (∀ t ∈ T, lo < t ∧ t < hi) →
    ∀ k : ℕ, k ≤ n →
      ∃ s : ℝ, lo < s ∧ s < hi ∧ s ∉ T ∧ (T.filter (· < s)).card = k := by
  intro n
  induction n with
  | zero =>
    intro T lo hi hlohi hcard _ k hk
    have hT : T = ∅ := Finset.card_eq_zero.mp hcard
    have hk0 : k = 0 := by omega
    subst hT; subst hk0
    exact ⟨(lo + hi) / 2, by linarith, by linarith, by simp, by simp⟩
  | succ n ih =>
    intro T lo hi hlohi hcard hT k hk
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    set m := T.max' hne
    have hm_mem : m ∈ T := Finset.max'_mem T hne
    have hm_le : ∀ x ∈ T, x ≤ m := fun x hx => Finset.le_max' T x hx
    have hm_Ioo := hT m hm_mem
    set V := T.erase m
    have hV_card : V.card = n := by
      rw [Finset.card_erase_of_mem hm_mem, hcard]; omega
    have hV_Ioo : ∀ x ∈ V, lo < x ∧ x < m := fun x hx =>
      ⟨(hT x (Finset.mem_of_mem_erase hx)).1,
       lt_of_le_of_ne (hm_le x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)⟩
    by_cases hkn : k = n + 1
    · subst hkn
      refine ⟨(m + hi) / 2, by linarith, by linarith, ?_, ?_⟩
      · intro hmem
        have := hm_le ((m + hi) / 2) hmem
        linarith
      · have hfilt : T.filter (· < (m + hi) / 2) = T := by
          apply Finset.filter_true_of_mem
          intro x hx
          have := hm_le x hx
          linarith
        rw [hfilt, hcard]
    · have hkle : k ≤ n := by omega
      obtain ⟨s, hsl, hsm, hsnotV, hscard⟩ := ih V lo m hm_Ioo.1 hV_card hV_Ioo k hkle
      refine ⟨s, hsl, lt_trans hsm hm_Ioo.2, ?_, ?_⟩
      · intro hsT
        by_cases heq : s = m
        · linarith
        · exact hsnotV (Finset.mem_erase.mpr ⟨heq, hsT⟩)
      · have hfilt : T.filter (· < s) = V.filter (· < s) := by
          ext x
          simp only [Finset.mem_filter, V, Finset.mem_erase]
          constructor
          · rintro ⟨hxT, hxs⟩
            exact ⟨⟨by linarith, hxT⟩, hxs⟩
          · rintro ⟨⟨_, hxT⟩, hxs⟩
            exact ⟨hxT, hxs⟩
        rw [hfilt, hscard]

noncomputable def splitSet (S : Finset (Cevian stdVerts)) (c : Cevian stdVerts) :
    Finset (S → Bool) := by
  classical
  exact (realized S).filter (fun σ =>
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ cevianRay c s ∈ openCompl S ∧ signVec S (cevianRay c s) = σ)

lemma card_splitSet_eq {S : Finset (Cevian stdVerts)} {c : Cevian stdVerts} (hc : c ∉ S) :
    (splitSet S c).card = (interPts S c).card + 1 := by
  classical
  set T := interParams S c
  have hT_Ioo : ∀ t ∈ T, 0 < t ∧ t < 1 := fun t ht => interParams_mem_Ioo hc ht
  have hT_card : T.card = (interPts S c).card := interParams_card hc
  have hex : ∀ k : Fin (T.card + 1),
      ∃ s : ℝ, 0 < s ∧ s < 1 ∧ s ∉ T ∧ (T.filter (· < s)).card = k.val :=
    fun k => rank_surj_Ioo_aux T.card T 0 1 zero_lt_one rfl hT_Ioo k.val (Nat.le_of_lt_succ k.isLt)
  choose pts hpts_pos hpts_lt hpts_notT hpts_rank using hex
  let f : Fin (T.card + 1) → (S → Bool) := fun k => signVec S (cevianRay c (pts k))
  have hf_mem : ∀ k : Fin (T.card + 1), f k ∈ splitSet S c := by
    intro k
    have hcomp : cevianRay c (pts k) ∈ openCompl S :=
      (ray_mem_openCompl_iff hc (hpts_pos k) (hpts_lt k)).mpr (hpts_notT k)
    simp only [splitSet, realized, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨cevianRay c (pts k), hcomp, rfl⟩, pts k, hpts_pos k, hpts_lt k, hcomp, rfl⟩
  have hdiff_of_between : ∀ {s₁ s₂ : ℝ},
      0 < s₁ → s₁ < 1 → 0 < s₂ → s₂ < 1 → s₁ ∉ T → s₂ ∉ T →
      (T.filter (· < s₁)).card < (T.filter (· < s₂)).card →
      signVec S (cevianRay c s₁) ≠ signVec S (cevianRay c s₂) := by
    intro s₁ s₂ hs₁0 hs₁1 hs₂0 hs₂1 hs₁T hs₂T hlt
    have hs12 : s₁ < s₂ := by
      by_contra hle
      push_neg at hle
      have hsub : T.filter (· < s₂) ⊆ T.filter (· < s₁) := by
        intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, lt_of_lt_of_le hx.2 hle⟩
      exact absurd (Finset.card_le_card hsub) (not_le_of_gt hlt)
    have hsub : T.filter (· < s₁) ⊆ T.filter (· < s₂) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, lt_trans hx.2 hs12⟩
    have hssub : T.filter (· < s₁) ⊂ T.filter (· < s₂) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => by rw [heq] at hlt; exact lt_irrefl _ hlt⟩
    obtain ⟨t, ht2, ht1⟩ := Finset.exists_of_ssubset hssub
    rw [Finset.mem_filter] at ht1 ht2
    have htT : t ∈ T := ht2.1
    have ht_lt : t < s₂ := ht2.2
    have ht_gt : s₁ < t := by
      have hge : s₁ ≤ t := not_lt.mp (fun h => ht1 ⟨htT, h⟩)
      exact lt_of_le_of_ne hge (fun heq => hs₁T (heq ▸ htT))
    have htT' : t ∈ interParams S c := htT
    rw [interParams, Finset.mem_image] at htT'
    obtain ⟨p, hp, htp⟩ := htT'
    have hp' := (mem_interPts_iff hc).mp hp
    have hray_t : cevianRay c t = p := by
      rw [← htp]
      exact (cevianRay_rayParam hp'.1 ((mem_points_iff_func_zero hp'.1).mp hp'.2.1)).2.2
    obtain ⟨d, hdS, hdp⟩ := hp'.2.2
    have hne : c ≠ d := fun heq => hc (heq ▸ hdS)
    have hzero : cevianFunc d (cevianRay c t) = 0 := by
      rw [hray_t]
      exact (mem_points_iff_func_zero hp'.1).mp hdp
    have htIoo := hT_Ioo t htT
    intro heq
    have hcon := congrFun heq ⟨d, hdS⟩
    exact cevianFunc_ray_sign_change hne htIoo.1 htIoo.2 ht_gt ht_lt hzero hcon
  have hsame_of_rank_eq : ∀ {s₁ s₂ : ℝ},
      0 < s₁ → s₁ < 1 → 0 < s₂ → s₂ < 1 → s₁ ∉ T → s₂ ∉ T →
      (T.filter (· < s₁)).card = (T.filter (· < s₂)).card →
      signVec S (cevianRay c s₁) = signVec S (cevianRay c s₂) := by
    intro s₁ s₂ hs₁0 hs₁1 hs₂0 hs₂1 hs₁T hs₂T hrank
    have hno_between : ∀ {a b : ℝ}, a < b →
        (T.filter (· < a)).card = (T.filter (· < b)).card →
        ∀ t ∈ T, ¬ (a < t ∧ t < b) := by
      intro a b hab heq t ht ⟨hat, htb⟩
      have hsub : T.filter (· < a) ⊆ T.filter (· < b) := by
        intro x hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, lt_trans hx.2 hab⟩
      have hne : T.filter (· < a) ≠ T.filter (· < b) := by
        intro h
        have hmem : t ∈ T.filter (· < a) := h ▸ Finset.mem_filter.mpr ⟨ht, htb⟩
        rw [Finset.mem_filter] at hmem
        linarith
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
      omega
    have hcomp1 : cevianRay c s₁ ∈ openCompl S := (ray_mem_openCompl_iff hc hs₁0 hs₁1).mpr hs₁T
    have hcomp2 : cevianRay c s₂ ∈ openCompl S := (ray_mem_openCompl_iff hc hs₂0 hs₂1).mpr hs₂T
    funext d
    by_contra hne
    have hnz1 : cevianFunc d.1 (cevianRay c s₁) ≠ 0 := (mem_openCompl_iff.mp hcomp1).2 d.1 d.2
    have hnz2 : cevianFunc d.1 (cevianRay c s₂) ≠ 0 := (mem_openCompl_iff.mp hcomp2).2 d.1 d.2
    have hprod : cevianFunc d.1 (cevianRay c s₁) * cevianFunc d.1 (cevianRay c s₂) < 0 := by
      by_cases h1 : 0 < cevianFunc d.1 (cevianRay c s₁)
      · have h2 : ¬ (0 < cevianFunc d.1 (cevianRay c s₂)) := by
          intro h2; apply hne; simp [signVec, h1, h2]
        have h2lt : cevianFunc d.1 (cevianRay c s₂) < 0 := lt_of_le_of_ne (not_lt.mp h2) hnz2
        nlinarith
      · have h2 : 0 < cevianFunc d.1 (cevianRay c s₂) := by
          by_contra h2; apply hne; simp [signVec, h1, h2]
        have h1lt : cevianFunc d.1 (cevianRay c s₁) < 0 := lt_of_le_of_ne (not_lt.mp h1) hnz1
        nlinarith
    set v₁ := cevianFunc d.1 (cevianRay c s₁)
    set v₂ := cevianFunc d.1 (cevianRay c s₂)
    have hdiff_nz : v₁ - v₂ ≠ 0 := by
      intro h0
      have : v₁ = v₂ := sub_eq_zero.mp h0
      rw [this] at hprod
      nlinarith [sq_nonneg v₂]
    set α := v₁ / (v₁ - v₂)
    have hα0 : 0 < α := by
      rcases lt_or_gt_of_ne hnz1 with h1 | h1
      · have h2 : 0 < v₂ := by nlinarith
        exact div_pos_of_neg_of_neg h1 (by linarith)
      · have h2 : v₂ < 0 := by nlinarith
        exact div_pos h1 (by linarith)
    have hα1 : α < 1 := by
      rcases lt_or_gt_of_ne hnz1 with h1 | h1
      · have h2 : 0 < v₂ := by nlinarith
        rw [div_lt_one_of_neg (by linarith)]; linarith
      · have h2 : v₂ < 0 := by nlinarith
        rw [div_lt_one (by linarith)]; linarith
    set t := (1 - α) * s₁ + α * s₂
    have ht0 : 0 < t := by nlinarith
    have ht1 : t < 1 := by nlinarith
    have hray_comb : cevianRay c t = (1 - α) • cevianRay c s₁ + α • cevianRay c s₂ := by
      ext <;> simp [cevianRay, t] <;> ring
    have hzero : cevianFunc d.1 (cevianRay c t) = 0 := by
      rw [hray_comb, cevianFunc_affine]
      change (1 - α) * v₁ + α * v₂ = 0
      dsimp only [α]
      field_simp [hdiff_nz]
      ring
    have htT : t ∈ T := by
      by_contra hnotT
      have hcomp := (ray_mem_openCompl_iff hc ht0 ht1).mpr hnotT
      exact (mem_openCompl_iff.mp hcomp).2 d.1 d.2 hzero
    rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
    · exact hno_between hlt hrank t htT ⟨by nlinarith, by nlinarith⟩
    · exact hne rfl
    · exact hno_between hgt hrank.symm t htT ⟨by nlinarith, by nlinarith⟩
  have hf_inj : Function.Injective f := by
    intro k₁ k₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact hdiff_of_between (hpts_pos k₁) (hpts_lt k₁) (hpts_pos k₂) (hpts_lt k₂)
        (hpts_notT k₁) (hpts_notT k₂) (by rw [hpts_rank k₁, hpts_rank k₂]; exact hlt) heq
    · exact hdiff_of_between (hpts_pos k₂) (hpts_lt k₂) (hpts_pos k₁) (hpts_lt k₁)
        (hpts_notT k₂) (hpts_notT k₁) (by rw [hpts_rank k₂, hpts_rank k₁]; exact hgt) heq.symm
  have hsplit_eq : splitSet S c = Finset.univ.image f := by
    ext σ
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hσ
      simp only [splitSet, Finset.mem_filter] at hσ
      obtain ⟨_, s, hs0, hs1, hcomp, hsig⟩ := hσ
      have hsnotT : s ∉ T := (ray_mem_openCompl_iff hc hs0 hs1).mp hcomp
      have hle : (T.filter (· < s)).card ≤ T.card := Finset.card_filter_le _ _
      let k : Fin (T.card + 1) := ⟨(T.filter (· < s)).card, Nat.lt_succ_of_le hle⟩
      refine ⟨k, ?_⟩
      rw [← hsig]
      exact hsame_of_rank_eq (hpts_pos k) (hpts_lt k) hs0 hs1 (hpts_notT k) hsnotT (hpts_rank k)
    · rintro ⟨k, rfl⟩
      exact hf_mem k
  rw [hsplit_eq, Finset.card_image_of_injective _ hf_inj, Finset.card_fin, hT_card]

open Classical in
lemma card_realized_insert {S : Finset (Cevian stdVerts)} {c : Cevian stdVerts} (hc : c ∉ S) :
    (realized (insert c S)).card = (realized S).card + (interPts S c).card + 1 := by
  classical
  let res : (↥(insert c S) → Bool) → (↥S → Bool) :=
    fun τ d => τ ⟨d.1, Finset.mem_insert_of_mem d.2⟩
  let extSign : (↥S → Bool) → Bool → (↥(insert c S) → Bool) :=
    fun σ b d => if h : d.1 ∈ S then σ ⟨d.1, h⟩ else b
  have hres_ext : ∀ σ b, res (extSign σ b) = σ := by
    intro σ b; funext d; simp [res, extSign, d.2]
  have hext_self : ∀ σ b, extSign σ b ⟨c, Finset.mem_insert_self c S⟩ = b := by
    intro σ b; simp [extSign, hc]
  have hext_res : ∀ τ, extSign (res τ) (τ ⟨c, Finset.mem_insert_self c S⟩) = τ := by
    intro τ; funext d
    by_cases h : d.1 ∈ S
    · simp [extSign, res, h]
    · have hdc : d.1 = c := by
        rcases Finset.mem_insert.mp d.2 with heq | hmem
        · exact heq
        · exact (h hmem).elim
      have hd_eq : d = ⟨c, Finset.mem_insert_self c S⟩ := Subtype.ext hdc
      rw [hd_eq]; simp [extSign, hc]
  have hne_ext : ∀ σ, extSign σ true ≠ extSign σ false := by
    intro σ heq
    have := congrFun heq ⟨c, Finset.mem_insert_self c S⟩
    simp [extSign, hc] at this
  have hres_maps : ∀ τ ∈ realized (insert c S), res τ ∈ realized S := by
    intro τ hτ
    simp only [realized, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    obtain ⟨p, hp, hsig⟩ := hτ
    have hpS : p ∈ openCompl S := by
      rw [mem_openCompl_iff] at hp ⊢
      exact ⟨hp.1, fun d hd => hp.2 d (Finset.mem_insert_of_mem hd)⟩
    refine ⟨p, hpS, ?_⟩
    rw [← hsig]; funext d; rfl
  have hboth_iff : ∀ σ ∈ realized S,
      (extSign σ true ∈ realized (insert c S) ∧ extSign σ false ∈ realized (insert c S)) ↔
        σ ∈ splitSet S c := by
    intro σ hσ
    constructor
    · rintro ⟨ht, hf⟩
      simp only [realized, Finset.mem_filter, Finset.mem_univ, true_and] at ht hf
      obtain ⟨p, hp, hsp⟩ := ht
      obtain ⟨q, hq, hsq⟩ := hf
      have hp_pos : 0 < cevianFunc c p := by
        have h := congrFun hsp ⟨c, Finset.mem_insert_self c S⟩
        rw [hext_self] at h
        exact of_decide_eq_true h
      have hq_neg : cevianFunc c q < 0 := by
        have h := congrFun hsq ⟨c, Finset.mem_insert_self c S⟩
        rw [hext_self] at h
        have hle := not_lt.mp (of_decide_eq_false h)
        exact lt_of_le_of_ne hle ((mem_openCompl_iff.mp hq).2 c (Finset.mem_insert_self c S))
      have hpS : p ∈ openCompl S ∧ signVec S p = σ := by
        refine ⟨mem_openCompl_iff.mpr ⟨(mem_openCompl_iff.mp hp).1,
          fun d hd => (mem_openCompl_iff.mp hp).2 d (Finset.mem_insert_of_mem hd)⟩, ?_⟩
        funext d
        have := congrFun hsp ⟨d.1, Finset.mem_insert_of_mem d.2⟩
        simpa [signVec, extSign, d.2] using this
      have hqS : q ∈ openCompl S ∧ signVec S q = σ := by
        refine ⟨mem_openCompl_iff.mpr ⟨(mem_openCompl_iff.mp hq).1,
          fun d hd => (mem_openCompl_iff.mp hq).2 d (Finset.mem_insert_of_mem hd)⟩, ?_⟩
        funext d
        have := congrFun hsq ⟨d.1, Finset.mem_insert_of_mem d.2⟩
        simpa [signVec, extSign, d.2] using this
      set a := cevianFunc c p / (cevianFunc c p - cevianFunc c q)
      have ha0 : 0 < a := div_pos hp_pos (by linarith)
      have ha1 : a < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      set r := (1 - a) • p + a • q
      have hrS : r ∈ openCompl S ∧ signVec S r = σ :=
        signVec_fiber_convex S σ hpS hqS (by linarith) ha0.le (by ring)
      have hr0 : cevianFunc c r = 0 := by
        rw [cevianFunc_affine]
        dsimp only [a]
        field_simp [show cevianFunc c p - cevianFunc c q ≠ 0 by linarith]
        ring
      obtain ⟨hs0, hs1, hray⟩ := cevianRay_rayParam (mem_openCompl_iff.mp hrS.1).1 hr0
      simp only [splitSet, Finset.mem_filter]
      exact ⟨hσ, rayParam c r, hs0, hs1, by rw [hray]; exact hrS.1, by rw [hray]; exact hrS.2⟩
    · intro hsplit
      simp only [splitSet, Finset.mem_filter] at hsplit
      obtain ⟨_, s, hs0, hs1, hrS, hsig⟩ := hsplit
      set r := cevianRay c s
      have hr0 : cevianFunc c r = 0 := (cevianRay_mem_stdTri c hs0 hs1).2
      have hopen := signVec_fiber_open S σ
      have hr_mem : r ∈ {p : ℝ × ℝ | p ∈ openCompl S ∧ signVec S p = σ} := ⟨hrS, hsig⟩
      rw [Metric.isOpen_iff] at hopen
      obtain ⟨δ, hδ, hball⟩ := hopen r hr_mem
      obtain ⟨v, hv⟩ := cevianFunc_dir c
      set M := max |v.1| |v.2| + 1
      have hM : 0 < M := by positivity
      set ε := δ / (2 * M)
      have hε : 0 < ε := div_pos hδ (by positivity)
      have hball_pt : ∀ t : ℝ, |t| ≤ ε → r + t • v ∈ Metric.ball r δ := by
        intro t ht
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        have h1 : |(r + t • v).1 - r.1| = |t| * |v.1| := by
          simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, add_sub_cancel_left, abs_mul]
        have h2 : |(r + t • v).2 - r.2| = |t| * |v.2| := by
          simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, add_sub_cancel_left, abs_mul]
        rw [h1, h2]
        have hm1 : |t| * |v.1| ≤ ε * M := by
          have : |v.1| ≤ M := by dsimp only [M]; linarith [le_max_left |v.1| |v.2|]
          nlinarith [abs_nonneg t, abs_nonneg v.1]
        have hm2 : |t| * |v.2| ≤ ε * M := by
          have : |v.2| ≤ M := by dsimp only [M]; linarith [le_max_right |v.1| |v.2|]
          nlinarith [abs_nonneg t, abs_nonneg v.2]
        have hεM : ε * M < δ := by
          dsimp only [ε]; field_simp [hM.ne']; linarith
        exact max_lt (lt_of_le_of_lt hm1 hεM) (lt_of_le_of_lt hm2 hεM)
      have hpos_mem : r + ε • v ∈ {p : ℝ × ℝ | p ∈ openCompl S ∧ signVec S p = σ} :=
        hball (hball_pt ε (by rw [abs_of_pos hε]))
      have hneg_mem : r + (-ε) • v ∈ {p : ℝ × ℝ | p ∈ openCompl S ∧ signVec S p = σ} :=
        hball (hball_pt (-ε) (by rw [abs_neg, abs_of_pos hε]))
      constructor
      · simp only [realized, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨r + ε • v, ?_, ?_⟩
        · rw [mem_openCompl_iff]
          refine ⟨(mem_openCompl_iff.mp hpos_mem.1).1, fun d hd => ?_⟩
          rcases Finset.mem_insert.mp hd with rfl | hdS
          · rw [hv, hr0, zero_add]; exact hε.ne'
          · exact (mem_openCompl_iff.mp hpos_mem.1).2 d hdS
        · funext d
          by_cases h : d.1 ∈ S
          · simp only [extSign, dif_pos h]
            exact congrFun hpos_mem.2 ⟨d.1, h⟩
          · have hdc : d.1 = c := by
              rcases Finset.mem_insert.mp d.2 with heq | hmem
              · exact heq
              · exact (h hmem).elim
            simp only [extSign, dif_neg h, signVec, hdc, hv, hr0, zero_add, hε, decide_true]
      · simp only [realized, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨r + (-ε) • v, ?_, ?_⟩
        · rw [mem_openCompl_iff]
          refine ⟨(mem_openCompl_iff.mp hneg_mem.1).1, fun d hd => ?_⟩
          rcases Finset.mem_insert.mp hd with rfl | hdS
          · rw [hv, hr0, zero_add]; linarith
          · exact (mem_openCompl_iff.mp hneg_mem.1).2 d hdS
        · funext d
          by_cases h : d.1 ∈ S
          · simp only [extSign, dif_pos h]
            exact congrFun hneg_mem.2 ⟨d.1, h⟩
          · have hdc : d.1 = c := by
              rcases Finset.mem_insert.mp d.2 with heq | hmem
              · exact heq
              · exact (h hmem).elim
            simp only [extSign, dif_neg h, signVec, hdc, hv, hr0, zero_add]
            exact decide_eq_false (by linarith)
  have hat_least_one : ∀ σ ∈ realized S,
      extSign σ true ∈ realized (insert c S) ∨ extSign σ false ∈ realized (insert c S) := by
    intro σ hσ
    have hσ' := hσ
    simp only [realized, Finset.mem_filter, Finset.mem_univ, true_and] at hσ'
    obtain ⟨p, hp, hsig⟩ := hσ'
    by_cases h0 : cevianFunc c p = 0
    · obtain ⟨hs0, hs1, hray⟩ := cevianRay_rayParam (mem_openCompl_iff.mp hp).1 h0
      have hsp : σ ∈ splitSet S c := by
        simp only [splitSet, Finset.mem_filter]
        exact ⟨hσ, rayParam c p, hs0, hs1, by rw [hray]; exact hp, by rw [hray]; exact hsig⟩
      exact Or.inl ((hboth_iff σ hσ).mpr hsp).1
    · have hp_ins : p ∈ openCompl (insert c S) := by
        rw [mem_openCompl_iff]
        refine ⟨(mem_openCompl_iff.mp hp).1, fun d hd => ?_⟩
        rcases Finset.mem_insert.mp hd with rfl | hdS
        · exact h0
        · exact (mem_openCompl_iff.mp hp).2 d hdS
      have hsig_ins : signVec (insert c S) p = extSign σ (decide (0 < cevianFunc c p)) := by
        funext d
        by_cases h : d.1 ∈ S
        · simp only [extSign, dif_pos h]
          exact congrFun hsig ⟨d.1, h⟩
        · have hdc : d.1 = c := by
            rcases Finset.mem_insert.mp d.2 with heq | hmem
            · exact heq
            · exact (h hmem).elim
          simp only [extSign, dif_neg h, signVec, hdc]
      cases hb : decide (0 < cevianFunc c p)
      · right; simp only [realized, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨p, hp_ins, by rw [← hb]; exact hsig_ins⟩
      · left; simp only [realized, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨p, hp_ins, by rw [← hb]; exact hsig_ins⟩
  have hfiber_card : ∀ σ ∈ realized S,
      ((realized (insert c S)).filter (fun τ => res τ = σ)).card =
        1 + if σ ∈ splitSet S c then 1 else 0 := by
    intro σ hσ
    have hsub : (realized (insert c S)).filter (fun τ => res τ = σ) ⊆
        {extSign σ true, extSign σ false} := by
      intro τ hτ
      rw [Finset.mem_filter] at hτ
      have heq := hext_res τ
      rw [hτ.2] at heq
      cases hb : τ ⟨c, Finset.mem_insert_self c S⟩ <;>
        (rw [hb] at heq; simp [← heq])
    by_cases hsp : σ ∈ splitSet S c
    · rw [if_pos hsp]
      have hboth := (hboth_iff σ hσ).mpr hsp
      have heq : (realized (insert c S)).filter (fun τ => res τ = σ) =
          {extSign σ true, extSign σ false} := by
        apply Finset.Subset.antisymm hsub
        intro τ hτ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
        rcases hτ with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hboth.1, hres_ext σ true⟩
        · exact Finset.mem_filter.mpr ⟨hboth.2, hres_ext σ false⟩
      rw [heq, Finset.card_pair (hne_ext σ)]
    · rw [if_neg hsp, add_zero]
      have hnot_both : ¬ (extSign σ true ∈ realized (insert c S) ∧
          extSign σ false ∈ realized (insert c S)) := fun h => hsp ((hboth_iff σ hσ).mp h)
      rcases hat_least_one σ hσ with ht | hf
      · have hnf : extSign σ false ∉ realized (insert c S) := fun h => hnot_both ⟨ht, h⟩
        have heq : (realized (insert c S)).filter (fun τ => res τ = σ) = {extSign σ true} := by
          apply Finset.Subset.antisymm
          · intro τ hτ
            have hmem := hsub hτ
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
            rcases hmem with rfl | rfl
            · rfl
            · exact (hnf (Finset.mem_filter.mp hτ).1).elim
          · intro τ hτ
            rw [Finset.mem_singleton] at hτ; subst hτ
            exact Finset.mem_filter.mpr ⟨ht, hres_ext σ true⟩
        rw [heq, Finset.card_singleton]
      · have hnt : extSign σ true ∉ realized (insert c S) := fun h => hnot_both ⟨h, hf⟩
        have heq : (realized (insert c S)).filter (fun τ => res τ = σ) = {extSign σ false} := by
          apply Finset.Subset.antisymm
          · intro τ hτ
            have hmem := hsub hτ
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
            rcases hmem with rfl | rfl
            · exact (hnt (Finset.mem_filter.mp hτ).1).elim
            · rfl
          · intro τ hτ
            rw [Finset.mem_singleton] at hτ; subst hτ
            exact Finset.mem_filter.mpr ⟨hf, hres_ext σ false⟩
        rw [heq, Finset.card_singleton]
  rw [Finset.card_eq_sum_card_fiberwise hres_maps]
  rw [Finset.sum_congr rfl hfiber_card, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hsplit_sub : splitSet S c ⊆ realized S := Finset.filter_subset _ _
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsplit_sub]
  simp only [Nat.cast_id]
  rw [card_splitSet_eq hc]
  omega

/-!
## 5. Exact region formula, double counting, Turan bound, and general position
-/

noncomputable def allCrossings (S : Finset (Cevian stdVerts)) : Finset (ℝ × ℝ) := by
  classical
  exact ((S ×ˢ S).filter (fun p => p.1.vertex ≠ p.2.vertex)).image (fun p => interPt p.1 p.2)

noncomputable def mult (S : Finset (Cevian stdVerts)) (p : ℝ × ℝ) : ℕ := by
  classical
  exact (S.filter (fun c => p ∈ c.points)).card

lemma mem_allCrossings_iff {S : Finset (Cevian stdVerts)} {p : ℝ × ℝ} :
    p ∈ allCrossings S ↔ p ∈ stdTri ∧ ∃ c₁ ∈ S, ∃ c₂ ∈ S, c₁ ≠ c₂ ∧ p ∈ c₁.points ∧ p ∈ c₂.points := by
  classical
  simp only [allCrossings, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨c₁, c₂, ⟨⟨hc1, hc2⟩, hdv⟩, rfl⟩
    obtain ⟨ht, h1, h2⟩ := interPt_spec hdv
    exact ⟨ht, c₁, hc1, c₂, hc2, fun h => hdv (congrArg Cevian.vertex h), h1, h2⟩
  · rintro ⟨ht, c₁, hc1, c₂, hc2, hne, h1, h2⟩
    have hdv : c₁.vertex ≠ c₂.vertex := fun hv => same_vertex_disjoint hv hne ht ⟨h1, h2⟩
    exact ⟨c₁, c₂, ⟨⟨hc1, hc2⟩, hdv⟩, (interPt_eq_of_mem hdv ht h1 h2).symm⟩

lemma mult_ge_two_of_mem_allCrossings {S : Finset (Cevian stdVerts)} {p : ℝ × ℝ}
    (hp : p ∈ allCrossings S) : 2 ≤ mult S p := by
  classical
  obtain ⟨_, c₁, hc1, c₂, hc2, hne, h1, h2⟩ := mem_allCrossings_iff.mp hp
  have hsub : ({c₁, c₂} : Finset (Cevian stdVerts)) ⊆ S.filter (fun c => p ∈ c.points) := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hc1, h1⟩
    · exact Finset.mem_filter.mpr ⟨hc2, h2⟩
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hne] at this

lemma card_realized_formula (S : Finset (Cevian stdVerts)) :
    (realized S).card = 1 + S.card + ∑ p ∈ allCrossings S, (mult S p - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have hempty : allCrossings ∅ = ∅ := by simp [allCrossings]
    rw [hempty, Finset.sum_empty, Finset.card_empty]
    have hreal : realized ∅ = Finset.univ := by
      ext σ
      simp only [realized, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      refine ⟨(1 / 4, 1 / 4), ?_, funext fun x => Finset.notMem_empty x.1 x.2 |>.elim⟩
      rw [mem_openCompl_iff]
      exact ⟨⟨by norm_num, by norm_num, by norm_num⟩, fun c hc => (Finset.notMem_empty c hc).elim⟩
    rw [hreal, Finset.card_univ]
    simp
  | @insert c S hc ih =>
    rw [card_realized_insert hc, ih, Finset.card_insert_of_notMem hc]
    have hsub_cross : allCrossings S ⊆ allCrossings (insert c S) := by
      intro p hp
      obtain ⟨ht, c₁, hc1, c₂, hc2, hne, h1, h2⟩ := mem_allCrossings_iff.mp hp
      exact mem_allCrossings_iff.mpr
        ⟨ht, c₁, Finset.mem_insert_of_mem hc1, c₂, Finset.mem_insert_of_mem hc2, hne, h1, h2⟩
    have hsub_inter : interPts S c ⊆ allCrossings (insert c S) := by
      intro p hp
      obtain ⟨ht, hcp, d, hdS, hdp⟩ := (mem_interPts_iff hc).mp hp
      exact mem_allCrossings_iff.mpr
        ⟨ht, c, Finset.mem_insert_self c S, d, Finset.mem_insert_of_mem hdS,
          fun heq => hc (heq ▸ hdS), hcp, hdp⟩
    have hpt : ∀ p ∈ allCrossings (insert c S),
        mult (insert c S) p - 1 =
          (mult S p - 1) + if p ∈ interPts S c then 1 else 0 := by
      intro p hp
      by_cases hpi : p ∈ interPts S c
      · rw [if_pos hpi]
        obtain ⟨ht, hcp, d, hdS, hdp⟩ := (mem_interPts_iff hc).mp hpi
        have hmult_ins : mult (insert c S) p = mult S p + 1 := by
          unfold mult
          rw [Finset.filter_insert, if_pos hcp, Finset.card_insert_of_notMem]
          intro hmem; exact hc (Finset.mem_filter.mp hmem).1
        have hmult_pos : 1 ≤ mult S p := Finset.card_pos.mpr ⟨d, Finset.mem_filter.mpr ⟨hdS, hdp⟩⟩
        omega
      · rw [if_neg hpi, add_zero]
        have hnotc : p ∉ c.points := by
          intro hcp
          obtain ⟨ht, c₁, hc1, c₂, hc2, hne, h1, h2⟩ := mem_allCrossings_iff.mp hp
          rcases Finset.mem_insert.mp hc1 with rfl | hc1S
          · rcases Finset.mem_insert.mp hc2 with rfl | hc2S
            · exact hne rfl
            · exact hpi ((mem_interPts_iff hc).mpr ⟨ht, hcp, c₂, hc2S, h2⟩)
          · exact hpi ((mem_interPts_iff hc).mpr ⟨ht, hcp, c₁, hc1S, h1⟩)
        have hmult_eq : mult (insert c S) p = mult S p := by
          unfold mult
          rw [Finset.filter_insert, if_neg hnotc]
        rw [hmult_eq]
    have hzero_new : ∀ p ∈ allCrossings (insert c S), p ∉ allCrossings S → mult S p - 1 = 0 := by
      intro p hp hnot
      have hle : mult S p ≤ 1 := by
        by_contra hgt
        push_neg at hgt
        obtain ⟨c₁, hc1, c₂, hc2, hne⟩ := Finset.one_lt_card.mp hgt
        rw [Finset.mem_filter] at hc1 hc2
        have ht := (mem_allCrossings_iff.mp hp).1
        exact hnot (mem_allCrossings_iff.mpr ⟨ht, c₁, hc1.1, c₂, hc2.1, hne, hc1.2, hc2.2⟩)
      omega
    have hsum_eq :
        ∑ p ∈ allCrossings (insert c S), (mult (insert c S) p - 1) =
          (∑ p ∈ allCrossings S, (mult S p - 1)) + (interPts S c).card := by
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
      congr 1
      · exact (Finset.sum_subset hsub_cross hzero_new).symm
      · rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub_inter]
        simp
    omega

lemma double_count_pairs (S : Finset (Cevian stdVerts)) :
    ∑ p ∈ allCrossings S, mult S p * (mult S p - 1) =
      2 * ((S.filter (·.vertex = 0)).card * (S.filter (·.vertex = 1)).card +
           (S.filter (·.vertex = 1)).card * (S.filter (·.vertex = 2)).card +
           (S.filter (·.vertex = 2)).card * (S.filter (·.vertex = 0)).card) := by
  classical
  set P := (S ×ˢ S).filter (fun q => q.1.vertex ≠ q.2.vertex)
  have hmaps : ∀ q ∈ P, interPt q.1 q.2 ∈ allCrossings S := fun q hq =>
    Finset.mem_image_of_mem _ hq
  have hP_card : P.card =
      ∑ p ∈ allCrossings S, (P.filter (fun q => interPt q.1 q.2 = p)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber : ∀ p ∈ allCrossings S,
      (P.filter (fun q => interPt q.1 q.2 = p)).card = mult S p * (mult S p - 1) := by
    intro p hp
    have ht := (mem_allCrossings_iff.mp hp).1
    set Sp := S.filter (fun c => p ∈ c.points)
    have heq : P.filter (fun q => interPt q.1 q.2 = p) = (Sp ×ˢ Sp).filter (fun q => q.1 ≠ q.2) := by
      ext ⟨c₁, c₂⟩
      simp only [P, Sp, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨hc1, hc2⟩, hdv⟩, hint⟩
        obtain ⟨_, h1, h2⟩ := interPt_spec hdv
        rw [hint] at h1 h2
        exact ⟨⟨⟨hc1, h1⟩, ⟨hc2, h2⟩⟩, fun h => hdv (congrArg Cevian.vertex h)⟩
      · rintro ⟨⟨⟨hc1, h1⟩, ⟨hc2, h2⟩⟩, hne⟩
        have hdv : c₁.vertex ≠ c₂.vertex := fun hv => same_vertex_disjoint hv hne ht ⟨h1, h2⟩
        exact ⟨⟨⟨hc1, hc2⟩, hdv⟩, (interPt_eq_of_mem hdv ht h1 h2).symm⟩
    rw [heq]
    have hdiag : ((Sp ×ˢ Sp).filter (fun q => q.1 = q.2)).card = Sp.card := by
      have heq_diag : (Sp ×ˢ Sp).filter (fun q => q.1 = q.2) = Sp.image (fun c => (c, c)) := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
        · rintro ⟨c, hc, rfl, rfl⟩; exact ⟨⟨hc, hc⟩, rfl⟩
      rw [heq_diag, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
    have hsplit := Finset.card_filter_add_card_filter_not (s := Sp ×ˢ Sp) (p := fun q => q.1 = q.2)
    rw [Finset.card_product, hdiag] at hsplit
    have hmul : Sp.card * Sp.card = Sp.card + Sp.card * (Sp.card - 1) := by
      cases h : Sp.card with
      | zero => simp
      | succ k => simp [Nat.mul_succ]; ring
    change ((Sp ×ˢ Sp).filter (fun q => ¬ q.1 = q.2)).card = Sp.card * (Sp.card - 1)
    omega
  rw [← Finset.sum_congr rfl hfiber, ← hP_card]
  -- Count P directly by vertex pairs
  set S0 := S.filter (·.vertex = 0)
  set S1 := S.filter (·.vertex = 1)
  set S2 := S.filter (·.vertex = 2)
  have hpart : S = S0 ∪ (S1 ∪ S2) := by
    ext c
    simp only [S0, S1, S2, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hc
      have hv : c.vertex = 0 ∨ c.vertex = 1 ∨ c.vertex = 2 := fin3_cases c.vertex
      rcases hv with h | h | h
      · exact Or.inl ⟨hc, h⟩
      · exact Or.inr (Or.inl ⟨hc, h⟩)
      · exact Or.inr (Or.inr ⟨hc, h⟩)
    · rintro (⟨hc, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩) <;> exact hc
  have hsame : ((S ×ˢ S).filter (fun q => q.1.vertex = q.2.vertex)).card =
      S0.card * S0.card + S1.card * S1.card + S2.card * S2.card := by
    have heq : (S ×ˢ S).filter (fun q => q.1.vertex = q.2.vertex) =
        (S0 ×ˢ S0) ∪ ((S1 ×ˢ S1) ∪ (S2 ×ˢ S2)) := by
      ext ⟨a, b⟩
      simp only [S0, S1, S2, Finset.mem_filter, Finset.mem_product, Finset.mem_union]
      constructor
      · rintro ⟨⟨ha, hb⟩, hv⟩
        have h : a.vertex = 0 ∨ a.vertex = 1 ∨ a.vertex = 2 := fin3_cases a.vertex
        rcases h with h | h | h
        · exact Or.inl ⟨⟨ha, h⟩, ⟨hb, hv.symm.trans h⟩⟩
        · exact Or.inr (Or.inl ⟨⟨ha, h⟩, ⟨hb, hv.symm.trans h⟩⟩)
        · exact Or.inr (Or.inr ⟨⟨ha, h⟩, ⟨hb, hv.symm.trans h⟩⟩)
      · rintro (⟨⟨ha, h1⟩, ⟨hb, h2⟩⟩ | ⟨⟨ha, h1⟩, ⟨hb, h2⟩⟩ | ⟨⟨ha, h1⟩, ⟨hb, h2⟩⟩) <;>
          exact ⟨⟨ha, hb⟩, h1.trans h2.symm⟩
    rw [heq]
    have hd12 : Disjoint (S1 ×ˢ S1) (S2 ×ˢ S2) := by
      rw [Finset.disjoint_left]; rintro ⟨a, b⟩ h1 h2
      simp only [S1, S2, Finset.mem_product, Finset.mem_filter] at h1 h2
      exact absurd (h1.1.2.symm.trans h2.1.2) (by decide)
    have hd0 : Disjoint (S0 ×ˢ S0) ((S1 ×ˢ S1) ∪ (S2 ×ˢ S2)) := by
      rw [Finset.disjoint_left]; rintro ⟨a, b⟩ h0 h12
      simp only [S0, S1, S2, Finset.mem_union, Finset.mem_product, Finset.mem_filter] at h0 h12
      rcases h12 with h1 | h2
      · exact absurd (h0.1.2.symm.trans h1.1.2) (by decide)
      · exact absurd (h0.1.2.symm.trans h2.1.2) (by decide)
    rw [Finset.card_union_of_disjoint hd0, Finset.card_union_of_disjoint hd12,
      Finset.card_product, Finset.card_product, Finset.card_product]
    omega
  have hS_card : S.card = S0.card + S1.card + S2.card := by
    have hd12 : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]; intro a h1 h2
      simp only [S1, S2, Finset.mem_filter] at h1 h2
      exact absurd (h1.2.symm.trans h2.2) (by decide)
    have hd0 : Disjoint S0 (S1 ∪ S2) := by
      rw [Finset.disjoint_left]; intro a h0 h12
      simp only [S0, S1, S2, Finset.mem_union, Finset.mem_filter] at h0 h12
      rcases h12 with h1 | h2
      · exact absurd (h0.2.symm.trans h1.2) (by decide)
      · exact absurd (h0.2.symm.trans h2.2) (by decide)
    conv_lhs => rw [hpart]
    rw [Finset.card_union_of_disjoint hd0, Finset.card_union_of_disjoint hd12]
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := S ×ˢ S) (p := fun q => q.1.vertex = q.2.vertex)
  rw [Finset.card_product, hsame, hS_card] at hsplit
  change ((S ×ˢ S).filter (fun q => ¬ q.1.vertex = q.2.vertex)).card = _
  nlinarith

lemma turan_bound (a b d : ℕ) :
    a * b + b * d + d * a ≤ (a + b + d) ^ 2 / 3 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (d : ℤ) ^ 2 ≥ (a : ℤ) * b + b * d + d * a := by
    nlinarith [sq_nonneg ((a : ℤ) - b), sq_nonneg ((b : ℤ) - d), sq_nonneg ((d : ℤ) - a)]
  zify
  nlinarith

lemma turan_exact (n : ℕ) :
    (n / 3) + ((n + 1) / 3) + ((n + 2) / 3) = n ∧
      (n / 3) * ((n + 1) / 3) + ((n + 1) / 3) * ((n + 2) / 3) + ((n + 2) / 3) * (n / 3) = n ^ 2 / 3 := by
  obtain ⟨q, rfl | rfl | rfl⟩ : ∃ q, n = 3 * q ∨ n = 3 * q + 1 ∨ n = 3 * q + 2 :=
    ⟨n / 3, by omega⟩
  · have h1 : 3 * q / 3 = q := by omega
    have h2 : (3 * q + 1) / 3 = q := by omega
    have h3 : (3 * q + 2) / 3 = q := by omega
    have hsq : (3 * q) ^ 2 / 3 = 3 * q ^ 2 := by
      have : (3 * q) ^ 2 = 3 * (3 * q ^ 2) := by ring
      rw [this, Nat.mul_div_right _ (by norm_num)]
    rw [h1, h2, h3, hsq]
    constructor <;> ring
  · have h1 : (3 * q + 1) / 3 = q := by omega
    have h2 : (3 * q + 1 + 1) / 3 = q := by omega
    have h3 : (3 * q + 1 + 2) / 3 = q + 1 := by omega
    have hsq : (3 * q + 1) ^ 2 / 3 = 3 * q ^ 2 + 2 * q := by
      have : (3 * q + 1) ^ 2 = 3 * (3 * q ^ 2 + 2 * q) + 1 := by ring
      rw [this]; omega
    rw [h1, h2, h3, hsq]
    constructor <;> ring
  · have h1 : (3 * q + 2) / 3 = q := by omega
    have h2 : (3 * q + 2 + 1) / 3 = q + 1 := by omega
    have h3 : (3 * q + 2 + 2) / 3 = q + 1 := by omega
    have hsq : (3 * q + 2) ^ 2 / 3 = 3 * q ^ 2 + 4 * q + 1 := by
      have : (3 * q + 2) ^ 2 = 3 * (3 * q ^ 2 + 4 * q + 1) + 1 := by ring
      rw [this]; omega
    rw [h1, h2, h3, hsq]
    constructor <;> ring

lemma exists_distinct_Ioo_avoid (F : Finset ℝ) (k : ℕ) :
    ∃ f : Fin k → ℝ, Function.Injective f ∧ ∀ i, 0 < f i ∧ f i < 1 ∧ f i ∉ F := by
  classical
  induction k with
  | zero =>
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨f, hfinj, hfspec⟩ := ih
    let B : Finset ℝ := F ∪ Finset.univ.image f
    have hinf : (Set.Ioo (0 : ℝ) 1).Infinite := Set.Ioo_infinite zero_lt_one
    obtain ⟨x, hxIoo, hxnotB⟩ := (hinf.diff (Finset.finite_toSet B)).nonempty
    simp only [Set.mem_Ioo, Finset.mem_coe, B, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and, not_or, not_exists] at hxIoo hxnotB
    let g : Fin (k + 1) → ℝ := Fin.snoc f x
    refine ⟨g, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · refine Fin.lastCases (fun _ => rfl) (fun j' h => ?_) j
        simp only [g, Fin.snoc_last, Fin.snoc_castSucc] at h
        exact (hxnotB.2 j' h.symm).elim
      · refine Fin.lastCases (fun h => ?_) (fun j' h => ?_) j
        · simp only [g, Fin.snoc_last, Fin.snoc_castSucc] at h
          exact (hxnotB.2 i' h).elim
        · simp only [g, Fin.snoc_castSucc] at h
          exact congrArg Fin.castSucc (hfinj h)
    · intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp only [g, Fin.snoc_last]
        exact ⟨hxIoo.1, hxIoo.2, hxnotB.1⟩
      · simp only [g, Fin.snoc_castSucc]
        exact hfspec i'

lemma exists_general_position_std (n : ℕ) :
    ∃ c : Fin n → Cevian stdVerts, Function.Injective c ∧
      regionCount c = ((1 + n + n ^ 2 / 3 : ℕ) : ℕ∞) := by
  classical
  set n0 := n / 3
  set n1 := (n + 1) / 3
  set n2 := (n + 2) / 3
  obtain ⟨hsum, hturan⟩ := turan_exact n
  obtain ⟨f0, hf0_inj, hf0_spec⟩ := exists_distinct_Ioo_avoid ∅ n0
  obtain ⟨f1, hf1_inj, hf1_spec⟩ := exists_distinct_Ioo_avoid ∅ n1
  let c0 : Fin n0 → Cevian stdVerts := fun i => mkStdCevian 0 (f0 i) (hf0_spec i).1 (hf0_spec i).2.1
  let c1 : Fin n1 → Cevian stdVerts := fun j => mkStdCevian 1 (f1 j) (hf1_spec j).1 (hf1_spec j).2.1
  let F : Finset ℝ :=
    (Finset.univ : Finset (Fin n0 × Fin n1)).image
      (fun ij => let p := interPt (c0 ij.1) (c1 ij.2); p.1 / (1 - p.2))
  obtain ⟨f2, hf2_inj, hf2_spec⟩ := exists_distinct_Ioo_avoid F n2
  let c2 : Fin n2 → Cevian stdVerts := fun k => mkStdCevian 2 (f2 k) (hf2_spec k).1 (hf2_spec k).2.1
  let eSum : Fin n0 ⊕ Fin n1 ⊕ Fin n2 ≃ Fin n :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
      (finSumFinEquiv.trans (finCongr (by omega)))
  let g : Fin n0 ⊕ Fin n1 ⊕ Fin n2 → Cevian stdVerts
    | Sum.inl i => c0 i
    | Sum.inr (Sum.inl j) => c1 j
    | Sum.inr (Sum.inr k) => c2 k
  have hg_inj : Function.Injective g := by
    intro a b hab
    rcases a with i | (j | k) <;> rcases b with i' | (j' | k')
    · have hp := congrArg param hab
      simp only [g, c0, mkStdCevian_param] at hp
      exact congrArg Sum.inl (hf0_inj hp)
    · have hv := congrArg Cevian.vertex hab; simp [g, c0, c1, mkStdCevian] at hv
    · have hv := congrArg Cevian.vertex hab; simp [g, c0, c2, mkStdCevian] at hv
    · have hv := congrArg Cevian.vertex hab; simp [g, c0, c1, mkStdCevian] at hv
    · have hp := congrArg param hab
      simp only [g, c1, mkStdCevian_param] at hp
      exact congrArg (Sum.inr ∘ Sum.inl) (hf1_inj hp)
    · have hv := congrArg Cevian.vertex hab; simp [g, c1, c2, mkStdCevian] at hv
    · have hv := congrArg Cevian.vertex hab; simp [g, c0, c2, mkStdCevian] at hv
    · have hv := congrArg Cevian.vertex hab; simp [g, c1, c2, mkStdCevian] at hv
    · have hp := congrArg param hab
      simp only [g, c2, mkStdCevian_param] at hp
      exact congrArg (Sum.inr ∘ Sum.inr) (hf2_inj hp)
  let c : Fin n → Cevian stdVerts := g ∘ eSum.symm
  have hc_inj : Function.Injective c := hg_inj.comp eSum.symm.injective
  let S : Finset (Cevian stdVerts) := Finset.univ.image c
  have hS_card : S.card = n := by
    rw [Finset.card_image_of_injective _ hc_inj, Finset.card_fin]
  have hS_img : S = Finset.univ.image g := by
    ext x
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and, c, Function.comp_apply]
    exact ⟨fun ⟨i, hi⟩ => ⟨eSum.symm i, hi⟩, fun ⟨a, ha⟩ => ⟨eSum a, by simpa using ha⟩⟩
  have hS0 : (S.filter (·.vertex = 0)).card = n0 := by
    have heq : S.filter (·.vertex = 0) = Finset.univ.image c0 := by
      ext x
      rw [hS_img]
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨a, rfl⟩, hv⟩
        rcases a with i | (j | k)
        · exact ⟨i, rfl⟩
        · simp [g, c1, mkStdCevian] at hv
        · simp [g, c2, mkStdCevian] at hv
      · rintro ⟨i, rfl⟩
        exact ⟨⟨Sum.inl i, rfl⟩, rfl⟩
    rw [heq, Finset.card_image_of_injective _ (fun i j h => by
      have hp := congrArg param h; simp only [c0, mkStdCevian_param] at hp; exact hf0_inj hp),
      Finset.card_fin]
  have hS1 : (S.filter (·.vertex = 1)).card = n1 := by
    have heq : S.filter (·.vertex = 1) = Finset.univ.image c1 := by
      ext x
      rw [hS_img]
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨a, rfl⟩, hv⟩
        rcases a with i | (j | k)
        · simp [g, c0, mkStdCevian] at hv
        · exact ⟨j, rfl⟩
        · simp [g, c2, mkStdCevian] at hv
      · rintro ⟨j, rfl⟩
        exact ⟨⟨Sum.inr (Sum.inl j), rfl⟩, rfl⟩
    rw [heq, Finset.card_image_of_injective _ (fun i j h => by
      have hp := congrArg param h; simp only [c1, mkStdCevian_param] at hp; exact hf1_inj hp),
      Finset.card_fin]
  have hS2 : (S.filter (·.vertex = 2)).card = n2 := by
    have heq : S.filter (·.vertex = 2) = Finset.univ.image c2 := by
      ext x
      rw [hS_img]
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨a, rfl⟩, hv⟩
        rcases a with i | (j | k)
        · simp [g, c0, mkStdCevian] at hv
        · simp [g, c1, mkStdCevian] at hv
        · exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨⟨Sum.inr (Sum.inr k), rfl⟩, rfl⟩
    rw [heq, Finset.card_image_of_injective _ (fun i j h => by
      have hp := congrArg param h; simp only [c2, mkStdCevian_param] at hp; exact hf2_inj hp),
      Finset.card_fin]
  have hmult2 : ∀ p ∈ allCrossings S, mult S p = 2 := by
    intro p hp
    have hge := mult_ge_two_of_mem_allCrossings hp
    have hle : mult S p ≤ 2 := by
      by_contra hgt
      push_neg at hgt
      have ht := (mem_allCrossings_iff.mp hp).1
      set Sp := S.filter (fun x => p ∈ x.points)
      have hv_inj : Set.InjOn Cevian.vertex (Sp : Set (Cevian stdVerts)) := by
        intro x hx y hy hxy
        by_contra hne
        exact same_vertex_disjoint hxy hne ht
          ⟨(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2⟩
      have hcard_img : (Sp.image Cevian.vertex).card = Sp.card :=
        Finset.card_image_of_injOn hv_inj
      have hsub_univ : Sp.image Cevian.vertex ⊆ Finset.univ := Finset.subset_univ _
      have heq_univ : Sp.image Cevian.vertex = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le hsub_univ
        rw [Finset.card_fin, hcard_img]
        exact hgt
      have hmem0 : (0 : Fin 3) ∈ Sp.image Cevian.vertex := heq_univ ▸ Finset.mem_univ _
      have hmem1 : (1 : Fin 3) ∈ Sp.image Cevian.vertex := heq_univ ▸ Finset.mem_univ _
      have hmem2 : (2 : Fin 3) ∈ Sp.image Cevian.vertex := heq_univ ▸ Finset.mem_univ _
      obtain ⟨x0, hx0, hv0⟩ := Finset.mem_image.mp hmem0
      obtain ⟨x1, hx1, hv1⟩ := Finset.mem_image.mp hmem1
      obtain ⟨x2, hx2, hv2⟩ := Finset.mem_image.mp hmem2
      rw [Finset.mem_filter, hS_img, Finset.mem_image] at hx0 hx1 hx2
      obtain ⟨⟨a0, _, rfl⟩, hp0⟩ := hx0
      obtain ⟨⟨a1, _, rfl⟩, hp1⟩ := hx1
      obtain ⟨⟨a2, _, rfl⟩, hp2⟩ := hx2
      obtain ⟨i, rfl⟩ : ∃ i, a0 = Sum.inl i := by
        rcases a0 with i | (j | k)
        · exact ⟨i, rfl⟩
        · simp [g, c1, mkStdCevian] at hv0
        · simp [g, c2, mkStdCevian] at hv0
      obtain ⟨j, rfl⟩ : ∃ j, a1 = Sum.inr (Sum.inl j) := by
        rcases a1 with i' | (j | k)
        · simp [g, c0, mkStdCevian] at hv1
        · exact ⟨j, rfl⟩
        · simp [g, c2, mkStdCevian] at hv1
      obtain ⟨k, rfl⟩ : ∃ k, a2 = Sum.inr (Sum.inr k) := by
        rcases a2 with i' | (j' | k)
        · simp [g, c0, mkStdCevian] at hv2
        · simp [g, c1, mkStdCevian] at hv2
        · exact ⟨k, rfl⟩
      have hp_eq : p = interPt (c0 i) (c1 j) :=
        interPt_eq_of_mem (show (0 : Fin 3) ≠ 1 by decide) ht hp0 hp1
      have hfunc2 := (mem_points_iff_func_zero ht).mp hp2
      change cevianFunc (c2 k) p = 0 at hfunc2
      rw [cevianFunc] at hfunc2
      have hv2' : (c2 k).vertex = 2 := rfl
      rw [hv2', mkStdCevian_param] at hfunc2
      have h1py : 1 - p.2 ≠ 0 := by rcases ht with ⟨h1, h2, h3⟩; linarith
      have hf2_eq : f2 k = p.1 / (1 - p.2) := by
        rw [eq_div_iff h1py]; linarith
      have hf2_memF : f2 k ∈ F := by
        rw [hf2_eq, hp_eq]
        exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
      exact (hf2_spec k).2.2 hf2_memF
    omega
  have hsum_mult : ∑ p ∈ allCrossings S, (mult S p - 1) = n ^ 2 / 3 := by
    have hdc := double_count_pairs S
    rw [hS0, hS1, hS2, hturan] at hdc
    have h2 : ∑ p ∈ allCrossings S, mult S p * (mult S p - 1) =
        2 * ∑ p ∈ allCrossings S, (mult S p - 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [hmult2 p hp]
    omega
  have hreal : (realized S).card = 1 + n + n ^ 2 / 3 := by
    rw [card_realized_formula S, hS_card, hsum_mult]
  refine ⟨c, hc_inj, ?_⟩
  unfold regionCount
  have hset : triangleInterior stdVerts \ ⋃ i, (c i).points = openCompl S := by
    rw [triangleInterior_stdVerts, openCompl]
    congr 1
    ext p
    simp only [Set.mem_iUnion, S, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨c i, ⟨i, rfl⟩, hi⟩, fun ⟨_, ⟨i, rfl⟩, hi⟩ => ⟨i, hi⟩⟩
  rw [hset, card_connectedComponents_eq S, hreal]

lemma upper_bound_std {n : ℕ} (c : Fin n → Cevian stdVerts) (hc : Function.Injective c) :
    regionCount c ≤ ((1 + n + n ^ 2 / 3 : ℕ) : ℕ∞) ∧
      (regionCount c = ((1 + n + n ^ 2 / 3 : ℕ) : ℕ∞) →
        crossingCount c = ((n ^ 2 / 3 : ℕ) : ℕ∞)) := by
  classical
  let S : Finset (Cevian stdVerts) := Finset.univ.image c
  have hS_card : S.card = n := by
    rw [Finset.card_image_of_injective _ hc, Finset.card_fin]
  have hset : triangleInterior stdVerts \ ⋃ i, (c i).points = openCompl S := by
    rw [triangleInterior_stdVerts, openCompl]
    congr 1
    ext p
    simp only [Set.mem_iUnion, S, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨c i, ⟨i, rfl⟩, hi⟩, fun ⟨_, ⟨i, rfl⟩, hi⟩ => ⟨i, hi⟩⟩
  have hreg : regionCount c = ((realized S).card : ℕ∞) := by
    unfold regionCount
    rw [hset, card_connectedComponents_eq S]
  have hcross_set :
      {p ∈ triangleInterior stdVerts |
        ∃ i j : Fin n, i ≠ j ∧ p ∈ (c i).points ∧ p ∈ (c j).points} =
      (allCrossings S : Set (ℝ × ℝ)) := by
    ext p
    rw [triangleInterior_stdVerts, Finset.mem_coe, mem_allCrossings_iff]
    simp only [Set.mem_setOf_eq, S, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ht, i, j, hij, hi, hj⟩
      exact ⟨ht, c i, ⟨i, rfl⟩, c j, ⟨j, rfl⟩, fun h => hij (hc h), hi, hj⟩
    · rintro ⟨ht, _, ⟨i, rfl⟩, _, ⟨j, rfl⟩, hne, hi, hj⟩
      exact ⟨ht, i, j, fun h => hne (congrArg c h), hi, hj⟩
  have hcross : crossingCount c = ((allCrossings S).card : ℕ∞) := by
    unfold crossingCount
    rw [hcross_set, Set.encard_coe_eq_coe_finsetCard]
  have hpart_card : (S.filter (·.vertex = 0)).card + (S.filter (·.vertex = 1)).card +
      (S.filter (·.vertex = 2)).card = n := by
    set S0 := S.filter (·.vertex = 0)
    set S1 := S.filter (·.vertex = 1)
    set S2 := S.filter (·.vertex = 2)
    have hpart : S = S0 ∪ (S1 ∪ S2) := by
      ext x
      simp only [S0, S1, S2, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hx
        have hv : x.vertex = 0 ∨ x.vertex = 1 ∨ x.vertex = 2 := fin3_cases x.vertex
        rcases hv with h | h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr (Or.inl ⟨hx, h⟩)
        · exact Or.inr (Or.inr ⟨hx, h⟩)
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    have hd12 : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]; intro a h1 h2
      simp only [S1, S2, Finset.mem_filter] at h1 h2
      exact absurd (h1.2.symm.trans h2.2) (by decide)
    have hd0 : Disjoint S0 (S1 ∪ S2) := by
      rw [Finset.disjoint_left]; intro a h0 h12
      simp only [S0, S1, S2, Finset.mem_union, Finset.mem_filter] at h0 h12
      rcases h12 with h1 | h2
      · exact absurd (h0.2.symm.trans h1.2) (by decide)
      · exact absurd (h0.2.symm.trans h2.2) (by decide)
    rw [← hS_card]
    conv_rhs => rw [hpart]
    rw [Finset.card_union_of_disjoint hd0, Finset.card_union_of_disjoint hd12]
    omega
  have hsum_le : 2 * ∑ p ∈ allCrossings S, (mult S p - 1) ≤
      ∑ p ∈ allCrossings S, mult S p * (mult S p - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    exact Nat.mul_le_mul_right _ (mult_ge_two_of_mem_allCrossings hp)
  have hdc := double_count_pairs S
  have ht := turan_bound (S.filter (·.vertex = 0)).card
    (S.filter (·.vertex = 1)).card (S.filter (·.vertex = 2)).card
  rw [hpart_card] at ht
  have hreal_le : (realized S).card ≤ 1 + n + n ^ 2 / 3 := by
    rw [card_realized_formula S, hS_card]
    omega
  refine ⟨?_, ?_⟩
  · rw [hreg]
    exact_mod_cast hreal_le
  · intro heq
    rw [hreg] at heq
    have hnat : (realized S).card = 1 + n + n ^ 2 / 3 := by exact_mod_cast heq
    rw [card_realized_formula S, hS_card] at hnat
    have hsum_eq : ∑ p ∈ allCrossings S, (mult S p - 1) = n ^ 2 / 3 := by omega
    have hpair_eq : 2 * ∑ p ∈ allCrossings S, (mult S p - 1) =
        ∑ p ∈ allCrossings S, mult S p * (mult S p - 1) := by omega
    rw [Finset.mul_sum] at hpair_eq
    have hpt_eq : ∀ p ∈ allCrossings S, 2 * (mult S p - 1) = mult S p * (mult S p - 1) := by
      intro p hp
      by_contra hne
      have hlt : 2 * (mult S p - 1) < mult S p * (mult S p - 1) :=
        lt_of_le_of_ne (Nat.mul_le_mul_right _ (mult_ge_two_of_mem_allCrossings hp)) hne
      have hstrict : ∑ q ∈ allCrossings S, 2 * (mult S q - 1) <
          ∑ q ∈ allCrossings S, mult S q * (mult S q - 1) :=
        Finset.sum_lt_sum (fun q hq => Nat.mul_le_mul_right _ (mult_ge_two_of_mem_allCrossings hq))
          ⟨p, hp, hlt⟩
      omega
    have hmult2 : ∀ p ∈ allCrossings S, mult S p - 1 = 1 := by
      intro p hp
      have hge := mult_ge_two_of_mem_allCrossings hp
      have heq_p := hpt_eq p hp
      have hpos : 0 < mult S p - 1 := by omega
      have h2 : mult S p = 2 := by
        have := Nat.eq_of_mul_eq_mul_right hpos heq_p.symm
        exact this
      omega
    have hcard_eq : (allCrossings S).card = n ^ 2 / 3 := by
      rw [← hsum_eq]
      calc (allCrossings S).card = ∑ _p ∈ allCrossings S, 1 := by simp
        _ = ∑ p ∈ allCrossings S, (mult S p - 1) :=
            Finset.sum_congr rfl fun p hp => (hmult2 p hp).symm
    rw [hcross, hcard_eq]

lemma main_std (n : ℕ) :
    (∃ c : Fin n → Cevian stdVerts, MaximizesRegions c) ∧
    (∀ c : Fin n → Cevian stdVerts, MaximizesRegions c →
      crossingCount c = ((n ^ 2 / 3 : ℕ) : ℕ∞)) := by
  obtain ⟨copt, hcopt_inj, hcopt_reg⟩ := exists_general_position_std n
  constructor
  · refine ⟨copt, hcopt_inj, fun d hd => ?_⟩
    rw [hcopt_reg]
    exact (upper_bound_std d hd).1
  · intro c ⟨hc_inj, hc_max⟩
    have hle := (upper_bound_std c hc_inj).1
    have hge : ((1 + n + n ^ 2 / 3 : ℕ) : ℕ∞) ≤ regionCount c := by
      rw [← hcopt_reg]
      exact hc_max copt hcopt_inj
    exact (upper_bound_std c hc_inj).2 (le_antisymm hle hge)

lemma main_general (n : ℕ) (v : Fin 3 → ℝ × ℝ) (hv : AffineIndependent ℝ v) :
    (∃ c : Fin n → Cevian v, MaximizesRegions c) ∧
    (∀ c : Fin n → Cevian v, MaximizesRegions c →
      crossingCount c = ((n ^ 2 / 3 : ℕ) : ℕ∞)) := by
  obtain ⟨⟨copt, hcopt_inj, hcopt_max⟩, hstd_cross⟩ := main_std n
  constructor
  · refine ⟨fun i => mapCevian hv (copt i), (cevianEquiv hv).injective.comp hcopt_inj, fun d hd => ?_⟩
    let d' : Fin n → Cevian stdVerts := fun i => unmapCevian hv (d i)
    have hd'_inj : Function.Injective d' := (cevianEquiv hv).symm.injective.comp hd
    have hd_eq : d = fun i => mapCevian hv (d' i) := by
      funext i; exact (cevianEquiv hv).apply_symm_apply (d i) |>.symm
    rw [hd_eq, regionCount_mapCevian hv d', regionCount_mapCevian hv copt]
    exact hcopt_max d' hd'_inj
  · intro c ⟨hc_inj, hc_max⟩
    let c' : Fin n → Cevian stdVerts := fun i => unmapCevian hv (c i)
    have hc'_inj : Function.Injective c' := (cevianEquiv hv).symm.injective.comp hc_inj
    have hc_eq : c = fun i => mapCevian hv (c' i) := by
      funext i; exact (cevianEquiv hv).apply_symm_apply (c i) |>.symm
    have hc'_max : MaximizesRegions c' := by
      refine ⟨hc'_inj, fun d hd => ?_⟩
      have h := hc_max (fun i => mapCevian hv (d i)) ((cevianEquiv hv).injective.comp hd)
      rw [regionCount_mapCevian hv d, hc_eq, regionCount_mapCevian hv c'] at h
      exact h
    rw [hc_eq, crossingCount_mapCevian hv c']
    exact hstd_cross c' hc'_max

end OMA.OeisA000212

theorem OMA.solution : type_of% @OMA.S_oeis_a000212.main := by
  intro n vertices hv
  exact OMA.OeisA000212.main_general n vertices hv

