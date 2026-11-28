import OMAReductions.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1_H2_R1_H2_R1
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

/-!
A sufficiently small rotation about the unique shared point preserves the
distance bounds and can introduce a distance absent from the original minimizer.
-/

-- Credit: @RiverMint78

namespace HingeRotation

open EuclideanGeometry Filter
open scoped EuclideanGeometry Topology

/-- A rotation about `z` can move finitely many points by arbitrarily little while making
the distance between the moved `x` and the fixed `y` avoid a prescribed finite set. -/
private theorem rotation_exists (z x y : ℝ²) (hx : x ≠ z) (hy : y ≠ z) (S : Finset ℝ)
    (δ : ℝ) (hδ : 0 < δ) (A : Finset ℝ²) :
    ∃ f : ℝ² → ℝ², Isometry f ∧ f z = z ∧
      (∀ a ∈ A, dist (f a) a < δ) ∧ dist (f x) y ∉ S := by
  classical
  let o : Orientation ℝ ℝ² (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let turn (t : ℝ) (p : ℝ²) : ℝ² := o.rotation (t : Real.Angle) (p - z) + z
  have isom (t : ℝ) : Isometry (turn t) := by
    apply Isometry.of_dist_eq
    intro p q
    simp only [turn, dist_eq_norm]
    rw [show o.rotation (t : Real.Angle) (p - z) + z -
          (o.rotation (t : Real.Angle) (q - z) + z) =
        o.rotation (t : Real.Angle) (p - z) - o.rotation (t : Real.Angle) (q - z) by abel]
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    congr 1
    abel
  have fixed (t : ℝ) : turn t z = z := by simp [turn]
  have atZero (p : ℝ²) : turn 0 p = p := by simp [turn]
  have turnContinuous (p : ℝ²) : Continuous fun t => turn t p := by
    simp only [turn, o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
    fun_prop
  have small : ∀ᶠ t : ℝ in 𝓝 0, ∀ p ∈ A, dist (turn t p) p < δ := by
    apply (Filter.eventually_all_finset A).mpr
    intro p _
    have continuousDist : Continuous (fun t : ℝ => dist (turn t p) p) :=
      (turnContinuous p).dist continuous_const
    have h : Tendsto (fun t => dist (turn t p) p) (𝓝 0) (𝓝 0) := by
      simpa only [atZero, dist_self] using (continuousDist.continuousAt (x := 0)).tendsto
    exact h.eventually (Iio_mem_nhds hδ)
  obtain ⟨ε, hε, smallOn⟩ := Metric.eventually_nhds_iff.mp small
  let η := min ε Real.pi
  have hη : 0 < η := lt_min hε Real.pi_pos
  let I := Set.Ioo (-η) η
  have orbitInj : Set.InjOn (fun t => turn t x) I := by
    intro s hs t ht hst
    have hv : o.rotation (s : Real.Angle) (x - z) = o.rotation (t : Real.Angle) (x - z) :=
      add_right_cancel hst
    have he := congrArg (fun v : ℝ² => o.rotation (-(s : Real.Angle)) v) hv
    rw [o.rotation_rotation, o.rotation_rotation, neg_add_cancel, o.rotation_zero] at he
    have hAngle := (o.rotation_eq_self_iff_angle_eq_zero (sub_ne_zero.mpr hx)
      (-(s : Real.Angle) + (t : Real.Angle))).mp he.symm
    have hstAngle : (s : Real.Angle) = (t : Real.Angle) := by
      simpa [← add_assoc] using (congrArg (fun u : Real.Angle => (s : Real.Angle) + u) hAngle).symm
    have hηpi : η ≤ Real.pi := min_le_right _ _
    have hcoe (u : ℝ) (hu : u ∈ I) : (u : Real.Angle).toReal = u :=
      Real.Angle.toReal_coe_eq_self_iff.mpr
        ⟨(neg_le_neg hηpi).trans_lt hu.1, hu.2.le.trans hηpi⟩
    simpa only [hcoe s hs, hcoe t ht] using congrArg Real.Angle.toReal hstAngle
  have orbitInfinite : ((fun t => turn t x) '' I).Infinite :=
    (Set.Ioo_infinite (show -η < η by linarith)).image orbitInj
  let forbidden (r : ℝ) : Set ℝ² := {p | dist p z = dist x z ∧ dist p y = r}
  have forbiddenFinite (r : ℝ) : (forbidden r).Finite := by
    by_cases hs : (forbidden r).Subsingleton
    · exact hs.finite
    obtain ⟨p, hp, q, hq, hpq⟩ := Set.not_subsingleton_iff.mp hs
    refine ((Set.finite_singleton q).insert p).subset ?_
    intro u hu
    have he : u = p ∨ u = q := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
      (V := ℝ²) (by simp) hy.symm hpq hp.1 hq.1 hu.1 hp.2 hq.2 hu.2
    simpa using he
  have badFinite : (⋃ r ∈ (S : Set ℝ), forbidden r).Finite :=
    S.finite_toSet.biUnion fun r _ => forbiddenFinite r
  obtain ⟨p, hp, hbad⟩ := (orbitInfinite.sdiff badFinite).nonempty
  obtain ⟨t, ht, rfl⟩ := hp
  have htSmall : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨(neg_le_neg (min_le_left ε Real.pi)).trans_lt ht.1,
      ht.2.trans_le (min_le_left ε Real.pi)⟩
  refine ⟨turn t, isom t, fixed t, smallOn htSmall, ?_⟩
  intro htS
  apply hbad
  refine Set.mem_iUnion.mpr ⟨dist (turn t x) y, Set.mem_iUnion.mpr ⟨htS, ?_⟩⟩
  exact ⟨by simpa only [fixed t] using (isom t).dist_eq x z, rfl⟩

end HingeRotation

open EuclideanGeometry Finset Erdos103
open OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1 (sep_dist mk_sep)

set_option maxHeartbeats 1000000 in
theorem OMA.solution : OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1_H2_R1_H2_R1.H1 := by
  classical
  intro n A hA L R hCover hShared hLeft hRight hCross
  obtain ⟨z, hAnchor⟩ := card_eq_one.mp hShared
  have hz : z ∈ L ∩ R := by simp [hAnchor]
  obtain ⟨hzL, hzR⟩ := mem_inter.mp hz
  have anchor_of_mem {a : ℝ²} (haL : a ∈ L) (haR : a ∈ R) : a = z := by
    simpa only [hAnchor, mem_singleton] using (mem_inter.mpr ⟨haL, haR⟩ : a ∈ L ∩ R)
  obtain ⟨x, hx⟩ := hLeft
  obtain ⟨y, hy⟩ := hRight
  have hxz : x ≠ z := fun h => (mem_sdiff.mp hx).2 (h.symm ▸ hzR)
  have hyz : y ≠ z := fun h => (mem_sdiff.mp hy).2 (h.symm ▸ hzL)
  let D := Metric.diam (A : Set ℝ²)
  let pairs := (L \ R) ×ˢ (R \ L)
  let margin (ab : ℝ² × ℝ²) := min (dist ab.1 ab.2 - 1) (D - dist ab.1 ab.2)
  have pairs_nonempty : pairs.Nonempty := ⟨(x, y), mem_product.mpr ⟨hx, hy⟩⟩
  let δ := pairs.inf' pairs_nonempty margin
  have hδ : 0 < δ := by
    obtain ⟨ab, hab, hEq⟩ := exists_mem_eq_inf' pairs_nonempty margin
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    obtain ⟨hlo, hhi⟩ := hCross ab.1 ha ab.2 hb
    change 0 < pairs.inf' pairs_nonempty margin
    rw [hEq]
    exact lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi)
  let spectrum := (A ×ˢ A).image fun ab => dist ab.1 ab.2
  obtain ⟨f, hIso, hfz, hMove, hNovel⟩ := HingeRotation.rotation_exists z x y hxz hyz spectrum δ hδ L
  have fixed {a : ℝ²} (haL : a ∈ L) (haR : a ∈ R) : f a = a := by
    rw [anchor_of_mem haL haR, hfz]
  have cross_rotated (a : ℝ²) (ha : a ∈ L \ R) (b : ℝ²) (hb : b ∈ R \ L) :
      1 < dist (f a) b ∧ dist (f a) b < D := by
    have hlim : δ ≤ margin (a, b) := inf'_le margin (mem_product.mpr ⟨ha, hb⟩)
    have hlo : δ ≤ dist a b - 1 := hlim.trans (min_le_left _ _)
    have hhi : δ ≤ D - dist a b := hlim.trans (min_le_right _ _)
    have hsmall := hMove a (mem_sdiff.mp ha).1
    have lower_triangle := dist_triangle a (f a) b
    rw [dist_comm a (f a)] at lower_triangle
    have upper_triangle := dist_triangle (f a) a b
    constructor <;> linarith

  let L' := L.image f
  let B := L' ∪ R
  have hInter : L' ∩ R = L ∩ R := by
    ext a
    change a ∈ L.image f ∩ R ↔ a ∈ L ∩ R
    simp only [mem_inter, mem_image]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hfu⟩
      by_cases huR : u ∈ R
      · simpa only [fixed hu huR] using And.intro hu huR
      by_cases hfuL : f u ∈ L
      · exact ⟨hfuL, hfu⟩
      have hdist := (cross_rotated u (mem_sdiff.mpr ⟨hu, huR⟩) (f u)
        (mem_sdiff.mpr ⟨hfu, hfuL⟩)).1
      rw [dist_self] at hdist
      norm_num at hdist
    · rintro ⟨haL, haR⟩
      exact ⟨⟨a, haL, fixed haL haR⟩, haR⟩
  have hCard : B.card = n := by
    have before := card_union_add_card_inter L R
    rw [hCover] at before
    have after := card_union_add_card_inter L' R
    have hImage : L'.card = L.card := card_image_of_injective _ hIso.injective
    rw [hInter, hImage] at after
    have hAcard : A.card = n := hA.1.1
    change (L' ∪ R).card = n
    omega
  have left_mem {a : ℝ²} (ha : a ∈ L) : a ∈ A := hCover ▸ mem_union_left R ha
  have right_mem {a : ℝ²} (ha : a ∈ R) : a ∈ A := hCover ▸ mem_union_right L ha
  have old_bounds (a b : ℝ²) (ha : a ∈ A) (hb : b ∈ A) (hne : a ≠ b) :
      1 ≤ dist a b ∧ dist a b ≤ D :=
    ⟨sep_dist hA.1 ha hb hne, Metric.dist_le_diam_of_mem A.finite_toSet.isBounded ha hb⟩
  have mixed_bounds (a b : ℝ²) (ha : a ∈ L) (hb : b ∈ R) (hne : f a ≠ b) :
      1 ≤ dist (f a) b ∧ dist (f a) b ≤ D := by
    by_cases haR : a ∈ R
    · rw [fixed ha haR] at hne ⊢
      exact old_bounds a b (left_mem ha) (right_mem hb) hne
    by_cases hbL : b ∈ L
    · have hf := fixed hbL hb
      have hab : a ≠ b := fun h => hne (h.symm ▸ hf)
      rw [← hf, hIso.dist_eq]
      exact old_bounds a b (left_mem ha) (right_mem hb) hab
    obtain ⟨hlo, hhi⟩ := cross_rotated a (mem_sdiff.mpr ⟨ha, haR⟩) b (mem_sdiff.mpr ⟨hb, hbL⟩)
    exact ⟨hlo.le, hhi.le⟩
  have new_bounds (a b : ℝ²) (ha : a ∈ B) (hb : b ∈ B) (hne : a ≠ b) :
      1 ≤ dist a b ∧ dist a b ≤ D := by
    rcases mem_union.mp ha with ha | ha
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
      rcases mem_union.mp hb with hb | hb
      · obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
        rw [hIso.dist_eq]
        exact old_bounds u v (left_mem hu) (left_mem hv) (fun h => hne (congrArg f h))
      · exact mixed_bounds u b hu hb hne
    · rcases mem_union.mp hb with hb | hb
      · obtain ⟨v, hv, rfl⟩ := mem_image.mp hb
        rw [dist_comm a (f v)]
        exact mixed_bounds v a hv ha hne.symm
      · exact old_bounds a b (right_mem ha) (right_mem hb) hne
  have hSep : B ∈ separatedSets n := mk_sep hCard (fun a ha b hb hne => (new_bounds a b ha hb hne).1)
  have hDiam : Metric.diam (B : Set ℝ²) ≤ D := by
    apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
    intro a ha b hb
    by_cases hab : a = b
    · rw [hab, dist_self]
      exact Metric.diam_nonneg
    · exact (new_bounds a b ha hb hab).2
  refine ⟨B, ⟨hSep, fun X hX => hDiam.trans (hA.2 hX)⟩, ?_⟩
  rintro ⟨e, he⟩
  have hxB : f x ∈ B := mem_union_left R (mem_image.mpr ⟨x, (mem_sdiff.mp hx).1, rfl⟩)
  have hyB : y ∈ B := mem_union_right L' (mem_sdiff.mp hy).1
  have hxImage : f x ∈ e '' (A : Set ℝ²) := by rw [he]; exact hxB
  have hyImage : y ∈ e '' (A : Set ℝ²) := by rw [he]; exact hyB
  obtain ⟨u, hu, hu'⟩ := hxImage
  obtain ⟨v, hv, hv'⟩ := hyImage
  apply hNovel
  refine mem_image.mpr ⟨(u, v), mem_product.mpr ⟨hu, hv⟩, ?_⟩
  calc
    dist u v = dist (e u) (e v) := (e.isometry.dist_eq u v).symm
    _ = dist (f x) y := by rw [hu', hv']
