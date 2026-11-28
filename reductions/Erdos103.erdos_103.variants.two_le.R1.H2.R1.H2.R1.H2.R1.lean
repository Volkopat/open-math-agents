import OMAReductions.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1_H2_R1

/-!
Use the graph of active distances, meaning distances equal to one or to the
optimal diameter. A disconnected graph allows translation of one component.
The remaining graph cases are a cut vertex and connectivity after any one
vertex is removed.
-/

open EuclideanGeometry Filter Finset Erdos103
open scoped Classical

namespace OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1_H2_R1_H2_R1

open OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1 (sep_dist mk_sep)

set_option maxHeartbeats 1000000 in
private theorem translate_part {n : ℕ} {A L R : Finset ℝ²} (hA : IsMinimiser n A)
    (hcover : L ∪ R = A) (hdisj : Disjoint L R) (hL : L.Nonempty) (hR : R.Nonempty)
    (hcross : ∀ x ∈ L, ∀ y ∈ R, 1 < dist x y ∧ dist x y < Metric.diam (A : Set ℝ²)) :
    ∃ B : Finset ℝ², IsMinimiser n B ∧ ¬ Congruent A B := by
  let D := Metric.diam (A : Set ℝ²)
  obtain ⟨x, hx⟩ := hL
  obtain ⟨y, hy⟩ := hR
  let d := dist x y
  have hd : 0 < d := one_pos.trans (hcross x hx y hy).1
  let margin (xy : ℝ² × ℝ²) := min (dist xy.1 xy.2 - 1) (D - dist xy.1 xy.2)
  have hP : (L ×ˢ R).Nonempty := ⟨(x, y), mem_product.mpr ⟨hx, hy⟩⟩
  let δ := (L ×ˢ R).inf' hP margin
  have hδ : 0 < δ := by
    obtain ⟨xy, hxy, hEq⟩ := exists_mem_eq_inf' hP margin
    obtain ⟨hl, hr⟩ := mem_product.mp hxy
    obtain ⟨hlo, hhi⟩ := hcross xy.1 hl xy.2 hr
    change 0 < (L ×ˢ R).inf' hP margin
    rw [hEq]
    exact lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi)
  let Spectrum := (A ×ˢ A).image fun xy => dist xy.1 xy.2
  have hInf : (Set.Ioo d (d + δ)).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨t, ht⟩ := (hInf.sdiff Spectrum.finite_toSet).nonempty
  have ht₀ : d < t := ht.1.1
  have ht₁ : t < d + δ := ht.1.2
  have htSpectrum : t ∉ Spectrum := ht.2
  let v : ℝ² := (t / d - 1) • (x - y)
  have hr : 1 ≤ t / d := (le_div_iff₀ hd).mpr (by simpa using ht₀.le)
  have hv : ‖v‖ < δ := by
    change ‖(t / d - 1) • (x - y)‖ < δ
    rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hr), ← dist_eq_norm]
    change (t / d - 1) * d < δ
    rw [sub_mul, div_mul_cancel₀ _ hd.ne', one_mul]
    linarith
  have hdist : dist (x + v) y = t := by
    have heq : x + v - y = (t / d) • (x - y) := by
      dsimp [v]
      rw [sub_smul, one_smul]
      abel
    rw [dist_eq_norm, heq, norm_smul, Real.norm_of_nonneg (by linarith), ← dist_eq_norm]
    exact div_mul_cancel₀ _ hd.ne'
  have hs (a : ℝ²) (ha : a ∈ L) (b : ℝ²) (hb : b ∈ R) :
      1 < dist (a + v) b ∧ dist (a + v) b < D := by
    have hlim : δ ≤ margin (a, b) := inf'_le margin (mem_product.mpr ⟨ha, hb⟩)
    have hLower : δ ≤ dist a b - 1 := hlim.trans (min_le_left _ _)
    have hUpper : δ ≤ D - dist a b := hlim.trans (min_le_right _ _)
    have hMove : dist (a + v) a = ‖v‖ := by rw [dist_eq_norm, add_sub_cancel_left]
    have h₁ := dist_triangle a (a + v) b
    have h₂ := dist_triangle (a + v) a b
    rw [dist_comm a (a + v), hMove] at h₁
    rw [hMove] at h₂
    constructor <;> linarith
  let L' := L.image fun a => a + v
  let B := L' ∪ R
  have hdisj' : Disjoint L' R := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
    have h := (hs u hu (u + v) hb).1
    rw [dist_self] at h
    linarith
  have hCard : B.card = n := by
    have hAdd : Function.Injective (fun a : ℝ² => a + v) := fun _ _ heq => add_right_cancel heq
    change (L' ∪ R).card = n
    rw [card_union_of_disjoint hdisj']
    change (L.image (fun a => a + v)).card + R.card = n
    rw [card_image_of_injective _ hAdd, ← card_union_of_disjoint hdisj, hcover]
    exact hA.1.1
  have hLeft (a : ℝ²) (ha : a ∈ L) : a ∈ A := by
    rw [← hcover]
    exact mem_union.mpr (Or.inl ha)
  have hRight (b : ℝ²) (hb : b ∈ R) : b ∈ A := by
    rw [← hcover]
    exact mem_union.mpr (Or.inr hb)
  have hOld (a b : ℝ²) (ha : a ∈ A) (hb : b ∈ A) (hne : a ≠ b) :
      1 ≤ dist a b ∧ dist a b ≤ D :=
    ⟨sep_dist hA.1 ha hb hne, Metric.dist_le_diam_of_mem A.finite_toSet.isBounded ha hb⟩
  have hNew (a : ℝ²) (ha : a ∈ B) (b : ℝ²) (hb : b ∈ B) (hne : a ≠ b) :
      1 ≤ dist a b ∧ dist a b ≤ D := by
    rcases mem_union.mp ha with ha | ha
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp ha
      rcases mem_union.mp hb with hb | hb
      · obtain ⟨w, hw, rfl⟩ := mem_image.mp hb
        have heq : dist (u + v) (w + v) = dist u w := by
          rw [dist_eq_norm, dist_eq_norm, show u + v - (w + v) = u - w by abel]
        rw [heq]
        exact hOld u w (hLeft u hu) (hLeft w hw) (fun h => hne (congrArg (fun z => z + v) h))
      · exact ⟨(hs u hu b hb).1.le, (hs u hu b hb).2.le⟩
    · rcases mem_union.mp hb with hb | hb
      · obtain ⟨w, hw, rfl⟩ := mem_image.mp hb
        rw [dist_comm a (w + v)]
        exact ⟨(hs w hw a ha).1.le, (hs w hw a ha).2.le⟩
      · exact hOld a b (hRight a ha) (hRight b hb) hne
  have hSep : B ∈ separatedSets n := mk_sep hCard (fun a ha b hb hne => (hNew a ha b hb hne).1)
  have hDiam : Metric.diam (B : Set ℝ²) ≤ D := by
    apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
    intro a ha b hb
    by_cases heq : a = b
    · rw [heq, dist_self]
      exact Metric.diam_nonneg
    · exact (hNew a ha b hb heq).2
  refine ⟨B, ⟨hSep, fun X hX => hDiam.trans (hA.2 hX)⟩, ?_⟩
  rintro ⟨e, he⟩
  have hxB : x + v ∈ B := mem_union.mpr (Or.inl (mem_image.mpr ⟨x, hx, rfl⟩))
  have hyB : y ∈ B := mem_union.mpr (Or.inr hy)
  have hxImage : x + v ∈ e '' (A : Set ℝ²) := by rw [he]; exact hxB
  have hyImage : y ∈ e '' (A : Set ℝ²) := by rw [he]; exact hyB
  obtain ⟨u, hu, hu'⟩ := hxImage
  obtain ⟨w, hw, hw'⟩ := hyImage
  apply htSpectrum
  refine mem_image.mpr ⟨(u, w), mem_product.mpr ⟨hu, hw⟩, ?_⟩
  calc dist u w = dist (e u) (e w) := (e.isometry.dist_eq u w).symm
    _ = t := by rw [hu', hw', hdist]

/-- A single shared anchor allows a small rotation of one side of the cut. -/
def H1 : Prop :=
  ∀ (n : ℕ) (A : Finset ℝ²), IsMinimiser n A →
    ∀ L R : Finset ℝ², L ∪ R = A → (L ∩ R).card = 1 →
    (L \ R).Nonempty → (R \ L).Nonempty →
    (∀ x ∈ L \ R, ∀ y ∈ R \ L,
      1 < dist x y ∧ dist x y < Metric.diam (A : Set ℝ²)) →
    ∃ B : Finset ℝ², IsMinimiser n B ∧ ¬ Congruent A B

/-- The rigid jump case with connectivity after deleting at most one vertex. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², IsMinimiser n A →
    (∀ B ∈ separatedSets (n + 1),
      Metric.diam (A : Set ℝ²) < Metric.diam (B : Set ℝ²)) →
    (∀ X : Finset ℝ², IsMinimiser n X → ∀ p ∈ X, ∀ v : ℝ², v ≠ 0 →
      (∃ q ∈ X, dist p q = 1 ∧ 0 < inner ℝ v (q - p)) ∨
      (∃ r ∈ X, dist p r = Metric.diam (X : Set ℝ²) ∧ inner ℝ v (r - p) ≤ 0)) →
    (∀ a ∈ A, ∀ b ∈ A, ∀ u : ℝ², ‖u‖ = 1 →
      (∀ q ∈ A, inner ℝ q u ≤ inner ℝ a u) → inner ℝ b u = inner ℝ a u →
      dist a b < 2 ∧ (2 < Metric.diam (A : Set ℝ²) →
        dist a b ^ 2 + ((Metric.diam (A : Set ℝ²))⁻¹) ^ 2 ≤ 4)) →
    (∀ L R : Finset ℝ², L ∪ R = A → (L ∩ R).card ≤ 1 →
      (L \ R).Nonempty → (R \ L).Nonempty →
      ∃ x ∈ L \ R, ∃ y ∈ R \ L,
        dist x y = 1 ∨ dist x y = Metric.diam (A : Set ℝ²)) →
    ∃ B : Finset ℝ², IsMinimiser n B ∧ ¬ Congruent A B

theorem main : H1 → H2 → OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1_H2_R1.H2 := by
  intro hAnchor hCore
  unfold H2 at hCore
  unfold OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1_H2_R1.H2
  filter_upwards [hCore] with n hn
  intro A hA hJump hBlocked hSupport
  by_contra hUnique
  apply hUnique
  apply hn A hA hJump hBlocked hSupport
  intro L R hCover hOverlap hLeft hRight
  by_contra hc
  have hCross (x : ℝ²) (hx : x ∈ L \ R) (y : ℝ²) (hy : y ∈ R \ L) :
      1 < dist x y ∧ dist x y < Metric.diam (A : Set ℝ²) := by
    have hxL := (mem_sdiff.mp hx).1
    have hyR := (mem_sdiff.mp hy).1
    have hxA : x ∈ A := by
      rw [← hCover]
      exact mem_union.mpr (Or.inl hxL)
    have hyA : y ∈ A := by
      rw [← hCover]
      exact mem_union.mpr (Or.inr hyR)
    have hne : x ≠ y := fun h => (mem_sdiff.mp hx).2 (h.symm ▸ hyR)
    exact ⟨lt_of_le_of_ne (sep_dist hA.1 hxA hyA hne)
        (fun hd => hc ⟨x, hx, y, hy, Or.inl hd.symm⟩),
      lt_of_le_of_ne (Metric.dist_le_diam_of_mem A.finite_toSet.isBounded hxA hyA)
        (fun hd => hc ⟨x, hx, y, hy, Or.inr hd⟩)⟩
  by_cases hz : (L ∩ R).card = 0
  · have hDisj : Disjoint L R := by
      rw [Finset.disjoint_left]
      intro x hx hy
      have hpos := Finset.card_pos.mpr ⟨x, mem_inter.mpr ⟨hx, hy⟩⟩
      omega
    have hL : L.Nonempty := hLeft.mono sdiff_subset
    have hR : R.Nonempty := hRight.mono sdiff_subset
    have hStrict (x : ℝ²) (hx : x ∈ L) (y : ℝ²) (hy : y ∈ R) :=
      hCross x (mem_sdiff.mpr ⟨hx, fun h => (Finset.disjoint_left.mp hDisj) hx h⟩)
        y (mem_sdiff.mpr ⟨hy, fun h => (Finset.disjoint_left.mp hDisj) h hy⟩)
    exact hUnique (translate_part hA hCover hDisj hL hR hStrict)
  · exact hUnique (hAnchor n A hA L R hCover (by omega) hLeft hRight hCross)

end OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1_H2_R1_H2_R1
