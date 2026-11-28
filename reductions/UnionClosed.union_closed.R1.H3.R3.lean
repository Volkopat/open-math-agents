import OMAReductions.R_UnionClosed_union_closed_R1

/-! The small-family bound of Falgas-Ravry, stated using the number of
distinct nonempty occurrence patterns. The argument uses the union of
all members avoiding a given element, so no relabeling is needed. -/

namespace OMA.R_UnionClosed_union_closed_R1_H3_R3

open Finset

private theorem sup_mem_family {m : ℕ} {A B : Finset (Finset (Fin m))}
    (hA : UnionClosed.IsUnionClosed A) (hBA : B ⊆ A) (hB : B.Nonempty) :
    B.sup id ∈ A := by
  classical
  induction B using Finset.induction_on with
  | empty => simp at hB
  | @insert X B hX ih =>
    have hXA : X ∈ A := hBA (mem_insert_self _ _)
    by_cases hem : B.Nonempty
    · rw [sup_insert]
      exact hA _ hXA _ (ih (subset_trans (subset_insert _ _) hBA) hem)
    · have hB0 := not_nonempty_iff_eq_empty.mp hem
      simpa [hB0] using hXA

private theorem occurrence_bound {m : ℕ} {A : Finset (Finset (Fin m))}
    (hA : UnionClosed.IsUnionClosed A) (hEx : ∃ X ∈ A, X ≠ ∅) :
    ∃ x : Fin m, ((univ.image (fun i : Fin m ↦ A.filter (fun X ↦ i ∈ X))).erase ∅).card ≤
      (A.filter (fun X ↦ x ∈ X)).card := by
  classical
  obtain ⟨X₀, hX₀, hX₀ne⟩ := hEx
  obtain ⟨x₀, hx₀⟩ := nonempty_iff_ne_empty.mpr hX₀ne
  let occ (y : Fin m) := A.filter (fun X ↦ y ∈ X)
  obtain ⟨x, _, hx⟩ := exists_max_image univ (fun y : Fin m ↦ (occ y).card)
    ⟨x₀, mem_univ _⟩
  let S := (univ.image occ).erase ∅
  let avoid (D : Finset (Finset (Fin m))) := (A \ D).sup id
  let send (D : Finset (Finset (Fin m))) := if D = occ x then A.sup id else avoid D
  have hrep (D : Finset (Finset (Fin m))) (hD : D ∈ S) :
      ∃ y : Fin m, D = occ y ∧ D.Nonempty := by
    obtain ⟨hne, him⟩ := mem_erase.mp hD
    obtain ⟨y, _, hy⟩ := mem_image.mp him
    exact ⟨y, hy.symm, nonempty_iff_ne_empty.mpr hne⟩
  have hxnon : (occ x).Nonempty := by
    have hx₀non : (occ x₀).Nonempty := ⟨X₀, mem_filter.mpr ⟨hX₀, hx₀⟩⟩
    exact card_pos.mp ((card_pos.mpr hx₀non).trans_le (hx x₀ (mem_univ _)))
  have hselected (D : Finset (Finset (Fin m))) (hD : D ∈ S) (hne : D ≠ occ x) :
      ∃ X ∈ A \ D, x ∈ X := by
    by_contra! hn
    have hsub : occ x ⊆ D := by
      intro X hX
      obtain ⟨hXA, hxX⟩ := mem_filter.mp hX
      by_contra hXD
      exact hn X (mem_sdiff.mpr ⟨hXA, hXD⟩) hxX
    obtain ⟨y, rfl, _⟩ := hrep D hD
    exact hne (eq_of_subset_of_card_le hsub (hx y (mem_univ _))).symm
  have havoid (y : Fin m) : y ∉ avoid (occ y) := by
    intro h
    obtain ⟨X, hX, hy⟩ := mem_sup.mp h
    obtain ⟨hXA, hn⟩ := mem_sdiff.mp hX
    exact hn (mem_filter.mpr ⟨hXA, hy⟩)
  have hdifferent (D : Finset (Finset (Fin m))) (hD : D ∈ S) : avoid D ≠ A.sup id := by
    obtain ⟨y, rfl, Z, hZ⟩ := hrep D hD
    obtain ⟨hZA, hy⟩ := mem_filter.mp hZ
    intro he
    apply havoid y
    rw [he]
    exact mem_sup.mpr ⟨Z, hZA, hy⟩
  have hrecover (D : Finset (Finset (Fin m))) (hD : D ∈ S)
      (X : Finset (Fin m)) (hX : X ∈ A) : X ∉ D ↔ X ⊆ avoid D := by
    constructor
    · intro hXD
      exact le_sup (f := id) (mem_sdiff.mpr ⟨hX, hXD⟩)
    · obtain ⟨y, rfl, _⟩ := hrep D hD
      intro hsub hXD
      exact havoid y (hsub (mem_filter.mp hXD).2)
  refine ⟨x, card_le_card_of_injOn send ?_ ?_⟩
  · intro D hD
    change D ∈ S at hD
    by_cases h : D = occ x
    · obtain ⟨Y, hY⟩ := hxnon
      obtain ⟨hYA, hxY⟩ := mem_filter.mp hY
      simpa only [send, if_pos h, mem_coe, mem_filter] using
        (show A.sup id ∈ A ∧ x ∈ A.sup id from
          ⟨sup_mem_family hA (Subset.rfl) ⟨Y, hYA⟩, mem_sup.mpr ⟨Y, hYA, hxY⟩⟩)
    · obtain ⟨Y, hY, hxY⟩ := hselected D hD h
      simpa only [send, if_neg h, mem_coe, mem_filter] using
        (show avoid D ∈ A ∧ x ∈ avoid D from
          ⟨sup_mem_family hA sdiff_subset ⟨Y, hY⟩, mem_sup.mpr ⟨Y, hY, hxY⟩⟩)
  · intro D hD E hE hDE
    change D ∈ S at hD
    change E ∈ S at hE
    by_cases hd : D = occ x <;> by_cases he : E = occ x
    · exact hd.trans he.symm
    · exact (hdifferent E hE (by simpa only [send, if_pos hd, if_neg he] using hDE.symm)).elim
    · exact (hdifferent D hD (by simpa only [send, if_pos he, if_neg hd] using hDE)).elim
    · have hev : avoid D = avoid E := by simpa only [send, if_neg hd, if_neg he] using hDE
      ext X
      by_cases hX : X ∈ A
      · have hn : X ∉ D ↔ X ∉ E := by
          rw [hrecover D hD X hX, hrecover E hE X hX, hev]
        simpa only [not_not] using not_congr hn
      · obtain ⟨y, rfl, _⟩ := hrep D hD
        obtain ⟨z, rfl, _⟩ := hrep E hE
        simp [occ, hX]

/-- The case above the small-family threshold with a three-element member. -/
def H1 : Prop :=
  ∀ (m : ℕ) (A : Finset (Finset (Fin m))), A ≠ {∅} →
    UnionClosed.IsUnionClosed A → (∀ X ∈ A, X.card ≠ 1 ∧ X.card ≠ 2) →
    (∃ X ∈ A, X.card = 3) →
    2 * ((univ.image (fun i : Fin m ↦ A.filter (fun X ↦ i ∈ X))).erase ∅).card < A.card →
    ∃ i : Fin m, (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => i ∈ X)).card

/-- The case above the small-family threshold with every nonempty member of size at least four. -/
def H2 : Prop :=
  ∀ (m : ℕ) (A : Finset (Finset (Fin m))), A ≠ {∅} →
    UnionClosed.IsUnionClosed A → (∀ X ∈ A, X.Nonempty → 4 ≤ X.card) →
    (∃ X ∈ A, X ≠ ∅) →
    2 * ((univ.image (fun i : Fin m ↦ A.filter (fun X ↦ i ∈ X))).erase ∅).card < A.card →
    ∃ i : Fin m, (1 / 2 : ℚ) * A.card ≤ (A.filter (fun X => i ∈ X)).card

theorem main : H1 → H2 → OMA.R_UnionClosed_union_closed_R1.H3 := by
  intro h1 h2 m A hne hA hno hEx
  by_cases hsmall : A.card ≤
      2 * ((univ.image (fun i : Fin m ↦ A.filter (fun X ↦ i ∈ X))).erase ∅).card
  · obtain ⟨x, hx⟩ := occurrence_bound hA hEx
    have h : A.card ≤ 2 * (A.filter (fun X ↦ x ∈ X)).card := by omega
    have h' : (A.card : ℚ) ≤ 2 * (A.filter (fun X ↦ x ∈ X)).card := by exact_mod_cast h
    exact ⟨x, by linarith⟩
  · have h : 2 * ((univ.image (fun i : Fin m ↦ A.filter (fun X ↦ i ∈ X))).erase ∅).card <
        A.card := lt_of_not_ge hsmall
    by_cases hthree : ∃ X ∈ A, X.card = 3
    · exact h1 m A hne hA hno hthree h
    · have hlarge : ∀ X ∈ A, X.Nonempty → 4 ≤ X.card := by
        intro X hX hXne
        have hp := card_pos.mpr hXne
        obtain ⟨h1X, h2X⟩ := hno X hX
        have h3X : X.card ≠ 3 := fun hc ↦ hthree ⟨X, hX, hc⟩
        omega
      exact h2 m A hne hA hlarge hEx h

end OMA.R_UnionClosed_union_closed_R1_H3_R3
