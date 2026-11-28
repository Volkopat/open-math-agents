import FormalConjectures.Paper.EisenbudGreenHarris
import Mathlib.Data.Finsupp.Lex
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Proof of the Caviglia-De Stefani theorem for the Eisenbud-Green-Harris conjecture. -/

-- Problem: The Eisenbud-Green-Harris conjecture — caviglia deStefani
-- Upstream: formal-conjectures FormalConjectures/Paper/EisenbudGreenHarris.lean:134 (declaration EisenbudGreenHarris.eisenbud_green_harris.variants.caviglia_deStefani)
-- Credit: @nijv (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace CL
open MvPolynomial Finset
noncomputable def monOfDeg (n e : ℕ) : Finset (Fin n →₀ ℕ) :=
  ((Fintype.piFinset (fun _ : Fin n => Finset.range (e + 1))).image
    Finsupp.equivFunOnFinite.symm).filter (fun u => u.degree = e)
lemma mem_monOfDeg {n e : ℕ} {u : Fin n →₀ ℕ} :
    u ∈ monOfDeg n e ↔ u.degree = e := by
  simp only [monOfDeg, mem_filter, mem_image, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro hdeg
  refine ⟨fun i => u i, fun i => ?_, ?_⟩
  · have hle : u i ≤ ∑ j : Fin n, u j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [← Finsupp.degree_eq_sum, hdeg] at hle
    dsimp only
    omega
  · ext i
    simp
noncomputable def monBox {n : ℕ} (D : Fin n → ℕ) (e : ℕ) : Finset (Fin n →₀ ℕ) :=
  (monOfDeg n e).filter (fun u => ∀ i : Fin n, u i < D i)
lemma mem_monBox {n : ℕ} {D : Fin n → ℕ} {e : ℕ} {u : Fin n →₀ ℕ} :
    u ∈ monBox D e ↔ u.degree = e ∧ ∀ i : Fin n, u i < D i := by
  simp [monBox, mem_monOfDeg]
lemma monBox_subset_monOfDeg {n : ℕ} (D : Fin n → ℕ) (e : ℕ) :
    monBox D e ⊆ monOfDeg n e :=
  Finset.filter_subset _ _
lemma lex_lt_iff {n : ℕ} {u v : Fin n →₀ ℕ} :
    toLex u < toLex v ↔ ∃ i : Fin n, (∀ j < i, u j = v j) ∧ u i < v i :=
  Finsupp.Lex.lt_iff
lemma toLex_add_single_strictMono {n : ℕ} (i : Fin n) :
    StrictMono (fun u : Lex (Fin n →₀ ℕ) => toLex (ofLex u + Finsupp.single i 1)) := by
  intro a b hab
  rw [Finsupp.Lex.lt_iff] at hab ⊢
  obtain ⟨j, hlt, hj⟩ := hab
  refine ⟨j, fun r hr => ?_, ?_⟩
  · simp [hlt r hr]
  · simp only [ofLex_toLex, Finsupp.coe_add, Pi.add_apply]
    omega
noncomputable def shadow {n : ℕ} (M : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) :=
  M.biUnion (fun u => Finset.univ.image (fun i : Fin n => u + Finsupp.single i 1))
lemma mem_shadow {n : ℕ} {M : Finset (Fin n →₀ ℕ)} {v : Fin n →₀ ℕ} :
    v ∈ shadow M ↔ ∃ u ∈ M, ∃ i : Fin n, u + Finsupp.single i 1 = v := by
  simp [shadow]
lemma shadow_subset_monOfDeg {n e : ℕ} {M : Finset (Fin n →₀ ℕ)} (hM : M ⊆ monOfDeg n e) :
    shadow M ⊆ monOfDeg n (e + 1) := by
  intro v hv
  rw [mem_shadow] at hv
  obtain ⟨u, hu, i, rfl⟩ := hv
  rw [mem_monOfDeg, map_add, Finsupp.degree_single, (mem_monOfDeg.mp (hM hu))]
lemma shadow_mono {n : ℕ} {A B : Finset (Fin n →₀ ℕ)} (h : A ⊆ B) :
    shadow A ⊆ shadow B := by
  intro v hv
  rw [mem_shadow] at hv ⊢
  obtain ⟨u, hu, i, rfl⟩ := hv
  exact ⟨u, h hu, i, rfl⟩
noncomputable def shadowBox {n : ℕ} (D : Fin n → ℕ) (M : Finset (Fin n →₀ ℕ)) :
    Finset (Fin n →₀ ℕ) :=
  (shadow M).filter (fun u => ∀ i : Fin n, u i < D i)
lemma mem_shadowBox {n : ℕ} {D : Fin n → ℕ} {M : Finset (Fin n →₀ ℕ)} {v : Fin n →₀ ℕ} :
    v ∈ shadowBox D M ↔ (∃ u ∈ M, ∃ i : Fin n, u + Finsupp.single i 1 = v) ∧ ∀ i, v i < D i := by
  simp [shadowBox, mem_shadow]
lemma shadowBox_subset_monBox {n e : ℕ} {D : Fin n → ℕ} {M : Finset (Fin n →₀ ℕ)}
    (hM : M ⊆ monBox D e) :
    shadowBox D M ⊆ monBox D (e + 1) := by
  intro v hv
  rw [mem_shadowBox] at hv
  obtain ⟨⟨u, hu, i, rfl⟩, hlt⟩ := hv
  rw [mem_monBox]
  exact ⟨by rw [map_add, Finsupp.degree_single, (mem_monBox.mp (hM hu)).1], hlt⟩
lemma shadowBox_mono {n : ℕ} (D : Fin n → ℕ) {A B : Finset (Fin n →₀ ℕ)} (h : A ⊆ B) :
    shadowBox D A ⊆ shadowBox D B := by
  intro v hv
  rw [mem_shadowBox] at hv ⊢
  obtain ⟨⟨u, hu, i, rfl⟩, hlt⟩ := hv
  exact ⟨⟨u, h hu, i, rfl⟩, hlt⟩
lemma shadowBox_empty {n : ℕ} (D : Fin n → ℕ) :
    shadowBox D (∅ : Finset (Fin n →₀ ℕ)) = ∅ := by
  simp [shadowBox, shadow]
lemma sub_single_add_single {n : ℕ} {u : Fin n →₀ ℕ} {s : Fin n} (hs : 1 ≤ u s) :
    (u - Finsupp.single s 1) + Finsupp.single s 1 = u := by
  ext j
  by_cases hj : j = s
  · subst hj; simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_eq_same]; omega
  · simp [Ne.symm hj]
lemma degree_sub_single {n : ℕ} {u : Fin n →₀ ℕ} {s : Fin n} (hs : 1 ≤ u s) :
    (u - Finsupp.single s 1).degree + 1 = u.degree := by
  have h := congrArg Finsupp.degree (sub_single_add_single hs)
  rw [map_add, Finsupp.degree_single] at h
  exact h
def IsLexBox {n : ℕ} (D : Fin n → ℕ) (e : ℕ) (M : Finset (Fin n →₀ ℕ)) : Prop :=
  M ⊆ monBox D e ∧ ∀ u ∈ monBox D e, ∀ v ∈ M, toLex v < toLex u → u ∈ M
noncomputable def lexSegBox {n : ℕ} (D : Fin n → ℕ) (e r : ℕ) : Finset (Fin n →₀ ℕ) :=
  ((((monBox D e).image toLex).sort (· ≤ ·)).reverse.take r).toFinset.image ofLex
lemma lexSegBox_subset_monBox {n : ℕ} (D : Fin n → ℕ) (e r : ℕ) :
    lexSegBox D e r ⊆ monBox D e := by
  intro u hu
  simp only [lexSegBox, mem_image, List.mem_toFinset] at hu
  obtain ⟨x, hx, rfl⟩ := hu
  have hx' : x ∈ ((monBox D e).image toLex).sort (· ≤ ·) :=
    List.mem_reverse.mp (List.mem_of_mem_take hx)
  rw [Finset.mem_sort, mem_image] at hx'
  obtain ⟨w, hw, hw'⟩ := hx'
  have : ofLex x = w := by rw [← hw']; rfl
  rwa [this]
lemma card_lexSegBox {n : ℕ} {D : Fin n → ℕ} {e r : ℕ} (hr : r ≤ (monBox D e).card) :
    (lexSegBox D e r).card = r := by
  have hinj : Function.Injective (ofLex : Lex (Fin n →₀ ℕ) → (Fin n →₀ ℕ)) := fun _ _ h => h
  rw [lexSegBox, Finset.card_image_of_injective _ hinj]
  set l := ((monBox D e).image toLex).sort (· ≤ ·)
  have hnodup : (l.reverse.take r).Nodup :=
    (List.nodup_reverse.mpr (Finset.sort_nodup _ _)).take
  rw [List.toFinset_card_of_nodup hnodup, List.length_take, List.length_reverse]
  have hlen : l.length = (monBox D e).card := by
    rw [Finset.length_sort, Finset.card_image_of_injective _ toLex.injective]
  omega
lemma isLexBox_lexSegBox {n : ℕ} (D : Fin n → ℕ) (e r : ℕ) : IsLexBox D e (lexSegBox D e r) := by
  refine ⟨lexSegBox_subset_monBox D e r, ?_⟩
  intro u hu v hv hlt
  set l := ((monBox D e).image toLex).sort (· ≤ ·)
  have hl_pair : l.reverse.Pairwise (fun a b : Lex (Fin n →₀ ℕ) => b ≤ a) := by
    rw [List.pairwise_reverse]
    exact Finset.pairwise_sort _ _
  simp only [lexSegBox, mem_image, List.mem_toFinset] at hv ⊢
  obtain ⟨vx, hvx, hv_eq⟩ := hv
  have hvx_eq : vx = toLex v := by rw [← hv_eq]; rfl
  rw [hvx_eq] at hvx
  refine ⟨toLex u, ?_, rfl⟩
  have hu_mem : toLex u ∈ l.reverse := by
    rw [List.mem_reverse, Finset.mem_sort, mem_image]
    exact ⟨u, hu, rfl⟩
  obtain ⟨iu, hiu_lt, hiu_eq⟩ := List.getElem_of_mem hu_mem
  obtain ⟨iv, hiv_lt, hiv_eq⟩ := List.getElem_of_mem hvx
  have hiv_lt_min : iv < min r l.reverse.length := by
    simpa [l, List.length_take] using hiv_lt
  have hiv_lt_r : iv < r := lt_of_lt_of_le hiv_lt_min (min_le_left _ _)
  have hiv_lt_len : iv < l.reverse.length := lt_of_lt_of_le hiv_lt_min (min_le_right _ _)
  have hiv_eq' : l.reverse[iv]'hiv_lt_len = toLex v := by
    rw [← hiv_eq, List.getElem_take]
  have hiu_lt_iv : iu < iv := by
    by_contra hge
    push Not at hge
    rcases eq_or_lt_of_le hge with rfl | hgt
    · rw [hiu_eq] at hiv_eq'
      exact lt_irrefl _ (hiv_eq' ▸ hlt)
    · have hle : l.reverse[iu]'hiu_lt ≤ l.reverse[iv]'hiv_lt_len :=
        List.pairwise_iff_getElem.mp hl_pair iv iu hiv_lt_len hiu_lt hgt
      rw [hiu_eq, hiv_eq'] at hle
      exact not_lt_of_ge hle hlt
  have hiu_lt_take : iu < (l.reverse.take r).length := by
    rw [List.length_take]
    exact lt_min (lt_trans hiu_lt_iv hiv_lt_r) hiu_lt
  have hget : (l.reverse.take r)[iu]'hiu_lt_take = toLex u := by
    rw [List.getElem_take, hiu_eq]
  rw [← hget]
  exact List.getElem_mem hiu_lt_take
lemma IsLexBox.total_subset {n e : ℕ} {D : Fin n → ℕ} {A B : Finset (Fin n →₀ ℕ)}
    (hA : IsLexBox D e A) (hB : IsLexBox D e B) : A ⊆ B ∨ B ⊆ A := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨a, haA, haB⟩ := Finset.not_subset.mp h1
  obtain ⟨b, hbB, hbA⟩ := Finset.not_subset.mp h2
  rcases lt_trichotomy (toLex a) (toLex b) with hlt | heq | hgt
  · exact hbA (hA.2 b (hB.1 hbB) a haA hlt)
  · have : a = b := heq
    exact haB (this ▸ hbB)
  · exact haB (hB.2 a (hA.1 haA) b hbB hgt)
lemma IsLexBox.subset_of_card_le {n e : ℕ} {D : Fin n → ℕ} {A B : Finset (Fin n →₀ ℕ)}
    (hA : IsLexBox D e A) (hB : IsLexBox D e B) (hc : A.card ≤ B.card) : A ⊆ B := by
  rcases hA.total_subset hB with h | h
  · exact h
  · exact (Finset.eq_of_subset_of_card_le h hc).symm.subset
lemma IsLexBox.eq_of_card_eq {n e : ℕ} {D : Fin n → ℕ} {A B : Finset (Fin n →₀ ℕ)}
    (hA : IsLexBox D e A) (hB : IsLexBox D e B) (hc : A.card = B.card) : A = B :=
  Finset.Subset.antisymm (hA.subset_of_card_le hB hc.le) (hB.subset_of_card_le hA hc.ge)
lemma IsLexBox.eq_lexSegBox {n e : ℕ} {D : Fin n → ℕ} {A : Finset (Fin n →₀ ℕ)}
    (hA : IsLexBox D e A) :
    A = lexSegBox D e A.card :=
  hA.eq_of_card_eq (isLexBox_lexSegBox D e A.card)
    (card_lexSegBox (Finset.card_le_card hA.1)).symm
lemma IsLexBox.card_union {n e : ℕ} {D : Fin n → ℕ} {A B : Finset (Fin n →₀ ℕ)}
    (hA : IsLexBox D e A) (hB : IsLexBox D e B) :
    (A ∪ B).card = max A.card B.card := by
  rcases hA.total_subset hB with h | h
  · rw [Finset.union_eq_right.mpr h, max_eq_right (Finset.card_le_card h)]
  · rw [Finset.union_eq_left.mpr h, max_eq_left (Finset.card_le_card h)]
lemma IsLexBox.shadowBox {n e : ℕ} {D : Fin n → ℕ} {L : Finset (Fin n →₀ ℕ)}
    (hL : IsLexBox D e L) :
    IsLexBox D (e + 1) (shadowBox D L) := by
  refine ⟨shadowBox_subset_monBox hL.1, ?_⟩
  intro u hu v hv hlt
  rw [mem_shadowBox] at hv ⊢
  obtain ⟨⟨w, hw, r, rfl⟩, _⟩ := hv
  obtain ⟨hdeg_u, hu_box⟩ := mem_monBox.mp hu
  refine ⟨?_, hu_box⟩
  rw [lex_lt_iff] at hlt
  obtain ⟨j, hjeq, hjlt⟩ := hlt
  have hdeg_w : w.degree = e := (mem_monBox.mp (hL.1 hw)).1
  have hsub_box : ∀ s : Fin n, 1 ≤ u s → u - Finsupp.single s 1 ∈ monBox D e := by
    intro s hs
    rw [mem_monBox]
    refine ⟨by have := degree_sub_single hs; omega, fun i => ?_⟩
    have := hu_box i
    simp only [Finsupp.coe_tsub, Pi.sub_apply]
    omega
  by_cases hrj : r < j
  · have hur : 1 ≤ u r := by
      have := hjeq r hrj
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
      omega
    refine ⟨u - Finsupp.single r 1, ?_, r, sub_single_add_single hur⟩
    apply hL.2 _ (hsub_box r hur) w hw
    rw [lex_lt_iff]
    refine ⟨j, fun i hi => ?_, ?_⟩
    · have hi_eq := hjeq i hi
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply] at hi_eq ⊢
      split_ifs at hi_eq ⊢ <;> omega
    · have hne : r ≠ j := ne_of_lt hrj
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_apply, if_neg hne] at hjlt ⊢
      omega
  · push Not at hrj
    have hu_supp : u.support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]
      intro h0
      rw [h0, map_zero] at hdeg_u
      omega
    set s := u.support.max' hu_supp
    have hs_pos : 1 ≤ u s :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Finset.max'_mem _ hu_supp))
    have hj_pos : 0 < u j := lt_of_le_of_lt (Nat.zero_le _) hjlt
    have hjs : j ≤ s :=
      Finset.le_max' _ j (Finsupp.mem_support_iff.mpr (by omega))
    refine ⟨u - Finsupp.single s 1, ?_, s, sub_single_add_single hs_pos⟩
    rcases lt_or_eq_of_le hjs with hlt_js | hjeqs
    · apply hL.2 _ (hsub_box s hs_pos) w hw
      rw [lex_lt_iff]
      refine ⟨j, fun i hi => ?_, ?_⟩
      · have hi_eq := hjeq i hi
        have hri : r ≠ i := ne_of_gt (lt_of_lt_of_le hi hrj)
        have hsi : s ≠ i := ne_of_gt (lt_trans hi hlt_js)
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_apply, if_neg hri, if_neg hsi] at hi_eq ⊢
        omega
      · have hsj : s ≠ j := ne_of_gt hlt_js
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_apply, if_neg hsj] at hjlt ⊢
        omega
    · rw [← hjeqs] at hs_pos ⊢
      set u' : Fin n →₀ ℕ := u - Finsupp.single j 1
      have hu'_box : u' ∈ monBox D e := hsub_box j hs_pos
      have hu'_deg : u'.degree = e := (mem_monBox.mp hu'_box).1
      have hu'_apply : ∀ i : Fin n, u' i = u i - (if j = i then 1 else 0) := fun i => by
        simp [u', Finsupp.single_apply]
      have hlt_w_le : w j ≤ u' j := by
        have h1 := hu'_apply j
        simp only [ite_true] at h1
        simp only [Finsupp.coe_add, Pi.add_apply] at hjlt
        omega
      rcases lt_or_eq_of_le hlt_w_le with hj_strict | hj_eq_w
      · apply hL.2 _ hu'_box w hw
        rw [lex_lt_iff]
        refine ⟨j, fun i hi => ?_, hj_strict⟩
        have hi_eq := hjeq i hi
        have hri : r ≠ i := ne_of_gt (lt_of_lt_of_le hi hrj)
        have hji : j ≠ i := ne_of_gt hi
        have h1 := hu'_apply i
        rw [if_neg hji] at h1
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_neg hri] at hi_eq
        omega
      · have hw_eq : u' = w := by
          have hle_all : ∀ i : Fin n, u' i ≤ w i := by
            intro i
            rcases lt_trichotomy i j with hij | rfl | hij
            · have hi_eq := hjeq i hij
              have hri : r ≠ i := ne_of_gt (lt_of_lt_of_le hij hrj)
              have hji : j ≠ i := ne_of_gt hij
              have h1 := hu'_apply i
              rw [if_neg hji] at h1
              simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_neg hri] at hi_eq
              omega
            · omega
            · have hui0 : u i = 0 := by
                by_contra hne
                have hle : i ≤ s := Finset.le_max' _ i (Finsupp.mem_support_iff.mpr hne)
                rw [← hjeqs] at hle
                exact not_lt_of_ge hle hij
              have h1 := hu'_apply i
              omega
          have hsum_eq : ∑ i : Fin n, u' i = ∑ i : Fin n, w i := by
            rw [← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum, hu'_deg, hdeg_w]
          ext i
          by_contra hne
          have hlt_i : u' i < w i := lt_of_le_of_ne (hle_all i) hne
          have hsum_lt := Finset.sum_lt_sum (fun x _ => hle_all x) ⟨i, Finset.mem_univ i, hlt_i⟩
          omega
        rwa [hw_eq]
noncomputable def deleteCoord {m : ℕ} (i : Fin (m + 1)) (u : Fin (m + 1) →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j : Fin m => u (i.succAbove j))
noncomputable def insertCoord {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ) :
    Fin (m + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (i.insertNth a (fun j : Fin m => w j))
@[simp]
lemma deleteCoord_apply {m : ℕ} (i : Fin (m + 1)) (u : Fin (m + 1) →₀ ℕ) (j : Fin m) :
    deleteCoord i u j = u (i.succAbove j) := by
  simp [deleteCoord]
@[simp]
lemma insertCoord_apply_same {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ) :
    insertCoord i a w i = a := by
  simp [insertCoord]
@[simp]
lemma insertCoord_apply_succAbove {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ) (j : Fin m) :
    insertCoord i a w (i.succAbove j) = w j := by
  simp [insertCoord]
lemma deleteCoord_insertCoord {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ) :
    deleteCoord i (insertCoord i a w) = w := by
  ext j; simp
lemma insertCoord_deleteCoord {m : ℕ} (i : Fin (m + 1)) (u : Fin (m + 1) →₀ ℕ) :
    insertCoord i (u i) (deleteCoord i u) = u := by
  ext k
  by_cases hk : k = i
  · subst hk; simp
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    simp
lemma insertCoord_injective {m : ℕ} (i : Fin (m + 1)) (a : ℕ) :
    Function.Injective (insertCoord i a) := by
  intro w₁ w₂ h
  have := congrArg (deleteCoord i) h
  simpa [deleteCoord_insertCoord] using this
lemma degree_insertCoord {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ) :
    (insertCoord i a w).degree = a + w.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succAbove _ i]
  simp
lemma degree_deleteCoord {m : ℕ} (i : Fin (m + 1)) (u : Fin (m + 1) →₀ ℕ) :
    u i + (deleteCoord i u).degree = u.degree := by
  have := degree_insertCoord i (u i) (deleteCoord i u)
  rw [insertCoord_deleteCoord] at this
  exact this.symm
lemma toLex_insertCoord_lt_iff {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w₁ w₂ : Fin m →₀ ℕ) :
    toLex (insertCoord i a w₁) < toLex (insertCoord i a w₂) ↔ toLex w₁ < toLex w₂ := by
  rw [lex_lt_iff, lex_lt_iff]
  constructor
  · rintro ⟨k, hkeq, hklt⟩
    have hki : k ≠ i := by
      rintro rfl
      simp at hklt
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
    refine ⟨j, fun r hr => ?_, ?_⟩
    · have := hkeq (i.succAbove r) (Fin.succAbove_lt_succAbove_iff.mpr hr)
      simpa using this
    · simpa using hklt
  · rintro ⟨j, hjeq, hjlt⟩
    refine ⟨i.succAbove j, fun k hk => ?_, ?_⟩
    · by_cases hki : k = i
      · subst hki; simp
      · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hki
        simp [hjeq r (Fin.succAbove_lt_succAbove_iff.mp hk)]
    · simpa using hjlt
lemma insertCoord_add_single_same {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ) :
    insertCoord i a w + Finsupp.single i 1 = insertCoord i (a + 1) w := by
  ext k
  by_cases hki : k = i
  · rw [hki]; simp
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
    simp
lemma insertCoord_add_single_succAbove {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (w : Fin m →₀ ℕ)
    (j : Fin m) :
    insertCoord i a w + Finsupp.single (i.succAbove j) 1 =
      insertCoord i a (w + Finsupp.single j 1) := by
  ext k
  by_cases hki : k = i
  · rw [hki]; simp
  · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hki
    by_cases hrj : j = r
    · subst hrj; simp
    · have hne : i.succAbove j ≠ i.succAbove r := fun h => hrj (Fin.succAbove_right_injective h)
      simp [hne, hrj]
def delBound {m : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) : Fin m → ℕ :=
  fun j => D (i.succAbove j)
lemma delBound_mono {m : ℕ} {D : Fin (m + 1) → ℕ} (hD : Monotone D) (i : Fin (m + 1)) :
    Monotone (delBound D i) :=
  fun _ _ h => hD (Fin.succAbove_le_succAbove_iff.mpr h)
lemma delBound_pos {m : ℕ} {D : Fin (m + 1) → ℕ} (hD : ∀ k, 1 ≤ D k) (i : Fin (m + 1)) :
    ∀ j, 1 ≤ delBound D i j :=
  fun j => hD (i.succAbove j)
lemma insertCoord_mem_monBox_iff {m e : ℕ} {D : Fin (m + 1) → ℕ} {i : Fin (m + 1)}
    {a : ℕ} {w : Fin m →₀ ℕ} :
    insertCoord i a w ∈ monBox D e ↔
      a ≤ e ∧ a < D i ∧ w ∈ monBox (delBound D i) (e - a) := by
  rw [mem_monBox, mem_monBox, degree_insertCoord]
  constructor
  · rintro ⟨hdeg, hlt⟩
    refine ⟨by omega, by simpa using hlt i, by omega, fun j => ?_⟩
    simpa [delBound] using hlt (i.succAbove j)
  · rintro ⟨hale, haD, hdeg, hlt⟩
    refine ⟨by omega, fun k => ?_⟩
    by_cases hki : k = i
    · rw [hki]; simpa using haD
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
      simpa [delBound] using hlt j
noncomputable def slice {m : ℕ} (i : Fin (m + 1)) (a : ℕ) (M : Finset (Fin (m + 1) →₀ ℕ)) :
    Finset (Fin m →₀ ℕ) :=
  (M.filter (fun u => u i = a)).image (deleteCoord i)
lemma mem_slice {m : ℕ} {i : Fin (m + 1)} {a : ℕ} {M : Finset (Fin (m + 1) →₀ ℕ)}
    {w : Fin m →₀ ℕ} :
    w ∈ slice i a M ↔ insertCoord i a w ∈ M := by
  simp only [slice, mem_image, mem_filter]
  constructor
  · rintro ⟨u, ⟨hu, rfl⟩, rfl⟩
    rwa [insertCoord_deleteCoord]
  · intro h
    exact ⟨insertCoord i a w, ⟨h, insertCoord_apply_same i a w⟩, deleteCoord_insertCoord i a w⟩
lemma slice_subset_monBox {m e : ℕ} {D : Fin (m + 1) → ℕ} {i : Fin (m + 1)} {a : ℕ}
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e) :
    slice i a M ⊆ monBox (delBound D i) (e - a) := by
  intro w hw
  rw [mem_slice] at hw
  exact (insertCoord_mem_monBox_iff.mp (hM hw)).2.2
lemma slice_empty_of_ge_bound {m e : ℕ} {D : Fin (m + 1) → ℕ} {i : Fin (m + 1)} {a : ℕ}
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e) (ha : D i ≤ a) :
    slice i a M = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  rw [mem_slice] at hw
  have := (insertCoord_mem_monBox_iff.mp (hM hw)).2.1
  omega
lemma card_eq_sum_card_slice {m e : ℕ} (i : Fin (m + 1)) {D : Fin (m + 1) → ℕ}
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e) :
    M.card = ∑ a ∈ Finset.range (e + 1), (slice i a M).card := by
  have hdisj : M = (Finset.range (e + 1)).biUnion (fun a => M.filter (fun u => u i = a)) := by
    ext u
    simp only [mem_biUnion, mem_range, mem_filter]
    constructor
    · intro hu
      refine ⟨u i, ?_, hu, rfl⟩
      have hdeg := (mem_monBox.mp (hM hu)).1
      have hle : u i ≤ u.degree := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    · rintro ⟨_, _, hu, _⟩; exact hu
  conv_lhs => rw [hdisj]
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [slice, Finset.card_image_of_injOn]
    intro u₁ hu₁ u₂ hu₂ heq
    simp only [mem_coe, mem_filter] at hu₁ hu₂
    rw [← insertCoord_deleteCoord i u₁, ← insertCoord_deleteCoord i u₂, hu₁.2, hu₂.2, heq]
  · intro a _ b _ hab
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro u hu₁ hu₂
    simp only [mem_filter] at hu₁ hu₂
    exact hab (hu₁.2.symm.trans hu₂.2)
lemma slice_shadowBox {m e : ℕ} {D : Fin (m + 1) → ℕ} (i : Fin (m + 1)) (a : ℕ)
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e) :
    slice i a (shadowBox D M) =
      if a < D i then
        shadowBox (delBound D i) (slice i a M) ∪ (if 0 < a then slice i (a - 1) M else ∅)
      else ∅ := by
  by_cases haD : a < D i
  · rw [if_pos haD]
    ext w
    simp only [mem_slice, mem_shadowBox, mem_union]
    constructor
    · rintro ⟨⟨u, hu, k, hk⟩, hlt⟩
      have hlt' : ∀ j : Fin m, w j < delBound D i j := fun j => by
        simpa [delBound] using hlt (i.succAbove j)
      by_cases hki : k = i
      · rw [hki] at hk
        right
        have hui : u i + 1 = a := by
          have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f i) hk
          simpa using this
        have ha : 0 < a := by omega
        rw [if_pos ha, mem_slice]
        have hu_eq : insertCoord i (a - 1) w = u := by
          ext r
          by_cases hri : r = i
          · rw [hri]; simp; omega
          · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hri
            have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f (i.succAbove j)) hk
            simpa using this.symm
        rwa [hu_eq]
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
        left
        have hui : u i = a := by
          have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f i) hk
          simpa [Fin.succAbove_ne i j] using this
        refine ⟨⟨deleteCoord i u, ?_, j, ?_⟩, hlt'⟩
        · rw [← hui, insertCoord_deleteCoord]; exact hu
        · ext r
          have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f (i.succAbove r)) hk
          by_cases hrj : j = r
          · subst hrj; simpa using this
          · have hne : i.succAbove j ≠ i.succAbove r :=
              fun h => hrj (Fin.succAbove_right_injective h)
            simpa [hne, hrj] using this
    · rintro (⟨⟨u', hu', j, rfl⟩, hlt'⟩ | hw)
      · refine ⟨⟨insertCoord i a u', hu', i.succAbove j,
          insertCoord_add_single_succAbove i a u' j⟩, fun k => ?_⟩
        by_cases hki : k = i
        · rw [hki]; simpa using haD
        · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hki
          simpa [delBound] using hlt' r
      · split_ifs at hw with ha
        · rw [mem_slice] at hw
          have hbox := (mem_monBox.mp (hM hw)).2
          refine ⟨⟨insertCoord i (a - 1) w, hw, i, ?_⟩, fun k => ?_⟩
          · rw [insertCoord_add_single_same, Nat.sub_add_cancel ha]
          · by_cases hki : k = i
            · rw [hki]; simpa using haD
            · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hki
              simpa using hbox (i.succAbove r)
        · simp at hw
  · rw [if_neg haD, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [mem_slice, mem_shadowBox] at hw
    have := hw.2 i
    simp at this
    omega
def IsCompressedBox {m : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (e : ℕ)
    (M : Finset (Fin (m + 1) →₀ ℕ)) : Prop :=
  ∀ u ∈ monBox D e, ∀ v ∈ M, u i = v i → toLex v < toLex u → u ∈ M
noncomputable def compressBox {m : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (e : ℕ)
    (M : Finset (Fin (m + 1) →₀ ℕ)) : Finset (Fin (m + 1) →₀ ℕ) :=
  (Finset.range (min (e + 1) (D i))).biUnion
    (fun a => (lexSegBox (delBound D i) (e - a) (slice i a M).card).image (insertCoord i a))
lemma mem_compressBox {m : ℕ} {D : Fin (m + 1) → ℕ} {i : Fin (m + 1)} {e : ℕ}
    {M : Finset (Fin (m + 1) →₀ ℕ)} {u : Fin (m + 1) →₀ ℕ} :
    u ∈ compressBox D i e M ↔
      u i ≤ e ∧ u i < D i ∧
        deleteCoord i u ∈ lexSegBox (delBound D i) (e - u i) (slice i (u i) M).card := by
  simp only [compressBox, mem_biUnion, mem_range, mem_image]
  constructor
  · rintro ⟨a, ha, w, hw, rfl⟩
    rw [insertCoord_apply_same, deleteCoord_insertCoord]
    exact ⟨by omega, by omega, hw⟩
  · rintro ⟨hle, hlt, hw⟩
    exact ⟨u i, by omega, deleteCoord i u, hw, insertCoord_deleteCoord i u⟩
lemma slice_compressBox {m : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (e a : ℕ)
    (M : Finset (Fin (m + 1) →₀ ℕ)) (ha : a ≤ e) (haD : a < D i) :
    slice i a (compressBox D i e M) = lexSegBox (delBound D i) (e - a) (slice i a M).card := by
  ext w
  rw [mem_slice, mem_compressBox, insertCoord_apply_same, deleteCoord_insertCoord]
  exact ⟨fun h => h.2.2, fun h => ⟨ha, haD, h⟩⟩
lemma compressBox_subset_monBox {m : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (e : ℕ)
    (M : Finset (Fin (m + 1) →₀ ℕ)) :
    compressBox D i e M ⊆ monBox D e := by
  intro u hu
  rw [mem_compressBox] at hu
  have hw := lexSegBox_subset_monBox (delBound D i) (e - u i) _ hu.2.2
  rw [← insertCoord_deleteCoord i u, insertCoord_mem_monBox_iff]
  exact ⟨hu.1, hu.2.1, hw⟩
lemma card_compressBox {m : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (e : ℕ)
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e) :
    (compressBox D i e M).card = M.card := by
  rw [card_eq_sum_card_slice i (compressBox_subset_monBox D i e M), card_eq_sum_card_slice i hM]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [mem_range] at ha
  by_cases haD : a < D i
  · rw [slice_compressBox D i e a M (by omega) haD]
    exact card_lexSegBox (Finset.card_le_card (slice_subset_monBox hM))
  · push Not at haD
    rw [slice_empty_of_ge_bound (compressBox_subset_monBox D i e M) haD,
      slice_empty_of_ge_bound hM haD]
noncomputable def lexRankBox {n : ℕ} (D : Fin n → ℕ) (e : ℕ) (u : Fin n →₀ ℕ) : ℕ :=
  ((monBox D e).filter (fun w => toLex u < toLex w)).card
lemma lexRankBox_lt_of_lt {n e : ℕ} {D : Fin n → ℕ} {u v : Fin n →₀ ℕ} (hu : u ∈ monBox D e)
    (hlt : toLex v < toLex u) :
    lexRankBox D e u < lexRankBox D e v := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨u, Finset.mem_filter.mpr ⟨hu, hlt⟩, by simp⟩
  · intro w hw
    simp only [mem_filter] at hw ⊢
    exact ⟨hw.1, lt_trans hlt hw.2⟩
noncomputable def lexRankSumBox {n : ℕ} (D : Fin n → ℕ) (e : ℕ) (M : Finset (Fin n →₀ ℕ)) : ℕ :=
  ∑ u ∈ M, lexRankBox D e u
lemma lexRankSumBox_slice_le {m e : ℕ} (D : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (a : ℕ)
    (ha : a ≤ e) (haD : a < D i)
    {S : Finset (Fin m →₀ ℕ)} (hS : S ⊆ monBox (delBound D i) (e - a)) :
    lexRankSumBox D e ((lexSegBox (delBound D i) (e - a) S.card).image (insertCoord i a)) ≤
      lexRankSumBox D e (S.image (insertCoord i a)) ∧
    (lexSegBox (delBound D i) (e - a) S.card ≠ S →
      lexRankSumBox D e ((lexSegBox (delBound D i) (e - a) S.card).image (insertCoord i a)) <
        lexRankSumBox D e (S.image (insertCoord i a))) := by
  set D' := delBound D i
  set L := lexSegBox D' (e - a) S.card
  have hLcard : L.card = S.card := card_lexSegBox (Finset.card_le_card hS)
  have hLsub : L ⊆ monBox D' (e - a) := lexSegBox_subset_monBox D' (e - a) S.card
  have hLlex : IsLexBox D' (e - a) L := isLexBox_lexSegBox D' (e - a) S.card
  have hEq : ∀ A : Finset (Fin m →₀ ℕ),
      lexRankSumBox D e (A.image (insertCoord i a)) =
        ∑ w ∈ A, lexRankBox D e (insertCoord i a w) := fun A => by
    rw [lexRankSumBox, Finset.sum_image (fun x _ y _ h => insertCoord_injective i a h)]
  rw [hEq L, hEq S]
  have hsplit : ∀ A B : Finset (Fin m →₀ ℕ),
      ∑ w ∈ A, lexRankBox D e (insertCoord i a w) =
        (∑ w ∈ A ∩ B, lexRankBox D e (insertCoord i a w)) +
        (∑ w ∈ A \ B, lexRankBox D e (insertCoord i a w)) := fun A B => by
    have hunion : A ∩ B ∪ A \ B = A := by ext x; simp; tauto
    rw [← Finset.sum_union (Finset.disjoint_left.mpr fun x h1 h2 =>
      (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2), hunion]
  rw [hsplit L S, hsplit S L, Finset.inter_comm S L]
  have hdiff_card : (L \ S).card = (S \ L).card := by
    have h1 := Finset.card_sdiff_add_card_inter L S
    have h2 := Finset.card_sdiff_add_card_inter S L
    rw [Finset.inter_comm S L] at h2
    omega
  have hpt : ∀ x ∈ L \ S, ∀ y ∈ S \ L,
      lexRankBox D e (insertCoord i a x) < lexRankBox D e (insertCoord i a y) := by
    intro x hx y hy
    rw [mem_sdiff] at hx hy
    have hlt : toLex y < toLex x := by
      rcases lt_trichotomy (toLex y) (toLex x) with h | heq | h
      · exact h
      · exfalso
        have hyx : y = x := heq
        exact hy.2 (hyx ▸ hx.1)
      · exfalso; exact hy.2 (hLlex.2 y (hS hy.1) x hx.1 h)
    apply lexRankBox_lt_of_lt
    · rw [insertCoord_mem_monBox_iff]; exact ⟨ha, haD, hLsub hx.1⟩
    · exact (toLex_insertCoord_lt_iff i a y x).mpr hlt
  have hlt_or_eq : (L \ S = ∅ ∧ S \ L = ∅) ∨
      ∑ w ∈ L \ S, lexRankBox D e (insertCoord i a w) <
        ∑ w ∈ S \ L, lexRankBox D e (insertCoord i a w) := by
    by_cases hne : (L \ S).Nonempty
    · right
      have hne2 : (S \ L).Nonempty := Finset.card_pos.mp (hdiff_card ▸ hne.card_pos)
      obtain ⟨x₀, hx₀, hx₀_max⟩ :=
        Finset.exists_max_image (L \ S) (fun w => lexRankBox D e (insertCoord i a w)) hne
      obtain ⟨y₀, hy₀, hy₀_min⟩ :=
        Finset.exists_min_image (S \ L) (fun w => lexRankBox D e (insertCoord i a w)) hne2
      have h1 : ∑ w ∈ L \ S, lexRankBox D e (insertCoord i a w) ≤
          (L \ S).card * lexRankBox D e (insertCoord i a x₀) := by
        simpa using Finset.sum_le_card_nsmul (L \ S) _ _ (fun w hw => hx₀_max w hw)
      have h2 : (S \ L).card * lexRankBox D e (insertCoord i a y₀) ≤
          ∑ w ∈ S \ L, lexRankBox D e (insertCoord i a w) := by
        simpa using Finset.card_nsmul_le_sum (S \ L) _ _ (fun w hw => hy₀_min w hw)
      have h3 := hpt x₀ hx₀ y₀ hy₀
      have hpos : 0 < (L \ S).card := hne.card_pos
      rw [hdiff_card] at h1 hpos
      nlinarith
    · left
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine ⟨hne, Finset.card_eq_zero.mp ?_⟩
      rw [← hdiff_card, hne, Finset.card_empty]
  constructor
  · rcases hlt_or_eq with ⟨h1, h2⟩ | hlt
    · simp [h1, h2]
    · omega
  · intro hneq
    rcases hlt_or_eq with ⟨h1, h2⟩ | hlt
    · exfalso
      apply hneq
      exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp h1)
        (Finset.sdiff_eq_empty_iff_subset.mp h2)
    · omega
lemma lexRankSumBox_compressBox_lt {m e : ℕ} {D : Fin (m + 1) → ℕ} (i : Fin (m + 1))
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e) (hnc : ¬ IsCompressedBox D i e M) :
    lexRankSumBox D e (compressBox D i e M) < lexRankSumBox D e M := by
  have hdecomp : ∀ A : Finset (Fin (m + 1) →₀ ℕ), A ⊆ monBox D e →
      lexRankSumBox D e A =
        ∑ a ∈ Finset.range (min (e + 1) (D i)),
          lexRankSumBox D e ((slice i a A).image (insertCoord i a)) := by
    intro A hA
    have hEq : A = (Finset.range (min (e + 1) (D i))).biUnion
        (fun a => (slice i a A).image (insertCoord i a)) := by
      ext u
      simp only [mem_biUnion, mem_range, mem_image, mem_slice]
      constructor
      · intro hu
        obtain ⟨hdeg, hbox⟩ := mem_monBox.mp (hA hu)
        have hle : u i ≤ u.degree := by
          rw [Finsupp.degree_eq_sum]
          exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        have huiD := hbox i
        exact ⟨u i, by omega, deleteCoord i u, by rwa [insertCoord_deleteCoord],
          insertCoord_deleteCoord i u⟩
      · rintro ⟨a, _, w, hw, rfl⟩; exact hw
    conv_lhs => rw [lexRankSumBox, hEq]
    rw [Finset.sum_biUnion]
    · rfl
    · intro a _ b _ hab
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro u hu₁ hu₂
      simp only [mem_image] at hu₁ hu₂
      obtain ⟨w₁, _, rfl⟩ := hu₁
      obtain ⟨w₂, _, heq⟩ := hu₂
      have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f i) heq
      simp at this
      exact hab this.symm
  rw [hdecomp (compressBox D i e M) (compressBox_subset_monBox D i e M), hdecomp M hM]
  have hex : ∃ a ∈ Finset.range (min (e + 1) (D i)),
      lexSegBox (delBound D i) (e - a) (slice i a M).card ≠ slice i a M := by
    unfold IsCompressedBox at hnc
    push Not at hnc
    obtain ⟨u, hu, v, hv, huv_i, hlt, huM⟩ := hnc
    obtain ⟨hdeg_v, hbox_v⟩ := mem_monBox.mp (hM hv)
    have ha : v i ∈ Finset.range (min (e + 1) (D i)) := by
      rw [mem_range]
      have hle : v i ≤ v.degree := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hvD := hbox_v i
      omega
    refine ⟨v i, ha, fun heq => huM ?_⟩
    have hlex : IsLexBox (delBound D i) (e - v i) (slice i (v i) M) :=
      heq ▸ isLexBox_lexSegBox (delBound D i) (e - v i) _
    have hdv : deleteCoord i v ∈ slice i (v i) M := by
      rw [mem_slice, insertCoord_deleteCoord]; exact hv
    have hdu_box : deleteCoord i u ∈ monBox (delBound D i) (e - v i) := by
      have hu' : insertCoord i (v i) (deleteCoord i u) ∈ monBox D e := by
        rw [← huv_i, insertCoord_deleteCoord]; exact hu
      exact (insertCoord_mem_monBox_iff.mp hu').2.2
    have hlt_d : toLex (deleteCoord i v) < toLex (deleteCoord i u) := by
      rw [← toLex_insertCoord_lt_iff i (v i), insertCoord_deleteCoord, ← huv_i,
        insertCoord_deleteCoord]
      exact hlt
    have hdu_mem := hlex.2 (deleteCoord i u) hdu_box (deleteCoord i v) hdv hlt_d
    rw [mem_slice, ← huv_i, insertCoord_deleteCoord] at hdu_mem
    exact hdu_mem
  apply Finset.sum_lt_sum
  · intro a ha
    rw [mem_range] at ha
    rw [slice_compressBox D i e a M (by omega) (by omega)]
    exact (lexRankSumBox_slice_le D i a (by omega) (by omega) (slice_subset_monBox hM)).1
  · obtain ⟨a, ha, hne⟩ := hex
    rw [mem_range] at ha
    refine ⟨a, Finset.mem_range.mpr ha, ?_⟩
    rw [slice_compressBox D i e a M (by omega) (by omega)]
    exact (lexRankSumBox_slice_le D i a (by omega) (by omega) (slice_subset_monBox hM)).2 hne
lemma clements_lindstrom_shadow_two (D : Fin 2 → ℕ) (hD_pos : ∀ i, 1 ≤ D i)
    (hD_mono : Monotone D) (e : ℕ) (M : Finset (Fin 2 →₀ ℕ)) (hM : M ⊆ monBox D e) :
    (shadowBox D (lexSegBox D e M.card)).card ≤ (shadowBox D M).card := by
  have hD01 : D 0 ≤ D 1 := hD_mono (by decide)
  by_cases hD0_one : D 0 = 1
  · have hlex : IsLexBox D e M := by
      refine ⟨hM, fun u hu v hv hlt => ?_⟩
      obtain ⟨hdu, hbu⟩ := mem_monBox.mp hu
      obtain ⟨hdv, hbv⟩ := mem_monBox.mp (hM hv)
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdu hdv
      have hu0 := hbu 0
      have hv0 := hbv 0
      have huv : u = v := Finsupp.ext fun r => by
        fin_cases r
        · change u 0 = v 0; omega
        · change u 1 = v 1; omega
      subst huv
      exact absurd hlt (lt_irrefl _)
    rw [← hlex.eq_lexSegBox]
  · have hD0_ge2 : 2 ≤ D 0 := by have := hD_pos 0; omega
    by_cases hne : M.Nonempty
    · set L := lexSegBox D e M.card
      have hLlex : IsLexBox D e L := isLexBox_lexSegBox D e M.card
      have hLcard : L.card = M.card := card_lexSegBox (Finset.card_le_card hM)
      have hLne : L.Nonempty := Finset.card_pos.mp (hLcard ▸ hne.card_pos)
      by_cases hfull : M = monBox D e
      · have hlex : IsLexBox D e M := ⟨hM, fun u hu _ _ _ => hfull ▸ hu⟩
        rw [show L = M from hlex.eq_lexSegBox.symm]
      · by_cases hsmall : e + 1 < D 0
        ·
          have hbox_eq : ∀ A : Finset (Fin 2 →₀ ℕ), A ⊆ monBox D e → shadowBox D A = shadow A := by
            intro A hA
            ext v
            simp only [mem_shadowBox, mem_shadow, and_iff_left_iff_imp]
            rintro ⟨u, hu, i, rfl⟩ r
            have hdeg := (mem_monBox.mp (hA hu)).1
            have hle : (u + Finsupp.single i 1 : Fin 2 →₀ ℕ) r ≤ (u + Finsupp.single i 1).degree := by
              rw [Finsupp.degree_eq_sum]
              exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
            rw [map_add, Finsupp.degree_single, hdeg] at hle
            have hD : D 0 ≤ D r := hD_mono (Fin.zero_le r)
            omega
          rw [hbox_eq L hLlex.1, hbox_eq M hM]
          obtain ⟨u_min, hu_min, hu_min_le⟩ := Finset.exists_min_image L toLex hLne
          have hsubL : shadow L ⊆
              L.image (· + Finsupp.single 0 1) ∪ {u_min + Finsupp.single 1 1} := by
            intro v hv
            rw [mem_shadow] at hv
            obtain ⟨u, hu, i, rfl⟩ := hv
            fin_cases i
            · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hu)
            · by_cases heq : u = u_min
              · subst heq; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
              · apply Finset.mem_union_left
                rw [mem_image]
                have hlt_u : toLex u_min < toLex u :=
                  lt_of_le_of_ne (hu_min_le u hu) (fun h => heq h.symm)
                have hdu := (mem_monBox.mp (hLlex.1 hu)).1
                have hdm := (mem_monBox.mp (hLlex.1 hu_min)).1
                rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdu hdm
                have hu0_gt : u_min 0 < u 0 := by
                  rw [lex_lt_iff] at hlt_u
                  obtain ⟨j, hjeq, hjlt⟩ := hlt_u
                  fin_cases j
                  · exact hjlt
                  · have h0 := hjeq 0 (by decide)
                    have hjlt' : u_min 1 < u 1 := hjlt
                    omega
                set w := (u - Finsupp.single 0 1) + Finsupp.single 1 1
                have hw0 : w 0 = u 0 - 1 := by simp [w]
                have hw1 : w 1 = u 1 + 1 := by simp [w]
                have hw_box : w ∈ monBox D e := by
                  rw [mem_monBox, Finsupp.degree_eq_sum, Fin.sum_univ_two, hw0, hw1]
                  refine ⟨by omega, fun r => ?_⟩
                  fin_cases r
                  · change w 0 < D 0; omega
                  · change w 1 < D 1; omega
                have hw_ge : toLex u_min ≤ toLex w := by
                  by_cases heq0 : u_min 0 = u 0 - 1
                  · have hweq : w = u_min := by
                      ext r; fin_cases r
                      · change w 0 = u_min 0; omega
                      · change w 1 = u_min 1; omega
                    rw [hweq]
                  · apply le_of_lt
                    rw [lex_lt_iff]
                    exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
                have hw_mem : w ∈ L := by
                  rcases eq_or_lt_of_le hw_ge with h | h
                  · have : u_min = w := h; rwa [← this]
                  · exact hLlex.2 w hw_box u_min hu_min h
                refine ⟨w, hw_mem, ?_⟩
                ext r; fin_cases r
                · simp [hw0]; omega
                · simp [hw1]
          have hcardL : (shadow L).card ≤ M.card + 1 := by
            calc (shadow L).card
                ≤ (L.image (· + Finsupp.single 0 1) ∪ {u_min + Finsupp.single 1 1}).card :=
                  Finset.card_le_card hsubL
              _ ≤ (L.image (· + Finsupp.single 0 1)).card + 1 := Finset.card_union_le _ _
              _ ≤ L.card + 1 := by
                  linarith [Finset.card_image_le (s := L) (f := (· + Finsupp.single 0 1))]
              _ = M.card + 1 := by rw [hLcard]
          obtain ⟨v_min, hv_min, hv_min_le⟩ := Finset.exists_min_image M toLex hne
          have hsubM : insert (v_min + Finsupp.single 1 1) (M.image (· + Finsupp.single 0 1)) ⊆
              shadow M := by
            intro x hx
            rw [mem_insert, mem_image] at hx
            rw [mem_shadow]
            rcases hx with rfl | ⟨u, hu, rfl⟩
            · exact ⟨v_min, hv_min, 1, rfl⟩
            · exact ⟨u, hu, 0, rfl⟩
          have hnotmem : v_min + Finsupp.single 1 1 ∉ M.image (· + Finsupp.single 0 1) := by
            rw [mem_image]
            rintro ⟨w, hw, heq⟩
            have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) heq
            simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
              Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)] at h0
            have hlt_w : toLex w < toLex v_min := by
              rw [lex_lt_iff]
              exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
            exact not_lt_of_ge (hv_min_le w hw) hlt_w
          have hcardM : M.card + 1 ≤ (shadow M).card := by
            calc M.card + 1
                = (M.image (· + Finsupp.single 0 1)).card + 1 := by
                  rw [Finset.card_image_of_injective _ (add_left_injective _)]
              _ = (insert (v_min + Finsupp.single 1 1) (M.image (· + Finsupp.single 0 1))).card := by
                  rw [Finset.card_insert_of_notMem hnotmem]
              _ ≤ (shadow M).card := Finset.card_le_card hsubM
          omega
        ·
          push Not at hsmall
          have hgap_ne : (monBox D e \ M).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hemp
            exact hfull (Finset.Subset.antisymm hM (Finset.sdiff_eq_empty_iff_subset.mp hemp))
          obtain ⟨g, hg⟩ := hgap_ne
          rw [mem_sdiff] at hg
          obtain ⟨hg_box, hg_nM⟩ := hg
          obtain ⟨hg_deg, hg_lt⟩ := mem_monBox.mp hg_box
          rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hg_deg
          let f : (Fin 2 →₀ ℕ) → (Fin 2 →₀ ℕ) := fun u =>
            if g 0 < u 0 then u + Finsupp.single 1 1 else u + Finsupp.single 0 1
          have hf_mem : ∀ u ∈ M, f u ∈ shadowBox D M := by
            intro u hu
            obtain ⟨hu_deg, hu_lt⟩ := mem_monBox.mp (hM hu)
            rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hu_deg
            have hne_g0 : u 0 ≠ g 0 := by
              intro h0
              have hug : u = g := Finsupp.ext fun r => by
                fin_cases r
                · change u 0 = g 0; exact h0
                · change u 1 = g 1; omega
              exact hg_nM (hug ▸ hu)
            rw [mem_shadowBox]
            by_cases hgt : g 0 < u 0
            · simp only [f, if_pos hgt]
              refine ⟨⟨u, hu, 1, rfl⟩, fun r => ?_⟩
              fin_cases r
              · change (u + Finsupp.single 1 1 : Fin 2 →₀ ℕ) 0 < D 0
                have := hu_lt 0; simp; omega
              · change (u + Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 < D 1
                have := hg_lt 1; simp; omega
            · simp only [f, if_neg hgt]
              refine ⟨⟨u, hu, 0, rfl⟩, fun r => ?_⟩
              fin_cases r
              · change (u + Finsupp.single 0 1 : Fin 2 →₀ ℕ) 0 < D 0
                have := hg_lt 0; simp; omega
              · change (u + Finsupp.single 0 1 : Fin 2 →₀ ℕ) 1 < D 1
                have := hu_lt 1; simp; omega
          have hf_inj : Set.InjOn f M := by
            intro u₁ hu₁ u₂ hu₂ heq
            have h0 := congrArg (fun x : Fin 2 →₀ ℕ => x 0) heq
            by_cases h1 : g 0 < u₁ 0 <;> by_cases h2 : g 0 < u₂ 0
            · simp only [f, if_pos h1, if_pos h2] at heq
              exact add_right_cancel heq
            · exfalso
              have hne2 : u₂ 0 ≠ g 0 := by
                intro h
                obtain ⟨hd2, _⟩ := mem_monBox.mp (hM hu₂)
                rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd2
                have : u₂ = g := Finsupp.ext fun r => by
                  fin_cases r
                  · change u₂ 0 = g 0; exact h
                  · change u₂ 1 = g 1; omega
                exact hg_nM (this ▸ hu₂)
              simp only [f, if_pos h1, if_neg h2, Finsupp.coe_add, Pi.add_apply,
                Finsupp.single_eq_same,
                Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)] at h0
              omega
            · exfalso
              have hne1 : u₁ 0 ≠ g 0 := by
                intro h
                obtain ⟨hd1, _⟩ := mem_monBox.mp (hM hu₁)
                rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd1
                have : u₁ = g := Finsupp.ext fun r => by
                  fin_cases r
                  · change u₁ 0 = g 0; exact h
                  · change u₁ 1 = g 1; omega
                exact hg_nM (this ▸ hu₁)
              simp only [f, if_neg h1, if_pos h2, Finsupp.coe_add, Pi.add_apply,
                Finsupp.single_eq_same,
                Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)] at h0
              omega
            · simp only [f, if_neg h1, if_neg h2] at heq
              exact add_right_cancel heq
          have hcardM : M.card ≤ (shadowBox D M).card := by
            calc M.card = (M.image f).card := (Finset.card_image_of_injOn hf_inj).symm
              _ ≤ (shadowBox D M).card := Finset.card_le_card (by
                  intro x hx
                  rw [mem_image] at hx
                  obtain ⟨u, hu, rfl⟩ := hx
                  exact hf_mem u hu)
          obtain ⟨u_max, hu_max, hu_max_ge⟩ := Finset.exists_max_image L toLex hLne
          obtain ⟨u_min, hu_min, hu_min_le⟩ := Finset.exists_min_image L toLex hLne
          have hu_max0 : u_max 0 = D 0 - 1 := by
            obtain ⟨hdm, hbm⟩ := mem_monBox.mp (hLlex.1 hu_max)
            rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdm
            have hbm0 := hbm 0
            by_contra hne0
            have hu_max1_pos : 1 ≤ u_max 1 := by omega
            set w := (u_max - Finsupp.single 1 1) + Finsupp.single 0 1
            have hw0 : w 0 = u_max 0 + 1 := by simp [w]
            have hw1 : w 1 = u_max 1 - 1 := by simp [w]
            have hw_box : w ∈ monBox D e := by
              rw [mem_monBox, Finsupp.degree_eq_sum, Fin.sum_univ_two, hw0, hw1]
              refine ⟨by omega, fun r => ?_⟩
              fin_cases r
              · change w 0 < D 0; omega
              · change w 1 < D 1; have := hbm 1; omega
            have hlt : toLex u_max < toLex w := by
              rw [lex_lt_iff]
              exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
            have hwL : w ∈ L := hLlex.2 w hw_box u_max hu_max hlt
            exact not_lt_of_ge (hu_max_ge w hwL) hlt
          have hsubL : shadowBox D L ⊆
              (L.erase u_max).image (· + Finsupp.single 0 1) ∪ {u_min + Finsupp.single 1 1} := by
            intro v hv
            rw [mem_shadowBox] at hv
            obtain ⟨⟨u, hu, i, rfl⟩, hv_lt⟩ := hv
            fin_cases i
            · apply Finset.mem_union_left
              apply Finset.mem_image_of_mem
              refine Finset.mem_erase.mpr ⟨?_, hu⟩
              rintro rfl
              have := hv_lt 0
              simp at this
              omega
            · by_cases heq : u = u_min
              · subst heq; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
              · apply Finset.mem_union_left
                rw [mem_image]
                have hlt_u : toLex u_min < toLex u :=
                  lt_of_le_of_ne (hu_min_le u hu) (fun h => heq h.symm)
                obtain ⟨hdu, hbu⟩ := mem_monBox.mp (hLlex.1 hu)
                obtain ⟨hdm, hbm⟩ := mem_monBox.mp (hLlex.1 hu_min)
                rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdu hdm
                have hu0_gt : u_min 0 < u 0 := by
                  rw [lex_lt_iff] at hlt_u
                  obtain ⟨j, hjeq, hjlt⟩ := hlt_u
                  fin_cases j
                  · exact hjlt
                  · have h0 := hjeq 0 (by decide)
                    have hjlt' : u_min 1 < u 1 := hjlt
                    omega
                set w := (u - Finsupp.single 0 1) + Finsupp.single 1 1
                have hw0 : w 0 = u 0 - 1 := by simp [w]
                have hw1 : w 1 = u 1 + 1 := by simp [w]
                have hw_box : w ∈ monBox D e := by
                  rw [mem_monBox, Finsupp.degree_eq_sum, Fin.sum_univ_two, hw0, hw1]
                  refine ⟨by omega, fun r => ?_⟩
                  fin_cases r
                  · change w 0 < D 0; have := hbu 0; omega
                  · change w 1 < D 1; have := hbm 1; omega
                have hw_ge : toLex u_min ≤ toLex w := by
                  by_cases heq0 : u_min 0 = u 0 - 1
                  · have hweq : w = u_min := by
                      ext r; fin_cases r
                      · change w 0 = u_min 0; omega
                      · change w 1 = u_min 1; omega
                    rw [hweq]
                  · apply le_of_lt
                    rw [lex_lt_iff]
                    exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
                have hw_mem : w ∈ L := by
                  rcases eq_or_lt_of_le hw_ge with h | h
                  · have : u_min = w := h; rwa [← this]
                  · exact hLlex.2 w hw_box u_min hu_min h
                have hw_ne_max : w ≠ u_max := by
                  intro h
                  have hbu0 := hbu 0
                  have : w 0 = u_max 0 := congrArg (fun x : Fin 2 →₀ ℕ => x 0) h
                  omega
                refine ⟨w, Finset.mem_erase.mpr ⟨hw_ne_max, hw_mem⟩, ?_⟩
                ext r; fin_cases r
                · simp [hw0]; omega
                · simp [hw1]
          have hcardL : (shadowBox D L).card ≤ M.card := by
            calc (shadowBox D L).card
                ≤ ((L.erase u_max).image (· + Finsupp.single 0 1) ∪
                    {u_min + Finsupp.single 1 1}).card := Finset.card_le_card hsubL
              _ ≤ ((L.erase u_max).image (· + Finsupp.single 0 1)).card + 1 :=
                  Finset.card_union_le _ _
              _ ≤ (L.erase u_max).card + 1 := by
                  linarith [Finset.card_image_le (s := L.erase u_max) (f := (· + Finsupp.single 0 1))]
              _ = L.card := by
                  rw [Finset.card_erase_of_mem hu_max]
                  have := hLne.card_pos; omega
              _ = M.card := hLcard
          omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp [lexSegBox, shadowBox, shadow]
lemma max_not_mem_last_pos_box {m e : ℕ} (hm : 2 ≤ m) {D : Fin (m + 1) → ℕ}
    (hD_pos : ∀ i, 1 ≤ D i) {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e)
    (hcomp : ∀ i : Fin (m + 1), IsCompressedBox D i e M)
    {u v : Fin (m + 1) →₀ ℕ} (hu : u ∈ monBox D e) (huM : u ∉ M)
    (hvM : v ∈ M) (hvu : toLex v < toLex u) :
    1 ≤ u (Fin.last m) := by
  have hne_coord : ∀ i : Fin (m + 1), u i ≠ v i := fun i heq =>
    huM (hcomp i u hu v hvM heq hvu)
  have hu0_gt : v 0 < u 0 := by
    rw [lex_lt_iff] at hvu
    obtain ⟨j, hjeq, hjlt⟩ := hvu
    by_cases hj0 : j = 0
    · subst hj0; exact hjlt
    · exfalso
      exact hne_coord 0 (hjeq 0 (Nat.pos_of_ne_zero (fun h => hj0 (Fin.ext h)))).symm
  by_contra h0
  have hu_last : u (Fin.last m) = 0 := by omega
  have hstep : ∀ t : ℕ, ∀ z ∈ M, z 0 = v 0 → z (Fin.last m) = t →
      (∃ z' ∈ M, z' 0 = v 0 ∧ z' (Fin.last m) = 0) ∨
      (∃ z₁ ∈ M, z₁ 0 = v 0 ∧ ∀ i : Fin (m + 1), i ≠ 0 → i ≠ Fin.last m → z₁ i = D i - 1) := by
    intro t
    induction t with
    | zero =>
      intro z hz hz0 hzt
      exact Or.inl ⟨z, hz, hz0, hzt⟩
    | succ t ih =>
      intro z hz hz0 hzt
      by_cases hfull : ∀ i : Fin (m + 1), i ≠ 0 → i ≠ Fin.last m → z i = D i - 1
      · exact Or.inr ⟨z, hz, hz0, hfull⟩
      · push Not at hfull
        obtain ⟨i, hi0, hilast, hzi_ne⟩ := hfull
        obtain ⟨hz_deg, hz_lt⟩ := mem_monBox.mp (hM hz)
        have hzi_lt : z i + 1 < D i := by have := hz_lt i; omega
        set z' : Fin (m + 1) →₀ ℕ := (z - Finsupp.single (Fin.last m) 1) + Finsupp.single i 1
        have hz'_box : z' ∈ monBox D e := by
          rw [mem_monBox]
          refine ⟨?_, fun k => ?_⟩
          · rw [map_add, Finsupp.degree_single]
            have := degree_sub_single (u := z) (s := Fin.last m) (by omega)
            omega
          · rcases eq_or_ne k (Fin.last m) with rfl | hkl
            · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
                Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast.symm]
              have := hz_lt (Fin.last m); omega
            · rcases eq_or_ne k i with rfl | hki
              · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
                  Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast, tsub_zero]
                omega
              · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
                  Finsupp.single_eq_of_ne hkl, Finsupp.single_eq_of_ne hki, tsub_zero, add_zero]
                exact hz_lt k
        have hz'0 : z' 0 = v 0 := by
          have h0l : (0 : Fin (m + 1)) ≠ Fin.last m := by
            intro h; have := congrArg Fin.val h; simp at this; omega
          simp [z', h0l, hi0.symm, hz0]
        have hz_lt_z' : toLex z < toLex z' := by
          rw [lex_lt_iff]
          refine ⟨i, fun r hr => ?_, ?_⟩
          · have hrl : r ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hr (Fin.le_last i))
            have hri : r ≠ i := ne_of_lt hr
            simp [z', hrl, hri]
          · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast, tsub_zero]
            omega
        have hz'M : z' ∈ M := hcomp 0 z' hz'_box z hz (by omega) hz_lt_z'
        have hz'last : z' (Fin.last m) = t := by
          simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast.symm]
          omega
        exact ih z' hz'M hz'0 hz'last
  rcases hstep (v (Fin.last m)) v hvM rfl rfl with ⟨z', hz'M, hz'0, hz'last⟩ | ⟨z₁, hz₁M, hz₁0, hz₁mid⟩
  · have hz'_lt_u : toLex z' < toLex u := by
      rw [lex_lt_iff]
      exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
    exact huM (hcomp (Fin.last m) u hu z' hz'M (by omega) hz'_lt_u)
  · by_cases hz₁l : z₁ (Fin.last m) = 0
    · have hz₁_lt_u : toLex z₁ < toLex u := by
        rw [lex_lt_iff]
        exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
      exact huM (hcomp (Fin.last m) u hu z₁ hz₁M (by omega) hz₁_lt_u)
    · have hz₁l_pos : 1 ≤ z₁ (Fin.last m) := by omega
      obtain ⟨hu_deg, hu_lt⟩ := mem_monBox.mp hu
      obtain ⟨hz₁_deg, hz₁_lt⟩ := mem_monBox.mp (hM hz₁M)
      rw [Finsupp.degree_eq_sum] at hu_deg hz₁_deg
      have h0l : (0 : Fin (m + 1)) ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      set mid := (Finset.univ.erase (0 : Fin (m + 1))).erase (Fin.last m)
      have hsum_split : ∀ x : Fin (m + 1) →₀ ℕ,
          ∑ i : Fin (m + 1), x i = x 0 + x (Fin.last m) + ∑ i ∈ mid, x i := fun x => by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1)))]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h0l.symm, Finset.mem_univ _⟩)]
        ring
      have hmid_le : ∀ i ∈ mid, u i ≤ z₁ i := by
        intro i hi
        rw [mem_erase, mem_erase] at hi
        rw [hz₁mid i hi.2.1 hi.1]
        have := hu_lt i; omega
      have hsum_mid_le : ∑ i ∈ mid, u i ≤ ∑ i ∈ mid, z₁ i :=
        Finset.sum_le_sum hmid_le
      have hsu := hsum_split u
      have hsz := hsum_split z₁
      have hz₁_sum_le : z₁ 0 + z₁ (Fin.last m) ≤ u 0 := by omega
      set z₂ : Fin (m + 1) →₀ ℕ :=
        (z₁ - Finsupp.single (Fin.last m) (z₁ (Fin.last m))) +
          Finsupp.single 0 (z₁ (Fin.last m))
      have hz₂0 : z₂ 0 = z₁ 0 + z₁ (Fin.last m) := by simp [z₂, h0l]
      have hz₂last : z₂ (Fin.last m) = 0 := by simp [z₂, h0l.symm]
      have hz₂mid : ∀ i : Fin (m + 1), i ≠ 0 → i ≠ Fin.last m → z₂ i = z₁ i := fun i h1 h2 => by
        simp [z₂, h1, h2]
      have hz₂_box : z₂ ∈ monBox D e := by
        rw [mem_monBox]
        refine ⟨?_, fun k => ?_⟩
        · rw [Finsupp.degree_eq_sum, hsum_split z₂, hz₂0, hz₂last]
          have hrest : ∑ i ∈ mid, z₂ i = ∑ i ∈ mid, z₁ i :=
            Finset.sum_congr rfl fun i hi => by
              rw [mem_erase, mem_erase] at hi; exact hz₂mid i hi.2.1 hi.1
          omega
        · rcases eq_or_ne k 0 with rfl | hk0
          · rw [hz₂0]; have := hu_lt 0; omega
          · rcases eq_or_ne k (Fin.last m) with rfl | hkl
            · rw [hz₂last]; have := hD_pos (Fin.last m); omega
            · rw [hz₂mid k hk0 hkl]; exact hz₁_lt k
      set c1 : Fin (m + 1) := ⟨1, by omega⟩
      have hc1_0 : c1 ≠ 0 := by intro h; have := congrArg Fin.val h; simp [c1] at this
      have hc1_last : c1 ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp [c1] at this; omega
      have hz₁_lt_z₂ : toLex z₁ < toLex z₂ := by
        rw [lex_lt_iff]
        exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
      have hz₂M : z₂ ∈ M := hcomp c1 z₂ hz₂_box z₁ hz₁M (hz₂mid c1 hc1_0 hc1_last) hz₁_lt_z₂
      rcases lt_or_eq_of_le hz₁_sum_le with hlt0 | heq0
      · have hz₂_lt_u : toLex z₂ < toLex u := by
          rw [lex_lt_iff]
          exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
        exact huM (hcomp (Fin.last m) u hu z₂ hz₂M (by omega) hz₂_lt_u)
      · have hmid_eq : ∀ i ∈ mid, u i = z₁ i := by
          intro i hi
          by_contra hne
          have hlt_i : u i < z₁ i := lt_of_le_of_ne (hmid_le i hi) hne
          have hsum_lt := Finset.sum_lt_sum hmid_le ⟨i, hi, hlt_i⟩
          omega
        have huz₂ : u = z₂ := by
          ext i
          rcases eq_or_ne i 0 with rfl | hi0
          · omega
          · rcases eq_or_ne i (Fin.last m) with rfl | hil
            · omega
            · rw [hz₂mid i hi0 hil]
              exact hmid_eq i (Finset.mem_erase.mpr ⟨hil, Finset.mem_erase.mpr ⟨hi0, Finset.mem_univ i⟩⟩)
        exact huM (huz₂ ▸ hz₂M)
lemma min_mem_last_lt_box {m e : ℕ} (hm : 2 ≤ m) {D : Fin (m + 1) → ℕ}
    {M : Finset (Fin (m + 1) →₀ ℕ)} (hM : M ⊆ monBox D e)
    (hcomp : ∀ i : Fin (m + 1), IsCompressedBox D i e M)
    {u v : Fin (m + 1) →₀ ℕ} (hu : u ∈ monBox D e) (huM : u ∉ M)
    (hvM : v ∈ M) (hvu : toLex v < toLex u) :
    v (Fin.last m) + 1 < D (Fin.last m) := by
  have hne_coord : ∀ i : Fin (m + 1), u i ≠ v i := fun i heq =>
    huM (hcomp i u hu v hvM heq hvu)
  have hu0_gt : v 0 < u 0 := by
    rw [lex_lt_iff] at hvu
    obtain ⟨j, hjeq, hjlt⟩ := hvu
    by_cases hj0 : j = 0
    · subst hj0; exact hjlt
    · exfalso
      exact hne_coord 0 (hjeq 0 (Nat.pos_of_ne_zero (fun h => hj0 (Fin.ext h)))).symm
  obtain ⟨hv_deg, hv_lt⟩ := mem_monBox.mp (hM hvM)
  by_contra hge
  have hv_last : v (Fin.last m) = D (Fin.last m) - 1 := by
    have := hv_lt (Fin.last m); omega
  have hstep : ∀ t : ℕ, ∀ z ∈ monBox D e, z ∉ M → z 0 = u 0 →
      (D (Fin.last m) - 1) - z (Fin.last m) = t →
      (∃ z' ∈ monBox D e, z' ∉ M ∧ z' 0 = u 0 ∧ z' (Fin.last m) = D (Fin.last m) - 1) ∨
      (∃ z₁ ∈ monBox D e, z₁ ∉ M ∧ z₁ 0 = u 0 ∧
        ∀ i : Fin (m + 1), i ≠ 0 → i ≠ Fin.last m → z₁ i = 0) := by
    intro t
    induction t with
    | zero =>
      intro z hz hzM hz0 hzt
      have hzl := (mem_monBox.mp hz).2 (Fin.last m)
      exact Or.inl ⟨z, hz, hzM, hz0, by omega⟩
    | succ t ih =>
      intro z hz hzM hz0 hzt
      by_cases hall0 : ∀ i : Fin (m + 1), i ≠ 0 → i ≠ Fin.last m → z i = 0
      · exact Or.inr ⟨z, hz, hzM, hz0, hall0⟩
      · push Not at hall0
        obtain ⟨i, hi0, hilast, hzi_ne⟩ := hall0
        obtain ⟨hz_deg, hz_lt⟩ := mem_monBox.mp hz
        have hzi_pos : 1 ≤ z i := by omega
        set z' : Fin (m + 1) →₀ ℕ := (z - Finsupp.single i 1) + Finsupp.single (Fin.last m) 1
        have hz'_box : z' ∈ monBox D e := by
          rw [mem_monBox]
          refine ⟨?_, fun k => ?_⟩
          · rw [map_add, Finsupp.degree_single]
            have := degree_sub_single hzi_pos
            omega
          · rcases eq_or_ne k (Fin.last m) with rfl | hkl
            · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
                Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast.symm, tsub_zero]
              have := hz_lt (Fin.last m); omega
            · by_cases hki : k = i
              · rw [hki]
                simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
                  Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast]
                have := hz_lt i; omega
              · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
                  Finsupp.single_eq_of_ne hkl, Finsupp.single_eq_of_ne hki, tsub_zero, add_zero]
                exact hz_lt k
        have hz'0 : z' 0 = u 0 := by
          have h0l : (0 : Fin (m + 1)) ≠ Fin.last m := by
            intro h; have := congrArg Fin.val h; simp at this; omega
          simp [z', h0l, hi0.symm, hz0]
        have hz'_lt_z : toLex z' < toLex z := by
          rw [lex_lt_iff]
          refine ⟨i, fun r hr => ?_, ?_⟩
          · have hrl : r ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hr (Fin.le_last i))
            have hri : r ≠ i := ne_of_lt hr
            simp [z', hrl, hri]
          · simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
              Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast]
            omega
        have hz'M : z' ∉ M := fun hmem => hzM (hcomp 0 z hz z' hmem (by omega) hz'_lt_z)
        have hz't : (D (Fin.last m) - 1) - z' (Fin.last m) = t := by
          simp only [z', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_eq_same, Finsupp.single_eq_of_ne hilast.symm, tsub_zero]
          omega
        exact ih z' hz'_box hz'M hz'0 hz't
  rcases hstep ((D (Fin.last m) - 1) - u (Fin.last m)) u hu huM rfl rfl with
      ⟨z', hz'_box, hz'M, hz'0, hz'last⟩ | ⟨z₁, hz₁_box, hz₁M, hz₁0, hz₁mid⟩
  · have hv_lt_z' : toLex v < toLex z' := by
      rw [lex_lt_iff]
      exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
    exact hz'M (hcomp (Fin.last m) z' hz'_box v hvM (by omega) hv_lt_z')
  · by_cases hz₁l : z₁ (Fin.last m) = D (Fin.last m) - 1
    · have hv_lt_z₁ : toLex v < toLex z₁ := by
        rw [lex_lt_iff]
        exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
      exact hz₁M (hcomp (Fin.last m) z₁ hz₁_box v hvM (by omega) hv_lt_z₁)
    · obtain ⟨hz₁_deg, hz₁_lt⟩ := mem_monBox.mp hz₁_box
      rw [Finsupp.degree_eq_sum] at hv_deg hz₁_deg
      have h0l : (0 : Fin (m + 1)) ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      set mid := (Finset.univ.erase (0 : Fin (m + 1))).erase (Fin.last m)
      have hsum_split : ∀ x : Fin (m + 1) →₀ ℕ,
          ∑ i : Fin (m + 1), x i = x 0 + x (Fin.last m) + ∑ i ∈ mid, x i := fun x => by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1)))]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h0l.symm, Finset.mem_univ _⟩)]
        ring
      have hsum_z₁_mid : ∑ i ∈ mid, z₁ i = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [mem_erase, mem_erase] at hi; exact hz₁mid i hi.2.1 hi.1
      have hsz := hsum_split z₁
      have hsv := hsum_split v
      set δ : ℕ := (D (Fin.last m) - 1) - z₁ (Fin.last m)
      have hδ_pos : 1 ≤ δ := by have := hz₁_lt (Fin.last m); omega
      have hδ_le : δ ≤ z₁ 0 - v 0 := by omega
      set z₂ : Fin (m + 1) →₀ ℕ :=
        (z₁ - Finsupp.single 0 δ) + Finsupp.single (Fin.last m) δ
      have hz₂0 : z₂ 0 = z₁ 0 - δ := by simp [z₂, h0l]
      have hz₂last : z₂ (Fin.last m) = D (Fin.last m) - 1 := by
        simp only [z₂, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_eq_same, Finsupp.single_eq_of_ne h0l.symm, tsub_zero]
        have := hz₁_lt (Fin.last m); omega
      have hz₂mid : ∀ i : Fin (m + 1), i ≠ 0 → i ≠ Fin.last m → z₂ i = 0 := fun i h1 h2 => by
        simp [z₂, h1, h2, hz₁mid i h1 h2]
      have hz₂_box : z₂ ∈ monBox D e := by
        rw [mem_monBox]
        refine ⟨?_, fun k => ?_⟩
        · rw [Finsupp.degree_eq_sum, hsum_split z₂, hz₂0, hz₂last]
          have hrest : ∑ i ∈ mid, z₂ i = 0 :=
            Finset.sum_eq_zero fun i hi => by
              rw [mem_erase, mem_erase] at hi; exact hz₂mid i hi.2.1 hi.1
          omega
        · rcases eq_or_ne k 0 with rfl | hk0
          · rw [hz₂0]; have := hz₁_lt 0; omega
          · rcases eq_or_ne k (Fin.last m) with rfl | hkl
            · rw [hz₂last]; have := hv_lt (Fin.last m); omega
            · rw [hz₂mid k hk0 hkl]; exact hz₁_lt k |> fun h => by omega
      set c1 : Fin (m + 1) := ⟨1, by omega⟩
      have hc1_0 : c1 ≠ 0 := by intro h; have := congrArg Fin.val h; simp [c1] at this
      have hc1_last : c1 ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp [c1] at this; omega
      have hz₂_lt_z₁ : toLex z₂ < toLex z₁ := by
        rw [lex_lt_iff]
        exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by omega⟩
      have hz₂M : z₂ ∉ M := fun hmem =>
        hz₁M (hcomp c1 z₁ hz₁_box z₂ hmem (by rw [hz₁mid c1 hc1_0 hc1_last, hz₂mid c1 hc1_0 hc1_last]) hz₂_lt_z₁)
      have hv_le_z₂0 : v 0 ≤ z₂ 0 := by omega
      rcases lt_or_eq_of_le hv_le_z₂0 with hlt0 | heq0
      · have hv_lt_z₂ : toLex v < toLex z₂ := by
          rw [lex_lt_iff]
          exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), hlt0⟩
        exact hz₂M (hcomp (Fin.last m) z₂ hz₂_box v hvM (by omega) hv_lt_z₂)
      · have hsum_v_mid : ∑ i ∈ mid, v i = 0 := by omega
        have hv_mid0 : ∀ i ∈ mid, v i = 0 := fun i hi =>
          (Finset.sum_eq_zero_iff.mp hsum_v_mid) i hi
        have hvz₂ : v = z₂ := by
          ext i
          rcases eq_or_ne i 0 with rfl | hi0
          · omega
          · rcases eq_or_ne i (Fin.last m) with rfl | hil
            · omega
            · rw [hz₂mid i hi0 hil]
              exact hv_mid0 i (Finset.mem_erase.mpr ⟨hil, Finset.mem_erase.mpr ⟨hi0, Finset.mem_univ i⟩⟩)
        exact hz₂M (hvz₂ ▸ hvM)
theorem clements_lindstrom_shadow (n : ℕ) :
    ∀ (D : Fin n → ℕ), (∀ i, 1 ≤ D i) → Monotone D →
      ∀ (e : ℕ) (M : Finset (Fin n →₀ ℕ)), M ⊆ monBox D e →
        (shadowBox D (lexSegBox D e M.card)).card ≤ (shadowBox D M).card := by
  induction n with
  | zero =>
    intro D _ _ e M hM
    have hlex : IsLexBox D e M := by
      refine ⟨hM, fun u _ v _ hlt => ?_⟩
      rw [lex_lt_iff] at hlt
      obtain ⟨i, _⟩ := hlt
      exact Fin.elim0 i
    rw [← hlex.eq_lexSegBox]
  | succ m ih =>
    cases m with
    | zero =>
      intro D _ _ e M hM
      have hlex : IsLexBox D e M := by
        refine ⟨hM, fun u hu v hv hlt => ?_⟩
        have hdu := (mem_monBox.mp hu).1
        have hdv := (mem_monBox.mp (hM hv)).1
        rw [Finsupp.degree_eq_sum, Fin.sum_univ_one] at hdu hdv
        have huv : u = v := Finsupp.ext fun i => by fin_cases i; change u 0 = v 0; omega
        subst huv
        exact absurd hlt (lt_irrefl _)
      rw [← hlex.eq_lexSegBox]
    | succ m' =>
      cases m' with
      | zero => exact clements_lindstrom_shadow_two
      | succ k =>
        set m := k + 2
        have hm : 2 ≤ m := by omega
        intro D hD_pos hD_mono e M hM
        suffices hmain : ∀ r (M : Finset (Fin (m + 1) →₀ ℕ)),
            M ⊆ monBox D e → lexRankSumBox D e M = r →
            (shadowBox D (lexSegBox D e M.card)).card ≤ (shadowBox D M).card by
          exact hmain _ M hM rfl
        intro r
        induction r using Nat.strong_induction_on with
        | _ r ihr =>
          intro M hM hr
          by_cases hlex : IsLexBox D e M
          · rw [← hlex.eq_lexSegBox]
          · by_cases hall : ∀ i : Fin (m + 1), IsCompressedBox D i e M
            · have hMne : M.Nonempty := by
                by_contra hemp
                rw [Finset.not_nonempty_iff_eq_empty] at hemp
                subst hemp
                exact hlex ⟨Finset.empty_subset _, fun _ _ _ hv _ => absurd hv (by simp)⟩
              have hCne : (monBox D e \ M).Nonempty := by
                by_contra hemp
                rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
                have heq : M = monBox D e := Finset.Subset.antisymm hM hemp
                exact hlex ⟨hM, fun u hu _ _ _ => heq ▸ hu⟩
              obtain ⟨u, huC, hu_max⟩ := Finset.exists_max_image _ toLex hCne
              obtain ⟨v, hvM, hv_min⟩ := Finset.exists_min_image _ toLex hMne
              rw [mem_sdiff] at huC
              obtain ⟨hu_box, hu_nM⟩ := huC
              have hvu' : toLex v < toLex u := by
                by_contra hle
                push Not at hle
                apply hlex
                refine ⟨hM, fun x hx y hy hlt => ?_⟩
                by_contra hxM
                have h1 : toLex x ≤ toLex u := hu_max x (mem_sdiff.mpr ⟨hx, hxM⟩)
                have h2 : toLex v ≤ toLex y := hv_min y hy
                exact not_lt_of_ge (le_trans h1 hle) (lt_of_le_of_lt h2 hlt)
              have hu_last : 1 ≤ u (Fin.last m) :=
                max_not_mem_last_pos_box hm hD_pos hM hall hu_box hu_nM hvM hvu'
              have hv_last_lt : v (Fin.last m) + 1 < D (Fin.last m) :=
                min_mem_last_lt_box hm hM hall hu_box hu_nM hvM hvu'
              set M₀ := M.erase v
              set M' := insert u M₀
              have huM₀ : u ∉ M₀ := fun h => hu_nM (Finset.mem_of_mem_erase h)
              have hM'sub : M' ⊆ monBox D e := by
                intro x hx
                rw [mem_insert] at hx
                rcases hx with rfl | hx
                · exact hu_box
                · exact hM (Finset.mem_of_mem_erase hx)
              have hM'card : M'.card = M.card := by
                rw [Finset.card_insert_of_notMem huM₀, Finset.card_erase_of_mem hvM]
                have := hMne.card_pos; omega
              have hrank_lt : lexRankSumBox D e M' < r := by
                rw [← hr, lexRankSumBox, lexRankSumBox, Finset.sum_insert huM₀]
                have hsumM : lexRankBox D e v + ∑ x ∈ M₀, lexRankBox D e x =
                    ∑ x ∈ M, lexRankBox D e x :=
                  Finset.add_sum_erase M (lexRankBox D e) hvM
                have hlt_rk := lexRankBox_lt_of_lt hu_box hvu'
                omega
              have hshadow_le : (shadowBox D M').card ≤ (shadowBox D M).card := by
                have hsub_u : shadowBox D M' \ shadowBox D M₀ ⊆
                    {u + Finsupp.single (Fin.last m) 1} := by
                  intro x hx
                  rw [mem_sdiff, mem_shadowBox] at hx
                  obtain ⟨⟨⟨a, ha, j, rfl⟩, ha_lt⟩, hx0⟩ := hx
                  rw [mem_insert] at ha
                  rcases ha with ha_eq | ha0
                  · rw [ha_eq] at hx0 ha_lt ⊢
                    rw [mem_singleton]
                    by_cases hj : j = Fin.last m
                    · subst hj; rfl
                    · exfalso
                      have hj_lt : j < Fin.last m := lt_of_le_of_ne (Fin.le_last j) hj
                      set w := (u - Finsupp.single (Fin.last m) 1) + Finsupp.single j 1
                      have hw_box : w ∈ monBox D e := by
                        rw [mem_monBox]
                        refine ⟨?_, fun t => ?_⟩
                        · rw [map_add, Finsupp.degree_single]
                          have := degree_sub_single hu_last
                          have hdu := (mem_monBox.mp hu_box).1
                          omega
                        · rcases eq_or_ne t (Fin.last m) with rfl | ht1
                          · simp only [w, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
                              Pi.sub_apply, Finsupp.single_eq_same,
                              Finsupp.single_eq_of_ne (Ne.symm hj)]
                            have := (mem_monBox.mp hu_box).2 (Fin.last m); omega
                          · by_cases ht2 : t = j
                            · rw [ht2]
                              simp only [w, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
                                Pi.sub_apply, Finsupp.single_eq_same,
                                Finsupp.single_eq_of_ne hj, tsub_zero]
                              have := ha_lt j
                              simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
                              exact this
                            · simp only [w, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
                                Pi.sub_apply, Finsupp.single_eq_of_ne ht1,
                                Finsupp.single_eq_of_ne ht2, tsub_zero, add_zero]
                              exact (mem_monBox.mp hu_box).2 t
                      have hu_lt_w : toLex u < toLex w := by
                        rw [lex_lt_iff]
                        refine ⟨j, fun r hr => ?_, ?_⟩
                        · have h1 : Fin.last m ≠ r := ne_of_gt (lt_trans hr hj_lt)
                          have h2 : j ≠ r := ne_of_gt hr
                          simp [w, h1, h2]
                        · simp only [w, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
                            Pi.sub_apply, Finsupp.single_eq_same,
                            Finsupp.single_eq_of_ne hj, tsub_zero]
                          omega
                      have hwM : w ∈ M := by
                        by_contra hw_nM
                        exact not_lt_of_ge (hu_max w (mem_sdiff.mpr ⟨hw_box, hw_nM⟩)) hu_lt_w
                      have hwM₀ : w ∈ M₀ := Finset.mem_erase.mpr
                        ⟨fun heq => not_lt_of_ge (le_of_lt hvu') (heq ▸ hu_lt_w), hwM⟩
                      have heq_add : w + Finsupp.single (Fin.last m) 1 = u + Finsupp.single j 1 := by
                        ext t
                        rcases eq_or_ne t (Fin.last m) with rfl | ht1
                        · simp only [w, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
                            Pi.sub_apply, Finsupp.single_eq_same,
                            Finsupp.single_eq_of_ne (Ne.symm hj)]
                          omega
                        · rcases eq_or_ne t j with rfl | ht2
                          · simp [w, ht1]
                          · simp [w, ht1, ht2]
                      exact hx0 (mem_shadowBox.mpr ⟨⟨w, hwM₀, Fin.last m, heq_add⟩, ha_lt⟩)
                  · exact absurd (mem_shadowBox.mpr ⟨⟨a, ha0, j, rfl⟩, ha_lt⟩) hx0
                have hv_lost : v + Finsupp.single (Fin.last m) 1 ∈
                    shadowBox D M \ shadowBox D M₀ := by
                  rw [mem_sdiff]
                  refine ⟨mem_shadowBox.mpr ⟨⟨v, hvM, Fin.last m, rfl⟩, fun t => ?_⟩, ?_⟩
                  · rcases eq_or_ne t (Fin.last m) with rfl | ht
                    · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
                      exact hv_last_lt
                    · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne ht, add_zero]
                      exact (mem_monBox.mp (hM hvM)).2 t
                  · rw [mem_shadowBox]
                    rintro ⟨⟨w, hw0, j, heq⟩, _⟩
                    have hwM := Finset.mem_of_mem_erase hw0
                    have hwne : w ≠ v := (Finset.mem_erase.mp hw0).1
                    by_cases hj : j = Fin.last m
                    · subst hj
                      exact hwne (add_right_cancel heq)
                    · have hj_lt : j < Fin.last m := lt_of_le_of_ne (Fin.le_last j) hj
                      have hw_lt_v : toLex w < toLex v := by
                        rw [lex_lt_iff]
                        refine ⟨j, fun r hr => ?_, ?_⟩
                        · have h1 : r ≠ Fin.last m := ne_of_lt (lt_trans hr hj_lt)
                          have h2 : r ≠ j := ne_of_lt hr
                          have h := congrArg (fun f : Fin (m + 1) →₀ ℕ => f r) heq
                          simp only [Finsupp.coe_add, Pi.add_apply,
                            Finsupp.single_eq_of_ne h1, Finsupp.single_eq_of_ne h2] at h
                          omega
                        · have h := congrArg (fun f : Fin (m + 1) →₀ ℕ => f j) heq
                          simp only [Finsupp.coe_add, Pi.add_apply,
                            Finsupp.single_eq_same, Finsupp.single_eq_of_ne hj] at h
                          omega
                      exact not_lt_of_ge (hv_min w hwM) hw_lt_v
                have hM₀_sub_M : shadowBox D M₀ ⊆ shadowBox D M :=
                  shadowBox_mono D (Finset.erase_subset v M)
                have hM₀_sub_M' : shadowBox D M₀ ⊆ shadowBox D M' :=
                  shadowBox_mono D (Finset.subset_insert u M₀)
                have hc1 := Finset.card_sdiff_add_card_eq_card hM₀_sub_M'
                have hc2 := Finset.card_sdiff_add_card_eq_card hM₀_sub_M
                have hle1 : (shadowBox D M' \ shadowBox D M₀).card ≤ 1 :=
                  (Finset.card_le_card hsub_u).trans (by simp)
                have hge1 : 1 ≤ (shadowBox D M \ shadowBox D M₀).card :=
                  Finset.one_le_card.mpr ⟨_, hv_lost⟩
                omega
              calc (shadowBox D (lexSegBox D e M.card)).card
                  = (shadowBox D (lexSegBox D e M'.card)).card := by rw [hM'card]
                _ ≤ (shadowBox D M').card := ihr _ hrank_lt M' hM'sub rfl
                _ ≤ (shadowBox D M).card := hshadow_le
            · push Not at hall
              obtain ⟨i, hni⟩ := hall
              set C := compressBox D i e M
              have hCsub : C ⊆ monBox D e := compressBox_subset_monBox D i e M
              have hCcard : C.card = M.card := card_compressBox D i e hM
              have hrank_lt : lexRankSumBox D e C < r :=
                hr ▸ lexRankSumBox_compressBox_lt i hM hni
              have hshadow_le : (shadowBox D C).card ≤ (shadowBox D M).card := by
                rw [card_eq_sum_card_slice i (shadowBox_subset_monBox hCsub),
                    card_eq_sum_card_slice i (shadowBox_subset_monBox hM)]
                refine Finset.sum_le_sum fun a ha => ?_
                rw [mem_range] at ha
                rw [slice_shadowBox i a hCsub, slice_shadowBox i a hM]
                by_cases haD : a < D i
                · rw [if_pos haD, if_pos haD]
                  by_cases hae : a ≤ e
                  · rw [slice_compressBox D i e a M hae haD]
                    have hlex1 : IsLexBox (delBound D i) (e - a + 1)
                        (shadowBox (delBound D i) (lexSegBox (delBound D i) (e - a) (slice i a M).card)) :=
                      (isLexBox_lexSegBox (delBound D i) (e - a) _).shadowBox
                    by_cases ha0 : 0 < a
                    · rw [if_pos ha0, if_pos ha0,
                        slice_compressBox D i e (a - 1) M (by omega) (by omega)]
                      have hdeg_eq : e - a + 1 = e - (a - 1) := by omega
                      have hlex2 : IsLexBox (delBound D i) (e - a + 1)
                          (lexSegBox (delBound D i) (e - (a - 1)) (slice i (a - 1) M).card) := by
                        rw [hdeg_eq]; exact isLexBox_lexSegBox (delBound D i) (e - (a - 1)) _
                      rw [hlex1.card_union hlex2]
                      apply max_le
                      · calc (shadowBox (delBound D i) (lexSegBox (delBound D i) (e - a) (slice i a M).card)).card
                            ≤ (shadowBox (delBound D i) (slice i a M)).card :=
                              ih (delBound D i) (delBound_pos hD_pos i) (delBound_mono hD_mono i)
                                (e - a) (slice i a M) (slice_subset_monBox hM)
                          _ ≤ (shadowBox (delBound D i) (slice i a M) ∪ slice i (a - 1) M).card :=
                              Finset.card_le_card Finset.subset_union_left
                      · rw [card_lexSegBox (Finset.card_le_card (slice_subset_monBox hM))]
                        exact Finset.card_le_card Finset.subset_union_right
                    · rw [if_neg ha0, if_neg ha0, Finset.union_empty, Finset.union_empty]
                      exact ih (delBound D i) (delBound_pos hD_pos i) (delBound_mono hD_mono i)
                        (e - a) (slice i a M) (slice_subset_monBox hM)
                  · have ha_eq : a = e + 1 := by omega
                    subst ha_eq
                    have hsc0 : slice i (e + 1) C = ∅ := by
                      rw [Finset.eq_empty_iff_forall_notMem]
                      intro w hw
                      rw [mem_slice] at hw
                      have hdeg := (mem_monBox.mp (hCsub hw)).1
                      rw [degree_insertCoord] at hdeg
                      omega
                    have hsm0 : slice i (e + 1) M = ∅ := by
                      rw [Finset.eq_empty_iff_forall_notMem]
                      intro w hw
                      rw [mem_slice] at hw
                      have hdeg := (mem_monBox.mp (hM hw)).1
                      rw [degree_insertCoord] at hdeg
                      omega
                    simp only [hsc0, hsm0, shadowBox_empty, Finset.empty_union,
                      Nat.zero_lt_succ, ↓reduceIte, Nat.add_sub_cancel]
                    rw [slice_compressBox D i e e M le_rfl (by omega)]
                    rw [card_lexSegBox (Finset.card_le_card (slice_subset_monBox hM))]
                · rw [if_neg haD, if_neg haD]
              calc (shadowBox D (lexSegBox D e M.card)).card
                  = (shadowBox D (lexSegBox D e C.card)).card := by rw [hCcard]
                _ ≤ (shadowBox D C).card := ihr _ hrank_lt C hCsub rfl
                _ ≤ (shadowBox D M).card := hshadow_le
section IdealPart
variable {n : ℕ} {k : Type*} [Field k]
noncomputable def lm (f : MvPolynomial (Fin n) k) (hf : f ≠ 0) : Fin n →₀ ℕ :=
  ofLex ((f.support.image toLex).max' ((f.support_nonempty.mpr hf).image toLex))
lemma lm_mem_support {f : MvPolynomial (Fin n) k} (hf : f ≠ 0) : lm f hf ∈ f.support := by
  have hmem := Finset.max'_mem (f.support.image toLex) ((f.support_nonempty.mpr hf).image toLex)
  rw [mem_image] at hmem
  obtain ⟨u, hu, heq⟩ := hmem
  have : lm f hf = u := by simp only [lm, ← heq]; rfl
  rwa [this]
lemma coeff_lm_ne_zero {f : MvPolynomial (Fin n) k} (hf : f ≠ 0) : coeff (lm f hf) f ≠ 0 :=
  mem_support_iff.mp (lm_mem_support hf)
lemma le_lm {f : MvPolynomial (Fin n) k} (hf : f ≠ 0) {u : Fin n →₀ ℕ} (hu : u ∈ f.support) :
    toLex u ≤ toLex (lm f hf) :=
  Finset.le_max' (f.support.image toLex) (toLex u) (Finset.mem_image_of_mem toLex hu)
lemma coeff_eq_zero_of_lm_lt {f : MvPolynomial (Fin n) k} (hf : f ≠ 0) {u : Fin n →₀ ℕ}
    (hlt : toLex (lm f hf) < toLex u) : coeff u f = 0 := by
  by_contra hne
  exact not_lt_of_ge (le_lm hf (mem_support_iff.mpr hne)) hlt
lemma support_X_mul (i : Fin n) (f : MvPolynomial (Fin n) k) :
    (X i * f).support = f.support.image (· + Finsupp.single i 1) := by
  ext d
  simp only [mem_support_iff, mem_image]
  have hcoeff : coeff d (X i * f) =
      if 1 ≤ d i then coeff (d - Finsupp.single i 1) f else 0 := by
    rw [X, coeff_monomial_mul']
    by_cases hle : Finsupp.single i 1 ≤ d
    · have h1 : 1 ≤ d i := by have := hle i; simpa using this
      rw [if_pos hle, if_pos h1, one_mul]
    · have h0 : ¬ 1 ≤ d i := by
        intro h1; apply hle; intro j
        by_cases hj : j = i
        · subst hj; simpa using h1
        · simp [Ne.symm hj]
      rw [if_neg hle, if_neg h0]
  rw [hcoeff]
  constructor
  · intro hne
    split_ifs at hne with h1
    · exact ⟨d - Finsupp.single i 1, hne, sub_single_add_single h1⟩
    · exact absurd rfl hne
  · rintro ⟨u, hu, rfl⟩
    have h1 : 1 ≤ (u + Finsupp.single i 1 : Fin n →₀ ℕ) i := by simp
    rw [if_pos h1]
    have hsub : u + Finsupp.single i 1 - Finsupp.single i 1 = u := add_tsub_cancel_right u _
    rwa [hsub]
lemma lm_X_mul (i : Fin n) {f : MvPolynomial (Fin n) k} (hf : f ≠ 0) (hxf : X i * f ≠ 0) :
    lm (X i * f) hxf = lm f hf + Finsupp.single i 1 := by
  apply toLex.injective
  apply le_antisymm
  · have hmem := lm_mem_support hxf
    rw [support_X_mul, mem_image] at hmem
    obtain ⟨u, hu, heq⟩ := hmem
    rw [← heq]
    exact (toLex_add_single_strictMono i).monotone (le_lm hf hu)
  · apply le_lm hxf
    rw [support_X_mul]
    exact Finset.mem_image_of_mem _ (lm_mem_support hf)
lemma weight_one_eq_degree (u : Fin n →₀ ℕ) : Finsupp.weight (1 : Fin n → ℕ) u = u.degree := by
  simp [Finsupp.weight_apply, Finsupp.degree_eq_sum, Finsupp.sum_fintype]
noncomputable def idealPiece (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    Submodule k (MvPolynomial (Fin n) k) :=
  Submodule.restrictScalars k I ⊓ homogeneousSubmodule (Fin n) k e
open Classical in
noncomputable def initMons (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    Finset (Fin n →₀ ℕ) :=
  (monOfDeg n e).filter (fun u => ∃ f ∈ idealPiece I e, ∃ hf : f ≠ 0, lm f hf = u)
lemma mem_initMons {I : Ideal (MvPolynomial (Fin n) k)} {e : ℕ} {u : Fin n →₀ ℕ} :
    u ∈ initMons I e ↔ u ∈ monOfDeg n e ∧ ∃ f ∈ idealPiece I e, ∃ hf : f ≠ 0, lm f hf = u := by
  classical
  simp [initMons]
lemma initMons_subset (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    initMons I e ⊆ monOfDeg n e := fun _ hu => (mem_initMons.mp hu).1
lemma shadow_initMons_subset (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    shadow (initMons I e) ⊆ initMons I (e + 1) := by
  intro v hv
  rw [mem_shadow] at hv
  obtain ⟨u, hu, i, rfl⟩ := hv
  rw [mem_initMons] at hu ⊢
  obtain ⟨hu_deg, f, hfI, hf0, rfl⟩ := hu
  refine ⟨shadow_subset_monOfDeg (initMons_subset I e)
    (mem_shadow.mpr ⟨lm f hf0, mem_initMons.mpr ⟨hu_deg, f, hfI, hf0, rfl⟩, i, rfl⟩), ?_⟩
  have hxf_mem : X i * f ∈ idealPiece I (e + 1) := by
    refine ⟨Ideal.mul_mem_left I (X i) hfI.1, ?_⟩
    change X i * f ∈ homogeneousSubmodule (Fin n) k (e + 1)
    rw [mem_homogeneousSubmodule]
    have h1 : (X i : MvPolynomial (Fin n) k).IsHomogeneous 1 := isHomogeneous_X k i
    have h2 : f.IsHomogeneous e := (mem_homogeneousSubmodule _ _).mp hfI.2
    simpa [add_comm] using h1.mul h2
  have hxf0 : X i * f ≠ 0 := mul_ne_zero (X_ne_zero i) hf0
  exact ⟨X i * f, hxf_mem, hxf0, lm_X_mul i hf0 hxf0⟩
lemma card_initMons_eq_hilbertFunction (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    (initMons I e).card = hilbertFunction I e := by
  classical
  set M := initMons I e
  set V := idealPiece I e
  have hpick : ∀ u : M, ∃ f ∈ V, ∃ hf : f ≠ 0, lm f hf = u.1 := fun u =>
    (mem_initMons.mp u.2).2
  let g : M → V := fun u => ⟨(hpick u).choose, (hpick u).choose_spec.1⟩
  have hg_ne : ∀ u : M, (g u : MvPolynomial (Fin n) k) ≠ 0 := fun u =>
    (hpick u).choose_spec.2.choose
  have hg_lm : ∀ u : M, lm (g u : MvPolynomial (Fin n) k) (hg_ne u) = u.1 := fun u =>
    (hpick u).choose_spec.2.choose_spec
  have hlin : LinearIndependent k g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push Not at hne
    set s := Finset.univ.filter (fun u : M => c u ≠ 0)
    have hs_ne : s.Nonempty := by
      obtain ⟨u, hu⟩ := hne
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩⟩
    obtain ⟨u_max, hu_max, hu_max_ge⟩ :=
      Finset.exists_max_image s (fun u : M => toLex u.1) hs_ne
    have hc_zero : coeff u_max.1 (∑ u : M, c u • (g u : MvPolynomial (Fin n) k)) = 0 := by
      have hval := congrArg Subtype.val hc
      simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero] at hval
      rw [hval, coeff_zero]
    rw [coeff_sum] at hc_zero
    have hsingle : ∑ u : M, coeff u_max.1 (c u • (g u : MvPolynomial (Fin n) k)) =
        c u_max * coeff u_max.1 (g u_max : MvPolynomial (Fin n) k) := by
      rw [Finset.sum_eq_single u_max]
      · rw [coeff_smul, smul_eq_mul]
      · intro u _ hun
        by_cases hcu : c u = 0
        · simp [hcu]
        · rw [coeff_smul, smul_eq_mul]
          have hu_s : u ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hcu⟩
          have hlt : toLex u.1 < toLex u_max.1 :=
            lt_of_le_of_ne (hu_max_ge u hu_s) (fun h => hun (Subtype.ext h))
          have h0 : coeff u_max.1 (g u : MvPolynomial (Fin n) k) = 0 :=
            coeff_eq_zero_of_lm_lt (hg_ne u) (by rwa [hg_lm u])
          simp [h0]
      · intro h; exact absurd (Finset.mem_univ u_max) h
    rw [hsingle] at hc_zero
    have hc_ne : c u_max ≠ 0 := (Finset.mem_filter.mp hu_max).2
    have hlm_ne : coeff u_max.1 (g u_max : MvPolynomial (Fin n) k) ≠ 0 := by
      rw [← hg_lm u_max]; exact coeff_lm_ne_zero (hg_ne u_max)
    exact mul_ne_zero hc_ne hlm_ne hc_zero
  have hspan : ⊤ ≤ Submodule.span k (Set.range g) := by
    intro f _
    suffices h : ∀ r (f : V),
        (∀ hf : (f : MvPolynomial (Fin n) k) ≠ 0,
          ((monOfDeg n e).filter (fun w => toLex w ≤ toLex (lm f.1 hf))).card ≤ r) →
        f ∈ Submodule.span k (Set.range g) by
      exact h (monOfDeg n e).card f (fun _ => Finset.card_le_card (Finset.filter_subset _ _))
    intro r
    induction r with
    | zero =>
      intro f hf_bound
      by_cases hf0 : (f : MvPolynomial (Fin n) k) = 0
      · have : f = 0 := Subtype.ext hf0
        rw [this]; exact Submodule.zero_mem _
      · exfalso
        have hdeg_lm : lm f.1 hf0 ∈ monOfDeg n e := by
          rw [mem_monOfDeg, ← weight_one_eq_degree]
          exact ((mem_homogeneousSubmodule _ _).mp f.2.2) (coeff_lm_ne_zero hf0)
        have hpos : 0 < ((monOfDeg n e).filter (fun w => toLex w ≤ toLex (lm f.1 hf0))).card :=
          Finset.card_pos.mpr ⟨lm f.1 hf0, Finset.mem_filter.mpr ⟨hdeg_lm, le_rfl⟩⟩
        have := hf_bound hf0
        omega
    | succ r ihr =>
      intro f hf_bound
      by_cases hf0 : (f : MvPolynomial (Fin n) k) = 0
      · have : f = 0 := Subtype.ext hf0
        rw [this]; exact Submodule.zero_mem _
      · set u := lm f.1 hf0
        have hu_deg : u ∈ monOfDeg n e := by
          rw [mem_monOfDeg, ← weight_one_eq_degree]
          exact ((mem_homogeneousSubmodule _ _).mp f.2.2) (coeff_lm_ne_zero hf0)
        have huM : u ∈ M := mem_initMons.mpr ⟨hu_deg, f.1, f.2, hf0, rfl⟩
        let u' : M := ⟨u, huM⟩
        set α : k := coeff u f.1 / coeff u (g u' : MvPolynomial (Fin n) k)
        set f' : V := f - α • g u'
        have hf'_mem : f' ∈ Submodule.span k (Set.range g) := by
          apply ihr f'
          intro hf'0
          have hlt_lm : toLex (lm f'.1 hf'0) < toLex u := by
            have hmem := lm_mem_support hf'0
            have hsub : f'.1.support ⊆ f.1.support ∪ (g u' : MvPolynomial (Fin n) k).support := by
              intro w hw
              rw [mem_support_iff] at hw
              simp only [f', Submodule.coe_sub, SetLike.val_smul, coeff_sub, coeff_smul,
                smul_eq_mul] at hw
              rw [mem_union, mem_support_iff, mem_support_iff]
              by_contra h
              push Not at h
              exact hw (by simp [h.1, h.2])
            have hle : toLex (lm f'.1 hf'0) ≤ toLex u := by
              rcases mem_union.mp (hsub hmem) with h1 | h2
              · exact le_lm hf0 h1
              · have := le_lm (hg_ne u') h2
                rwa [hg_lm u'] at this
            refine lt_of_le_of_ne hle ?_
            intro heq
            have hcu : coeff u f'.1 = 0 := by
              simp only [f', Submodule.coe_sub, SetLike.val_smul, coeff_sub, coeff_smul,
                smul_eq_mul, α]
              have hne_gu : coeff u (g u' : MvPolynomial (Fin n) k) ≠ 0 := by
                have := coeff_lm_ne_zero (hg_ne u')
                rwa [hg_lm u'] at this
              rw [div_mul_cancel₀ _ hne_gu, sub_self]
            have hne_lm := coeff_lm_ne_zero hf'0
            have : lm f'.1 hf'0 = u := heq
            rw [this] at hne_lm
            exact hne_lm hcu
          have hssub : (monOfDeg n e).filter (fun w => toLex w ≤ toLex (lm f'.1 hf'0)) ⊂
              (monOfDeg n e).filter (fun w => toLex w ≤ toLex u) := by
            rw [Finset.ssubset_iff_of_subset]
            · exact ⟨u, Finset.mem_filter.mpr ⟨hu_deg, le_rfl⟩,
                by simp [not_le_of_gt hlt_lm]⟩
            · intro w hw
              simp only [mem_filter] at hw ⊢
              exact ⟨hw.1, le_trans hw.2 (le_of_lt hlt_lm)⟩
          have hcard_lt := Finset.card_lt_card hssub
          have hbound : ((monOfDeg n e).filter (fun w => toLex w ≤ toLex u)).card ≤ r + 1 :=
            hf_bound hf0
          omega
        have heq_f : f = f' + α • g u' := by simp [f']
        rw [heq_f]
        exact Submodule.add_mem _ hf'_mem
          (Submodule.smul_mem _ α (Submodule.subset_span ⟨u', rfl⟩))
  let B : Module.Basis M k V := Module.Basis.mk hlin hspan
  have hfin := Module.finrank_eq_card_basis B
  rw [Fintype.card_coe] at hfin
  exact hfin.symm
lemma mem_monomialIdeal_iff_support {S : Set (Fin n →₀ ℕ)}
    (hclosed : ∀ u ∈ S, ∀ i : Fin n, u + Finsupp.single i 1 ∈ S)
    (f : MvPolynomial (Fin n) k) :
    f ∈ Ideal.span ((fun u => monomial u (1 : k)) '' S) ↔ ∀ u ∈ f.support, u ∈ S := by
  classical
  have hclosed_add : ∀ d : ℕ, ∀ w : Fin n →₀ ℕ, w.degree = d → ∀ u ∈ S, u + w ∈ S := by
    intro d
    induction d with
    | zero =>
      intro w hw u hu
      have hw0 : w = 0 := by
        ext i
        have hle : w i ≤ w.degree := by
          rw [Finsupp.degree_eq_sum]
          exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        simp only [Finsupp.zero_apply]
        omega
      simpa [hw0] using hu
    | succ d ih =>
      intro w hw u hu
      have hne : w.support.Nonempty := by
        rw [Finsupp.support_nonempty_iff]
        intro h0; rw [h0, map_zero] at hw; omega
      obtain ⟨i, hi⟩ := hne
      have hi_pos : 1 ≤ w i := by
        have := Finsupp.mem_support_iff.mp hi; omega
      have hdeg_sub : (w - Finsupp.single i 1).degree = d := by
        have := degree_sub_single hi_pos; omega
      have hmem := ih (w - Finsupp.single i 1) hdeg_sub u hu
      have hmem' := hclosed _ hmem i
      rwa [add_assoc, sub_single_add_single hi_pos] at hmem'
  let J : Ideal (MvPolynomial (Fin n) k) :=
    { carrier := { f | ∀ u ∈ f.support, u ∈ S }
      add_mem' := fun {a b} ha hb u hu => by
        rcases Finset.mem_union.mp (MvPolynomial.support_add hu) with h | h
        · exact ha u h
        · exact hb u h
      zero_mem' := fun u hu => by simp at hu
      smul_mem' := fun g f hf u hu => by
        have hmul := MvPolynomial.support_mul g f hu
        rw [Finset.mem_add] at hmul
        obtain ⟨w, _, v, hv, rfl⟩ := hmul
        rw [add_comm]
        exact hclosed_add w.degree w rfl v (hf v hv) }
  constructor
  · intro hf
    have hle : Ideal.span ((fun u => monomial u (1 : k)) '' S) ≤ J := by
      rw [Ideal.span_le]
      rintro _ ⟨u, hu, rfl⟩ v hv
      rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hv
      rwa [hv]
    exact hle hf
  · intro hf
    rw [f.as_sum]
    refine Ideal.sum_mem _ fun u hu => ?_
    have hmon : monomial u (coeff u f) = C (coeff u f) * monomial u (1 : k) := by
      rw [C_mul_monomial, mul_one]
    rw [hmon]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨u, hf u hu, rfl⟩)
lemma hilbertFunction_monomialIdeal {L_slice : ℕ → Finset (Fin n →₀ ℕ)}
    {S : Set (Fin n →₀ ℕ)} (hS : ∀ u, u ∈ S ↔ u ∈ L_slice u.degree)
    (hdeg : ∀ e, L_slice e ⊆ monOfDeg n e)
    (hshadow : ∀ e, shadow (L_slice e) ⊆ L_slice (e + 1)) (e : ℕ) :
    hilbertFunction (Ideal.span ((fun u => monomial u (1 : k)) '' S)) e = (L_slice e).card := by
  classical
  have hclosed : ∀ u ∈ S, ∀ i : Fin n, u + Finsupp.single i 1 ∈ S := by
    intro u hu i
    rw [hS, map_add, Finsupp.degree_single]
    exact hshadow u.degree (mem_shadow.mpr ⟨u, (hS u).mp hu, i, rfl⟩)
  set L : Ideal (MvPolynomial (Fin n) k) := Ideal.span ((fun u => monomial u (1 : k)) '' S)
  set V := idealPiece L e
  have hmemV : ∀ f : MvPolynomial (Fin n) k, f ∈ V ↔ ∀ u ∈ f.support, u ∈ L_slice e := by
    intro f
    constructor
    · rintro ⟨h1, h2⟩ u hu
      have h1' : f ∈ L := h1
      have h2' : f.IsHomogeneous e := (mem_homogeneousSubmodule _ _).mp h2
      have hdu : u.degree = e := by
        rw [← weight_one_eq_degree]; exact h2' (mem_support_iff.mp hu)
      have huS : u ∈ S := (mem_monomialIdeal_iff_support hclosed f).mp h1' u hu
      have huL : u ∈ L_slice u.degree := (hS u).mp huS
      rwa [hdu] at huL
    · intro h
      refine ⟨?_, ?_⟩
      · change f ∈ L
        rw [mem_monomialIdeal_iff_support hclosed]
        intro u hu
        rw [hS, mem_monOfDeg.mp (hdeg e (h u hu))]
        exact h u hu
      · change f ∈ homogeneousSubmodule (Fin n) k e
        rw [mem_homogeneousSubmodule]
        intro u hu
        rw [weight_one_eq_degree]
        exact mem_monOfDeg.mp (hdeg e (h u (mem_support_iff.mpr hu)))
  let b : L_slice e → V := fun u =>
    ⟨monomial u.1 (1 : k), (hmemV _).mpr fun v hv => by
      rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hv
      rw [hv]
      exact u.2⟩
  have hlin : LinearIndependent k b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc u
    have hval := congrArg (fun x : V => coeff u.1 x.1) hc
    simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero, coeff_zero,
      coeff_sum, coeff_smul, smul_eq_mul, b, coeff_monomial] at hval
    have hsum : ∑ x : L_slice e, c x * (if x.1 = u.1 then (1 : k) else 0) = c u := by
      rw [Finset.sum_eq_single u]
      · simp
      · intro x _ hxu
        rw [if_neg (fun h => hxu (Subtype.ext h)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ u) h
    rw [hsum] at hval
    exact hval
  have hspan : ⊤ ≤ Submodule.span k (Set.range b) := by
    intro f _
    have hsupp := (hmemV f.1).mp f.2
    have hfeq : f = ∑ u ∈ f.1.support.attach,
        coeff u.1 f.1 • b ⟨u.1, hsupp u.1 u.2⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, SetLike.val_smul, b]
      conv_lhs => rw [f.1.as_sum]
      rw [← Finset.sum_attach f.1.support (fun u => monomial u (coeff u f.1))]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hfeq]
    exact Submodule.sum_mem _ fun u _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨u.1, hsupp u.1 u.2⟩, rfl⟩)
  let B : Module.Basis (L_slice e) k V := Module.Basis.mk hlin hspan
  have hfin := Module.finrank_eq_card_basis B
  rw [Fintype.card_coe] at hfin
  exact hfin
lemma X_pow_eq_monomial (i : Fin n) (m : ℕ) :
    (X i : MvPolynomial (Fin n) k) ^ m = monomial (Finsupp.single i m) (1 : k) := by
  induction m with
  | zero => simp [monomial_zero']
  | succ m ih =>
    rw [pow_succ, ih, X, monomial_mul, mul_one, ← Finsupp.single_add]
lemma purePowersIdeal_eq_monomialIdeal {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) :
    (purePowersIdeal hc d : Ideal (MvPolynomial (Fin n) k)) =
      Ideal.span ((fun u => monomial u (1 : k)) ''
        { u : Fin n →₀ ℕ | ∃ j : Fin c, d j ≤ u (Fin.castLE hc j) }) := by
  set SP : Set (Fin n →₀ ℕ) := { u : Fin n →₀ ℕ | ∃ j : Fin c, d j ≤ u (Fin.castLE hc j) }
  apply le_antisymm
  · rw [purePowersIdeal, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    change (X (Fin.castLE hc j) : MvPolynomial (Fin n) k) ^ d j ∈
      Ideal.span ((fun u => monomial u (1 : k)) '' SP)
    rw [X_pow_eq_monomial]
    exact Ideal.subset_span ⟨Finsupp.single (Fin.castLE hc j) (d j), ⟨j, by simp⟩, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨u, ⟨j, hj⟩, rfl⟩
    change monomial u (1 : k) ∈ purePowersIdeal hc d
    have hsplit : u = (u - Finsupp.single (Fin.castLE hc j) (d j)) +
        Finsupp.single (Fin.castLE hc j) (d j) := by
      ext r
      rcases eq_or_ne r (Fin.castLE hc j) with rfl | hr
      · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_eq_same]; omega
      · simp [hr]
    have hmon : monomial u (1 : k) =
        monomial (u - Finsupp.single (Fin.castLE hc j) (d j)) (1 : k) *
          (X (Fin.castLE hc j) : MvPolynomial (Fin n) k) ^ d j := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, ← hsplit]
    rw [hmon]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
lemma isLexFull_shadow {e : ℕ} {L : Finset (Fin n →₀ ℕ)}
    (hLsub : L ⊆ monOfDeg n e)
    (hLlex : ∀ u ∈ monOfDeg n e, ∀ v ∈ L, toLex v < toLex u → u ∈ L) :
    ∀ u ∈ monOfDeg n (e + 1), ∀ v ∈ shadow L, toLex v < toLex u → u ∈ shadow L := by
  set D : Fin n → ℕ := fun _ => e + 2
  have hmon_eq : ∀ d ≤ e + 1, monBox D d = monOfDeg n d := fun d hd => by
    ext u
    simp only [mem_monBox, mem_monOfDeg, and_iff_left_iff_imp]
    intro hdeg i
    have hle : u i ≤ u.degree := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [D]; omega
  have hsh_eq : shadowBox D L = shadow L := by
    ext v
    simp only [mem_shadowBox, mem_shadow, and_iff_left_iff_imp]
    rintro ⟨w, hw, i, rfl⟩ r
    have hdeg := mem_monOfDeg.mp (hLsub hw)
    have hle : (w + Finsupp.single i 1 : Fin n →₀ ℕ) r ≤ (w + Finsupp.single i 1).degree := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    rw [map_add, Finsupp.degree_single, hdeg] at hle
    simp only [D]; omega
  have hboxL : IsLexBox D e L := by
    rw [IsLexBox, hmon_eq e (by omega)]
    exact ⟨hLsub, hLlex⟩
  have hboxS := hboxL.shadowBox
  rw [IsLexBox, hmon_eq (e + 1) le_rfl, hsh_eq] at hboxS
  exact hboxS.2
def clBound {c : ℕ} (d : Fin c → ℕ) (e : ℕ) (i : Fin n) : ℕ :=
  if h : i.1 < c then d ⟨i.1, h⟩ else e + 2 + ∑ j : Fin c, d j
lemma clBound_pos {c : ℕ} {d : Fin c → ℕ} (hd_pos : ∀ j : Fin c, 1 ≤ d j) (e : ℕ) (i : Fin n) :
    1 ≤ clBound d e i := by
  unfold clBound
  split_ifs with h
  · exact hd_pos ⟨i.1, h⟩
  · omega
lemma clBound_mono {c : ℕ} {d : Fin c → ℕ} (hd : Monotone d) (e : ℕ) :
    Monotone (clBound (n := n) d e) := by
  intro i₁ i₂ hle
  unfold clBound
  by_cases h1 : i₁.1 < c
  · by_cases h2 : i₂.1 < c
    · rw [dif_pos h1, dif_pos h2]
      exact hd (Fin.mk_le_mk.mpr hle)
    · rw [dif_pos h1, dif_neg h2]
      have hle_sum : d ⟨i₁.1, h1⟩ ≤ ∑ j : Fin c, d j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨i₁.1, h1⟩ : Fin c))
      omega
  · by_cases h2 : i₂.1 < c
    · exfalso; exact h1 (lt_of_le_of_lt hle h2)
    · rw [dif_neg h1, dif_neg h2]
def inBoxPred {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) (u : Fin n →₀ ℕ) : Prop :=
  ∀ j : Fin c, u (Fin.castLE hc j) < d j
open Classical in
noncomputable def boxSlice {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) (e : ℕ) : Finset (Fin n →₀ ℕ) :=
  (monOfDeg n e).filter (inBoxPred hc d)
lemma monBox_clBound_eq_boxSlice {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) (e d_deg : ℕ)
    (hle : d_deg ≤ e + 1) :
    monBox (clBound (n := n) d e) d_deg = boxSlice hc d d_deg := by
  classical
  ext u
  simp only [mem_monBox, boxSlice, mem_filter, mem_monOfDeg, inBoxPred]
  constructor
  · rintro ⟨hdeg, hlt⟩
    refine ⟨hdeg, fun j => ?_⟩
    have := hlt (Fin.castLE hc j)
    simp only [clBound, Fin.val_castLE, j.isLt, ↓reduceDIte] at this
    exact this
  · rintro ⟨hdeg, hin⟩
    refine ⟨hdeg, fun i => ?_⟩
    unfold clBound
    split_ifs with hi
    · exact hin ⟨i.1, hi⟩
    · have hle_i : u i ≤ u.degree := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
open Classical in
lemma shadow_filter_inBox_eq_shadowBox {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) (e : ℕ)
    {A : Finset (Fin n →₀ ℕ)} (hA : A ⊆ monOfDeg n e) :
    (shadow A).filter (inBoxPred hc d) = shadowBox (clBound (n := n) d e) A := by
  ext v
  simp only [mem_filter, mem_shadowBox, mem_shadow, inBoxPred]
  constructor
  · rintro ⟨⟨w, hw, i, rfl⟩, hin⟩
    refine ⟨⟨w, hw, i, rfl⟩, fun r => ?_⟩
    unfold clBound
    split_ifs with hr
    · exact hin ⟨r.1, hr⟩
    · have hdeg := mem_monOfDeg.mp (hA hw)
      have hle : (w + Finsupp.single i 1 : Fin n →₀ ℕ) r ≤ (w + Finsupp.single i 1).degree := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
      rw [map_add, Finsupp.degree_single, hdeg] at hle
      omega
  · rintro ⟨⟨w, hw, i, rfl⟩, hlt⟩
    refine ⟨⟨w, hw, i, rfl⟩, fun j => ?_⟩
    have := hlt (Fin.castLE hc j)
    simp only [clBound, Fin.val_castLE, j.isLt, ↓reduceDIte] at this
    exact this
open Classical in
noncomputable def clBoxInit {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) : Finset (Fin n →₀ ℕ) :=
  (initMons I e).filter (inBoxPred hc d)
noncomputable def clLexBox {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) : Finset (Fin n →₀ ℕ) :=
  lexSegBox (clBound (n := n) d e) e (clBoxInit hc d I e).card
open Classical in
noncomputable def clLexFull {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) : Finset (Fin n →₀ ℕ) :=
  (monOfDeg n e).filter (fun u => ∀ v ∈ boxSlice hc d e \ clLexBox hc d I e, toLex v < toLex u)
def clLexSet {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) : Set (Fin n →₀ ℕ) :=
  { u | u ∈ clLexFull hc d I u.degree }
lemma mem_clLexSet {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (u : Fin n →₀ ℕ) :
    u ∈ clLexSet hc d I ↔ u ∈ clLexFull hc d I u.degree := by
  unfold clLexSet
  exact Iff.of_eq Set.mem_ofPred_eq
def clPureSet {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) : Set (Fin n →₀ ℕ) :=
  { u : Fin n →₀ ℕ | ∃ j : Fin c, d j ≤ u (Fin.castLE hc j) }
noncomputable def clTotalSlice {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) : Finset (Fin n →₀ ℕ) :=
  clLexBox hc d I e ∪ (monOfDeg n e \ boxSlice hc d e)
lemma clBoxInit_subset {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    clBoxInit hc d I e ⊆ boxSlice hc d e := by
  classical
  intro u hu
  simp only [clBoxInit, boxSlice, mem_filter] at hu ⊢
  exact ⟨initMons_subset I e hu.1, hu.2⟩
lemma clLexBox_subset {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    clLexBox hc d I e ⊆ boxSlice hc d e := by
  rw [← monBox_clBound_eq_boxSlice hc d e e (by omega)]
  exact lexSegBox_subset_monBox (clBound (n := n) d e) e _
lemma clLexBox_card {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    (clLexBox hc d I e).card = (clBoxInit hc d I e).card := by
  apply card_lexSegBox
  rw [monBox_clBound_eq_boxSlice hc d e e (by omega)]
  exact Finset.card_le_card (clBoxInit_subset hc d I e)
open Classical in
lemma clShadow_box {c : ℕ} (hc : c ≤ n) {d : Fin c → ℕ} (hd_pos : ∀ j : Fin c, 1 ≤ d j)
    (hd : Monotone d) (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    (shadow (clLexBox hc d I e)).filter (inBoxPred hc d) ⊆ clLexBox hc d I (e + 1) := by
  classical
  have hL_sub_deg : clLexBox hc d I e ⊆ monOfDeg n e :=
    Finset.Subset.trans (clLexBox_subset hc d I e) (Finset.filter_subset _ _)
  have hM_sub_deg : clBoxInit hc d I e ⊆ monOfDeg n e :=
    Finset.Subset.trans (clBoxInit_subset hc d I e) (Finset.filter_subset _ _)
  rw [shadow_filter_inBox_eq_shadowBox hc d e hL_sub_deg]
  have hlex_next : IsLexBox (clBound (n := n) d e) (e + 1) (clLexBox hc d I (e + 1)) := by
    have h1 := isLexBox_lexSegBox (clBound (n := n) d (e + 1)) (e + 1) (clBoxInit hc d I (e + 1)).card
    rw [IsLexBox, monBox_clBound_eq_boxSlice hc d (e + 1) (e + 1) (by omega)] at h1
    rw [IsLexBox, monBox_clBound_eq_boxSlice hc d e (e + 1) le_rfl]
    exact h1
  apply (isLexBox_lexSegBox (clBound (n := n) d e) e _).shadowBox.subset_of_card_le hlex_next
  have hMsub : clBoxInit hc d I e ⊆ monBox (clBound (n := n) d e) e := by
    rw [monBox_clBound_eq_boxSlice hc d e e (by omega)]; exact clBoxInit_subset hc d I e
  have hshM_sub : shadowBox (clBound (n := n) d e) (clBoxInit hc d I e) ⊆ clBoxInit hc d I (e + 1) := by
    rw [← shadow_filter_inBox_eq_shadowBox hc d e hM_sub_deg]
    intro v hv
    rw [mem_filter] at hv
    rw [clBoxInit, mem_filter]
    exact ⟨shadow_initMons_subset I e (shadow_mono (Finset.filter_subset _ _) hv.1), hv.2⟩
  calc (shadowBox (clBound (n := n) d e) (clLexBox hc d I e)).card
      ≤ (shadowBox (clBound (n := n) d e) (clBoxInit hc d I e)).card :=
        clements_lindstrom_shadow n (clBound (n := n) d e) (clBound_pos hd_pos e)
          (clBound_mono hd e) e (clBoxInit hc d I e) hMsub
    _ ≤ (clBoxInit hc d I (e + 1)).card := Finset.card_le_card hshM_sub
    _ = (clLexBox hc d I (e + 1)).card := (clLexBox_card hc d I (e + 1)).symm
lemma clLexFull_inter {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) {u : Fin n →₀ ℕ} (huB : u ∈ boxSlice hc d e) :
    u ∈ clLexFull hc d I e ↔ u ∈ clLexBox hc d I e := by
  classical
  simp only [clLexFull, mem_filter]
  have hu_deg : u ∈ monOfDeg n e := (Finset.mem_filter.mp huB).1
  constructor
  · rintro ⟨_, hgt⟩
    by_contra huL
    exact lt_irrefl _ (hgt u (mem_sdiff.mpr ⟨huB, huL⟩))
  · intro huL
    refine ⟨hu_deg, fun v hv => ?_⟩
    rw [mem_sdiff] at hv
    rcases lt_trichotomy (toLex v) (toLex u) with h | heq | h
    · exact h
    · exfalso; have hvu : v = u := heq; exact hv.2 (hvu ▸ huL)
    · exfalso
      have hlex := isLexBox_lexSegBox (clBound (n := n) d e) e (clBoxInit hc d I e).card
      rw [IsLexBox, monBox_clBound_eq_boxSlice hc d e e (by omega)] at hlex
      exact hv.2 (hlex.2 v hv.1 u huL h)
lemma clShadow_full {c : ℕ} (hc : c ≤ n) {d : Fin c → ℕ} (hd_pos : ∀ j : Fin c, 1 ≤ d j)
    (hd : Monotone d) (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    shadow (clLexFull hc d I e) ⊆ clLexFull hc d I (e + 1) := by
  classical
  have hsub : clLexFull hc d I e ⊆ monOfDeg n e := Finset.filter_subset _ _
  have hlex : ∀ u ∈ monOfDeg n e, ∀ v ∈ clLexFull hc d I e, toLex v < toLex u →
      u ∈ clLexFull hc d I e := by
    intro u hu v hv hlt
    rw [clLexFull, mem_filter] at hv ⊢
    exact ⟨hu, fun w hw => lt_trans (hv.2 w hw) hlt⟩
  intro x hx
  have hx_deg : x ∈ monOfDeg n (e + 1) := shadow_subset_monOfDeg hsub hx
  by_contra hx_n
  simp only [clLexFull, mem_filter, hx_deg, true_and, not_forall, not_lt] at hx_n
  obtain ⟨v, hv_sdiff, hxv⟩ := hx_n
  rw [mem_sdiff] at hv_sdiff
  obtain ⟨hvB, hvL⟩ := hv_sdiff
  have hv_deg : v ∈ monOfDeg n (e + 1) := (Finset.mem_filter.mp hvB).1
  have hv_sh : v ∈ shadow (clLexFull hc d I e) := by
    rcases eq_or_lt_of_le hxv with h | h
    · have : x = v := h; rwa [← this]
    · exact isLexFull_shadow hsub hlex v hv_deg x hx h
  rw [mem_shadow] at hv_sh
  obtain ⟨w, hw, i, hw_eq⟩ := hv_sh
  have hw_inBox : inBoxPred hc d w := by
    intro j
    have hv_in := (Finset.mem_filter.mp hvB).2 j
    have hle : w (Fin.castLE hc j) ≤ v (Fin.castLE hc j) := by
      rw [← hw_eq]; simp
    omega
  have hwB : w ∈ boxSlice hc d e := Finset.mem_filter.mpr ⟨hsub hw, hw_inBox⟩
  have hwL : w ∈ clLexBox hc d I e := (clLexFull_inter hc d I e hwB).mp hw
  have hv_in_sh : v ∈ (shadow (clLexBox hc d I e)).filter (inBoxPred hc d) :=
    Finset.mem_filter.mpr ⟨mem_shadow.mpr ⟨w, hwL, i, hw_eq⟩, (Finset.mem_filter.mp hvB).2⟩
  exact hvL (clShadow_box hc hd_pos hd I e hv_in_sh)
lemma clInit_eq {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (hIp : purePowersIdeal hc d ≤ I) (e : ℕ) :
    initMons I e = clBoxInit hc d I e ∪ (monOfDeg n e \ boxSlice hc d e) := by
  classical
  ext u
  simp only [clBoxInit, boxSlice, mem_union, mem_filter, mem_sdiff]
  constructor
  · intro hu
    by_cases hin : inBoxPred hc d u
    · exact Or.inl ⟨hu, hin⟩
    · exact Or.inr ⟨initMons_subset I e hu, fun h => hin h.2⟩
  · rintro (⟨hu, _⟩ | ⟨hu_deg, hnot⟩)
    · exact hu
    · rw [mem_initMons]
      refine ⟨hu_deg, monomial u (1 : k), ⟨?_, ?_⟩, monomial_eq_zero.not.mpr one_ne_zero, ?_⟩
      · apply hIp
        rw [purePowersIdeal_eq_monomialIdeal]
        apply Ideal.subset_span
        refine ⟨u, ?_, rfl⟩
        have hnot' : ¬ inBoxPred hc d u := fun hin => hnot ⟨hu_deg, hin⟩
        unfold inBoxPred at hnot'
        push Not at hnot'
        exact hnot'
      · change monomial u (1 : k) ∈ homogeneousSubmodule (Fin n) k e
        rw [mem_homogeneousSubmodule]
        intro v hv
        rw [coeff_monomial] at hv
        split_ifs at hv with hvu
        · subst hvu
          rw [weight_one_eq_degree]
          exact mem_monOfDeg.mp hu_deg
        · exact absurd rfl hv
      · have hsupp := lm_mem_support (f := monomial u (1 : k))
          (monomial_eq_zero.not.mpr one_ne_zero)
        rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hsupp
        exact hsupp
theorem clements_lindstrom_main {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (hd : Monotone d) (I : Ideal (MvPolynomial (Fin n) k))
    (hIp : purePowersIdeal hc d ≤ I) :
    ∃ L : Ideal (MvPolynomial (Fin n) k), IsLexIdeal L ∧
      ∀ e, hilbertFunction I e = hilbertFunction (L + purePowersIdeal hc d) e := by
  classical
  by_cases hzero : ∃ j : Fin c, d j = 0
  · obtain ⟨j, hj⟩ := hzero
    have h1I : (1 : MvPolynomial (Fin n) k) ∈ I := by
      apply hIp
      have hgen : (X (Fin.castLE hc j) : MvPolynomial (Fin n) k) ^ d j ∈ purePowersIdeal hc d :=
        Ideal.subset_span ⟨j, rfl⟩
      simpa [hj] using hgen
    have hItop : I = ⊤ := Ideal.eq_top_of_isUnit_mem I h1I isUnit_one
    refine ⟨⊤, isLexIdeal_top, fun e => ?_⟩
    have htop : (⊤ : Ideal (MvPolynomial (Fin n) k)) + purePowersIdeal hc d = ⊤ :=
      top_sup_eq _
    rw [hItop, htop]
  · push Not at hzero
    have hd_pos : ∀ j : Fin c, 1 ≤ d j := fun j => Nat.pos_of_ne_zero (hzero j)
    have hSL_closed : ∀ u ∈ clLexSet hc d I, ∀ i : Fin n, u + Finsupp.single i 1 ∈ clLexSet hc d I := by
      intro u hu i
      rw [mem_clLexSet, map_add, Finsupp.degree_single]
      exact clShadow_full hc hd_pos hd I u.degree (mem_shadow.mpr ⟨u, (mem_clLexSet hc d I u).mp hu, i, rfl⟩)
    refine ⟨Ideal.span ((fun u => monomial u (1 : k)) '' clLexSet hc d I),
      ⟨⟨clLexSet hc d I, rfl⟩, ?_⟩, ?_⟩
    · intro u v huv hlt hvL
      rw [mem_monomialIdeal_iff_support hSL_closed] at hvL ⊢
      intro w hw
      rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hw
      rw [hw]
      have hvS : v ∈ clLexFull hc d I v.degree := (mem_clLexSet hc d I v).mp (hvL v (by
        rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton]))
      rw [mem_clLexSet, huv, clLexFull, mem_filter]
      exact ⟨mem_monOfDeg.mpr huv, fun x hx =>
        lt_trans ((Finset.mem_filter.mp hvS).2 x hx) hlt⟩
    · have hT_deg : ∀ e, clTotalSlice hc d I e ⊆ monOfDeg n e := fun e u hu => by
        rw [clTotalSlice, mem_union] at hu
        rcases hu with h | h
        · exact (Finset.mem_filter.mp (clLexBox_subset hc d I e h)).1
        · exact (mem_sdiff.mp h).1
      have hT_iff : ∀ u, u ∈ clLexSet hc d I ∪ clPureSet hc d ↔ u ∈ clTotalSlice hc d I u.degree := by
        intro u
        have hu_deg : u ∈ monOfDeg n u.degree := mem_monOfDeg.mpr rfl
        simp only [Set.mem_union, clTotalSlice, mem_union, mem_sdiff]
        by_cases hin : inBoxPred hc d u
        · have huB : u ∈ boxSlice hc d u.degree := Finset.mem_filter.mpr ⟨hu_deg, hin⟩
          have huSP : u ∉ clPureSet hc d := by
            rintro ⟨j, hj⟩; have := hin j; omega
          simp only [huSP, or_false, huB, not_true_eq_false, and_false]
          rw [mem_clLexSet]
          exact clLexFull_inter hc d I u.degree huB
        · have huB : u ∉ boxSlice hc d u.degree := fun h => hin (Finset.mem_filter.mp h).2
          have huSP : u ∈ clPureSet hc d := by
            unfold inBoxPred at hin; push Not at hin; exact hin
          simp only [huSP, or_true, hu_deg, huB, not_false_eq_true, and_self]
      have hT_shadow : ∀ e, shadow (clTotalSlice hc d I e) ⊆ clTotalSlice hc d I (e + 1) := by
        intro e v hv
        rw [mem_shadow] at hv
        obtain ⟨u, hu, i, rfl⟩ := hv
        have hv_deg : (u + Finsupp.single i 1).degree = e + 1 := by
          rw [map_add, Finsupp.degree_single, mem_monOfDeg.mp (hT_deg e hu)]
        rw [← hv_deg, ← hT_iff]
        have hu' : u ∈ clLexSet hc d I ∪ clPureSet hc d :=
          (hT_iff u).mpr (by rw [mem_monOfDeg.mp (hT_deg e hu)]; exact hu)
        rcases hu' with huSL | ⟨j, hj⟩
        · exact Or.inl (hSL_closed u huSL i)
        · refine Or.inr ⟨j, ?_⟩
          simp only [Finsupp.coe_add, Pi.add_apply]; omega
      have hsum_eq : Ideal.span ((fun u => monomial u (1 : k)) '' clLexSet hc d I) +
            purePowersIdeal hc d =
          Ideal.span ((fun u => monomial u (1 : k)) '' (clLexSet hc d I ∪ clPureSet hc d)) := by
        have hp : (purePowersIdeal hc d : Ideal (MvPolynomial (Fin n) k)) =
            Ideal.span ((fun u => monomial u (1 : k)) '' clPureSet hc d) :=
          purePowersIdeal_eq_monomialIdeal hc d
        rw [hp, Submodule.add_eq_sup, ← Ideal.span_union, Set.image_union]
      intro e
      have hhilb_rhs : hilbertFunction
          (Ideal.span ((fun u => monomial u (1 : k)) '' (clLexSet hc d I ∪ clPureSet hc d))) e =
          (clTotalSlice hc d I e).card :=
        hilbertFunction_monomialIdeal hT_iff hT_deg hT_shadow e
      have hhilb_lhs : (initMons I e).card = hilbertFunction I e :=
        card_initMons_eq_hilbertFunction I e
      have hdisj1 : Disjoint (clBoxInit hc d I e) (monOfDeg n e \ boxSlice hc d e) :=
        Finset.disjoint_left.mpr fun x h1 h2 => (mem_sdiff.mp h2).2 (clBoxInit_subset hc d I e h1)
      have hdisj2 : Disjoint (clLexBox hc d I e) (monOfDeg n e \ boxSlice hc d e) :=
        Finset.disjoint_left.mpr fun x h1 h2 => (mem_sdiff.mp h2).2 (clLexBox_subset hc d I e h1)
      have hcard_eq : (initMons I e).card = (clTotalSlice hc d I e).card := by
        rw [clInit_eq hc d I hIp e, clTotalSlice,
          Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2,
          clLexBox_card hc d I e]
      rw [hsum_eq, hhilb_rhs, ← hhilb_lhs, hcard_eq]
end IdealPart
end CL
namespace BC
open MvPolynomial Finset CL
variable {n : ℕ} {k : Type*} [Field k]
noncomputable def clNext {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) (e r : ℕ) : ℕ :=
  (boxSlice hc d (e + 1)).card -
    (shadowBox (clBound (n := n) d e)
      (lexSegBox (clBound (n := n) d e) e ((boxSlice hc d e).card - r))).card
lemma mem_lexSegBox_of_card_ge_le {D : Fin n → ℕ} {e m : ℕ} {u : Fin n →₀ ℕ}
    (hu : u ∈ monBox D e)
    (hcard : ((monBox D e).filter (fun w => toLex u ≤ toLex w)).card ≤ m)
    (hm : m ≤ (monBox D e).card) :
    u ∈ lexSegBox D e m := by
  classical
  by_contra hu_not
  have hlex := isLexBox_lexSegBox D e m
  have hsub : lexSegBox D e m ⊂ (monBox D e).filter (fun w => toLex u ≤ toLex w) := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨u, Finset.mem_filter.mpr ⟨hu, le_rfl⟩, hu_not⟩
    · intro w hw
      refine Finset.mem_filter.mpr ⟨hlex.1 hw, ?_⟩
      by_contra hnot
      push Not at hnot
      exact hu_not (hlex.2 u hu w hw hnot)
  have hlt := Finset.card_lt_card hsub
  rw [card_lexSegBox hm] at hlt
  omega
theorem lpp_to_isLPPSeq {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (L : Ideal (MvPolynomial (Fin n) k)) (hL : IsLexIdeal L)
    (q : ℕ → ℕ) (hq : ∀ e, hilbertFunction (L + purePowersIdeal hc d) e + q e = (monOfDeg n e).card) :
    (∀ e, q e ≤ (boxSlice hc d e).card) ∧ ∀ e, q (e + 1) ≤ clNext hc d e (q e) := by
  classical
  obtain ⟨⟨SL, hSL⟩, hlex⟩ := hL
  let SL' : Set (Fin n →₀ ℕ) := { u | monomial u (1 : k) ∈ L }
  let SP : Set (Fin n →₀ ℕ) := clPureSet hc d
  have hclosed : ∀ u ∈ SL' ∪ SP, ∀ i : Fin n, u + Finsupp.single i 1 ∈ SL' ∪ SP := by
    intro u hu i
    rcases hu with huL | ⟨j, hj⟩
    · left
      change monomial (u + Finsupp.single i 1) (1 : k) ∈ L
      have : monomial (u + Finsupp.single i 1) (1 : k) = X i * monomial u 1 := by
        rw [X, monomial_mul, one_mul, add_comm]
      rw [this]; exact L.mul_mem_left _ huL
    · right; refine ⟨j, ?_⟩; simp only [Finsupp.coe_add, Pi.add_apply]; omega
  have hL_eq : L = Ideal.span ((fun u => monomial u (1 : k)) '' SL') := by
    apply le_antisymm
    · rw [hSL, Ideal.span_le]; rintro _ ⟨u, hu, rfl⟩
      exact Ideal.subset_span ⟨u, by change monomial u 1 ∈ L; rw [hSL]; exact Ideal.subset_span ⟨u, hu, rfl⟩, rfl⟩
    · rw [Ideal.span_le]; rintro _ ⟨u, hu, rfl⟩; exact hu
  have hLP_eq : L + purePowersIdeal hc d =
      Ideal.span ((fun u => monomial u (1 : k)) '' (SL' ∪ SP)) := by
    rw [Submodule.add_eq_sup, hL_eq, purePowersIdeal_eq_monomialIdeal hc d, ← Ideal.span_union,
      Set.image_union]; rfl
  let T (e : ℕ) : Finset (Fin n →₀ ℕ) := (monOfDeg n e).filter (fun u => u ∈ SL' ∪ SP)
  have hT_iff : ∀ u, u ∈ SL' ∪ SP ↔ u ∈ T u.degree := fun u => by
    simp [T, mem_monOfDeg]
  have hT_deg : ∀ e, T e ⊆ monOfDeg n e := fun e => Finset.filter_subset _ _
  have hT_sh : ∀ e, shadow (T e) ⊆ T (e + 1) := by
    intro e v hv
    rw [mem_shadow] at hv
    obtain ⟨u, hu, i, rfl⟩ := hv
    rw [Finset.mem_filter] at hu ⊢
    exact ⟨mem_monOfDeg.mpr (by rw [map_add, Finsupp.degree_single, mem_monOfDeg.mp hu.1]),
      hclosed u hu.2 i⟩
  have hhf : ∀ e, hilbertFunction (L + purePowersIdeal hc d) e = (T e).card := fun e => by
    rw [hLP_eq]; exact hilbertFunction_monomialIdeal hT_iff hT_deg hT_sh e
  let A (e : ℕ) : Finset (Fin n →₀ ℕ) := (boxSlice hc d e).filter (fun u => u ∈ SL')
  have hT_split : ∀ e, (T e).card = (A e).card + (monOfDeg n e \ boxSlice hc d e).card := by
    intro e
    have heq : T e = A e ∪ (monOfDeg n e \ boxSlice hc d e) := by
      ext u
      simp only [T, A, boxSlice, mem_filter, mem_union, mem_sdiff, Set.mem_union, SP, clPureSet,
        Set.mem_ofPred_eq, inBoxPred]
      by_cases hin : ∀ j : Fin c, u (Fin.castLE hc j) < d j
      · have hnot : ¬ ∃ j : Fin c, d j ≤ u (Fin.castLE hc j) := by
          rintro ⟨j, hj⟩; have := hin j; omega
        simp [hin, hnot]
      · have hex : ∃ j : Fin c, d j ≤ u (Fin.castLE hc j) := by
          push Not at hin; exact hin
        simp [hin, hex]
    have hdisj : Disjoint (A e) (monOfDeg n e \ boxSlice hc d e) :=
      Finset.disjoint_left.mpr fun u h1 h2 => (mem_sdiff.mp h2).2 (mem_filter.mp h1).1
    rw [heq, Finset.card_union_of_disjoint hdisj]
  have hbox_add : ∀ e, (boxSlice hc d e).card + (monOfDeg n e \ boxSlice hc d e).card =
      (monOfDeg n e).card := fun e => by
    rw [add_comm]; exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have hq_eq : ∀ e, (A e).card + q e = (boxSlice hc d e).card := by
    intro e
    have h1 := hq e
    rw [hhf e, hT_split e] at h1
    have h2 := hbox_add e
    omega
  refine ⟨fun e => by have := hq_eq e; omega, fun e => ?_⟩
  have hA_lex : IsLexBox (clBound (n := n) d e) e (A e) := by
    rw [IsLexBox, monBox_clBound_eq_boxSlice hc d e e (by omega)]
    refine ⟨Finset.filter_subset _ _, fun u hu v hv hlt => ?_⟩
    rw [mem_filter] at hv ⊢
    refine ⟨hu, ?_⟩
    have huv : u.degree = v.degree := by
      rw [mem_monOfDeg.mp (mem_filter.mp hu).1, mem_monOfDeg.mp (mem_filter.mp hv.1).1]
    exact hlex u v huv hlt hv.2
  have hA_eq_seg : A e = lexSegBox (clBound (n := n) d e) e ((boxSlice hc d e).card - q e) := by
    have hcard : (A e).card = (boxSlice hc d e).card - q e := by have := hq_eq e; omega
    rw [← hcard]; exact hA_lex.eq_lexSegBox
  have hsh_sub : shadowBox (clBound (n := n) d e) (A e) ⊆ A (e + 1) := by
    have hA_deg : A e ⊆ monOfDeg n e :=
      Finset.Subset.trans (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [← shadow_filter_inBox_eq_shadowBox hc d e hA_deg]
    intro v hv
    rw [mem_filter, mem_shadow] at hv
    obtain ⟨⟨u, hu, i, rfl⟩, hin⟩ := hv
    rw [mem_filter] at hu ⊢
    refine ⟨mem_filter.mpr ⟨mem_monOfDeg.mpr (by
      rw [map_add, Finsupp.degree_single, mem_monOfDeg.mp (mem_filter.mp hu.1).1]), hin⟩, ?_⟩
    change monomial (u + Finsupp.single i 1) (1 : k) ∈ L
    have : monomial (u + Finsupp.single i 1) (1 : k) = X i * monomial u 1 := by
      rw [X, monomial_mul, one_mul, add_comm]
    rw [this]; exact L.mul_mem_left _ hu.2
  have hcard_sh : (shadowBox (clBound (n := n) d e) (A e)).card ≤ (A (e + 1)).card :=
    Finset.card_le_card hsh_sub
  unfold clNext
  rw [← hA_eq_seg]
  have hq1 := hq_eq (e + 1)
  omega
theorem isLPPSeq_to_lpp {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (q : ℕ → ℕ)
    (hle_box : ∀ e, q e ≤ (boxSlice hc d e).card)
    (hnext : ∀ e, q (e + 1) ≤ clNext hc d e (q e)) :
    ∃ L : Ideal (MvPolynomial (Fin n) k), IsLexIdeal L ∧
      ∀ e, hilbertFunction (L + purePowersIdeal hc d) e + q e = (monOfDeg n e).card := by
  classical
  let A (e : ℕ) : Finset (Fin n →₀ ℕ) :=
    lexSegBox (clBound (n := n) d e) e ((boxSlice hc d e).card - q e)
  have hA_sub : ∀ e, A e ⊆ boxSlice hc d e := fun e => by
    rw [← monBox_clBound_eq_boxSlice hc d e e (by omega)]
    exact lexSegBox_subset_monBox _ _ _
  have hA_card : ∀ e, (A e).card = (boxSlice hc d e).card - q e := fun e => by
    apply card_lexSegBox
    rw [monBox_clBound_eq_boxSlice hc d e e (by omega)]
    omega
  have hA_sh : ∀ e, (shadow (A e)).filter (inBoxPred hc d) ⊆ A (e + 1) := by
    intro e
    have hA_deg : A e ⊆ monOfDeg n e :=
      Finset.Subset.trans (hA_sub e) (Finset.filter_subset _ _)
    rw [shadow_filter_inBox_eq_shadowBox hc d e hA_deg]
    have hlex_next : IsLexBox (clBound (n := n) d e) (e + 1) (A (e + 1)) := by
      have h1 := isLexBox_lexSegBox (clBound (n := n) d (e + 1)) (e + 1)
        ((boxSlice hc d (e + 1)).card - q (e + 1))
      rw [IsLexBox, monBox_clBound_eq_boxSlice hc d (e + 1) (e + 1) (by omega)] at h1
      rw [IsLexBox, monBox_clBound_eq_boxSlice hc d e (e + 1) le_rfl]
      exact h1
    apply (isLexBox_lexSegBox (clBound (n := n) d e) e _).shadowBox.subset_of_card_le hlex_next
    rw [hA_card (e + 1)]
    have hn := hnext e
    unfold clNext at hn
    have hsh_le : (shadowBox (clBound (n := n) d e) (A e)).card ≤ (boxSlice hc d (e + 1)).card := by
      rw [← monBox_clBound_eq_boxSlice hc d e (e + 1) le_rfl]
      exact Finset.card_le_card (shadowBox_subset_monBox (lexSegBox_subset_monBox _ _ _))
    have hq1 := hle_box (e + 1)
    dsimp only [A] at hsh_le
    omega
  let F (e : ℕ) : Finset (Fin n →₀ ℕ) :=
    (monOfDeg n e).filter (fun u => ∀ v ∈ boxSlice hc d e \ A e, toLex v < toLex u)
  have hF_inter : ∀ e u, u ∈ boxSlice hc d e → (u ∈ F e ↔ u ∈ A e) := by
    intro e u huB
    simp only [F, mem_filter]
    have hu_deg : u ∈ monOfDeg n e := (mem_filter.mp huB).1
    constructor
    · rintro ⟨_, hgt⟩
      by_contra huA
      exact lt_irrefl _ (hgt u (mem_sdiff.mpr ⟨huB, huA⟩))
    · intro huA
      refine ⟨hu_deg, fun v hv => ?_⟩
      rw [mem_sdiff] at hv
      rcases lt_trichotomy (toLex v) (toLex u) with h | heq | h
      · exact h
      · exfalso; have hvu : v = u := heq; exact hv.2 (hvu ▸ huA)
      · exfalso
        have hlex := isLexBox_lexSegBox (clBound (n := n) d e) e ((boxSlice hc d e).card - q e)
        rw [IsLexBox, monBox_clBound_eq_boxSlice hc d e e (by omega)] at hlex
        exact hv.2 (hlex.2 v hv.1 u huA h)
  have hF_sh : ∀ e, shadow (F e) ⊆ F (e + 1) := by
    intro e
    have hsub : F e ⊆ monOfDeg n e := Finset.filter_subset _ _
    have hlex : ∀ u ∈ monOfDeg n e, ∀ v ∈ F e, toLex v < toLex u → u ∈ F e := by
      intro u hu v hv hlt
      rw [mem_filter] at hv ⊢
      exact ⟨hu, fun w hw => lt_trans (hv.2 w hw) hlt⟩
    intro x hx
    have hx_deg : x ∈ monOfDeg n (e + 1) := shadow_subset_monOfDeg hsub hx
    by_contra hx_n
    simp only [F, mem_filter, hx_deg, true_and, not_forall, not_lt] at hx_n
    obtain ⟨v, hv_sdiff, hxv⟩ := hx_n
    rw [mem_sdiff] at hv_sdiff
    obtain ⟨hvB, hvA⟩ := hv_sdiff
    have hv_deg : v ∈ monOfDeg n (e + 1) := (mem_filter.mp hvB).1
    have hv_sh : v ∈ shadow (F e) := by
      rcases eq_or_lt_of_le hxv with h | h
      · have : x = v := h; rwa [← this]
      · exact isLexFull_shadow hsub hlex v hv_deg x hx h
    rw [mem_shadow] at hv_sh
    obtain ⟨w, hw, i, hw_eq⟩ := hv_sh
    have hw_inBox : inBoxPred hc d w := by
      intro j
      have hv_in := (mem_filter.mp hvB).2 j
      have hle : w (Fin.castLE hc j) ≤ v (Fin.castLE hc j) := by rw [← hw_eq]; simp
      omega
    have hwB : w ∈ boxSlice hc d e := mem_filter.mpr ⟨hsub hw, hw_inBox⟩
    have hwA : w ∈ A e := (hF_inter e w hwB).mp hw
    have hv_in_sh : v ∈ (shadow (A e)).filter (inBoxPred hc d) :=
      mem_filter.mpr ⟨mem_shadow.mpr ⟨w, hwA, i, hw_eq⟩, (mem_filter.mp hvB).2⟩
    exact hvA (hA_sh e hv_in_sh)
  let SL : Set (Fin n →₀ ℕ) := { u | u ∈ F u.degree }
  have hSL_closed : ∀ u ∈ SL, ∀ i : Fin n, u + Finsupp.single i 1 ∈ SL := by
    intro u hu i
    simp only [SL, Set.mem_ofPred_eq, map_add, Finsupp.degree_single] at hu ⊢
    exact hF_sh u.degree (mem_shadow.mpr ⟨u, hu, i, rfl⟩)
  let L : Ideal (MvPolynomial (Fin n) k) := Ideal.span ((fun u => monomial u (1 : k)) '' SL)
  refine ⟨L, ⟨⟨SL, rfl⟩, ?_⟩, ?_⟩
  · intro u v huv hlt hvL
    rw [mem_monomialIdeal_iff_support hSL_closed] at hvL ⊢
    intro w hw
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hw
    rw [hw]
    have hvS : v ∈ F v.degree := hvL v (by
      rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton])
    simp only [SL, Set.mem_ofPred_eq, huv, F, mem_filter] at hvS ⊢
    exact ⟨mem_monOfDeg.mpr huv, fun x hx => lt_trans (hvS.2 x hx) hlt⟩
  · let T (e : ℕ) : Finset (Fin n →₀ ℕ) := A e ∪ (monOfDeg n e \ boxSlice hc d e)
    have hT_deg : ∀ e, T e ⊆ monOfDeg n e := fun e u hu => by
      rw [mem_union] at hu
      rcases hu with h | h
      · exact (mem_filter.mp (hA_sub e h)).1
      · exact (mem_sdiff.mp h).1
    have hT_iff : ∀ u, u ∈ SL ∪ clPureSet hc d ↔ u ∈ T u.degree := by
      intro u
      have hu_deg : u ∈ monOfDeg n u.degree := mem_monOfDeg.mpr rfl
      simp only [Set.mem_union, T, mem_union, mem_sdiff]
      by_cases hin : inBoxPred hc d u
      · have huB : u ∈ boxSlice hc d u.degree := mem_filter.mpr ⟨hu_deg, hin⟩
        have huSP : u ∉ clPureSet hc d := by rintro ⟨j, hj⟩; have := hin j; omega
        simp only [huSP, or_false, huB, not_true_eq_false, and_false]
        exact hF_inter u.degree u huB
      · have huB : u ∉ boxSlice hc d u.degree := fun h => hin (mem_filter.mp h).2
        have huSP : u ∈ clPureSet hc d := by unfold inBoxPred at hin; push Not at hin; exact hin
        simp only [huSP, or_true, hu_deg, huB, not_false_eq_true, and_self]
    have hT_sh : ∀ e, shadow (T e) ⊆ T (e + 1) := by
      intro e v hv
      rw [mem_shadow] at hv
      obtain ⟨u, hu, i, rfl⟩ := hv
      have hv_deg : (u + Finsupp.single i 1).degree = e + 1 := by
        rw [map_add, Finsupp.degree_single, mem_monOfDeg.mp (hT_deg e hu)]
      rw [← hv_deg, ← hT_iff]
      have hu' : u ∈ SL ∪ clPureSet hc d :=
        (hT_iff u).mpr (by rw [mem_monOfDeg.mp (hT_deg e hu)]; exact hu)
      rcases hu' with huSL | ⟨j, hj⟩
      · exact Or.inl (hSL_closed u huSL i)
      · exact Or.inr ⟨j, by simp only [Finsupp.coe_add, Pi.add_apply]; omega⟩
    have hsum_eq : L + purePowersIdeal hc d =
        Ideal.span ((fun u => monomial u (1 : k)) '' (SL ∪ clPureSet hc d)) := by
      rw [Submodule.add_eq_sup, purePowersIdeal_eq_monomialIdeal hc d, ← Ideal.span_union,
        Set.image_union]; rfl
    intro e
    rw [hsum_eq, hilbertFunction_monomialIdeal hT_iff hT_deg hT_sh e]
    have hdisj : Disjoint (A e) (monOfDeg n e \ boxSlice hc d e) :=
      Finset.disjoint_left.mpr fun x h1 h2 => (mem_sdiff.mp h2).2 (hA_sub e h1)
    have hbox_add : (boxSlice hc d e).card + (monOfDeg n e \ boxSlice hc d e).card =
        (monOfDeg n e).card := by
      rw [add_comm]; exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
    rw [Finset.card_union_of_disjoint hdisj, hA_card e]
    have hle := hle_box e
    omega
theorem duality_clNext {d : Fin n → ℕ} (hd : ∀ j : Fin n, 1 ≤ d j)
    {e r_e r_e1 : ℕ} (he : e < ∑ j : Fin n, (d j - 1))
    (hr_e : r_e ≤ (boxSlice le_rfl d e).card)
    (hr_e1 : r_e1 ≤ (boxSlice le_rfl d (e + 1)).card)
    (hdual : (boxSlice le_rfl d (∑ j : Fin n, (d j - 1) - e)).card - r_e ≤
      clNext le_rfl d (∑ j : Fin n, (d j - 1) - e - 1)
        ((boxSlice le_rfl d (∑ j : Fin n, (d j - 1) - e - 1)).card - r_e1)) :
    r_e1 ≤ clNext le_rfl d e r_e := by
  classical
  set s := ∑ j : Fin n, (d j - 1)
  set e' := s - e - 1
  have he'1 : e' + 1 = s - e := by omega
  let uTop : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => d i - 1)
  have huTop_app : ∀ i, uTop i = d i - 1 := fun _ => rfl
  have huTop_deg : uTop.degree = s := by rw [Finsupp.degree_eq_sum]; rfl
  let τ : (Fin n →₀ ℕ) → (Fin n →₀ ℕ) := fun u => uTop - u
  have hτ_le : ∀ {m} {u : Fin n →₀ ℕ}, u ∈ boxSlice le_rfl d m → u ≤ uTop := by
    intro m u hu
    rw [Finsupp.le_def]
    intro i; rw [huTop_app]; have := (mem_filter.mp hu).2 i; change u i < d i at this; omega
  have hτ_inv : ∀ {m} {u : Fin n →₀ ℕ}, u ∈ boxSlice le_rfl d m → τ (τ u) = u := by
    intro m u hu; ext i
    have hle := Finsupp.le_def.mp (hτ_le hu) i
    simp only [τ, Finsupp.coe_tsub, Pi.sub_apply]; omega
  have hτ_mem : ∀ {m} {u : Fin n →₀ ℕ}, m ≤ s → u ∈ boxSlice le_rfl d m →
      τ u ∈ boxSlice le_rfl d (s - m) := by
    intro m u hm hu
    rw [boxSlice, mem_filter, mem_monOfDeg] at hu ⊢
    have hle := hτ_le (mem_filter.mpr ⟨mem_monOfDeg.mpr hu.1, hu.2⟩)
    refine ⟨?_, fun i => ?_⟩
    · have hadd := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
      rw [map_add, huTop_deg, hu.1] at hadd
      change (uTop - u).degree = s - m; omega
    · have := hd i; change (uTop - u) i < d i
      simp only [Finsupp.coe_tsub, Pi.sub_apply, huTop_app]; omega
  have hτ_rev : ∀ {m} {u v : Fin n →₀ ℕ}, u ∈ boxSlice le_rfl d m → v ∈ boxSlice le_rfl d m →
      (toLex u < toLex v ↔ toLex (τ v) < toLex (τ u)) := by
    intro m u v hu hv
    have hlu := hτ_le hu; have hlv := hτ_le hv
    simp only [lex_lt_iff]
    constructor <;> rintro ⟨i, heq, hlt⟩ <;> refine ⟨i, fun j hj => ?_, ?_⟩
    · have h1 := Finsupp.le_def.mp hlu j; have h2 := Finsupp.le_def.mp hlv j
      have := heq j hj; simp only [τ, Finsupp.coe_tsub, Pi.sub_apply]; omega
    · have h1 := Finsupp.le_def.mp hlu i; have h2 := Finsupp.le_def.mp hlv i
      simp only [τ, Finsupp.coe_tsub, Pi.sub_apply]; omega
    · have h1 := Finsupp.le_def.mp hlu j; have h2 := Finsupp.le_def.mp hlv j
      have := heq j hj; simp only [τ, Finsupp.coe_tsub, Pi.sub_apply] at this; omega
    · have h1 := Finsupp.le_def.mp hlu i; have h2 := Finsupp.le_def.mp hlv i
      simp only [τ, Finsupp.coe_tsub, Pi.sub_apply] at hlt; omega
  have hcard_symm : ∀ m ≤ s, (boxSlice le_rfl d m).card = (boxSlice le_rfl d (s - m)).card := by
    intro m hm
    refine Finset.card_bij (fun u _ => τ u) (fun u hu => hτ_mem hm hu)
      (fun u₁ hu₁ u₂ hu₂ h => by rw [← hτ_inv hu₁, ← hτ_inv hu₂, h])
      (fun v hv => ⟨τ v, by
        have h1 := hτ_mem (Nat.sub_le s m) hv
        rwa [Nat.sub_sub_self hm] at h1, hτ_inv hv⟩)
  have hcard_e' : (boxSlice le_rfl d e').card = (boxSlice le_rfl d (e + 1)).card := by
    have h1 := hcard_symm (e + 1) (by omega)
    have h2 : s - (e + 1) = e' := by omega
    rw [h2] at h1; exact h1.symm
  have hcard_e'1 : (boxSlice le_rfl d (e' + 1)).card = (boxSlice le_rfl d e).card := by
    rw [he'1]; exact (hcard_symm e (by omega)).symm
  let A := lexSegBox (clBound (n := n) d e') e' r_e1
  let SA := shadowBox (clBound (n := n) d e') A
  have hSA_le : SA.card ≤ r_e := by
    unfold clNext at hdual
    rw [he'1] at hdual
    have hsub_r : (boxSlice le_rfl d e').card - ((boxSlice le_rfl d e').card - r_e1) = r_e1 := by
      omega
    rw [hsub_r] at hdual
    have hSA_box : SA.card ≤ (boxSlice le_rfl d (s - e)).card := by
      rw [← he'1, ← monBox_clBound_eq_boxSlice le_rfl d e' (e' + 1) le_rfl]
      exact Finset.card_le_card (shadowBox_subset_monBox (lexSegBox_subset_monBox _ _ _))
    rw [← he'1] at hdual hSA_box
    dsimp only [SA, A] at hSA_box ⊢
    omega
  let C := (boxSlice le_rfl d (e' + 1) \ SA).image τ
  have hC_lex : IsLexBox (clBound (n := n) d e) e C := by
    rw [IsLexBox, monBox_clBound_eq_boxSlice le_rfl d e e (by omega)]
    refine ⟨?_, ?_⟩
    · intro w hw
      rw [mem_image] at hw; obtain ⟨v, hv, rfl⟩ := hw
      have h1 := hτ_mem (by omega : e' + 1 ≤ s) (mem_sdiff.mp hv).1
      have h2 : s - (e' + 1) = e := by omega
      rwa [h2] at h1
    · intro u hu w hw hlt
      rw [mem_image] at hw ⊢
      obtain ⟨v, hv, rfl⟩ := hw
      have hvB := (mem_sdiff.mp hv).1
      have hv_notSA := (mem_sdiff.mp hv).2
      have hτuB : τ u ∈ boxSlice le_rfl d (e' + 1) := by
        have h1 := hτ_mem (by omega : e ≤ s) hu; rwa [← he'1] at h1
      refine ⟨τ u, mem_sdiff.mpr ⟨hτuB, ?_⟩, hτ_inv hu⟩
      intro hτu_SA
      have hSA_lex := (isLexBox_lexSegBox (clBound (n := n) d e') e' r_e1).shadowBox
      rw [IsLexBox, monBox_clBound_eq_boxSlice le_rfl d e' (e' + 1) le_rfl] at hSA_lex
      have hτv_mem : τ v ∈ boxSlice le_rfl d e := by
        have h1 := hτ_mem (by omega : e' + 1 ≤ s) hvB
        have h2 : s - (e' + 1) = e := by omega
        rw [h2] at h1; exact h1
      have hv_gt : toLex (τ u) < toLex v := by
        have hrev := (hτ_rev (m := e) (u := τ v) (v := u) hτv_mem hu).mp hlt
        rwa [hτ_inv hvB] at hrev
      exact hv_notSA (hSA_lex.2 v hvB (τ u) hτu_SA hv_gt)
  have hC_card : (boxSlice le_rfl d e).card - r_e ≤ C.card := by
    have hinj : Set.InjOn τ (↑(boxSlice le_rfl d (e' + 1) \ SA) : Set (Fin n →₀ ℕ)) :=
      fun u₁ hu₁ u₂ hu₂ h => by
        rw [Finset.mem_coe, mem_sdiff] at hu₁ hu₂
        rw [← hτ_inv hu₁.1, ← hτ_inv hu₂.1, h]
    rw [Finset.card_image_of_injOn hinj]
    have hSA_sub : SA ⊆ boxSlice le_rfl d (e' + 1) := by
      rw [← monBox_clBound_eq_boxSlice le_rfl d e' (e' + 1) le_rfl]
      exact shadowBox_subset_monBox (lexSegBox_subset_monBox _ _ _)
    have hsplit := Finset.card_sdiff_add_card_eq_card hSA_sub
    omega
  let B := lexSegBox (clBound (n := n) d e) e ((boxSlice le_rfl d e).card - r_e)
  have hB_sub_C : B ⊆ C := by
    apply (isLexBox_lexSegBox (clBound (n := n) d e) e _).subset_of_card_le hC_lex
    rw [card_lexSegBox (by rw [monBox_clBound_eq_boxSlice le_rfl d e e (by omega)]; omega)]
    exact hC_card
  let τA := A.image τ
  have hτA_sub : τA ⊆ boxSlice le_rfl d (e + 1) := by
    intro w hw; rw [mem_image] at hw; obtain ⟨v, hv, rfl⟩ := hw
    have hvB : v ∈ boxSlice le_rfl d e' := by
      rw [← monBox_clBound_eq_boxSlice le_rfl d e' e' (by omega)]
      exact lexSegBox_subset_monBox _ _ _ hv
    have h1 := hτ_mem (by omega : e' ≤ s) hvB
    have h2 : s - e' = e + 1 := by omega
    rwa [h2] at h1
  have hτA_card : τA.card = r_e1 := by
    have hinj : Set.InjOn τ (A : Set (Fin n →₀ ℕ)) := fun u₁ hu₁ u₂ hu₂ h => by
      have h1 : u₁ ∈ boxSlice le_rfl d e' := by
        rw [← monBox_clBound_eq_boxSlice le_rfl d e' e' (by omega)]
        exact lexSegBox_subset_monBox _ _ _ hu₁
      have h2 : u₂ ∈ boxSlice le_rfl d e' := by
        rw [← monBox_clBound_eq_boxSlice le_rfl d e' e' (by omega)]
        exact lexSegBox_subset_monBox _ _ _ hu₂
      rw [← hτ_inv h1, ← hτ_inv h2, h]
    rw [Finset.card_image_of_injOn hinj, card_lexSegBox]
    rw [monBox_clBound_eq_boxSlice le_rfl d e' e' (by omega)]; omega
  have hdisj : Disjoint (shadowBox (clBound (n := n) d e) B) τA := by
    rw [Finset.disjoint_left]
    intro y hyB hyA
    have hy_box : y ∈ boxSlice le_rfl d (e + 1) := hτA_sub hyA
    rw [mem_shadowBox] at hyB
    obtain ⟨⟨w, hwB, i, rfl⟩, _⟩ := hyB
    rw [mem_image] at hyA
    obtain ⟨v, hvA, hv_eq⟩ := hyA
    have hwC : w ∈ C := hB_sub_C hwB
    rw [mem_image] at hwC
    obtain ⟨z, hz, hz_eq⟩ := hwC
    have hzB := (mem_sdiff.mp hz).1
    have hz_notSA := (mem_sdiff.mp hz).2
    have hvB : v ∈ boxSlice le_rfl d e' := by
      rw [← monBox_clBound_eq_boxSlice le_rfl d e' e' (by omega)]
      exact lexSegBox_subset_monBox _ _ _ hvA
    have hz_eq_v : v + Finsupp.single i 1 = z := by
      ext j
      have h1 := congrArg (fun f : Fin n →₀ ℕ => f j) hv_eq
      have h2 := congrArg (fun f : Fin n →₀ ℕ => f j) hz_eq
      have hle_v := Finsupp.le_def.mp (hτ_le hvB) j
      have hle_z := Finsupp.le_def.mp (hτ_le hzB) j
      simp only [τ, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply] at h1 h2 ⊢
      omega
    apply hz_notSA
    have hA_deg : A ⊆ monOfDeg n e' := by
      intro x hx
      have hxB : x ∈ boxSlice le_rfl d e' := by
        rw [← monBox_clBound_eq_boxSlice le_rfl d e' e' (by omega)]
        exact lexSegBox_subset_monBox _ _ _ hx
      exact (mem_filter.mp hxB).1
    dsimp only [SA]
    rw [← shadow_filter_inBox_eq_shadowBox le_rfl d e' hA_deg]
    exact mem_filter.mpr ⟨mem_shadow.mpr ⟨v, hvA, i, hz_eq_v⟩, (mem_filter.mp hzB).2⟩
  have hsub_u : shadowBox (clBound (n := n) d e) B ∪ τA ⊆ boxSlice le_rfl d (e + 1) := by
    refine Finset.union_subset ?_ hτA_sub
    rw [← monBox_clBound_eq_boxSlice le_rfl d e (e + 1) le_rfl]
    exact shadowBox_subset_monBox (lexSegBox_subset_monBox _ _ _)
  have hle_card := Finset.card_le_card hsub_u
  rw [Finset.card_union_of_disjoint hdisj, hτA_card] at hle_card
  unfold clNext
  dsimp only [B] at hle_card
  omega
lemma boxSlice_eq_castSucc_of_lt_last {m : ℕ} (d : Fin (m + 1) → ℕ)
    {e : ℕ} (he : e < d (Fin.last m)) :
    boxSlice le_rfl d e = boxSlice (Nat.le_succ m) (d ∘ Fin.castSucc) e := by
  classical
  ext u
  simp only [boxSlice, mem_filter, mem_monOfDeg, inBoxPred]
  constructor
  · rintro ⟨hdeg, hin⟩
    exact ⟨hdeg, fun j => hin j.castSucc⟩
  · rintro ⟨hdeg, hin⟩
    refine ⟨hdeg, fun j => ?_⟩
    cases j using Fin.lastCases with
    | last =>
      have hle : u (Fin.last m) ≤ ∑ i : Fin (m + 1), u i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      rw [← Finsupp.degree_eq_sum, hdeg] at hle
      change u (Fin.last m) < d (Fin.last m); omega
    | cast i => exact hin i
lemma clNext_eq_castSucc_of_lt_last {m : ℕ} (d : Fin (m + 1) → ℕ)
    {e : ℕ} (he : e + 1 < d (Fin.last m)) (r : ℕ) :
    clNext le_rfl d e r = clNext (Nat.le_succ m) (d ∘ Fin.castSucc) e r := by
  classical
  let d' : Fin m → ℕ := d ∘ Fin.castSucc
  have hbox_e : boxSlice le_rfl d e = boxSlice (Nat.le_succ m) d' e :=
    boxSlice_eq_castSucc_of_lt_last d (by omega)
  have hbox_e1 : boxSlice le_rfl d (e + 1) = boxSlice (Nat.le_succ m) d' (e + 1) :=
    boxSlice_eq_castSucc_of_lt_last d he
  have hlex_eq : lexSegBox (clBound (n := m + 1) d e) e ((boxSlice le_rfl d e).card - r) =
      lexSegBox (clBound (n := m + 1) d' e) e ((boxSlice (Nat.le_succ m) d' e).card - r) := by
    unfold lexSegBox
    rw [monBox_clBound_eq_boxSlice le_rfl d e e (by omega),
      monBox_clBound_eq_boxSlice (Nat.le_succ m) d' e e (by omega), hbox_e]
  have hsh_eq : shadowBox (clBound (n := m + 1) d e)
        (lexSegBox (clBound (n := m + 1) d e) e ((boxSlice le_rfl d e).card - r)) =
      shadowBox (clBound (n := m + 1) d' e)
        (lexSegBox (clBound (n := m + 1) d' e) e ((boxSlice (Nat.le_succ m) d' e).card - r)) := by
    rw [hlex_eq]
    have hsub : lexSegBox (clBound (n := m + 1) d' e) e ((boxSlice (Nat.le_succ m) d' e).card - r) ⊆
        monOfDeg (m + 1) e := by
      intro u hu
      have h1 := lexSegBox_subset_monBox _ _ _ hu
      rw [monBox_clBound_eq_boxSlice (Nat.le_succ m) d' e e (by omega)] at h1
      exact (mem_filter.mp h1).1
    rw [← shadow_filter_inBox_eq_shadowBox le_rfl d e hsub,
      ← shadow_filter_inBox_eq_shadowBox (Nat.le_succ m) d' e hsub]
    ext v
    simp only [mem_filter]
    constructor
    · rintro ⟨hv, hin⟩; exact ⟨hv, fun j => hin j.castSucc⟩
    · rintro ⟨hv, hin⟩
      refine ⟨hv, fun j => ?_⟩
      cases j using Fin.lastCases with
      | last =>
        have hdeg : v.degree = e + 1 := mem_monOfDeg.mp (shadow_subset_monOfDeg hsub hv)
        have hle : v (Fin.last m) ≤ ∑ i : Fin (m + 1), v i :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        rw [← Finsupp.degree_eq_sum, hdeg] at hle
        change v (Fin.last m) < d (Fin.last m); omega
      | cast i => exact hin i
  unfold clNext
  rw [hbox_e1, hsh_eq]
theorem clNext_at_sigma_sub_one {m : ℕ} (hm : 2 ≤ m) (d : Fin (m + 1) → ℕ)
    (hd : ∀ j : Fin (m + 1), 2 ≤ d j)
    (hlast : d (Fin.last m) = ∑ j : Fin m, (d j.castSucc - 1)) :
    let d' : Fin m → ℕ := d ∘ Fin.castSucc
    let σ := ∑ j : Fin m, (d' j - 1)
    (∀ r, 0 < r → r < (boxSlice (Nat.le_succ m) d' (σ - 1)).card →
      clNext (Nat.le_succ m) d' (σ - 1) r = r ∧
      clNext le_rfl d (σ - 1) r = r - 1) ∧
    (let d'' : Fin (m + 1) → ℕ := Fin.lastCases (σ - 1) d'
     (boxSlice le_rfl d'' (σ - 1)).card = (boxSlice (Nat.le_succ m) d' (σ - 1)).card - 1 ∧
     (boxSlice le_rfl d'' σ).card = (boxSlice (Nat.le_succ m) d' (σ - 2)).card) := by
  classical
  intro d' σ
  have hσ_ge2 : 2 ≤ σ := by
    let j0 : Fin m := ⟨0, by omega⟩
    let j1 : Fin m := ⟨1, by omega⟩
    have hne : j0 ≠ j1 := by intro h; have := congrArg Fin.val h; simp [j0, j1] at this
    have hpair : (d' j0 - 1) + (d' j1 - 1) ≤ σ := by
      have hsub : ∑ j ∈ ({j0, j1} : Finset (Fin m)), (d' j - 1) ≤ σ :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      rwa [Finset.sum_pair hne] at hsub
    have h0 : 2 ≤ d' j0 := hd j0.castSucc
    have h1 : 2 ≤ d' j1 := hd j1.castSucc
    omega
  have hσ_pos : 1 ≤ σ := by omega
  let vTop : Fin (m + 1) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (Fin.lastCases 0 (fun j => d' j - 1))
  have hvTop_last : vTop (Fin.last m) = 0 := by
    change Fin.lastCases 0 (fun j => d' j - 1) (Fin.last m) = 0; simp
  have hvTop_cast : ∀ j : Fin m, vTop j.castSucc = d' j - 1 := fun j => by
    change Fin.lastCases 0 (fun r => d' r - 1) j.castSucc = d' j - 1; simp
  have hvTop_deg : vTop.degree = σ := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_castSucc, hvTop_last, add_zero]
    exact Finset.sum_congr rfl fun j _ => hvTop_cast j
  have hvTop_mem : vTop ∈ boxSlice (Nat.le_succ m) d' σ := by
    rw [boxSlice, mem_filter, mem_monOfDeg]
    refine ⟨hvTop_deg, fun j => ?_⟩
    change vTop j.castSucc < d' j
    rw [hvTop_cast]; have hdj : 2 ≤ d' j := hd j.castSucc; omega
  have hvTop_uniq : ∀ v ∈ boxSlice (Nat.le_succ m) d' σ, v (Fin.last m) = 0 → v = vTop := by
    intro v hv h0
    have hdeg := mem_monOfDeg.mp (mem_filter.mp hv).1
    have hin := (mem_filter.mp hv).2
    have hle_all : ∀ j : Fin m, v j.castSucc ≤ d' j - 1 := fun j => by
      have := hin j; change v j.castSucc < d' j at this; omega
    ext r
    cases r using Fin.lastCases with
    | last => rw [h0, hvTop_last]
    | cast j =>
      rw [hvTop_cast]
      by_contra hne
      have hlt : v j.castSucc < d' j - 1 := lt_of_le_of_ne (hle_all j) hne
      have hsum_lt : ∑ i : Fin m, v i.castSucc < ∑ i : Fin m, (d' i - 1) :=
        Finset.sum_lt_sum (fun i _ => hle_all i) ⟨j, Finset.mem_univ j, hlt⟩
      have hsum_v : ∑ i : Fin m, v i.castSucc = σ := by
        have := hdeg; rw [Finsupp.degree_eq_sum, Fin.sum_univ_castSucc, h0, add_zero] at this
        exact this
      omega
  let shift : (Fin (m + 1) →₀ ℕ) → (Fin (m + 1) →₀ ℕ) := fun u => u + Finsupp.single (Fin.last m) 1
  have hshift_inj : Function.Injective shift := fun _ _ h => add_right_cancel h
  have hbox_σ_eq : boxSlice (Nat.le_succ m) d' σ =
      insert vTop ((boxSlice (Nat.le_succ m) d' (σ - 1)).image shift) := by
    ext v
    simp only [mem_insert, mem_image]
    constructor
    · intro hv
      by_cases h0 : v (Fin.last m) = 0
      · exact Or.inl (hvTop_uniq v hv h0)
      · right
        have hpos : 1 ≤ v (Fin.last m) := Nat.pos_of_ne_zero h0
        refine ⟨v - Finsupp.single (Fin.last m) 1, ?_, sub_single_add_single hpos⟩
        rw [boxSlice, mem_filter, mem_monOfDeg] at hv ⊢
        refine ⟨by have := degree_sub_single hpos; omega, fun j => ?_⟩
        have hne : j.castSucc ≠ Fin.last m := Fin.castSucc_ne_last j
        have := hv.2 j
        change (v - Finsupp.single (Fin.last m) (1 : ℕ)) j.castSucc < d' j
        simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne hne, Nat.sub_zero]
        exact this
    · rintro (rfl | ⟨u, hu, rfl⟩)
      · exact hvTop_mem
      · rw [boxSlice, mem_filter, mem_monOfDeg] at hu ⊢
        refine ⟨by rw [map_add, Finsupp.degree_single, hu.1]; omega, fun j => ?_⟩
        have hne : j.castSucc ≠ Fin.last m := Fin.castSucc_ne_last j
        have := hu.2 j
        change (u + Finsupp.single (Fin.last m) (1 : ℕ)) j.castSucc < d' j
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne hne, add_zero]
        exact this
  have hvTop_not_img : vTop ∉ (boxSlice (Nat.le_succ m) d' (σ - 1)).image shift := by
    rw [mem_image]; rintro ⟨u, _, hu⟩
    have h1 := congrArg (fun f : Fin (m + 1) →₀ ℕ => f (Fin.last m)) hu
    simp [shift, hvTop_last] at h1
  have hcard_σ : (boxSlice (Nat.le_succ m) d' σ).card =
      (boxSlice (Nat.le_succ m) d' (σ - 1)).card + 1 := by
    rw [hbox_σ_eq, Finset.card_insert_of_notMem hvTop_not_img,
      Finset.card_image_of_injective _ hshift_inj]
  let uLast : Fin (m + 1) →₀ ℕ := Finsupp.single (Fin.last m) σ
  have huLast_mem : uLast ∈ boxSlice (Nat.le_succ m) d' σ := by
    rw [boxSlice, mem_filter, mem_monOfDeg]
    refine ⟨Finsupp.degree_single _ _, fun j => ?_⟩
    have hne : j.castSucc ≠ Fin.last m := Fin.castSucc_ne_last j
    change uLast j.castSucc < d' j
    simp only [uLast, Finsupp.single_eq_of_ne hne]
    have hdj : 2 ≤ d' j := hd j.castSucc; omega
  have hbox_d_σ : boxSlice le_rfl d σ = (boxSlice (Nat.le_succ m) d' σ).erase uLast := by
    ext v
    simp only [mem_erase, boxSlice, mem_filter, mem_monOfDeg, inBoxPred]
    constructor
    · rintro ⟨hdeg, hin⟩
      refine ⟨?_, hdeg, fun j => hin j.castSucc⟩
      intro rfl
      have := hin (Fin.last m)
      change uLast (Fin.last m) < d (Fin.last m) at this
      simp only [uLast, Finsupp.single_eq_same] at this
      have : d (Fin.last m) = σ := hlast
      omega
    · rintro ⟨hne, hdeg, hin⟩
      refine ⟨hdeg, fun j => ?_⟩
      cases j using Fin.lastCases with
      | last =>
        change v (Fin.last m) < d (Fin.last m)
        have hle : v (Fin.last m) ≤ ∑ i : Fin (m + 1), v i :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        rw [← Finsupp.degree_eq_sum, hdeg] at hle
        have hlt : v (Fin.last m) < σ := by
          by_contra hge
          have heq_last : v (Fin.last m) = σ := by omega
          apply hne; ext r
          cases r using Fin.lastCases with
          | last => simp [uLast, heq_last]
          | cast i =>
            simp only [uLast, Finsupp.single_eq_of_ne (Fin.castSucc_ne_last i)]
            have hsum : (∑ j : Fin m, v j.castSucc) + v (Fin.last m) = σ := by
              rw [← Fin.sum_univ_castSucc, ← Finsupp.degree_eq_sum, hdeg]
            have hle_i : v i.castSucc ≤ ∑ j : Fin m, v j.castSucc :=
              Finset.single_le_sum (f := fun j : Fin m => v j.castSucc) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
            omega
        have : d (Fin.last m) = σ := hlast; omega
      | cast i => exact hin i
  have hcard_d_σ : (boxSlice le_rfl d σ).card = (boxSlice (Nat.le_succ m) d' (σ - 1)).card := by
    rw [hbox_d_σ, Finset.card_erase_of_mem huLast_mem, hcard_σ]; omega
  constructor
  · intro r hr_pos hr_lt
    have hbox_eq : boxSlice le_rfl d (σ - 1) = boxSlice (Nat.le_succ m) d' (σ - 1) :=
      boxSlice_eq_castSucc_of_lt_last d (by have : d (Fin.last m) = σ := hlast; omega)
    let mA := (boxSlice (Nat.le_succ m) d' (σ - 1)).card - r
    have hmA_pos : 0 < mA := by omega
    have hmA_lt : mA < (boxSlice (Nat.le_succ m) d' (σ - 1)).card := by omega
    let A := lexSegBox (clBound (n := m + 1) d' (σ - 1)) (σ - 1) mA
    have hA_lex := isLexBox_lexSegBox (clBound (n := m + 1) d' (σ - 1)) (σ - 1) mA
    have hA_card : A.card = mA := by
      apply card_lexSegBox
      rw [monBox_clBound_eq_boxSlice (Nat.le_succ m) d' (σ - 1) (σ - 1) (by omega)]; omega
    have hA_sub : A ⊆ boxSlice (Nat.le_succ m) d' (σ - 1) := by
      rw [← monBox_clBound_eq_boxSlice (Nat.le_succ m) d' (σ - 1) (σ - 1) (by omega)]
      exact hA_lex.1
    have hA_deg : A ⊆ monOfDeg (m + 1) (σ - 1) :=
      Finset.Subset.trans hA_sub (Finset.filter_subset _ _)
    have hsh_eq : shadowBox (clBound (n := m + 1) d' (σ - 1)) A = insert vTop (A.image shift) := by
      have hdeg_s : σ - 1 + 1 = σ := by omega
      rw [← shadow_filter_inBox_eq_shadowBox (Nat.le_succ m) d' (σ - 1) hA_deg]
      ext w
      simp only [mem_filter, mem_shadow, mem_insert, mem_image]
      constructor
      · rintro ⟨⟨u, huA, i, rfl⟩, hin⟩
        have hwB : u + Finsupp.single i 1 ∈ boxSlice (Nat.le_succ m) d' σ := by
          rw [boxSlice, mem_filter, mem_monOfDeg]
          exact ⟨by rw [map_add, Finsupp.degree_single, mem_monOfDeg.mp (hA_deg huA)]; omega, hin⟩
        by_cases h0 : (u + Finsupp.single i (1 : ℕ)) (Fin.last m) = 0
        · exact Or.inl (hvTop_uniq _ hwB h0)
        · right
          cases i using Fin.lastCases with
          | last => exact ⟨u, huA, rfl⟩
          | cast j =>
            have hu_last : 1 ≤ u (Fin.last m) := by
              have hne : Fin.last m ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
              simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne hne, add_zero] at h0
              exact Nat.pos_of_ne_zero h0
            let u' := u + Finsupp.single j.castSucc 1 - Finsupp.single (Fin.last m) 1
            have hu'_shift : shift u' = u + Finsupp.single j.castSucc 1 := by
              dsimp only [shift, u']
              exact sub_single_add_single (by
                have hne : Fin.last m ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
                simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne hne, add_zero]
                exact hu_last)
            refine ⟨u', ?_, hu'_shift⟩
            have hu'_box : u' ∈ monBox (clBound (n := m + 1) d' (σ - 1)) (σ - 1) := by
              rw [monBox_clBound_eq_boxSlice (Nat.le_succ m) d' (σ - 1) (σ - 1) (by omega),
                boxSlice, mem_filter, mem_monOfDeg]
              refine ⟨?_, fun t => ?_⟩
              · have h1 := congrArg Finsupp.degree hu'_shift
                rw [map_add, Finsupp.degree_single, map_add, Finsupp.degree_single,
                  mem_monOfDeg.mp (hA_deg huA)] at h1; omega
              · have hne : t.castSucc ≠ Fin.last m := Fin.castSucc_ne_last t
                have ht := hin t
                change u' t.castSucc < d' t
                simp only [u', Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne hne,
                  Nat.sub_zero]
                exact ht
            apply hA_lex.2 u' hu'_box u huA
            rw [lex_lt_iff]
            refine ⟨j.castSucc, fun t ht => ?_, ?_⟩
            · have ht1 : t ≠ j.castSucc := ne_of_lt ht
              have ht2 : t ≠ Fin.last m := ne_of_lt (lt_trans ht (Fin.castSucc_lt_last j))
              simp only [u', Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
                Finsupp.single_eq_of_ne ht1, Finsupp.single_eq_of_ne ht2, add_zero, Nat.sub_zero]
            · have hne : j.castSucc ≠ Fin.last m := Fin.castSucc_ne_last j
              simp only [u', Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
                Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne, Nat.sub_zero]
              omega
      · rintro (rfl | ⟨u, huA, rfl⟩)
        ·
          have hA_ne : A.Nonempty := Finset.card_pos.mp (by omega)
          obtain ⟨u0, hu0⟩ := hA_ne
          let j0 : Fin m := ⟨m - 1, by omega⟩
          let uTop' := vTop - Finsupp.single j0.castSucc 1
          have hvTop_j0 : 1 ≤ vTop j0.castSucc := by
            rw [hvTop_cast]; have hdj0 : 2 ≤ d' j0 := hd j0.castSucc; omega
          have huTop'_add : uTop' + Finsupp.single j0.castSucc 1 = vTop :=
            sub_single_add_single hvTop_j0
          have huTop'_box : uTop' ∈ boxSlice (Nat.le_succ m) d' (σ - 1) := by
            rw [boxSlice, mem_filter, mem_monOfDeg]
            refine ⟨by have hdeg_u := degree_sub_single hvTop_j0; rw [hvTop_deg] at hdeg_u; change uTop'.degree + 1 = σ at hdeg_u; omega, fun t => ?_⟩
            change uTop' t.castSucc < d' t
            have ht := (mem_filter.mp hvTop_mem).2 t
            change vTop t.castSucc < d' t at ht
            simp only [uTop', Finsupp.coe_tsub, Pi.sub_apply]; omega
          have huTop'_A : uTop' ∈ A := by
            rcases lt_trichotomy (toLex u0) (toLex uTop') with hlt | heq | hgt
            · exact hA_lex.2 uTop' (by
                rwa [monBox_clBound_eq_boxSlice (Nat.le_succ m) d' (σ - 1) (σ - 1) (by omega)]) u0 hu0 hlt
            · have : u0 = uTop' := heq; rwa [← this]
            · exfalso
              rw [lex_lt_iff] at hgt
              obtain ⟨t, ht_eq, ht_lt⟩ := hgt
              have hu0_B := hA_sub hu0
              cases t using Fin.lastCases with
              | last =>
                have hsum0 : ∑ i : Fin m, u0 i.castSucc + u0 (Fin.last m) = σ - 1 := by
                  rw [← Fin.sum_univ_castSucc, ← Finsupp.degree_eq_sum,
                    mem_monOfDeg.mp (mem_filter.mp hu0_B).1]
                have hsum_eq : ∑ i : Fin m, u0 i.castSucc = σ - 1 := by
                  have h1 : ∑ i : Fin m, uTop' i.castSucc = σ - 1 := by
                    have := mem_monOfDeg.mp (mem_filter.mp huTop'_box).1
                    rw [Finsupp.degree_eq_sum, Fin.sum_univ_castSucc] at this
                    have hlast0 : uTop' (Fin.last m) = 0 := by
                      simp [uTop', hvTop_last]
                    omega
                  rw [← h1]
                  exact Finset.sum_congr rfl fun i _ => (ht_eq i.castSucc (Fin.castSucc_lt_last i)).symm
                have hlast0 : uTop' (Fin.last m) = 0 := by simp [uTop', hvTop_last]
                omega
              | cast i =>
                have hi_lt : u0 i.castSucc < d' i := (mem_filter.mp hu0_B).2 i
                by_cases hij : i = j0
                · subst hij
                  have hsum_all : ∑ t' : Fin m, u0 t'.castSucc ≤ σ - 1 := by
                    have hdeg := mem_monOfDeg.mp (mem_filter.mp hu0_B).1
                    rw [Finsupp.degree_eq_sum, Fin.sum_univ_castSucc] at hdeg; omega
                  have hlt_all : ∀ t' : Fin m, t' ≠ j0 → t' < j0 := fun t' hne =>
                    lt_of_le_of_ne (by change t'.1 ≤ j0.1; have : j0.1 = m - 1 := rfl; omega) hne
                  have hsum_prev : ∑ t' ∈ Finset.univ.erase j0, u0 t'.castSucc =
                      ∑ t' ∈ Finset.univ.erase j0, (d' t' - 1) := by
                    refine Finset.sum_congr rfl fun t' ht' => ?_
                    have hlt' : t'.castSucc < j0.castSucc :=
                      Fin.castSucc_lt_castSucc_iff.mpr (hlt_all t' (Finset.mem_erase.mp ht').1)
                    rw [← ht_eq t'.castSucc hlt']
                    have hne : t'.castSucc ≠ j0.castSucc := ne_of_lt hlt'
                    simp [uTop', Finsupp.single_eq_of_ne hne, hvTop_cast]
                  have hu0_j0 : u0 j0.castSucc = d' j0 - 1 := by
                    have : uTop' j0.castSucc = d' j0 - 2 := by
                      simp [uTop', hvTop_cast]; omega
                    omega
                  have hsum_eq : ∑ t' : Fin m, u0 t'.castSucc = σ := by
                    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), hsum_prev, hu0_j0]
                    exact Finset.add_sum_erase Finset.univ (fun t' => d' t' - 1) (Finset.mem_univ j0)
                  omega
                · have hne : i.castSucc ≠ j0.castSucc := fun h => hij (Fin.castSucc_injective m h)
                  have huTop_i : uTop' i.castSucc = d' i - 1 := by
                    simp [uTop', Finsupp.single_eq_of_ne hne, hvTop_cast]
                  omega
          exact ⟨⟨uTop', huTop'_A, j0.castSucc, huTop'_add⟩, (mem_filter.mp hvTop_mem).2⟩
        · refine ⟨⟨u, huA, Fin.last m, rfl⟩, fun j => ?_⟩
          have hne : j.castSucc ≠ Fin.last m := Fin.castSucc_ne_last j
          have := (mem_filter.mp (hA_sub huA)).2 j
          change (u + Finsupp.single (Fin.last m) (1 : ℕ)) j.castSucc < d' j
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne hne, add_zero]
          exact this
    have hvTop_not_A : vTop ∉ A.image shift := fun h =>
      hvTop_not_img (Finset.image_subset_image hA_sub h)
    have hcard_sh_d' : (shadowBox (clBound (n := m + 1) d' (σ - 1)) A).card = mA + 1 := by
      rw [hsh_eq, Finset.card_insert_of_notMem hvTop_not_A,
        Finset.card_image_of_injective _ hshift_inj, hA_card]
    have hcl_d' : clNext (Nat.le_succ m) d' (σ - 1) r = r := by
      unfold clNext
      have hdeg_s : σ - 1 + 1 = σ := by omega
      rw [hdeg_s, hcard_σ]
      change (boxSlice (Nat.le_succ m) d' (σ - 1)).card + 1 -
        (shadowBox (clBound (n := m + 1) d' (σ - 1)) A).card = r
      rw [hcard_sh_d']; omega
    let uMin : Fin (m + 1) →₀ ℕ := Finsupp.single (Fin.last m) (σ - 1)
    have huMin_box : uMin ∈ boxSlice (Nat.le_succ m) d' (σ - 1) := by
      rw [boxSlice, mem_filter, mem_monOfDeg]
      refine ⟨Finsupp.degree_single _ _, fun j => ?_⟩
      change uMin j.castSucc < d' j
      simp only [uMin, Finsupp.single_eq_of_ne (Fin.castSucc_ne_last j)]
      have hdj : 2 ≤ d' j := hd j.castSucc; omega
    have huMin_notA : uMin ∉ A := by
      intro hmem
      have hall : boxSlice (Nat.le_succ m) d' (σ - 1) ⊆ A := by
        intro u hu
        rcases lt_trichotomy (toLex uMin) (toLex u) with hlt | heq | hgt
        · exact hA_lex.2 u (by
            rwa [monBox_clBound_eq_boxSlice (Nat.le_succ m) d' (σ - 1) (σ - 1) (by omega)])
            uMin hmem hlt
        · have : uMin = u := heq; rwa [← this]
        · exfalso
          rw [lex_lt_iff] at hgt
          obtain ⟨t, ht_eq, ht_lt⟩ := hgt
          cases t using Fin.lastCases with
          | last =>
            have hsum_u : ∑ j : Fin m, u j.castSucc + u (Fin.last m) = σ - 1 := by
              rw [← Fin.sum_univ_castSucc, ← Finsupp.degree_eq_sum,
                mem_monOfDeg.mp (mem_filter.mp hu).1]
            have hsum0 : ∑ j : Fin m, u j.castSucc = 0 :=
              Finset.sum_eq_zero fun j _ => by
                rw [ht_eq j.castSucc (Fin.castSucc_lt_last j)]
                simp [uMin, Finsupp.single_eq_of_ne (Fin.castSucc_ne_last j)]
            simp only [uMin, Finsupp.single_eq_same] at ht_lt
            omega
          | cast j =>
            simp only [uMin, Finsupp.single_eq_of_ne (Fin.castSucc_ne_last j)] at ht_lt
            omega
      have := Finset.card_le_card hall
      omega
    have huLast_not_sh : uLast ∉ shadowBox (clBound (n := m + 1) d' (σ - 1)) A := by
      rw [hsh_eq, mem_insert, mem_image]
      rintro (heq | ⟨u, huA, hu_eq⟩)
      · have h1 := congrArg (fun f : Fin (m + 1) →₀ ℕ => f (Fin.last m)) heq
        simp [uLast, hvTop_last] at h1; omega
      · apply huMin_notA
        have : u = uMin := by
          apply hshift_inj
          rw [hu_eq]; ext t
          cases t using Fin.lastCases with
          | last => simp [shift, uLast, uMin]; omega
          | cast j => simp [shift, uLast, uMin, Finsupp.single_eq_of_ne (Fin.castSucc_ne_last j)]
        rwa [← this]
    have hlex_d : lexSegBox (clBound (n := m + 1) d (σ - 1)) (σ - 1)
        ((boxSlice le_rfl d (σ - 1)).card - r) = A := by
      unfold A lexSegBox
      rw [monBox_clBound_eq_boxSlice le_rfl d (σ - 1) (σ - 1) (by omega),
        monBox_clBound_eq_boxSlice (Nat.le_succ m) d' (σ - 1) (σ - 1) (by omega), hbox_eq]
    have hsh_d : shadowBox (clBound (n := m + 1) d (σ - 1)) A =
        shadowBox (clBound (n := m + 1) d' (σ - 1)) A := by
      rw [← shadow_filter_inBox_eq_shadowBox le_rfl d (σ - 1) hA_deg,
        ← shadow_filter_inBox_eq_shadowBox (Nat.le_succ m) d' (σ - 1) hA_deg]
      ext v
      simp only [mem_filter]
      constructor
      · rintro ⟨hv, hin⟩; exact ⟨hv, fun j => hin j.castSucc⟩
      · rintro ⟨hv, hin⟩
        have hv_sh' : v ∈ shadowBox (clBound (n := m + 1) d' (σ - 1)) A := by
          rw [← shadow_filter_inBox_eq_shadowBox (Nat.le_succ m) d' (σ - 1) hA_deg]
          exact mem_filter.mpr ⟨hv, hin⟩
        have hv_ne : v ≠ uLast := fun h => huLast_not_sh (h ▸ hv_sh')
        have hv_box' : v ∈ boxSlice (Nat.le_succ m) d' σ := by
          rw [boxSlice, mem_filter, mem_monOfDeg]
          exact ⟨by have := mem_monOfDeg.mp (shadow_subset_monOfDeg hA_deg hv); omega, hin⟩
        have hv_box_d : v ∈ boxSlice le_rfl d σ := by
          rw [hbox_d_σ]; exact mem_erase.mpr ⟨hv_ne, hv_box'⟩
        exact ⟨hv, (mem_filter.mp hv_box_d).2⟩
    have hcl_d : clNext le_rfl d (σ - 1) r = r - 1 := by
      unfold clNext
      have hdeg_s : σ - 1 + 1 = σ := by omega
      rw [hlex_d, hsh_d, hdeg_s, hcard_d_σ, hcard_sh_d']
      omega
    exact ⟨hcl_d', hcl_d⟩
  ·
    dsimp only
    let d'' : Fin (m + 1) → ℕ := Fin.lastCases (σ - 1) d'
    let uMin : Fin (m + 1) →₀ ℕ := Finsupp.single (Fin.last m) (σ - 1)
    have huMin_mem : uMin ∈ boxSlice (Nat.le_succ m) d' (σ - 1) := by
      rw [boxSlice, mem_filter, mem_monOfDeg]
      refine ⟨Finsupp.degree_single _ _, fun j => ?_⟩
      change uMin j.castSucc < d' j
      simp only [uMin, Finsupp.single_eq_of_ne (Fin.castSucc_ne_last j)]
      have hdj : 2 ≤ d' j := hd j.castSucc; omega
    have hbox1 : boxSlice le_rfl d'' (σ - 1) = (boxSlice (Nat.le_succ m) d' (σ - 1)).erase uMin := by
      ext v
      simp only [mem_erase, boxSlice, mem_filter, mem_monOfDeg, inBoxPred]
      constructor
      · rintro ⟨hdeg, hin⟩
        refine ⟨?_, hdeg, fun j => ?_⟩
        · intro rfl
          have := hin (Fin.last m)
          change uMin (Fin.last m) < d'' (Fin.last m) at this
          simp [uMin, d''] at this
        · have h := hin j.castSucc
          change v j.castSucc < d'' j.castSucc at h
          simp only [d'', Fin.lastCases_castSucc] at h
          exact h
      · rintro ⟨hne, hdeg, hin⟩
        refine ⟨hdeg, fun j => ?_⟩
        cases j using Fin.lastCases with
        | last =>
          change v (Fin.last m) < d'' (Fin.last m)
          have hle : v (Fin.last m) ≤ ∑ i : Fin (m + 1), v i :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
          rw [← Finsupp.degree_eq_sum, hdeg] at hle
          have hlt : v (Fin.last m) < σ - 1 := by
            by_contra hge
            have heq_last : v (Fin.last m) = σ - 1 := by omega
            apply hne; ext r
            cases r using Fin.lastCases with
            | last => simp [uMin, heq_last]
            | cast i =>
              simp only [uMin, Finsupp.single_eq_of_ne (Fin.castSucc_ne_last i)]
              have hsum : (∑ j : Fin m, v j.castSucc) + v (Fin.last m) = σ - 1 := by
                rw [← Fin.sum_univ_castSucc, ← Finsupp.degree_eq_sum, hdeg]
              have hle_i : v i.castSucc ≤ ∑ j : Fin m, v j.castSucc :=
                Finset.single_le_sum (f := fun j : Fin m => v j.castSucc) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
              omega
          simpa [d''] using hlt
        | cast i =>
          have h := hin i
          change v i.castSucc < d' i at h
          change v i.castSucc < d'' i.castSucc
          simpa [d''] using h
    have hcard1 : (boxSlice le_rfl d'' (σ - 1)).card =
        (boxSlice (Nat.le_succ m) d' (σ - 1)).card - 1 := by
      rw [hbox1, Finset.card_erase_of_mem huMin_mem]
    have hcard2 : (boxSlice le_rfl d'' σ).card = (boxSlice (Nat.le_succ m) d' (σ - 2)).card := by
        have hd''_pos : ∀ j : Fin (m + 1), 1 ≤ d'' j := fun j => by
          cases j using Fin.lastCases with
          | last => simp [d'']; omega
          | cast i => simp only [d'', Fin.lastCases_castSucc]; have hdi : 2 ≤ d' i := hd i.castSucc; omega
        let uTop'' : Fin (m + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => d'' i - 1)
        have huTop''_deg : uTop''.degree = 2 * σ - 2 := by
          rw [Finsupp.degree_eq_sum, Fin.sum_univ_castSucc]
          change (∑ i : Fin m, (d'' i.castSucc - 1)) + (d'' (Fin.last m) - 1) = 2 * σ - 2
          simp only [d'', Fin.lastCases_castSucc, Fin.lastCases_last]
          change σ + (σ - 1 - 1) = 2 * σ - 2; omega
        have hsymm : (boxSlice le_rfl d'' σ).card = (boxSlice le_rfl d'' (σ - 2)).card := by
          refine Finset.card_bij (fun u _ => uTop'' - u) ?_ ?_ ?_
          · intro u hu
            rw [boxSlice, mem_filter, mem_monOfDeg] at hu ⊢
            have hle : u ≤ uTop'' := Finsupp.le_def.mpr fun i => by
              have := hu.2 i; change u i < d'' i at this
              change u i ≤ d'' i - 1; omega
            refine ⟨?_, fun i => ?_⟩
            · have hadd := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
              rw [map_add, huTop''_deg, hu.1] at hadd; omega
            · have := hd''_pos i; change (uTop'' - u) i < d'' i
              simp only [Finsupp.coe_tsub, Pi.sub_apply]
              change d'' i - 1 - u i < d'' i; omega
          · intro u₁ hu₁ u₂ hu₂ heq
            ext i
            have h1 : u₁ i ≤ d'' i - 1 := by have := (mem_filter.mp hu₁).2 i; change u₁ i < d'' i at this; omega
            have h2 : u₂ i ≤ d'' i - 1 := by have := (mem_filter.mp hu₂).2 i; change u₂ i < d'' i at this; omega
            have h3 := congrArg (fun f : Fin (m + 1) →₀ ℕ => f i) heq
            simp only [Finsupp.coe_tsub, Pi.sub_apply] at h3
            change d'' i - 1 - u₁ i = d'' i - 1 - u₂ i at h3; omega
          · intro v hv
            rw [boxSlice, mem_filter, mem_monOfDeg] at hv
            have hle : v ≤ uTop'' := Finsupp.le_def.mpr fun i => by
              have := hv.2 i; change v i < d'' i at this; change v i ≤ d'' i - 1; omega
            refine ⟨uTop'' - v, ?_, ?_⟩
            · rw [boxSlice, mem_filter, mem_monOfDeg]
              refine ⟨?_, fun i => ?_⟩
              · have hadd := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
                rw [map_add, huTop''_deg, hv.1] at hadd; omega
              · have := hd''_pos i; change (uTop'' - v) i < d'' i
                simp only [Finsupp.coe_tsub, Pi.sub_apply]
                change d'' i - 1 - v i < d'' i; omega
            · ext i; have := Finsupp.le_def.mp hle i
              simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega
        rw [hsymm]
        have heq_box : boxSlice le_rfl d'' (σ - 2) = boxSlice (Nat.le_succ m) d' (σ - 2) := by
          have := boxSlice_eq_castSucc_of_lt_last d'' (e := σ - 2) (by simp [d'']; omega)
          have hd''_cast : d'' ∘ Fin.castSucc = d' := by ext j; simp [d'']
          rwa [hd''_cast] at this
        rw [heq_box]
    exact ⟨hcard1, hcard2⟩
theorem shadowBox_ge_add_two_of_ge_sigma {m : ℕ} (hm : 2 ≤ m) (d' : Fin m → ℕ)
    (hd' : ∀ j : Fin m, 2 ≤ d' j)
    {h : ℕ} (hge : ∑ j : Fin m, (d' j - 1) ≤ h)
    (hle : h ≤ (boxSlice (Nat.le_succ m) d' (∑ j : Fin m, (d' j - 1) - 2)).card) :
    h + 2 ≤ (shadowBox (clBound (n := m + 1) d' (∑ j : Fin m, (d' j - 1) - 2))
      (lexSegBox (clBound (n := m + 1) d' (∑ j : Fin m, (d' j - 1) - 2))
        (∑ j : Fin m, (d' j - 1) - 2) h)).card := by
  classical
  set σ := ∑ j : Fin m, (d' j - 1)
  let j1 : Fin m := ⟨m - 2, by omega⟩
  let j2 : Fin m := ⟨m - 1, by omega⟩
  have hj12 : j1 ≠ j2 := by intro heq; have := congrArg Fin.val heq; simp [j1, j2] at this; omega
  have hj1_lt_j2 : j1 < j2 := by simp [Fin.lt_def, j1, j2]; omega
  have hσ_ge2 : 2 ≤ σ := by
    have hpair : (d' j1 - 1) + (d' j2 - 1) ≤ σ := by
      have hsub : ∑ j ∈ ({j1, j2} : Finset (Fin m)), (d' j - 1) ≤ σ :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      rwa [Finset.sum_pair hj12] at hsub
    have := hd' j1; have := hd' j2; omega
  let vTop : Fin (m + 1) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (Fin.lastCases 0 (fun j => d' j - 1))
  have hvTop_last : vTop (Fin.last m) = 0 := by
    change Fin.lastCases 0 (fun j => d' j - 1) (Fin.last m) = 0; simp
  have hvTop_cast : ∀ j : Fin m, vTop j.castSucc = d' j - 1 := fun j => by
    change Fin.lastCases 0 (fun r => d' r - 1) j.castSucc = d' j - 1; simp
  have hvTop_deg : vTop.degree = σ := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_castSucc, hvTop_last, add_zero]
    exact Finset.sum_congr rfl fun j _ => hvTop_cast j
  let u₂ : Fin (m + 1) →₀ ℕ :=
    vTop - Finsupp.single j1.castSucc 1 - Finsupp.single j2.castSucc 1
  let w₁ : Fin (m + 1) →₀ ℕ := vTop - Finsupp.single j1.castSucc 1
  let w₂ : Fin (m + 1) →₀ ℕ := vTop - Finsupp.single j2.castSucc 1
  have hu₂_add_j2 : u₂ + Finsupp.single j2.castSucc 1 = w₁ := by
    apply sub_single_add_single
    have hne : j2.castSucc ≠ j1.castSucc := fun h => hj12 (Fin.castSucc_injective m h).symm
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne hne, Nat.sub_zero,
      hvTop_cast]
    have := hd' j2; omega
  have hu₂_add_j1 : u₂ + Finsupp.single j1.castSucc 1 = w₂ := by
    ext r
    have hne : j1.castSucc ≠ j2.castSucc := fun h => hj12 (Fin.castSucc_injective m h)
    simp only [u₂, w₂, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hr1 : r = j1.castSucc
    · subst hr1
      simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne, Nat.sub_zero, hvTop_cast]
      have := hd' j1; omega
    · simp only [Finsupp.single_eq_of_ne hr1, add_zero, Nat.sub_zero]
  have hw12_ne : w₁ ≠ w₂ := by
    intro heq
    have h := congrArg (fun f : Fin (m + 1) →₀ ℕ => f j1.castSucc) heq
    have hne : j1.castSucc ≠ j2.castSucc := fun h => hj12 (Fin.castSucc_injective m h)
    simp only [w₁, w₂, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hne, Nat.sub_zero, hvTop_cast] at h
    have := hd' j1; omega
  have hu₂_box : u₂ ∈ boxSlice (Nat.le_succ m) d' (σ - 2) := by
    rw [boxSlice, mem_filter, mem_monOfDeg]
    refine ⟨?_, fun j => ?_⟩
    · have h1 := congrArg Finsupp.degree hu₂_add_j2
      have h2 : w₁.degree + 1 = vTop.degree :=
        degree_sub_single (by rw [hvTop_cast]; have := hd' j1; omega)
      rw [map_add, Finsupp.degree_single] at h1
      rw [hvTop_deg] at h2; omega
    · change u₂ j.castSucc < d' j
      simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply, hvTop_cast]
      have := hd' j; omega
  let Up := (boxSlice (Nat.le_succ m) d' (σ - 2)).filter (fun u => toLex u₂ ≤ toLex u)
  have hUp_card : Up.card ≤ d' j2 - 1 := by
    let φ : (Fin (m + 1) →₀ ℕ) → ℕ := fun u =>
      if u j1.castSucc = d' j1 - 1 then u j2.castSucc else d' j2 - 2
    have hUp_props : ∀ u ∈ Up,
        (∀ j : Fin m, j < j1 → u j.castSucc = d' j - 1) ∧
        u j1.castSucc + u j2.castSucc + u (Fin.last m) = d' j1 + d' j2 - 4 ∧
        ((u j1.castSucc = d' j1 - 1 ∧ u j2.castSucc < d' j2 - 2) ∨ u = u₂) := by
      intro u hu
      have huB := (mem_filter.mp hu).1
      have hge_u := (mem_filter.mp hu).2
      have hdeg := mem_monOfDeg.mp (mem_filter.mp huB).1
      have hin := (mem_filter.mp huB).2
      have hlt_eq : ∀ j : Fin m, j < j1 → u j.castSucc = d' j - 1 := by
        intro j hj
        have hle_j : u j.castSucc ≤ d' j - 1 := by have := hin j; change u j.castSucc < d' j at this; omega
        by_contra hne
        have hlt_j : u j.castSucc < d' j - 1 := lt_of_le_of_ne hle_j hne
        have hex : ∃ t : Fin m, t < j1 ∧ u t.castSucc < d' t - 1 := ⟨j, hj, hlt_j⟩
        let Slt := Finset.univ.filter (fun t : Fin m => t < j1 ∧ u t.castSucc < d' t - 1)
        have hSlt_ne : Slt.Nonempty := ⟨j, mem_filter.mpr ⟨mem_univ j, hj, hlt_j⟩⟩
        let t0 := Slt.min' hSlt_ne
        have ht0 := mem_filter.mp (Finset.min'_mem Slt hSlt_ne)
        have hlt_lex : toLex u < toLex u₂ := by
          rw [lex_lt_iff]
          refine ⟨t0.castSucc, fun r hr => ?_, ?_⟩
          · have hr_lt : r.1 < m := lt_trans hr t0.isLt
            let r' : Fin m := ⟨r.1, hr_lt⟩
            have hr_eq : r = r'.castSucc := by ext; rfl
            rw [hr_eq]
            have hr'_lt : r' < t0 := hr
            have hr'_j1 : r' < j1 := lt_trans hr'_lt ht0.2.1
            have hr'_not : r' ∉ Slt := fun hm' => not_lt_of_ge (Finset.min'_le Slt r' hm') hr'_lt
            have hr'_ge : ¬ u r'.castSucc < d' r' - 1 := fun hlt' =>
              hr'_not (mem_filter.mpr ⟨mem_univ r', hr'_j1, hlt'⟩)
            have hr'_le : u r'.castSucc ≤ d' r' - 1 := by
              have := hin r'; change u r'.castSucc < d' r' at this; omega
            have hne1 : r'.castSucc ≠ j1.castSucc := ne_of_lt (Fin.castSucc_lt_castSucc_iff.mpr hr'_j1)
            have hne2 : r'.castSucc ≠ j2.castSucc :=
              ne_of_lt (Fin.castSucc_lt_castSucc_iff.mpr (lt_trans hr'_j1 hj1_lt_j2))
            simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne hne1,
              Finsupp.single_eq_of_ne hne2, Nat.sub_zero, hvTop_cast]
            omega
          · have hne1 : t0.castSucc ≠ j1.castSucc := ne_of_lt (Fin.castSucc_lt_castSucc_iff.mpr ht0.2.1)
            have hne2 : t0.castSucc ≠ j2.castSucc :=
              ne_of_lt (Fin.castSucc_lt_castSucc_iff.mpr (lt_trans ht0.2.1 hj1_lt_j2))
            simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne hne1,
              Finsupp.single_eq_of_ne hne2, Nat.sub_zero, hvTop_cast]
            exact ht0.2.2
        exact not_lt_of_ge hge_u hlt_lex
      have hsum3 : u j1.castSucc + u j2.castSucc + u (Fin.last m) = d' j1 + d' j2 - 4 := by
        have hpart : ∀ f : Fin m → ℕ,
            ∑ j : Fin m, f j =
              (∑ j ∈ (Finset.univ.erase j2).erase j1, f j) + f j1 + f j2 := by
          intro f
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j2)]
          have hj1_in : j1 ∈ Finset.univ.erase j2 := Finset.mem_erase.mpr ⟨hj12, Finset.mem_univ j1⟩
          rw [← Finset.sum_erase_add _ _ hj1_in]
        have htot_u : (∑ j : Fin m, u j.castSucc) + u (Fin.last m) = σ - 2 := by
          rw [← Fin.sum_univ_castSucc, ← Finsupp.degree_eq_sum, hdeg]
        have htot_d : ∑ j : Fin m, (d' j - 1) = σ := rfl
        rw [hpart (fun j => u j.castSucc)] at htot_u
        rw [hpart (fun j => d' j - 1)] at htot_d
        have hrest : ∑ j ∈ (Finset.univ.erase j2).erase j1, u j.castSucc =
            ∑ j ∈ (Finset.univ.erase j2).erase j1, (d' j - 1) := by
          refine Finset.sum_congr rfl fun j hj => hlt_eq j ?_
          have h1 := (Finset.mem_erase.mp hj).1
          have h2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
          have hj_lt : j.1 < m := j.isLt
          have : j.1 ≠ m - 2 := fun h => h1 (Fin.ext h)
          have : j.1 ≠ m - 1 := fun h => h2 (Fin.ext h)
          simp only [Fin.lt_def, j1]; omega
        rw [hrest] at htot_u
        have := hd' j1; have := hd' j2
        omega
      refine ⟨hlt_eq, hsum3, ?_⟩
      have huj1_le : u j1.castSucc ≤ d' j1 - 1 := by
        have := hin j1; change u j1.castSucc < d' j1 at this; omega
      have huj1_ge : d' j1 - 2 ≤ u j1.castSucc := by
        by_contra hlt_j1
        have hlex_lt : toLex u < toLex u₂ := by
          rw [lex_lt_iff]
          refine ⟨j1.castSucc, fun r hr => ?_, ?_⟩
          · have hr_lt : r.1 < m := lt_trans hr j1.isLt
            let r' : Fin m := ⟨r.1, hr_lt⟩
            have hr_eq : r = r'.castSucc := by ext; rfl
            rw [hr_eq, hlt_eq r' hr]
            have hne1 : r'.castSucc ≠ j1.castSucc := ne_of_lt hr
            have hne2 : r'.castSucc ≠ j2.castSucc :=
              ne_of_lt (Fin.castSucc_lt_castSucc_iff.mpr (lt_trans hr hj1_lt_j2))
            simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne hne1,
              Finsupp.single_eq_of_ne hne2, Nat.sub_zero, hvTop_cast]
          · have hne : j1.castSucc ≠ j2.castSucc := fun h => hj12 (Fin.castSucc_injective m h)
            simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same,
              Finsupp.single_eq_of_ne hne, Nat.sub_zero, hvTop_cast]
            have := hd' j1; omega
        exact not_lt_of_ge hge_u hlex_lt
      by_cases hj1_eq : u j1.castSucc = d' j1 - 1
      · left
        have := hd' j1; have := hd' j2
        exact ⟨hj1_eq, by omega⟩
      · right
        have hj1_eq2 : u j1.castSucc = d' j1 - 2 := by omega
        have huj2_ge : d' j2 - 2 ≤ u j2.castSucc := by
          by_contra hlt_j2
          have hlex_lt : toLex u < toLex u₂ := by
            rw [lex_lt_iff]
            refine ⟨j2.castSucc, fun r hr => ?_, ?_⟩
            · have hr_lt : r.1 < m := lt_trans hr j2.isLt
              let r' : Fin m := ⟨r.1, hr_lt⟩
              have hr_eq : r = r'.castSucc := by ext; rfl
              rw [hr_eq]
              by_cases hrj1 : r' = j1
              · rw [hrj1]
                have hne : j1.castSucc ≠ j2.castSucc := fun h => hj12 (Fin.castSucc_injective m h)
                simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same,
                  Finsupp.single_eq_of_ne hne, Nat.sub_zero, hvTop_cast, hj1_eq2]
                have := hd' j1; omega
              · have hr'_lt : r' < j1 := by
                  have h1 : r'.1 < m - 1 := hr
                  have h2 : r'.1 ≠ m - 2 := fun h => hrj1 (Fin.ext h)
                  simp only [Fin.lt_def, j1]; omega
                rw [hlt_eq r' hr'_lt]
                have hne1 : r'.castSucc ≠ j1.castSucc := ne_of_lt (Fin.castSucc_lt_castSucc_iff.mpr hr'_lt)
                have hne2 : r'.castSucc ≠ j2.castSucc := ne_of_lt hr
                simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne hne1,
                  Finsupp.single_eq_of_ne hne2, Nat.sub_zero, hvTop_cast]
            · have hne : j2.castSucc ≠ j1.castSucc := fun h => hj12 (Fin.castSucc_injective m h).symm
              simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same,
                Finsupp.single_eq_of_ne hne, Nat.sub_zero, hvTop_cast]
              have := hd' j2; omega
          exact not_lt_of_ge hge_u hlex_lt
        have := hd' j1; have := hd' j2
        ext r
        cases r using Fin.lastCases with
        | last =>
          simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply,
            Finsupp.single_eq_of_ne (Fin.castSucc_ne_last j1).symm,
            Finsupp.single_eq_of_ne (Fin.castSucc_ne_last j2).symm, Nat.sub_zero, hvTop_last]
          omega
        | cast i =>
          by_cases hi1 : i = j1
          · subst hi1
            have hne : j1.castSucc ≠ j2.castSucc := fun h => hj12 (Fin.castSucc_injective m h)
            simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same,
              Finsupp.single_eq_of_ne hne, Nat.sub_zero, hvTop_cast, hj1_eq2]; omega
          · by_cases hi2 : i = j2
            · subst hi2
              have hne : j2.castSucc ≠ j1.castSucc := fun h => hj12 (Fin.castSucc_injective m h).symm
              simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same,
                Finsupp.single_eq_of_ne hne, Nat.sub_zero, hvTop_cast]; omega
            · have hi_lt : i < j1 := by
                have h1 : i.1 < m := i.isLt
                have h2 : i.1 ≠ m - 2 := fun h => hi1 (Fin.ext h)
                have h3 : i.1 ≠ m - 1 := fun h => hi2 (Fin.ext h)
                simp only [Fin.lt_def, j1]; omega
              rw [hlt_eq i hi_lt]
              have hne1 : i.castSucc ≠ j1.castSucc := fun h => hi1 (Fin.castSucc_injective m h)
              have hne2 : i.castSucc ≠ j2.castSucc := fun h => hi2 (Fin.castSucc_injective m h)
              simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_of_ne hne1,
                Finsupp.single_eq_of_ne hne2, Nat.sub_zero, hvTop_cast]
    have hcard_le : Up.card ≤ (Finset.range (d' j2 - 1)).card := by
      refine Finset.card_le_card_of_injOn φ ?_ ?_
      · intro u hu
        rw [Finset.mem_coe, Finset.mem_range]
        rcases (hUp_props u hu).2.2 with ⟨h1, h2⟩ | rfl
        · simp only [φ, if_pos h1]; omega
        · have hu₂_j1 : u₂ j1.castSucc ≠ d' j1 - 1 := by
            have hne : j1.castSucc ≠ j2.castSucc := fun h => hj12 (Fin.castSucc_injective m h)
            simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same,
              Finsupp.single_eq_of_ne hne, Nat.sub_zero, hvTop_cast]
            have := hd' j1; omega
          simp only [φ, if_neg hu₂_j1]
          have := hd' j2; omega
      · intro u₁ hu₁ u₂' hu₂' heq
        have hp1 := hUp_props u₁ hu₁
        have hp2 := hUp_props u₂' hu₂'
        have hu₂_j1 : u₂ j1.castSucc ≠ d' j1 - 1 := by
          have hne : j1.castSucc ≠ j2.castSucc := fun h => hj12 (Fin.castSucc_injective m h)
          simp only [u₂, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same,
            Finsupp.single_eq_of_ne hne, Nat.sub_zero, hvTop_cast]
          have := hd' j1; omega
        rcases hp1.2.2 with ⟨h1a, h1b⟩ | rfl
        · rcases hp2.2.2 with ⟨h2a, h2b⟩ | rfl
          · simp only [φ, if_pos h1a, if_pos h2a] at heq
            ext r
            cases r using Fin.lastCases with
            | last => omega
            | cast i =>
              by_cases hi1 : i = j1
              · subst hi1; rw [h1a, h2a]
              · by_cases hi2 : i = j2
                · subst hi2; exact heq
                · have hi_lt : i < j1 := by
                    have h1 : i.1 < m := i.isLt
                    have h2 : i.1 ≠ m - 2 := fun h => hi1 (Fin.ext h)
                    have h3 : i.1 ≠ m - 1 := fun h => hi2 (Fin.ext h)
                    simp only [Fin.lt_def, j1]; omega
                  rw [hp1.1 i hi_lt, hp2.1 i hi_lt]
          · simp only [φ, if_pos h1a, if_neg hu₂_j1] at heq; omega
        · rcases hp2.2.2 with ⟨h2a, h2b⟩ | rfl
          · simp only [φ, if_neg hu₂_j1, if_pos h2a] at heq; omega
          · rfl
    rwa [Finset.card_range] at hcard_le
  let A := lexSegBox (clBound (n := m + 1) d' (σ - 2)) (σ - 2) h
  have hu₂_A : u₂ ∈ A := by
    apply mem_lexSegBox_of_card_ge_le
    · rwa [monBox_clBound_eq_boxSlice (Nat.le_succ m) d' (σ - 2) (σ - 2) (by omega)]
    · rw [monBox_clBound_eq_boxSlice (Nat.le_succ m) d' (σ - 2) (σ - 2) (by omega)]
      have hle_σ : d' j2 - 1 ≤ σ :=
        Finset.single_le_sum (f := fun j : Fin m => d' j - 1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j2)
      exact le_trans hUp_card (le_trans hle_σ hge)
    · rw [monBox_clBound_eq_boxSlice (Nat.le_succ m) d' (σ - 2) (σ - 2) (by omega)]; exact hle
  have hA_sub : A ⊆ boxSlice (Nat.le_succ m) d' (σ - 2) := by
    rw [← monBox_clBound_eq_boxSlice (Nat.le_succ m) d' (σ - 2) (σ - 2) (by omega)]
    exact lexSegBox_subset_monBox _ _ _
  have hA_deg : A ⊆ monOfDeg (m + 1) (σ - 2) :=
    Finset.Subset.trans hA_sub (Finset.filter_subset _ _)
  let shift : (Fin (m + 1) →₀ ℕ) → (Fin (m + 1) →₀ ℕ) := fun u => u + Finsupp.single (Fin.last m) 1
  have hshift_inj : Function.Injective shift := fun _ _ h => add_right_cancel h
  have hsub_sh : ({w₁, w₂} ∪ A.image shift) ⊆
      shadowBox (clBound (n := m + 1) d' (σ - 2)) A := by
    rw [← shadow_filter_inBox_eq_shadowBox (Nat.le_succ m) d' (σ - 2) hA_deg]
    intro v hv
    simp only [mem_union, mem_insert, mem_singleton, mem_image] at hv
    rw [mem_filter, mem_shadow]
    rcases hv with (rfl | rfl) | ⟨u, huA, rfl⟩
    · refine ⟨⟨u₂, hu₂_A, j2.castSucc, hu₂_add_j2⟩, fun j => ?_⟩
      change w₁ j.castSucc < d' j
      simp only [w₁, Finsupp.coe_tsub, Pi.sub_apply, hvTop_cast]
      have := hd' j; omega
    · refine ⟨⟨u₂, hu₂_A, j1.castSucc, hu₂_add_j1⟩, fun j => ?_⟩
      change w₂ j.castSucc < d' j
      simp only [w₂, Finsupp.coe_tsub, Pi.sub_apply, hvTop_cast]
      have := hd' j; omega
    · refine ⟨⟨u, huA, Fin.last m, rfl⟩, fun j => ?_⟩
      have hne : j.castSucc ≠ Fin.last m := Fin.castSucc_ne_last j
      have := (mem_filter.mp (hA_sub huA)).2 j
      change (u + Finsupp.single (Fin.last m) (1 : ℕ)) j.castSucc < d' j
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne hne, add_zero]
      exact this
  have hdisj : Disjoint ({w₁, w₂} : Finset (Fin (m + 1) →₀ ℕ)) (A.image shift) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    rw [mem_image] at hv2; obtain ⟨u, _, rfl⟩ := hv2
    have hpos : 1 ≤ shift u (Fin.last m) := by simp [shift]
    rw [mem_insert, mem_singleton] at hv1
    rcases hv1 with h | h
    · have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f (Fin.last m)) h
      simp [w₁, hvTop_last] at this; omega
    · have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f (Fin.last m)) h
      simp [w₂, hvTop_last] at this; omega
  have hcard := Finset.card_le_card hsub_sh
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_pair hw12_ne,
    Finset.card_image_of_injective _ hshift_inj] at hcard
  have hA_card : A.card = h := by
    apply card_lexSegBox
    rw [monBox_clBound_eq_boxSlice (Nat.le_succ m) d' (σ - 2) (σ - 2) (by omega)]; exact hle
  rw [hA_card] at hcard
  dsimp only [A] at hcard
  omega
theorem clNext_n2 (d : Fin 2 → ℕ) (hd0 : 2 ≤ d 0) (hd01 : d 0 ≤ d 1) (e r : ℕ)
    (hr_pos : 0 < r) (hr_lt : r < (boxSlice le_rfl d e).card) :
    clNext le_rfl d e r = if e < d 1 - 1 then r else r - 1 := by
  classical
  let aMin (m : ℕ) : ℕ := m + 1 - d 1
  let aMax (m : ℕ) : ℕ := min m (d 0 - 1)
  have hbox_eq_Icc : ∀ m, (boxSlice le_rfl d m).image (fun u => u 0) = Finset.Icc (aMin m) (aMax m) := by
    intro m; ext a
    simp only [mem_image, boxSlice, mem_filter, mem_monOfDeg, inBoxPred, Finset.mem_Icc, aMin, aMax]
    constructor
    · rintro ⟨u, ⟨hdeg, hin⟩, rfl⟩
      have hsum : u 0 + u 1 = m := by rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
      have h0 : u 0 < d 0 := hin 0
      have h1 : u 1 < d 1 := hin 1
      omega
    · rintro ⟨h1, h2⟩
      have ham : a ≤ m := le_trans h2 (min_le_left _ _)
      let u : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm (Fin.cons a (Fin.cons (m - a) finZeroElim))
      refine ⟨u, ⟨?_, fun j => ?_⟩, rfl⟩
      · rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]; change a + (m - a) = m; omega
      · fin_cases j
        · change a < d 0; omega
        · change m - a < d 1; omega
  have hinj0 : ∀ m, Set.InjOn (fun u : Fin 2 →₀ ℕ => u 0) (boxSlice le_rfl d m : Set (Fin 2 →₀ ℕ)) := by
    intro m u₁ hu₁ u₂ hu₂ heq
    have h1 : u₁ 0 + u₁ 1 = m := by
      have := mem_monOfDeg.mp (mem_filter.mp hu₁).1; rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at this
    have h2 : u₂ 0 + u₂ 1 = m := by
      have := mem_monOfDeg.mp (mem_filter.mp hu₂).1; rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at this
    ext j; fin_cases j <;> simp at * <;> omega
  have hcard_box : ∀ m, (boxSlice le_rfl d m).card = (Finset.Icc (aMin m) (aMax m)).card := fun m => by
    rw [← hbox_eq_Icc m, Finset.card_image_of_injOn (hinj0 m)]
  have hlex_iff_0 : ∀ m, ∀ u ∈ boxSlice le_rfl d m, ∀ v ∈ boxSlice le_rfl d m,
      toLex u < toLex v ↔ u 0 < v 0 := by
    intro m u hu v hv
    have h1 : u 0 + u 1 = m := by
      have := mem_monOfDeg.mp (mem_filter.mp hu).1; rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at this
    have h2 : v 0 + v 1 = m := by
      have := mem_monOfDeg.mp (mem_filter.mp hv).1; rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at this
    rw [lex_lt_iff]
    constructor
    · rintro ⟨j, hj_eq, hj_lt⟩
      fin_cases j
      · exact hj_lt
      · have h0 := hj_eq 0 (by decide)
        change u 0 = v 0 at h0
        change u 1 < v 1 at hj_lt
        omega
    · intro hlt
      exact ⟨0, fun j hj => absurd hj (by fin_cases j <;> decide), hlt⟩
  have he_le : aMin e ≤ aMax e := by
    have hpos : 0 < (Finset.Icc (aMin e) (aMax e)).card := by rw [← hcard_box e]; omega
    rw [Nat.card_Icc] at hpos; omega
  have hcard_e : (boxSlice le_rfl d e).card = aMax e + 1 - aMin e := by
    rw [hcard_box e, Nat.card_Icc]
  let mA := (boxSlice le_rfl d e).card - r
  let A := lexSegBox (clBound (n := 2) d e) e mA
  let A' := (boxSlice le_rfl d e).filter (fun u => aMin e + r ≤ u 0)
  have hA'_eq : A = A' := by
    have hA'_lex : IsLexBox (clBound (n := 2) d e) e A' := by
      rw [IsLexBox, monBox_clBound_eq_boxSlice le_rfl d e e (by omega)]
      refine ⟨Finset.filter_subset _ _, fun u hu v hv hlt => ?_⟩
      rw [mem_filter] at hv ⊢
      have := (hlex_iff_0 e v hv.1 u hu).mp hlt
      exact ⟨hu, by omega⟩
    have hA'_card : A'.card = mA := by
      have himg : A'.image (fun u => u 0) = Finset.Icc (aMin e + r) (aMax e) := by
        ext a; simp only [A', mem_image, mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨u, ⟨huB, hge⟩, rfl⟩
          have hmem : u 0 ∈ Finset.Icc (aMin e) (aMax e) := by
            rw [← hbox_eq_Icc e]; exact mem_image.mpr ⟨u, huB, rfl⟩
          rw [Finset.mem_Icc] at hmem; omega
        · rintro ⟨h1, h2⟩
          have hmem : a ∈ (boxSlice le_rfl d e).image (fun u => u 0) := by
            rw [hbox_eq_Icc e, Finset.mem_Icc]; omega
          rw [mem_image] at hmem
          obtain ⟨u, huB, rfl⟩ := hmem
          exact ⟨u, ⟨huB, h1⟩, rfl⟩
      have hinj' : Set.InjOn (fun u : Fin 2 →₀ ℕ => u 0) (A' : Set (Fin 2 →₀ ℕ)) :=
        (hinj0 e).mono (Finset.filter_subset _ _)
      rw [← Finset.card_image_of_injOn hinj', himg, Nat.card_Icc]
      omega
    exact (isLexBox_lexSegBox (clBound (n := 2) d e) e mA).eq_of_card_eq hA'_lex
      (by rw [card_lexSegBox (by rw [monBox_clBound_eq_boxSlice le_rfl d e e (by omega)]; omega),
        hA'_card])
  let SA' := (boxSlice le_rfl d (e + 1)).filter (fun v => aMin e + r ≤ v 0)
  have hsh_eq : shadowBox (clBound (n := 2) d e) A = SA' := by
    have hA_deg : A ⊆ monOfDeg 2 e :=
      Finset.Subset.trans (by rw [hA'_eq]; exact Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [← shadow_filter_inBox_eq_shadowBox le_rfl d e hA_deg, hA'_eq]
    ext v
    simp only [SA', A', mem_filter, mem_shadow, boxSlice, mem_monOfDeg, inBoxPred]
    constructor
    · rintro ⟨⟨u, ⟨⟨hu_deg, hu_in⟩, hu_ge⟩, i, rfl⟩, hv_in⟩
      refine ⟨⟨by rw [map_add, Finsupp.degree_single, hu_deg], hv_in⟩, ?_⟩
      simp only [Finsupp.coe_add, Pi.add_apply]; omega
    · rintro ⟨⟨hv_deg, hv_in⟩, hv_ge⟩
      refine ⟨?_, hv_in⟩
      have hv_sum : v 0 + v 1 = e + 1 := by rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hv_deg
      by_cases hv1 : 1 ≤ v 1
      · refine ⟨v - Finsupp.single 1 1, ⟨⟨by have := degree_sub_single hv1; omega, fun j => ?_⟩, ?_⟩,
          1, sub_single_add_single hv1⟩
        · have := hv_in j; simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega
        · simp only [Finsupp.coe_tsub, Pi.sub_apply,
            Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), Nat.sub_zero]; exact hv_ge
      ·
        have hv0 : 1 ≤ v 0 := by omega
        refine ⟨v - Finsupp.single 0 1, ⟨⟨by have := degree_sub_single hv0; omega, fun j => ?_⟩, ?_⟩,
          0, sub_single_add_single hv0⟩
        · have := hv_in j; simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega
        · simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
          have : aMax e ≤ e := min_le_left _ _
          omega
  have hSA'_card : SA'.card = (Finset.Icc (max (aMin (e + 1)) (aMin e + r)) (aMax (e + 1))).card := by
    have himg : SA'.image (fun v => v 0) =
        Finset.Icc (max (aMin (e + 1)) (aMin e + r)) (aMax (e + 1)) := by
      ext a; simp only [SA', mem_image, mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨v, ⟨hvB, hge⟩, rfl⟩
        have hmem : v 0 ∈ Finset.Icc (aMin (e + 1)) (aMax (e + 1)) := by
          rw [← hbox_eq_Icc (e + 1)]; exact mem_image.mpr ⟨v, hvB, rfl⟩
        rw [Finset.mem_Icc] at hmem; omega
      · rintro ⟨h1, h2⟩
        have hmem : a ∈ (boxSlice le_rfl d (e + 1)).image (fun v => v 0) := by
          rw [hbox_eq_Icc (e + 1), Finset.mem_Icc]; omega
        rw [mem_image] at hmem
        obtain ⟨v, hvB, rfl⟩ := hmem
        exact ⟨v, ⟨hvB, by omega⟩, rfl⟩
    have hinj' : Set.InjOn (fun v : Fin 2 →₀ ℕ => v 0) (SA' : Set (Fin 2 →₀ ℕ)) :=
      (hinj0 (e + 1)).mono (Finset.filter_subset _ _)
    rw [← Finset.card_image_of_injOn hinj', himg]
  unfold clNext
  change (boxSlice le_rfl d (e + 1)).card - (shadowBox (clBound (n := 2) d e) A).card = _
  rw [hsh_eq, hSA'_card, hcard_box (e + 1), Nat.card_Icc, Nat.card_Icc]
  dsimp only [aMin, aMax] at he_le hcard_e ⊢
  split_ifs with hlt <;> omega
end BC

namespace KL
open MvPolynomial Finset
variable {n : ℕ} {k : Type*} [Field k]
noncomputable local instance : GradedAlgebra (homogeneousSubmodule (Fin n) k) := MvPolynomial.gradedAlgebra
abbrev homogPiece (n : ℕ) (k : Type*) [Field k] (d : ℕ) :
    Submodule k (MvPolynomial (Fin n) k) :=
  homogeneousSubmodule (Fin n) k d
noncomputable def idealSub (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    Submodule k (homogPiece n k e) :=
  (Submodule.restrictScalars k I ⊓ homogPiece n k e).comap (homogPiece n k e).subtype
lemma mem_idealSub {I : Ideal (MvPolynomial (Fin n) k)} {e : ℕ} (x : homogPiece n k e) :
    x ∈ idealSub I e ↔ x.1 ∈ I := by
  simp [idealSub]
noncomputable def quotientHF (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) : ℕ :=
  Module.finrank k (homogPiece n k e ⧸ idealSub I e)
noncomputable def monOfDeg (n e : ℕ) : Finset (Fin n →₀ ℕ) :=
  ((Fintype.piFinset (fun _ : Fin n => Finset.range (e + 1))).image
    Finsupp.equivFunOnFinite.symm).filter (fun u => u.degree = e)
lemma mem_monOfDeg {n e : ℕ} {u : Fin n →₀ ℕ} :
    u ∈ monOfDeg n e ↔ u.degree = e := by
  simp only [monOfDeg, mem_filter, mem_image, Fintype.mem_piFinset, mem_range,
    and_iff_right_iff_imp]
  intro hdeg
  refine ⟨fun i => u i, fun i => ?_, ?_⟩
  · have hle : u i ≤ ∑ j : Fin n, u j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [← Finsupp.degree_eq_sum, hdeg] at hle
    dsimp only; omega
  · ext i; simp
lemma weight_one_eq_deg (u : Fin n →₀ ℕ) : Finsupp.weight (1 : Fin n → ℕ) u = u.degree := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.degree]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rfl
lemma monomial_mem_homogPiece {e : ℕ} {u : Fin n →₀ ℕ} (hu : u ∈ monOfDeg n e) :
    monomial u (1 : k) ∈ homogPiece n k e := by
  rw [mem_homogeneousSubmodule]
  intro v hv
  rw [coeff_monomial] at hv
  split_ifs at hv with hvu
  · subst hvu; rw [weight_one_eq_deg]; exact mem_monOfDeg.mp hu
  · exact absurd rfl hv
lemma support_subset_monOfDeg {e : ℕ} {p : MvPolynomial (Fin n) k}
    (hp : p ∈ homogPiece n k e) : p.support ⊆ monOfDeg n e := by
  intro u hu
  rw [mem_monOfDeg]
  have h := (mem_homogeneousSubmodule _ _).mp hp (MvPolynomial.mem_support_iff.mp hu)
  rwa [weight_one_eq_deg] at h
lemma eq_sum_monOfDeg {e : ℕ} (p : homogPiece n k e) :
    p = ∑ u : monOfDeg n e, coeff u.1 p.1 • (⟨monomial u.1 (1 : k), monomial_mem_homogPiece u.2⟩ :
      homogPiece n k e) := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [SetLike.val_smul, smul_monomial, smul_eq_mul, mul_one]
  rw [Finset.sum_coe_sort (monOfDeg n e) (fun u => monomial u (coeff u p.1))]
  conv_lhs => rw [p.1.as_sum]
  exact Finset.sum_subset (support_subset_monOfDeg p.2) (fun u _ hu => by
    rw [MvPolynomial.notMem_support_iff.mp hu, monomial_zero])
noncomputable def homogPieceBasis (e : ℕ) : Module.Basis (monOfDeg n e) k (homogPiece n k e) :=
  Module.Basis.mk
    (v := fun u : monOfDeg n e =>
      (⟨monomial u.1 (1 : k), monomial_mem_homogPiece u.2⟩ : homogPiece n k e))
    (by
      rw [Fintype.linearIndependent_iff]
      intro g hg u
      have hcoeff := congrArg (fun x : homogPiece n k e => coeff u.1 x.1) hg
      simp only [ZeroMemClass.coe_zero, coeff_zero, AddSubmonoidClass.coe_finsetSum,
        SetLike.val_smul, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one,
        mul_zero] at hcoeff
      rw [Finset.sum_eq_single u] at hcoeff
      · simpa using hcoeff
      · intro v _ hvu; rw [if_neg (fun h => hvu (Subtype.ext h))]
      · intro hu; exact absurd (Finset.mem_univ u) hu)
    (by
      intro x _
      rw [eq_sum_monOfDeg x]
      exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩))
instance homogPiece_finiteDimensional (e : ℕ) : FiniteDimensional k (homogPiece n k e) :=
  Module.Finite.of_basis (homogPieceBasis e)
lemma finrank_homogPiece (e : ℕ) : Module.finrank k (homogPiece n k e) = (monOfDeg n e).card := by
  rw [Module.finrank_eq_card_basis (homogPieceBasis (n := n) (k := k) e), Fintype.card_coe]
lemma hilbertFunction_add_quotientHF (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    hilbertFunction I e + quotientHF I e = (monOfDeg n e).card := by
  have h1 := Submodule.finrank_quotient_add_finrank (idealSub I e)
  have h2 : Module.finrank k (idealSub I e) = hilbertFunction I e := by
    unfold hilbertFunction idealSub
    let f : homogPiece n k e →ₗ[k] MvPolynomial (Fin n) k := (homogPiece n k e).subtype
    have heq : Submodule.map f
        ((Submodule.restrictScalars k I ⊓ homogPiece n k e).comap f) =
        Submodule.restrictScalars k I ⊓ homogPiece n k e := by
      rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr inf_le_right]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f
      (Submodule.injective_subtype _)
      ((Submodule.restrictScalars k I ⊓ homogPiece n k e).comap f))).trans
      (congrArg (fun M : Submodule k (MvPolynomial (Fin n) k) => Module.finrank k M) heq)
  rw [← finrank_homogPiece (k := k) e]
  unfold quotientHF
  omega
lemma isHomogeneous_ideal_ofList {rs : List (MvPolynomial (Fin n) k)}
    (hrs : ∀ r ∈ rs, ∃ d, r.IsHomogeneous d) :
    (Ideal.ofList rs).IsHomogeneous (homogeneousSubmodule (Fin n) k) := by
  apply Ideal.homogeneous_span
  intro x hx
  obtain ⟨d, hd⟩ := hrs x hx
  exact ⟨d, (mem_homogeneousSubmodule d x).mpr hd⟩
lemma homogeneousComponent_mul_of_isHomogeneous {g p : MvPolynomial (Fin n) k} {d m : ℕ}
    (hg : g.IsHomogeneous d) :
    homogeneousComponent m (g * p) =
      if d ≤ m then g * homogeneousComponent (m - d) p else 0 := by
  apply MvPolynomial.ext
  intro u
  rw [coeff_homogeneousComponent]
  by_cases hdeg : u.degree = m
  · rw [if_pos hdeg]
    split_ifs with hdm
    · rw [coeff_mul, coeff_mul]
      refine Finset.sum_congr rfl fun xy hxy => ?_
      rw [HasAntidiagonal.mem_antidiagonal] at hxy
      by_cases h1 : xy.1.degree = d
      · have h2 : xy.2.degree = m - d := by
          have := congrArg Finsupp.degree hxy
          rw [map_add, hdeg, h1] at this; omega
        rw [coeff_homogeneousComponent, if_pos h2]
      · rw [hg.coeff_eq_zero h1, zero_mul, zero_mul]
    · rw [coeff_mul, coeff_zero]
      refine Finset.sum_eq_zero fun xy hxy => ?_
      rw [HasAntidiagonal.mem_antidiagonal] at hxy
      have hne : xy.1.degree ≠ d := by
        intro h1
        have := congrArg Finsupp.degree hxy
        rw [map_add, hdeg, h1] at this; omega
      rw [hg.coeff_eq_zero hne, zero_mul]
  · rw [if_neg hdeg]
    split_ifs with hdm
    · symm
      have hhom : (g * homogeneousComponent (m - d) p).IsHomogeneous m := by
        have h := hg.mul (homogeneousComponent_isHomogeneous (m - d) p)
        rwa [Nat.add_sub_of_le hdm] at h
      exact hhom.coeff_eq_zero hdeg
    · rw [coeff_zero]
lemma exists_homog_of_mem_sup_span {I : Ideal (MvPolynomial (Fin n) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) k))
    {g p : MvPolynomial (Fin n) k} {d m : ℕ}
    (hg : g.IsHomogeneous d) (hp : p.IsHomogeneous m)
    (hmem : p ∈ I ⊔ Ideal.span {g}) :
    (m < d ∧ p ∈ I) ∨ (d ≤ m ∧ ∃ q : MvPolynomial (Fin n) k, q.IsHomogeneous (m - d) ∧ p - g * q ∈ I) := by
  rw [Submodule.mem_sup] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  rw [Ideal.mem_span_singleton] at hb
  obtain ⟨r, rfl⟩ := hb
  have hcomp : homogeneousComponent m (a + g * r) = p := by
    rw [hab, homogeneousComponent_eq_self hp]
  rw [map_add, homogeneousComponent_mul_of_isHomogeneous hg] at hcomp
  have ham : homogeneousComponent m a ∈ I :=
    MvPolynomial.homogeneousComponent_mem_of_mem hI ha m
  by_cases hdm : d ≤ m
  · rw [if_pos hdm] at hcomp
    refine Or.inr ⟨hdm, homogeneousComponent (m - d) r, homogeneousComponent_isHomogeneous _ _, ?_⟩
    have hsub : p - g * homogeneousComponent (m - d) r = homogeneousComponent m a := by
      rw [← hcomp]; ring
    rw [hsub]; exact ham
  · rw [if_neg hdm, add_zero] at hcomp
    refine Or.inl ⟨by omega, hcomp ▸ ham⟩
lemma exists_homog_mul_eq_of_isHomogeneous {I : Ideal (MvPolynomial (Fin n) k)}
    (_hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) k))
    {g : MvPolynomial (Fin n) k} {d : ℕ} (_hg : g.IsHomogeneous d)
    (hreg : IsSMulRegular (MvPolynomial (Fin n) k ⧸ I) g)
    {p : MvPolynomial (Fin n) k} {m : ℕ} (_hp : p.IsHomogeneous m)
    (hgp : g * p ∈ I) : p ∈ I := by
  have h1 : g • Ideal.Quotient.mk I p = g • (0 : MvPolynomial (Fin n) k ⧸ I) := by
    rw [smul_zero]
    change Ideal.Quotient.mk I (g * p) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hgp
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hreg h1)
lemma regular_homog_deg_pos {c : ℕ} {d : Fin c → ℕ}
    {f : Fin c → MvPolynomial (Fin n) k}
    (hfd : ∀ i, (f i).IsHomogeneous (d i))
    (hf : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (List.ofFn f)) :
    ∀ i : Fin c, 1 ≤ d i := by
  intro i
  by_contra h0
  have hdi : d i = 0 := by omega
  have hfi_hom : (f i).IsHomogeneous 0 := hdi ▸ hfd i
  have hfi_C : f i = C (coeff 0 (f i)) := by
    apply MvPolynomial.ext; intro u
    by_cases hu : u = 0
    · subst hu; simp
    · have hdeg : u.degree ≠ 0 := by
        intro hd
        apply hu; ext j
        have hle : u j ≤ ∑ r : Fin n, u r :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        rw [← Finsupp.degree_eq_sum, hd] at hle
        simp only [Finsupp.coe_zero, Pi.zero_apply]; omega
      rw [hfi_hom.coeff_eq_zero hdeg, coeff_C, if_neg (Ne.symm hu)]
  by_cases ha : coeff 0 (f i) = 0
  · have hfi0 : f i = 0 := by rw [hfi_C, ha, map_zero]
    have hreg_i := hf.regular_mod_prev i.1 (by simp)
    have hget : (List.ofFn f)[i.1]'(by simp) = f i := by simp
    rw [hget, hfi0] at hreg_i
    have hnt_all : Nontrivial (MvPolynomial (Fin n) k ⧸ (Ideal.ofList (List.ofFn f) • ⊤ :
        Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k))) :=
      hf.quot_ofList_smul_nontrivial ⊤
    have hle_take : (Ideal.ofList ((List.ofFn f).take i.1) • ⊤ :
        Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) ≤
        Ideal.ofList (List.ofFn f) • ⊤ := by
      apply Submodule.smul_mono_left
      exact Ideal.span_mono (fun x hx => List.mem_of_mem_take hx)
    have hnt_i : Nontrivial (MvPolynomial (Fin n) k ⧸
        (Ideal.ofList ((List.ofFn f).take i.1) • ⊤ :
          Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k))) := by
      rw [Submodule.Quotient.nontrivial_iff] at hnt_all ⊢
      intro htop
      rw [htop] at hle_take
      exact hnt_all (top_unique hle_take)
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (MvPolynomial (Fin n) k ⧸
        (Ideal.ofList ((List.ofFn f).take i.1) • ⊤ :
          Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)))
    exact hxy (hreg_i (by simp))
  · have hunit : IsUnit (f i) := by
      rw [hfi_C]
      exact (IsUnit.mk0 (coeff 0 (f i)) ha).map C
    have hmem : f i ∈ Ideal.ofList (List.ofFn f) :=
      Ideal.subset_span (by simp)
    have htop : Ideal.ofList (List.ofFn f) = ⊤ := Ideal.eq_top_of_isUnit_mem _ hmem hunit
    apply hf.top_ne_smul
    rw [htop, Ideal.smul_top_eq_map]; simp
lemma isRegular_of_perm_homog {rs rs' : List (MvPolynomial (Fin n) k)}
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) rs)
    (hperm : rs.Perm rs')
    (hhom : ∀ r ∈ rs, ∃ d ≥ 1, r.IsHomogeneous d) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) rs' := by
  refine ⟨hreg.toIsWeaklyRegular.prototype_perm hperm ?_, ?_⟩
  · intro a b t hsub K hK_eq
    have ha_mem : a ∈ rs := hsub.subset List.mem_cons_self
    obtain ⟨da, hda, ha_hom⟩ := hhom a ha_mem
    have ht_hom : (Ideal.ofList t).IsHomogeneous (homogeneousSubmodule (Fin n) k) := by
      apply isHomogeneous_ideal_ofList
      intro r hr
      have hr_mem : r ∈ rs := hsub.subset (List.mem_cons_of_mem a (List.mem_cons_of_mem b hr))
      obtain ⟨dr, _, hdr⟩ := hhom r hr_mem
      exact ⟨dr, hdr⟩
    have hb_mem : b ∈ rs := hsub.subset (List.mem_cons_of_mem a List.mem_cons_self)
    obtain ⟨db, _, hb_hom⟩ := hhom b hb_mem
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    let I : Ideal (MvPolynomial (Fin n) k) := Ideal.ofList t
    have hItop : (I • ⊤ : Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) = I := by
      simp
    have hhom_K : ∀ q : MvPolynomial (Fin n) k,
        (Submodule.Quotient.mk q : MvPolynomial (Fin n) k ⧸
          (Ideal.ofList t • ⊤ : Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k))) ∈ K ↔
            b * q ∈ I := by
      intro q
      simp only [K, Submodule.mem_torsionBy_iff]
      change (Submodule.Quotient.mk (b * q) : MvPolynomial (Fin n) k ⧸
        (Ideal.ofList t • ⊤ : Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k))) = 0 ↔
          b * q ∈ I
      rw [Submodule.Quotient.mk_eq_zero, hItop]
    have hzero_hom : ∀ e : ℕ, ∀ q : MvPolynomial (Fin n) k, q.IsHomogeneous e → b * q ∈ I → q ∈ I := by
      intro e
      induction e using Nat.strong_induction_on with
      | _ e ih =>
        intro q hq hbq
        have hqK : (Submodule.Quotient.mk q : MvPolynomial (Fin n) k ⧸
            (Ideal.ofList t • ⊤ : Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k))) ∈ K :=
          (hhom_K q).mpr hbq
        rw [hK_eq] at hqK
        rw [Submodule.mem_smul_pointwise_iff_exists] at hqK
        obtain ⟨y, hyK, hay⟩ := hqK
        obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        have hbr : b * r ∈ I := (hhom_K r).mp hyK
        have hsub_mem : q - a * r ∈ I := by
          have : (Submodule.Quotient.mk (a * r - q) : MvPolynomial (Fin n) k ⧸
              (Ideal.ofList t • ⊤ : Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k))) = 0 := by
            rw [Submodule.Quotient.mk_sub, sub_eq_zero]
            exact hay
          rw [Submodule.Quotient.mk_eq_zero, hItop] at this
          simpa using I.neg_mem this
        have hcomp := MvPolynomial.homogeneousComponent_mem_of_mem ht_hom hsub_mem e
        rw [map_sub, homogeneousComponent_eq_self hq, homogeneousComponent_mul_of_isHomogeneous ha_hom] at hcomp
        by_cases hda_le : da ≤ e
        · rw [if_pos hda_le] at hcomp
          have hbr_comp := MvPolynomial.homogeneousComponent_mem_of_mem ht_hom hbr (db + (e - da))
          rw [homogeneousComponent_mul_of_isHomogeneous hb_hom,
            if_pos (Nat.le_add_right db _), Nat.add_sub_cancel_left] at hbr_comp
          have hr_in : homogeneousComponent (e - da) r ∈ I :=
            ih (e - da) (by omega) _ (homogeneousComponent_isHomogeneous _ _) hbr_comp
          have har_in : a * homogeneousComponent (e - da) r ∈ I := I.mul_mem_left a hr_in
          simpa using I.add_mem hcomp har_in
        · rw [if_neg hda_le, sub_zero] at hcomp
          exact hcomp
    have hbp : b * p ∈ I := (hhom_K p).mp hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, hItop]
    rw [MvPolynomial.mem_iff_homogeneousComponent_mem ht_hom]
    intro e
    have hbp_e := MvPolynomial.homogeneousComponent_mem_of_mem ht_hom hbp (db + e)
    rw [homogeneousComponent_mul_of_isHomogeneous hb_hom,
      if_pos (Nat.le_add_right db e), Nat.add_sub_cancel_left] at hbp_e
    exact hzero_hom e _ (homogeneousComponent_isHomogeneous e p) hbp_e
  · have heq : Ideal.ofList rs = Ideal.ofList rs' := by
      show Ideal.span {r | r ∈ rs} = Ideal.span {r | r ∈ rs'}
      congr 1; ext x; exact hperm.mem_iff
    rw [← heq]; exact hreg.top_ne_smul
abbrev KoszulChain (n : ℕ) (R : Type*) (p : ℕ) :=
  { s : Finset (Fin n) // s.card = p } → R
def koszulSign (T : Finset (Fin n)) (i : Fin n) : ℤ :=
  (-1 : ℤ) ^ ((T.filter (· < i)).card)
lemma koszulSign_mul_self (T : Finset (Fin n)) (i : Fin n) :
    koszulSign T i * koszulSign T i = 1 := by
  unfold koszulSign
  rw [← mul_pow]; norm_num
lemma koszulSign_insert_comm {T : Finset (Fin n)} {i j : Fin n} (hi : i ∉ T) (hj : j ∉ T)
    (hij : i ≠ j) :
    koszulSign T i * koszulSign (insert i T) j =
      -(koszulSign T j * koszulSign (insert j T) i) := by
  unfold koszulSign
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h1 : (insert i T).filter (· < j) = insert i (T.filter (· < j)) := by
      ext x; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxj⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hxj⟩
      · rintro (rfl | ⟨hx, hxj⟩)
        · exact ⟨Or.inl rfl, hlt⟩
        · exact ⟨Or.inr hx, hxj⟩
    have h2 : (insert j T).filter (· < i) = T.filter (· < i) := by
      ext x; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxi⟩
        · exact absurd (lt_trans hlt hxi) (lt_irrefl _)
        · exact ⟨hx, hxi⟩
      · rintro ⟨hx, hxi⟩; exact ⟨Or.inr hx, hxi⟩
    have hi_not : i ∉ T.filter (· < j) := fun h => hi (mem_filter.mp h).1
    rw [h1, h2, Finset.card_insert_of_notMem hi_not, pow_succ]
    ring
  · have h1 : (insert i T).filter (· < j) = T.filter (· < j) := by
      ext x; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxj⟩
        · exact absurd (lt_trans hgt hxj) (lt_irrefl _)
        · exact ⟨hx, hxj⟩
      · rintro ⟨hx, hxj⟩; exact ⟨Or.inr hx, hxj⟩
    have h2 : (insert j T).filter (· < i) = insert j (T.filter (· < i)) := by
      ext x; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hx, hxi⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hxi⟩
      · rintro (rfl | ⟨hx, hxi⟩)
        · exact ⟨Or.inl rfl, hgt⟩
        · exact ⟨Or.inr hx, hxi⟩
    have hj_not : j ∉ T.filter (· < i) := fun h => hj (mem_filter.mp h).1
    rw [h1, h2, Finset.card_insert_of_notMem hj_not, pow_succ]
    ring
def koszulDiff {R : Type*} [CommRing R] (x : Fin n → R) (p : ℕ)
    (f : KoszulChain n R (p + 1)) : KoszulChain n R p :=
  fun T => ∑ i : Fin n,
    if h : i ∈ T.1 then 0
    else koszulSign T.1 i •
      (x i * f ⟨insert i T.1, by rw [Finset.card_insert_of_notMem h, T.2]⟩)
lemma koszulDiff_zero {R : Type*} [CommRing R] (x : Fin n → R) (p : ℕ) :
    koszulDiff x p (0 : KoszulChain n R (p + 1)) = 0 := by
  ext T; simp [koszulDiff]
lemma koszulDiff_add {R : Type*} [CommRing R] (x : Fin n → R) (p : ℕ)
    (f g : KoszulChain n R (p + 1)) :
    koszulDiff x p (f + g) = koszulDiff x p f + koszulDiff x p g := by
  ext T
  simp only [koszulDiff, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_add, smul_add]
lemma koszulDiff_sub {R : Type*} [CommRing R] (x : Fin n → R) (p : ℕ)
    (f g : KoszulChain n R (p + 1)) :
    koszulDiff x p (f - g) = koszulDiff x p f - koszulDiff x p g := by
  ext T
  simp only [koszulDiff, Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_sub, smul_sub]
lemma koszulDiff_smul {R : Type*} [CommRing R] (x : Fin n → R) (p : ℕ)
    (r : R) (f : KoszulChain n R (p + 1)) :
    koszulDiff x p (fun s => r * f s) = fun T => r * koszulDiff x p f T := by
  ext T
  simp only [koszulDiff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [mul_zero]
  · rw [zsmul_eq_mul, zsmul_eq_mul]; ring
lemma koszulDiff_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (x : Fin n → R) (p : ℕ) (f : KoszulChain n R (p + 1)) :
    koszulDiff (fun i => φ (x i)) p (fun s => φ (f s)) =
      fun T => φ (koszulDiff x p f T) := by
  ext T
  simp only [koszulDiff, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · exact (map_zero φ).symm
  · simp only [map_zsmul, map_mul]
lemma sum_antisymm_eq_zero {R : Type*} [AddCommGroup R] (F : Fin n → Fin n → R)
    (hdiag : ∀ i, F i i = 0) (hanti : ∀ i j, i ≠ j → F i j + F j i = 0) :
    ∑ i : Fin n, ∑ j : Fin n, F i j = 0 := by
  rw [← Finset.sum_product']
  let Slt := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)
  let Sgt := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1)
  let Seq := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 = p.2)
  have hpart : (Finset.univ : Finset (Fin n × Fin n)) = Slt ∪ (Sgt ∪ Seq) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, Slt, Sgt, Seq,
      true_iff]
    rcases lt_trichotomy i j with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have hd1 : Disjoint Slt (Sgt ∪ Seq) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp only [Slt, Sgt, Seq, Finset.mem_filter, Finset.mem_union] at h1 h2
    rcases h2 with h2 | h2 <;> omega
  have hd2 : Disjoint Sgt Seq := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp only [Sgt, Seq, Finset.mem_filter] at h1 h2
    omega
  rw [show (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n)) = Finset.univ from rfl,
    hpart, Finset.sum_union hd1, Finset.sum_union hd2]
  have hSeq : ∑ p ∈ Seq, F p.1 p.2 = 0 :=
    Finset.sum_eq_zero fun ⟨i, j⟩ hp => by
      have h : i = j := (Finset.mem_filter.mp hp).2
      subst h; exact hdiag i
  have hSgt : ∑ p ∈ Sgt, F p.1 p.2 = ∑ p ∈ Slt, F p.2 p.1 := by
    refine Finset.sum_nbij Prod.swap ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ hp
      simp only [Sgt, Slt, Finset.mem_filter, Prod.swap_prod_mk, Finset.mem_univ,
        true_and] at hp ⊢
      exact hp
    · intro _ _ _ _ h; exact Prod.swap_injective h
    · rintro ⟨i, j⟩ hp
      refine ⟨(j, i), ?_, rfl⟩
      simp only [Sgt, Slt, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · rintro ⟨i, j⟩ _; rfl
  rw [hSeq, add_zero, hSgt, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun ⟨i, j⟩ hp =>
    hanti i j (ne_of_lt (Finset.mem_filter.mp hp).2)
lemma koszulDiff_comp_koszulDiff {R : Type*} [CommRing R] (x : Fin n → R) (p : ℕ)
    (f : KoszulChain n R (p + 2)) :
    koszulDiff x p (koszulDiff x (p + 1) f) = 0 := by
  ext T
  simp only [koszulDiff, Pi.zero_apply]
  have hexpand : ∀ i : Fin n,
      (if hi : i ∈ T.1 then (0 : R)
       else koszulSign T.1 i • (x i * ∑ j : Fin n,
         if hj : j ∈ insert i T.1 then 0
         else koszulSign (insert i T.1) j •
           (x j * f ⟨insert j (insert i T.1), by
             rw [Finset.card_insert_of_notMem hj, Finset.card_insert_of_notMem hi, T.2]⟩))) =
      ∑ j : Fin n,
        if h : i ∉ T.1 ∧ j ∉ T.1 ∧ i ≠ j then
          (koszulSign T.1 i * koszulSign (insert i T.1) j) •
            (x i * x j * f ⟨insert j (insert i T.1), by
              have hj' : j ∉ insert i T.1 := by
                simp only [mem_insert, not_or]; exact ⟨h.2.2.symm, h.2.1⟩
              rw [Finset.card_insert_of_notMem hj', Finset.card_insert_of_notMem h.1, T.2]⟩)
        else 0 := by
    intro i
    by_cases hi : i ∈ T.1
    · rw [dif_pos hi]; symm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [dif_neg (fun h => h.1 hi)]
    · rw [dif_neg hi, Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ insert i T.1
      · rw [dif_pos hj, mul_zero, smul_zero, dif_neg]
        intro h; rw [mem_insert] at hj
        rcases hj with rfl | hjT
        · exact h.2.2 rfl
        · exact h.2.1 hjT
      · have hcond : i ∉ T.1 ∧ j ∉ T.1 ∧ i ≠ j := by
          rw [mem_insert, not_or] at hj
          exact ⟨hi, hj.2, Ne.symm hj.1⟩
        rw [dif_neg hj, dif_pos hcond]
        rw [zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, Int.cast_mul]; ring
  simp_rw [hexpand]
  apply sum_antisymm_eq_zero
  · intro i; simp
  · intro i j hij
    by_cases h1 : i ∉ T.1 ∧ j ∉ T.1
    · have hc1 : i ∉ T.1 ∧ j ∉ T.1 ∧ i ≠ j := ⟨h1.1, h1.2, hij⟩
      have hc2 : j ∉ T.1 ∧ i ∉ T.1 ∧ j ≠ i := ⟨h1.2, h1.1, hij.symm⟩
      rw [dif_pos hc1, dif_pos hc2]
      have hj1 : j ∉ insert i T.1 := by simp only [mem_insert, not_or]; exact ⟨hij.symm, h1.2⟩
      have hi2 : i ∉ insert j T.1 := by simp only [mem_insert, not_or]; exact ⟨hij, h1.1⟩
      have hset : (⟨insert j (insert i T.1), by
          rw [Finset.card_insert_of_notMem hj1, Finset.card_insert_of_notMem h1.1, T.2]⟩ :
            { s : Finset (Fin n) // s.card = p + 2 }) =
          ⟨insert i (insert j T.1), by
            rw [Finset.card_insert_of_notMem hi2, Finset.card_insert_of_notMem h1.2, T.2]⟩ :=
        Subtype.ext (Finset.insert_comm j i T.1)
      rw [hset, koszulSign_insert_comm h1.1 h1.2 hij, neg_smul, mul_comm (x i) (x j),
        neg_add_cancel]
    · have h1' : ¬ (i ∉ T.1 ∧ j ∉ T.1 ∧ i ≠ j) := fun h => h1 ⟨h.1, h.2.1⟩
      have h2' : ¬ (j ∉ T.1 ∧ i ∉ T.1 ∧ j ≠ i) := fun h => h1 ⟨h.2.1, h.1⟩
      rw [dif_neg h1', dif_neg h2', add_zero]
def isKoszulCycle {R : Type*} [CommRing R] (x : Fin n → R) :
    (p : ℕ) → KoszulChain n R p → Prop
  | 0, _ => True
  | p + 1, z => koszulDiff x p z = 0
def IsHomogIn (I : Ideal (MvPolynomial (Fin n) k)) (e : ℤ) (r : MvPolynomial (Fin n) k ⧸ I) : Prop :=
  (e < 0 ∧ r = 0) ∨ (0 ≤ e ∧ ∃ p : MvPolynomial (Fin n) k, p.IsHomogeneous e.toNat ∧ Ideal.Quotient.mk I p = r)
lemma isHomogIn_zero (I : Ideal (MvPolynomial (Fin n) k)) (e : ℤ) : IsHomogIn I e 0 := by
  by_cases h : e < 0
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, 0, isHomogeneous_zero _ _ _, map_zero _⟩
lemma isHomogIn_add {I : Ideal (MvPolynomial (Fin n) k)} {e : ℤ} {a b : MvPolynomial (Fin n) k ⧸ I}
    (ha : IsHomogIn I e a) (hb : IsHomogIn I e b) : IsHomogIn I e (a + b) := by
  rcases ha with ⟨hneg, rfl⟩ | ⟨hnn, p, hp, rfl⟩
  · rcases hb with ⟨_, rfl⟩ | ⟨hnn, _⟩
    · exact Or.inl ⟨hneg, add_zero 0⟩
    · omega
  · rcases hb with ⟨hneg, _⟩ | ⟨_, q, hq, rfl⟩
    · omega
    · exact Or.inr ⟨hnn, p + q, hp.add hq, map_add _ p q⟩
lemma isHomogIn_sub {I : Ideal (MvPolynomial (Fin n) k)} {e : ℤ} {a b : MvPolynomial (Fin n) k ⧸ I}
    (ha : IsHomogIn I e a) (hb : IsHomogIn I e b) : IsHomogIn I e (a - b) := by
  rcases ha with ⟨hneg, rfl⟩ | ⟨hnn, p, hp, rfl⟩
  · rcases hb with ⟨_, rfl⟩ | ⟨hnn, _⟩
    · exact Or.inl ⟨hneg, sub_zero 0⟩
    · omega
  · rcases hb with ⟨hneg, _⟩ | ⟨_, q, hq, rfl⟩
    · omega
    · exact Or.inr ⟨hnn, p - q, hp.sub hq, map_sub _ p q⟩
lemma isHomogIn_zsmul {I : Ideal (MvPolynomial (Fin n) k)} {e : ℤ} (c : ℤ)
    {a : MvPolynomial (Fin n) k ⧸ I} (ha : IsHomogIn I e a) : IsHomogIn I e (c • a) := by
  rcases ha with ⟨hneg, rfl⟩ | ⟨hnn, p, hp, rfl⟩
  · exact Or.inl ⟨hneg, smul_zero c⟩
  · refine Or.inr ⟨hnn, c • p, ?_, map_zsmul _ c p⟩
    rw [zsmul_eq_mul]
    have hc : ((c : MvPolynomial (Fin n) k)).IsHomogeneous 0 := by
      have : (c : MvPolynomial (Fin n) k) = C (c : k) := by simp
      rw [this]; exact isHomogeneous_C _ _
    simpa using hc.mul hp
lemma isHomogIn_sum {I : Ideal (MvPolynomial (Fin n) k)} {e : ℤ} {ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) k ⧸ I)
    (hf : ∀ i ∈ s, IsHomogIn I e (f i)) : IsHomogIn I e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isHomogIn_zero I e
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isHomogIn_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
lemma isHomogIn_mul_homog {I : Ideal (MvPolynomial (Fin n) k)} {e : ℤ} {d : ℕ}
    {g : MvPolynomial (Fin n) k} (hg : g.IsHomogeneous d)
    {a : MvPolynomial (Fin n) k ⧸ I} (ha : IsHomogIn I e a) :
    IsHomogIn I (e + d) (Ideal.Quotient.mk I g * a) := by
  rcases ha with ⟨hneg, rfl⟩ | ⟨hnn, p, hp, rfl⟩
  · rw [mul_zero]; exact isHomogIn_zero I (e + d)
  · refine Or.inr ⟨by omega, g * p, ?_, map_mul _ g p⟩
    have hdeg : (e + (d : ℤ)).toNat = d + e.toNat := by omega
    rw [hdeg]
    exact hg.mul hp
def IsHomogChain (I : Ideal (MvPolynomial (Fin n) k)) (p : ℕ) (t : ℤ)
    (f : KoszulChain n (MvPolynomial (Fin n) k ⧸ I) p) : Prop :=
  ∀ s, IsHomogIn I (t - p) (f s)
lemma isHomogChain_koszulDiff {I : Ideal (MvPolynomial (Fin n) k)} {p : ℕ} {t : ℤ}
    {f : KoszulChain n (MvPolynomial (Fin n) k ⧸ I) (p + 1)}
    (hf : IsHomogChain I (p + 1) t f) :
    IsHomogChain I p t (koszulDiff (fun i => Ideal.Quotient.mk I (X i)) p f) := by
  intro T
  apply isHomogIn_sum
  intro i _
  split_ifs with h
  · exact isHomogIn_zero I (t - p)
  · apply isHomogIn_zsmul
    have h1 := isHomogIn_mul_homog (isHomogeneous_X k i)
      (hf ⟨insert i T.1, by rw [Finset.card_insert_of_notMem h, T.2]⟩)
    have hdeg : t - ↑(p + 1) + (1 : ℕ) = t - (p : ℤ) := by push_cast; omega
    rwa [hdeg] at h1
def KoszulExactAt (I : Ideal (MvPolynomial (Fin n) k)) (p : ℕ) (t : ℤ) : Prop :=
  ∀ z : KoszulChain n (MvPolynomial (Fin n) k ⧸ I) p,
    IsHomogChain I p t z →
    isKoszulCycle (fun i => Ideal.Quotient.mk I (X i)) p z →
    ∃ v : KoszulChain n (MvPolynomial (Fin n) k ⧸ I) (p + 1),
      IsHomogChain I (p + 1) t v ∧
      koszulDiff (fun i => Ideal.Quotient.mk I (X i)) p v = z
noncomputable def finsetInd (s : Finset (Fin n)) : Fin n →₀ ℕ :=
  s.sum (fun i => Finsupp.single i 1)
lemma finsetInd_apply (s : Finset (Fin n)) (i : Fin n) :
    finsetInd s i = if i ∈ s then 1 else 0 := by
  classical
  unfold finsetInd
  rw [Finsupp.finsetSum_apply]
  by_cases hi : i ∈ s
  · rw [if_pos hi, Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Finsupp.single_eq_of_ne (Ne.symm hji)]
    · intro h; exact absurd hi h
  · rw [if_neg hi]
    exact Finset.sum_eq_zero fun j hj => by
      have hne : j ≠ i := fun h => hi (h ▸ hj)
      simp [Finsupp.single_eq_of_ne hne.symm]
lemma finsetInd_degree (s : Finset (Fin n)) : (finsetInd s).degree = s.card := by
  classical
  rw [Finsupp.degree_eq_sum]
  simp_rw [finsetInd_apply]
  simp
lemma finsetInd_insert {s : Finset (Fin n)} {i : Fin n} (hi : i ∉ s) :
    finsetInd (insert i s) = finsetInd s + Finsupp.single i 1 := by
  unfold finsetInd
  rw [Finset.sum_insert hi, add_comm]
lemma finsetInd_le_iff {s : Finset (Fin n)} {α : Fin n →₀ ℕ} :
    finsetInd s ≤ α ↔ ∀ i ∈ s, 1 ≤ α i := by
  rw [Finsupp.le_def]
  constructor
  · intro h i hi; have := h i; rw [finsetInd_apply, if_pos hi] at this; exact this
  · intro h i; rw [finsetInd_apply]; split_ifs with hi
    · exact h i hi
    · exact Nat.zero_le _
lemma finsetInd_erase_add {s : Finset (Fin n)} {k₀ : Fin n} (hk : k₀ ∈ s) :
    finsetInd (s.erase k₀) + Finsupp.single k₀ 1 = finsetInd s := by
  rw [← finsetInd_insert (Finset.notMem_erase k₀ s), Finset.insert_erase hk]
lemma koszulExactAt_bot_zero {t : ℤ} (ht : t ≠ 0) :
    KoszulExactAt (⊥ : Ideal (MvPolynomial (Fin n) k)) 0 t := by
  intro z hz _
  have hz0 := hz ⟨∅, Finset.card_empty⟩
  simp only [Nat.cast_zero, sub_zero] at hz0
  rcases hz0 with ⟨hneg, hzero⟩ | ⟨hnn, p, hp, hmk⟩
  · refine ⟨0, fun s => isHomogIn_zero _ _, ?_⟩
    ext T
    have hT : T = ⟨∅, Finset.card_empty⟩ := Subtype.ext (Finset.card_eq_zero.mp T.2)
    rw [hT, koszulDiff_zero, Pi.zero_apply, hzero]
  · have ht_pos : 1 ≤ t.toNat := by omega
    have hdeg_supp : ∀ {u : Fin n →₀ ℕ}, u ∈ p.support → u.degree = t.toNat := by
      intro u hu
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hu) (hp.coeff_eq_zero hne)
    let pick (u : Fin n →₀ ℕ) (hu : u ∈ p.support) : Fin n :=
      u.support.min' (by
        rw [Finsupp.support_nonempty_iff]
        intro hu0
        have hd := hdeg_supp hu
        rw [hu0, map_zero] at hd; omega)
    have hpick_pos : ∀ (u : Fin n →₀ ℕ) (hu : u ∈ p.support), 1 ≤ u (pick u hu) := by
      intro u hu
      have hmem : pick u hu ∈ u.support := Finset.min'_mem _ _
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmem)
    let q (i : Fin n) : MvPolynomial (Fin n) k :=
      p.support.attach.sum fun u =>
        if pick u.1 u.2 = i then monomial (u.1 - Finsupp.single i 1) (coeff u.1 p) else 0
    have hq_hom : ∀ i : Fin n, (q i).IsHomogeneous (t.toNat - 1) := by
      intro i
      apply IsHomogeneous.sum
      intro u _
      split_ifs with hpi
      · have hpos : 1 ≤ u.1 i := hpi ▸ hpick_pos u.1 u.2
        have hadd : (u.1 - Finsupp.single i 1) + Finsupp.single i 1 = u.1 := by
          ext j; by_cases hj : j = i
          · subst hj; simp; omega
          · simp [Finsupp.single_eq_of_ne hj]
        have hdeg : (u.1 - Finsupp.single i 1).degree = t.toNat - 1 := by
          have h := congrArg Finsupp.degree hadd
          rw [map_add, Finsupp.degree_single, hdeg_supp u.2] at h; omega
        intro v hv
        rw [coeff_monomial] at hv
        split_ifs at hv with hvu
        · subst hvu; rw [weight_one_eq_deg]; exact hdeg
        · exact absurd rfl hv
      · exact isHomogeneous_zero _ _ _
    have hp_eq : ∑ i : Fin n, X i * q i = p := by
      simp only [q, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hterm : ∀ u : { u // u ∈ p.support },
          ∑ i : Fin n, X i * (if pick u.1 u.2 = i then
              monomial (u.1 - Finsupp.single i 1) (coeff u.1 p) else 0) =
            monomial u.1 (coeff u.1 p) := by
        intro u
        rw [Finset.sum_eq_single (pick u.1 u.2)]
        · rw [if_pos rfl, X, monomial_mul, one_mul]
          have hadd : Finsupp.single (pick u.1 u.2) 1 + (u.1 - Finsupp.single (pick u.1 u.2) 1) = u.1 := by
            ext j
            by_cases hj : j = pick u.1 u.2
            · subst hj; have := hpick_pos u.1 u.2; simp; omega
            · simp [Finsupp.single_eq_of_ne hj]
          rw [hadd]
        · intro i _ hi; rw [if_neg hi.symm, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [hterm]
      rw [Finset.sum_attach p.support (fun u => monomial u (coeff u p))]
      exact p.as_sum.symm
    let v : KoszulChain n (MvPolynomial (Fin n) k ⧸ (⊥ : Ideal _)) 1 := fun s =>
      let i := s.1.min' (Finset.card_pos.mp (by omega))
      Ideal.Quotient.mk ⊥ (q i)
    refine ⟨v, ?_, ?_⟩
    · intro s
      refine Or.inr ⟨by omega, q _, ?_, rfl⟩
      have hdeg : (t - (1 : ℕ)).toNat = t.toNat - 1 := by omega
      rw [hdeg]; exact hq_hom _
    · ext T
      have hT : T = ⟨∅, Finset.card_empty⟩ := Subtype.ext (Finset.card_eq_zero.mp T.2)
      rw [hT, ← hmk]
      simp only [koszulDiff, Finset.notMem_empty, ↓reduceDIte, koszulSign, Finset.filter_empty,
        Finset.card_empty, pow_zero, one_zsmul, v]
      have hv_eq : ∀ i : Fin n,
          Ideal.Quotient.mk (⊥ : Ideal _) (X i) *
            Ideal.Quotient.mk ⊥ (q ((insert i ∅ : Finset (Fin n)).min' (Finset.insert_nonempty i ∅))) =
          Ideal.Quotient.mk ⊥ (X i * q i) := by
        intro i
        have hmin : (insert i (∅ : Finset (Fin n))).min' (by simp) = i := by simp
        rw [hmin, map_mul]
      simp_rw [hv_eq]
      rw [← map_sum, hp_eq]
lemma koszulExactAt_bot_succ (p : ℕ) (t : ℤ) :
    KoszulExactAt (⊥ : Ideal (MvPolynomial (Fin n) k)) (p + 1) t := by
  classical
  intro z hz hcyc
  let eBot : (MvPolynomial (Fin n) k ⧸ (⊥ : Ideal (MvPolynomial (Fin n) k))) ≃+*
      MvPolynomial (Fin n) k :=
    RingEquiv.quotientBot (MvPolynomial (Fin n) k)
  have heBot_mk : ∀ a : MvPolynomial (Fin n) k, eBot (Ideal.Quotient.mk ⊥ a) = a := fun _ => rfl
  let f : KoszulChain n (MvPolynomial (Fin n) k) (p + 1) := fun s => eBot (z s)
  have hf_cyc : koszulDiff (fun i => (X i : MvPolynomial (Fin n) k)) p f = 0 := by
    have h1 := koszulDiff_map eBot.toRingHom (fun i => Ideal.Quotient.mk (⊥ : Ideal _) (X i)) p z
    change koszulDiff (fun i => (X i : MvPolynomial (Fin n) k)) p f =
      fun T => eBot (koszulDiff (fun i => Ideal.Quotient.mk ⊥ (X i)) p z T) at h1
    rw [h1, hcyc]
    ext T; simp
  by_cases hneg : t - ↑(p + 1) < 0
  · refine ⟨0, fun s => isHomogIn_zero _ _, ?_⟩
    rw [koszulDiff_zero]
    ext s
    rcases hz s with ⟨_, h0⟩ | ⟨hnn, _⟩
    · exact h0.symm
    · omega
  · have hnn : 0 ≤ t - ↑(p + 1) := by omega
    let d : ℕ := (t - ↑(p + 1)).toNat
    have hf_hom : ∀ s, (f s).IsHomogeneous d := by
      intro s
      rcases hz s with ⟨hlt, _⟩ | ⟨_, q, hq, hmk⟩
      · omega
      · have hfs : f s = q := by dsimp only [f]; rw [← hmk]; rfl
        rw [hfs]; exact hq
    let A : Finset (Fin n →₀ ℕ) :=
      Finset.univ.biUnion (fun s : { s : Finset (Fin n) // s.card = p + 1 } =>
        (f s).support.image (· + finsetInd s.1))
    have hA_deg : ∀ α ∈ A, α.degree = d + (p + 1) := by
      intro α hα
      simp only [A, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hα
      obtain ⟨s, u, hu, rfl⟩ := hα
      have hu_deg : u.degree = d := by
        by_contra hne
        exact (MvPolynomial.mem_support_iff.mp hu) ((hf_hom s).coeff_eq_zero hne)
      rw [map_add, hu_deg, finsetInd_degree, s.2]
    have hA_ne : ∀ α ∈ A, α.support.Nonempty := by
      intro α hα
      rw [Finsupp.support_nonempty_iff]
      intro h0
      have := hA_deg α hα
      rw [h0, map_zero] at this; omega
    let g_α (α : { α // α ∈ A }) : KoszulChain n (MvPolynomial (Fin n) k) (p + 2) := fun U =>
      let k₀ := α.1.support.min' (hA_ne α.1 α.2)
      if h : k₀ ∈ U.1 ∧ finsetInd U.1 ≤ α.1 then
        let U' : { s : Finset (Fin n) // s.card = p + 1 } :=
          ⟨U.1.erase k₀, by rw [Finset.card_erase_of_mem h.1, U.2]; rfl⟩
        koszulSign U'.1 k₀ •
          monomial (α.1 - finsetInd U.1) (coeff (α.1 - finsetInd U'.1) (f U'))
      else 0
    have hg_α_diff : ∀ (α : { α // α ∈ A }) (s : { s : Finset (Fin n) // s.card = p + 1 }),
        koszulDiff (fun i => (X i : MvPolynomial (Fin n) k)) (p + 1) (g_α α) s =
          if finsetInd s.1 ≤ α.1 then
            monomial (α.1 - finsetInd s.1) (coeff (α.1 - finsetInd s.1) (f s))
          else 0 := by
      intro α s
      set k₀ := α.1.support.min' (hA_ne α.1 α.2)
      have hk₀_pos : 1 ≤ α.1 k₀ :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Finset.min'_mem _ _))
      by_cases hks : k₀ ∈ s.1
      ·
        let T : { s : Finset (Fin n) // s.card = p } :=
          ⟨s.1.erase k₀, by rw [Finset.card_erase_of_mem hks, s.2]; rfl⟩
        have hs_eq : insert k₀ T.1 = s.1 := Finset.insert_erase hks
        by_cases hle : finsetInd s.1 ≤ α.1
        · rw [if_pos hle]
          have hterm : ∀ i : Fin n,
              (if hi : i ∈ s.1 then (0 : MvPolynomial (Fin n) k)
               else koszulSign s.1 i • (X i * g_α α ⟨insert i s.1, by
                 rw [Finset.card_insert_of_notMem hi, s.2]⟩)) =
              monomial (α.1 - finsetInd s.1)
                (if hi : i ∈ s.1 then 0
                 else -(koszulSign T.1 k₀ * koszulSign T.1 i) •
                   coeff (α.1 - finsetInd T.1) (X i * f ⟨insert i T.1, by
                     have hiT : i ∉ T.1 := fun h => hi (Finset.mem_of_mem_erase h)
                     rw [Finset.card_insert_of_notMem hiT, T.2]⟩)) := by
            intro i
            by_cases hi : i ∈ s.1
            · rw [dif_pos hi, dif_pos hi, monomial_zero]
            · rw [dif_neg hi, dif_neg hi]
              have hik : i ≠ k₀ := fun h => hi (h ▸ hks)
              have hiT : i ∉ T.1 := fun h => hi (Finset.mem_of_mem_erase h)
              have hkT : k₀ ∉ T.1 := Finset.notMem_erase k₀ s.1
              have hk_ins : k₀ ∈ insert i s.1 := Finset.mem_insert_of_mem hks
              have herase : (insert i s.1).erase k₀ = insert i T.1 := by
                ext x; simp only [mem_erase, mem_insert, T]
                constructor
                · rintro ⟨hxk, rfl | hxs⟩
                  · exact Or.inl rfl
                  · exact Or.inr ⟨hxk, hxs⟩
                · rintro (rfl | ⟨hxk, hxs⟩)
                  · exact ⟨hik, Or.inl rfl⟩
                  · exact ⟨hxk, Or.inr hxs⟩
              by_cases hαi : 1 ≤ α.1 i
              · have hle_ins : finsetInd (insert i s.1) ≤ α.1 := by
                  rw [finsetInd_le_iff] at hle ⊢
                  intro j hj; rw [mem_insert] at hj
                  rcases hj with rfl | hjs
                  · exact hαi
                  · exact hle j hjs
                have hcond : k₀ ∈ insert i s.1 ∧ finsetInd (insert i s.1) ≤ α.1 :=
                  ⟨hk_ins, hle_ins⟩
                dsimp only [g_α]
                rw [dif_pos hcond]
                have hU'_eq : (⟨(insert i s.1).erase k₀, by
                    rw [Finset.card_erase_of_mem hk_ins, Finset.card_insert_of_notMem hi, s.2]; rfl⟩ :
                      { u : Finset (Fin n) // u.card = p + 1 }) =
                    ⟨insert i T.1, by rw [Finset.card_insert_of_notMem hiT, T.2]⟩ :=
                  Subtype.ext herase
                rw [hU'_eq]
                have hexp : Finsupp.single i 1 + (α.1 - finsetInd (insert i s.1)) =
                    α.1 - finsetInd s.1 := by
                  ext j
                  rw [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Finsupp.coe_tsub,
                    Pi.sub_apply, Pi.sub_apply, finsetInd_apply, finsetInd_apply]
                  by_cases hji : j = i
                  · subst hji; simp [hi]; omega
                  · simp [Finsupp.single_eq_of_ne hji, hji]
                have hcoeff_Xi : coeff (α.1 - finsetInd T.1)
                    (X i * f ⟨insert i T.1, by rw [Finset.card_insert_of_notMem hiT, T.2]⟩) =
                    coeff (α.1 - finsetInd (insert i T.1))
                      (f ⟨insert i T.1, by rw [Finset.card_insert_of_notMem hiT, T.2]⟩) := by
                  have hsub_add : α.1 - finsetInd T.1 =
                      Finsupp.single i 1 + (α.1 - finsetInd (insert i T.1)) := by
                    ext j
                    rw [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Finsupp.coe_tsub,
                      Pi.sub_apply, Pi.sub_apply, finsetInd_apply, finsetInd_apply]
                    by_cases hji : j = i
                    · subst hji; simp [hiT]; omega
                    · simp [Finsupp.single_eq_of_ne hji, hji]
                  rw [hsub_add, X, coeff_monomial_mul, one_mul]
                rw [hcoeff_Xi]
                have hsign : koszulSign s.1 i * koszulSign (insert i T.1) k₀ =
                    -(koszulSign T.1 k₀ * koszulSign T.1 i) := by
                  have hs1 : s.1 = insert k₀ T.1 := hs_eq.symm
                  rw [hs1, mul_comm (koszulSign T.1 k₀) (koszulSign T.1 i)]
                  have h := koszulSign_insert_comm (T := T.1) (i := i) (j := k₀) hiT hkT hik
                  have h2 := congrArg (fun z => koszulSign (insert k₀ T.1) i * koszulSign T.1 i * z) h
                  have hsq1 := koszulSign_mul_self T.1 i
                  have hsq2 := koszulSign_mul_self (insert k₀ T.1) i
                  calc koszulSign (insert k₀ T.1) i * koszulSign (insert i T.1) k₀
                      = (koszulSign T.1 i * koszulSign T.1 i) *
                          (koszulSign (insert k₀ T.1) i * koszulSign (insert i T.1) k₀) := by rw [hsq1, one_mul]
                    _ = koszulSign (insert k₀ T.1) i * koszulSign T.1 i *
                          (koszulSign T.1 i * koszulSign (insert i T.1) k₀) := by ring
                    _ = koszulSign (insert k₀ T.1) i * koszulSign T.1 i *
                          -(koszulSign T.1 k₀ * koszulSign (insert k₀ T.1) i) := h2
                    _ = -(koszulSign (insert k₀ T.1) i * koszulSign (insert k₀ T.1) i) *
                          (koszulSign T.1 i * koszulSign T.1 k₀) := by ring
                    _ = -(koszulSign T.1 i * koszulSign T.1 k₀) := by rw [hsq2]; ring
                rw [show α.1.support.min' (hA_ne α.1 α.2) = k₀ from rfl, herase,
                  mul_smul_comm, smul_smul, hsign, X, monomial_mul, one_mul, hexp, smul_monomial]
              ·
                have hnot : ¬ (k₀ ∈ insert i s.1 ∧ finsetInd (insert i s.1) ≤ α.1) := by
                  intro ⟨_, hle'⟩
                  have := finsetInd_le_iff.mp hle' i (Finset.mem_insert_self i s.1)
                  omega
                dsimp only [g_α]
                rw [dif_neg hnot, mul_zero, smul_zero]
                have hcoeff0 : coeff (α.1 - finsetInd T.1)
                    (X i * f ⟨insert i T.1, by rw [Finset.card_insert_of_notMem hiT, T.2]⟩) = 0 := by
                  rw [X, coeff_monomial_mul']
                  rw [if_neg]
                  intro hle_s
                  have h1 := Finsupp.le_def.mp hle_s i
                  rw [Finsupp.single_eq_same, Finsupp.coe_tsub, Pi.sub_apply,
                    finsetInd_apply, if_neg hiT, Nat.sub_zero] at h1
                  omega
                rw [hcoeff0, smul_zero, monomial_zero]
          dsimp only [koszulDiff]
          simp_rw [hterm]
          rw [← map_sum]
          congr 1
          have hcycT : coeff (α.1 - finsetInd T.1)
              (koszulDiff (fun i => (X i : MvPolynomial (Fin n) k)) p f T) = 0 := by
            rw [hf_cyc, Pi.zero_apply, coeff_zero]
          simp only [koszulDiff, coeff_sum] at hcycT
          have hcoeff_zsmul : ∀ (c : ℤ) (a : MvPolynomial (Fin n) k) (u : Fin n →₀ ℕ),
              coeff u (c • a) = c • coeff u a := fun c a u => map_zsmul (MvPolynomial.lcoeff k u) c a
          have hsplit : ∑ i : Fin n,
              coeff (α.1 - finsetInd T.1)
                (if h : i ∈ T.1 then 0 else koszulSign T.1 i •
                  (X i * f ⟨insert i T.1, by rw [Finset.card_insert_of_notMem h, T.2]⟩)) =
              koszulSign T.1 k₀ • coeff (α.1 - finsetInd s.1) (f s) +
              ∑ i : Fin n,
                if hi : i ∈ s.1 then 0
                else koszulSign T.1 i • coeff (α.1 - finsetInd T.1)
                  (X i * f ⟨insert i T.1, by
                    have hiT : i ∉ T.1 := fun h => hi (Finset.mem_of_mem_erase h)
                    rw [Finset.card_insert_of_notMem hiT, T.2]⟩) := by
            have hkT : k₀ ∉ T.1 := Finset.notMem_erase k₀ s.1
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀)]
            congr 1
            · rw [dif_neg hkT, hcoeff_zsmul]
              congr 1
              have hsub_add : α.1 - finsetInd T.1 = Finsupp.single k₀ 1 + (α.1 - finsetInd s.1) := by
                ext j
                rw [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Finsupp.coe_tsub,
                  Pi.sub_apply, Pi.sub_apply, finsetInd_apply, finsetInd_apply]
                by_cases hjk : j = k₀
                · subst hjk; simp [hkT, hks]; omega
                · simp [Finsupp.single_eq_of_ne hjk, T, hjk]
              have hs_sub : (⟨insert k₀ T.1, by rw [Finset.card_insert_of_notMem hkT, T.2]⟩ :
                  { u : Finset (Fin n) // u.card = p + 1 }) = s := Subtype.ext hs_eq
              rw [hs_sub, hsub_add, X, coeff_monomial_mul, one_mul]
            · let F : Fin n → k := fun i =>
                if hi : i ∈ s.1 then 0
                else koszulSign T.1 i • coeff (α.1 - finsetInd T.1)
                  (X i * f ⟨insert i T.1, by
                    have hiT : i ∉ T.1 := fun h => hi (Finset.mem_of_mem_erase h)
                    rw [Finset.card_insert_of_notMem hiT, T.2]⟩)
              change _ = ∑ i : Fin n, F i
              rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ k₀)]
              have hFk₀ : F k₀ = 0 := dif_pos hks
              rw [hFk₀, zero_add]
              refine Finset.sum_congr rfl fun i hi_er => ?_
              have hik : i ≠ k₀ := (Finset.mem_erase.mp hi_er).1
              have hiff : i ∈ T.1 ↔ i ∈ s.1 := by simp [T, hik]
              dsimp only [F]
              by_cases his : i ∈ s.1
              · rw [dif_pos (hiff.mpr his), dif_pos his, coeff_zero]
              · rw [dif_neg (mt hiff.mp his), dif_neg his, hcoeff_zsmul]
          rw [hsplit] at hcycT
          have hmul := congrArg (fun c : k => koszulSign T.1 k₀ • c) hcycT
          rw [smul_zero, smul_add, smul_smul, koszulSign_mul_self, one_zsmul,
            Finset.smul_sum] at hmul
          have hsum_eq : ∑ i : Fin n,
              koszulSign T.1 k₀ • (if hi : i ∈ s.1 then (0 : k)
                else koszulSign T.1 i • coeff (α.1 - finsetInd T.1)
                  (X i * f ⟨insert i T.1, by
                    have hiT : i ∉ T.1 := fun h => hi (Finset.mem_of_mem_erase h)
                    rw [Finset.card_insert_of_notMem hiT, T.2]⟩)) =
              -(∑ i : Fin n, if hi : i ∈ s.1 then (0 : k)
                else -(koszulSign T.1 k₀ * koszulSign T.1 i) •
                  coeff (α.1 - finsetInd T.1) (X i * f ⟨insert i T.1, by
                    have hiT : i ∉ T.1 := fun h => hi (Finset.mem_of_mem_erase h)
                    rw [Finset.card_insert_of_notMem hiT, T.2]⟩)) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            split_ifs
            · simp
            · rw [smul_smul, neg_smul, neg_neg]
          rw [hsum_eq] at hmul
          exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hmul)).symm
        ·
          rw [if_neg hle]
          dsimp only [koszulDiff]
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : i ∈ s.1
          · rw [dif_pos hi]
          · rw [dif_neg hi]
            have hnot : ¬ (k₀ ∈ insert i s.1 ∧ finsetInd (insert i s.1) ≤ α.1) := by
              intro ⟨_, hle'⟩
              apply hle
              rw [finsetInd_le_iff] at hle' ⊢
              exact fun j hj => hle' j (Finset.mem_insert_of_mem hj)
            dsimp only [g_α]
            rw [dif_neg hnot, mul_zero, smul_zero]
      ·
        dsimp only [koszulDiff]
        rw [Finset.sum_eq_single k₀]
        · rw [dif_neg hks]
          have hle_iff : finsetInd (insert k₀ s.1) ≤ α.1 ↔ finsetInd s.1 ≤ α.1 := by
            simp only [finsetInd_le_iff, mem_insert]
            constructor
            · intro h j hj; exact h j (Or.inr hj)
            · rintro h j (rfl | hj)
              · exact hk₀_pos
              · exact h j hj
          by_cases hle : finsetInd s.1 ≤ α.1
          · rw [if_pos hle]
            have hcond : k₀ ∈ insert k₀ s.1 ∧ finsetInd (insert k₀ s.1) ≤ α.1 :=
              ⟨Finset.mem_insert_self k₀ s.1, hle_iff.mpr hle⟩
            dsimp only [g_α]
            rw [dif_pos hcond]
            have hU'_eq : (⟨(insert k₀ s.1).erase k₀, by rw [Finset.erase_insert hks, s.2]⟩ :
                { u : Finset (Fin n) // u.card = p + 1 }) = s :=
              Subtype.ext (Finset.erase_insert hks)
            rw [hU'_eq, show α.1.support.min' (hA_ne α.1 α.2) = k₀ from rfl, Finset.erase_insert hks,
              mul_smul_comm, smul_smul, koszulSign_mul_self, one_zsmul, X, monomial_mul, one_mul]
            have hexp : Finsupp.single k₀ 1 + (α.1 - finsetInd (insert k₀ s.1)) =
                α.1 - finsetInd s.1 := by
              ext j
              rw [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_tsub, Finsupp.coe_tsub,
                Pi.sub_apply, Pi.sub_apply, finsetInd_apply, finsetInd_apply]
              by_cases hjk : j = k₀
              · subst hjk; simp [hks]; omega
              · simp [Finsupp.single_eq_of_ne hjk, hjk]
            rw [hexp]
          · rw [if_neg hle]
            have hnot : ¬ (k₀ ∈ insert k₀ s.1 ∧ finsetInd (insert k₀ s.1) ≤ α.1) :=
              fun ⟨_, h⟩ => hle (hle_iff.mp h)
            dsimp only [g_α]
            rw [dif_neg hnot, mul_zero, smul_zero]
        · intro i _ hik
          by_cases hi : i ∈ s.1
          · rw [dif_pos hi]
          · rw [dif_neg hi]
            have hnot : ¬ (k₀ ∈ insert i s.1 ∧ finsetInd (insert i s.1) ≤ α.1) := by
              intro ⟨hmem, _⟩
              rw [mem_insert] at hmem
              rcases hmem with h | h
              · exact hik h.symm
              · exact hks h
            dsimp only [g_α]
            rw [dif_neg hnot, mul_zero, smul_zero]
        · intro h; exact absurd (Finset.mem_univ k₀) h
    let g : KoszulChain n (MvPolynomial (Fin n) k) (p + 2) :=
      fun U => ∑ α ∈ A.attach, g_α α U
    have hg_diff : koszulDiff (fun i => (X i : MvPolynomial (Fin n) k)) (p + 1) g = f := by
      funext s
      have hcomm : koszulDiff (fun i => (X i : MvPolynomial (Fin n) k)) (p + 1) g s =
          ∑ α ∈ A.attach, koszulDiff (fun i => (X i : MvPolynomial (Fin n) k)) (p + 1) (g_α α) s := by
        simp only [koszulDiff, g]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with hi
        · simp
        · rw [Finset.mul_sum, Finset.smul_sum]
      rw [hcomm]
      simp_rw [hg_α_diff]
      rw [Finset.sum_attach A (fun α => if finsetInd s.1 ≤ α then
        monomial (α - finsetInd s.1) (coeff (α - finsetInd s.1) (f s)) else 0)]
      rw [← Finset.sum_filter]
      let S_img := (f s).support.image (· + finsetInd s.1)
      have hsub : S_img ⊆ A.filter (fun α => finsetInd s.1 ≤ α) := by
        intro α hα
        rw [Finset.mem_image] at hα
        obtain ⟨u, hu, rfl⟩ := hα
        rw [Finset.mem_filter]
        refine ⟨?_, le_add_of_nonneg_left (zero_le (a := u))⟩
        simp only [A, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
        exact ⟨s, u, hu, rfl⟩
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_image (fun u₁ _ u₂ _ h => add_right_cancel h)]
        simp_rw [add_tsub_cancel_right]
        exact (f s).as_sum.symm
      · intro α hα hnot
        have hle := (Finset.mem_filter.mp hα).2
        have hnot_supp : α - finsetInd s.1 ∉ (f s).support := by
          intro hmem
          apply hnot
          rw [Finset.mem_image]
          exact ⟨α - finsetInd s.1, hmem, tsub_add_cancel_of_le hle⟩
        rw [MvPolynomial.notMem_support_iff.mp hnot_supp, monomial_zero]
    refine ⟨fun U => Ideal.Quotient.mk ⊥ (g U), ?_, ?_⟩
    · intro U
      by_cases hd0 : d = 0
      · refine Or.inl ⟨by omega, ?_⟩
        rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
        refine Finset.sum_eq_zero fun α _ => ?_
        dsimp only [g_α]
        rw [dif_neg]
        intro ⟨_, hle⟩
        have hdeg_le : (finsetInd U.1).degree ≤ α.1.degree := by
          rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
          exact Finset.sum_le_sum fun i _ => Finsupp.le_def.mp hle i
        rw [finsetInd_degree, U.2, hA_deg α.1 α.2, hd0] at hdeg_le
        omega
      · refine Or.inr ⟨by omega, g U, ?_, rfl⟩
        have hdeg_eq : (t - ↑(p + 2)).toNat = d - 1 := by omega
        rw [hdeg_eq]
        apply IsHomogeneous.sum
        intro α _
        dsimp only [g_α]
        split_ifs with h
        · set k₀ := α.1.support.min' (hA_ne α.1 α.2)
          rw [zsmul_eq_mul]
          have hC : ((koszulSign (U.1.erase k₀) k₀ : MvPolynomial (Fin n) k)).IsHomogeneous 0 := by
            have : ((koszulSign (U.1.erase k₀) k₀ : ℤ) : MvPolynomial (Fin n) k) =
                C ((koszulSign (U.1.erase k₀) k₀ : ℤ) : k) := by simp
            rw [this]; exact isHomogeneous_C _ _
          have hmon : (monomial (α.1 - finsetInd U.1)
              (coeff (α.1 - finsetInd (U.1.erase k₀))
                (f ⟨U.1.erase k₀, by rw [Finset.card_erase_of_mem h.1, U.2]; rfl⟩))).IsHomogeneous (d - 1) := by
            intro v hv
            rw [coeff_monomial] at hv
            split_ifs at hv with hv_eq
            · subst hv_eq
              rw [weight_one_eq_deg]
              have hadd := congrArg Finsupp.degree (tsub_add_cancel_of_le h.2)
              rw [map_add, finsetInd_degree, U.2, hA_deg α.1 α.2] at hadd
              omega
            · exact absurd rfl hv
          simpa using hC.mul hmon
        · exact isHomogeneous_zero _ _ _
    · have hmap := koszulDiff_map (Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial (Fin n) k)))
        (fun i => (X i : MvPolynomial (Fin n) k)) (p + 1) g
      rw [hmap, hg_diff]
      ext s
      exact eBot.injective (by simp [f, heBot_mk])
lemma koszulExactAt_sup_regular {I : Ideal (MvPolynomial (Fin n) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) k))
    {g : MvPolynomial (Fin n) k} {d : ℕ} (hg : g.IsHomogeneous d)
    (hreg : IsSMulRegular (MvPolynomial (Fin n) k ⧸ I) g)
    {p : ℕ} {t : ℤ}
    (hex1 : KoszulExactAt I (p + 1) t)
    (hex0 : KoszulExactAt I p (t - d)) :
    KoszulExactAt (I ⊔ Ideal.span {g}) (p + 1) t := by
  intro z hz hcyc
  let J := I ⊔ Ideal.span {g}
  let π : (MvPolynomial (Fin n) k ⧸ I) →+* (MvPolynomial (Fin n) k ⧸ J) :=
    Ideal.Quotient.factor le_sup_left
  have hπ_mk : ∀ a : MvPolynomial (Fin n) k, π (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J a :=
    fun _ => rfl
  have hlift : ∀ s : { s : Finset (Fin n) // s.card = p + 1 },
      ∃ a : MvPolynomial (Fin n) k,
        IsHomogIn I (t - ↑(p + 1)) (Ideal.Quotient.mk I a) ∧
        Ideal.Quotient.mk J a = z s := by
    intro s
    rcases hz s with ⟨hneg, h0⟩ | ⟨hnn, a, ha, hmk⟩
    · exact ⟨0, Or.inl ⟨hneg, map_zero _⟩, by rw [map_zero, h0]⟩
    · exact ⟨a, Or.inr ⟨hnn, a, ha, rfl⟩, hmk⟩
  choose rep_z hrep_hom hrep_mk using hlift
  let z_lift : KoszulChain n (MvPolynomial (Fin n) k ⧸ I) (p + 1) :=
    fun s => Ideal.Quotient.mk I (rep_z s)
  have hz_lift_hom : IsHomogChain I (p + 1) t z_lift := hrep_hom
  have hz_lift_π : ∀ s, π (z_lift s) = z s := fun s => hrep_mk s
  let dz := koszulDiff (fun i => Ideal.Quotient.mk I (X i)) p z_lift
  have hdz_hom : IsHomogChain I p t dz := isHomogChain_koszulDiff hz_lift_hom
  have hdz_zero_J : ∀ T, π (dz T) = 0 := by
    intro T
    have h1 := koszulDiff_map π (fun i => Ideal.Quotient.mk I (X i)) p z_lift
    have h2 : (fun s => π (z_lift s)) = z := funext hz_lift_π
    have h3 : (fun i => π (Ideal.Quotient.mk I (X i))) = (fun i => Ideal.Quotient.mk J (X i)) := rfl
    rw [h2, h3] at h1
    have hT := congrFun h1 T
    change koszulDiff (fun i => Ideal.Quotient.mk J (X i)) p z T = π (dz T) at hT
    rw [← hT, hcyc]; rfl
  have hw_ex : ∀ T : { s : Finset (Fin n) // s.card = p },
      ∃ wT : MvPolynomial (Fin n) k ⧸ I,
        IsHomogIn I ((t - d) - p) wT ∧ Ideal.Quotient.mk I g * wT = dz T := by
    intro T
    rcases hdz_hom T with ⟨hneg, h0⟩ | ⟨hnn, a, ha, hmk⟩
    · exact ⟨0, isHomogIn_zero _ _, by rw [mul_zero, h0]⟩
    · have haJ : a ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        have h1 := hdz_zero_J T
        rw [← hmk, hπ_mk] at h1
        exact h1
      rcases exists_homog_of_mem_sup_span hI hg ha haJ with ⟨hlt, haI⟩ | ⟨hle, q, hq, hsub⟩
      · refine ⟨0, isHomogIn_zero _ _, ?_⟩
        rw [mul_zero, ← hmk, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
        exact haI
      · refine ⟨Ideal.Quotient.mk I q, ?_, ?_⟩
        · refine Or.inr ⟨by omega, q, ?_, rfl⟩
          have hdeg : ((t - (d : ℤ)) - (p : ℤ)).toNat = (t - (p : ℤ)).toNat - d := by omega
          rw [hdeg]; exact hq
        · rw [← hmk, ← map_mul, eq_comm, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
          exact hsub
  choose w hw_hom hw_eq using hw_ex
  have hw_cyc : isKoszulCycle (fun i => Ideal.Quotient.mk I (X i)) p w := by
    cases p with
    | zero => trivial
    | succ p' =>
      ext U
      have hg_mul : g • koszulDiff (fun i => Ideal.Quotient.mk I (X i)) p' w U = g • (0 : MvPolynomial (Fin n) k ⧸ I) := by
        rw [smul_zero]
        change Ideal.Quotient.mk I g * koszulDiff (fun i => Ideal.Quotient.mk I (X i)) p' w U = 0
        have hsm := congrFun (koszulDiff_smul (fun i => Ideal.Quotient.mk I (X i)) p'
          (Ideal.Quotient.mk I g) w) U
        rw [← hsm]
        have hfun : (fun s => Ideal.Quotient.mk I g * w s) = dz := funext hw_eq
        rw [hfun]
        have h0 := koszulDiff_comp_koszulDiff (fun i => Ideal.Quotient.mk I (X i)) p' z_lift
        exact congrFun h0 U
      exact hreg hg_mul
  obtain ⟨u, hu_hom, hu_diff⟩ := hex0 w hw_hom hw_cyc
  let z' : KoszulChain n (MvPolynomial (Fin n) k ⧸ I) (p + 1) :=
    fun s => z_lift s - Ideal.Quotient.mk I g * u s
  have hz'_hom : IsHomogChain I (p + 1) t z' := by
    intro s
    apply isHomogIn_sub (hz_lift_hom s)
    have h1 := isHomogIn_mul_homog hg (hu_hom s)
    have hdeg : (t - (d : ℤ)) - ↑(p + 1) + (d : ℕ) = t - ↑(p + 1) := by ring
    rwa [hdeg] at h1
  have hz'_cyc : isKoszulCycle (fun i => Ideal.Quotient.mk I (X i)) (p + 1) z' := by
    change koszulDiff (fun i => Ideal.Quotient.mk I (X i)) p
      (z_lift - fun s => Ideal.Quotient.mk I g * u s) = 0
    rw [koszulDiff_sub, koszulDiff_smul, hu_diff]
    ext T
    simp only [Pi.sub_apply, Pi.zero_apply, dz, hw_eq T, sub_self]
  obtain ⟨v, hv_hom, hv_diff⟩ := hex1 z' hz'_hom hz'_cyc
  refine ⟨fun U => π (v U), ?_, ?_⟩
  · intro U
    rcases hv_hom U with ⟨hneg, h0⟩ | ⟨hnn, a, ha, hmk⟩
    · exact Or.inl ⟨hneg, by dsimp only; rw [h0, map_zero]⟩
    · exact Or.inr ⟨hnn, a, ha, by dsimp only; rw [← hmk, hπ_mk]⟩
  · have hmap := koszulDiff_map π (fun i => Ideal.Quotient.mk I (X i)) (p + 1) v
    change koszulDiff (fun i => Ideal.Quotient.mk J (X i)) (p + 1) (fun U => π (v U)) =
      fun s => π (koszulDiff (fun i => Ideal.Quotient.mk I (X i)) (p + 1) v s) at hmap
    rw [hmap, hv_diff]
    ext s
    simp only [z', map_sub, map_mul, hz_lift_π s]
    have hg0 : π (Ideal.Quotient.mk I g) = 0 := by
      rw [hπ_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
    rw [hg0, zero_mul, sub_zero]
theorem koszulExactAt_of_regular :
    ∀ {c : ℕ} {d : Fin c → ℕ} {f : Fin c → MvPolynomial (Fin n) k},
      (∀ i, (f i).IsHomogeneous (d i)) →
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (List.ofFn f) →
      (∀ p > c, ∀ t : ℤ, KoszulExactAt (Ideal.ofList (List.ofFn f)) p t) ∧
      (∀ t : ℤ, t ≠ ∑ i : Fin c, (d i : ℤ) → KoszulExactAt (Ideal.ofList (List.ofFn f)) c t)
  | 0, d, f, _, _ => by
    have hbot : Ideal.ofList (List.ofFn f) = ⊥ := by simp [Ideal.ofList]
    rw [hbot]
    refine ⟨fun p hp t => ?_, fun t ht => ?_⟩
    · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      exact koszulExactAt_bot_succ p' t
    · simp only [Finset.univ_eq_empty, Finset.sum_empty] at ht
      exact koszulExactAt_bot_zero ht
  | c + 1, d, f, hfd, hf => by
    let f' : Fin c → MvPolynomial (Fin n) k := f ∘ Fin.castSucc
    let d' : Fin c → ℕ := d ∘ Fin.castSucc
    have hsplit : List.ofFn f = List.ofFn f' ++ [f (Fin.last c)] := by
      rw [List.ofFn_succ', List.concat_eq_append]; rfl
    have hreg_app := (RingTheory.Sequence.isWeaklyRegular_append_iff _ (List.ofFn f')
      [f (Fin.last c)]).mp (hsplit ▸ hf.toIsWeaklyRegular)
    have hI'_hom : (Ideal.ofList (List.ofFn f')).IsHomogeneous (homogeneousSubmodule (Fin n) k) :=
      isHomogeneous_ideal_ofList fun r hr => by
        rw [List.mem_ofFn] at hr; obtain ⟨i, rfl⟩ := hr; exact ⟨d' i, hfd (Fin.castSucc i)⟩
    have hf'_reg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (List.ofFn f') := by
      refine ⟨hreg_app.1, ?_⟩
      intro htop
      apply hf.top_ne_smul
      have hle : Ideal.ofList (List.ofFn f') ≤ Ideal.ofList (List.ofFn f) := by
        rw [hsplit]
        exact Ideal.span_mono (fun x hx => List.mem_append_left _ hx)
      exact (top_unique (htop.le.trans (Submodule.smul_mono_left hle))).symm
    have hlast_reg : IsSMulRegular (MvPolynomial (Fin n) k ⧸ Ideal.ofList (List.ofFn f'))
        (f (Fin.last c)) := by
      have h1 := (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mp hreg_app.2
      have hItop : (Ideal.ofList (List.ofFn f') • ⊤ :
          Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) =
          Ideal.ofList (List.ofFn f') := by simp
      have e : (MvPolynomial (Fin n) k ⧸ (Ideal.ofList (List.ofFn f') • ⊤ :
          Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k))) ≃ₗ[MvPolynomial (Fin n) k]
          (MvPolynomial (Fin n) k ⧸ Ideal.ofList (List.ofFn f')) :=
        Submodule.quotEquivOfEq _ _ hItop
      exact (e.isSMulRegular_congr _).mp h1
    have hI_eq : Ideal.ofList (List.ofFn f) =
        Ideal.ofList (List.ofFn f') ⊔ Ideal.span {f (Fin.last c)} := by
      rw [hsplit, Ideal.ofList_append, Ideal.ofList_singleton]
    have ih := koszulExactAt_of_regular (f := f') (d := d') (fun i => hfd i.castSucc) hf'_reg
    rw [hI_eq]
    refine ⟨fun p hp t => ?_, fun t ht => ?_⟩
    · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      exact koszulExactAt_sup_regular hI'_hom (hfd (Fin.last c)) hlast_reg
        (ih.1 (p' + 1) (by omega) t) (ih.1 p' (by omega) (t - d (Fin.last c)))
    · have hsum_split : ∑ i : Fin (c + 1), (d i : ℤ) =
          (∑ i : Fin c, (d' i : ℤ)) + (d (Fin.last c) : ℤ) := Fin.sum_univ_castSucc _
      exact koszulExactAt_sup_regular hI'_hom (hfd (Fin.last c)) hlast_reg
        (ih.1 (c + 1) (by omega) t) (ih.2 (t - d (Fin.last c)) (by omega))
lemma socle_eq_zero_of_koszulExactAt {I : Ideal (MvPolynomial (Fin n) k)} {e : ℕ}
    (hex : KoszulExactAt I n ((e : ℤ) + (n : ℤ)))
    {r : MvPolynomial (Fin n) k ⧸ I} (hr : IsHomogIn I e r)
    (hann : ∀ i : Fin n, Ideal.Quotient.mk I (X i) * r = 0) : r = 0 := by
  let z : KoszulChain n (MvPolynomial (Fin n) k ⧸ I) n := fun _ => r
  have hz_hom : IsHomogChain I n ((e : ℤ) + (n : ℤ)) z := by
    intro s; simpa using hr
  have hz_cyc : isKoszulCycle (fun i => Ideal.Quotient.mk I (X i)) n z := by
    cases n with
    | zero => trivial
    | succ m =>
      ext T
      simp only [koszulDiff, Pi.zero_apply, z]
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs
      · rfl
      · rw [hann i, smul_zero]
  obtain ⟨v, _, hv⟩ := hex z hz_hom hz_cyc
  have hv0 : v = 0 := by
    ext U
    have hle : U.1.card ≤ n := by
      simpa using Finset.card_le_univ U.1
    omega
  have := congrFun hv ⟨Finset.univ, Finset.card_fin n⟩
  rw [hv0, koszulDiff_zero, Pi.zero_apply] at this
  exact this.symm
lemma exists_not_mem_biUnion_subspaces [Infinite k] {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} (s : Finset ι) (W : ι → Submodule k V) (hW : ∀ i ∈ s, W i ≠ ⊤) :
    ∃ v : V, ∀ i ∈ s, v ∉ W i := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨v₁, hv₁⟩ := ih (fun i hi => hW i (Finset.mem_insert_of_mem hi))
    by_cases hv₁a : v₁ ∉ W a
    · refine ⟨v₁, fun i hi => ?_⟩
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | his
      · exact hv₁a
      · exact hv₁ i his
    · push Not at hv₁a
      have hv₂_ex : ∃ v₂ : V, v₂ ∉ W a := by
        by_contra hall; push Not at hall
        exact hW a (Finset.mem_insert_self a s) (eq_top_iff.mpr fun v _ => hall v)
      obtain ⟨v₂, hv₂⟩ := hv₂_ex
      have hbad_sub : ∀ i ∈ s, Set.Subsingleton { t : k | v₁ + t • v₂ ∈ W i } := by
        intro i hi t₁ ht₁ t₂ ht₂
        by_contra hne
        have hdiff : (t₁ - t₂) • v₂ ∈ W i := by
          have := Submodule.sub_mem (W i) ht₁ ht₂
          simpa [sub_smul] using this
        have hv₂_in : v₂ ∈ W i := by
          have := Submodule.smul_mem (W i) (t₁ - t₂)⁻¹ hdiff
          rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul] at this
        have hv₁_in : v₁ ∈ W i := by
          have := Submodule.sub_mem (W i) ht₁ (Submodule.smul_mem (W i) t₁ hv₂_in)
          simpa using this
        exact hv₁ i hi hv₁_in
      have hfin : (({0} : Set k) ∪ ⋃ i ∈ s, { t : k | v₁ + t • v₂ ∈ W i }).Finite :=
        (Set.finite_singleton 0).union (s.finite_toSet.biUnion fun i hi => (hbad_sub i hi).finite)
      obtain ⟨t, ht⟩ := (Set.infinite_univ.sdiff hfin).nonempty
      have ht0 : t ≠ 0 := by
        intro h0
        apply ht.2
        exact Or.inl (by simp [h0])
      refine ⟨v₁ + t • v₂, fun i hi => ?_⟩
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | his
      · intro hmem
        have : t • v₂ ∈ W i := by
          have := Submodule.sub_mem (W i) hmem hv₁a
          simpa using this
        have hv₂_in : v₂ ∈ W i := by
          have := Submodule.smul_mem (W i) t⁻¹ this
          rwa [smul_smul, inv_mul_cancel₀ ht0, one_smul] at this
        exact hv₂ hv₂_in
      · intro hmem
        exact ht.2 (Or.inr (Set.mem_biUnion his hmem))
theorem exists_regular_linForm_of_lt [Infinite k] {c : ℕ} (hc : c < n)
    {d : Fin c → ℕ} {f : Fin c → MvPolynomial (Fin n) k}
    (hfd : ∀ i, (f i).IsHomogeneous (d i))
    (hf : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (List.ofFn f)) :
    ∃ ℓ : MvPolynomial (Fin n) k, ℓ.IsHomogeneous 1 ∧
      IsSMulRegular (MvPolynomial (Fin n) k ⧸ Ideal.ofList (List.ofFn f)) ℓ := by
  classical
  let I := Ideal.ofList (List.ofFn f)
  have hI_hom : I.IsHomogeneous (homogeneousSubmodule (Fin n) k) :=
    isHomogeneous_ideal_ofList fun r hr => by
      rw [List.mem_ofFn] at hr; obtain ⟨i, rfl⟩ := hr; exact ⟨d i, hfd i⟩
  have hfin := associatedPrimes.finite (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I)
  let sAss : Finset (Ideal (MvPolynomial (Fin n) k)) := hfin.toFinset
  have hmem_sAss : ∀ P, P ∈ sAss ↔ P ∈ associatedPrimes (MvPolynomial (Fin n) k)
      (MvPolynomial (Fin n) k ⧸ I) := fun P => hfin.mem_toFinset
  have hproper : ∀ P ∈ sAss,
      (Submodule.restrictScalars k P).comap (homogPiece n k 1).subtype ≠ ⊤ := by
    intro P hP htop
    have hAss : IsAssociatedPrime P (MvPolynomial (Fin n) k ⧸ I) := (hmem_sAss P).mp hP
    rw [isAssociatedPrime_iff] at hAss
    obtain ⟨hP_prime, x, hx_eq⟩ := hAss
    have hx_ne : x ≠ 0 := by
      intro hx0
      have : P = ⊤ := by rw [hx_eq, hx0]; simp
      exact hP_prime.ne_top this
    have hX_ann : ∀ i : Fin n, Ideal.Quotient.mk I (X i) * x = 0 := by
      intro i
      have hXi_P : (X i : MvPolynomial (Fin n) k) ∈ P := by
        have hmem : (⟨X i, (mem_homogeneousSubmodule 1 (X i)).mpr (isHomogeneous_X k i)⟩ :
            homogPiece n k 1) ∈ (Submodule.restrictScalars k P).comap (homogPiece n k 1).subtype := by
          rw [htop]; exact Submodule.mem_top
        exact hmem
      rw [hx_eq, Submodule.mem_colon_singleton] at hXi_P
      change (X i : MvPolynomial (Fin n) k) • x = 0 at hXi_P
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact hXi_P
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hp_not : p ∉ I := fun h => hx_ne (Ideal.Quotient.eq_zero_iff_mem.mpr h)
    have hex_e : ∃ e : ℕ, homogeneousComponent e p ∉ I := by
      by_contra hall; push Not at hall
      exact hp_not ((MvPolynomial.mem_iff_homogeneousComponent_mem hI_hom p).mpr hall)
    obtain ⟨e, he⟩ := hex_e
    have hcomp_ann : ∀ i : Fin n,
        Ideal.Quotient.mk I (X i) * Ideal.Quotient.mk I (homogeneousComponent e p) = 0 := by
      intro i
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have hXp : X i * p ∈ I := by
        have h1 := hX_ann i
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h1
        exact h1
      have hcomp := MvPolynomial.homogeneousComponent_mem_of_mem hI_hom hXp (e + 1)
      rw [homogeneousComponent_mul_of_isHomogeneous (isHomogeneous_X k i),
        if_pos (Nat.le_add_left 1 e), Nat.add_sub_cancel] at hcomp
      exact hcomp
    have hkosz := (koszulExactAt_of_regular hfd hf).1 n hc ((e : ℤ) + (n : ℤ))
    have hzero := socle_eq_zero_of_koszulExactAt hkosz
      (Or.inr ⟨Nat.cast_nonneg e, homogeneousComponent e p,
        by simpa using homogeneousComponent_isHomogeneous e p, rfl⟩) hcomp_ann
    exact he (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  obtain ⟨ℓ, hℓ_not⟩ := exists_not_mem_biUnion_subspaces sAss
    (fun P => (Submodule.restrictScalars k P).comap (homogPiece n k 1).subtype) hproper
  refine ⟨ℓ.1, (mem_homogeneousSubmodule 1 ℓ.1).mp ℓ.2, ?_⟩
  intro x y hxy
  dsimp only at hxy
  rw [← sub_eq_zero]
  by_contra hne
  have hann : ℓ.1 • (x - y) = 0 := by rw [smul_sub, hxy, sub_self]
  have hmem : ℓ.1 ∈ ⋃ P ∈ associatedPrimes (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I),
      (P : Set (MvPolynomial (Fin n) k)) := by
    rw [biUnion_associatedPrimes_eq_zero_divisors]
    exact ⟨x - y, hne, hann⟩
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨P, hP, hℓP⟩ := hmem
  exact hℓ_not P ((hmem_sAss P).mpr hP) hℓP
theorem exists_regular_in_subspace [Infinite k] {c e : ℕ}
    {f' : Fin c → MvPolynomial (Fin n) k}
    (V : Submodule k (homogPiece n k e))
    {g : MvPolynomial (Fin n) k}
    (hg_mem : g ∈ Ideal.ofList (List.ofFn f') ⊔ Ideal.span (Subtype.val '' (V : Set (homogPiece n k e))))
    (hg_reg : IsSMulRegular (MvPolynomial (Fin n) k ⧸ Ideal.ofList (List.ofFn f')) g) :
    ∃ v ∈ V, IsSMulRegular (MvPolynomial (Fin n) k ⧸ Ideal.ofList (List.ofFn f')) v.1 := by
  classical
  let I' := Ideal.ofList (List.ofFn f')
  have hfin := associatedPrimes.finite (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I')
  let sAss := hfin.toFinset
  have hmem_sAss : ∀ P, P ∈ sAss ↔ P ∈ associatedPrimes (MvPolynomial (Fin n) k)
      (MvPolynomial (Fin n) k ⧸ I') := fun P => hfin.mem_toFinset
  let inclV : V →ₗ[k] MvPolynomial (Fin n) k := (homogPiece n k e).subtype.comp V.subtype
  have hproper : ∀ P ∈ sAss,
      (Submodule.restrictScalars k P).comap inclV ≠ ⊤ := by
    intro P hP htop
    have hAss : IsAssociatedPrime P (MvPolynomial (Fin n) k ⧸ I') := (hmem_sAss P).mp hP
    have hI'_le : I' ≤ P := by
      have hann := hAss.annihilator_le
      intro a ha
      apply hann
      rw [Submodule.mem_annihilator]
      intro y _
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      change Ideal.Quotient.mk I' (a * r) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (I'.mul_mem_right r ha)
    have hV_le : Ideal.span (Subtype.val '' (V : Set (homogPiece n k e))) ≤ P := by
      rw [Ideal.span_le]
      rintro _ ⟨v, hv, rfl⟩
      have hmem : (⟨v, hv⟩ : V) ∈ (Submodule.restrictScalars k P).comap inclV := by
        rw [htop]; exact Submodule.mem_top
      exact hmem
    have hgP : g ∈ P := (sup_le hI'_le hV_le) hg_mem
    rw [isAssociatedPrime_iff] at hAss
    obtain ⟨hP_prime, x, hx_eq⟩ := hAss
    have hx_ne : x ≠ 0 := by
      intro hx0; apply hP_prime.ne_top; rw [hx_eq, hx0]; simp
    rw [hx_eq, Submodule.mem_colon_singleton] at hgP
    have hgx0 : g • x = g • (0 : MvPolynomial (Fin n) k ⧸ I') := by rw [smul_zero]; exact hgP
    exact hx_ne (hg_reg hgx0)
  obtain ⟨⟨v, hv⟩, hv_not⟩ := exists_not_mem_biUnion_subspaces (V := V) sAss
    (fun P => (Submodule.restrictScalars k P).comap inclV) hproper
  refine ⟨v, hv, ?_⟩
  intro x y hxy
  dsimp only at hxy
  rw [← sub_eq_zero]
  by_contra hne
  have hann : v.1 • (x - y) = 0 := by rw [smul_sub, hxy, sub_self]
  have hmem : v.1 ∈ ⋃ P ∈ associatedPrimes (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k ⧸ I'),
      (P : Set (MvPolynomial (Fin n) k)) := by
    rw [biUnion_associatedPrimes_eq_zero_divisors]
    exact ⟨x - y, hne, hann⟩
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨P, hP, hvP⟩ := hmem
  exact hv_not P ((hmem_sAss P).mpr hP) hvP
noncomputable def boxSlice {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) (e : ℕ) :
    Finset (Fin n →₀ ℕ) :=
  (monOfDeg n e).filter (fun u => ∀ j : Fin c, u (Fin.castLE hc j) < d j)
lemma quotientHF_sup_regular {I : Ideal (MvPolynomial (Fin n) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) k))
    {g : MvPolynomial (Fin n) k} {m : ℕ} (hg : g.IsHomogeneous m)
    (hreg : IsSMulRegular (MvPolynomial (Fin n) k ⧸ I) g) (e : ℕ) :
    quotientHF (I ⊔ Ideal.span {g}) e + (if m ≤ e then quotientHF I (e - m) else 0) =
      quotientHF I e := by
  let J := I ⊔ Ideal.span {g}
  let πe : (homogPiece n k e ⧸ idealSub I e) →ₗ[k] (homogPiece n k e ⧸ idealSub J e) :=
    Submodule.mapQ (idealSub I e) (idealSub J e) LinearMap.id (by
      intro x hx; rw [Submodule.mem_comap, LinearMap.id_apply, mem_idealSub]
      exact Ideal.mem_sup_left ((mem_idealSub x).mp hx))
  have hπe_surj : Function.Surjective πe := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker πe
  rw [LinearMap.range_eq_top.mpr hπe_surj, finrank_top] at hrn
  suffices hker : Module.finrank k (LinearMap.ker πe) =
      if m ≤ e then quotientHF I (e - m) else 0 by
    change quotientHF J e + Module.finrank k (LinearMap.ker πe) = quotientHF I e at hrn
    dsimp only [J] at hrn
    omega
  by_cases hme : m ≤ e
  · rw [if_pos hme]
    let mulg : homogPiece n k (e - m) →ₗ[k] homogPiece n k e := {
      toFun := fun x => ⟨g * x.1, by
        rw [mem_homogeneousSubmodule]
        have h := hg.mul ((mem_homogeneousSubmodule _ _).mp x.2)
        rwa [Nat.add_sub_of_le hme] at h⟩
      map_add' := fun x y => Subtype.ext (mul_add g x.1 y.1)
      map_smul' := fun a x => Subtype.ext (by simp [Algebra.mul_smul_comm])
    }
    let μ : (homogPiece n k (e - m) ⧸ idealSub I (e - m)) →ₗ[k]
        (homogPiece n k e ⧸ idealSub I e) :=
      Submodule.mapQ (idealSub I (e - m)) (idealSub I e) mulg (by
        intro x hx; rw [Submodule.mem_comap, mem_idealSub]
        exact I.mul_mem_left g ((mem_idealSub x).mp hx))
    have hμ_inj : Function.Injective μ := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      change Submodule.Quotient.mk (mulg x) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero, mem_idealSub] at hy
      rw [Submodule.Quotient.mk_eq_zero, mem_idealSub]
      exact exists_homog_mul_eq_of_isHomogeneous hI hg hreg
        ((mem_homogeneousSubmodule _ _).mp x.2) hy
    have hrange_eq : LinearMap.range μ = LinearMap.ker πe := by
      ext y
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      simp only [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨w, hw⟩
        obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ w
        rw [← hw]
        change Submodule.Quotient.mk (mulg q) = (0 : homogPiece n k e ⧸ idealSub J e)
        rw [Submodule.Quotient.mk_eq_zero, mem_idealSub]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨q.1, rfl⟩)
      · intro hxJ
        change Submodule.Quotient.mk x = (0 : homogPiece n k e ⧸ idealSub J e) at hxJ
        rw [Submodule.Quotient.mk_eq_zero, mem_idealSub] at hxJ
        rcases exists_homog_of_mem_sup_span hI hg ((mem_homogeneousSubmodule _ _).mp x.2) hxJ with
          ⟨hlt, _⟩ | ⟨_, q, hq, hsub⟩
        · omega
        · refine ⟨Submodule.Quotient.mk ⟨q, (mem_homogeneousSubmodule _ _).mpr hq⟩, ?_⟩
          change Submodule.Quotient.mk (mulg ⟨q, _⟩) = Submodule.Quotient.mk x
          rw [Submodule.Quotient.eq, mem_idealSub]
          change g * q - x.1 ∈ I
          have : g * q - x.1 = -(x.1 - g * q) := by ring
          rw [this]; exact I.neg_mem hsub
    rw [← hrange_eq]
    exact (LinearEquiv.finrank_eq (LinearEquiv.ofInjective μ hμ_inj)).symm
  · rw [if_neg hme]
    have hker_bot : LinearMap.ker πe = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [LinearMap.mem_ker] at hy
      change Submodule.Quotient.mk x = (0 : homogPiece n k e ⧸ idealSub J e) at hy
      rw [Submodule.Quotient.mk_eq_zero, mem_idealSub] at hy
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, mem_idealSub]
      rcases exists_homog_of_mem_sup_span hI hg ((mem_homogeneousSubmodule _ _).mp x.2) hy with
        ⟨_, hxI⟩ | ⟨hle, _⟩
      · exact hxI
      · omega
    rw [hker_bot, finrank_bot]
theorem quotientHF_regular_eq_card_boxSlice :
    ∀ {c : ℕ} (hc : c ≤ n) {d : Fin c → ℕ} {f : Fin c → MvPolynomial (Fin n) k},
      (∀ i, (f i).IsHomogeneous (d i)) →
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (List.ofFn f) →
      ∀ e : ℕ, quotientHF (Ideal.ofList (List.ofFn f)) e = (boxSlice hc d e).card
  | 0, hc, d, f, _, _, e => by
    have hbot : Ideal.ofList (List.ofFn f) = ⊥ := by simp [Ideal.ofList]
    rw [hbot]
    have hbox : boxSlice hc d e = monOfDeg n e := by
      ext u; simp [boxSlice]
    rw [hbox, quotientHF]
    have hisub : idealSub (⊥ : Ideal (MvPolynomial (Fin n) k)) e = ⊥ := by
      ext x; simp [idealSub]
    rw [LinearEquiv.finrank_eq (Submodule.quotEquivOfEqBot _ hisub), finrank_homogPiece]
  | c + 1, hc, d, f, hfd, hf, e => by
    let f' : Fin c → MvPolynomial (Fin n) k := f ∘ Fin.castSucc
    let d' : Fin c → ℕ := d ∘ Fin.castSucc
    have hc' : c ≤ n := by omega
    have hsplit : List.ofFn f = List.ofFn f' ++ [f (Fin.last c)] := by
      rw [List.ofFn_succ', List.concat_eq_append]; rfl
    have hreg_app := (RingTheory.Sequence.isWeaklyRegular_append_iff _ (List.ofFn f')
      [f (Fin.last c)]).mp (hsplit ▸ hf.toIsWeaklyRegular)
    have hI'_hom : (Ideal.ofList (List.ofFn f')).IsHomogeneous (homogeneousSubmodule (Fin n) k) :=
      isHomogeneous_ideal_ofList fun r hr => by
        rw [List.mem_ofFn] at hr; obtain ⟨i, rfl⟩ := hr; exact ⟨d' i, hfd (Fin.castSucc i)⟩
    have hf'_reg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (List.ofFn f') := by
      refine ⟨hreg_app.1, ?_⟩
      intro htop; apply hf.top_ne_smul
      have hle : Ideal.ofList (List.ofFn f') ≤ Ideal.ofList (List.ofFn f) := by
        rw [hsplit]
        exact Ideal.span_mono (fun x hx => List.mem_append_left _ hx)
      exact (top_unique (htop.le.trans (Submodule.smul_mono_left hle))).symm
    have hlast_reg : IsSMulRegular (MvPolynomial (Fin n) k ⧸ Ideal.ofList (List.ofFn f'))
        (f (Fin.last c)) := by
      have h1 := (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mp hreg_app.2
      have hItop : (Ideal.ofList (List.ofFn f') • ⊤ :
          Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) =
          Ideal.ofList (List.ofFn f') := by simp
      exact ((Submodule.quotEquivOfEq _ _ hItop).isSMulRegular_congr _).mp h1
    have hI_eq : Ideal.ofList (List.ofFn f) =
        Ideal.ofList (List.ofFn f') ⊔ Ideal.span {f (Fin.last c)} := by
      rw [hsplit, Ideal.ofList_append, Ideal.ofList_singleton]
    have hrec := quotientHF_sup_regular hI'_hom (hfd (Fin.last c)) hlast_reg e
    rw [← hI_eq] at hrec
    have ih_e := quotientHF_regular_eq_card_boxSlice hc' (fun i => hfd i.castSucc) hf'_reg e
    have ih_sub := quotientHF_regular_eq_card_boxSlice hc' (fun i => hfd i.castSucc) hf'_reg
      (e - d (Fin.last c))
    have hbox_rec : (boxSlice hc d e).card +
        (if d (Fin.last c) ≤ e then (boxSlice hc' d' (e - d (Fin.last c))).card else 0) =
        (boxSlice hc' d' e).card := by
      set m := d (Fin.last c)
      let j₀ : Fin n := Fin.castLE hc (Fin.last c)
      have hsub_box : boxSlice hc d e ⊆ boxSlice hc' d' e := by
        intro u hu
        simp only [boxSlice, mem_filter] at hu ⊢
        exact ⟨hu.1, fun j => hu.2 j.castSucc⟩
      have hsdiff_eq : boxSlice hc' d' e \ boxSlice hc d e =
          (boxSlice hc' d' e).filter (fun u => m ≤ u j₀) := by
        ext u
        simp only [mem_sdiff, boxSlice, mem_filter, not_and, not_forall, not_lt]
        constructor
        · rintro ⟨⟨hu1, hu2⟩, hnot⟩
          refine ⟨⟨hu1, hu2⟩, ?_⟩
          obtain ⟨j, hj⟩ := hnot hu1
          rcases Fin.lastCases (motive := fun j => d j ≤ u (Fin.castLE hc j) → m ≤ u j₀)
              (fun h => h) (fun j' h => absurd (hu2 j') (not_lt.mpr h)) j hj with h
          exact h
        · rintro ⟨⟨hu1, hu2⟩, hge⟩
          exact ⟨⟨hu1, hu2⟩, fun _ => ⟨Fin.last c, hge⟩⟩
      have hcard_split : (boxSlice hc d e).card +
          ((boxSlice hc' d' e).filter (fun u => m ≤ u j₀)).card = (boxSlice hc' d' e).card := by
        rw [← hsdiff_eq, add_comm, Finset.card_sdiff_add_card_eq_card hsub_box]
      rw [← hcard_split]
      congr 1
      by_cases hme : m ≤ e
      · rw [if_pos hme]
        symm
        refine Finset.card_bij (fun u _ => u - Finsupp.single j₀ m) ?_ ?_ ?_
        · intro u hu
          simp only [boxSlice, mem_filter, mem_monOfDeg] at hu ⊢
          refine ⟨?_, fun j => ?_⟩
          · have hadd : (u - Finsupp.single j₀ m) + Finsupp.single j₀ m = u := by
              ext r; by_cases hr : r = j₀
              · subst hr; simp; omega
              · simp [Finsupp.single_eq_of_ne hr]
            have hdeg := congrArg Finsupp.degree hadd
            rw [map_add, Finsupp.degree_single, hu.1.1] at hdeg; omega
          · have hne : Fin.castLE hc' j ≠ j₀ := by
              intro heq
              have := congrArg Fin.val heq
              simp [j₀] at this; omega
            have := hu.1.2 j
            simpa [Finsupp.single_eq_of_ne hne] using this
        · intro u₁ hu₁ u₂ hu₂ heq
          have h1 : u₁ = (u₁ - Finsupp.single j₀ m) + Finsupp.single j₀ m := by
            ext r; by_cases hr : r = j₀
            · subst hr; have := (mem_filter.mp hu₁).2; simp; omega
            · simp [Finsupp.single_eq_of_ne hr]
          have h2 : u₂ = (u₂ - Finsupp.single j₀ m) + Finsupp.single j₀ m := by
            ext r; by_cases hr : r = j₀
            · subst hr; have := (mem_filter.mp hu₂).2; simp; omega
            · simp [Finsupp.single_eq_of_ne hr]
          rw [h1, h2, heq]
        · intro v hv
          simp only [boxSlice, mem_filter, mem_monOfDeg] at hv
          refine ⟨v + Finsupp.single j₀ m, ?_, by simp⟩
          simp only [boxSlice, mem_filter, mem_monOfDeg]
          refine ⟨⟨by rw [map_add, Finsupp.degree_single, hv.1]; omega, fun j => ?_⟩, ?_⟩
          · have hne : Fin.castLE hc' j ≠ j₀ := by
              intro heq; have := congrArg Fin.val heq; simp [j₀] at this; omega
            simpa [Finsupp.single_eq_of_ne hne] using hv.2 j
          · simp
      · rw [if_neg hme, eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro u hu hge
        have hdeg : u.degree = e := mem_monOfDeg.mp (mem_filter.mp hu).1
        have hle : u j₀ ≤ ∑ i : Fin n, u i :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j₀)
        rw [← Finsupp.degree_eq_sum, hdeg] at hle; omega
    have ih_e' : quotientHF (Ideal.ofList (List.ofFn f')) e = (boxSlice hc' d' e).card := ih_e
    have ih_sub' : quotientHF (Ideal.ofList (List.ofFn f')) (e - d (Fin.last c)) =
        (boxSlice hc' d' (e - d (Fin.last c))).card := ih_sub
    split_ifs at hrec hbox_rec <;> omega
theorem ci_linkage_quotientHF {d : Fin n → ℕ} {g : Fin n → MvPolynomial (Fin n) k}
    (hgd : ∀ i, (g i).IsHomogeneous (d i))
    (hg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (List.ofFn g))
    {I : Ideal (MvPolynomial (Fin n) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) k))
    (hGI : Ideal.ofList (List.ofFn g) ≤ I) :
    let G := Ideal.ofList (List.ofFn g)
    let J := G.colon I
    let s := ∑ i : Fin n, (d i - 1)
    J.IsHomogeneous (homogeneousSubmodule (Fin n) k) ∧ G ≤ J ∧
      ∀ e ≤ s, quotientHF J e + quotientHF I (s - e) = quotientHF G (s - e) := by
  intro G J s
  have hd_pos : ∀ i : Fin n, 1 ≤ d i := regular_homog_deg_pos hgd hg
  have hG_hom : G.IsHomogeneous (homogeneousSubmodule (Fin n) k) :=
    isHomogeneous_ideal_ofList fun r hr => by
      rw [List.mem_ofFn] at hr; obtain ⟨i, rfl⟩ := hr; exact ⟨d i, hgd i⟩
  have hJ_hom : J.IsHomogeneous (homogeneousSubmodule (Fin n) k) := by
    intro e p hp
    change ((MvPolynomial.decomposition.decompose' p e : _) : MvPolynomial (Fin n) k) ∈ J
    rw [MvPolynomial.decomposition.decompose'_apply]
    rw [Submodule.mem_colon]
    intro a ha
    rw [smul_eq_mul]
    rw [SetLike.mem_coe, MvPolynomial.mem_iff_homogeneousComponent_mem hI] at ha
    rw [MvPolynomial.mem_iff_homogeneousComponent_mem hG_hom]
    intro m
    rw [homogeneousComponent_mul_of_isHomogeneous (homogeneousComponent_isHomogeneous e p)]
    split_ifs with hem
    · have hmem : p * homogeneousComponent (m - e) a ∈ G := by
        have := Submodule.mem_colon.mp hp _ (ha (m - e))
        rwa [smul_eq_mul] at this
      have hcomp := MvPolynomial.homogeneousComponent_mem_of_mem hG_hom hmem m
      rw [mul_comm, homogeneousComponent_mul_of_isHomogeneous
        (homogeneousComponent_isHomogeneous (m - e) a), if_pos (by omega)] at hcomp
      have hsub : m - (m - e) = e := by omega
      rw [hsub, mul_comm] at hcomp
      exact hcomp
    · exact G.zero_mem
  have hGJ : G ≤ J := fun a ha => Submodule.mem_colon.mpr fun b _ => by
    rw [smul_eq_mul]; exact G.mul_mem_right b ha
  refine ⟨hJ_hom, hGJ, ?_⟩
  have hG_hf : ∀ e, quotientHF G e = (boxSlice le_rfl d e).card :=
    quotientHF_regular_eq_card_boxSlice le_rfl hgd hg
  let uTop : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => d i - 1)
  have huTop_apply : ∀ i, uTop i = d i - 1 := fun i => rfl
  have huTop_deg : uTop.degree = s := by
    rw [Finsupp.degree_eq_sum]; rfl
  have hG_top_one : quotientHF G s = 1 := by
    rw [hG_hf s]
    have hsing : boxSlice le_rfl d s = {uTop} := by
      ext u
      simp only [boxSlice, mem_filter, mem_monOfDeg, Finset.mem_singleton]
      constructor
      · rintro ⟨hdeg, hlt⟩
        ext i
        rw [huTop_apply]
        have hle_all : ∀ j : Fin n, u j ≤ d j - 1 := fun j => by
          have := hlt j; simpa using Nat.le_sub_one_of_lt this
        by_contra hne
        have hlt_i : u i < d i - 1 := lt_of_le_of_ne (hle_all i) hne
        have hsum_lt : ∑ j : Fin n, u j < ∑ j : Fin n, (d j - 1) :=
          Finset.sum_lt_sum (fun j _ => hle_all j) ⟨i, Finset.mem_univ i, hlt_i⟩
        rw [← Finsupp.degree_eq_sum, hdeg] at hsum_lt
        exact lt_irrefl s hsum_lt
      · rintro rfl
        exact ⟨huTop_deg, fun i => by
          have := hd_pos i
          change d i - 1 < d i; omega⟩
    rw [hsing, Finset.card_singleton]
  have hG_symm : ∀ e ≤ s, quotientHF G e = quotientHF G (s - e) := by
    intro e he
    rw [hG_hf e, hG_hf (s - e)]
    refine Finset.card_bij (fun u _ => uTop - u) ?_ ?_ ?_
    · intro u hu
      simp only [boxSlice, mem_filter, mem_monOfDeg] at hu ⊢
      have hle : u ≤ uTop := Finsupp.le_def.mpr fun i => by
        rw [huTop_apply]; have := hu.2 i; change u i < d i at this; omega
      refine ⟨?_, fun i => ?_⟩
      · have hadd := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
        rw [map_add, huTop_deg, hu.1] at hadd; omega
      · have := hd_pos i
        change (uTop - u) i < d i
        simp only [Finsupp.coe_tsub, Pi.sub_apply, huTop_apply]; omega
    · intro u₁ hu₁ u₂ hu₂ heq
      have hle1 : u₁ ≤ uTop := Finsupp.le_def.mpr fun i => by
        rw [huTop_apply]; have := (mem_filter.mp hu₁).2 i; change u₁ i < d i at this; omega
      have hle2 : u₂ ≤ uTop := Finsupp.le_def.mpr fun i => by
        rw [huTop_apply]; have := (mem_filter.mp hu₂).2 i; change u₂ i < d i at this; omega
      ext i
      have h1 := Finsupp.le_def.mp hle1 i
      have h2 := Finsupp.le_def.mp hle2 i
      have h3 := congrArg (fun f : Fin n →₀ ℕ => f i) heq
      simp only [Finsupp.coe_tsub, Pi.sub_apply] at h3
      omega
    · intro v hv
      simp only [boxSlice, mem_filter, mem_monOfDeg] at hv
      have hle : v ≤ uTop := Finsupp.le_def.mpr fun i => by
        rw [huTop_apply]; have := hv.2 i; change v i < d i at this; omega
      refine ⟨uTop - v, ?_, ?_⟩
      · simp only [boxSlice, mem_filter, mem_monOfDeg]
        refine ⟨?_, fun i => ?_⟩
        · have hadd := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
          rw [map_add, huTop_deg, hv.1] at hadd; omega
        · have := hd_pos i
          change (uTop - v) i < d i
          simp only [Finsupp.coe_tsub, Pi.sub_apply, huTop_apply]; omega
      · ext i; have := Finsupp.le_def.mp hle i
        simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega
  have hG_zero_gt : ∀ m > s, quotientHF G m = 0 := by
    intro m hm
    rw [hG_hf m, boxSlice, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro u hu hlt
    have hdeg : u.degree = m := mem_monOfDeg.mp hu
    have hle : ∑ i : Fin n, u i ≤ s := Finset.sum_le_sum fun i _ => by
      have := hlt i; change u i < d i at this; omega
    rw [← Finsupp.degree_eq_sum, hdeg] at hle; omega
  let R (e : ℕ) := homogPiece n k e ⧸ idealSub G e
  let mulLeft {a b : ℕ} (x : homogPiece n k a) : R b →ₗ[k] R (a + b) :=
    Submodule.liftQ (idealSub G b)
      { toFun := fun z => Submodule.Quotient.mk ⟨x.1 * z.1, by
          rw [mem_homogeneousSubmodule]
          exact ((mem_homogeneousSubmodule _ _).mp x.2).mul ((mem_homogeneousSubmodule _ _).mp z.2)⟩
        map_add' := fun z₁ z₂ => by
          change (idealSub G (a + b)).mkQ _ = (idealSub G (a + b)).mkQ _ + (idealSub G (a + b)).mkQ _
          rw [← map_add]; congr 1; apply Subtype.ext; exact mul_add _ _ _
        map_smul' := fun c z => by
          change (idealSub G (a + b)).mkQ _ = c • (idealSub G (a + b)).mkQ _
          rw [← map_smul]; congr 1; apply Subtype.ext; simp [Algebra.mul_smul_comm] }
      (fun z hz => by
        rw [LinearMap.mem_ker]
        change Submodule.Quotient.mk _ = 0
        rw [Submodule.Quotient.mk_eq_zero, mem_idealSub]
        exact G.mul_mem_left x.1 ((mem_idealSub z).mp hz))
  let mulR {a b : ℕ} : R a →ₗ[k] R b →ₗ[k] R (a + b) :=
    Submodule.liftQ (idealSub G a)
      { toFun := fun x => mulLeft x
        map_add' := fun x₁ x₂ => by
          apply LinearMap.ext; intro y
          obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
          change (idealSub G (a + b)).mkQ _ = (idealSub G (a + b)).mkQ _ + (idealSub G (a + b)).mkQ _
          rw [← map_add]; congr 1; apply Subtype.ext; exact add_mul _ _ _
        map_smul' := fun c x => by
          apply LinearMap.ext; intro y
          obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
          change (idealSub G (a + b)).mkQ _ = c • (idealSub G (a + b)).mkQ _
          rw [← map_smul]; congr 1; apply Subtype.ext; simp [Algebra.smul_mul_assoc] }
      (fun x hx => by
        rw [LinearMap.mem_ker]
        apply LinearMap.ext; intro y
        obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        change Submodule.Quotient.mk _ = 0
        rw [Submodule.Quotient.mk_eq_zero, mem_idealSub]
        exact G.mul_mem_right z.1 ((mem_idealSub x).mp hx))
  have hmulR_mk : ∀ {a b : ℕ} (x : homogPiece n k a) (y : homogPiece n k b),
      mulR (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
        Submodule.Quotient.mk ⟨x.1 * y.1, by
          rw [mem_homogeneousSubmodule]
          exact ((mem_homogeneousSubmodule _ _).mp x.2).mul ((mem_homogeneousSubmodule _ _).mp y.2)⟩ :=
    fun _ _ => rfl
  have hnondeg : ∀ t : ℕ, ∀ e : ℕ, s - e = t → e ≤ s →
      ∀ r : R e, (∀ w : R (s - e), mulR r w = 0) → r = 0 := by
    intro t
    induction t with
    | zero =>
      intro e hse he r hr
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ r
      have h0 : s - e = 0 := hse
      have h1 := hr (Submodule.Quotient.mk ⟨1, by
        rw [h0, mem_homogeneousSubmodule]; exact isHomogeneous_one (Fin n) k⟩)
      rw [hmulR_mk, Submodule.Quotient.mk_eq_zero, mem_idealSub] at h1
      rw [Submodule.Quotient.mk_eq_zero, mem_idealSub]
      simpa using h1
    | succ t ih =>
      intro e hse he r hr
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ r
      have he_lt : e < s := by omega
      have hX_ann : ∀ i : Fin n, Ideal.Quotient.mk G (X i) * Ideal.Quotient.mk G x.1 = 0 := by
        intro i
        have hx_i : Submodule.Quotient.mk
            (⟨X i * x.1, by
              rw [mem_homogeneousSubmodule]
              simpa [add_comm] using (isHomogeneous_X k i).mul
                ((mem_homogeneousSubmodule _ _).mp x.2)⟩ : homogPiece n k (e + 1)) = (0 : R (e + 1)) := by
          apply ih (e + 1) (by omega) (by omega)
          intro w
          obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
          have hw' : mulR (Submodule.Quotient.mk x)
              (Submodule.Quotient.mk (⟨X i * y.1, by
                rw [mem_homogeneousSubmodule]
                have h := (isHomogeneous_X k i).mul ((mem_homogeneousSubmodule _ _).mp y.2)
                have hd : 1 + (s - (e + 1)) = s - e := by omega
                rwa [hd] at h⟩ : homogPiece n k (s - e))) = 0 := hr _
          rw [hmulR_mk, Submodule.Quotient.mk_eq_zero, mem_idealSub] at hw' ⊢
          dsimp only at hw' ⊢
          have heq_mul : X i * x.1 * y.1 = x.1 * (X i * y.1) := by ring
          rwa [heq_mul]
        rw [Submodule.Quotient.mk_eq_zero, mem_idealSub] at hx_i
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        exact hx_i
      have hsum_d : ∑ i : Fin n, (d i : ℤ) = (s : ℤ) + (n : ℤ) := by
        have hnat : ∑ i : Fin n, d i = s + n := by
          have : ∑ i : Fin n, d i = ∑ i : Fin n, ((d i - 1) + 1) :=
            Finset.sum_congr rfl fun i _ => by have := hd_pos i; omega
          rw [this, Finset.sum_add_distrib]
          simp [s]
        exact_mod_cast hnat
      have hkosz := (koszulExactAt_of_regular hgd hg).2 ((e : ℤ) + (n : ℤ)) (by omega)
      have hx0 := socle_eq_zero_of_koszulExactAt hkosz
        (Or.inr ⟨Nat.cast_nonneg e, x.1, by simpa using (mem_homogeneousSubmodule _ _).mp x.2, rfl⟩)
        hX_ann
      rw [Submodule.Quotient.mk_eq_zero, mem_idealSub]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx0
  have hfin_Rs : Module.finrank k (R s) = 1 := hG_top_one
  let τ : R s ≃ₗ[k] k := LinearEquiv.ofFinrankEq (R s) k (by rw [hfin_Rs, Module.finrank_self])
  intro e he
  have hes : e + (s - e) = s := Nat.add_sub_of_le he
  let castR : R (e + (s - e)) ≃ₗ[k] R s :=
    Eq.rec (motive := fun m _ => R (e + (s - e)) ≃ₗ[k] R m) (LinearEquiv.refl k (R (e + (s - e)))) hes
  let pairMap : R e →ₗ[k] Module.Dual k (R (s - e)) := {
    toFun := fun r => τ.toLinearMap.comp (castR.toLinearMap.comp (mulR r))
    map_add' := fun r₁ r₂ => by ext w; simp
    map_smul' := fun c r => by ext w; simp
  }
  have hpair_inj : Function.Injective pairMap := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    apply hnondeg (s - e) e rfl he r
    intro w
    have h1 := congrArg (fun f : Module.Dual k (R (s - e)) => f w) hr
    simp only [pairMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearMap.zero_apply] at h1
    exact castR.injective (τ.injective (by simpa using h1))
  have hfin_eq : Module.finrank k (R e) = Module.finrank k (Module.Dual k (R (s - e))) := by
    rw [Subspace.dual_finrank_eq]
    exact hG_symm e he
  have hpair_bij : Function.Bijective pairMap :=
    ⟨hpair_inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin_eq).mp hpair_inj⟩
  let pairEquiv : R e ≃ₗ[k] Module.Dual k (R (s - e)) := LinearEquiv.ofBijective pairMap hpair_bij
  let Ibar : Submodule k (R (s - e)) := Submodule.map (idealSub G (s - e)).mkQ (idealSub I (s - e))
  let Jbar : Submodule k (R e) := Submodule.map (idealSub G e).mkQ (idealSub J e)
  have hmap_Jbar : Submodule.map pairEquiv.toLinearMap Jbar = Ibar.dualAnnihilator := by
    ext φ
    obtain ⟨r, rfl⟩ := pairEquiv.surjective φ
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ r
    simp only [Submodule.mem_map, LinearEquiv.coe_coe, Submodule.mem_dualAnnihilator]
    constructor
    · rintro ⟨r', hr', heq⟩ w hw
      have hrr : r' = Submodule.Quotient.mk x := pairEquiv.injective heq
      subst hrr
      obtain ⟨x', hx'J, hx'eq⟩ := hr'
      obtain ⟨y, hyI, rfl⟩ := hw
      have hxx : Submodule.Quotient.mk x = Submodule.Quotient.mk x' := hx'eq.symm
      rw [hxx]
      have hxyG : x'.1 * y.1 ∈ G := by
        have := Submodule.mem_colon.mp ((mem_idealSub x').mp hx'J) y.1 ((mem_idealSub y).mp hyI)
        rwa [smul_eq_mul] at this
      have hmul0 : mulR (Submodule.Quotient.mk x') (Submodule.Quotient.mk y) = 0 := by
        rw [hmulR_mk, Submodule.Quotient.mk_eq_zero, mem_idealSub]; exact hxyG
      change τ (castR (mulR (Submodule.Quotient.mk x') (Submodule.Quotient.mk y))) = 0
      rw [hmul0, map_zero, map_zero]
    · intro hann
      refine ⟨Submodule.Quotient.mk x, ?_, rfl⟩
      refine ⟨x, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_idealSub, Submodule.mem_colon]
      intro a ha
      rw [smul_eq_mul]
      rw [SetLike.mem_coe, MvPolynomial.mem_iff_homogeneousComponent_mem hI] at ha
      rw [MvPolynomial.mem_iff_homogeneousComponent_mem hG_hom]
      intro m
      rw [homogeneousComponent_mul_of_isHomogeneous ((mem_homogeneousSubmodule _ _).mp x.2)]
      split_ifs with hem
      · set deg_a := m - e
        have ha_hom : (homogeneousComponent deg_a a).IsHomogeneous deg_a :=
          homogeneousComponent_isHomogeneous deg_a a
        have ha_I : homogeneousComponent deg_a a ∈ I := ha deg_a
        by_cases hms : m ≤ s
        ·
          have hprod_hom : (x.1 * homogeneousComponent deg_a a).IsHomogeneous m := by
            have h := ((mem_homogeneousSubmodule _ _).mp x.2).mul ha_hom
            rwa [Nat.add_sub_of_le hem] at h
          let prodElem : homogPiece n k m := ⟨x.1 * homogeneousComponent deg_a a,
            (mem_homogeneousSubmodule _ _).mpr hprod_hom⟩
          have hzero : (Submodule.Quotient.mk prodElem : R m) = 0 := by
            apply hnondeg (s - m) m rfl hms
            intro w
            obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
            rw [hmulR_mk, Submodule.Quotient.mk_eq_zero, mem_idealSub]
            have haz_hom : (homogeneousComponent deg_a a * z.1).IsHomogeneous (s - e) := by
              have h := ha_hom.mul ((mem_homogeneousSubmodule _ _).mp z.2)
              have hd : deg_a + (s - m) = s - e := by omega
              rwa [hd] at h
            let yElem : homogPiece n k (s - e) :=
              ⟨homogeneousComponent deg_a a * z.1, (mem_homogeneousSubmodule _ _).mpr haz_hom⟩
            have hyI : Submodule.Quotient.mk yElem ∈ Ibar :=
              ⟨yElem, (mem_idealSub yElem).mpr (I.mul_mem_right z.1 ha_I), rfl⟩
            have h0 := hann (Submodule.Quotient.mk yElem) hyI
            change τ (castR (mulR (Submodule.Quotient.mk x) (Submodule.Quotient.mk yElem))) = 0 at h0
            have hmul0 : mulR (Submodule.Quotient.mk x) (Submodule.Quotient.mk yElem) = 0 :=
              castR.injective (τ.injective (by simpa using h0))
            rw [hmulR_mk, Submodule.Quotient.mk_eq_zero, mem_idealSub] at hmul0
            simpa [prodElem, yElem, mul_assoc] using hmul0
          rw [Submodule.Quotient.mk_eq_zero, mem_idealSub] at hzero
          exact hzero
        ·
          have hG0 := hG_zero_gt m (by omega)
          have hsub_top : idealSub G m = ⊤ := by
            by_contra hne
            have : Nontrivial (homogPiece n k m ⧸ idealSub G m) :=
              Submodule.Quotient.nontrivial_iff.mpr hne
            have hpos : 0 < quotientHF G m := Module.finrank_pos
            omega
          have hprod_hom : (x.1 * homogeneousComponent deg_a a).IsHomogeneous m := by
            have h := ((mem_homogeneousSubmodule _ _).mp x.2).mul ha_hom
            rwa [Nat.add_sub_of_le hem] at h
          have hmem_top : (⟨x.1 * homogeneousComponent deg_a a,
              (mem_homogeneousSubmodule _ _).mpr hprod_hom⟩ : homogPiece n k m) ∈ idealSub G m := by
            rw [hsub_top]; exact Submodule.mem_top
          exact (mem_idealSub _).mp hmem_top
      · exact G.zero_mem
  have hdim_ann := Subspace.finrank_add_finrank_dualAnnihilator_eq Ibar
  have hdim_Jbar : Module.finrank k Jbar = Module.finrank k Ibar.dualAnnihilator := by
    rw [← hmap_Jbar]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective pairEquiv.toLinearMap
      pairEquiv.injective Jbar)
  have hdim_quot : ∀ (K : Ideal (MvPolynomial (Fin n) k)) (hGK : G ≤ K) (m : ℕ),
      Module.finrank k (Submodule.map (idealSub G m).mkQ (idealSub K m)) + quotientHF K m =
        quotientHF G m := by
    intro K hGK m
    let Kbar := Submodule.map (idealSub G m).mkQ (idealSub K m)
    have h1 := Submodule.finrank_quotient_add_finrank Kbar
    have hle : idealSub G m ≤ idealSub K m := fun x hx =>
      (mem_idealSub x).mpr (hGK ((mem_idealSub x).mp hx))
    have h2 : Module.finrank k (R m ⧸ Kbar) = quotientHF K m :=
      LinearEquiv.finrank_eq (Submodule.quotientQuotientEquivQuotient (idealSub G m) (idealSub K m) hle)
    rw [h2] at h1
    change quotientHF K m + Module.finrank k Kbar = quotientHF G m at h1
    dsimp only [Kbar] at h1
    omega
  have hI_cnt := hdim_quot I hGI (s - e)
  have hJ_cnt := hdim_quot J hGJ e
  have hsym := hG_symm e he
  change Module.finrank k Ibar + quotientHF I (s - e) = quotientHF G (s - e) at hI_cnt
  change Module.finrank k Jbar + quotientHF J e = quotientHF G e at hJ_cnt
  change Module.finrank k Ibar + Module.finrank k Ibar.dualAnnihilator = quotientHF G (s - e) at hdim_ann
  omega
end KL

namespace GM
open MvPolynomial Finset
open KL (monOfDeg mem_monOfDeg weight_one_eq_deg monomial_mem_homogPiece support_subset_monOfDeg eq_sum_monOfDeg homogPiece_finiteDimensional)
variable {n : ℕ} {k : Type*} [Field k]
abbrev homogPiece (n : ℕ) (k : Type*) [Field k] (d : ℕ) :
    Submodule k (MvPolynomial (Fin n) k) :=
  homogeneousSubmodule (Fin n) k d
noncomputable def quotientHF (I : Ideal (MvPolynomial (Fin n) k)) (d : ℕ) : ℕ :=
  Module.finrank k (homogPiece n k d ⧸
    ((Submodule.restrictScalars k I ⊓ homogPiece n k d).comap (homogPiece n k d).subtype))
noncomputable def linForm (c : Fin n → k) : MvPolynomial (Fin n) k :=
  ∑ i : Fin n, C (c i) * X i
lemma linForm_isHomogeneous (c : Fin n → k) : (linForm c).IsHomogeneous 1 := by
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  have h1 : (C (c i) : MvPolynomial (Fin n) k).IsHomogeneous 0 := isHomogeneous_C _ _
  have h2 : (X i : MvPolynomial (Fin n) k).IsHomogeneous 1 := isHomogeneous_X k i
  simpa using h1.mul h2
noncomputable def mulLinMap {ℓ : MvPolynomial (Fin n) k} (hℓ : ℓ.IsHomogeneous 1) (d : ℕ) :
    homogPiece n k d →ₗ[k] homogPiece n k (d + 1) where
  toFun g := ⟨ℓ * g.1, by
    rw [mem_homogeneousSubmodule]
    simpa [add_comm] using hℓ.mul ((mem_homogeneousSubmodule _ _).mp g.2)⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' a x := Subtype.ext (by simp [Algebra.mul_smul_comm])
lemma exists_poly_sup_mulLin_eq_top {D : ℕ} (V : Submodule k (homogPiece n k (D + 1)))
    (c₀ : Fin n → k)
    (hc₀ : V ⊔ LinearMap.range (mulLinMap (linForm_isHomogeneous c₀) D) = ⊤) :
    ∃ P : MvPolynomial (Fin n) k, P ≠ 0 ∧
      ∀ c : Fin n → k, MvPolynomial.eval c P ≠ 0 →
        V ⊔ LinearMap.range (mulLinMap (linForm_isHomogeneous c) D) = ⊤ := by
  classical
  let ι := monOfDeg n (D + 1)
  have hdecomp : ∀ u : ι, ∃ v : homogPiece n k (D + 1), ∃ g : homogPiece n k D,
      v ∈ V ∧ v + mulLinMap (linForm_isHomogeneous c₀) D g =
        ⟨monomial u.1 (1 : k), monomial_mem_homogPiece u.2⟩ := by
    intro u
    have hmem : (⟨monomial u.1 (1 : k), monomial_mem_homogPiece u.2⟩ : homogPiece n k (D + 1)) ∈
        V ⊔ LinearMap.range (mulLinMap (linForm_isHomogeneous c₀) D) := by
      rw [hc₀]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hmem
    obtain ⟨v, hv, w, ⟨g, rfl⟩, hEq⟩ := hmem
    exact ⟨v, g, hv, hEq⟩
  choose v g hv hg using hdecomp
  let M_poly : Matrix ι ι (MvPolynomial (Fin n) k) := fun w u =>
    C (coeff w.1 (v u).1) + ∑ i : Fin n, X i * C (coeff w.1 (X i * (g u).1))
  let M_eval (c : Fin n → k) : Matrix ι ι k := M_poly.map (MvPolynomial.eval c)
  have hM_eval_apply : ∀ (c : Fin n → k) (w u : ι),
      M_eval c w u = coeff w.1 ((v u + mulLinMap (linForm_isHomogeneous c) D (g u)).1) := by
    intro c w u
    change MvPolynomial.eval c (C (coeff w.1 (v u).1) +
        ∑ i : Fin n, X i * C (coeff w.1 (X i * (g u).1))) =
      coeff w.1 ((v u).1 + linForm c * (g u).1)
    simp only [map_add, eval_C, map_sum, map_mul, eval_X, coeff_add, linForm,
      Finset.sum_mul, coeff_sum, mul_assoc, coeff_C_mul]
  have hM_c₀ : M_eval c₀ = 1 := by
    ext w u
    rw [hM_eval_apply, hg u]
    simp only [Matrix.one_apply, coeff_monomial]
    by_cases h : u = w
    · subst h; simp
    · have h1 : u.1 ≠ w.1 := fun heq => h (Subtype.ext heq)
      have h2 : w ≠ u := Ne.symm h
      simp [h1, h2]
  have hdet_eval : ∀ c : Fin n → k, (M_eval c).det = MvPolynomial.eval c M_poly.det := by
    intro c
    exact (RingHom.map_det (MvPolynomial.eval c) M_poly).symm
  refine ⟨M_poly.det, ?_, ?_⟩
  · intro hzero
    have h1 : (M_eval c₀).det = 0 := by rw [hdet_eval c₀, hzero, map_zero]
    rw [hM_c₀, Matrix.det_one] at h1
    exact one_ne_zero h1
  · intro c hP
    have hdet : IsUnit (M_eval c).det := by
      rw [isUnit_iff_ne_zero, hdet_eval c]
      exact hP
    let A := (M_eval c)⁻¹
    have hmul : M_eval c * A = 1 := Matrix.mul_nonsing_inv (M_eval c) hdet
    rw [eq_top_iff]
    intro x _
    rw [eq_sum_monOfDeg x]
    refine Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ ?_
    have hcomb : (⟨monomial w.1 (1 : k), monomial_mem_homogPiece w.2⟩ : homogPiece n k (D + 1)) =
        ∑ u : ι, A u w • (v u + mulLinMap (linForm_isHomogeneous c) D (g u)) := by
      apply Subtype.ext
      apply MvPolynomial.ext
      intro m
      rw [AddSubmonoidClass.coe_finsetSum, coeff_sum]
      simp only [SetLike.val_smul, coeff_smul, smul_eq_mul]
      by_cases hm : m ∈ monOfDeg n (D + 1)
      · let m' : ι := ⟨m, hm⟩
        have hsum : ∑ u : ι, A u w * coeff m (v u + mulLinMap (linForm_isHomogeneous c) D (g u)).1 =
            (M_eval c * A) m' w := by
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [hM_eval_apply c m' u, mul_comm]
        rw [hsum, hmul, Matrix.one_apply, coeff_monomial]
        by_cases hmw : w = m'
        · subst hmw; simp [m']
        · have h1 : w.1 ≠ m := fun heq => hmw (Subtype.ext heq)
          have h2 : m' ≠ w := Ne.symm hmw
          simp [h1, h2]
      · have hzero_lhs : coeff m (monomial w.1 (1 : k)) = 0 := by
          rw [coeff_monomial, if_neg]
          rintro rfl; exact hm w.2
        rw [hzero_lhs]
        symm
        refine Finset.sum_eq_zero fun u _ => ?_
        have hzero_u : coeff m (v u + mulLinMap (linForm_isHomogeneous c) D (g u)).1 = 0 := by
          by_contra hne
          exact hm (support_subset_monOfDeg (v u + mulLinMap (linForm_isHomogeneous c) D (g u)).2
            (MvPolynomial.mem_support_iff.mpr hne))
        rw [hzero_u, mul_zero]
    rw [hcomb]
    refine Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ ?_
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hv u))
      (Submodule.mem_sup_right ⟨g u, rfl⟩)
theorem green_hyperplane_codim_le [Infinite k] :
    ∀ (D : ℕ) (V : Submodule k (homogPiece n k (D + 1))),
      Module.finrank k (homogPiece n k (D + 1) ⧸ V) ≤ D + 1 →
      ∃ c : Fin n → k, V ⊔ LinearMap.range (mulLinMap (linForm_isHomogeneous c) D) = ⊤
  | 0, V, hcodim => by
    by_cases htop : V = ⊤
    · exact ⟨0, by rw [htop, top_sup_eq]⟩
    · have hne : ∃ x : homogPiece n k 1, x ∉ V := by
        by_contra hall; push Not at hall
        exact htop (eq_top_iff.mpr fun x _ => hall x)
      obtain ⟨x, hx⟩ := hne
      let c : Fin n → k := fun i => coeff (Finsupp.single i 1) x.1
      have hx_eq : x = mulLinMap (linForm_isHomogeneous c) 0
          ⟨1, by rw [mem_homogeneousSubmodule]; exact isHomogeneous_one (Fin n) k⟩ := by
        apply Subtype.ext
        change x.1 = linForm c * 1
        rw [mul_one]
        apply MvPolynomial.ext
        intro u
        by_cases hu : u ∈ monOfDeg n 1
        · have hdeg : u.degree = 1 := mem_monOfDeg.mp hu
          rw [Finsupp.degree_eq_sum] at hdeg
          have hex : ∃ i : Fin n, u = Finsupp.single i 1 := by
            have hne0 : ∃ i ∈ (Finset.univ : Finset (Fin n)), u i ≠ 0 := by
              by_contra h0; push Not at h0
              have : ∑ i : Fin n, u i = 0 := Finset.sum_eq_zero fun i _ => h0 i (Finset.mem_univ i)
              omega
            obtain ⟨i, _, hi⟩ := hne0
            refine ⟨i, Finsupp.ext fun j => ?_⟩
            by_cases hji : j = i
            · subst hji
              have hle : u j ≤ ∑ r : Fin n, u r :=
                Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
              simp only [Finsupp.single_eq_same]; omega
            · have hle : u i + u j ≤ ∑ r : Fin n, u r :=
                Finset.add_le_sum (s := Finset.univ) (f := fun r => u r)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ i) (Finset.mem_univ j) (Ne.symm hji)
              simp only [Finsupp.single_eq_of_ne hji]; omega
          obtain ⟨i, rfl⟩ := hex
          simp only [linForm, coeff_sum, coeff_C_mul, coeff_X, c]
          rw [Finset.sum_eq_single i]
          · simp
          · intro j _ hji
            have hne_s : (Finsupp.single j (1 : ℕ)) ≠ Finsupp.single i 1 := fun h =>
              hji (Finsupp.single_left_injective one_ne_zero h)
            simp [hne_s]
          · intro hi; exact absurd (Finset.mem_univ i) hi
        · have h1 : coeff u x.1 = 0 := by
            by_contra hne0
            exact hu (support_subset_monOfDeg x.2 (MvPolynomial.mem_support_iff.mpr hne0))
          have h2 : coeff u (linForm c) = 0 := by
            by_contra hne0
            exact hu (support_subset_monOfDeg
              ((mem_homogeneousSubmodule _ _).mpr (linForm_isHomogeneous c))
              (MvPolynomial.mem_support_iff.mpr hne0))
          rw [h1, h2]
      refine ⟨c, ?_⟩
      have hlt : V < V ⊔ LinearMap.range (mulLinMap (linForm_isHomogeneous c) 0) := by
        refine lt_of_le_of_ne le_sup_left fun hEq => hx ?_
        rw [hEq]
        exact Submodule.mem_sup_right
          ⟨⟨1, by rw [mem_homogeneousSubmodule]; exact isHomogeneous_one (Fin n) k⟩, hx_eq.symm⟩
      have hdim_gt : Module.finrank k V <
          Module.finrank k ↥(V ⊔ LinearMap.range (mulLinMap (linForm_isHomogeneous c) 0)) :=
        Submodule.finrank_lt_finrank_of_lt hlt
      have hdim_tot := Submodule.finrank_quotient_add_finrank V
      have hdim_le : Module.finrank k ↥(V ⊔ LinearMap.range (mulLinMap (linForm_isHomogeneous c) 0)) ≤
          Module.finrank k (homogPiece n k (0 + 1)) := Submodule.finrank_le _
      exact Submodule.eq_top_of_finrank_eq (by omega)
  | D + 1, V, hcodim => by
    by_contra hnone
    push Not at hnone
    have hpoly : ∀ i : Fin n, ∃ P : MvPolynomial (Fin n) k, P ≠ 0 ∧
        ∀ c : Fin n → k, MvPolynomial.eval c P ≠ 0 →
          (V.comap (mulLinMap (isHomogeneous_X k i) (D + 1))) ⊔
            LinearMap.range (mulLinMap (linForm_isHomogeneous c) D) = ⊤ := by
      intro i
      let μi := mulLinMap (isHomogeneous_X k i) (D + 1)
      let Wi := V.comap μi
      have hX_eq : μi = mulLinMap (linForm_isHomogeneous (Pi.single i (1 : k))) (D + 1) := by
        ext g
        simp only [μi, mulLinMap, LinearMap.coe_mk, AddHom.coe_mk, linForm]
        congr 1
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji; simp [Pi.single_eq_of_ne hji]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      have hne_top_i : V ⊔ LinearMap.range μi ≠ ⊤ := by
        rw [hX_eq]; exact hnone (Pi.single i 1)
      let φ : homogPiece n k (D + 1) →ₗ[k] (homogPiece n k (D + 1 + 1) ⧸ V) :=
        V.mkQ.comp μi
      have hker : LinearMap.ker φ = Wi := by
        ext g
        simp [φ, Wi, Submodule.Quotient.mk_eq_zero]
      have hdim_Wi : Module.finrank k (homogPiece n k (D + 1) ⧸ Wi) =
          Module.finrank k (LinearMap.range φ) := by
        rw [← hker]
        exact LinearEquiv.finrank_eq (φ.quotKerEquivRange)
      have hrange_le : LinearMap.range φ ≤
          Submodule.map V.mkQ (V ⊔ LinearMap.range μi) := by
        rintro _ ⟨g, rfl⟩
        exact ⟨μi g, Submodule.mem_sup_right ⟨g, rfl⟩, rfl⟩
      have hne_sub : Submodule.map V.mkQ (V ⊔ LinearMap.range μi) ≠ ⊤ := by
        intro heq
        apply hne_top_i
        rw [eq_top_iff]
        intro y _
        have hy : V.mkQ y ∈ Submodule.map V.mkQ (V ⊔ LinearMap.range μi) := by
          rw [heq]; exact Submodule.mem_top
        obtain ⟨z, hz, hzy⟩ := hy
        have hsub : y - z ∈ V := by
          rw [← Submodule.Quotient.mk_eq_zero]
          change V.mkQ (y - z) = 0
          rw [map_sub, hzy, sub_self]
        simpa using Submodule.add_mem _ (Submodule.mem_sup_left hsub) hz
      have hdim_range_lt : Module.finrank k (LinearMap.range φ) <
          Module.finrank k (homogPiece n k (D + 1 + 1) ⧸ V) :=
        lt_of_le_of_lt (Submodule.finrank_mono hrange_le) (Submodule.finrank_lt hne_sub)
      have hWi_codim : Module.finrank k (homogPiece n k (D + 1) ⧸ Wi) ≤ D + 1 := by omega
      obtain ⟨ci, hci⟩ := green_hyperplane_codim_le D Wi hWi_codim
      exact exists_poly_sup_mulLin_eq_top Wi ci hci
    choose P hP_ne hP_ok using hpoly
    let P_all : MvPolynomial (Fin n) k := ∏ i : Fin n, P i
    have hP_all_ne : P_all ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hP_ne i
    have hc_exists : ∃ c : Fin n → k, MvPolynomial.eval c P_all ≠ 0 := by
      by_contra hall; push Not at hall
      exact hP_all_ne (MvPolynomial.funext fun c => by rw [hall c, map_zero])
    obtain ⟨c, hc⟩ := hc_exists
    have hPc : ∀ i : Fin n, MvPolynomial.eval c (P i) ≠ 0 := by
      intro i hi
      apply hc
      simp only [P_all, map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    apply hnone c
    rw [eq_top_iff]
    intro x _
    rw [eq_sum_monOfDeg x]
    refine Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ ?_
    have hu_deg : u.1.degree = D + 2 := mem_monOfDeg.mp u.2
    have hex : ∃ i : Fin n, 1 ≤ u.1 i := by
      by_contra h0; push Not at h0
      have hsum : ∑ i : Fin n, u.1 i = 0 := Finset.sum_eq_zero fun i _ => by have := h0 i; omega
      rw [Finsupp.degree_eq_sum] at hu_deg; omega
    obtain ⟨i, hi⟩ := hex
    let u' : Fin n →₀ ℕ := u.1 - Finsupp.single i 1
    have hu'_add : Finsupp.single i 1 + u' = u.1 := by
      ext j
      by_cases hji : j = i
      · subst hji; simp [u']; omega
      · simp [u', Finsupp.single_eq_of_ne hji]
    have hu'_deg : u'.degree = D + 1 := by
      have h := congrArg Finsupp.degree hu'_add
      rw [map_add, Finsupp.degree_single, hu_deg] at h; omega
    have hu'_mem : u' ∈ monOfDeg n (D + 1) := mem_monOfDeg.mpr hu'_deg
    let g : homogPiece n k (D + 1) := ⟨monomial u' (1 : k), monomial_mem_homogPiece hu'_mem⟩
    have hg_top : g ∈ (V.comap (mulLinMap (isHomogeneous_X k i) (D + 1))) ⊔
        LinearMap.range (mulLinMap (linForm_isHomogeneous c) D) := by
      rw [hP_ok i c (hPc i)]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hg_top
    obtain ⟨w, hw, _, ⟨q, rfl⟩, hwg⟩ := hg_top
    have hmon_eq : (⟨monomial u.1 (1 : k), monomial_mem_homogPiece u.2⟩ : homogPiece n k (D + 2)) =
        mulLinMap (isHomogeneous_X k i) (D + 1) g := by
      apply Subtype.ext
      change monomial u.1 (1 : k) = X i * monomial u' 1
      rw [X, monomial_mul, one_mul, hu'_add]
    rw [hmon_eq, ← hwg, map_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left hw) (Submodule.mem_sup_right ?_)
    refine ⟨mulLinMap (isHomogeneous_X k i) D q, ?_⟩
    apply Subtype.ext
    change linForm c * (X i * q.1) = X i * (linForm c * q.1)
    ring
theorem gotzmann_persistence_pos [Infinite k]
    (Q : Ideal (MvPolynomial (Fin n) k)) (D : ℕ)
    (hgen : Q = Ideal.span {q ∈ Q | ∃ e ≤ D, q.IsHomogeneous e})
    (hpos : 0 < quotientHF Q D)
    (heq : quotientHF Q D = quotientHF Q (D + 1))
    (hle : quotientHF Q D ≤ D) :
    ∀ m : ℕ, 0 < quotientHF Q m := by
  have hD : 1 ≤ D := by omega
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  let Qsub (e : ℕ) : Submodule k (homogPiece n k e) :=
    (Submodule.restrictScalars k Q ⊓ homogPiece n k e).comap (homogPiece n k e).subtype
  have hmem_Qsub : ∀ {e : ℕ} (x : homogPiece n k e), x ∈ Qsub e ↔ x.1 ∈ Q := by
    intro e x; simp [Qsub]
  obtain ⟨c, hc⟩ := green_hyperplane_codim_le D' (Qsub (D' + 1)) hle
  let ℓ : MvPolynomial (Fin n) k := linForm c
  have hℓ : ℓ.IsHomogeneous 1 := linForm_isHomogeneous c
  let R (e : ℕ) := homogPiece n k e ⧸ Qsub e
  let mulℓ : R (D' + 1) →ₗ[k] R (D' + 2) :=
    Submodule.mapQ (Qsub (D' + 1)) (Qsub (D' + 2)) (mulLinMap hℓ (D' + 1)) (by
      intro x hx
      rw [Submodule.mem_comap, hmem_Qsub]
      exact Q.mul_mem_left ℓ ((hmem_Qsub x).mp hx))
  have hsurj_D : ∀ x : homogPiece n k (D' + 1), ∃ q ∈ Qsub (D' + 1), ∃ g : homogPiece n k D',
      q + mulLinMap hℓ D' g = x := by
    intro x
    have hx : x ∈ Qsub (D' + 1) ⊔ LinearMap.range (mulLinMap hℓ D') := by
      rw [hc]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hx
    obtain ⟨q, hq, _, ⟨g, rfl⟩, hEq⟩ := hx
    exact ⟨q, hq, g, hEq⟩
  have hmulℓ_surj : Function.Surjective mulℓ := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hx_decomp : x ∈ Qsub (D' + 2) ⊔ LinearMap.range (mulLinMap hℓ (D' + 1)) := by
      rw [eq_sum_monOfDeg x]
      refine Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ ?_
      have hu_deg : u.1.degree = D' + 2 := mem_monOfDeg.mp u.2
      have hex : ∃ i : Fin n, 1 ≤ u.1 i := by
        by_contra h0; push Not at h0
        have hsum : ∑ i : Fin n, u.1 i = 0 := Finset.sum_eq_zero fun i _ => by have := h0 i; omega
        rw [Finsupp.degree_eq_sum] at hu_deg; omega
      obtain ⟨i, hi⟩ := hex
      let u' : Fin n →₀ ℕ := u.1 - Finsupp.single i 1
      have hu'_add : Finsupp.single i 1 + u' = u.1 := by
        ext j
        by_cases hji : j = i
        · subst hji; simp [u']; omega
        · simp [u', Finsupp.single_eq_of_ne hji]
      have hu'_mem : u' ∈ monOfDeg n (D' + 1) := by
        rw [mem_monOfDeg]
        have h := congrArg Finsupp.degree hu'_add
        rw [map_add, Finsupp.degree_single, hu_deg] at h; omega
      let g : homogPiece n k (D' + 1) := ⟨monomial u' 1, monomial_mem_homogPiece hu'_mem⟩
      obtain ⟨q, hq, w, hqw⟩ := hsurj_D g
      have hmon_eq : (⟨monomial u.1 1, monomial_mem_homogPiece u.2⟩ : homogPiece n k (D' + 2)) =
          mulLinMap (isHomogeneous_X k i) (D' + 1) g := by
        apply Subtype.ext; change monomial u.1 1 = X i * monomial u' 1
        rw [X, monomial_mul, one_mul, hu'_add]
      rw [hmon_eq, ← hqw, map_add]
      refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
      · rw [hmem_Qsub]; exact Q.mul_mem_left (X i) ((hmem_Qsub q).mp hq)
      · refine ⟨mulLinMap (isHomogeneous_X k i) D' w, ?_⟩
        apply Subtype.ext; change ℓ * (X i * w.1) = X i * (ℓ * w.1); ring
    rw [Submodule.mem_sup] at hx_decomp
    obtain ⟨q, hq, _, ⟨g, rfl⟩, hEq⟩ := hx_decomp
    refine ⟨Submodule.Quotient.mk g, ?_⟩
    change Submodule.Quotient.mk (mulLinMap hℓ (D' + 1) g) = Submodule.Quotient.mk x
    rw [Submodule.Quotient.eq, ← hEq]
    simpa [sub_eq_add_neg] using Submodule.neg_mem _ hq
  have hmulℓ_bij : Function.Bijective mulℓ :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hmulℓ_surj, hmulℓ_surj⟩
  let eℓ : R (D' + 1) ≃ₗ[k] R (D' + 2) := LinearEquiv.ofBijective mulℓ hmulℓ_bij
  let mulX (i : Fin n) : R (D' + 1) →ₗ[k] R (D' + 2) :=
    Submodule.mapQ (Qsub (D' + 1)) (Qsub (D' + 2)) (mulLinMap (isHomogeneous_X k i) (D' + 1)) (by
      intro x hx; rw [Submodule.mem_comap, hmem_Qsub]
      exact Q.mul_mem_left (X i) ((hmem_Qsub x).mp hx))
  let φ (i : Fin n) : Module.End k (R (D' + 1)) := eℓ.symm.toLinearMap.comp (mulX i)
  have hφ_spec : ∀ (i : Fin n) (v : R (D' + 1)), mulℓ (φ i v) = mulX i v := by
    intro i v; exact eℓ.apply_symm_apply (mulX i v)
  have hφ_mulℓ : ∀ (i : Fin n) (w : homogPiece n k D'),
      φ i (Submodule.Quotient.mk (mulLinMap hℓ D' w)) =
        Submodule.Quotient.mk (mulLinMap (isHomogeneous_X k i) D' w) := by
    intro i w
    apply hmulℓ_bij.1
    rw [hφ_spec]
    change Submodule.Quotient.mk (mulLinMap (isHomogeneous_X k i) (D' + 1) (mulLinMap hℓ D' w)) =
      Submodule.Quotient.mk (mulLinMap hℓ (D' + 1) (mulLinMap (isHomogeneous_X k i) D' w))
    congr 1; apply Subtype.ext
    change X i * (ℓ * w.1) = ℓ * (X i * w.1); ring
  have hcomm : ∀ i j : Fin n, φ i * φ j = φ j * φ i := by
    intro i j
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨q, hq, w, hqw⟩ := hsurj_D x
    have hv_eq : (Submodule.Quotient.mk x : R (D' + 1)) =
        Submodule.Quotient.mk (mulLinMap hℓ D' w) := by
      have h1 : (Qsub (D' + 1)).mkQ x = (Qsub (D' + 1)).mkQ (q + mulLinMap hℓ D' w) := by rw [hqw]
      rw [map_add] at h1
      change Submodule.Quotient.mk x = Submodule.Quotient.mk q + Submodule.Quotient.mk (mulLinMap hℓ D' w) at h1
      rw [(Submodule.Quotient.mk_eq_zero _).mpr hq, zero_add] at h1
      exact h1
    change φ i (φ j (Submodule.Quotient.mk x)) = φ j (φ i (Submodule.Quotient.mk x))
    rw [hv_eq]
    apply hmulℓ_bij.1
    rw [hφ_spec, hφ_spec, hφ_mulℓ, hφ_mulℓ]
    change Submodule.Quotient.mk (mulLinMap (isHomogeneous_X k i) (D' + 1)
        (mulLinMap (isHomogeneous_X k j) D' w)) =
      Submodule.Quotient.mk (mulLinMap (isHomogeneous_X k j) (D' + 1)
        (mulLinMap (isHomogeneous_X k i) D' w))
    congr 1; apply Subtype.ext
    change X i * (X j * w.1) = X j * (X i * w.1); ring
  let subA : Subalgebra k (Module.End k (R (D' + 1))) := Algebra.adjoin k (Set.range φ)
  have hsubA_comm : ∀ a ∈ subA, ∀ b ∈ subA, a * b = b * a := by
    intro a ha b hb
    refine Algebra.adjoin_induction
      (p := fun x _ => ∀ y ∈ subA, x * y = y * x) ?_ ?_ ?_ ?_ ha b hb
    · rintro _ ⟨i, rfl⟩ y hy
      refine Algebra.adjoin_induction
        (p := fun z _ => φ i * z = z * φ i) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨j, rfl⟩; exact hcomm i j
      · intro r; simp [Algebra.commutes]
      · intro x y _ _ hx hy; rw [mul_add, add_mul, hx, hy]
      · intro x y _ _ hx hy; rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
    · intro r y _; simp [Algebra.commutes]
    · intro x y _ _ hx hy z hz; rw [add_mul, mul_add, hx z hz, hy z hz]
    · intro x y _ _ hx hy z hz; rw [mul_assoc, hy z hz, ← mul_assoc, hx z hz, mul_assoc]
  let _ : CommRing subA := {
    (inferInstance : Ring subA) with
    mul_comm := fun a b => Subtype.ext (hsubA_comm a.1 a.2 b.1 b.2)
  }
  let Φ_sub : MvPolynomial (Fin n) k →ₐ[k] subA :=
    MvPolynomial.aeval (fun i => (⟨φ i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : subA))
  let Φ : MvPolynomial (Fin n) k →ₐ[k] Module.End k (R (D' + 1)) :=
    subA.val.comp Φ_sub
  have hΦ_X : ∀ i : Fin n, Φ (X i) = φ i := by
    intro i; simp [Φ, Φ_sub]
  have hΦ_comm : ∀ p q : MvPolynomial (Fin n) k, Φ p * Φ q = Φ q * Φ p := by
    intro p q; rw [← map_mul, ← map_mul, mul_comm]
  have hΦ_ℓ : Φ ℓ = 1 := by
    apply LinearMap.ext
    intro v
    apply hmulℓ_bij.1
    change mulℓ (Φ ℓ v) = mulℓ v
    have h1 : Φ ℓ = ∑ i : Fin n, c i • φ i := by
      simp only [ℓ, linForm, map_sum, map_mul, hΦ_X]
      refine Finset.sum_congr rfl fun i _ => ?_
      change (Φ (algebraMap k _ (c i))) * φ i = c i • φ i
      rw [AlgHom.commutes, Algebra.smul_def]
    rw [h1]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hφ_spec]
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    change ∑ i : Fin n, c i • (Qsub (D' + 2)).mkQ (mulLinMap (isHomogeneous_X k i) (D' + 1) x) =
      (Qsub (D' + 2)).mkQ (mulLinMap hℓ (D' + 1) x)
    simp_rw [← map_smul]
    rw [← map_sum]
    congr 1; apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [SetLike.val_smul, mulLinMap, LinearMap.coe_mk, AddHom.coe_mk, ℓ, linForm,
      Finset.sum_mul, Algebra.smul_def, algebraMap_eq]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hℓ_pow_hom : ∀ m : ℕ, (ℓ ^ m).IsHomogeneous m := by
    intro m; simpa using hℓ.pow m
  let v₀ : R (D' + 1) :=
    Submodule.Quotient.mk ⟨ℓ ^ (D' + 1), (mem_homogeneousSubmodule _ _).mpr (hℓ_pow_hom (D' + 1))⟩
  have hΦ_v₀ : ∀ e : ℕ, ∀ he : e ≤ D' + 1, ∀ p : homogPiece n k e,
      Φ p.1 v₀ = Submodule.Quotient.mk
        ⟨p.1 * ℓ ^ (D' + 1 - e), by
          rw [mem_homogeneousSubmodule]
          have hp := (mem_homogeneousSubmodule _ _).mp p.2
          have h := hp.mul (hℓ_pow_hom (D' + 1 - e))
          rwa [Nat.add_sub_of_le he] at h⟩ := by
    intro e
    induction e with
    | zero =>
      intro _ p
      have hp_eq : p.1 = C (coeff 0 p.1) := by
        apply MvPolynomial.ext; intro u
        by_cases hu : u = 0
        · subst hu; simp
        · have hu_not : u ∉ monOfDeg n 0 := by
            rw [mem_monOfDeg]; intro hdeg
            apply hu; ext i
            have hle : u i ≤ ∑ j : Fin n, u j :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
            rw [← Finsupp.degree_eq_sum, hdeg] at hle
            simp only [Finsupp.coe_zero, Pi.zero_apply]
            omega
          have h0 : coeff u p.1 = 0 := by
            by_contra hne
            exact hu_not (support_subset_monOfDeg p.2 (MvPolynomial.mem_support_iff.mpr hne))
          rw [h0, coeff_C, if_neg (Ne.symm hu)]
      have h1 : Φ p.1 v₀ = coeff 0 p.1 • v₀ := by
        conv_lhs => rw [hp_eq]
        change (Φ (algebraMap k _ (coeff 0 p.1))) v₀ = coeff 0 p.1 • v₀
        rw [AlgHom.commutes]
        rfl
      rw [h1]
      change coeff 0 p.1 • (Qsub (D' + 1)).mkQ _ = (Qsub (D' + 1)).mkQ _
      rw [← map_smul]
      congr 1; apply Subtype.ext
      simp only [SetLike.val_smul, Nat.sub_zero, Algebra.smul_def, algebraMap_eq]
      rw [← hp_eq]
    | succ e ih =>
      intro he p
      have hsum_val : p.1 = ∑ u : monOfDeg n (e + 1), coeff u.1 p.1 • monomial u.1 (1 : k) := by
        conv_lhs => rw [eq_sum_monOfDeg p]
        rw [AddSubmonoidClass.coe_finsetSum]; rfl
      have hterm_hom : ∀ u : monOfDeg n (e + 1),
          ((coeff u.1 p.1 • monomial u.1 (1 : k)) * ℓ ^ (D' + 1 - (e + 1))).IsHomogeneous (D' + 1) := by
        intro u
        have h1 : (coeff u.1 p.1 • monomial u.1 (1 : k)).IsHomogeneous (e + 1) :=
          (mem_homogeneousSubmodule _ _).mp
            (Submodule.smul_mem _ (coeff u.1 p.1) (monomial_mem_homogPiece u.2))
        have h2 := h1.mul (hℓ_pow_hom (D' + 1 - (e + 1)))
        rwa [Nat.add_sub_of_le he] at h2
      have hterm : ∀ u : monOfDeg n (e + 1),
          Φ (coeff u.1 p.1 • monomial u.1 (1 : k)) v₀ =
            (Qsub (D' + 1)).mkQ ⟨(coeff u.1 p.1 • monomial u.1 (1 : k)) * ℓ ^ (D' + 1 - (e + 1)),
              (mem_homogeneousSubmodule _ _).mpr (hterm_hom u)⟩ := by
        intro u
        rw [map_smul, LinearMap.smul_apply]
        have hu_deg : u.1.degree = e + 1 := mem_monOfDeg.mp u.2
        have hex : ∃ i : Fin n, 1 ≤ u.1 i := by
          by_contra h0; push Not at h0
          have hsum : ∑ i : Fin n, u.1 i = 0 := Finset.sum_eq_zero fun i _ => by have := h0 i; omega
          rw [Finsupp.degree_eq_sum] at hu_deg; omega
        obtain ⟨i, hi⟩ := hex
        let u' : Fin n →₀ ℕ := u.1 - Finsupp.single i 1
        have hu'_add : Finsupp.single i 1 + u' = u.1 := by
          ext j
          by_cases hji : j = i
          · subst hji; simp [u']; omega
          · simp [u', Finsupp.single_eq_of_ne hji]
        have hu'_mem : u' ∈ monOfDeg n e := by
          rw [mem_monOfDeg]
          have h := congrArg Finsupp.degree hu'_add
          rw [map_add, Finsupp.degree_single, hu_deg] at h; omega
        have hmon : monomial u.1 (1 : k) = X i * monomial u' 1 := by
          rw [X, monomial_mul, one_mul, hu'_add]
        conv_lhs => rw [hmon, map_mul, Module.End.mul_apply, hΦ_X]
        let p' : homogPiece n k e := ⟨monomial u' 1, monomial_mem_homogPiece hu'_mem⟩
        rw [ih (by omega) p']
        have hsub : D' + 1 - e = (D' + 1 - (e + 1)) + 1 := by omega
        let w : homogPiece n k D' := ⟨p'.1 * ℓ ^ (D' + 1 - (e + 1)), by
          rw [mem_homogeneousSubmodule]
          have h := ((mem_homogeneousSubmodule _ _).mp p'.2).mul (hℓ_pow_hom (D' + 1 - (e + 1)))
          have hdeg_eq : e + (D' + 1 - (e + 1)) = D' := by omega
          rwa [hdeg_eq] at h⟩
        have hw_eq : (⟨p'.1 * ℓ ^ (D' + 1 - e), by
            rw [mem_homogeneousSubmodule]
            have h := ((mem_homogeneousSubmodule _ _).mp p'.2).mul (hℓ_pow_hom (D' + 1 - e))
            rwa [Nat.add_sub_of_le (by omega)] at h⟩ : homogPiece n k (D' + 1)) =
            mulLinMap hℓ D' w := by
          apply Subtype.ext
          change p'.1 * ℓ ^ (D' + 1 - e) = ℓ * (p'.1 * ℓ ^ (D' + 1 - (e + 1)))
          rw [hsub, pow_succ]; ring
        rw [hw_eq, hφ_mulℓ]
        change coeff u.1 p.1 • (Qsub (D' + 1)).mkQ _ = (Qsub (D' + 1)).mkQ _
        rw [← map_smul]
        congr 1; apply Subtype.ext
        change coeff u.1 p.1 • (X i * (p'.1 * ℓ ^ (D' + 1 - (e + 1)))) =
          (coeff u.1 p.1 • monomial u.1 (1 : k)) * ℓ ^ (D' + 1 - (e + 1))
        rw [hmon]; simp only [p', smul_mul_assoc, mul_assoc]
      calc Φ p.1 v₀
          = Φ (∑ u : monOfDeg n (e + 1), coeff u.1 p.1 • monomial u.1 (1 : k)) v₀ := by
              rw [← hsum_val]
        _ = ∑ u : monOfDeg n (e + 1), Φ (coeff u.1 p.1 • monomial u.1 (1 : k)) v₀ := by
              rw [map_sum, LinearMap.sum_apply]
        _ = ∑ u : monOfDeg n (e + 1), (Qsub (D' + 1)).mkQ
              ⟨(coeff u.1 p.1 • monomial u.1 (1 : k)) * ℓ ^ (D' + 1 - (e + 1)),
                (mem_homogeneousSubmodule _ _).mpr (hterm_hom u)⟩ :=
              Finset.sum_congr rfl fun u _ => hterm u
        _ = (Qsub (D' + 1)).mkQ (∑ u : monOfDeg n (e + 1),
              ⟨(coeff u.1 p.1 • monomial u.1 (1 : k)) * ℓ ^ (D' + 1 - (e + 1)),
                (mem_homogeneousSubmodule _ _).mpr (hterm_hom u)⟩) := (map_sum _ _ _).symm
        _ = Submodule.Quotient.mk ⟨p.1 * ℓ ^ (D' + 1 - (e + 1)), _⟩ := by
              change (Qsub (D' + 1)).mkQ _ = (Qsub (D' + 1)).mkQ _
              congr 1; apply Subtype.ext
              rw [AddSubmonoidClass.coe_finsetSum]
              change ∑ i : monOfDeg n (e + 1), (coeff i.1 p.1 • monomial i.1 (1 : k)) *
                  ℓ ^ (D' + 1 - (e + 1)) = p.1 * ℓ ^ (D' + 1 - (e + 1))
              rw [← Finset.sum_mul, ← hsum_val]
  have hQ_ker : Q ≤ RingHom.ker Φ.toRingHom := by
    rw [hgen, Ideal.span_le]
    rintro q ⟨hqQ, e, he, hq_hom⟩
    change Φ q = 0
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    have hx_v₀ : Φ x.1 v₀ = Submodule.Quotient.mk x := by
      have h := hΦ_v₀ (D' + 1) le_rfl x
      rw [h]
      congr 1; apply Subtype.ext
      simp
    rw [← hx_v₀, ← Module.End.mul_apply, hΦ_comm, Module.End.mul_apply]
    have hq_v₀ : Φ q v₀ = 0 := by
      have h := hΦ_v₀ e he ⟨q, (mem_homogeneousSubmodule _ _).mpr hq_hom⟩
      rw [h, Submodule.Quotient.mk_eq_zero, hmem_Qsub]
      exact Q.mul_mem_right _ hqQ
    rw [hq_v₀, map_zero]; rfl
  intro m
  have hℓm_not_mem : ℓ ^ m ∉ Q := by
    intro hmem
    have hzero : Φ (ℓ ^ m) = 0 := hQ_ker hmem
    rw [map_pow, hΦ_ℓ, one_pow] at hzero
    have hnt : Nontrivial (R (D' + 1)) := Module.nontrivial_of_finrank_pos hpos
    obtain ⟨v, hv⟩ := exists_ne (0 : R (D' + 1))
    have := congrArg (fun f : Module.End k (R (D' + 1)) => f v) hzero
    exact hv this
  have hne_top : Qsub m ≠ ⊤ := by
    intro htop
    have hm : (⟨ℓ ^ m, (mem_homogeneousSubmodule _ _).mpr (hℓ_pow_hom m)⟩ : homogPiece n k m) ∈
        Qsub m := by rw [htop]; exact Submodule.mem_top
    exact hℓm_not_mem ((hmem_Qsub _).mp hm)
  have _ : Nontrivial (homogPiece n k m ⧸ Qsub m) :=
    Submodule.Quotient.nontrivial_iff.mpr hne_top
  exact Module.finrank_pos
end GM

namespace RM
open MvPolynomial Finset
open KL (homogPiece idealSub mem_idealSub quotientHF monOfDeg mem_monOfDeg weight_one_eq_deg monomial_mem_homogPiece support_subset_monOfDeg eq_sum_monOfDeg homogPieceBasis homogPiece_finiteDimensional finrank_homogPiece hilbertFunction_add_quotientHF)
open scoped Pointwise
variable {n : ℕ} {k : Type*} [Field k]
noncomputable local instance : GradedAlgebra (homogeneousSubmodule (Fin n) k) :=
  MvPolynomial.gradedAlgebra
lemma mem_monomialIdeal_iff_support {S : Set (Fin n →₀ ℕ)}
    (hS : ∀ u ∈ S, ∀ i : Fin n, u + Finsupp.single i 1 ∈ S)
    (p : MvPolynomial (Fin n) k) :
    p ∈ Ideal.span ((fun u => monomial u (1 : k)) '' S) ↔ ∀ u ∈ p.support, u ∈ S := by
  classical
  have hS_add : ∀ v : Fin n →₀ ℕ, ∀ u ∈ S, u + v ∈ S := by
    intro v
    induction v using Finsupp.induction with
    | zero => intro u hu; simpa using hu
    | single_add i a b _ _ ih =>
      intro u hu
      have h1 : ∀ m : ℕ, u + Finsupp.single i m ∈ S := by
        intro m
        induction m with
        | zero => simpa using hu
        | succ m ihm =>
          have : u + Finsupp.single i (m + 1) = (u + Finsupp.single i m) + Finsupp.single i 1 := by
            ext j; simp [add_assoc]
          rw [this]; exact hS _ ihm i
      rw [← add_assoc]
      exact ih _ (h1 a)
  constructor
  · intro hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨u, hu, rfl⟩ v hv
      rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hv
      rwa [hv]
    · intro u hu; simp at hu
    · intro x y _ _ hx hy u hu
      rcases Finset.mem_union.mp (MvPolynomial.support_add hu) with h | h
      · exact hx u h
      · exact hy u h
    · intro r x _ hx u hu
      have hne : coeff u (r * x) ≠ 0 := MvPolynomial.mem_support_iff.mp hu
      rw [coeff_mul] at hne
      obtain ⟨⟨a, b⟩, hab, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      rw [HasAntidiagonal.mem_antidiagonal] at hab
      have hb : b ∈ x.support := MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hterm)
      rw [← hab, add_comm]
      exact hS_add a b (hx b hb)
  · intro hsupp
    rw [p.as_sum]
    apply Ideal.sum_mem
    intro u hu
    have hmon : monomial u (coeff u p) = C (coeff u p) * monomial u (1 : k) := by
      rw [C_mul_monomial, mul_one]
    rw [hmon]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨u, hsupp u hu, rfl⟩)
lemma homogeneousComponent_eq_zero_of_ne {p : MvPolynomial (Fin n) k} {i e : ℕ}
    (hp : p.IsHomogeneous i) (hne : i ≠ e) : homogeneousComponent e p = 0 := by
  ext u
  rw [coeff_homogeneousComponent, coeff_zero]
  split_ifs with h
  · exact hp.coeff_eq_zero (by omega)
  · rfl
lemma infinite_ratFunc (k : Type*) [Field k] : Infinite (RatFunc k) := by
  apply Infinite.of_injective
    (fun m : ℕ => algebraMap (Polynomial k) (RatFunc k) (Polynomial.X ^ m))
  intro a b h
  have h1 := IsFractionRing.injective (Polynomial k) (RatFunc k) h
  have h2 := congrArg Polynomial.natDegree h1
  simpa using h2
section BaseChange
variable (n k)
abbrev Kext (k : Type*) [Field k] := RatFunc k
noncomputable def mapK : MvPolynomial (Fin n) k →+* MvPolynomial (Fin n) (Kext k) :=
  MvPolynomial.map (algebraMap k (Kext k))
noncomputable def vecBasis : Module.Basis (Module.Basis.ofVectorSpaceIndex k (Kext k)) k (Kext k) :=
  Module.Basis.ofVectorSpace k (Kext k)
noncomputable def polyProj (i : Module.Basis.ofVectorSpaceIndex k (Kext k))
    (p : MvPolynomial (Fin n) (Kext k)) : MvPolynomial (Fin n) k :=
  ∑ u ∈ p.support, monomial u ((vecBasis k).coord i (coeff u p))
lemma coeff_polyProj (i : Module.Basis.ofVectorSpaceIndex k (Kext k))
    (p : MvPolynomial (Fin n) (Kext k)) (u : Fin n →₀ ℕ) :
    coeff u (polyProj n k i p) = (vecBasis k).coord i (coeff u p) := by
  classical
  unfold polyProj
  rw [coeff_sum]
  by_cases hu : u ∈ p.support
  · rw [Finset.sum_eq_single u]
    · simp
    · intro v _ hvu; rw [coeff_monomial, if_neg hvu]
    · intro h; exact absurd hu h
  · rw [MvPolynomial.notMem_support_iff.mp hu, map_zero]
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [coeff_monomial, if_neg (fun h : v = u => hu (h ▸ hv))]
lemma polyProj_add (i : Module.Basis.ofVectorSpaceIndex k (Kext k))
    (p q : MvPolynomial (Fin n) (Kext k)) :
    polyProj n k i (p + q) = polyProj n k i p + polyProj n k i q := by
  ext u
  rw [coeff_add, coeff_polyProj, coeff_polyProj, coeff_polyProj, coeff_add, map_add]
lemma polyProj_zero (i : Module.Basis.ofVectorSpaceIndex k (Kext k)) :
    polyProj n k i 0 = 0 := by
  ext u; simp [coeff_polyProj]
lemma polyProj_mapK_mul (i : Module.Basis.ofVectorSpaceIndex k (Kext k))
    (g : MvPolynomial (Fin n) k) (p : MvPolynomial (Fin n) (Kext k)) :
    polyProj n k i (mapK n k g * p) = g * polyProj n k i p := by
  ext u
  rw [coeff_polyProj, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun xy _ => ?_
  rw [coeff_polyProj, mapK, coeff_map, ← Algebra.smul_def, map_smul, smul_eq_mul]
lemma polyProj_C_mul_mapK (i : Module.Basis.ofVectorSpaceIndex k (Kext k))
    (c : Kext k) (g : MvPolynomial (Fin n) k) :
    polyProj n k i (C c * mapK n k g) = ((vecBasis k).coord i c) • g := by
  ext u
  rw [coeff_polyProj, coeff_C_mul, mapK, coeff_map, mul_comm, ← Algebra.smul_def,
    map_smul, coeff_smul, smul_eq_mul, smul_eq_mul, mul_comm]
lemma eq_sum_polyProj (p : MvPolynomial (Fin n) (Kext k)) :
    ∃ S : Finset (Module.Basis.ofVectorSpaceIndex k (Kext k)),
      p = ∑ i ∈ S, C (vecBasis k i) * mapK n k (polyProj n k i p) := by
  classical
  let S : Finset (Module.Basis.ofVectorSpaceIndex k (Kext k)) :=
    p.support.biUnion (fun u => ((vecBasis k).repr (coeff u p)).support)
  refine ⟨S, ?_⟩
  ext u
  rw [coeff_sum]
  have hterm : ∀ i, coeff u (C (vecBasis k i) * mapK n k (polyProj n k i p)) =
      ((vecBasis k).repr (coeff u p) i) • vecBasis k i := by
    intro i
    rw [coeff_C_mul, mapK, coeff_map, coeff_polyProj, mul_comm, ← Algebra.smul_def]
    rfl
  simp_rw [hterm]
  by_cases hu : u ∈ p.support
  · have hsub : ((vecBasis k).repr (coeff u p)).support ⊆ S :=
      Finset.subset_biUnion_of_mem (fun u => ((vecBasis k).repr (coeff u p)).support) hu
    rw [← Finset.sum_subset hsub]
    · have hrepr := (vecBasis k).linearCombination_repr (coeff u p)
      rw [Finsupp.linearCombination_apply, Finsupp.sum] at hrepr
      exact hrepr.symm
    · intro i _ hi
      rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
  · rw [MvPolynomial.notMem_support_iff.mp hu]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    simp
lemma mem_idealMap_iff (I : Ideal (MvPolynomial (Fin n) k))
    (p : MvPolynomial (Fin n) (Kext k)) :
    p ∈ Ideal.map (mapK n k) I ↔ ∀ i, polyProj n k i p ∈ I := by
  constructor
  · intro hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨a, ha, rfl⟩ i
      have h1 : mapK n k a = C (1 : Kext k) * mapK n k a := by simp
      rw [h1, polyProj_C_mul_mapK, smul_eq_C_mul]
      exact I.mul_mem_left _ ha
    · intro i; rw [polyProj_zero]; exact I.zero_mem
    · intro x y _ _ hx hy i
      rw [polyProj_add]; exact I.add_mem (hx i) (hy i)
    · intro r x _ hx i
      have hr : r = ∑ u ∈ r.support, C (coeff u r) * mapK n k (monomial u 1) := by
        conv_lhs => rw [r.as_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [mapK, map_monomial, map_one, C_mul_monomial, mul_one]
      obtain ⟨S, hS⟩ := eq_sum_polyProj n k x
      have hrx : r * x = ∑ u ∈ r.support, ∑ j ∈ S,
          C (coeff u r * vecBasis k j) * mapK n k (monomial u 1 * polyProj n k j x) := by
        conv_lhs => rw [hr, hS]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_mul]; ring
      rw [smul_eq_mul, hrx]
      have hproj_eq : polyProj n k i (∑ u ∈ r.support, ∑ j ∈ S,
          C (coeff u r * vecBasis k j) * mapK n k (monomial u 1 * polyProj n k j x)) =
          ∑ u ∈ r.support, ∑ j ∈ S,
            polyProj n k i (C (coeff u r * vecBasis k j) *
              mapK n k (monomial u 1 * polyProj n k j x)) := by
        ext v; simp only [coeff_polyProj, coeff_sum, map_sum]
      rw [hproj_eq]
      apply Ideal.sum_mem
      intro u _
      apply Ideal.sum_mem
      intro j _
      rw [polyProj_C_mul_mapK, smul_eq_C_mul]
      exact I.mul_mem_left _ (I.mul_mem_left _ (hx j))
  · intro hall
    obtain ⟨S, hS⟩ := eq_sum_polyProj n k p
    rw [hS]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hall i))
lemma isHomogeneous_mapK {p : MvPolynomial (Fin n) k} {d : ℕ} (hp : p.IsHomogeneous d) :
    (mapK n k p).IsHomogeneous d := by
  intro u hu
  rw [mapK, coeff_map] at hu
  have hne : coeff u p ≠ 0 := fun h => hu (by rw [h, map_zero])
  exact hp hne
lemma isHomogeneous_polyProj {i : Module.Basis.ofVectorSpaceIndex k (Kext k)}
    {p : MvPolynomial (Fin n) (Kext k)} {d : ℕ} (hp : p.IsHomogeneous d) :
    (polyProj n k i p).IsHomogeneous d := by
  intro u hu
  rw [coeff_polyProj] at hu
  have hne : coeff u p ≠ 0 := fun h => hu (by rw [h, map_zero])
  exact hp hne
lemma isHomogeneous_idealMap {I : Ideal (MvPolynomial (Fin n) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) k)) :
    (Ideal.map (mapK n k) I).IsHomogeneous (homogeneousSubmodule (Fin n) (Kext k)) := by
  intro e p hp
  change ((MvPolynomial.decomposition.decompose' p e : _) : MvPolynomial (Fin n) (Kext k)) ∈
    Ideal.map (mapK n k) I
  rw [MvPolynomial.decomposition.decompose'_apply, mem_idealMap_iff]
  intro i
  have hcomm : polyProj n k i (homogeneousComponent e p) =
      homogeneousComponent e (polyProj n k i p) := by
    ext u
    rw [coeff_polyProj, coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_polyProj]
    split_ifs <;> simp
  rw [hcomm]
  exact MvPolynomial.homogeneousComponent_mem_of_mem hI ((mem_idealMap_iff n k I p).mp hp i) e
lemma hilbertFunction_idealMap (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    hilbertFunction (Ideal.map (mapK n k) I) e = hilbertFunction I e := by
  unfold hilbertFunction
  let V : Submodule k (MvPolynomial (Fin n) k) :=
    Submodule.restrictScalars k I ⊓ homogeneousSubmodule (Fin n) k e
  let VK : Submodule (Kext k) (MvPolynomial (Fin n) (Kext k)) :=
    Submodule.restrictScalars (Kext k) (Ideal.map (mapK n k) I) ⊓
      homogeneousSubmodule (Fin n) (Kext k) e
  have : FiniteDimensional k V := by
    have hle : V ≤ homogPiece n k e := inf_le_right
    have : FiniteDimensional k (homogPiece n k e) := homogPiece_finiteDimensional e
    exact FiniteDimensional.of_injective (Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
  let bV := Module.finBasis k V
  let vK : Fin (Module.finrank k V) → VK := fun j =>
    ⟨mapK n k (bV j).1,
      ⟨Ideal.mem_map_of_mem _ (bV j).2.1,
       (mem_homogeneousSubmodule e _).mpr (isHomogeneous_mapK n k
         ((mem_homogeneousSubmodule e _).mp (bV j).2.2))⟩⟩
  have hlin : LinearIndependent (Kext k) vK := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hval := congrArg Subtype.val hc
    rw [ZeroMemClass.coe_zero, AddSubmonoidClass.coe_finsetSum] at hval
    have hcoord : ∀ i : Module.Basis.ofVectorSpaceIndex k (Kext k),
        (vecBasis k).coord i (c j) = 0 := by
      intro i
      have hproj : polyProj n k i (∑ r : Fin (Module.finrank k V), c r • (vK r).1) = 0 := by
        have h1 : (∑ r : Fin (Module.finrank k V), (c r • vK r : VK).1) = 0 := hval
        simpa [SetLike.val_smul, polyProj_zero] using congrArg (polyProj n k i) h1
      have hsum : polyProj n k i (∑ r : Fin (Module.finrank k V), c r • (vK r).1) =
          ∑ r : Fin (Module.finrank k V), ((vecBasis k).coord i (c r)) • (bV r).1 := by
        ext u
        simp only [coeff_polyProj, coeff_sum, coeff_smul, map_sum, vK]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [smul_eq_mul, mapK, coeff_map, mul_comm, ← Algebra.smul_def, map_smul,
          smul_eq_mul, smul_eq_mul, mul_comm]
      rw [hsum] at hproj
      have hV0 : (∑ r : Fin (Module.finrank k V), ((vecBasis k).coord i (c r)) • bV r : V) = 0 := by
        apply Subtype.ext
        rw [ZeroMemClass.coe_zero, AddSubmonoidClass.coe_finsetSum]
        simpa [SetLike.val_smul] using hproj
      exact (Fintype.linearIndependent_iff.mp bV.linearIndependent) _ hV0 j
    apply (vecBasis k).repr.injective
    ext i
    simpa using hcoord i
  have hspan : ⊤ ≤ Submodule.span (Kext k) (Set.range vK) := by
    intro x _
    obtain ⟨S, hS⟩ := eq_sum_polyProj n k x.1
    have hmem_V : ∀ i, polyProj n k i x.1 ∈ V := fun i =>
      ⟨(mem_idealMap_iff n k I x.1).mp x.2.1 i,
       (mem_homogeneousSubmodule e _).mpr (isHomogeneous_polyProj n k
         ((mem_homogeneousSubmodule e _).mp x.2.2))⟩
    have hx_eq : x = ∑ i ∈ S, (vecBasis k i) •
        ∑ j : Fin (Module.finrank k V),
          (algebraMap k (Kext k) (bV.repr ⟨polyProj n k i x.1, hmem_V i⟩ j)) • vK j := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      conv_lhs => rw [hS]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [SetLike.val_smul, AddSubmonoidClass.coe_finsetSum, Algebra.smul_def]
      congr 1
      have hrep := congrArg Subtype.val (bV.sum_repr ⟨polyProj n k i x.1, hmem_V i⟩)
      rw [AddSubmonoidClass.coe_finsetSum] at hrep
      dsimp only at hrep
      conv_lhs => rw [← hrep]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [SetLike.val_smul, SetLike.val_smul, smul_eq_C_mul, map_mul]
      change mapK n k (C (bV.repr ⟨polyProj n k i x.1, hmem_V i⟩ j)) * mapK n k (bV j).1 =
        (algebraMap k (Kext k) (bV.repr ⟨polyProj n k i x.1, hmem_V i⟩ j)) • mapK n k (bV j).1
      rw [Algebra.smul_def, mapK, MvPolynomial.map_C]
      rfl
    rw [hx_eq]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨j, rfl⟩
  let bVK : Module.Basis (Fin (Module.finrank k V)) (Kext k) VK :=
    Module.Basis.mk hlin hspan
  rw [Module.finrank_eq_card_basis bVK, Fintype.card_fin]
lemma isRegular_mapK {rs : List (MvPolynomial (Fin n) k)}
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) rs) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) (Kext k)) (rs.map (mapK n k)) := by
  rw [RingTheory.Sequence.isRegular_iff] at hreg ⊢
  refine ⟨?_, ?_⟩
  · rw [RingTheory.Sequence.isWeaklyRegular_iff_Fin] at hreg ⊢
    intro i
    have hi : i.1 < rs.length := by simpa using i.2
    have hstep := hreg.1 ⟨i.1, hi⟩
    have htake : (rs.map (mapK n k)).take i.1 = (rs.take i.1).map (mapK n k) :=
      (List.map_take).symm
    have hofList : Ideal.ofList ((rs.map (mapK n k)).take i.1) =
        Ideal.map (mapK n k) (Ideal.ofList (rs.take i.1)) := by
      rw [htake, Ideal.map_ofList]
    have hget : (rs.map (mapK n k))[i.1] = mapK n k (rs[i.1]) := List.getElem_map _
    intro x y hxy
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hsmul_top_K : ∀ (J : Ideal (MvPolynomial (Fin n) (Kext k))),
        (J • ⊤ : Submodule (MvPolynomial (Fin n) (Kext k)) (MvPolynomial (Fin n) (Kext k))) = J :=
      fun J => by simp
    have hsmul_top_k : ∀ (J : Ideal (MvPolynomial (Fin n) k)),
        (J • ⊤ : Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) = J :=
      fun J => by simp
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero, hsmul_top_K,
      hofList, mem_idealMap_iff]
    have hdiff : mapK n k rs[i.1] * (p - q) ∈
        Ideal.map (mapK n k) (Ideal.ofList (rs.take i.1)) := by
      have h1 : (Submodule.Quotient.mk (mapK n k rs[i.1] * (p - q)) :
          MvPolynomial (Fin n) (Kext k) ⧸
            (Ideal.ofList ((rs.map (mapK n k)).take i.1) • ⊤ :
              Submodule (MvPolynomial (Fin n) (Kext k)) (MvPolynomial (Fin n) (Kext k)))) = 0 := by
        rw [mul_sub, Submodule.Quotient.mk_sub, sub_eq_zero]
        have hxy' : (mapK n k rs[i.1]) • (Submodule.Quotient.mk p :
            MvPolynomial (Fin n) (Kext k) ⧸
              (Ideal.ofList ((rs.map (mapK n k)).take i.1) • ⊤ :
                Submodule (MvPolynomial (Fin n) (Kext k)) (MvPolynomial (Fin n) (Kext k)))) =
            (mapK n k rs[i.1]) • Submodule.Quotient.mk q := by
          dsimp only at hxy
          change (List.map (mapK n k) rs)[i.1] • _ = (List.map (mapK n k) rs)[i.1] • _ at hxy
          rw [hget] at hxy
          exact hxy
        exact hxy'
      rwa [Submodule.Quotient.mk_eq_zero, hsmul_top_K, hofList] at h1
    intro j
    have hj := (mem_idealMap_iff n k _ _).mp hdiff j
    rw [polyProj_mapK_mul] at hj
    have hstep' : rs[i.1] • (Submodule.Quotient.mk (polyProj n k j (p - q)) :
        MvPolynomial (Fin n) k ⧸ (Ideal.ofList (rs.take i.1) • ⊤ :
          Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k))) =
        rs[i.1] • 0 := by
      rw [smul_zero]
      change Submodule.Quotient.mk (rs[i.1] * polyProj n k j (p - q)) = 0
      rw [Submodule.Quotient.mk_eq_zero, hsmul_top_k]
      exact hj
    have hz := hstep hstep'
    rwa [Submodule.Quotient.mk_eq_zero, hsmul_top_k] at hz
  · intro htop
    have hsmul_top_K : (Ideal.ofList (rs.map (mapK n k)) • ⊤ :
        Submodule (MvPolynomial (Fin n) (Kext k)) (MvPolynomial (Fin n) (Kext k))) =
        Ideal.ofList (rs.map (mapK n k)) := by simp
    have hsmul_top_k : (Ideal.ofList rs • ⊤ :
        Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) =
        Ideal.ofList rs := by simp
    rw [hsmul_top_K, ← Ideal.map_ofList] at htop
    have h1 : (1 : MvPolynomial (Fin n) (Kext k)) ∈ Ideal.map (mapK n k) (Ideal.ofList rs) := by
      rw [← htop]; exact Submodule.mem_top
    have hall := (mem_idealMap_iff n k _ 1).mp h1
    have h1_ne : (1 : Kext k) ≠ 0 := one_ne_zero
    have hex : ∃ i, (vecBasis k).coord i (1 : Kext k) ≠ 0 := by
      by_contra h0; push Not at h0
      apply h1_ne
      apply (vecBasis k).repr.injective
      ext i; simpa using h0 i
    obtain ⟨i, hi⟩ := hex
    have hproj1 : polyProj n k i 1 = C ((vecBasis k).coord i 1) := by
      have := polyProj_C_mul_mapK n k i 1 1
      simpa [Algebra.smul_def] using this
    have hCmem : C ((vecBasis k).coord i 1) ∈ Ideal.ofList rs := hproj1 ▸ hall i
    have hunit : IsUnit (C ((vecBasis k).coord i 1) : MvPolynomial (Fin n) k) :=
      (isUnit_iff_ne_zero.mpr hi).map C
    have htop_k : Ideal.ofList rs = ⊤ := Ideal.eq_top_of_isUnit_mem _ hCmem hunit
    exact hreg.2 (by rw [hsmul_top_k, htop_k])
lemma lex_descend_from_ratFunc {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (hK : ∃ LK : Ideal (MvPolynomial (Fin n) (Kext k)), IsLexIdeal LK ∧
      ∀ e, hilbertFunction (Ideal.map (mapK n k) I) e =
        hilbertFunction (LK + purePowersIdeal hc d) e) :
    ∃ L : Ideal (MvPolynomial (Fin n) k), IsLexIdeal L ∧
      ∀ e, hilbertFunction I e = hilbertFunction (L + purePowersIdeal hc d) e := by
  classical
  obtain ⟨LK, ⟨⟨S0, hS0⟩, hlexK⟩, hhf⟩ := hK
  let S : Set (Fin n →₀ ℕ) := { u | monomial u (1 : Kext k) ∈ LK }
  have hS_closed : ∀ u ∈ S, ∀ i : Fin n, u + Finsupp.single i 1 ∈ S := by
    intro u hu i
    change monomial (u + Finsupp.single i 1) (1 : Kext k) ∈ LK
    have heq : monomial (u + Finsupp.single i 1) (1 : Kext k) = X i * monomial u 1 := by
      rw [X, monomial_mul, one_mul, add_comm]
    rw [heq]; exact LK.mul_mem_left _ hu
  let L : Ideal (MvPolynomial (Fin n) k) := Ideal.span ((fun u => monomial u (1 : k)) '' S)
  have hL_lex : IsLexIdeal L := by
    refine ⟨⟨S, rfl⟩, fun u v huv hlt hvL => ?_⟩
    rw [mem_monomialIdeal_iff_support hS_closed] at hvL ⊢
    intro w hw
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hw
    rw [hw]
    have hvS : v ∈ S := hvL v (by
      rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton])
    exact hlexK u v huv hlt hvS
  have hmapL : Ideal.map (mapK n k) L = LK := by
    apply le_antisymm
    · rw [Ideal.map_span]
      rw [Ideal.span_le]
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      dsimp only [S] at hu
      simpa [mapK] using hu
    · rw [hS0, Ideal.span_le]
      rintro _ ⟨u, hu, rfl⟩
      have huS : u ∈ S := by
        change monomial u (1 : Kext k) ∈ LK
        rw [hS0]; exact Ideal.subset_span ⟨u, hu, rfl⟩
      have hmap_u : monomial u (1 : Kext k) = mapK n k (monomial u (1 : k)) := by simp [mapK]
      dsimp only
      rw [hmap_u]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨u, huS, rfl⟩)
  have hmapP : Ideal.map (mapK n k) (purePowersIdeal hc d) = purePowersIdeal hc d := by
    unfold purePowersIdeal
    rw [Ideal.map_span]
    congr 1; ext p; simp [mapK]
  refine ⟨L, hL_lex, fun e => ?_⟩
  rw [← hilbertFunction_idealMap n k I e, hhf e, ← hilbertFunction_idealMap n k (L + purePowersIdeal hc d) e]
  have hsum : Ideal.map (mapK n k) (L + purePowersIdeal hc d) = LK + purePowersIdeal hc d := by
    rw [Submodule.add_eq_sup, Submodule.add_eq_sup, Ideal.map_sup, hmapL, hmapP]
  rw [hsum]
end BaseChange
lemma isHomogeneous_aeval_of_deg_one {m : ℕ}
    (g : Fin n → MvPolynomial (Fin m) k) (hg : ∀ i, (g i).IsHomogeneous 1)
    {p : MvPolynomial (Fin n) k} {d : ℕ} (hp : p.IsHomogeneous d) :
    (MvPolynomial.aeval g p).IsHomogeneous d := by
  rw [p.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro u hu
  have hdeg : u.degree = d := by
    have := hp (MvPolynomial.mem_support_iff.mp hu)
    rwa [weight_one_eq_deg] at this
  rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_eq_C_mul, mul_one]
  have hC : (C (coeff u p) : MvPolynomial (Fin m) k).IsHomogeneous 0 := isHomogeneous_C _ _
  have hprod : (u.prod fun i a => g i ^ a).IsHomogeneous u.degree := by
    rw [Finsupp.prod, Finsupp.degree]
    have : ∀ s : Finset (Fin n),
        (∏ i ∈ s, g i ^ u i).IsHomogeneous (∑ i ∈ s, u i) := by
      intro s
      induction s using Finset.induction with
      | empty => simpa using isHomogeneous_one (Fin m) k
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha]
        have hpow : (g a ^ u a).IsHomogeneous (u a) := by
          simpa [mul_one] using (hg a).pow (u a)
        exact hpow.mul ih
    exact this u.support
  have hmul := hC.mul hprod
  rw [zero_add, hdeg] at hmul
  exact hmul
set_option maxHeartbeats 800000 in
theorem exists_graded_algEquiv_map_eq {ℓ : MvPolynomial (Fin n) k}
    (hℓ_hom : ℓ.IsHomogeneous 1) (hℓ_ne : ℓ ≠ 0) (t : Fin n) :
    ∃ Ψ : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k,
      (∀ p d, p.IsHomogeneous d → (Ψ p).IsHomogeneous d) ∧
      (∀ p d, p.IsHomogeneous d → (Ψ.symm p).IsHomogeneous d) ∧
      Ψ ℓ = X t := by
  classical
  let c : Fin n → k := fun i => coeff (Finsupp.single i 1) ℓ
  have hℓ_eq : ℓ = ∑ i : Fin n, C (c i) * X i := by
    ext u
    rw [coeff_sum]
    by_cases hdeg : u.degree = 1
    · have hex : ∃ i : Fin n, u = Finsupp.single i 1 := by
        have hne : u.support.Nonempty := by
          rw [Finsupp.support_nonempty_iff]
          intro h0; rw [h0, map_zero] at hdeg; omega
        obtain ⟨i, hi⟩ := hne
        refine ⟨i, ?_⟩
        have hui : 1 ≤ u i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
        have hsum : ∑ j : Fin n, u j = 1 := by rwa [← Finsupp.degree_eq_sum]
        ext j
        by_cases hji : j = i
        · subst hji
          have hle : u j ≤ 1 := by
            rw [← hsum]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
          simp; omega
        · have hsum2 : u i + u j ≤ ∑ r : Fin n, u r := by
            rw [← Finset.sum_pair (Ne.symm hji)]
            exact Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
          rw [Finsupp.single_eq_of_ne hji]; omega
      obtain ⟨i, rfl⟩ := hex
      rw [Finset.sum_eq_single i]
      · simp [c, coeff_C_mul, coeff_X]
      · intro j _ hji
        have hne : Finsupp.single j (1 : ℕ) ≠ Finsupp.single i 1 := by
          intro h
          have h1 := congrArg (fun f : Fin n →₀ ℕ => f j) h
          rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hji] at h1
          exact one_ne_zero h1
        rw [coeff_C_mul, coeff_X, if_neg hne, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [hℓ_hom.coeff_eq_zero hdeg]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [coeff_C_mul, coeff_X, if_neg (fun h => hdeg (by rw [← h, Finsupp.degree_single])),
        mul_zero]
  have hex_s : ∃ s : Fin n, c s ≠ 0 := by
    by_contra hall; push Not at hall
    apply hℓ_ne
    rw [hℓ_eq]
    exact Finset.sum_eq_zero fun i _ => by simp [hall i]
  obtain ⟨s, hs⟩ := hex_s
  let fwd : Fin n → MvPolynomial (Fin n) k := fun j => if j = s then ℓ else X j
  let bwd : Fin n → MvPolynomial (Fin n) k := fun j =>
    if j = s then C (c s)⁻¹ * (X s - ∑ i ∈ Finset.univ.erase s, C (c i) * X i) else X j
  have hfwd_hom : ∀ j, (fwd j).IsHomogeneous 1 := by
    intro j; dsimp only [fwd]; split_ifs
    · exact hℓ_hom
    · exact isHomogeneous_X k j
  have hbwd_hom : ∀ j, (bwd j).IsHomogeneous 1 := by
    intro j; dsimp only [bwd]; split_ifs
    · have hsub : (X s - ∑ i ∈ Finset.univ.erase s, C (c i) * X i :
          MvPolynomial (Fin n) k).IsHomogeneous 1 := by
        apply IsHomogeneous.sub (isHomogeneous_X k s)
        apply IsHomogeneous.sum
        intro i _
        simpa using (isHomogeneous_C (Fin n) (c i)).mul (isHomogeneous_X k i)
      simpa using (isHomogeneous_C (Fin n) (c s)⁻¹).mul hsub
    · exact isHomogeneous_X k j
  let Φ₁_to : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k := MvPolynomial.aeval fwd
  let Φ₁_inv : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k := MvPolynomial.aeval bwd
  have hcomp1 : Φ₁_inv.comp Φ₁_to = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, AlgHom.id_apply, Φ₁_to, Φ₁_inv, aeval_X, fwd]
    by_cases hjs : j = s
    · subst hjs
      rw [if_pos rfl, hℓ_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), map_add, map_mul,
        aeval_C, aeval_X, map_sum]
      simp only [bwd, if_pos rfl]
      have hsum_er : ∑ i ∈ Finset.univ.erase j, (MvPolynomial.aeval bwd) (C (c i) * X i) =
          ∑ i ∈ Finset.univ.erase j, C (c i) * X i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hij : i ≠ j := (Finset.mem_erase.mp hi).1
        rw [map_mul, aeval_C, aeval_X, ← C_eq_algebraMap]
        dsimp only [bwd]; rw [if_neg hij]
      rw [hsum_er, ← mul_assoc, ← C_eq_algebraMap, ← C_mul, mul_inv_cancel₀ hs, map_one, one_mul,
        sub_add_cancel]
    · rw [if_neg hjs, aeval_X]
      dsimp only [bwd]; rw [if_neg hjs]
  have hcomp2 : Φ₁_to.comp Φ₁_inv = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, AlgHom.id_apply, Φ₁_to, Φ₁_inv, aeval_X, bwd]
    by_cases hjs : j = s
    · subst hjs
      rw [if_pos rfl, map_mul, aeval_C, map_sub, aeval_X, map_sum]
      simp only [fwd, if_pos rfl]
      have hsum_er : ∑ i ∈ Finset.univ.erase j, (MvPolynomial.aeval fwd) (C (c i) * X i) =
          ∑ i ∈ Finset.univ.erase j, C (c i) * X i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hij : i ≠ j := (Finset.mem_erase.mp hi).1
        rw [map_mul, aeval_C, aeval_X, ← C_eq_algebraMap]
        dsimp only [fwd]; rw [if_neg hij]
      rw [hsum_er, hℓ_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_sub_cancel_right,
        ← mul_assoc, ← C_eq_algebraMap, ← C_mul, inv_mul_cancel₀ hs, map_one, one_mul]
    · rw [if_neg hjs, aeval_X]
      dsimp only [fwd]; rw [if_neg hjs]
  let Φ₁ : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k :=
    AlgEquiv.ofAlgHom Φ₁_inv Φ₁_to hcomp1 hcomp2
  let σ := Equiv.swap s t
  let Φ₂ : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k := MvPolynomial.renameEquiv k σ
  let Ψ : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k := Φ₁.trans Φ₂
  have hΦ₂_hom : ∀ (e : Equiv.Perm (Fin n)) (p : MvPolynomial (Fin n) k) (d : ℕ),
      p.IsHomogeneous d → (MvPolynomial.rename e p).IsHomogeneous d := by
    intro e p d hp
    have : MvPolynomial.rename e p = MvPolynomial.aeval (fun i => X (e i)) p := by
      rw [MvPolynomial.rename_eq_aeval]; rfl
    rw [this]
    exact isHomogeneous_aeval_of_deg_one (fun i => X (e i)) (fun i => isHomogeneous_X k (e i)) hp
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · intro p d hp
    rw [AlgEquiv.trans_apply]
    change (MvPolynomial.rename σ (Φ₁ p)).IsHomogeneous d
    have hΦ₁p : Φ₁ p = MvPolynomial.aeval bwd p := rfl
    rw [hΦ₁p]
    exact hΦ₂_hom σ _ d (isHomogeneous_aeval_of_deg_one bwd hbwd_hom hp)
  · intro p d hp
    rw [AlgEquiv.symm_trans_apply]
    change (MvPolynomial.aeval fwd (Φ₂.symm p)).IsHomogeneous d
    have hΦ₂p : Φ₂.symm p = MvPolynomial.rename σ.symm p := rfl
    rw [hΦ₂p]
    exact isHomogeneous_aeval_of_deg_one fwd hfwd_hom (hΦ₂_hom σ.symm p d hp)
  · have hΦ₁_ℓ : Φ₁ ℓ = X s := by
      have hsym : Φ₁.symm (X s) = ℓ := by
        change MvPolynomial.aeval fwd (X s) = ℓ
        rw [MvPolynomial.aeval_X]; dsimp only [fwd]; rw [if_pos rfl]
      rw [← hsym, Φ₁.apply_symm_apply]
    rw [AlgEquiv.trans_apply, hΦ₁_ℓ]
    change MvPolynomial.rename σ (X s) = X t
    rw [MvPolynomial.rename_X, Equiv.swap_apply_left]
lemma graded_algEquiv_isHomogeneous_map
    (Ψ : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k)
    (hΨ : ∀ p d, p.IsHomogeneous d → (Ψ p).IsHomogeneous d)
    (_hΨ_inv : ∀ p d, p.IsHomogeneous d → (Ψ.symm p).IsHomogeneous d)
    {I : Ideal (MvPolynomial (Fin n) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) k)) :
    (Ideal.map Ψ.toRingHom I).IsHomogeneous (homogeneousSubmodule (Fin n) k) := by
  have hcomm : ∀ p e, homogeneousComponent e (Ψ p) = Ψ (homogeneousComponent e p) := by
    intro p e
    have h1 : homogeneousComponent e (Ψ p) =
        homogeneousComponent e (∑ i ∈ Finset.range (p.totalDegree + 1),
          Ψ (homogeneousComponent i p)) := by
      congr 1
      rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
    rw [h1, map_sum]
    by_cases he : e < p.totalDegree + 1
    · rw [Finset.sum_eq_single e]
      · exact homogeneousComponent_eq_self (hΨ _ e (homogeneousComponent_isHomogeneous e p))
      · intro i _ hie
        exact homogeneousComponent_eq_zero_of_ne
          (hΨ _ i (homogeneousComponent_isHomogeneous i p)) hie
      · intro h; exact absurd (Finset.mem_range.mpr he) h
    · have h0 : homogeneousComponent e p = 0 :=
        homogeneousComponent_eq_zero e p (by omega)
      rw [h0, map_zero]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi_lt : i < p.totalDegree + 1 := Finset.mem_range.mp hi
      exact homogeneousComponent_eq_zero_of_ne
        (hΨ _ i (homogeneousComponent_isHomogeneous i p)) (by omega)
  intro e q hq
  change ((MvPolynomial.decomposition.decompose' q e : _) : MvPolynomial (Fin n) k) ∈
    Ideal.map Ψ.toRingHom I
  rw [MvPolynomial.decomposition.decompose'_apply]
  have hmem : Ψ.symm q ∈ I := by
    rw [Ideal.mem_map_iff_of_surjective (f := Ψ.toRingHom) Ψ.surjective] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    simpa using ha
  have hcomp : homogeneousComponent e (Ψ.symm q) ∈ I :=
    MvPolynomial.homogeneousComponent_mem_of_mem hI hmem e
  have hq_eq : homogeneousComponent e q = Ψ (homogeneousComponent e (Ψ.symm q)) := by
    rw [← hcomm (Ψ.symm q) e, Ψ.apply_symm_apply]
  rw [hq_eq]
  exact Ideal.mem_map_of_mem _ hcomp
lemma graded_algEquiv_hilbertFunction
    (Ψ : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k)
    (hΨ : ∀ p d, p.IsHomogeneous d → (Ψ p).IsHomogeneous d)
    (hΨ_inv : ∀ p d, p.IsHomogeneous d → (Ψ.symm p).IsHomogeneous d)
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    hilbertFunction (Ideal.map Ψ.toRingHom I) e = hilbertFunction I e := by
  unfold hilbertFunction
  let eL : ↥(Submodule.restrictScalars k I ⊓ homogeneousSubmodule (Fin n) k e) ≃ₗ[k]
      ↥(Submodule.restrictScalars k (Ideal.map Ψ.toRingHom I) ⊓
        homogeneousSubmodule (Fin n) k e) := {
    toFun := fun x => ⟨Ψ x.1,
      ⟨Ideal.mem_map_of_mem _ x.2.1,
       (mem_homogeneousSubmodule e _).mpr (hΨ _ e ((mem_homogeneousSubmodule e _).mp x.2.2))⟩⟩
    invFun := fun y => ⟨Ψ.symm y.1,
      ⟨by
        have hy := y.2.1
        change y.1 ∈ Ideal.map Ψ.toRingHom I at hy
        rw [Ideal.mem_map_iff_of_surjective (f := Ψ.toRingHom) Ψ.surjective] at hy
        obtain ⟨a, ha, ha_eq⟩ := hy
        have hsy : Ψ.symm y.1 = a := by
          rw [← ha_eq]; exact Ψ.symm_apply_apply a
        rw [hsy]; exact ha,
       (mem_homogeneousSubmodule e _).mpr (hΨ_inv _ e ((mem_homogeneousSubmodule e _).mp y.2.2))⟩⟩
    left_inv := fun x => Subtype.ext (Ψ.symm_apply_apply x.1)
    right_inv := fun y => Subtype.ext (Ψ.apply_symm_apply y.1)
    map_add' := fun x y => Subtype.ext (map_add Ψ x.1 y.1)
    map_smul' := fun c x => Subtype.ext (map_smul Ψ c x.1)
  }
  exact (LinearEquiv.finrank_eq eL).symm
lemma graded_algEquiv_isRegular
    (Ψ : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k)
    {rs : List (MvPolynomial (Fin n) k)}
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) rs) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (rs.map Ψ) := by
  refine (Ψ.toAddEquiv.isRegular_congr ?_).mp hreg
  rw [List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun r _ x => by simp [smul_eq_mul]
section ElimVar
noncomputable def evZero (n : ℕ) (k : Type*) [Field k] :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin n) k :=
  MvPolynomial.aeval (Fin.cases (0 : MvPolynomial (Fin n) k) (fun i => X i))
noncomputable def embSucc (n : ℕ) (k : Type*) [Field k] :
    MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  MvPolynomial.rename Fin.succ
lemma evZero_X_zero : evZero n k (X 0) = 0 := by simp [evZero]
lemma evZero_X_succ (i : Fin n) : evZero n k (X i.succ) = X i := by simp [evZero]
lemma embSucc_X (i : Fin n) : embSucc n k (X i) = X i.succ := by simp [embSucc]
lemma evZero_comp_embSucc : (evZero n k).comp (embSucc n k) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext; intro i; simp [evZero, embSucc]
lemma evZero_embSucc (p : MvPolynomial (Fin n) k) : evZero n k (embSucc n k p) = p :=
  AlgHom.congr_fun (evZero_comp_embSucc (n := n) (k := k)) p
lemma evZero_surjective : Function.Surjective (evZero n k) :=
  Function.RightInverse.surjective (evZero_embSucc (n := n) (k := k))
lemma isHomogeneous_evZero {p : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hp : p.IsHomogeneous d) :
    (evZero n k p).IsHomogeneous d := by
  apply isHomogeneous_aeval_of_deg_one _ _ hp
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact isHomogeneous_zero _ _ _
  · exact isHomogeneous_X k i
lemma isHomogeneous_embSucc {p : MvPolynomial (Fin n) k} {d : ℕ} (hp : p.IsHomogeneous d) :
    (embSucc n k p).IsHomogeneous d := by
  have : embSucc n k p = MvPolynomial.aeval (fun i : Fin n => (X i.succ : MvPolynomial (Fin (n + 1)) k)) p := by
    simp [embSucc, MvPolynomial.rename_eq_aeval]; rfl
  rw [this]
  exact isHomogeneous_aeval_of_deg_one _ (fun i => isHomogeneous_X k i.succ) hp
lemma sub_embSucc_evZero_mem (p : MvPolynomial (Fin (n + 1)) k) :
    p - embSucc n k (evZero n k p) ∈ Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [evZero, embSucc]
  | add p q hp hq =>
    have : p + q - embSucc n k (evZero n k (p + q)) =
        (p - embSucc n k (evZero n k p)) + (q - embSucc n k (evZero n k q)) := by
      simp only [map_add]; ring
    rw [this]; exact Ideal.add_mem _ hp hq
  | mul_X p j hp =>
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [map_mul, evZero_X_zero, mul_zero, map_zero, sub_zero]
      exact Ideal.mul_mem_left _ p (Ideal.subset_span (Set.mem_singleton _))
    · have : p * X i.succ - embSucc n k (evZero n k (p * X i.succ)) =
          (p - embSucc n k (evZero n k p)) * X i.succ := by
        rw [map_mul, evZero_X_succ, map_mul, embSucc_X]; ring
      rw [this]; exact Ideal.mul_mem_right _ _ hp
lemma mem_ker_evZero_iff (p : MvPolynomial (Fin (n + 1)) k) :
    evZero n k p = 0 ↔ p ∈ Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k)) := by
  constructor
  · intro h0
    have h := sub_embSucc_evZero_mem p
    simpa [h0] using h
  · intro hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro _ rfl; exact evZero_X_zero
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro r x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]
lemma isHomogeneous_map_evZero {I : Ideal (MvPolynomial (Fin (n + 1)) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k))
    (_hX0 : (X 0 : MvPolynomial (Fin (n + 1)) k) ∈ I) :
    (Ideal.map (evZero n k).toRingHom I).IsHomogeneous (homogeneousSubmodule (Fin n) k) := by
  have hcomm : ∀ p e, homogeneousComponent e (evZero n k p) =
      evZero n k (homogeneousComponent e p) := by
    intro p e
    have h1 : homogeneousComponent e (evZero n k p) =
        homogeneousComponent e (∑ i ∈ Finset.range (p.totalDegree + 1),
          evZero n k (homogeneousComponent i p)) := by
      congr 1; rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
    rw [h1, map_sum]
    by_cases he : e < p.totalDegree + 1
    · rw [Finset.sum_eq_single e]
      · exact homogeneousComponent_eq_self (isHomogeneous_evZero (homogeneousComponent_isHomogeneous e p))
      · intro i _ hie
        exact homogeneousComponent_eq_zero_of_ne
          (isHomogeneous_evZero (homogeneousComponent_isHomogeneous i p)) hie
      · intro h; exact absurd (Finset.mem_range.mpr he) h
    · rw [homogeneousComponent_eq_zero e p (by omega), map_zero]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi_lt := Finset.mem_range.mp hi
      exact homogeneousComponent_eq_zero_of_ne
        (isHomogeneous_evZero (homogeneousComponent_isHomogeneous i p)) (by omega)
  intro e q hq
  change ((MvPolynomial.decomposition.decompose' q e : _) : MvPolynomial (Fin n) k) ∈
    Ideal.map (evZero n k).toRingHom I
  rw [MvPolynomial.decomposition.decompose'_apply]
  rw [Ideal.mem_map_iff_of_surjective (f := (evZero n k).toRingHom) evZero_surjective] at hq
  obtain ⟨p, hpI, rfl⟩ := hq
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [hcomm]
  exact Ideal.mem_map_of_mem _ (MvPolynomial.homogeneousComponent_mem_of_mem hI hpI e)
lemma quotientHF_map_evZero {I : Ideal (MvPolynomial (Fin (n + 1)) k)}
    (hX0 : (X 0 : MvPolynomial (Fin (n + 1)) k) ∈ I) (e : ℕ) :
    quotientHF (Ideal.map (evZero n k).toRingHom I) e = quotientHF I e := by
  have hX0_le : Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k)) ≤ I :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hX0)
  have hiff : ∀ p : MvPolynomial (Fin (n + 1)) k,
      p ∈ I ↔ evZero n k p ∈ Ideal.map (evZero n k).toRingHom I := by
    intro p
    constructor
    · exact fun hp => Ideal.mem_map_of_mem _ hp
    · intro hp
      rw [Ideal.mem_map_iff_of_surjective (f := (evZero n k).toRingHom) evZero_surjective] at hp
      obtain ⟨q, hq, heq⟩ := hp
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at heq
      have hsub : p - q ∈ Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k)) :=
        (mem_ker_evZero_iff (p - q)).mp (by rw [map_sub, heq, sub_self])
      simpa using I.add_mem hq (hX0_le hsub)
  let f : homogPiece (n + 1) k e →ₗ[k] homogPiece n k e := {
    toFun := fun x => ⟨evZero n k x.1,
      (mem_homogeneousSubmodule e _).mpr (isHomogeneous_evZero ((mem_homogeneousSubmodule e _).mp x.2))⟩
    map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1)
    map_smul' := fun c x => Subtype.ext (map_smul _ c x.1)
  }
  let g : homogPiece n k e →ₗ[k] homogPiece (n + 1) k e := {
    toFun := fun x => ⟨embSucc n k x.1,
      (mem_homogeneousSubmodule e _).mpr (isHomogeneous_embSucc ((mem_homogeneousSubmodule e _).mp x.2))⟩
    map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1)
    map_smul' := fun c x => Subtype.ext (map_smul _ c x.1)
  }
  let φ : (homogPiece (n + 1) k e ⧸ idealSub I e) →ₗ[k]
      (homogPiece n k e ⧸ idealSub (Ideal.map (evZero n k).toRingHom I) e) :=
    Submodule.mapQ (idealSub I e) (idealSub (Ideal.map (evZero n k).toRingHom I) e) f (by
      intro x hx; rw [Submodule.mem_comap, mem_idealSub]
      exact (hiff x.1).mp ((mem_idealSub x).mp hx))
  let ψ : (homogPiece n k e ⧸ idealSub (Ideal.map (evZero n k).toRingHom I) e) →ₗ[k]
      (homogPiece (n + 1) k e ⧸ idealSub I e) :=
    Submodule.mapQ (idealSub (Ideal.map (evZero n k).toRingHom I) e) (idealSub I e) g (by
      intro x hx; rw [Submodule.mem_comap, mem_idealSub, hiff]
      change evZero n k (embSucc n k x.1) ∈ _
      rw [evZero_embSucc]; exact (mem_idealSub x).mp hx)
  have hEquiv : (homogPiece (n + 1) k e ⧸ idealSub I e) ≃ₗ[k]
      (homogPiece n k e ⧸ idealSub (Ideal.map (evZero n k).toRingHom I) e) :=
    LinearEquiv.ofLinearMap φ ψ
      (by
        apply LinearMap.ext; intro y
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        change Submodule.Quotient.mk ⟨evZero n k (embSucc n k x.1), _⟩ = Submodule.Quotient.mk x
        congr 1; exact Subtype.ext (evZero_embSucc x.1))
      (by
        apply LinearMap.ext; intro y
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        change Submodule.Quotient.mk ⟨embSucc n k (evZero n k x.1), _⟩ = Submodule.Quotient.mk x
        rw [Submodule.Quotient.eq, mem_idealSub]
        have h := sub_embSucc_evZero_mem x.1
        simpa using I.neg_mem (hX0_le h))
  exact (LinearEquiv.finrank_eq hEquiv).symm
lemma isRegular_evZero_of_cons {rs : List (MvPolynomial (Fin (n + 1)) k)}
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) k) (X 0 :: rs)) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (rs.map (evZero n k)) := by
  rw [RingTheory.Sequence.isRegular_cons_iff'] at hreg
  have hsmul : ((X 0 : MvPolynomial (Fin (n + 1)) k) • ⊤ :
      Submodule (MvPolynomial (Fin (n + 1)) k) (MvPolynomial (Fin (n + 1)) k)) =
      Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k)) := by
    ext p
    simp only [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton,
      dvd_iff_exists_eq_mul_right, smul_eq_mul, Submodule.mem_top, true_and, eq_comm]
  let e1 : QuotSMulTop (X 0 : MvPolynomial (Fin (n + 1)) k)
      (MvPolynomial (Fin (n + 1)) k) ≃ₗ[MvPolynomial (Fin (n + 1)) k]
      (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k))) :=
    Submodule.quotEquivOfEq
      ((X 0 : MvPolynomial (Fin (n + 1)) k) • ⊤ :
        Submodule (MvPolynomial (Fin (n + 1)) k) (MvPolynomial (Fin (n + 1)) k))
      (Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k))) hsmul
  let kerEq : RingHom.ker (evZero n k).toRingHom = Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k)) := by
    ext p; exact mem_ker_evZero_iff p
  let e2 : (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k))) ≃+*
      MvPolynomial (Fin n) k :=
    (Ideal.quotEquivOfEq kerEq.symm).trans
      (RingHom.quotientKerEquivOfSurjective (f := (evZero n k).toRingHom) evZero_surjective)
  let eAdd : QuotSMulTop (X 0 : MvPolynomial (Fin (n + 1)) k)
      (MvPolynomial (Fin (n + 1)) k) ≃+ MvPolynomial (Fin n) k :=
    e1.toAddEquiv.trans e2.toAddEquiv
  have he_mk : ∀ p : MvPolynomial (Fin (n + 1)) k,
      eAdd (Submodule.Quotient.mk p) = evZero n k p := fun _ => rfl
  refine (eAdd.isRegular_congr ?_).mp hreg.2
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun r _ x => ?_
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change eAdd (Submodule.Quotient.mk (r * p)) = evZero n k r * eAdd (Submodule.Quotient.mk p)
  rw [he_mk, he_mk, map_mul]
lemma isLexIdeal_lift_X0 {Lbar : Ideal (MvPolynomial (Fin n) k)} (hL : IsLexIdeal Lbar) :
    IsLexIdeal (Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k)) ⊔
      Ideal.map (embSucc n k).toRingHom Lbar) := by
  let L := Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k)) ⊔
    Ideal.map (embSucc n k).toRingHom Lbar
  obtain ⟨⟨Sbar, hSbar⟩, hlex_bar⟩ := hL
  have hS_mon : IsMonomialIdeal L := by
    refine ⟨{Finsupp.single 0 1} ∪ (fun u => Finsupp.mapDomain Fin.succ u) '' Sbar, ?_⟩
    dsimp only [L]
    rw [Set.image_union, Set.image_singleton, Ideal.span_union]
    congr 1
    rw [hSbar, Ideal.map_span]
    congr 1; ext p
    simp only [Set.mem_image, exists_exists_and_eq_and]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, by simp [embSucc, rename_monomial]⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, by simp [embSucc, rename_monomial]⟩
  refine ⟨hS_mon, fun u v huv hlt hvL => ?_⟩
  by_cases hu0 : 0 < u 0
  · have hexp : u = (u - Finsupp.single 0 1) + Finsupp.single 0 1 := by
      ext j
      by_cases hj : j = 0
      · subst hj; simp; omega
      · simp [Finsupp.single_eq_of_ne hj]
    have hdiv : monomial u (1 : k) = monomial (u - Finsupp.single 0 1) 1 * X 0 := by
      rw [X, monomial_mul, mul_one, ← hexp]
    rw [hdiv]
    exact Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)))
  · have hu0_eq : u 0 = 0 := by omega
    have hv0_eq : v 0 = 0 := by
      rw [Finsupp.Lex.lt_iff] at hlt
      obtain ⟨j, hlt_j, hj⟩ := hlt
      simp only [ofLex_toLex] at hlt_j hj
      by_cases hj0 : j = 0
      · subst hj0; omega
      · have h0lt : (0 : Fin (n + 1)) < j := Fin.pos_iff_ne_zero.mpr hj0
        have := hlt_j 0 h0lt; omega
    let u' : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => u i.succ)
    let v' : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => v i.succ)
    have hu_eq : Finsupp.mapDomain Fin.succ u' = u := by
      ext j
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [hu0_eq]; exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)
      · rw [Finsupp.mapDomain_apply (Fin.succ_injective n)]; rfl
    have hv_eq : Finsupp.mapDomain Fin.succ v' = v := by
      ext j
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [hv0_eq]; exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)
      · rw [Finsupp.mapDomain_apply (Fin.succ_injective n)]; rfl
    have huv' : u'.degree = v'.degree := by
      have h1 : (Finsupp.mapDomain Fin.succ u').degree = u'.degree := by
        rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succ,
          Finsupp.mapDomain_of_notMem_range _ _ (by simp), zero_add]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finsupp.mapDomain_apply (Fin.succ_injective n)]
      have h2 : (Finsupp.mapDomain Fin.succ v').degree = v'.degree := by
        rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succ,
          Finsupp.mapDomain_of_notMem_range _ _ (by simp), zero_add]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finsupp.mapDomain_apply (Fin.succ_injective n)]
      rw [← h1, ← h2, hu_eq, hv_eq, huv]
    have hlt' : toLex v' < toLex u' := by
      rw [Finsupp.Lex.lt_iff] at hlt ⊢
      obtain ⟨j, hlt_j, hj⟩ := hlt
      simp only [ofLex_toLex] at hlt_j hj ⊢
      cases j using Fin.cases with
      | zero => omega
      | succ i =>
        refine ⟨i, fun r hr => ?_, hj⟩
        exact hlt_j r.succ (Fin.succ_lt_succ_iff.mpr hr)
    have hv'_mem : monomial v' (1 : k) ∈ Lbar := by
      have hev := Ideal.mem_map_of_mem (evZero n k).toRingHom hvL
      have hmap_L : Ideal.map (evZero n k).toRingHom L = Lbar := by
        rw [Ideal.map_sup]
        have h1 : Ideal.map (evZero n k).toRingHom
            (Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k))) = ⊥ := by
          rw [Ideal.map_span, Set.image_singleton, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
            evZero_X_zero, Ideal.span_singleton_eq_bot]
        have h2 : Ideal.map (evZero n k).toRingHom (Ideal.map (embSucc n k).toRingHom Lbar) = Lbar := by
          rw [Ideal.map_map]
          have hcomp : (evZero n k).toRingHom.comp (embSucc n k).toRingHom = RingHom.id _ :=
            RingHom.ext fun p => AlgHom.congr_fun (evZero_comp_embSucc (n := n) (k := k)) p
          rw [hcomp, Ideal.map_id]
        rw [h1, h2, bot_sup_eq]
      rw [hmap_L] at hev
      have hev_v : evZero n k (monomial v (1 : k)) = monomial v' (1 : k) := by
        have hmv : monomial v (1 : k) = embSucc n k (monomial v' (1 : k)) := by
          rw [← hv_eq]; simp [embSucc, rename_monomial]
        rw [hmv, evZero_embSucc]
      simpa [hev_v] using hev
    have hu'_mem : monomial u' (1 : k) ∈ Lbar := hlex_bar u' v' huv' hlt' hv'_mem
    have hmu : monomial u (1 : k) = embSucc n k (monomial u' (1 : k)) := by
      rw [← hu_eq]; simp [embSucc, rename_monomial]
    rw [hmu]
    exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hu'_mem)
theorem d0_eq_one_reduction {c : ℕ} (hc : c + 1 ≤ n + 1) (d : Fin (c + 1) → ℕ)
    (hd0 : d 0 = 1)
    {I : Ideal (MvPolynomial (Fin (n + 1)) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k))
    {f : Fin (c + 1) → MvPolynomial (Fin (n + 1)) k}
    (hfd : ∀ i, (f i).IsHomogeneous (d i))
    (hfI : ∀ i, f i ∈ I)
    (hf : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) k) (List.ofFn f))
    (hIH : ∀ (I' : Ideal (MvPolynomial (Fin n) k)),
      I'.IsHomogeneous (homogeneousSubmodule (Fin n) k) →
      ∀ (f' : Fin c → MvPolynomial (Fin n) k),
        (∀ i, (f' i).IsHomogeneous (d i.succ)) →
        (∀ i, f' i ∈ I') →
        RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (List.ofFn f') →
        ∃ L' : Ideal (MvPolynomial (Fin n) k), IsLexIdeal L' ∧
          ∀ e, hilbertFunction I' e =
            hilbertFunction (L' + purePowersIdeal (Nat.le_of_succ_le_succ hc) (d ∘ Fin.succ)) e) :
    ∃ L : Ideal (MvPolynomial (Fin (n + 1)) k), IsLexIdeal L ∧
      ∀ e, hilbertFunction I e = hilbertFunction (L + purePowersIdeal hc d) e := by
  have hf0_ne : f 0 ≠ 0 := by
    intro h0
    have hcons : List.ofFn f = f 0 :: List.ofFn (f ∘ Fin.succ) := List.ofFn_succ
    rw [hcons, h0, RingTheory.Sequence.isRegular_cons_iff] at hf
    have : (1 : MvPolynomial (Fin (n + 1)) k) = 0 := hf.1 (by simp)
    exact one_ne_zero this
  have hf0_hom : (f 0).IsHomogeneous 1 := by simpa [hd0] using hfd 0
  obtain ⟨Ψ, hΨ, hΨ_inv, hΨ0⟩ := exists_graded_algEquiv_map_eq hf0_hom hf0_ne 0
  let I1 := Ideal.map Ψ.toRingHom I
  have hI1_hom : I1.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k) :=
    graded_algEquiv_isHomogeneous_map Ψ hΨ hΨ_inv hI
  have hI1_hf : ∀ e, hilbertFunction I1 e = hilbertFunction I e :=
    graded_algEquiv_hilbertFunction Ψ hΨ hΨ_inv I
  have hf1_reg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) k)
      (X 0 :: List.ofFn (fun i : Fin c => Ψ (f i.succ))) := by
    have h1 := graded_algEquiv_isRegular Ψ hf
    have hlist : (List.ofFn f).map Ψ = X 0 :: List.ofFn (fun i : Fin c => Ψ (f i.succ)) := by
      rw [List.ofFn_succ, List.map_cons, hΨ0, List.map_ofFn]; rfl
    rwa [hlist] at h1
  have hX0_I1 : (X 0 : MvPolynomial (Fin (n + 1)) k) ∈ I1 := by
    rw [← hΨ0]; exact Ideal.mem_map_of_mem _ (hfI 0)
  let Ibar := Ideal.map (evZero n k).toRingHom I1
  let fbar : Fin c → MvPolynomial (Fin n) k := fun i => evZero n k (Ψ (f i.succ))
  have hfbar_reg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (List.ofFn fbar) := by
    have h1 := isRegular_evZero_of_cons hf1_reg
    rwa [List.map_ofFn] at h1
  obtain ⟨Lbar, hLbar_lex, hLbar_hf⟩ := hIH Ibar (isHomogeneous_map_evZero hI1_hom hX0_I1) fbar
    (fun i => isHomogeneous_evZero (hΨ _ _ (hfd i.succ)))
    (fun i => Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hfI i.succ)))
    hfbar_reg
  let L := Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k)) ⊔
    Ideal.map (embSucc n k).toRingHom Lbar
  refine ⟨L, isLexIdeal_lift_X0 hLbar_lex, fun e => ?_⟩
  have hLP_X0 : (X 0 : MvPolynomial (Fin (n + 1)) k) ∈ L + purePowersIdeal hc d :=
    Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton _)))
  have hmap_LP : Ideal.map (evZero n k).toRingHom (L + purePowersIdeal hc d) =
      Lbar + purePowersIdeal (Nat.le_of_succ_le_succ hc) (d ∘ Fin.succ) := by
    rw [Submodule.add_eq_sup, Submodule.add_eq_sup, Ideal.map_sup, Ideal.map_sup]
    have h1 : Ideal.map (evZero n k).toRingHom
        (Ideal.span ({X 0} : Set (MvPolynomial (Fin (n + 1)) k))) = ⊥ := by
      rw [Ideal.map_span, Set.image_singleton, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        evZero_X_zero, Ideal.span_singleton_eq_bot]
    have h2 : Ideal.map (evZero n k).toRingHom (Ideal.map (embSucc n k).toRingHom Lbar) = Lbar := by
      rw [Ideal.map_map]
      have hcomp : (evZero n k).toRingHom.comp (embSucc n k).toRingHom = RingHom.id _ :=
        RingHom.ext fun p => AlgHom.congr_fun (evZero_comp_embSucc (n := n) (k := k)) p
      rw [hcomp, Ideal.map_id]
    have h3 : Ideal.map (evZero n k).toRingHom (purePowersIdeal hc d) =
        purePowersIdeal (Nat.le_of_succ_le_succ hc) (d ∘ Fin.succ) := by
      unfold purePowersIdeal
      rw [Ideal.map_span]
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
        refine Fin.cases ?_ (fun i => ?_) j
        · simp [hd0, evZero_X_zero]
        · dsimp only
          have hcast : Fin.castLE hc i.succ = (Fin.castLE (Nat.le_of_succ_le_succ hc) i).succ := rfl
          rw [hcast, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, evZero_X_succ]
          exact Ideal.subset_span ⟨i, rfl⟩
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        apply Ideal.subset_span
        refine ⟨(X (Fin.castLE hc i.succ)) ^ d i.succ, ⟨i.succ, rfl⟩, ?_⟩
        have hcast : Fin.castLE hc i.succ = (Fin.castLE (Nat.le_of_succ_le_succ hc) i).succ := rfl
        rw [hcast, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, evZero_X_succ]; rfl
    rw [h1, h2, h3, bot_sup_eq]
  have hqI : quotientHF Ibar e = quotientHF I1 e := quotientHF_map_evZero hX0_I1 e
  have hqLP : quotientHF (Lbar + purePowersIdeal (Nat.le_of_succ_le_succ hc) (d ∘ Fin.succ)) e =
      quotientHF (L + purePowersIdeal hc d) e := by
    rw [← hmap_LP]; exact quotientHF_map_evZero hLP_X0 e
  have hadd1 := hilbertFunction_add_quotientHF I1 e
  have hadd2 := hilbertFunction_add_quotientHF (L + purePowersIdeal hc d) e
  have hadd3 := hilbertFunction_add_quotientHF Ibar e
  have hadd4 := hilbertFunction_add_quotientHF
    (Lbar + purePowersIdeal (Nat.le_of_succ_le_succ hc) (d ∘ Fin.succ)) e
  have hhf_bar := hLbar_hf e
  rw [← hI1_hf e]
  omega
end ElimVar
section ArtinianRed
noncomputable def evLast (m : ℕ) (k : Type*) [Field k] :
    MvPolynomial (Fin (m + 1)) k →ₐ[k] MvPolynomial (Fin m) k :=
  MvPolynomial.aeval (Fin.lastCases (0 : MvPolynomial (Fin m) k) (fun i => X i))
noncomputable def embCast (m : ℕ) (k : Type*) [Field k] :
    MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin (m + 1)) k :=
  MvPolynomial.rename Fin.castSucc
lemma evLast_X_last {m : ℕ} : evLast m k (X (Fin.last m)) = 0 := by simp [evLast]
lemma evLast_X_castSucc {m : ℕ} (i : Fin m) : evLast m k (X i.castSucc) = X i := by simp [evLast]
lemma embCast_X {m : ℕ} (i : Fin m) : embCast m k (X i) = X i.castSucc := by simp [embCast]
lemma evLast_comp_embCast {m : ℕ} : (evLast m k).comp (embCast m k) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext; intro i; simp [evLast, embCast]
lemma evLast_embCast {m : ℕ} (p : MvPolynomial (Fin m) k) : evLast m k (embCast m k p) = p :=
  AlgHom.congr_fun (evLast_comp_embCast (m := m) (k := k)) p
lemma evLast_surjective {m : ℕ} : Function.Surjective (evLast m k) :=
  Function.RightInverse.surjective (evLast_embCast (m := m) (k := k))
lemma isHomogeneous_evLast {m : ℕ} {p : MvPolynomial (Fin (m + 1)) k} {d : ℕ}
    (hp : p.IsHomogeneous d) : (evLast m k p).IsHomogeneous d := by
  apply isHomogeneous_aeval_of_deg_one _ _ hp
  intro j
  cases j using Fin.lastCases with
  | last => simp; exact isHomogeneous_zero _ _ _
  | cast i => simp; exact isHomogeneous_X k i
lemma isHomogeneous_embCast {m : ℕ} {p : MvPolynomial (Fin m) k} {d : ℕ}
    (hp : p.IsHomogeneous d) : (embCast m k p).IsHomogeneous d := by
  have : embCast m k p = MvPolynomial.aeval
      (fun i : Fin m => (X i.castSucc : MvPolynomial (Fin (m + 1)) k)) p := by
    simp [embCast, MvPolynomial.rename_eq_aeval]; rfl
  rw [this]
  exact isHomogeneous_aeval_of_deg_one _ (fun i => isHomogeneous_X k i.castSucc) hp
lemma sub_embCast_evLast_mem {m : ℕ} (p : MvPolynomial (Fin (m + 1)) k) :
    p - embCast m k (evLast m k p) ∈
      Ideal.span ({X (Fin.last m)} : Set (MvPolynomial (Fin (m + 1)) k)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [evLast, embCast]
  | add p q hp hq =>
    have : p + q - embCast m k (evLast m k (p + q)) =
        (p - embCast m k (evLast m k p)) + (q - embCast m k (evLast m k q)) := by
      simp only [map_add]; ring
    rw [this]; exact Ideal.add_mem _ hp hq
  | mul_X p j hp =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [map_mul, evLast_X_last, mul_zero, map_zero, sub_zero]
      exact Ideal.mul_mem_left _ p (Ideal.subset_span (Set.mem_singleton _))
    · have : p * X i.castSucc - embCast m k (evLast m k (p * X i.castSucc)) =
          (p - embCast m k (evLast m k p)) * X i.castSucc := by
        rw [map_mul, evLast_X_castSucc, map_mul, embCast_X]; ring
      rw [this]; exact Ideal.mul_mem_right _ _ hp
lemma mem_ker_evLast_iff {m : ℕ} (p : MvPolynomial (Fin (m + 1)) k) :
    evLast m k p = 0 ↔ p ∈ Ideal.span ({X (Fin.last m)} : Set (MvPolynomial (Fin (m + 1)) k)) := by
  constructor
  · intro h0; simpa [h0] using sub_embCast_evLast_mem p
  · intro hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro _ rfl; exact evLast_X_last
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro r x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]
lemma isRegular_evLast_of_cons {m : ℕ} {rs : List (MvPolynomial (Fin (m + 1)) k)}
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (m + 1)) k) (X (Fin.last m) :: rs)) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin m) k) (rs.map (evLast m k)) := by
  rw [RingTheory.Sequence.isRegular_cons_iff'] at hreg
  have hsmul : ((X (Fin.last m) : MvPolynomial (Fin (m + 1)) k) • ⊤ :
      Submodule (MvPolynomial (Fin (m + 1)) k) (MvPolynomial (Fin (m + 1)) k)) =
      Ideal.span ({X (Fin.last m)} : Set (MvPolynomial (Fin (m + 1)) k)) := by
    ext p
    simp only [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton,
      dvd_iff_exists_eq_mul_right, smul_eq_mul, Submodule.mem_top, true_and, eq_comm]
  let e1 : QuotSMulTop (X (Fin.last m) : MvPolynomial (Fin (m + 1)) k)
      (MvPolynomial (Fin (m + 1)) k) ≃ₗ[MvPolynomial (Fin (m + 1)) k]
      (MvPolynomial (Fin (m + 1)) k ⧸
        Ideal.span ({X (Fin.last m)} : Set (MvPolynomial (Fin (m + 1)) k))) :=
    Submodule.quotEquivOfEq
      ((X (Fin.last m) : MvPolynomial (Fin (m + 1)) k) • ⊤ :
        Submodule (MvPolynomial (Fin (m + 1)) k) (MvPolynomial (Fin (m + 1)) k))
      (Ideal.span ({X (Fin.last m)} : Set (MvPolynomial (Fin (m + 1)) k))) hsmul
  let kerEq : RingHom.ker (evLast m k).toRingHom =
      Ideal.span ({X (Fin.last m)} : Set (MvPolynomial (Fin (m + 1)) k)) := by
    ext p; exact mem_ker_evLast_iff p
  let e2 : (MvPolynomial (Fin (m + 1)) k ⧸
        Ideal.span ({X (Fin.last m)} : Set (MvPolynomial (Fin (m + 1)) k))) ≃+*
      MvPolynomial (Fin m) k :=
    (Ideal.quotEquivOfEq kerEq.symm).trans
      (RingHom.quotientKerEquivOfSurjective (f := (evLast m k).toRingHom) evLast_surjective)
  let eAdd : QuotSMulTop (X (Fin.last m) : MvPolynomial (Fin (m + 1)) k)
      (MvPolynomial (Fin (m + 1)) k) ≃+ MvPolynomial (Fin m) k :=
    e1.toAddEquiv.trans e2.toAddEquiv
  have he_mk : ∀ p : MvPolynomial (Fin (m + 1)) k,
      eAdd (Submodule.Quotient.mk p) = evLast m k p := fun _ => rfl
  refine (eAdd.isRegular_congr ?_).mp hreg.2
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun r _ x => ?_
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change eAdd (Submodule.Quotient.mk (r * p)) = evLast m k r * eAdd (Submodule.Quotient.mk p)
  rw [he_mk, he_mk, map_mul]
lemma isHomogeneous_colon_homog {I : Ideal (MvPolynomial (Fin n) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) k))
    {g : MvPolynomial (Fin n) k} {d : ℕ} (hg : g.IsHomogeneous d) :
    (I.colon {g}).IsHomogeneous (homogeneousSubmodule (Fin n) k) := by
  intro e p hp
  change ((MvPolynomial.decomposition.decompose' p e : _) : MvPolynomial (Fin n) k) ∈
    I.colon {g}
  rw [MvPolynomial.decomposition.decompose'_apply, Submodule.mem_colon_singleton]
  rw [Submodule.mem_colon_singleton] at hp
  have hmul_comp : homogeneousComponent (e + d) (p * g) = homogeneousComponent e p * g := by
    ext u
    rw [coeff_homogeneousComponent]
    by_cases hdeg : u.degree = e + d
    · rw [if_pos hdeg, coeff_mul, coeff_mul]
      refine Finset.sum_congr rfl fun xy hxy => ?_
      rw [HasAntidiagonal.mem_antidiagonal] at hxy
      by_cases h2 : xy.2.degree = d
      · have h1 : xy.1.degree = e := by
          have := congrArg Finsupp.degree hxy
          rw [map_add, hdeg, h2] at this; omega
        rw [coeff_homogeneousComponent, if_pos h1]
      · rw [hg.coeff_eq_zero h2, mul_zero, mul_zero]
    · rw [if_neg hdeg]
      exact ((homogeneousComponent_isHomogeneous e p).mul hg).coeff_eq_zero hdeg |>.symm
  have hpg : p * g ∈ I := by simpa [smul_eq_mul, mul_comm] using hp
  have hcomp := MvPolynomial.homogeneousComponent_mem_of_mem hI hpg (e + d)
  rw [hmul_comp] at hcomp
  simpa [smul_eq_mul, mul_comm] using hcomp
lemma isHomogeneous_map_evLast {m : ℕ} {I : Ideal (MvPolynomial (Fin (m + 1)) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k)) :
    (Ideal.map (evLast m k).toRingHom I).IsHomogeneous (homogeneousSubmodule (Fin m) k) := by
  have hcomm : ∀ p e, homogeneousComponent e (evLast m k p) =
      evLast m k (homogeneousComponent e p) := by
    intro p e
    have h1 : homogeneousComponent e (evLast m k p) =
        homogeneousComponent e (∑ i ∈ Finset.range (p.totalDegree + 1),
          evLast m k (homogeneousComponent i p)) := by
      congr 1; rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
    rw [h1, map_sum]
    by_cases he : e < p.totalDegree + 1
    · rw [Finset.sum_eq_single e]
      · exact homogeneousComponent_eq_self (isHomogeneous_evLast (homogeneousComponent_isHomogeneous e p))
      · intro i _ hie
        exact homogeneousComponent_eq_zero_of_ne
          (isHomogeneous_evLast (homogeneousComponent_isHomogeneous i p)) hie
      · intro h; exact absurd (Finset.mem_range.mpr he) h
    · rw [homogeneousComponent_eq_zero e p (by omega), map_zero]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hi_lt := Finset.mem_range.mp hi
      exact homogeneousComponent_eq_zero_of_ne
        (isHomogeneous_evLast (homogeneousComponent_isHomogeneous i p)) (by omega)
  intro e q hq
  change ((MvPolynomial.decomposition.decompose' q e : _) : MvPolynomial (Fin m) k) ∈
    Ideal.map (evLast m k).toRingHom I
  rw [MvPolynomial.decomposition.decompose'_apply]
  rw [Ideal.mem_map_iff_of_surjective (f := (evLast m k).toRingHom) evLast_surjective] at hq
  obtain ⟨p, hpI, rfl⟩ := hq
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [hcomm]
  exact Ideal.mem_map_of_mem _ (MvPolynomial.homogeneousComponent_mem_of_mem hI hpI e)
lemma quotientHF_colon_last_rec {m : ℕ} {K : Ideal (MvPolynomial (Fin (m + 1)) k)}
    (hK : K.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k)) (e : ℕ) :
    quotientHF K e = quotientHF (Ideal.map (evLast m k).toRingHom K) e +
      (if 1 ≤ e then quotientHF (K.colon ({X (Fin.last m)} : Set (MvPolynomial (Fin (m + 1)) k)))
        (e - 1) else 0) := by
  let Kbar := Ideal.map (evLast m k).toRingHom K
  let K' := K.colon ({X (Fin.last m)} : Set (MvPolynomial (Fin (m + 1)) k))
  let f : homogPiece (m + 1) k e →ₗ[k] homogPiece m k e := {
    toFun := fun x => ⟨evLast m k x.1,
      (mem_homogeneousSubmodule e _).mpr (isHomogeneous_evLast ((mem_homogeneousSubmodule e _).mp x.2))⟩
    map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1)
    map_smul' := fun c x => Subtype.ext (map_smul _ c x.1)
  }
  let π : (homogPiece (m + 1) k e ⧸ idealSub K e) →ₗ[k]
      (homogPiece m k e ⧸ idealSub Kbar e) :=
    Submodule.mapQ (idealSub K e) (idealSub Kbar e) f (by
      intro x hx; rw [Submodule.mem_comap, mem_idealSub]
      exact Ideal.mem_map_of_mem _ ((mem_idealSub x).mp hx))
  have hπ_surj : Function.Surjective π := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨Submodule.Quotient.mk ⟨embCast m k z.1,
      (mem_homogeneousSubmodule e _).mpr (isHomogeneous_embCast ((mem_homogeneousSubmodule e _).mp z.2))⟩, ?_⟩
    change Submodule.Quotient.mk ⟨evLast m k (embCast m k z.1), _⟩ = Submodule.Quotient.mk z
    congr 1; exact Subtype.ext (evLast_embCast z.1)
  have hrn := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hπ_surj, finrank_top] at hrn
  suffices hker : Module.finrank k (LinearMap.ker π) =
      if 1 ≤ e then quotientHF K' (e - 1) else 0 by
    change quotientHF Kbar e + Module.finrank k (LinearMap.ker π) = quotientHF K e at hrn
    dsimp only [Kbar, K'] at hrn hker; omega
  by_cases he : 1 ≤ e
  · rw [if_pos he]
    let mulX : homogPiece (m + 1) k (e - 1) →ₗ[k] homogPiece (m + 1) k e := {
      toFun := fun x => ⟨X (Fin.last m) * x.1, by
        rw [mem_homogeneousSubmodule]
        have h := (isHomogeneous_X k (Fin.last m)).mul ((mem_homogeneousSubmodule _ _).mp x.2)
        have hd : 1 + (e - 1) = e := by omega
        rwa [hd] at h⟩
      map_add' := fun x y => Subtype.ext (mul_add _ x.1 y.1)
      map_smul' := fun c x => Subtype.ext (by simp [Algebra.mul_smul_comm])
    }
    let μ : (homogPiece (m + 1) k (e - 1) ⧸ idealSub K' (e - 1)) →ₗ[k]
        (homogPiece (m + 1) k e ⧸ idealSub K e) :=
      Submodule.mapQ (idealSub K' (e - 1)) (idealSub K e) mulX (by
        intro x hx; rw [Submodule.mem_comap, mem_idealSub]
        have hx' := (mem_idealSub x).mp hx
        rw [Submodule.mem_colon_singleton] at hx'
        simpa [mulX, smul_eq_mul, mul_comm] using hx')
    have hμ_inj : Function.Injective μ := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [Submodule.Quotient.mk_eq_zero, mem_idealSub, Submodule.mem_colon_singleton]
      change Submodule.Quotient.mk (mulX x) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero, mem_idealSub] at hy
      simpa [mulX, smul_eq_mul, mul_comm] using hy
    have hμ_range : LinearMap.range μ = LinearMap.ker π := by
      ext y
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      simp only [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨w, hw⟩
        obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
        rw [← hw]
        change (Submodule.Quotient.mk (⟨evLast m k (X (Fin.last m) * z.1),
          (mem_homogeneousSubmodule e _).mpr (isHomogeneous_evLast
            ((mem_homogeneousSubmodule e _).mp (mulX z).2))⟩ : homogPiece m k e) :
          homogPiece m k e ⧸ idealSub Kbar e) = 0
        rw [Submodule.Quotient.mk_eq_zero, mem_idealSub]
        simp [evLast_X_last]
      · intro hπx
        change Submodule.Quotient.mk (f x) = 0 at hπx
        rw [Submodule.Quotient.mk_eq_zero, mem_idealSub] at hπx
        change evLast m k x.1 ∈ Kbar at hπx
        rw [Ideal.mem_map_iff_of_surjective (f := (evLast m k).toRingHom) evLast_surjective] at hπx
        obtain ⟨q, hqK, hq_eq⟩ := hπx
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hq_eq
        have hqeK : homogeneousComponent e q ∈ K :=
          MvPolynomial.homogeneousComponent_mem_of_mem hK hqK e
        have hqe_ev : evLast m k (homogeneousComponent e q) = evLast m k x.1 := by
          have hcomm : evLast m k (homogeneousComponent e q) =
              homogeneousComponent e (evLast m k q) := by
            have h1 : homogeneousComponent e (evLast m k q) =
                homogeneousComponent e (∑ i ∈ Finset.range (q.totalDegree + 1),
                  evLast m k (homogeneousComponent i q)) := by
              congr 1; rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
            rw [h1, map_sum]
            by_cases hlt : e < q.totalDegree + 1
            · rw [Finset.sum_eq_single e]
              · exact (homogeneousComponent_eq_self
                  (isHomogeneous_evLast (homogeneousComponent_isHomogeneous e q))).symm
              · intro i _ hie
                exact homogeneousComponent_eq_zero_of_ne
                  (isHomogeneous_evLast (homogeneousComponent_isHomogeneous i q)) hie
              · intro h; exact absurd (Finset.mem_range.mpr hlt) h
            · rw [homogeneousComponent_eq_zero e q (by omega), map_zero]
              symm; refine Finset.sum_eq_zero fun i hi => ?_
              have hi_lt := Finset.mem_range.mp hi
              exact homogeneousComponent_eq_zero_of_ne
                (isHomogeneous_evLast (homogeneousComponent_isHomogeneous i q)) (by omega)
          rw [hcomm, hq_eq, homogeneousComponent_eq_self
            (isHomogeneous_evLast ((mem_homogeneousSubmodule e _).mp x.2))]
        have hdiff_ker : evLast m k (x.1 - homogeneousComponent e q) = 0 := by
          rw [map_sub, hqe_ev, sub_self]
        have hdiff_mem := (mem_ker_evLast_iff _).mp hdiff_ker
        rw [Ideal.mem_span_singleton] at hdiff_mem
        obtain ⟨r, hr⟩ := hdiff_mem
        have hdiff_hom : (x.1 - homogeneousComponent e q).IsHomogeneous e :=
          ((mem_homogeneousSubmodule e _).mp x.2).sub (homogeneousComponent_isHomogeneous e q)
        have hr_hom_eq : x.1 - homogeneousComponent e q =
            X (Fin.last m) * homogeneousComponent (e - 1) r := by
          have h1 := congrArg (homogeneousComponent e) hr
          rw [homogeneousComponent_eq_self hdiff_hom] at h1
          have h2 : homogeneousComponent e (X (Fin.last m) * r) =
              X (Fin.last m) * homogeneousComponent (e - 1) r := by
            ext u
            rw [coeff_homogeneousComponent]
            by_cases hdeg : u.degree = e
            · rw [if_pos hdeg, coeff_mul, coeff_mul]
              refine Finset.sum_congr rfl fun xy hxy => ?_
              rw [HasAntidiagonal.mem_antidiagonal] at hxy
              by_cases h1' : xy.1.degree = 1
              · have h2' : xy.2.degree = e - 1 := by
                  have := congrArg Finsupp.degree hxy
                  rw [map_add, hdeg, h1'] at this; omega
                rw [coeff_homogeneousComponent, if_pos h2']
              · rw [(isHomogeneous_X k (Fin.last m)).coeff_eq_zero h1', zero_mul, zero_mul]
            · rw [if_neg hdeg]
              have hhom : (X (Fin.last m) * homogeneousComponent (e - 1) r).IsHomogeneous e := by
                have := (isHomogeneous_X k (Fin.last m)).mul
                  (homogeneousComponent_isHomogeneous (e - 1) r)
                have hd : 1 + (e - 1) = e := by omega
                rwa [hd] at this
              exact (hhom.coeff_eq_zero hdeg).symm
          rw [h1, h2]
        refine ⟨Submodule.Quotient.mk ⟨homogeneousComponent (e - 1) r,
          (mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous (e - 1) r)⟩, ?_⟩
        change Submodule.Quotient.mk ⟨X (Fin.last m) * homogeneousComponent (e - 1) r, _⟩ =
          Submodule.Quotient.mk x
        rw [Submodule.Quotient.eq, mem_idealSub]
        have hval : (⟨X (Fin.last m) * homogeneousComponent (e - 1) r,
          (mem_homogeneousSubmodule e _).mpr (by
            have h := (isHomogeneous_X k (Fin.last m)).mul
              (homogeneousComponent_isHomogeneous (e - 1) r)
            have hd : 1 + (e - 1) = e := by omega
            rwa [hd] at h)⟩ - x : homogPiece (m + 1) k e).1 = -homogeneousComponent e q := by
          change X (Fin.last m) * homogeneousComponent (e - 1) r - x.1 = -homogeneousComponent e q
          rw [← hr_hom_eq]; ring
        rw [hval]; exact K.neg_mem hqeK
    rw [← hμ_range]
    exact (LinearEquiv.finrank_eq (LinearEquiv.ofInjective μ hμ_inj)).symm
  · rw [if_neg he]
    have he0 : e = 0 := by omega
    subst he0
    have hker_bot : LinearMap.ker π = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [LinearMap.mem_ker] at hy
      change Submodule.Quotient.mk (f x) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero, mem_idealSub] at hy
      change evLast m k x.1 ∈ Kbar at hy
      rw [Ideal.mem_map_iff_of_surjective (f := (evLast m k).toRingHom) evLast_surjective] at hy
      obtain ⟨q, hqK, hq_eq⟩ := hy
      have hx_const : x.1 = C (coeff 0 x.1) := by
        ext u
        by_cases hu : u = 0
        · subst hu; simp
        · have hne : u.degree ≠ 0 := by
            intro h0; apply hu
            ext i; have hle : u i ≤ ∑ j, u j :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
            rw [← Finsupp.degree_eq_sum, h0] at hle; simp; omega
          rw [((mem_homogeneousSubmodule 0 _).mp x.2).coeff_eq_zero hne, coeff_C, if_neg (Ne.symm hu)]
      have hq0K : homogeneousComponent 0 q ∈ K :=
        MvPolynomial.homogeneousComponent_mem_of_mem hK hqK 0
      have hq0_eq : homogeneousComponent 0 q = x.1 := by
        have hq0_const : homogeneousComponent 0 q = C (coeff 0 q) := by
          ext u
          by_cases hu : u = 0
          · subst hu; simp
          · have hne : u.degree ≠ 0 := by
              intro h0; apply hu
              ext i; have hle : u i ≤ ∑ j, u j :=
                Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
              rw [← Finsupp.degree_eq_sum, h0] at hle; simp; omega
            rw [coeff_homogeneousComponent, if_neg hne, coeff_C, if_neg (Ne.symm hu)]
        have hc0 : coeff 0 q = coeff 0 x.1 := by
          simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hq_eq
          have h1 := congrArg (coeff 0) hq_eq
          have hev0 : ∀ p : MvPolynomial (Fin (m + 1)) k, coeff 0 (evLast m k p) = coeff 0 p := by
            intro p
            conv_lhs => rw [p.as_sum]
            rw [map_sum, coeff_sum]
            by_cases h0 : (0 : Fin (m + 1) →₀ ℕ) ∈ p.support
            · rw [Finset.sum_eq_single 0]
              · simp [evLast]
              · intro u hu hu0
                have hmon_hom : (monomial u (coeff u p)).IsHomogeneous u.degree := by
                  have h1 : (monomial u (1 : k)).IsHomogeneous u.degree :=
                    (mem_homogeneousSubmodule u.degree _).mp (monomial_mem_homogPiece (mem_monOfDeg.mpr rfl))
                  simpa [C_mul_monomial, mul_one] using (isHomogeneous_C (Fin (m + 1)) (coeff u p)).mul h1
                have hhom := isHomogeneous_evLast hmon_hom
                have hdeg_ne : (0 : Fin m →₀ ℕ).degree ≠ u.degree := by
                  intro hdeg0; apply hu0; ext j
                  have hle : u j ≤ ∑ i, u i :=
                    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
                  rw [← Finsupp.degree_eq_sum, ← hdeg0] at hle; simp at hle ⊢; omega
                exact hhom.coeff_eq_zero hdeg_ne
              · intro h; exact absurd h0 h
            · rw [MvPolynomial.notMem_support_iff.mp h0]
              refine Finset.sum_eq_zero fun u hu => ?_
              have hu0 : u ≠ 0 := fun h => h0 (h ▸ hu)
              have hmon_hom : (monomial u (coeff u p)).IsHomogeneous u.degree := by
                have h1 : (monomial u (1 : k)).IsHomogeneous u.degree :=
                  (mem_homogeneousSubmodule u.degree _).mp (monomial_mem_homogPiece (mem_monOfDeg.mpr rfl))
                simpa [C_mul_monomial, mul_one] using (isHomogeneous_C (Fin (m + 1)) (coeff u p)).mul h1
              have hhom := isHomogeneous_evLast hmon_hom
              have hdeg_ne : (0 : Fin m →₀ ℕ).degree ≠ u.degree := by
                intro hdeg0; apply hu0; ext j
                have hle : u j ≤ ∑ i, u i :=
                  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
                rw [← Finsupp.degree_eq_sum, ← hdeg0] at hle; simp at hle ⊢; omega
              exact hhom.coeff_eq_zero hdeg_ne
          rw [hev0, hev0] at h1; exact h1
        rw [hq0_const, hc0, ← hx_const]
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, mem_idealSub, ← hq0_eq]
      exact hq0K
    rw [hker_bot, finrank_bot]
lemma quotientHF_eq_sum_colon {m : ℕ} {I : Ideal (MvPolynomial (Fin (m + 1)) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k)) (e : ℕ) :
    quotientHF I e = ∑ j ∈ Finset.range (e + 1),
      quotientHF (Ideal.map (evLast m k).toRingHom
        (I.colon ({X (Fin.last m) ^ j} : Set (MvPolynomial (Fin (m + 1)) k)))) (e - j) := by
  have hrec_gen : ∀ (e j : ℕ),
      quotientHF (I.colon ({X (Fin.last m) ^ j} : Set (MvPolynomial (Fin (m + 1)) k))) e =
        ∑ r ∈ Finset.range (e + 1),
          quotientHF (Ideal.map (evLast m k).toRingHom
            (I.colon ({X (Fin.last m) ^ (j + r)} : Set (MvPolynomial (Fin (m + 1)) k)))) (e - r) := by
    intro e
    induction e with
    | zero =>
      intro j
      have hhom : (I.colon ({X (Fin.last m) ^ j} : Set (MvPolynomial (Fin (m + 1)) k))).IsHomogeneous
          (homogeneousSubmodule (Fin (m + 1)) k) :=
        isHomogeneous_colon_homog hI (by simpa using (isHomogeneous_X k (Fin.last m)).pow j)
      have h := quotientHF_colon_last_rec hhom 0
      simpa using h
    | succ e ih =>
      intro j
      have hhom : (I.colon ({X (Fin.last m) ^ j} : Set (MvPolynomial (Fin (m + 1)) k))).IsHomogeneous
          (homogeneousSubmodule (Fin (m + 1)) k) :=
        isHomogeneous_colon_homog hI (by simpa using (isHomogeneous_X k (Fin.last m)).pow j)
      have h := quotientHF_colon_last_rec hhom (e + 1)
      have hcolon_succ :
          (I.colon ({X (Fin.last m) ^ j} : Set (MvPolynomial (Fin (m + 1)) k))).colon
            ({X (Fin.last m)} : Set (MvPolynomial (Fin (m + 1)) k)) =
          I.colon ({X (Fin.last m) ^ (j + 1)} : Set (MvPolynomial (Fin (m + 1)) k)) := by
        ext p
        simp only [Submodule.mem_colon_singleton, smul_eq_mul, pow_succ, mul_assoc]
        constructor <;> intro hp <;> simpa [mul_comm, mul_left_comm, mul_assoc] using hp
      simp only [Nat.succ_sub_one, Nat.le_add_left, ↓reduceIte, hcolon_succ] at h
      rw [h, ih (j + 1)]
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [add_zero, Nat.sub_zero]
      rw [add_comm]
      have hsum :
          (∑ r ∈ Finset.range (e + 1),
            quotientHF (Ideal.map (evLast m k).toRingHom
              (I.colon ({X (Fin.last m) ^ (j + 1 + r)} : Set (MvPolynomial (Fin (m + 1)) k))))
              (e - r)) =
          ∑ r ∈ Finset.range (e + 1),
            quotientHF (Ideal.map (evLast m k).toRingHom
              (I.colon ({X (Fin.last m) ^ (j + (r + 1))} : Set (MvPolynomial (Fin (m + 1)) k))))
              (e + 1 - (r + 1)) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        have hjr : j + 1 + r = j + (r + 1) := by omega
        have her : e - r = e + 1 - (r + 1) := by omega
        rw [hjr, her]
      rw [hsum]
  have h0 := hrec_gen e 0
  have hcolon0 : I.colon ({(1 : MvPolynomial (Fin (m + 1)) k)} :
      Set (MvPolynomial (Fin (m + 1)) k)) = I := by
    ext p; simp [Submodule.mem_colon_singleton]
  simpa [pow_zero, hcolon0] using h0
lemma lpp_le_of_hilbertFunction_le {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    {L₁ L₂ : Ideal (MvPolynomial (Fin n) k)} (hL₁ : IsLexIdeal L₁) (hL₂ : IsLexIdeal L₂)
    (hle : ∀ e, hilbertFunction (L₁ + purePowersIdeal hc d) e ≤
      hilbertFunction (L₂ + purePowersIdeal hc d) e) :
    L₁ + purePowersIdeal hc d ≤ L₂ + purePowersIdeal hc d := by
  classical
  let boxSlice' (e : ℕ) : Finset (Fin n →₀ ℕ) :=
    (monOfDeg n e).filter (fun u => ∀ j : Fin c, u (Fin.castLE hc j) < d j)
  have hmon_set : ∀ (L : Ideal (MvPolynomial (Fin n) k)), IsLexIdeal L →
      let P : Ideal (MvPolynomial (Fin n) k) := purePowersIdeal hc d
      let U : Set (Fin n →₀ ℕ) := { u | monomial u (1 : k) ∈ L + P }
      (∀ u ∈ U, ∀ i : Fin n, u + Finsupp.single i 1 ∈ U) ∧
      L + P = Ideal.span ((fun u => monomial u (1 : k)) '' U) ∧
      (∀ e, hilbertFunction (L + P) e = ((monOfDeg n e).filter (fun u => u ∈ U)).card) ∧
      (∀ e u v, u ∈ boxSlice' e → v ∈ boxSlice' e → toLex v < toLex u → v ∈ U → u ∈ U) := by
    intro L ⟨⟨SL, hSL⟩, hlex⟩
    let P : Ideal (MvPolynomial (Fin n) k) := purePowersIdeal hc d
    let U : Set (Fin n →₀ ℕ) := { u | monomial u (1 : k) ∈ L + P }
    have hU_closed : ∀ u ∈ U, ∀ i : Fin n, u + Finsupp.single i 1 ∈ U := by
      intro u hu i
      change monomial (u + Finsupp.single i 1) (1 : k) ∈ L + P
      have heq : monomial (u + Finsupp.single i 1) (1 : k) = X i * monomial u 1 := by
        rw [X, monomial_mul, one_mul, add_comm]
      rw [heq]; exact (L + P).mul_mem_left _ hu
    have hLP_eq : L + P = Ideal.span ((fun u => monomial u (1 : k)) '' U) := by
      apply le_antisymm
      · rw [Submodule.add_eq_sup]
        refine sup_le ?_ ?_
        · rw [hSL, Ideal.span_le]
          rintro _ ⟨u, hu, rfl⟩
          exact Ideal.subset_span ⟨u, Ideal.mem_sup_left (by rw [hSL]; exact Ideal.subset_span ⟨u, hu, rfl⟩), rfl⟩
        · unfold P purePowersIdeal
          rw [Ideal.span_le]
          rintro _ ⟨j, rfl⟩
          dsimp only
          have hpow : (X (Fin.castLE hc j) : MvPolynomial (Fin n) k) ^ d j =
              monomial (Finsupp.single (Fin.castLE hc j) (d j)) 1 := by
            rw [X_pow_eq_monomial]
          rw [hpow]
          exact Ideal.subset_span ⟨Finsupp.single (Fin.castLE hc j) (d j),
            Ideal.mem_sup_right (by rw [← hpow]; exact Ideal.subset_span ⟨j, rfl⟩), rfl⟩
      · rw [Ideal.span_le]
        rintro _ ⟨u, hu, rfl⟩; exact hu
    have hhf : ∀ e, hilbertFunction (L + P) e = ((monOfDeg n e).filter (fun u => u ∈ U)).card := by
      intro e
      unfold hilbertFunction
      let A := (monOfDeg n e).filter (fun u => u ∈ U)
      let W := Submodule.restrictScalars k (L + P) ⊓ homogeneousSubmodule (Fin n) k e
      let bW : Module.Basis A k W := Module.Basis.mk
        (v := fun u : A =>
          ⟨monomial u.1 (1 : k), ⟨(Finset.mem_filter.mp u.2).2,
            monomial_mem_homogPiece (Finset.mem_filter.mp u.2).1⟩⟩)
        (by
          rw [Fintype.linearIndependent_iff]
          intro g hg u
          have h1 := congrArg (fun x : W => coeff u.1 x.1) hg
          simp only [ZeroMemClass.coe_zero, coeff_zero, AddSubmonoidClass.coe_finsetSum,
            SetLike.val_smul, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul, mul_ite,
            mul_one, mul_zero] at h1
          rw [Finset.sum_eq_single u] at h1
          · simpa using h1
          · intro v _ hvu; rw [if_neg (fun h => hvu (Subtype.ext h))]
          · intro hu; exact absurd (Finset.mem_univ u) hu)
        (by
          intro x _
          have hx_supp : ∀ u ∈ x.1.support, u ∈ A := by
            intro u hu
            rw [Finset.mem_filter]
            refine ⟨support_subset_monOfDeg x.2.2 hu, ?_⟩
            have hx_mem : x.1 ∈ Ideal.span ((fun u => monomial u (1 : k)) '' U) :=
              hLP_eq ▸ x.2.1
            exact (mem_monomialIdeal_iff_support hU_closed x.1).mp hx_mem u hu
          have hx_eq : x = ∑ u : A, coeff u.1 x.1 •
              (⟨monomial u.1 (1 : k), ⟨(Finset.mem_filter.mp u.2).2,
                monomial_mem_homogPiece (Finset.mem_filter.mp u.2).1⟩⟩ : W) := by
            apply Subtype.ext
            rw [AddSubmonoidClass.coe_finsetSum]
            simp only [SetLike.val_smul, smul_monomial, smul_eq_mul, mul_one]
            rw [Finset.sum_coe_sort A (fun u => monomial u (coeff u x.1))]
            conv_lhs => rw [x.1.as_sum]
            exact Finset.sum_subset hx_supp fun u _ hu => by
              rw [MvPolynomial.notMem_support_iff.mp hu, monomial_zero]
          rw [hx_eq]
          exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩))
      rw [Module.finrank_eq_card_basis bW, Fintype.card_coe]
    have hlex_box : ∀ e u v, u ∈ boxSlice' e → v ∈ boxSlice' e → toLex v < toLex u →
        v ∈ U → u ∈ U := by
      intro e u v hu hv hlt hvU
      have hP_mon : P = Ideal.span ((fun w => monomial w (1 : k)) ''
          { w | ∃ j : Fin c, d j ≤ w (Fin.castLE hc j) }) := by
        apply le_antisymm
        · unfold P purePowersIdeal; rw [Ideal.span_le]
          rintro _ ⟨j, rfl⟩
          dsimp only
          rw [X_pow_eq_monomial]
          exact Ideal.subset_span ⟨Finsupp.single (Fin.castLE hc j) (d j), ⟨j, by simp⟩, rfl⟩
        · rw [Ideal.span_le]
          rintro _ ⟨w, ⟨j, hj⟩, rfl⟩
          have hexp : w = (w - Finsupp.single (Fin.castLE hc j) (d j)) +
              Finsupp.single (Fin.castLE hc j) (d j) := by
            ext r
            by_cases hr : r = Fin.castLE hc j
            · subst hr; simp; omega
            · simp [Finsupp.single_eq_of_ne hr]
          have hdiv : monomial w (1 : k) =
              monomial (w - Finsupp.single (Fin.castLE hc j) (d j)) 1 *
                (X (Fin.castLE hc j)) ^ d j := by
            rw [X_pow_eq_monomial, monomial_mul, mul_one, ← hexp]
          dsimp only; rw [hdiv]; exact P.mul_mem_left _ (Ideal.subset_span ⟨j, rfl⟩)
      let SL' : Set (Fin n →₀ ℕ) := { w | monomial w (1 : k) ∈ L }
      let SP : Set (Fin n →₀ ℕ) := { w | ∃ j : Fin c, d j ≤ w (Fin.castLE hc j) }
      have hclosed : ∀ w ∈ SL' ∪ SP, ∀ i : Fin n, w + Finsupp.single i 1 ∈ SL' ∪ SP := by
        intro w hw i
        rcases hw with hwL | ⟨j, hj⟩
        · left
          change monomial (w + Finsupp.single i 1) (1 : k) ∈ L
          have : monomial (w + Finsupp.single i 1) (1 : k) = X i * monomial w 1 := by
            rw [X, monomial_mul, one_mul, add_comm]
          rw [this]; exact L.mul_mem_left _ hwL
        · right; refine ⟨j, ?_⟩; simp only [Finsupp.coe_add, Pi.add_apply]; omega
      have hLP_union : L + P = Ideal.span ((fun w => monomial w (1 : k)) '' (SL' ∪ SP)) := by
        rw [Set.image_union, Ideal.span_union, ← hP_mon, ← Submodule.add_eq_sup]
        congr 1
        apply le_antisymm
        · rw [hSL, Ideal.span_le]; rintro _ ⟨w, hw, rfl⟩
          exact Ideal.subset_span ⟨w, by change monomial w 1 ∈ L; rw [hSL]; exact Ideal.subset_span ⟨w, hw, rfl⟩, rfl⟩
        · rw [Ideal.span_le]; rintro _ ⟨w, hw, rfl⟩; exact hw
      have hv_in : v ∈ SL' ∪ SP := by
        have hv' : monomial v (1 : k) ∈ Ideal.span ((fun w => monomial w (1 : k)) '' (SL' ∪ SP)) :=
          hLP_union ▸ hvU
        exact (mem_monomialIdeal_iff_support hclosed _).mp hv' v
          (by rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton])
      have hv_notSP : v ∉ SP := by
        rintro ⟨j, hj⟩; have := (Finset.mem_filter.mp hv).2 j; omega
      have hvL : monomial v (1 : k) ∈ L := hv_in.resolve_right hv_notSP
      have huv_deg : u.degree = v.degree := by
        rw [mem_monOfDeg.mp (Finset.mem_filter.mp hu).1, mem_monOfDeg.mp (Finset.mem_filter.mp hv).1]
      exact Ideal.mem_sup_left (hlex u v huv_deg hlt hvL)
    exact ⟨hU_closed, hLP_eq, hhf, hlex_box⟩
  obtain ⟨_, hLP₁, hhf₁, hlex₁⟩ := hmon_set L₁ hL₁
  obtain ⟨_, hLP₂, hhf₂, hlex₂⟩ := hmon_set L₂ hL₂
  rw [hLP₁, Ideal.span_le]
  rintro _ ⟨u, hu₁, rfl⟩
  let e := u.degree
  by_cases hinBox : u ∈ boxSlice' e
  · let A₁ := (boxSlice' e).filter (fun w => monomial w (1 : k) ∈ L₁ + purePowersIdeal hc d)
    let A₂ := (boxSlice' e).filter (fun w => monomial w (1 : k) ∈ L₂ + purePowersIdeal hc d)
    have hcard_le : A₁.card ≤ A₂.card := by
      have hsplit : ∀ (L : Ideal (MvPolynomial (Fin n) k)),
          ((monOfDeg n e).filter (fun w => monomial w (1 : k) ∈ L + purePowersIdeal hc d)).card =
          ((boxSlice' e).filter (fun w => monomial w (1 : k) ∈ L + purePowersIdeal hc d)).card +
            (monOfDeg n e \ boxSlice' e).card := by
        intro L
        have hsub : monOfDeg n e \ boxSlice' e ⊆
            (monOfDeg n e).filter (fun w => monomial w (1 : k) ∈ L + purePowersIdeal hc d) := by
          intro w hw
          rw [Finset.mem_sdiff] at hw
          rw [Finset.mem_filter]
          refine ⟨hw.1, ?_⟩
          have hnot : ¬ ∀ j : Fin c, w (Fin.castLE hc j) < d j := fun h =>
            hw.2 (Finset.mem_filter.mpr ⟨hw.1, h⟩)
          push Not at hnot
          obtain ⟨j, hj⟩ := hnot
          apply Ideal.mem_sup_right
          have hexp : w = (w - Finsupp.single (Fin.castLE hc j) (d j)) +
              Finsupp.single (Fin.castLE hc j) (d j) := by
            ext r
            by_cases hr : r = Fin.castLE hc j
            · subst hr; simp; omega
            · simp [Finsupp.single_eq_of_ne hr]
          have hdiv : monomial w (1 : k) =
              monomial (w - Finsupp.single (Fin.castLE hc j) (d j)) 1 *
                (X (Fin.castLE hc j)) ^ d j := by
            rw [X_pow_eq_monomial, monomial_mul, mul_one, ← hexp]
          rw [hdiv]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
        have hunion : (monOfDeg n e).filter (fun w => monomial w (1 : k) ∈ L + purePowersIdeal hc d) =
            ((boxSlice' e).filter (fun w => monomial w (1 : k) ∈ L + purePowersIdeal hc d)) ∪
              (monOfDeg n e \ boxSlice' e) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
          by_cases hbox : w ∈ boxSlice' e
          · have hdeg := (Finset.mem_filter.mp hbox).1
            simp [hbox, hdeg]
          · constructor
            · intro h; exact Or.inr ⟨h.1, hbox⟩
            · rintro (h | ⟨h1, h2⟩)
              · exact absurd h.1 hbox
              · have := hsub (Finset.mem_sdiff.mpr ⟨h1, h2⟩)
                exact Finset.mem_filter.mp this
        have hdisj : Disjoint
            ((boxSlice' e).filter (fun w => monomial w (1 : k) ∈ L + purePowersIdeal hc d))
            (monOfDeg n e \ boxSlice' e) :=
          Finset.disjoint_left.mpr fun w h1 h2 => (Finset.mem_sdiff.mp h2).2 (Finset.mem_filter.mp h1).1
        rw [hunion, Finset.card_union_of_disjoint hdisj]
      have hle_e := hle e
      rw [hhf₁ e, hhf₂ e] at hle_e
      change ((monOfDeg n e).filter (fun w => monomial w (1 : k) ∈ L₁ + purePowersIdeal hc d)).card ≤
        ((monOfDeg n e).filter (fun w => monomial w (1 : k) ∈ L₂ + purePowersIdeal hc d)).card at hle_e
      rw [hsplit L₁, hsplit L₂] at hle_e
      change A₁.card + (monOfDeg n e \ boxSlice' e).card ≤
        A₂.card + (monOfDeg n e \ boxSlice' e).card at hle_e
      omega
    by_contra hu₂
    have hA₂_sub : A₂ ⊂ A₁ := by
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨u, Finset.mem_filter.mpr ⟨hinBox, hu₁⟩, fun h => hu₂ (Finset.mem_filter.mp h).2⟩
      · intro w hw
        have hwB := (Finset.mem_filter.mp hw).1
        have hw₂ := (Finset.mem_filter.mp hw).2
        refine Finset.mem_filter.mpr ⟨hwB, ?_⟩
        rcases lt_trichotomy (toLex u) (toLex w) with hlt | heq | hlt
        · exact hlex₁ e w u hwB hinBox hlt hu₁
        · have : u = w := heq; exact absurd (this ▸ hw₂) hu₂
        · exact absurd (hlex₂ e u w hinBox hwB hlt hw₂) hu₂
    have hlt := Finset.card_lt_card hA₂_sub
    omega
  · have hnot : ¬ ∀ j : Fin c, u (Fin.castLE hc j) < d j := fun h =>
      hinBox (Finset.mem_filter.mpr ⟨mem_monOfDeg.mpr rfl, h⟩)
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    apply Ideal.mem_sup_right
    have hexp : u = (u - Finsupp.single (Fin.castLE hc j) (d j)) +
        Finsupp.single (Fin.castLE hc j) (d j) := by
      ext r
      by_cases hr : r = Fin.castLE hc j
      · subst hr; simp; omega
      · simp [Finsupp.single_eq_of_ne hr]
    have hdiv : monomial u (1 : k) =
        monomial (u - Finsupp.single (Fin.castLE hc j) (d j)) 1 *
          (X (Fin.castLE hc j)) ^ d j := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, ← hexp]
    dsimp only
    rw [hdiv]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
theorem artinian_reduction_step {m c : ℕ} (hc' : c ≤ m) (d : Fin c → ℕ)
    {I : Ideal (MvPolynomial (Fin (m + 1)) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k))
    {f : Fin c → MvPolynomial (Fin (m + 1)) k}
    (hfd : ∀ i, (f i).IsHomogeneous (d i))
    (hfI : ∀ i, f i ∈ I)
    (hf_cons : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (m + 1)) k)
      (X (Fin.last m) :: List.ofFn f))
    (hIH : ∀ (I' : Ideal (MvPolynomial (Fin m) k)),
      I'.IsHomogeneous (homogeneousSubmodule (Fin m) k) →
      ∀ (f' : Fin c → MvPolynomial (Fin m) k),
        (∀ i, (f' i).IsHomogeneous (d i)) →
        (∀ i, f' i ∈ I') →
        RingTheory.Sequence.IsRegular (MvPolynomial (Fin m) k) (List.ofFn f') →
        ∃ L' : Ideal (MvPolynomial (Fin m) k), IsLexIdeal L' ∧
          ∀ e, hilbertFunction I' e = hilbertFunction (L' + purePowersIdeal hc' d) e)
    (hCL : ∀ (J : Ideal (MvPolynomial (Fin (m + 1)) k)),
      J.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k) →
      purePowersIdeal (Nat.le_succ_of_le hc') d ≤ J →
      ∃ L : Ideal (MvPolynomial (Fin (m + 1)) k), IsLexIdeal L ∧
        ∀ e, hilbertFunction J e =
          hilbertFunction (L + purePowersIdeal (Nat.le_succ_of_le hc') d) e) :
    ∃ L : Ideal (MvPolynomial (Fin (m + 1)) k), IsLexIdeal L ∧
      ∀ e, hilbertFunction I e =
        hilbertFunction (L + purePowersIdeal (Nat.le_succ_of_le hc') d) e := by
  classical
  let hc : c ≤ m + 1 := Nat.le_succ_of_le hc'
  let fbar : Fin c → MvPolynomial (Fin m) k := fun i => evLast m k (f i)
  have hfbar_reg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin m) k) (List.ofFn fbar) := by
    have h := isRegular_evLast_of_cons hf_cons
    rwa [List.map_ofFn] at h
  let Ij (j : ℕ) : Ideal (MvPolynomial (Fin (m + 1)) k) :=
    I.colon ({X (Fin.last m) ^ j} : Set (MvPolynomial (Fin (m + 1)) k))
  let Ibar (j : ℕ) : Ideal (MvPolynomial (Fin m) k) :=
    Ideal.map (evLast m k).toRingHom (Ij j)
  have hIj_hom : ∀ j, (Ij j).IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k) := fun j =>
    isHomogeneous_colon_homog hI (by simpa using (isHomogeneous_X k (Fin.last m)).pow j)
  have hIbar_hom : ∀ j, (Ibar j).IsHomogeneous (homogeneousSubmodule (Fin m) k) := fun j =>
    isHomogeneous_map_evLast (hIj_hom j)
  have hIj_mono : ∀ j, Ij j ≤ Ij (j + 1) := by
    intro j p hp
    rw [Submodule.mem_colon_singleton] at hp ⊢
    rw [smul_eq_mul, pow_succ, ← mul_assoc]
    exact I.mul_mem_right _ (by simpa [smul_eq_mul] using hp)
  have hIbar_mono : ∀ j, Ibar j ≤ Ibar (j + 1) := fun j => Ideal.map_mono (hIj_mono j)
  have hfbar_mem : ∀ j i, fbar i ∈ Ibar j := fun j i =>
    Ideal.mem_map_of_mem _ (Submodule.mem_colon_singleton.mpr (by
      rw [smul_eq_mul]; exact I.mul_mem_right _ (hfI i)))
  have hL_ex : ∀ j, ∃ L : Ideal (MvPolynomial (Fin m) k), IsLexIdeal L ∧
      ∀ e, hilbertFunction (Ibar j) e = hilbertFunction (L + purePowersIdeal hc' d) e :=
    fun j => hIH (Ibar j) (hIbar_hom j) fbar (fun i => isHomogeneous_evLast (hfd i))
      (hfbar_mem j) hfbar_reg
  choose Lseq hLseq_lex hLseq_hf using hL_ex
  have hLP_mono : ∀ j, Lseq j + purePowersIdeal hc' d ≤ Lseq (j + 1) + purePowersIdeal hc' d := by
    intro j
    apply lpp_le_of_hilbertFunction_le hc' d (hLseq_lex j) (hLseq_lex (j + 1))
    intro e
    rw [← hLseq_hf j e, ← hLseq_hf (j + 1) e]
    unfold hilbertFunction
    exact Submodule.finrank_mono (inf_le_inf_right _ (hIbar_mono j))
  let dropLast (u : Fin (m + 1) →₀ ℕ) : Fin m →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => u i.castSucc)
  let UJ : Set (Fin (m + 1) →₀ ℕ) :=
    { u | monomial (dropLast u) (1 : k) ∈ Lseq (u (Fin.last m)) + purePowersIdeal hc' d }
  have hUJ_closed : ∀ u ∈ UJ, ∀ i : Fin (m + 1), u + Finsupp.single i 1 ∈ UJ := by
    intro u hu i
    refine Fin.lastCases ?_ (fun r => ?_) i
    · have hdrop : dropLast (u + Finsupp.single (Fin.last m) (1 : ℕ)) = dropLast u := by
        ext j
        have hne : j.castSucc ≠ Fin.last m := Fin.castSucc_ne_last j
        change (u + Finsupp.single (Fin.last m) (1 : ℕ)) j.castSucc = u j.castSucc
        simp [Finsupp.single_eq_of_ne hne]
      have hlast : (u + Finsupp.single (Fin.last m) (1 : ℕ)) (Fin.last m) = u (Fin.last m) + 1 := by
        simp
      simp only [UJ, Set.mem_ofPred_eq, hdrop, hlast]
      exact hLP_mono (u (Fin.last m)) hu
    · have hdrop : dropLast (u + Finsupp.single r.castSucc (1 : ℕ)) = dropLast u + Finsupp.single r 1 := by
        ext j
        change (u + Finsupp.single r.castSucc (1 : ℕ)) j.castSucc = u j.castSucc + Finsupp.single r (1 : ℕ) j
        by_cases hjr : j = r
        · subst hjr; simp
        · have hne : j.castSucc ≠ r.castSucc := fun h => hjr (Fin.castSucc_injective m h)
          simp [Finsupp.single_eq_of_ne hne, Finsupp.single_eq_of_ne hjr]
      have hlast : (u + Finsupp.single r.castSucc (1 : ℕ)) (Fin.last m) = u (Fin.last m) := by
        simp [Fin.castSucc_ne_last]
      simp only [UJ, Set.mem_ofPred_eq, hdrop, hlast]
      have hmul : monomial (dropLast u + Finsupp.single r 1) (1 : k) =
          X r * monomial (dropLast u) 1 := by
        rw [X, monomial_mul, one_mul, add_comm]
      rw [hmul]
      exact (Lseq (u (Fin.last m)) + purePowersIdeal hc' d).mul_mem_left _ hu
  let J : Ideal (MvPolynomial (Fin (m + 1)) k) :=
    Ideal.span ((fun u => monomial u (1 : k)) '' UJ)
  have hJ_hom : J.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k) := by
    apply Ideal.homogeneous_span
    rintro _ ⟨u, _, rfl⟩
    exact ⟨u.degree, monomial_mem_homogPiece (mem_monOfDeg.mpr rfl)⟩
  have hP_le_J : purePowersIdeal hc d ≤ J := by
    unfold purePowersIdeal; rw [Ideal.span_le]
    rintro _ ⟨r, rfl⟩
    dsimp only
    rw [X_pow_eq_monomial]
    apply Ideal.subset_span
    refine ⟨Finsupp.single (Fin.castLE hc r) (d r), ?_, rfl⟩
    simp only [UJ, Set.mem_ofPred_eq]
    have hlast : (Finsupp.single (Fin.castLE hc r) (d r)) (Fin.last m) = 0 := by
      have hne : Fin.last m ≠ Fin.castLE hc r := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      exact Finsupp.single_eq_of_ne hne
    have hdrop : dropLast (Finsupp.single (Fin.castLE hc r) (d r)) =
        Finsupp.single (Fin.castLE hc' r) (d r) := by
      ext j
      change (Finsupp.single (Fin.castLE hc r) (d r)) j.castSucc =
        Finsupp.single (Fin.castLE hc' r) (d r) j
      by_cases hj : j = Fin.castLE hc' r
      · subst hj
        have heq : (Fin.castLE hc' r).castSucc = Fin.castLE hc r := rfl
        rw [heq]; simp
      · have hne : j.castSucc ≠ Fin.castLE hc r := by
          intro h; apply hj; ext; simpa using congrArg Fin.val h
        rw [Finsupp.single_eq_of_ne hne, Finsupp.single_eq_of_ne hj]
    rw [hdrop, hlast, ← X_pow_eq_monomial]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨r, rfl⟩)
  have hJ_hf : ∀ e, hilbertFunction J e = hilbertFunction I e := by
    intro e
    have hhf_mon : ∀ {N : ℕ} (U : Set (Fin N →₀ ℕ)),
        (∀ u ∈ U, ∀ i : Fin N, u + Finsupp.single i 1 ∈ U) →
        ∀ deg, hilbertFunction (Ideal.span ((fun u => monomial u (1 : k)) '' U)) deg =
          ((monOfDeg N deg).filter (fun u => u ∈ U)).card := by
      intro N U hUc deg
      unfold hilbertFunction
      let A := (monOfDeg N deg).filter (fun u => u ∈ U)
      let W := Submodule.restrictScalars k (Ideal.span ((fun u => monomial u (1 : k)) '' U)) ⊓
        homogeneousSubmodule (Fin N) k deg
      let bW : Module.Basis A k W := Module.Basis.mk
        (v := fun u : A =>
          ⟨monomial u.1 (1 : k), ⟨Ideal.subset_span ⟨u.1, (Finset.mem_filter.mp u.2).2, rfl⟩,
            monomial_mem_homogPiece (Finset.mem_filter.mp u.2).1⟩⟩)
        (by
          rw [Fintype.linearIndependent_iff]
          intro g hg u
          have h1 := congrArg (fun x : W => coeff u.1 x.1) hg
          simp only [ZeroMemClass.coe_zero, coeff_zero, AddSubmonoidClass.coe_finsetSum,
            SetLike.val_smul, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul, mul_ite,
            mul_one, mul_zero] at h1
          rw [Finset.sum_eq_single u] at h1
          · simpa using h1
          · intro v _ hvu; rw [if_neg (fun h => hvu (Subtype.ext h))]
          · intro hu; exact absurd (Finset.mem_univ u) hu)
        (by
          intro x _
          have hx_supp : ∀ u ∈ x.1.support, u ∈ A := fun u hu =>
            Finset.mem_filter.mpr ⟨support_subset_monOfDeg x.2.2 hu,
              (mem_monomialIdeal_iff_support hUc x.1).mp x.2.1 u hu⟩
          have hx_eq : x = ∑ u : A, coeff u.1 x.1 •
              (⟨monomial u.1 (1 : k), ⟨Ideal.subset_span ⟨u.1, (Finset.mem_filter.mp u.2).2, rfl⟩,
                monomial_mem_homogPiece (Finset.mem_filter.mp u.2).1⟩⟩ : W) := by
            apply Subtype.ext
            rw [AddSubmonoidClass.coe_finsetSum]
            simp only [SetLike.val_smul, smul_monomial, smul_eq_mul, mul_one]
            rw [Finset.sum_coe_sort A (fun u => monomial u (coeff u x.1))]
            conv_lhs => rw [x.1.as_sum]
            exact Finset.sum_subset hx_supp fun u _ hu => by
              rw [MvPolynomial.notMem_support_iff.mp hu, monomial_zero]
          rw [hx_eq]
          exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩))
      rw [Module.finrank_eq_card_basis bW, Fintype.card_coe]
    have hqJ : quotientHF J e = ((monOfDeg (m + 1) e).filter (fun u => u ∉ UJ)).card := by
      have h1 := hilbertFunction_add_quotientHF J e
      rw [hhf_mon UJ hUJ_closed e] at h1
      have h2 : ((monOfDeg (m + 1) e).filter (fun u => u ∈ UJ)).card +
          ((monOfDeg (m + 1) e).filter (fun u => u ∉ UJ)).card = (monOfDeg (m + 1) e).card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
        congr 1; ext u; simp only [Finset.mem_union, Finset.mem_filter]; tauto
      omega
    have hq_fiber : ∀ j ∈ Finset.range (e + 1),
        ((monOfDeg (m + 1) e).filter (fun u => u ∉ UJ ∧ u (Fin.last m) = j)).card =
          quotientHF (Ibar j) (e - j) := by
      intro j hj
      have hje : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      let Uj : Set (Fin m →₀ ℕ) := { v | monomial v (1 : k) ∈ Lseq j + purePowersIdeal hc' d }
      have hUj_closed : ∀ v ∈ Uj, ∀ i : Fin m, v + Finsupp.single i 1 ∈ Uj := by
        intro v hv i
        simp only [Uj, Set.mem_ofPred_eq]
        have : monomial (v + Finsupp.single i 1) (1 : k) = X i * monomial v 1 := by
          rw [X, monomial_mul, one_mul, add_comm]
        rw [this]; exact (Lseq j + purePowersIdeal hc' d).mul_mem_left _ hv
      have hLjP_eq : Lseq j + purePowersIdeal hc' d =
          Ideal.span ((fun v => monomial v (1 : k)) '' Uj) := by
        apply le_antisymm
        · rw [Submodule.add_eq_sup]
          refine sup_le ?_ ?_
          · obtain ⟨⟨S0, hS0⟩, _⟩ := hLseq_lex j
            rw [hS0, Ideal.span_le]
            rintro _ ⟨v, hv, rfl⟩
            exact Ideal.subset_span ⟨v, Ideal.mem_sup_left (by rw [hS0]; exact Ideal.subset_span ⟨v, hv, rfl⟩), rfl⟩
          · unfold purePowersIdeal; rw [Ideal.span_le]
            rintro _ ⟨r, rfl⟩
            dsimp only
            rw [X_pow_eq_monomial]
            exact Ideal.subset_span ⟨Finsupp.single (Fin.castLE hc' r) (d r),
              Ideal.mem_sup_right (by rw [← X_pow_eq_monomial]; exact Ideal.subset_span ⟨r, rfl⟩), rfl⟩
        · rw [Ideal.span_le]; rintro _ ⟨v, hv, rfl⟩; exact hv
      have hq_Lseq : quotientHF (Ibar j) (e - j) =
          ((monOfDeg m (e - j)).filter (fun v => v ∉ Uj)).card := by
        have h1 := hilbertFunction_add_quotientHF (Ibar j) (e - j)
        rw [hLseq_hf j (e - j), hLjP_eq, hhf_mon Uj hUj_closed (e - j)] at h1
        have h2 : ((monOfDeg m (e - j)).filter (fun v => v ∈ Uj)).card +
            ((monOfDeg m (e - j)).filter (fun v => v ∉ Uj)).card = (monOfDeg m (e - j)).card := by
          rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
          congr 1; ext v; simp only [Finset.mem_union, Finset.mem_filter]; tauto
        omega
      rw [hq_Lseq]
      refine Finset.card_bij (fun u _ => dropLast u) ?_ ?_ ?_
      · intro u hu
        simp only [Finset.mem_filter, mem_monOfDeg] at hu ⊢
        refine ⟨?_, ?_⟩
        · have hsum : u.degree = (dropLast u).degree + u (Fin.last m) := by
            rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_castSucc]; rfl
          omega
        · intro hmem; apply hu.2.1; simp only [UJ, Set.mem_ofPred_eq, hu.2.2]; exact hmem
      · intro u₁ hu₁ u₂ hu₂ heq
        have h1 := (Finset.mem_filter.mp hu₁).2.2
        have h2 := (Finset.mem_filter.mp hu₂).2.2
        ext r
        refine Fin.lastCases (by rw [h1, h2]) (fun i => ?_) r
        have := congrArg (fun f : Fin m →₀ ℕ => f i) heq
        exact this
      · intro v hv
        simp only [Finset.mem_filter, mem_monOfDeg] at hv
        let u : Fin (m + 1) →₀ ℕ :=
          Finsupp.equivFunOnFinite.symm (Fin.lastCases j (fun i => v i))
        refine ⟨u, ?_, by ext i; change Fin.lastCases j (fun i => v i) i.castSucc = v i; simp⟩
        simp only [Finset.mem_filter, mem_monOfDeg]
        have hu_last : u (Fin.last m) = j := by
          change Fin.lastCases j (fun i => v i) (Fin.last m) = j; simp
        have hu_drop : dropLast u = v := by
          ext i; change Fin.lastCases j (fun i => v i) i.castSucc = v i; simp
        refine ⟨?_, ?_, hu_last⟩
        · rw [Finsupp.degree_eq_sum, Fin.sum_univ_castSucc]
          have h1 : ∑ i : Fin m, u i.castSucc = v.degree := by
            rw [Finsupp.degree_eq_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            change Fin.lastCases j (fun r => v r) i.castSucc = v i; simp
          rw [h1, hu_last, hv.1]; omega
        · intro hmem; apply hv.2
          simp only [UJ, Set.mem_ofPred_eq, hu_drop, hu_last] at hmem
          exact hmem
    have hqJ_sum : quotientHF J e = ∑ j ∈ Finset.range (e + 1), quotientHF (Ibar j) (e - j) := by
      rw [hqJ]
      have hpart : (monOfDeg (m + 1) e).filter (fun u => u ∉ UJ) =
          (Finset.range (e + 1)).biUnion
            (fun j => (monOfDeg (m + 1) e).filter (fun u => u ∉ UJ ∧ u (Fin.last m) = j)) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
        constructor
        · rintro ⟨hu_deg, hu_not⟩
          refine ⟨u (Fin.last m), ?_, hu_deg, hu_not, rfl⟩
          have hle : u (Fin.last m) ≤ ∑ i : Fin (m + 1), u i :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
          rw [← Finsupp.degree_eq_sum, mem_monOfDeg.mp hu_deg] at hle; omega
        · rintro ⟨_, _, hu_deg, hu_not, _⟩; exact ⟨hu_deg, hu_not⟩
      rw [hpart, Finset.card_biUnion]
      · exact Finset.sum_congr rfl hq_fiber
      · intro j₁ _ j₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro u h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.2.symm.trans (Finset.mem_filter.mp h2).2.2)
    have hqI_eq := quotientHF_eq_sum_colon hI e
    have h1 := hilbertFunction_add_quotientHF J e
    have h2 := hilbertFunction_add_quotientHF I e
    dsimp only [Ibar, Ij] at hqJ_sum
    omega
  obtain ⟨L, hL_lex, hL_hf⟩ := hCL J hJ_hom hP_le_J
  exact ⟨L, hL_lex, fun e => (hJ_hf e).symm.trans (hL_hf e)⟩
end ArtinianRed
lemma quotientHF_succ_le_of_le_n2 (I : Ideal (MvPolynomial (Fin 2) k)) (e : ℕ)
    (hle : quotientHF I e ≤ e) :
    quotientHF I (e + 1) ≤ quotientHF I e := by
  classical
  have hcard : ∀ m : ℕ, (monOfDeg 2 m).card = m + 1 := by
    intro m
    have hbij : (monOfDeg 2 m).card = (Finset.range (m + 1)).card := by
      refine Finset.card_bij (fun u _ => u 0) ?_ ?_ ?_
      · intro u hu
        rw [Finset.mem_range]
        have hsum : u 0 + u 1 = m := by
          have := mem_monOfDeg.mp hu
          rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at this
        omega
      · intro u₁ hu₁ u₂ hu₂ heq
        have h1 : u₁ 0 + u₁ 1 = m := by
          have := mem_monOfDeg.mp hu₁; rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at this
        have h2 : u₂ 0 + u₂ 1 = m := by
          have := mem_monOfDeg.mp hu₂; rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at this
        ext j; fin_cases j <;> simp at * <;> omega
      · intro a ha
        have ham : a ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        let u : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm (Fin.cons a (Fin.cons (m - a) finZeroElim))
        refine ⟨u, ?_, rfl⟩
        rw [mem_monOfDeg, Finsupp.degree_eq_sum, Fin.sum_univ_two]
        change a + (m - a) = m; omega
    rw [hbij, Finset.card_range]
  have hadd_e := hilbertFunction_add_quotientHF I e
  have hadd_e1 := hilbertFunction_add_quotientHF I (e + 1)
  rw [hcard e] at hadd_e
  rw [hcard (e + 1)] at hadd_e1
  have hpos : 0 < hilbertFunction I e := by omega
  let V : Submodule k (homogPiece 2 k e) := idealSub I e
  have hV_pos : 0 < Module.finrank k V := by
    have h1 := Submodule.finrank_quotient_add_finrank V
    rw [finrank_homogPiece, hcard e] at h1
    change quotientHF I e + Module.finrank k V = e + 1 at h1
    omega
  let mulX (i : Fin 2) : homogPiece 2 k e →ₗ[k] homogPiece 2 k (e + 1) := {
    toFun := fun x => ⟨X i * x.1, by
      rw [mem_homogeneousSubmodule]
      simpa [add_comm] using (isHomogeneous_X k i).mul ((mem_homogeneousSubmodule e _).mp x.2)⟩
    map_add' := fun x y => Subtype.ext (mul_add _ x.1 y.1)
    map_smul' := fun c x => Subtype.ext (by simp [Algebra.mul_smul_comm])
  }
  have hmulX_inj : ∀ i, Function.Injective (mulX i) := by
    intro i x y hxy
    apply Subtype.ext
    have h1 : (X i : MvPolynomial (Fin 2) k) * x.1 = X i * y.1 := congrArg Subtype.val hxy
    exact mul_left_cancel₀ (MvPolynomial.X_ne_zero i) h1
  let W0 := Submodule.map (mulX 0) V
  let W1 := Submodule.map (mulX 1) V
  have hW_le : W0 ⊔ W1 ≤ idealSub I (e + 1) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [mem_idealSub]; exact I.mul_mem_left _ ((mem_idealSub x).mp hx)
    · rintro _ ⟨x, hx, rfl⟩
      rw [mem_idealSub]; exact I.mul_mem_left _ ((mem_idealSub x).mp hx)
  have hnot_le : ¬ W1 ≤ W0 := by
    intro hsub
    have hne_V : ∃ g : homogPiece 2 k e, g ∈ V ∧ g.1 ≠ 0 := by
      have : Nontrivial V := Module.nontrivial_of_finrank_pos hV_pos
      obtain ⟨⟨g, hg⟩, hne⟩ := exists_ne (0 : V)
      exact ⟨g, hg, fun h0 => hne (Subtype.ext (Subtype.ext h0))⟩
    let S : Set ℕ := { a | ∃ g : homogPiece 2 k e, g ∈ V ∧ ∃ u ∈ g.1.support, u 0 = a }
    have hS_ne : S.Nonempty := by
      obtain ⟨g, hgV, hg0⟩ := hne_V
      obtain ⟨u, hu⟩ := MvPolynomial.support_nonempty.mpr hg0
      exact ⟨u 0, g, hgV, u, hu, rfl⟩
    let a0 := Nat.find hS_ne
    obtain ⟨g, hgV, u0, hu0_supp, hu0_eq⟩ := Nat.find_spec hS_ne
    have hmin : ∀ (h : homogPiece 2 k e), h ∈ V → ∀ u ∈ h.1.support, a0 ≤ u 0 :=
      fun h hh u hu => Nat.find_min' hS_ne ⟨h, hh, u, hu, rfl⟩
    have hmemW0 : mulX 1 g ∈ W0 := hsub ⟨g, hgV, rfl⟩
    obtain ⟨h, hhV, hgh⟩ := hmemW0
    have hpoly : (X 0 : MvPolynomial (Fin 2) k) * h.1 = X 1 * g.1 := congrArg Subtype.val hgh
    let v0 := u0 + Finsupp.single 1 1
    have hcoeff_rhs : coeff v0 (X 1 * g.1) ≠ 0 := by
      have : coeff v0 (X 1 * g.1) = coeff u0 g.1 := by
        rw [X, mul_comm, coeff_mul_monomial, mul_one]
      rw [this]; exact MvPolynomial.mem_support_iff.mp hu0_supp
    have hcoeff_lhs : coeff v0 (X 0 * h.1) = 0 := by
      rw [X, coeff_monomial_mul']
      split_ifs with hle0
      · by_contra hne
        rw [one_mul] at hne
        have hmem_supp : v0 - Finsupp.single (0 : Fin 2) 1 ∈ h.1.support :=
          MvPolynomial.mem_support_iff.mpr hne
        have hge := hmin h hhV _ hmem_supp
        have h0_pos : 1 ≤ u0 0 := by
          have := Finsupp.le_def.mp hle0 0
          simp [v0] at this; exact this
        have hsub0 : (v0 - Finsupp.single (0 : Fin 2) (1 : ℕ)) 0 = a0 - 1 := by
          simp only [Finsupp.coe_tsub, Pi.sub_apply, v0, Finsupp.coe_add, Pi.add_apply,
            Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
            add_zero, hu0_eq]; rfl
        omega
      · rfl
    exact hcoeff_rhs (hpoly ▸ hcoeff_lhs)
  have hW0_lt : W0 < W0 ⊔ W1 := lt_of_le_of_ne le_sup_left (fun heq =>
    hnot_le (le_sup_right.trans heq.symm.le))
  have hfin_lt : Module.finrank k W0 < Module.finrank k ↥(W0 ⊔ W1) :=
    Submodule.finrank_lt_finrank_of_lt hW0_lt
  have hfin_W0 : Module.finrank k W0 = Module.finrank k V :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (mulX 0) (hmulX_inj 0) V)).symm
  have hfin_le : Module.finrank k ↥(W0 ⊔ W1) ≤ Module.finrank k (idealSub I (e + 1)) :=
    Submodule.finrank_mono hW_le
  have hq0 := Submodule.finrank_quotient_add_finrank V
  have hq1 := Submodule.finrank_quotient_add_finrank (idealSub I (e + 1))
  rw [finrank_homogPiece, hcard e] at hq0
  rw [finrank_homogPiece, hcard (e + 1)] at hq1
  change quotientHF I e + Module.finrank k V = e + 1 at hq0
  change quotientHF I (e + 1) + Module.finrank k (idealSub I (e + 1)) = e + 2 at hq1
  omega
end RM

namespace CDS
open MvPolynomial Finset
open scoped Pointwise
noncomputable local instance {n : ℕ} {k : Type*} [Field k] :
    GradedAlgebra (homogeneousSubmodule (Fin n) k) :=
  MvPolynomial.gradedAlgebra
noncomputable abbrev qHF {n : ℕ} {k : Type*} [Field k] (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) : ℕ :=
  KL.quotientHF I e
private lemma monOfDeg_cl_eq_kl (n e : ℕ) :
    CL.monOfDeg n e = KL.monOfDeg n e := by
  ext u
  rw [CL.mem_monOfDeg, KL.mem_monOfDeg]
private lemma boxSlice_kl_eq_cl {n c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) (e : ℕ) :
    KL.boxSlice hc d e = CL.boxSlice hc d e := by
  ext u
  simp only [KL.boxSlice, CL.boxSlice,
    CL.inBoxPred, Finset.mem_filter,
    KL.mem_monOfDeg, CL.mem_monOfDeg]
private lemma hilbertFunction_add_qHF {n : ℕ} {k : Type*} [Field k]
    (I : Ideal (MvPolynomial (Fin n) k)) (e : ℕ) :
    hilbertFunction I e + qHF I e = (CL.monOfDeg n e).card := by
  rw [monOfDeg_cl_eq_kl]
  exact KL.hilbertFunction_add_quotientHF I e
private lemma qHF_anti {n : ℕ} {k : Type*} [Field k]
    {I J : Ideal (MvPolynomial (Fin n) k)} (hIJ : I ≤ J) (e : ℕ) :
    qHF J e ≤ qHF I e := by
  have h1 := hilbertFunction_add_qHF I e
  have h2 := hilbertFunction_add_qHF J e
  have hle : hilbertFunction I e ≤ hilbertFunction J e := by
    unfold hilbertFunction
    have : FiniteDimensional k (KL.homogPiece n k e) :=
      KL.homogPiece_finiteDimensional e
    let VI : Submodule k (MvPolynomial (Fin n) k) :=
      Submodule.restrictScalars k I ⊓ homogeneousSubmodule (Fin n) k e
    let VJ : Submodule k (MvPolynomial (Fin n) k) :=
      Submodule.restrictScalars k J ⊓ homogeneousSubmodule (Fin n) k e
    have hsub : VI ≤ VJ := fun x hx => ⟨hIJ hx.1, hx.2⟩
    have : FiniteDimensional k VJ :=
      FiniteDimensional.of_injective
        (Submodule.inclusion (inf_le_right : VJ ≤ KL.homogPiece n k e))
        (Submodule.inclusion_injective _)
    exact Submodule.finrank_mono hsub
  omega
private lemma idealSub_eq_of_le_of_qHF_eq {n : ℕ} {k : Type*} [Field k]
    {I J : Ideal (MvPolynomial (Fin n) k)} (hIJ : I ≤ J) {e : ℕ} (hq : qHF I e = qHF J e) :
    KL.idealSub I e = KL.idealSub J e := by
  have : FiniteDimensional k (KL.homogPiece n k e) :=
    KL.homogPiece_finiteDimensional e
  have hle : KL.idealSub I e ≤ KL.idealSub J e :=
    fun x hx => (KL.mem_idealSub x).mpr (hIJ ((KL.mem_idealSub x).mp hx))
  have h1 := Submodule.finrank_quotient_add_finrank (KL.idealSub I e)
  have h2 := Submodule.finrank_quotient_add_finrank (KL.idealSub J e)
  change qHF I e + Module.finrank k (KL.idealSub I e) = _ at h1
  change qHF J e + Module.finrank k (KL.idealSub J e) = _ at h2
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
private lemma qHF_succ_eq_zero_of_eq_zero {n : ℕ} {k : Type*} [Field k]
    (I : Ideal (MvPolynomial (Fin n) k)) {e : ℕ} (h0 : qHF I e = 0) :
    qHF I (e + 1) = 0 := by
  have : FiniteDimensional k (KL.homogPiece n k e) :=
    KL.homogPiece_finiteDimensional e
  have htop_e : KL.idealSub I e = ⊤ := by
    by_contra hne
    have : Nontrivial (KL.homogPiece n k e ⧸ KL.idealSub I e) :=
      Submodule.Quotient.nontrivial_iff.mpr hne
    have hpos : 0 < qHF I e := Module.finrank_pos
    omega
  have hmon_e : ∀ u ∈ KL.monOfDeg n e, monomial u (1 : k) ∈ I := fun u hu => by
    have hmem : (⟨monomial u (1 : k), KL.monomial_mem_homogPiece hu⟩ :
        KL.homogPiece n k e) ∈ KL.idealSub I e := by
      rw [htop_e]; exact Submodule.mem_top
    exact (KL.mem_idealSub _).mp hmem
  have htop_e1 : KL.idealSub I (e + 1) = ⊤ := by
    rw [eq_top_iff]
    intro p _
    rw [KL.mem_idealSub]
    have hp := congrArg Subtype.val (KL.eq_sum_monOfDeg p)
    rw [AddSubmonoidClass.coe_finsetSum] at hp
    rw [hp]
    apply Ideal.sum_mem
    intro u _
    rw [SetLike.val_smul, smul_eq_C_mul]
    apply Ideal.mul_mem_left
    change monomial u.1 (1 : k) ∈ I
    have hdeg : u.1.degree = e + 1 := KL.mem_monOfDeg.mp u.2
    have hex : ∃ i : Fin n, 1 ≤ u.1 i := by
      by_contra hnone
      push Not at hnone
      have hu0 : u.1 = 0 := by
        ext i; have := hnone i; simp only [Finsupp.coe_zero, Pi.zero_apply]; omega
      rw [hu0, map_zero] at hdeg; omega
    obtain ⟨i, hi⟩ := hex
    let u' : Fin n →₀ ℕ := u.1 - Finsupp.single i 1
    have hu_eq : u' + Finsupp.single i 1 = u.1 := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [u']; omega
      · simp [u', Finsupp.single_eq_of_ne hj]
    have hu'_deg : u' ∈ KL.monOfDeg n e := by
      rw [KL.mem_monOfDeg]
      have h1 := congrArg Finsupp.degree hu_eq
      rw [map_add, Finsupp.degree_single, hdeg] at h1; omega
    have hmul : monomial u.1 (1 : k) = X i * monomial u' 1 := by
      rw [← hu_eq, X, monomial_mul, one_mul, add_comm]
    rw [hmul]
    exact I.mul_mem_left _ (hmon_e u' hu'_deg)
  unfold qHF KL.quotientHF
  rw [htop_e1]
  have : Subsingleton (KL.homogPiece n k (e + 1) ⧸
      (⊤ : Submodule k (KL.homogPiece n k (e + 1)))) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton
private lemma clNext_boxCard {n c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ) (e : ℕ) :
    BC.clNext hc d e (CL.boxSlice hc d e).card =
      (CL.boxSlice hc d (e + 1)).card := by
  unfold BC.clNext
  simp only [Nat.sub_self]
  have hlex0 : CL.lexSegBox (CL.clBound (n := n) d e) e 0 = ∅ := by
    simp [CL.lexSegBox]
  have hsh0 : CL.shadowBox (CL.clBound (n := n) d e) ∅ = ∅ := by
    simp [CL.shadowBox, CL.shadow]
  rw [hlex0, hsh0, Finset.card_empty, Nat.sub_zero]
private lemma card_boxSlice_symm {n : ℕ} (d : Fin n → ℕ) (hd : ∀ j, 1 ≤ d j)
    {e : ℕ} (he : e ≤ ∑ j : Fin n, (d j - 1)) :
    (CL.boxSlice le_rfl d (∑ j : Fin n, (d j - 1) - e)).card =
      (CL.boxSlice le_rfl d e).card := by
  classical
  set s := ∑ j : Fin n, (d j - 1)
  let uTop : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => d i - 1)
  have huTop_deg : uTop.degree = s := by rw [Finsupp.degree_eq_sum]; rfl
  refine Finset.card_bij (fun u _ => uTop - u) ?_ ?_ ?_
  · intro u hu
    rw [CL.boxSlice, Finset.mem_filter, CL.mem_monOfDeg] at hu ⊢
    have hle : u ≤ uTop := Finsupp.le_def.mpr fun i => by
      have := hu.2 i; change u i < d i at this; change u i ≤ d i - 1; omega
    refine ⟨?_, fun i => ?_⟩
    · have hadd := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
      rw [map_add, huTop_deg, hu.1] at hadd; omega
    · have := hd i; change (uTop - u) i < d i
      simp only [Finsupp.coe_tsub, Pi.sub_apply]; change d i - 1 - u i < d i; omega
  · intro u₁ hu₁ u₂ hu₂ heq
    ext i
    have h1 : u₁ i ≤ d i - 1 := by
      have := (Finset.mem_filter.mp hu₁).2 i; change u₁ i < d i at this; omega
    have h2 : u₂ i ≤ d i - 1 := by
      have := (Finset.mem_filter.mp hu₂).2 i; change u₂ i < d i at this; omega
    have h3 := congrArg (fun f : Fin n →₀ ℕ => f i) heq
    simp only [Finsupp.coe_tsub, Pi.sub_apply] at h3
    change d i - 1 - u₁ i = d i - 1 - u₂ i at h3; omega
  · intro v hv
    rw [CL.boxSlice, Finset.mem_filter, CL.mem_monOfDeg] at hv
    have hle : v ≤ uTop := Finsupp.le_def.mpr fun i => by
      have := hv.2 i; change v i < d i at this; change v i ≤ d i - 1; omega
    refine ⟨uTop - v, ?_, ?_⟩
    · rw [CL.boxSlice, Finset.mem_filter, CL.mem_monOfDeg]
      refine ⟨?_, fun i => ?_⟩
      · have hadd := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
        rw [map_add, huTop_deg, hv.1] at hadd; omega
      · have := hd i; change (uTop - v) i < d i
        simp only [Finsupp.coe_tsub, Pi.sub_apply]; change d i - 1 - v i < d i; omega
    · ext i; have := Finsupp.le_def.mp hle i
      simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega
private lemma card_boxSlice_eq_zero_of_gt {n : ℕ} (d : Fin n → ℕ)
    {e : ℕ} (he : ∑ j : Fin n, (d j - 1) < e) :
    (CL.boxSlice le_rfl d e).card = 0 := by
  classical
  rw [CL.boxSlice, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u hu hlt
  have hdeg : u.degree = e := CL.mem_monOfDeg.mp hu
  have hle : ∑ i : Fin n, u i ≤ ∑ i : Fin n, (d i - 1) := Finset.sum_le_sum fun i _ => by
    have := hlt i; change u i < d i at this; omega
  rw [← Finsupp.degree_eq_sum, hdeg] at hle; omega
private lemma list_ofFn_succ' {m : ℕ} {α : Type*} (f : Fin (m + 1) → α) :
    List.ofFn f = List.ofFn (f ∘ Fin.castSucc) ++ [f (Fin.last m)] := by
  rw [List.ofFn_succ', List.concat_eq_append]; rfl
private lemma mem_ideal_ofList_ofFn {n c : ℕ} {k : Type*} [Field k]
    (f : Fin c → MvPolynomial (Fin n) k) (i : Fin c) :
    f i ∈ Ideal.ofList (List.ofFn f) :=
  Ideal.subset_span (by simp)
private lemma ideal_ofList_le_iff {n : ℕ} {k : Type*} [Field k]
    (rs : List (MvPolynomial (Fin n) k)) (I : Ideal (MvPolynomial (Fin n) k)) :
    Ideal.ofList rs ≤ I ↔ ∀ r ∈ rs, r ∈ I := by
  change Ideal.span {x | x ∈ rs} ≤ I ↔ ∀ r ∈ rs, r ∈ I
  rw [Ideal.span_le]
  rfl
private lemma ideal_ofList_ofFn_le {n c : ℕ} {k : Type*} [Field k]
    {f : Fin c → MvPolynomial (Fin n) k} {I : Ideal (MvPolynomial (Fin n) k)}
    (hfI : ∀ i, f i ∈ I) :
    Ideal.ofList (List.ofFn f) ≤ I := by
  rw [ideal_ofList_le_iff]
  intro r hr
  rw [List.mem_ofFn] at hr
  obtain ⟨i, rfl⟩ := hr
  exact hfI i
private lemma isRegular_append_singleton_of_homog {n : ℕ} {k : Type*} [Field k]
    {rs : List (MvPolynomial (Fin n) k)} {g : MvPolynomial (Fin n) k} {dg : ℕ}
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) rs)
    (hr_hom : ∀ r ∈ rs, ∃ d ≥ 1, r.IsHomogeneous d)
    (hg_hom : g.IsHomogeneous dg) (hdg : 1 ≤ dg)
    (hg_reg : IsSMulRegular (MvPolynomial (Fin n) k ⧸ Ideal.ofList rs) g) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (rs ++ [g]) := by
  rw [RingTheory.Sequence.isRegular_iff] at hreg ⊢
  refine ⟨?_, ?_⟩
  · rw [RingTheory.Sequence.isWeaklyRegular_iff_Fin] at hreg ⊢
    intro i
    have hi_len : i.1 < rs.length + 1 := by simpa using i.2
    by_cases hlt : i.1 < rs.length
    · have htake : (rs ++ [g]).take i.1 = rs.take i.1 := by
        rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      have hget : (rs ++ [g])[i.1] = rs[i.1] := List.getElem_append_left hlt
      let j : Fin rs.length := ⟨i.1, hlt⟩
      have hstep := hreg.1 j
      have heq_sub : (Ideal.ofList ((rs ++ [g]).take i.1) • ⊤ :
          Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) =
          (Ideal.ofList (rs.take j.1) • ⊤ :
            Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) := by
        rw [htake]
      let e := Submodule.quotEquivOfEq _ _ heq_sub
      intro x y hxy
      apply e.injective
      apply hstep
      dsimp only at hxy ⊢
      have hmap : ∀ z, rs[j] • e z = e ((rs ++ [g])[i] • z) := fun z => by
        rw [map_smul]; change rs[i.1] • e z = (rs ++ [g])[i.1] • e z; rw [hget]
      rw [hmap, hmap, hxy]
    · have hi_eq : i.1 = rs.length := by omega
      have htake : (rs ++ [g]).take i.1 = rs := by
        rw [hi_eq, List.take_left]
      have hget : (rs ++ [g])[i.1] = g := by
        simp [hi_eq]
      have heq_sub : (Ideal.ofList ((rs ++ [g]).take i.1) • ⊤ :
          Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) =
          Ideal.ofList rs := by
        rw [htake]; simp
      let e := Submodule.quotEquivOfEq _ _ heq_sub
      intro x y hxy
      apply e.injective
      apply hg_reg
      dsimp only at hxy ⊢
      have hmap : ∀ z, g • e z = e ((rs ++ [g])[i] • z) := fun z => by
        rw [map_smul]; change g • e z = (rs ++ [g])[i.1] • e z; rw [hget]
      rw [hmap, hmap, hxy]
  · intro htop
    have hsmul : (Ideal.ofList (rs ++ [g]) • ⊤ :
        Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) =
        Ideal.ofList (rs ++ [g]) := by simp
    rw [hsmul] at htop
    have h1 : (1 : MvPolynomial (Fin n) k) ∈ Ideal.ofList (rs ++ [g]) := by
      rw [← htop]; exact Submodule.mem_top
    have hle_ker : Ideal.ofList (rs ++ [g]) ≤ RingHom.ker (MvPolynomial.eval (0 : Fin n → k)) := by
      rw [ideal_ofList_le_iff]
      intro p hp
      rw [RingHom.mem_ker]
      have hpos : ∃ d ≥ 1, p.IsHomogeneous d := by
        rw [List.mem_append, List.mem_singleton] at hp
        rcases hp with h | rfl
        · exact hr_hom p h
        · exact ⟨dg, hdg, hg_hom⟩
      obtain ⟨d, hd, hp_hom⟩ := hpos
      have hev0 : MvPolynomial.eval (0 : Fin n → k) p = coeff 0 p := by
        rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
      rw [hev0]
      by_contra hne
      have := hp_hom hne
      rw [Finsupp.weight_apply, Finsupp.sum_zero_index] at this
      omega
    have h01 : MvPolynomial.eval (0 : Fin n → k) (1 : MvPolynomial (Fin n) k) = 0 := hle_ker h1
    rw [map_one] at h01
    exact one_ne_zero h01
private lemma isRegular_of_append_left {n : ℕ} {k : Type*} [Field k]
    {l₁ l₂ : List (MvPolynomial (Fin n) k)}
    (h : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (l₁ ++ l₂)) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) l₁ := by
  rw [RingTheory.Sequence.isRegular_iff] at h ⊢
  refine ⟨?_, ?_⟩
  · rw [RingTheory.Sequence.isWeaklyRegular_iff_Fin] at h ⊢
    intro i
    have hi : i.1 < (l₁ ++ l₂).length := by rw [List.length_append]; omega
    let j : Fin (l₁ ++ l₂).length := ⟨i.1, hi⟩
    have hstep := h.1 j
    have htake : (l₁ ++ l₂).take j.1 = l₁.take i.1 :=
      List.take_append_of_le_length (Nat.le_of_lt i.2)
    have hget : (l₁ ++ l₂)[i.1] = l₁[i.1] := List.getElem_append_left i.2
    have heq_sub : (Ideal.ofList (l₁.take i.1) • ⊤ :
        Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) =
        (Ideal.ofList ((l₁ ++ l₂).take j.1) • ⊤ :
          Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) := by
      rw [htake]
    let e := Submodule.quotEquivOfEq _ _ heq_sub
    intro x y hxy
    apply e.injective
    apply hstep
    dsimp only at hxy ⊢
    have hmap : ∀ z, (l₁ ++ l₂)[j] • e z = e (l₁[i] • z) := fun z => by
      rw [map_smul]; change (l₁ ++ l₂)[i.1] • e z = l₁[i.1] • e z; rw [hget]
    rw [hmap, hmap, hxy]
  · intro htop
    apply h.2
    have hle : Ideal.ofList l₁ ≤ Ideal.ofList (l₁ ++ l₂) := by
      rw [ideal_ofList_le_iff]
      intro x hx
      exact Ideal.subset_span (by simp [hx])
    have hsmul1 : (Ideal.ofList l₁ • ⊤ :
        Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) = Ideal.ofList l₁ := by simp
    have hsmul2 : (Ideal.ofList (l₁ ++ l₂) • ⊤ :
        Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) =
        Ideal.ofList (l₁ ++ l₂) := by simp
    rw [hsmul1] at htop
    rw [hsmul2]
    exact (eq_top_iff.mpr (htop.le.trans hle)).symm
private lemma isRegular_last_smul {n m : ℕ} {k : Type*} [Field k]
    {f : Fin (m + 1) → MvPolynomial (Fin n) k}
    (hf : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (List.ofFn f)) :
    IsSMulRegular
      (MvPolynomial (Fin n) k ⧸ Ideal.ofList (List.ofFn (f ∘ Fin.castSucc)))
      (f (Fin.last m)) := by
  rw [RingTheory.Sequence.isRegular_iff, RingTheory.Sequence.isWeaklyRegular_iff_Fin] at hf
  have hm : m < (List.ofFn f).length := by simp
  let j : Fin (List.ofFn f).length := ⟨m, hm⟩
  have hstep := hf.1 j
  have htake : (List.ofFn f).take j.1 = List.ofFn (f ∘ Fin.castSucc) := by
    change (List.ofFn f).take m = List.ofFn (f ∘ Fin.castSucc)
    rw [list_ofFn_succ', List.take_left']
    simp
  have hget : (List.ofFn f)[m] = f (Fin.last m) := by
    rw [List.getElem_ofFn]; rfl
  have heq_sub : Ideal.ofList (List.ofFn (f ∘ Fin.castSucc)) =
      (Ideal.ofList ((List.ofFn f).take j.1) • ⊤ :
        Submodule (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)) := by
    rw [htake]; simp
  let e := Submodule.quotEquivOfEq _ _ heq_sub
  intro x y hxy
  apply e.injective
  apply hstep
  dsimp only at hxy ⊢
  have hmap : ∀ z, (List.ofFn f)[j] • e z = e (f (Fin.last m) • z) := fun z => by
    rw [map_smul]; change (List.ofFn f)[m] • e z = f (Fin.last m) • e z; rw [hget]
  rw [hmap, hmap, hxy]
private lemma purePowersIdeal_mono_deg {n c : ℕ} {k : Type*} [Field k] (hc : c ≤ n)
    {d₁ d₂ : Fin c → ℕ} (hle : ∀ i, d₁ i ≤ d₂ i) :
    purePowersIdeal (k := k) hc d₂ ≤ purePowersIdeal (k := k) hc d₁ := by
  unfold purePowersIdeal
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  dsimp only
  have hexp : (X (Fin.castLE hc i) : MvPolynomial (Fin n) k) ^ d₂ i =
      X (Fin.castLE hc i) ^ (d₂ i - d₁ i) * X (Fin.castLE hc i) ^ d₁ i := by
    rw [← pow_add, Nat.sub_add_cancel (hle i)]
  rw [hexp]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
private lemma artinian_reduction_helper {m c : ℕ} {k : Type*} [Field k] [Infinite k]
    (hc' : c ≤ m) (d : Fin c → ℕ) (hd : Monotone d)
    {I : Ideal (MvPolynomial (Fin (m + 1)) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k))
    {f : Fin c → MvPolynomial (Fin (m + 1)) k}
    (hfd : ∀ i, (f i).IsHomogeneous (d i))
    (hfI : ∀ i, f i ∈ I)
    (hf : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (m + 1)) k) (List.ofFn f))
    (hIH : ∀ (I' : Ideal (MvPolynomial (Fin m) k)),
      I'.IsHomogeneous (homogeneousSubmodule (Fin m) k) →
      ∀ (f' : Fin c → MvPolynomial (Fin m) k),
        (∀ i, (f' i).IsHomogeneous (d i)) →
        (∀ i, f' i ∈ I') →
        RingTheory.Sequence.IsRegular (MvPolynomial (Fin m) k) (List.ofFn f') →
        ∃ L' : Ideal (MvPolynomial (Fin m) k), IsLexIdeal L' ∧
          ∀ e, hilbertFunction I' e = hilbertFunction (L' + purePowersIdeal hc' d) e) :
    ∃ L : Ideal (MvPolynomial (Fin (m + 1)) k), IsLexIdeal L ∧
      ∀ e, hilbertFunction I e =
        hilbertFunction (L + purePowersIdeal (Nat.le_succ_of_le hc') d) e := by
  have hc_lt : c < m + 1 := Nat.lt_succ_of_le hc'
  obtain ⟨ℓ, hℓ_hom, hℓ_reg⟩ := KL.exists_regular_linForm_of_lt hc_lt hfd hf
  have hℓ_ne : ℓ ≠ 0 := by
    intro h0
    have hnt : Nontrivial (MvPolynomial (Fin (m + 1)) k ⧸ Ideal.ofList (List.ofFn f)) := by
      rw [Submodule.Quotient.nontrivial_iff]
      intro htop
      have hsmul : (Ideal.ofList (List.ofFn f) • ⊤ :
          Submodule (MvPolynomial (Fin (m + 1)) k) (MvPolynomial (Fin (m + 1)) k)) =
          Ideal.ofList (List.ofFn f) := by simp
      exact hf.2 (by rw [hsmul, htop])
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (MvPolynomial (Fin (m + 1)) k ⧸ Ideal.ofList (List.ofFn f))
    exact hxy (hℓ_reg (by simp [h0]))
  obtain ⟨Ψ, hΨ_hom, hΨ_symm_hom, hΨ_ℓ⟩ :=
    RM.exists_graded_algEquiv_map_eq hℓ_hom hℓ_ne (Fin.last m)
  let I₁ := Ideal.map Ψ.toRingHom I
  let f₁ : Fin c → MvPolynomial (Fin (m + 1)) k := fun i => Ψ (f i)
  have hI₁_hom : I₁.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k) :=
    RM.graded_algEquiv_isHomogeneous_map Ψ hΨ_hom hΨ_symm_hom hI
  have hf₁d : ∀ i, (f₁ i).IsHomogeneous (d i) := fun i => hΨ_hom (f i) (d i) (hfd i)
  have hf₁I : ∀ i, f₁ i ∈ I₁ := fun i => Ideal.mem_map_of_mem _ (hfI i)
  have hd_pos : ∀ i, 1 ≤ d i := KL.regular_homog_deg_pos hfd hf
  have hreg_app : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (m + 1)) k)
      (List.ofFn f ++ [ℓ]) :=
    isRegular_append_singleton_of_homog hf
      (fun r hr => by
        rw [List.mem_ofFn] at hr; obtain ⟨i, rfl⟩ := hr; exact ⟨d i, hd_pos i, hfd i⟩)
      hℓ_hom le_rfl hℓ_reg
  have hreg_map : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (m + 1)) k)
      (List.ofFn f₁ ++ [X (Fin.last m)]) := by
    have h := RM.graded_algEquiv_isRegular Ψ hreg_app
    rw [List.map_append, List.map_ofFn, List.map_singleton, hΨ_ℓ] at h
    exact h
  have hreg_cons : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (m + 1)) k)
      (X (Fin.last m) :: List.ofFn f₁) := by
    refine KL.isRegular_of_perm_homog hreg_map
      (List.perm_append_singleton (X (Fin.last m)) (List.ofFn f₁)) ?_
    intro r hr
    rw [List.mem_append, List.mem_ofFn, List.mem_singleton] at hr
    rcases hr with ⟨i, rfl⟩ | rfl
    · exact ⟨d i, hd_pos i, hf₁d i⟩
    · exact ⟨1, le_rfl, isHomogeneous_X k (Fin.last m)⟩
  obtain ⟨L, hL, hhf⟩ := RM.artinian_reduction_step hc' d hI₁_hom hf₁d hf₁I hreg_cons
    hIH (fun J _ hJ => CL.clements_lindstrom_main (Nat.le_succ_of_le hc') d hd J hJ)
  refine ⟨L, hL, fun e => ?_⟩
  rw [← RM.graded_algEquiv_hilbertFunction Ψ hΨ_hom hΨ_symm_hom I e]
  exact hhf e
private lemma clNext_of_ne_sigma_sub_one {m : ℕ} {k : Type*} [Field k]
    (d : Fin (m + 1) → ℕ) (hd_pos : ∀ j, 1 ≤ d j)
    (_hge_last : ∑ j : Fin m, (d j.castSucc - 1) ≤ d (Fin.last m))
    {I : Ideal (MvPolynomial (Fin (m + 1)) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k))
    {f : Fin (m + 1) → MvPolynomial (Fin (m + 1)) k}
    (hfd : ∀ i, (f i).IsHomogeneous (d i))
    (hfI : ∀ i, f i ∈ I)
    (hf : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (m + 1)) k) (List.ofFn f))
    (hEGH_d' : ∀ K : Ideal (MvPolynomial (Fin (m + 1)) k),
      K.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k) →
      (∀ j : Fin m, f j.castSucc ∈ K) →
      ∃ L : Ideal (MvPolynomial (Fin (m + 1)) k), IsLexIdeal L ∧
        ∀ e, hilbertFunction K e =
          hilbertFunction (L + purePowersIdeal (Nat.le_succ m) (d ∘ Fin.castSucc)) e) :
    (∀ e, qHF I e ≤ (CL.boxSlice le_rfl d e).card) ∧
    (∀ e, (e + 1 < d (Fin.last m) ∨ ∑ j : Fin m, (d j.castSucc - 1) ≤ e) →
      qHF I (e + 1) ≤ BC.clNext le_rfl d e (qHF I e)) := by
  let d' : Fin m → ℕ := d ∘ Fin.castSucc
  set σ := ∑ j : Fin m, (d' j - 1)
  set s := ∑ j : Fin (m + 1), (d j - 1)
  have hs_eq : s = σ + (d (Fin.last m) - 1) := Fin.sum_univ_castSucc (fun j => d j - 1)
  let 𝔟 := Ideal.ofList (List.ofFn f)
  have h𝔟I : 𝔟 ≤ I := ideal_ofList_ofFn_le hfI
  have h𝔟_hf : ∀ e, qHF 𝔟 e = (CL.boxSlice le_rfl d e).card := fun e => by
    rw [← boxSlice_kl_eq_cl]
    exact KL.quotientHF_regular_eq_card_boxSlice le_rfl hfd hf e
  have hle_box : ∀ e, qHF I e ≤ (CL.boxSlice le_rfl d e).card := fun e => by
    rw [← h𝔟_hf e]; exact qHF_anti h𝔟I e
  refine ⟨hle_box, fun e hor => ?_⟩
  rcases hor with hlt_last | hge_σ
  · obtain ⟨L, hL, hhf⟩ := hEGH_d' I hI (fun j => hfI j.castSucc)
    have hlpp := BC.lpp_to_isLPPSeq (Nat.le_succ m) d' L hL (fun t => qHF I t)
      (fun t => by rw [← hhf t]; exact hilbertFunction_add_qHF I t)
    rw [BC.clNext_eq_castSucc_of_lt_last d hlt_last]
    exact hlpp.2 e
  · change σ ≤ e at hge_σ
    by_cases hes : e < s
    · obtain ⟨hJ_hom, h𝔟J, hlink⟩ := KL.ci_linkage_quotientHF hfd hf hI h𝔟I
      let J := 𝔟.colon I
      have hf'J : ∀ j : Fin m, f j.castSucc ∈ J := fun j =>
        h𝔟J (mem_ideal_ofList_ofFn f j.castSucc)
      obtain ⟨L, hL, hhf⟩ := hEGH_d' J hJ_hom hf'J
      have hlpp := BC.lpp_to_isLPPSeq (Nat.le_succ m) d' L hL (fun t => qHF J t)
        (fun t => by rw [← hhf t]; exact hilbertFunction_add_qHF J t)
      set e' := s - e - 1
      have he'1 : e' + 1 = s - e := by omega
      have he'1_lt : e' + 1 < d (Fin.last m) := by
        have := hd_pos (Fin.last m); omega
      have hJ_step := hlpp.2 e'
      rw [← BC.clNext_eq_castSucc_of_lt_last d he'1_lt] at hJ_step
      have hJ_e' : qHF J e' = (CL.boxSlice le_rfl d e').card - qHF I (e + 1) := by
        have h1 := hlink e' (by omega)
        change qHF J e' + qHF I (s - e') = qHF 𝔟 (s - e') at h1
        have hsub : s - e' = e + 1 := by omega
        rw [hsub, h𝔟_hf (e + 1)] at h1
        have hsym := card_boxSlice_symm d hd_pos (e := e') (by omega)
        rw [hsub] at hsym
        omega
      have hJ_e'1 : qHF J (e' + 1) =
          (CL.boxSlice le_rfl d (e' + 1)).card - qHF I e := by
        have h1 := hlink (e' + 1) (by omega)
        change qHF J (e' + 1) + qHF I (s - (e' + 1)) = qHF 𝔟 (s - (e' + 1)) at h1
        have hsub : s - (e' + 1) = e := by omega
        rw [hsub, h𝔟_hf e] at h1
        have hsym := card_boxSlice_symm d hd_pos (e := e) (by omega)
        have hse : s - e = e' + 1 := by omega
        rw [hse] at hsym
        omega
      rw [hJ_e', hJ_e'1, he'1] at hJ_step
      exact BC.duality_clNext hd_pos hes (hle_box e) (hle_box (e + 1)) hJ_step
    · have hzero : qHF I (e + 1) = 0 := by
        have hle := hle_box (e + 1)
        rw [card_boxSlice_eq_zero_of_gt d (by omega)] at hle; omega
      omega
private lemma prop_3_4_strict {m : ℕ} {k : Type*} [Field k]
    (d : Fin (m + 1) → ℕ) (hd_pos : ∀ j, 1 ≤ d j)
    (hstrict : ∑ j : Fin m, (d j.castSucc - 1) < d (Fin.last m))
    {I : Ideal (MvPolynomial (Fin (m + 1)) k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k))
    {f : Fin (m + 1) → MvPolynomial (Fin (m + 1)) k}
    (hfd : ∀ i, (f i).IsHomogeneous (d i))
    (hfI : ∀ i, f i ∈ I)
    (hf : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (m + 1)) k) (List.ofFn f))
    (hEGH_d' : ∀ K : Ideal (MvPolynomial (Fin (m + 1)) k),
      K.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k) →
      (∀ j : Fin m, f j.castSucc ∈ K) →
      ∃ L : Ideal (MvPolynomial (Fin (m + 1)) k), IsLexIdeal L ∧
        ∀ e, hilbertFunction K e =
          hilbertFunction (L + purePowersIdeal (Nat.le_succ m) (d ∘ Fin.castSucc)) e) :
    ∃ L : Ideal (MvPolynomial (Fin (m + 1)) k), IsLexIdeal L ∧
      ∀ e, hilbertFunction I e = hilbertFunction (L + purePowersIdeal le_rfl d) e := by
  have hcl := clNext_of_ne_sigma_sub_one d hd_pos (Nat.le_of_lt hstrict) hI hfd hfI hf hEGH_d'
  obtain ⟨L, hL, hhf⟩ := BC.isLPPSeq_to_lpp (k := k) le_rfl d (fun e => qHF I e)
    hcl.1 (fun e => hcl.2 e (by omega))
  refine ⟨L, hL, fun e => ?_⟩
  have h1 := hilbertFunction_add_qHF I e
  have h2 := hhf e
  omega
theorem caviglia_deStefani_infinite {k : Type*} [Field k] [Infinite k] :
    ∀ (n : ℕ) {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ),
      Monotone d →
      (∀ i : Fin c, 2 ≤ (i : ℕ) → ∑ j ∈ Finset.Iio i, (d j - 1) ≤ d i) →
      ∀ (I : Ideal (MvPolynomial (Fin n) k)),
        I.IsHomogeneous (homogeneousSubmodule (Fin n) k) →
        ∀ (f : Fin c → MvPolynomial (Fin n) k),
          (∀ i, (f i).IsHomogeneous (d i)) →
          (∀ i, f i ∈ I) →
          RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (List.ofFn f) →
          ∃ L : Ideal (MvPolynomial (Fin n) k), IsLexIdeal L ∧
            ∀ e, hilbertFunction I e = hilbertFunction (L + purePowersIdeal hc d) e := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro c hc d hd hgrow I hI f hfd hfI hf
    by_cases hc0 : c = 0
    · subst hc0
      have hP0 : purePowersIdeal hc d ≤ I := by
        unfold purePowersIdeal; rw [Ideal.span_le]; rintro _ ⟨i, _⟩; exact Fin.elim0 i
      exact CL.clements_lindstrom_main hc d hd I hP0
    by_cases hlt : c < n
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      have hc' : c ≤ m := Nat.le_of_lt_succ hlt
      exact artinian_reduction_helper hc' d hd hI hfd hfI hf
        (fun I' hI' f' hf'd hf'I hf' =>
          ih m (Nat.lt_succ_self m) hc' d hd hgrow I' hI' f' hf'd hf'I hf')
    have hcn : c = n := by omega
    subst hcn
    have hd_pos : ∀ i : Fin c, 1 ≤ d i := KL.regular_homog_deg_pos hfd hf
    obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := Nat.exists_eq_succ_of_ne_zero hc0
    by_cases hd0 : d 0 = 1
    · refine RM.d0_eq_one_reduction le_rfl d hd0 hI hfd hfI hf ?_
      intro I' hI' f' hf'd hf'I hf'
      have hd'_mono : Monotone (d ∘ Fin.succ) := fun a b hab => hd (Fin.succ_le_succ_iff.mpr hab)
      have hgrow' : ∀ i : Fin m, 2 ≤ (i : ℕ) →
          ∑ j ∈ Finset.Iio i, (d j.succ - 1) ≤ d i.succ := by
        intro i hi
        have hsum_le : ∑ j ∈ Finset.Iio i, (d j.succ - 1) ≤
            ∑ j ∈ Finset.Iio i.succ, (d j - 1) := by
          have hinj : Function.Injective (Fin.succ : Fin m → Fin (m + 1)) := Fin.succ_injective m
          rw [← Finset.sum_image (f := fun j : Fin (m + 1) => d j - 1)
            (g := Fin.succ) (fun a _ b _ h => hinj h)]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
          intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          rw [Finset.mem_Iio] at hj ⊢
          exact Fin.succ_lt_succ_iff.mpr hj
        exact le_trans hsum_le (hgrow i.succ (by simp; omega))
      exact ih m (Nat.lt_succ_self m) le_rfl (d ∘ Fin.succ) hd'_mono hgrow' I' hI' f' hf'd hf'I hf'
    have hd2 : ∀ i : Fin (m + 1), 2 ≤ d i := fun i => by
      have h0 : 2 ≤ d 0 := by have := hd_pos 0; omega
      have hle : d 0 ≤ d i := hd (Fin.zero_le i)
      omega
    by_cases hm0 : m = 0
    · subst hm0
      have hf0_ne : f 0 ≠ 0 := by
        intro h0
        have hcons : List.ofFn f = [f 0] := by simp [List.ofFn_succ]
        rw [hcons, RingTheory.Sequence.isRegular_cons_iff'] at hf
        exact zero_ne_one (hf.1 (by simp [h0] : (f 0) • (0 : MvPolynomial (Fin (0 + 1)) k) = (f 0) • 1))
      let u0 : Fin 1 →₀ ℕ := Finsupp.single 0 (d 0)
      have hf0_eq : f 0 = C (coeff u0 (f 0)) * (X 0) ^ d 0 := by
        rw [X_pow_eq_monomial, C_mul_monomial, mul_one]
        ext u
        rw [coeff_monomial]
        split_ifs with hu
        · subst hu; rfl
        · by_contra hne
          have hdeg : u.degree = d 0 := by
            have hw := hfd 0 hne
            rwa [KL.weight_one_eq_deg] at hw
          apply hu; ext i; fin_cases i
          have hsum : u 0 = u.degree := by rw [Finsupp.degree_eq_sum, Fin.sum_univ_one]
          change u0 0 = u 0
          simp only [u0, Finsupp.single_eq_same]
          omega
      have hcoeff_ne : coeff u0 (f 0) ≠ 0 := by
        intro h0; apply hf0_ne; rw [hf0_eq, h0, map_zero, zero_mul]
      have hP_le : purePowersIdeal le_rfl d ≤ I := by
        unfold purePowersIdeal; rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩; fin_cases i
        change (X 0 : MvPolynomial (Fin 1) k) ^ d 0 ∈ I
        have hmul : (X 0 : MvPolynomial (Fin 1) k) ^ d 0 =
            C (coeff u0 (f 0))⁻¹ * f 0 := by
          conv_rhs => arg 2; rw [hf0_eq]
          rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hcoeff_ne, map_one, one_mul]
        rw [hmul]; exact I.mul_mem_left _ (hfI 0)
      exact CL.clements_lindstrom_main le_rfl d hd I hP_le
    by_cases hm1 : m = 1
    · subst hm1
      let 𝔟 := Ideal.ofList (List.ofFn f)
      have h𝔟I : 𝔟 ≤ I := ideal_ofList_ofFn_le hfI
      have h𝔟_hf : ∀ e, qHF 𝔟 e = (CL.boxSlice le_rfl d e).card := fun e => by
        rw [← boxSlice_kl_eq_cl]
        exact KL.quotientHF_regular_eq_card_boxSlice le_rfl hfd hf e
      have hle_box : ∀ e, qHF I e ≤ (CL.boxSlice le_rfl d e).card := fun e => by
        rw [← h𝔟_hf e]; exact qHF_anti h𝔟I e
      have hcard_mon2 : ∀ e, (CL.monOfDeg 2 e).card = e + 1 := by
        intro e
        have heq : (CL.monOfDeg 2 e).card = (Finset.range (e + 1)).card := by
          refine Finset.card_bij (fun u _ => u 0) ?_ ?_ ?_
          · intro u hu
            have hdeg := CL.mem_monOfDeg.mp hu
            rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
            rw [Finset.mem_range]; omega
          · intro u₁ hu₁ u₂ hu₂ heq0
            have h1 := CL.mem_monOfDeg.mp hu₁
            have h2 := CL.mem_monOfDeg.mp hu₂
            rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at h1 h2
            ext j; fin_cases j <;> simp at * <;> omega
          · intro a ha
            rw [Finset.mem_range] at ha
            let u : Fin 2 →₀ ℕ :=
              Finsupp.equivFunOnFinite.symm (Fin.cons a (Fin.cons (e - a) finZeroElim))
            refine ⟨u, ?_, rfl⟩
            rw [CL.mem_monOfDeg, Finsupp.degree_eq_sum, Fin.sum_univ_two]
            change a + (e - a) = e; omega
        rwa [Finset.card_range] at heq
      have hnext : ∀ e, qHF I (e + 1) ≤ BC.clNext le_rfl d e (qHF I e) := by
        intro e
        set r := qHF I e
        by_cases hr0 : r = 0
        · rw [qHF_succ_eq_zero_of_eq_zero I hr0]; exact Nat.zero_le _
        by_cases hrmax : r = (CL.boxSlice le_rfl d e).card
        · rw [hrmax, clNext_boxCard]; exact hle_box (e + 1)
        have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
        have hr_lt : r < (CL.boxSlice le_rfl d e).card :=
          lt_of_le_of_ne (hle_box e) hrmax
        have hr_le_e : r ≤ e := by
          have hsub : (CL.boxSlice le_rfl d e).card ≤
              (CL.monOfDeg 2 e).card := Finset.card_le_card (Finset.filter_subset _ _)
          rw [hcard_mon2 e] at hsub; omega
        have hstep_le : qHF I (e + 1) ≤ r :=
          RM.quotientHF_succ_le_of_le_n2 I e hr_le_e
        rw [BC.clNext_n2 d (hd2 0) (hd (by decide)) e r hr_pos hr_lt]
        split_ifs with hlt_d1
        · exact hstep_le
        · by_contra hgt
          have hq_eq : qHF I (e + 1) = r := by omega
          let Sgen : Set (MvPolynomial (Fin (1 + 1)) k) := {q ∈ I | ∃ t ≤ e, q.IsHomogeneous t}
          let Q : Ideal (MvPolynomial (Fin (1 + 1)) k) := Ideal.span Sgen
          have hQI : Q ≤ I := Ideal.span_le.mpr (fun q hq => hq.1)
          have hQ_gen : Q = Ideal.span {q ∈ Q | ∃ t ≤ e, q.IsHomogeneous t} := by
            apply le_antisymm
            · exact Ideal.span_mono (fun q hq => ⟨Ideal.subset_span hq, hq.2⟩)
            · exact Ideal.span_le.mpr (fun q hq => hq.1)
          have hQe : qHF Q e = r := by
            have hle1 : qHF I e ≤ qHF Q e := qHF_anti hQI e
            have hle2 : KL.idealSub I e ≤ KL.idealSub Q e :=
              fun x hx => (KL.mem_idealSub x).mpr (Ideal.subset_span
                ⟨(KL.mem_idealSub x).mp hx, e, le_rfl, (mem_homogeneousSubmodule _ _).mp x.2⟩)
            have h1 := Submodule.finrank_quotient_add_finrank (KL.idealSub I e)
            have h2 := Submodule.finrank_quotient_add_finrank (KL.idealSub Q e)
            have : FiniteDimensional k (KL.homogPiece (1 + 1) k e) :=
              KL.homogPiece_finiteDimensional e
            have hfm : Module.finrank k (KL.idealSub I e) ≤ Module.finrank k (KL.idealSub Q e) :=
              Submodule.finrank_mono hle2
            change qHF I e + Module.finrank k (KL.idealSub I e) =
              Module.finrank k (KL.homogPiece (1 + 1) k e) at h1
            change qHF Q e + Module.finrank k (KL.idealSub Q e) =
              Module.finrank k (KL.homogPiece (1 + 1) k e) at h2
            omega
          have hQe1 : qHF Q (e + 1) = r := by
            have hle1 : r ≤ qHF Q (e + 1) := hq_eq ▸ qHF_anti hQI (e + 1)
            have hle2 : qHF Q (e + 1) ≤ r := by
              have h := RM.quotientHF_succ_le_of_le_n2 Q e (by change qHF Q e ≤ e; omega)
              change qHF Q (e + 1) ≤ qHF Q e at h; omega
            omega
          have hsub_eq : KL.idealSub Q (e + 1) =
              KL.idealSub I (e + 1) :=
            idealSub_eq_of_le_of_qHF_eq hQI (by omega)
          have h𝔟Q : 𝔟 ≤ Q := by
            apply ideal_ofList_ofFn_le
            intro i
            have hdi_le : d i ≤ e + 1 := by
              have hle_d1 : d i ≤ d 1 := hd (Fin.le_last i)
              have := hd2 1; omega
            by_cases hle_e : d i ≤ e
            · exact Ideal.subset_span ⟨hfI i, d i, hle_e, hfd i⟩
            · have hdi_eq : d i = e + 1 := by omega
              have hmemI : (⟨f i, (mem_homogeneousSubmodule _ _).mpr (hdi_eq ▸ hfd i)⟩ :
                  KL.homogPiece 2 k (e + 1)) ∈ KL.idealSub I (e + 1) :=
                (KL.mem_idealSub _).mpr (hfI i)
              rw [← hsub_eq] at hmemI
              exact (KL.mem_idealSub _).mp hmemI
          let M := (d 0 - 1) + (d 1 - 1) + 1
          have hpos_M : 0 < qHF Q M :=
            GM.gotzmann_persistence_pos Q e hQ_gen (by change 0 < qHF Q e; omega)
              (by change qHF Q e = qHF Q (e + 1); omega) (by change qHF Q e ≤ e; omega) M
          have hzero_M : qHF Q M = 0 := by
            have h1 : qHF Q M ≤ qHF 𝔟 M := qHF_anti h𝔟Q M
            rw [h𝔟_hf M] at h1
            have hsum_d : ∑ j : Fin 2, (d j - 1) = (d 0 - 1) + (d 1 - 1) := Fin.sum_univ_two _
            rw [card_boxSlice_eq_zero_of_gt d (by rw [hsum_d]; omega)] at h1; omega
          omega
      obtain ⟨L, hL, hhf⟩ := BC.isLPPSeq_to_lpp (k := k) le_rfl d (fun e => qHF I e)
        hle_box hnext
      refine ⟨L, hL, fun e => ?_⟩
      have h1 := hilbertFunction_add_qHF I e
      have h2 := hhf e
      omega
    have hm : 2 ≤ m := by omega
    let d' : Fin m → ℕ := d ∘ Fin.castSucc
    let f' : Fin m → MvPolynomial (Fin (m + 1)) k := f ∘ Fin.castSucc
    set σ := ∑ j : Fin m, (d' j - 1)
    set s := ∑ j : Fin (m + 1), (d j - 1)
    have hs_eq : s = σ + (d (Fin.last m) - 1) := Fin.sum_univ_castSucc (fun j => d j - 1)
    have hσ_le : σ ≤ d (Fin.last m) := by
      have h := hgrow (Fin.last m) (by simp; omega)
      have hsum_eq : σ = ∑ j ∈ Finset.Iio (Fin.last m), (d j - 1) := by
        refine Finset.sum_bij (fun j _ => j.castSucc) ?_ ?_ ?_ ?_
        · intro j _; exact Finset.mem_Iio.mpr (Fin.castSucc_lt_last j)
        · intro a _ b _ hab; exact Fin.castSucc_injective m hab
        · intro b hb
          rw [Finset.mem_Iio] at hb
          exact ⟨⟨b.1, hb⟩, Finset.mem_univ _, by ext; rfl⟩
        · intro j _; rfl
      rw [← hsum_eq] at h
      exact h
    have hf'_reg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (m + 1)) k) (List.ofFn f') := by
      have hsplit : List.ofFn f = List.ofFn f' ++ [f (Fin.last m)] := list_ofFn_succ' f
      rw [hsplit] at hf
      exact isRegular_of_append_left hf
    have hd'_mono : Monotone d' := fun a b hab => hd (Fin.castSucc_le_castSucc_iff.mpr hab)
    have hgrow_d' : ∀ i : Fin m, 2 ≤ (i : ℕ) → ∑ j ∈ Finset.Iio i, (d' j - 1) ≤ d' i := by
      intro i hi
      have hsum_eq : ∑ j ∈ Finset.Iio i, (d' j - 1) =
          ∑ j ∈ Finset.Iio i.castSucc, (d j - 1) := by
        refine Finset.sum_bij (fun j _ => j.castSucc) ?_ ?_ ?_ ?_
        · intro j hj; exact Finset.mem_Iio.mpr (Fin.castSucc_lt_castSucc_iff.mpr (Finset.mem_Iio.mp hj))
        · intro a _ b _ hab; exact Fin.castSucc_injective m hab
        · intro b hb
          rw [Finset.mem_Iio] at hb
          have hb_lt : b.1 < m := lt_trans hb i.isLt
          exact ⟨⟨b.1, hb_lt⟩, Finset.mem_Iio.mpr hb, by ext; rfl⟩
        · intro j _; rfl
      rw [hsum_eq]
      exact hgrow i.castSucc (by simp; omega)
    have hEGH_d' : ∀ K : Ideal (MvPolynomial (Fin (m + 1)) k),
        K.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k) →
        (∀ j : Fin m, f' j ∈ K) →
        ∃ L : Ideal (MvPolynomial (Fin (m + 1)) k), IsLexIdeal L ∧
          ∀ e, hilbertFunction K e =
            hilbertFunction (L + purePowersIdeal (Nat.le_succ m) d') e := fun K hK hf'K =>
      artinian_reduction_helper le_rfl d' hd'_mono hK (fun j => hfd j.castSucc) hf'K hf'_reg
        (fun I' hI' f'' hf''d hf''I hf'' =>
          ih m (Nat.lt_succ_self m) le_rfl d' hd'_mono hgrow_d' I' hI' f'' hf''d hf''I hf'')
    by_cases hstrict : σ < d (Fin.last m)
    · exact prop_3_4_strict d hd_pos hstrict hI hfd hfI hf hEGH_d'
    have hlast : d (Fin.last m) = σ := by omega
    have hσ_ge2 : 2 ≤ σ := by
      let j0 : Fin m := ⟨0, by omega⟩
      let j1 : Fin m := ⟨1, by omega⟩
      have hne : j0 ≠ j1 := by intro h; have := congrArg Fin.val h; simp [j0, j1] at this
      have hsub : ∑ j ∈ ({j0, j1} : Finset (Fin m)), (d' j - 1) ≤ σ :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      rw [Finset.sum_pair hne] at hsub
      have h0 : 2 ≤ d' j0 := hd2 j0.castSucc
      have h1 : 2 ≤ d' j1 := hd2 j1.castSucc
      omega
    have hcl_other := clNext_of_ne_sigma_sub_one d hd_pos hσ_le hI hfd hfI hf hEGH_d'
    have hbox_eq_σ1 : CL.boxSlice le_rfl d (σ - 1) =
        CL.boxSlice (Nat.le_succ m) d' (σ - 1) :=
      BC.boxSlice_eq_castSucc_of_lt_last d (by omega)
    set h := qHF I (σ - 1)
    by_cases hcrit : 0 < h ∧ h < (CL.boxSlice (Nat.le_succ m) d' (σ - 1)).card ∧
        qHF I σ = h
    · obtain ⟨hh_pos, hh_lt, hqI_σ⟩ := hcrit
      have hcl_at := BC.clNext_at_sigma_sub_one hm d hd2 hlast
      have hcl_d'_h : BC.clNext (Nat.le_succ m) d' (σ - 1) h = h :=
        (hcl_at.1 h hh_pos hh_lt).1
      let 𝔟' := Ideal.ofList (List.ofFn f')
      let 𝔟 := Ideal.ofList (List.ofFn f)
      let V : Submodule k (KL.homogPiece (m + 1) k (σ - 1)) :=
        KL.idealSub I (σ - 1)
      let Q : Ideal (MvPolynomial (Fin (m + 1)) k) :=
        𝔟' ⊔ Ideal.span (Subtype.val '' (V : Set (KL.homogPiece (m + 1) k (σ - 1))))
      have h𝔟'Q : 𝔟' ≤ Q := le_sup_left
      have hQI : Q ≤ I := by
        refine sup_le (ideal_ofList_ofFn_le fun j => hfI j.castSucc) ?_
        rw [Ideal.span_le]
        rintro _ ⟨x, hx, rfl⟩
        exact (KL.mem_idealSub x).mp hx
      have hQ_hom : Q.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k) := by
        have h1 : 𝔟'.IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) k) :=
          KL.isHomogeneous_ideal_ofList fun r hr => by
            rw [List.mem_ofFn] at hr; obtain ⟨j, rfl⟩ := hr; exact ⟨d' j, hfd j.castSucc⟩
        have h2 : (Ideal.span (Subtype.val ''
            (V : Set (KL.homogPiece (m + 1) k (σ - 1))))).IsHomogeneous
              (homogeneousSubmodule (Fin (m + 1)) k) :=
          Ideal.homogeneous_span (homogeneousSubmodule (Fin (m + 1)) k) _ (by
            rintro _ ⟨x, _, rfl⟩; exact ⟨σ - 1, x.2⟩)
        exact Ideal.IsHomogeneous.sup h1 h2
      have hQ_σ1 : qHF Q (σ - 1) = h := by
        have h1 : qHF I (σ - 1) ≤ qHF Q (σ - 1) := qHF_anti hQI (σ - 1)
        have hleV : KL.idealSub I (σ - 1) ≤ KL.idealSub Q (σ - 1) :=
          fun x hx => (KL.mem_idealSub x).mpr
            (Ideal.mem_sup_right (Ideal.subset_span ⟨x, hx, rfl⟩))
        have : FiniteDimensional k (KL.homogPiece (m + 1) k (σ - 1)) :=
          KL.homogPiece_finiteDimensional (σ - 1)
        have ha := Submodule.finrank_quotient_add_finrank (KL.idealSub I (σ - 1))
        have hb := Submodule.finrank_quotient_add_finrank (KL.idealSub Q (σ - 1))
        have hfm := Submodule.finrank_mono hleV
        change qHF I (σ - 1) + _ = _ at ha
        change qHF Q (σ - 1) + _ = _ at hb
        omega
      have hQ_σ : qHF Q σ = h := by
        have h1 : h ≤ qHF Q σ := hqI_σ ▸ qHF_anti hQI σ
        obtain ⟨LQ, hLQ, hhfQ⟩ := hEGH_d' Q hQ_hom
          (fun j => h𝔟'Q (mem_ideal_ofList_ofFn f' j))
        have hlppQ := BC.lpp_to_isLPPSeq (Nat.le_succ m) d' LQ hLQ (fun t => qHF Q t)
          (fun t => by rw [← hhfQ t]; exact hilbertFunction_add_qHF Q t)
        have h2 := hlppQ.2 (σ - 1)
        have hdeg_s : σ - 1 + 1 = σ := by omega
        rw [hdeg_s, hQ_σ1, hcl_d'_h] at h2
        omega
      have hsubQ_eq : KL.idealSub Q σ = KL.idealSub I σ :=
        idealSub_eq_of_le_of_qHF_eq hQI (by omega)
      have hflast_Q : f (Fin.last m) ∈ Q := by
        have hmemI : (⟨f (Fin.last m), (mem_homogeneousSubmodule _ _).mpr (hlast ▸ hfd (Fin.last m))⟩ :
            KL.homogPiece (m + 1) k σ) ∈ KL.idealSub I σ :=
          (KL.mem_idealSub _).mpr (hfI (Fin.last m))
        rw [← hsubQ_eq] at hmemI
        exact (KL.mem_idealSub _).mp hmemI
      have hflast_reg : IsSMulRegular (MvPolynomial (Fin (m + 1)) k ⧸ 𝔟') (f (Fin.last m)) :=
        isRegular_last_smul hf
      by_cases hh_le : h ≤ σ - 1
      · by_cases hspec : m = 2 ∧ d ⟨0, by omega⟩ = 2
        · obtain ⟨rfl, hd0_2⟩ := hspec
          have hd0_2' : d 0 = 2 := hd0_2
          have hσ_eq_d1 : σ = d 1 := by
            have : σ = (d 0 - 1) + (d 1 - 1) := Fin.sum_univ_two (fun j => d' j - 1)
            have h1 : 2 ≤ d 1 := hd2 1
            omega
          have hd_last : d (Fin.last 2) = d 1 := by rw [hlast, hσ_eq_d1]
          obtain ⟨v, hvV, hv_reg⟩ :=
            KL.exists_regular_in_subspace V hflast_Q hflast_reg
          have hvI : v.1 ∈ I := (KL.mem_idealSub v).mp hvV
          have hv_hom : v.1.IsHomogeneous (d 1 - 1) := by
            let vpoly : MvPolynomial (Fin 3) k := v.1
            have hv' : vpoly.IsHomogeneous (σ - 1) := (mem_homogeneousSubmodule _ _).mp v.2
            rw [hσ_eq_d1] at hv'
            exact hv'
          have hreg_f'v : RingTheory.Sequence.IsRegular (MvPolynomial (Fin 3) k)
              (List.ofFn f' ++ [v.1]) :=
            isRegular_append_singleton_of_homog hf'_reg
              (fun r hr => by
                rw [List.mem_ofFn] at hr; obtain ⟨j, rfl⟩ := hr
                exact ⟨d' j, hd_pos j.castSucc, hfd j.castSucc⟩)
              hv_hom (by have := hd2 1; omega) hv_reg
          have hofFn_f' : List.ofFn f' = [f 0, f 1] := by
            simp [List.ofFn_succ, f']
          by_cases hd1_2 : d 1 = 2
          · let dtilde : Fin 3 → ℕ := ![1, 2, 2]
            let ftilde : Fin 3 → MvPolynomial (Fin 3) k := ![v.1, f 0, f 1]
            have hperm : (List.ofFn f' ++ [v.1]).Perm (List.ofFn ftilde) := by
              rw [hofFn_f']
              have hlist : List.ofFn ftilde = [v.1, f 0, f 1] := by simp [List.ofFn_succ, ftilde]
              rw [hlist]
              exact List.perm_append_singleton v.1 [f 0, f 1]
            have hftilde_reg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin 3) k)
                (List.ofFn ftilde) := by
              refine KL.isRegular_of_perm_homog hreg_f'v hperm ?_
              intro r hr
              rw [hofFn_f'] at hr
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with (rfl | rfl) | rfl
              · exact ⟨d 0, hd_pos 0, hfd 0⟩
              · exact ⟨d 1, hd_pos 1, hfd 1⟩
              · exact ⟨d 1 - 1, by omega, hv_hom⟩
            have hftilde_hom : ∀ i : Fin 3, (ftilde i).IsHomogeneous (dtilde i) := by
              intro i; fin_cases i
              · simpa [ftilde, dtilde, hd1_2] using hv_hom
              · simpa [ftilde, dtilde, hd0_2'] using hfd 0
              · simpa [ftilde, dtilde, hd1_2] using hfd 1
            have hftilde_I : ∀ i : Fin 3, ftilde i ∈ I := by
              intro i; fin_cases i
              · exact hvI
              · exact hfI 0
              · exact hfI 1
            obtain ⟨L₁, hL₁, hhf₁⟩ := RM.d0_eq_one_reduction le_rfl dtilde rfl
              hI hftilde_hom hftilde_I hftilde_reg
              (fun I' hI' f'' hf''d hf''I hf'' =>
                ih 2 (by omega) le_rfl (dtilde ∘ Fin.succ)
                  (fun a b hab => by fin_cases a <;> fin_cases b <;> simp [dtilde] at hab ⊢)
                  (fun i hi => by fin_cases i <;> simp at hi)
                  I' hI' f'' hf''d hf''I hf'')
            have hP_le : purePowersIdeal le_rfl d ≤ L₁ + purePowersIdeal le_rfl dtilde := by
              refine le_trans (purePowersIdeal_mono_deg le_rfl fun i => ?_) le_sup_right
              fin_cases i
              · change 1 ≤ d 0; omega
              · change 2 ≤ d 1; omega
              · change 2 ≤ d (Fin.last 2); omega
            obtain ⟨L, hL, hhf⟩ := CL.clements_lindstrom_main le_rfl d hd
              (L₁ + purePowersIdeal le_rfl dtilde) hP_le
            exact ⟨L, hL, fun e => (hhf₁ e).trans (hhf e)⟩
          · have hd1_ge3 : 3 ≤ d 1 := by have := hd2 1; omega
            let dtilde : Fin 3 → ℕ := ![2, d 1 - 1, d 1]
            let ftilde : Fin 3 → MvPolynomial (Fin 3) k := ![f 0, v.1, f 1]
            have hperm : (List.ofFn f' ++ [v.1]).Perm (List.ofFn ftilde) := by
              rw [hofFn_f']
              have hlist : List.ofFn ftilde = [f 0, v.1, f 1] := by simp [List.ofFn_succ, ftilde]
              rw [hlist]
              change [f 0, f 1, v.1].Perm [f 0, v.1, f 1]
              exact List.Perm.cons (f 0) (List.Perm.swap v.1 (f 1) [])
            have hftilde_reg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin 3) k)
                (List.ofFn ftilde) := by
              refine KL.isRegular_of_perm_homog hreg_f'v hperm ?_
              intro r hr
              rw [hofFn_f'] at hr
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with (rfl | rfl) | rfl
              · exact ⟨d 0, hd_pos 0, hfd 0⟩
              · exact ⟨d 1, hd_pos 1, hfd 1⟩
              · exact ⟨d 1 - 1, by omega, hv_hom⟩
            have hftilde_hom : ∀ i : Fin 3, (ftilde i).IsHomogeneous (dtilde i) := by
              intro i; fin_cases i
              · simpa [ftilde, dtilde, hd0_2'] using hfd 0
              · simpa [ftilde, dtilde] using hv_hom
              · simpa [ftilde, dtilde] using hfd 1
            have hftilde_I : ∀ i : Fin 3, ftilde i ∈ I := by
              intro i; fin_cases i
              · exact hfI 0
              · exact hvI
              · exact hfI 1
            have hdtilde_pos : ∀ i : Fin 3, 1 ≤ dtilde i := fun i => by
              fin_cases i <;> simp [dtilde] <;> omega
            have hdtilde_strict : ∑ j : Fin 2, (dtilde j.castSucc - 1) < dtilde (Fin.last 2) := by
              rw [Fin.sum_univ_two]; simp [dtilde]; omega
            have hdtilde'_mono : Monotone (dtilde ∘ Fin.castSucc) := fun a b hab => by
              fin_cases a <;> fin_cases b <;> simp [dtilde] at hab ⊢ <;> omega
            have hftilde'_reg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin 3) k)
                (List.ofFn (ftilde ∘ Fin.castSucc)) := by
              have hsplit : List.ofFn ftilde =
                  List.ofFn (ftilde ∘ Fin.castSucc) ++ [ftilde (Fin.last 2)] :=
                list_ofFn_succ' ftilde
              rw [hsplit] at hftilde_reg
              exact isRegular_of_append_left hftilde_reg
            have hEGH_tilde' : ∀ K : Ideal (MvPolynomial (Fin 3) k),
                K.IsHomogeneous (homogeneousSubmodule (Fin 3) k) →
                (∀ j : Fin 2, ftilde j.castSucc ∈ K) →
                ∃ L : Ideal (MvPolynomial (Fin 3) k), IsLexIdeal L ∧
                  ∀ e, hilbertFunction K e =
                    hilbertFunction (L + purePowersIdeal (Nat.le_succ 2) (dtilde ∘ Fin.castSucc)) e :=
              fun K hK hKmem =>
                artinian_reduction_helper le_rfl (dtilde ∘ Fin.castSucc) hdtilde'_mono hK
                  (fun j => hftilde_hom j.castSucc) hKmem hftilde'_reg
                  (fun I' hI' f'' hf''d hf''I hf'' =>
                    ih 2 (by omega) le_rfl (dtilde ∘ Fin.castSucc) hdtilde'_mono
                      (fun i hi => by fin_cases i <;> simp at hi)
                      I' hI' f'' hf''d hf''I hf'')
            obtain ⟨L₁, hL₁, hhf₁⟩ := prop_3_4_strict dtilde hdtilde_pos hdtilde_strict
              hI hftilde_hom hftilde_I hftilde_reg hEGH_tilde'
            have hP_le : purePowersIdeal le_rfl d ≤ L₁ + purePowersIdeal le_rfl dtilde := by
              refine le_trans (purePowersIdeal_mono_deg le_rfl fun i => ?_) le_sup_right
              fin_cases i
              · change 2 ≤ d 0; omega
              · change d 1 - 1 ≤ d 1; omega
              · change d 1 ≤ d (Fin.last 2); omega
            obtain ⟨L, hL, hhf⟩ := CL.clements_lindstrom_main le_rfl d hd
              (L₁ + purePowersIdeal le_rfl dtilde) hP_le
            exact ⟨L, hL, fun e => (hhf₁ e).trans (hhf e)⟩
        · exfalso
          have hd'_le : ∀ j : Fin m, d' j ≤ σ - 1 := by
            intro j
            have hj_lt : j.1 < m := j.isLt
            by_cases hm2 : m = 2
            · have hd0_ge3 : 3 ≤ d ⟨0, by omega⟩ := by
                have := hd2 ⟨0, by omega⟩; omega
              let jother : Fin m := if j.1 = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
              have hne : j ≠ jother := by
                intro heq; have hv := congrArg Fin.val heq
                dsimp only [jother] at hv
                split_ifs at hv with h0
                · simp only at hv; omega
                · simp only at hv; omega
              have hpair : ∑ i ∈ ({j, jother} : Finset (Fin m)), (d' i - 1) ≤ σ :=
                Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
              rw [Finset.sum_pair hne] at hpair
              have hoth : 3 ≤ d' jother := by
                have hle0 : d ⟨0, by omega⟩ ≤ d jother.castSucc :=
                  hd (Fin.zero_le jother.castSucc)
                change 3 ≤ d jother.castSucc; omega
              have hdj : 2 ≤ d' j := hd2 j.castSucc
              omega
            · have hm3 : 3 ≤ m := by omega
              let j1 : Fin m := if j.1 = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
              let j2 : Fin m :=
                if j.1 = 0 then ⟨2, by omega⟩
                else if j.1 = 1 then ⟨2, by omega⟩
                else ⟨1, by omega⟩
              have hne1 : j ≠ j1 := by
                intro heq; have hv := congrArg Fin.val heq
                dsimp only [j1] at hv
                split_ifs at hv <;> simp only at hv <;> omega
              have hne2 : j ≠ j2 := by
                intro heq; have hv := congrArg Fin.val heq
                dsimp only [j2] at hv
                split_ifs at hv <;> simp only at hv <;> omega
              have hne12 : j1 ≠ j2 := by
                intro heq; have hv := congrArg Fin.val heq
                dsimp only [j1, j2] at hv
                split_ifs at hv <;> simp only at hv <;> omega
              have hsub : ∑ i ∈ ({j, j1, j2} : Finset (Fin m)), (d' i - 1) ≤ σ :=
                Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
              rw [Finset.sum_insert (by simp [hne1, hne2]), Finset.sum_pair hne12] at hsub
              have h0 : 2 ≤ d' j := hd2 j.castSucc
              have h1 : 2 ≤ d' j1 := hd2 j1.castSucc
              have h2 : 2 ≤ d' j2 := hd2 j2.castSucc
              omega
          have hQ_gen : Q = Ideal.span {q ∈ Q | ∃ t ≤ σ - 1, q.IsHomogeneous t} := by
            apply le_antisymm
            · refine sup_le ?_ ?_
              · rw [ideal_ofList_le_iff]
                intro r hr
                rw [List.mem_ofFn] at hr
                obtain ⟨j, rfl⟩ := hr
                exact Ideal.subset_span ⟨h𝔟'Q (mem_ideal_ofList_ofFn f' j),
                  d' j, hd'_le j, hfd j.castSucc⟩
              · rw [Ideal.span_le]
                rintro _ ⟨x, hx, rfl⟩
                exact Ideal.subset_span ⟨Ideal.mem_sup_right (Ideal.subset_span ⟨x, hx, rfl⟩),
                  σ - 1, le_rfl, (mem_homogeneousSubmodule _ _).mp x.2⟩
            · exact Ideal.span_le.mpr (fun q hq => hq.1)
          have h𝔟Q : 𝔟 ≤ Q := by
            apply ideal_ofList_ofFn_le
            intro i
            cases i using Fin.lastCases with
            | last => exact hflast_Q
            | cast j => exact h𝔟'Q (mem_ideal_ofList_ofFn f' j)
          have hpos_M : 0 < qHF Q (s + 1) :=
            GM.gotzmann_persistence_pos Q (σ - 1) hQ_gen
              (by change 0 < qHF Q (σ - 1); omega)
              (by change qHF Q (σ - 1) = qHF Q (σ - 1 + 1)
                  have hdeg_s : σ - 1 + 1 = σ := by omega
                  rw [hdeg_s]; omega)
              (by change qHF Q (σ - 1) ≤ σ - 1; omega)
              (s + 1)
          have hzero_M : qHF Q (s + 1) = 0 := by
            have h1 : qHF Q (s + 1) ≤ qHF 𝔟 (s + 1) := qHF_anti h𝔟Q (s + 1)
            have h2 : qHF 𝔟 (s + 1) = (CL.boxSlice le_rfl d (s + 1)).card := by
              rw [← boxSlice_kl_eq_cl]
              exact KL.quotientHF_regular_eq_card_boxSlice le_rfl hfd hf (s + 1)
            rw [h2, card_boxSlice_eq_zero_of_gt d (by omega)] at h1; omega
          omega
      · exfalso
        have hh_ge : σ ≤ h := by omega
        obtain ⟨g, hgV, hg_reg⟩ :=
          KL.exists_regular_in_subspace V hflast_Q hflast_reg
        let gSeq : Fin (m + 1) → MvPolynomial (Fin (m + 1)) k := Fin.lastCases g.1 f'
        let d'' : Fin (m + 1) → ℕ := Fin.lastCases (σ - 1) d'
        have hgSeq_hom : ∀ i, (gSeq i).IsHomogeneous (d'' i) := fun i => by
          cases i using Fin.lastCases with
          | last => simpa [gSeq, d''] using (mem_homogeneousSubmodule _ _).mp g.2
          | cast j =>
            simp only [gSeq, d'', Fin.lastCases_castSucc]
            exact hfd j.castSucc
        have hgSeq_I : ∀ i, gSeq i ∈ I := fun i => by
          cases i using Fin.lastCases with
          | last =>
            simp only [gSeq, Fin.lastCases_last]
            exact (KL.mem_idealSub g).mp hgV
          | cast j =>
            simp only [gSeq, Fin.lastCases_castSucc]
            exact hfI j.castSucc
        have hgSeq_reg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (m + 1)) k)
            (List.ofFn gSeq) := by
          have hsplit : List.ofFn gSeq = List.ofFn f' ++ [g.1] := by
            rw [list_ofFn_succ']
            have h1 : gSeq ∘ Fin.castSucc = f' := by ext j; simp [gSeq]
            have h2 : gSeq (Fin.last m) = g.1 := by simp [gSeq]
            rw [h1, h2]
          rw [hsplit]
          exact isRegular_append_singleton_of_homog hf'_reg
            (fun r hr => by
              rw [List.mem_ofFn] at hr; obtain ⟨j, rfl⟩ := hr
              exact ⟨d' j, hd_pos j.castSucc, hfd j.castSucc⟩)
            ((mem_homogeneousSubmodule _ _).mp g.2) (by omega) hg_reg
        let 𝔤 := Ideal.ofList (List.ofFn gSeq)
        have h𝔤I : 𝔤 ≤ I := ideal_ofList_ofFn_le hgSeq_I
        obtain ⟨hK_hom, h𝔤K, hlink⟩ :=
          KL.ci_linkage_quotientHF hgSeq_hom hgSeq_reg hI h𝔤I
        let K := 𝔤.colon I
        have hs'' : ∑ i : Fin (m + 1), (d'' i - 1) = 2 * σ - 2 := by
          rw [Fin.sum_univ_castSucc]
          simp only [d'', Fin.lastCases_castSucc, Fin.lastCases_last]
          change σ + (σ - 1 - 1) = 2 * σ - 2; omega
        have h𝔤_hf : ∀ e, qHF 𝔤 e = (CL.boxSlice le_rfl d'' e).card := fun e => by
          rw [← boxSlice_kl_eq_cl]
          exact KL.quotientHF_regular_eq_card_boxSlice le_rfl hgSeq_hom hgSeq_reg e
        have hK_σ2 : qHF K (σ - 2) + h =
            (CL.boxSlice (Nat.le_succ m) d' (σ - 2)).card := by
          have h1 := hlink (σ - 2) (by rw [hs'']; omega)
          change qHF K (σ - 2) + qHF I (∑ i : Fin (m + 1), (d'' i - 1) - (σ - 2)) =
            qHF 𝔤 (∑ i : Fin (m + 1), (d'' i - 1) - (σ - 2)) at h1
          have hsub : ∑ i : Fin (m + 1), (d'' i - 1) - (σ - 2) = σ := by rw [hs'']; omega
          rw [hsub, hqI_σ, h𝔤_hf σ] at h1
          have hbox2 := hcl_at.2.2
          change (CL.boxSlice le_rfl d'' σ).card =
            (CL.boxSlice (Nat.le_succ m) d' (σ - 2)).card at hbox2
          omega
        have hK_σ1 : qHF K (σ - 1) + h =
            (CL.boxSlice (Nat.le_succ m) d' (σ - 1)).card - 1 := by
          have h1 := hlink (σ - 1) (by rw [hs'']; omega)
          change qHF K (σ - 1) + qHF I (∑ i : Fin (m + 1), (d'' i - 1) - (σ - 1)) =
            qHF 𝔤 (∑ i : Fin (m + 1), (d'' i - 1) - (σ - 1)) at h1
          have hsub : ∑ i : Fin (m + 1), (d'' i - 1) - (σ - 1) = σ - 1 := by rw [hs'']; omega
          rw [hsub, h𝔤_hf (σ - 1)] at h1
          have hbox1 := hcl_at.2.1
          change (CL.boxSlice le_rfl d'' (σ - 1)).card =
            (CL.boxSlice (Nat.le_succ m) d' (σ - 1)).card - 1 at hbox1
          omega
        have hf'K : ∀ j : Fin m, f' j ∈ K := fun j =>
          h𝔤K (by
            have hmem := mem_ideal_ofList_ofFn gSeq j.castSucc
            simpa [gSeq] using hmem)
        obtain ⟨LK, hLK, hhfK⟩ := hEGH_d' K hK_hom hf'K
        have hlppK := BC.lpp_to_isLPPSeq (Nat.le_succ m) d' LK hLK (fun t => qHF K t)
          (fun t => by rw [← hhfK t]; exact hilbertFunction_add_qHF K t)
        have hstepK := hlppK.2 (σ - 2)
        have hdeg_s1 : σ - 2 + 1 = σ - 1 := by omega
        unfold BC.clNext at hstepK
        rw [hdeg_s1] at hstepK
        have hdiff_h : (CL.boxSlice (Nat.le_succ m) d' (σ - 2)).card -
            qHF K (σ - 2) = h := by omega
        rw [hdiff_h] at hstepK
        have hsh_le_box : (CL.shadowBox
            (CL.clBound (n := m + 1) d' (σ - 2))
            (CL.lexSegBox
              (CL.clBound (n := m + 1) d' (σ - 2)) (σ - 2) h)).card ≤
            (CL.boxSlice (Nat.le_succ m) d' (σ - 1)).card := by
          have hlex_sh := (CL.isLexBox_lexSegBox
            (CL.clBound (n := m + 1) d' (σ - 2)) (σ - 2) h).shadowBox
          have hsub := Finset.card_le_card hlex_sh.1
          rwa [hdeg_s1, CL.monBox_clBound_eq_boxSlice
            (Nat.le_succ m) d' (σ - 2) (σ - 1) (by omega)] at hsub
        have hh_le_box2 : h ≤ (CL.boxSlice (Nat.le_succ m) d' (σ - 2)).card := by
          omega
        have hsh_ge := BC.shadowBox_ge_add_two_of_ge_sigma hm d'
          (fun j => hd2 j.castSucc) hh_ge hh_le_box2
        change h + 2 ≤ (CL.shadowBox
            (CL.clBound (n := m + 1) d' (σ - 2))
            (CL.lexSegBox
              (CL.clBound (n := m + 1) d' (σ - 2)) (σ - 2) h)).card at hsh_ge
        omega
    · have hnext : ∀ e, qHF I (e + 1) ≤ BC.clNext le_rfl d e (qHF I e) := by
        intro e
        by_cases he : e = σ - 1
        · subst he
          have hdeg_s : σ - 1 + 1 = σ := by omega
          rw [hdeg_s]
          by_cases hh0 : h = 0
          · have hq0 : qHF I (σ - 1) = 0 := hh0
            have hq_s0 : qHF I σ = 0 := by
              have := qHF_succ_eq_zero_of_eq_zero I hq0
              rwa [hdeg_s] at this
            rw [hq_s0]; exact Nat.zero_le _
          by_cases hhmax : h = (CL.boxSlice (Nat.le_succ m) d' (σ - 1)).card
          · have hmax_d : qHF I (σ - 1) = (CL.boxSlice le_rfl d (σ - 1)).card := by
              rw [hbox_eq_σ1]; exact hhmax
            rw [hmax_d, clNext_boxCard, hdeg_s]
            exact hcl_other.1 σ
          have hh_pos : 0 < h := Nat.pos_of_ne_zero hh0
          have hh_lt : h < (CL.boxSlice (Nat.le_succ m) d' (σ - 1)).card := by
            have hle := hcl_other.1 (σ - 1)
            rw [hbox_eq_σ1] at hle
            exact lt_of_le_of_ne hle hhmax
          have hcl_at := (BC.clNext_at_sigma_sub_one hm d hd2 hlast).1 h hh_pos hh_lt
          obtain ⟨LI, hLI, hhfI⟩ := hEGH_d' I hI (fun j => hfI j.castSucc)
          have hlppI := BC.lpp_to_isLPPSeq (Nat.le_succ m) d' LI hLI (fun t => qHF I t)
            (fun t => by rw [← hhfI t]; exact hilbertFunction_add_qHF I t)
          have hle_h : qHF I σ ≤ h := by
            have h1 := hlppI.2 (σ - 1)
            rwa [hdeg_s, hcl_at.1] at h1
          have hne_h : qHF I σ ≠ h := fun heq => hcrit ⟨hh_pos, hh_lt, heq⟩
          change qHF I σ ≤ BC.clNext le_rfl d (σ - 1) h
          rw [hcl_at.2]
          omega
        · exact hcl_other.2 e (by change e + 1 < d (Fin.last m) ∨ σ ≤ e; omega)
      obtain ⟨L, hL, hhf⟩ := BC.isLPPSeq_to_lpp (k := k) le_rfl d (fun e => qHF I e)
        hcl_other.1 hnext
      refine ⟨L, hL, fun e => ?_⟩
      have h1 := hilbertFunction_add_qHF I e
      have h2 := hhf e
      omega
theorem caviglia_deStefani_main {n : ℕ} {k : Type*} [Field k]
    {c : ℕ} (hc : c ≤ n) (d : Fin c → ℕ)
    (hd : Monotone d) (hgrow : ∀ i : Fin c, 2 ≤ (i : ℕ) → ∑ j ∈ Finset.Iio i, (d j - 1) ≤ d i)
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) k))
    (f : Fin c → MvPolynomial (Fin n) k) (hfd : ∀ i, (f i).IsHomogeneous (d i))
    (hfI : ∀ i, f i ∈ I)
    (hf : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) (List.ofFn f)) :
    ∃ L : Ideal (MvPolynomial (Fin n) k), IsLexIdeal L ∧
      ∀ e, hilbertFunction I e = hilbertFunction (L + purePowersIdeal hc d) e := by
  have : Infinite (RM.Kext k) := RM.infinite_ratFunc k
  apply RM.lex_descend_from_ratFunc n k hc d I
  let IK := Ideal.map (RM.mapK n k) I
  let fK : Fin c → MvPolynomial (Fin n) (RM.Kext k) :=
    fun i => RM.mapK n k (f i)
  have hIK : IK.IsHomogeneous (homogeneousSubmodule (Fin n) (RM.Kext k)) :=
    RM.isHomogeneous_idealMap n k hI
  have hfKd : ∀ i, (fK i).IsHomogeneous (d i) := fun i => RM.isHomogeneous_mapK n k (hfd i)
  have hfKI : ∀ i, fK i ∈ IK := fun i => Ideal.mem_map_of_mem _ (hfI i)
  have hfK : RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) (RM.Kext k))
      (List.ofFn fK) := by
    have h := RM.isRegular_mapK n k hf
    rwa [List.map_ofFn] at h
  exact caviglia_deStefani_infinite n hc d hd hgrow IK hIK fK hfKd hfKI hfK
end CDS
theorem OMA.solution :
    type_of% @EisenbudGreenHarris.eisenbud_green_harris.variants.caviglia_deStefani :=
  fun {_ _ _ _} hc d hd hgrow I hI f hfd hfI hf =>
    CDS.caviglia_deStefani_main hc d hd hgrow I hI f hfd hfI hf
