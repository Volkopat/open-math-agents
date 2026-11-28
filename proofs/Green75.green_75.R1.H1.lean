import OMAReductions.R_Green75_green_75_R1
import Mathlib

-- Step Green75.green_75.R1.H1: hypothesis H1 of reduction Green75.green_75.R1
-- Credit: @marcusbuffett
-- Kupitz-Perles in general position: from the lexicographically lowest point p the other
-- points are totally ordered by angle, and the line from p to the median point has imbalance
-- at most 1.

open Green75 Finset

namespace G75Step

/-- Antisymmetry of the cross product in its last two arguments. -/
lemma cross_swap (p q x : ℝ × ℝ) : cross p q x = - cross p x q := by
  unfold cross; ring

/-- Transitivity of the angular order around `p` for points in the closed upper-right half plane
seen from the lexicographic minimum `p`. -/
lemma cross_trans (p u v w : ℝ × ℝ)
    (hu : p.1 < u.1 ∨ (p.1 = u.1 ∧ p.2 < u.2))
    (hv : p.1 < v.1 ∨ (p.1 = v.1 ∧ p.2 < v.2))
    (hw : p.1 < w.1 ∨ (p.1 = w.1 ∧ p.2 < w.2))
    (huv : 0 < cross p u v) (hvw : 0 < cross p v w) : 0 < cross p u w := by
  unfold cross at *
  have key : (v.1 - p.1) * ((u.1 - p.1) * (w.2 - p.2) - (u.2 - p.2) * (w.1 - p.1)) =
      (u.1 - p.1) * ((v.1 - p.1) * (w.2 - p.2) - (v.2 - p.2) * (w.1 - p.1)) +
      (w.1 - p.1) * ((u.1 - p.1) * (v.2 - p.2) - (u.2 - p.2) * (v.1 - p.1)) := by ring
  have hu1 : 0 ≤ u.1 - p.1 := by rcases hu with h | ⟨h, _⟩ <;> linarith
  have hw1 : 0 ≤ w.1 - p.1 := by rcases hw with h | ⟨h, _⟩ <;> linarith
  rcases hv with hv | ⟨hv1, hv2⟩
  · have hv' : 0 < v.1 - p.1 := by linarith
    rcases hu with hu' | ⟨hu1', hu2'⟩
    · have : 0 < (v.1 - p.1) * ((u.1 - p.1) * (w.2 - p.2) - (u.2 - p.2) * (w.1 - p.1)) := by
        rw [key]; nlinarith [mul_pos (sub_pos.mpr hu') hvw, mul_nonneg hw1 huv.le]
      exact pos_of_mul_pos_right this hv'.le
    · rcases hw with hw' | ⟨hw1', hw2'⟩
      · have : 0 < (v.1 - p.1) * ((u.1 - p.1) * (w.2 - p.2) - (u.2 - p.2) * (w.1 - p.1)) := by
          rw [key]; nlinarith [mul_pos (sub_pos.mpr hw') huv, mul_nonneg hu1 hvw.le]
        exact pos_of_mul_pos_right this hv'.le
      · exfalso
        rw [← hu1'] at huv
        simp only [sub_self, zero_mul, zero_sub] at huv
        nlinarith [mul_pos (sub_pos.mpr hu2') hv']
  · exfalso
    have hv1' : v.1 - p.1 = 0 := by linarith
    rw [hv1'] at hvw
    nlinarith [mul_nonneg (sub_pos.mpr hv2).le hw1]

theorem h1 : ∀ X : Finset (ℝ × ℝ), 2 ≤ #X →
    (∀ p ∈ X, ∀ q ∈ X, ∀ x ∈ X, p ≠ q → x ≠ p → x ≠ q → cross p q x ≠ 0) →
    ∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧ imbalance X p q ≤ 1 := by
  classical
  intro X hX hgen
  have hne : X.Nonempty := card_pos.mp (by omega)
  obtain ⟨p, hp, hmin⟩ := X.exists_min_image (fun x => toLex x) hne
  -- every other point lies strictly after `p` in the lexicographic order
  have hpos : ∀ x ∈ X, x ≠ p → p.1 < x.1 ∨ (p.1 = x.1 ∧ p.2 < x.2) := by
    intro x hx hxp
    have h := hmin x hx
    rcases (Prod.Lex.le_iff).mp h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, lt_of_le_of_ne h2 ?_⟩
      intro h3; exact hxp (Prod.ext h1.symm h3.symm)
  set Y := X.erase p with hY
  have hYcard : #Y = #X - 1 := card_erase_of_mem hp
  -- the number of points to the right of the ray from `p` through `q`
  let R : ℝ × ℝ → ℕ := fun q => #(Y.filter fun x => cross p q x < 0)
  have hRX : ∀ q, rightCount X p q = R q := by
    intro q
    unfold rightCount
    congr 1
    ext x
    simp only [mem_filter, hY, mem_erase]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨⟨?_, hx⟩, h⟩
      rintro rfl; rw [cross_self_left] at h; exact lt_irrefl _ h
    · rintro ⟨⟨_, hx⟩, h⟩; exact ⟨hx, h⟩
  -- strict monotonicity of `R` along the angular order
  have hRlt : ∀ q ∈ Y, ∀ q' ∈ Y, cross p q q' < 0 → R q' < R q := by
    intro q hq q' hq' hlt
    apply card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨q', ?_, ?_⟩
      · simp only [mem_filter]; exact ⟨hq', hlt⟩
      · simp only [mem_filter, cross_self_right, lt_irrefl, and_false, not_false_eq_true]
    · intro x hx
      simp only [mem_filter] at hx ⊢
      refine ⟨hx.1, ?_⟩
      have hxY := hx.1
      rw [hY, mem_erase] at hxY hq hq'
      have h1 : 0 < cross p x q' := by rw [cross_swap] at hx; linarith [hx.2]
      have h2 : 0 < cross p q' q := by rw [cross_swap] at hlt; linarith
      have := cross_trans p x q' q (hpos x hxY.2 hxY.1) (hpos q' hq'.2 hq'.1)
        (hpos q hq.2 hq.1) h1 h2
      rw [cross_swap]; linarith
  have hRinj : ∀ q ∈ Y, ∀ q' ∈ Y, R q = R q' → q = q' := by
    intro q hq q' hq' he
    by_contra hqq
    have hq1 := hq; have hq1' := hq'
    rw [hY, mem_erase] at hq1 hq1'
    have h0 := hgen p hp q hq1.2 q' hq1'.2 (Ne.symm hq1.1) hq1'.1 (Ne.symm hqq)
    rcases lt_or_gt_of_ne h0 with h | h
    · exact absurd he (hRlt q hq q' hq' h).ne'
    · have h' : cross p q' q < 0 := by rw [cross_swap]; linarith
      exact absurd he (hRlt q' hq' q hq h').ne
  have hRle : ∀ q ∈ Y, R q < #Y := by
    intro q hq
    apply card_lt_card
    rw [Finset.ssubset_iff_of_subset (filter_subset _ _)]
    exact ⟨q, hq, by simp [cross_self_right]⟩
  -- `R` is a bijection from `Y` onto `range #Y`, so the median value is attained
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Y) (t := range #Y)
    (fun q _ => R q) (fun q hq => mem_range.mpr (hRle q hq))
    (fun a b ha hb h => hRinj a ha b hb h) (by simp)
  have hYpos : 0 < #Y := by omega
  obtain ⟨q, hq, hqR⟩ := hsurj ((#Y - 1) / 2) (mem_range.mpr (by omega))
  have hq1 := hq
  rw [hY, mem_erase] at hq1
  refine ⟨p, hp, q, hq1.2, Ne.symm hq1.1, ?_⟩
  -- left and right counts add up to `#X - 2`
  have hsplit : leftCount X p q + rightCount X p q + 2 = #X := by
    unfold leftCount rightCount
    have hdisj : Disjoint (X.filter fun x => 0 < cross p q x) (X.filter fun x => cross p q x < 0) := by
      rw [disjoint_filter]; intro x _ h1 h2; linarith
    rw [← card_union_of_disjoint hdisj]
    have hpq : p ≠ q := Ne.symm hq1.1
    have hrest : (X.filter fun x => 0 < cross p q x) ∪ (X.filter fun x => cross p q x < 0) =
        (X.erase p).erase q := by
      ext x
      simp only [mem_union, mem_filter, mem_erase]
      constructor
      · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
        · refine ⟨?_, ?_, hx⟩ <;> rintro rfl
          · rw [cross_self_right] at h; exact lt_irrefl _ h
          · rw [cross_self_left] at h; exact lt_irrefl _ h
        · refine ⟨?_, ?_, hx⟩ <;> rintro rfl
          · rw [cross_self_right] at h; exact lt_irrefl _ h
          · rw [cross_self_left] at h; exact lt_irrefl _ h
      · rintro ⟨hxq, hxp, hx⟩
        rcases lt_or_gt_of_ne (hgen p hp q hq1.2 x hx hpq hxp hxq) with h | h
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl ⟨hx, h⟩
    rw [hrest, card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hpq, hq1.2⟩), card_erase_of_mem hp]
    omega
  rw [hRX, ← hqR] at hsplit
  unfold imbalance
  rw [hRX, ← hqR]
  rw [abs_le]
  constructor <;> omega

end G75Step

theorem OMA.solution : OMA.R_Green75_green_75_R1.H1 := G75Step.h1
