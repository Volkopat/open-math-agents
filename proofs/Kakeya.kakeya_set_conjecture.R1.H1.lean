import OMAReductions.R_Kakeya_kakeya_set_conjecture_R1
import Mathlib

-- Step Kakeya.kakeya_set_conjecture.R1.H1: hypothesis H1 of reduction Kakeya.kakeya_set_conjecture.R1
-- Credit: @ivillar. From the definition of Hausdorff measure (scale 1/2): a cover by sets t_j with sum of diam^s < eps; each nonempty t_j of positive diameter sits in the ball around one of its points of radius 2 diam(t_j) <= 1, and the pieces of diameter 0 (singletons) form a countable set Z.

/-! Step Kakeya.kakeya_set_conjecture.R1.H1. -/

open MeasureTheory Metric
open scoped ENNReal

namespace P8Kakeya

theorem cover : ∀ {n : ℕ} {s : ℝ}, 0 < s → ∀ {F : Set (EuclideanSpace ℝ (Fin n))},
    Measure.hausdorffMeasure s F = 0 → ∀ {ε : ℝ≥0∞}, 0 < ε →
    ∃ (x : ℕ → (EuclideanSpace ℝ (Fin n))) (r : ℕ → ℝ) (Z : Set (EuclideanSpace ℝ (Fin n))),
      Z.Countable ∧ F ⊆ Z ∪ ⋃ j, Metric.ball (x j) (r j) ∧
      (∀ j, 0 ≤ r j ∧ r j ≤ 1) ∧
      (∑' j, ENNReal.ofReal (r j) ^ s) ≤ (2 : ℝ≥0∞) ^ s * ε := by
  intro n s hs F hF ε hε
  classical
  rw [Measure.hausdorffMeasure_apply, ENNReal.iSup_eq_zero] at hF
  have h1 := hF (1 / 2)
  rw [ENNReal.iSup_eq_zero] at h1
  have h2 := h1 (by norm_num)
  obtain ⟨t, ht⟩ := iInf_lt_iff.mp (lt_of_eq_of_lt h2 hε)
  obtain ⟨hcov, ht⟩ := iInf_lt_iff.mp ht
  obtain ⟨hdiam, hsum⟩ := iInf_lt_iff.mp ht
  let x : ℕ → EuclideanSpace ℝ (Fin n) := fun j => if h : (t j).Nonempty then h.some else 0
  let good : ℕ → Prop := fun j => (t j).Nonempty ∧ ediam (t j) ≠ 0
  let r : ℕ → ℝ := fun j => if good j then 2 * (ediam (t j)).toReal else 0
  let Z : Set (EuclideanSpace ℝ (Fin n)) := ⋃ j, {y | y ∈ t j ∧ ediam (t j) = 0}
  have hfin : ∀ j, ediam (t j) ≠ ⊤ := fun j => ne_top_of_le_ne_top (by norm_num) (hdiam j)
  refine ⟨x, r, Z, ?_, ?_, ?_, ?_⟩
  · apply Set.countable_iUnion
    intro j
    apply Set.Subsingleton.countable
    intro a ha b hb
    exact (ediam_eq_zero_iff.mp ha.2) ha.1 hb.1
  · intro y hy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov hy)
    by_cases h0 : ediam (t j) = 0
    · exact Or.inl (Set.mem_iUnion.mpr ⟨j, hj, h0⟩)
    · right
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      have hne : (t j).Nonempty := ⟨y, hj⟩
      have hg : good j := ⟨hne, h0⟩
      have hxj : x j = hne.some := dif_pos hne
      have hrj : r j = 2 * (ediam (t j)).toReal := if_pos hg
      rw [Metric.mem_ball, hxj, hrj]
      have hed : edist y hne.some ≤ ediam (t j) := edist_le_ediam_of_mem hj hne.some_mem
      have hdl : dist y hne.some ≤ (ediam (t j)).toReal := by
        rw [dist_edist]
        exact ENNReal.toReal_mono (hfin j) hed
      have hpos : 0 < (ediam (t j)).toReal := ENNReal.toReal_pos h0 (hfin j)
      linarith
  · intro j
    by_cases hg : good j
    · have hrj : r j = 2 * (ediam (t j)).toReal := if_pos hg
      rw [hrj]
      have hle : (ediam (t j)).toReal ≤ 1 / 2 := by
        have := ENNReal.toReal_mono (by norm_num) (hdiam j)
        simpa using this
      constructor
      · positivity
      · linarith
    · have hrj : r j = 0 := if_neg hg
      rw [hrj]
      norm_num
  · calc (∑' j, ENNReal.ofReal (r j) ^ s)
        ≤ ∑' j, (2 : ℝ≥0∞) ^ s * ⨆ _ : (t j).Nonempty, ediam (t j) ^ s := by
          apply ENNReal.tsum_le_tsum
          intro j
          by_cases hg : good j
          · have hrj : r j = 2 * (ediam (t j)).toReal := if_pos hg
            rw [hrj, iSup_pos hg.1, ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_toReal (hfin j), ENNReal.ofReal_ofNat,
              ENNReal.mul_rpow_of_nonneg _ _ hs.le]
          · have hrj : r j = 0 := if_neg hg
            rw [hrj, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hs]
            simp
      _ = (2 : ℝ≥0∞) ^ s * ∑' j, ⨆ _ : (t j).Nonempty, ediam (t j) ^ s := ENNReal.tsum_mul_left
      _ ≤ (2 : ℝ≥0∞) ^ s * ε := mul_le_mul' le_rfl hsum.le

end P8Kakeya

theorem OMA.solution : OMA.R_Kakeya_kakeya_set_conjecture_R1.H1 :=
  P8Kakeya.cover
