import OMAReductions.R_itp_courtade_kumar_R1
import Mathlib

open Real Finset
-- Step itp-courtade-kumar.R1.H2: finite-sum entropy decomposition of mutual information.

namespace CourtadeKumarBridge

open OMA.S_itp_courtade_kumar
open scoped BigOperators

lemma bitFlipKernel_pos {n : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < (1 : ℝ) / 2)
    (x y : Cube n) : 0 < bitFlipKernel p x y := by
  unfold bitFlipKernel
  apply prod_pos
  intro i _
  split_ifs
  · linarith
  · exact hp

lemma jointProbability_nonneg {n : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < (1 : ℝ) / 2)
    (f : Cube n → Bool) (b : Bool) (y : Cube n) :
    0 ≤ jointProbability p f b y := by
  unfold jointProbability cubeAverage
  apply div_nonneg
  · apply sum_nonneg
    intro x _
    split_ifs
    · exact (bitFlipKernel_pos hp hp' x y).le
    · exact le_rfl
  · positivity

lemma mi_term_eq {n : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < (1 : ℝ) / 2)
    (f : Cube n → Bool) (b : Bool) (y : Cube n) :
    (if 0 < jointProbability p f b y then
      jointProbability p f b y * log (jointProbability p f b y /
        (functionMarginal p f b * observationMarginal p f y))
     else 0) =
      jointProbability p f b y * log (jointProbability p f b y) -
        jointProbability p f b y * log (functionMarginal p f b) -
        jointProbability p f b y * log (observationMarginal p f y) := by
  by_cases hpos : 0 < jointProbability p f b y
  · rw [if_pos hpos]
    have hfb : 0 < functionMarginal p f b := by
      have hle : jointProbability p f b y ≤ functionMarginal p f b := by
        unfold functionMarginal
        exact single_le_sum (fun y' _ => jointProbability_nonneg hp hp' f b y')
          (mem_univ y)
      exact lt_of_lt_of_le hpos hle
    have hob : 0 < observationMarginal p f y := by
      have hle : jointProbability p f b y ≤ observationMarginal p f y := by
        unfold observationMarginal
        exact single_le_sum (fun b' _ => jointProbability_nonneg hp hp' f b' y)
          (mem_univ b)
      exact lt_of_lt_of_le hpos hle
    rw [log_div hpos.ne' (mul_pos hfb hob).ne', log_mul hfb.ne' hob.ne']
    ring
  · rw [if_neg hpos]
    have hzero : jointProbability p f b y = 0 :=
      le_antisymm (not_lt.mp hpos) (jointProbability_nonneg hp hp' f b y)
    simp [hzero]

end CourtadeKumarBridge

open OMA.S_itp_courtade_kumar CourtadeKumarBridge in
open scoped BigOperators in
theorem OMA.solution : OMA.R_itp_courtade_kumar_R1.H2 := by
  intro n p hp hp' f
  unfold mutualInformation
  congr 1
  simp_rw [mi_term_eq hp hp' f, sum_sub_distrib]
  have hB : (∑ b : Bool, ∑ y : Cube n,
      jointProbability p f b y * log (functionMarginal p f b)) =
      -∑ b : Bool, negMulLog (functionMarginal p f b) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro b _
    rw [← sum_mul, negMulLog]
    unfold functionMarginal
    ring
  have hY : (∑ b : Bool, ∑ y : Cube n,
      jointProbability p f b y * log (observationMarginal p f y)) =
      -∑ y : Cube n, negMulLog (observationMarginal p f y) := by
    rw [sum_comm, ← sum_neg_distrib]
    apply sum_congr rfl
    intro y _
    rw [← sum_mul, negMulLog]
    unfold observationMarginal
    ring
  have hJ : (∑ b : Bool, ∑ y : Cube n,
      jointProbability p f b y * log (jointProbability p f b y)) =
      -∑ z : Bool × Cube n, negMulLog (jointProbability p f z.1 z.2) := by
    rw [Fintype.sum_prod_type]
    simp_rw [negMulLog, neg_mul, sum_neg_distrib, neg_neg]
  rw [hB, hY, hJ]
  ring
