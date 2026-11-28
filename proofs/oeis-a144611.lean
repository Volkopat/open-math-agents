import OMAStatements.S_oeis_a144611
import Mathlib

-- Disproof at n = 40 (Danny Rorabaugh, OEIS A144611, Mar 14 2015: the two words first disagree at 40).
-- slopeFloor 41 - slopeFloor 40 = 24 - 23 = 1 (since 57 < 41 sqrt 2 <= 58 and 56 < 40 sqrt 2 <= 57),
-- logFloor 41 - logFloor 40 - 1 = 64 - 63 - 1 = 0 (since 2^64 <= 3^41 < 2^65 and 2^63 <= 3^40 < 2^64).

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a144611.main) := by
  intro h
  have h40 := h 40
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg 2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have s41 : OMA.S_oeis_a144611.slopeFloor 41 = 24 := by
    unfold OMA.S_oeis_a144611.slopeFloor
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> nlinarith
  have s40 : OMA.S_oeis_a144611.slopeFloor 40 = 23 := by
    unfold OMA.S_oeis_a144611.slopeFloor
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> nlinarith
  have l41 : OMA.S_oeis_a144611.logFloor 41 = 64 := by
    unfold OMA.S_oeis_a144611.logFloor
    rw [Int.floor_eq_iff, le_div_iff₀ hl2, div_lt_iff₀ hl2]
    have e1 := Real.log_le_log (by positivity) (show ((2 : ℝ) ^ 64) ≤ (3 : ℝ) ^ 41 by norm_num)
    have e2 := Real.log_lt_log (by positivity) (show ((3 : ℝ) ^ 41) < (2 : ℝ) ^ 65 by norm_num)
    rw [Real.log_pow, Real.log_pow] at e1 e2
    push_cast at e1 e2 ⊢
    constructor <;> linarith
  have l40 : OMA.S_oeis_a144611.logFloor 40 = 63 := by
    unfold OMA.S_oeis_a144611.logFloor
    rw [Int.floor_eq_iff, le_div_iff₀ hl2, div_lt_iff₀ hl2]
    have e1 := Real.log_le_log (by positivity) (show ((2 : ℝ) ^ 63) ≤ (3 : ℝ) ^ 40 by norm_num)
    have e2 := Real.log_lt_log (by positivity) (show ((3 : ℝ) ^ 40) < (2 : ℝ) ^ 64 by norm_num)
    rw [Real.log_pow, Real.log_pow] at e1 e2
    push_cast at e1 e2 ⊢
    constructor <;> linarith
  rw [s41, s40, l41, l40] at h40
  norm_num at h40
