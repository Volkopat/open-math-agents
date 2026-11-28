import OMAStatements.S_oeis_a246396
import Mathlib

-- Problem: A246396: Nonnegative integers k satisfying cos(k) <= 0 and cos(k+1) <= 0.
-- Upstream: formal-conjectures statements/oeis-a246396.lean:0 (declaration OMA.S_oeis_a246396.main)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof.  Let t be a term: cos t <= 0 and cos (t + 1) <= 0.  By the sum formula
--   cos t + cos (t + 1) = 2 cos (t + 1/2) cos (1/2),
-- and cos (1/2) > 0, so cos (t + 1/2) <= 0.  Again by the sum formula
--   cos (t - 1) + cos (t + 2) = 2 cos (t + 1/2) cos (3/2),
-- and cos (3/2) > 0 because 3/2 < pi/2 (as pi > 3).  Hence cos (t - 1) + cos (t + 2) <= 0, so
-- cos (t + 2) <= 0 or cos (t - 1) <= 0.  In the first case t + 1 is a term.  In the second case
-- t - 1 is a term (and t >= 1 since cos 0 = 1 > 0).

theorem OMA.solution : type_of% @OMA.S_oeis_a246396.main := by
  intro t h
  obtain ⟨h0, h1⟩ := h
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have c12 : 0 < Real.cos (1 / 2 : ℝ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have c32 : 0 < Real.cos (3 / 2 : ℝ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have e1 : Real.cos (t : ℝ) + Real.cos ((t : ℝ) + 1)
      = 2 * Real.cos ((t : ℝ) + 1 / 2) * Real.cos (1 / 2 : ℝ) := by
    rw [Real.cos_add_cos]
    have a1 : ((t : ℝ) + ((t : ℝ) + 1)) / 2 = (t : ℝ) + 1 / 2 := by ring
    have a2 : ((t : ℝ) - ((t : ℝ) + 1)) / 2 = -(1 / 2 : ℝ) := by ring
    rw [a1, a2, Real.cos_neg]
  have e2 : Real.cos ((t : ℝ) - 1) + Real.cos ((t : ℝ) + 2)
      = 2 * Real.cos ((t : ℝ) + 1 / 2) * Real.cos (3 / 2 : ℝ) := by
    rw [Real.cos_add_cos]
    have a1 : ((t : ℝ) - 1 + ((t : ℝ) + 2)) / 2 = (t : ℝ) + 1 / 2 := by ring
    have a2 : ((t : ℝ) - 1 - ((t : ℝ) + 2)) / 2 = -(3 / 2 : ℝ) := by ring
    rw [a1, a2, Real.cos_neg]
  have hmid : Real.cos ((t : ℝ) + 1 / 2) ≤ 0 := by
    by_contra hneg
    have hpos : 0 < Real.cos ((t : ℝ) + 1 / 2) := not_le.1 hneg
    have : 0 < 2 * Real.cos ((t : ℝ) + 1 / 2) * Real.cos (1 / 2 : ℝ) := by positivity
    linarith
  have hsum : Real.cos ((t : ℝ) - 1) + Real.cos ((t : ℝ) + 2) ≤ 0 := by
    rw [e2]
    have : Real.cos ((t : ℝ) + 1 / 2) * Real.cos (3 / 2 : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hmid c32.le
    linarith
  by_cases hnext : Real.cos ((t : ℝ) + 2) ≤ 0
  · left
    refine ⟨?_, ?_⟩
    · have : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
      rw [this]
      exact h1
    · have : ((t + 1 : ℕ) : ℝ) + 1 = (t : ℝ) + 2 := by push_cast; ring
      rw [this]
      exact hnext
  · right
    have hnext' : 0 < Real.cos ((t : ℝ) + 2) := not_le.1 hnext
    have hprev : Real.cos ((t : ℝ) - 1) ≤ 0 := by linarith
    have ht : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · exfalso
        rw [h] at h0
        simp at h0
        linarith
      · exact h
    refine ⟨ht, ?_, ?_⟩
    · have : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
        rw [Nat.cast_sub ht]
        simp
      rw [this]
      exact hprev
    · have : ((t - 1 : ℕ) : ℝ) + 1 = (t : ℝ) := by
        rw [Nat.cast_sub ht]
        simp
      rw [this]
      exact h0
