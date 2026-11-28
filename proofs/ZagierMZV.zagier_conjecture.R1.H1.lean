import OMAReductions.R_ZagierMZV_zagier_conjecture_R1
import Mathlib

-- Step ZagierMZV.zagier_conjecture.R1.H1: hypothesis H1 of reduction ZagierMZV.zagier_conjecture.R1.
-- The Q-span of the multiple zeta values of weight 0 has dimension 1 (Zagier's d_0 = 1).
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: the only admissible index of weight 0 is the empty one (a nonempty admissible index starts with an
-- entry >= 2), and its value is 1. So the set of weight-0 values is {1}, whose Q-span in R has dimension 1.

open ZagierMZV

theorem OMA.solution : OMA.R_ZagierMZV_zagier_conjecture_R1.H1 := by
  have hset : mzvSetOfWeight 0 = {1} := by
    ext x
    constructor
    · rintro ⟨s, ⟨hadm, hw⟩, rfl⟩
      cases s with
      | nil =>
        rw [Set.mem_singleton_iff]
        rfl
      | cons a rest =>
        exfalso
        have ha : 1 < a := hadm.1
        have hw' : a + rest.sum = 0 := by simpa [weight] using hw
        omega
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨[], ⟨trivial, rfl⟩, rfl⟩
  show Module.finrank ℚ (mzvSpanOfWeight 0) = zagierDim 0
  have hd : zagierDim 0 = 1 := rfl
  unfold mzvSpanOfWeight
  rw [hset, hd]
  exact finrank_span_singleton one_ne_zero
