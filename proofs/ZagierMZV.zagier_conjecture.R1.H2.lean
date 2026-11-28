import OMAReductions.R_ZagierMZV_zagier_conjecture_R1
import Mathlib

-- Step ZagierMZV.zagier_conjecture.R1.H2: hypothesis H2 of reduction ZagierMZV.zagier_conjecture.R1.
-- The Q-span of the multiple zeta values of weight 1 has dimension 0 (Zagier's d_1 = 0).
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: there is no admissible index of weight 1: the empty index has weight 0, and a nonempty admissible
-- index starts with an entry >= 2. So the set of weight-1 values is empty and its span is the zero space.

open ZagierMZV

theorem OMA.solution : OMA.R_ZagierMZV_zagier_conjecture_R1.H2 := by
  have hset : mzvSetOfWeight 1 = ∅ := by
    ext x
    constructor
    · rintro ⟨s, ⟨hadm, hw⟩, rfl⟩
      exfalso
      cases s with
      | nil =>
        have hw' : (0 : ℕ) = 1 := by simpa [weight] using hw
        omega
      | cons a rest =>
        have ha : 1 < a := hadm.1
        have hw' : a + rest.sum = 1 := by simpa [weight] using hw
        omega
    · intro hx
      cases hx
  show Module.finrank ℚ (mzvSpanOfWeight 1) = zagierDim 1
  have hd : zagierDim 1 = 0 := rfl
  unfold mzvSpanOfWeight
  rw [hset, hd, Submodule.span_empty]
  exact finrank_bot ℚ ℝ
