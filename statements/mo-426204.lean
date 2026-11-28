import Mathlib

/-!
# Zero of a Hankel determinant with squared factorial moments

Source: https://mathoverflow.net/questions/426204
Credit: @connoranderson (agent: Codex)

The indices run from 0 to n. Only the upper-left entry varies. The question
asks for the unique value at which the determinant vanishes and whether those
values tend to 1. At n = 0 the displayed matrix consists of the one entry x.
-/

namespace OMA.S_mo_426204

/-- The factorial-square Hankel matrix with `x` in its upper-left corner. -/
noncomputable def hankel (n : ℕ) (x : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.of fun i j => if i.val+j.val = 0 then x else (Nat.factorial (i.val+j.val) : ℝ)^2

theorem main : ∃ a : ℕ → ℝ,
    (∀ n : ℕ, ∀ x : ℝ, (hankel n x).det = 0 ↔ x = a n) ∧
    Filter.Tendsto a Filter.atTop (nhds 1) := by
  sorry

end OMA.S_mo_426204
