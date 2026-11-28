import Mathlib

/-!
# Off-diagonal corners of normal matrices

Source: Mustafa Said, https://mathoverflow.net/questions/158834/a-matrix-completion-problem
See Bhatia and Choi, *Corners of normal matrices*, https://arxiv.org/abs/0707.2138.
Credit: @wtho704

The question asks for a sequence of normal block matrices of size `2 * n`,
with square blocks `A`, `B`, `C`, and `D` of size `n`, such that the ratio
of the operator norms of `B` and `C` tends to infinity.
-/

open Filter

namespace OMA.S_mo_158834

/-- The usual operator norm on Euclidean complex space. -/
noncomputable def operatorNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) M‖

theorem main :
    ∃ A B C D : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ,
      (∀ n, IsStarNormal (Matrix.fromBlocks (A n) (B n) (C n) (D n))) ∧
      (∀ᶠ n in atTop, C n ≠ 0) ∧
      Tendsto (fun n => operatorNorm (B n) / operatorNorm (C n)) atTop atTop := by
  sorry

end OMA.S_mo_158834
