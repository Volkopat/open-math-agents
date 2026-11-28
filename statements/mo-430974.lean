import Mathlib.Analysis.Matrix.PosDef

/-!
# Sharp lower eigenvalue bound for correlation matrices

Source: https://mathoverflow.net/questions/430974
Question by getraparth, 22 September 2022, CC BY-SA 4.0.
Credit: @etaubman

The source asks for the best lower bound given only the dimension, unit diagonal,
positive semidefiniteness, and an off-diagonal magnitude bound. The statement
preserves its epsilon range and gives the exact bound, with attainment. Bounding
all eigenvalues and attaining the bound expresses that it is the minimum.
-/

open scoped ComplexOrder

namespace OMA.S_mo_430974

def Admissible (n : ℕ) (ε : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A.PosSemidef ∧ (∀ i, A i i = 1) ∧ ∀ i j, i ≠ j → ‖A i j‖ ≤ ε

theorem main : ∀ (n : ℕ), 0 < n → ∀ (ε : ℝ), 0 ≤ ε → ε ≤ 1 / Real.sqrt 2 →
    (∀ A : Matrix (Fin n) (Fin n) ℂ, Admissible n ε A →
      ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) (μ : ℂ) →
        max 0 (1 - ((n : ℝ) - 1) * ε) ≤ μ) ∧
    ∃ A : Matrix (Fin n) (Fin n) ℂ, Admissible n ε A ∧
      Module.End.HasEigenvalue (Matrix.toLin' A)
        ((max 0 (1 - ((n : ℝ) - 1) * ε) : ℝ) : ℂ) := by
  sorry

end OMA.S_mo_430974
