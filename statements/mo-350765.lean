import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed

/-!
# Principal-submatrix inverse perturbations

Source: https://mathoverflow.net/questions/350765
Credit: @etaubman

The max norm is the maximum absolute matrix entry, using Mathlib's
Matrix.Norms.Elementwise scope. The conjectured implicit constant is uniform
in the dimension, the two positive definite matrices, and the chosen principal
submatrix. An embedding enumerates its index subset without repetitions.
-/

namespace OMA.S_mo_350765

open scoped Matrix.Norms.Elementwise

theorem main : ∃ C : ℝ, 0 < C ∧
    ∀ (p k : ℕ) (e : Fin k ↪ Fin p) (A B : Matrix (Fin p) (Fin p) ℝ),
      A.PosDef → B.PosDef →
      ‖(A.submatrix e e)⁻¹ - (B.submatrix e e)⁻¹‖ ≤ C * ‖A⁻¹ - B⁻¹‖ := by
  sorry

end OMA.S_mo_350765
