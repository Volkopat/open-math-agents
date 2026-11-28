import Mathlib

/-!
# Determinant of a certain positive-definite block matrix

Jay asks for a dimension-dependent lower bound for a positive-definite flat
block Gram matrix, allowing complex entries and explicitly asking about the
real sign-matrix specialization. In total dimension `2*n`, the real case has
a positive determinant bound `(2*n)⁻ⁿ` and a positive lower eigenvalue bound.
Over the complex numbers, examples of total dimension four have both their
determinant and smallest eigenvalue arbitrarily close to zero.

Source: https://mathoverflow.net/questions/209697
-/

namespace OMA.S_mo_209697
open Matrix
open scoped ComplexOrder

/-- Unit diagonal Gram blocks with cross block `B` and its adjoint. -/
noncomputable def gram {K : Type} [RCLike K] {n : ℕ} (B : Matrix (Fin n) (Fin n) K) :=
  fromBlocks 1 B B.conjTranspose 1

/-- Real sign matrices have a discrete determinant bound at each dimension. For complex
phases no positive bound holds even at a single fixed dimension. -/
theorem main : (∀ (n : ℕ), 0 < n → ∀ B : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, |B i j| = (Real.sqrt (2*(n:ℝ)))⁻¹) → ∀ hp : (gram B).PosDef,
    ((2*(n:ℝ))^n)⁻¹ ≤ (gram B).det ∧
      ∀ i, ((2*(n:ℝ))^(3*n-1))⁻¹ ≤ hp.isHermitian.eigenvalues i) ∧
    (∀ ε : ℝ, 0 < ε → ∃ B : Matrix (Fin 2) (Fin 2) ℂ,
      (∀ i j, ‖B i j‖ = 1/2) ∧ ∃ hp : (gram B).PosDef,
        (gram B).det.re < ε ∧ ∃ i, hp.isHermitian.eigenvalues i < ε) := by
  sorry

end OMA.S_mo_209697
