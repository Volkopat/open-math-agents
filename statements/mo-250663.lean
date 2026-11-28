import Mathlib

/-!
# Condition number after a non-standard transform

Source: https://mathoverflow.net/questions/250663
Asked by MathOverflow user randomprojection.

Given a positive definite matrix `A` and a diagonal matrix `B` with positive diagonal
entries, the question asks whether the inequality
`κ((A + B) (I + B)⁻¹) ≤ κ(A)` is generally true, where `I` is the identity matrix and
`κ` is the condition number.

Translation choices.
* Matrices are real `n × n` matrices indexed by `Fin n`; `A.PosDef` is Mathlib's notion of
  a (symmetric) positive definite matrix, and `B` is `diagonal d` with every `d i > 0`.
* The condition number is the standard one for the spectral norm:
  `κ(M) = ‖M‖ * ‖M⁻¹‖`, where `‖·‖` is the operator norm induced by the Euclidean norm
  (Mathlib's `Matrix.Norms.L2Operator` norm) and `M⁻¹` is the matrix inverse. All matrices
  to which `κ` is applied here are invertible.
* `main` is the affirmative answer: the inequality holds for every size `n`, every positive
  definite `A` and every such `B`.
-/

namespace OMA.S_mo_250663

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The spectral condition number `‖M‖ * ‖M⁻¹‖` of a real square matrix. -/
noncomputable def condNum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ := ‖M‖ * ‖M⁻¹‖

theorem main :
    ∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℝ, A.PosDef →
      ∀ d : Fin n → ℝ, (∀ i, 0 < d i) →
        condNum ((A + diagonal d) * (1 + diagonal d)⁻¹) ≤ condNum A := by
  sorry

end OMA.S_mo_250663
