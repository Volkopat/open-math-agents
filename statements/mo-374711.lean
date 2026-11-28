import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Real.Sqrt

/-!
# All solutions of a quadratic equation with a square root

Source: https://mathoverflow.net/questions/374711
Source author: Alison, 23 October 2020.
Credit: @etaubman

For arbitrary real symmetric positive definite matrices `A` and `B`, the
solution set of `xᵀ A x = sqrt (xᵀ B x)` consists of the origin together with
`sqrt (uᵀ B u) • u` for all vectors on the unit ellipsoid `uᵀ A u = 1`.
This also covers the source's special case `A = f(B)` whenever both matrices
are positive definite.
-/

namespace OMA.S_mo_374711

def qform {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (A.mulVec x)

theorem main : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
    A.PosDef → B.PosDef → ∀ x : Fin n → ℝ,
    qform A x = Real.sqrt (qform B x) ↔
      x = 0 ∨ ∃ u : Fin n → ℝ,
        qform A u = 1 ∧ x = Real.sqrt (qform B u) • u := by
  sorry

end OMA.S_mo_374711
