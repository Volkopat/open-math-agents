import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith

/-!
# When does this linear matrix equation have a unique positive definite solution?

Source: https://mathoverflow.net/questions/258111
Question by Joppi, 27 December 2016 (CC BY-SA 3.0).
Credit: @etaubman

For positive matrix size, the answer is that no symmetric positive definite
solution exists. Matrix.PosDef over the reals includes symmetry.
-/

namespace OMA.S_mo_258111

open Matrix

theorem main : ∀ (n : ℕ), 0 < n → ∀ A N Q : Matrix (Fin n) (Fin n) ℝ,
    Aᵀ = -A → Nᵀ = -N → Q.PosDef →
    ¬ ∃ X : Matrix (Fin n) (Fin n) ℝ,
      X.PosDef ∧ X * A - A * X + Nᵀ * X * N + Q = 0 := by
  sorry

end OMA.S_mo_258111
