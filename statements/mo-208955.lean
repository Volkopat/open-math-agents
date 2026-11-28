import Mathlib

/-!
# MathOverflow 208955

Source: https://mathoverflow.net/questions/208955
-/

namespace OMA.S_mo_208955

open Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator

def RowCirculant {n : ℕ} (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (a (j-i) : ℂ)

theorem main : ∀ (n : ℕ), 0 < n →
    ∀ a : Fin n → ℝ, (∀ j, 0 ≤ a j) → ‖RowCirculant a‖ = ∑ j, a j := by
  sorry

end OMA.S_mo_208955
