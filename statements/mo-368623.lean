import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Source: https://mathoverflow.net/questions/368623 -/

namespace OMA.S_mo_368623

open scoped Matrix.Norms.Operator

/-- Nonnegative matrices violate the proposed monotonicity by arbitrarily
large factors in the norm induced by the vector supremum norm. -/
theorem main : ∀ C : ℝ, 0 < C → ∃ A : Matrix (Fin 4) (Fin 4) ℝ,
    (∀ i j, 0 ≤ A i j) ∧ ‖A ^ (2 : ℕ)‖ = 1 ∧
    C * ‖A ^ (2 : ℕ)‖ ^ (1 / 2 : ℝ) < ‖A ^ (3 : ℕ)‖ ^ (1 / 3 : ℝ) := by
  sorry

end OMA.S_mo_368623
